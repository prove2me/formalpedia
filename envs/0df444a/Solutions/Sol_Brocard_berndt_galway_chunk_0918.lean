-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0918
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:56:30.394028+00:00
-- url     : https://prove2.me/submissions/80361ef4-7308-43c2-827b-ec46714e5c02

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 164928057 ≤ n < 165107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 164929307 1250 164928057 164928077
    0x60106030b12010e0d030e0c100813080a0302070308070309020a0b1b120901020706020d14030c0417010c030b030a0c0e070201020f070f1a011d0402310615 68
    0x200c0c0580306200750642c000320b600010040b0090207000788500728280c28018082600010401403c807840200f440250741c1245040c01c2e2655184403000002c00d200d407910034800c1d150010b0180504464202c01081e07403500050308560240c00d5009072070654000c2e00c940c000b9581d16081503083c2c83c1d41007802944246a402d051280f000b180c4050a10003400c0d07880036454076a030000561078020700c0c0c2404480048040b071200c0a0b5070b410003040018102500c040e004115425002800c034005c1c944003c15000c2c4003000040d0b044061109840040200d0316a41c0b0342c001e0460001c0e4001c054088409001a040c080034004508001a220031041d90200d083e8554900d0640114503506000e4098411550200082800c84482c6070182c40e16a00075051b29803002c4c900e00d408030282110110f40e07079030400d10700010045041c4010320240420a00108560181e817280b0005504031200f0201810300d4401d0305004030500d2030380032087e0b903209110200300b001d961034129072954803800c000003000240c84801 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 164930557 1250 164929307 164929319
    0x1b0306040f03020f070e090d090605030c0304110405070f14190c0c2d0608070905061804020a1d060403170d090b010608040308070306060519020c1509130e0601 70
    0xe200740c041e4000e00c1510180c2000344240341c107159031548055082e50128042c4019a20140240d031030120345030030f04058441c5020009030003400020b00380e017004c1d080071000405000000280c0505504010720400c054a44814050f051030b0540b142000050784000321700c03050100c203904442862400d54010340b00c01c00d151f041160380e070116001c100c3d0605054580050f0001091001c200c452121100429404110382882d00290145511000c00c010b0402c0601c1181074003c1405000d07900d044c0c52441d0f03119001d0200c64040e8401500c0302b030300b0034800100c80b104294000540c010000b02001580842100d400401035103015030300010300b81901d40944486268140001050081e42c0c4590100c3c1c3e40403a901c4640d81860240c0c000301c042110a4200810168807400c5a940100142010482c0c242400310092840c0540c41980800340c1011200c03405170360003009102d0803041e000b0030005405141244685072a0800740c0007601a0603183c0002218070346074080d8002c0300c11010010516686480303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 164931807 1250 164930557 164930573
    0x6050627030a0501140f0103020901030f0303020c10020913110d05060d080f031501081302010807200318091306050a02040909030309170f0301091d0d020a051b030604 73
    0xc0c039112031100003000c0010640c0c4050007050149405200001105440900c0f45080c1c4a402040400003401b14801400141e85480805041d280c02904141c0322440d00e24003903009104909100c6054454112008900301c46034004240c110341c10340d51222103d074040552825100030011201c10340c841030108030f2200101da030100b81e000e000241030894100704c0382c4519000f64012a50f1140c0d804000041002542d011101d20f05182801e2030140024509100070590616014030000c1c10010488045075a181c4142c0c1b01003090a0241c0400c1c080c10000e0010f10799035409109903840e100004406034170300d4500008124403504006051a42d200302c07941c0c401c801170000805800e25140d0070701c030100782000303240705015030301d07100392000106101181004200a00c21040042d004041008040213030845482581d04559000101080355441d00d8110001c05001e9504d5442c54032541000c0d860f40f17035000170b4412285008034182c03a4000380801031811408030b000107650b0198410400301d80054040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 164933057 1250 164931807 164931847
    0x103111801180e060a0f0302060a030e07051c060c020c0603070e010309060504060b09010e0613090203070302031212090d17091204081605030a02010903140f030a050a03050a060506 79
    0x51401c407032621a40802c94501d000d03650040c8100d1841082000100d040c40c61080d03010f04820310801d202c04c0d26540c0003036024400c034080802019194501105461820040c1710b0141c800141151108e9680100d02c01e03100f0190082660000d04080d141100e81c0d0002c100380c50520310150540b80356070384050003500d0742910030b40c00c241007544c0e1310302040c0803c1d40c5101c0e071800386124101c04951a200d600c100f2042481c1030304403154100041c0d00707101580c0e5070441010005a10700c48040f0f0071903400d00006e0309000c2c02d03510117034050140c0d07a5030070303036441c8104000e01c0081441900440a500c0e038203015641c0c1d800340c060781d402003202c1100482c2c0302a01822441d510008000072251000c4801104260320b800562041c4103540c080010450310346600b2044030080c020650080c8800e0342c0c240c0008017558450310019060305111071044104100074040500070f4034050089035a2048008d00c020040e030702c44d0b00c034180000c2c504008900c1c0400240141412280004e10542c1444403520780c0700711a90354 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 164934307 1250 164933057 164933059
    0x1b030d0f1413180506090703110c0105250c02010203030c0d1806060518101401020f0105070c200a090b060904060807031106040b030a09030e0303190e01031118 70
    0x1141d04111000441d100502803404600c0c0300803140c40c03404040c6001c001ca5207034200303162410001000241e444805649920007600d1070f0128081c0b110382c0300c0d40c500e8480c10042c4200ba500b000304002c4101c03048403284901044141c00314594011031001203901c8e095880c0001d005810400110b00441415400b070010100300b10703000200108d00c0d42200000516021003214440e46544e4200603070700d0312020302c04400b0403e401103112460584000d8410051034003810806540c8036501d042c1c0350340700308a13649040e01d0420003005141030520f070140c8014440308003140e031105921402d0320001c8092900c200c468a0151008100c10b09000c00400a4020720382043c0d0086028041c001c140e036203c0c003c00000f800c40c000a010302c10b0035420b0001e5140d10f01076240c2d0290030104402c002101007101140d40c8480e900200050091031440d088540d617541080140c0d0611001c61528804445109084803859460300d07201d00e0000305100540680e079203201e040d0039410b0288140f0124900400c802580100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 164935557 1250 164934307 164934317
    0x51f050703030f0c0804120306061211040e040606050301050c0712110f030409050406060e01030201050f09150c010b040f150905040804050d14060603030412030302130b0a050702031b030d0f 83
    0x600681a8411103d130304001070002401c0c5410301c824043c0c213a118400002e11440c06100d16410910064490801c46100401040d9604102c240408102003654080c0441802c1404141000e05015015140f00d0080070700c00d501c1e00c804500c07803510ba9070031104096400794141c80c89405414065038103803400d0310f914516000706c1c008013104500510041002d80b07544000080c1d207040605140c01140c1c4190040c250b81291a001800942c0c1c03c0020f6580e42c81c1045512a0303600071380000300750114104022400741c100e020800b10104003040d00001c01c50340c1c1c103840030004100041916800d6804201e4040c100e20b5410700c05100d004082e4010700d45c0103018100303040c64036644030082626039009400a9484103007020500003150310078040c1135080b2038220001e609003828800d4580caa00580b10f0000d092523400654289600103540036480200128205c4030384926410801a0080d4400502244640242503540382056140380704860440e0000d0010040304642e01410b60f8455100d44850b41400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 164936807 1250 164935557 164935571
    0x90e040c0806010b0a0e0d1a070210050109020901030f2705010905030a090f1502030a030b0d0203010c0f090b1812100c0207030b07210c1103071b051f05070303 70
    0x1d18204140b40c02061041461a99181c807010b00403d082030b43e8040d640f29140e100c80c2400030601c0c4c2100102c071407880c89041c1010352107040c4c040e480d00c11070b01d2070594030b0381c10800000782941d401e40c00f1349001d1500f81c90a210f0040300c491000d00710340409140789920384098845e50007181440b00000c100741d2064000103048006915201c0c07454005030047c01c0001c0b1110030610000101442c00c00051005401011501907001c0c1701a480b0b000e840e020400f09581c44e07403084041e50300c030840614070342c0c1c0280080040c4007804800800110b000309800000c6201446e00003403a180c1502107800c0102c922a811880b81e4084081080e0440d441c4210844ca114044104406032a40c0c0304565a15a4039001010010b18500c4c041c4032041c801003c001c01e20420b0754440040c00c0240c180608080380c5d04c0000165101001404d65101c000f034001503a00d4800802c40e80304015007000c4c00a66003055021040340d440d6680200714a41c24954204040c0c0082100c8036102039000b0406061103030301c0f03424041005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 164938057 1250 164936807 164936819
    0x706051e07120f02041410050406020606040506151210141e062203050601120b04030806030f0d0201140109110a05072301020d0e01020915160506011205010e0d090e040c 74
    0x1c0e0b04160400400c3d1205005d45981c0c6e89425480040d05145900f0402d0805180582c0a510f4180c02040307540640e88800001d21075507a908103461010b2f007645001e5407902c00580c08840c1030f0a04a6041d00014580c003408202d004c44090301207007144008280b90041c00032035070b40c00c0c1200b4800034002d03002141030090045030707440e02460032a0100c0f000f0014088070b02d1424098a0844103070700014144c0c0c19403035040086007801d00306551054040c1030443c0c1d140c0f15880030a20b06190070071542c50754050a400e401000da4103401429802c00300d11509261a600d503400f25044503501c1d17800035505041040305450440c00307400540040c50082c0c14031100c4090a00c50900981e00103107c40107140d5001400c110181210310403030040d01c0f00303d07008604002c2c022003c41c0000c2c403840d1000c0892400460001403e00034210030003074240c2d21205030b03002540e50b002000b217640b002100417607542d403e0803411200e2010024110903040d01550721509200e242c4a4186154400a881955488841500031500d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 164939307 1250 164938057 164938061
    0x9060c0a03030b01030908030402100207050301051f050a050303070327090c0815090112020402091c052a040c0c061e0608030c0606040b01230706051e07120f 69
    0x802680640903058451603490000c0880700c2100c00ca6041c140b4021640010400003002c1c0da5200d5070550b0f4610040018900580c82c0c031906610a070f616600781010401c01414208506034504000340e00aa80591680100144503c260013240e0b0564410702200c004248a44030425071006c452184c5040c09041440740130803200c10340c100300c1d4003a13281c2c0c601c20200c0703a001e1240c60b441404044190070180c962000600d6202c810b00c40c144980c0c64484000c01590b8855044520100e4000d10031899000c04a20980f07040c0b0601c6001d4496025051041d500341c0c1c219542840842c01c3c40304036a01c0038207013108100042521081040411040400320781c0062010f11443c0f11645030920440e48920100c48440d055807556000043c141d0018031280c010f0100000d074441e0403001c125030204059940c1c0004031815074004404a4907626040c040042842c2c0c1000181201c82c01001f0902c85a681c09150360318400c08031580402c1c00034240d00181d003461044100340d40c0030003643e0300400c0f074410301500041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 164940557 1250 164939307 164939317
    0x603040f050d0519021b06220f0f080604031b140f21040302010e0d020d05060a05010303030f05131b0b0d020d0e01060f0b030c040906060c050c04050c07060e030906 72
    0x85000003d0301101100200540d5a240280d44010001b11001c841c0c4010b152140301030541c020840442c03240ba4007240d0425844460008038001c81100740e44011025841c2031a20403d031108a01c4070001c00e90500200d103076480340e81c00d916030414811100088000c070020500b001d40303c4e0000301740310b100440e1342841081810700940e4018507500740e4011300240002e012104070f41145004200400050340c02c45211400e103401100d02d8000e114141c0007003943c0b040080300c0109580101d10070807041e40703078640c02a8141c3c3e0080c0e400304a18010403c545044940558205094040713901040b400a145c050002821188540840d821a40c1d981401c00316074012032800d401c0c040e008140c042c50402544651011b01e00c0341d80090154038030f082040c0385221a140941482110000002447c0900040480d001044543d0003003100903030302c28004040460302d00040701d55018240300e4012521381806041e00070500d10040920f0038100da03880c0c00040c401e940865200340414440c0c4425917070b46d200585 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 164941807 1250 164940557 164940583
    0x80f090414060306180d050c030f041502010605061c020c0a080307020a030e0301150506070507050604060e130903050d090201180b09010f080106022d06191d0c0603040f05 75
    0x141c940c1030030010142014001042c00040950300392020140543c00188031040d01c1c55810b004d50754520702e10507075095208130748150500c1d01c00042c0024054203e1903985003130b8011a0300070840d207911082000220301c00c40c0d11820030001e0440c00380c050140240d0040145034920000c8418480301c0e5501d0700c146402c11609480035800c0304034083d00349a0070400800050200301e000300700c003807113040c807002c00e204c4d1038020036000761b9002c101e90003000390406c0144003520000303012a0b203460341d51000402583c0764600c07070350164400540c44022044038ac0508138070141d058540c103007001d1140c641c403002007901c0c0d88146d04000a441ea8090348010343c400701009404081115590740c4400700c00074001004481c0c44200b0020100010401107901150b02c24181c120a07c50103000a002c1d00b41d5102d00c5580066104c00c0e00580d403d100d40c0c2000f000302c0540036141080c00744007000443c040031200d0040082d0007981074100d0080c58086141510027076910a103e941d04524010140d2191071030005004200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 164943057 1250 164941807 164941841
    0x20d0c080f06090d1b0c080c040b030a0203070306020a0905040f060602061006022515080105011d0a03020418120f1b020105070318152601030807080f0904 68
    0x20300803004140011110800356000900b020305200304025030b00d040040040301041101d90410000700c080f00e030341a00039500700c00c2607000315495000982e20ba01245010512a07403504020802c6410041503220303c8a80050240040d2465601c8950180d48002961001c0089060000c145036450f48501010400d090f00c0001d0114100a00680351050141051400081c454400c01010750700082c400c0005400504801c1d003c00b001404d80751111640e041020f2240d2810414111540d1140210381292002d1b41c85181500d040c01c0b5900d00d10010104084d040134883c142400076041541102965610001885600101035100c4545041e240c2c524000001c829042000042d54170100100d0b42039000c0ca080c0c001e98000394000f8266120302a0010248445500881c003410030303100210000b00215101034000ca07042100c000c0100844003c1c221840a14000d6407691074607018019060f66402800c25107071560030744a0001ca41c2208552480d06c5c08200712241c581e480c0c1e402940d0810300ca00c40340c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 164944307 1250 164943057 164943059
    0xa0608011a0f010507050304030f0609020d030225060f0c170309070e160807080a0b030f0703021305010b0304081b07180b040c1b060b06030c0c190507060e0607020d0c 73
    0x410559881d242e08150400c1414800307100414004030440f02140c0e403014600f6000790f540c0c600b4401038403200700302940c0109048000014150007107640d1380c0072810005403030624001c100b14000f600996000e06000500d0720200c1804036406540d0100c400c50281e40c01c2c180c500c42e042c10880080c0e20445042409800561007049440b1a00d068150030140030100140b21444005008203c1d9500034525010480c150700440c0300700540b98407003852606d000d4142c54054000d9038540382c1e50394143c4030813800360b0310390616114408854840e55060315071490704241f458031603480e500c100b078101c82900c40c09560209115105c500b000c00c5614010442001d80d103040000f0080710000300e9102c0014540202d00704080c2100040e030140302d50701405541440100c104e1500e09101009012001c0881e4000c200001800201c445140c0038081d111072107002c89505c1569204d240b11440c84500b002032480c0c0c00144203103d0b20340900d40e0f482844902401c180d080034010780000da640d480b030007410360f40000c0301e583c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 164945557 1250 164944307 164944309
    0x60605040e070f0c0f14010504031112032a13060819020712121404060527070920130305060106030b06030c0901051209010203100f0605070b0a0608011a 67
    0x10341c0550101c06824605100d40340301001030004441114014040d50000d15144c2c100001c4415908003001d056000304810700e0075140c050002030700f070361184403d071291069a442412000e002c591007041907000040c051091012554000b515030512001c4150040c03241410070300070805640010310881d5940e0900341456813196210070680c1e01030110341801084100046041c1a55804040f541ca10340103800d980e101303041e00010280d440201811203805000c0c0028030101d901700501031009104019400e107042d1030a0008103092032901d103c50740090f40c040051100c81d500c4031070702c14046084080c140040e403030820b6080d032140718007480b82d0844001c14424030004000071400340249080c200174040c4005d0001d401c1d80001891a6001030000482c9080c0341d00c254280ca01d03005505501945509002400502030b40003154194000c2c1d44041d00003e6140c0c0c0001d2080c2194480c1d102c9a180541684a04080071001001c8080c159200c90b0001403180b82440741d007000c04504802480c041001e40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 164946807 1250 164945557 164945579
    0xc2701030e0f1b0901080c1917100e0c01020a120302040509010608160201020306060f0715020f0315010c0206090108040212160f171903020118080301050f220c110106060504 76
    0xd03d8a0003982e030b1900500150100043d640c004001c101d0b291502000000e1241440500e6034110001081025488611041d00010410704400803542c0c14428900e50302e15850f0741d11542c42ca0507005a101c002044007080046440b45002200c0d4a07026152a8070f031400304103484400ea0010001516000070480101d101d94017581130680ca0344025465401c085000a189004802190707112200c0007501030104130b41e0300403060b01c0916429065454030025450401140c00441d1003003401c9c3c0648002e07141940c80380500c02c0c2c900381e00900f001c2c200100c0900464180c03400500c2281c0109032a60341d81c9402c0303010410500e2144c14286810f0903241007082c040100925a400001c0800048140340440100811104800d4803803009048108800b401c00724050081000e0221108211600c0f100078440c03c0c90046050f1030083e2540c1400001c0101448181008403a00103030188420305c0081010b2042e4120450502d4149002c040c120011403c0c1405c48550b60300800c0810400201048115610 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 164948057 1250 164946807 164946853
    0x18010c020708071511060a0203071b0f060504060209090103050d020c0111030a110313180605030d080c0a0203071704030b0906133305040b0c2701030e0f 67
    0x948003a155281c41c2c4240745648000d00c1c050400c522004006110009116019440300045444125062810000440c2000794415070321071001030800d24a6403450140102242e91050740403401a84100854071190300821001d08200c1d203076a0200464115950703071b032000e14003030360080e0b02414040548020291511071503120803814406110000308400300048142da80c11021428400003000708040d01a041d8410340ca042c02c18074000da1070203d40b0490115083c01c404001c14401c200642e1203c0406550760408101c440008458000007000100302c240985072100c440c1c0112420900136a59001500056240c0e60140c0200071404001740206a06150740128018000c0e00701420094155524280c0b14200604106040b61260706e59400d078603290498034100110080407241a04404005000156401c2d01d419904001103030510310858212083c0038504035041184418aa0011072610400d95443d410300d507036101c00b0206040706100e0320069649900150010200503604c4413141406 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 164949307 1250 164948057 164948081
    0x1206040c0501030608010b090117010605030a0503040306060617130305040906030f060f050403082202130c02010c05040b180301061a0c0d14040e1009020a0e090a0e0307080f070b1801 80
    0x11f0141d404810b1700c40c550b401c0d054950203140c0c41e01014401a80901500240d44241d400d4403401d00010b06018000c0040c00c2503e100341400d0018680d01d590480c2e1500b48a400c1c52624900f031400700f01d104401e00382280c03100e882810580d0401d641c610801040307030030f5030303005407416207107005164104000c4d48110100d08190b10001c00013420541c9004140c0704001300303540c1e50320100c0141200d099039150913607900355078010100003841c20001d820002038031180300d921001d0360811500704d034250b0203201641c2c156420042d4483c1445c04400540410285541040fa015542d4032008680001a44c20091414480c07418084e50f030481c106c1e0691411405c004d0000800c041c4440c04040058040221002c030340c001c44540c1c0254035481506440c000f141d5105d102070910015410030100e4004090340c1c3c0b91501250a000c41d60380c1c04d8001c40c192000150071040941082181d100040d11080c040c08050036a4130400d030420f451613441080940c000d42c1c011100542c0b100120007010424002c91010b005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 164950557 1250 164949307 164949311
    0x30221071b08070303120b060304030e0f01030509062404090c050901060905060f0703021c08010512030702090a0c090902070317060d0507090507050d020d0603030807020703031d1206040c050103060801 88
    0x300d00b00d54a500c40b1030303900000b0100640300078170310f035980d040307800c250000e01c402414190707641064031f0b01030b150a68605c4024012969142018807541c040c3c803400780300d40b07a01c1c00588419a95404908114441d4601c3d80f40302d60102c1410035010b4507588903c00304548140031320a55542030404011a020050b0f00c024200b11858006000380d440c1c1105462030094042e902c03540307810f11464181d080c03e804c0c91000d11480307031103a0322421041e4031022250480c0d100f0354140308001d22800c00341c0e49070304c62000c0c0a50400d1003400400c036800c500e90f1011a40c1c01e0707985092542c0700c0d1241d41800590b4044c01043d400241c00312038a104142070b030100d04d500054101c540c842071500076550b0a4443d00303588200035500303503030f4800102c01070700540c00c8403441318036150115665101415440c00078a55400240c0011310700354005248540001085415640c01da102e2085c6041e04101c4030091400c140105a005074112804210060081000c01d00030751003a0800001d480c144000103003207a089600140b5942c1c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 164951807 1250 164950557 164950559
    0xb010e0106021908040b0a0e090c122a0301060215060a080c190b0d02030114030604051908040e04081903021606150b0403200406050f0d030221071b 65
    0x1680001d1002040e07034941d405240070f607486040499850003181c1c07095441c40d03070000700351951aa101c41001402102110300c81c525807101881c0c0c00f0039004140c28064003000d07140c081342c80940401d0b01e40061400907000102c2c2d00c500711000080a0704281d10100169000900d08031b0283c2070340f101c2c83c0d481901620754a00d41f03450044601c0d5560365050a02d40034040854840c10000c02ca0000c0300040e14190b2000f41e5030384084120702000354002d108001130703100451000f40b064a008258039010340e400c000104404101c007410f0320b0101504680c215000141000005464041c80710418811405941c400341ca8603c0e0120a00002a20403018010140704001c05c0041c007019107034041c1c48a030403038000104520400e00702c0d003071090540c00004003005c1c00b04000040082d00c0e01e200785a08100800806000c602c1e03400c1c031094030030600513140d01c01112212400c99041c96541c043d410b80c001c0c8103d6400c5026010411401a01013148010034100011001d0a1002411740c0c5941011426265003130a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 164953057 1250 164951807 164951819
    0x1061e120b151b19080c0f0109110102010c090609090c091a07020117040209010b0c03070b040308100f03110108060604080706030911030d0f030f180b01030b010e01 72
    0x1228580900106114030080314810341000ca61001c0c103200303009803011030a0541c04151920030303000000308400300700940c441d08030010b40101d80352404a1815203c1071010302c69683d1802c2e1504100b006003954840d00720f0400e21041d0034042c0014041c0a4a03511294000c0d400c002425155444070070010302402c65010449142d0052100040329403c0344001550380001a01302e401c40c0c07090b40038120703855a8628900d0340d440d40c0001001e110b0700c00d88a01801b02c0b14030521303403203041007240c0107907200d07030310100420421100700300500160501c4400c2e00e01e000050f41d640c115070031098909a000821000c00c01c0303c402104a070040c06860401c4c000020545140e9407003030102d16090a480c10451684042841600d0310015039003e007880300e046e41c280a8486c80c00600400c10030340256114845440311446a050100d140c00401c102c95030386400b90101031405801809500b204000e8159542480010b2100c10001c0d0802051117001425a294035504101d454040180c00040201202c0c00c010000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 164954307 1250 164953057 164953097
    0x8010507140a030902060c0709150b0403060c0302040b03040c0504111309090203031911010606051611060903070306060302040c02030909010e0702030d0f0506120c01052a010e0a05060106 82
    0x54681d210703070810740e501940c407021000b030300e440b0300025000403001c24844030b1000003190030070a07503d44680c00c0011003008000c00300600c2c240e01c1141e803204401c010a00210709240c2200030644418103001d0300d802d940c1c501075507050388101c50646960103052401d00092519000702070304801c1d8810150308203034184030049210361861090305025540c4e0150482103403030500c01d0b5100312850800210b06002001000382074441c1c080c8040c0829442c181001c209035010780b0644113011400030a55074110415a5000300c5220120f080603840f1a0500018000303903007c008603409544240f01c08920b051030341c030502003555111044c510a6410038009000a5114911800c0c11070f0a180c0c010311072501d64103010307800e6204000302c0c0c0c00d44074108450180035a1161b0049800307420181e5141c4000707159811a203403070f07200d10301f08240054010044030350f2400c03004c1c02c400202d00c8021011000d8030440803041e401c44290882145242e003084580d4801d1220501050b401080365040108034610915483c40c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 164955557 1250 164954307 164954327
    0x1406040504091104020a090e161d01030603060f0b0913080708160203030a0806180103051b04060504020c250503070b0d020909090f0f0304050f010e0d151508010507 72
    0x402940d5a02d1040184010703900740400001014100b1541d9002c2d00d8401006404a800751000c104445d4001c20003001d1801d01d031210801280d81ca00c11102c50540082b04884410310000b810142c4610300400400c2c458840d800171102619000907060f8605018000540d030300801c2c00d608600c86006860200306200102c414540d17200300440c0d6112070b0129203184241c840340029426101c0415404401c03500085946d008410440d0306080664400103082a488402d0000800d01d4004c07502140008007030041817860540020004254031b41c40b030340441c040381c1142100c2c81e20769001e18141c0e130071800360940c0140c154030030b8001c11161906040219595081d0341c450304980002c0045d80c0070943c00a9030584500c2040108000d1503410100c0d00c0c03554919044c0d11140700c4c0c3c001c50381a2940705800204a83c00c4580140410340d901d1030f1440191503141d405061660041c0d07400106c90f000070103450309070041e0188808001b4101458100381c008041c815004111540c0c03400040c80750082c1c0081c0b0100c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 164956807 1250 164955557 164955559
    0x101506020c0d060b0a09050408040e1602100b031005190e07030b0c0304020103090807050a1502070b0f06120d0c03030c080405100f021e090f0114030106050a020726060114060405 78
    0x10030000109000728413000000d0b030044000c913147c18188010441114010302c112101010502c80d0341e200d903244034034285c00745030003080035a0100f240d0b000180c1d1503401c848020100102569504921000c0c1c003030a5600449020300c00420350400464008406d01c07880198400d090014001c950459071000525940a048803c05d000080b0025045a1094000c46d10069000311199201e250301d2030016a55900d0010403503016552607100e1210620724829a80410b0f08407000100d145c0301c08080580304280500020741001d869092021016820018640682500e03034031009105801c1c1002401c0301e5001d04440f08001d00310781401b0103e44009516502d07485c450000289401002da280b900900c00e50610214800304000c24102c0184420050500064146c0341c010f1040001001100c03800c00500341403420841c01d1005002051280024005108203801104e07013a940354601801000c48040700140d0103212540010784141c81840f9040c0100080440c00d00002e2800700058200c0c05540075207 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 164958057 1250 164956807 164956811
    0x2030301080d05072d0804080a0c0b030907030206090409080c0706080c03010e0a05091c050409060506130e090703020a0b0405040f0c0813020301062112050903031c0e101506020c0d06 80
    0x4503407500304070b03419000c1d00c82c0e1200740b00d035482e40e545070708c0ca1b12106821010340324401503100c0042c10000141c1180d2052941e0300152071014219800c0040a0308482c11641c0c20079030303407402040047e0b800d070b0090040840320001401071901d000001803501000400b04204054240700400144484180c0035801070a01c1740049040da844152440c504110a642c1c10200250510290240c0380c1080042082e2000d9200900c91262100240102c43c400c0310b1883d18a240d0b0348508224021910000580203c0e004040d50001070303884d00001c1c1111080e41204000700000207080000d441d0621602e0307410700c43d0b000c0500c140d101d6840041c0512000406520303d41580b0f1110f40f046507820750224018003510b510b0304003410400c01c08400c5d1418040d10480d0f141d10310028030070f02c42e4050020798000c440c00400035440e080c0380078441c4060307200c015440e00681d40c48402c02c0392490818008140d80309514000041c43d500b2444108180b0405036010f90207540040342059070039282c00c0e103480c0300c02e5044600 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 164959307 1250 164958057 164958113
    0xb0102060412050d090b0601020d140901050f0c0f0303060f100c140a06020d06051804080304020f0409081908160207032006030403030b01020106050907080f070201060b0a02030301080d0507 83
    0x400d44041c401d111400008078076049803001002181e5400360300030131003170f804c883c039017032b2414419501600c0d41812510f03280c1c018031101843d50700c11002403a020801d195841c0c10082c000f8101ca00d4000d100c80712134682d410210412955042ca07598030740142008603005901d4103407aa5000d0007101e4108e00182c25818903094404513103030100700c0f0f0904650702200c00c642d1281000140b000030145402558455160061440840544d500b440c50285402111603032454070f440d1f08200701e020302d070390009400940b41c40d0340e1070100320028050800100c800202c00443c09120f0801001e003000204101800c4500b041d55100b61503000810b0030550341d20100c01008a07061041100c201d289000000d84c1c8113400000b0002010303815008050b40c4442078000748585d5032544200711030a00100c4d801000a1007035000520340e03041441c045034200c2d0150000240b01e5440342140c0e10035510a00107000580d00003c010028803408100391844007481d80340035800c0802036a15030340e90903a001022000315161040e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 164960557 1250 164959307 164959343
    0x12081305060d09050c042a11190203060601182705040b07080903130308030411030706090305060c16020d030309120c1707110607110a060309030807020105040c051207030230010b01020604 82
    0x10707580235406c1ca811f0440f11841c05c003242c604c2c0c0801021000701d00a003c0e40003c14030300c0d406144080e80149074001401d01710341c142846200f2540300c1c0700003003411880c2031a00440300201d52188601403401141100007900d0700d02c01c060280ca501418901704c5a0040081010342458115011300344c9510209982d0b0303d44403800c0900803505420025641401550f00006840390040d00352000c1741d100710103584140c1e43d002610b000d980217401c814050722030300e05030f910014a8503013a00d0f84041e00c28200000c0302e10310760719036446d01c580030307034945011407102e1072850244810701040d4030110030040585480c01100ba075841c0640c140c450984c80c0516400701d441c00401c0784a0350402e8440c1d0001d0901801243d541070014007500c0102d00507030100b0010808151080d00c103010740c1d071090b80c0043c1611241c5207040140320145007200360144150040a0000c00140d85030502c1c89460340d0b80303035000219014010f4005902c60078147e0407450b580c1c07600741100641d98011070100c1d486500101e4448000101c06 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 164961807 1250 164960557 164960567
    0x60402070611130806090604050a020d030c150c0e0604051507051c03020d0e0606010e131e0606030e1f09030306050d06060f060912081305060d09050c042a 68
    0x42481c02c0e280010840002c1d041a454000080311000f00484165440d070100c25601c1703803001d440141c100d4014900d488054100a2400300d04980b1910f00107010361b50300e850340b1066036019041c00c1e01c080d072242d1482004990281005040400884040e4030f02071401d4005800034100c0b186000210344e000c2802000d12000340301c1e0848901400050850314210490020001c0d0701141490046500c0c14003a400f4109000500d80d00c11581038503a10b00751001c2800f00a9a16a080440c4008a884002d0a20000e510405c030308500a0340d150082080c2e400e04030701406884288400c1c81d1281d1201d11003008000384280c040c10805090100000d044010307040450180110760440c917002410068404108681503110104550507404000c0b03840d6292882140c00704a288180d45e2203500300303107100010038551070081400e009100005081e66980d840401e11680007680c040c05d16a944007420401e00c1010702640c108408121420041c03005001c010903051090451841d43c2d032001c061980c6185800b031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 164963057 1250 164961807 164961821
    0x3110d020106080733020120040b0a36080f010b030a060932010b01091203050d0b030d050c0f0c060a051e03090f190c030b0403050717220803030604020706 68
    0x4181451502e00d41c00c5c2010380a02a1301440c040700122304c20528404424a8094a05030707003860720702615062810700c04139154042508800c102011041078036043d84900968204801c40304110804403030700c2c250289042400c540a1008aa41482090308169801080010403954010700004038442a800d001c140300d02024941141308000c84080402c072482e15100420104240000b80001b88030b036401100c440e071851003401205a074003404440001e014502070101080d4401b4002054a00d2800003481d264803d164403002c200c00280205188405104c40030723412191200804190110201045243c40b40a0315807042041c04101102c2000709a9170346104c0d0060840b0113602c0b8206005480c0e120ba800c9a140003c5100c0c0f44120145070b1105101d10708500d4000d0f01c4070241c245503449107500305500420480c2040410003250300000d5001040c1010001c7c1070342d01a84407200700c0758402c1d801c0da5000d00c03001c5d400c1d0888000c105030100001213a42c00401a540540c440b8034901d041800f0b0444 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 164964307 1250 164963057 164963129
    0x603010e1305031903050118090503030118020d05011202011b0f150e010501080c040c090f03080a05071401050106030e150c1303150f180f02040908120403110d0201060807 75
    0x190081c5113046a500d600428160f5100048607000c00b40d601f00780c281215805200200300341c0087c80108041c0d0b0000d1003845440c0d500e40c0001d45461801019a812030f6001d811080581c0d036105090b00039540d020540f0140031401200e00403060500f40c44d525101c1c4d450490003021454440c0198020076015003102020b00c507544000d01003961986045c41d02c1d10300802807580200d182c100c16205041c440c0307a2840441d00d0701c0b0f0b149030980d410740e2903044041d0b110403142d07010311508020550010f22110030030324221031302c07200004455040c207000905840c0c0d24003115030187d0007244424001e407078120205821031403414809654001c1581c4030411991561301c040e200c458540b4158040c18825000152000e04144041100d4040404c03503e0080303c402c0e902510200403c4c80010060502e58004c0500c2805035401a0078081c4c0e821045c000e01000b01c0d400c40004406020f2071442d02c1c0708004902c03020364580001c0c00001c1c10540c2141e0303105070600c940111400e01001c17210b07004460010118030f0b01a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 164965557 1250 164964307 164964337
    0xb0402010c0b07080402030d09260304120c0305010b0a0501120c090f03050307060c0f02030a030c0507020a080d020105011406070201080606040509041b060504050907080a06090606020d0e0603010e130503 89
    0x6040c031406000741c00e080740c0071b80c00381c000d080210300036071f2007800028140c401c5511040e00e03010f003c61041016240480528486110801011404400140404903841e2152400b120901d086291150070341c0c4420b0304803805006408010b00550785c001141540c00000194001920391141800300c031909050b40c42104107030600c010102c00e2010100040100324003c40c01440903944522045480d503a401c10048010303002480785a00c1c01744284c1255100e80501d240c41402c080d4160000b5602007006e0340410310030f80c070840791030700c4403502805081d00405104229034022802c980c0410f00510403500c009041000328000200107030307240015140500000340c00300700c035031030586489071601c0306200314048680c1189030002940d42c131a40441d8103503040070302415240e0f00c3d154425a601c00c00a0031002104d40c540384049140080e521451009207495030040131840361004016010301c003d900680d01407030b000c00c014030482546405a43d0841c0380450749070b03441156401c045041d8061912b160610304 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 164966807 1250 164965557 164965561
    0x3120c060b030a020d0212030f0d1a0d0308060613170a0201091e06110a02041103060a0501030b09040b0613050906061f1d030705041418190b0402010c0b 67
    0x5588850414406841031400300105031800041603916240080001d50103c81c2403501001400d0201031000b03441c9810084900786136591086c03c1c160742009111404080c2c2da0980312206110508940701d03149025240411224425103006044400060030340b805000001000c0c1c80201004c002d5000600075030b0424140751000c0521a500d980c100303c02680014902a004503031000e40107421501405200d1022038054582032094039885115803113449103006070f004400160322280944800d0204220700180d47c1d20300001013010f0004180c0000741010710f05650340400ea250041c490341c0058000c000b02c803040c5c0d18040060034030040100342d4140d890908040c03246850000548078010300302190040700807100701070b58103181c2d07561005540016190300210441071180342c0156000c85000303800d484480ea00c610114050390000b103600400c0301d10440402610100c880000c900c4070004002030030b180e4404401c41040d850500760082c00001e4090045011a07000b4000d0149013540039200c15014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 164968057 1250 164966807 164966843
    0x3020301020f0d050708070516030314100603051501090302040905010b06040f0302041d15060303090a08070e010602070602100506060904180302010509031e1309150807050109060f050306030703 85
    0x290f0080a801120b860a18003c1200d06000742041132007000503a0b226400c054400d030060481c0b0700b08050079001c0c03680c3e03000500d40b132510404c10700b445281e01b4809011107501c2d100c0000c00701c1d803004101ca052000c43c030400b41d00c0b5a1740042ca46045075012100880d54041030309080d401060000030032a4801e0000800142000980c580c003400c40f40200c50420060700318a81d071481c0c1140510a10f1200d1308100480700d00b001c11030a07143d401400182c1161f081405810208605c0c0506400001710f07076209140400255800204090150113144007800b0443e03e802d0019654641d40b03440120403a0315000001c0307031502d8041c1594038151004005011500c1d01488444203c85000005e41c019424800040d400d4200003085403070500c46000c0c1c50030015041110381b070b03068104001c4140441d01d695000164881e85000d40301c103069240c51482071191904a40c4ca24190301e540c000b9040c03003030404c0100111031300401c10039189881800c10a0b500d5591600080c24801039401c002c092004e000e09111305 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 164969307 1250 164968057 164968087
    0x10081e0103030f02011505010503011811030a0902120309150f0702061303020907300209060d0606080a060f0b0703030209120102030709090203010b03070c03020a050609162403020f040302030102 85
    0x100c443c440d0000c100e02c4540d15041882d110003806624045881000104035070444540402d05800346140002105c43d0132440221060380180c0341100e03440c1e1912826001e501c3c250760b9410090781036030000d601e800d91400100314482c8041c10f40c5c1050081c0443c5141c0340544040441c0d88295005100c0d44c3d80300c0f100b1503000001c1586020030703402501c5e88000a68000e0103031294400c0b0a40301d27004039480740110100401d44056070402003900d940c0070f21101000c2c3d1941d05c003912454240b060049049810058014200d0f1002030440d051541800010003c4000302d460b414140c4500000d107541e591401d081c194064494119455003114001c00288004074044d4055801410182c1d00c040c485d0b552050100182d0000b801220b11401d42000840d0368240614540d6900d00d200b40155000402d990321042e082c101c0483d01c40400303800c0000c0900c2500107036041400a1f03c4606115041e0f154001c05c0301580200e560303001c00a05500080060b8900f210409a500079907008009555541c1040c0681403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 164970557 1250 164969307 164969327
    0xb0d0204060801052706130e0c2b110a03021009060e0111060a020d0908030412021509060f06060f0406050415050405010c0312020f03070305091b10081e010303 70
    0x4002540b000004c0740e140380c419040c90740c1044a1121840481602d07260990101025002c260301a802003228000300c440342c0112445441d007580a0260108a8010f22600195204189581200c2d4241d5524030034614607045000c00d82151000c81d407145010007086001d85190006980300000d1610380c0c0c1c16540c8110580240c80169860b080d01e8031049006680898034405000f07a41e41082000079804581503011b0980f1209189001c0b414884585a010032039206480a4039150392041c00038840f140c04102410101c0710300c000f003c3d114942240b12980320309020300368141020a0303d020891544c0c070102621209020302a0f166a919519000a0115803062040c09184111184181005030044007610b040310340684414207803044a90302201e400000c0c240c42032007a0390900c40790810325485c41c0074602c03918080d100000e103421306e903295914195003244089004103190704010b400307441d20700200e01170f140c560500e10100e0303c5240200c000240b52181d084034070680e0b01d000006050344080d24036 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 164971807 1250 164970557 164970569
    0x190e130b0d0b040b06120303011a0313080f0d0b0f0d0b090a051603030e1005090603041b0605071515050112240e070207140f010314070e15030609130203070b0d0204 72
    0xa501c80c6d00c0c222805440780001d20814595443c01540c0f04400070301400207580c000419808804c2c44040f80da6542c84580002134400301c41c52001c900c060007400c09128010585508803008860f907420180010882048903000400c000d183e2030110303c6da00c904000403403505a0210171388007414204c10305052111107522041c1c0c00036007115804201d03820141c0c08200801400d03600e95103484025010f201d000d510142007100c800ca2403a040c010403502c0c091000002d82485d96886a9600d810706141da00000c505c000300002d03a2409401c501044103850f046000c494081c03d00c00c008121307411a201c0200f80c00c1035400d41808400e039015800d084016016416101d03071000d091a603850b140400c07617881c42c144c000e14070301d1415100c41c03840310b252016000d05980300502d40840c407203000103604440c80c0380642c0c805001c14a0100341401c00d24010f166107000c002881c0d0860306510304030002544204010300300543c0403c5030400c020940d02e0500180e03018104400801e40d403000b80418200003584107200e11 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 164973057 1250 164971807 164971819
    0x6020918060a0e06061801111f06081902100302070212010c2705060d020403140c030c0102030909040f05010608150708010e06090402010311190203190e130b0d0b040b06 74
    0x403c2d580c4100080794007808025140301e04050885a40303100c002200c1c0c5189051000650b1a4901000d0802504814a0410701448203580d400500d2106581294009001c3d941190002c5c100280285c0783d8401c069404580c1b500741300329548410b600130f03c038008000c3d400086040c9661140c4005410000c46c018440c0d98140f06030381d0701c0e2821a1111798011402144102d440001c000c0343c6040f40103411002c2c2070400061402e0358035510000002107140041000d82c004202c04c900515040c4a0f404108100780007851611021900040c940c02d801040100554404140141071000950080020309080000c42d01d12441c03803802c40e08a00800c4078210006a00c040c0003149540205d05454003c1d00090b000f400c4336100c0d41e0056014000348071181030b004806101c1c002c008198039407181180e0314290051666420718a2090391803814154640b01400601c40c140000c0b0746481d81410b11055821800080300c813009400108030110b07214000c0d01202144062000380b00e010301829000d079100b2114 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 164974307 1250 164973057 164973059
    0x1d01031b030e12040f0303030c0e131a100203090402070503040e0106120f0b0915030c0a0b04090e030a090b0c01180606080c010c12050a17010801020c061f09020706020918060a 77
    0x580381651113103005081078510184010000203000e600401824289030520754025020040810801e40702000c09101d816110039402910792800400c01160329010b46c0e200c554501d90300ca003c2e650344210143c00c0c0c0190303800644c3c00d05000f8140181c5018180a00004e105940c1d10f40009000e03c801204455005281030708012041c46a40300d4207903c00c0c000f0b00a107140395070741000301c8000f60100810a815008564114100741d4a80f201400580861250542c88a0900c6a040b00f21018220388460310350041061707910890b00704031290b00325101d200000340c0d00c0e80181c28681c0501860300680034103030301d100410f100704001c680144003075400742000c03642512890b00044810140c0b40001a062410f002001c003e0144520018050204075050900d16000440c4400107000e000340e10400f0181d601140f10300c0401814007030305405c400703c3c49110078185140030000c91000d5583c41140c404690000d18030040011a0301901c000c10001064007a0100103101186020328080703445c1c0d403081085c104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 164975557 1250 164974307 164974333
    0x30f03100609030213052802041806050321040902030c04031a1311040e0303040501090210081603051b070f0201030b010518060d020418090314040302011d01031b030e 73
    0xa403420071030b07030001c001c10640c001d1140a078000f070101800c01c246480712a071052205503a0380c44d02a0742d0081000006a03100d14148003031000c0c503001c2b90b030842c265080c04020029a03a0002d401e83d0340152000307003e01180a074983c0c1c107040e4840c5070300000b946400801000080e14081d0080e100b200e01a84c0440e01400302d12604a210401c11280707071480b5003001c1d420b800030903400c00000e40d41c0d072005400016100250a0a545990401c84086402e42c3d100c0080600310b0800f40025400c00b099402e0150f4182042d40f030310314801d025001c0b02410545e450001510100d00e03603195001003100003040d0f540d5840c1c14200700c1101010084240d0101c2d007400400342c01544940d00301c41c0615181c8500c402085078060070042c1550000900b100300a40900005c580c6041e0b500c0c214102032480c0c440011404114500604400d041840d040d84000c428032003000940d8005504201c00030310302c2e10200b01003040400590080c81041c542c070180e2000c40f0b80d1112000c3d01a4054012003107030340100d80c0c881030191307 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 164976807 1250 164975557 164975567
    0x7080105100b040602031c0b03030d0b130c0f05090d0c03080703030501080309061806040302041103090c010201060e07110703051905010501050d03020d08150409210201140601180305030f031006 85
    0x4401d0500583c0308100800f518031f00503248500c801d51038480420800c1c0345c01c0010785150031080414203400d032b6604500050f1310300080e15440350100d42c0701c10b1188404a144c050180c10b106441a1305108000620122503554004034045071988500001150364803070501c0c4c00079410100c0c0449c00301c0d14040000c81e51000001c15519070060040040d072034462389c2080c914040b00c50701c0d4800d800400030f0001000503601c0e0301030150001c072070301d00c1e0036240d25090001514045184c4030301c6055903d0088140100b43c1200c101d0756001c4501e00708070130f102440400061402a243d40050954050720346c0c103158142041500b119100e010310001d211590720f400411400f078031a014020050781c410454401100d000700c10305a0700000040400002c80000004901a40c0002c0390848013515210360f0710641c2001e48100038150b072401c0c03000b04002400d20183e603600a401510190500055006201e880c4c00558500c201940e400016291510340c040c035510032070380041d501000c110f11a1600811054071130 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 164978057 1250 164976807 164976809
    0x2130b040f0e0c0a0f0b092407020307090203010b03010302040207020613090e0c0102070e01030f03020708120715051b0c07031502041a0c030403080d020417070302090106031806021b07080105100b04 87
    0x215484c00646020401d0303c0070303840190441c2e000b1300d194103d040d5045c480403c00d8010900008d910707507070b07105a20405003080880d400080e61700344140b00600041c2409802e481c1540d0341550010b81d01c02d21400058030500490702d4107501c6201005021a56a00941201000100e21030441d00481752150040ea111009401100f010500220041010501c0d040c000050280203006840640d506e13054118180700200c42080c00c000d100203241c2c0100728840c4404524181c41c0d5000700801d05010394002c1d850707550402403181034040804e19402600050120000542d030118101a07100c0c2000c0c5c80c078010f500144181020180621100307201990500100d81300da400f2200070714541270555440c0b4905822840312244190303828003010824030025003556000300180001070114074034610400c441e8000c141c002d0800c160400105800b0307101c09544170310529500880260303d0303010804061801070590682d5035030600c00c070000000d04a01c1944400d01518880c01d2402406454110b042294131031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 164979307 1250 164978057 164978069
    0x40519200f0a03090212160603060608070f02120a080414010b060a1b080304050f0f160b03040f020910030b090a021008070e1f120c02030702130b040f0e0c0a 69
    0x420071644641e004080010004401941070000e43c0500c0741e00030580c0e00d100c3c0e40400103950321810240d01807807450003410000300301a180505c400b40c1440b1000b4400c0502401c15801c0c030892401e840000c0303001703001071484000141d2a003600c42c0d007443e000402c0c111050310142c40c0100c607140c4070002c0080600a000400ca00608503910708440e4200496814007003034072051010020844803c00251ba0300021130049004900a00115048010f00307420440c103101d070792000f54444900d14601402e030080d120100c0f00e001c20b10076200d580e2800c010241c0c01e025203000754001180c4040013825868000c00070300380c0340185c1004c035041d41c07606116035490b03603003010185d4009a240c01004406214000c40c0e070f4801000c1c5450000e42c401040883c4d805030403000c07503103441688030440a9010364804200c00044107031000511000076464000380d02da02c200e02000e8040c03003078900365202c0840207812102580c0005801000106484459000100482c03500911035025250440e81c55141142d003a10540e64 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 164980557 1250 164979307 164979371
    0x60303050306060c0c0d06050a0c0f09060c03020f01060902040e0c0a0c02060c010b10030b01030c020307480f06030207050606040f0905060412200c040218040519 71
    0x1942001c018843e04004018006031042c1c2103140502d854808546d55103901c103100104150422a03600c0068442c0c1c02d0b80b039005c21a02480c1c40e650107521003401403c0315854100b01c0d9070032143d42802c81c14180c405006c00d080f0f40c248600000d0120081d4003e000316900b0707001104140c0ca0794000d0309824031500c0c0b8480e001600465004026103413480003408003440e10070001440a2408011404075995000e01e1320100381d0301d44c00081c06c0d5806010340c0c13515448903c051454601280d4030240d0604949100c8000d481507440b800b41d4888454410f43d90307031000300c8a10040c2c050300c1141c5248026280c040c0e000078800300b55000803031600900a465215610401401d00c41d502c540c140710080c800c0c0381054001a0b19040f506e0003086051010780d00480c01b507503404030100c12840c0e016282e2081229203042d01d0003c1480f15400d100c1c04185a00f0b291422603000d41e13100b064200c18640c400d03103042007503441403401c014050036501c40700e1074542080590005000056508201a03216101c02c0301010400c6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 164981807 1250 164980557 164980561
    0x301080a0204110910030b030d02030a1407020f0a09060f0b031e070e04021b061303200c120102030f24010309290106030f02040f050108070c05030c0c130603030503 72
    0x200d019007083c030501c01629451814041c4100020b0b500020460b6a440400e6541050100d94141849010444941c9000551400d50701002c0100300b00003101e0000c0c400d100c045810401c66a0351a00000c8900004025144541d100c000d42c5d40140f140344a481181000038200103822110841600d03c500082c05600072101e0007640101401e100c01045503007000010300108403103945500c09080c05c501c940c0131807092114209416403601ca0054120742c08060203416020000b40d04c1409050b044110486107a100c00440320710714030740602a90203640c0001c2640940b00d510205601071803003181e415040e080d8a803942d41c00b1041103e8040300180182e054120f1840f00d6500035002807900c13601c01c589020203c5161907010320440d13030007186411440c0400004100d110390600900e04458140d000842c909032502c41100b1464040b441446e050054600c00140c091380102c1ca500203035500300f4140c9071344030a5019010303243c4020f400098441c40ca046003c140d041e43c07a104503410340b0f501d92555131440d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 164983057 1250 164981807 164981809
    0xc050a1d0303030109140a051314030409052d0907090c050c010213080d1409010311090a060915020312150319030806040f0216080903010e1903090b0301080a02 70
    0x2011400c0455000c00090340c5091000d034804000035030007006180000145c03069030b0b40804a030110040c100a503128104010b02031100d0b80c40b0002c4000f1607004656114008215001c079042d400303a0391000080d1446c28040040040a07003000071801c00c00c443c5411403840070a5003d000e1035009444c5620b1950052105028250716030f480301446240500340b81c0d0501d04c0001689080ea40802050001d009400904001c01541049150804281420701040c88400103401070001e001d54010700303040503254850603014601c0241150503024000e446161003c0e1610785c06003503003243d442051402d40c492030401c80c0345403000c82561482460080c008a29491348404904142d80c0b00c89104d900d401807000c545100d01306055940450392103904c0b40d00c82c2d49003800c1000216441a0a0210000c0c010022400040118100952103682c488115505c80520801181c01072600500c2030205100c0c4120b0303c4001e0484c80c600300801ba12aa0b5511007040c0c940e000d181450000b031080c500d070707035002000c0c130401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 164984307 1250 164983057 164983067
    0x2090a0207030f0f03110d1a03071503020304020f04020c16090902010903020f120a0b06041b051603180305030d0e15040b0a0f110a230f0304050106050405070203030711010c050a 78
    0x12030350b10b2401243c0042c0503400c412172940610760007001f2540c0c502c0c20340c041312a2083c0a02449038100d02a020040c60309040c60100015914008105640040000d04559030043c4d4140035882c040c2003103440c0c61300e80480d299a040e00c3d42da803c00c019051000003804103030314094505003d9060f506c42e584103155509110707030070740b5140c445607118020406103030184004014240030396004202c01141c5081180502040b110b040c25030b8001d01c8280250180c1c142e811000316009114646101c141c0900c8905040b902e0307180c03064014900600070341e40002404070000190440041072a01049000c80d030790306542c2d46030031410f0440d000d01d190794000340100312801c0541c2d500044404000c02e030110403140c080200c0e501d0303d1085503009c4001c9985081c2a510407241000400094040001c0100700030481805002e0004440c2c401500000003500b00202908070500030240035105102608000d107010391a0f400c1142c1c410000790816121b0007080005010316400d2030300030b480da04d140944038401110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 164985557 1250 164984307 164984327
    0x180712050a0b04050c03040b06030a03090303080601141b0606090114060a020f0313060e090f010504020a05070c121a01030308130203160f0503012904090c0e0a050402090a0207030f 79
    0x189a51100039103020b0f22940a400d03c0351008403555907880c50549030080144001410841c02039011424100000f03410079407440507640c01d030800b00d04c3c51b070351880102d402c07842d914900000c60002007006216140c909403280300c001c1032402500c90686e0ba800600c0301e0302c82c2c240305030b540c02041c0400f1442d584c2042c000801c804007483c41924502d40803140d00500d142d01040d0281da01b03c0c15040d04000c081d6004500003500b4100b103c5042c4181018003580b404a90180100d0784181e07400503070000800d010380110707009a5400100b03490520b9807802881000759584001390f4001c1c070507038026802071186200d1103050300d500d603c4d02031700c50f281c90100c00308000c44000201c3e01880383d0100700d11044281c021a000404907088401d926030709250a2500396112484407a86800045104003c881454030a4058000742520b00081c500d240c0d05010508000641c0f100191021001c2404501281c680003281710f1070084e100b1031043d40f61a90701104a100310000500091801e081000c0b18a1003402045 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 164986807 1250 164985557 164985571
    0xd061b0810061b06020408060f0603010921020f07030602040f080d210608030c07090b06042105071a04050a0501081306090501020d061d091204030803040804121118071205 75
    0x740f01c0380c00340c0c0c5403000c130790003600201710580c070010800410359001c2c8110307030340302d10143d0003800716542541d5118040343c10440c00481458000d0000038006108200a51005120008584500382c0d6420204003d503c1402011066040c03400b0110760154002840c1014070460341d00c42100e20054142d42c03441c82d050305000c1c6c010a03196140000c01d00400c201524441d000a8082c04401e85490418400c4a40354205540140341c14001041007800448500f45201002403088c51015280e2a0403410010980c003c0710380b11080c890b80806524500300500103451f000d803401030220780c40340c0040d40e407441e003150800d480140f81c0c80284002481604010700861158002604111107403070994207440c079a40280320044148a11401c0c02c112080c0600c1d00301c000301c07000d00b40c0e48107544800503087c4264000544501000808201081000d00c102c60040040f80c0001500e0401450200320802031410100e04c0b51001005e440c1d076035052900410300810550b291000700302c0f070200b407440107010020901 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 164988057 1250 164986807 164986847
    0x40501050d0b061306031e060b0d05061f09031b03081603090b04060507111503010e10150504050315160c050a0b011e060207031a150d061b081006 64
    0x802e400c4e4503060880c014100903200491110b24440c1c8440c00d01191020000510b4180300080000d0700031541103482c8a01196800b01d600d540d0740c000700e850344114140c4d010020b50710780c00b910005544881e1400a0301e204113100d508540081c54014000704072400045c02c0601e040000f811840c030307c0112196801c1c424188a02801da0b104044200c0d90000c2c1c0c804000309000050f1082005200101d00000301411562071143c00013201d000b442600050048001071070b12031010441022405003120002c003103140f8904a0000c03800d1004040360002d100d502d0003442080885d026027500e154030300e031145040e503401d40210b50440d1011104d10405910946840c003861215070007142c400340010f030182c032090b40303004100052041d1083c05070030030b980210119048200c05000007802c00310a40162111004240c40700d88a00c49291011001c140640c0d5001c07410640e100100040c6400001414407200040041703035003051020380b02d1403402c4610003114042c15100f440254041c1e503a14000c12441644 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 164989307 1250 164988057 164988067
    0x11010e03122d060a05031606230304030302091008042004060e15011106070806040b13021809060d0c05040207030201021605010e0705180f0c09030a030c17040501050d0b06 75
    0x400300c510b01040c9941d482070300114041003554106405000d000b05003d400415483c00e407051095041c9015009040400809c0e0034248415602901080c1d10745000040c040e40e00e0034180340c0507000b5071241d40018013138680c0180032480d160040302801e01c01c030b0300211082c0d40c960310840c4841414003504d00c0541e01964034200861000d0400c208035118484c40401410f2075154280007406080b00f0307544d2800d40342c0c4100c040100d8541d002112540080b010f5401090b10004000068038006032a07100c2c00c0702d5440410000429070204010002c3d007502030380d50f1107150700e0788814413288443c4210040c1101100d40310400c82820203500a084050083c400141041c105044080c01b28025540c00d940c00d07034680601000a00e4144039180c01000c0c100c9034000c001914441244401100415000c841e605400000d15006034020854420040007000e4a0024101d490302500310384d00020280c5251180038074200300f4081d4003003290251601616030b2420003440110807070190081701e055a8010405003d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 164990557 1250 164989307 164989351
    0x2010c0e0a140405190e0609120301080709020f0f0a0203030a0e071208090315040b04031202040f0306020c0a0618052404021003060812030108060907050a0909060902090406060611010e0312 83
    0x10503000486c0d5040050300c502e003000c100092a0112495850140e40010001000014030019802c8100c0e10901e10240c2c96804004150b2594001c5130b54803031400d04002400038410368040002c5100b13800701d442c1001482c510040301951969107000da02c0e1203840454000000c58991030141407a424001c2c100c0d0400d000745141c1410607a410345044800354060302c10b12080580103a5070400101c07102030110308080c81c000745442c00703502030b02c0b026140c6079002540c4680e04100b40035058107140c2214080c401d0416622180b550b60039910b40683c0c1500541c05c000d1031002883d81d0107004d52a4506044040742c88540800c000c6248441c1c0c00c109042d07503070310001044001840030017068020808a40d80b01e41c90200038074188800201101107542107040140304e1751351501d107124244c901070400042c4180c84c510703000004141c01a000b03588a95680d04000c20400a60002015181242d03607202050308441452400da515050540c50150414400e080e2601d07407404889601c010307001d41d000d0503408104 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 164991807 1250 164990557 164990561
    0xf060903030203071d100c1a01080303070e18270106080303071b0302120a17150406060f080103120905060d0501090e070501020a200a0602010c0e0a14040519 69
    0x8012004079402200700804150001010840c81a100c00ea0400300c0303511070005000fa25030511600e0500048078000818010032010082c241c842c46002480c0700d50b102e6201a0b41c1c0d4000b1200d500001d440701801d1011820811034407000381c0d940306070009903a22072405468128289801c044100301c0d00345ca0030f6145000900428009103403400107507035681400d0900138031041050644900d8210004242d10009500150030010034403c504042e03191110124216144140814048811507a0f070701808820800d081c40e4003419001120100b003d65078900e0155007030302101d0492008992480c00400c0402d200506105440000346420801191200c00080141e0003101c8400c003696034850041c400801c0a03c2132110710744504004040c2c2500c0e00000130b43c3c80040780c1c0700030184008001602248000c40755002002e600081a8102c0c150304c0f210001c0c001d200e4500389200241441e100e2080b14145078603d20700761400070050703060322890481131001505010b0555a0304c80c00d024000f624600840c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 164993057 1250 164991807 164991821
    0xc030d1d0706030204050a05040507120902040e1509010509060c0307030b031006030602070c3620030f0708040f020108070c08040b0c0f0102030f070c08090a170f01140a090f06 77
    0x10f9103005898504200900c034410005402c5540640c2c80e050074080229000700712540000000200400c10503132030320207d03000d00701920801005109a840e400c0d0650b0040b11194171a8040800030032041d9148119260f0300c80c400d0f6110580c1c1282040480c01081c03094105031444030010b0121540c500e80302941e01c080300e030140d00c2550515804140d0004100d44158030500074800300b41c107255880603080d40a513600659500da8242800d144001005102154104400d41d441001081550100f030350640e000340d40c0304031070806512144074002170015026000c1140640c0e00601043c5001000d0780c015607200341d002d4000300c1440320354411640000e402138014409002c4400f0a10346601c011400c03189800c07070318031540145034018020007502e0000a03072103a034080c0d040d103420f60700d4042c2403d00d8155403142c00002500301103a0280407400c078441c1446001c140c5c240c1d408071440040060140c501325203d4880c404498040740303001c00d07401102600f2007100980141001c110304289543ca81b41242d6003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 164994307 1250 164993057 164993069
    0x60e06010626091009061e0903020d090b0a050309030d0510090e0318090403050408010f05071407020a090b0303090303122d041e02060d09050708030c030d1d07 70
    0x7070640b0301c4a80440c1610100001619070808602410501041600d481c4030344030404ca800e42da11001800e00106030000a900403492001021450040c025640600b13100a400c0d8050f101d046507081c0302c00d1264098100300c8204111041c1008040c08c800ca91550000e04000400e120074090441c2c0240e00313104a0340a81040319403004040d143c42c00e11000d0368481d10044116800c148122040703035091100c55136990300304484201141c2d56900e42a20300380520740062100b503203072041024801c0220352169000302015204c1c070481c401c4040404489104022009420140c091001c01c012140b5401c54929580000c00762400c0c0350400c008240b45d50021070359800041404018485980c09050030103440c80b803410250380c20400384c17250000c812070011707000400280e0a090303c0f0f01c1500f007081f41c2c003d82c1a030040c4013641d101008070504002d085030103003d440600521030006114074001040300e09940c0c120000e1800d2941030182c840040403007140c003030120ba1400202c07000000d0144114405040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 164995557 1250 164994307 164994317
    0x3070917070323191a0712140601020a02041a0d0602041a070512030603150a05040c05010e0307050405060307080307030207150509130902010e03010f140c04050904030c060e060106 79
    0x1c9036080c421501c0811110700700c29441d0f510500f003800310340400e0200303100201c1925822614814501011070805101c800c0c1402603402e401c2c0001c0ba43d20030011410401545d109110700140c068511040b801c050300d080d800f41c1e102c55030510040c146034000081d5013807183c0c4802103001d802d8002c40c104511a01c000c5902c6c40d070002d070900000540001d00311101f91840000360909016940307003a91218070109400c14600003000140c480d07501080801d00c1a501140c2802c045c1c180318504401900b000e880c11980004001c1010460b54410000350814880007001071410a10340024400100f1015080507018002d5003004038140e4810401045020f2181d40240342051809021050105404920f981041408c0000008035035464504240d01700300c0358400204013400707100503a0040c200070ba800d81c06500700300b0442d82c8102191f11001010700740418140c2282d03500009680307140714a01072240d10040034070104000c248a400300d4100785118000001d5449160b0081614280c0c00740c3c0b19400040c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 164996807 1250 164995557 164995559
    0xe0a03060f0c0210051b07060b1306030303050601140412060204080d020a020306011212050901020f010603030306080d0507051009052a10050a02060105120a061103070311030f040204020307091707 86
    0x1540c10020300040c40113000c010061810003d0351400c2ca00380030084000061000300d001010701140d648134462499005160b0710283c2c3c0c0925000e009403980c1d11081d0086858000003070000d5015100b0030040605006082c0c0c60a424491016400048041e09540e880e509010104a50b10200305a451041e800d4004002400b503a104051a144050b0030002c0b51030941e014200001d0320701501c8402d101900d0406545400109004070f1400300d8001072401c40d9070030050b00205050b0564449805d80712140240e410740484010706075164860000003d01c0c503448820903583c0720344c1c0c6a002e440818460001d840d081d1001114294144500c0700483d181a83d080700302400924054050550703404890500609011902001030740b00c14051103418080c1814512034494a4000d000454440e030780301c801041420580d0680c200305810880310480441d2070281549004001c0d0350991388126481941c0c1d01c1c840d540d0340c2c03d01010b900050603081c1400000c10011407902c2d084410f20196881f181c00505100d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 164998057 1250 164996807 164996831
    0x2132c041506120f0f032d09050a03020312070809061207173702070c090501080708060721090b04021503070c0305130b1306020714010801060e0a03060f 67
    0x202c55030b51112000d6180b81c3e0303c0c600011008108400b103117070058140350408032641030590b4850084403c621f61719060b8020b04c884104042a002c0500c0e955a03a8070342c505845005000442d901030002a40c1688003040d6000201c20020050072464441c20400741420220004a00507030819150b1416082c3c1001c00c1048255015642c40280e2246070445078103030402c0c503003d43c0220482d003100544820950380102003e1643c015504501007a108215942c807000d0805403520303070f942e000d206d900604100c00000c941d00002803100030384100750007502030f41d1641d20080d18680d000c088003030074200d041074000301d4080142c800c61000074018004208246007502c1003103440d01e50050000b0b1651014401d000849a010f2031103d44143d0604207079a83c1c40001c02e10b8444440079501c01c000d121000128074207020b24188128080b00c3c150b4088440c1da035112920000300c010032000c01d82c001207400004001640c405d40b20090001400f400a0900300d449840e44010789080d401d00a1049403952900001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 164999307 1250 164998057 164998061
    0x2040807030b0a090b0609060102010b1e03011812080718030605010801050601180506090f0a03140607050712080a0219020105150d08072a0602071802132c0415 70
    0x4049203e15003000b002c01c569440303116140d8080e19181c000c070a04400540c06034003d5004e95842d040c0100803903c00d0031514602d06008056aa01a020b5405d2040b00b6101d4413048442520781680090344001c00540814129080c010003000c41040190080001440c0c15040280704055070203540080f03071540c10140c07003d0075943c0251840d810081e00c007000b9020342404030000300589500300e540c565100c854900240100307482c202c01c5940004100000420400d22016080700d601c0d070307002515102c0c1d403022030598103070203004c03005404080b5038059005a288100805a4491142c40c03005082c81130300c21801c04011010300120015030354842c01e00c001d010144511807480d0404032502e0460001d1036071402d03d20700600c0c00c028400c058a02850031408500085a10350f60001c8000070501540c841000b07507600045e1103000b600a0310701d0421031000d460740c000c1b5061a280c4072200c00a45242c0300c2d001d4482011244643c2205101120300485d012403540c11502603070044820004e5100c0322100101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 165000557 1250 164999307 164999311
    0x1d072304090504140c180601030209150a2601030303051b030a150f06050d0f0902030a150f0207020f090403030e010c0e040e0106081005040503090a030b1524180402040807030b 77
    0xa480d44441c0c0c2d40d41781a92503140390031124400440383c403180c0d220580107030080c2c081d8440b0254010070224090107910903281c05800c5030100c40c0c0e1051074150440c218010350340d18859081100595400061000c00e0081d04055080b24030075484000c20540074080416a82064826a00c2c4985440503a0280e5540303c04a1000d4841c041614010302d1034103402034072500c2071820000c0000e480d402c50401d400c44076813001e5000358001d81600c001e040b161908400220000700194005807404212031648140c3e8826500c05540c082c3c114803062080b00e04008200d01e00500c01c908050b110075800301480070a000300f04082c0300d40e884030102400001c0800080d51000a020503913070b0b02d0301d40104074036407000810301150180b0047c005960303102c0d41001e0b410341c03180030b02080e04805103240000402000031401c6208803060740c0d0410401030504100916401c59101c44200240c9401d0318449907010900108101c4488050340d4452100e801c1c0420b00b070f60400d034440d1181d9045010b040040c4110300c04199 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 165001807 1250 165000557 165000593
    0x30f0c03190f02040b13181b08060f03010c030e10050f1f080a03050d18080d020d02090904030503040c091103070f030b03060f010f1d072304090504 65
    0x3821840d0448440049044842549101d40d495082500c04802e02d40d04943c00b0f0604c2d910f245a4520034890940c02001880c40340e8242428600502080d403251889500c0a00c461034801034201401010121000c1d44041c00702a4019034038501503256503030034401d0102d520f103940c030302007100448a20094241030380604590115801e0204015040d04002070311503100311510420195042c101102c03208500c41600180d01c54400ca065039400c2c19005000303050300d29900d007003d0207003222070701040088030326441c2c00910f0300200707001d0003900f1801e540150051101140c0d0060501803100c00061060301c054901ba404900d0000911003032003002e000000103455914801c0c841c00e040c41c14ad03802d0501c4010311348000c100c22164100c030b80714465040600c01303080040c12a0010b0822003400504000203103d40390300e100c0280c50024902d0304964032504600114405503d4580c0c82c050166404000d040c52400400c0e4461403040b41c80200d1030180000d4000c8c0c3c90002002c0c40e107840d024450304020b08440d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 165003057 1250 165001807 165001831
    0xd0f03020102130e011a1204022704030207050a091a1003020d1401050405061002070b03060a03060f1a030f03070f02030705090c0306010f03060509040303200a0e030606220203041505040305030f 85
    0x56a030079180c110319250030541c19100d4802d008016075152b50310a030071003a0014540550b4047c0310600d5400900f000903248100d4011201507918007091003154806112201080421164000140b810000342c1c801c01d0300d41c0c100540740007203101c0503004a5610801d09401c0109003801400a0305091152681c00501990020000d58203098003030740d070b44007074842e0805000000000411640f9001818402107a0000040c40311280440e40e100240403135900c40101c0804e400612030301d62034001101d02e491420a4041c5113800700c5612810030004c021042680c15204080002419803a100009440f03520601200d07500c0e420458001010740d552090580c0426040c0381c01449142d031280101504a98542000a6488840d80032894000020081405c0e10301000c00c00020302c0c0e80110505d00c0c203050440076154660340e0141000142c80c00a10050003070f41ca401080f1481d2405980255003060059507007140960004103800c2c20390b41d0450b02200004c5c0040103100c00c42e40b000703040540203d100880 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 165004307 1250 165003057 165003067
    0xb0109030b0406020a0201020712110f03030c0a0e0604030b0702071701150510030b0a0f051504080303042604090b040c0c0506060d0323040609080703020d0f03020102130e011a 77
    0x399408400c0042c1c00038010f40c0c0e0000769595864000d41c101c501c116400155044e450500701400b03061030030b8525400c03040f0b00070100c0f1110f0110001c0126486107000c3c0c4441420304a440c4801c0721054040f0300c040750046410007011001c5008890081c0c4161200c0d4010f050039414000541406103400c040c10b8050381c1426541e0300d004a445000505072642502c81c4600e404500c8012400b80101c4503e041e000b040c3c2180115004007114840020b4480035587c400075840c00a0105071284640c1c0b29260792500280046800104950b2903640c8001140c003e03d01140000341119030140d00c40e41c4210b4180790b0300c500d4980d840c00c00e80540b00c88400c0c181040441e85400d0b071240b81c0c0301d40006010500c904130344411a010103008010700d40010803202c07080343c0151034020358030449900900908000c101c0240c1d00080e0072000003201c8040d41e5014064a101030b00d141e46000f0f110890035022010b654003849900740b1940c090042c1e80007032001c4642404207516219000051340e490000740c41c00c1c907404010f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 165005557 1250 165004307 165004313
    0xa0b0a03050715260705090f2e09030b011712030a0203100905090c0112110f0901020105011502100f0f0905071e140603040c08030f04050f01110618030d0e01020d0b010903 75
    0x89081c5c2c1c0a0080c0c00c140d079a0348083c0c400074400d00004140503a001c075040c506508007401440d240001c00b11081c01d050701900342a60140c400220a10008150440000052121102d0b2403101e1695050440c1150701799600c01c0103100240d04102c0e8180c1c00d055020007040b82011048098000603e1390003030801c010b0500b503a20b0364480c400343c02e515043c817105295070115582190b0ac5030708042c01c10300b5417588410070703000c42a80b1503204500c0340d40150308010011601c00510322100100341d00c4c40d0000c000e01c84032400014050040000140b000d25542c0030101680340150251000da248650060104241805d811449a003102250f0700103070307500341a0a205080c000c00100c44008000c681c465126559440e080c45411420342000b2614000400c15030240c140d5403000d0300503550203d801c84040f51625004513890700840380e2036000380d40880040303034003c612812003030111400f140c1a6407500036060036480035504410002c900b00d0b940001da100309881c60b403140d110090300034607110004601c0c44d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 165006807 1250 165005557 165005627
    0x90c10020c10020709060305060a140708010e090307120203070b101203031d010603140106150f0503090c100f02060604050601140319060308030106020d020a0203060a0b0a03050715 79
    0x484640110706694682c1009802044608010070880c0d03c24441c5546900e0b0541c0c43d5901561303a00462410301444060128145c009584645000e90b5410000e80c0303001c4621030700c03810240c801c0d00540000c21404011845240e24102201010340007907540700034529010308090001071101070024940f004c10f100781240b005003654404d0301840c000c10802c00c0300044841b48101a04660380562030040300000300102c030440c44041c00000c00080004a17a0b1b00c02500c404c0a800020700000b549020356454818050800b0f580c221001c942100c1c004000040840e100c0ca00b11110079020961540420003041d80c108a42c80d03200405035070510150070120000703845201002c660503086000031000400a004405240d42c0c441801d94040c81002d580f401c110480751b00038081c0343d005004810400341d025000140030511158041c00901007075a69401c244005d00ac4d803294a0b034003568000000004c148108a20710181090f110803600140c420304010742034000140007210403100d00400030689170451 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 165008057 1250 165006807 165006823
    0x8030f0f0402011b15021602010f0e090712020705060106122403060903050f220504090c05040e031b010606030b01080f070815060a030f05072d02010b0a030308090c1002 74
    0x4c1c00402240c40840c5070268801039950040c0c0d024074404030306008030760075004481d42d0890007070703d50240240c10200100e0b00c10340344508454111098802003260584201826540c5d401c11200050500c541030f03803603a0030940b081c3d10207070010300c0000380d4079004c800e6441407419203c0d01c0d070601134184201d040c81039182d0580d40310141035a69122008800d0501a1040365000800400140d659200540d948480000c40e1000c812040d580040301150303c1c20a8031031032060a41003042102c8061030b290800014151007003080d17030103000074800d10081e01c60b1692904045106280049501801d0402c020111400158050704008840e010f0001030f0603a040119000b0100e850505801d41e9000c40c6943c045030982d42c0d01c0d41103580043c088103520b5244d80f04a0f0790380c90380b02050115407200d2000320343c04821380342c000b101c02d2031844042a0182c071803081c0c1d4207070012030f000219140745070340c3c002103040186602c140e010907048030401030040000c2c0701c10441510101c501060105004000965032225 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 165009307 1250 165008057 165008087
    0x615030201200312090619060509150402040506130503061302060706050709050d050d03050703150b0309010906020c100606030c0503060d020d0b150103061401080610051608030f0f040201 82
    0x72031400b180400c014021982c0f030344407a0b5540003840c1022545580d468004441e41c1150001c10190f02100341c000e8020b500403a00020712008490315100b0710709104102c034510755503100f07501708000500d940b118005400d05a02e04160320b49170515000a1500707003480184145901000140e104005a86c0d81d410740e40350682003600010303a580c803103805844420064110380e83c0000211100000c03c01c00042450744500c25680030b0066403580501a015103113454040302061101803414880560040041c6a2082d00e6000100d40400d007612040d08981c00b0304680351039a00402c001d008510740c0c6006040085c0103515003041041d410f402c004150b8080900010f01c0b071034104c4003110542d45c803480c0c0907010541003040c6c8201d40c02d1480c0a01540700300b00b144980400c1c1003440c000341100011848282404041e11010361b540c0e240c000f00030600a01e0041e0f80d09010060061103114035000900c0244540300300e440e5a030368108004c10140109008000c0140110000c00b0040183d07800243c002c080a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 165010557 1250 165009307 165009347
    0x703050c0a051e0f0703020a05060d180507080d1803060903020f1c0207050f060f09130e0a1e0515060f032407020303010812090a0302100c0615030201 66
    0x20a10520340c100944940050007030300c18000c0c030052800820034500c00341c6030035400300c0b02900d03c4101e01c07903150082d51002030b5001030700440801c21801e00070010500c4024202c0006110000d86041105292640301d05032016480700b142441024030402620352020818113050341c42c81c4805c4004d10000c986400010324042d11104032000305402004005548502e2505480461081c2445031000f2030048010100500c00c04030005030a040401181c0304014015000d186814080351042d64240c1c000341400f60800c0800d80c07503c1162480740b203029000342904010f040d145940d0f04004085c601d031501c0340281124040240e4001450004040046000c2036103182e0842d0b85000c0000c1c8611403003092203805010700743e44110564818440300d128070300c0035001d18a040d1201ca100700e950380003d0254054690191100c0c03103040c007d0001405076100c0082035811044d8a96020490354414003d4990105620f00c1e0200b040008502032002c0d2206250b64800e201490b680000702512074100741a00300c01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 165011807 1250 165010557 165010567
    0xa0215120a1109270109060302010c0f1403040f060909020903100b04061805090706020a1a060d120302090901060201230604060503030403080c1b0d080309070e010f0911030c070305 79
    0xd169407094440f5a4401010001c60b140c55400600c000d03100742c0e07002c01c000680200013040300303d010300c01c050550703406a6a0481c842643d0b9903410b0041ca004105071342224150402c02000311080000300040c100b25514129080c1c904980582200e116401c0350000d20300511039203140752000a0f121800e0000c140c00414501c640c040410020324103a04151400e1040a00002804036103400050141c64060112404240e8507041280c131081103c400521201a62003100e440078059040d4942209000f4061520008503a0720707180c0c81c0d0401d800c9000800c0d000f0034151064034016048034010880c0d80000e101e900b20820708104200f0584c4501d0004880020110b00301da12954801005000302904880e5a25140c4c1055100364024041d21080361065400c008001d0020ba40c03080b1381c0318009481c3c000c800750f0700d5071101c40700d400060540750684182c030f00004c0d4402d81c140d10a402410010031010702c5a0600b02c0880c05d03101c00d0610000010020014803102003084c01c115596203070545800c540712 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 165013057 1250 165011807 165011831
    0x80f060603131a0109020702010801050f010905191206050402011e1e020a050312010503060a02040503100908090a061e02060f010608100b1206091513020306060408010e0a0215120a 79
    0x91003c5403280c00c2d541402e0300000c110740156900602445000740c0304c030b00c0c1a070790320401c02104041d0001d140d80020071180303040085091100d0030300d42d11042c0f0260701421a8442101010b42c070703c5c0020035110280c55205101c10355800581c020318804641d801c80250421603034001d4500140741c1030f96150034541854810305107109001003610144e00c40192070303490600720881a520780003805454880c2c05803101040401e0072a10842d81121409000f40000019a400c100020403000300141c035958410808040c81c0c0c0d442100000140c03500b0b45403640000345c101c810840108840003003c080d5402007040c840c0b40a0810b5850f41150581e2030b0081301640c5030b00015802100b280d0003086240c0d40231030828400441c1aa41a22500099034150450303955030a54500f00b40d4003480c0103801c1039407441270070011401500203580c00040600301524107640c804042d400c4a41d54020b90000e900841c50842c110301d00300154010080c1d15040c4c840c28141012102e00c0c03180c03000f506a508140d070381d030b01136210 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 165014307 1250 165013057 165013073
    0x105061e031b04030b040c230913083c18010212040303090501021603020f13020912030c0c0406030b011206090c0b21090712080904110a080f06060313 66
    0x120b4086041096140d03680c0c0d20f07241502c20710589003181d0303141100001041c0c40e40903692961210f0301c0300c026880998400400c0c850310000140280249141420f190400b1860107001401c044101d614504803240405d01e003819244186440025207400d8a00d00c0c50340400040142c03444a4002c0d61080c5242140301c00503840c1051410300c000c2d1501c004a0300109164025854400700e400a03000d84034020b035980260b000d071208900000b54031425100741210503017004000d80600803990800145808081b60003e04c400909984080e5241c0c00020801e44802041c402c0810141042d1000d016242c01c541e03e8910714601402104c43c22081407894409000141d0444005150030681d00d0140703d440303050420042c0d21201408a41d0011905104840850840322500c40c2e48481d020700340c56801c0100c41405001900c8041d01c0707006051080d81040d036a0380c420250008402035500340d031031245072000f0f0001d0900800030706006007101e00300709858030383d001147e900500860380c04480440034508100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 165015557 1250 165014307 165014341
    0xc02190519060e190918050319170f04030c172106010801151404082d010e030a080a0905010c0e01121109210303100306050105061e03 59
    0x15004501c00d0303228000811410301d420a4500c66903400d0040c0f0b41c20f20a010380621001090f441c0c807404a401001070070302540c405810242059801c0000a040ba240d0925582294220400200380c0340d044003003080c0c02c04071201c80c1c090b00c4403621015162080e01c01035119030041001c3c1c1407200d00018102080040d040140303040e00ad845d02c0d9a129805018035501c00c1c510f5400003880b0681181c007083e9a580109803044c121240c1181e070a441c40e070300310801c072003000490401c0e000b00d080078040400d442c1c609000f01c480c03a040f00e0741d4410410900300c440720141d00680c8103038601130740350180f516041e48001c13080320802c80711401d145c03285499000101000b403d12040203001f65190802260b24941d11200c44040068240e8030603000b84901c60104003298184c401d0381005c0a020040d01d00242000c4070200c200030300d85c8023450030310703094a00143d085600c03c50304204140c0c50b0950a00400c00c403072040c0380c0540000d46038141450f0418650001d080c001000700204c950002c4001100765140c004695 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 165016807 1250 165015557 165015559
    0x9090a080a051204050312070503090a1b0b041508130b010b091305040f0b06040b0d0b0601031b0201060513020a0206150619030212010911040611100c02150906070c021905 75
    0x911921303042c10081c0c0c03079800880200120045900220b50301e00d2081040c2c030b003e9220320010300034a04071959a4200c00c182ca104020000c4903950740014210185c00252008102903540742451042001c070060010b1401066100101c0b500c201c41400f0a690500c99412b6900c0c0e040d11031750b81d6500100141d0b00d080e00e0080440d08c80c3c1400100010005440c001c1e400e02031150600284039105d10040005035121180208c3c2c0001a0586900209611600d1503820a0060500003441d00b0301c92881c5c5038004403d040b00f40942c0d1207403420030040c280004425030340109410114107080c40380c08001d407184e0010b01360030078110000f40b01d42d0a540d1918202c4400c44070580840480548015014029401c2444128a0b2a42c1c68000098410640c0603085021200034a260314081c1071900603034038802104000700c0d4502c1500c010300300c0703c03a84ac401c0b1001c80c401c0c1d80041107216601c12070b40001030710040c80b0280300e03001a82840143c41d000390280444a40c12a0010031110301e459810030400c0b4160b11503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 165018057 1250 165016807 165016837
    0x70e0a031707030201050f060d1e05030726070c090e0f10061e240201200409152909040903030905060c030c090f0f0a0603020a0201060509090a080a05 66
    0x42003044508000b89000d9110360000d00140da950420a9070700071044950725007001d80000440001030b010b0000101ca00041c5260311550101034440914640044200b03c03030202210b00e0301c0650301d500b014074003a0000c43d00c6106140680715134428010011a02c0344004203512440003244400f000e014800f1280850702c12940e100001020a902900c0e891040d4128059480c1507403190410254001003030360024040c2001ca40c119071158a103140103d9485400c5540c3c03004100d04001c4094201c5011030364401c001a112420050b0841c200c80340aa010421280302c084104149501d0381c1c059068003041c80030302d00c0e42454010b03408101d84511109241d100340341025500030103401d41e01004501c0e000380201d51956440c81400c041920054036440b0190780103005035001803508881c2443c000d000a41800040b0b1100808500c040316540c0000300820f802198000929074244107240040c00c3c00c5810713005d20704200a24030f07140c0c03ca8980150a410300010742c2c240d2130b40248222055039a000d811 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 165019307 1250 165018057 165018083
    0x4021c050a0506071d01230304080f03090a03030b060703090512100608060a0c0507050c06031005030a0b070e0a0b0316050910090e150108060432040203071a03070e0a03 74
    0x4004000d005c040000b140d403d408840c00d107501c210f10485c0100310700103480001c4a91301c00000c407681c0005204980d4018100282881d120341c14000d11300a41501d0024401d541c81403401070103981d03a043d2090f000791406d01c01c1c11b0100340c1c01803410045802c1503885954450003400324904042031811100c005905102d400111081c000600e5440380070428070400c800196004125070031b11600c1009051903028000c400c0081c80d04000440d080000d4440c00c03c1c070310383d8550100c1c0c1130184640c810740d149800785c0c3c104a60942c01404068120b8000c49800c00031a050010a0503580000b400343d003480030320702000c0031400d03000d0000c480d418a0020844000e040401000600e000b0103070165a00303031988240440c4007010b0b000000d4680c003038141c41d113000350794500d01400000d01e45c06126070a021304010340409880000c025004c10002d010480c04c44a02e044d005051400c0541e60040201c1900b02c5010115070702d07210103981c3c001c0924a06054103540d018001205900c017900081c1100c0c2c2002d032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 165020557 1250 165019307 165019321
    0x30d0204031b0803040303050a0e0f0d12030b030d09092c250608070e03070e0705090306060a080309011224140a03051903050708070c0609080604021c050a0506 70
    0x8641c600350030900c0c40382d04240c032640d40c04d44134010b622004020510a00c1070046403070141d07040b50b07441c0d00080d10b03048a60040000089045100c04803d440051041140c020b555030315000384901c0000c240c0080c50303044c15045005144c00321602c100145036544045072880080c2c075072441d0000d50b8590510441d40800c08005c1916000001400510250364242456011140500c000210741030f9440700b20450382c45100c20707602010049034890b40750103a16070100d2003441d42e485003401502c1d517a0318031f5180d0021780c041c075250030800307868144110302c0100c08012150000003158544802803a0408484103000540b001034882c000b440d601c0b0381104c140341c0102d981e50040c032908a4040001c00c003005481d59003840040c074990b0101920a4101240000300c0880d0a40d0028410344a072600d14504031290f281c0b00d4043d044004121100c100e1003004200c181c1c0c2c094103003c060107040c0050400e40c102030b40000c0c00484410880100c01070715070443d809016080c024600080c0e00103003540c61030f241400c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 165021807 1250 165020557 165020573
    0x2508030a090501020d0c05070e09011e020c0d0912030c1a160801090b01080f0705040f0f0812030c070222050403030c030e0d020604111c0501020d3b030d020403 70
    0x70041d50f00502c60000c0e48405540f203150800551500400030f00034240c1000c3e66100b00000081140d0815904e502010310420114154286a155003d500588a0000e00c81090600f03036100c025204100e0f84075802d00c598003501c07002e039081da5810300b41280c2070415403905600360b00b90b1f40702001d1166901010050340d011250721400c202809a030351600c00c0e0b0380701c400003412074500b12406030000b41c6090024400501c02c561171604100d2030b0a00c1400c1c207980b40302e030300620401e075084583c242d9011001008002400c0010a8405034a41c00319400c2d45030040401e502401816406071244080c01800e401c200850b215107040c03d00710020500c514a8642005005880c18416a01c0002e1a00e2216000d0050105082c020048241e0207805942c039a52036642c3c00d031282e45456540466040c049010b52821b2a6400e002a4880c030000344c1c440c44035050b16070864100d042c44000524000e00207a60a01107501c1c00303207003014622400710903900b41400c1c00b0b103103010300d000307001c2c43c070744005800b0040c0000b50b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 165023057 1250 165021807 165021809
    0x90b09071a04030b070f02010609090311060108012904020405090114030c0303030c1605151008060601091d09070302040612110f010507030f11030d140a0903022508030a09 75
    0x4610385101ea15829101415948254800030b0318003000300002c1008244035180f8618080071910010502e40e80b2400040201c82c07060030120701281a4445905d656003042c400c1c980100384c581c000300b040704542608500b08603044c440103124813100201c45032559696038103a4002d041c002d801d008440d0784400150348031301e0b40d00d04542e100e40b107084c0031003d60740b5000086910407040c204c4102d00f0445203000f1a51640d036181c0c01102c0c00d0240020b50088401010202c5110b048016001c0b144249080711041c1052000fa02142c10492101300c28001400c0118039540c0e05011210304080607650000000e0400f0001d4000a40c030505000b40040c8066642000001140c0280c46958000208104109030083d08048113804501c2c20b008910110380201110103c8080310304055002d001e83e50754031415544900f0768001220740d03d0031101c140c3d01c110314980d0b40c4100c0b1040c0c100060768184e100a0750721260ba80300c11740b99900c00c0b6043d0342e0f1f000c5c5004075030000f00007210850782c03510f00412004d040c506603 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 165024307 1250 165023057 165023069
    0x1050a0507020c0d0206090111030403050d030b0910030b010303200a05010b1206060d142103070f0e0310020c0102040f030b070e0913020d060209060a11071a160204090b0907 76
    0xf400301209203a1501c0346884000759402001980b4020244005441742210540350300310a000038440000822005e11640d07401d01815580040c030a07004004010754024094105a006280c102d020300024103481e04990660341c240c00e0810780c8444810214507814a200c480f801e1902525003910200001500802c1260400321107040c40c280048408a688400c11500c880d806145907801d038001c5100c02544049480c200b006071680e901c1c01c0c024848580301040d180d4407414000000304800644e1103a842841106185440c001400780c01d8006075035401003917040c00e1240d500190316001840300350304641c001c0c444014080c20300ca590b0705020341109011280000400c1c40d1065002280c0350990481e8420080100c600070030300d8098003448410380890500308c0e009035023040764000503902e40d0081e04402e0440d43d0f0703e0400142c3e0109103810702055511060140101030f1043380031009040a582d4010a0800e1080d18000c040c0001405400000000750001c0c2c00c00782880f01150f4040f42801c26280 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 165025557 1250 165024307 165024313
    0x3160603050a0b0a091a030313140906030d0e012f070e130609020609131a03010203070207030620120f070509010c02010e0117011701050c09180a0e01050a050702 71
    0x81e6481c01d01054900c0c083c2201c0e880182c51506200c100c0703e035401040030114442e00749085c2d02c040c101292940d072120b52001070254040c88100038208a07031811055880007940ca004007030030701c400030130742d200700300c1e4480800d01a40101013080781c3d1150b500e80e1244100c81e00414001c40c005401c9000e2010140030f041164000c030384002c1510400306001501030041400d9102e240705840c1c56130b41c001c5c00d482d00b080380c0c030a07010448800d65984038880c1c1598400d0f1035600080040802d1429445070303941d100c0f4039001f030740140f041000e059008608a0103c1c4d8101101280d20594132100c3e032065580141040306182020550b131002d0394581014074801d49094111211503242c3c40700958080c0500d511860018610b25024070040d40b1886400100c0007060510002d0081240885000f04200740c00010030f0b036841c0c5007945406407003409640d400507503840469140c441e09078041641c1071600211000014842d0340854801d1b1070b554403400203002a90000c029078280703110054060301066612000500c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 165026807 1250 165025557 165025561
    0x1005070e090a0908040302090a0204050d150c0305070813020a05030618070803040506031b0d0608010f1d0705010309031106040b06090f090d030f0f18060e070e0105040216020316060305 81
    0xca10034200035513040115141014915400c010554200070640c01d816a001d120010780c43e102e00c0801c000603441800e06c0c0902c0c0566803506411250320b1800b0004050404083c41550b0f40c12111464102e042d000009200000d00d00110700c0c2900b499010a030503100750b80800155091a8581542480c119016958001d6842c00b1480d5030340203900850743d11a0b0b0410100f00000c0d280c0c201e2240840030b04c00800d0404200108040499100e603100207420b03516168410754514040c4140b540c403401c04184103c00d8201c00410903501e05003401003030305060743c82028078245030280b03060310104203000084440900c0c05281100b03c0007c25240359009410311404503c51040440b00f180c451110b640080000225002084015003c0c2085d40d2140070f0740d9111280700345044d40030750030003800700c2072070200300c10000e250903011a80012200700f02d03604003801c01e000700d0051030036050448608860240e11100511040420b194692400075814468130000014003d2800301e8242100c41580301007180d9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 165028057 1250 165026807 165026821
    0x6030f030406020d120b0d030906090b0f041a1606020d18050c04050c09100e090903090901181508010b0909071d0901090c080a0c06021b09091005070e09 67
    0x340554041c02c0056000080303802c602c0c074810780c12680303404d09105005c40d501124101050200d881208141e00242500c1801d1202c5c42e0041200f400a144070f1f031003103207404c0750082494090f00943c002c4602008401d0341070300b4104510700170303100c641080c00c12001140f0784d9450000001c3d81301400d80d12880b030030000010700741000c3c107020b070340c0c0c89030400050028002d003003003000f0040030014030848080100b0b00400c11143c80b281e800313880350540e41d1a041e2a03101010f0421000c180000c0c412201540300708410900b40d1600058241111418000142041003400707100d005004880c06d41190b0003040c5400188002e015007148120080076105401c10380c48501000d0340f500801e000f8080d14400d0a050381303080c02c0a1a1000754420a85400040c0b4941c6546e580c040c2c0000c00d502c000001d0703010f940d207141401183c0d19488000c04c0d4600060110101240144068000140d04184900380590005000d81d0042c4104c2c2194076a00c8810080d41c80c00b5400603022420f1100b80a00840100c0b00081075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 165029307 1250 165028057 165028063
    0x31206030201080430030207110306091e01020408100b102c04021c060303170702100207060905161701090c0b0a050d1a09071e051e0d020306030f 64
    0xa0326010303514034119a555440e40c411004004a03d11142d8025480306001d00389040c501c4005550182c0e00960744160718100b13004036100341c1d20114840d400c16020300400c09400200102100c0440c20148010712504003581d00a0182d6405141e003070080c402041c031001120784c49251401030444000c1c112020100c402ca580540440740007201c0318a1000c0b5030700901141401442da90402880545072848916101c41401180726860031001d0715100103104240c0c100303036a0520301c10205000d04040c94000c400030b503284091901c5020306c59000500700184600380d08031000180c0c100c0202c8008450f0010007024600c8070707201d1100b10b46681038406410110601580001d04c0e0001d4454a029040c2040101a51b101c044d40500b4800c8c2040300c1c0c140c0d91824047c179500310580c01410641c2607192000d004818200400f20340801442c0304100c50030b0540c4182c640c0e0320400500d0510345039004009440620204440e103e041c030302001c40c12542013003050b0021031107558103800b82d4109030064034007255 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 165030557 1250 165029307 165029309
    0x150804030c06180c080a050106060503041218080a03020718020f12131202010207020102100902011706061b06040c090b1804050c040e24130f0501020405041107031206 73
    0x400070307840a2401010501a802206040c548404840810081a51800708110059028103c07540150a2003028094280710b50002000c503030070010700c0d40c5030a940c1c14040611030a86030040c80800c40303c448107180142c40301405088003d007168646881400c01075950310310f603c5100c074000c28a5180f090032001a009071403c40001d4402c003824150001006440903c00a0002c0f05a030300e154051804280900e80945880c2d00c0d80d000169107014a0000a080c90018130312500c0d01c0e800d0003400360050740e2144241c0307a800120241c1c6a01c80e2142c07070014a640c454440307c20002a0302c090300140c84640490242d000d0351003240d401682ca50344144240507900041d04140d40641c00b9003103030101000c4070180c00c1d40b191040b03041da1400009000090200e13003050041422030f0b80f0404c1c00782c020b450071991005649901c00075400c0c40c0c1ca0080c0c00d40c02400043c200c000d10b40a501c050b68403c0081c2501a00c0c050a00200107000c003641802c81c1c0c0d040d5402049099000032445c610f148110700d400e2060308 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 165031807 1250 165030557 165030563
    0x507050105060a0f260307030504061706090c031e07030c1101090804061202070203070603020306120f28021534110d02100e10031a1c050d030501150804 67
    0x440254505176060141c01e20214003842c4000c1600740c0d007038881d00148000c01d031f11482a254251900c0c00d06030010000f01c04450310358541010b44061000b907984080b512903018806540150380e030b41e07940d100c01c203020b586194404810481d040c11b2181c22a0180c1000000c101c0c5a550b5060038014094a94280c1c0e00303502c405402980204002d01206210303100c00302111204800c05850640c030356002c2403800039564088030001c2d9000c02800010b04e4006a105080100350008002c12005811540c0c1c49186031b101154030003450407078006074003900c1c04103403001c160024010021307888510300c540300e150711169400754002c0b40c54a16050510302440d040140520b4580303004140c003003e80e00c6900d503429aa400d16440888a050540160b40d0042c900d582208943e40380e405a504083c2400b84500101d0542800d250902860384150262004000130b00a0104ca4182d10000748000640704c480750640c028045015605504200c150075800c828102c50004204000c08a10314004881c1050f043e5402 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 165033057 1250 165031807 165031829
    0x111f03200a0e2202030f0109020c0601060521010f1706010608060d08040e100609050109050310050408070f0305121b1e090d0302011b0503041e150207030507050105060a 74
    0x1845810b1045058107404000541440b0020341101e68003401003000d4a00710401c03e8000080016694440c10703075a0050134100b03415810326915003c4c19883c1c405c140902e00801002060305007840c2c0380243c0102031000f49100c04031065840e680c8441d4440c0b00d5005610020071451010650540000346e003504031041c07641c808807541c0f01c060402038110b000390700549010805100110342e15a480c1c180030700520960740020015841e1140140c80c441440d400507041c4510b180d030800050700e000c507200e50440f01c18240040d06a9451070000c085019130800a0310031020040705204054110009000c1000d4660380c94041344d55000c014402507046c003a4041203540b084c000500a05d81c60500a000070100710302041c1010421400b08006944442054006079181c1404100000411180c400910018540145945016264104800b402003a05102e403001e1007114400d00008800c209591104648155541c0400342002043e640010100f074038103518041c04220b40f071a114002604032a1a2006 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 165034307 1250 165033057 165033067
    0x40f060206010e013204020f040e1503060123130509070906090204060c0206090a08010e0309041d1c0c020406030b1e040506160c080301090912031e0207111f0320 71
    0x5a411917094101010380040c0c0034412000200f200401800242c0400001e1024070b2030940102901d150100a40398000e0b08003500602002e001d04100700001c000c0d017080c241c3c0408500f000f2581c00100b40380008803984c64107050052152006c01c0d01d0007181d003900070604c015902c50076000101e2289108000116120b00f60000060808001138041900c004000115041e070300c03083c1900b0b4610b03071055018581c10002d403405140c80d16210b14501081806607201c1551522400c0d00c0d507449200c01088500d109141c000c1c61810b1042c13212980060340034000b030102554a10b403541080c00151408005505a42802882200484c18461081e6008001400c045d2220202a415101103160300c03020081c0007120344000c103881d20010360091000007800138404c03c1c03e080c9102121181d83d20a4105410100ca0416145c200d8100c0c500245001c0070040c0e4405107807411100c01904010f44a408c1680a0403035240e90311241581e20782098252000e101c0c03415102c00400d0740301605200301e0325004080c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 165035557 1250 165034307 165034379
    0xc06040b0c132c060a031b0f060804020a081c031a060403050f0105090a030f12021902011407030c1707020a0f260a0c0b0c040f060206010e01 62
    0x455500101d021650358035080c00c520444034409100d4106903016294074280003221103e691001d121501810900f003624144440062a6035000d0301c0081c0a0b038280d500403951903840300340000000d00030050050801c0d0b42e2081e010b07000840071141a4400d80b02480f00046102d030114000341c3c9400942c0344100300403c0c142d01500103040e11840e064514007121034080c065120900144051400f0700010140341c0c040548590035548000c0024416401c402c40c0c0070300080e0400e42c0c0c5040840907003445444022404c1001c4000d028942e80c002c50025401c4506198680650044000301c0d03840c2007140c00c55850420580c2a5175074020040c002400800190085c41c8194139a1600616288155400c42030603072901a40c0301d0b0754141c10380e40f000030050010250001c009850141c44040c0700c006003043d061141c0035004900044001d40644c00340b03800035010401c604212030107030884036a110032013034030352368002e5903003209018000c240c80e060300c0049851070741c81c199596841b00c070711040505062307040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 165036807 1250 165035557 165035573
    0x8030a090c0506040807030b010b0c12030702031e0702090c0a020c060904090b0c030f060405010303080609040f05030c0106030b091209010c0c2412050c030a0b01020f0d03060e0a020c0604 82
    0x2400545144500540c0881d490381ca483c000c000400494000b44113031741c103509040d281030700180e108204410b010480400c84210101d84804550080400c2d03e4480c1c1d0b40002c240c1c114450b540d4427500c1415802c000c1c044242d061809400c2d458001d50f03030015103a4854251200d588955080a0050307805a640a449468410020900b0721000303070000c92190b025030341c3e44e100391034140c420180180c0b0110401904d140b0300700c51180e20240440c3c0a000f25495518050315040000d014036001d004990002010301c9074400445141950101c1120b644a000c4c4000c14000c2080340000c98807007481c4030200300d65402c0080d04003a0710035465001890150b020006403a60782c3c2e2481d0440e8101840000000c40c6107a000e01c12030000c00c8580702c03015080e16260010038030030031300e04e040034003924200034800e04000c0001031780d034000051480040d00e50040310060f407078202030760442d1001d0320070102c5501c003d83d815085002203445c202c264a506480310b002c00380aa0141201140c85036101d5800140402c0303242e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 165038057 1250 165036807 165036821
    0x60903110c22140901020408100c08041e0b070e0f0f131d0706031a04151806030f0c050a0605190f0e0310090302070504090b010b0a030b0307080d0e01080408030a 71
    0x40c4800680a0302c01141105000800c413900d14481e580030400304503156040c04030f0300403c0b02c620000c10508100c107001400c010406071006e0301d20a00209400850b104080041c1c0802b900712040c00340918040300d0040218030b807411414041c8c0c02d614003202d81e90818040070184207400800756000d490504801e44c0090048031045402d06044800c2da014403401031100d9800390181d0b036030200300d201000d07000c002054290809240200d2521962100030310007082040145c0e02c040c3e580e1600c0700c0300b101604000e0070302030f000540709048003144001000258051201222003d44031134052603500c007800d80782d5000c2d5202c042c1c0b10008443d82180303154441c0090000a02103414945191f4001c1d0b40424540b214404807520701c1591a42428141501080104002d10003140c3c14407041c141c40d82d0f511600d00040c0304058000074086500c000c070754001d41040d04005c1b0b0180c02c0f0760400e903a03000c15690f140d09403607000001c070b042c50320880fa041d441001c665229940003400145140c42e0031248000601136 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 165039307 1250 165038057 165038119
    0x9210f030f0405280203060f13021509060f0c010c020d1b0303060f061d0f030d0e03190c06030e060c030f04030915030c030501051801030201051c0504060903110c 71
    0x25080300f0300f131503903030038000300d40c0740c03800c02c410508044020b2050600e0110084d0550035928042c1c07007003020420000c007001c04030690590f40140400054003050f030b014040c1031b0344030382d200c0303404540000d10f50000005000c80d9a0390744000d21004404200036621003140e05020380c00110070085040806001c800d01400c42c40c0f103464001041551201000b140c03c100e030300404001054140c0030100c5402c120400c0e440f8801c02c5580d80b100c8403080c00041c3c0d0700c2c65800107240602c0780301e00304035900741d90500001454082d540f94200c0e1003640751500c289414100c1c0158000f0a103000520341c000100000d01910034600d00b80140c0c40c540b02c50380e2201c2d24407401402102080085100810941042c50000320444810380740481c542c20040400740c04e88005070802d5001d0134030b080b024030710001207466403030440f602802d005540e40c0d180214415034812110968542c070703090505002c200000c0780d10171814103001c0c0e69104040c0400061842d00c0c0c90744007060700d9100340341141082508100301002c88400f01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 165040557 1250 165039307 165039313
    0x2010c02160803120414060f0603160501080a1a10020f12030c0f07020301092001091d0c090d0501021903110304021011190605010e07090308120a02070b09210f030f0405 74
    0xa001d03581b151030424120f5491803548103803c10300c441c5003000c1015218400c0d03201e210800190034880001e0001200420741042240c452180d21980c80f01a400e14400f03c4010f0440d010109503841d01940c0c3d0800510b54185620800c071a922401d20204103907030040440c1c0a02d00d280244141e0264825080324600f40d90555039800140c0000d00404c03c010440b041031079054100d450b004002400141c0d0a80c48140c01e1481300e200c12010843c568040380d400b80028503450340321220480801c4445000d214002c11307542c400249203410580c541030021035550b550f681440b0910071503d1101050105070390080d003041c0b000c02da01d41c001340510b10040c44d01400364203c40c8078045003101e190104c1c0c0d40b102c090729195910001880180785001900303904c0142410311441451440e80c4001c0340344158214242c0141c011000b15401191640403200c1158100d05011428106107040ca501d500e000c0c403409008a0f204c2e100c220311ba48054061700c2e60503006840340c0d8103540e119004903105040080c03045500d40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 165041807 1250 165040557 165040583
    0x3041b08011d061b030a090501090c06020102040806060409030f082206020c0f0a0b0f0402030304030f03020303060f04110405010c1511030a0e0105041e0f050d02010c021608031204 79
    0x49800d11a03007070314114078941001031220b00c0c8440c506024001d41071589626241c0f40101d041354801c41100c5c1c00c480120000244c6c003129003003a900400c5a81d0b001454400e04d4080014010350540241050322004020340b04240c030741c2d004000c11540d02d985e004020071410103c0011042c05000180e078018086500d104a8003407400d0310746500607030f0303581c1101c403550301040c0305124181c10421080c43c500540000c0c00003804036107a4003600040182190054007a4000040c00c548060064400541d400a04201c25452600c0c020f500c0303420031100c50f4080c251035620742d801c2b072500d8018646502d0000b441d8a10b01030900b001100d5114150300c055983d402e003c103a2117001901c030f22032002051003040400d51207003004400c0c40705580c0c192031941403d80c10300c018400400e880c0300b080e100420218000e02500481d6183c40210048000b4001d8a0360213800404502143c042d0081c1082f8140c03a8255004e96400c00400050440140200000360b48180702845c2d02410520764242c2003400390034481114 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 165043057 1250 165041807 165041819
    0x1202010c0c0b04060203041a04060c080f0403121d010f050d020c0a020a09050f24041a04050708160503091e1005040501021b0607080a0b0f121c110303041b 68
    0x140c0c4280c1c001320050f440010100705210701d03e8104410140000e06403454035181a00040000c0c2c070f2401c014024040001c5c030800d6000100040794003d50748511003600070440004040c0070b101c2094080004000340ba40d41014540c0316480d407601200c1642c99090424600740b90701d2000303400041c0c181000f0305c603e24904000d65280c2d040f10000b00045880441c45103400690b080500c10050107152902c43d083c03240004602c0b80510000c1d09800586001a001001d001c1c8e82c0265441401110341180c6040180030015600001041c40784000303009140003000c80002c115154881201c0500264000403e540100902ca00c50200590280011203007601e020000040c2102d0301500c0403190b80e07600081021b03400581403480f1485d0110080030785018500340c040900b048500500028800307a66049800b03040d0f840186070701c80d0391000303800e8658905501d481c80740e41e0a0919120780040e04081d04682c901c0c1d100b0b00407181c4804081002d0340c1141c65039542e80100f00508001c441044100640120309 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 165044307 1250 165043057 165043079
    0x23070c020d080304060c02070f12081b010b030c15120c12010f0504060603141317040801050f06030d1b05070b030a0c230702010c05030904180308060108011202010c0c 73
    0x7003409110040e5480c1002d1a009044804080560096400c48581081460b400d03000000444642100c4841141c140345496034040c032880d01c0320300501b00c0780024003225010552001c2404e21080e800c50701900c0608081003940141e42d10b19801e51601007001031802c2c1d0190b500660003061b203c400364108010002001c0300c00350260401c0b001100b03041000c02c124505802640010071841c2020412041c01071104000020300600c058070900000c040311003040384860784101c0c1420147d46d00c0c2e171520b81314010310b8042d01d400d40d5000f141041d0800400d25034030f80031135803985d419040d4032005214145a00740c60710482600c202641c050280c8100081d030091540000c611440480000082c140c43d26500a0088555848001d05401d2080020b10340364034060201c0d600315409007020002e0b0096454581d2940c8580d088050b0810304085038000c0b145142c2115090440c425210444540d850400455144100348149448a005025103d0241d4010a0030803600d81c0610101401c058844c980f40314 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 165045557 1250 165044307 165044329
    0x60f09030109080a020d030c0c150513020a060504051302090a12050a0c120308162708010603030302030f1302130b120a2105030c040302040c02150408120a23070c02 72
    0xf40c0c000031b40f00403010794940309041c54045a400d1050080e10151100600d0b2100c4944007485c0d02e41d540041013565160b0346880c0c2c00c07207600400c1074801585906000300980c009110755409541a40145844880c2d54000d60b401c04ca8058844000c2c94900a801d0841ca0201d40040d906401000d04081c08035a0320040303240544000c95180d1a08012841d004058100040c04507040f031a5030255115640d81c842c07181c540d010b19080000458580520091989111651181c42e496280c14800001c050f05500514030070b00030500c1c0f0038841d6a4210344690710742c1301d55400035800440828040c1c3c442101d94050740c04103502801c484481d02001801501d412007655041e2103010b40d01c02c045604c9100c060107542051a130789001403e5091034031089c02c1c18015400001e1156403202c00008141e1310800c0791242c101500d640f82802c81c00c090500c3c03981584507907054504400e10700c0c00683d0222a40c05010f01c0407844008003d102c8454410307480204002403c0ca0040100766096540540d5407101005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 165046807 1250 165045557 165045577
    0x207141005221502030309100c0e0406030c090507021f0203040f02060d060806090307050601030b090a081902011419050a0e1b030d08010e0a053103090503010506060f0903010908 78
    0xa0155042c908480c210300220b10014007194401c0040107c00032001c6900c84034405504800709407549103000aa505442800406030014500003000090011940c490011188440010003103500d8800c42240c90b240b20a400c06010300301e25040d28066542036004540c041d015035040b01c0b50a1060f0300003180360b40070040d5007100740e49078003043c019410700b40040b1782c005060b80020741c0752940030355481d601c0741d005110180200c108503000511200c028440005a00d5018149550701d549910380010146a0103280320019031816440703412a414003494a400f071656103800c0c12142415280c040043c1500030540030b2556114120306648003010060b070350035081d20340003003c0168078201c103040c600a01c15180404002c1800300400920b40107030034940c3c004e00d440c640401d195860a42038403030500d407140035810700301c000074116402c0300700e14000c58000d0707100e51f4401c10005c4d07a980800d401d880c010307640c155115608006010a803414440100006480503002103030180700d0b602c50010b140c0103001c182c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 165048057 1250 165046807 165046867
    0x7121b0206010b180906030c120f07051e21030a020c15070201050906072f030f0c0906040c03110f0403120201050103030507020f190602010e0d0207141005 68
    0x80540150148030060240403241d85480c2052869500314805100682030180502d00c0500030403510703102440840107000f4003610240160256111169807454a0801d018090085560208942c46c6c00c00c00d041031103801800701e2688030226000c1000604045c894a08414006464000c00304000c1c4050300f080c4000e034000d009004503100500048100d041949120600c08201c12801070ba000f8003a034903a80300540320507413207136507502c1c0c28001e54181c84400d145c2060020031524071500440452042c01c00f00360240c400b000c41010324035650307018401610b0ba00c408100002003481c14180d019400c104160f103004240003820b600c6849241c0c2c8000340000e0428000074043c02441007e1042140d44982c91008000541c5075850040c0940900c4000a01c07030380003040c5041c0180d8074580d043c071583c0200c40182402940e03442d8060700030085051340c500f46005080c05883c0b154004103c2c00100c2d5076040740c00300e480b5040400c0184007403600d4280c0083c04030030b0141040c0d1003070750180007070410f07183c0c001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 165049307 1250 165048057 165048101
    0x2100f050702190c090b1302040305060105130203240102030409050a0905010c0804030807030f1407020c120a050a02040e210702010806040b01170c1b01020915030601050406080712 79
    0x2000b03043c9000c820044440c0d8200d1403034100024104040c0108549a44100044640c1002d000a10b5076010700c4c0510b10f030600200c1d001c82801030109985048503011559900c4180181e07004c41c06a0004854580f60100558500d0b0591041051040c28183c4144152031505880d00350b205d0803660191205105143d98142220803c802440780886c1d14080c0d0404005a01d801d54000702103401c014600d500f003689403100300c8800c403890f4018002405440d00226050b00e04030720300071b50740c0c48000e0380d0b1481500c0c001080d030143c00d03000ca0444082c43d003010141107000126000c0c04090104080070305294403803180e14400c00070488003262000c4800c1c0c18025615460350000400c4d0711009401d041c452031400a2400703a0742e8002d070003440c0e0504080740c4000f50740da401030766040760f000c0d0f1a603000c0101e0008ad100d5265038010350003080c0d600070071928000a20354200c112806408201c400a01042080100313101150180414650000030b902d09504030301a1040e615003034a080500036001e09400c0c920b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 165050557 1250 165049307 165049321
    0x1020c0619050c0d0f0b10080f0609010b090904020604150915021603030c020102010b100c02040f0902030c01050d09122001050601090b0c010216051e0a02090403030c02100f05 77
    0xd00148001005000b141020f003c0c4035014030030360700c19080f116130707812441d104600990001031030b000c0e0040a00f0a2400b203114041c20361442106c0d00f025510800001410500d00307100c105040e102c115804505150710041449954031021300141da2000381484001905182c100488604e420f140da81c0301045132500b0f03085485038088801d88002d54100d501c031003600d80c02c04043d0307004503a050f1400e00480d040a00050340101400c00031641c00a081412030b080c01d640181c032808141c0e00c03d4a0070000c010310310190108482521000951540001c0c0c2d40501c90b40c4031f080075148901140c5000500a1150381d03034018401303000514080454011000d6011101c0202107422004107158000d20261030080002000b0404034041d4000d042c00c00b0946080609096060340e400c44030f04400810805400d04045540d5100c40c100c2000c0c40d58205444100d0703190108076044040d6015000350216100c03607030103402400440e00e840b411072143e107907c1c03030480f0114060390710b00d6a5802000105030800ba0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 165051807 1250 165050557 165050581
    0x71403060a060501020606090a0f0501060203030709090203040c0e04051c0f03051302090c1803031b160b0906181801030506060a0803031f050a09140f06030a121101020c06 75
    0xd1070001042e142c10000c01143c0d03000720b010380e8813000440f121881aa200d40b00300c1e00030118481300d0320341030345407000100d58150008000d500890351034540c141c40a9442c5406016884100d400501007220100200401c1010050894000384640e041c0c60410020003151100b604d10241103400080841d40f604d500300c0e8141c4602900400300e0543d0b50b2034200319401103041e005000d0034000300c81c42c00160314808045a148241c070045001401e80303980702c07602c80780320110751418075040050f400384911000f620002090b9020448401002040c18011441c0c100403042c0c005070700d5084102c2a5501484095494140100c8604020340030001c2550660a00f1480c0800040c41e45004500303a00050249040c0001640d40c01011490210f4500343d204400401498043c0c3c0010b4004031100c0c030120706a195908802da1092070300309501c0144d511652440d010f01400e80701036426030002c80089002c100100c0800b1126800da00345498061000d000040c02ca0f840401b845001ea0040c6003030290840041d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 165053057 1250 165051807 165051811
    0x903040f120201020c01122d1b09030318121401110a1706180f0106031802151305150c010b1005030627100501021606020601050411040807140306 64
    0x49201c1c0d507403038003150b8000b035a01c070381e0381000780d05100c0850100070040c4000c0d0482c0541c1b03c1c10b4040601021310402e5500500d0007600c6d02c50780c0340c50600c0c2d0031120310303203000f6403400003004c141c0c2c0d54500452940c0c40c25a40c0c44021054000002d40c41480442d2100801c015100c0076032203180710142d5071031440c0b43c99003111000b00c504403500070300300250011140c0c80290316011a03000b407840b00041c2c4030000000ca4080b002e035013060000291034200074100b00b0070350140d4101c65440e14217000d013004082d1348054840078140003d61080d41e1514541589480c074002d0000080222060b01c416500c5000103a080c00b52480e40312030042002840290310a000c1c06009160802035411441404034464041c025002c010b06043c000c4040c035000e0280d043c04042501c0c0a0050101c08110700c3c20180700d10300480045007e52b5000d4454070000c01a0261070a501e4800c95885902400300f82c0d09100800002d0008000d044008110600020400742d0b42481240000c2090ba203205003480030003000d043c1007105c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 165054307 1250 165053057 165053069
    0x302040806011211220f02070605090319080105030304090c030f110a030f0603020a1406160f0c171c020c060408010c0801060c050604030e0103020f0a09081002070510020903070e0903040f 82
    0x1002d2103a40080c3c03d4004c03030b141d003408458800f24801b180c2941c074000070b00230741c03001030041070a0070b0600c411010040010040070103a60809028101051000c2d180c0c10b10038421a030f05507004200401c08116079910502c88491580340210f1019500010340c01034600d00c030490b00780c850300015000c0580e901840b0b00305940003900300c144142480d5400061504c441d511030300c100d44c119985c12022550b9032100703d4003240540d40b070744c0c0140070b4a420102d05118081c2411a0008400b00c40820b0300c00b6160381031600c0416a80c000c01245001108000341c2c2d800502d400e20551080d182c0d11025075903500c0240c405049030703a000060724448400c0080c003ca00681c00803042c4101119078101203130000c40c02e01e5201c1d4042c03c00031880d10780500100c000340b1510740780304400c4101080c0b41c405076501c034808004889009088882608802100c41c08910407018000c043d0343c040385550011036207a0300507001804005040c0c85001d80c5d80c001102a069007128110580d0300005410721546022680c90740c041d00c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 165055557 1250 165054307 165054319
    0x80a0b010509040c030b030a080c0d0804020f0409020109170f100c021e0a06050901051e092d010905030c010c020c01051c0e010c020d14090117070302040806011211 72
    0x5240060414407462030840d009513114210500202d0003504a01c0040ba0080e04403401c444070740c2070484060300a1000d8202c5402140924188a40325594590049400820b0a0134130720088007004010030a040701241803142c0d0080000310400e148030801c1b050044000904104600041064140703510b000f045260746240c05e00c0b5200b415400a0f907050703540910316520300a0561404414500980b442c0300420a03030030041003107404c08042d040203025084480c0407031a242e1a60480c440e240c80100c3d82041698000340b5004212a2800508040030401f00c00c0c20180602980c101400e4070011a000da42c07070f81c0000303005d0010440910564065102c02c0c406084040c0030303400001c0c014130a050a0030300144a003421004005c11581c09039500c081c050000b00180c0c2d00315070007e503c0e1700b8417441110215182c01e140301042e00c1d25404175000b41e04165540c5440c00d02d12050a5240c0c200541440300701642030001040d04c40702000303024041c3c084000180c3c44a8030501c2e03c200c40e54000120039000d01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 165056807 1250 165055557 165055571
    0x30409090302010f11120c0408061005040c0906080a021809040501061a07080f091c060b01020c0a120308041407030c14180f1b030a0213080304030506061c0506090d080a 74
    0x10113170b40c064552405000610364869260030800c070059000d00d800440c0240a5081441090303034082480707034203c4030705903030501400c0e68101c021343d0382c008503103d150042411840003503800e070519030042c6000e0010b03140c13050900326810042003803071034100d03012925070795620720601201103002c40c1100c0841c515071049150800b903a0b19800907004800064050441c0030907096915921404441e020031501040034030031003114140b40300a80261002c030780c00b40c060307140d80340c8a0f0f0a0518600c0c041e941d880c7d1400c5000e0003156812034803440000c200f9075240162100d00e018240d420f001041c0214001c4013110074090805501303078030905685502d580701da0021201210710442a0086a81c862200c0340d40d80c0170350f40c0e015030320706001921146140b0b64240c004204000c240c49940900403826199a00d441c040e5201d5500e0741d6244075600000e400391f400354000800c140381c101142d060312481e8492a14040e5200d66540b8507121041c0c8804022340c0003201c50b102c15580c890352640c2c1c44100340c00300f88094 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 165058057 1250 165056807 165056831
    0x15060509011a03070c082d0702030a0f020301200307080606031509070504050301360209010306090602040b0712030509010b150306030f0304150905090c030a1d030409090302010f 78
    0x1d0100c03407041442c1c0040800001c00312030061110034015031308150700c690754540089111081603090b500e04401c0300c8886038a02c2c180e580680580f40d003550301800405400110b9143d00c0d80f00c0144c071204980c9903490340a805617803200e103203c0004070106a40c1030350b12428100c1010740171600051046004220030f1040007501114000b034140451001e8032280031070307180d110044800c0d120703d0308261780541c20300380d04c181d8000c0340c134a6016201050207003200056041d845200d50030030719160060340c4070070b0f004018808921a94408141c070b511501006141030b13521540a03250f17030444072041d00e910490320080c42c55940c01d030003000da010202d14000c0003c4802c0000040b007440c03072911000c03003251020000501c1c54070304000480303501c00000222611503503a0f81c6196524a0f10320b210100041d040c600004050030101e6455004880240e41c290556441200e120000d14a0311041d100d6400c0c50307950307411aa10140010406006401800b0800c1c1685040c06030946802442440f4050718014800c0c0380 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 165059307 1250 165058057 165058079
    0x30a150209010306031b1d01080d110115060e0306060108101505091801080d0203030c0415031811040b032107020a03050706121a030601061110091506050901 69
    0x10210410005844403050740c0120000d00e401d0300b0040414410701c5024043c0f0b00b058034a1022250000071625241c40080121130301c5107000c0c0700f014501da12403a07026070900c3c024400240f55100a000000b0700381030075074042c4500c626a030b00c800e0106005000115003418107121342c44c0e01c01c1081c01d11607824107111044200c4103c0d030340b1038110b9407140003c6000f1403900c90800c40d00c1c00c1c00000e00882ca10b080713244035180c00750002e100d41e503c544100010f48000074008400d9a200d0340d0340450780c50901d8501480300d132460280d840100109030350340788141c400001d07001000000900960300ca541a6544e00d0500046483c42550726100394415010200d803000c44e0441441d0002c00008129111451840070402441c0107810040036400707a100d021913196440501d040d003201c2d040d40203000203078213211030000c4170790448040d6070140c00c20070050007801d014442081c03001c01e6070412151184829200b40707007240c040d0340b0100c0e551703070101100c10400070f1070740950400341c18111421070041d4504250044 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 165060557 1250 165059307 165059333
    0x280207110405060a091a030601063204170115060c020a030f0201050f0705010509060606120414070b0a02030705120a05030a0e1908091807020a03030911100c11030a 72
    0x1c415600d8800060503070b2600715140c0c00804140703509110140c21803d283ca01030010905007806846858000689144030b18040200c01d40b0740c1121144d1400483c0c10010030000d40f03009900a44810800050112402407458405135070402c00007d080c03461110342180060981d00c4101080352940080015941d050000c20403213520808200b4040c0480c40142c645024000103075940d02000326405052090640101d0711428000c010340d001507580c401004070728000d400b132110f01007070380a0020340000c5051040607002c4044400b01c5030340540d03500d0481901d6005c41000c2006800114064081041c02c11140c090481002010381c184158130380b00408901008004070441915454542c0e888202808490800100030018120140c81c074100f2448030740c0100e40c02da0140c0f400c42c5911451858904015000d82e103141e0190003461016102100900101d01c41540c40340807900300003400b541c600f4501f0a841440c0e0f00c070344150310401e0411040d00b01c440703000303140290400568000098520b0711104 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 165061807 1250 165060557 165060559
    0xc0e10030e011104030308010e0708280e071509050d0308060d0c090213030312050919021206090d0206180303071d09040303020c0705060909070c020d080328020711 72
    0xc0d981c094445203030b02605103210022045003000030044149075000c1f904a0590301604101da810361125002142d00c140b045852344920382026401220920707442c10924140211500c0102e0301e101c25010190409075182e021030720b116104800c4d102c429400042d5080100790880d400410000d103a103020f040410020041445a0a007040300e00c20005082000005000405011501c9086500035001400c0944c001940070440d0050005154141d40c01f5252007820804040e00036901d40c140042e28034009050101c3c2d120a040d01d90600140d001c2000c944102c0041008140d1030310480b401900300368020b45545c0c0c00e410600d24108441e800002220f82004240c900030710340074540c01e007026410030044607031948801c803002800141981a0094155840c1720710070741e0003644e9201c00300403583c491851441e0300f00119a000031041401450101161030010303101c11001110f039554518154000c4a03410000765005400c4c02c45104041c1680e000d0701c3e000d6900314035006940c1c4030061924021210a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 165063057 1250 165061807 165061811
    0xb0909030a03110418021b0d020c21030304061a09070c0308060406090510050310020a140903070302100513120305090904050106120609110f0109180902061b010c0e1003 74
    0x70003c07100500c04440050041021001580130495200400795100c005401407840c00c0e200050380740000412000c0404885400400e844110701c0140603049128100150b01c0b070111122000c1050410b1000b10703c40d92150000281c01850f41e1400ca043c88003030402603005540c0c42c4108101c080d00001080ba40d543c060418240c160b60b07060000d0080c10791a00a08042c0c5e08000c20f0020131103031040b2910a55400700d0590b0312107011404608102d0284003210000103900b6544107000070300ca07000030160f001e4050191100f0a4a940215100390040c40000001980004680e4801c501545606001c1c1003650b044044c0c002207a00c0042081c000d0000740c5121343c212502107801c02409510000c01444202c2c0207032544882810224024a01d00c001a03c0f00b0a4440c481c0c1280d10b1700c482682160320058650302240c81c200344000c20002804806901d00341ea5851404002d82d80d208094887d00c1c1400544615112880025600b91001140002c0520405c0b81c00c010316641d500c0801d4480d0715540ca80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 165064307 1250 165063057 165063071
    0x6030705030c070f030c0203150705090f041b09031403130b030a061a070b09070e0112050a0203030f09120705011e0201060f030305072604120305070b0108010f0b0909030a03 76
    0xb55600d10700c070750307a4000d2003121500000c108060304200d00c000e600b8000c03400c0d12500f824a080840360b00000b1200c00000030b40401c40c040131849c224105000078000079000140624200d20034203001860400030002003016400c0410400c8040098013944c4109a0090f50615800700c03004404000180180c02c1c00003404000900c42c0c810ba60700c5600242500010360500a0359041030718103581c00754000f40c580241d100d001074034400000414208441c680c0005a0f0030307038a02408548002194141203800707004000304a0302580d8200060000031348000022961303604000d0030007414070804400070185400540f01040180e820184003070040801181140201000380412070040855400041507058500000700a00d5481000f81c10661b1050409024144961800c2103454100d405400445038042000340082c0d003910704130741c0089100b07003000c0742410b10a81c0e0b83e4000307074000d8100003a16035544000c10001d48050281414008080d50700c0e0030f040c20210151516840713640e290b00141074850322 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 165065557 1250 165064307 165064321
    0x636090216050d0302041404140c0a09030c0e100504091709030c0306010803090a080609070303030903030209030d020a11010c020a030b1305060a06030b0f1e100f030602130b090603070503 82
    0x400ca07034859008043e1101a0f89100c400390003500306004060150002c07200034480c2d400e10b44260085120201d007060080d86e6980b6441003540d110f9804442048000440000001d07014020100038020b28442c0e200c1d280340c0340580500c281c82c154803c5218904104031100441e44ea08580f4161840403440380c0e648201c2c441c00b02c2d24020441c901c59400d4441c2200000d6450300c0400070f004528012107124406541d65515035076100001e03103410125800c1240c2c1000021300070f50240d500e00d4440d04001d400c1084400000c0d040402142881c00941c00180790441000040c004080c1412424201142c00c4649034000c91000612800018008800f031004102c902041140c80310601d0380c00703000c0b61641d01d850401400640340d1031104880d8440e09c500461031212039484414400c02031403462104000020340c1ca040d140c140540701c42d502020740000400c00780f200d918000b014500403078001d41c0e03c90100c203111014540c43c0c0d0200b050480144080c44060b9142d0044a0b040309880c03030020b48a4884031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 165066807 1250 165065557 165065587
    0xf0402010e10021b03070f0608091009050d0216060504170a1704170a030c020d0201170109060f05120a02100311130504050a11041215020406360902 65
    0xd4141d40c00803031072620444065001130b444180030080c01c3c90105520103201810340c0d4520a021312015010b845000740b00e11032154403460350100709a0f04448207013001a020760100c600d42007090b903068100b00c40c8526000d40400011030312600000443c107605240c000021f2490150380030341c160200803600d048000e510108908000741d604000240a05202c1c2800d21401d035101d41300741100d50f076480800322070300040841c0817681107400d032301c0c4c0b50404505642003250b018040d81040741406444400008103083c0a0841d50180520b01d100299640c1005041010298a54131061083c22060881c2d103910300085107119410381d040d201804003884607501030b4040e0144007001c61040700d0225900c0c10300074540d1602d000304c07003003034404004070740b5000c100c14103860302100c400407800e1040004008200b119501d5a40a41c000d41c001c11395000d0401485050740e2099114000041010180c1c0302a5840420001d207021510201e0f0400b03440441e20620401006201e80c0d150180e000ca80c00303030000c00b12 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 165068057 1250 165066807 165066827
    0x705070507081902130b03071202030a050a050c030f0a0c33050405040509010911060d0b061305010e0a030b04080a0309050d081005041e0203060d0f0c05010e04060e0f040201 76
    0x1c816500040d915841c03110a00c50502c00580c8a05443d14000b45c041d0028802d01c0402000540585902820180380219000940c41e080b40c05114407001c0700c0100d10140107030356149110304060801c21380304004240c60309d42c0c0d103501031200380c0085107568001620689410b0440302c14183c070400010f98006410400c0340e0400a0b07004100007082110442940000100700341e44007150200040e0301d90443c03a40c225a0040c500901d03107007258502040c0d524110000d450780240c41c201c042a20241d010206c2c0c071030780150b2080401415040d03014041340d82c00618941d1088020341d00012098915214400c0a000150018040c03140014444107103910a07000040301580003000c40381c00c01c8003081c0c02400f0781c40856211010740090507011646143c40c0c01404460b5903480c8001042c03820000c2074000940c80980a1507000024081c00381c0082d5048400c9035030340d4041e080e0030340403510300400034000400d071004051295162403802e0003244003ca91007900112880d0218100765a1840140d5a030a00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 165069307 1250 165068057 165068069
    0xc1704050a0c0303120c080606031f0503030f0403062f0a090f080f070605030603030d050a06050d0c1701091e14011104060201061a161e060507030b090f0705070507 72
    0x3403032008000d061708004c0001440303004e2103003000481c0080c1411039140e2829113551754801b030200f01080b41d00c0c4800003040e40d580e21140010507441d40da54000ba01d5584081a4540d000002080400a110b040d02c91400000d080c4c2a2101510458005000c43c2c45011030b0302c02c0d45e0440201e510a0594401d1070400d01800c45c3d01c48030780e841521032124031341e0380c03410030782c158003a220b10350002c1080c520480640307000311800740040d803e04000c45070600190030010b10300701c0030550342e490016071030303860460344100c0c0d50181c09210822800c0c400f4601c0741d2484203503050346a078188815880080c01c00815204e90401608508034030308120300d0f054842c0001001c460300e544d0708120a941c00901e0360070090007101c0c2c05400800440b66109603009484180140c0013a10034400c0c06500c500c060b80b140320329074103446554100890340d140030b1140028880c1d00c6045d104580d45100b00107000d80c151240c0005104101e4100b00285004140c00e0403401004003002c0804c540403911500300b210400c422005414 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 165070557 1250 165069307 165069323
    0x110a06090b06040513030f050a1b030f11060c090603040203010b10020c032407050c100c050901080105040b0d060c02190515100b1909050301020705060709090c1704050a 74
    0x5090150508100b618014031071440c21012442400310401e0744860b481c0e040c0c4460940d00c418134016911340d0009814032003480b0307800e0f07482281c10400c45400390324284a1303111901c1c2c08240e03680081c40030407180781c41d2400740c1c010000c0c41032141441003a12040e240c100c03402560b940d60340c40460f0242c2003030141e1a0b048958002c9001d015600803c011082420039401c0f500029140710f21581d42d0790080300700030b502c03490030fa000c01c0e1001c0c4501cbc010305205140301e0403114282e00c6550304000321204180208000355010640e44803070340e40001814010301c6c0c00c071000e105204192000a03160b01c20024000c0500d40d40b840b490071503500910004800070541303124201070010078288541c90f03070302e902942e1061100c05800a04625148810081a1280307031810505084500400140281108102100b40f10740e000000440d0b6400b4002040c4451154010300031034106160040e010b41c2107034002d8551241403040c2150887d0f8407223110380c66160701c0b80403841c15881d50705140b0b040c1103007840080c080c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 165071807 1250 165070557 165070571
    0x50d1410091101020304030b24031024080d0f0212180a050114070b06060906040b0903010501050307050102030a0503040c05120604120513030f1a0109150b0307050703110a06 76
    0xc01503102005203400742e802250b02150300001242c580c410303030000034400300c03280c3c010a1084845840000196806001e01c80303d42840c00c0000e46801c400705a80614542c60320708010031000130035010030783c055841000b10401410b210215840b000b081043c0000c000040004404052013003001c0603244080500452b41c40000c003034542a1340c14150300160151200c0b04000400c1c1d4828948a00c0041c035809445051145583e150100303004003038445940903c0601c5204015a00c0d0001440140744281c01c865440c0c0c0326178117150035560160701841c031070f030040f400030003031a6004403c862105540d441e2403680d9540e0340c81c2001400768103402c600d4006824050720030003a400029920b020b03900524010854000040c03088030070303200ba10040301140400d00c400b0400245215203200c50341e40b11360304a8400c0c0d0801d240481d0055400da1000703100030340b5802006090164540038030f01400700070104600d145400310015040d4401d0540003002c104111000c0720901c2424003000c0032041d07101c88180310f45 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 165073057 1250 165071807 165071833
    0xc0e0a06030b120601030f240c0c0515090601180e01020c0601030c270e0307060e06160c05031911070e070e09060d06020c01240e0702070609050d14 65
    0x510071255043e01640495020300c000c9000003c40504881c0e022241e002c9403259955a191540d60000d0f8000ea4040300d1003100060b45800e01070000c8860060341d8070810620301d41050351500241800000d01918644284010742c071000c20380781d040d60068265030900c182d000380c07803000901080714044115440481d0040c500701001c54120b040360301071302c107a042061b203551043c1e842c0b40a289182c040901116401041075403a504100704c40c0c041403080c0d034205209910740906444690101185a400c904104900f90700c020024805401091500040c0704040741d0362950f0f80d105170b68044540003224641182510700c034094640000da502c00913a011140c2e1218020350f01103090b10080e0210341000c42c0a8035a044c103001d40e5219103c0141000649441364441c88002c4d400841000c0f507554030f800081040942501c401c0f1040708900c121815100c1c50030400301d05405015150f80110340041d4010000c0c0356114101c05c003590000c036440161154213282c10701512130100c0c854480f43c06203131041e6000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 165074307 1250 165073057 165073061
    0x1f0206040816020a09240b18060d02070c0303031b17040c03150b03011a0102060a090611071410060501140901120c02030c0714031905010b0301091b1401120c0e0a0603 73
    0x51b03002504140c4201e405000643c1401542500801c2080a0f0910608241090104101e030b01013401500301c80c5080c004220301070590f03114850a90300394a42c6e20342017040683c94403400c0710541c038051681c650615803c0000b0100440399200074107844c01403003c40c0c01d101038510f00400031756000341550803604403184070748085c100000c1c03d140309503c1d24050442d800948a10300d03081660583c058065650345e40f040800a0040e0f98007070301c01d265520301c04501940904010481c15020361000c010304418100d007540b07031070b86804141034140d0401c02c0c1001240d0708010b801040c1400d28900b151034840140048402c807032100c440340707541801c1c51030300b55030700f80c0100050940320803100070340304141d454100855250b540c074039000c0e425030300c00740b40c1d0b840a04594448512540c80b035000480c940c02007400103030070b5481d010015100200060560540700590404050081181c0b000d0010400c26010010f061100004149a44030307440b00320740101d95101d10302401248070018243d5a0481c3c48260080c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 165075557 1250 165074307 165074321
    0xc100c060e03120712060314030903071403030a050a0e0301051602060604050c0d020a03110304030f080f0f0105012006010b0309120c100b0a080a030c021f0206040816020a09 76
    0x4240c1d1078005031003001070000c012075039079035548001a096522501c0c0c1c115101c2c000d003076400038a1540d0b101d000c00001c41888002e11141c504100458844801c03074101810803030349501860541031000c160321010348010050fa05800c2c03042c01c3c82d5880d000d0452058454102a0b184035505510304410003400c29001030040c00c00703101c140c0c00c403152556a00280b0086400549640310442024424203540d00c025400070241d00c0018030300400d0f00701c0078140482150f00182c45c114049003010318610040355000321500c3e40010004920074244c1441d031010341c000e10303060041c02e0404c40722210000080c0c2c1c800c2c01c260480340c048070403510103603917a03d641c0001e17810640303400b000f5004600c60140c19582100c02d4803180b01c41040034044140162081d0401415088100c40c0c0001203039400140c1804284a0740c14198042c1d19440324441480c81044250001c881031004810940b000222540750700080b110391003684042603d607160001c01c02803a0407440d942000754054109a400300703190429800c101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 165076807 1250 165075557 165075563
    0x90c0f1d060405040c031214040b030a05160903080306042705010c05070308150a0806010602060402131406120c0a0816050f030a080711060403061d03030601050403060e0c100c 77
    0xd4180e844010400081e2241a50b0240200c0300e808024004036500701c201001d8000141002106aa01c40c0840182900540c1c41100108004010003c10309020b000e05507000c00c80b965401080d84c8000005442c280481c0406000c08030084001000c2e030b240d56009100f400d0304441c88842280300c1c0980c00c2c0004c26020000c48480d400e06600312041401201a28074080d41603d8031407144d69071300031100e514041c0d8581258045110000080e2212040c00354901038507141d40a4a001c0c038040c018403c10040004110701030a00d091010980201080c030125001b840441d042a03008404d5500b80c0c0c904a0b006c001590711203001d80000400c440005103898110306c0042c84120030035500c00421000341103028030650075030030880070500040c080c80000d121107480740700101c11070180c09003c1540ca81090f0011107070659183c81c51007011600100c0340c10a0740001005601d1342c0f4080b8002040707809684001400326480b00c0c0d1036881c044080c8102202d074500585031040c81c4482540c000c5c52445031030710139 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 165078057 1250 165076807 165076859
    0x5060709050906130f09060c17060a141903120e09010503030f0313080705010c09060201050f2701020702090a0914030f07030f0c0b010312090504090c0603090c0f 71
    0xa2142004071002e4401e08004240c80c2980d0f0300e241030a00038040000550011359a40c0c101903000600d60b00c503a18210519030b41c2e100810602c90705020b40c0f01005001184214816a0200641c1400d020601480c56013070321400420702d4885015114071080750801024040e5046400540b59484144000d410320201e58003c0e0590780c4d81e06040d01d030301c00c808010f00451401c0002405034010710160743d40a520821109250202030b49845007101c210a1a42c40044e180c01000c1004580c24080d45030000300518443d091402c00c0c0e40404001c0126000e41541e680b11035180e2030202d0429030582e0925038024008212529050f1440340050001c0d05d000c031000c01406c20310f5220484008241c0301c6d050199078903c2e180000c6600d003030350b00741100b842100800c440420644c1c0060580e60751580214031900c1d83d85214183d418011b40f100c5e060f5046580200d20b010128404111401c10b000f04850381801c000030700e03280300d061000e00301186420840000f120200001501c503681501203ca1065038260303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 165079307 1250 165078057 165078059
    0x9010e09032505100c1404030503031512030307030504030e01020118022205090601081905030405010c020d06020a0e03060603160b030a060b07150f02311206020301030605090c030312060a1205060709 87
    0xb2142c0c1034087c502018019600900000f039032402c041014504815006080007099071283d58a1403030740e40100c90500010b9250002e110402d5002280850f4060b0240001d12901124441c02c68552142c400064130580351942e40c0821040303010460b6644414281c024045841d0030341f0f11968900c0d01307104d95101482408080c00100c1d10254481c111141c0c030501031464503140c40c1c011181c001c0b1811059038400b000040304000500d543c070090640f100740b41c1700c01401582c4403003014186078004000e180a03800014900bc0c000180508a40a41d4480480f0396282d840d40b580940040240c3c0d00a851030310b00000d080300c01d00000800a41c030900071080705003c079601d600050000e038041c1304921404801c880c0522140b42190742080701d00140e01940f4900d80c2c503034580b04c0b2040d8007945101078600b00e600000510512495000d070315401035054000b0070a0388400e60209643c2d00c9042c1c00c4490302240c04c004140345503070b501801401800c014040b0116200241000f98445805880080110b0741000c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 165080557 1250 165079307 165079337
    0x9140f0403120c03060b0d050402090a0b0f042c03190e010f051803030a0c170a0503190905120415080403120c03021204080909010e09032505100c 64
    0x195845140d2658515081d18105481c40000d0911944918141070b140c400204541c950303500903100d00300c080702c00415642024010701a481c4d4000d082150307031030308080342080503840308150b21194602c252000180c80d0014280425280e400c0b040440b90840800254220741358000003400441e0a02501c4110b00a100315090715020149130030907002c40c0344408500407045c024401f920320404c183ca40001c1328a2240c0c0000d0035070b0312225402e40810b0f44040280288042c80c0c412407840800c0a0507203151010f9000003402a00008144024001c2400544500c6030300e0b1f038101900940d800400c452000c100200c1d40403031500180624040051ba5010550440c1d114068060044d901510382420702041050100c01600398100b4910506030204810300b5040003923003160340720f54064241d464452600380100300c102e83c01a4403141c01c3c02010710511541810101c00c451110251510040d00d11208556100642c0848007010300a401140108070201481d81c014a0080f1b81d01d640c0d00c0720a5003165 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 165081807 1250 165080557 165080581
    0xd0c06021e120c10050c0307020106210609020607050f06190c0e100203040b040b0a021204030b010902130305010f050403031b140d11131a090607111203040914 70
    0x11041060701d0340071040c0d030300c411107001c8002d18541c0040c1054803030242c1191008410740c0d4007603c009644403800000c0143c815828030880000d0049002c2d654010000400006542e58403404090207081d9540c80c21400c41d55141d0844042c280d105054440780d21220301c030644c42e440d0840700e00003803da101c00900044100c0d803060700d00d505c440340c40b0303500c09181880034040c8071400340701420298401000003143c441c042c1809000200f000d1080c00d540c5095941000341407508032080c0080404040c4424000280903071601c605650031080f00580310700d5140c550030000c945560001e031455190100021440b5101c0c0c000a124a010340ca05000b5061035083c0d400d1456012141c80001a1903422a0941d84481c10024034407a03043c1c0030302040c202c0b0003001044060307114600702010103004590800450590000e400311007802c050420b400c012200000c42e0040c4684038009110001d505200225582c0b90003522200c0080c080460340c8840d155510340c00185203000e020341d0100082c40016064400f01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 165083057 1250 165081807 165081853
    0x4170d0e0f060a0e0402040f0b0904060816060c0305090402030a0e062508060d050f06070311070807110d060509150114210c0907032c06060d0c050d0c0602 68
    0x545258a0032000b800b0444d420b169a46496a120b9001c1000241450707021144201500142000176518981c03041000308940040d48841542d0300940c0c07042c0c1a01d103520741c1c900d00b210064103140d2000c0e205c81c0b50807200c0b0320910251030392240c0b000c018068194050303440481030030407113400c0700c00c01c3e160021040500d07128085c16109001030303442c0c4002c826209152060300070b90090b100f01801d0b00980c4d03400d801c061040d41300c03180950100302000b2100c2c0e4907000c1e00200c51540c01c940c034500702c040e4a81c06464403541e8000303803041c030541d044500d40b52101002d00780d006401c100100510306001c2d00003a290041a01e003801d0301e0a1440000c1103015a001d984010f420000b4042100400c1c05440740b210104140c0b5800c14600420424004035143c14500f144074044a9400144142e194034080040002951246985442d5012101454600000c60540052040301c0d802e030301c506149411100d00041c2d810035500b00e80c15200202c2041012034a82c810384003990203a465806200c0e0b551003d40c0e141c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 165084307 1250 165083057 165083059
    0x60307050d151b0e2d030307060e0309090106030605090a1a03010905010e150c090d020a03050303151002160e092404060518030f1b190201090501030908030a0e010204170d0e0f 77
    0x30140d50205c0c400e05040c0100f2121000c1d0541b401c1a501d034958104440485858106070b4200052020f000d10780008411302610032401d0800419040a0200711341b0100209000c810f076995114004581540780740c80101140010001d04c80e211441c905980038203049044156944500000c000391194441b01da1485205a282d4480c03e203c801420801961035124003682c00030203c0c01c2c0400452002d00045208510079203001406086410030f110003c0000d1031020119040210800756140d000000e803c102c649090b8144011340354860100d06014100d18000b01d4030b600196803501a060070f080b03e610440c004c590400541d520041034000740c1ca0f1174914149250010411100030035481409450010100e645629030740120802c10307450104403039900b4a004000407c14000c5680c441860f1000d00000c0c6400d1000007171035683c441c3c00d408064000300c60181c85201d004000c00b0b0940c1a00c0c0141601203000760b140012100c010345540040806500103103240c0e0701003090703080401044030400c170 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 165085557 1250 165084307 165084349
    0x8070f05090402090613030c1809021809070b0a170609010302150307120501080f06090d0f031d070e010f0506190e0d02030f070e090105060307050d151b0e 68
    0x5203900400c4025400f92240340d174000d0090011049100c0d00c00106d0000d1880b440c801c00c41e050808001e4508500503903181982076051080071001070300e0301d100380d101000c01000c2a0030390b40c03070b9140000c0c240550707500302c44104030380400c0703841c052640240c81c07010342003842106010948404081c00f540da00d0900004e504a8020f401e0510310000c2c00c0001c603800015480c0010485083c0010f842c01d0f03607000ea001104a134031900800010b0402030003030319005a040002010030a0103241c001e81007800c800945001e065443c1d140300146101c4409428803115801c0c16100241c1d00d4210032820484203001c0d9642400115501007040d0400800301c44101204001c00c000e000014102154000d0943c0b4000c0d400110791030414005072002c0101290341c0c072482002d001420700b090701c8100a91001040030310540c0c1484240025030b20040b4856007034903000d40e1106000001d41c140034814943c0165035054040c0391801e0b02000f10300c5c07003c030054a1061039542c0c03c0460205d008010842c4401d0094205100e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 165086807 1250 165085557 165085567
    0x18070203040b13090507090305060604050403140d060e131211030301090b120d020303010929010c140604050115060201021c0b040b150901090e07080406150e04050d08070f05 76
    0x1054400c0501500d80b0391683d900d10b0f00b911071415100ba541c1c165505d0000c00d900303000074400c00c40b081c01116400a4284c408200314613194030700030840d214040c20b14500364400034017144024903e41041c0080d052200e414040c43c01c1c25603050094401c034030410b81e800d80000403103507182d0f80324010380030b2400e4070540114203690a1407401c1000b0800840c0b03141c0d004190b00d08400a480c000e00101c440f11740742e43c028540700d40c58421950244c601d1140358464000c00313108000e0300d009000d00e001480841c203280804514130186407e216540c0d0901800c4c060b0f1003414100020010150040540b03403002034081c01010390744d50001e81c04c1c0c0c051030300090039000c0d010f00fa110300020550711107444400004c0c000b207204202140441c0020f40e14441d80485400c00043d007540958000c0b400c00020250039071a161036141c407060082803034801500040030386032940550908810085081400350102010703402903820715241a03580c900044001720701041c503a900007241280900d5030303003403215402d468541c604 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 165088057 1250 165086807 165086819
    0xa0b04020415030209090f06070302070c17030f0408030a09090c0503040f020f0d0303061e150c0309150509040c030605030703080306030708011b120c05120a060b0a030b1807020304 79
    0xc0c0401403002d000e00310b070030079000015a07509040307540140c5c0d400c00500046408401070341e0130406c0c000c00000505004005050000d90a20601012101308405051030006110314403070640c4204d0300709840500d00881d01141e82c042c04001026100b080351503200c1107e1342d0b4003058068403504000700020400501c0020045148001c110402d580b000b024040c1c40c1200c880064554036100000b540001d40d1441c06204460b1200c2c104000007040314008001145070002d01080090000c1d08242004242040e0208240c010600784001c2d0240c29149590741c8048840107001d070308401c640c9072040b410320104424440c081e11862044d980040c0c06459000e0441d194092150b1000d03040a4262141c4040000c0c0348a080c4991604080f4443ca865143d18007030500800702d60301000c040703800c02d1509031040c0340d09800c90f003200d1900d20b113111190351954414080078020006540582c4800342c000a00a04840e41036000e042e51200c103c030f80c404121803400b070810000b40122500d2016910410040c041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 165089307 1250 165088057 165088061
    0xf0902090102071503060807050f1f09050a060c05010b040b1302090303090406060201050610080702101a09070302040504150b03012d0e01050a09020a0e19051509030d020a0b040204 79
    0x640c85041c0100c4484030740d03030242d50311040c584114820009030745034400c2c046543c05100d94801003400326400700580c8003003400100d4480000e40b840110782c5031801640c00c054007940400d0000c05005011000d00350391880c0151490002c1c2d0000c44540d460143c441015291512a25103480c002500c1c1c400318580c1c18800030000e6000304c0d2203642c1403000303005009050381e440c01400d003d08025030002c5600d007000024072641c1c1d5620b0203220306020312081000300c003136400209007020741d03812003000c506249008020340c12000112071960304100720400300012280c158000703004a0700107440801c850082d4880b00d0442c1c1c50113001d41c1e6208003007000100700042c41382c0c0a1009035407511074015010b403d04000d42d040c5080c030b648800d5070026054010041380c58602002e400801034420709600c1c1c01c0720450014005000c1c500307131500c54000b80f4060110390b55402000406043c001e0300840d000201c18503200c0302500602d01c8140301788202c4610041403880806c0d01d1168640c00b031040582500c1d41c4d030170000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 165090557 1250 165089307 165089317
    0xc072f060d0216121b080a0c15090b010e100e060d020f0910050f0108060f010c051c020a0510020408030418020d18020103141003060e0f0d02070e070206010f0902 71
    0x100c640d020b010300400f160381940340c05285807094800c000c05603034180018005a2141e0301c8140130100b01c0c0f1554010412a00840d035100049103030809091080d860302101c0d501c20259082e024905d0000d01d007003045110301da50750503200d04640d50506a0f51f0000040c40c00004ca000b5842c4c81c092580100311903081100300d545e10644020a44603d060651020409940b4211000781c42241c0c07814042281c2e040003038101280e880280780100b92850f11601090030b035850003010134100960481e4101c00d02805100303501542c1c00092045120b05071102d0020765840c0d034101d041d40c0b14000c800c51480701003090701c03c035411194130f40d01031414070345000e50440c40e00c0b22040c0d40141c0150200f21450348405244954884018918020924280e950000604a41c0c0380c004088040c0407500500200300c641007804800c9941c030a5000c03400032001ea8103d81010112002038400307101c0c00300c40b10724007030300405d8040541c0c400d041e14410341e9480620499075141c084c45000121455048140000c00342600280 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 165091807 1250 165090557 165090577
    0x60f09050f07150305090f010e0714010504030f0201111f1a1806210723040506030c060c030909090a0209150904030e01020a12110d03020415050a020f03030c072f06 72
    0x203207070514011f203504c1c00e494000600c081d054029180904c032450030780004c001c9140c130070700e03200e400c050460780d401c0701400d510403020b410702880f0081100040c004018800300012846e598242e406560b00075440034100e152680314100e05c7e0340354122070905141c28a8038410f44210954144c0d51504000d10010000c1001c90b803401078114010044240d0003000403400901d40142a07150400d01880d450740d8025982140501c590300b0001408455600000d0503006100704407022645c46103400b030074602e5842100354440d0400511402c200342c450b07002c11030000042c002e543d6005103075160000e00c81c1c1003103140c0e03502c0d0788120b549010a0101e40700728042e2842102c10f004446590354180c50b850041c0c0c07050b083c15000615110000c140c1020280200c0f00c2d2442c65007015800c0070700b4042070a400801c3c040004040200100b00807040764401c11440f03140845001c20f07030350399051094001c0c4440c1c2c410b05040e980380f40b030440c441034603a450301940303000c0c00b0ba00c0c02442180d400703c00412019501c000044 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 165093057 1250 165091807 165091813
    0x6010608060d080a0203090f122d0703060504060b010804050d0503130b0f010303200312060a0e011707060903020f0d1b09020d061a030a0c020307060f09050f0715030509 74
    0xd10300041c1c20340000d080c042090f17001180ca81c071410381000a518240080c1c1c0d800345200c00c22280c0c034040000307406601c03051080d041b408000410049400b00c8003130101203074024401c038000081031002503806035000310f025000c14040070003034000640c2c4115081d0380090144e4406500c4140070ba00c218003458101390a049403003c1e6002d55100d112149905840c403007040a060b1b0f004000f016000007a0b000e802c44400141c0c01000d00308182140c5900032803042248049049000504996400724040b02170102240882015611802442031802c94070f20942d4141c854a00041400c6000d440808200c2e54014091800b04601c07500744050b4a44d110720498000450003c203c140341c0e0f40f2102c0d40d014004510006031655001c046000030740700e066100c030140e8402801c0c5008214104000c59034044014100442d054640e64802c03883c504c01d4150141c0320510304109841864a180c12991416024400b103c000100d080c400d1501d840300303842103069880113502a041414080d40206901010350341c15 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 165094307 1250 165093057 165093079
    0x30e06010e060f0a030b100e09120714010204060203040f090b06090d050f01050c0a02061501020a02010c080d060f0905070201050603101503080d05070f09120b0c1c0218010e030601060806 82
    0x4036405242c0c07600100d44070140641000200241582d20f1f100070706a5107039a00340c504040c5d820686541051840709410341c1c0024480c002e100c16110803040281c48000215907881d03884600039101c0c1c00c14061080180b100c18000503040e001c0d4020340c5010341000f0422803602a180041002d040c0c0b103190121902c0c0121078031056946402e110b054400c3c2c0d1402c1c649541d403264070740000e0400300020300e81440400550003103076050340d0001c0c0180d5a1a420300341000d402240782809031807030091500d803203880307030801c0030118922503442103090031a1980c01c01403040d9103900c0b00590980f403003250740640541c0b01000071105465690404040120900700e1102819100d44568038107520488180e01e80d542c42d0780130712291700c0c0e10948040845c03046242554001e41003280b0340d2900e02002c40090541c44c0300c4030202c2c0281442c00104e8042034003101400382040d60a1011401a4008002e110319100c03080c801c04140d94010540020380060080160030241c2c02c00b102510b080102400040c1c020031100ca03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 165095557 1250 165094307 165094309
    0x40f05100221040b0601050307110706030b010e1c0305030a020702041112060d03080a0c050f07030f09051509240c0616052802010b041e0507030e06010e060f 69
    0x1500104030034084096980c6010340d40c0c0d652402c00c0d4640c0302c40d402a5640400010070f903000b505582103a824a04030707683e9250044116103280405c19808198040c5113000a804d58043c2c0c0000542e510a03240c6088540404041191f581302c21841d40207281c80007441f1074002441140290352110640000500301803c2c3d03000b1038202c0d800020341d10b240c40b400186100c40b040031509882d60228046a011491108a50340200034600c080c2c100000541c0340c0115002882c0150b06484214000c2c10b0556102d44003810010168000e403a460004581700840105440c149809031910078800303501218070f01601c0f00207100a07940344000c0303030414015504800342c2c4d10b050080142900c410503402000c1c14184489500f40008943c4001424002d0400c9040c0101004654103d096440240546890307030034014160b01600c039505125611074613003004440912880300c0c000c000e000d03443c5810000d59071014410340441d018941350041a07400940100300c442042e0325007941c040000340607103c140344224 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 165096807 1250 165095557 165095563
    0x12060411041a0409180503040603051012050a020406090e0a030534062904020703020a021011060906010302060417010f02040e01080c010c26070206030a0209011107030201080a05040f05 81
    0x960701c441149400a000c02c0130300b0ba580a5605074104455013211124150f903201507a0784a107104100a240e104c1e40003030302654282580200801c01001410080c02c61894400d4641e0000b14040348202c0c1b4084003c5a2203480c0e100748100389100c01300404031a109602c040da01d42d04a2020241a03a2410f5610b10044a10341203c51011a200900c8842c4d108a464094240e84a03007103129282c0300c041819400ca05010031418022160a55006998582a0500300c3c00d0100d000400b942041041000016031a404072405c00c0b01d9240300280c510a495130540a03807600c000f031102941c00310040c0f20500c103a00302050b680040301c1d40b0600001e07250f1445e14880b07007660411780c8031640218040d0010441c0903406e200d014070458003480c0078818503503c1d40e19034040000020740403200025145207411000d10b007608032036040307400800554032480c11421440103548040b13205030005040241d4204200c4000070010180c039416101c0c1a400d5072070071464170007404018000da8542c0a4441c0c0c03407001c52014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 165098057 1250 165096807 165096839
    0x14010c020c030f010b03060c0d18211d1005041509090b0102060f180109050f0d0201181203110f0d061a1c0b030c0303030a050103030210021206041104 66
    0xa4000d0022041d2075010141010315068030100141d0500c1411001940c001c0b401c5540640d8070005c090320f401002d1810002020142c00b041020442c51007903909001000c0414034429609140c0350703000a020b114100d0b0b20b003125140c1200d07503012054150800d4500b8450650703142501c0e1601a04080c0e88000300841944110484008a51030340301c2400b20942c24026440c546030700b03000421860504a104a451210040003004c1d0b00c84010030110a0341b200f9004803000070780007000c40301c4280c0309621080c0c0fa000103150140c055031078200204118112924141c44003600012080444002d8407001d070064850b4101c1d09122280c01c00080c100002c00c000030b010074a0781e6110019000b428000b40d003041c041846500b000b60801841140a0000b14180031035a503d4001c9000c00c0080c05500441d02d8814012107442e414000401044000300720380e030115040b42c0c066030171a44108941006030303040340710b00032540307142d01107000024582c0c0c20a070300460012424881c445140a07602c0707030f40450210f15 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 165099307 1250 165098057 165098081
    0x6090303150b0d15051003090302030f0a03020c150103030203070b06030c100206041a10140a0e040b0406110f07060e0f06091b0f062b1104030b07080603191401 70
    0x8040b0307408008420303074070031009030140b82030008402d136007040300041203850390804000805031900e1000040610910903550358150006103640c468194140140207500407080003000703032145030f840d070b0410228bd0400714100c80d0150040d515001c6da0761144041141b009000c01e0300361080a844000c00c0d1108a21041100502da014004508292900c004100307890503a6114424000b4140540481d06002010848080c0b42e0030b024403000f000045030710700d4000e5001c0d00240007010100000c1c451a4000c0d2071041c2d00c240d404010598001c0c200f540c440c0510040301041c080280001c03400500250321800710205071a044520305120100030340c2c82c1403402c4510500c50f0300700700841c403136801015084143c1000d040740c0a030060a2904003042041c007510b284070b021003440c018551907034164004060301d400c8060030709101c58445424591421390003444100c1e800c90205001a0282d071180010350b01584005003d4214804800c0c081d40c124240c002069924904141402c8c0e9842070910800c2c00c1311071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 165100557 1250 165099307 165099329
    0x803040608040501200a110709020d0e0607140d0e0c15190203160803060d05070602160501031a060d0e01020d09050606190620011e0b0a030c030609030315 68
    0x19081c070785542968181d10706080c05c03148106851034607031054800e0751003890003842d00202848540706400d141c032070654010300f405440080c207115002c800b5005650711541031821510207031102d14089842107074100e00c6000e0030f001800350000c2c50100b60403a10002600d001140c01c004505000240d40c1511090348410700711001030071203808520500c174941d540c0d0f0140084c5003058203207000da029102001c0300080070031390f0000004081e6034500495210f4150040c084500072520780c0ba019549980881070100e00c0c00740614002000d610a0195140410441d40300c100301405074428091f40d40c100060700094980c445075001030120003403002c0e00401080003408142d041e041d050550800c400a05007074060b0908544110519010301d5070001111034030325103108085040e107040c0d0500c500b1008501345550900b0500c0b010f881d010258a00f511008840401201e89014200a4418182d01c4010700c04d0a078540c00b0000b16038150f1104123030b28000c0c04d02040b110503d0381041c40c0790030325410462103c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 165101807 1250 165100557 165100561
    0x604060f06091e0c0f0c020d020414070f1205091506010219081201080c0109151b0b09071415070804090510170a021c05010f020c010605040e03032e0803040608 70
    0x503219000380030000140341454140c0e03008071702000b03054100415000e401040a10f03c1d5804640300ca51140705600b6107854042c8090a103020020005004070442100240c08074075949003500c01031080c5401241c100e80285071840700100d050000400040081d07066005410203400040024100d00599920842042e40c0e20000d4180b07803c1f8581040c0c00407156580410802c41542c2d0700041000e0545855044913000202c02e1601220748001200c803a00c0351010031281d100401c85646485400380400a09580240740c442c000b0607501d046003042103501683d0f540309a41d209020000400645008030b21940c42d290321070b140380c7c00b660002c0d900d802250048410400200d91f107000180814880130300505129180390f00003c03104040f40700c5e01c50b90462285020f20400c2025030020520305200503056441e4164000b5143c001d00c07451003118002c5041c4078469020507004801c0386e1007090080d140301c010032000303013000000104400080040d40c2c590100400c0f00b05003000600700901190740c0e04507241c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 165103057 1250 165101807 165101861
    0xf060901020a0815010e0603090c180a0e1204060f0302040915050a060503090a0303050c070c08010e0d0306030b072a0f061b0905040f0204030b01141009080604060f0609 74
    0x203000f0040c8240304031240004481c59036039000c440c0300d100b00b10480322a602d903202c0444060a048600c40c2d00c0b544280d681d00010442018510f003a80304143c1f15200b08003030390341c078540c8a403144001c0000f150002001c00041c48070070700801409900c1046494018103040e21890f0801c1180e624229071082200802010442482d0601800c00078000d81c2c6403603410750030890304040d501c600001c030003400d0603165400a5101c0c4905400d81d40c41c941c00041264000da45c0302001802400a9503c0c51881d0040b80c80c41c4040ca4024041d20741140d90180b807451841e50342c06800c46107803d0540000c40c8141c01c922502c1003050320441030001d0540540d6446070100d40070310700001201d1450b1005074401c4102a07220300265082110241140c1058078085100022003400e04000e00c03454000030302d43c1180c3d2707002191490a4101c250507006068814400040c4c0007003081d40c816056115940781c1c2d50003040054002241d80c0c10072261240c04200204038a9250040700040d40c050219945100b0f0320000d14420b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 165104307 1250 165103057 165103067
    0x50105040c0b0c030901030207240c030c0201140f060a05091e0703060b0901080a1b031a010206010f060e04110408011506110a02010c05070b040608180c060403140f060901020a 77
    0x1c2c0103079007410345802a1801565107a02420380c0301c0d0706265022a04200b40103514840f11516a00200500541401c01e0300b8803000302550420040002d241c140c3c0403000ba40148a0f000aa1120400088255449400001c0c2c0c140c1c0040c08550004024000003c0584410440f00d005807000c10104c3d034211840300e8180740309107004000f40209401c00004100072180d00c0111003050b0020300e018002651050322010207050040c25441003980410070f4244210b0b4143e010125004030342c0d05e44042c450819004a940d02405c0c004d000c10506040000c2003501d0040096032034813003010340b020540610001016220ba040b03640003490a94481d4004a9030075400e80350040074194600308824181000c036a015034500140304024148500c1010304005c1c01000c2010380014100c41001503602c03034035008000c3c0a02c80c1600c0903d00010840e8800a6660f004140d14156000240c03655060031b02c0e586480d20003060040603900503000d0f0082441c1c080390113018451150341e12100142e80d80154010040c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 165105557 1250 165104307 165104309
    0x504080f0a03080f06030a080c030c060f100509130c060e01080f04120f02161508010918060c0e032d120409020721081006030905060604180f050105040c 67
    0x105603000301a000380029001403c0d90380101089203000d010382c0d1500080b038034080520070003a0025030042088541200300000800035405101f040e9001070301d50b070002d10310382c00701521411f03100001c50b0030900243c01d0030400c0784c0e480352190f40e01e503030726022545446c81c0d50340301500b010001641c41d586000315035800903c0d00750801000c180101e010325150300c0d40811320180041c840d003046104081c1000d4039100b042054200e500d519059041c0d19520b0451004882030022510086a800c43c000203002c8554403408103510103555040685000c40c1e903440c0003c002b080a000c00b0300042041065290303d00b00840207042030309100c2420007006514400c880029050030b840780c07075800548515451201c1c242035030211003100c040544c44418501e840e40d0101c410360b81d000a615030b001400805154081190744c0150304d8510b003220320f10b84400d0220155100c8180203049688488040341da981096030048035820079074a0700710352408175030b640c006803005412000e4820b80c1d1584203000501005010500c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 165106807 1250 165105557 165105583
    0x3110307030e090c09120f1c020a1712130308130c031211030d02030a0b060f160809040606080603010b010e0a0303111e1f020f09040509030d0507050408 67
    0x14104186a81c004000e855482c1c500350285610b180803d08110184003500d4241d400203100e80d0303041d58070b041e5490741c49148104840c10b51041d0010f840f10a0180d0400440344000c0758042c0c50264501d440c3c10748a40100c1da058940414200054920801c0c44140c280c0607035041650302c15800031500b0b0051500390b000c1d28848444051004000001c0c0e1032005e820110b0b0b6100301d2030307821008407a009030f80c10107411000c04058040042d0403484c40300c00307500962013945121070801425444030300f44080c60040000325202c44900304400c228258111203210040303441800081c0c03400d28080041000d40d2020713030107240407039040d50610400c2c3c9028010791003000d000f0701e8504440717941080040d5421895120107401c0c80803041501c2c0805406024101500f02c25032240031214102d007221a9039440140f003030740b01c80074000c0324800c55903c05008507000840d69001080c1012402401c000c02880060100700f058841040035040e00385550041ea17125200c0b81e00c850b6212840c201c100e0382810280381e101 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 165107913 1106 165106807 165106813
    0x5160b0d090f0b0907030b090a0c0501051b0d09030c0902130302011407020904030806040e01150b220311030f0304080a03050702040e0f01050a27020d03050f030a090311 74
    0x60003102e02ca075030220b4031581c422382a25151f04041c54000c2080c2d4402d02c0c108640d40c8510042c002404240c551075400e50440003805141132188848400840d40a00d01042400040e104001c0244611942507242a990b606043e24038030142c000241030215110f1516000803901c0d00342d8009660203441c824142c18075081c080c014160850b00305100f2420a100307401ca20406000354400302980701158600c0601380806002c190b000108990800e210081c01c00d524510a4052a4000c40c0904208101256840300341820070214502e03401c450b6100b0001008060741c0010600340c001d8041c50501d0300e0703402903c0000c01134407101c0107a040600c070b4500e40c3c03000e038401940128001c05001e6001c21180d640085561022a0508944250548451400c2d80036003080352880a0080c403e28040d07107400d9400d010303031056400c1601e0310452175a03101940d0080542009004821801103001 = true := by decide +kernel

theorem cover : BRFrame.Cov 164928057 165107913 := by
  have h0 := BRFrame.cov_init 164928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 164928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 164928057 ≤ n) (h2 : n < 165107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
