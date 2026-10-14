-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0890
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:29:14.113504+00:00
-- url     : https://prove2.me/submissions/2cfb244d-4cdf-4d63-9f19-9ca33994880b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 159892086 ≤ n < 160071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 159893336 1250 159892086 159892099
    0x105280902131d070f090f1e0e060901060e030129100c050309190527070203040803090d0f08040306020403030f05070308060909030f040803090a06020f030a0302030406060b0316030b 80
    0x40110100c143d078003018626044030490030385c400951303406489800403032041240c120f0204031b107032054408003100c902d000007010523240d840f098406481400c40700c8c940c02010050040115500441149131210401000862005142d01505000d00e15036807000c008800048503090b414180004605241c81840c50844100c40355900d17020b55038032480121902a42e4449105c9543c401031710104009094000c2c140c44c000060340c00c0d9052820020721084000090b0840858001c6000100300c030100c5148101442c1800c0c40382d42005500c0744100c0341510003a2083c90031100144040009001030b61041d8001038445007107086c0201040c4541d4001000d0240400a900100b5086480c96512040807180c05903155215a0700070b0a5025480701441c04a401150114950034040050420a941911040d200f10350381d0404076654584443c0c03003d00c5070010003140c5802e40c070a400440d88103006500101d000ca0303071a8640c403042e030300c1200c4034003404c0081074614401942c180502e003000c110031240c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 159894586 1250 159893336 159893369
    0x3191e02070b040e0a0f0903030f0e060717150409030909140105060f090d02060c010204051503010303051e04120f2901211401050103030206130506010528090213 71
    0x3010035442107028245600300c480b0f0009a40c403015400201e503006c5083c01c240711483d92440c01401808001c01c1e00e10348242030810420000100041552007511299211071813070000411000a18801501102800c96010032258540d11917010720401c41d8481e80c0d5052000e440d1500d05000c50301c01c0c207803c1c0c801074903200040101e42c0d25001a105601c024141442d60352980b200041d00d40e408402000350022008140d00c1038500040d8007a0080340e0080c2c8050540032492010522148024080180420010b005454242801070751103c044050340403442d14094948400343d0804108000031103401b00080a40d00030410480d40813012007941c1544510f440c3c0700103c40c0880b03202c05005449030202005100300400054603034091030b498011001c022001d07414105a4068602400f09078098070403400410000c2c544402c00e024101c5d040005040c0300c0e42484d00700000f1844d031659030143c865112050a5907500c65035005070003030410040041c0d607032044114900d0b1005080c1d0102800030080e405 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 159895836 1250 159894586 159894599
    0xc0e0907180e06070e03150a05060f0603010302100318140106031505100306050a180b090129010c03090816090615020601030803040c0b0d0f0b04090f0b040503191e0207 74
    0x9003e0b4100d0766908104064003d68404280f52081d418040c05604907500f040c01003000c0380340e04c03d5000704803d03500444024418424880d0b58442840000d4010080c4001c81c02054825800141590100d0244580800068540c401d03040040000002d0696407441c04200300a008050071740e2003040b62070244024a05180071440c812014800a0309407503c80f00040e1444031284c4c8580400b10040321092003000c490300304401802c0040f82e065407503600c0d00804540c5801d44500e00001d106000d8800542c03885120011510241030351700447c00d00c0102400418100310134088006c07481443e18884094900d8000c2d410107803002c03a03202c402d80d80d1a540c0380c985200d6001c240d40341941e403c1034a940ea00e03103d9151050b11244203074004118228082420750008440741c016911884d03a410050051205260800c4125820044004c0400c91070030b907008009403640c040d10754854000c0064906096145400f003d0301e000f40c4060800051650043d210340c0601c050300c0e8581303035072544003c054007800d040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 159897086 1250 159895836 159895843
    0x306010f0914010f1107080f07050a0f03061104091107120807090303081305010606020303162d03090804120309091103130807051005060f101b0c0e0907180e 69
    0x8400e9810040740b0540c000059001e4140c240d5170045070401c41e40386981d210101a118030000e0084080d0b4010810001103d1510f56400c0b0305807222004030031120b07407a40e922900109607131b0081044030310080c080012000d00394031411100510441ca402c2d5070351598604698a02170401c08001400300150503c036800e5440003841041e40d50505180000d43c81f0b0440d00485407184940042c035a40c20881c0104007a0b42c00300c055270003800c09003014a04e0351807480054404c81400c6213400042c50303180b8841c07285002000c841c10102c1c2c82c282800909400da503200c1e0581c6500603007100040c034402c03440e0941010780c440760250041c0700d9030700200700c8200110342c2c0d80794a100203400442004415805141031140450231501100d90000440e01c80c0703400000b03001c0180000300c0d00b440c400e2009080c20750882c02e01e00c2d01081c42100980c0d801001801001c9200c040c407503507110681b1b240b003040c04040b03114a0303207210141c081d000160062014a1600c0e4801440808040366580d0365401d20380d10340d0440f400003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 159898336 1250 159897086 159897119
    0xf09010c08070e041401032d0302030f03040201050912030a02071e05010e011b050c040e0a02010e011d0303040e06030f070303080708062d010f0311030a0f090f05030306010f09 77
    0xc0c40c140346004000030016015281d50301c0c3c0717801c07516251000081008085035900e403080540ba0b0303c0c08510400040d680b04080c001b8003000d030240e04200030800114520a000759401803050403c54206a031030000b00d41070008510340e01000b9440040d81500b603e404112040081c25041c03441c203143c0500c0000e09052502500c200c0c1d06000c0e002c2c40c0709409a01070703403800700031340c03a45540050440f41074203086584406e841d0400d4000c601e041d580d44d03504003000c503110000a40603107800b40a8900800111b5007400b07842d10681f080140180f1f440203030b64050005000401000b0070848580c10540c08260400152035001c41e00c0b0b601161003000001d81003040c0748d501c8121400c081d125a81c40c0400304003007141d2018a04c4030f0704501c03240401011181e49021810302c03c00e030b80740c001303000b22100258112210b041d001102e02000b400000c00003041604502420b40008a0105001700180c0d01c9401c3c1b981d10b0801200d603070700301004116995900c5901121403c1151910040e114078101c510110302c4481d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 159899586 1250 159898336 159898351
    0x501090513020f0705060a0b09010e040b0a0e0102040b03220b01060c05121204170406051c0f05070801030308100f0608040507030b160206150105191e03050f09010c08 73
    0x1c1881c0d0110069060307050f25101a95903504564a41840c07400c19154401101d0010400d850304416410a060090880b41669009039008403191141d443c0c25140c084c00410000c0810740320490010800b80030300103800144410b04000d512802c054110007801e4052207650030540d0b08116040e004103a020340d10300d0454009040002901c62203081031418240c2d00038030440304d0000061405002c03d84001c81c0c074440c034068180f4900c201100300e004200380c0b144e0300c228000110107104041d0a11200a181c940d02e021909000554880d451013000030759200300c8802021540d000010810f05400c0403131194401c000031010034103d8209540050f10051138000d020401c802d00c40043c0402008010110145400c0765a0750041c1c50101100c08448411289550050140102103159224203914003040400140c44160400740480703051720341c6480705070b8010b0030045145840181d4a00c0074000c10400310441d03a01150074903000ca0301001c5148050101d050030307071400318038008580e4400116600b0054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 159900836 1250 159899586 159899599
    0x506070f080304080405010e01031b03110c060405010b10030b01230912010b031608120a020a0b070201050601110a0209060108090a140606010207080f031c060801090c050a08010605010905 82
    0x1906028150210354603006005600000a00c0103026981010f40200e803426031382d6a948004c40c000440c1900c200c04032828003085401041100c45002c0d82009960300c0c01e501c3c00c68146094189500d03e800819102910965945e0021039541d0520600d48d244a0440741400e00081c070301034000806054414a54200d10b02032252801c1c000e40c40001204d4103d05c004010090302040114428002c00d801441d01d48070344280e1126030494040034004104440ca1a4040c0040a030355444001180d48000300d0001103000c0c20300c01c1400100403203038050254410354000207841c64400000350404040885600d40740c3d0141881d030f4010b0341c4401405501034428a0440466100c2100c807a1500c2c2da5110020903444492030809d0100782d001030614804c9400360f08446107550349881031510b96800d0301c0e020a25400c00c0081d001c2c108420440c4036024404103400054540d40c0351142400c40700c5550040f180e0050814041101e490308110030009410100b008012180c03509002a02c2140c02d8850f00d4003482 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 159902086 1250 159900836 159900847
    0x50a110a0e07090b0f0705101422022103040303030e0c010c120e0609100206060901120218150405180f0313050f04060807061106010803250c05120102120603060403090506 75
    0x102d4000984001b03541c8881129600c520100c500030240c800c21060301e88040310f50303000075003409400e0200706080240d1500c001c40041d55800f4005114000b00c5080f6490400400d81e80d084d004c01c0005000130760080c0c7e00020707688828806e1a04102101026604200a8600f108081440d6038035009089120382010b0b000100d40c8800308600f40600300c1410341c4480d461911448060f00841e0107442140c0848050180b6a219030900321311000e07640d8003035045255614000311602c0784000068018a40500c2283d540340c3d002c000405a0780101c49800fa0300b824000c0d0701e030b40b041080101c403070000304000165040101c015503003402ca0f2582d1148030f11841c040c40d480c088980303c1e03a0082c03000e41110010f0710901a250750380179040034845820031100c3c0c401c442c000556680c01000ba61810f2500090902e4072014240407030340c1000d40100151141440300f800000e07ea500c0c2c02411204120100016072034402e075a00f103480d0014001c003018081c0d04004100300c0001e52240550060fa24119041034944 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 159903336 1250 159902086 159902107
    0x503060f0a05030106090606030e070e010e07030f0204030c150e0102060c07031103030a0603120305040c17030c06160e01020105060315040510021314010c11100507050a110a0e07090b 80
    0x30205622480c3c25520300344000c036100e0300540180c01030300c80c980c80c240b044003011400380f03030384c6c0c110391007240f42034030a000060101900d000c1e0030580110051801207008001604842d00302c1e070040c1e0044403109c4801c0000c2282d2641541609000415070408011440b0040f00103074540c80c000303080303484140000420104040c0507944070b07420700c01258112911b80ca0040070700c000503c81404140c4100c0c00300c112405080c0c2c441e0003134a2155901c01014404146000d4600c1d03020481000c16884900007031044c0c40e00f01c0420402a0b2041c8d02c2031140c990b034901815005485610403c090301d045904003020404562000504030351003a018031440030301691281403903818410002425007000740001074400e41c1c00301d004540810340b01070105041c4103554640041d65401c08015008180203040044041c3c149481d00c08401e00c1521401d2080c5061140c0d540c00342041d0460708200c4104002c1703100300015003081015400500b41c0040119190b0034460f8001d0001c40c0c0314403132405caa1100042d00c0701390 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 159904586 1250 159903336 159903349
    0x105070c210b01080618030f0901030f140f040b0603010605031209010302071406070207090b030d0311040b04180f050103030c150b090c12091c050d1128050306010503060f 75
    0x50b03800200b16425035840321601034032200240c0d00d044061410600c4490711020100c1200d211000b554909490008040b005401500b20b0304120507003280d0750005501900301c0aa15103104200d0764000070303000d1809103080150040050310881c000e07071500d03005100c682c60001e021080c0300030411102d078030b44d820000100c1c040d00c102540182404121240c40c5207030342000500a0003046543c082d28141519034100da011500c0301292194190f010400c00c200c1d0b0b9009a11031030fa0f2000400010345016103a13004200e035944640c1c8917584000c18150000c2044150388251804109009001d00c02545540c8006201000811707020b4840310501005a07203e00c850b5000102e4110090402051032410301c2001015401c01c40c5000b40c0080020b000407442d00011070001c3c3c0503212084804070200c120f08046559400c0b03000621215540c030724108010040040140a20705002036100003154030158850b408114000307104018480b00340144032441e070b00a82a00c2e481003040d40c0b22032500c1c1076000003a88 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 159905836 1250 159904586 159904649
    0x60702040213061e1704110d120e0310050c09060f04091107020102010b0d0309060f120501090902010915090b03152805060301030c09200d0204030b060105070c 70
    0x210708031250000500340741c0184c1101d0406850104404034004003950070790b196034210400c5103090404400042c00147c040b40d04c000590005000f4079826003440d55a143d0120520780c1050224421340010380192804014650b81502e600405025509026000c43d185001e41e4207000d03c503450119980705900074050503500107008410091002030480040c02c1c42d60750196509038019403d0114a0500382412050a400203034941d80f4004c1451514004403405110118210104200030f802e0001c1054540603140c040c00c911000002c40030242d1001419401207588400c50710b49003020803801c0560401c1546c803c03102d0030140b11f40da9564258404800b100f8080da0380e075000e481000642c02d880c131013801004160482c0c842582c52a51a030041007003c3c002444000c0c0101c58a80050000030f44030380183c0344003100c582c0b010140c2c8042045688141c1c1040070400141540071a0030010710040d6051941c00000c01e0030158a8581d56495524141005000310f01205128494024015064540c40740 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 159907086 1250 159905836 159905857
    0x306261c0c0c0b09040e01020901021c030f09120f0f050319140f041407081002090406030206071208101233060e0106050a0c120207030f1b080f0304050607020402 71
    0x101c0b03a0700e81c41864807a8110b02050b030b000f54648580b0681e000814401c40703071003a105800918845400340c210101e519038082086041680320500d60b2100d2005000c0c880b1454420f80503601040740c2040010000c100c160544000c1207004200061707000e407c4000c50f60065003401018801d414512241c10141c4603800601ca01e0000c01e104011600c07501040301130040784190384402201114032030b9655200301a0141c0740103a001050b5641c880c0c0d4855000303100c40840500302141550f078a80001d0481d42141d0400e55800d00c00b00d10302e104855010511345e0b400410180d403003032882d0070a04ca100c1281100c43c4003d20103048808840c40809026032107070010b50b18040f40d85c021510142003032014040b54860707100f54018850000c076409024000340c0d2400d8503541c1d500a405199034a403103507659a0400b00100703600a001c00803010030340000d5100d54450058407002c000701c102160b12400c440d0190b0101002c2c0d049030b8081440d401c1d012003102d0881c1d0080360030948400c07203400020000e02c209000c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 159908336 1250 159907086 159907103
    0x3040315020304020a052202220e04050607140f1804110c0105100605091903300806151b0d0c050d05070b0a020a1803030306261c0c 58
    0x31944080d190000c500c290b10954000400700c0c0c1d10024440b891012907484040b100c000c80c064000305c20940e000e400290960140040c8184900c40b42c90600b9005422881045c0c5510040100380081081116040b200c64501600c408a8940400c6410b008040480040d0840003c400351602103d04682c110150001c100f00404a00001c4000c059400b0a840fa1040c0d402d090000e2000c240c0410700400302ea0351034485600e85005001080b5a15409594038182416600c00110100d0042e0141211540340b01da603195880c0d0443c50b11410700326903142c248003080b41d50301c01c101944e114541c103234030043c0306400c802d6103803d07451500801c6a064003146480340e01c40c1d0300c62080711560200b20180e15a005005407a92072201070422a102d2041440c060560351140000c610011550381c000d10380325506240c8080c0c4840500c0042d142c0700741550090740040e0302c1d11400e20080500e411040404441d5900342403080030000c0004d40c1f0342101d0000d20510805a00309904814028005c0490195105210 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 159909586 1250 159908336 159908363
    0x4030215040f05250915120c0b130504050108010c0f0e0307120516150e0d03050d02070b0f09011e0b120307050d0e0604030302061603020c0708010906050f060d0f0302030403 76
    0x145202c07106031031a00c00c041d03044c010000780c4100b942c440d4110802c4c140349070250060521032500380e05482e02c9012a284003042e40d0000b484654040680302e9000c148050804452600c400c0005454060300804442d9140000c240d120700e4011250070844544c0b4101001480b288a00080c02e05129601c420510030303240c2d4a940c100100403c0b038203410300c0040d07080156241c448082d079461110f2039620b400849e004a040d86202d1911920220013280320385009440c3c0008101082d0a1341c020740001c444845c0c9117014440003020302603003a41d00001c030308020000d0030b64100050038030003440c070015500c20713513070744101181c0303454080c510740312030744510116941c03040c0b03d14009944190300c4003841c1c0001d0416601005a2400b0720454007229050b074002c000325111804d1011030026100049030905600708002d07400d01d0818400c440081000500000d45c114050030000240d8a004041181440c90707001008105d80d18020228261604200032400e050224a0b06a286200300d800203000390500c80b04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 159910836 1250 159909586 159909613
    0x1320d060e070e0103020105120406110403150f0203060d0b10050d030f02010c08060a210c0612050a06050303070803040f0c1401120c09060c0813060302120f04030215040f05 76
    0x8100035072040c01088801d41c0c1d64503042c0d204190000e000081c0001c8040103a90021600c11240c140c0040c0642d0000a038500c9601c400c2e14250700640c402c42d004039804041c088100420320442c80002902a410341c03951400c000010183c46003020000c1c045002c05001c543c0300034100305d0950141c200036000d003d2031243c9040c083c2424406860140044d0b0910b401a41d120b0322400007a0300805001e82008801d50401c980950410780842480e1242c071600341c140e40100340c50003a902c0040c8000d071641003510035082100e5080d10001008000c2c1541405000c001c903071000800c8a00c1d0503040b00c003103070b2252928907000103050030070a000740540c0318411010881c0b0b4520703010301c8000780e801d0322603510003d5010707540c000395402080b080c0081500b80408128150040d03607940c04245c0300e03500142c0742c00e044c107080138a113040c80d40103040003035404980710448055080e82503401c52222200e110140c80c0c00d54000b1358911f02815086d00e080c554401003410403142001a201250303104058035030034012140c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 159912086 1250 159910836 159910841
    0x70309150c0908070f030f020d020d0c0e090f070f0302010e011803060b040506120a14070b070b01051504140f01031803020f06060a03050a110105070506090610090501320d06 76
    0x901102030042d500000b820861544445c4112903000c000d80e000c22406400b0400e44901044003640c21000b206d0380d0800040140300d41d00050800000b80b480355060030440c5514180320300d405108590302031241440f03c00a00d00c2807808595091034183c921607019001200e0618003041a6080422045d101100b088210340044180801c00c3d6010030080d961001003148070441c1401d801d84603008480014017264910b081103140901200444401a94074149103d19902188041d01c50fa080d11005028900d002201420741c4074140d40c5080c10942403070611000c4014005810b40305241c170040070069030b4004d07009901580d0748840c840080380c0312400c0203074603514250740014140c000e03100091140d2500745000301c1601e8011000b018221255910440d0398504d00b4a410b0501206000060000e0000c00c02207110b802890040c02c52410210030f001c41a865640005000c2800d140040c0315001d80c940d0f08041c021034422110141c2040d4000891070540c1c2c0e1070050382c11818240b400000d202898 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 159913336 1250 159912086 159912089
    0x3030b030f030c0607211a030d03150e0420010e040c050c06060123090d1202480d0b070c0b0a0207020a06050705030c06160f0206010e070309150c09 65
    0x1d0060711629517504500f02d4481c1c50a280b41541104146003684c1180703c5603102180e4004200c143d50400d0380750a000a18010350400c0440c0025221603000013540c1d41c081461000300300307090f17041403141000d41d202040301a181c400c40e8007138641e048409045031311640746a10031400c041c0040002c4110040000c00d40c3d40002100c3c5401d200ea0800724100b544115000001c0c0c142c0c614a4055900d55101510426801030745013a5000c00ca5100c98008102c0c901c40c0b54132040610340080140f00c600200c1c0e02c80b107052000c42045004650144e22190344240340c1c140131124410742e118000030800100203041e641032828050501d005070010005516009000741e50000d0259046082c3e65843c030f01340300168441c41000a42000c21207004004440c0507038081c1494a101c2d90689091100400c4094601241200c198291000c641000c0c1c89160f04403040000345169880a02145d41c105141300b80321040140205e002c06903140740c600305105010010b006c80d0fa480c0e00b020b0002e6810444000d0070a141c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 159914586 1250 159913336 159913357
    0x7180612050708040c1401090b19090b03150d02120106090e010f0645020703120903141e040e06040605030a0f020f0d02040203040f032a060903030b030f03 68
    0x7044041006240910400b03442644d00c41c80c82e24200e42403052900001d800d9048440c1802560600443c082c1e41d00000740014035050203a070640e04842040c000c02070030459003c0c4135220410010301c11300c0041020320450541041c5d1b03007070b01004428804114200c907005514181c40d46007980c00b280c22003154000350210110341000b40505c0c0f80061008040302c4080c03117240d0b0101c5076a05c40510203e0420003585008c80d54489298140c2c051b5800c800d130001c0120000c0c403007198001924010141c012404c0404259560742c20003001c0540e0354060002c1c083c88480c18441800800d80f14800940d06510024480c06140d103035454030b40e01c01d14032002d40700680c0e00034820f9040003c00701e00c03400c0015000361071a07004281480e0b5032500d03400b0301c0358000b1500100b0360020740c10760342940541c50f180000c0d0f001e07611859103d029100f040c103008024200f03900517003036049440c0040d651218064800d0070f102503045400050b90041918017035009025040324140c0502607020080e0146401101400d14442c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 159915836 1250 159914586 159914591
    0x603020907050a02060f0a090804030b04060f05040f020f03011d0601080f030a020d05030910050f041a0601020d1404090501080a05010c020c130c03111b0705090103170307180612 78
    0x1501c20301500d0390f0054000b2440113034400710004040384282040c094101c2141400010b0126654941c1520b80c2d00540050314414040e100340020801c1901c249180ea0b02d83c6001006030303081541d1980580011320a01034441c0d11802d06507500c0b40d80a43c012250b2840542c1104884940d00c1c04550300c65409105003000d030700405600441030f24010041306c5040d11030394040d001a0900003020354140c1c0000d002c1856034406d039204905119110b100c0d0f40d00983c0c2103080c00c038683c82d0030700d49240102c00c4107645682c90300300407050ac04a640c0001d01518908114203107039100081010300000a030043d0707409413850754208000000e4402022600d031025900510007800991301d1510280e966101c17850100c2d8000381064410b00d88080315900050716900325150215800c1015a1102e6403904030240d0095440940080725800e80c0c0100404801031106603040700c281d61450b02c40116410003c240b11074050800000590100e20982d82c032140c00005003c40a49243c032600c0040494111a10300103038580b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 159917086 1250 159915836 159915841
    0x50114010815011a0714070306050a0219170a0b041e09031205010e0f06060c01050709090b03070f0e280504060c2d0201110d0c030c0804030c023106030209 68
    0x15400412081c0d140c0c074414a01d8603001d85e036901c5075040c1d407200103008110301401d4030200c00100740b400b076180100015000540c031843e1400f15038005410301c4410074284420700a00540b806440d005183e40724004000c00a601c0802802040c050402d40f0030301e400d6421002072141c1030321025407100074518003d035220760508964441e002c040724400e004840f203821402c00040c0c510401b0140145c1d0080000d1729650a10032020301403030945c0c0c81aa1240d01107401e204080c03007112864496000c0e2000110000e240a51401043c482045220301458614400031030004204402c2c030000714000e500d00b2030418130a00d003415429401040706403802ca500d030b82090848030119103d284000346100005507004861142d8038001c210607400c00740504255500d03640707069046001400030300011030000c41e01145800c403d40c002412111400000418408442d0070f000c0861b9005100702655a81982d0b2a1466008440c201c81034401c50f07a8039a580c05d800300d8003005c0115168005800b1a4820b541501498 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 159918336 1250 159917086 159917099
    0x20c060112050613060b03012904140f040203031c0606030f050601020c010e0103061a0306030709052e0e010308280e010c061d0f0714011b05011401081501 68
    0x2030041d2030010b48a50f0203000030616a2020041c1e00076010700c114000120301c08400c0110b400c3d11090400394050b103549100a95081e108000b5203101d0354002c54007080944507500302c01100e9400030780451210b0000c40c0004046460800407210b8121004441101021400001c0070103010f01d03006140001e410242c001c6103400c0140516030107400d05030060403081c0070640044a1703100c090128281015118035001603850f1015400750342e40d009903c174243c0c2e2460034a05051414115078032150001740b501e01000442810400070708440c1040c0d01d42400000390072416408000c0c000e40141d5a5012888000070802c03071000c000b050324032001800d4040485014400460440c100010b0002007940c400d8075507007079031190301000c102510640b40080d8050b044003070744400e03d029404100060703008503400c40c01200c00700000c02c002c000c4080d0440c4030b4117445000901102c0301d1400ca4002114000a00d41003080c00c0d0040e10b40c1c0da421040c4401d05603550400942c0d911a207510301c203007a00d6103000101d04c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 159919586 1250 159918336 159918359
    0x9010b0301081c0f180906120b1806130302121209010b030705100309051009030f1205010b040306021809040804061b0b01030809060409092006090901031106070510020c0601 76
    0x10103a25290041c4003004c0b404152400c80070b0410491012041032800700c1e40041ca403041001609400c929264150410b103800411740d0f0f0040c00500031030065030190342c5034400c0025469405410b0307813120b080500d41d030301d010b0346400a2001c034800c0440300071506a200c0d1a264a003144500c1a020080c4160045da1083c140c0b20225400340c07580000081c140580318502980007904900e02ca44115540b4120b01e000c1c0c001203c20f00e410031070002c4c1c1c10b8a1000301141e07101804980c1c45440050401c06035145c08075080ea584503e05c001000c158001c103803900c40400c0304000351740101022f091103510346064648082b641d07100f0f0007440b02150f0758030312940031a0500c4203d03100543d40400e00013040e03421a15403100540189001603808042040701042d0215940190107803980715130341d0240e044803640c800018800c002001140900d40a106c8201c0070381d01c004550741188d0b0050001c02601450001164142c1b08100c8094442e1042619071200c1c10901d0307009107074607455001075401990300c0c1c0022261 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 159920836 1250 159919586 159919633
    0xa0213090b0a05091204140a08031303060c03090203161a090604050d08160b0a27030f02120a02031c05060112050a02090a080d0306051005160f0209010b030108 70
    0x1044100c030700158440080f42d01054100544074222030b07500304034503250441507225420401c001c03404e0030000c0019041103004038018000c014081c41c10105c4148803407111612a10028014580fa402c0d0b00284030f000c0d502c681c00c445d0700682039640c60a6951b1115220050610548166440f624801d0b8195481d50b01920094500207000398541458a0b08000a24144032019107182404200170a04d65038002c80c080b6100c1d11800000045d4078108442d0022941511a81074041c0003da81003514852640c1030021082d038035003440803001f004200100c0c6800502c0d20780da0b10480d800217625682c5a0004098072058400c00000c0e00603600419608050300e10944400e80032440a1102c00c04031201c0380c01c010f602c01d1103041c0046c10301c2d00020000d0b040c00c0c256030016100341c2210180b400c4203549030181001400d003e8500d10200010910014250b11540c041c0f410407020103560b11040004200301d5004071600186085c03c2541c45401006c1c80750300c2031040c00361902c108250059005280313508a03c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 159922086 1250 159920836 159920843
    0x80a0c03120c0906080c0c070807030302070807060909020d0b0307060309060b040e0c061e030115030c09031e02010c022707090b0409110910020607030b040b0906060c0a08030103050a021309 83
    0x1120140f03413440c251030742c0364003400c844401ca20512803008107880411085004004100080003418514200682840050b800460441d0450442402450f40184198049078407a00005075240990a07210300140803050700c05626004154000448540c160441d058070b070f020b51307400c201c0c0f002a4410001190300284c0c040145402c080100d0f10a07107020400751075410018440c5041c0c2071203c44449041e5403098104029600700b1405070140f0943c144510507203540c850911400d074038119107070510f886568440480b01e80030305809000840e445281e6489400e035000c0c0c049504884100c0e0f44000000c000c11080c1d850101000c0006c042034131400040044a4010304004e260030b040607450400350200880d1500410410401c241543d01c42c1c07912100c62900542c0500a50709003034000400740c03441003000301d100e071b0b04281103052150740d1040190713000801110743c266200000e5a06c6400c2200c0c001014000d81004400001800790106d044110548201c500380c07000402540c3e0780049500145019 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 159923336 1250 159922086 159922097
    0x50406050a1e21141303020f01060b1902030c070306020f040b04030b090c220c0c140a0b0604060609090b01090314071409070c02040507020f0a05030d0509010905060f13080a0c03120c 80
    0x903201304d0070050709103465000e03205482030424401c207122709684503030b030200d44a504001100c82e03140030751750301003400d40035144003440c60310614410343d0350344281a002c007400312540003d005040320034003000c5070700405500340c0c00d54550756242040401400d044600e00b0003802284100c800a261100c0342c010081c2880501e41c005111442007800140102541f00050203141441000850144c46000c04000b040d68010010481b2a1500ca02d01003400782640c1d00541c00d002d010321285810441c010705413200e850000502180241c0121010001c42d44054020342e0545541e00e0084008110b09065a01d00c2005e165907081500501c03a2282c8200c2e41400040c4a07500315800624050f00034070b80002c05031040351381c8c84d0025901282002d101e2603088500361700002c2c0c140881c05040c00358a0340041140d00802c104115915019203485000b88407001c525035580c0041c01c8601c040c1c021000c2941c0221415071030750541305004c0d01d0300c0c0381c2c0c4c50164081072002c0f9441100e48200d009000701e641155940 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 159924586 1250 159923336 159923341
    0x1b0a0c0e090718020904021c06090501120212011d070311060f0708090d05160303090e06030d0807030219090915030507060c0302010f090f12050a050406050a1e2114 72
    0x18441c003241e2001e8036115a5400b04913031704070759885001a240400b0050b6016140d162810a88002c950840d4455840c840c00c201c010080d24a04c0341c07072180003903010340d10100d0041a44403200c0c0100908148101220b203400000c002d612800a001307010380b0b06c00c0c03103d180d108050341e04004044c010b8824440c481c100c10041d0030000755145000e0f080e4444054601103010f11a65900c031300b08441c40400084558513075404005165109424100078180a0031192407401c1140c00709480b02c8406104605006070b40000c178042034801d40c115002e604035582c01d8101400c240000402984c941e11031801c945082080d1800c008500203c03c0049039841030092151510340f400945900c18012070990544d5030303540d0b10302c400c1d0b5901c2c000c0f8404039204000100c00b03c0101d02d004c207c000e0000d141202007000501c511105190010111b900303454141c201251121580d0340c08070b81100e00003022100c1c000c281d04040c14541e4000f071742c0100e054004460701d02c100082c44030280403954105001d01e00c00428001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 159925836 1250 159924586 159924599
    0x9030506090303010509040821070527091512060a0504150c0e0f0301020906031f06050a0228050f0f060a09020105040b03060409050a0f0203061006080f06061b0a0c0e0907 75
    0xc009027510000045107200031461901c01440e82210035a000c240009925081d999200403110340401d1144d266006414424010070003001d4001c2c0002d4408a0100c500006a80d0301c0811031080e00c1000101c80142c40d101d0080c078041c0009480c111a00b28120020750a2400345000e85001c141044d40c80c1e4201c070b42c4140410185551210486815541c00c105541903a120b04006600c21010200c5440d401d4415041c0100350b0045640a00200700781401452005d81c1d000c00c0040094480d0340d0440855286001401d0840040701d500612030720502245d60760a0601090001016002505403811355403481c8184050368140300000380016000c1009001c0d02c0d002c0001340d50016005000058621255940d00380380107140401a2440e440424980d0118501008031aa02030300036002015541d19108001c0c02205000d04080617081c00d0600094141d100c5001f6a04c03c44c0520008000400300d0244076611191441c1e82590342048100b00403420102c001c003880d0141030820b000b459000d14045 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 159927086 1250 159925836 159925853
    0x806160302040f090b10210905070914070e010f090e0a0f0903020601150e0d020603060103090c140102061f051201110a03050a0e120307030b030a120903050609030301050904 76
    0x25040061503402e02011822550001c03c1c003015110301c42c2c00081d0004100e08010720002034540b44000c0007008084070301c2c0004562074812050b801600003103181480c83c80c0950520200340c0104820b03030300e840007500c0007080301e45265001d030314203489036011100c001c3d004580035040100f40b0700c0458070040d42000429540811540d120f800040b000482408040c03000b0180c0b20303502030640042e44010010b000c0701034880d03d480d22503101030900c543c2c03c1da0300394080b43c6040710011010380704440120001d40240d0090700501c40d200d80c088152100740e40c070740b003680c400c509400d035011380144521000580c0e03007004401c00b1004111047c03c80c80b07596181034200040702904140840080d502c0304002e603c007116240c082c00d1408500e0300d0100c1d0790720302089410304851031540c2072001036201e0a81d100809030300108980e004030003850085000fa220030042840c014107900000c03d0803041580c07102c0c0880d0b02030780038425a88600300743c0d611740e16400100c40e600e000c280203040d4020f0340103010800040088 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 159928336 1250 159927086 159927121
    0x10e0f1c05030d06031406190e010f050108030406020c010c05030d0504020604180f0507170714210a1b090501120603050f0a050d0c050601120c030203030307050703090509010806 78
    0x90819a1000d181a07680340e0460b081003010091070b6840300d5003402000201501c0140c0c901540c00100400d207841300c035001403004205160b401650307503094059500b000070341122100d00c01d90744040c0b1103943c0d507214a599070390081c490000140141c441454140d0700c689900600302d90000000c506000c0c0b4960f00500600000d04126070140c8204000201c10314050020305222001290009189001c008100c0075074400500420400180100045e140d180e150101c5400070750a01d0985020401d010303400c00c09200c1c1c0120a82d4030400c80560004106103024903501c00c0d03103400340034000054144a00c0c1901c1d918207081c0404910b1410003803010754401c10300241c29410b106804201705030b0b00e8944505114030b003508287d050700007110346003d00000300074014803030b003151038088000c984940b185600c80c4410300440744500000c400d03c10034800d41d400100003458000741a284d49080019010702281d101031421004201084800125480c2440d6102d0484582d400a841c8540d1071303c003118400400b1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 159929586 1250 159928336 159928369
    0x20a030e03010c3e0c1903050307060e0111070602040305010c0311031b0720190f0e0405010213080619050105090606031e1801051501020a12021005070c11010e0f 71
    0x2107089200560305504c1211520310741406040700721649000c1c800e035950501364002807509548001c1000a10001c1140c01711a04508001440581600502e0240c0302c03104110381c4106012900c0010b0162940c0103008491040008105940341424283c041e07134240c04052420381c07001c0c000501c4100358001c41048650749200e88905d04996640d50361211910540040325100c5c02000700b00d11420310302e8581d45104000300d90703100c9032868110545000d1840e400b8840c0351041020220b81045000d40680d41c06481c8a11404101c41c0c446100c1a6070340011101c3c0800514250850714040801380706180c1a2100600301034080d80e2011f080c070000380c1c00030b0241120450742121050200c1c0c42d07003400300d0040c0f1880d900e41581221207a080360035100040e00080da507a0440d81e0f8040c00380e070002248140b0942c00300c09100c0020700f0440c11790400006401d426400c600b08410000707415030001d140401c06106805c5044006010801100c0791105040301c0b035041403001504000501d4041c00d002c0308c1440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 159930836 1250 159929586 159929657
    0x6040b030406090b1008150c041518150f0c020a0e04030c020d0305030702010b09091b031002030a051006020a0302070e0603100603050105071106191515020a030e03010c 74
    0x461360340e000403142c00c55644040c0741c0700c014180103102042c008180c01310b504104280d03c5040ca03540c00e0038140305501ca4030081c60349035a142c10301302d8001c6603c40d8010400e4440c813801c0b1a95031455140c3c56050340202c00c00600303680c5a508060340a20054610640c01400c1004042d0424505020110001d041076050088030b240e0178005a6962104c040c103d882691450b480e0700348150088d0940c2c581305001882000c000c0300b001246000001c2d0800c4000006900c07001e18407100000ca41840440800001094000000c115111610350011401000f84c509051030311540d82d14200e0f110890304200900580001d901004200c0c29050394603003000740181515055031461a9800440b05558130449031a511a001c0014460f040031000c4d401e00d2654000d06081c0c64240d442c6466401c80300c0d081034040f540c032540381c0c0a00c07103242240c501070006440f982030300700748080700030b03542d0454241e080b0001000721201c2c260505040c0074024450029480e03c04c00380e0303020301000c09580748011400c141e080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 159932086 1250 159930836 159930851
    0x8040b0c1b030c160f1206090218040606030201090e01031a1b1314040203090d11070e0f04150b0310180203070605070501050906070804020103090201170702010f14010506040b030406 80
    0x11000d0000b801980d07450f000078114800302405880d50b9801543c460400f019809804101500303840001d410070b11b5003d900001d0200003271000410425000c012a0340041c0305804210804c141c0d9800f05060301e0003601c41501c5281d4440e1909254942400000c0c09210480d0205040e10b9440300000c0c1c010704682d020381084030100140320a507410030b03407101d0308645c2c0b03000040003200c40c036645188000030f0a540039441d51421403030156907121001464010420301d118120302e205400e000d501d0180860000c0341109040c91284000c22540940302911082c0e01c1d00903610381540c4e2480b41952036400a4054007040c42e031036944400414205600d01815520740708510700503941805141c004d41100c0d201e0f10303100d29003400c01508580000b00703148080c1c0d100c0418041e0315600710319616032282d0709180100707600f11a4030040340c000245241c001a541e8042c0c040c4217440c1e806400c074801c0c45420f40001c0203030f018001451880c5c081700b8401c15821a0003004180f08500300c1100031584640542c0700840d00c2c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 159933336 1250 159932086 159932137
    0x60e040809040b03070506130608090703030203090910050405040609020f0103060501080601050f190305010305070b0906090f060c0d35040f0812010b310509150607050c0102070608040b0c 82
    0x40d405040f0b2343c0ba003096090010302107160010140354200e607900307004241d0103003160340180d520b1040303003860351040029000103400112800b000780068440030f0002d0080f41007518014020f0030903440100d00c502629001c820395944a031040204a40c0141c1d6188071503101e040055915910680d00d0411403441085002030203030131003240070b8001c415590300103810f6245091880c2040c4150304031211240d030411920400da51000300703039051400c003214079041d40301003100064000e100d4504202102d02500c9007032009207030411102543d1041d81c442009012840542c4d000040300c2030321201408010081c040b4010980440717820746d145204030000c900d0310300d92821400720504c01b45d010040411000459080758029003100d211194075001d1290305001c4030045040144da0341340542401004d5034030009010b036200000582001e403014250a95030b008508095460704151a510707070142c0f094800008a840c440c90000344641c1e0005845c00300c80e1180f4200380f60a074040c14100102e611081141d00d4074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 159934586 1250 159933336 159933349
    0x161a0402032805010e07081603050304090216051605040501080f060c070507030506010f0602070b03060603070c03140406030506090919031115070f020609031903020904110f0409060e040809040b030705 88
    0x14803000340007444050325087c10301d840e20a1b60004130300c5000b000241040040c900005842c1a110000405601e4540820f0916001d0300300d420003420320f21460781e41c0400840352003048400d640040ea410301c0700d40c0e00c400d922070782c0d41c81a074007000850744034100190250780014007400140e44240203680500e035403510388034038102d420b03000b0070800a1002c10030061150108420700050803216007081c114a040b00018140340001481c580c18450030000d203804041c482c2543d4a0000000c0040300d0700e45031520b100400074001101e00502551142d03002c40c0119100249010104001c0c0300ca011600711196002c85d00c00f01200312110080c407418080d000c080980a8200d8032403800c40d500d041250311340700380003464000c000c2c00510f5150005c20034001c103820207045168039149141805a5a4500800820020071101c2c4840024441c0490003004a1059100520807504c03501800d20000b61030b0105042c81d0700d400c1d02c0040c01c1ca40c0800007101541000d0b0014603210398000c05031a40541d032140403070311 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 159935836 1250 159934586 159934601
    0x3020a0b0c0d0c0308010e0702010603060204081e0109020607021302040509131101090302010203091014030c0c070807060c060903030f050c03071d0d0620161a040203280501 76
    0xd819002148201d8264420070041c4070a1606191480103005030381c60242c20700c8418040c409800a0010014800c03e000b50001e100965000d8411982c8694520800341c0f1000a69080c4181c0540182c040c0c0d4569014095080f0103a00280250b1501100d903007005002044100603407029502070100203810343c0e40250652155038051401410b000c25403a1072050000082101414401510005e00241c0da0010650b0041e10003079601b030b68050600401a00c50480400a03949100d500102f00190608440d000e01812801d844c12a062652119400b9880e69103a020307850015005141e1540402c1e510f8110f040c080b03009040001c1c0500606d07502405441044440342e02c03c0c5000420701040f240c0c0110b04002d4080c442ca046095400442e001648243e00c20201400710380e1940d8110b20340c81e10405904801000c0b5040c1581d0f513200000340c1244d042041c0c02c059600401640813480c9a80c0c40c83c00c1b0f00e104603070007005003070001c00040344401c2400b41d04003800030400c00403000d000000d07001d2141c0322 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 159937086 1250 159935836 159935849
    0x20703170313050601260102030f0105042712021c02120702060705010504140c271e0403031506050405030a26070b061c0b01031106191701140d060f020403020a 70
    0x8003101d540115520f5450020f0a801c4c1180c8c2c8100108046030145903802810369604540204601002e450b0184030041d103c4185111101e6030b81c002001c1001d088541011b0412503001e40b0582c0100c0107000b0b03403503c0c01841d4240540c01c1441c0c01c801c12442e450081a500740b00411460a0820544400342110030480f1b0403902c2d1a180c064243c444003082040d00440c1604a0b06000001c088000311303615080c4a5410700130a242031004a10425500003004850406010818100d46081d0400070043c000035904045441d0001101161840c440c0c17080b90f041e103c3c00340092070818032580d180c25404a034443c078016440c0310040344003c8094104014841c2038044c05c0e2030706441c20b28404001008040c1512016070408187e003440004050b07010303060440c3e4004c0400c428251804000c54460702c500d1155040150664240e0b08203c1d801c03841500292902c80d00b1a4503583e01d82502d03a0101c0c00c0c03c03454a071b10108456810000408540040f04240070302400035081658950100b0707601c01c1c0ba138000301c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 159938336 1250 159937086 159937109
    0x10609020d0525020d0c0212030a05030f01090902090408030403020705040e010c020705060a140a0314070309060c08071d0406050a150f0e0a0501030207080c07090b0f01020703170313050601 83
    0xc1100846006840844404101d0341030302c115401002e981c41940c044003c4c144190000c0103401e6588203107144c888000988d06a030381d04c1503140c20080c1180e0013141c1042c2c9215082c03001007002c0300c843c4540301099601408421443c1c44036201e000c2d00340c000400460851203040d90200321501e07280070f025407030b8102d00004a2584c0100602034105072040d04481c0c0105004c0c441c0100c071507800708220000042500741c4035520908000f044000e00070040c800d2200445880c00e006c01c49926034086942da42c002d51040186840d03080044500c030900f914140c0009801c051480444101c04c0000aa4201c00800000c0c4059032440030034582c064070f5201411003402424048840c54011401d05070000325407a0000d10800ca49000a2102c01c560003101c0c10507501203140d400f00040b0004845daa58444022a0120343c0d0300c25814015003081010140074000c10394440000394000610ba806480d400358006440d0658a000130703070b4a810050250a03810103551020012400900030701e4080e1100d0300b40d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 159939586 1250 159938336 159938341
    0xe040201050d0213030834110105070b1e070203030f060f03070302030604050102030406050606070503162f1327030e100806030c0105040501050307120f1406130b0102070b0c010609020d05 82
    0x101c106c0315100c1f020f0311035109900b07209440b41e811985580310301140e002c03441d81c144c0c811030001240c5500803c10002c0c0b505605600340700c40d60407008542c0701c107800e10502000096031644800c1380c481c0426a42c8101d40f141c01c101242c16480c104030b465224a0300501107400c0a6603d0300003034035048007aa819074284c1d40c0002484280086802019480700c41034a0580c5410b240b030303541e00c0c0d492154244060044040d00381000801070204410b89040010006c581e8400788210014605508003442241c1324001c10503541e0765140080c000e109071a070300f190b1002007807240502040140e2410010440c1000100a640c5d0001d65604000541c0c0a0701a900d40469241c004103151130484111003450522800303010400241e030707200e021242c3c450a07903e094000d15850100c520007070b08034444000000d50034581c0e80314160041601c0706d403040d00d040b51110b0a001e0000700740012078200d0590b0b140141c000c070500780080d01400f402007283c0c25401c00006003045c3c0e1080c1c00001c9800046c3c15440c003680b550103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 159940836 1250 159939586 159939607
    0x304090902030c01021c05030406020d09110a090605130902042706050919062a05070203151e1e010e010510030c0818030d0203070f08010905010e040201050d02130308 73
    0x10010780f401081c00203101001d4513003000314a4000c030300c41c800108036000000038100309154054501e800c82d030322000d02c1040401c0c40c00c81840c011141c1d00714080e0b00040800190315003d400340204440020b400c120007101c1301c1959002400c1004016a0450b803030309840d1452007120701d000210f8203218040114111460f207050010340c1d00c082d0414800341e00185124414030084860700b58519805100080e036840d220140b02403504200038400756941c1701e4039984686c036800c48020000c0314422025030389447c1450036410b4500e403080d14403201c019054020140c00401c0ca24007960800700e07500c1c001750610141040d002010100340c010100201014004100e581000082180300c80d045042c28004890015401414540700900d4141c140400221203030b21100188121983c408800d4020340d41d0303281c01d10f80949809981d9000c0c400203000c5400000c0e05130a0707881924181c0b1a4414042d01c0307611141c00444040d0840e032032140801d9803c03c504041c1480100306000103500c01c04126495121005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 159942086 1250 159940836 159940843
    0x917040e0106090308030a022a01050a0b06030108030a0c05190609030e120c01030b0f0402030408040e010611060f06061204061a010215011703120f040606090209060d09080c030409090203 82
    0xb40500144000300d0307400c1c4000b403080ca09a0b0f03404044e103880142c6030100d514010046050201622096074041d02c1030390078050040d00414801c0c2d80c0c0f4070b0144001c00915041c00102d220901c00d42200780c005203c1c06254034852104280b2181c000c0c002ca42d02d0307500b440640c0d801000040b904480b401d41c4e5000c2c84007056040303000d01c40c0c00b241c11a042100c9400036151942c40304103401400e4100b59070394981907180e6840c039008008000b0080c1045459182a00e401446a800342c000e400c101c003965000080c1c0e20b0720a0703c0d5850350b500300c040980007a4417400310303000050801815841c0d00c81024060f040d401640364084500c1280078103404580120001d0032507600780034580b011030454200314590b102d03002c9200c5155044801c5824069100c0c92580701d880d09501030315000d00700c6800d2900c10311400344001c9071036900441c0607020410a095441d84140300b00d105816025400145c1807003841141c400d00d6120494660140315480e2901c00703042c41490941c2d00c0f0303800c00101070f40d0300c0c41040150709042 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 159943336 1250 159942086 159942089
    0x30d0608060a0b1e0102030c0111040f050a0501050a0305060402040b07030e04140603031c093005071109060d05010e072105150a02071b0501120b0f01050c010917040e01 74
    0x4242000184100c00100d42d420385404019034401410714070407401c5900c07c00448600d4284a4000c20000106520326400340c2d000c4c0c49001420000b2100204441c50800058000c80c2c005840d401c4c41c1120200301034010f000000c160039441030b400d10000584030140401000e196101b6500c1c0c00c40940750008010461b41c01118100f000c0081c2410084543c500000725030301381010040d1129445c141d0410075002d00011503004149078004e00301c607200359500e00c2c03840002d1200d0603007080d02c80030080c3c0e00300c81328000d038800a0044540c00900400303070304040a501d50000409000403040345c103240c0301c0720b003554500341d0a00310710307440780c20700700050f0111481c0c0d01000980c02058100c2e41442d511344030707038035015512500c1c81c1c84001408218080900e40c102c880d0158040c0b6801c503044000010000c0d8a0241e1180e03501003444044440305400c181d1144c90b40700740c8000c6c00c00c41c03140004001111107802c040e00340300040d941d868440c000314401c84051207660100300d291540e640d00744203030005c0340300c0c0c10b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 159944586 1250 159943336 159943351
    0x4060204090f060b04051225050a170c1c050708160504021201030803070908010c0309030305063a06050a0603060e0a05030906030a090b0717090a0819030e030d060806 73
    0x20300780144200c144a82c02ca904441040300e600302c400041c14821810001030003201028850b002308a01d50040c0e000c00f4110413a8000c0ba041208990740d4406859484286039840719640c0112a448001c0d03c0e183d1111002180f8104a14548410642c1c03014501031040c0c00506080e8000c40d551382810701c0301510b100203031006071015400c0a2559007100c604000602000b0301c134000110000740c0036441100c1c6400144592402884030020425015004048685007540001e0902001811904202030400c100c1a0450b4aa0300c0c0032280e070301c812014407149488401c5003443c440c842c4011981c84d0050600400c24030100045aa10b90315201e811540d100780c980816402c5130101c1c0000c04c1c000b2064a803a00c00c1031b07610a58036600c40d100c07800144803106000b00034140e04000c1c41642a0b01144040c03000300b40c00d0566601e5190202100e03507660044000906811040040075854841e400e15860b0030541400d0114050400e404240e042d504600368442210b0780c1c4110400155104200e030b01c0c0c00941 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 159945836 1250 159944586 159944591
    0x4060b0a050d080903010e25050405090606011d1009170105090304060f02010609021809060406050609040f020702030d120501060504060f0c0c0503030d15050303030f06240304060204090f 82
    0x1078100420610394414802410a810201d07003202162402c0d00040061240310003514070818045a0480d00c08684900300c000c108210311010030a81071502c9aa4010070030480104480e541303800044812040c0e50315031200007184103c2e809896182e03c00001390440031074903400ca94504248014828000d2416400e40c0c4d0b1303040c0018042d0241c4007000312002d5a140e890603140074214600c1c241d0140c03807140d000c444151310000c0c0d185c5900d02058801603130351400f213940d14603903103852003048140c6415010b0310358044030402c4013010501d810f078403c0b640c82405040140c10000c00760002401c000b6607001c0000401c00814000d00100c400303104840c050011424003905240c1021402440c07482990014820300100c14180c105000803002c02c0030007000c008080360741d83e62425484034090700d42c1c6104140d814030f940e08040f602d13180101c01e984c80383e508900154425030b1201e041000d0722195805211042083c0b40141c451000341074000d42c811402035502582d00c615100c00601203546444030141040d2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 159947086 1250 159945836 159945839
    0xc021309020a2111060f2208060109020a0e010f1b0f140102120a050106020a030c03032a110c0603060910080304081506010c0213051521010b060a05031612020a020604060b0a 76
    0x189146c0c213550f00d01a811501e0618403108449002e10000250016a002d2148500015203042650010014400b50340c2e20944006124001950b01d050110440000305646402d564410840483c0d0040760310701840110780d050a00d51101c200d202444c42080038981d40008120301c014605500c090340100b0100d404000319890600c5c020346525070240018200a458000c400034144a42c10122a100012000c2c2462800d202d022100d030510f5202288c002c106403102003000880b005c02d80d4201c010740640b90724903650b503450030440302c9034000b0000081100780f03400200f0001c404101034400307003005000500d50145001c07608100000c00428444c10050b808c0709000058031034003084c4243d01a0208085030131340310990300413960468886607580203041d02c042c44800b0b00e0700d20651010b03665410020081e1b400c1c1101400028485d22000d2004500d042010a2000260142d26900e100c05031400362041c0d10610038001c2a68404860500107034041c0003403006021807441180360682003268141e00d82c6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 159948336 1250 159947086 159947107
    0x110c060705030a090b070c0b06060c1011130b040906050a14010c02272d010b0703090b0a030f06060302180609121501090c0c021309020a211106 63
    0x1180020104010007501001145003501541c2254240c0d075480500c0d04111701e0000c0f0028580c0e50500400d5031a1190480851001e0904004a8000d140d240d000b4013440d1641030700b10406840341c8440d400c1e20603c10000345d1050842030f000c020107488003270a41540c4502c0c00c910306060310040d4020750312666080c1010045028110351091805401b030a0101c010115400041c045600d01c03504800c0390800168805e2030200044996031003080000c00022071b400200517a002c240300e03482c006000d40c1103510014058248480c0180114030700c13034035101c0c40301e039151907800c14541c0040420344007080e2188100107502502c0e010348000b400c1ca9107130440c1404180b69804881d003035400c5039103000301000100c2d1105916590200002806000c00312101103044001d5031000c41024800e2101480c80c200801d128035220b03400e10a00d01ea0014109418111030050102c01821090003c907480010142d001603860750880101c641d4032000c0400300074042c55414100c0d00e00d030301d50340c0d100c2c4605020040c0a521 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 159949586 1250 159948336 159948343
    0x80723030a0f09060513050f0307030221070c1202120c09010902180a06020a0c0f03030915030e01110a0f02010501051503060a030f0503091503100315110d060504110c 73
    0x21040725040410000c008400d540d00410943c64058049030402007045500e14046c017000c50700d02d1150003150342805140000b2070b100d018001004006800003c103841528881810800c01800120b416516240a69407910b040d01c010740c0c48000841103c1c0c01c52003d602d0402d02046209400034080c2241c2d0728000d0008018050500032840690f50101b0700d618056483d841800418401078180d16150b500c03084065540d00b401502101c1075141c408020446450100c141c800300c0e40e2586900f44514282490ba80d800030a50552004040d5079001107131168409000307001d00340f03803604105a681c40c0d440e00000e22030b0aa009000c419a0306190040109032030718208040495002c0d00078644903241d52000a14101059101074420620a01c0110920a0210007441100011504080170350400303008031031a4041194041811240e60008001040d0001c4406000e03401800340007440340d042c1502e0100346d4101e00303410310304150b682c0c000b403040d0708003842081e1a106a256540c0e0400050041b550b0340c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 159950836 1250 159949586 159949591
    0xf04020a0e0909070509090c0a0b18040f180b060901060207080a0f030207030c0306050108060a060e060103050604112206022a0a05130b040b090c180f06030708072303 73
    0x40d050810020703183d50001d22009002d00302c01800080c142c140f0030710301541c1d02c005c0543c00b481800c844100040110f1000304840ca80014040c025255104601c20440103110750403855080c03e44804070310003030485403841070b4221441014440c0740c0c4c0c1882410711940c804145c01c2281594000501400042000213000d40f00591041821001034030b01e01c2c0c12810071703a16a20041c400c501c100004810040c254000300e0680322440c0454049540d41a03a0078299503140c0b0407114001ca1610204445521940103907602580c0a007000c6a420f048005103c885e500800041500114203a000c2c40f11102c103201a00052810348020b11600b19204050740f00380348040030070f440c2081e4180250360b264843d0114080181002043c925050b02c0b140714040c0500f5000110500c12442c14000800525198180c0303402518802d500c9414540d50502600f907141c0f04400c460340c0400c050b8a5910745560301802503104940c1580d45000600713061002038400c100d20401000300124140142c40300010040540c1c0d07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 159952086 1250 159950836 159950839
    0x81b06090a08090a03080a020d1d130207170406120501091a06070302010f0903030e010e0604110f010e0402031302011103040b0a0302030606070c08060106090e04050601060c022701050f04020a0e 85
    0x10781d00c401803c0050707400041c075440241030303140102d540803071a82c001c2441101c1d00c1154486070400d1002c3c6142110078a01c000f20705902c2100038581031408507465010301107a07481100d10601d0a40c0b000c0c040141500300b0740c04040000c0b44817803001280d041c03d014040c0108850741c0241310f900b101020311684800704903401030040d600030035183c050510035003010701c201480f01c4003080200f441b820020041c0040181ca140c0d41c1d82444d4210015040000b62544600c2e0003203070b10b040b0f200303655040011009a54020504000c0d50000300b0b00107a0343ca100442c0501608140c07405442914800948004242c0720a80055002400204190400c140450b03201c05e589107001643c3c2c1c1d842500191841c010403401414401c014071002caa810300000340d8034103983c9551210b25059540314003440720101c00301d500030304541041d001005030740e002e144420013661004103401c0b01c2c61003210050140c01c1014007407500703681c00d500040002d4181200c05000c01070080d1810b61400e06c00c5a0040c218510380d51040c0d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 159953336 1250 159952086 159952103
    0x40302060f04030c1e0b090a17010906060b070215041208031003050303040f2303091201020f0f0403150b0108041103031909050901060306050a150c080403081b06090a 73
    0x1854152021001c0314042c60303114800c0c10b49a41c0325601c269000c17070a50140010f14809071808130700d641c412000e40e00c009400401c001c0c0414200401c2c001c0d54440c0345c0581099649541c1200001a840c1c0641c5000c2d244001c1e5158031207a150040180c81c48407450b03416001c0500704030501c4280c080e01164001d81da00080300d55542c0e152802121039500d407030b520150190102000344000c01890a0900700a1409114540300714440345d401d001605e0302854942e501030340104400c030600d041400ba000b02c03458060000600f01100d841212095511001100c045020001418403c03c00f1074008e110751034000242c100041c1c401c440c0080c14441010300042c04004a0080300c0030144d40810454003000b20245011104490b14000a00041c01c0340c0a900e100342000000496481e21034480c2c01c0440ea402000f584941d071a000e004a03544010742c0408041180800130100803c0305007000b800194401c0490581c6c80e10b80c902a01c04e40c06c40c02c00344208541100c018851108000903e0800c001c1d000702c8071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 159954586 1250 159953336 159953347
    0x80406050408040e04050d0e0102161707050d03020f0d020705090a02030910020a030608070503120307050a1202040e151206010603020d0b18090708010203042d050604060510170304030206 82
    0x2c0b0405003d568001111041941e01308401c1010201c0c1ca0010481d890722a003410542031401a600ca404203c121752420f000034408000007017013618440e40d044101c106403154140c484011404c140680041a0090f0b8014040c0c00d400102c01c010150403079101b840070700300060506c0700040b1102c5000d469150400c0e00400400d160140601c85104112844041190b90384014070020340504902d104058050042c0348001803541000320f184641103070104a002d01e9643c4946041c2e815030031401e0058104440c05868181901d6070b44010400f80031040c0d20040c681c617108000312045a16810700e103000d021459070380f5030f0503100051540d055905c942005030711022070107a5000105100808240c0c842265445010461648200030340112403010580e44400e0b100c01c2e42c0340c242c0c441981c00515100c0e0081d040c14030310203a00010f008035520080708510f4032802d620f956240084c00c1d00c01740c0b071160f41c1c1d1003800800400600312500901c089854515820170001d1065124000c0d44406030088100180e0f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 159955836 1250 159954586 159954593
    0x60b09040f0209101d0102030c1531110402070f0605070201150f03050607020307050d0f110d09060206060307030f260c0606032a010c050106180f1b0804060504 70
    0x1607881880e0007900510001c8031311075000b450f1100302c00410701c00750009410b0748a60b500c00710488000107101002041d00700400d000220107504018034512010040f901c0742c01000110b0000403121800c500440403d06265050956031a5000701000e0300c50340c0f041000000123581380240f0f40c1c1c0e00c0c2c0c22510006280d41c03070b004203a015040d0003003442903140402c0e4010607040d0b2a007400e0340a0702d0040080710b00b10303030324041c09a03920312491101521650050a00100360361140140e906004c1003131809800c00c143c4010891704d080d92fa00341c1003000c90b00401040c0f00540e0b042000700c0d48004214010300b80d82c4d24544610309000800c90000c0c150b81e80601401c1110590007c0d6114800f82e0000260343d102d20b4a64a03039151141994014400e01400d07000c42515000c401101c2143c4100f182905151050000151013180100034225015503d4103800502c08400c01e034420403205802c10046a03852814417400100e0344241601051070040103424588030b40d110300907075031041e80198006100c4e2124113 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 159957086 1250 159955836 159955841
    0x32301050a14071215060c0b0105010201050615030705040e0c1b0c101d0303040803040e0601030614040e01090804120311010507020705060703030b03031903051e060f2412070201060b09040f 83
    0x11000002d00950080001c0d59a40c0090011542800340c081c0441c68ad8880c00120b0a035841039605650141c5401101c0300317100e0303030007000b9908003d135406c1441ca0187e580351500b4000760111740c840d403810808116201c8840d40716021400d481c1098010308403240580700082c1c0c0d81c1d42024548070810020b5181400c8056155550705840007004088a88a40da0796420960b03c1d03100d8000c0c0c900042d02c030004a03034694081d010f01da09850000d61002003490382c107024000200701c0304040000540d00c64980202150000380100003030320119491950704c403900e080c0071b428200c030810140003d81c90b1170104062180e02040650030f0790800c0f40c249546410b030f42011000350071000700700d03070741400300081031160900043c0c28485039121a0f1410701190791010020309011640f0b20a08060710050000148a89000900300140320801400e000051080c602080c551000b44e2880d2141803400081d05d58900b055220180c2d8010039034402400b8450402c1280c0c00d480c010051a280210385582c5a004081d1564 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 159958336 1250 159957086 159957101
    0x60b03030403050d021504051e030702130b030c0d0c140a0905010618120b19060905010b0414091605130801020a080105040c0e060f03040507032301050a140712 70
    0x102280c1e140c0c1c0e101c1c10856290b50240000780c01600c10301c60305100c2c0040207a90b45108940000103004000c0d034200e11900f0000e03c480444402d804104007004c0180d50740c140c200100000b28000044c0b1008650038185040380e400001d41c49006480c80000000c1c0500301c07d407064901000d0b454040f040041c021400c0242075030801e1410b03508010010907450b034049411100411402039404002c0da5441c0c403000c40e4244100050301c2c481100c4000340c20303010180010030ba06480504001a03081e601c1c150314085817001e03040b080c1c3c034250004041040201111a00b5107580301141c8031505400c000421810710307040f100d8420240800070a201d00000c0109006070010036108000759078803810a41d00800c415424041d20348554506a110107800388504c00030f84c001c51002d40000e18000c007510800f108c1fa00700900840b40340c0705402010001502d2039540f07501419019411201809071162100e003524801040801105d160031205284c100718000c009800c8800350406450118100d115000548000f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 159959586 1250 159958336 159958339
    0x11125050c15031f031a09031603090305101104090e01020909040f031e12091509031d0306160c020f10091a030609060111033901091e060b 61
    0x30594115840c0c044503004500c01c40c000d0943d02d481c02c0800c601c81ca00d0050f1070001400c406d00c0c001360b158a041c0d594407441e0b0002c1810040368200383c11440c4003c109120754030200c0001d541154104100b081c1040584103060038180e082c800c50000c00000565801a44660f624464580c411001000029030448901d4000506201d425142500744904c01790701c041c80850004135500341c0c0301e11400d508030310185415680e81d5401e047c4002d4085920140106520075205000316004031450420b161180c011203d11a0f1960681f184035040d074201e00e88030504038640a80c00c01000c018a00440701e21307810014041d404d191088035501e001280008101d01c1c880c0c0c2d00048401419035406030407641e64012a18007912a01001d008006141e800380400d5450300d411503213482c041a5590702405000d42d280314200100c0f07044c00d0920484401c0b00a000c10f2160a81045c200000075050044400803c41801c220090140c07030b006a03956003090b04540b0f244200d1102c015059802c22846404c10000f0500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 159960836 1250 159959586 159959599
    0x40c0b070b01060f02010903021914030415080a0209061c02120a0204090b030708070e0408070b0c0901030609090b0601080606040801050c0d0e07030308061003020d0e0708011125050c 80
    0x3a949030010240c5001e01901000c80d40514042d4046441400341380769040d40350b8060000d00d40c034011184c5404410b600102c0b40b40f40c0b41c1c1340003954a030040010f03100400c40d40318009107910406102625000d0003602c10030100380100410031003622810101c50642030445006000b00c000c05030300d00000e01612804d03a00c030303460a0061107103050340c03a00070707009a03030300550f0030030510f14160209a520003580c07040d9850f5411440b000c12039081002c403043e078005e00135104c403854003899a407482d00c8440100c800111000c804a0010030070b591510458003e0b00051100708174544c0c00e601c40710340e60440101860704201e000000101d041c1c4641d800e4030014441c0e00024015400c0058951040303400901160007040d01e0700c0d104000e00e80000590300b085a42582310f02103580c4440d81400310b0300702c60900203405d0503001c100c0524104d00c075104540840c601080074140741d5040205440c256140650344064001c0f06120b08241c10340c00000020b5410b01082c034520509204c1e142081c1488600e0751115800300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 159962086 1250 159960836 159960847
    0x80601031e140606120c070201020a020a0e0f0a05010b180616062a0c0807060603170703090b040b0f0d06030c030803011701140a2a120506100c0803040c0b 68
    0x1403203a0000d481c0284401c481c040380f607481d407007401801c2c00f403c90b440d01043e144102003000c0d0300ca40c400a0509034010710568804c40850740114901010750b5010b40e041c0300d000c00400001041c4106038580100420780240b0041d450006401900d0280c80342d05822018483d0f01d5404d5903440700c04440785d100010503c520b0303800c0c0b60305011b001005400480060048903116510040442e103a03664030030109038990800c0d02d01d041d100e0418541084408649443e918400031022410a103000c175413a00240c040155583c5d69481d0040c010344c640d81c00b0080702c56042c042070100030303d000c060b03503241002820050786170a084100c03a0064a01684050304488040c0404006e004e0b0f0b80300114182c039500701c00001d808140d200540d0072100c805032403000c89014000405d08401d1070b600948030400108184801c1c412802d8103c074800c10f01c01c140000030808100031004200c0b43c038002c0d10707400b260844510312240080c080280807084220401084c0744800000241007202100410019010f0a0780c099101e5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 159963336 1250 159962086 159962141
    0x30b070201061814160504081207030e010e1f27150908030a110c0907021006090510091e18031202030717090f030c0c01110607020d08060103 62
    0xc041c14082c03080c0841c2180e0302204a031040b8011540c40c5562012004140ea80d00d0b4517a1401d2504804c0c81001c1100401000403200000c010310a0811940200240c2d0340d0384920b0b014180c003100c842d043d81400010300c2c4e454496543c444640110001b081d507803030034181c0d07002d104540b4200050b0414001c40007200c1d000c4c501c02c880c0c0146d2029210102219070601c403004000b40c50300c0c0781a115650341a4001c00503280d00341d00c81e500d860380c01001c030ba0484a143c80b61b03500165038090125030240040e40448612030b00310910b8040d070802095015000c01081c1401c0c0341c04203600000c0e01815404949454100050802c015440c0c0c081070386034241000081c080100e000038400c4001429000501c94051183c00a00d02e8403c0301c1c0120f00c11384412000400c1f40c2d442e170035000c0c0001d01c0080c10380640c1041c41411907041c0028022070410401a1246448000002d41340d1003d4440d541d9040d0b20540c100090140c0020381001c3c102c405013405402a902c03403004a01824034900b02040c00c0e0000c0c0100c0054 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 159964586 1250 159963336 159963341
    0x1090209130b0c04080d03111b06061f02072c071701090b030606280605190c12030f1512060501051f0e150c03030a0b040c0509100207030b070201 64
    0x4a44540c00c5002c19440e112441c4460740600d0007040c100d40c100e50618440140a9031110140001c0c01c40c40a00302030340420300d02c00d1189545024000754005c14100029841c2034503410140c0000c408070030172044910040203540c0d442c03a0184d100c030b02076403600c00f800c0340d09048424110000203a13200e20b038500d40804000e02000719111a82105000c450000c00e18410a00074030010090180003402195659010001000020005a6561124040700050301350520141f6005840903072a543c1d035500380b40820812108040d101d031410001840800303000180c1070380903206104454034010501100800d0b4031002040360029603400d41c030100c1c3c000599400c0c07601e5020398090040004110ba070381d030794040c088018841c40c06002404202c4450704111401042e03914140000900680b9103103800c084a00101c0d80512560300301c5500103c20020000624040c0e088240e0040e2408d20581c0c4030b5480180281c0995a9014441c550701d00350f2040c9544204052401160410103d031200c0c180341801070300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 159965836 1250 159964586 159964621
    0x1d0618010303121a01141c060b0405031014040206030c0c011a010215010e010b0a02030d0603050a02090c040605120402030a0f0b06030f0c0a0312020a050307060221060d02040e01090209 81
    0x141039013001560070114032010744110075850180c4555a02d4056010b10b001554410011145221418040d500184000d40300342c201619100360545d036074a04003400c051403c400c000c0304500460600d000c0c1d20748566101d4010f90042d505988858603a1a40c0c9602d094a02542120112640c6030484030f41c560094810310b00c1d4000c000307070207942c5085000050010700100900882c90080c90050040104030307000030003040202c1040c07043c0c038207240400c2c480e10141ca0b4203500550b590350041250f80f0540c0303843c600345038001d242c1d100d8091034903190007005007403070142c008003c170b0100c0180c001409540f07081c4865880540c0c060a44c01210b00e4502d80f0019081e42502d00600a1048002c14070052200184980000c00014000070010740346581d8020032000c04400081103000b428201c01c0003c4080014010f481d204520258a0b5442c04081f10503001400c21602240750300b81040c071500e901c4044c034030103540760180d80110740e03915001905400b50602c528001d4001c2d10200800c010050b00c12840c46 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 159967086 1250 159965836 159965867
    0x1101020d0510080616050a121b090e010f090c09030f06050a0501050a0308031303031b0507030f0305010513200c0c09071107090b0f04050103060507090602071d0618010303 75
    0x40b55500c40e010156521800c8801103030884045003040c8035140110041d00a4400c2c920b0b00705d0f050f4004215240a039100a0f1031a800c9400206541078150b40080d40c2c0c0300a02004548040f19601d0075400c400021454070071403c1440c2d42d07400068040740324004030b10145400c180164803038115454488000c0608941d861441440c0000100da41d02d800e110840c03ca0344c00c80304203411500c0d0710011203100c00c00c0f150700714103065071003103074440c5090009c2008030040f4060f114a0340b0f558150078090400c00a000b002400c0520f00300052200796540c4070682c5005183c0400004e03014072402d114000041c0400300c102e000b40f40880c0030b40d1141800202c4070340b400005c5d1813401141c5c562032400e4606240a0303451040641054900740072aa00d554003100b0740c4403000740008601c1071040c0c046800c9950a810a5a26039200c01c204280c80d40c004010100801c21440280081413400c003100301006403000600038002c0c0c0701808540282c0c1d440408149140740040481c896580d40c0c034000c0c0c00c2e40100140344 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 159968336 1250 159967086 159967111
    0xc1715011e0509360903040509011e06170406090c0902040b1b060601080402121911030c030a05120f040302100305010302030d0e060a0302030705070605160e04050c0d0c1101020d05 79
    0x8500c1075074050004c814140124010701c0a0404004560aa8600102071640f203100611002500f42d6550703080c10700038014082c6052281d82d448040c00310b0b40742690003030000e10440d84880c441c01141213507480c0d800350700900c0004891096290000886180380d00008201d0300104001c91603080c404014240c2c80b010040e00810b01d4500602251244000c8400704d000c100400e00103005824500c03580c8007414101025204031106425054407982591001510b4481e00200d8603005828204200d5844003021402001000c101e603035070590f00c030401c40b4203490010002c00c50101049007181610b020b55401003101a800743d600c3d00c014010312092005900ca842340502d000800d5000303200500140f00050903003480e02d100244160065800601b00008101c0104140380c040703025885000c3c00384011401301110b030124008001e041c1e8441c3c183d058031440c944002c0c0301030044e20700112182d1140303001d00800c107110554000e54009140c010350621550001a010f05481031075031107144920380c0d80306203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 159969586 1250 159968336 159968359
    0x12021611011706100f090e070305160203030603100b0d0c09090b060a0311010e210c03010606020d08010e1810050f07030b0108042409060f0c1715011e0509 68
    0x2c2e4903004010381da110381040354041e00078009841802c08140303880881c10118081540d0300d0207a500c40d00c0807590080000c0e80c0e4818400302400300c0160340f403441c1c0644011821402d150000a4481414042c0c100040d542e0b0710503032240b40c8070954525405900318a26100d00341e074800307000c4060082c1c0501180e0424800c400551245001501e0009983e0052200036003403015200544250f0080c141d00d43c1c2c030010200c42c42246e00040031106c44070121103005440344a1202c0149429121036030040d0040d0f40041040211a55001034442d04541c6054050034460725848540805484544409a00f0380036211881030714503116040075015000412076000c040d501c2c03444c1101240c52603502180091008000301c1d01042098160406c405051504543c0e03c075103849004007183d41c0c01c503040f076410f40c42d45151645180c0e5841044400b01690408003820006600440e80584000704500c900c3c040300c031201c494a0340315460051884020564030890b0418204010b486d0b500901840c5109080e20081b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 159970836 1250 159969586 159969617
    0x11030601150c11060706020702150421080d02160c06080402091602100213091a030d05030c090406060905030c010306060f030c1806090f120201020a02011202161101 72
    0x20000e0403110490035607104405221421100d41a41d40340a658070440140e03a508140c0d00c0301d00505225200b150010303540d0442d4030500100011403180400130b240244805c00070000060041c5102e400301845120074210245000700103170003004180030000e807000c00c1036100c41020380040c04c01d250051401030001c540d80e001c119020303a01280c0c0290801840c60200781c44410404c40c3d9200d07024540156580b210001050314226084402401242a0802e80c100400d48040c490300c0c4191640e54079003600c040034400420742d540304260483d020001c8c00000180c0b60b911810540f80e284030028814000e01ea03890000800000075401a40d10901414199485941c064400e1000701c0710300e9258140300880e244400d03001451403a60314000d01440c035900304001e0810ba0780348000341545854100d1018204192040380c0441c5800000004400941440250380c00040850101d9030910b4041d0142d401001494040d0245494607501e25078007a0061003000f404202c0d008556030281d03108280c60032202d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 159972086 1250 159970836 159970843
    0x7171c02090f010305060301091b0609050103050c090105030903040b070c030605010b03040309050f0d0b0a14010f060207030b060a080f0105040506062b020d14010207110901060f18080703050a1103 86
    0x5185a8020b140c500b020505500030703040580e006100900000b150b07802c540301c1d140302d480b40c00342c041c1811500c00401e0044035000341009000c0c18080c40c08100c2490884810105486000d00d03243c144100800000c065000400031200a010768a0384191284060318040c00384000780d0100f2207006003803000224410b02901d09482c800e54240d42c0c1d00310f12900e00310a100d4482e10040c10340f500301103403201d46d401188081d800d1a0090b01d01e85400a95450100e040720354103101a004a00e8002c00da01c01085a95800101c1c80141e80d0090b081010720b460f1300d03001a0b1070311807940c01002d290040c0c41401c000c4103010340c06244a14040c0060750b00c10b80e6034508100d08816031102402c1c0488241010040301c1c003001e60751100c240d1000c1c000401c20f183c2d41e200c0800c40d64140d02e0040c183d030740001d49c00040000110b00b00c820f6083c10b445a00750755041480c0504400002c203408410420182c55002c40b007400c3e0301104008004000a40e5200c40d00c80c20310030707220a40c06c1020b40c0c0d003a4180728110031904000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 159973336 1250 159972086 159972097
    0x1b090e0f0601080f0402040e010908190e01120509031c0209041103061e030307020402040f14150a080402040b120304030c08121213020301060b03010e090c1c050307171c02 75
    0x507900c0e1581607a900c0b1310040c44103405042a45c000741e136041e1740360702c15000f4411443c98074050190161601ba905101d20311901e0b2410340b040070400e02c546034095030f0b40c0010312449000f0001c040400d081d600c144034113203540210455088480ca44085121404005a0080c10b81c19401c0c1c2382400203038170401e011201403200b030310640c2e00000e900400607004071810400140d040070040990346004901c0d000038080e030b0040e8010720400c4225410070000c000c4107143c0c112039194240d0784002c04100c200c403402c041d4080c0704001c205002c140e2000400315640c0d54800400540010304846804a1010301e096590304140011a0380c07010311703140030a4102e40080d43e82c41490014104602e17103010801400038800015002040c0c40c0001c0e03001c0c0006070340a02917500900120300b02c4e40e44070341c0343c40240745d903a140c060840341305500002c20061050303d80c59000082c40280c26040030078001c2038035280346148a0040064030b05c41c0d64906a512035000c6000500070240c52009000100004411210491144 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 159974586 1250 159973336 159973339
    0xc010b0409030f030906060909050303012102011205061207080102040f050a0806060d08040305061e150109030b0c0c06090309040b03030309030a0e06090904030c2a0b030a1b090e0f06 80
    0x2510724204150384a40c0041c01c400c2d2003050041f440566034079140c0207541c90b15104070741700d0304044014010075006550681c00c960030741c0300d41c4258403d186c0003c5e180020b1406288141c5403950b00060050f211482807026030309880080350060342d03480000b18000d401c103009260000e10b010400207a00e2130450450000d85501d90003600c1680c0b5488108201c02c5154041110042c000f8000040454818002180f0030180da02da07450320710b5a884451044280002e101ca07400e201c50071700318001c42e43c6c864064410b495004100740f450340c80e000c0c01040540038084016040703100e41e0041008407900400506159002034400740590003102c0101522404202c8415446a005108920505100e804070a00c503480260040d46484142000b040315160101c50690204801c82d405108000c918001345204060070400c801e03d510400244034501d040c203201c2c8190420b400b1001c1740000070316520181d042034508204096a1852500160041c1d80f288180b40d051b1407510000f0300030303c1004003198403901d030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 159975836 1250 159974586 159974597
    0x906110f031b0111070c030b011a180411040609150201060315050a1103010e040b0606030c070201051c140f090607140c0c060a0c060b0604061407140a03050c010b040903 74
    0x40203040503205030b01c1c2000d0910544d2121189820300c0c105100919805024018400c0b40c80d00b50704003480301d0070040c2d000401428661450140464020003034511100e4940c41a04e005454000020060140c0b08259a002c0000080c001a8a03400400075005c9400100012450b200212000c1c1c0c00c90307090384006800325404058610381010b4981c405030340000780410000b40e0401b0160000b030a500700340c004c07150a441880034001848a100400c030340c84441161a82d20310316000f0300c40700c154082c040000741801400304002540802c02c210f0b104005880c07030002c008000c101240ca130b10544003950401505a1100c0226085000206080e0b00c0741030745455585071204d0f4020b030040160710050b140d079090302845c5003041c0d0a5a0b81e100801f0042184d545403005400181001811181e01c44d819521901c010401001090f400c58882e4101000c0e40e0303034058464810741032a08101c03002e0f503405009405108000c008140c0c120016041d1003003104003c003d41617000091004440c802000a0080f50 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 159977086 1250 159975836 159975847
    0x302040f0e0304060f0c050a03080601080a09080405060702040207170406080c13060c1505150301062102011b0506010303120b03060f040602180d1101081012110105190906110f03 78
    0xd0050001e482c010303405240c051b825800588900342810100d120450004118070144600c0d50303446a81c281e00308680316400c001c4040b140d56041c4040c03081c0d00c5a2801000041615810b544d00ca905446180e60403020000641901e1181070040758403600410012504c0364010400c5030b0b40001c15030b61f00888000d802c9000c82d041200a640340503c1078021920307444800f42603500c40355140249070040c1348000000c180e0007003000070103081d1011600010002c202d07008200507019080b02c00d0400c51902030925041501074111040c800000c2e50001030030b0f031b02c194000001015840302c12081c150b50700c058200f280e080e00204040d161007040d9525198400c0c140c01080109104c3c1d03004180c18600c485048140020300382c0822180140083c0c1a1540c1145a12407151035030403002c10b42e400a1442814800c4030b0a0014103e1042404e03000035051805000400c02c5036400b07031045690055040503140030200401740000d00b000d18501508002580d4140c180b881010006140d611007540d940c060350502 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 159978336 1250 159977086 159977099
    0x903040b03180a030807090510140f0906040b132c071101180224030103060b0102010609022b051302270f010e07140405010809070506040f0302040f0e0304 68
    0x160000380030345440e03010b400d501d400300510800c41161074600c01e8917040ea0f54501244094024009940280e0103226845010401158041c076081e01c048607030300b00700351a0b06888050b54924003614000036048040041d0220b0009130303d001a10001340140403c03414141c4411150500c1605079090051541484d21400c940c0d00e205180f180d8020346074600041c80c504103030081400c1d0fa08092704c41c801002560280000e40c281a08903030600c46d24160b901050130002c8003c0d0754030340f10504c006005180c2e03d01d4602c01d5070b0f200b9003040b00207021f108000c1d515500003449403000d04c95800620b03200003076022406052034000f400345070f219440070207454007003540540a100c50001e0f41c4110940349007006140c2c1e5908031780c4400c9039005020000705400c0560402640445021010b003c0c2030170700050304550100140201700f00d40c00d4850a10340440e06455080c0100d01d401444c2e0071482c0d200c100810045401c00300d20501a084070300895050000c001400b00120490794050b06020b81d40d0010841407049 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 159979586 1250 159978336 159978359
    0x1b02010f0c02040f02091c0f03120204030b010f0501110a0302030409020d090b04060207030f0206010e040303020c1009030e040b0f0a03020607020a120804050a0b0c0604030f0201090503071217090304 87
    0x510031414007080c50011a40010100c030080c802101640307601080310141400c101410052000c8004001500d1120540390703030401c1d0034900402410400101100142d03010160190340c020742d84210405004d5840d0865200d44400b140605800100b51050824003c0000560b0058258040d0040d6103014201010b4070069032102c218000100d4581c121038000810325182144075034000c0740d0060301c1d24218500101601c00901c1d154003103500c4000107005207202c80508542059140c200182d5404100c0512424a120384520f054514548038011080c550071450507246801e0484041141140c900104855045112240b6400202d404c2060005041120082c2005c0d80000c0858a40c1e0340d80341000e88100e078140f001182c3c94803022a081203036040000801e070103001c0c8080701600700901c542c001551b50300014000b404024a800c41090198000c1d48030082454001e000d40f580c0346d81c2424441b170000009850100050400340d41d00824171443c803001406040075201540c94949045110003d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 159980836 1250 159979586 159979607
    0x9041a160e01030219120e03040305012a080f040f0209070915050a080a0b01140a05070b0a022115030f010504051b0d060b032e0605090c0a08042910061b0201 69
    0x106c1907501d0314410070300c00d0104054002075104a0011420f12619002c81000549400c800c41b0460041040c51290301e41010020354000094400d07a1040d0740c0368101441c4441c0601070103904110148140105554408442d0060700c1180e04052011491400122424400c2c00a0742c400914200c02090944a013034200c404100c205252054080d0201c14820049900ac05d10030004224001050f10030000906a6240d00c000001021401c0c1072154003c410200301004905800c0a4400c000a403801030741c02e007151071858060100d50a002c544100d1070f0090406550a440314445d040c80031410400340710103c1130240026068812204003aa07a01c40a0320030940d8483d0300d401407040e000c4d421103101c64030001e81a408101d4420b900c0c484031100080b600550801c600030f40c0307003000300081f104510003200c0044044d403410006981e80e606005a0300040010b000c0045e55810300e400003103460f0b407045030f030003411a403800c0b166040d65100e050343c0300d00d100c0005946484401f11101e0156008030040704 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 159982086 1250 159980836 159980867
    0xd0c0f020d1206030b010e070306060503043305010602030a0e1203220504090f0b060405240d05010908070b0f1b0c160902030702010f0b0f09041a160e01030219 70
    0x3e00ba5260758440300d00e003900340c024003000e500c0c502c2002107035a0306003c1c102c028149410140c2c61814281c40c0c6201d62400e04040c00c034010303071884983c115401d48240f11a410034002c1420000ca5841f180300030345130350000801c400020281400c081c824600010800c1c58150070200661070480006c184403070050702403190907481145828000303069140d50162404e03403482044803030b030305803503a140030802e04001034a1107000f54648000c00842682c905010032407000f0031800c1201e14449140060385c03000c8802c0c0d000b4015401c000100081252940103001007a102c2e07008004240e03101442d50301c007544c04840302000c09104401020f1016441002004032031718200680e1030300f480c1115400d08588095001c0d4050a40c00010051110340c2842a203840d220102c0050016030440e4002419444800c130702941b1800e0080c001c85d003041540000c80007071040c102d203408098a49821141e103d114440c90000100b0041c0c070590700f1a40c42442102c41e082c9409200c0c11881d1000801256903050001400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 159983336 1250 159982086 159982091
    0x11a030c040501083106052202040e070302031911090405030a05160b04050703060b040606090513140c0301080601090525021002041701060b040602120d0209040603080d0c0f020d12 79
    0x1d80b21150b25545c000703100307407041c10000048159450088101e400084c600c4a07080701c8001e4003d50701c0417091031140b01d260100c40c0032944042d889140760604e0102c1e4402035040c81511034000c0041c40c01240002024011801200071100341c200f0700c61310200855008107160070030440d03064420301560103402801d03540740341c400f45c0b080e003a0f41c1c0518041040e5404da907140e08c01c82d0308008014090043c80650305080c1d506101c5180f50050281000515000e424400e0003450030383c100c2e24030f4a40c011401440302e428840c40744d0500d0200800e035680280a172100c075005071000451041c0340c17401942c0c012203d211104180340410815400100c092200880841c041d1100d0005081e02d9400940080c1041e00040b91074010b09401079801c4031201e40c0030b6665110148800c000054000c94050480350710314140b0340c2c0d02c43d0140034500007403140c140c00300e50051030588080b0a1148150282c1000c54007003030304010304c10422800750350740c42c201540000140d000c10300048100d841416a085082003d0402 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 159984586 1250 159983336 159983371
    0x307030f0501140a0b0a05040b030a0209090f061e0901020a05030109020703090519051e18090c1519140d020d1103010603152c060303070f03030203011a030c04050108 73
    0x1083c600c0310054078003a09040d11104044140d05e071440c0c0c188000c1004a500700048010701d00440c0d02ca40d45100007a104012000001e0851f003410b00c41240454170001c01d94070f0500e8261160150f0500c0c2031444043d00b61143d00003983c003030052003265009251601c0d841d0071130b803a0508581c007a61211004500300846602c00003250307201c074174520341495079000322603210314100014000f401c0e04200b21266100d03030255078801c16840d80c000e210240c4d001c0038907c58990303581d1040e040c039040c140c008803508500c0d299008403d507601d000c00f80c040c40c8080c5203c0c1504070210602126541403419030820101005c00552096806942c014a015100d501000c900e00814080e12803650304260f010b0404242c80d00d03150812481149200800b4146200c01c1c000d404205150002c10810b10042c00341d402818140410004d03a410800d84881d95404500703040101c0592030000c0203900280708919644c418201c050000030090701c15280320308012203c19091914180045070b440f400031380030751541604c1c5602c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 159985836 1250 159984586 159984611
    0x150b010c140c0a0f08010e01090b040807170a0503070806040504020114090d0b0c0c1c0203090d1104020c0f070503030403020312070f0b090c10170412050f1204050f0c0307030f0501 79
    0xf80a0041c4901c03a60010124900b503950f6013075800500b0403180a925003412040021906885550010781017111145c859225181c01d240380c499a03403040c0d408070f170081032000c11075600500542c0306400ca55100c000640310b1100b44000d072401500c0090204212150002101418901500140034001c03c0c0714030740c2910b070700c608500507025244d624409a0014121003000b030304112029004c1104299211840401c0728000e4036400b0b9140c0347c0c4c2c03180b401c0390200e80900c8000c0740b000c00003540080085542e02e51140342e150f80c40c04ac8000344c00c220b000d12040050207140110a49040303d8010780608648041103071044000d90144008440e0340c03001c15a1030020401025250b449400701400400d00e280b0b0000800c0151405440c042040000c020400100000f07842c2500340c01642c003c002c1d0100208036a810358080c06a5001e17691014000300f041003800039990101c9000718010010707504160700c0100380d1619901c66494550b0182d0090300204000748148140c5051640900c00005982c09045c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 159987086 1250 159985836 159985849
    0x80a0515100201090c0b0403030503010306020c01020403120201020307020c09091b0a03120206010602011104031e021f090f051918020415030204140a050108070507140109030c150b010c140c 83
    0x2a541d0340180e54031980c0d10100203a00d85440c025010411500342441d00d0756500a000e80b005000c01400d40f074012440400d04042501900c0103581d100a03405507242e400c842c005e0003074000b1110700340107110310718000704103090541925002d00112800f5000c00341d04034414040165040c981290801d403612000800b04450220214915596a000c0c200d194540307400203007528402c4025501aa40401080001a0060341c409100040c0003000b103105007007500004846008510019034526642030032118119030001d80001900e8540c1d83c1c1c020306a45420034410150f440611768a441c1842202c203002d9900d880d00840d500790039604025240030380f10400400018608110803001c40d0300420b042c0030814002d803001c0c40c411025a90030390414074200000f0050384003d0104018000001400c10600c441522601e0000e12040002c0c02002081c0c0f8009081a000c1c400645102101c6084103401059500900c207804205039581c1078010425200c1c0c1604200c03c13040d080c0a4030a03405004560744810 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 159988336 1250 159987086 159987109
    0xf0303040f030c06030e0706110a0f120f080402030604060b0a0b0a0f120b0d031409180601020d020f0606090a061e080c0d2406050904050c10090501080a0515 69
    0x6000e0510705034550b00e0030b00e40c180240d4110307900307143c10301c150076201d03080c0010a070044901c2483c0803280c044005011a083c100700c80d00c080c01955241066000780551401040300740c9d2402d940f41c8054450000c0b003141c40380e0040c1d0707009605401c03207004600401e06075080010041030040802c91800c0e0b50f00311a071890391024464002050307250000d41c0c001d41e003225180d0601d0901341d000348006002e040024195012019008051042c0c50024400306160a815141c004102501064203d010980c28104511044519900501c241404840c0461000c112440300c05103240080c0719545518040104c2404010441281c0ca581da43c40060500000850030000a103180d010b0301199003403400460400b52100c80050040d00001c0601000604010300704a46041d89107107011180c40843c1e041010306015440326a004920b10180b0080c4003010036601e5103a00708880400011880781402c2c0c680c0c560328494207000c00c060000180b110032113600110b500c103901a25900840c9030440c0000c4044090303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 159989586 1250 159988336 159988349
    0x2070b03070c0611031603200a030b100306080601060c0623150105270d050f030a0318080906071b1202030f0c090402060c0c040906020d0c0e09150f030304 68
    0x804600b42c051214620907001d407110050030442c40c51130322461a80c400b202203500c100c101543d940000341d0880c01191511681d2003020a07460303070303282c4004000f006486c000300c06502c61803070400107200442c0a440303030400306d9000d1400f81189a00e814010780d054040290203407215921034056000e01c041248103903078141d0560b0805145030400c00205240703051074084543c1800010400f810701400b5005e4000e8540c0c1800038540c00c030042020100d045c21100c0d9100401c60301c00c400c52645c1540c0088040c00d03880032a650200141302c01c83d01455001560301c6006042c0b07281c100126001410104024807034180100825100200400c103030b466a6102070748805c00106142c901c220451a0a00030000c501c049503000341880540140013692010024100920035500020b07002003100081c0540c13281200300800411030044c0d42d052400281d804107903411a11031405411003050740c001e501c800d6800c00f0107090301c4a19552949800c820082d99144541e2011190f1a291800c1e9410030080000d0b000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 159990836 1250 159989586 159989597
    0x50c07060b01020606030601170a080a0504181107060b011b0302030c12070c0b0304050708100507030c0512010b090307090501030609021c150c05120a090212011505060a02070b0307 79
    0x1504024003180d01c0140124110b4002605218083c0d80000e82141510744100000d807040140302211854a048868000e01090b80071400250079070700034000c0c00c2141da0900d405c000c00c101525004003210070701c8038006111503051000c070003c114164001720360740d0018140084030b11007441d448068480c06450882c0180d00c00101920072076400d0140380d0f0384010902c01c91341000c2455454074101ca041d4001d009a140004c00080c2c01d1050801c0036100500c007400503501480100d50071403016000445001c00031a0410303095a41c8240302d0021100c6014140340d002c20b081c0d017402d1100d245c0d50b0040034203a5143c0700b040004200300703a45105581c02103103c0c0c94001000b19452040c08968082c90f4040900f400607107072003501080800031140d40207004d5110000782c00c0c2c0e1480c8143d499020f0500b4059914010008205180b4135035448481802d00803103205011140c01642e0501b03940081101d8a035945181500708920b003416005040012568015503d1441d02d60009001940045403644006036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 159992086 1250 159990836 159990847
    0xc010603031d0f040903170f040b0609070f030c0e1002030304060b03031e0d06121115030c18040605061c0f0218060702030c1c0b010e070c150609050c 66
    0x6401142c030000b82140d54000c903098241550015281c96456a80c09000c0c035200e000c1c00b8101486000a0003c48011401d030686c18202195000c0001404560496200c400c0801240040c078102108601c51207156680c03c0010621440c1100a408440704c04c4090041c443c60320312090f038072a03800c02c901c20110350042d034030b030329003030030628181da29030300300c2c540a078004000000041414038140300304035003c80703c9169581118142d50740109140e5000d00050b10301c403220b034010040481c0351000c90aa040314105030b43c24182841d516140b005894090041030204444401e1850720025100c6000d4000c3c0006002950742011882540c40202c4600d041c49510050f20b0070b017a01ca110385082e000711480c2c01c50801e041140c40c40803240807100038500ca010702040120031950208000d400164000e481501075203448240c0e1828040000380480b14012a4000400d6503030650500b140300380b05694a00000e03c805032a61081c80b104044800910313610b898020030b11544900030a4045c100b442645036685 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 159993336 1250 159992086 159992093
    0x12007090c080112030f05070c05060d0e1006050f010c0203010204080706030e0708061302130b040f1d0a020f15040b2b021c050a0b03060c040e0c36060c010603 70
    0x4000580141c481540e11388200c50210f030b40003500005100340c600344150703524007900f0403401c4a8070039441150b0114001802e0f900c03c0c1c0c104d4100c15a108188422550310441410740f42c01a101c07280a0140c0048000c0c0342d41640e90f00ca8828900b1950014000503e000c9d210400d80342400310503048100465181c8544080b2010304210160050904d140034101c0741c200044615902c1683c804044c0c8100d01103914a00e4400243d07001e40d042080080041100420401d41c00000d00010640c03691a08040c070301c2e034080d5000114185441a85c01003281014404200410030f00071000120110800018080807510502c040001c0c1204070960210207403400c105800c0440c02a9941742052540d801403004036100701418000083c10241c0c4003020405076681d800c0000140640c4021a6140c410704040c414208007075001081924401203106e41c8560350130410304185d1081161100300030070b011400c0308080724140c03030011010b4400e920000c01d80c5070303403000120180c0000c0400d0210741d65400041042 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 159994586 1250 159993336 159993347
    0x100605030d050414040203040c0b0a090915120b04140703080d050a0c0807121e050405060a062301090522050a0b010905011202090a0b0703020d17010302012007090c 72
    0x840e1100c0c5000b500d02410604d00454407a040c0039030314003c0c4d07008000324081054008042015102d01510242c8440081800500c24201da1180c0d4014500e010343d15203035001842e02c0413043d0b42c4642c2a40070280d00340c0e0b6409510f480011303c00d45200c07e48c10b4806083c4034092000d18015405442c0042c0c0300c00f1004052030483e4801b0b0f1100c100c40c6e281c8101d045400c0d400c43e0342e80744e008400303040a00d40154610340729000b41c1245015600c860b01c4005055003210001d41c000390045000358105d800643d40d286015007210030500400f602e110714204c00c2d0a6003a6031269040702e00d8010315000d04020b54034404180c4414074540340c46280d190441010916117420300c9102d07800700c2e03c081d05000039950980003030f001c0d51242c001d00e0b0404c622065000c0f44801150119004010003901c0030045994030000c2d0030042d0000b40b42240180640a8103e1295100c0c081e029a20010201250b109074a0f517030041d0b80070700f81100c840e542c5284d040013003c00c510301404031100400f000000490104c04500b4010704 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 159995836 1250 159994586 159994603
    0xc1506010e0d1e1e110301050702071a0702090c120a0c050a0311090d0c05100903020f060903100c030c021e030d02132304110c0c060d090510060503 65
    0x401000c2440c82841c0d96404050700c14640c0c00140b0310714400722410400c091507000c03020142c164903004040c3d04000c0c0f148100748002c3c90040041100001001e0101400c3c0c980550780d0000507800002e0074040810314800d10140404900c1d00e072032a214407030340400c0459030308490112880da80820720216040101014560001c440c010410040c0c0c070b8410040c1c8107019200510041580d501010380400321036200722441403100404e80510140b01d40341503100387c5110b00901e8082c0b2203207211810098080c3c3c1043e800d072788d0b00034602d9580510350000e014841d0400481d8990500c5242c41c074624404051150300c8142d4500c0ea40421600381040f8007903e008405440c5203220740e032503000d54070500ea010003659403c0c5000200940c1d100c45040b0000c0c21192590000014059884080389000080d65180707504841e050f1810703c810f5807800c000603803034002d4100103022904841ca81c2415850810020b06824885800c000b5206506465442c5081405084c0300c5450382c1da02070503c42440c0405c070805 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 159997086 1250 159995836 159995839
    0x40605060607020a0605030c040906081c14070602070807060203040b0402030d0c051b0420190c0201021b1302070f0b01080f07030b070903020d0803151504120602040b0c1506 76
    0xb8545141c59000c81c00d40d020a200b024100003010000c50000a00c400c111801001c0c4080e0900406483c2e03140280c9034090010403140081d01010341040050007040550950180030404a00380092616208041e510080c1c080751030403010008840040e15520103540039601604104003249014810f01d031800100c800c1d10002d00c0800c026800018000007140c102441d04442c96030740c116415070104024016121843c3c2c5400160005007500d100c110000e0414100c625840c0b070010028414241d40716905860080e0050300b1000030441e51200c0c0007118000c6000280031490741c920346009a0f0101e82200301c0440348902c0b00c0c03d0040c188a8000720712409848594050060800f50309034a03960b843d040d2100622000d84940010769050041e41800001c54010300b00444440407454000904d5004a94800005401201c608401d042400c90341c04840701440b80d071490035041c08842a007207140f11404681c4d01e0703000c200200720842c002e00940303503144401c4003c08207403007440410180d01c0707401400325 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 159998336 1250 159997086 159997099
    0x21031403130606142409040618140402010e1011070f170304062f0102030f01080f07060807030b03030906040b030105010210020f0315010c140c1005071203023004060506 74
    0x1846642d81154161005e1504101e05c1da80c400e05c1000c20b070881c020302040e1544607292040c002590401e400712980d00e0403c5541c02c200c0703160501220b05d20b18000303803006070000d4814441c0d99503905000380390101d60121401e081c1b17122960012070610b40400c5410180354480803034070410400c0511244409284401400341d400e044c01e24500801411840760741e4034600810b5034000c040d5490311040900050701c2103009643d0b07498070130301180c2152401c0c8510700c041d00c1070f540c07510031404d03011540ca804e031034080c1d40b0030007180c6481100304c0c0540440840c1c0e9078103000400901c049035603158000d0005140700c452003a01c9600d080700181c1401c09107180c0c0606140100840c44880d2184021a03078021640d0380444071501d41040120b0300364207410710060102c44000640d010315400040c02c001100360468042c842150b120300200c9a600901c080186100c0c0303286035921b04580a40c01401001c211480c1d0b501c0954060708001511640d48c003050039a00740c544080c0002e1100c54061140c0c8200c0603143c6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 159999586 1250 159998336 159998369
    0xa020708030f2a01050f0412020303060d0b0603010b190603110307020a1506030212010f06080c030303010509040f15021909180b0f0301020a02030415030621031403130606 75
    0xb4034080b4400d41129140c9540180440d100300c4419102141e40042044000c1040c1e00d4040c10303407135250704242c0d429a4000d0b007007046082c20b684000b0441e8812a8041c000380010340056848082902000c0c11403941552243d001181c59120b105100600500c40c07590451100c4ca00100a0120740c240e00c4809000300b400c01c104980c0d250000350041016030b020140820216050800c04000e01590300000e5000303210140004e00303018150081e10f245d000c030303c1c4104001941c419015a8030400a1409900b45c0c1040c40100400c0c68807101c9594058000c01e61510407001564500500643d00c440d402d4450340e02048144aa2941ca85084003803080c1c0d0a140300f000717091601030340b4000d807800c506034511a2101740d04001c40d00d9107005c400c2008405030095403560710246010751290854018100d00d845035803041c60390780e8071034050b0504403a00c413034420b00c4596450040d5076a21007050400d80600003c0c044a00e545c3e504900158402e8103064200c402000643c90184113644403039100d901000c04d40c2d01e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 160000836 1250 159999586 159999607
    0x91002010c050a11010605151305040b0a030204050c0d05090d0e01091d090c0310060311040204050d03050f0906040312020d1103180301060b040603051e09101a040509030a02070803 79
    0xc6440300d14150800004c03408681044901500060b0411604800c050040c02540381c0d48030040c0400092080e00b2018250702d400c00c1c00111001008a580e101c000051f0800150400b035215613004031703180c01c017680740c00d580c982e504081d02c20030b503001001c1d94029040c0f2152164001184146440240713010304c115480c048041a81c0d1403002150b0147c114200c0201e0b0344481c0c100684025440d015090342d000355a000700c00b100070b0190303110a440c07044c40351001d81040e00d06403080300c1c191240181201c400b041d030354034200c54a0f003106260304a50034040100040311f60300c800140c00298410460340c8682e405010009040ca40e00c20254410b0028035490400c203003a0110075100500c4a00780300c4000003000c400081c2c0500581e601c14211880d00260119259034550002c51251200c0e20400f04c02c1c04000f034500b03401000c07c0fa007100a940082c0400016002142c001d4001c12b50014103e00c2140500b1000404030740e42641c1d148039942c80024a95021601880300074010054070002e1030800180c03d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 160002086 1250 160000836 160000847
    0x5040501020a0b090f060103060606140c0304060302031f151b1104110409150602190b0103020609010e03030d200a09030209040501060b0c0105010f091e092105091002010c 75
    0x300000e1a00c3d206600081542c4030401210b50300d40c458408940d550b5941e0b003070181c004c0c0441c3c01401c1c005082d400109040b502040201e8080d012400c00461400e450240214020340001c7c15142440303130300e000507210410380050804068150403101c25600c24180b90054401800c044074101c2c401e0481010102107400c00150103420041602c0c0807079200160a0444028815074201c1a1a50f05e0100002c482d40010844041a1441e58003191008000310100424220f00004020301400c0104018001410f020340a0140c1c0c1348107040c0203840010400000e81903401480d0882c0300c0c0c1ccc2c0e80380c02e0304580c011401c0b012820203468244071850320001540042c007018003400081e0046890760081800c00c5025400a80180300c03049074580c442030140381d460b01a10081c13051410242c4102008915038002e4440c00501030303814200c03d18000b0345206007601070407400005481a0900c040b081f04011440610400310001c5965902e5440724004200304651715940c40700c00843e803400c403d1000c49500310 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 160003336 1250 160002086 160002103
    0x90a0e100504081206060c010f0522050d11160617070503090307030c0807020603013305091201060305030d0c35040602040312050304151415060903030a05190504050102 74
    0x44d030b10540d550b15040401c0051140c45410314003036203030050108081d556644030500030320039681c0224038951100382c9000038698105c005030042e008002c01c0b102c0140100d0108280e0303007080c020348015040c5c440d1911070301c022640c0701d280030a1b600824100008000120140c6c00101407c00798113605201402994a024401d001001c3c004050000c4003880034190543d07000715030040c10b1a40e80d40e11207044d0406661178000c141c00c071303a40b0081c01c81000d070201d54484080c009180c0d211401d0030403440c20028100e1901203d400d0703039540c070322011011600038401800320112082011070030354210742c1c2c01002c0d00d910100e18800c400003918445403c86a8130b6002c100d00b441c03000802201d1b141ca00f1f190001303214603070008006884000303082d804913402c000510300c901d0242c41455005040810f0103020748682c0d5540b4080f000136000011090750101900c15001c810103032080c0e04120309600441d2640d0720400a020120344085004d50b00c0001060302000c648480f0b00d0414189441e042c00070350b40b030840c1d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 160004586 1250 160003336 160003357
    0x206070e010507022e0f020303070e010e060d05040602040f0b040506040603020a051603020a2f13060e010e01080717030a030b06090409030f020f0703050618010b090a0e10050408 78
    0x9807903004d41d51040fa52903420000d07864040301403c4405003104950110280302400b0888010803030581074008000d40303100d01055150450a4541140111030403103ca90703086501a42c14403025078004040e100b55481144903840060342c40d0700f4504200c0101803d41c0c08100521b50410003400561107a00650f0b04465040c04c016890324154402520340c0d000d203a500e60158581481c10340181b640c00200800340c280152903103e0001c1c1e5075001e07403140c2e96003100c1100802c1c0544420040a082c502031100300031210640c0014440e0f200c5a00c1d20961000380d0002c0480020f400c01440241001e0041400400240407141c2651591101c220344038003515aa800905948402c0c000c0d01e41c80f987c003211000c4000410411032813006240142c00b05020f945070744014030456406602e8060001002019290081c004040a90381d100b4803400c20440a03100b030080d9500d9004502e4181c60f4101c03418025410f0802c00314820030300b055030300d2510030ba134802043d1843c102000d0101089000f021038003401e04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 160005836 1250 160004586 160004597
    0x7060b010e12070303080a111b010e0a060e0706050a1209020a090c03020a120b03120304110406030b0109050903040e07030b010e0a06030e0606030a0b0c18030d110d0206070e01 77
    0x64800680303442480d0305034980c110b4050340a80c0d80c0c07148049528410340c0e00c241c4070090702e81c0340c062007103046400c200020140030100b086402c800010b04c406807003150440304004100c80d2600c0c0401402e2208000040303c80c5034031a4034040c15602c05006000142245141940c2000100c1e40020030300c40344a91511049580c07000c0700070640d141c0d00a41d1015080300b1000707000c54450200300500960103142400c00195411030003a80c21411801442400140100203042c1c5106500e007100d007035440500b048441c00c16001c1c651456440303e014110046024030189202c942c50305401d142541d5000340400201d420820052080c0c541c958140703500000f0724500010001d02100040c0c9003c440312003c144e015a10080c0000ca8035459004007251110401c1903a810342c640c0010b059440808050042c540041c6c0303000107484500980142c890b40c40d0000c0c81c890159426004079050140460480c0c001504a218403600701900708003080b4202590f100908e100c0c42c00349001000d010f0000740c030504201 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 160007086 1250 160005836 160005851
    0x50f0f06120a080304080309010e0a020f04020d0204030c09091502121602010e011a0102210304140703170a030501060e13020f0408070906140117040b04020607120f020c0d05030706 79
    0x4000b08807502040b54441450741d40c90a01d0b041070070035a017007101d40045560030152042a888404113509800369405419845424150790401010350004804e00c580c41d81e0900001011841c000c40f40c1004004001d000601c0201a0034103611110b8040039500c0914010001100c440381110ba040760b0050040d02c01160780112034030203d000d801103040b2090035600f8103001d20780b90006030021a100391400d03000c0b65a841c03215070b040181002035007650f002490090001030085240450180c130440c40c3c00066400b629141e1741c3d1040c1b500302400307440c60703080700104003281c0305605803003043c0c050100d50500880344803c0700d00189250002d8000c1c80c400540114401851503c00030948014242000c240c400c226140d50b83c450050103070344258a0000b0182c07070710002c5540564010b184540c241d040e52001540c3e540c41d40d20046401900c1245c01290030071190340400c10b801203203041071020303550705080b003040104000e24101544c00c002c0c0c8109102001e55001440000444148a034061030208010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 160008336 1250 160007086 160007119
    0x80105150d0c35100605030f100f0602030306040f0b030c0d0203070906141023130b04060804050d08150910080d02060415150501030b0409060609060603050f0f06 71
    0x50080c12502c3d212400003c9a81600580d00204210800d0381240d42d101a55601410803d80000501c01d017004104200301013400f10310b21900c0c1e81c0e0702180305860480710340c0e560100803e5002e4103911040c0140c0010080c8010f80c6458003804a281204135000e00c50340e0400c0d0b0000792281041c4802d14404c1c000c100295084ad1014401070000345190402044040e503210000e021034910303082c0c0c461292862110801d20280140840030494024040c1404100381c01e84907007203154015540158070603240a0002080718900e002800034165694a61005041c03d02d4014038000440e0715543c1804242d038100100c0c500711802514801c0000c441054642d2103001e070b035902188454002640e1400389801e1402c41607000614640101d119500795042c0d40350100c2c15030121540e520000d80161200380c404c00856201e80c0000078020b0008200003010001c030743d00c5808840140e8422008182c848100700021383e01403141541c46000900e110100303280c8040100b2010900901452040c55031043c40580d2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 160009586 1250 160008336 160008347
    0x40308031501140c010b030f010e150703020415030606030c03050f1308040e01080c0102210307050c0f1f0b010513050922051501060c03020a030e22020901080105150d0c 74
    0xf03200c003ca0341ca651000114181806030803030005c00c42c003a01c200000078100302c1381442202c90550b210005018815109646d99040c510003034158010150217001c00b040380d040316040107081d1085500c2c0000d0040c0340078405020340f03201c03041c2030b82858034002c104180700c40843c07800c039407040580208031500782040c5481c840750301864000300c888840000000c1103200c1c00044110014100f6021200c0ba00c1741c48a090192545007100c00b08141414808900743c1030180b005040900c5050b000d95500300100c1c6132861178080b16450110a403154082c084850ba54903210700c116aa0302882c0c050718040d4a075580b458545041c0c45254024031001e400903c0c800c1a11000100b00c80c4403180e00c8944003407500302250344807000428071062101c05030000034524010511101030b1356164028007915200d58600303032550407402d48010303041030140482464921042c0c01100b8000740a0304016282e12143c0c00040ca00da01c1604014040d850004264810901c18029034445d40c0d0416000706000b0140e0104850 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 160010836 1250 160009586 160009607
    0x204030503040308030604110a020703080d0f0e0604290103120c08030103080405041803020c0d111002100507020303090a06110f0d1a03030a270f080303070e06040308031501 76
    0x28a00021401004104e04a001913000b5141107030300f0f01c17080a0032070405a4520030b44100d0009a8807410007000080d044202814044500c0400060a20113811040d016240034607001e4810307802c51303c208002c1003088581d083c8070f800da00c0c021504414000e907200040f14010301003d001e50464100c05090580320b005d0782d900f2164040006512941e50b071030b08554940060156510490421418006020144003601c4102d07425034010b2200c804d84100740140c4038011700b41a01c0c51807030700c0c202682d1604e13424451810308c0780c41c2e4014138001c03070380041c540c08442d03016040c4e00441d0410414042a01c4000410a1600d50400c1000600c0c8003200360031240383c420320009030b00400cae0105000400389082d030302510307100030040800d00fa400740a604260300d038820150000049000c81d54400000000040c01c800d000f5401e020500300551550700d4000112040d600c941ca05500000030400300b0b990000140031301c44e1099840508050869581810074000204128a07410480c0302c2211560707c140ea1000c1e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 160012086 1250 160010836 160010843
    0x80d1103071202030d060902070c06110708072606010e04080a02030d110703020f0105101a0d02070f050706020c060d0b0d0c0e16091a0309120c010501030b0601050c0607050c01020403 80
    0x4446502c08019403203400402c008088945881000111202e0038001c5a506540c041580c0b48050304109003524280a005c03201c0c0450720030391300d0200e07030380f04108184006456a06c020b4500f10b0402d0001406c590400c5401e030130260091001000042d0005c0e1540c4d4116130f114a0454503001851800c9207103014042001041d581001390b4500700b4140c0800a2050304c0c000d87c282c070891541c00d807200b42a0340c1c090380e040c6109820010204901102c4040201901c41030740341c62480c1500c007850040c203a800c03a200c199910110003056030100842000004001e100a0000d0032000b140080040c0807405400246000b55480307113030800c00c55441403030854000e503000110700c26803929200381d00c10b030100071140c0e080b50000c0e0b0201c0d954450f008800d15001c46005005003407510000b01d40f101e1103034102400d0b0f104503100340310078401d000c4228000340c8110718403103000080e10341c9942031000d20340c04090021070601c9401c01c4402d41505c00419a5980b00c1e1032030400326610100c81c55183d009204503400034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 160013336 1250 160012086 160012103
    0xf1201090b0a1a044b06030e0c010f0207050301050a06090501050d05030a0c03200d031a130b060909040b1006030905060a11090307032f0109090b1801030b1b04080d110307 75
    0x1790500c00320340d03060303002020000f40782041c00c640f01c02c4180c00312031005e040302c44a9032000050f0319981d071064101891407400d910580e10081c1c0d4460200e429140141c400c47c0e51161908024071a104542c4a03403401170070120340d00510480c858807080e4492151419030b070300700b1011801c0c04040c18050303150400c4a134980b01081c0300c9002c401e4491500c940b00086054000782c10640c042003040458000441c0400f001401c269110000c01d450100030b03d8200105500502d0610070264242d171602c4100c0c1c45640282e00c0030000307103001011084003601603084042410f282c141c10201159000413081e5205402180021702c1303120b2140401454001c01042541c1031007a004003104003c041e0005103541580440003007600e03407003082c03482c0b4000c001c2d62029002503094602005444065001081030f88000b40c1004d000781541c1d908044580c109030810740340c80070a08140304000101441022200c003585220034285410011503d480355808407020040000b041c88440040900344111418940d200025 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 160014586 1250 160013336 160013429
    0xd05030103150b13020c010f0501061b05120a090603051b0405090a0905030d0b1503090604120909060306050403120b1507030e040e0c0102061602030f0f1201090b0a1a04 74
    0x30308011b03511640319900d2a501300001d0f07501c101420300845044c0c6050303481d03002c003000b42e40400300e010b03002810003a90148514001c00300c41d041c1c031000034500c45401d60740300304d10789051001c0038003070301e00107050a5941c11146102640780e4140c0340c00d480980da402c071100700083d10b85000050150843c04000740a6000010305194150302680c040310300700304103941a00c6200040d0341c50700203d01040340c40e001c00703400c11000180082d032587c81000381001c10303041101d502501c0f025840210341c0a50006c4820380d40c0c44051005254015480d5101a1850201400541c0c4003030b001c00c4c004505d030403104003003a0011aa600405004110b058030819010f44100203030501413120b140c0c0c0d0b0040008503409030007800082000c5030704500d1001a4100d071354004601d0405030400000f1264040c5400b04048042441811100105840224000c02c0d040c1c81c003065104001c4100300b2a500150b205242c0307175011440c0c2da8030285100003950b044915101141e00c0c020301d1000d5481c0c0120003a922000f10b401350303620 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 160015836 1250 160014586 160014619
    0xa1514030603100f0e16052704080a021504030909180c0b0307030207140c09160914060d05040c05040b01030b0904020d0809060403060501090c0f021b030f030414030f0d05030103150b 80
    0x886c14200c0e00c0864500100b071000404800e4040d0142d40795540714640e0341c1c0001d0108074200014020201e46104680040c2055100c800c80e500c010344e0110b000901c400010000c0c0c01660041ea00300c56503880c0307c0e540d0200141d550905040c01c91044403032440c004000a44154000d40c140d9200a4010703029132041c0c456100c88546850f14590024031904402c000300741401102000b0030452031203500c1d903610103130614110119526000e110143d00030740c104600d65450503e0300544c1d00840c403c0c61480b5900d4102420007003603031100c681d5141007500d040040e59041c1c1c0c0d070145080d046601500c2d100304a11160404546910803036151640000340010000304000c019807025040300c10b03050741000203070b403441003c54060110100c054016070268591100710191100c070424409001800c60700c0c1401c0d218001d5045800951207106860344150003c40e00b41424001d5423101403040c009402000307400c0038003130001d0106001c003910400d42c81d41300061340e5009038800f13802c003c00200020000c0c214800c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 160017086 1250 160015836 160015873
    0x5040207061506050702090a02070609020411030a0e060709061101020912070e011a07030e040e06071106010837020a03200909190609020a1514030603100f0e 69
    0x1002c02c4038404040b0002440391158081e9440e4540c01400030310749440c0c6003d440b020350007883d03041c1e070442c3d9181e003074a00603030b21841103004640940003000d07140c4c540114040229501e414442040350041c01c10010000d501c040440c040d2103883c20075003106214070030418028010b80070400c6d00708507031f440d20781207260740004c0440441d1441c00001d074660b070302d64002841c0c00320300c807000f540103030b070107200703202c00a4003801000b04000c01c01382c00041c60a1601c1d01161602005a0348000410f9034100300c0011000181f1540d405481088002c0103c0b40010080d241000c07000350314502c40340d00780c410349400002e0440484802640003449458040d40320b00304131003010b100700c10214500e0000004100c050409616061107028500040c11310b401e803440501d1004100c0400403140c059850a04c0001648e030811480003400440880c4540810340d020b002d0b01042e85c04a480d0b4410000f8002c00c00507590001303500b088030102000c00f042d1060240e8030607019081c480600000c1d4007414000303510021096 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 160018336 1250 160017086 160017101
    0x306060a0c0b0112120e150d15090605030c010c1509051204030b010528060e0a0b0705030c0f06150d14010c020d0f11030306060f090604080d0816020d0f03060504020706 74
    0x41c01174451100007140b082e60769111544074190003843c41e801b20041c500701c50000c0c0a101814a5001c1000385100504505402086e0400d550303c1d5651102408175040800034104900000e00304180f2020040c2c490025684140c60803490064659407408100441408081548108070030a16161a2280f0301341401543c01d0050600a02c41031a68103c01d01148854800e0401a0420305a0160810030300320b4003505074100f0703240c010b8200c03440001d24400d50002860f8041c0207001075921001a401e0361420419100b00ea418103034801c0060007234100c100301d142c0c1410803080340d04054405141c41c040c01b0508200d00f104a1039403814415011450f00428000031808042c1e4944688c01d0300711906654211044c20084030315407044c40000c18a0602600520010301e400790000e08240800000816a500c250000f900d981c1104480504181d0401203040c0c0012840304821403440082d0342c02135482026044010410181c60103010441d40070341d12020107400094015075440318641841000303811038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 160019586 1250 160018336 160018343
    0x10c080a120b0a1d06030705060703030204030b010b0309070e090c040c02011a031209041a04110406140403031b0c030b070c170a020d110106090c0c12030605060306060a0c0b0112 78
    0x400e80095050700c0c0c4000340d141600c01411100d803a404c0c010341c4a00e007141c4010040c50301885803e45c0812503544036406030401074070a582c0540d4036419171411840011040e4030201c40e48105100b8010402c0000c60b0301c1056807444121410b640c1c0d10b0102c10b52900c00d000b0f01da160000e240650440c400b56064006002c104030020105a03041c190b00e0070b2581d210104280e0314807030803040c0710f000d0003440c01d60025034410032030320724600243c1014000074040f1250201410344a4a0028040007a207400c400e04242c11601c45c00203d00b89407a44d1409000341810141082c6803442c8141b00d001001180010000a160025030004d4280740800000c0c10428074400181e030018401d00e0310300303101d00f03032503084480b0015940c1c0034100180041100b070f18807508052070b0386a15502c0341c2c004502c20000340702e085081c10b855030340c0307140540751800c044a5244021055904140c101b5400b4006915460200d03034215500350f82d0150386240c41c001c2121340130740242004102c1d40307002000140c40e07a142c640d00ca00a500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 160020836 1250 160019586 160019591
    0x51e010b0414060420030a0c020a0b010e070f050708090103020f07052d010204050a050d050a051b1305090604020909030705030301080123100b031806070315060309150902010c080a12 80
    0x80d00d002400b03812030081c00129600820008047c5034844e042000c0402560040701d07080c400681c4c2d4071001c040309802c551081070500c020481d13007903880360911840000d14205140350210688a40949100e51421241850340008003140d030721a18600312212981c004080e07079030700f2981d4500512031020540400d0b02c14521138030702d801c0004040c8220380c2180d80c0184481d80385860305051000405414205866074001c201c07008010410510140c0a0b01c01524112006220340008010f02c18041145d154031041c6018204a4071a48c0041c0a541198040707500e0b494565031039000c00d04d035115188000745a0701001c0000542004150480481115a80121189015031013014184207034121840d402c18441c80c2010040c07003110000658110060704c00003401304428400b4545041015a01c2038000b03036503485580030420b0115070000281c509880c0c248a61200b03600d900c0c0481c1c1803055402c04a50750341c1e41c4413045a000311550812a64405200e9440340c074207050140501c024480c0d4030a0030b90 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 160022086 1250 160020836 160020851
    0xd06021306121404060507020102070b0f0907172517060103110f0616050309040603030e1002010e070302270408190201050417031005030609010608010e0307051e010b04140604 77
    0xb5160b0288000182110103410455034980c1c584001030710740a0031302029075500300051008603100b45100c901c02c68a501c0804964144204400d24080c3d01d64062034481880007554100306101141e0240441319008a102e21212403100f50071001790650301454101025401070010240049280390499000b0440702042e40046070078403030001b019200c9254041e00c10003400c40085562006001d03690301640413282400c100d200424120f400580003500440c041d41c540702403e01c0d02d80c0120700c84270f1585c4021310030242c1840b02d2039aa40007a02000340706803007094011a038420042906851074a0b0300c007003c2902d00b4a0700f002c281651080c021446015651130300c1c4084180140201c078040c540c07203003a9424042940a03000c2140c5c1001d08802141c84034110700090960b82004924044d480304000011103034540350b602400c4070340300f50703640d84150414001c90000c2080407650031000c80e190a169014408000d414a00401d0340d185d41c154010701e813091918801c107400e20103e2240509035030401400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 160023336 1250 160022086 160022117
    0x30e030f10060906080313150309080a270602070501050702030f03040b1b0d0801050f041d010515271b0f09100c0b04021012230c070c0b090d06021306 66
    0x2881075288071031506448200400c1400d001c2c90f12654148c2c02e81c603000031622415a94941241d0000c6007910000f201c0180401030348803000c41c131000a1076408822080d4500e41000a9220300c507500c00c16042c010081340c2c10055450034042604400e145405403999130740c640d030f8a55840d800440550700302c52040c1c035084440f060000750001c0d5481c01505c40d41e00503232900342040f907040900701507250040e450b4808040c00c80041c1d6607a00054000f800089554600700da00c6032614140004418403443e02c4403050000c030581c4249160490b058101c40114550302c0d81c01d141017403485550700c0c40b03082c03e00098064420000e500513090740401210700301c1d035210402500b110403082c2d00501500011111010500524264112098041c003e003011036075074400c2c03902c00c8122002400103120b41c907003819a40c030990407125941680310000c0c2c0d4075141814840c0c1c4940341609154001c50306441000074070b4450350ba0324860111940c3d40d10a0055584168001e40c20955065920a45020840e1801100d150 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 160024586 1250 160023336 160023343
    0x51b04030b06090c070503031003060b0a05010e090601180e16050406020c0111070510090e060427050a021201090302010509010605033403050a051002031003030e030f1006090608 78
    0x46076080344001915407a031004028001c0300281a4145503902000407200180302440518415030f03004c004844601d155041c00b100380d0f9880415a8480c807000c20007400341e40e8000d41562203058054410f00559500c00c1d0042c0c1d9031017218580b4001c080026130000030082044280c107485030000c2481481c0990381c200b01074599000e9809100090380008040d941554030030038548500c00c66180031242e0850742d8002003030300c03c2d0b80e944180f03000904c0e10400303126211807508043d0300300d101035070f08005814071000e141035a0f0b080f800c4212540006c4005000601508200030f50760f44d50010000c0d030007404100c12840c02825204000c4015500f420001154401c040c4614402c445020f4043c006161440300b0440d83e50154454510600a84034000510192019110720180d80300d00005c0c24070f80741e0380c2407041c07800400140c0e100384180108208000140a007200004499060030031911120101001034240f0189014103c854803490b10140089446a04100100d5120120410009446000041e21f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 160025836 1250 160024586 160024589
    0x10b0a0501091205150c0426070b0d0e0102030708090c010c0b01090f0f0f0b0a0e060607060209010c050a0620070218061219150b0a090c180306051b04 66
    0x1203108031608200c183d00d004890200390340f0a0b01500d01040200c280095812001e0300e04130003040010805005258900070180381e29440600c84c0d00e00600000115541c440460040f000ca143d800310389900324543c50f07002403600d00c55840080d51685405100100103c9040b5030b40303c0144a030801107034085d4001c15000b80425000040d102d07540e824044004040c3c0000c41c1d003e0701c0e01e40c2d114041c0f070704803400b44174400403400300369400300d00e941d01c40c0204001c100c8503070415aa0040381ca000c0c02501d546000448134050350054000d6121100400180c810300706c28440541307980a03ca00c42c5081217450f50000d80003d41500b240911042410150302490042e010000c0d0081400400001100d0408807c10761040d0020300d015015008500300c0342c00c1c03221503418081c42e0008641c030744c010007440f00403c03011a084100200001d036030301000a1102040c52003002a955a50040d14032164825207613030352a0450014036a00c1c185e038a00d031000040004403005d6018190207002c0b6071411041c1d004440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 160027086 1250 160025836 160025839
    0x200304060c020f040b090f09030723120c0a120e0301020a030501080d03020405131d03070b0708010506030405191704030507030b010801021612050d110307030b0a060228020405010b0c010b0a05 84
    0x14984d40c587c007440c4204400640101c00c0c80c4402c2c00408009502c000c0e0081d2150700da407801804000301815103600c0c082d0031507110700e0700038028448c080b4242d600113420f0f15056000705840302220400403013541c0c80548005090382650000a0700800d42e900348d006241201d0382041150341e43c03250b0403070403130072801540103030350f8490b0600580c2550b1622907080b11182c088050600101d40580c1304866295070b021540445103421007804108e005908001c04074010b00040c0c0b800c1d072442c6000d640740c0380c45140c13107141140701c3c2c3c60314108101400500c520034020202c0c0c6c881850f94131501c038240039544441e42d00c0201e400e181c5c00c02c0040740c52001070090320300c071008400c101040703080c903503448200d0035044603102c40421406101c0440d410070140541e140d801c00e036994081d0f59090505d030040c150f80c00180190700a003074920041000650000d8101650304c000c45480a1040e1082000d140000d0303800c4000e9846030904001241fa900003200401a1181c203100030404240c50000b4410f81995510545 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 160028336 1250 160027086 160027099
    0x4020a1704021c2003010504020a090507111e070b070809150d110301050f0a05060a11010204031401061809050601050f0102100e0717030304050d200304060c020f040b 73
    0x118502500589255001803009261940003d101803202d2841c1d19142c00036a080075078480400000451500380b030a100c401507000744402c0c60300760081001d801240c800d2404059403040000d208501c50a05111894440070994190b000044541d04c6800410901c00d0020300516000046030329180c0100d945076503102d4090360070a8000e07070400080f140708417282c200c0748102708000411b0b8150b80c410790f800e038800040095180c0d414031f024400302d40707920002c1d1801850382d1030080c403607655003901b40c1d40309410390314090722450f0b050b0355482d0190069500040031401100038804a810040d04410140c4040421006102ea10f00043c203054844042e80507103180c10400041c845410301085540d079660040c012500c00c01031100d40003040b40e232412110003c94104000510001041030b801c0410f2800c144011401d5080c192980794036641003908020a006c40c011030209050081c040046a40c540755080e603407580c3e0780e44c0018240b8880464221320507281d00030458071700d01d071611035140001c0004e07000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 160029586 1250 160028336 160028357
    0x9060c0d050307120e0a060209060c0a0602040927020405130b0c040e130f0b0606040b0d090c0503010c0203160302070e070302090a1a07030c06021b010615020309100c3e04020a 77
    0x6507c005d5015000301c5410030f404100b85540302d54100020203181d03200f502c00683e228a00700031b02e0201c4020f4810344c80d1026998030001c0c03482c1d031580e081079801901101c0000b11900e84882070780301c00c408075000802e1181040c00f00003203918107138041c10480d0700454042c0000c3d619145001360012070140c008000c1d201c1c109003040070641c54245554400310142030781d46415152004a1071607005102d60150781d5807210b09090400020460f520011304066000b4400000e48400194580c014800c0041040718040c402c10181882044614003c0c4255503810700981401080100a0351100c500c4d2401280c545800003443c1051840c00842d000041304000c2c10261590b40c01c443c214130042c400e0b55001d400f80103650400300c2032299026031041c0e001c00040c40d40d241090510000310003421a0341950402d000700c80c229141d00c82c50344200074952500b100e401000d03141c152090403180b080d404c2c0040c010031036411980a6203261780000c0d100c02400c104d010711103500b000140d1095200e204005400a0706 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 160030836 1250 160029586 160029593
    0x11030d091b05190614040905010801020703030e2d01180b0103110f0d08030615040f060e0a050a030f030212040603140f04030909021c11040608090604021509060c0d050307120e0a 78
    0x3175000b000d9100810a520f0a55201c410400780d0303100780c10500207a580000c0d500101a058455030068034460702c0540b5000d100401d0388090003c11203940402c0d0041d040310805401020750101119041740c210071044105075042200811000340001c480c0b402d0001400d9085280040b910301640b100200318990070078552360341056581010f40002e4000c0c0c080e58a007031020141001400107031a442401140003807420b6001031441c106d0328611405114107100c107104035200d0350010030550350813a58001d10203516140480c980890385400122000011502190650340741d0044407010a250800f14120303110601402d510100548005000c00c101d40c07003c0004001c66005081d0650402a8152801031038015007000c0d42c003520014080700e9000101400001d030011801381c1c2100c2402d000b02220300d4035a0115048240008100e41400703c04103a02056540d07040440b051020b43c042034900c20540d4250181a54100703540e09000f184c401b0b0fa0b02540418144600641e401400c0c0092250044c542c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 160032086 1250 160030836 160030847
    0x105060619020a050d03020d0c140405060702013b100f1407020916020607090803090112020408011406040b0609010c110105280e09070c0311030d091b051906 69
    0x41c0724000354003c3d8128800869021301c1114400307003c0c1e84025986038840248401210078150480040c881501503a10920f0400002c1e501551429605146c0c0c4041500068032a00340010440201c80200117401c0d00b081200c0807100d000b03854030203035010080501410812201e05804144001840c0c05a40001e035501c24034a488808490340c03413241c54130006401055080300200c4200020f500ca441c0912503107a41001003036401011440c01041d040c0c00d02c0c82e02a140d20801d80c15074100010405d402080e85900c0e4100c40c02840000300821020042e00b0016003d42002c03903100b4800c80c9424030340748a604144d02142c00c0e083e0169511081501a41c2e145141008400d5480c1e04010b0240b0164440b070890b01c5600300b0803605000e80d80d428407030885006040c440c0403a1041d00412412041c0078200d50012031200039154181003141c100c0c500408501e19500038440800c204031b0070700f03440c001440500780c1800521410040d40c801040c4e180c4003803003410040c81e000101780b011002400c00c22700e4400c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 160033336 1250 160032086 160032127
    0x7050c092d0a0b0607060605031203091011040f0909060c05040b09060c0a02090702060405070605070308071b06050a0b1903030504031506030c0f090c0809060a0c050706060f1701050606 81
    0x2c034001a10603080c000300700240c000e55000c07598241e0350a0144103a140401281a02c47d0281c44100c2c91480d1150720305441e00109032a1401c0d0703e0311514030003200d400c0c22081e54080c0081180203140595150b0450b0081c0811000c04d982061400c1c4034210703100d00ca5000c0b58150f500c0206050300c0c2c1240e04d41400035550240030b0108450040071030b403100583d901550140202421384c028045800d150030b20500f010102e9000380c0500408119410022750010710301984001c00f400e0541c10781000c0d598000410600e02402016145407108104000c41070360b0014401c6041554800c4c003031f800018182c41100900d00014002c140240710420000342d822445134031041d452440803802559a039030f441c08003121074110b0210a01e00312014410307015907104d0555168541d1611821074141081000c3d2107046c041c210b8038045445418010b0310b14000c404079050b0780d600040801400b9940c1130602d041c80d5907405680080c9046a10054010b14140161801a140141030500e03150201c1c0c41c07030030b504840 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 160034586 1250 160033336 160033351
    0xb090f0406030209090a200a06030914120a0306050f03071a0c0708060a11030417030601030e060f04020f01090b040e06151b07080a05121e07050c092d 66
    0x22a10040b006807140d03c4140c4c02001158001c0085000a10f850711204086000b15883c101e00800d510111380d0b0342410b0b510032035440703040024801b909810302040c00e100e40c50385074110740304402020020b542c80780010035000d0302c1030b5410031600b6120420041c1c0c003081c0169140d4540c0c000342c0c0c1402030480d4001c51440326030202204601e0710155101e400d05240c001d503c07640060700020b0400902d0141c9001c0c1038102008a12054503500e02a91580300c0c11404d05010031011381e0107c00140603900076132010010362100c400701c581925200702d107800c1102c0d084604074080c0142550031000c40d4018450708094078403d810f034a05007400c00c50780390240341c4000c04030ba1703010400711000d01c00b00d0000c1c00100b040b013040e0324207100c00350004a81c16150408035030044110340c1c8550400000b083c0040f40d508611584441c007940d0b02d030304d41c4180109440148142c2d803020880006d060040050001d090910020107455108450b5540e2200301005100303e0503616400300b009520355030341102c11960542c0600c6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 160035836 1250 160034586 160034591
    0x10020c0106081b10090b03040308060102120d09020a15080f040303090c03200603091509011506020715020d1b02040f021303110609060a0518151b070b090f04 69
    0xd85401c8140f600c00c0715101c0022601c0c912001e140b0506102c070413039080314524103100c0d4180b03140c0b007420030580c4801400034041212002c0815501da10a000e11048610510512078030f800710750814400510358070794202e200d0f0b2082000040d0351500501e4100c060341c010340380c159a5070b940906007160180000e100300c0805d5030304d05840e00059007080400c8040c41c05080080c510000d403c0a1406050b445c400d8030744070720782c05d000b04410a00009100503140403685004002a1184150a800b411078514603030701c440b03401840850b0007036000071254103c503140f02c611400c1c040099000d0ba00c1c5c00d40e40302c1a00000e000e10914001c81c0c4011301500da18240b000e4000644000011028412600a044104100401c0c50420030030f00c80f80040341c1c12000c2c400ca80b41031501c00f19800040e218854045c14005101011441d036503002502c090b440000800030b408142e001111000c80c141e40d912801c90700c0010007028642c149a044000b80d40c00680795140e441a14000250040000280d0380d00740e1346d980580c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 160037086 1250 160035836 160035839
    0x7020309030102040b040810060b04050f01030905070e09190b2d0115020d0203090f0405090709020307020a060515030703060e10020f0703170705040b0d0e0a050c0406061110020c0106 80
    0x8600340f0080c001045400e82c069115420080d0050600c0714050403642254141101800742d518250304840494404450a00300007240038010380152140c02d1000c1c10034000c50703030002041543c030084a481000940e095808241181c041c004c0c0300c072010701003d8504d01a10b400030b03620400810601d2610708401c604142007003a500d032101c1000304260860030103060045280801190104038461840341d445c00952304110496000c911b203032440090091081e13440d43d01040c2c422100b44582e10203000380d0001990380c1d2600700006562043c00d81000c603031551410001170381082c161303502040403903c020064610341d0700d1500e4100107440e40c15405515030107803110030b01c40b00c00e040c401052880604a106603c0e5003a03400c0251203040d403020765008103541003080200726a8003500300c805070303200406c54689401c2d44007032907401001300011800207842910b44660900100080640c0030010488050203110b03242c100c101d560000a022003d03c41d401800c9517000b803026078015000c00000b80b0700000380203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 160038336 1250 160037086 160037089
    0x1202040e0d091401091805040809030a08031906031a0c04050a0f050a0608010501080711070b120402040501081c051b120301060e030109030516030e04050a06090e060f070807020309 79
    0x50070007022031011400c1d18000f00410008103445005008003401c202e038685141500f8034012420200e8001d01c0c943d03840c0001800c00440303406071401800003804a4422001500d00140a94801c0e01e04d940d00c0421b40c0f031907204c0c030580c5014040a480d030080d1200608039080483e1a00a403010b084010303103242c180000311342c42e101d0548000040c540c55201004481c6010b0070f0001c0b02c0215040303481003103950401400a66041948641c00c030f016490012644040f08030180e050062a1300040c41e410301c0001d629002c5235851480c0ca0285008440420950f40e80d01c00c8950749801c0d000962141e5118149080010f6000c1c20290a14001d500104801c3c4a031160001d41440c030510344490040c1000302c0140314042c2d11aa05044000b01a0000c004404660320007074402d0044041c54000c60045214982c201445040813001e240005041446a82801003980000c1d0051b030241c0d0040764500041c00c0a90f09001480600411901444c9001a124444200c8100600800c048203621040081644c103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 160039586 1250 160038336 160038343
    0xc0f170c01090209061801030212070b0301170d02070f17100c0c05190f08030c28020c01020303040803010b0703050c0a030915020c090a02030603010608030f1305010908071202040e 79
    0x100e62080000034546096104006002c01d002e810140108001e0302c40d2502c80c01400e54603415690112407024500550b0440c0c1031408940d13030401940d8210100000a8003200108400540c00c182c4040d40d40003d070710082240c0e1420144220a101040e0742810440145609284080742e80c0e00c3c010342c1d0038030100d07400310b03004c0d606030b070a102d4005092241c02c503007800401e00840e610711950424010821100fa2500840d6014040c400b034292913001022506420382c8030101c900a410021612941d855031030812084040794000d440c0150051718030a000c40c0d803010040b03a1059034802031440c256401c00c803400d901500306180413002c0c0041000b0b550740701d80d020480710780014481e545195038035003000120444041010295029580501c2e0380003810b0b9220745460b6406002a90f00603129900d0400085c0548103a5100d204140030002d1440c8100c54844020b0420301111989414565510001105d100034940b05003241030700700d000144909035901c0009180030340000c3c0045035003415010050709 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 160040836 1250 160039586 160039597
    0x6030c170c070b0903160201050f070506090607090801110d0b06220f050603091b032401090e060c0403030302030408071703040201120209030c0f0a080d08100503010902010c0f17 78
    0x4401d40208012081185499040d5446413180e0003850400d00c041d80c5892004501d000024140200802d0107409400004141c4420541180031115241402200707252103000070b440d03150020704049408110340005006142c00310b50030204140ca081b182c02b0301c20f0024000c1041860348107500b0005038000c0071070780307500701000703c100f029031030030304d8035045000145211a03800240901000c0c0308100c604400403820f085154001d11140c140c0c040204006801c0c1481c06017000ca0554121400c00c800d003c03283c802070b040c0c80960300c0c100812542c08102e10f554000803180405211010441840002d10a4018540042c46400c103d42014090303651103284a9000c164156200740c0407080000390340c0d11045a450b443c2006001310700c0c0070040000b094842d501402850701a1440036560745040c0c40c2d0140c600010150907003580c0c100075036140000d12008098480348160b01444d08041074510301807050480c000d40c140c443d903200c11032582c1c42c80e20041043c4001e0303034807100040d602d20300354083c0401000d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 160042086 1250 160040836 160040851
    0xe18090a08220e100b07110406171b0d24090305070302010510050a0504020a02070b07060603120e010228020307060206060328030c080c030d05070e061306030c17 71
    0x410782d20781c90255a819080030303486194003003200740c180440d803014080b0b404143e41907074102c59070f144003e0500641d490f45412032150007610f0420005043c1d120b22520030f0007241e00109464086041c2d180c0000f03100c26070412942c1c409101d070915000903001e00005030500035107100c001244031918200004503410308000717038041140010130310101982171166641c00f00f040f5115000c0c03541080007140d041e0803103000d418083c907070014200c014207000304508001403904614050383c880541c80d0020107005503100448107152825019038645000320401081428180c0c000d0060261110301642258032809076100741240a102400258034140002e0000d019950020030b5a81045000e00d850b254220240b1100c8180c4600141000d083c9481c03901682501441d05442684860600c0b800c41e01c10301c8044030882c840041c10314414109030b00894800d5445c0c1c1c4543c00048032040c2480f820384504480342e00020240e400902005020361b01c00f00401001d803404800c017440c0c041c502106254140d8911 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 160043336 1250 160042086 160042117
    0x5180c090d05010e0a0b16090603020903070306090c03111008060405100302030f06090d020f070320061909060f050327030705010b0a050402040f0924120506070e18090a08 75
    0x2021b1007101c910440d00424131710303428404102003003402440c90310309002e40801c02d5000520034004d59410412940555000241001803107581d1030550410401e0784801c031240d191800096140f80703803600e120013502c0c10ad521a042c0d141d560700c00304802003c0007803c40300000001c000100240e141000390500f000d0340380004003603608003280748614107500d45420034119407055086d1030721048046401d408490744a6090b8216000c5186106201110410710b03e40020010403607140000754941130390070146042d00d0301c17918540c9801c412030300101240201d01c0814010004504a10030040c04440c04411103c00d10311a2000c0501030750551b4031204094035160745401000307195260906600703000740f00c00c07201149041e25000c281540d4103100d10913040500d43c0c5820171250701e0301c21b03060308524a2034110340c241c02c0b686810701e00d402003003003c00940b4a442440d0004000c1c038060026504c040000410001c1801b10440010031182c000601d010700e107006041d041700004103804044e16400c03181c032242 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 160044586 1250 160043336 160043353
    0x100504060510050406060c0f050304090c0903110306010609030f0f05060901150e01030209010608090f07030c15030501030b27060702060702150103170d0b0d030509040605180c090d05010e 82
    0x221503102c0c00c56000644105e1a2080c00c200f09500300c0445951258011401100c800b518248582940103d60141041c182044044480d15600c81186400d40b40b00d0014002d80c1c1949406060741ca807024013840001c6244d82609002203075003e80b0940089208040c02500100e035591039504285047e036020a1581d1111a15811050020030120250424440c0101a50300d9600041e5001d541031203582e05103c0c4400126044690074022121902004400c69141594a113440001104644034407a80d0850040c000703503099119002e600d04990b000850321480e074882e000c1010581e454039241c441c1e0380000038141711101c4803d101c41803103040580c028017603e00d448400079040001810084600810480c0144001016a001c0244002605448035101e002c411107600041481203003544c0d10516550086d4100b55001d80107040218082c0c030103102c4199150f09106121000201314125030450200007a03101d42c514000e0309803c04010410302407400c464071100e0860b40301845882254128429 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 160045836 1250 160044586 160044601
    0x613080c070609080f03030405061303140f030a1113030204022a03040906080a03090e0c0d0207050d18030c051905130b09060f090f061f0804060c0206040305040e091005040605 77
    0x1600340d117801c0d07014600e03614244e81d03503030b454400003040095110211803e074400d151088401d2035595181c101090360710b00b015518100c03590403c0b2948201141410140b0255038418001d58542c0c20304210000c10180c2140d003004040c0d0001500d101500310503010b002164aa010004810030000c02e01840e41d0308c1c240003010f8242c4130b842e04448440c1c2d100712a20070019620403080070132908211081e40e129210520780a07442e1080f141d0441200340003160341414080d0100b41501c20821640760903030588071550036060760a403d44405003031811000810406401c00a070045640305a0300100340c1c0f0703541c0740c20020b89861400e10209070480c0e07407911140842d051451505400100c201d030078400e03419040d0002101260014008441e8046001c0420b4003030f195034100314110218000c80728403c034054080101240f604440c181c80080c24183d0020b01c80e800420018001d80c1c0603134403949030a0074890000410070000d001e0500d24840c100181c1c41c400c040348503160203184540c2010039642401d00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 160047086 1250 160045836 160045843
    0x20a061a220c03090201050d0e100c0324050a0303080c09030703050604051209060313020f10030b1906140c0a050105010e07030506100801121e080a0f050a020613080c07060908 77
    0x80c101c028507113004100f001503a00034003550281e0364000c40103c2d201e0007140e103803405c0240001d40c00c2c4005081800d045a501d130540c101c44d0b20403403c150b0058071169240003103240605d8500c034042e0080312a29040c00400c9c86210090381c4018000189454245241c0210f031400c0c5180d8025245600410188400c01005024012004801c1a0803500f041c0c80c0400144131440080c007900958115042d41200715160050f5448007400010028408110f032080b001d80588040b1031480d1141d4000360000e903005400c3d1026500b035401d140c0e56840782c0c41890324007091a40c0301341d8210380d03c0d204030440c031000500d003402414040d0104010451403401c000d0300c007400b903c50160a03a841445a004100710180e030140c801d42c11074481d42c0c841c00712860303907041602c08505403170b503901d07481710009503240c09000100703005000905140d9103082c40c80180c83c0003103405014181070840142c1100d00403c0c07803444142c400668540c000c02c1d440c0d01d802c108401e06494106c0c1c5501c26804100018000c0144c40c07400d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 160048336 1250 160047086 160047101
    0x31209090b010f0c020301090215030a0e010203090316031403010b1b0f120a0e210c09010e06090703110d1d03040b1b0a020a0b19030903020a061a22 65
    0x640c09210703250307090700040c1400030b892069000300140206407000790f6809411081c1740725005001c1c0061802c01c402550b11076442120380c3c400d501d00300418064405014421244140d150340050341c02d2800c20b04c054110246160300070b500b000448034207044a0b40301c040c000c40c000e11a9030490744d5035813104001c1c80304040b141a0810120741040e040e04003070a001103403009220164030072607903940c00b01c0f000948000b01c02c0c20400340c01c821161080a1520300c002200804c1c8a00303c8102c034416000001001000c0b41c0074001c0000c2c0c100d540c0086071560038000c01301a0424458100440d004407150b240071030f160044049005444d0b2601c10030110400a42c501401102120014501d800e0424884080c184150300c00d2440c4080d880306080002d000611442207019401030201c1a0700355280c1148026401c001c2014040c0660303070481c0d505047c000d1084c0d848660785600501954410b80e05c2d01d10040c030704508004100009481607a400d9a00c2c0301c06143c40b000350107810300340800150100400c41d001e8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 160049586 1250 160048336 160048349
    0x903080a080108190305031f0f06020309090f16050a05070204050906071202040f120218010e041b18050907050301050c1c02160807110a090e0d030b011d0f0901031209 73
    0x107031400074002c61b030b220301107903400307000c418104600d40e81d84144155002c001c1e038028408040c0b00c80001c107034191302000400c003400d0110f5102d0b5480d01d510300809100402a0760018043d1704110078101281e002c0ea01034806010f903818480d007003109940210341039401c2181c4801c0710303410840801c44080d4104410180e02c1c0d0110404500f450b043c0700c0054408061409189110396829403031808554030070303119400b8600c5581e01d168240d6980c1220000d2004240c1c0d003100c1404041030100c01003062005002d0445030203081040c000c1302d010130000000c003405044164103000700d20021902d034609018040c010004c602c134040c0c1d0b83d0107941200100c81d420620b001070041c01001542103044818901064443c0c00000c45c65039110300740790103a003009a8018541c1c02c000c030329100181c9508282d0140d080c80801d00195402481445c100324211462000c840f40030a4607000d040c0c54a50706003043e0035070124040d02c01d040144107640000d842040913031040f0f60702800e984108012039844503592008080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 160050836 1250 160049586 160049623
    0x62115050a06061d0306150d06060306020408120a09050103051306090b150f0f01320d0f05060d0b0a0e1005070f080709030201051e03070f08010807030209160903080a080108 76
    0x10380001d44845015018038451048100da0340c4403948e942601018480c0e101c40100b000541d01e241c200f02940152040581c1401075100d00c0b03440600040c2211491140c0b5610001c90d9420400150300801028201101c05488a5800d00024101e482180402409000c4e0f0f00c0252514002e000c0102c6402c1c90414001c1c00351041d040d0072030310345041c08100342c4000d00313200c015038200340c1800c10031165013098603411644200a0300000d1103c4401484800030380f810921811914003c40c2094400030b590310f60300401451610380101b801d03a030a4917009108913001080c2c2c480c01c05502c40c03810b5019092010000e507a0002d01061a80124540c040c003481400c0516882c5040100645541820310010341071200014908110305416080e04d0050b064480c02582c403400d100800070142e40642440d03001007291340c3c0011071842800035040045a0b4004c1591203030303543e00404e0401e040c803140190400c9c000307907650110004000798040c0035090100d94800c021980760030007943c40c0915030040e100a01c03c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 160052086 1250 160050836 160050887
    0x3060503030d090303020913140a02072105043501090203030708030403090e0412020105180703021512040f05012a0302090102070803042304062115050a0606 69
    0x840101c00d0300c0b15404203040000e80c240140c141600603214030650544d10240d10141450310550683c08a00c40d1101c103e00c003400b03030703035617401e480c00300d1180742c901514910004c081e082000c0c0a803480b007108155249000d60500380d89294001500000c4102540907080d031583c3d0151140305001d80700c1c4e000d50048000c2c8250901d40c2c0110f6201d00c10031902420a0500100103000e0501810698000f440c2d045d03c500001c2c0b5141c1030100301c1d00c09442c04403006500b0040420b01c488540288a02c00e00000405418490b143d0f44c200040010142e903045122102441900940303030881010600c03a07070003000e002d00d00c100070b85402070845901a0920008040c28445406081d2200310400c50051160800507a12815000180d10700042c0c1c1d8401c600c284000a00440d4001c241e00618264049500204a10340c040c001000181c440d103000c0c1c100c904040314503507102d1045124202a800380944900343c500904650080150f803822202c0303c20041d2903500070003000d944450030340408080c141c1c084a094 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 160053336 1250 160052086 160052089
    0x9120d0503060d0305071a0108011a01090501050a030f150515041505030606090a14040f090b0703110c01020f0a09080604020a031401060806090c010201060806090a0308180f0703060b01030605 84
    0x41c040500074900074001c11074500c2c1018020000c98007180c1e0003c0342d000680d854410111448442405070702d00039400c2407141441ca1042c2582280e0545058685101030340c03c1400465094108484070400c00d610b8000018800f407140c821031484490030011044418101000c0c01060b1a00c0c40d04205280e00c20002042a5200e2107200b12034000c0921340300ea074903151500010450b000f00000c150344100c1d1008002280d1310240e0303580605031004d5406111242c07421070369504a42c00000054015608d10000800c410700c654841e40180030303c2070301d04d2304110013841202d007240c202d40102c54540302c2c0007802c0601e050300540d0f104000d1030301500400b542d250a6010071325000c0e692000401894030750600c4940c410003900043c0c0038007201c0c4103ca02900e0700e001b03644e90b6a0700814405015505c2c111020400b00340c00f04020b80305420550083c20b030300440307a604441d0000c00508500c04d024810a039020810301c10b1080c6414602c03103900034106c0a081d4104501110442000681410710300001081107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 160054586 1250 160053336 160053347
    0xd180606171501060e0d050d020a0b0a0603020d0b060a030b15010810051315090c0305010e06030a0f0f060b100c0b10060c030531080708030f031315020c010209120d 72
    0x19070301315241860b240705e90f40e004551142408070009156005a400c3c08004690000c2d04142150142008000740d45800003418211103081c00086d4015407400714580114401c80103903600258090114100c90f5034989402d0703442607058030054038015500e685c120556a0091425400031051102581c0300761510340010350600c1690101918103031200c1c44150b02110019110004040c800400d0000c0768500701e004004000c00d000720b203403011568020840d107003400600e07201f030036a0007212270200c91800d85030b1400c092003400049903075607290b081c141000d8039400001d828885880e1900c00c101c981520f402100d19030300505426008140303c10400005034000c2d080c050140c3c00d41070180c0e541243c110510510900035000800d120000c40c600038180300c4c0200741c041190003a4042d207040c1601c80542540340e1141100d40c000749502400850351404100c400c10404ca8416010944444a1565120166040001c5104150f50b001c41c80c50708030304004008401c1d41d00002c0103058104d1001602419 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 160055836 1250 160054586 160054589
    0x30304150c2c0409080c0309030708120a05130b0703030b1201090302250e1509010e04030905120309030a140d02060f07080601050f191b170d180606171501 68
    0x401c1842c01040304816101c9a004004141e040861580c2e24507070440425625404003074150700238400d080000444100101c1d00303074030600c008500203140600405048a0507001f88120074080340003010002a043d4003000100982480f03928042100c6440c03a007004001c0744644a0100d40d44d0600c3c00050001c0e50108025554005460b0b900a455464003040300d0300001e140c01c0301081c00700d00c400b03225070b42800d00c560f65160b0a080b104a14141e0300c2d00500b1504101c16600107011440405041c40b5510b0441d0490407240c13105c2d41124103100034400003c1c90540d50b11004e8468203c05100c1005c090018400a220402140000c100b10304281d8a0b440304910020184030401c502100403a82c168402d00c1195520003003d041540c464418284d0280c8000702c0c21036040208035001e550541120f41607101901c0a178210158a04694070b006901849504c0000c0f480a41a6502e103514000c10048010662160203040c00147c41410b05c140011908103040c007841959001e800100c02081d80b0140260 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 160057086 1250 160055836 160055897
    0x23011b0b01030311071d040b1e01090f020c06070809070503070b031303020a1406091006140112020904060807050a0e0402030a030f0e06030906160302090307050d14030304150c 77
    0x801d480d84d169426040c0081c540200d030710000c1c3c16074a0b6000070079494081d40100e00134040c0900c5d81d00c4102445055200b1500d540018020880040090b0394840d400f40c1c5c900c0024030009450b04400262007802c181b0b00b20380803004a0034410502c032854a007000550050102500180021800c0c1901000c207400001c0c18480840e006019400c1010310900907500d01ca0f81c0528401c030b030b6401c42415076480303034800c031080696849281d901501040c0280a100201c9a000c41402c0b10010050300454045020010301c20049400300903044442d2264810710009084040c050b081035800c1404000041e03482d940124080c45585041c00301580d40803609038009640348c1411084043d210304141ca96585140e1000c0c6e10140c00300400c0600100402e62a20401301c0c00f0100540c040d044030160308900402da001078044c0c0c030160052045007040241d11000c2401410212500c40d01c00342c2491966100701c804845041c500401c4607540d0000340955144180141050b1a2248032a0f489144002c0301348401c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 160058336 1250 160057086 160057097
    0x513150909020f0705120c010c03140a0c2f060606120613090209070507060b01020a0b22060608010b03150114060703120e160b0f03070807050423011b0b010303 70
    0x10f15240d980c02044600103540082650801d00d0807260f01d89207038100380c909039195400c000001030702c28070910598070b600101c15a02006a121754030400020301c142104072040c419600170f80b003420005004107d03641c81030305090350180d156400059040110181105001e082c092100c030942c3c06108402690020040d00c02e04180600030140101900380040c02075081512074003402040c41c0d0000c0240100342c044c1c401803006915171401265144011000680014400408942c005a91032281ea503c804e502c5200d0a40f02c1003511070808842c501e0307014003038aa5540c0d0801213241400d2022884960046030410703110b6240110700010360003052509441100c1c002103900c20980203411048100a8020307041228080c0041c01aa032015242a08001004c1c00350000035980001e00c121410519a002c3d010f080d5195070100340c9181c00007614000920600380404074100c1002d00b0780030304490b00c03002d04088001c0321780005020526500900404070ba400e0050401082c41509d0f200c0c1126410310300f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 160059586 1250 160058336 160058347
    0x4090206160305030402040c0215040305030a0b151806030118111b07050f04020f040e060a030b070f0f110a0f1b060203030405120a020616021c051315090902 69
    0x1049031040c91142407000c0e0952015070203141d4404040c0d442a4405d5800300a800c00c07401090303a842c440000c1c0c6103401c0c001e44c40002c0000348240d000e19003098003030001056480d04000000d090321150304d01e146401e8808a44048007542c0c49100014210007500c5091a650502e100d95031300d0b5030651300350b4018507104d5235078660b003240320011a1a0004025511440c401610070050b449125a00c2414801d03095051004d90b81c0c0760610880b54a80355100060380ba10346080d08108035007000070111755101c005480000081106508110322840461740c41c10440d9140400140c2043c0400c01680100402c595070341d84a4540051400241504034105007102c01c018034200d5910700c0000f009000d0000a004000f0300c8603000006580140d10031f906841140c94a50004003150203a4460003006074004400304184030151f41040c500c0211510680c1d00c030501100d007a03a6440c03c2d02d1215400520f0000b8030300c500500b02c550303180240c03140c2a01c0070544080e038100204900528016404440d42c0000c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 160060836 1250 160059586 160059589
    0xa090b071d0d0305090301060905060d11030c15030405060f01030309211401021e0f0a0f03020c03030412170405120a0516080304020a080102030108030703110f010e1006081209040902 80
    0x120a200c0290040030b2081685503071a00400c150002100d440c080c2d82080408280b44d40180207040c4208805004403000200b10344600201345540c541080c1c06009034032204516449841250b240d0000744c000c41c1e59030f03080507e841841c003d4011324414990155800510000c0d0b40701041400311040300b10382180050740c140da5140c4a03511044020a104c0c80050b0000c8112010340251443c01e06030613110f19003105411000c4020f01c21220300203060b00c0100907a0007d0381c094465001c00380c03158600142060005290f0a14592050380d00790f810b80d8542e010859000c0c0e008030401480d80c0c2c03542203941c05080a9903103681e1000292441c1a1000780441d0042c1000d02c900c060303c0c959072002c2040c0e91019181d041c542c40c0b6500c1610240c2c0100302614010943c1d100500031241264141d800a5140040980701194090038180003c3c806002d442186424400c00740502c1d000310303540d1030103814a2104100a0f0088454550010103d50410302c0100310a80c42c0d0400d9680000b419a408155545140b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 160062086 1250 160060836 160060877
    0x2120609060406050421090f0816060305090a1506050906010507030914030f0604080a030e030c0c010302071e11030d0e0102070308031305060a020a020d090302060a11070803040b070b0a090b07 84
    0x2650503d1030010111b019003069000034048100d030550704600071007a480d4100e2640b52040d403540b03c4a241813042041240c64402d61003240d010600c1402d0719408180d550b2a21451004007100c1d821003a100d500c01d00003840d0400440d60000c40c2428051700e0710500ea6000ba005101d6807080e40125800300c500440103032000e100d082c51408030f400548649242c80c0c034003407481e82c00c10310104002a2500703000680f800c40000407100e0683c801401410400d036802c00440207544400740407183d421003514010304224440c400d007071103544200550307102c80c00030304141407030461160412010080c0ca8460030000381d0b004201030003981c0d000754074a9625660010000040f0b041c1c0132000384584070300c1d020481c2c01440342d406080c1e480942d509036030340d030030150000300c1e09d4400d54040654411403c100300d0f41c42602500d82c910310f604201d01900c101c213507203202180c11034005911083e0119000605a01080040c19203207510003100c810400441d10f4548481240d41d0005003c0c0d014441d1003501528205443c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 160063336 1250 160062086 160062113
    0xc0903030c0f05030f1b0c0d02013926091c020d081b07080d0801062709061406030702070b0c0703021f0314090309130e030a080103021206090604060504 67
    0x2800c0c11750742c44625058400c0803244103061908180981c12040b94580342550511565a40507914161001c007207072150f4898280c0e107203d241c5201d02d11000c030a083c100310302c2e00625060103040300950f6960ba42554076581c020b85500d0546004041000484560301c210308200c1d007140d201d0101000d510b50344081403520f000c00c6030150400300c000c604241010a0b07030403ea0a0071102034240d90360940e07901c01503580d801d562401c4001050840f0014040c90f841010000174182c3c08000354000908881c080400c40011500a98000ca0300d50301c0502000001e19640e50780b4220a8510764071718541440029181c00c0d02e80034220307001c640000ca246141c4810801400603503002415610a0800100440c2c01000019039080c046401d101ca10400b0300c5540301028425036152000c2c501d480544c10400c20468809034840352100c1c1e6401001c0002e90080016054009142c1c0f00c0184035415401004003010f0080c0000703800c4c0d8842e80410a00071004661141c11030780c40200071400741c68520300030600700c446 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 160064586 1250 160063336 160063357
    0xa0b13090219090b181905040203100e010b010906170609041506080c0103050f070e1009030c0b09010212030405030f03182b030605091303050f0f0702040c0903030c0f0503 75
    0x360102050701046136212807a8038030700701c03010003050089503419020301c9400c5884242c5540414243c2d522288260003095021740300034242c0380064508006c4c1c004807103408a48009580d56298030343d2031560030a0b1294054100c5042203c8807400000b060300340d20400a0455004e4070318200072604004402d00000030848105005021581d102c0318003907030f591070300e110860000e81000f000c542c5070b900b00040e0700d000d0703106681c40b0702018080b007051010040801d100740003000302103940080440c00308002c1c0c5020f480300030b0b1100da65102d903034002490050348002c1026660000c1091000181e0004100e8000c040800301c11034070f0340c0d95441c02210454803c50f0440f201d002e8460030b041d02d042d10840c00103442c0700c0031062101b0f40300e21080c1101181c0250107403640045010001c50f00d05014010400403141c07107464510f00e0324502900d40721103a0400640300e400120041108021407500303010340b461807115454101311503840c40c0c80007444e42020403030141103461a210003100703008040c4112420f0303050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 160065836 1250 160064586 160064629
    0x130f03060e070605031603091704030b1801020a1e0e06040b030a050a1b0507210c0b0702010b09012309101a0703020607050310030c0603020307080a0b130902 69
    0x560342030510280041030000c52440c041e100c03010a505000e84142d9001d400c1143c44010f100304054015402001c0180c0c051340c0d24201d601000390f00c1c03119000140084e511466003140581003c002240159122158004103640140040c080b0340b903100340800c06003000700cc14501100b00440d03050f540ea414070302d4480e801c60070002d0045044420301e002940078904a400030800d541d19101c84000321a42200c19000c1c0024100300146810300c100d0280800304c2c06950140380d0980c1d85810a143c1c50207400c0c108011485422007402840000100c031940140280024444c400f4044c0014910040502070700c10808282c030210004020440184110000d018180c61201c1c100b1068444103d580361003061800d0800360000c852144102050320000c17503041e0000e100c643c541120035100d0f0f4200034044810081c1081c000000300c3c145107260f400911850703e0042c0d480c00c01090051111034000c082038940d03414400201c0c1d46e1303100c04001c0b5140d0041147c00243c1c50440f84000380007040110707801c400200d03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 160067086 1250 160065836 160065839
    0xa0207050a1b1805070e030106030201050d0b0609030102040e01030506090f06040b090a060c021606031505040e1f090c0e06030a06050a06081605180f0105040903090b07030306060e011b08130f 84
    0x98056000d140110095106d02c0c0c01d2402c3c038010582a2031032400001d00240741031207030745c0400c04550450010040020901d50400c200300c0701103422a00684e01030b88281c0220f2004005101e01488220307000600030020740b510f100c4801c14255183c10150005041c13016001c0011303890103040c0200c1c9011036001800380013040244034003d582e070307002c485010f56000c6ca903100090f0041c000c0c0301c0c01a1714003001d541e68981c24505410000244041c00d030260a0340200000500c0c841c40184030f8500500109070001a401243c1c200400c420080d40c1201c015500c4c00820720007507a40c00214a000a070b48050702155030b41c0e9032039440c2d002d4045640814440e1040303200144042c540c180a40e426103005644498000782420000214000151051500e01000000500c818146500105461400f904202000d543d0742c00080d500751340200f074140c0001340e5480003031007516803002d00724640c2842460200c0807211508540300ea002e0319050000c16450f000210901c42518600101000307001e035411801300b80303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 160068336 1250 160067086 160067129
    0x7080307090509060103092d02030304030602070c0b0304050c040903030e07060e27070c050a02061b010501080d1d04060e0f0a2a050a140f040e0a0207050a1b 69
    0x603003003402983d104180400c002500381d4802d101d0108a26007082901c0c40d00d50b0300e0350769010f910074550300d981c3c07409520070400c00242e241000100002c500c40c50005a4600c0d0300d09082445648580010384540010000c4c0f0010800001e50040703403000c115400503549085d0300e004c0c5c004010071107032003200e402010b0340082c51a0700481e4568000606a4118065481c40238404802a88815416405158401c04102110711681490441c54410340c00c03030b8200c403280c0d000901e41d41c00110f0101c1001c0b580036000500d01e2000e004142c0142001801410b0804040704054035010080c014421500c185165880c0725a446821550003030040781000c98181c201042a120156401c458002c6003900b01654580012000708083ca070360710105400d9100e0050b1007074115255401014001c0401c2280c2000d6855030107000028042501c24243c220f0b65507107451800d1000c1400141f0848600e4810302840000c40c901203076490400d80d010f001c8060041c00b16061491050454100c0e1140180c46008030401c07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 160069586 1250 160068336 160068347
    0xa03150b01020f01060623040e01090c0e090f060607020f090a0509213a02190212091005190305041406070c1401061706100501171b07080307 62
    0x908207030300740d82c03c8180b442d044909a031846e2041c100040c004502c01404800425002c100007803102c202c035850b09903500e40303d07200b414003078211004081c1d403007038001e22250304044002d00a0a040d01c00c60000d2411010081c06c0c454001d0209010391030014081e0304641d100c5800040001004000030200e0030040b413a5402020b0840e0120018450701f10300d22514030704101c01440f100c489100051074011a4003240560700d06001c480d0300061130080a048918403103150031400206400001070322801001040369001a4203001002550000d84007901c5176000d01d800c8502104041c0d0f121041089444001c46c1c0900c1420307207104e103003e4610f10070340000d585500114066030003003d4804400c80031a6115489d8502a6885008103541d0100c0c0c50014607160f004000c8401041e00008506640c4c03103a210b0288103d400c5005290485020031611142c0c07000c6100142c002860064442008940d4800c00b4880141c2040705c0b14501400300a22202c1000894400d550720848003501c3e42020798002c1e09 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 160070836 1250 160069586 160069601
    0x1303060608030d0605030f0d030f06030209161e1e0c0b0f09120f12100b070c090e0726030706020c010e01050603010e0706110304030b16020d03020a05030c090a0315 72
    0xa80f00e080001c005454070f03000a201241842c0c140141142194820050307006250048850b6000e5460303081c00000369840307020360b031310910150503090100001d001d0010044807540030a035003005400c0582e08030f502e500001c1b84078034000b8013080804118400e1400c0d81c6003500b00c0b00060404032030b2000c105007071904007074480c011000301c0b00700c80b0b900c00fa01004840a0040940b91499550207100d501501c000c010400743e000b480411036845a161207520020321903000036002e4072001c8142400700301900c0c0d64800c1c401488104030251008504080c211644001040c40b02402412090b10800f08850f06004980610342e110100319035601d0004081c40c0a8040c0490040c0d940d440d1030700080c8282818000c0c3c01c0408850030240140750b0030324400f41e5484001c4052507030103200c103000220000386044059409034407480150000c203421007000920300f0b42c00d600c80e0001c050041c0001220507803c481500c0e040081c207165640c136404202d0100d240000c03d50320182c9105140300362901203a060360701862 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 160071942 1106 160070836 160070857
    0x50406030209040332090f0d0b0103030c030212030112150614060d0b060a0302090909070b0f0a020a02042412050a0206160f0c060e031b0402130306060803 68
    0x340484205e00d02c2000c038600010382043ca45411001d920b8224422500030036007031020741e11081c1810f01840300400340880c00680408041c028330210740e00380d2001c0091758032980e48501e030750805242248151403007284049103065510250050000b900e800c40074051900319503800303009031940b1034090300d0f11040e5109031a02c11a40c0300401000c2144055030301580b40c1d031822041000c0c20f50090200c0445071b1002c4c01c1042108045010346100c140d2001c2c1481e04c0d80065582a0700740000c680000350b11501e844d552130034245824944681c079a881d80741c005041625001418004180716030003070010380c0300d0620a001440c00b032004090306010550b500756450010b9035000c035040b012890460703c60300500824404958000038840020904800a160782029943c0c4130703006152f10002c2c1d5004a800281102d000414101d80100456100c0d600b00283c1c0c0da07031000d0a44030707041410b500 = true := by decide +kernel

theorem cover : BRFrame.Cov 159892086 160071942 := by
  have h0 := BRFrame.cov_init 159892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 159892086 ≤ n) (h2 : n < 160071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
