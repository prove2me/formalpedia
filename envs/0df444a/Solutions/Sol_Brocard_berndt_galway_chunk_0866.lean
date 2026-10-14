-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0866
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:16:01.797746+00:00
-- url     : https://prove2.me/submissions/bee633be-6d12-43e1-970e-64b36ec162f9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 155575539 ≤ n < 155755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 155576789 1250 155575539 155575543
    0xc05040e011a072319060e0303130f0c1802030103061d0d110c0604030506070206010906051804030e0d050c040f1a060702010203040806090a0c0603020723010f0e030702090603 77
    0x2070780c01c030318842500d048200d070b80b140400b51144c1011030076580e9a405280940c1d00a100a80c1d03040705100500055038114685101190300d68880c41816500c00d0081088400420700c140f41035030b410448001c0c200100e031030500b00491407030700911088402c61251001c400c8540d0080d5040c0c910414083c40b690056014483c1500d000710300503502c9900c007041e400c15050046801c0c0302d00e9070440e003c2e51308402d08000030581aa2050b40115481c3d4014420000c1403a814020a809003400000900065203003200103100004a040c070701850004c400c010408040c00b516000c504680042c10104040d0a40d003469034507a00048034450041c1c1c1041c150005c840c1d02752003020070388100e0403000c41c40d081c282010300020307401c1b4080803410362000700004500450104110b0380f04182c4840102550511490301c181104480d9004009141c01804500005003104c0c801c444c0003070080e481381103010002101a0f000d01003e58402c00500d1602c10402c1203e4002b02c0241055030086e511142d45454140c00c0c0741d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 155578039 1250 155576789 155576819
    0xc0102040803040939020102160b010609060206010e040816050d020a031d0a030b060d08070c08072c0619031a060306100905070309121107060f020318130c05040e01 72
    0x5451400c040c0340080e225800d420650842d0005c80c0700050606100551504020138001000e417031500b0000010449242e005100320040c100310720240040b5450310706900f0a42d000607000610000e07011459443c02c0c0140000c514071540c0100c1168458440038401944402c000141a00010900a04100c124a07110500303000d4100c0030781200c000340e1450b12400003051018041c0d80c0c0c0012a4011140840c1d4050040d010302c070702a000014030280f800c0c2c0d8885c98241207a0021000c42d040c11841c0e000111803901c4009494917040318101f0913524407000401e007140107120307061000b410040101c10300c0607402c11402e0310179011400c2d0f121034507240300700340ea680d00466000410300c500c0a01400030341045c2d000160007030018203000c1040001669040040601d80d500040000c41c0c41180d03241150040210000030191410710805440002100a4903407180440ca91100d010111040415407524440b038465015410000c02001c031034038038010302c282d00c244684003400c44404000b01d24400000a10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 155579289 1250 155578039 155578091
    0xe1519031a0f040504050307080f0c010b0f06040302010e010c060f020c0709060503030f13030b130b0f07020d0f050f030708240315190c021c08011202010c05030c01020408030409 78
    0x240c252000c042c100806024018402c40c0c05010a010a10000f40f03250081d01815244100b0f15481f040050b52044c00c407192048220320800d22038900c81d1050301c5840464080d85d40a10b400028101c00780016127403603050b1000100030b40c0c504034a0a1000d2032541c0030345605891790b800d980e5015a180750386019a8042c0c0201985600308200c2050400d02250080c03100c24003942038401c400ea503a80300c1401e800d0f005c44007006060711009548080004070038400f6441036820001c0400c904000000a40d511030300301d1450b0610403001c640b0003003180aa4241d82d01c116140d03206035624685214010254030043e22021400022402061b800c0c4a5a0fa4017045038040600104898044660101c80052000d002c6509901070256000100c90305800b49540036400d540040c0042064103141071040b44c6090303c4a410080e94030014000b2010010aa40d14030f502464015070002090a003a4158460341c0341c1c0c186a5840003800040e0b101c0301001500440300c2c00e060810001c12042c8401110062041e0302c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 155580539 1250 155579289 155579299
    0x30c01081905130f03020c04180c05061b010905010903020f0d1209060e0a0b1506120609100509040b090607050c0c1207050d06090b0112030f0e1519031a 67
    0x7900300c9030819034003803540520a11080700620b82651101c150051501d40f0540060b041310a41000a0800c0d01514010303048003492609403050a80318518061614020b10b44a0741c00050f090010000803486058040c14200080080100514000b402410b80303100850240c00703212012500d14501007800c03014481561540401c46c17444034680340051036455030071100c17950b43e50303d900d01c581e008104098401c0c0c842c40e0285114141828040703100310510000300e22880080160205807404500e07240e03040b080946840507a43c40d8001000c6c6a60015080190400e08200403c024407008140040c09006054103540707450f25611030403980c501c101080140e0302d60045404d42000e05000100c030110000e40350541e1700e419280c1002614940a40a081d84d5482d1100350030f106016082640754010000c2c2800c980c0883c690303540c007502802841c1c075050b050141c0086201c0c1c941d180d011071490300341652400740356604881c1190801c0d040c070207008140040e2070300a10344010040141442226030b00181 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 155581789 1250 155580539 155580571
    0x7050105030f0f1e090309010801050a0f06200a0f0314040f03020603060a03060e010b01030e01020a0e090406020d050403050a08070e0306011710091211010522140f060105030c0108 79
    0x1020122140c043d04e42000344084410800380140001101c4d402100304401959840c0d0481d4001010b680060300140c0c4104614041003054604c02c4102108403122806c0c00300d1200c3c855050007001200e0b00d000c062150143c400080200817901c05009410781c440d80f1400015485130790083c2c514041c07801200350170078403403e0602c0549443c2c40590351100c401410303081d5698403540c945e4159030321409200040e81d16144010255a05401505242d00d0b55100031810b0104a2100911852070445010301035071107040031a0902c41c9540440f0f00300740301d00905200904241ca402885079000510302000120114046036410703118803101011640001c0c02400d8590800c46984907100c910002d002a80c0f00729520752140b039807240101e150450207800c686201e014928400b5006000e403105020050345410b0810229000d00b01521103001d80c02480407005013041d10308003024401c3c0d8624282c542c402c06201010407000095414142c640035402e40b001d0041e0300c4015900f1610943e040364042130400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 155583039 1250 155581789 155581801
    0x9090c07111c02040c02010c020c0d1a040203070914191401050105090f0910091d0a0813180501080f010c050f03040303060b070b04060b0f01020c0f130204120507050105030f 76
    0x80100c40306081c50382d42c481030003500c69000608540e80034501c1c0000d0303510f81044400140c0c042c002c201050100361000310300c040071a520006c10341001c3d59071049880841010509544080100b10007409688600f000001c414034183d52110b0009c50760310b00e8400f1340340301401c0780c0045406460500807594103028400d07400d0600564054000c01c0265400c0303414203902e51a181c3e10501818001d5003000d0070301c00018103040c08030080da44000945600d004547c1901808154002401001250002412501c40490001051000b142ea40c402c02d02064051310091400c003180d80518103d5070110200c40e6868000d59041d0b0070307590340710308101c007245080c090007010b44001d8005541c858828030300000d03410744a41e081c440c150404141a00ca08030580108810480d89102e41b544d40001211044046854100000d5a41c1c0040e41c03107a0060201444241054036800d6040401c0001c624065484076240c2c0c640701d00c0241c002d003050b15140304094000034154015402c0707a000d8429940307402c500350348030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 155584289 1250 155583039 155583049
    0x8070f0b031b09220507030b01080112020117072613111306030305030f060103050c040302060d0605090114043e0c061003060b0a0b1e040503100209090c0711 69
    0x40c01441010b003820031042840703654840c0381050303182c414140f07900706240304401c540403500c0040582051525008100c21260b80081e8864110b5100511440a00f081c5100488404210701030700f41c81c650421080c014160b03005078111301c11030740d00926680041030140103110a48000c4c5c504542ea100742d00c00782000724100300d0310f0a40c0c0b1032014280f501ca03c81d480440e80100c3c2c1c0181d10a07070000e840807083c8009150100140c0360049000d1034180681e051a01e1099664030480c030000344541e20000b0341880700d0507142c0200000f0440180152415a500c5400d06610205071b040c0c0c1d03200700d03d0710203080390108200c00382d0042c3c0250300a20184a6210031001c1010711b207000340c0c4a044460910440c80015410000e4511400c50348400c1d803011880e601d4584151450071900c01d11482c2c40100521400c201c44c03094950348540c44400580101c020903290500d403084da00265011f005c0c0300c54858180b90903400400d4114000d0302c3c858203559172a081c1180364011001e00520300c0c8090242400a840c02d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 155585539 1250 155584289 155584321
    0x121401030b0718050d050115060801050a08070302150a03150605030604061d0112050709111207030203250c0f050a1703011809080405120703050609121e0f0c0708070f0b03 75
    0x415000003036008c4144066503082030f0541c0c458030004020340018802c0741814400301d130051000310000d002c2c150031a2f0001d1007804512010350a07421020035060131640c804d030808aa1070038020b0020500d1358880344004c00301d9008445041c05281400800180380d60310400302c5101010380216840d1036401c050b02841d00c105042800e40f40c07840780070404a00b00f480c901c20340b64042c4919007180c0e9901115600000c40b4480203203841e050520510802092100501c0c0110351000a00c40403103038007409500907102ca100c41d000103441d121040000e00d003001030010700141c4039800342d260900201c04204071609188001d00801e021540010000003400413540c21140d1003500c0749044c0360074641c0b514045004120340348011400383d0311581c41001801400d0103156004425400500180000410900d4861103412001c3c1d1107015441083d4940500c2c190542d1400c000310340c540d82c2e5800e500f2048644c0e652a80c0284602801084800904110041182800c480b0a180c20508582e6140041906040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 155586789 1250 155585539 155585543
    0x103052208071b080d0909060605070f0501020c0d0201050411040c120e1203070309060c0e0a0e09010b0d0804061103040501120209040e03040f0603140c030c0307121401030b0718050d 80
    0x500c3e0300c506106000c507110341034050700b1030000804500340080c0b40180303034081903488650414a0140c0906c013040c2d10004441545420405183c0d000a080c0781003402841072501064003405144040c910071035041d0840340c0914028032070101160041410001142c5078000c195011403c1d4900c59a1050280e40000700a00341883c103807110300c041803c1482099004584020001c0c3d590300340d05007044401e120726a40301c040d501c0d04000c01c141e2600824030500c0c99020f45201e07032a0002c00070303034000025008546030110140c001350704100e285c81d0100b0150003601503507011400e40904910140d40c004203450443d14140c1d02d40350072400209000c9c0003544000c403c079402a4482d11900c80500c4208010710090034000c8a00039100e1410900030205da42c61803041d1440c03803d1002707000d804451003090320780002d000802c80307503213488101c800c1d5040240d9840002400d4140710650444414444559040364001c1510390ba0380d40d680c02c0b04980e00911840380041611005000f4000e034100703031100901c414 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 155588039 1250 155586789 155586803
    0x602032506050112050f1c120603060c05030f01060804020d0206070f0209042103051e0601180e06150702030a0605070507080c010605030d020a050601060c0c090c0e010305220807 78
    0xc03106445040c2a54026048100d01a0904a401c41044020040001001c1d80340700542480e09050002108800791081140c04102c05101c402040b030a42da40301400a40d40603404000080b0040000750a07034008560812213001400000160036001d0691140702e20760081020310040304550800202d50403614003919107a540d00c502d10010780350429480e009034011840480481c001120b041800c2c400b2104400402d41080107020710001d01d40c01841400605540d100c4443c0d54030401212080000601ca180e0049040c00004083c801c140c040c50091506540446209600e0f809500d0a4441d0810094240e8811034103400400d05560201d600110740c0e141252074184103465a4010350082102000d10b0b9555000c1048145400c0040e581958441c1c00600a400050b40f2043e4540380b05116813800e1168018100042100f00451900941015541040b52800c03408004200c0e124050445001c01d1a00c07001c80c0101c06180c03203024450140103900742a4050a0b650341c6c5581c4c00841c4115441 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 155589289 1250 155588039 155588107
    0x40e060f10210906020d1b030c020a30050408060708070c0b06010e030f0709150e0a02090406090216020a090e0a03050f090a03120f0503010608150a0512010902040b0406060203 77
    0x2034054001403806d59200d200104ea040118403080d903c004915201c4400e061511000c0745c3c0f80c58000c00c00002441d000603a420607000024041410744c0200e02141c4100d5814640180380607420601a01c15500840101c80c00c0395034001050b500302c841035408078045400041550001031b40c03100c1050340003406141c0032495002d8a000710f49006962000c0c1c0845410003502440700070400d1080815100c8142c8240070400d2800c0c40c4600c83e40006085030404580020b404401500c03242c10440050061107003c540e944005070040d201d074110140c049104e4050310701c00154504280c0200c00110f5003c8003d807401c0c00d42035a06481561081010080c2102c0500600c1650755503000c00e140214090b645404041c840300000514540881920700f05104090006002040c2d0202e181603201d041c0b01c0c40002d5410400e0001460382000d6481107500018403600000b4240040d089008028400d44080c000441c000e01080706442c40c0d8050000160b00071700a04c0e64400042080541d54880d810ac0e45550b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 155590539 1250 155589289 155589293
    0x304061b1b06050c0c030105040201050f030a090807060c0809120a0e03010b0918120c0601090b1309031d0105041a0307120504050d0e0603090601180e03040e060f102109 74
    0x10441c029440340011030310200b00c0d241900e406100b0f010300c00004078001c002501d440ea001800a0103a03032041c0b002e881d00440002d2413103905a0042001c41e400c1a203840d106c0b600b518018014015001100c800a0654008104044000501f101c42d0100d40d051035811711080010842d40100d042d4201985903489142140203070b01d034031510703900411905942d0040c1c8184041040d15004001122802c01101000300d40107501001c66580d05650407413401140f00010030002520a80c10842e8552680786000c0e01c0c0d40805800c15100c17180b107603605208001068181005650324000c07886096412801d1072484100c1901c1c40703005540c0300c0c41904085c64442d012402c2c40c4102c0710100c038201e90310780c4900144426242c0000182000c59021600d2034074514160004075183e0106102e241030810b502010603034500070355086141c04200382412240c482d50349001801c01c1c401300f40c4426000d580701c0307545c19580703091246514582d45056114205407030035481d1041c001060840b071082c6101e80d11010080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 155591789 1250 155590539 155590583
    0xc040504020c03091f080615070b0702010c0906020d020604120507120801030606050a03080a031d0312100920090301060302040e0a02010905040522020a0f080d0306080304061b 77
    0xc01030000740b00564950100d0340c2403044d414044800000b40c81d00150701344089030b0784514120362062054440c94100b22220303a442c0301a005c0c1a90041c002c64111017049040341e81540013170004100f075a580100c0c0c5a81d504107903290041c0c0074031000140c00081c006400b245211143d811203601038135160385846204e48488503403000b1032002200217140c6100420600160f802480e001d45412110b002001c1e2643d0f031448458442c41d41c2000c14513440304a81401030041480b421021010368080d43c2d5203c000382920144031108803203a43c4a095040c1002c0307101c642c40d200d91000b189904480d842d000e040544088000d4103c040c3c2c440d41992503070310100043c1c4540c00b8461003605400001c2074251882c1c800035005d0680d0b5080640603926010400a15002c4088901601200328141110115441c00455002409900840c00c050550100002c0031540007035070500c01511540c0800101391110000c0c3c0d00d038440c2c0d00c02d0000107950b0003000d0b04090b000e810141e00c0c03603201303220741001f01004800010b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 155593039 1250 155591789 155591797
    0xa050603040c031119030b1306050a0b01080903090f150c0a1110022802060705010203040b011805040b070807050c07090606090f03080d11130e0403030c030b01170c04050402 76
    0x10b41c00301d01d80804004100b18000301528840c0102d4404541020f00124040e80c550144405800c1004a5001c11034918941424503600e540010043c441450301c8d010500c083c03d001e240450001d221140000d090610110550350400c20040044560700e120504111513180300c02031102654004205a10703900340c041280186080c4100d01010fa000d012904110306980e889040784150340040104540a1b000045030094034455041030f00c50481d45400483c80c1400b440301e009005602c004103010511807080c0f071070b42c120341c130034909844031841511140e0203403401138400174910044040030490007401000351541c0312a091903d14104010b13010854600319469215040c003569546051010b10f61042c1440054640300500981c2c0500d0b5660320740c610702c608105c08502c503a41d01e071641101e261480886240505110129200c1500c0d490440c0114006a40480c08070b0b14080c891106a4002c0c0665021100c0503140d01300404107045e094a17038550000c1c45039800000802c004034980e07507148058 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 155594289 1250 155593039 155593043
    0xa05060901110633031f020403020d0f0c0f03050309012a0b070e03070e0c0a0e1002010218090402010c02120316150f060506030103080c030403021315050109050117060a05060304 78
    0x801d007456a1a100c2800c2c8080c0040410b4000c1388503191031442d240000d40c00050541520424490041308207110001c0c041c076003000b076000c1074031091501405510107140005a00401d110140582e60f511603050564940c0702c0100036400a000140780c0750b005d0660300c929004d001001080f2440b0300703138107080f03911240c400803030b02c0719160402c0c440380b290700c0320300ca0704500c1c2c1c02e03001025494100744413007204035401040c03881c0b00c0c1300000b42d0252880c41a004140300c1080a40000301d1740c4884c59000e4080d4202443c1007489460b0003800000c2c03071408841490240b41c068581d441903040341d800303000c410490a204c9001511007000f03841094035118242104060041c000c44c08050721140700c0c0001e8417000303e0404130403410300c04180314a9655200701d0341141da110030029030b503d4200030801d00f14010303680060760041c040c1a00c0c00030002d0582004000202e0760f10000084c907140c80065505540c9401914005204110840644c51083c040160462002041c0c1042c40b0b42d80ca0001d106540308441c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 155595539 1250 155594289 155594311
    0x7020d05030c06060108130609170301081005060303070b0a020a110d020c03060f06090121061d0c0406080c01030f02040f14090112030507080714010606020c030c0d020a050609011106 80
    0x140802e10a000c11500300800f481c201c403050400e0b140040286140000103403105503200307000c00404c00d11508072b61400c100102d4803522982c4da01011038960090100c082046800c1100086c0303246004012641e080c0c0d03028261407581d88a03e0030b44030081d0894820481408501007600500e04002c00822603d2140c0d94002c0c0f010f5500f002c140f40c142507000d031941c00844903240522034140e590700c4856054500e00c006e114460029460022600e8807501c00240140c0d16080c0a0044544c4598044009007a2a812524403140f0300050008445031751140220700d800c41b401e410015072181d0426401d06800620150419844401d51980b10390150b205e16050394041030004101d08250702c1260040800d0104d8030000207050b203015020b4440c40800800d00a40003401c1d10802c17100f0910103d203050b14030001c1203000e0300d4600180d95001070145062092155070f1401c40c80e803030400521801d0b0356001c0c00c00c9070598900414043c40e6001f107078007035042c01464030303180c2541e180400c1094412150105 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 155596789 1250 155595539 155595547
    0x9060d06031103070512071401180920120703020a050c03030a051b0301060c0b07050c0a0b010504060b0a120f18030302031e01030b060d0201030626150405070b07050307020d0503 78
    0x42500e80f580c140c3c000d074010400205000070b000404901d00048423440c4404c1c080d03c2441c0c03401228030f5045840c4190310810441c40214502c00d1560200700710014402c1c0a4800d00583c594030152741c080c22140c0350301d0041680001c0c1c0c0300f52298001d80352000361070400c24108480b4443e000d0440c2c1040b51400696a80d44040200300b1444407541b8145d881d13483c9403a8599410107400070800600300001805450700d040105101c9440340e4104c0f9400c08506055403c0945685042c410065081c41490310803814004041031203d083c2c811145503001a4031070094200c41d012400c0041c0c83c2c41c95100011075515550b4004400020040002c1c451080d070f001a41c03840c0103045901c20001c10043d041c02107240000510018100258181d00400101c403841509400d41c40101c024240c070783c01112501c070028030303190110412801c5e0b41441060207022754041226190062801d002c04407005411035101007410021940d860000349030380344c00340040d2468001540c01080222481e41d00448403075100003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 155598039 1250 155596789 155596823
    0x5060c030c01061e0b07020a03060609020a1101150512250602100c0e0f0d08221205060c0705010b060f0d050f07080a0c0302070204050f0603070b070b040809060d0603 73
    0x310410000d080c03000807214200742c1e280c030700140860141c0070f885c01c078040008150082d50754903000b0000440d80084103100040c2c0303a20340304c0c002c1d4220700480d070086000c666003061216010b00503904c40218041d080b400052500041110744240c94001030702900a03841c10800d0001100b80700c103000308d6800c085a41c02491301c20000d103001221030100300c241d86803606120000d030b40944010040d1a044861144903607117400010381410922500421002000460fa0320301072028001c2400300a401c01d0782c00c445c80e07a5014200f88221040310007040340d0025000504403000b0716001d030940a0043c00006072014505010580039400b44103071003441c00c404100c403001001640200c0d6400916081844c2e40c80c208a0005402c00b5405055a0341558030b070001d103420a4480d81c161445250024010700031400c061140c8042e00030140c0780d80d07000380108903000ca01c00e183c0c01c0c02c07298070303036448145810550391701d0312448603541141080942c032a40401c01428400c8a40c003541c4081d40c0143c2c44440c0207005c013 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 155599289 1250 155598039 155598041
    0xb03030a0201090b011d01091109130b040e0606030709022101080a0606170a1104021317060906090a08070c030b0702010e0c0a0308040b03060f06070b070f03090b1f05060c030c01 78
    0x5901c0106013440f2008401c4111030006d24032411245004000328111541e00c4200311f840c00343c17159071904180d0b42c40340e440000105820074140044140c90400c0b0383c10101c0846529118121050347c1c05034044101040301c074846500134010742c0c1396102c03035012000c484c46100c8885602070b0700504043d417100c040c80003400b400784525001000701d00000380c1c15641520000780c8902400c00e02500b00c800c0800580d90303940f00c3d40c04883c0c1c2c40d4010311a4441580c1c4502c160449252140010750140c4a10400545582d000045050040c0354260041c010200c003503803019402d07801041d0449910a8041c4000000b408103132000340a800d41d6000402c0005401348040d05d48219680c00501c03603a04401d003000882d00e03000488060b240c07042c030019541e5950310081040c009840c45c20030f80220001612005000c2140d03441801090310f0341d142c5600e146050011415a00d19102c01b0301b40d4440c8d50003041801c1810000481c0b07107850041c10f105a40c1d610000200300307070003804a04a4031b8000042c11426403400b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 155600539 1250 155599289 155599291
    0x20301060e090f0402090c0d020d150602010501050a12060213080a060c02010c050406050c0106050904030512010b04181e0203090304030c080303040308041707080a050c24190b03030a0201090b 84
    0x109462600721868840024800c940f000f0700044d018603a88004180c55100e0501120401100340406550300e0401c070000d1401010f88a02c1c6c0c082d08601d100020175214810301802d4101d80006007c0708009081c4001180041c1a141046032440d5080041c1c1c54207644401d0840c004003c1280504031250702d905140c1c041d1801036a1603411a458401c8030341040341c00c4400e540603a506031070099200d4030382e1100103005250a4212039400303801c8000304410158054001c160030368031030390751000d166a82c808601d1503011b54002c2c02c2580b807140c04000741605a6910500d1103003141400701048140d2182c0d030200700d9205075135035801900001004e00c14040f101402800614004c0015407861400362030007000e14201900040050115441030130b461300a0314182e0b1034850308245c0407540c0d028511009001540194138020040c01101c03e4058844140312144011621b080743c4003041c2d5070b40c0b0900d1941900741041d075464840c1d940c801700149803010405080b420005400009410405082c980c80341d00d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 155601789 1250 155600539 155600567
    0x2030a06061d16050a090e040521030108030904020d0906110409060b04030506060409050a05030406020d080c09010f030b031603150b030f0d1407050d020d030e03040302030a12170a02030106 83
    0x256003060040f908200c9101c480c200b40c80b864801d0719030710f4508007100c0c00703003030307039011042c1718200d102070000b84a8080b43c01c041d041f05852001c115a02a83d2010210740002d100c0d041c070607042441395449500b010780080c40e03900c0384a6800030301380300c40d943c1312012521442d50488840da0089424003000740c0ca4490352002c2c1900c000c45d1800e00e0b1841d0f8500340d48034402044103008070340f05c180c01d004201042080120f026400790030360740c9130354585400a503191904100040000e00e504080785d807a0720746a04481072090103035a41d01010b2100142a40508514100c482c2c05d441245000c1090f0510a01410040c520400e140030100383c9401c03260050b142c0301e42d2124400c2d001003003140c1810100088401e03000d01203050442c03618940c3c05000320b0f20302075585e0140890040c84034101c0c07036590100384005144503644040201800007089c07140e5074040c6000c0250103601c040c0341a00811114a120904d100051078070040250031903e12a5400b842a07031112100da4000c0014051180c11500244543c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 155603039 1250 155601789 155601839
    0x80a0f0908120d021303081b0d140702090705090a0306060e0903030f010e190f0902040501150906080901020d0e0a110103110405010302070201020c040c02070321080105011b02030a0606 81
    0x41808110002140f203a480419207880e400200340d440c1e441c44134501401182c10202c503d448940c40e8007080002c092000581030702d0f000b43c1104045042c01221000d03c4d00c3e4403280e2441c1410216424002c003054003601031014000180f010507a1691404a444040e41c8129004a441440c100c0c49803a1030201034003560017600148204665240741c4081c060448002203145030302c9881f070946a4071071010f10955803008900f0500d5210000355150403081c0b81c24403d4404121907aa203213419041a003141e17403008001043d1501c00c119081c0b0401d03c107500854604001860181c00000d20f1044860b20f02a0940da40c20991010050004e005004400140c007030038203120b6080c90400b0301c1c5a600c507500505041c1940892410290f910070410f4112041001c0c204104200c010704000c0c1d6642c02ca0720046a0703842d09100004008080703500001c0c5a2005902c6400090342040e0041d50788800d81c0c180070382c0ba0107041c0300c80e40c0540e808100d01c0c000240121000291242407050003030000303800310503881c095 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 155604289 1250 155603039 155603053
    0x10020703030908010c0e012109140c030c030309040b0109081e07082e0209090907051e031915020f0901080a0905150a0f0501030b070806030601030f02010813080a0f0908 74
    0x754100391200d418070004d01c1c0407224512203035844509a088e42001d007149901c1d140f29401001102802d135050007000c801100c80d052000300c20140d507820301200040d0160028030060856052a030080d00003650305050800070680ca07503070014a400d44400b604c2030150b00184105001c0035040c03181a000c0c200c4980a022002d5415001510180e03d001c880c0c80d4900500d030240d4018401c1c1e90564440a8000b01210401d0810b6144107a0302c4a050249901c9400020386030041d69500d9a034418100ca40030300902295114400e013000100030103a0260385101125444203044002c0313100800b4142505c106c25a100c010307410005140c401e00030704440d5a1441c088280340841c034009000340c50b4481c1b000d000029503442c00c0100c0c002d4245034030481a15030500001104106015900c0d51181902d555548600d50b5034004050741c8190a11000d020040c001241c01c000d0b5200d116415800342da40c084401e00c072007203070341c50110940c03005c08030000042241c2ca50307148480d0700c03001803001041000010544 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 155605539 1250 155604289 155604311
    0xb04060518061b0d15060206240d0c0302181f0806040b06040608010f060911030c1e070b01080f060a0204060210150b0c0a0b1e01060302090409021002070303090801 72
    0x500c002c080c1140200d695031104015081d00254111000700c054800c051103054812412485013010314003602e40513000d0580060b13522004c10700204c400006000031002540c0418040c41800c5045c2135054440c200c001c0008400b60700c401c44214040d120100181442d85040141440414078601c015240e0504001b01045450360020f01a0f8205030448010304003501c450380010000c00f043e40c031101b00b0b5400c000400102c0c2050341c0c0820100d4003c0001848048030621007200da5110845000b07031012000e000340440a0f40d0b4410846020001c800324038688000380d240d013a40030038260300241081c0d121030780d0540c00403400d0151036001004d1502c154241410040065214440b2130140780c14103a59032900804181d0056064000385082111141d070344448010550712191019410b5443c80310f1400401c010012080c3c2642c0c3e4486040807258069003411001c4006c2d60024070141d503c903450b0f8014101503950f03252207518440290300217051a0789036107070142044115921886c411b9142000742e0007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 155606789 1250 155605539 155605543
    0x1201080c030607120b031c030f050c030c04060c050a0213020301090f0905030d15050d05010b030f070501020303040b06270702120711090c0706020a05070309051f08060f0d0b04060518 80
    0x1031a07008401000c2610b01c28007012071f14011505541c200d032801200c005900b81501603000032025003084e5000d00c09aa111520060710348003d23121a08a803200300020488103201e000c035180601d2080b07090750201901d54002451000301c0c10a1080c43d41d60000042091071100d11a410151b40c040c0b100307120f403c0701e070b07100c0940fa4010744e41409005900d8843c0c0802d08240040694003802000f410200c0840041c200b9500a080e00e0080600038420f02c0740d14004014002a0b5a0807500142e0045d8513665860f951068120409029641c1040800031600c40340c0704c4103058485d4ac01c82e0f20b1500c0c022482d022000903c2c080400c17401031803944003044410f01282014080062441054807030151079210841e826016100d400c10142c4118404100c045405d54400c2c020030740c203070180d603030070313010310b40355001c0010062056044100302c801c4c000240760309034015030544d64000300040c004c003084001180800c800800c640b00460300304051504100c100300881c400d450304200403005c00700800d220740030981d07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 155608039 1250 155606789 155606807
    0x5011e05060a090e0c070b0106050403080a031d030c0c0f04270f0b0717010501090620010b03031c060b0a0504090203040c050d081308012912031201080c030607 70
    0x103000c0c1d000050a001c41070b0041001000404c403c0f131000600f40345c0501000c41e640c03c1901c00311075a4403030340d000040da14424000d68050340c4d0000700b078a2400c1c10510b0160000e110307000b91140d010562140180744003c0c2800a080703400301000181881840340010000415202c0f004244102c0c5041120080658200d030101281d0001e1611484a5100c40c200350066810a00005003118064820004041e9000740d03802901c5a5640d400101641c89034015038070341e600c80c040c2d500090328903002c01200a00340c2a0280340c0c01c445c0f0000040200951011030f0840d44103102100c5007846044410558032524400c40c8020400e401c00700d41455a0554020200e100314410040810380220218041c428800f83d210028900141300c5070040000e0300e4484156003244280304040c5050b100002021007040c018203a07005210074280c1d2020781025650700f002808070b10290340000c116008482011403c100902210300901545a01c0d50300d000d080b1490510044d0825000380c00c030781c00348580d19411422031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 155609289 1250 155608039 155608049
    0x3160807140306030c0d05030c010b0418060b0a030210030c081806040b041401050103140c040504030e060d020d110c100c09271a01090609030206070303050702030d15050405011e 78
    0x1842d034a8071071100103441c0481481c8100d1348086081c03031071000c200e40000148824010b000c000d00103d40c02d2003c1204803a0540440c7c0381d2007654080083c0080c400340c0c030503041c450b8010a604210345e1260041a410b40b1004a0040860b984240081d519a04061020743c0320306480c081d4280409130303d00c0c1d162107640280009114460620201c1d082103071300404c040346152214000c03c810360703403402c0c1003e22110054400669018041d406146801e040c01150f200d5034141d01c620b9040940b45050203074a40c000c079142090141d0034450310745001402e000e1380c400d01ea6150318064458009425081c00e00820100d000d42862414442c04c0066400c60396410850f54080020100000c0c4055164001d01c00a9001c030720940c58402840721505807900341507840c0740280c2e100040607440301016188295a400041d61290b4140300c0f60b00020320a810055201000d48143c6c1e0a207171031140c6140c02e172048500148507017101400280200c0c01c00e0301c00c6034010070300322282f1031407150800b16840002c003d501132 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 155610539 1250 155609289 155609327
    0x50c03150324060604120606140d0f02090c0c010204030609020102120a0e060307030e010e0a0b06030d0507060b030307020a0305060702370519081305010903172d03160807 75
    0x3846130341c520055500415604003084801045071500c1c0f0000d00d0b5038040c620140385004a9800c107410944a901c01c0b50b43d0141710600c8080c030300d40030000d1481e001010704488210030801d046c0a21828005000114401c0c02c0100b40385505100181c00d00050f4614072024a1050000c0d40d60300794802c0c08195032120996159a4a464001c4100c006c0d0500001884042d070800050701b450f020009903a030000d901a007210300c115210001010313200e00c8107614010004900748006c00c086815580108a903a2008040b0b925000055011444100d802c0d44240c9954105404020700d0b41d40500242410040321180c130541c07010b1111300e520b03a121000c00c580c0e8490140e01c03001820003000b045a0042140c036000304085440c02840c1141407a40400403817040000c0c4003000040a500945480c800c0d01d0780641c1c103a42d040002c50352610355410030000c01c6042c0407001d40484010080e018021030b00b5005007000d80d52403800003200020030420016203c10001854200134400c1e0740444c00311400125621 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 155611789 1250 155610539 155610541
    0x118030806061201150e010e030318060c1606020c0a050a030323030c13080a0503030408030406110a030b10021c0c050c090703060e0702010506010507080a12050c03150324 75
    0x704640340106061501543c880e01c002058043e014919a0200b01c1150745d8a002085032000444200385104038a0750941d0003809054980340402500c50100440604540c1c01d1490b036105251030550241144001030030540c42c2404000d9060011000d910fa041d9110f030443c500c0e000128450309007610000c3d080207000b800034488903170460529011009107051142c0c403404c04000090315540320581105050350182000940710002099050800750420302031405c50341c81c3e48036101c00e40d00c020b00441e00180d0f90180d5105000003040508902c0c040c540d0001080c00070a0240300c03950080515403c1954000503c09801f8a0841c4901c6aa0900e80c44e041d0026007180c03a0251414042880440d4000d98580402200e103a059200d481202d048035018146074a8a043c203908072801074070143e0002e84100000c8011403288001805040300c00e24002c646981604454070844006490042e00480c0020500c8011040d0440d030b4820610101c019045a0041c130b2180c1080481c180c1860400b000d40f40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 155613039 1250 155611789 155611801
    0x40f06030b06160c050a0f030b0117030f0301080606090c03040f14190809010327021e0d03210614090402010917030a021207050d08101d04110301180308 67
    0x400d840b00050724041407004502c0744d281c1003100100c02d000d85030160a40000c00110346a0518041007200e41140440007075908110076103146004000c1000100c0c801001001c40e4208030000540c0203000324070150000d8145407041124040f40902220200141417040c800030071000d0f50302e07602c5154000e070030002109262400c20300f0504030b0642d0b81218807200d071001083c010110001d000004c8240e0341000403c81c2c0c0103034003103400381c044040445040381020200050400c40420031580062002d1300100541c04000211050f1708004202d000036040c3e032020f546e100b10200500d8800e281140d05120140c201101c0208600d0401c001c14030442c8c3d26001702d8196402001c41e040036140d0b4181c1c900c0095080070086946e039011102540061141540f140108807641055440f082d6200340502860711000000703d0383c10601402041100b0003481d000668030b510f18600c20205903001101840c189414201612304914120a4900076414202044c120365003812050742d0f0307a0380c9814030b20030a403200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 155614289 1250 155613039 155613049
    0x20702010e012d0804110406061d1302030a0f0b06090d0314090307060507051510030b072706030b06041427100305010c0c0b01170109061103061005040f06030b 70
    0x103040d0680803021403004110280d000c4c09841c441c0e40600b000f0921021000c0a220484070544a0100003031405585400035075000c80e200402c0400080078203040c2d00d20180b40204036401520f2000501742d0b0b4140c80d800c07200c45405460030310542100c2c031900f440001d6021845010419100400b000441120317440d85510440543d250000f000e4220303500c142c3ca030200a01141d22070682617070203100c0da011226841050750650341c4142103031161480c203d8615a154541068090114000d000380c210100f1641100b02620040c580086010500524035009001c3c0403a021000d0790390040100b040f0503c0b8020140c7d032400a070013025580706005c54003d0f0101c0315100030200b418070242d904030302404100d94402e1a05d00580380190020441c860b1510b90a65100f810884020030400a030303c010801c40030300d20b076000e200700003d2001040c0002c00741d8840703080321402700c120401c5090100502109040064aa80385a9980c1c00c16500d81410040380708004585d501c00c1e6010076444200d00c417110713114 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 155615539 1250 155614289 155614337
    0x3020d06080304060207061d0607020f0d02090c0301050a0f150f020f03220603090b060405060d02120105040c050a1d07050d0213030b0c0a080115180f0504050a020702010e01 76
    0x428025243c0750342d01c845000391100c41c140b15500004217054075801c0b001014084160450000900103481d012a0ba801c0c402c20740b000c441019070260f4500c0001d00541c5030b80f100e45120703255007602c4643c0ca6052008021a506440d0080c0b02010b8900c0030502c82c01084040401110b8601e00b0b00b0640c0505040c4124a807599101040e51503001c0880c210602e01101c407820200d00c0e03518104ca080785501d80c501101183c00580000e020200140007280f114245503000c00c5e0000e1b0050051220106190041401090340e10010206030b9904e608200030700001046410103028112103402c1d0349440c049500f96222482c5110503104280c0f9808107403520b00030422514402e2441d10195100e03179541410b000c49000c140300603580c480c41e03103001500c22003a88040b03c0481d51035469105481c0d0a080c5408011810403270500c1c00c3c80224880081065900141440280341c844ca03400841d071700782401d200c19281c0103084c07001d00c3c600521810005070f802001c41005540b0a10300030740d1042031100c0148020310 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 155616789 1250 155615539 155615549
    0x70f080c030714030309010f110a12060807030302031206030a020a1a0d11120106080709170c0301020f030a0e0c09360309090c3c04170c04051603020d06 67
    0x801183e1803d100000c000b0754032801c003041c0200411000c0f065520182c0341240120481c040c0d040120460304c600500b5900c626000d50000014041c0d241c9609918000703140d0001d0780580c0c0080f400000c5d078281c00c0c0c0d056078029002d8000d00110342280d800700321034108031301590a010900408695050401d0410b44120b590403000500609032a0507001b00640c1c4032301810110b140810001046183c040c0e540b1500841c0190b8900c040c40d8036013005105a2129072090a00c240103c40f0300603000e5809002408807013030510038065070790030300103030000803200b20b10030f441819000141c4910040e650340c6011a40700003c0451106a0017401001d44001820480c02d25212500b020b100c1120b01d0f4000301402d8071003420740c2d0356209916158240c2d1031b10301440d500069940c0307905c0a00f484000142c0e5032203000c142d500640010031504102c0584540c0c201d03400040b4078008490031081c8150080100c1401044107840801040c00c05455642e01d01c0c0c51001d00d04d0a040d00051304080700c2c0d280c4d500c0b9000503c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 155618039 1250 155616789 155616803
    0x70809100c031d06030a0e0a05010501090e1e100203090c10022518090201020a0605150108060402070c0e060303070c0e0703060f12021c0605070801170102070f080c0307 74
    0x10100500251040506100540014840c00c5110281d40d0b882c02401c3e02e5504010281810340d0340c2c2200711310181030007c1e0850440c4c0101072003540003600c2402101c1c003070130781c2400102e00111214003407880c140d81c0245810031110a21410070ba00403000c10f1403650016201005139588d41c404010514000208075400d40000c000901c03c1440c982c08140510418003200c6042601644148216080300b1103000c1c0c600000c0311a1a822030100715540011201403040c015a070b00c0750010340301c10003124012121450b1100c0045524100e03580c0c0000c06a60101c41103400314141002521900c007009454029642c1182d088404500640d500b0019100708070341c00f05840040341c1e2142880501c5d0710f01500d440c03003c03d041c0030b00801c0007050816480c041e00d00700c80c00344103140b20355003c0003d10300c0788101c0003449002c00303000b11010070081d0140c540300b451603407a1423080e549491500200300b004c0558004441e4410300010780010701c8900902c00c00340d0403c854940b14800301504a040d4400c0c072100400c40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 155619289 1250 155618039 155618059
    0x80406050a180b040606060c0804090207060b03030c070f0e040f0609050705030322080706020a080a0c1502180a0807050f040209030d091d0c0a050c01090803151207080d05070809 78
    0xc400d5002c160300c901c0c0308100506c029652114203580035440b80c3d0005003050b00c14001804012030baa07015050250041c207010801a0610000c070741568042c070a03440441d00031110134080d080c2c01d6030700d00d0010328569800040a14040d00d0303041007102e8140000700340584070309003141440310420070701014050040a0341c3d60ac40c4049404103c442904202440700480c2040002d031a036000319200741150f0140c0c02511600c1038075035903191a030384000c0342001405503403007480001c2014041c0121a905c030030700380140d0741c44070410080c040d540510300641c49aa0800d80602c0350380e10100e4560201c40c01a00c1c5600c041032030400003006030003410052500b510501640e451303042d912203c410201d40394400c42001110360003a05e0324441204886124071300c1001c00c1030f180203611440080c0300c4500c3c1c16000143c0c14040f035840001d02d071b0003601c0e001142c044003c139041051070700b1716070302411488007001400c5991402d1112511a625802080b0070f008000c04c41505010101c812aa100c03031000f4030b51810 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 155620539 1250 155619289 155619293
    0x4060603060305120702010c2d0b0f100302210106170102042105030301060e01020c030105010303030b03100216030819020d050708070206060307030212011434080406050a18 76
    0x148018882550386102c4d00c000b500c1501c0f281c1013111030300754040e99540b03011001a1912040703c0d4515841c020050100a04100808011100101028403030005040700d0704011140c1c0017910000340181c0d4804050620400040c3d440c42e054200d40d5440d11501103060345980040e500511081d40034503086600c1c514600300b180810742c0140103945450040c60016007aa8813030700038108c0b00a000419650040005002850288012200004051044a15102d28080403d082d0784082e4411004079840f4004007406203420320994100d003030040303021401d190205850f512105442c6401a00340a011030114902414808586d45018042081959213000034840c00d001882d044410000080c0c11902140100e8800f254081c0a0040200184542c906507020003020041002e0340607225035a03240c4004503000811811032290000d00b405050b280b400e444100a0390707060041e10060314148001011031075402a0910303810a400c04030010740c5035142001a002008590400402454a801c010302 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 155621789 1250 155620539 155620541
    0x30209060412031403010b030103060f0b030a150c0c0209040b0612030708090102060a05090a0b06010224010806010b0a02060a0f0f050c031b0a09090519061517010b090d050c04060603 80
    0x90828804ea035640b83c0e100349441616480d010a0164030746226003000100080f490f50b0b00007410908040500150225071300c00020728006901c2d0f0102c424600031510009120b05074446c910115480307003810b030441000755000a4072280c008100820724800c80740841e00c1d5450700c411480742101648100c83c0d44980906250399590040880c00c0d006104060000310303448028054103004241d410010040c40050790f94464409000070324941c110321905208084a2003250301200f18503110400296295040010740c506000058110022035102048044800d540c009804d030b51214114000103524407000f980b80c03000e084445480c108080c204018000910690070003235024010030429400990070014607c5070742c0c0521034048000c01d001420800107406582c00c11544030f1841520381c100f9006910300b50302200c0c410340000c1038544811454000c8107401c1101e035041001003040110b01c5601d4a0308240940c07246506103402403c0b1103440748100002007061400480006009010b4035803550790082c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 155623039 1250 155621789 155621819
    0x50d080405010f11040b030601030f02040b09121b0108040c030c0b0d0c030e0d0c0602070b0406060312020601080c13020d06060f1202070503031302030304080d020a032a120302090604 80
    0x80d400d5481c0411500c411a0743e0311072049500080038800e400e00341303401191402500020320300b0303060640b903511b01403031000a4070080010b007284001558854200d44180710491400c5154140c072030344040714151788018100000405c02800b468588041d03510380c03406507001c0b100359000070b01c0c9500d241c40118040c0345c24030142a01c51000b0604100d00c05606400310705a8045130300c16012500551038281c400ca11660302043c44030b004078000b41c40c141446c1c2d101e8003014401c80b025103507113a071510240b0402c003410600f145180c2642c80186110350401d100c0544500110100600c10031022501e011061040d405980c269813405d8410085c107076444002070001c13141844084005280c5942200041d242c6200f958000ca401600950842d0f68207810001751218802c020307681484140000141c1c00c03800c1100910564566003c0d14a0045500d009070510240d100c1008009810502c6c0070f00f20b171a0580da011007140c20600140b9000112001900203209070344600b03411140000c0c1c0420040c2d00e010f00c80f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 155624289 1250 155623039 155623043
    0x602070302060402091e07110a05120408061b0307032a0807021006060905060c190602090a090c0c06050c1e0c370201050d0603031e0e0f1309050d0804 66
    0x703210340d0f508480b152010191b028640d807004c404404140e105204c0d045141c085441c43c000c5400c4d100e51510740503e00303a000761038014450b40000b014040380c2020302c000c50300089440c0040d4500c1c0000a0390940c180002002e4104041ea2003505507500003003418020040e5808125042803031081900c0200441c108988040161003220052105401d07144501c008490f02c9a441c48115414a82000740c554005005c221551003024500d0310000ca60600340034a0078400c0c0001691341c2c1600c0244841051164450f06016241c0648950120303002007a25001603400300e0005215560f1411108031409110311800ca1410801e08140201003a40c00400c0d07901c0034034080300c03540d0340210440b02c03c14840d41081a15100000c2001c0e170069041d101e42101c8500c1414a681804104000c0d4030480e4204c0e40150000b40b058030f40322040c001030b407074044e0795403426182404001c400a404600d0126003040118001c0c8a40b0091000301d819562100520b15440030640350701e140030800c01084001c1c01d583c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 155625539 1250 155624289 155624299
    0x70501050c0c0a03030504020303280201111608030a0615020106060e0301020903071503020408100f0c03050123030304050402030423060105030a02120316060f060b0f03010b0a09030602070302060402 87
    0x114828114001c02d85241030111002040c200c03607555000c5010b0070010f00308a03054030081c0980382049201003080310020155222822400101003402800d4440d00e003101c2030750304d5041240345801246810043c5030f4680040000c1c9c0c5c6da8541110b104021b00302c0340d1183e5591046008481c0c10580d064009000b11000ca0740d82d030030355003000341c209802c078481d004149a05502c0b004042000507000c0e1540320860b83c90303040040c1030903a14003045090107084a9029500f80d07842d00450712100561041d0f00301140946400c0241e5070501c000c4015620b03901e20141e40d0313080034946030420365500300125009040c0203041036440e8103040c43d104c6000142d006103071240224046850742c070010005103035412100c0c020300134000a0100d0302400031000465020180c40e000c20002099001415000000310511515000500c0003c0b20b080c00d00702d580580001101e818104818032903489404240c80c19211501034455646c403224409a0300140075a0004280c03500114006060540209083e44034600940d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 155626789 1250 155625539 155625541
    0xc030d090e0f071b060914030304030e0613051e120d0207091d0a050f060c0a0804060f02040509040c0e07050703052d04230a082802060f07050105 64
    0x4426a0144100d008140d03203101e59000058044901028540e003007096030800c01201011916071305588030b04402c040e500359450705200410040031040c0305816019402c051415410240e40013410784240e001080c0c46003401045141c00c10604110f40300081400600c641c4100f010301c04c0d00c00040108041d203502c600600f19241c414140b002c2121440c901e0789074040c1c92610300340104000140750701a0100260b20443d0074480c002c5400b00210009240078000520300308c10f000c00581e1424000400c0649941000d124901440340c2041c409904641c0c0040e0118400c020b241c0382400a0003260f000c0ca600020203801e001c14023441c00a60300960740740040006c0c1d10b035120042960280b250340001000541e0410440c4030050404e00740e203446295841c0152a14820718cc10030155800c950400d605441c0b01e0b008034420480c98010400d8060b07000d5402c412041d01d00b001e41510307002c002a0741c46411110a481040c2510540301c51013615a00802c501d0302c0e040074006845082d0802c00d401c8816610b070bd4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 155628039 1250 155626789 155626813
    0x50f0d0605031009330e03031519030201050c0a1a150d0b060f0f04020c0f070503010e030912011806061509030c231302070512030c03180c040e0c03 65
    0x7018080031145c1040840071440c3d0038100c1c100b4100740d80d0b0380c800d0001c00e40003010f00801100c0c1c015440c40c020340078001c54480c10314441c0f00c0d68403001000c2407032062440d160042000009442c03082c1c00c40350242001d5071920070b40340400d41000342040000702072100c0a6401947c46003015600c41c003c41440501c020240c490f1018040407416005014201342049030011b41540f0300351084070b0740000c01030070b40690710034440003280a9800107090710400e50040017078001003100c1004054010032044000713002610090740c038940c4130300c140240390303015052007500710282442c01d402c0540d00c101d5008071b030030b020300e40d17414100e0080906010703400d50310103034a0783e005140e40300f41e45890a4036000300f80390984034075001c105001c1e0b0b00b40b1121082c1c0d079650404455115a10a480181c03e082c0e022005aa82c200608d415414031601c426820001503041c81480090000da0301903e030300070085400841d1200703e41c1195407610620840c0c07154010308140b01d11048440110f03900202220990450300390301082 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 155629289 1250 155628039 155628041
    0x11503050709170a061506030f0504021e03190813090e060a0209030c03070f0f0b0a0813020f030d09030611090102250f0305030703080708060906040c050f0d06050310 73
    0x155401c40009004000602c050b0394403c1d040c445038003882d0212220189035503a86000d403880910700c401c505c000401c00300140c40c4c0600401030070a610880400251a00c0c2d400900d807402c042d0354405001482c1c409101250700d0130070101c1d064010702c405001d4003a100340344c07502995004d420404200c0301d00c3d12000602d01c0c05030045070b80328070400c1c02501d01551500400e0009402040050b0381c94891a1100c1c8200d4505020f81e00141c0401c4544420660410015035210181c0d40d2010101c00d03401c00036803d500b076101c0d21140d000207240245041c0c04a150001454030030055224031f0f418051803070f0003400903800030044002c0362b104c0c41050080d500b6440351000140900c170310745809604900d070940305516082403016914070241c282560388540700e00d01143c100186030421940f83d40b0000300c110030b068100182681c00400b6151210040c40c15070041a00c610010707091901481d240c2d811005194094016650b041341d00643c4a0345030103408a0380d001030003036803054900074003403248018108161 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 155630539 1250 155629289 155629291
    0x30c0a0305190213020a02030d06060c080714070302040e060411090613020d06090c0f020106080307020f0d0c030b0c0405040b0303190f090b0f030103110d020a1403031201060801150305 81
    0x1c600a0800694040008040c000b00c0180890b8400d900e0100c5007000115480a8100c0c04400e42c01907032078500004841080f03c81542100d02400749540454001030f082004480c4040e910688400c16030290031000e92400c005500002d600c2801e02c5640301003e207001420501c1a801220800d04995048040c04142242503401c10340100501540319040b2005130000c003550a61840c0000d0025502c0950703004480c000b000000004450540448005509000b6200580400c070051441c0a0555000841010f045001240079092040c02c01c0c0510440d045950000c0d5003000d2101d0061800724034581c6941d000d40540d61090b40390120300d0185080000c140ca50039601d44807040c81540406038103480780c041058617001081041900401e030303004c45c41c000e05a030800501200f5125415490411203101d40c038201c890091146c035181c08051b0b40d984000000f00d48109100c101d111060348007203400d5114030300605070f80c01a08000014416846040701c3e040780c26050a031001c0d648420300132000d40380 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 155631789 1250 155630539 155630543
    0xc060c030a0b0d1502070201051603020a02032a0f0f0d06020c0d09030f0f140703030302180f0a0303050c010b300f0601050f010908011406330a090b0c06010302030c0a03 74
    0xc0d074003030180d815244c980c000d0207414014106030341052180c24062406081d0500101c0040c0c108522500c1103050410980078500c281030640c03460700a4051082060050b06c0806c244030703e47c0344040c40900d0329444884840c0d141d028203a407001254030f05141000c1d40c05241882d5a5201720440001c041d48100441810390340d01490100100c01c083e21000401042a0f50507207141e00ca40750404082d080800a500c015407194070050b071214628420101042c0ca0b0007000c900960301500302c02c100c0d036a030707518100c01e60b541810701c2c80d2180c00b0104003d0050249440054000b045408117800c0c05824200c1c80240c141c041c0804030400f0310050700b841d100c5044034070b110841c0c0c0c0301d42c006100714600000d0348030502e00185031180304d4568500c0c4240c00e66030221110061080d000090002508000c108031310b0100074003035480440314284040e0340d21445a41800c500e610700202d04400c20512030720403040140440802142c441100c0c10746591251403c4c441280310b80300b41041d890040c00c22011540c2120f03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 155633039 1250 155631789 155631803
    0x109150e060904140f040516030807030c052505090903040b031501050904021b010b01050a050706050a090f141b0a03020d02010314010f05030705040608071502030c060c030a0b0d 78
    0x3012410500080c2d80161034030310b40c082d0310b032003582031040401e010b6075224040c240174400c007500b4181440b07414445010440c050100d884101840410b8486045403a1661316240021b1444070b2810040c4c1030602d4181d8544404481c000318200031100b50b1921401c1d500304440404841e103842d500d81c0c0e66482548141c0b1f01038503050000078801007a40601c00b01c40703501818554900034443c800034080b6409050039006500c00070b8250080c580e824403407159212401c0c2400c901e490040140a003035406100001050135840c1d8002540b01038254000301c14140c3c0c0504510b140a01e1494070844114010768059102d103e0121000345204503010b00c081805400343c0214502415034003848004052560164141503c0d0380304500c00344030491403d03000f403d1030801340354043d09202c1018100300d105c2d80300c03500c154201039040c00162008107003801291040d140601c00701520200583c118050100300c00301c07600400007045542003207040118400c1c0d0703200c1ea00f0809001800100084e180f0b500c50090004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 155634289 1250 155633039 155633057
    0x100501050c010e01020a080108150405060c18030303040b0108190c14011701030503180405090c1c08070809270a021c020c03120c070302061b07050318010915 69
    0x5940104000c00001000c1000442d84000c0708050a00360390120700708000140403400108003107038060001444001c25609040843d00345602c2e00d070740c0c1b480c000c3c1449141200000381781d99621281e121001c3c010030b0241c04d40c0e80328a064240211102c009200718181d50085101180840140420504c0d0581e03024004600e082d0400341e9540202000059040c1800015a400c40c0786a1341508020700071403240c0000d55541c120b840c4401c03200703400c400990b405117085c407050008400300801c948800d0201555411104100c0300e002c28600ac00002d13010305200400101a000d1050880040c40e1743c40e0250350416032150007140903001c40105405a501039150500070811822290f001000340441201d42e86800140320387e140f008903070081790a400c1c1c1c0e91002814002d40d000200001e82e014900da9020f40c1042000d890203501c44500400d0305000c0403c103c403142c50342d00704c80c09641010b90800100ca840b05180b80020924402044816000c80c048410000e08000440340954100710350b6a0340302d0030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 155635539 1250 155634289 155634299
    0x7090203040201021606141c021801090605120a0c03020f030408030604150b0706050901060503070b04051903231c020a03120606020c040209042d061e051306031e05060f10 75
    0x701d800000e0340f104d03100c2881d102c03880844000d0000d02451404032210707643c0c2400c0140050501c4003d98048410312206000c2000c07804400c00440340d1007150c145021940c40501c2e03d08900030702ca84030020b082c0840c04001e00c400c0c4207021001d50310404081d50208220360700b80c40038010300c4d07156100302c03100c4e00000c00000c400034003150021a080b045c644008100705486000003810301a09811090584034081410003030381c508280c8036443c0086044d2030800300d40c155143c0c0d412602c1403517401d0080100c603500120218408000d07004511030754090880800c200d5090080d02c0c1c02050500ba030003d0300800c07580044072110f1141c0d0b0110b0320303560000e02400c01d015040c00003940201d403c40303a205070344102c0e2410381c02d21801401e04041035050410b0180303115200c84001c035160f07030300b0818000b04030004204030300351b206800038142e42d022501800064038080f006406054030390801880e503c1002a03444009958101000d09140b10b0310507911150f0b00d40c100d09004070702c01c803003001500e03003441401c2007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 155636789 1250 155635539 155635577
    0xb03060d030507050717010c0e0a0506160516180b01030b1c030905030a0308010608070201020c060f1f090e1209030712050a0b01120c0510080a020310030507090203040201021606 78
    0x800613101d0810f03544190307030b110101c407418100c446044035141d444c1da40c2d20038440c0e4020611910400f044406020050070000031448078061155400e000443c000458024030004002400300b065030780a660328074580b40c0c01e0b90040051a02501400c3c01c0c200386481c0020341c001d0180031100074018010f80b80000182002c0c01c81403104d041c060b824840680320100d49070301e0510062200a000c1c0e00c0d00801540b6140000306002002030002c3e045900c18070080141040100e003254001200304c113402503507281c541302090400980002004480030707803140000c5c103d0045d0801500d400304202641d00b041c0150210130b89a20800c102190306800c960000c0c0040083c0e6080c60740300034041c0302241d400d28040d9490342001710080c2c018442c260b0514604070100b06240743e05001510058803500400c448040014103014406012a1003d540101c00107800101c015450402550420121034603d036550444070700035481a14264018003c00310989080d2095209060403918240d40f174444082d00da0322100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 155638039 1250 155636789 155636797
    0x40c080c0901091a041401090e07140c0316060606090e0103080304050c130b030709060305151f1e0b040b0403081c060608060a091e020d06030b070c06060b03060d0305 73
    0x54107120380e401020810f401c004d50301500190320303618000c0d9030314200550f074140c40e41103150281c100302d03409100f030140700d04041455420014500305005d41c1640b0743e038910a140135240148580d8400030030008010740000031000407141c0285401c1003004c0e11200c00b10b4103101a40110303c6000d01002c010400120310900441e0b0082c013850955010074040c0000074514001350002e0f1100c80e0f103607100c60b407892400340084001080d0041042050510350394505031079000000400700121440c5000401041d100800303078803e001384e0075802d034403a503c5d0f00703410000c0030301c20b0300c45035414928940210f00100e25070b00b1a4103a40000350014181495a511040558000d42903441204281d21580c080100e0a004010281c66070f83c840800c00d103030070001e0222050490f0300c003042541c102660040d200032101e845c1c022408501c400980e4880c00d00012030098401544020940c00034841008000340c1d101600070002449410144051390340c1c0c4d18031100902068646643c03040d680d181140002c2c1c001e000078 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 155639289 1250 155638039 155638057
    0xa0504030f020f180103030f0c02010c030c14060109060e01140315180303100e0f01030308070c05030403150203010510030e0706051605010e060a1d030d05100902030405010902040b040c080c 83
    0xb241a800025002c140845040d200f00861000c40e84d0043c0304260700159400044c1c00c2d02d103407458061000e0340000340841001d09001c0c0500104403142d000740000c0c030b00807040b44041d20382280d501356552a40e48009104601c119000c1490030270021a986544500c94140a6001002801201c012001d41c4000d01e03005455201a07250b590f84e0310310180c800380040e500c144401568008981d18000e00104007460041c44020490074820040c40065040000d0780d0704000145080760026813203107085031452280b60000b17040c400610300f4540503107001c0d4000354140c520545110052105c03851040c1c05992140003c03440e40d800c861010301c1007e104401902c100c03c007003120700d00c0c0710405031142d6003100c01e0140011041c1d000341c400c020384403090303015182c1c1c0c00c0c5c00e02241c0251b03103860602590300c03801401a00c160710741d190408207980c0b980500000015106180d021984ca040c03d1030071074024047c07000c00b20f0040c3d003002d8501486141600c240324074500c542c0c881142e0b6940c0c40106c0c0d5900e600107050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 155640539 1250 155639289 155639299
    0x15260d0315080706090303030b040203040209160c060501090b0a0f06020c0607020103020702121005010b071a070509100206070906030501050d060e10060303030b0910050d03031a0616060e01020a0504030f02 90
    0x207140d0b0001c20042c402000c143e102e0091050941c10020203461040003205e00480c0100184030050300c072040507e0b8000d072110024000c031000d20b5000c44036182c2c0401c000d0021401d181c0041090807855001c032030442012100c25030304542d40c05040d455511b2505c00d900260f004540d500040e800c260700102542031051400600d440f222b640050481c17242c05c0c072101516802060340300941406071040a000d0b1500103016400e025403607079505007104a44144c129040e40e503001140c0600d000340d05440c12114000c01209101a40b20002550780200f110410001000c212001941c5402403103101d0507594003402918015a00341c0b507400141050304180742640c440e48000c2460f80f022845180003443c86641d0118400c4040b4040000340c110107400000c5010b0409810000d03a5510701ca80c0d0240c50385800d01140110045c500103001d04401030205401c850000740d10420b414402201c15007252080001b00305689203554107030308034002c070440f810218508200c11f1000c12150a602034a075440101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 155641789 1250 155640539 155640581
    0x9011b09032d03050903070602070b0d02092103070b060f010c0f0c0305011118060a0c1502040306020703030c02060901051512070503030a0f0801061704111315260d03 73
    0x80b012003118801e04040d0002440410b4014191a0038402080107003101c2c402028001e00b0440c4d000325a21840700c541d00c0d250790010b010f015940300c0884110100d200c040e0040700c120031034040303141c981c3d00500049031042680400581c0d130f8600030035140d0070b10106954203643c11140b940c40a155030f14921050340c51180484000000500902809210200040d00b40f900d440184070b400301c2200c0805050b511405c030a01c02d02d18910381c45480b800e0040d82104480003100c5080345a580240704540000e001c0740d000007050300c00e140c1c058020640150041d8210342d0666140b0303001500700c5506070360030100512002d0600e8128a840c4811f40d1110013104240c60764503542d280083d140d41d11200010000c079a02d03150400216800404003030050155050280200507030311520789546c800144003e01910140d00105443d40f9144034070140306003014001c10030a10f0403144010184428401c841811200000020508415840180410340d5142c010000c0000080d81500500a0101c022941e224494 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 155643039 1250 155641789 155641853
    0xe013306120e0607020c0a0501031109090c13060804020909010e0d0f0504120f0302060c120c07030e13050910060b1b0a020a0e0a0c1b031d120609011b0903 68
    0x102505000301100c0c0c0081100365003d0081c08107542e0f623035103c14140740c81c01c0c2d40b020102215004590070703440200c842c0c07402075541081c28402c500600c2849a0082c07250b41d0f01107451b0760010700d03231405240200c48440099940c400d41e5400d0710312481201d03d00c0c0d00011008010303617000340030f0140f0761400790400a0030a0745801e101e09200035104016a0074420035817000b00bd044d010b00c08540c2141c88501083d28003410012aa4030205010b0480d45e14043d000455201740341c45140d0150108600805450400700701d00c1005000c0c0c02c09449040250142c0d1f440280c840e40d80d48504800c0781d00120200d400c24160026000b120102c90040c14240e0203400782c50340050f550400b0359005030a1601640d40d0394200706003104210340f00c6500d020140171408070405445820900c1d81c0382c0d1780380d0600d4804208802c0f101111182d1410002c1641c2010800b800000d0f604004210107209000e5903008000c0c00460740a4100038164101e40e034804100814414008161028000d68100d41032076a1402c0b0f04d4071203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 155644289 1250 155643039 155643043
    0x7020d03050f0f190f08011e0e012303030405010e1309050a050313060903021c140f072309040b130b070c0201171006030c020c040e013306120e 63
    0x1a00f40303041050b000254029004400503103400c80420386103095500451880c50240c041001030081503441a0f0201d0300c1304c40c000d40310006101400d202281100c055954412002032052101c100304450415030900302101d003000000e55048880503910041500d50440503c00d840703000c541110701d050703100c07041c0f400802c00410103200440d104200540da00d01d45401d145070540203c0d00305100b04880b180c42000548d40d22149040e0707121040502095007815032521f02c4a94044002c1031559006030b54480b000c2c8140412010101e960544210142c0401003803600c2c04920a50407182d4001c0d41c1c8008107001c95001c070b10f115171111001101410305070403521150641d500031100b47c0d0010381b072000c40a0455920000003181c604498103610110b003004c4001c0041c1401e2402030384101561400c100c41c01038804c00c10709000707180113041080807030016404d05018100d80b010110180c0c01d00b50141b602c8032088105096860110f800d10b1405505221003210383c0c68009088090598454000a1620b002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 155645539 1250 155644289 155644297
    0x20a0b07020d080c0906030a1121090d0905060414190b250302060c090117010906030506070f05070b040305040b0c0705011103072102120705010e0106050f0607020d03050f 75
    0x150000c1a50005049000f000c0030401007040201c102c00303000d0200c498592800b13480e0050704c05c0300c1c0426407003400c503600d4101d0f001c2c0d0a10f017108aa0b101d002e100ca0304100d1060580035500c51401d650103120f190b48207035012461b61146580101e010002001241c448000740d0000c0080100640040c0c0d0146190b4042d500454104e0f02c000007000941c03102000d511240c284460041102040004003151000794a460b0300618441140d24000780741142c9131b01c11840c0100c440242c0f4440c03c180c0d611100300b00001c0085003c21210b41c07180c100400e100c03a00455520701100090381d5801e140c5082c40d43e40d445801e4029004030f05201c0f0902001c140310500d00050020008010000e00e0128a007500042c514000b14020400c80d070003c114803c042902e4144060b16a1400844120030007200302040b49016110681400d075540003184c6d0750100081900805440d0081d40001d0024903154400c00419110300000c1c075a00610803c4000c0041c20100c00c40c06616029080036428040b5601c04a102640 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 155646789 1250 155645539 155645551
    0x6030f0706020c03070f06024c0c0201110a11070902030106050c15060a03020f0f0301090309031b06120b040b041b02061b040b1606060906080c090c030604020a020a0b 73
    0xf6410000d01810b08001d1100200341400c0c00d10748a601e40103020351128111b03240341c1c444d5040b4076490302521414144030401c2e910b040d000c02d804542e0414801c60ba042a60442420190500b142c01c42d14a01c14081d0307000c0d025008072594507140d040c140035201d200f908028081c503401164400140500584040c0d030090041d619074968501d0318400e014105581040b06c9484c1006003428001c10740c9038803580b1001d695041e02c0c0c8101e80b0781603900081c01c5000345001c2662641c01c01d0030510070181d10000c001c04982c49481e01500803011314a8404030001c5d01c0c000e0b000060b4111965800942240c0c0110340c2d52003029200080122101000c60301f521049824480902a50903540d80c1750745d41000013170b91010140012581e100c108003800c00b007904c1070b8407482c010b82502181900e282e103103001c2c10150150780481d041001980c0c500351000076002038400d00c0054040d48010882c24201001100e210754042002c240c69580d5400420000307400c1501e00404500c91241c505000901502040d4010340c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 155648039 1250 155646789 155646793
    0xa0501050103080c011d0304050d081e090a0f0605030a0216171309230c2515090210210e01050a0e1605040507170403090e0a0207020a0e06030f070602 66
    0x5513116801d403d50341d842100707480c99071000c09400c0b851b020100c10741d400c1d2407044174020810605810300280382d028100180200c200554080744048060741c008001c880f03815144900d0050f0344071006c1041c0e04440c8940800305800304000350456000c8d500810b4003940ca0081e1510454080e15086150030301164049140c1d0030000c0c118071042d07120718001004241000c014880c036400c88a01c404918555142c00804894a0004c03d04a504d52000d80b000a10500311040c6070038124079160701e03031405505007920040c3d030352889418000020b00500303803415005170603212050300081c4200c9400800082070300c0c1e0000c4001701900207401c02e0080b280b030301281c1c00010980b41026a40036044650b0b030000040660710482c0008e150300b003900a58021180c0031a800240c55035664401e03940748081c0351620305800c96010804c0300301034005402005549401750910610303038815a98008030f214021000e580400a2141084049c0e59818115030182001d07054500e1402c1141455141110b160441009a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 155649289 1250 155648039 155648047
    0x408070b0a110c2b050d020a0504121514010302011704060b060d09020a1403061501090902040602010504050615030c04020d020d020307090311011404050f0a08060702031309091e050a050105010308 86
    0x29618098100590710010861382a0f2000b11a40640300d0711407100b007801903940100309802060b000320181c030000d10b0071070100070b42804c5074984880c0300b00998848940451610050030040503007161014140c0364181c6550340b5a51025501c2825924014012036a07240c50300d40f15101c548600c0b025000100c2d0405000c21081c41520412444020700d4100d00048812441c00003d0350b80c000440c5078011000c403003200002e05640b80100c408501580040c04030038000100001c140e41d0552045e0b1003180103a09840e2991507441c51643e643c0301d203ea034030303602d640240c0c6074074564036059004040c04100700500525000c01e0b50305100980c0c0003210058082743d485072040050025814511102d8042460096550804410403401e140528001c4501480503181c00014079210000004042e1880d10116081c03490641c07c001e5a99220f04008080da45511b500050507030410300802c2105030348640001581c0c0303034043d9120300d541d0000c041a0313400e01c0341c0808803010850070301c15036018500a44020b60f40b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 155650539 1250 155649289 155649313
    0xf06120b30010617030306011b0215070b07030e070b0a0306030209010e041406040f060504151b020c0d1208060a180209011d0108040201080a11030901150e0408070b0a110c 75
    0x2c41d410f540c0a913000e0b038110503660ba62010007004a0358032007000d003000042001c00d48102c2e654080d070b00d50000d4010a000d800e142400118401800c03040b481303a002040c442d95001c50031400c2c5c4034841c00c80c2d041e0794040801400034452707000140c0041c0203a0b140004186a883d00091582c4001703074010501e86480e4000d100c14001c0c50000d04d80c218820b0340041c0503c0c00d0654031a110040d0f0030300301030580c0342d4440c0442e0401400d0400d8035440d100518082c4450448401c02d40340740c40010000d01d000d403080b110100400d090131000e0a0b003a503003010407401e6042400b4403e07103204000611040e84660700800201e400c030300c59000e4111030440c14a006840b000f032704001503c201c4124024043e90704590050329526a0b00400265100781d081c607248480740c9550b1200d0003e80071075131403401206400f20401a4000e015032140348642804401150b1460341c2d00d00f2410084401d0324003900540c1d0800506020554580e18150885c0030881c1c005410b0f00416407451254020004512050308035100c0031031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 155651789 1250 155650539 155650541
    0x21023010b0703080606071e03020d020c121510030f03020106050a0504020405100309061d0604020901090207081b0c06030405010f241205070906061101060f06120b3001 74
    0xc058464600024681541500d024118050040100380f2481c1c0004002d010003880c0440442ca00442c001401c169030b50030b140c06900c843d40803000300014840e1191042561803d01c1c17814a5620f107550142940e170701011502604c400000300150a0140111000000130b250400e155101c60b00940c0005500c50800b001c10038a101c590b8040e5100c1c0d0300601c014005a0f60b103102080740c020090400081e420301030316080010b00760480741d0f0000140707030f01500e5a1030321010500c288118821030318501c06a89a0000000301e000d0948081d01d191001d100d03250505203811008001c0151040864070342c5507a150009499510444044034580d449007120514049140a80ba11042d03c405901c48441c03440c0041c0060200b05126a003518140d03603201009021003401100050400e400c01402469105c0501030141002c0d0f5080f0340c2d1561a00310300088071a9220500300c1036070381e41c1d039503ca1610482c1c4d6441000c0e1404651842c0c2c08001c8000c0c0c1070040c265803441b00540408040003030210001214814 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 155653039 1250 155651789 155651791
    0xe19060203090c1f0e041b1107050a0b0a020708060c03010e0403090305060403050405090a090203030904090c05090108152a0306011101060f060210050603030a05030912041d1e0105010807021023 85
    0xa00840c14940b507d84c00e19540540d032100807101d03161009410703408210b002d140400a51207660490170346c107000701d0881a0070004000c0203030070303800301d46640c7c0d0b4900144d81c0e41c00080301c2000141e082440140158846d4403645500035000e8640f0000a0361203072610fa08041040e9021004220001010415070034400c0144d90301c15a01d8a00b0030580c032403a008207440e441000c5003144519a20000c4c50704201c019480074001d0000980f55801942e141c810321582c8094460564060017100000181420b910b01e0b046082e01d05180078441e12803221003420b000a4101038006030500601c0001030240c008244180801400381e04800c1c0015850140003074203040c020f1112441c5035082800304450b0707440000c02c42c1c903542c0e494a4643e9896a8800441e400c0c00b801d0140f03550b0700180018002112415049020b4001c8061781000c04161540b0400700c5040035041d120801174110700d00100200c2d03010b90440c80d0f010740725006960b08110044001d000301c402014071600440e03c99180300318082510390048d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 155654289 1250 155653039 155653067
    0x1e0c0f030d02031024080a0608030d0902040b1507060207080c03070c031101020f07120f080c0105061f0f030b01030605031501030614060d060b061204030e040e19060203090c1f 77
    0x19900502c5d44540594401031082503101400303001d0020402c0c040540d03101c90020f2622005803030b25480d10281c01009007165440607482a418524150410720306900a80c50b0110b440c1d88079440e262403665284082e400203502a02c090b0024080310700b4a40b01480140142441001d030b005410341985850b21510f6141c6086604540c405122505409000100d0a05885404540312500c440c03c1c070780201040c01030040200711140100300e0b0081c40005400050050200315903200c20764820002c0210380154410350800000d4802807a4a00c0d070b402540b00c60350112045c503001c00c0154441e80070901d019207800c0d010000141c020010002e02150303104482c00c071760700502d14030a14103014000a100344083c141c080c00030340d514040349400f0360720181100c0700206400c0310301d0391524040c180503007180e051030b0b00e0b140035505003520750000e1a030104a035400041c00482130341c400d10f02a10b0b100000d410040c5070034201e01c80d80e031001d54207a44135510f4100c0420804000401a0181c810080143c0442940 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 155655539 1250 155654289 155654309
    0x60a090b0d030c050304050a062a030801051c170a120b01082d070806030d020a02150f09040608030a020d020f030d0e01020d0f020a030b061e0c0f030d020310 69
    0x180940c95520491040700d21a094900700d9440c80190614900f10720550b88040c2d4080c4401c400003c9003134120f02a603607a030201d9400c214400f00c00300183ea10040d141072000f0300207544a03005000520b09012543c0881c018041c65030785c600700f0307a80c540840d601041070000e4640c80114602c0c0c5159031001c80d1052000c1c820741c1c01c1c0800030210f80060400000035104035540d100c1e00c0c906080c204150345586414441d081d48560190801e0350002c1c01c040c2c400d40d030441c02401001c0340f5054041c000100c120045902801d0b0320120300d00b1107070b540340780d4201c112215814441004502d213140d0f01c40c040c1002400362407001d16074804190a01915040d6030101003070139034018240c1c40201d83c201009a80c0038134450034002c00d01c130700a909540d0080c400c2c007840c041c40320b1902c40020002640c981c00b034110000d468404000300d5003175070300300181d9001d800401440302140c090160a04030035400603188142801003100c600443c21052642190000c1c1c080f5600241d01004000c40f000d01e03174504100629100340 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 155656789 1250 155655539 155655551
    0x180a14030115080601030305031e1003170304120e0f13060504050603150a051806100315060b03060409052113090b060a2f16060806010512040303020405120303060a09 73
    0x58642c644d1310510019050160220000300325078914401c102500c03110301d001c05c40600e011760130201317080010702055805002404000280300040c01c22640281c0e0802ea2148020415040c00c403103c0c0c806120701ca80206045030f03612f11503111106294001c1952410110b001400d1a00f400b00303d0f44028011071103580030f880d020510000721091140c00c01c81041d80812079507252071000440341c00c0c84489421912400040000521081d40c0c04810f4038804c152200c4040c115001c61000c1d034401d07002d000d00380c20040010940500d080e038041920b45120314159842c00d144950b84a012030203011111400000000706800b19000f00e401000c0038100015041005a035030303101003040c40c0652000d0500b4041c00d031b0381d005401c1034011813041100f100e94160440034441c6108150303e8080c01685040b4000060401240c044c0c01040864410309060355881c1c20080101030300e410300280508203030207156003000085100e45551642c502c05070039100c015513503414000c040c040d0f4801d1a61080511520344a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 155658039 1250 155656789 155656799
    0x6010e010c060f020405060c0102030f06060406020c0d1505090706090801060e01050108090c03010507110709110313031103161a060915030319030c08070809070b180a14030115 77
    0x10505441e8035400903000126050120000c4009115079005203074050300205580c01c100805400031032061940364014200d5844850034032006010758014400981c126121194441c244000c3c0a2034443c017a4042d0001260840081c004850040c1c4040c01145c10039a014419560000c1c0e0200040c00400c0c001c021882c5000c481307210345007041c081c039410400c1c4140818000032040000041685009000b0803c0c0d0829070b1014003080b502001c81d180900480c07034000381103130981c03187c1010340e04650311540c03565541981201032820390740411420710011441100040b00108003408036040e801805064040c40c5041441042c6510605a6080c00c0700004100035519240900354000c0f54180705464072000041c0064214004c001010030303c03540304801a60702942c540c20603410382d00c4070f44566106450b00d18044070074034012a1821510340c4003880030403210f00030000074100c1d00ca0311740c3c9c049201c20045000401c14071443d4048280e40642c2500c1c9499850207100c1d05030303a042c00c840c036040128038007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 155659289 1250 155658039 155658047
    0x30906170705120c07020a0b1e040302030303060607140f0606040f1a060d060504110d360c050607061a010201061d0406060b040b03011404020c031b03040503030c100506010e01 77
    0x385082d580c18118407004521340600c000c003030383c101c10340c01402440c156485a1804046e504441e0308140d14101e00b89142c0040c1c0b804004803404d0f80e401501a500d036517105d00030300609502a500c220b417407641c00081901d42c008240686981100f0300c0d0f002c0c140504040d02044180c81603004410340300c40c501040c041402c06942e22807050f01506440680d02c5000c400000c20091070550301107070700507041410840c2245a0b80004140003140d658007003100032041c0480468410086d2184140c42c1076031080088216016400d00d850188500b00b41000103072a800455081d400c10b5208644240e1140000e989800200c0060326a014080c40200641440c00300740fa5040450415411304121000c0045014801c807500f1200240690140844c2e4407a036440058000f58030074403618080600d2030005006901e814000c4800130503662000b517090202c0050301c810005604072902d60303248820040060551001c0c0301034104400500003a094420001114000341c03640100230303d042180084810429a0700 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 155660539 1250 155659289 155659297
    0x71502120a020c013203040c17060a02071509050f010525030203180102070f0605010f0605040e0618090d110c060a0809010906020f04060f4107030906170705 69
    0x91a00b10b5610828084c0045c5801c0d1506000c000140003419100042c40c0000007580211702c1b5030b420445213030340d42410101040c0c11003030100d41d0760000c0340400d5030b461046d00900982030007031141c40c1c481d041c411706800844521181c115801d42019500d000c0c298000e01ca07280c3d210207190202d14400d0b02010907050b07010700140c020750501da404004990103e51029140e40a0b10b80b1400865443c00c40e420191302e080000d4104641c424140400402c24441c2c2c01d412004803030480d21a02d08090400300801811500141030036003086007400c1406400707002c1c5034072a01074001d0304003400320081030810080580b10fa4200d252250340c055000f04030b140c1ca0b0300048560400d05440d1542d55511070154580c05081c0465002e80704a0002c0b0300e00c449181068000c10071605141c41300c1d41612001d210030b03980e01000c02c103c42145507c0c102414000e0008070110001d0780c881040c40310800b40c0d070304100030381900b01c0202540003c0c0c0d5520240b080b1608045411240154030389000308900c4d182000030721600c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 155661789 1250 155660539 155660563
    0x1107060e0d060b030a0f140c01020601030f03030905060708090705060c0d0e0111030a0203041d090c06030c0d021b070605030f040f240b03010b1c06021b071502120a02 73
    0x15a01d01141c1071041940c85003542c43c0005003600c0a401c49810411308100d90345600303440344000882d105602000014085100070010f80103044c15a1031911008501e039000c0700b0603000d0540300d044080001c1c0c001c0c4401441000c4589410380c02d410115000ca01d840302c0d83d000315006920030441e00c5850100040c8030040500341d0f00e801c0c0c0b480d00081c030049481411080e4030480c58840420502040d0f034000c0043c0083d22000c0007c2405025241c0c0d41448241040e01c01a419401c00d0380115420b0070118010b41c1e1040d005070b00f0b507180214200041c4201d034001307021040107540b5208800000b03102804943c0041c91a45409401c609101030440030510004d070000340440500350300542000b604040c0c02e003000602c006050204103210228070b0242000e01c0d00d0038860351a000d4080d0941c0303030081041b800c081c0381d0786100710b181020380e50303070070084d401020591000c40b41000b02808483c0104503560140c10200b081e129011102d0381e01a1410302c2c040d500703100303da2080c003040c44c0b503030760006542801e41 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 155663039 1250 155661789 155661799
    0x403030608010c2003070512030910050f040201030e0f03040f030b060d08030f090a02040915200f03100b0a02031321060b0d0804060c031b0309050d0302070e13031107060e 75
    0x40401413686203540b0910000034034074041c2451070224031354039001039846115480d00755000c01103e105041c045030021039060305000d1004011502551081c0d11800e072190700502110220704504050030302d5604182e00074042c03468062400d2041000c4a00526041041920410408030040c0d540c90780b9400300038000403075910024001041c80d4001c112a054861b005042089a011a4100701c4c01d646044840744601e0303400e0890500f180c1d0b00f1031b003143d070b00c40c00340d610603608043e8219407650301d651004c0d00d8840c4407854a04e02003000141030300100301154194006681d10b6458450042c0c007100c140c1d00c101540002e018545c810a21811098000c141d8010000181400c960000031700b2031a03000c00241440b04007080220390107811091500721a40251140344c8061106000d51401e844000c0c401400500f041e1010066070a2103d105480c040c440d00507101c146455000c086403c803002c4900b4800140c4051540040c0340d0040701c800059040400903200981c10140003511520103031240502030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 155664289 1250 155663039 155663087
    0x20414160207090c052d030a0504061a01020c01030c03060e090105071d0f2205010e06010e0306150f0a03052b05072f03010509150705160201080406140a050403030608010c 75
    0x140c000441d03051441b0442d110650786a0400300302c00402410110303802c032852464044907422b06165140c000c003040b00140e008103500600c550044014107801c030040400c0c161901008a8412800181c25100b070310302c0000007881d0315050380010007801550482c8807a51034900312280c1940c03104407514001c49030035603c00d8a01500000e083c0d0501407404142c2801a140800210b104c1504c00d145078042c2c44240d880d114860900d4041545800d022365071244101410488803c03141401e95114803040700c003d03c40c0720843e42e40d0b1540780c10005250114042d80c803644055011801180d0340000c201402e500d0480d05082c19a80c40e59244002850841c900da000200c0034200c540020101000291001d8028001030a1482d00999260008049500c00a010000103007020780f1030401d6079134484880c903200b540103070690019981350b1005801521a02e446215101d003034004404058055041150002100d01c0c19040090464440381c100d001581d040c80398108030141c1c0100c3c0030561280b0031101480c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 155665539 1250 155664289 155664337
    0xf020c040207110301020a020f01060515090f011b0c061403012303010b03010606030203010e060d020901060f1412160203131a090d08040f08010b010912020414160207090c05 76
    0x80c602c0070f800899419800028031491442c0d010070219580c804640c000d120280d112005c20800443c500c01001c0054024080743c551880c0042c03d06c508000181804507000c00516103518804c2261326054a5200911400b00491a407041c1c440311155081d65006085504014124041c0000c1c04814011110642c2c012980c6540c00e610408541358018000c01c2420350350b00340a000794100744a90344405000700000303203440c20140024100b6640c0140501c02c0d90b0b003001d4055074252450f0300040100302e48070b00c038140140c91620041c03440701c03041c00d5950400d02d403984070800405482d880c068115003080c003424414002113240941620555080030074521120300d04004540500d00c01f1640c80790308607441c442800300400c000c00607114500c0a83c6c4016407070304821400e07502441c42040c00120f441008003d0003444250030b180c9513100420100c6c400112803000d009c1c0365825100e5440403c1050f9a4610305501002107100400c1c8440c0280702d85459448080c0c10f5008940601c284103821600c0408 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 155666789 1250 155665539 155665553
    0x904080d060b04080703050c03070b071e0602031302130903081b09060301030803011511030a0806060c07030b16080103050606090603070e0702240f0402040b0402090a090c030b010f020c040207 84
    0xb602410280c00c0d16165544c103015982c2c03c4a1000740c685000e40c039001c800c5801c010655400356800074486520b0100c0b950f454000032003107035032003200c548000d441680005d03945000071401005800c071091a60035641c01004100b0a1120782c0c0302160b03190001c0342c0006074000c281c1c0c41c0c0c4104180c2414290420f00c078551025031007201d030290380c00b05000001104007c45072003d541a40c03401c07100400750200c00e10003543c114407007a280c11140e90083c007840d000300f8802d14a06501c408003800072b03801c100c0c3c0e41a0309841c2c800c480c0c108840500390f03c8100b00d84d003066240c0c0c00c49407101c03038900640d81e9403450300d4003a00d817580501031601540414001070781c2a10304004d000000c003180c200e112120b10700307030000a40301c85a008590100500f000c0701c064064003208090790084401040e94101502d45500b0000244401e15141c1e4101c2e8083c40b2070101a0b40c7e0740d01e000018940618003281d20354001c07600600700d80c0718851441c10f00c007440c0464580b4135400284c0c0c01d4024002d942c0141e0311001418801d07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 155668039 1250 155666789 155666801
    0x50f0c0c030702120703050106060c2604080a0b07020606190902070501110706150b1206120c0301090c17060c04060e030a02040903020a032a030c0f0c0b040e150904080d 74
    0x203500100308020f040c6448200140ca1760032680544c00811005445001c103c802c140c2244014005030000c8815620044103400f140c4410294116528509541c0b007410740e051455640b0160b80300845030b004c1000050b01803140b5544084120b804100f04007402920442401e031600a2031416580401c4100402200b5880354426605100c141a141d1b0020b181180140c042803840c00c040c0059044001445810b0005450b2030f0040c861050000b9074032081482045840c441c0e1740a44e6200304640720446031028403c950401d406114004002414191403800901641c80c01526030782c4040100315406460704151420b6540500d000400509400700083c60b201403000301170350240c0740900c4007080640008440c620903201c2d4032041038004428150a42002c41c110403400d81c919100010300021388181400c000e054070548000c2e51441742c070f807116806405160080030030908002000c0c820900312076000d541c02440c0c0d17080c400300592101d01040d0303450805803004100400119010290080d250014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 155669289 1250 155668039 155668043
    0x2130b040308130e0408030624130906050a0e2a120103060c020607091403070e010e010315050907050103090204020d0c030b0111060405030403081e03010b090103050a050f0c0c0307 79
    0xa8545449003000402c5501460001c8401580c40400064007441d80c02c1007440b4507080010541075907101410300660900c0c906800728004200040092408980c50140c41640800c080541640b4200720501c004c0b9460342c0c000710711441c40400c08116240c0a8100c0950000304440b200c1d0581c08480342400215021131a41d000800d00841e9400f0100c00c854105412070780500c10a2115150644d03060b40c80c0d071425a103a00004030100024040012146000c61039504043c080314891030741d400b00c1511500d000c0e04425407103000e00c0b004209000e4081810140503451110412084c00c4c80b03a05995610022703c11a818907440b048850b00f03659890741079030301d0f001c02c040d8180001e07514010000d00410706040e00c40c0c04103c80402c1c803140c0c0c2c840080e01d144a01c7e4850020b528160564440740c0c00f982101840703404200558000854010394a8040d40c024081000d0312030b03c030b0003c00f0000d81070317507402800098268941400c01085054189040b0303040f24454000304c0d0b0b074a0341d0400441c2903105540340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 155670539 1250 155669289 155669309
    0xd02060412030c2604060b01030207120518090f010e1b0a0822030306031b0b0d0b03010e070605030a0c08070e011805030115170309060a050d06050d05030705060a1503060213 76
    0x182c4194801c20032507205601c03c1c4001c0100c54647c2c4019812801001700c00350840410701b03c00181d46005400030300c402c40148603200d004680038030001d0080307142228140010b00c441801040080340308480580c000c0103d04501100c2c0c0808203c3d1015406860b0800c1e04001c007400205d81c80c41c0a803c854511900c1400c02c010203410941405000791031544411985036019081d256120440d00c03141009507105105000e00d4540e0a0700c540c0040c0c94120205603140d50790304c0d000203091404000210023001780d9160f207a00c0307107001d00071102182c101d654500c0500903408100004164402a200b5000400b407c104002c80c224403d4039142d1356440e00586e41561a003241d8820004000801408848010010810103103121103110703101d014a03081950488410b02013000d0980c00394000d0070400401d4400018816507071000640d00c41e81803141a1696040010384030184241480340e16131200da444428842c207040501000d500e64081c0c48094903041d07000c03c0804002d03000001040040041d146 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 155671789 1250 155670539 155670587
    0xa0305040807060c050a1103040506040605090402090a030308150306040f0201050c120310050411040302061c150306050f09060103020114220b0903101125150e0d02060412030c 77
    0x14050f0282e445411b960010806114501c40152400003c6809542001e0105030820385003a100f42c5103070300a41e0f0010380c41a001e000e000c2c0645c68014186000754040d0761005140c1c200f40404d8400848541441030203a00460700b00008110700315181c42000b0390a1828aa44512806038182031609240041c800c040380042404001c280c01510202512000c903010413512a0304940b13002244034034400250441000d12107129507448010110080c0c62524002042001e1a803908000c00e1001c3c0d0001c0358040e548800388084d0101050802d903214090b940100115411500082d240c034500003006800c0500000f15001c0402c030300c3e08400c0d00c0e5400f84291324800c1e03499103500805904031004c03260281c45502a02c4030440524040c002507040c3d03000d5410324000018120800080f0202480340c014910f80d450440000d030101130748000492a0040003845400f80d500380360038101558094000c43d4012814000860100661400031400d40d0400090302d1a200c4801d48401c0c64601d00c95007107806000d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 155673039 1250 155671789 155671811
    0x614060a0c020a060e0307051210110c0a0b1803031b0319051314120319111206040f020702030606040b120706030203010603060b0711040b01051c140c09060a030504080706 75
    0x14110340c08003011400d41f101c0b02c0d10f401c140000c51990388140605a80b010a00c0ca011404039440708450042c0c8a502d0751a007606a8903441c54030070101c108441c041c2c0c01000700060806070484c55590040c018015510f18284401c4004000030928101e1208941c00000700c1c288400c10300620700020002c0700180315601e00a0303034800c0c000292030420380b22003035801c1c0303e024000c40101e0b8054203224111500c5003142c0300c500540079001420700307800c14000c0e84c8401a00918800300060038900b94013103013001440c07511009210650305503c442502c4580103000020041c0d03000320b02c1a42c0000c0c10380d40010301c1040c00b00010b400f8080314018910301d00030310601062003641600194169902520140b000e595128560701040c8181e5002400b8644a040d00f0900d901d020707040a103c110381450070608107142100010608503044420601a0b95a9001c074003d0080310f100712944482c0882c012428400358401144807841007110840070140d41e50000b804010320702d019101c0207600031004100c42c02c114 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 155674289 1250 155673039 155673047
    0x1080a02090d031d12120c0709140403180b0f0706090822050a0b03010e0702010e0f0f0c0f01081602420412140c1b0a06030614060a0c020a06 62
    0x65400100001002e901d0210303541000001d19007405c0c4000000d004c15108904500c40f2500300070032140c4140190340300022420070078060300c45809000c0300465158241071402500307104030740001d0030300106010802c021440c850070030359440d08000340520341c0d5000c103458036800074041010010004100400c0e4845110b14004542281d0b8002c00c00340c0c02c000392142c0400c10001c40b641300d6039071592810001440f20284010f05103802800740d000110384503094481c0c9509141e030300d9020184590001c06155584401004080414070041c0d921030449a203241c00240291002020750503040d10070641c12403c41d208101c40714540c0e001060100100f80035011400f54400c000c140e140c00d401307072a040d5480480e2040f00207030140358010499005407a01240640d41c10210811204440100b40031034140d440c03090001400404040c100001001c04810030450041c0c42c40d0403100405152007400d0204869001156440d080d040f6542d40d01d406901c582140d02e4400c000c0d000b9008950b187c4000780c81604 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 155675539 1250 155674289 155674307
    0x203030f070f0c08060f06010e060c07061806080f01090b061c050612010c0c03111f06030b01061d0415090e01090506070c030c0f0f020603070f02070914040201080a02090d03 76
    0xc103c1501401c60350700c079995a40e0311400c0d036946400d0060a03000c911158050040407604440113001c00341412910350606041c1601e9901150218039403403001c601c111102032504002d840d4a080080301c40c1444100902d0500c4140034a401c00d07a5107007500c0c142a41c0342410b80d50388441ca1044542d8550800180390041d120654055003d000344040032008044180101b416240850303076140b42c0e040e01500c048502030200100c06403180140300e607404140d01012440d0803022094000803c100f441c5150843e440072050b840001001202c181d0010340c001100780d8108085011540820004403516030390f8800c04c03165103e6070300d51b40341c0b001c990071001e010340200c1440c0c0d010340145d0b141c66461440956a90183d0704000700054141140c0c04000b0700000408540140a402e140b0070001e01c3e54041001356000795040c20204140800d41c0c0701555040107000060480d1041c00d0244181c0d68010207034805010300001e06000c1e1510002d094000e041c0c0c151814090b00402011810140341006007860103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 155676789 1250 155675539 155675543
    0x180c0c0d0512072a03020309030606040606210609060303021b01021b0402032502030301080d020307030c062d0911062805090907030e06060a0b0301120203030f070f 72
    0x150310000e10581e0141d8103031540d00714100aa81855990640d04071001c140181c190b00800440500c0c10746800c2401c42541c0c84988607400955403414280205440c24a0082c4482d1045041c003138184441580481340b4041d0b607040765000783c10500c10002020103003a468200050a500c0c00314000245603000440c04182d1100c10b0084204980980c01207071a20b881000340001c4604c010349102071801c2c140e00859018003084040e507401d05481003a011462885550040180d202100520000c241809051108092400290318240c0f907036401130711024a4450240c1525500c000e403c0e0000d1404211810b01c1031205180c00a21041240d04d1004040b20b4800344d030900b0000d51008828188034ac220317003946900c150344000304401c000414001c0307039902055004100c0d0510003c80e090722100c2e8103d028180c0b40d1008240c000804100e03529184d001003426120f0001240c0400c03d140d581c1c02200d040d144859803d00f41c0c002540080b80c514401c0116070300301c641c2c002030351101740303c01c03101c048010074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 155678039 1250 155676789 155676793
    0x8010e09070b040515090a0308040816060f030e0a0507060503150306060307050409020a0e0903030a0b10080103060b03030f070804050108090f070b0a0905040c0305091213050f180c0c 80
    0x40c44140ca025034418a50080503260354007040188140d00d09034003130044010811000c50701d010b481e000460800c1d070b0141c0c4116407128010134140300d800e100340000c1e0b949210350f5a11080f42840d042d0300400703001820f24550141035445d804008000d80c107206100c0e000d0b8015080380d00c1c0c42d0f0784540090055008403050f051074507004450300842d1901080c4035001c0c8000400410344641810308000c01010203080c22030b03100d06016800140e0744010340c249407040308d1483c007640d100e1501c8000d03c826614900c1505224610702e40a00704004d42000c07140303040d2504400005011380c60741011034510711400c0e4060040c01d4001c2078040400c1140070041c4107803030082c1d0b10845107840d6008625910b4903446060540c07500f0150b814060301d41d1040240442c0c0106140c450420350ba18400f1030104c03009102804006501e6608000d414101040300c11500c00d5145880b07480d10102c0181716556003042d00580d03120310385004480c019580c0d852900c2c0300786502d0341c0104806080050140700241d00441040840d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 155679289 1250 155678039 155678041
    0x105130b010602010e0a0b0702031b01090204141312110307060213080705060f0c1204080c0a170a0303050903091009060905040507090e07090801060902070611070323071208010e 78
    0x14038418011040d0b00708920f40240506c07042540c0b540000c0740010703c0c9500b10300c414030882d16180040784072684d034aa158000085c400c0d40c140180000d4400d2890800080e042c0a01400044542e03514071346e402540200d802403110b8018601202e684050301c00d0340c0914400490304000f8000c0e558018070b064805d2040034400c0d59503c10031070b521540c1d18443d5aa00001c1070040a50503505100140005403003c82030321751000c0103e0301405142c2164100030542c0c0c1c4400f107110a5801e02c04843c0d0040c0c81d2604000c010000312411403981e440c0c40390380040c100368540c400b0803240321040050b54201c1c800140448086141d000c002440c81c1194851040081c800310030020b2a81014850035000e11a140c0c0c2d41d50302582442140501110050920b80411881c00300024403c2028880d03000070f0000c0300c5001d40d8480d5503080c01c40075188074ad4846140e0040c10080c440000b40c01940c820f07441048403031442211500000300c0e584074000e0180240c00b04251885600f1480e0340121524140d0b082100700802e2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 155680539 1250 155679289 155679299
    0x1b03041409060406050306061e210f0f0c1909060314060f040f0b06120f0c0103060506120a0c0c0b0708180c0d03080a020403140c0123030402010e0a05030105130b01 72
    0x10744c0d000380304198040c0c10203400300c1c01350306180800007680071403c40460300421030400403400500040202400c4001306006066001c0000d21000002015040082440203a51010b058840c01c01440c144c0c825802200302c1c40c1c400750390003190741c014206500100401c594a04110482100c039401c49103450095030005880000d5040480d0b0085402482641c3c054410340e455400a50028108a60200e860001360201500812036800c40070742c5480030b4007005815000240944038983c02061164406010b0208a10100c0301c0c1d00d03900c541080d10100c2da80000000c1a10340e5580450302401c40040c7d0402c001e159038011103c1070003103540001c00c04030403040c841c10769100c072000d0f01c540745d001410000707030004a44181c00550b048280050700502e030551306c5e5600041401344540c903049070381200c181c403145983c00c0381125451000c1c01c10004c0c40c25841c0c410010301d40c0710040c002814401d103c44090225143c5141000207082c014008200500300f9100c5409000c070035850850341c0450100000c10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 155681789 1250 155680539 155680541
    0x504080703021c08041203090f060c021c050f0901140d15050a030816030210090507050f030d080109020d0f0f020d06050303040810020d0e0607080115020706050307051b030414090604 80
    0x1103121564440c00240c440e942e403400e20211b051071680405445502180100d1070b00380050b10803034800d80d000079154403e0726001e42408071640c9844030847c0b0080990b1400381e00001260108400d140301c00707555010140050b9405900b003002484115004103241001114a81c4180200b207110900d40d09000d60700c50070801c081d034403404000c00940301030040210000c1c250441c840b00d20702c0b07401176815107554413101e1422201c100c2d0701614160b1207801c0c03c1000c2e051164813110003800642c060710001a5044000d8035125042c4541020140d0010300d0762101001a441352103c901030003030030b005104902d95204007035001803100381c542da468504000f49518000080b60b0807100b40c0e002801c40c00c414040c0000081d0408901110000c1d00d400f02c03140b9031b1760709100007441903205072101074203941400b0b181c5c00040300745d407151029544a00420300030030b030700035003541da1003241c0b0b1520035a07a1b22000d10602e29a0002103d001c01c0744004075021a00502c4051700220f00c6100741e4400c000c43c1d40380340800c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 155683039 1250 155681789 155681833
    0x8010209100f0306030b19230121020301020a0503060f0f090a090204150305010204060f020706201507031b0813030503060303070b01030f031d010e01031a0301050408070302 76
    0x7603001c100090015001030054982c06040042d508000980a560740c44290719000300300c480800100840000100c00b594074402c590351190b5042d0b8148558258180740c01c103646d41801102c44611203403a10143c0407100e22510260700307502134000c0d91140e6001030090440d8101b03a415502c5801ca07426580080d050105800401c6035009100008540310000b812004041c480005e0b42c1007620345040c401100a0000304000651142000603a07892030320390300506540c5013012180c1150480a0b04010440d070022a10800c1c0200c5051030611810b0f08186034949004002082c403114a6042042039440d003561024941c5444080c10300002d007030f02d040c11100085c00315844000020480a242c002c40d10440c0035690014014040341d20341343c0607441d8189004000d0b03004445442c86003d81c581010390022580038040c00081064815a6826002074801001580d0081c1010303940c41e2140c0c800754074003c54240301240079000300014103003814000c22542c003100c03064025220300c00c2d0303a002078a109002c0d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 155684289 1250 155683039 155683057
    0x18190b0106110607091401090f0807091d0a030807030b03240c0406050f0d09050604080304020a051017041b0605270303030703020705010902040c050c070e01080d030b1c0f0c080102 79
    0x31040040c28050641e1031044000f04c030604000c23401001051409801c01c8100c003411030302004202c86880d109000d415105030142c204a46d80c1039a0300810b44075030020781c00c0405039060070321420316601c507002100103011a40d44070b030b8144202c9000b40a04d49041108401c1b940e41c05203441d1003a9541022202248603034451000010340030040100c0f0900d07000d019103000000444040b802100c0c03504e9280c680360081c0e800380c801c1c00e400020b000c11880c148032244010a4240c0c0d8076040d6082201c0060311802c043c81d03001182400c80400034040080d400131421320030052101560905445500050031034000300d051441000b65011b12080502070448180c801c404000c00441c5182d0320641c04a000c1d40203040210307a25902e8980000040e91a40621000600c081e1369079074840480008052034070900b980152a0a90b5403801813040e45000b09182404440e941404188020440081103410322070502c52060110210014003c10034090074150941703008881e20740b00345403100d06443c01c130f104031000c0d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 155685539 1250 155684289 155684297
    0x504020c1e0c060316081501080118150807050f030102030f18030705070e160f0e0415080a0b040b15060703030e0c040e0f0106080a0b18190b0106110607 67
    0x52504288186480141c8440c0820709a0701e509400304007092503508150b410404014880c41d4100300300364060081503000e00e0038401c0720042c0142500292103d401800f0b02c0c2000c0c082d10a0301f8040d80080c3e003141240c41e144480c9203c5566442030341c1a00ca011500400d4031808030342042c508a86014000e407401240302510780c41c41e0f9114192070701004040e80d02d00403128001800511301040090012000a000b542c030040d40600e1b03e4907462100c1401c0942c00b9061182c0910400d01855100c003034051094000d0300c000030003200b4100007000020280c5e20405080c8249900c1e5002c03c0b0503a5a801d0103140f00e8400301680d034442030070b1014a42d5803103003c19040b5206000c0a00443e01c42e4000c45200c020803402e031015900359002040aa603000028081c2c035a011a07000c0c00180402d11429004203141c1000d0884800c0a644501c03003540d01822080180d1303010050888500814040502010340c6070300000a009064504891494000d101d10310205050b00f0122410703002c0420b4103445600c40d66a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 155686789 1250 155685539 155685553
    0xd030509030d03023f091c08040512090d06060801020409060f0303020a0308060a12030c050706051810090503060114090c0f030708280f0b030a020114030606120f04020301060504020c 80
    0x40e850880b10034410750301c0b0403140c1012000009505013079176401070420300c0281060081117840000c80242c0e1506400410513143d0401c80070840100700110706002540c0040d0f5586500000103215030440080580054605600013801c004154010f0003100c1602005006032aa01c6440c50903815003484050050b80001b4a0400081c0c80340c2801c5900180042c0018845034603045e0070046812994001c0b0041000d00101c4404d000003040044010002440c00718581460100b2040e0705500300701480340101611001c000c110f50151a0b20000b134940502243e91541e524064040c10014032502d05004180074008035142405650480358034800942500c1d00e180c4030707071204403021003000b442e100c03101a00410128030300c44026551000c00301020b101040400700d120b544c3c4100d42222121b1442640504d00110041c1d800c00000b20807890380133000d907100e540d4080812414400c143c0703800414040841000310304450501d04134000c030b0003a0000c019498890045c00100d00c144600c8203c41c0c6e20100d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 155688039 1250 155686789 155686837
    0x503040303050a0f14060112061401210509061f120206090a0e0a0c080a0e07050105030406060801060b07050d0804150b0d0203060a0203010312080f0f070e0d030509030d0302 76
    0x90003094101081e110001030b40480111307158125102d030140c802c0180005010301030740f0340c1c0c400e410303c002004401e42000102c0c034042c2d50310060311110780d4003418041c480c902c0c1c050f41004240f0305080c031422514244150314118074030326211030044914480c01d00c142c01d00e005040c02e070342e5104030030345aa44018810200c02a020069590000400c159000100d11b001142003000e00103842e000381c3c00d1881c045200480d064000e800301070003e20700f041d150324049041c0090384002801808441084c240141e5946890410901070250f68001c1e003100d41c20103000083c40b188400c000c085080c0140b050340c00b80d0070355590803074808400780c0b00030303000c004440e5020070710402540c00100c0210b00140800203040d015030209003051001c07925840e6030740e404001007007802801c400d49480054589001c0c00c140c500959001d07035804010780718400030200e443c0003900c3c0038000c08026480040c000e00c03140ca44007a40c50000c2980d8025400d19010b0f028451005001d28068020355030001141041406035440380 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 155689289 1250 155688039 155688041
    0x90c05040506060c01140a0f021c0b010908150604110a0e0103020f120414010605091303050a09030f050732060f0412080406020c1e0904020f18010503011b0503040303 73
    0x5442c0710361062040200c080e41583c01d01c580300131034100c4405840ba903e002001c28044900e0f07403a113205154010440580703c024450000703d42c1c0200900300246031481007004031010714640d013001d00346118242d07d911a14000201c400d1048400715414030107030800303102c1d111980c0541c900c05008202407202400b42d0358040e0f00030303100e11011200c1550500310003c0072031600e9002654103854503590508595076048081c0035a80240c101510166140d00740103203610b03503080e009030340941000801320310807400d01e00c21091400115002415078082500c2c0e400d00035250344051007024042c9401d090301c03aa403841c0700d240c09241c0c0151a501114146584010b0140c260302c10890902900420407000c248402001003411045001e10711690301c0707034100503003c0c7c81d109041001d1032054106614a52900704030080842c0702e0007081da000d8050341c6030b91000c9004040190070301540005040b101110b18000031407294104d540480c0240048081c240010f01065407002003c0005001040010042402 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 155690539 1250 155689289 155689291
    0x1a0d03050d020f071101090308071103030f0c1506040c02030f131707060206100f0312120c050a0201230115020f0706031b0806060409090203010933090c050405 70
    0xc0c10414902001054140100d80c4041e9a911201c800484c030345050010010058a400c1028280b070500c440c11502ca401c480d0080840003440e9401d401c0000c415901d0500507180a403011001c500d44542061300b406d0f85130340c00b044481440b1000e100c0003034680d01d0580a10040144190061464281d5480c1002929440391aa00505c1c02483d180055600300030035254143c07c0e001c8025054050514100a00b0030901400d2006120716002c014400da400901d103460450f5408071500b0206001d8000685001089840340399445107407444142003281c0000c02089080e01650080000e042c0040c406050059444104a90754411000520400c020a001d41c1c45841c00341c0100c559203e0214181864042c0d140c0014000986510a40540000350071201031848158284280300e840e107800400c0a502461198484194a80b02101c0170b41d1800e5003c01c8203ea00880302e8074020000042e0311581440c5281c034401022070001101e4030805541c07141c1e10146900c07064030301a0302d1a000400001e018 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 155691789 1250 155690539 155690543
    0x40204050d0516060f0807030e0a1a1602011404140718090611070510050a0b0603040501020a1103030c04150905030a0b0601140906030a09060605130603060b041a0d 72
    0x1508010218103541c902581a00c4244104001c203000e9114006010250100790700c5002072010b800c2203c00705075001080b60782c0c015150302d40001d10a0b140300c00c452074064504000342006c10030341e221008041d00c4140b82c4d80319511304002c000c4032030140e413001c9003200e4042c45c10464000d504404100080c112041028000c3d0124045844260b2581081d0060001da081c1210f105da13914800700041161034000c40c10010b50200660707007043c10325200c2035280c24114260021240e641c2c40000c2220035a54450305070360b0300140207070303803613180615100e8000e5201100e404080342c03401280121a000000441c0c0c801e81c40c030300469040c02d1800550044130030440303400340d09000b030b03495010902c0c0d1400c00030341c0012800b03036080e0707511828420005401d201c42200500f100e614100b051140d25110340049a421035070800d000100b03c003460030503800400c0c8a07001250b202030525807441d2004001e42028007942d002d40e0f01000540b0110f0100300840e440180003142e0310f01e411440400300e240110410300118 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 155693039 1250 155691789 155691791
    0x120109051512100c08090a03080c040b0a09030501050f01050d0b060f09090a02120601080a1419050303040510021309020702120d030c0212070305040e070905090103060f23011404 78
    0xe0340000550109202c40001c9210350010403200120b0046000b260003809440c2410003070340c2001080f40341c940761032940180034062044041a0102607d908071001082c0e05403500c0d8a805441d000102104618030081c0c50702d600300000300e01030740c406c103148034122000142908501c2000d80c0d200d5040c20002005660f0018070100391120a4864500151003443c9210240c015643c00703204121540500307000c2c0c0d011650003000184102203000541c81d540c1034110001d00c0c00d000400c04000d1a102d00398071000b0408500300a524100040040554000c61141c401e94105800e001400302c02c034000c00d09041a5245000c808115014455000b000c5145c00030f0119101c00000701c4a49142c030381500701540010343c2d140c0254031402e80c140204190015060040751500c030050b180180107014500a06049010781300214003400e0041d40340300b00034840984100c4036580e49081010080c555212051445810800100409440702e110120101c007050b4610a141e401c01e81c4080010500c1060f180c0c100e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 155694289 1250 155693039 155693071
    0x804021c02030115170109051e0109080705210f1608091206100b0f030403030b030f010e0601091b1d0f0d0b0403030c0801080d050a090308030907031712010905 70
    0x981c0b000e0103294190100c95210f8580d075803070010401007a2a1554100da4240d00d42a4001d00140c40031544076619030755918488042110500c21760300526a0001c02000c81f040010182c04100002c141d900c00601c011241045044010484140714400c04081c43c100c040108403050900f4050851140e1079401482d801e07040c01c130354401041c000d12400381b08a41b907601080c100a10000241c1000001d810b2010555042007415410620907000207031000b07007031544522076011952001c0225082d0100004000e00030000040300c000c2e1103101c2809510051400e081b045008845203410b450342004d05903403501811146000480088400d101001c1d81c044d040c070202d81c0095071142c1407529182c2c00b81080d240386d403c2c1464060100c03088003001d141802000c20040144040c0428560b40e4610780741426070707403864041421a0711101c2500300810074a004410b00c40c105e580091a030040e6071042d011103520f02c0307a00c4591546800b079800f02d21503030410b1200600440384607400040d041440d22040031301c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 155695539 1250 155694289 155694293
    0x812100503010c030615050a050d0203040f020d0309090b1807031d01090302011e1e0203070203090a060c0b01060302031b18120d090909030507021e090702030a021c0804021c 76
    0x9680c101000b603c0060384400050100c1c018000300500f002d101401c1061a00501020142443c0111041041080e038040000b90500c0500d2441010f0280c0c0200901d001042c1482c01400792100ca00980c04200e28020340e1420600382071502c0d400b0b2450284c072103034155545103003c401600010001d070743c400180024080f244c0009000b100c0a0a2113038001191984a102d00548401041c42028810030300b0716815542d24401d441c9108003c0654020150741c90f601d0319000d9240d48100d031310103904562901400100b0b184e0050f0354400651041001c0407090b642c80200300c069000550701e0075407074000c01280d03801c20320342040140f00101c5140d0f540140c2103001000201540c160f510125490380210580c0d50801d503002182c03102070240844200b00000312518002c00720300a60a00901071810f100d03003240e0310822151041005c400007410714030240703820340c00217441350080c03036042000d4400c0184402d4004042003e03016003203c0c3d40d680911340d42e20b5030200300c1b0500840c0c90210402024142401c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 155696789 1250 155695539 155695541
    0x50c090d02060901030908030a0c0810150503090304030c031202060f061c03181e08030f070201030207140a050309011701031101050f0f0d05070e0f010807181d0f0105030604081210050301 82
    0x441000c0c0c09c100042d40ca030320341c1c0c40074003c950000d00e50141d41050310030a0011541e109458004503003e850903c1c1c40350344000c46a86903214039080544104c2021364000104410500031300d00c8640d165080d203129407607244110f9507100090f5503056000b0140c1149002c2c0d04c00c5081c6082764640203141040c003041c82520300720200741403504610011090300750010f03144488818a14010305480000354607020881c4480c5203d400b0342c000003410150006000d60601c03112146203031240300d0050075601c0800403441c1660356541b04003409030201c0d801c1400344072003001021a10f8101d03a00301030041c40010a2200444096001c80d54402001000340904040d130300700d040290104d44002d030000591410400c0d805401d240154100600c00c2110040d61403560f640503c15035081440390401010303c1c56131310003000c00490103030802d09405044089032082000301c900e0603070140910400542007662100c003410b803110301c111800703803140030208509500c80050b4032001d58008910349210015545820001c0c1c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 155698039 1250 155696789 155696791
    0x1401060302060d05090c060705030d021b01021215010c080f03040302030c06010f050102120a0f11010b04091113020c030f0d090c06050d14010f120c0801140901050c090d0206090103090803 82
    0x800d9a1340d41e1820810541010010880c150004072683c034105585969241d030381c3d1256044564030a90082203d106145030121008004140d010003551541c030050403a880c1034104840440c9403591409130b1400307550080350020905504903030f0740c3c0e1600f0b604901c88a10f0381c1c4080d0049045100c1049044034000381480064060700249401588851511000a103400030380d0310a0341c400e0303204000d80700f1002d41014407161008064141451000c120660703032401400c141c0c0b0b05941160901305030b1020000c030301c1550b13201d0700400c5802e499281001941e0000728080c00222200c03550041084494120b01d1a000e8445414101300228038000203980c1e079641095035a0014022440100e1890b60a01103405109140c405451000d40650b00d40202c034043c030405845803508000804003020248400d128010026000c0e6800078080d0018420a200c4102000c4a2070520340d46044027180c141d0980508171103810741c1c000c2424058407002e0b020804281e00804009040c103a031610303c0c3c00041d050300701039 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 155699289 1250 155698039 155698057
    0x1909090512070c030b010503031204030c021815240715060b0a0503010806060d05121b0106080a03020f0a12050309010b120f0d0306030b01030b180105040c05040f09020a03140106030206 81
    0x81003103d0b185161007030f25640f041c1c212170701c682c10030b02c140300140c414610519882600752900300110050340c004504040d191480700108580e5200c00c118004140c102012a106c00a50b281054901c6501d8485400202c9407135808480104200d8039000c1805041c0075441104000000107259079901010000342e80400364800203c6d4010004000c60881840307840c1d8060b205a5400302c1594242c2c0e1015251900d020480401c01000319844c004008070080481c19103c1c120000c10110762034091455030b03040707075000840c0144984d0403c0706120b131010270f00c440e61560103104442e003440000000c1d529500028045003a940d6103145141f040d0381c4010701440e62103c85009004c80c20320700c2043d11300341100300700c031603013498201a000c00004408407402030440b904104a115a51541043d0100e039011202c81811258200ba043c4420301600d040e1403800c50754229002c1140d11000030740c800941d481d10740060b5000300599008c1003c1024002e0351216410b0394400052407540303a1703000449a030040d50030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 155700539 1250 155699289 155699303
    0x6040303200a080601090509040b06150f03011e05060a0f03050a27170a05030103020d030c170301062c01030b130c031401080c10110109020a03030c05060105190909051207 75
    0x1803180320358000411b8406060191f44031940c0f40383c6500d0300480c20074064080c500503a000801307200038102c0482681c0c18640d0f441c80103a03480d40c1d80c03541034004619400c1c05100980410740001800c1c0707440c0044500c42801c903280d9420350045000c00358000d0200070035000d01c7c0c0342c5480c215503010810782803400c101e000d6001c0900b0807100c01d082c48a40c40c08198509800b18404100d81340300345400a0607241120742c110b4610320000d24520b001c0301c4101040000070501c02f480c0c0900001d8210401c05035058070880d58500e100b000e402c9960704d80640003274030000010141111911385030351007a041905401d8019202520362800791000c00308440d01018510f0000c0d80d1690101103c2c40703241c1c41517004060300d6000f01b80e88040d074000180c500da1920003000c103000944100c5030f0044001e400c042040d940051205ca000d80e07580c10050000b0003129003c486c5406520004110b902d0030340b03d0342700203040c80680460310500300004400140f00e81d10060300c1741d204080440380c000c0e07401c1d40200700451013915 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 155701789 1250 155700539 155700541
    0x1050909161e050405090612010912030b01021b0913080d060515091c061803171305060c0a0905040e15010605040e28110a09080f06040303200a08 64
    0x220040c42290310264100c184014101180b040e680d00c40203541c02c0d21011035401000780ca940b40060913031519203075036074503030f50810001c88103010640c100c205181007680c030305100e070322070200c01241c4580c15492402d401e407444c1c004580b801e0820085165010019110310401080582c03542d03415a0024580000a952607020900040c140340c00d0014240340030f110a41c0c1040709400006854070382116200720610320718034403030741031000720340044068035007150f080c140403c5282001044c15204a403031088854180f40032594107080311a810510076001006440e580e220340d0f0310219184d000f42181c00800650102c0865203580e40e210b110812144000140300c03c041050100703040920503070001b03041c014140410840301c185200e480e0350009402403060f0301c5003014040307085c1c0c10705803504003800c05142190342040310080e08010290082d450301c1e1241c5495036080025520094481c030b51101d50040360209000900a800c00e1544814015003020107020071501d500243c0c206880010016034118 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 155703039 1250 155701789 155701831
    0x6030c03090c151202040b09190b0d05060901050306040b0c0c0c09010b04030623131e030804021203040b070212070b160b0f010302060711030c0d1113090201080a050601050909 77
    0x100b01400c1303c0c0d14803e01942030a240207454135146c01941440d50041494420f800d600303400441d0101c000e440101c200381c0d00c1d00f002404c448000c1c00e0440700c240c00f66203030100101d004d107000124141304551040d145000760790b0311103042d4200d130008000100903218a90400405580c1c5600241c080c3c038458034001c1d1614951f007071250070395001c03240018038000d100fa803400287c196504050b500000d20b04490003000322502d0110400200c041e8103891001c40b0084500400d0f074882c11184c0201e0003200c00c0710b140001d011280788c40340316520410031820300400c0b87c4001410b060540300c1c2d03210f95a83c2070f24080d59490b0041e540c10f9004a180f014004c0036007080e0300421402c80e071070035045403000d1042d014542c19640820220307c500040500b0225407205401d07459541001010310150740a0034640d40c108407450310004080814058603c100c40444c9181c0c0c00c401c1e280301d8600d072150141d68100c00c80e1101084403000b40409490241004030400c901031041d04c0d80f4170441e000b10100504400701c600d400d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 155704289 1250 155703039 155703047
    0x30c0509131e0203060a0e06010c0605091e0303010510080a0b041d070603140a0e1e010902011220070c03020d0c06020615150c0f120c0d051306030c03090c15 69
    0x19402e80300c03450f0310500501103e600c801c3d4014040d035404c0011103109495110050300d04c00441200105218144020031001c0340001c20b840030f04c030354a076000000710100c80c1c01c0c4c00d4403030000740140344e0030004600e2031200ca14440c201c8143c020b01600d00006c0d941c0148804601aa054900c0000405980c0f0041e841964030800411005000903e020013044039915103c04e1402d201610b81c2d411181c4401480c81001c40a020b079403450588000da41c02c54402400c40f8a018251013501640480c1201c0480b90014045015010b0926400440f401c44003405a42000964218590968640a0000002c801610307501c41d4040e1850017824110116032400c90020b16000000705410800710061a1303c041a440c0c00d0180320717009603031889094848141404a41c5484403d042c122041d1260100d031508801101e00100b100403c14820b440b03c0311040081507445100e030090401066044c1082040b00700d00ca503101039450750030740c5030119505007542c0360303100b003070511b40c0201940c445010b01a500203908 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 155705539 1250 155704289 155704331
    0x6070c0c050424091406040902030124060201060605282a1509030c110f030709050a0e0a0c0b070303020f13060f0c150914070801050601140405030607030c050913 71
    0x441c20f0300b440200c1c0703800009008000080c006d079006035140ea00000031940c080d001071000c0c031038046220301321203950742405101080071300c600c2002d54600900402d1152160089652410500b400042406061400c0d25a000304001e046010081404940d01000020201007281f00c0b020118510501c1e0039424100c610159001c90030ba4900d181c03140500009811150000005400c001d00d200c1b442d80080c017285091060504041d898007445102013011240b6078000d9004000c1722008012820340703181425558100703040043c0c100304c94048100300c640b14000080503054824500503060910318581c015860300001c0c640c9988000c4c50905014840e840420300c07940f1801c0786001c00c0e04401540f514403142e0100440c1c9003106480711040424025480000c0c52000142c1d42100d03882c683d030302c1142d4000e081c1a150180040c9800b400d01200424003801da405451009001c0c0c2407648540780103400414100e02d0b83ea017401010b01501802d0340e50360314054100c41c9500b002043d80385008c0380321a03440f62 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 155706789 1250 155705539 155705549
    0x904210203040f050a030f26040b0705070e040206030f040312020c0a03020c01030626070302090702150601140406051e0c01060801110f0910021009060e0c0d030206070c0c050424 78
    0x2c6a40401c10100e00c0040b540007c16400c81c2c504031841440412202c0c03840c8140d882059045400600040d119130080d0080c503500d8040c0701a546801d4450140c088040010303180698402400d00210701c480400c44201a00548282098030704825405102c1c1c05a030404401c001c0d031a00102011020701d0380520000b05007841c01d03e42006034134140072034021400702e00d061003d140111049051a21141040140c02a41c2c004041c168549820b40e03000350303175903807501c0a00c460802a40c00718140d03500a45140210001c16803c0c0c80c240b0741803020441c0c02c0c0c3c1001401011201c210082041d28112441c01011f160390340e04000704100e41002d0001e820354020b10070006008070104050084400482c080d035401340c90440b0140306c866040e68049141020400203600000d241c81030300c804101ea40e60100d0025120981550500b01d55602080300d000a58003010b03002d6048107001540092040007400e448034442e120300290b2070344510210f000c8a6030314012078138044e285182c4898440c412096800100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 155708039 1250 155706789 155706799
    0x4080a0f141c0f0504030b010e041704140405041a07180503060c0405040203041511091002031603030b12060103050f0601051e01030903030f09030c110103020702010e0904210203040f05 81
    0x25403203911611540b101558107070400c001a2643c80342c0a1013081103034002d42e00480c40f1005961201a09412204199400c49030400303402104c0ca50702010380269400c45000100d0382051201007001d000c00b0b07010003042110000107105c1801c0e80007142d01d00d403501030001c55855079900405e1440e00d10080a881e04103e200340c0c0004200419290082c040b9003e45038181d80168681d125441e000440040003034801010358249003c501001c0c1d4440c01800d600201215621a540c41c001821390f01d07882290307a842c501c140b1041d00034010034003981010034016405450ba643d0141c034000ea1904010080e001244c4036000f249187c0481201008800d000d0001140c0f00c01e048641c0c44c1001e40f2040c02d0b42075240c18181c40c1c550032010325009a01c000b0005d0003c0e80c05011480051400901c0c01e007550707e04507211188400820440e511a1090340c5000341c1c18ac686589041c040d004120007144014001c58400092000c803c07028201543c3c4074424200381e8005507110343c141040c00401e400709801c1715010b1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 155709289 1250 155708039 155708053
    0x709030f02060d2007050c010f0507110102100e0102030907060801050108010311013c050301050a090b0d0c06020703111e060c0c040615110c0d1704080a0f14 69
    0x424048034080e4034160341250703030310fa650782c1081005000d02a1250340e00541100403209841d580b844000400b0054070500c141c0761002a41c00065910301034808800c00011801d2100f900000c0700108120556034050040b00c049400201c482e0042d2481850303442002e0350080b003072084030320081001e800980039074100181e4070b6040c040024070840051201804d1545a484e402101f41d001d20349550000003d0103003444100061001c1201c400900c4160030706244120802080e801d1280c000c0d41d041c9c61001300088907452400c0002d2015120003083e6035402445101140300251405261038010585034001d0001e01d03185040080e640d00f41c0288460046014907440c0c60314a40c8552000d000d41c4003150b0440d115044001052b140c051210807081d006480c000c0e0208030420741018681c44d0440c039a40c0d03040c800e00601051034940c50500c00040e044a04c1e10041400243c0d500604260a03041141490030555206000c601d820300d002420340d014210000503c0500072401c0d1035100f500c408900601078 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 155710539 1250 155709289 155709293
    0xd050a050606070201050a0306051c031e1407051501080f190f0605090f010c0905150c0604080703050705012a0e03061503010603060608010c03150b0307180801020706090b070903 78
    0x11030300c00c1401c02070410000047c2c3d0a4002e002ea40517102600c0c004d0120303902000c80800032101c0c0c05210300207501050b95024000184015411803050308500340c1d076644846814007401c0d68407070300031038012506400340204100180b662124482c2c0201428802090b010310b00080e101d0410072000034030320b0030a412400160105000280740000941d00c040005426694581c00781e00741080c5c89001d40070355003003c05200160764400c46c0182954001c540d803291075401004040c0c070601c541030340703100260020340008001c200000040c007451030081c184a45400000c1e9100d508680c0803c8506d1003401015011040881402c05800580c6145060004040314142c000030360b030f1800208014030340116004412540e0301c081d04094001d5a101209212490b00c40c040c640c06803030341c96815000646003801c0c02a030001090065802c032424107840903d107440f9044112403c0e44401031546002c0c903090400111100244020107900b070180c1000561031800d0b2614000300719000d4580c3d001c0144000c004e00c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 155711789 1250 155710539 155710549
    0x80105010f1409010c0f050d1b0c0311010c0c1d130206030609250c110301020f0a080604110a0201090b0105060f0a0305040f02120f2407030902040912050d050a0506 72
    0x69402c4401c076280c4550b16030004a41c226042a801401c0421003800c01080113000a403000544803541c6550720b500d011300380021500d0026243c040c01e40d001c00c02c020008036409a1404c0d21045041c5043c04002d045619031240d0442c4543c0b01035001c40c13100381c1210b10684510019908450014a0303101d4200c0980c00180c001e000c09441188280790b0b200100301c0045a00c41c2490a0b151a8100d46940402400002e0410b40d810300080d03441e01c60000a08070945010302c00c8480500c0c80b40403950801c00030f22003c842500008120702d07003007585d90904105a0340e015000e40028a0181e00215180941d4039102c4061003040e07000d00d0045100380041380c0041810029280c50f401d5500d0002442c0d0759904112541d4024880c004e07400c206961560b0120341c0001c200c18903290900811100710105074440c0c4c1000c4109204484541d1070060045007446109404c1754580030300082021404944a458503122070100302c40c100040b0b1000604d030b1101d55014082d0070361101c160f250801036031612901081c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 155713039 1250 155711789 155711807
    0xf1a0403021e04061e08101b0f090302031608011b020d032f04081605011d03160b090f0303030609010b030c070501050f041e151505060304080406080105010f 69
    0x11101902c078040c408035030b2900c0e40b01400400c01c03081c0da1205825407002c3c5110300340c000d00541805e4015206400c114465078050b1540c595182c100c40c000c00c400501003255441c0f5042c1d111000c00003101000800f6a038200001c51140704030102d0303081c24900d440051800c64800c00110200c812001c803540d00742540100300c5803010111410003180d000a0010f895460704d0782000640136502070005080c8c0b02403000c001400a50351490b003150b4000354540310f081d5403d41148181c1c2d0000f801d14950031350051000202a0005501504445001c0d1120b581c42501446980104c0251300022a041e4078528120071101160781058018510314100000410034440050003084259a8004081104aa5400201c4800380c0e000030082180b401c4c01403400f135242c0d1054506441d81c03039a2181e1030404143c0100b000c640554441500041026040c1520300901358504403010340c104000303c005030585401e0000c601c65442400000d40d07441c1050307400381101206030055410404d110786013040494004c8000d07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 155714289 1250 155713039 155713069
    0xc09141308030a0e07090608011401030c350c010f050c0712020d050d030501140a060816031b09180c02030703030207050705040908030402031005090d0e0d0c0f1a040302 74
    0x1182d030740e50f41d403030f00d8002804000c02903110078030403104c00007190800743d4004403d45402c0c0e0001d111105d00c3e003030142c0b4890420300010341204421b01c0b00704140c1481040d81c071aa84440d07200200280c240311020103e964840c0f48514240d002490302c0500c0e50f9210406018800c180d003012800c010f0300224560340c82e4042d007c4c064030004280c40712b106641e12110002c45059028048803240d0414a03c028080c1100303204a050310300e041000c45805203400c4e05901300341c0300e440d910018240d0b280e0f00718142031501078480f102410351b194034001040a098002041c45403070394a80804081c908200301300564603880c0761301d810390318100e11803486a030701100712444250146805030325819282420f50901e5141da115581c05890544e41c10108020840903520a034000c070b09495564014081d400c044e03c81c101c85010030340c0c00841450040d14000c0144005041c40a080351101c505d09a0f9400b9039038078176800c840a4607070300071001c0028041640c0366000881100c0c02c000d080034039640c081005400d0408031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 155715539 1250 155714289 155714303
    0x20f0d05100902070503130603090f02010804020d0b0c0a08100f060f110607080a14070923100804140a020303030109020307030231050301050c120408040308070c091413 74
    0x1103515071881c4944803015201400c800c40d6101d460780f034641c0c0e40c0e80c0210041c0300c0142100c40c00040307441c000c0c130414100c0c2e0b0b00601002c0340d01806500448450030001c0040b40d1060f4200c2c154030108074000c030018401c03844860590307a02c0c01c6580c805415072000030041c108001c0fa5440c24048401000801c1c001c41c0c0c12401c25007501225100c0c2a40c020148003141140c030300c68078041210301540701c1c0e4218004c400281c0c0410940540100c0454074810440b0709201258820408001a68500c2c07160301481c0c580d04002541c000012001034448042c503200f1000040c0203405010a100c00301c0a0308a90390a50030007001302a4159001ca52240414403070003842d150b01000080846000750100c5182d070304902c000c044660010141481159101e070440c0301d2a0104100c04241800d0500c5540d000b2082000d5103401c0c00f03d01884000b001000520468050381d0a100002c0041e0901d0043c0c440d0318410714441c401c80d030070304000000302c4400d101c4845c1107043c40b009000c0041101c50381d0090302908240 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 155716789 1250 155715539 155715541
    0x603060a03030804210806010e0414011e030501020c0109021c0f11120d120c0e030709020d0605060f04090c08250311041217070302070b0319060305060a0c03020f0d05 73
    0x309403880c03848606400c0c18100d400302001100346d5101c2d14080c402d43d001d0701d40081c4244000c00303000449034000c19a440280d40c01c03006102410782d54050000c41080750500110b0315450b95125426038100064444942e91034280a904524004e181c81c408401c800e4901e40d980000b0342c1380c10710944124840070f8840c0c1c03040c21240350b442d20b80030010010010307a07800303e139a0082c510b140280b60b100000c01d0380c10203500c0d0202c03800c000c80c85100341c4690100000c00411070282490400b4009521001c001550181d0351880042c072030302c4642c0502a01d044e055040ca4649143c00c8154041d5141c4240400c00c00585904010040c506014074448110000350011039a90380720809800500300c00740740a2003c0c0002c00c00040d44108038680b043c20320300c100e841183c42c85100041c00d60500541200901503000b080081c400c4001100245500c040c0c103920188040030542441d00840d4100e0b001aa8960011300030003d0000c0903000d01c5c00010118542145480100018141c0500580300b1608126423154 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 155718039 1250 155716789 155716793
    0x1060e0112150f030b09010e06090a170c0d05040603111c0504021201021c1a010e063406050609071409030f0322210803131506050f0603060a03030804 66
    0x1c44250060710b0f040071100c941e15143c0c24811500f403012108040190b00700002610303075080110340d0314000c4a04000402e090788281c0d8070906005400300c0c1008940005000c0810440810842d041150002e900d490340c8c0c075402c2002c002c017925046440001c80b800308000e0100d41a61800405001d00d0f081c81d400140d0f0f07180c52000400e0404441403c120070360011600e81c05c01071486841c2203090760034400411010003480a10004040700421250100346040c0900c011418510020a54514001c6007182c00000c10074000d4004090848507580100b01a4203080800105100703654026508036048040391030102e800502005088224101d07150000c50340d5810f584080050707640d03024040f07055a4590704c900c3c502d000d804000e07500c41c414100d080d131000590110b403000441012052410118070010b01500d0707004140d4006019403250084c175400410118940d200d40343d404000120002c144186801c0412a4007003500061900c9144100144201d5a03110720040e000c40f0b5143c102500107079294 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 155719289 1250 155718039 155718071
    0x210050604090b0c0a120519050c0c0109080301170102030609070f090f090f110408030d0c2d03050702070605180607080c0d020d0507081e09040e1501060e0112 70
    0x100b50050145100a090204455842d4043c2a58020b11790300d5900e204441c00c062400d40318103540c02048078940c000b0880c00b124480d00581d42c06032006056900d400c038101201c9007101d1308a0317025075040101000500065034400140d141c12142d03107000707500758144407000404140000d826402806070103c0d2500c4124040c1551000070300060212041a81e591524080904400210405440e00e41221810440880c200b5102a0380c6900300030360910324014100002021100740d04020b02c07d01213601c20186240600030402c01054400307009544e5401003002d03050307601c0078012400355041004144142680001900c01030003050702802d8607409000c0c04a0085d100c0c5803009003403500c002a40604a81c800070f60803d0303808050b0f080b03816640c0001030072034041c0a252002002080b00f044090010b9907900b90034418100b01d4800705283c103015200080c00c4650205d0809a5078010702202400313124011030503801800e041c18018204015078000030205541084006c0b101030346c440350366100c1600 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 155720539 1250 155719289 155719301
    0x7081303021e030405030f06010b0403060f18120f0e01050a140f22060c02010512180f010e010b0a030c0b030a0e0a06020c01051b16050c0315040201140301060210050604 74
    0x100c0500b5200303050311110440d00c07540240100c50180c40b444200650021000601d54100c2d050101d44a041608550341d01029000b8001444809a01c840c131806048403200c400905c00c0d4891400c500c0301011307000c8040e05d4050042e00101c24410038806101450f608003040707417507001041c82e003203803480203941101c40705004100442c0a4030402103100c80400d0300301003044004486c07206001b03041658034101110618001c080c000d000900c03d1000f130251600a0901e0b0340c100034520301405941ca0304403001803626070406c10507103441e0744800700781d240b4420030322861041d4002607916168590458072802490001c62185404240c800000144d04400d241d001020034007440044c0c4085440380e04103c03010b500014200c80040d4a007001150b0900d80340d47c1103802103d4180d00b042d0401004009007240c4d2618030100780c031540140540c01c0151350f01032202c1c0c19100c01950041c03400d41441d00004000c0c03281540d10201608007000180321194001a0107100200c003458042040e688117004203024040d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 155721789 1250 155720539 155720563
    0xe1902030106030b1602210703050c01020c0d120b0f0904030804020d050d0804060c0c020d0602130e010305030703030c0503090a020f060c0102210c04050a1a0f0a0302030f0f0708130302 81
    0xa0b804244001180300c010321501c5c0d41596801c03a503010402106809002901071483c00501c0c0c401c000c2c00b00001d000d5005001031408200c001800e069060705000c0c10004405002000501c5411800d481d00301544503103089024140e644002442c0380202040c8085030160002e000e2081c03010010b07046554024403500b069900c0320503684420724000000d04006000c0c1c80445825003440940b80009200346100044980c00521903095046c0741c0d00e0b1500254491400f4401d032001c280c40200d40d0801202c07001303000310f20030f0b0011940d407542420001d04566007214018104030080050040c060030000356404017640454a201504e118100001c0240c4101502100e440d400480c040c0300c4217004a10401081d008041c22000c50350761252621000d21640c00740e65440714a40009000511200e00440802e41c440c115091404c1e000039900d8219800c82c2004e000000d8002007042603c15030b200b0000d400840d4541182418106a54040c0c10b9000007020b035040740c101d90703008809251003000f1101c0a00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 155723039 1250 155721789 155721803
    0x90f0b0108371401050f01020a0609030504050a0609030203010605060405060f13090513030314090a0303020310050a030c09060f0b0901050a1710030515092503061404020103050603010e190203010603 87
    0x5a980061030b00a0168030596044070380001c3e00004590404901c81c81c0c3e440016406880c5168241c2e8a00005120b0303040e040d001c124041c000803e0645a0303543e140f010700107030b0b281d0140c024694030401d420b5550035041240a15014401008107446020548040f5000c141e101034481c80021001d482d152a2948400c9a460070700703051140f41c06d043c41100c80c9544c06558140040086d650300c02003d61001d946070f2070382e944121030140c0424071039405550000d01280e05580c0301c60340c0744001034400c0c0e00f6800568140c0d0603400100024103082c8070380002030400a040d001014034142025266008058030750b030500c840011100950b81c414083c1d00c00d0700c0e0307006850b0000307400c2900300204119154001120700380314100032101e0380380b440b0050324810840c3c0c5c0b004210291702424800768141c000d2200d8070084501444c040001403880c01141100c12041c09540d0261610380001400d0721005080c5900a0345802032200e05c1e0440450b130740b00c00c01486805070b00c0002d41440440d004007442d5101a21321 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 155724289 1250 155723039 155723131
    0x80a02100212160206070f0e120d09180501050105090105090d06090b150103090213180605072a0209040215040801020409020910090e04020d08040803030907090f0b0108 74
    0x142802ca14854000e40505240d007075002d03036180040c0e07914442902c031407001c5520008420007161040c402c5040e0b1150240600040a074030241051406c05ca000c078aa0100b81c01d040300780400241d070301002c0d000b1690200d003480b203541b401c0b0002c4e107030b0303c1a17000c1c10703040010008555034281c8541d121904203942c4260200710f03174210340c1000107141c10107549929180021100d001d00c6584a40502c40d5007540040c4050280c3c048101c10f00020405110050411414420f5038408545244521445148207840f000240b00041840e440c0e162641c407003107100020403510f85000760729070040c1e4550050b8191a4642c05401c1605200420b0085610008641d80009004035101070190050602e40c1d909441c650300d4001080300555100c03185014095515502c41e000502528012000f503889178003940401e440c10b13482d0104141142d0003129281141d501941c4100201c044502c85e0a01d0032140c140208a0000e80800082030100c01800c002d810141d05c14880004040170366010246841c0303040301c0c2d912 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 155725539 1250 155724289 155724307
    0x3020c0306221103030d060501092c060d0b040f0203010510150e0619020a170702061905090607031706010906120209031002270603130308150306090c0307090b01050304080a021002 79
    0x2407d41c07405041c2c0003d03440c2d40c001803110089d50000404140c180e0300e1a12101c0500c00092440000501c1035500480600090010550924189015901951030060b012a09006040c25540e014081c180c081040c40020800324200c01e14460340c01540c1e01e4034200407040800010f116004003100744d0741c82d030100d0381101130706030300002c154850b0741c0b1801c1c1034100c0080c9844100a580500c1e030300a0341002041205180540c515168459113110604069007000481c1c008508140c10540301100415411035071f0988080404000980c0080c0910308880b52500b0940300821150503040451a11600803d040705155024407007036210100d4018115240d40d010a8544100c074490761000508840e1314000e2a160f007040700440e80f0481d80003042c0505070a441d5022106014010180b004240821a003803003540e0341848a0350140012500a03c80340541500305400d00850764040040d60f132400310081c080d40d80040580f544039800802c0c4903100c440c03881c2c0c168103003802d8104988029200190480b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 155726789 1250 155725539 155725541
    0x130c091701140108011104060c050a06050c120603010c05090409080d020307210c08010501080a02070b010b030a0c080105030a08030c1308010c0314090606040f1401080a03020c0306221103030d 84
    0x3100c40c41030382c6044400e980ea4909035080b2820b03a80c180504440401040c014a03001d55024a146481360003110100d0b070386038403540700311102034640000f15400002d50b84110b400c0c1e86521500082c0c00c40007003201000859000c4d1043c4100c1010602950311204408203001c0440180c48401c211401c6c159a0380c81d142c000240b04410241c6d44031416039100c160707900603503010700c2021051a82501c680a0300e0f42090019500c100c0024084a203540c0c0070811540000c0c94a40038600802200c01460b4407410b11403a100151681c0465020800005800420041d07500184d001403198125415581e2911400030b6006d00e8031848806010ba26000d28001500060551200305040700c0c0742d40c00c1244021aa2408549c18019a50b403069688407501050b000d160941c031180c000140a000040c000a5034030b4840d1801ea0309910a1045421203000207042c540c041c4041008500114003604062804030028080e20308800550002c1c02c42c0302c101e1a04000d200c000307a0060490003001c0b07a03103c10030210548 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 155728039 1250 155726789 155726801
    0x402070f0b0c0310060e0d0819032412030203070f050a0521090909190302031c06050603010608060402040314030903070f050d1e0c062705130c091701 66
    0x110a074020000090074658004180c131300070600700340080c0300145000302c200c401c1200411000d038041e400c1d2001c0c0002032000401071400c10000b0b8010f01e110460041d010b42102d041511036410202c40703942c00341828400780d0100c400d80301d8a6043c030300000c41604040f86140200c0e07000615815010818009000e0b0004140c806031307200f6401c40f000c460f4420b200051240300c130400840900f509100000340c1d0300c1c01d50ba10603404442c0030200c620034140400031185003055000c0507005a04002402102455855a002486a109601840128030300000b14407240300520401042001450114006035078540450f00215013110311030050304198031599032039600c13a21000303100b8071880d0400901d240c500c070950340869000410200c42c1440030303203500c4000c14148106030061000f2110b4103000424100b4840050711307140d511003880304901d8000814407811810b01ea042401020400c01050381c0f84c040980c064200b069021650441d500e2042d20a08c0301d41d004448140c40c200c08803200400158451 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 155729289 1250 155728039 155728043
    0x405132d0b01140405101403070f0206090a0b0f041119050103050610080126160807120b0a1a0d03080901061a0a0302131a0a0e010e01080f13020402070f 67
    0x1008030241e1040159110410042c108151000c244001c001e0303407078004980c114080c11810031a00112040d02c40b0105075000311f40a0000c0303640611224500f43c0c1c1000a581c0c4040c040000b0005c000d40350700c03a42d0410720004d1414225040c01d1002904114400d81001649500038080e109059200c03c46040d81e24528011140060b2600e80091805d2410561003000c032243c5880d2015280d080c42e0940c1d58241c031492565551031820305603034109090800a04007400d850140100805042c0400749041c44405e81c00b61240000d91880880420b40700b61404e07820072203071240020007110749a483d80205861110300c5074080350100300300040c1a0490340d464800c0075107000030040152905440300c030554060400c41d000d0003061002d111a18000d900419800c00740c00c6072007601c035650741038262103a840d074221541000d40200b041c49110ba0480d0103a034241d0703001d0820840b07c44841c8002803014000030310101300d40c14400c0100d4541d42c0d590301c04d070808540241c0255903451881c2801102980b80d6401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 155730539 1250 155729289 155729291
    0xe0a05030c3901030c0203070f0c170303100605030403030b04020a020c09061c061a032b0302030601020c010f1e08010f0807061d0406050603190b060408030405132d 72
    0x20012030b0002420070061900d180070180d4502100000450003000e9010711034003540b204101c0c550100d00600787c030300040c40c86411250011418820b0801407003071001558242548240140310071829119211801d4500a1800039200ea88500b0100c003d440c004a080307400ca0300c002425915a9030218020300d201800381c42400761500c1da0010301c11100d124045072090109519160300000320380e50003000d0290420010700c0098004a40000d080441c1c000c80a05160902200c98091080e045041d80ce480f016080850440c900980042d440b000b040c8403041c1000f0f060002c2184a03030040240a4044000f482030f110304299001010302070410a000c0c5510880c100440050509000910740c01a0340b410794401c560266915100d070503003110080c060303034881e07110000410b45442d0803000e948245041d0310304060324a8254001c0b8200c0b18a003450b10f001e8403080000703100070a4000308540440e0401e86031054418001502900146180e05030b40d104880585d81003d0385030004440e80d6182a00904 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 155731789 1250 155730539 155730583
    0x70b0c0c040e0d0e06090f03010c0f110312040b04032a0c1205031b1906020d0e010e060627010f0611010209090c250b0709060908100e0a05030c 63
    0xc2c1e0350755190500003260001e000b0b058506940e0030b081002c0c00004501401d0150308180000010b400e485045414500198040c4111200c950307108580745015000035015600d13100701a0304804105500034405403022200401140425102d0100b0a03d0710b034a6060f003001ca0085240002e42240030b425041c1d600416241c1d020403d00f0505454480c0306601c00c0041d0310f84141007100d850302c0008403802030843c0c0200c82401c149400111113a1040901c59079005903500070740304003c0c040710a1550805078980c9081c90000059800240840d00040102c0342c405603680300c05a00c008083d081d01a078078a44644000008101108000400960708580c8560070001c00350342f0101e08034050005e034903a11103480c02c041012445a03a00a00ca03141c040140e400c2805496645942e12628440d402c8901c0c40c0b0b43c00800616551203090000940b40500c0c00540c80c9151103d080d41d07925072241c80c054100d42c0d40e5100d540c001c80c10004400310715440810b980c0c941d03800c042d4180d19184146066686a8110710b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 155733039 1250 155731789 155731811
    0xf06010e04111b12040806070908010e07060311300f0c0a0f0e03010c09080105010f0605072003061e0609040515040206090a14040c2604020102070b0c0c04 68
    0x80503804007080480e03102c50402c00c0e201d50022541d0b040100000c0f59000e0904011002c140304002030024110040051a145c10081d00080c415080d580c40130300180d1500f501410343c0e84021403164103c5100b4500403980038400c0b00014514440d81c00200800b15008210400d01c0c48030b550340040c0c88142c100001640c0d655100101c1041030221800c0c051003104218501d9510300444074403803121114500341c070701150444003003406c599031155124082100b07511f00b0031102c4002d0084d68003600c41c98131541c100c240340c0350001c0c0040c084e4900045c90034812010182e41070382d050104440440009044a103075003020b007030f0300c446042c14544004c000c911000005c0d4160800030340080c090b56104000b403203000f000701403810b8a80009002264400760410141800360740b007040400141480303a104529000d444400c1104036004002e50006000f801342900c1030f015090074180c400d003150b59044201c59035072440101d0900042c2d401c80b9100500210311481d400d10001005151010240c504011003180b00d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 155734289 1250 155733039 155733041
    0x120305010305070e0a020f1602040c2c060d050f0a0507081003020904030908060106030c0912210e0d06091209081c030902030f0c03060c0304080904090206120f06010e04 74
    0x9000280c0a03070f000c42420802c161589400c5948003184a10050030b001c2d00b541000500d910000c1d811032285211000d004c20743c9424030030032054041e03904002e45500030f40b050314030247c0d44d0640202c05824426890540c1c584a42044030040700080c00200514900414400e141d00026500c4401182c500030000351101d0054140601270590307044a02026491542089401500140100e0400045105c00581e04e00108034040c082d041a0328081400f0320115002419401c5581c06400041a440403190110300d80c50442d6460030606901e41f0080381000310140c0754019419441034201c0c10100c1003c0501803141e0201e040c09103e02164001100c1c0b03404104d650700180c1c06011a9504190050104035500c0c02c0c2c1603c03410381b503003408102800315400090070301c164480d00102a0b000712418400914040c030499502440700e247c1c4500b9030400780c89e44160b501500d91011700650769017103020159a2960180c811041007084a10130610701481d052102c03070000d4aa190100c0c6c02d880c0e00202916003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 155735539 1250 155734289 155734291
    0x4050c1b01090809061c05010b040812090904030302071a010b0409061508070318050a05030703080f01030f0f0807201c023d17010f030308041106040b0a030504120305 73
    0x29007041134440400142e81e01c0340391002c01050705c48100304070343c0c6030034000c650092060f840280d403510715118050b410308d400c6000b11100d1420811000d0b003a0f960308035130140c00607054540141c0715602c51806050301010010403920b02d01c2d11400019080303847c84011310a07102050310034001e0ee030b80c4d810a042d01100074041c1c54045032203a00041d503420b21940c0706103c10002041c00111a0700f581d250a410000c00100503102a000010010103245d0044a84c40d0044e80303110b9022150b626544508140170202e120081266010030041810302c0880016140b415800549084840e6500600010b1a40361210428000d940540700c801c008086903c180300d1454000e04042c9403c07003115120003040b000c0d5240c2e2a02c41c0040e8075480300d41d19604101a1000c1c03c6929201088000c1c52003070b060b4840f050f0700c101c9504100b03d00038070000b0ba2050701c050b0460b9100034070680d1090901300003001d5000340c0c1c20100c20f41c2c001003519031300280d25401890040b8003c41c5508408132104000b01c042d988 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 155736789 1250 155735539 155735543
    0x12061306080a03031113030b10050108071e0e15070611030105010926061905010e040f080924070b180604030c1a10081c020705010c030306030204050c1b0109 69
    0x8810700d1000884c0c00781e003100c040c0080c03c00381d141c9004031000041442445036002074800003030f08003c0186400e040500e8038041c00c002d0810380d005181c00b910040c046c50201240c6800030440091408010740140c01d05521440300510f0360110074414580c05c102d035000448244d454500b01800b0321074200c01c1d802243d040e503074180d60b5201c840341046000d1a200d1341c21100e0a54514008844200800e0f05000603800b550300c07a0b502d040b0350003407208601c050b1003041c1c224001c4d1a407400c041c4070001f061709170ba030882e16611500c410b4603041e01c180011000c1c4030080d180103400200508024020102e08000c1003250710420401c40140c0301c0100c8400100340e07086449403180d01c030030b000c071340132074014000c800300e10b441404888004980080e100c514110f094512040700040c2c0a002c2c0b1012505125610900703080300240f0504d806060002560381459200301418003400440314014184290404005103070050018485401e0468415119034000ca804030528003084000101001d810700030548015 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 155738039 1250 155736789 155736793
    0x180e0c190315050f0d0b07090e0a0b0d11040905070605030907060c0c0302040209060714030301050103060e100509060a0b0304120807140906030613090f060c111504050708031206130608 81
    0x20300f004188102151400040c0c3e40c0303c03001915440006140d110424032800f070036586c1c210307060302d08507200c810040c010709803040282c04d000519401fa00c0302010b40c5186078020903c0554207400102250090000d1a0b02500c140200716000c2281070300400114017801d00c0e0b60440ea42c040d40c03844201c03024015507600800c843d072165002c00252a007600134001c803010051a00c0c0c940449036581e01c0c409000110788100c00e030004001003059680511070640203101c82070480e52140382180e8850039142c01401510f10034046400032480c02c0e01d6031080103000e000d00341e50040e5a0f0400b414801881e410f4026240300240c400d90000340402d105809140400500306110340c2050390f4a4104001600010000e0b43c00526209003422800074a000c1c1e911b49030300400282242901d44e09014054402584500f001d00c9402204484e50350030009607030602d000425004c038010740b200e146c01814103085071300c04a26031001091070150741507100c02890148208488001e45202e012520701d05a072514400c6001607 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 155739289 1250 155738039 155738081
    0x70501020a082d040312080a0207020d020907020f0a05010510050102070810051f0b18150409091103011d0f010504031205041a100302040e0715180e0c1903 68
    0x2041101c0d00f03088450307074a0059944078048080c03050340d00294800e5602c44203543c658400603402001641d0000e01641c415813030040030340c0200713540540b0044024010f0001c0701c0000d030020b10912a09903100403070001c0d1514150f09040c980e018003000d950012000582850003c2d46600004940d0102d5071110040c000b680c0d11007207a507000380801822046501403103101080304454448840028000d120a2540c6400c0c461401c21040d11b0b41c840c046000700a8017850240b040c480b81300342c90840789035120108500e042131030b00b10051103011150700e40641c00c07c601039120313110480030341100c824400101c40384044048440350070b0b50400d41e00a000320b15040c1c0031624080f40398002c03542c01401344800e1943e26880c1420820000011540d070003558020701400e00462420f030160b6901c41c41c640f4001c0c100541041911813800c00000c142d241072102400c1c1c402c0103401c4000b40315000304003541c159005e51511001000b6640c0c000c002e10003c0070700c404440f4030100e00070300c20512110b005070509004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 155740539 1250 155739289 155739307
    0x30f0c120e0a02100c05071d1801060b09060a120905010b1c081905070b0108010203010614090a0905130b04123f0e011d010e120a180b070308040302070501020a08 71
    0x21720b02d0b02503095400340104400450800d0000511f01011414032100040619262140e51720324854258000d000e070341400c03401c1040501441c25104da0400444030706503901000b400c1a20104042212551520b05001882c02480010744c0a45e81500301035455585ea40d13042030304e008040c0c07069100109241818440261650760701c0c2c201d6204c1e8031060504920344649520350a1050000368000c1d80643c2d00000140031034be910003c450041c1507861386a6080c42c1181000901c803440714020800744a80c1d9000107669440701854030480c842d0030220717002c0942041d09061400305400004180814401821110203d54800148105600c0d01d824210b20840c007941d07180710501c121803440300f101c8c2c4600082500782000e2186090210020100c0c004500d0400d258a00b175801a0821000da90001c2110b000000000c504892140b400d5151801008080d80911400b0b202d05410250310410003103184010190800701181c00b585c001d40803225070942c0c45004990703502c50a40f0080034440203102d2426 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 155741789 1250 155740539 155740547
    0xe0102031c0f060905090f01061205070b091909050403170910051b0d0603050c0a030503030a020c0307060903050306010305011e2114060f010e010501091401030f0c120e0a0210 77
    0x6080c0d01440490b42c10781d030b2050ba04c21348401341d071260700701d402421400882800174851480144a14040c0d07607078420303003a01c5150b2200c01c0c92142e0b82007810000b41d5805c40b079490988641c0c13082c1e18801d0741510103444401890081004860450105244103540b150200095245ca4401c000000017040d40304000c040c0500170b00340c05848003040503040e98414601c01011006886000707000a400600c151960415515003081c2020241c011640c40ca401e10100750040103c82d809800242c1c09a07039028030400451462249d0310000e010185061122001c2607030000040d40031701c000740e80034001c6980b500d81d01d43c290f01202980036103851046204011040d003031124411030000700c10201c901407545484054070f101004c2a1700d10150410360412030314070340d2301c2c00190241084490990817581010f001920443c1b182c05000d051140c02080c1400c140e21941026611210100051010714000e407800707484403646103d20207000f03060441550350400001848000a50010300301c81ca45410940e040d1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 155743039 1250 155741789 155741801
    0x106062a030c020a0914010909020303030105090702030708030a02040e150a05010e0105040f080c091302010e09091c02010203010614030c0906130b2b0504050c010f020f010504060c0e0102031c 84
    0xd050041d02d1404401694803041130000400e10320320045034000f08245040005e4005030444850780b4500760100700980c80001c241e80c15130350150303429805030700c500a081e440c6000b0418010800c0200000304001d040d8190060400c4600888000015071103121a81c0c200c04d030302c00310b1b081d0401c104003030030411580700f411700e60304503001070414510301a114840340020b0200c130707001a0026445008076012034100010b100d41e001d0b4840480d01c45159032580000d02101500c1c125500c40d00c4480b0100b400404240000c090903000c10901107807030a070546019001c0d4200f4810400481c2c0c1c01e40400100d581028112403042807003803803444c03401880408015458203c882440c0e12000000004660040280020f008203c103140541215125001c4c10b21a03007000c6240e40c0368180d04200074000001d40005030310b118030b4000d091401030102c941c1002ca00e032400700e0b003e07210590300302404c0c4005e000b00c0b507203c0c1c40818140d80d14100d45940481c016692071181140107844c51008030380d000b03181001c0d03901030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 155744289 1250 155743039 155743043
    0x906130809060d0603050601260606060307050f0a020705030f01090302060604230103050a0b0a0204081c0e0418050607050f041401090329070201051608090703020306040c06020106062a 81
    0x207030501000903e208111410758000b12619444072005018900540c1c80750381007480060016400c002d02d41c14203544405014141034000d24010010403441800b8409448111040d50f021135200c0540707080095884042d4440c280c0680a0800c40c0109a40c044c0501440d05801d82c00822030754482c1800c0c4030040c0002c40c281d42c126541400030b2646080000c0c421030081d40564000c0010501508003c10302c844064420342c450392040004105401c00420001d01c6800340003402c0306e5120700b8500584280990140700b640c4549030414003211981402820400a8041c4049813a5983d03444426100e5118890000140c0d1405010800c07100c92240900d40140c641071410002c100d540745d84004480c6514042410030920701c0450b80b036074400114000b98000c21b284002d03c600d088c54051035052444400140c1d0421412200080c1c0086042004200031640607080381c10500d003078244041e06040038001d800055007000b03c0020b5062044800c1900035020a1140407110030b1a0300b0901060b46100701 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 155745539 1250 155744289 155744299
    0x1e0d0804030c06020f0c0f010f0804210f02100902150a02072417010e06060c010603050708012901140a030b030601030309060f1b1b1211090906130809 66
    0x80840003410b07000702c100c010030b40d0340c0040081c040b118581030f003003098a484081c0902c030201d0b0a039406c0c0e0b03030040b0701c41c0d4000c4460800d030711152110306041858252030032400900c00c0a1440f42c0e10f0b4180c2c420300e250110798669007a16110910f540c000d1064810140c4065401071600c030940c40b40084100081c070f40d02149004941002d5901e0001007116803ca02000341a00f0b41c038061006466007000c80f42110310300300b40b11005198101244105418000740400e8040c00000c502d02c1e81d41034095200e47c02940c0c22804030740301c00e55130710130640c080c12072440400d60940150010415641d001c0303511418016050312000d40010b0324000c03400791504401506030402d61540c11009a9032014003005010314020f40d9501000c0d428404050031880f4003041c044104030100fa0000801d40b07811228183c000e030b101c81000c41d80c80040c4a602642c01550304000c683c64080e490030000c11202c0c000e02e00c1c00b82400e4915410555424024640306c0c141119117040103215000494001040b000c02003541c0440141 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 155746789 1250 155745539 155745547
    0x7120209150c0f07060e0a08031e0d1d010b0109170a060c260402090c0a02190302070b160501153c032009040c060c05190614061e0d08 59
    0x425a0b28001e030542c0202c002c54550901c0c00300c1400c00e002d1080240022304019807400b000320f8900703018000b07070a048240441020402004092280c2c11401c40c1c182019089103120b12290100c43c0200f020b554041c2c0410741c42200092107a864940300c0d0501800600a81910926500c803100a4a4200358030380811110005101e59505d410300c052201040c0b01508031400e140038410703c140b440019100d0115041d050200e04001c0d03a0002d045900b82006100da407152100a1409a00d02100c0e078001d00007a400101d151a000d1010005a103c0e00c1d0158009004070780b4109455800341200e1b0142c1c03844e00c07040c94a001d60300c5042c0814401d400e007100882640b01090b02c441ca101a01545c0c0045881c00c1c00d05120041100c1400089000244215141351043c1401ea44000356582288035001c1030202c034102020a11000340585030b580c480041c440e00040c2090306d0310078010030044003c0c0072028100c400ac5070346400d01c0050f80c2d40740140360100c60301d080141404c0100700c030401c140c12190f1450400c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 155748039 1250 155746789 155746813
    0x80c030a0b090a022101051e12060108060a0b04090c0905040f0611070203150601171803040b09100207180902130e07030317060102030a030513120807120209150c 71
    0x141491161005440040e180d0011148844002120707405c1c001c204d00e034034001440a60340f959a80b5075103140a000c8150b10202640c00b043e00d150040108a20a0042e200001106000403034410710600107a4003c0043c00b114208100407900c0b142c80c003604d0751403103100a1088429952200d40c0003405107001014110f0143d03200004d0312920b810301c410301c0801040213411820200440d0f2214402e4103d00001440c0c0040000c00c10300c0806061401140783c1e00c0801d001c81c41e01c1d064269105151810343e40e4442d142c4046070b8056000c90300090058401c1c440d43c00400d48003050320410307540400f9410034001920700c40040501090708043e0703407060184120061310009407090000c9404220060b2908503c0d5040150014510240914001020408000b004ea078040210740c0d41c2c0d9054107000a06d034a1b08202d040c81d031100340c2030081069111920b81030481d6007100a0603c5002203a94600d880020700e84600180d020325400903410054241503c107212140c5e5000d052005a0803046448480101d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 155749289 1250 155748039 155748049
    0xa09151407121d070501090506070f020103270804150e030c13021309050906011d0f07030608060a0617070f0b090f0a0329090a020f060d140f090d080c030a0b 69
    0xd80f03040c1011340c8a068200b006581140240300140030490740582007080c00e403a1400e641c098000001d0405a48200c16202c440302035044c21905d0110502c141c1e030b054a01e14110690740c1c85030003181121080180c001b81c9007803007070000c040e41e003401402806076000e0a9050195490f10380d421b40320665000e1180f204103031f820404000c02050344503000b14441c189015070b9404d0503410b800500c5940040c00c810650b03107800801040c0c00c43d0084454410310355580c04201c00411054000594078014030040c02040c48041d0010000d03100010741c00035805118402407960f0303030f885101e502410a20588208007820f2054050151008050304d404040352001d00001c402d40610307003040310180c0400001071081d40e25681142c03281c204101d540c01041c20481c103038943c3c1d4021080700030710aa0409040c00340c15250f00d81907504602d009078051201c0b440c503a440e400108400c0300c404089100d001b001501c1c0c11030010f204030b06030a4648910000e40c07a007401c81c1c14680e20042071a2401034403a02210255114 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 155750539 1250 155749289 155749331
    0x91b060c1501050a0e0103020d080706090b04030323070f080c0f041d0906071d4207031707111e2b030207050f060a0915140712 56
    0x40340032882640c10070b403c102d0484c6094000c1c1c43e854001d4401880140c45203200c3c0b07240715411400c850f440d9162481c01001070101e840000340400381e41801d110800d5090303044400d000031a5141031403980480c10781640009021070314840022440801d8500700c5000c2d0128070b40100200d09820b240101d805030241c0b0395446a070080b9409581e600c000c50210151a01c03158110311200040c04003410310f044001c1036000076072071103800702c03908901c400e01c55542c03d03114400705030864150180000c1c7e404801da0010861200900601b00c0c80181101d0307942e0b050b400c030391001da41a1240520702124451503415120018039036414040070030762141c021202040f1204c40d1312081556807030b80d1183c0700b0910741000788515032802d0844489007003000400703203404603242e20500e9160040c1c0780c20145c05e00d00d01e842d01c442c814400383e004003800d010f078500c02e542003030401c07034003e80900700444081008a0211b900f8040c0d142144c0e4042d902150800d8800d80301c140b01030742180d0001c2152201c620b503420300c4c914 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 155751789 1250 155750539 155750563
    0x504090603080912010b01020309060a02010e0a1506060305040b040807020a0b070804030c05331201030f03020708151b0c16060e03030a0905061e1903050f091b060c 72
    0x140109000b01c141ca006544d116180302804000d100c1d01c0c0c0f800d00003030350300d000d0030003900e10801c008202102200d2003540030b2501a90704004075102822b43d410003a8220140d00d141940c0c582c108500401c00354080d000700d6000300d0780030468013000e561f5a00c2c0c2e58056044807008aa1003d510f00c40080c2061400d4054003115004203c0c95a81d10300e9450140c148050540c4998040c44221103200380d00000241c1c0e0180b25891014001a404d009090b9140ca038881c91001e07070000c050040012052003000300e1401e00d098420780885420b50303103e0803210360391a6800704168001500c60b00148517000f280711500c8402050403202820200003028030360900030a4400d5040c101c0c0e007980108070043e840f280107914900190050341c83c007810b080000b08621108e018490141d0000200050003034501c5010021b03070141c0e0401c0d503403118030940000000701c1d14003048000180c03d06010400d0b41c90700101c558051029030300184030110100104001c0001e030b098034140e0004050000e10f00681d8244800742c0c03012 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 155753039 1250 155751789 155751803
    0xc0f1f050c100c080f0a060b04061106070302270310140405010c0905010c060e070902070c18063c0f06021009050303010b181c02130509060601030c0504090603 70
    0xe00303211040b032074074090b000c8000301c41d814081c0c06001180c1200100340c0000c000c0b14440c100e036441611040240c00181d00400740c0c07882c006000250306610001e10300c1200003000a0340c5090b03d07401812000c4e0300501918034070219800501501c4549691403190400f00c000d402d49800740b081c901030408692650f111000203200820802040180c203201d1202c4841c0e040c01c00030041400c01f00005d0450341d00200050182d40e035a101c0f141c240c6c0f4108540d400424120b007055640310b01a02d0400322500c039a00c5034050100252085040c150001c0c028001a40e1540728503d08100b03006a07030b95046c14681e90316a15090460a2000718201a6206074002c0c1243e087c040005500c1c0c180000e141204c58102522240e1400005900050b4048101c038111800102040e8560648140b420703a00c510361160a83e20a48000700c1c00c00b81100440181c803240d000b100e10500480d01e90403403500b0f941c41284e4a00054210700d000400350360080e0b008800d501064540203080070340784d9001c002111801d4005a03159 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 155754289 1250 155753039 155753047
    0x3090c09140603060903180d140102072f0114090d0c080c03060c0301090c090b031006092c070c06020708041401260a0f1404060b0a0501020c0f1f05 65
    0x50080c0c100345600440140c0c01400589428075545031207007d41245d20442d880c001c604032500d50740e0801480001908003542d540c01c00300d1890018003e500017881180c01450510f00a04100f41030056100f100701012400f03100c4403510701c0111659085000c074420040001e002e000040d452300130300942840d02c240b4140c50036504100007140b600c3c00100d5114400d82c800410024004584016241101d04008001c40c02c1d5101d020140e030700c9140c2e6003085030810404070801c044420080060f400302e4205460324500389450304000d00340b13103411b4680441c800034107001901d03600740080320080e88403000786041640d940c441c0d541c41d02070380d00506040d502e520003c1014090039040080100b102e400901301444103249002d51080b0040101d40c2032822024400c0004d000750f02d0603001605410413032a810030184403070042031201c4a8080e0740a40c0c0701840e080d040c04460401c00301d0101070703c2e4160000c152a000c6031040201d000302000090390070900341550616105504e0f104002503040c40c0d2200f54036 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 155755395 1106 155754289 155754311
    0x31e0309021203041508060627030d030f060905190b0f0d0f120212090402130302030609031b01090f0b0711120d2a0f03090c09 56
    0x1400340c186000b01d0140400203005852404a90b50024202400c007215940c0b806c0b40c1c0c1581243d41040740350055401400b0103e44490b540304915118920400400d05003408052900c000c40d8481d51024032450042c000c18016081c880020800c0c2c2c034045844003100c14a0750205008030b540e0340b440d08010b8039400b5004402c400003030440c1045280c6c40c5098802c40408802c10384804000241d031030341132440403405040481100100303a04003c810300402c802035004204038028000c010310000010f0f2400e001c1c4512990030300c40a90b0300d0300d100c0c0080e8400c00942482007100d5900d00707a8110000b44407080704500d00c5800c664141ca0300d582d6100c05851a00700d12540d038585225025420414031801801403801140000b000c1c0024800c0c004000182003030b070003404032180421014260300e82d1040080380200e00007840c01083c080001c1c6c451000b940b01c19000b00030b0395521000c400c20 = true := by decide +kernel

theorem cover : BRFrame.Cov 155575539 155755395 := by
  have h0 := BRFrame.cov_init 155575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 155575539 ≤ n) (h2 : n < 155755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
