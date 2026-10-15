-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4652
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:18:27.044426+00:00
-- url     : https://prove2.me/submissions/8b862527-0d36-44e4-a691-9ebfc1a5568d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 836510791 ≤ n < 836690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 836512041 1250 836510791 836510821
    0x12042a1401181409011e030b0a060909030c050607090302090114120d090603110901091806030f0b06030c010314060628020a0210031401170f010e060a0b0306 69
    0x3000854049038804980381c0c01100c65000c9100464101024540c8407807070a200d440070303010b0071800743c1c2d0f0480c00420702c010b110310350708074502020807072043c003a180d603c601503941800350002da25180e48400200f100152400b4000d050703406919002007206203071906a180c210000c02c0f0b1380400c5950002840140e44008003a81121848186207802540200004401c00354800841c0e4441c401d440256034201e0708800003104851198408001d540e26949115049200e84a200380c001014184103002c0501040c01031100d8a1480710002507081e100c0d5141c415240950405076202c1241e9410030103d441c0401c0120020102842c09000c0c0030790010119489a0f40604158841c001c0400c084000d405c150580c000c072070529060f4a03044102050029485010130442030340510724940080b0550b0b8003d005190b402d1510302121010390b0b05c0c02c45200b02c00c0300000302e560140c1c0030b400010070908000740618806480100050300c400e09100308500d0840d0340e4008454080c1d08000c04011940740b01c40c0171 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 836513291 1250 836512041 836512049
    0x50403020a1d15090720061005030d1d09041a13060516080403030506030a0203120403030908030a1209240b041d031204050a0203100504050606090112030c060f0212042a 74
    0x1245031508040a4000030b01d001c5c12075000f00a00c10001041105c40c2c1d10382c8d141c0201d500c01d038140c0d44849688501207034400100d10342400e0901000d0217002e004e05200f0100c0b98410701400f52403c01c000d8181c841d01c0c9804e004e8544080080b041c03903148050100c503101d02900003148450f00c45c0400740d0004050014000108080e003070650340d000044245d10700f4000d44000c01da009042c0e844140d100c1002180035080b9010075400120300f00c002051999000040342c07034604481d200c200350044180040300150032059402c03035091445012000300b0048441c00028119042030022030005500c60a1008488080c5c1c0310320f038240414402017007400400300c1226031003500c42440a00c1a900c40c2401843e242c04400020b42503c40d204a4220711800e50340490701940c421000d03290300da100c070410050381c000d00b03000d1000d810940c1c2c01ca1400080c050403418844610030383c0d000c02c0d98050072040e04200e0704500204810009494100410041e80c00701402d10f00c2d00b0a81e6680b01401d021845c010700c0300301802 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 836514541 1250 836513291 836513297
    0x10f0501050702100f1b0b160305040201200709060b070614060a1202150a1d03120901080709090c020f0f01020f0f1b1605210d0f050403020a1d150907 66
    0x13031135801d2601c82d69001c2208041c1b4074151000c02c3c41450311104a480c00c0305c44c035030b000d0f1003a02c04281c034503c2401040e00a54050b5298640c010390002c041d2040601c0420b010168400e010700080e4401c0035009810040202405960326010f29081c500f007500c3e800c0e5661001500d500e820001142d654401c69025951000200054481d89101141000451041d00c50101c1c0d40410003800595010f071a4a040c02c10305240c5d4400c0d51a5035050554864031f280c407201d2981c0007071194810b554407880e0031a500c51858645101d51580d175040178003c81e4038041900c801a0000f243c01550b01d0010441304d0b9151a6202c000c500c2c240c00c82c4070707036207050041d072550175550701c03000503681c2c1180b00340c6004043c0080c2c15802d444240030302880401080c401440b1b00c0d03000d000c01007150294490650585004141303c800603040001221030103e413104188149007090007070502c00413003d601ca5601c904090045c00301401801501400018284440289000325402200f41080c105845001a690708908141 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 836515791 1250 836514541 836514557
    0x150b090307091523060a030203130b0429090705040c05070804060519080906060103020310080f070e1f0b13090513060e0102090117070c02031005010f050105070210 72
    0x44002400c2040070b62102c0b240600f0400c44010b0f0400c40c44407507080760380c140c8849038081031660954554013001140705900041c28007402d1a0107001e5001140c1c08070303000600b59441911a074518040a00030b0710141d074412980442454204040000410035100030f1021803894a070180d0f10b607030713a00d005004240c05503854011303c2000d680100290341a60b03038055280d5464540720f043c001c040b41c005800c03007980042c1c9141c201c0900e90044041a0040b42c2a002030690390b640c960040d406503001805202d15018002d00001d242d180505c20a1450380c817070409061031500e0030030300703411108005c2c191981c0d44682403104400c1c450320b400882c0031604461100764030f82ca000b4440c1c440c4100140d010f01400ba0428003084441c40f0b0710b001c032800d900d00c0384404100c0344424100305402c034003401c10f03e40c3c04504c10078802222004102d41541d4002200d1500b0010b820082d40483e0078141e803030310b503040c810b91101c005014444d001012440034240a190190801305603400088980170140c003d44d061140340 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 836517041 1250 836515791 836515807
    0x114010b0d09140d020705121b06130308090f0a051c051f020a080108032502040902100203030403021908120702070504060602160b0c0307140a020301050a09021003150b 74
    0x164020b0121990082c00c0050f040104511a0b625000307040d0144005002c0c208021400c3d00d0010b8211a07101d000d1070007030404c024041c0d80c000c408690f040030b1a51026042c00441c400e0038000fa00c0784080c601c500308403501c0d0224031050000040303818023400d02c07905800c0030601c0180c40d643e1440d040501046482c1e00f82c400142046030801040d89140c0b08070401a0444030307460b0495800805685905035a41c4070726070b0340c80c1c1e4459103d0062010b0303a503450100015032030f04680c00f440d03090000c1e030000700001181081c0ba80014203007145006c90b007025800202c00c11051540501c0003400010214070310962244040d03480791010b1042c46401c5000490500200340d01da4400c11100001d1305c0090000c102c11794031544060350701d05591400c0080121241c43c04510901c0f0041900c20a02010300150704105141e0754011201100c540c000344903200c1c044101c009a5405d010f01030040c90f00c0e141c0041c60075818010f02c610203141d1180102411f041500c001a0a0103200307107007045074800c1c4a05500c0e5415 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 836518291 1250 836517041 836517067
    0xe030f070c0905160210050708071d03300316030903031503080d060807051f051e04090605030f06150d140f0d09150c0303020d05070c140114010b 64
    0x1c94001040355440e090800c00c207640c203044901c140040f55004c9a5a0804004e001c105982d005c550304070000d041c100200354154041c0000003810b00103454820715040310000801e1512660075101c445444d06440b14014080b12121150a602c2441105034030394902480c0c11f810b00c0400903040c0f1304041e640d119030340516100f640007a006000c1405a03561603907690a000c920f40d00701100c00c2c0b01030b924000380000c4c0c081c0002990012a40083c049240040100904400760030f038440d03905090100c00c000640300c60208801047e5481250b00e10350340c546082c1610b160444510381c001d98001c0d44990652401d071800001c4c140d41c0318100e65510301410200030301265500240303000060a5034218a03604410140220b00003180111070811203a415003241c200300c0d0721a0280c80350303c2038100ea5a81098040344989060310902d03000781005460003101c0d1540b907044440403100e1600080a42a0703a0041041c1c0c042103410f1300c0c40200080c8040150981c00d9607410701e0601c00c03240c156200182481541c08 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 836519541 1250 836518291 836518313
    0x40809090405010c1814040509070b0304051606090b0d0e01060b1809070c12050306150c100f0b030c04020702040902030102070c0602190b131419060b040e030f07 71
    0xa014203810a1030425140081c0a40511110070011503415440d4400350300340d126006089a0310600f50390149061030042c4801080301801001440c0202200030400c1141c460080d809503101d10020500c108141c074512021494030b070440401c020b95030100300011070140c026642d4412980304001500355800400a005064035400340c0410750020a00a145002800306c3c1304058000b40c5000c092a0f80c1c1e8001190300c3d1150400050012103000b10700480e15104101942c3c0c01070000d003140c184a84241d010045a4010f0000307d403c83d4020005048008054064200c00c500c4601d824000c82c140800020b031640350244203680110f0780031a02c041903655940042000540140c000c5694002e80e040508402c8441d01444015100303600710428011405a09888080d1300425005050b8940422030820744003c10344c195071100268080034447c840511050a01803a0020b411002c810300d407400f64140da2b51021030f10310861030709100c401c440d0804011602d030b011400f118150342c0e03515841d05080c03147c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 836520791 1250 836519541 836519557
    0x41802040614090c160f06090203070e010312030b0a050103020703020c1e030d0c0305090d051e03040816150f1b05070e06030613320703020f190e0408 66
    0x1d0402000242400007a1009101a102a01e04050b1561036072030310440d610a0340a004001c8007021825008213982142426105106a02c0401c41041580003c3d282204a40007180c9200f03201004001300180030721034130750541041c00c0512075a00081c000940c5105075100d014189900059000105072081c09819005c003401044103200700ca682c402c1b140e0390701000001e10b00910528074040b02042c0141801444240d156036250f02d852695003d008400104110455881c41840e40132041c2c00a40d056401c54000d5050085440d2441c0040302c910b000920300781e401410610603401d102c2c4e0203040c41000d03c2c035045c600b0031100c82180c0744400ca6100301c10b0b01c84141403100d4113030303103208112000c00c200d8102e03058411184201c1e10740c401016141c15040d1000085445040a2440094801f1003030380c081c0d8002d9068280c0d00c50700d0300e03120304c000340620b811045c0c19003282d02e003801145440c1d2004c881809098a43c00e06860402d80041c551001d13500070700d8130300c080c040c000a0400240c0e0741151100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 836522041 1250 836520791 836520799
    0x6040323040909030206010515030a3243020a051902040c141215044113300801050915091302041b0305070518041802 52
    0x95aa0360721800001c140f0312a0407401401403500014152901d030811000710920081c106c3d01c0c5031600403903603000700840122806d4140181c40b060181c1140d9080c250703016442405064074901d020303a04022034814605a040c00040a100d502e40001060b840e180c1c0c0745003480c5245110620300c804181d2800302e001800a18a10034400e240d07130400c503401d0140300c0346032003601e0501900c500d006044e10362441c2d0f070703288440c030307030400d003d9450b4414000004a812030760300358194880c03203010000318003134502140325201e10028503880e4801d400c0b580b11000094214038400000608400d04c84800c4030300001d0b10811f844921400c041c014403005240d10540c1c0c8641350701d001040f4150159174200c40c003051b140b64000c034081d98000900b90801c0b841c00e42c0f0030031207400058160480c1300700300101c128018080c280500a5a04c1003030040c0c8840c031814480c840031641003440c01403150801800c0d908010305d0001004400d00441440d2428100e00051800080f2000b1810300003010316081c2800320114084c0d80 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 836523291 1250 836522041 836522047
    0xc0302060c0a110102030a050a050703090536090304060c0c0e100503010c0c0803010506131205060f07020f151f061121040b0c0708011e050114010206040323 69
    0x240300006082c90100d4810b0b0040d0903c450a10f0040e80c4034052503481d000415000c01c08141c907244154001c1160364402d003840c09000d42c444010030b00c942c0803c40088604c940c01454022481c80d4019800c05401c40d40e101600d091078047c04140d05c9004a20604050118149580080094a121074009002c5000c00c400051620074840b81c0302014038800d1601a510b0141c6080720648510710f108401c2e50000da2503440d41c1d28040500c07509074004090070392030003c1c200c80441e01c0749800082c00c0316070340958000d100c03c0c01c3c080c00101c541d0402a002100b954025203162001c003d01041a9003e10092000f403402503445502044c921641c50200180d4200b00040c00710303005400070082409900802c007182c01a401c00d2801e1240e8441c1c007403142104600c240402c00900d100c20b002442140ba1260035100c101c2d568220303003401d5a40c0c1402000c03481c003d40203003903900d840d1f034803c26004059941ca100c070000712040010351a0300011344044e0810600b9a0381200c40000e2500712400144000041c0e69 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 836524541 1250 836523291 836523307
    0x304300b0a050f0106171614040914070912120e060d0618091e03090e010e0a11070809040c0306081f0e060f0109020903120726160803040c030206 64
    0x10003000c0482e0301e0383d00c02100c24004200170340f007480c15070f81e01030386110203080355182c692119501028070854074040000d40614400e08810b14030180c4020024031902050000c111000b55848203001400c903420844441e1042080c2154038001c0b902d110b4108285400c01d118124003141c07940b000f0640141c001c00009460080f406140e03010404840b100802002c126102d40c03c200140c070307000400944403001c4c401420134100f004072980301c99640709051405e550780d0ba440e00c03921104026800400c4d02a64142000191011350148000c000e110070082e03450024180d50302d20960007000745460007155a0745003a442d2500a40c0400054035079941241c2c201142c40c1103500712000d01d150024581810403410315a0140c00160041c064000002002e080d0307824510b0b660b000b0f40050102c1d60b40752241d4a000b00c0d058010100401000b030003442c0c0c501800040154204c804000800391000b0443c08103c0101c2c100c10042d40702c200141d1011460b5929110f9080003514a0300e40d0b04040d51142c0c0014440ba = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 836525791 1250 836524541 836524561
    0x30207020a0e0a1b0e09150a0305030a08070e13050423280209131502040e0103050f0703020919020d06080a0201090e090705040e0f06070f030e0304300b 67
    0x391003183d0000003403211440e4201c4038101c0b004010741d06000700c3d84101c40308180f413401e000c906503c400d410b0480d102001460000aa0b2040c4d40d40c030540c0c1c503400014031860195808002e16a100e0007504200760300700030a0b0003080398003c50280800074136598401003000c1102e11000c1c0c19a084002c0301d03000c26003480d1403403e0f484403000c2c000d10148280300c1820811074644803d142503816001003a003009691088030740d200e2590450000c90f00c22a504440b001120310034400b400c06842071456a50a07507045107003191a00c01c001c0039014031070740584020401a51740119480d03201c00202c2c011710001c0034160352640640a840794002000d400c4c5540860040000104200018002d0340d80c0c02c8a2a43c1d06400c600721041030711a5181d40c0c0002c0411721160070683c100c030882905100407100f015038641d0180781004000e680305800540c0c1c03109155041a03040c043c4030380ca00203440285203060b2030f0a40501c20b200c0401c8480c100302e00b0409131b0402c84103c40e1030b4482426000640c10560703244c2602c203c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 836527041 1250 836525791 836525819
    0x903020601180b0f0402070203030c0d0206060f010201050f15010210090b1509130803041e0b06090a0b130c1106041b0f030b06040e120a18051c030e01030207020a 71
    0x10684030b44490740d40030211040c000c0002c0003401924400311449680c0600019610030364050344c0500c400c201e200781c0d41c08204400c5034048110b80c00341c00c050800743c08000c2c0302c110440f080c0c2e0440e8105010302a000841284e440e400c4006038210b04072451781c4c600140e05203d0614000500d0900d40781c00202400400c1108912a0200e441e6442c10070b10080100141d6503c240d4091416909401c0e0100c00036400900568002c1e004010f41c6211404200120034036a038580c038101c400d40a050140400c1d0b0914940e5660814070001c0244a00c0d44602c01084c1c045480505032000640c0b00d08401e040103000f0041c0c0d08401c803449080d5615490241014030030039440c11514405150188000100c041da00c400c54400d0343d41c406584036450f01c5410412001d41030304e2112001900903490319010404500340208100c96941c0c803401500100044081c2d66584198002400f50215910810030175800e00341d03c0303442c2a49418400700004412004070004d00854074000e4010160300e50105501c1181480d0f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 836528291 1250 836527041 836527049
    0xc101d030408061609060210150e04030507050d03051308090d082704020a1205060a0503060a1e09030504050d05010f02030a020706050907050109180b060a030204030c060f080a1e0903020601 83
    0x5510503044c0c0d2848112014203051040310010b820207140040510811b420030b15081408505031f000e803d45842000200d03680646084001c14000511101042001e110352141d00e0345508080026180400c4038141c000c0700f08a00500d11200010304014994030080c10310700c1c10b0b4104413025162000e25000d0511030450001403424034400c1c00d00740c0301d00e241500071600000300c4c40c1d0742c00607000e040c480780310301030000900b460360f1220000030702180366141045064850700f9010740210344d81403070000100042c45010100303d441403c00c06d0160100360442d0031103040b01c0094036840d15908150070b001c0e00505a1420100c291400003040c85a0004203170007a000c0c213070081b8000c02c6030303480c1ca82c12241d0b02c04d950300c01d990110304880f070700304404054480714030443d00003464041105180600050520f61040c010040070a902040034400e000e4200701c28000350910b0b0400001c0c0c0284620040d0060700700400c00d950803522500030106100388005040d998000310301c024041b141403481c019440d0360007405 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 836529541 1250 836528291 836528311
    0x115050c0f2413050706050c01020c060c1c020301050f06072d02130e12090402070204181101080138030403020604170f071707020d12030b0103020c101d03040806 71
    0x200d400c42d0f0043d112100c14540c03180080183c50725124080e03405401100d81c5146d5950b091102e851203030710510000e4031494007128900d980d80c3e0142400c40b52070700782e20051140a84180014000c5413558030342d402000302c04071480e64851036a85406200301c90844c2c181494000c0b8400585803030f0f00c4244203504030a100b00d4143c01443c0565900c4011590481440c8209030b1229481161120403200102030145c00600050700c0c0c800d894010405030344c10417825000c0e001030402d808083c031000200e420429002403234417240075490049080a44000c2060005c02c43d17100ca502100c0610000420040d84d8456090741c907201d240c41d0030080e448a6080350151109402d1404414800002800301d441c4101c4100702141000381984582c61101c0e5202440b41038503108200030005130b81c5004100e0441880340114000c00d608600000b41540d0f0340100341c605050051100054100d00401d203034203180884480003440b02c006401c480c803004403002c200400c5000004022840f110049a600d00c9149080e0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 836530791 1250 836529541 836529613
    0x6030c020735240f1503030d02040b0c07080129030102090a0e06040b01080c120903090301060b07050c031b040f060e07030605040506371503230115050c0f 68
    0x19100f01c1000804031010103a000301c0e800007490200324401c11242d131042c007404590402801c561203c00700e0f44550009c0b0480c6501040182c0540c90402800018081d401d00911400709a004880760103900302c01481c03c040e1021520440689003581914035180000702100c0805540d22074000b00800c00351010f0303000e203081c4003911156500410070180100d074443c0e039807441c090104100101d91300300607010358520b010400c0409805c4e5000d004003030152101c0008541d940c00e01d46042c5280003442c1c2042c9020b50003800001c00101248005d107031040744103940c0480c0c00700f19041600010103e40d00140c0000144030188140b0580c19403012054803002d503002c00007074540104100c40c1410440c103144010201618011952408440c800321b840e100203050810703981ca400c1807901101c0c00d40184400a95100d181c1544074600c00440001915a0000070b00b40354100320900c034420281c40c00c0c041c18004006041c88260300c2c20801110341e40d1501c42a1040140250f20001d40da800b02c2e85003034491640303d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 836532041 1250 836530791 836530843
    0x1703070302093007140f040b0306010f18050c0406120b0d0c140a030b07030902010c1401140c03130303050c1b1c080c070210120c0f0906030c020735 65
    0x44d0b0782082c0c079824100c804600c01e000341000080008011503940007500d540491940c0c0d1010420745018269007130b45c032048207040c080251540d0350000304501085080000f8841c030481c1440032982a40c1c91450300151034850040040054a400310310705801480b00c200041c01c1c801d106c003411045e54030702d0940d00c01003480c181c2045240b4146020203005041031b08041590240a40c1c82222030301c2c4103061070b02d03140c2d04c1501d66855000780c1000c1c070b50550751540200141450b60031103056026414002c0d203070179401c1141c0c00b00c1e0f500d240d51000906269803400841c0c0d02e01414015600031912100c100f20074034074030140b6182c03102d001003620052100060491041c06000b030300014456000d8030205c504140c440c1e0200501ea05c80388810205000e403035049080046458040c0d107004140c41e07110021249184400244540791703540c020b000301b601e040d04810106501062240c216841c40442c480e12180c0c002c441010f0050b521703400b441c07050b100342d000b0040031030100d00352550503082c00b800000c1d8910 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 836533291 1250 836532041 836532043
    0x711010b01080f1302030f010b0f0d080d05190204030c080106060215360313080f070b0f040b0c16050906090703020313120c1e17030703020930 63
    0x548880d0108072860005841e0050307201e006075110321346207407407103100300541c0100c0e00b0845151342c0c02c44265110a07694220342020f03058903800d00020740340e180c01c4881076103d400050190150301c01a064030b8802198200d069400325100351540381100b19902c681c0c91400c01304103011031140000950030705a00050003400818041d0011041110b01c00007592a0043c0e900e118129059000443c03010480c18004108540030358800680c41d00029a42e565945144091207001341d07000d9102030b403121121144c03d4901080d9441101c05c0b00d59119101c0d403803041d070350409000e943c00c1801e16040208460350720317410004881264440d01ca80e441d02c0c85441d8000d100d00004101c0b0b803503401c24040c04c00f180229200754001c6521101c0c050310002c018149950341c01582c1d403103480360030000b85034500e100184001003280300c134048050b0603104039140321503940488410484000000d00d04000c000140b0080c0603404440303881c1c40c014040b1011004010200d01201c8a40341103540910000b022140350240c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 836534541 1250 836533291 836533301
    0x201150b1201140a0b0a090b0a08010302030f0a031d0114070303060e0108060408040b071e0b0108010b030609070e130c09050f0a0c0e060d02071b0501030e0d0f0f030207050d08071101 80
    0x3c058001101c05051929041150b4403444104007040761200c00002c040c4c2140300905080c84c0c0380da840c02c90f1545580101850120000c02a0304107410460031080026007100c0504080900065a00e42c52203111780103070340c09503d641c6013070f072540d000248840c10158180e000c0e00a90700c01140d091402d90303d03107190660341c03501113030001d100302010081032040440f450701429403a8803c090040ca200d4686150000d21504c09000700c07034100c014401884298421300030300e14044800d40040089140070f0b20b05982e50032603440b50f000780082d1440400c014a1511981c40c4110740c1049001d01081e954922103c018001218404a900c943d8000b10300b800440c0e004441e543d50700d41e603a0b040142c51030800c202030390f8404801c05405c15400c00c09038000602500743c1c48002c0300e84480042d2210702c0d001c0050140d440120b030480258004040303d07910582c0040c0440c0c2c40510714075000c5181c001066040d0004c1c481c2d510003a00920406101002030390b40400c46c940f0070000b5580d104155000c80001d103003616 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 836535791 1250 836534541 836534579
    0xe01080307080d2a0e030a08090f1212031e040b070f110a1407090e0a030f02010902131a1f080a1b02060a240504020a0201150b1201 58
    0x80c0003004680007080c405005000e882c100ca10f400601180b5500d409407850980301c0e100c04040f40309010b603082403078002c8503100c81d0b000700b98090b049118480d40c1d12340c85485080078440c13140c241e1024039081502c4070417603104c162200ca400c607440301e070300c8890001264100321900002d40361502c9a242440389185a01802141e2000a10240d601c40c5c020a4031041071050111003003001202c0a500005420003410b20380700e010754026030300c80c1c40c030340c42c641d080c41215082418107508000351034401403000285500710a0b01490b0076841c004c00c121041780501a8900007946c013280b961015052042280c2c0702c0d200004150700d00d805004581c03070612801020840c0070204c030514002c8403140050040601c02da000c4584c107030002d01c0c1a045581c0c60840304414524900690040c1e0030400842e4040c03150740948680890100e176081c041080344440507034240038040c040c40e0045070b00e12015000f50006489140e55200045180361100e6510241d500019186c80c0c00c500f1000001074950b0025030105690 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 836537041 1250 836535791 836535793
    0x7050f0f0909011104060c03020f06060105070b1b0708091003150915030803010b03071d031b0d1202010c171302060304020a091404030e01030e060621011404020301060e0108 76
    0x500142401c00a0108004000382c01070354030342440100603042c400080c4094001a1520b0150b22400c2c180240340c90783c66103940446034031020600640b6038004c020755500d150700c0907000b1042e9545c4407258802c620030700e16102c2c07403807004540041084074180c0036080750f210640f030700380a00d100744404809582606030b4030385040000b000c0070701c0700d4406500582c902000800b08000055604e0392114240e074002d0340280d0a80c5004001e000322980d022007600019010740340c44c1038000006000103511604110f00981201110240801c03c41d01e518066490054001064182072a01207001034041d018190407000060081c1707841a04112200141502070512070030030019a0300305602303105444c3d102130000c0e0b03071025140c100014005094050700d0109070700380e452080e0304d080c1031602a0944054040b89030500d810081c00c1d1424190016015603c50402c9440d411821680b20680900701c85003040e642c969401e00755400101c18507050b05a000318429002040000e0780c0c1c09281420401c20302440f242 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 836538291 1250 836537041 836537059
    0x50c120c03090c0315010302040b0916051803010c030515011d040b1c060b0114030c120705091c0c09060308030f090c0a121205040609062706050c07050f 67
    0x120031800055540007107120700b1204010050741c0020f28042e0700d40f1808110218080042c01142840e0050211148094a0615036810f00e000d581c0301418070410398104100c000300d5202013080454114600d0642c015000300720018507003030000d01a24080703804c40800c3c1d44015803d0019445081800703500c044800f10425800e04c82400c01c00600403602941c3d501c00381496030740041c5032444410880e020700c901c50020300c1d001c1a10001d01300201248540c43c07170030002d104000414000b034044600d6800c120313900d03034581d42e6002420755503406440312042c3c000711620320404d4400100405004d4141c020041010341968440144040d100f40d400020141ca0f0140040780d1010182d0600d650403800103001c5c0c0369a040c0d100e0201e14100d0f507540c000e41c6103144c2c262501051065110b42003501c542c003890580e1074a0f08200c8040c0c1502420b114860030003031401851404400d03403540a1603482c04411082081542c0c81c68020700c0781d0001403031000d150041c0071f000142c034907080c0c2e500c0a101101a2000d40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 836539541 1250 836538291 836538301
    0x2503210e19090509070b031e16200a0507090c030f110a20030a0c06050a091212022a0f0c0a0504090602070507031410050603070b031b1c050c12 63
    0x1420003d401804144988000851095403030000f179031040310020200340d025080380302512400400504000b05907401c3c043e072800b4003640180180b40e4810b0ac4022000310490101c006880c2c0003803428083d0150080f410702040c5034803c0e0300034a08011040d03034140000012602e0040c12105c180e03444980c100340411030320094a0040c1d40201d80030008004000c134580701d041c41581154401c101c03410000703040da00282c040010074401d01e904911032042c10807800300c0a0f521701c0c1d42d6021850781d1a09002a0026101c80d00c4419012650900041d030703005240c1502c20000c51a403d24070107004851070192020061754072600041030a140301d00200300d10b00061500b030034007004101d452020b841c415001c000d050041102040b0f01c2d1300a501c5800c515a40f0000c528455060101ca10061040316041038180b0045580c001040029114000403213039507a00e6416101101120040d201c4a60700c102080028240c0c180d0104500000d0120f44103020f142c0e910603140c40c20b481460304141d5900d1708800820 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 836540791 1250 836539541 836539559
    0x8060411060f0408060402010f0302070c06050c0a1b06020f0f10050c2203020a170307290108030901080a06231201060e09011103092503210e19 63
    0x144034460054012071401050010034640b5502c990002001603008209000c21968030102c1c84980e50031901e4218101582956909904181ea210703d600300040842d48100e00d01d014450820425844030610a10b00c52039005012603206612680300075001d00001154201c4011600900c900140d07005001c002c000c0d1741042d0000d002c003a101050f070300e00521000b03608903c0700300100150044000c071a82c00c00d1540c410003000b54400e800500e60115000991001460004152020700b940020050300c0e11011100846440e80c2000840064018003000041c1e56507003c8002d103074901003070341d0b174842550f07540300380030285d40c1c1c44d1007650314101090010300400031005d64a09031501005007603210040d01142d80700c0c00d4801d02c1c0c011400340304110082c4032469000744180481c000d5100b2008d41186005010707140c480074071110b103c0000c5001264264040f41180602000d0741c1d0249134040348003008400900c0c50080c2201074030210700350070101c1c0124074140800c48c8501200c2100750840c5070414400c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 836542041 1250 836540791 836540813
    0x12070e0a05130f24050a0506100c0b0606070203151b040f0302090405010f0e010e010e0c03060105060f091323010b040b0c1002040602010917030c030f15041b0f0801080604 75
    0x5503804866162003440b035248079013440404020725000032a0500f401c0340c24008541740503100d9842040443da5620390070303820800605007583c000300c040030320303130340b504040341c51441a400d000358517005410425201403c0c802540b0300071041d14000c0b0400c0540d50300103404500c202c0c0900b000c01600700ba0108014075001008961103440b48002081d0003100c415000b095072140c0040c03040a035100c4c50b10041a040901c50200c04090182c01403942c1c01034000426290b03081805040d015180002e200460450303a8001c035400804003400c502000f103489807a680040054100e901c42142c0c05400da80208003500c0d4605060368020342065203031900d4444502c00700e500648404d855030182c078850401418252019000030292900045083c081e58940341e58440400401008543c0090052042c100d12220950368030140c84d8440a080351121404030071b140008101c195805420b00720042c122007880b00c80903a10340341d9500d8030041451000c006680f1240d0034007604240364003030800100440e05481407 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 836543291 1250 836542041 836542043
    0xd12090609030b0f07030207051b1801150302071a0405060402040b300106030c240810050d03090305010c031508030a08160e0d03030e1501030f06051512070e0a05130f 73
    0x100500c0d102660b500c260809292b40c54080084180003185050746c02d00b03026140003030105409002e402d41c102003e026031100001140010580d0100301441044001c581c0740707005811000c8240d03100e1070903160480d9205000c0742d089009506050b6040b00c1030601c04140260354180c2d034130002c504186c0b45010030140c01c02c0c000c070485540d00c5400000200307400142943c05000c41c4481540004201c0c2e1a824608064013580d0b000c00030714404000c4031454251009060700e9040340c40d420310803000d040c104c2d281030b0070b0303007000e003555281c00403114010790140e110001c02d03038005114060f0180d5520481d500c1303001d80c030b0406c0f000c00d883e07500050b4282140142940d107032045051218079804031001180904542240850100781d69150506840d002044441001e108007000c00000d5810359641610190b000303000203001503201c00c0030440c1505802c00212500c903000d452842000e0360410b1880e503409062240f40b101102e004040384200545000d0305102d0384444440b00ca040c3c100d940c07039410350012644 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 836544541 1250 836543291 836543297
    0x31104030b240d0303050108060c070b0403050904150e1501140702120102040308041e0807120b0a060509070203040e16091a04080102191e021c020106050d12090609030b0f07 76
    0x1d10115903900f0003034418044c042c2d070380005c842d030610666a2600402400014840303e040c400e250024000d04100d03944983c0c140b0300680c07511411030205d405808406088901651000808542e00d400307805454461a546030181034000084001511004480c10001d48050010040f00002d03041015904644a0f4200001440c181e502d0711500303a2500700b031304144039801c002110f880300d490442462402408501024000d00340c42c0108041e501c09a9090040c0090300c0c11000890701126a4441402801e0190071041c840c545070000a403030b0f621600580c440c0b190224085501111520400d40700540301d600d0f491171740ca082c0004020350417011310050f80300010030400841c4074102070019100005008903104c4020a0b1400e018000b03400c0020910103006400c00880030050780007801c1c4060700c0512102690340a5000c05c1203003d80b085400c11500100800070300c404100041e00d200709001c40c5d954070f68200540b154000c0741c904095100142092542c40041006801800381c100d80080ba142 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 836545791 1250 836544541 836544601
    0x9011409091005012003160f020306040b0601030c0e0a090e0304090911040605030102070215030601200312010608040c06050f070212070e0c091c020d08040e07031104030b 75
    0xd8009894501d00b1241544110705200c0100a0b55170840a04411074500384054035840008004150362170140003c0003801704aa0399192040c081e005449904c8141c0240980340c081c0391034103044135085d100f40c903110f00080c6044a10300006120384009400031300006c4c45015070a01c1c0104500107000c49141c640b00c50f0004120001c1d090480384285584c4174800c45001403030105c000100411a6402d512650007a40100a24401640d84008a081305240c203c0c1c80c03610b075220100100d500c4041c8502d40030001c244c04170030550205000002d001d12880d4080300c81500d030388038001211007610540d0010000f14989000b4032501b40110b0140804038044404a410003840d1380010b0222015041b11600030b802c00b1707a003030010381c80b4544c505c0c0d44068400c080c81e10300341c03985010400d507072500940d10018000c510862021561000880032140d0307008190f030b60b00c2d50749482d000c25560005540c0000400d181c0451890544250300070340b01200d030048411142595080d91040003400020724291007002d540c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 836547041 1250 836545791 836545807
    0xf022d0f19020f0609090a0f0231060c0203060a1a0604140a06030614040e070302030a2312031501020a0c08030406170c03060d0809031c12050903090114 67
    0x1084115021049001840c01d0901c01d40140f02d011096010f0075030050b0010025290b0503116041c01c2504402d440380e000031000c030000d112900a02072490b1241c00d51461220f4007044800080d440c00c0043c4142c82162002941c501050324070540d0701c00000e42613009200020108440d42d4080c88940918035907050260210100141959016820582c20a04180304140c0380c0c0c00e20070062400303002282010490241420fa420458801c00c8072102e20031364403030310440c0003030205201c041700860340582240d02869062400c075147c200440d620030000c40d03100d000c21a6401c00021031803800e0280e590624a1520307001100503600e14070b4a0340c94194400c844a4100046161014034010040c990140d620b850170000b0090007003c089035480c4e1a83c1e03d00040c00110040e01e0201c0380c00c00c400716212240c401851a0400060052114060345405181c11282041c07111070410840341116503140384150080c511080d0403540243e6a01c1000e0f031060242210329402980c4124406203c00c892a04007518 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 836548291 1250 836547041 836547043
    0x3060317040e0901140c2506140f0403360b0d0c020723151612020105090a030311090a030c140a08030307120908070605070f022d0f 58
    0xd0a40406a408000600304688080240e00b6600714103200000c0c040034000f90541944000050f080005203030000035550941074a0118400c825041282900f84140c00f9080c100c0040c01c1d046020300390034501d100040c059840d103054940c8507551507103d031040064180d0100d888500c40c154100004004495010340d07041c445c1600b80c00401940100c5551a10300c0070780ca03c107583d030f0450400c05640c042c0206220000c004000030020415207280c1062078048400000c100407070386039040c0211000007400c20352481c0c0e00300e0400c001600415024241d50007154040b030896100302c401040136000b1110000c000303403103900000307414224040040e06108542d07000540d103d0a50744116240f4222000400c02030390b030511040707104001200e8040005140403022a200c1c40700914800070803010703000c42c0e10131100e150302c07019249801003c030a48503503584ca027001c010a01070721100040b5214910b0500c0341d41c8006802c0072020b00c62424220200b000307201c480d5101803842c00011481c090510b01c5507480c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 836549541 1250 836548291 836548313
    0x60315090e06070e0a14092211031216060b03070503191e020604060e1507030c0c1703070b09030d0212040c0b130b07060b06030a021c05040b0402010807030603 70
    0x58814003504140c18283d03005040040c0e8900c0c414011021680100000740d550008040d45010070754114041d55074003150641c08445034030004200d80b01d4454648288203440108140b40d04041d01114150841d981e100c3d002e078018008214039415140c244840001c1c90750704019038a0300c02404a513089601d07007001034104004001c20080300070380007440c24148000e12115500c00083d10840c500224500d0700400c2e124031481c040d413000c2c00a00e4841a03034980f60650f0307001c8100e4000c0c0d81d650701c1e103106160003006101000015114541400d1000ca100b024100305800303404185402103186c40500c1da6645c0c50014003c08080e050b00082c8195042a2501c0c001007100c106418140345561919162801030401590411091002c0521003103011540e5240c1010a81300ca0b0446152103000e5890900c014001c4001d040e6040340010081c06013030040d64003d0003003103280310b0090340c0000500d2080380481da000c41c0d019050140030000f04015500562803507030400d1031032801154442e100c0e01c4000039a5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 836550791 1250 836549541 836549561
    0x230c070f17120114010804080a0c080f0c01050a0b13230f06100201090b243a0b06040903090f080c10030b0d02010f0c14031b0d080106031509 62
    0xd900142ea5109203002050160141c00c5006881c0300b02c03599940000c0c034952004000401ca4003000603070305021405651500315040c0d0050080e41e69001042e0501d6041c0c001c1015007003950f00b040d02103941c1d0000390080280c0d8040c003074400d403140c0d0060801d010203440d0790102c110b0080c04015820621009880496204a00e40719511440b8144001403140d11b8800700359100459252405900015141e58007940d0002c1890080003c2100c10344290403640300c0c90030b02183d120209070b07101c903661003001c0d0a4455018804400320218511a11000d606503d20300000341302c8004440040c055261562050701140d00034681030000303503242da9100005031074a40090000e43e00119101c20345180443d032450148003545002d0201610090109441c20023a01c1d00905100b11080e10801b9144200d041c0c1c41c1d0540c00c4109501c000c820000d003961654000b100042103c3c03410080e00b410440000f40c42000481956588440c48c1c1c81d00c0001ca00505a4003035036901004140300015100c02c0d1401030201513 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 836552041 1250 836550791 836550833
    0x181501030c0e06131e060c080702150a0905030c0d03090b030c0c0708010b09060604030b0604270f0b1003080d0b0a181d0d090303050c010905060712230c070f 69
    0x15051240207000c402080580102d141440b070030038000c0540c41f904e8030800070380c00f40b4000e44034150703840022840d40c02404d1201d44c9803004900104c2aa42c040312040840e04240d0995400c601d60005010015216403030140c0800c0c044801040b4041ca0200115030081c01c4101a6003094848405582400186d51089036180c4d1a081151414601a0321082d004402200c1da5460700c0d1650350384098180004000e144100c0c0d070344079000c4420010b8105080019500713045020400c2d880c0c60442906031100d42c1c1030f1906946200003801400707171110f2000c2901c3d004842c4504141200c00000c01802d1500d40003900040c9550300007420035040b41c00843e503501000400300d550805074101d02a180c00c2c0320ba03172105560280320142c40d031030f07003140c1c100c0190707071301490710a9a072a04062034502400840307074011b00900c0b5800800c00741c15403100d80c00101d04400c20091082842c028000f000701148008047c03078600300b01001c01e222401000c0149075203881100343ca41c001c01c081e04c0c1d031903910107405980509 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 836553291 1250 836552041 836552077
    0x62f0f16230f01050621011d0d080903070c052101051602010b19060c0201050708041508090f060105060a1106011413112a06010801020702181501030c0e06 68
    0x140704061101c0049034518400800c12494400000b03a00490b2103501208040c01e448002500c03041c0c20b4101c41c400d440c40490406401100f017002c250f4400c0c1882e0110005407400021a10684010040391842a0400400301036141840204040c810f408211040d0380f00c00e0818104078580700b8040c1078400c8030140d0050800501c4410080e09680b462200d03288140c6c0c4400340e0030440f030b030504c4c82541a1005461703c5c0c0c1c0b100003a880142d03124844c2c100e01400a100110300080e040c42d40f160340b1400884240d680e03079280d8961050003a9076a2408030f4030b204582041d001407000c0d04000c405132025105600d0800240e03002202c1b21130034501d0a800014441d40d0501581045051040b203440500000310410048c15100403d6161340340114424030300000b41c07410780f080c001c0e030a20002d0103c103c90081078443c156502c2030020b00079032207000200d0140204c01d00d540010402409400e20808008079141070009618004400400c0e514880310140031005050a1968039688080c0501518030456607003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 836554541 1250 836553291 836553353
    0x100b0906070f0309090b010c03083112140c1b150a02010911060708030115180b0a031406030d032f03010801060e13030507030c080304062f0f16 63
    0xc1030b100d40328075047c107001e6403140c0040000d82c070642c11940030f40600320703580b9280d041c00c2c1603c081070100f001204100080041c64070030702401d24404c06003107a03035403502c050060400e0100c0c411030050441010141d003111510b0040c98282e045822940140185403070f203407100d102e403003008a402c07103400702c0010f03035644406a0410070204824032812100b10b0321681040e81c107035699403140c401402212007440c1000c5800521f5402100d6010640002808448000e500e40481191a402c01e82d50540003d082c8502c0040310000c98403814017600010340607182884840109501420814a40303103c0004400700746c03040039401401d0082207404d5400c5840d50382d45400005402d49149400c0f04003441d40680c144040c44181c00402e42c05980e060600300c3c0c545007a814241c5400c2501ca4002d020031a001080100308229503001c100e96001608011000100e001d512030740741024000790708070740f240800c002c0d8240000f42c4007500d4040c080c07030030100e400b001e035a880340c100382c107900c2540c0341c56510011004c07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 836555791 1250 836554541 836554559
    0xf0f040902042c1005040b122e090201050301120f0210050c010b03030c0717150a1b090806070302090a17012a0503180f0616020c0108100b0906070f0309 67
    0x412008003050030b483d6080036010705140300901d10401303101c0c41c0c2c0c0c1c0c10001841d480d07a0030805c0056941c08142e80060442a2250340f044960b40601489849008004144004244036242d02d0913010380d503413429a03081641c500030034289404240c480c400a4403031100140d407028602400d0344015603401c0e44071440b582c1da003070a441c0301c00e503a14440d070428010703800003420010303481e022182131401040140031000415407c00d100310114042241c0d088040001140302900070708511460311000034007041021804842c2c51881e80103070621a007007071000c038400900c039401401c01ca44005004c24145691202c100768007121941083c51a039440714030119081e40e051039a500600350040c05152000118a001080b0b80300003041d000b003443e0030a40c42642d4100421030074404181c41011a020703402c12038100340009200059500061180c4601c400d81d951154901e6406507103001e042c0c1000c80e040004003000c0e50401341c41990082003e00002c0b0105500c3c4543c4030a46000e030b229130a0f8581000c80784 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 836557041 1250 836555791 836555849
    0x6011d070f20010b1806240d0e07060e0103090b010510050c060a0606030e070e0c0d18051c030e0a26040e0405070e070f0e0a0f270507050f0f04090204 66
    0x22103042a240790400c081c6d03403100e03690080b50480758480c110b2003144040c1d2003803460043c0d0100c10000c91802225034442c1400040500c2030700c05946910019411600044050b82c0320000c0041201ca4080b0040080d410540008910001d203418100d0a000b560103000349171980803141d85441e01c1e180c840030851517400d40f04000b42e150721400500780041c04d1129807112a030001c1e01002001c44002014070f8002c41d40d03481100c05803a442196403403004503051030756072041c1081900003a0345041052044140c028440c141c15994000c0c0600f0340711f011600e580050900e10480403c0c50381049010840d00c10307444004001505101e48800c04908107810040d00c1c21806802c540e804442941c14466402c0d0091001003030030305a49800c0610600380d00c0403e980361080c1c0e000d8031100610070f4001c03502000201442022050414813246680a98052542952801e580304000301d00700b04048516074081400074840d5210700442a450290307200c001c4c0040f0b03440760380000c40c000e190f0502d000e01e040c81d80c804 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 836558291 1250 836557041 836557069
    0x13110d090615050f0108130c03060606030b0954160e040206070b041a130204180b01030b040809191e06081303020a061d06011d070f20010b 61
    0x107141c4c0041040d00080c2681d40064080b5a4503956041c0c50010030050341c01000c00f03107520000c140310030b566500d001760191800c260b185106040000000d104681100c0d041025080003025128207403403030309519054880e400c0494190031401062146848500030094024150b080009200940740b00766012505400c075001100520709580c144005690f403070081e10742e03903a0441410f242c2c40e02c880c9460803c00800000380045081c842c4e0400c04c14000811090f40310768002d480038000d1034500c6000404540c3c4010008081c51211001400403800c2c00107025070103445090094945400701000400d89045400c0f804180035400302c0600905044850300f90030341c032240400300300290518401500c40f00c0010002d85d80c0c030011041c0d0005262082205882c0b660b040182004481840c44003a400002c0404c54015103104910000030441610000f403001d50001135506101503c50300f808480c0900b9035038a042c104101c003440c0d44000259032840c000d4540720071000243c200120414004a2581ea02e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 836559541 1250 836558291 836558299
    0x11090702030c030a08190519060b0c19260703030f140403050a02011107060f0c1e2613030e030f070b070503040b0d0203060103050c0913110d09061505 66
    0x4054040c0b9400420350300c80c008242040c9429503134114002042c0886410181041e909120522803190704903c000c032010007003584240b04890b100c40b00094503104c2c11300340d1241503109442110b01c024030240c106900d80d00c10750228043e405404419040d49511509010399664001a56801c150f01845210000348042006200f40810100c94061034030b8010009014000d0004505404074400c2d4403140b2903502455a85840e002e080c200000144041c0c1e407000e50b0989000080c080e21070150410394030524051400c488000503070f02c021034a5000e843e0184112140c00c851030a0420b501c019100d11610301a2506d054a4000c0c0c20004c3c4900084108a8004e400194110b2200300300843e108040c3c0d4000c40302d4540c2c4000398a4aa45580325035400135005480100708014504402d400550041c04260707828400c6860b03500101146116410089038003907248032500d070344075409400000d5020082110b05080604038150b140594404860440b030059440c01c850a0706010240607201408040d2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 836560791 1250 836559541 836559547
    0x203220311090402060c0118060b040501051005070f0b07020313141003150506030709140301231504050901061e0b030c0d020415030504022d1c0c031109070203 70
    0x52540c1d103000d820407080d140145840c0d00081d0540d2640c1040300c0140070000000c0080010f0074101402c29040904110354050501c20004082d16050140d60b05032030000b019490040f51503c03080d0340a42c8040d204503040e044948207400455141c8290310312440e600d4010303690300c958207c04c810800c0c00c150058600e020865408a081c0e840d0310007400401c01107401c00040c10388403501900c60910840e800540d120000004100300107a0010051007100c0b43c10800c01c0340c0c02c0c028400c043c241c03500c40302c041c074080c809150710143c0041c45120300d0303800022074410844001c25460100b01a904101c50a01580c0e4569004000a21200f050b540d14084c1200100400c01c1c1014401a95840090100041050086010f2502c00c0711941224020440c4041c540003007107006002901420702110240e00c903003000303013035241c80c7c0d50021400442c030402d0079a800c50802090003080b001c2101243d81a401e00755450740741000461a08000e00550b000b00e1803200d00384440010000c0e0320074000c1448045400078 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 836562041 1250 836560791 836560793
    0x60b010806150316111209120c03101d0d0302030907060c0b0a240e19021801050a0909050903190c0b0f06010c02210c03030703020606040f060302030d02032203 70
    0x1602038070340040c2a220342e800c0a0084c808101d640c1e4805802c0403a65005900400021b01c41d908000c0001460544010801d8a190b501c0035131210760304624076402d50003031103050041221643c04a2114040301050f030b071000c0c4c1031802e21031510107000307805008aa400410310441481c20030031303440104024904142d41c8804bc2da00c410310018060034011865071190700288941c01d00c1002d03501981c3d001412401800c4d0b545021001034402955078002004d182480b40001500714021500061606161517900c4010301b001141d06501c0810607208000007410041001d01d814050580603c50400c01580c5030701c1c83c1c03000000c1d103254103080f400034403000f0100400003074003100100e940420000e42078895551020016614010241e1000394080446145445c02154402181425482c00800c80d2000320061082c10313076a105210b030141c0564800303000502c103454150851344034502140c0c404210642d0302d03404289042c00e65080f54001d60008140192030f4840a100c9060801004418807c800e00e5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 836563291 1250 836562041 836562079
    0x23010e04090f050a03030c1d030d0c03030e0d020c310203040303090609080c070b0310090509030c01061710051302040203130b0106090810020c15100504020304060b010806 75
    0x404982902490321030441c001444524075903038240542040a4071800512481c000303005020b10140d00010802c4455021181c0d51400f085200c0e2355005001040d03984000c1c4000d552120403a2022810036444141c050319581091004642c840050780040044c10340030000c1001c0800c0e80e40c01695424405c141750120281e0780c40d02100342003203503200180d40b13031203504040b0042c0081c2c1001420075410705e031032101000f01e00c50081c00c01c1c01618007520102902d58034030b410544815901c2640300d00800c041803103182c250760311454001c8540000c403490107280113490360a44207158031100d440030300524400382e0040280940441449104000c2001d4a0070b0b20170001c18401c40440a802035601100207501310b50300c084000350964010760f06045560f502c09008041c4650b0f4019410b05004820003070508102600903243c1010b807030750280800d002c0900403141d8901008120300543d1100c100e0006440d00c45100450089000c0d01012456403a0800090502000030b065036004515000855610b402 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 836564541 1250 836563291 836563307
    0x120303070813030512010605071a0906060402131809141f09051006080f071d01210b040803061e2202040305160510090f0b070201050f0a092301 63
    0x103403602c403941c1c8052050404a070140584051180504c00b25000801c207203802002400c40c1d40d02ca8070000440841b90600e8803000b5000f42c50b11030b0319910680c086042d61800340c024021002844e01c0d8a550b9940c2d810b0411003141d010200282c110307a4941c2c0d03000520403a03400c2c0b100030492500090035050440800100a1211507a0682900c3c0e566116141008400e02124070f01070001d8800b80152a141c60560f130300d4240326180b45c1d42600c6400030008081440e0b603030342d03040c4403241b4403107500580c40c0c881d043c0d01c01076403c0715000440a551805100040300c88044502850040d000039850f0b00d826024002c40034152039003074910720f054a8a000c820359801750102e01403100d02080344400c003c6da0302e500019004541000340070b802910885100e00050844801c11504100c3d804c040405030000256180810f81c09003ea540502031800e100705a408801042407502c10f1401ca80307016190302d0091503541001104100195983e4010072443c03e603503040340b046030540742031400150301c2c800003c0d080d60b07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 836565791 1250 836564541 836564551
    0x1e190b07020c10090306020f090d060c0f0c03080402062104050102030105010f09080d030e010e10021206040603170a0c1a18030a09050904020d0f241103010e040f05010c0903021203030708 82
    0x346d00010000d20204605096541c0c410002cac0c0100c60301c603c0307403424201500984000c100015810112519658400c0c000070480580640320040c0c035840e542c0034451290700c0510303009024115103240d507001100711100d4500c1b5502880c0016125410100014400034480701c245040101c004424030150b003001c150001c1d942060304000480301c8840500901400d9080103242e96402a0700d00a00108440e13002041150480e80762907603a503582004010031038090b80406454860906a1a05081205d1000702040880c508000580c0490345d9515117900385820306440401000000348403400040004040304e45801b640514202180f2440060203000c180c440c3c03522900145010a085d9160000032290b10f40d0041d140c40300c2c040d62810000ca01c0f203819094988945a24102c030030803085e09120700024284440c40300381c81c6918115090020440103441500c07921501415013001500c248207011502e082500c401d5074240c55030040000c2e10400580001103034100300100140307694040c140c203501c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 836567041 1250 836565791 836565803
    0x2010c1202130b0c070e06040e0a03080714041410030b031009111207050307080a050a02101205040c0611010b090f04030c120509120a051e190b07020c100903 69
    0xe208441c155500b51149903100300070301480001e0541c0010808612002a10103521001404d5202c0000b0720003100c03410510610140c100c0542c8600107885940030316041141498058000d241703151140002e82d0180e8071060101606d2000d84540c0c0c10300003000c080c0410346090800000d5950804a074882d0342c110020703c0560385d1800010304100800c0310150b684200504501000300d0b1841100e59540388034010648240306010000403080400210226004d0740800070344090380c00356003030101c600d40f0b07076401d8400e00c29100902c02d00c1d07910a22429208901410024050518203e000f170415070f11031580c01c040364142882901d09844510340303160040007203030385081240da55050885a070001810010021103644c0d80028080e03078440040c103180901100c2c41520400000d00e566950a00418028920b40100c42c843d09a80900d1461110520080c4141c40f400c0c04041e40c0c00e02d901f00e0306001202c1d03030315091040c4036980d1b074100700358031891101352401070000c50310341006011065a8440103080d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 836568291 1250 836567041 836567047
    0x105090601030e0613030219080a12110c06010501260c090f03060f060901150f030b0103021909030b06030c0603040b04051c050a08071d010c0c0b07080d0b0102010c1202 74
    0x46034480d0b480b8522a200f00b1054841c1800c00343c00c0c54070b041c161a0f005030010720800d50020100a090b060321040c15501a105518090040c18195401c445100c4600c0985595401548141c49408000d2416901c9000078003629814003001600f142a81c5c0ca5640654200003204908511005003207030304176102c803001c10344840c00e427030008103c034112541294040c0261414040071545140355039004450880e070b100966230b00d0b15400158044039840c05c000007820107000102c1140250301905070700c00107140151605804c2c081100c845070002d000200020700c800010000d0101c2d2084080d04000110301030403d180181d0005503c07408040c101801201151000c01c00300507040040e40d1b40d032005440c0305ca00c20502a03c2c06001a0840007520740402c8000c40060754092203040703081010b00070618501003030038002004403082000c0c1001212450000d02c400f0a0500d8044060004640310b1404559102c4d505082e14090310013000c0224190381c103100707108000903003000948080c01480c040041e2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 836569541 1250 836568291 836568301
    0x4030b1e010602281403030103030f140306040e0a1202030c1c0e060a0c17030720190213180c120203031206131b0f08040f0230100506090f010509 64
    0x321690819800511500083c25040c5017600040013840c1242e001c1c1c2c452401e0108180420340b4403200c02400c20810b00000c10000300301d80383c184d00540141c0100012201096855034800314218280104071380941d00c04181521115010803a250f8018000300d4a285d08031110314002c1d01c0c804018001c1440f44402041c2221490320410312440c4541d0003142c24074445c4101004808280d00541e28100042c10803c3d00030300038040c90a10300803022042004107009d402035601c604000021321422070303000040d12280c004081c1c4a0041800d20202c00503c42250006c03403a18440815a5034062412585140002c0300540c1d0084140d03000c0350420390400c40300e40c1d111000140326103540311000408a01e8808101c00d44603200c950302071b114015480f0750848012520040d40d1b8003400711001080300ea01c465001c001414072085007644482c10031095030f42c042c0c940044c000d007800040d0713190803160b1200b2a180500c4006010781c5401c00c0068030190018200016803202c658414043c0700d00990303004001c21 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 836570791 1250 836569541 836569603
    0x80f0a0203070606180605010503191113080d080106021b010305100509070c0b060d0503220806090f01050114090a0b1203040605030402040f0209010c030813020604030b1e010602 78
    0xd002d20354400003c006540e1950241c1d500d120928081016140c41d1403004522940590203c1e80031b0030a10b080b051000c01070650f20005004200d2440300c44500c180081d50101c0f68125100c00034003018000b4182c1050850710040420005a01100440d8007040303c0e02a0030040b9112034040b82801c2c03030081025a03400719a58903813401a4411a040800c4500700f00030306510030042402548246861016501d07100204515402d0006003d041c0d60001c0002c5a10310003c0b008860318503281e0342130181c1007641c1e0004c030390030a10700f02d85c0075026812039680c080c3c1d440c00038400e09000d402040810318810800c7d0000c80d01e1900c005006150080d912660504079948002d002c0b4074289104044030ba0b12500d03800014486d0700203940480c02103040c40105010050741d4000d503019550103035203034454482c440e03c007100d0f400c0f80a0310704010b007000c00041e00c001d138480c0c10060002d180900d0f9031411508110410500351611403140728494000d501c0140980381e0701041505000c0e00c01300c070780100204000450 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 836572041 1250 836570791 836570797
    0x9060f04030e0a0b280203130b1b07030c0305010c050415080912031915140114040b030408070b06010c020112090515160f0f050405040507020a2f0607080f0a0203 71
    0x1c12008000f00c2c00304881c442d10030804024444409070030b403c0721240c06003031f0f90700d004404400f002c2c401c044405000c00a0f020010346004107000c03825020b20300505101ca03050000c2c0c1c0d042038654043c0c1c40410700901409000e02c802140e010303d8801c0c60310740340005413001001d0505000040000500110300c521204021a1006a00701c2c03165981c0c2e81440e004601e90015500c40d5040054140200320004110248000d01210881c00e1803800c1621010011940010b952051075030745c2105210210f10045500040c511803403040041e540e441c81c4500f055141410010007039410000741c212001e0050740d0101c1212241302080c000840c11038035030319092b810300440200b42180f000e400310401080e007240d04643c44d40f984d200d0321081404040440e00315414150314001c100469070402c000c101c54142540695400926841175070400e0f202c0e5911a8181203007400300f42c0781943d020452140903601c8144904501341e045408610b4002e01c1d0b82e9464050060018800c0e41c00c0c404902030501d40c1c000c0c421 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 836573291 1250 836572041 836572049
    0x12060103020d06090515041a040b01020f10020a11010506011409030a021210110a09270903090e06010f022d0a030309061d030d0507091d0f09060f04030e0a 68
    0x3e2100b19100c1c10500000e04044400c10035000038145030a4590829209610000010042c03d0000004031f0061101a0034803007040ca045100c0d100c0850b10f42e04083c00a40c07001c0300004005640d030032010400811104011106511591402c0140070032a030300002c5101c012480c801c4103c1d11b880344803000a09000c40ca00010b034000c240e03001180f03000100482e90b0f0b940e10041c0d41c01040003900030003682c10240a910000070101c1d4001100b03100c148005a80751213164155041440c1c9403924018070030a03030340c4241c0700300e0100c0c80c502c034188600d400c86440b460380010286014880c0308030311074009581d41d1021035181207a114550010b0783d0941b60608103042840400c003210385410940c030340200144060746058548501e88a042400200100700e0a0307290084030000b1414240881c20303100007401e0190065060104549001607074500141c980c9000000000e0700d2450b038034000d480304800042c000e100360300f80e4002a0030002000f41c80c00009400a802d40380070341441c202070000c240c4044845d08 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 836574541 1250 836573291 836573317
    0x405030a060e011508061f150309110402090114091c0f0b0a05040b0a02220902040303030e01110f1c09060501080d0206060a180b0402041205070b07081206010302 71
    0x12840c0107001040d00a0030340c1ca0020802008808822205140c070b4018070300940403140c10000108200c3e0706000030040756504d038019480180c6a98406422007140c1ea9210140426201c01d5001d062010702c1e59004c0c007003071041d074066150142c2040000c01d04610905846c440f160003042c001450b86a180e40381d00040d40d080c1d849104440305050880311244101011210701d01d02d50001340c032424250041c00d01966015480081e00d482d0700e2070220180d003002e4098425100040e810303440807500303110207034010171403100016601c40c01d50800a0969036808410050360303041111890401c80084100d07035820140c682c03159201c5040b030520321401c0010301e90103100035050442d030400f8801164080703412240f01d0011a0624aa080302c01c0e80c42e60011540e895020391001410400c0700300c00ca500340020043e03180000741541c5400005800c03030304103820801040590500e00400c00000704812400380c4030100342c99052407096a5803c14a00c9034040c00700e510a50400422000d9000c0d8044d100c898100070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 836575791 1250 836574541 836574553
    0x30c01020301091d070b04060f03090c0e190e0705060901090306020a08150d0b0601030e010b090405030406140408100b0406171513030905120304080303090609061605070b040602040503 81
    0x10004802500501d050700100d101c42103105900320f0320000d90b000441c0d5021b1591410a803902c501982c0c080d2051000400381a11142040e00141c0440f4880c0050600860000c0090a242003271541140d00d00c40380c1d8140c90702d04031540384130580003e800c02c1120710855003903a80e0690300004072010b400f41d6000030304d041e002081030710b0103640114406219074010207101100134014401c02006641000c0007800803c225004281d455100350080c1048000250000c50f0408840b0b02080f00c81804440684071600003181c1408115031010080f41c8103052000c0c8641024205903105c1d8076020005404a6141d030758190038010358803540c01c15801406120005004604001841510b850300911504030011404000504211818242d010074607015501c032a072407400c003018070900c0e00d40e01450003154482440f001860120810055100e4011180039064034100341441030701e0031030003400380c81110341104450803c8035800700075111406e421105525050303d03282043d800034413a54000b80d4040c000c007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 836577041 1250 836575791 836575799
    0x1104020c060702071a0a1b050f070306021305010206010803030f070216180f020a09030602030a021b0307060c020c0d030e0d121706040b0303071205091c11010926030c01020301 77
    0x11130360004903400c19801e1a982481c0101c00c649a2140314524070100340c21b90f0508511400c90410340501e80d1068084074a4400030101541c0341507042d5204a81140e0000b4894030540c0003050030400415080c00180402d505010380d25031030f40001800c4040c0c41c0d801c040010005403007009400301c0d2140210988280b11f40b1042d80c1502c0c0a00c4112000d400d40c1062101d1041420074801c40c1c1c000c040c103645408085095988400107948050001103651fa000e10004203003920b445601400d001c5c04a0003140d0300c00d1740345044415528070554034402c0d50440c24914502d500e42c24540c400d4642e1514114001011600c00209954040b15024120007001050086410f802c2459010744641f290710016071030b40d802e0104004d0301c0a0800b011b0b0190000d00030003000800a072801c200c603900900f080346c00c01e044d400104c2c254070310514840c0d02690b101d1420313500b17016a651900d188094286041c03025541020b4010462124616028903240001c03050a030000d501030043d1510542e50300000e5540c0d50351 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 836578291 1250 836577041 836577043
    0xa180e07020607020705060a0f09080d050403021815010f1e20010e0a0f0f1515080f0c0108070c0b0408041e0311010f1e391104020c060702 61
    0x400c40e100e40261003000c2c0455900e900008aa0f03003201c0004154920740036a111003240d500000700044010700484070008549007405010300e040040481e07840e19129442c5004029002d01d0500080a0b0280010180030001c040b18054034000242805c2c1000c40c54240d01d41140c818040e400d10b810602241076200049170341c001284500303a840060201000001815010f00300c61084442c100d01c1e031b200c0608040018204100000f0181c007801790350001055a8881032500b821507458440c685985548966030140c8103070040d005044c0c0340c401800305070100f29240d80d03550440c81080e070500003210001104107100700305020840345d02010346003603418035181001d0369420501410b5009a507400c181c0445040000c24201120b8208840044080c954001501d2009603400000f0401454184902d0105440b034802c42c007070111545c5102441c243d0904404501011340442c0021000041c110302102c02d0301c0d41c607003c0071600400c603046101c041d580001d009205115244540340200707420020880e030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 836579541 1250 836578291 836578319
    0xd14010e1b010207031211030f04091401140906210a121809020a0c060207030c1a0c37020f210d0b04061703040603060905090d050a18 59
    0x203161088400030950441205280401903a440b03006a1203a00d04202040100402c4080b44d4030714142088260b501c11040c0d821940880c4a0300b030140d100240402c43d00740c1300d00c21011620628014044554104015811710b41810a40786100b800e400001c6042c030760381c4611040810503d401c6502d6102c003080002c035107030310b41d801342a070f0b0050b4003001b503840070740c00b030301d189100e0f581900c04181312142040c07031000c000c0d04140d19800800181c00d20102c0040c0541c0b0080021a0090321070600807003452400c13a440d86044500e0400d210003000c00e1042c51011b401c2920704001000500c2d00e1589084854280d20700ca42c610000c102506006c1c00505080d008030342261500c000c0340130740d00140c0700555503000b0901200d04050500e1410002100024801c3d03200f10104007005002042440d521192a40002041e40300a54580c0002904118241d01489054000c100e0307a81c1c103115a00d0070a040c1074442034410111001d1040015804401e0b91040d02c10114860104039510031141c1c4401130a00964 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 836580791 1250 836579541 836579561
    0xa0f0e0406081e12030403080723030703060314010c050a03090f0c0e060102060c120609090a06110c0f010b0904030503060a1a03010302010e460806161115060d1401 72
    0x40204c8444800540c484400c99110f550142c0b0b501710503807183c0710300f01d0340c0e44480003034500320b441c0d00f045c100c600b090400300940c054846071703030041581421410040d08100c4040341e00821a850a00950290b80c2c03c2070603210456040d027000a0082000c1c10b00f420100707068540280001400350000c10100d0140b41180c4c0909001c0e0f08550031a518030006a1141c490010881d0014503820000713841b41ca0300300c40080d4450020420745640c0b5000d40d449000783c400080703004c10844000b040c4401c03242c004029120325400c01800902c000e841c6034000c2201c2e50009000a01080000000115281c82e20700b409001402c00a002404002c01004010034581081c0422800581036086004803490005101c40c203031084219801c11240c0e141414200121804540600013081c030320951640015109440300103221140151541c0e29112285820809a880244050007154003000c240340000144d40700803900d01d02c60300842134442d000081d410200c81170000b00200001017600f000c0702c0c010740094042c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 836582041 1250 836580791 836580793
    0x15060f0a110303010b040b0906040b0310061b02060d0f0b0d050d141206040902030c03030c0f0f0706080a0c023d0c0c020409020612101503020a0f0e0406081e 69
    0x12051501d4100d44912080c0308200c011803041c0401c1c41320032070600081c20443c2d80101020f18050f070742d040c0d200940c0c00031183d00302150060201049040d4214010484543c00f080411504003503d9001070580c1c01036042d0640c089640c0c00f80c2d600840115849409602c034000d0400c40031400c00c1c50401e9490712705074048400580c4042e140400e0005201c10345644900800040282e6524039080c00b0042010b01030580e810f10401d0440850783d2800e000401482c20001e0103004c2c0864850151890802000d500200703560049008011403039010704442e80102c8100c0003ca51601218012860003007944041e44040307404451814001c08400801031403014040d4103030342001c50140b8008121004103003003c01040c0c4044809005190a51041064a200500c45801c082c00030a003070b01074090840b01810f11388140c1d0000d04c14500301483d00c580000709840c095281c01c48901c1c0c010706200080450324107101004203840c001e680d49402640141c03100c04200c0d1100c1c1407034081d90214080c410303003510603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 836583291 1250 836582041 836582057
    0xf0c0a080403141c0f0c0201030902091005150901020a1b030203060703020307020d0c080f1605011a0910061e1112190234080d0c03030c030506100815060f0a 69
    0xa001c00c00807081021000b145c030703000c0c03c00805590035985640c0004c0202c0c105035584400c070b00141d45440e1800c0c0110f200e40b007455026401c010922025403a0030300f4006880c5000c0c082c034000707030f80d000915085150f4098a02c00d0344003007034030403240c00740071f1a04000d500d800f59004000304aa0b1650281d885684564200d800c040020041601e841c05201d0020308036250820060761044600c400400103000d82c2d0f041d145a80550b0385455084900030101803940707284d401d41d444110304d4480061900703c0741803032150798581d250a1000e07124003640b280314006680e003c3c24003900326000d0110340e101402c030b000c1514203840c13442145132039660108460103c90101c100341e0444603440050340f01c1c8811280ca00c2c24900f2116041c1d603075400000d01c90500841e009400e00882c0c071700400d000e4204040d000e078540c4a0500078510b8041c05507243c01c5d02d03810030545010b00f0083c155132800d54000010710075040943d2140c5070340043c180c0d600c22503201c29400910008920070301190240080255003016514101 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 836584541 1250 836583291 836583313
    0x10050d031103030718120f060218060f0306030c120604060b0d140d02070801140c0d02040b040608040b01091802010f0219150e0c060a1404050901090e010e0d050f0c0a08040314 77
    0x4006c03151000609031415418031240098038503401400c0301c01321041000b82c50410040011510351268a0328054140044140201d0307083c1041111490b44044a0401c600307080030110340c0d99038000a001903d11600d8180140991700d034106118622504583d0f1207640505213280540c0da8442c81c8880300040c804c440300010200410b100b0350318143d40c0c003c4240400c1c1c941802003001e0b03801c080300e8486540e40c02c0100242b6210940000c1005182544541300546041e061021100e14140c0c450182d03a07050906000c100c49250303e80d15085035090820022001c00102c040f840c0c160350494141078892003516020a00c00b0811421500004200c000e2090358145000640c903440440c1d407a0703801890074000c00d01140e000f80c0740d03030610a0a400401e41810b07038840014040900c01e03401081d50980c1c075001e00588200a01407601544004c0300105403510b2080e40080c024401c1402490314000c0220343d050391203100341321007020103410001140e2140d4403410070384490f400c40d003207614240c070515002403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 836585791 1250 836584541 836584559
    0x210d02210106050c0c040b1c05060714040e0406090606081e010f2307050c1207050d02060115030902030a05060901020c0706020f0607050d1d010b1810050d031103030718 74
    0x14955400c1c5038054507030050005d0900c4090300e400e0400342d520040c09610701c100034400151a0464030f020700c0060071142000a80030f072941c05004949051824100400d104210641000f503400c00c1e88014000b0f0402134a0030003000902c25900842041d02a03040c1201c00746038211811051982000020001405441015000c0341c0074800a08a00007441041d0013042c06801c8445a100345603080040c035110401c003406081c441c144111421240d004174142e018014104140340e43c020700d900051240d0750400c41e0034807050b1544203203842016182e00100046480c14042d003050313194403000b102c0150620301c800c2c40c080c0d00303d0b40200c1070381c0c0b0594030009130b41c41c4006001d01d408a15240a044642c031410700894403507200c002c10040c05901d580101e46510b21080031128041001c00000a082140700100b29401601c540c1c0106105070001c24070032050140003126003180e84c1244c820001201e2440d0039940c1c3d000b443c030b025905020100811440680000008180c15161503403a40e10035200c5400c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 836587041 1250 836585791 836585797
    0x7031403070213151409070f1710140405240102120f03041106070308010e06010c02190602071e1206060806040b222001180303021b030303040203210d0221010605 71
    0x86a40f06c200074000c40e611601654240d40340d078040e8900707181c003004841c0082c4034040c4c003964103646242d40003c1c100b1185d91000c81c060360f002e00840e01444035003026028000a40d09a0301d02818000945d84100d030107a0003040302c0310300c02c4001d0f085552940804500b80100f5013040ba03007030300c0c103580c1007011b1881ca142040460b408079078180c54680c02d990801e4254901074500416148c14008444640e02c0565100240101c14020751000400c016003020300081c280801a40000c44c0d072401941d2208041ca491401241914405460300c4841e42d0242058005884030341e1101034540101d8040c0000d00c208510004d128400d4100302d40f2980b0400e941c0034101041c41103011341891003c2104084803040003080e22a9070300145405151301c880307540040304181c2261b0085015a01c00c2c3da0295444040b4021402c81c502e0840155003549000d0300840d8a0f02000341044a89000c207884100001da405015616040e00410045480c3c0440d1404039045581ea0001f4900841000000160003449a011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 836588291 1250 836587041 836587079
    0x50a060e0f0415030803340e0f010e01050c01021207080a0c08010f23060307030f0506030604032007080304060306030614040c05150d15060807110703140307021315 72
    0x8048034a96200d8845c46d07000948140c0e0f290b000030004011a0807244185000c0700343ca1001f0710402c00d82d17607101805140400f003625005821642d04401030b6038008a41c0e0012103030a08045540c1e061420b42d0600a00c1034110541d8414610380030b000c00c0309d5001d116684541c40b5214100145051a0415690480240700e00010041070800603c07409d0038078071100910019401000340b4402c1020b001a03020b40088582c2c4001039903c413584001004513009843e00490141e016005504003600c0061580f03c1400d0341c0e00c501404080340d05103c10081200c0c80040088105880d00d407074944038024054900e5110039182c0038244010440e11040414a0a00a0381d02044400d890380c5410207110b0303408030502d410700603d20280031282510845009508184143d501c8980700281804000362041c0406410007081182c2428410010580000c101c81a45d400c080f10309003020b22a60581c0c034601c941200203400042c103140440c4407000340d4020060805e0816514500140c6403181c0104001c41644 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 836589541 1250 836588291 836588321
    0xa0903090e160c05210a1407230a05010501030b1006020c0109060e1210061e061205040c0b070f03030f1505130b0616020906040c020a120207050a060e0f04 68
    0x71080380c50b1070291400110607889481513900314203500c44000c0d000c000521590021040c0020f031031003201e6004c03031a0004409010311850074000241c440c0003025150b40442001000e805a088985000810581b43c0b4141d01800a1001c1e68491411650b440400e035428100c000108a020412500106900c030303441d481030790742c40002032503d0801c90308003400741400c0350000c420b541658600130060061800c05907100b50301084c40e61409050000b0344901780020301004e03145400c18041e480e032020f508034400810f50808129074035281014002c048499000d2420501c00041240410611141e0307111420700a440c10030207100307014502c4d400d030790312101c00c501d0301d4100560612061415a5044280c24010131000034041d9449020404582c048080002644220441d036001c5151040015500950580b8144007a050510b0040d641e805070310001082410f8025011880c107100b00000b10007132070010442d1000700c0d41c810010f04016640320805010300f03e4421941d6450030a40944114116000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 836590791 1250 836589541 836589571
    0x40509150d02010c0c090c180f08060f0c360103060f0608090c03060c0c190309030f1110030b0111030901140a1412070e040b0609060d11030a0903090e 66
    0x2c0c0c011181d000100030221003c07458020086682c500c00e01c0780200c0c1d840c0b01d4a030100250741c0743c0420b00da04015540030310054481d622041c0041040451066009090700848d1055521500d4150301e403401094494805000304081d074880c181140d0402d007105c4401d00e0504180681440c004406649042c09240074211707010008200c400e101d483c80c140e0104d00082601c110081c43c40029003844002e581c01d0b054250042808821001c1c03c0c01801d0a5010ba442e13100021941c669004d405080d081c030024110070251900c00042c032070901d0400c003098900030669082c62180e800c01800030124400307a18000742c0480101101e960000003291400700b4143c440c58001c91402171242d5907540051040000c0240602c50b1590340c0100e0b1010703007415408562040183c0c602454014100703911303084c1c090710980c00c2041c0740c901c680b503042c00c441c0041d0044c5d903201c1d52501c0802024003e007d0007802190310440c004201314600c2035581c08110701ca03100e90b991480d900d54a105081004c0e00075134424204030200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 836592041 1250 836590791 836590793
    0x30f050906130507171e0f06010b09040902030d11010c020a2001140301030b150618010807031509020301060809060403050301050906011b110a0918110f100302040509150d 75
    0x68180c582429208108035810b080e140c2101510f45e03801080d240c00903601442ca80f0082070040341488602c40b0340c000040000c00401c4c8070031a61140e040c45103d040380400130740268241ca464101170800ba40103011140e08000b00d942c0141120610040d10951354a89400a000d052000c11404034044d045102c0c03144114164210641500003249198140807841d8a10648003040401544c021030141d82c6082c0c0920b010000305070f8201e21880b1070b612858003040310300011911072200342000f64080c80c186010740d0354110140e004001600c2650980785800500188001c40c6800031810303101180d5602840380c403400aa280d0f201c1050b0380080108200b800103105904054075a02e83c481414584860002c110b100510403643c500503050381c4040c0c01c0c40c0320700228202410120002c21a541e006c0041030781c0001d40c0e1111030306101000706000b03890980d403015556041c070b007243c000c440205044080036079108080c0095019229440c02440140001484000034181041c0e910801400300841601c030b07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 836593291 1250 836592041 836592061
    0x20324040608060109150f06031a010e091906050301022b0203071d0a320a050109090e0102131514040b12280e1501030c1e0b0f0703030f050906 63
    0x11b001c2001a2480e0080004407507449429110040c101a200000c40c1840300e851400d0302c1c4101c0c13002c6810303c42c3d0601c9040c0e4030344440e4101c1c2c1e88090390f0f204c407944048041691601810895020a074558008a000e414020380d907400d000c5482c07003039201c904206024181d108181c2c04100c80d1003002c611754102000a90340d0020011005a00041c040005a911000141d100c4034a440740b03501000e00111002035082c42d1903881e003e00072011144a80c140f440e1100003409444c1178001c4200550310344240e86070450094041d00d10351003103014000c0d56aa11500710203240c4c04101503030f000050103201e152064041d02004c603020703542058659490700050b11400c0200d500081c00200404100e410803000c40000008240b010580010340170600203030b01c1100b18504000400103560307400d070b071100410008640d40806021208950306940c01140c14081c00b940080302640a41466040001c0d15071071141a640140196071198408021403c0f55507501400c61704211451f00080c0d20103c00f003a410303c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 836594541 1250 836593291 836593301
    0xf050405090d0923031002040510090509060103091703040f15091203051905010b03091b091b0c01050a02040f0b1c0b0604030602043302070302060a09030501020324040608060109 78
    0xc00341e1220204d280d60000428502511a03190102c0e96074041401d105600e030014040529150924044103524188400078040311350140c01d40d41072540c0c1d010074404202c480c56280e04203100c125203282c0c89207040d041c601c16036542140c00b00c46103407103903560b1034041da15031040f0400e05410010380c800601c641d103070950003803201800c0a0001d44150303c1c2481000c991b40182c034042e201d0381c09101d0b2203040901c0d00c1c61a0031401109044403031040440510300c1e454542c81154042c1c01100761031031088100030302c64424820001a810254200420004030048640042088401d0080d4140500e9a1882800458041c07088014010710031911090382078001c80d000340072041c40c010314080c680ba580e6501c80d81240d0142d07200315860000000058001c403900d010280c85072032031a11210f42880c8c0032000a450b8085404020320842c07000c55981e0340e4500c20550701d00607643c07201c021952401c184002c2c0648552103120083c0140c4544000c0c030b107070b041c01d000e02401c646100f401070a050342042100c0c00904 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 836595791 1250 836594541 836594579
    0x15090907051c141605180609030a050a020f010e09040b0604110403150b0604081203223917190c0609230105030901150f050405090d09 59
    0x400d09208a408100c4650000b6100c41c0c504103000521941c3c00760001e00e4000000e05401e2400d52020b03500c0d84880e042011212043d000075032042c10500694005101d40c09883c481c15094803c00d014101007010005210003da4002c50740d040c00b928024004450b209501c42c0305036000350440700030500040703007040010b07001700000b030006c211141f20b502000300b03036081540b0984100c5080300c3c2641068003203200b149005042512107911785801e04080d269180024070040120210010005541c09102d2410b0001d010749112152814005810484509112090b50b9110403440001e00d8890b00ca0040f002400b1269100e144245146041d01c2c054030440003600903e614094002d11280c1c480540d0051a10240300d8641903c010381031010007841c000c640d4208124064000300400c404051110640b080790009281c05941d030368540e44100c3c050662050802c0c1190020100841c3c01c1202d00c0080040d40d105803020071150740c42602c00c035903030300c0c01c060494045611080d081c0307e02c00d900c03145920f8107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 836597041 1250 836595791 836595797
    0x72a0e01061e021e031b0a08040b0313061d0f060601020d1b0c03080a1404030203030f0a1b05031c06030f02010e0312031f090b010819060506030a0902090615090907 72
    0x24180c8040c21301e10801303800c1d2100d0016080004c100d038402d402403203032400919410000b000d500d4465601c0e11100d102c3c1e806031029488012000840031074040c6e013603420f515444201072156103400e1001004808000011505a004034501803006500024240d841614141c0c0208104400880c099904411071380d40e05c001501071001d014040707203050790898021442a007a00307560b244480c1004007181c04c5513003d030615003002c006c10009640d000003600c0c07051401403546aa15195128142c5e0f610041c20381d030204100c8490600d80a11101001800d407540792000f1884800d504100c290086030024007004000070160b481c02805544289900340350090040c00301c900c11000d0080e0b03468182c01c2105c100307072001442001d00c0c0901202c42c1212000f424444000d2040041e50400a05141001003591060303248092101d24861001d030412002040c010300001c0d82ca00700407000300f010309a410016409010f01d040070614904050f101040716049031f2113440d0a20490300100000350b40003508a03420 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 836598291 1250 836597041 836597053
    0x90307050301090f0302010b0306161416050c01021902060d1a06070c03110117070f03021b0303271b0a0f080c030d0e24072a0e01061e02 60
    0x75203003482520b2000380a19012031041020b0301e0000c1c29140f5041005010343c10401c00d00072402071181010390031100500744070b001e00d07908a41c0300440740542080c3c20141910300002500b4844045080c12015034280c2c02c2da00443c901844c1e6803281603005c0b00c000c0d04450104070084600502c5d50000f00000300e6401160f08402c0c58000044090f0001c9400b66044d52a00b641001013041503500c4016855081c02c00e40030110b0110851020214020002818025600024040309100354125200406031031841c030406a90307885481e83d80e420440b00c010a61502d51800e0034809080c1e840d4a02e185100c000401005408143c045507414540c1141a00300c0340585000c5403c0401c10780320320107080310500034240d81c00130104240c07800d09605609000d100395185502141d480c0c200458912446416020303840d0411a180e2120340d11502101819600f8511002c160045440c0125130400c2e43c00325101490b00c0c0c42d030209042940c028400c1c1c00101d02116a1014001441c1c54025039590490051b220 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 836599541 1250 836598291 836598299
    0x3081005090f01090c0309020d0204050403020c03060c130503030c031e07050a030c02010e01030b010f18080613050d05030709050d05160b03100609030c0e041509050114011509030602090307 83
    0x1000c0381c0142c8148074503910240060144109622401806102c40e1038148030800303e03500411000f07403002e5806030159494400007405c2c18000c001e030f898001c1020302100c01034036091164880316003107460b140800500004e40003d440c80c0000540e010555034001a6180040e40f011164500c1c0d84500d01030b140e00010301c0a000458070902a551441d4043d8a88060071002031000410f620b500040c29414103180c42030341d002c9640d001c083e00040c1d00c0c481c00c00c0b15000681c00070000b5410300035444102e4501ca0081000003085004003050141d0780308600b200c8104140500542d118041120b1220015194a0f001c010034a03002200d184403502030810b4503003400015242110300c00d907a4000310620540041030000306040da50181c1e00520542c50625a1941181e40b540c040640c107125100c00f007a4410040350602080c450311104181080404000c86442458a980030303008052420f402602d414000013880300c2d0100d02041f03581a00c1e503d801c2102c2c20350703451800035000f01f0340150f014030038100d02107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 836600791 1250 836599541 836599549
    0x141003051b0706061508040c060e040905010207050d0f090608160903051c14090906041104080601080c1e01081b090a0905040204061502030304082223120a03081005 72
    0x100341a4000c90010841e6400c200c92030003445c0e1a03107801c02c2048070341d50400006c110140b498000f03940c081c0c034248200c00e002c00c0000d0701400c1c400002078141c0d440020341e82d0030000002500b03284141140ca8035852640040c20660700b690861240001045c0c44130300003400d05110340242010f0404070b080041405072251681d03894160003840c0294100c6008241c0f840f036070b0f00010188004205107070120324001c0c2e1080400ca03600c0c030152801d03010f59260540c01d04090003d2041c0d5001d4083d95040390050342e17640d100f042d62141018041c0d80541e00c100392045403161100c52074000c645060315040800c2d1681c01030105025401200058850401d00171488259140980400203001400e800310b80380c242801000b086500c503030310900300741460120881005801205aa501a8110381200d80f2f8003a182c40c2c90f40400303a801140d920114101e007011a644d00e9134110b5200c0c1108a03045000a500000c0910000401204402410391704ca9900710002911404640d588171141000300002542e50340081 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 836602041 1250 836600791 836600797
    0xf1d031603030e040f0b151b032d0310031209030b0a02280207051c0204020d0507080a0b030c060a17040f03081e04080a110604060510141003051b 64
    0x80b00018100e0100050510301801110109203484a0400507030701d6160001f8801c81c02186a0b0096400c08200e401207a899141c94a18813140e0000b40c0341d6038030101a400060a503001e5082c40c0e07021081c81c80220301c1000f40180d920540c045100ca40c40d06003582c51304202c612903a00031104100ca00c15010002461203103c0c903024000c11440581c988040e418201001c0554460880c98a06410326000319284e0008500d01100c0c002e9070341c03014010050300c041c0160705400d81c000e500a80001103a540384401648071078855144c946c0e950380e0a89404084105540ca01c4840395419445080354200900d400b00043c035492205040c0100c1f100c02d03505100611010440d0103543d0380d03082808480c02d154022000e19880800d20740c40e000c81003203180c5605480840500090312441002c0b4200d40e4550003860311078070000a110407076980345810710700352025101c200d4215031800f4044400044021940020414851700108000d4151100390821001002c00510004144ea180e129020901ca110401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 836603291 1250 836602041 836602043
    0xa030e0307020a260f0c040e07080604080403060b0402091509040f320903040303050f040b031005040b0d02031002090f1302040603060b03220201180e01150f1d031603 73
    0x12000c0d15550384c070000300340b200c02c1c1e611800103420615a1540c82800400e003190409130071580040d070036101d05083c1c3d260690701c1d04030408512400027807201380003c00f0040c00441b80318410600448158005001c144d00400c0c5505402c4400710030b030b03081c01940a801420401c94080d000080c09280c0c5045a004d0704d0f080090000d92a80c42207070300c1820300309282c480105018000c910078450809407245582c0348282e21000d000c00002040828072030344102c0481e801010000302154413420840404620900389104462280c0e01d490340f500300b10305210f05200700c20b640040140c00f501441e00e50050180d4044103034075501101d50500014903a4540d0f040c11a101004400180c5560800d880a400c42d01141c000c0340c0b05000900c01c0111031b501d80120440ca0034400001e807a03183c2941d20060718400c184061501c03820f000c1c03080215003031403001c4025040ba0180380b2810a440c00345001560300b0202114204001101111410045508054140003564018088401c00890800998564001504 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 836604541 1250 836603291 836603309
    0x100e0f1203070602120708010302030616050f04080105090d0801080c0f03070f120605060409020906190b0a020a060b0d0b0c0a02190311010518100c05041d070f0309080a030e0307020a 80
    0x106440c1030300042c5c914135032294482c2000c040a50460b000a42e803482c0003484420351b103906042d50380803c0c1c071038000d03124200300440c0480d8955484581031030282400301c0700150a40320707182c15642c03030318441c0034064126903904002c0d00b04115018280848481260a184e030148a00c500005150700d4001044005001071110650300d0a102e103418801ea60018146620880c1082062001341c0c0d1840355903034100c0012140401c203442d160ba03075040c4003100c03984025039003440400e002442a070041107800203544070b0b081c00c101e0801490208a003088000130040c007032414500020700c19944042c0200300900031801150038007960320303031141c0b01c4050241c4100d0009040711441c080b2403009008540d00704030a0b2049928020703400100a940311a503820303007082140c9a03502203003090b001c0c8045a0281a11200101900140f002050705540d400e4441c20700060440c01504071442c4240f24135415590b00064040c03401e5641c9100710050000343c0721046032070004200c0c210050b916042d00704010b0052007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 836605791 1250 836604541 836604547
    0x4080303010905010303110307020319060b0307080304050109091a22150e0c0703021b01090e010e070e0a0311010c06060b07050604020906040b0d060e12070302011a100e0f1203070602 80
    0x1ca0001c02d000640d07e8041c401c2da0040c0110300c010307a00854000d102c0c455052003980900250308080000d01041c030700c00c0d40c250003031800200b100b4070301100500507104280c0311440303881c4d41c4074252801c81c4c5c07124410a0840c00e114580c001c85c0c4c605090b08801c203a044405440752004174840c1f0000310b50000c0210b0403640d4060404100c00043e040c5440c1d0f000140c906000d08060f401d48020391038030f54060051503030050030101c0c1c1c0341c980c1c002e000100281207115020901980c440003c44406001500d011010906141684c1c00503d09014040e060f02e034001c60b581d040030a44c0380152504800d40c0005c64907191525004604e0f581080003824002d0701030401010f240c1828014020b0b03000700a0728160240382031005080040e268040d843c1c81c181c1d8021000550344074030440e140e00380950441112800200001e8103030a0503415000560482492110003c2c40400c05041100a000705007e17000401c00407a090500c41c6009241141d1405025100c4010028156440307400c591203c00215842c82d808 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 836607041 1250 836605791 836605793
    0x904050703050712030e01050309031c1b02060f1003030f0c05070e0903070b010623091c0302100e0313090e010e241b120411090f0618070f0c020303040803030109050103 74
    0x400f10044a080d000e00700a481d50403c0006940c03284181d4030142c82c1c070001c0300b4108500403a2940300e0034002100c01d1032403107650013007400291207010036110b4a0719842d01744301081203401c0c5050074004503649621132511411a040c3c064030315001c0701c101a01e8a01601e00300042004144d02e11074801e0b03540d04080d694441c9203181009566206810007400c0001c0d91203025040c0074580a000c0c010a5102079040e1920900000198070321030a242d0460f481e003070180c80008140d000a01612060000362090040c0003481440300d81d01d0103024040108200d80410400c00341101c0c1e8400c07064016464004102c00580503071203444c18904c04150400d0810745540030301551481c501e550b4010005800c60004180750440f881d046005400d10050b00712a040007081c108046078455a10900d8082e208204914000f0f00310a0064811a40d81d409143c80800600b8500300b14030f04e06100e00102d4607001030f104440d51b0100c1c4d8440c0721100480e00b501c020003003c40d071102c082011750700030718221202142c0c5d907045d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 836608291 1250 836607041 836607047
    0x6040b1003120f02060a0e0d050d02090414010f14030a0b0901180308071106160f021513060606021f0b0111031306031d0d1d0603070f0f0c11090405070305071203 71
    0x18003103c025440c0003800d581f070b80d00200750303924507056502e0103a488610080e0311300000d1180d030710842d50161500e01401d43e00440714416a040380d181c0584507c21641c0e60241044014401040d15415001159030f200000c4c03481d62101e03084010174000066210310b9031080c481d410200d00c3c0541c0841c82041c20048203683c8030070115001114540544000c0c10581350484085064142003014002c8501d0380c030051620030420500956041c070500d41090404500041760601040e9080d1606030030404003281160000034956050841c4685050820b1140d0302d01c4001822000c0945040080f50303840c205201d001000549420301412415166051030b141010f800c6449010000307100c01c42030340b81804c6203000450000e8818495023000402014404419000601c607508050b40c002d4020040c0040598898940d0300c03480c0c03803911260100034400704180d40000303041d04000d06582495074841c8040c1070090803590082c6c41071080b41d456940b260f443c141885016007140b024041c20090480c00d00d54 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 836609541 1250 836608291 836608303
    0x804060f06031502030a020c030f0a081501080f09011b0e0a050d0c0605090a03020406080a02090604020f0a0c0f050105071119030e0405060f130b040b100206040b1003120f02 76
    0x640e500e0100714151655840041d07070542c400752442015400710000b010542940c04450002001700705076541d0b0940d483c0ca240f007903005111068001a0302d0b80000c1d010f423030456000720907050140c46044469981d00050310a0403001408504c25548480c443c0f110328007402024a100a01619801007d845407010311007404610343c000c9100e501420900307000710300078900b04400d880d190710702266078108500110350f0341000e50b800203401514000f030010762200f02081c08541207200b152004601e8a070303103080000382cec0079800c58910390b030780c04014106025004942d4507540f00c0c0b03e608c544845001d83d40316542101e60440d1440701003181f029448154440a00c410180f005c0c02c12440448480281c0300108000a0210428051561070000c10126900e240800902e81d0000f00011481810383c64200c000e48290190ba0b03002d41e040021b01901490140024001040c1d00e60040640390b44540b03600e0605000607115003070b88800c411000c00801c8544140344681c0c912620350010070f14624400a00d412 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 836610791 1250 836609541 836609561
    0xe01140a0f0605061b120721110307150513030909090606050a08011401150905041a10120c020102070503030c1c0e0307141912170a06030507121a190c080406 69
    0x10340700b04503002c00154003400c01c080c8181352040107074410420700230540b11000c041002c80118070021406c2401c02c82c010f03141200d50b40c80c00d00140a00d0301c03041d09113008154100001000324990080520420400c1d41c45102a00d018520200c0d0381d5131303242d02041e42c030600c43d040030640e80d44401d90540c4482400e04e050b801000c0d40c1ca821082d1014150700102507110900440d441151100036402d0041c0c4030641c4495803c0c0003e00c0d41d15140280000503150401e08021121030500b4451030890040c0188251034600360440051443c42d5549413141403541d01143c181007aa401c0004070b800da6451903c15144248e007031200a540d00c645a050020354008000131085090f44450302c0b06040c04034925034030101a9011510b086a6440840e05480d881e4094501c00800719000c2e0401071194826001541182e000f801a40c032055242c100d4044800c80c0c400000d0641004008000c40c4414600b404076441403000203200445210300c0607080907070b00d02d200b00f03800080b511414003050210b01d2040e825a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 836612041 1250 836610791 836610823
    0x20c030909060d082d0c150112051b040e1b040506040204081507031b091d1e060102010609060605030a05090f101119050d0e01140a0f0605061b 63
    0x48442d603943d07000d0b01c0c46082c42c0955241d09400700440783d4000c880d10b540c17810540d84251510b440f580143c895642018407010020722455000016080740ca0a441014007a00007019082040d8480c1511203035194442070203421503030741c0e48040901c610500051074503a06c1c0b00000d003402d09200c0204000d50310050400c611440c410081007010300d4000a010764003400000aa06099840140c20390043c1441d140c00441542c50040b410019540301c070460003541c00d099000402c4d101d4400d84002d10810032582d103002c05941004000340b030442c85100c2d0307a205034144004180ca54890704510262005984001c011860100034480084828002c0b1513001e1407140c0103100c41c068000000740c2c0d0f41861000e0019590b03441007001c0421480400701e035222130000e9860140c07150451343c018041e80c48442001c035650720340003880b0104403060140b0000ca500d02850903a550b100d240034000100040300c09611b005580344800682074603040090250351640c0c1c200000003240820303040741002d045d100c41400d1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 836613291 1250 836612041 836612059
    0x5211504140606061c090203072312060606090d080409090b0105010e030a052e0c0908060906010f030b0601030912020714010908030304030315170109110f0a05011d04020c03090906 79
    0x580501745e41d1081c40c458a007a0125041c0c0950000c2402c0950682200c12840d0f980c45401c500203080503480f40c081401592013001054203a14019240c1030103a8000740d110100300403691203031030414250030925024241803407800d036a44504104442414a04071108403c20004100075070b0010940300080009401070040c0a140795034158950301d034480146564440d100000c030485242002e90501e03503c410000b000401c0c10302001800d807182e140f14086451242c0000104828001b0030100e04950f41c2d1070280d20b0b0603003503075520242ca003801000c41e410150784451100118402960017441c102c16600030740040390900403104d04104e21007030200c0c18403810b0388040040280001c2140d52203505840c0000300680d0030074103200814110ba00c0a217001e00300d0103100e4403814065015001c40d0348146110f007440c42210091184640c0c4003020180c1c491400c6004110550050446612410154945800c40728070180001c0c01c0740c000e108000450741c008a0352420030300f072003c071035a000b001c01c482c0041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 836614541 1250 836613291 836613307
    0x161704121706180903090d140705060717030604090f0c1511210403240b090f06040902030f0d020c0306011d0a0213090c03020702040f0203010521150414060606 70
    0x26a88401c0c49000e1210982c01c0000c1d8004c00c00f401a142182c8009250500540160400c44501c42074541d60501c140145e51740050f5030702e003020460b10500e03072018540c0c1d4461400000f41d46503400060071607400a4503006c0e9440003480c0c0242140320684075590050816040c105159412044900c1c000203001c1070100c0d900380e4500c0003520048038202c29070741d122819002d8080c11031a004680c8010000b0900203140000c1002621400c044e031405180b081011141060410039299003c0e10700c01260745d10314011440c7c03824030350454401e25001070204c1da19001d44d2221245030200008829005811806d2003403007604d424041c0c207006052010070704440c040f480e0b181d0b5104c0240a05404541a80003601d2542040200c41c800000c2120f41005c001015100c400600a03500c480c20417440f4501d041c504001d419000e20a8034142d030b40c0603103030b0f00c007031344482d0284440414030854105e61880745030008441080380144040c821403054048005043d1803040061602d040900002e00c16001072203528 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 836615791 1250 836614541 836614549
    0x60509030a091a04050402040b041a07120e040e061611010506100804030215010b36010e06070f05251d0a14041412030f161704121706 59
    0x2030a5991074006605021043d00054106204650005400900202d070005141e00043c020f841181e005403140003214040b1110407401d07224256000341b440c03071801c4201c0c0810b40b0408944650f00000f40002800c048949001d40c58203400707c0d1a0b05440a0148040c480c141e0f108107020082c403900002804981416030002c0d040340d0b011444101000b6200340010203161003000700c8203450580c07800405113561100346004403a03004000303400f51040e41d000711070045540004070a581000414200000d005084011218040e82c0d4000075807120003030040700082200c40224030030141c450002030400f0751401c0e10101000c00010404212220012010001c43c04033320107044400f0310240d2a0b01490341d80c400464000d184410000f003a4440150802c01003080e20140380e00c2c0c25158000b22000600201c92860b01440704850000300301c108400031401c100c6443c00580c81d01c0200d8103107000c0c0c000e50008154a03095084400b500c1403844202d120080642041142c1035035051107400b8121880c2c940007203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 836617041 1250 836615791 836615807
    0xc141c05031e090319090302010f05130501080a09050303011404060e011401080a0e0109260c1c03090515100f030b060108070207170304081513061e090609060509030a 73
    0x2c6550340c408800150010100f4400c6030f10140504018507844100c1500041800c4d45c640002ca002c141520003010f0301c0e81c01582030319561403142c6404001107040100441d00c80502030150310015407940c081100040040c4040c5002c1c01c0350040d040d09000e8190100001d44a60782c5c0718052001c0c2103401800b81d56241c2d044c2071520034080c00d148015480749030201004181c2c06244210715480c00c40007400304513500d0421180c07445180e1a518244500080f07101562007600400960340d4003904007606505c44e4001078500c13480503401c00280130030a40d2601c034242100210b1340818807500300104849101c40c10894800740024146030445103045030789003045171038050300d91410300203007a002500c168400c000c1c14000c1c0944402c040000c580804600e540c0760410301581e01a40980403c0002c244030b40780e6124404e001c1c1a1a046914a094480c00002c11007504039044402c00c0d211b00b9819000036008010043c0d02c250f100007003030544c80c10614210342003d484044a41c000300101c00b2620ba024140c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 836618291 1250 836617041 836617081
    0x11a03061302010207232d01020115350607090902190c110a080d1211270402031006030c09030c1814040b090d0908100c0c141c0503 58
    0x124104042008210f8881c00844403a4014400484001021f02c20004546180b41e90704d0100b1104075201c1c0164241c0d2203040c4120310120400008010710b000280d6403281d9400e8200000c40c980c103203c800304c205640e1015002c00164080b1040c41481540502d644006108d200b030110306000100e008101e125001d584d0729020450010040b10610010210090360142c3c0141801040c1d6590402c082d1034010b04070340c2c0c4022800c0b0304503003400890180125074403044024001d902d40054240cbc0c1881d130010301b00d0740b110f504801d00901203064071a0720003507010784c0c242c803034900c500c034070f03103500182a2080115080208808a2400c10000d072000c2042c00556455840b101e4442d076410740842c00900300c000303543c0a8102c0500a00042c400d00345292401506054103813902220070030000e681140c01d41c4141145940422100c400307030405640039204001651802c1200145652a401c0443c40c40e1a41440c8580008440d2282d0302c001d0f00c0170001203031050508605601d4882c201c1c0c00751412000c0d0f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 836619541 1250 836618291 836618309
    0x6090307150506012601140607020913150603051e030c070504020d020c0118021009180903141201090501060f051204050102121906090506030c21011a03061302010207 73
    0x200d103c503070003040c100b1012141c5280c01110701044800001c3c00000a02c01c00d0164030040426906508100040743c02c819005010043e0700d0700c941c000c072800b02151050640e590360458880520301400d90017054004d502901c0104680304254060008503140b0f940081ca0b00e40c000c0201100c4070202003107050842e801103800585509400302103401a200d41c0e00c443c0ca480d440c040040304a104800100302001c0e0080c0c0741c10a18054080781a80c0410a44c010245402c2903001441e0803605940c1242d50510b2092505403a4000c0b4920740c240c036904101c00c082800d151500051080e01e03000d1044d13500604192400004003aa0080050700900c00e095036550b00109820001c4c0600c4800d404440f0b05811601c2d01e601f01e0b103080082e000740c582004440611300c070704080000451290501481e401004028082e00b514103030501080070000c5105003948500700007405410580a0038460b5023030441254943c4003018034070004050038008002c141d070001700000441c650160740d00150381070545644007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 836620791 1250 836619541 836619551
    0x8010e18070b0f0d0b0102031606091e060b0f15040b0c0c0603041202060912040e0a110a030222060c080a1e050a03180b06130902130b030609030715 65
    0x141015041000640201100b103000103492407418145070003c0844401d1303410b04001400c921801240c891050401c09800e0043c59050308010407055801160304038800d030a40c442a602243e0076440c0c002c41000e09a800a540350104485410498064943d80404590040d02c1d54080c4103604041d02503405501c40c01079001c25401c4d00c0786410080c3c0c544a02c40100078940341e203482c2c604056522040c450503001801500c0201e00d0461000801d03e80d03100044e0b0541d0b003400c0c1004e00174042034600500d10b810580c0c0f2040091485400c0600510310078244d0364016039a4414110b219104280c1c892201901204001b0100b1401d5030082680c000310341e210090541c1e8006249085801c0c4101c42e02503120290b82d0122801c010b13400000800c607070201900d05101000200d4003030307008031614820285c184180040066190303d001604c101020100500c0022025819008182c05e000710100845000d0b03902c1070010f80b41c0c94104030581c1d006004a00840c60701040d43e86281d29041034581001b5042d03110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 836622041 1250 836620791 836620831
    0x63302061302010c0c0b2d0d09020f0a141206040831060504092f09060d05010801050103030306150f03090309180c030b030a0803150f0909070e0708010e 67
    0x159051350300c0c40340c00000c00e007025a1100180c1d02075a00800000c1080103a00d0308030040b282044080c0705290040e400d1440c100305150220b640a8100104100c1e44514515042c1903a5a24401404050140d8818200d4000c1508040c00409006403100d2001c50703100c90108000a60314008079402d0143c0c0e511200047c0441e079521042d604869040402d072504d400801190065004020b030089640141041c00544c1c0c00501c007120f0418500641040043c003811040c07a40c4046000801c1c240001070101403810001104410440720281c0018089035140c000410600d68175010741c60203046a02084544076403203840280240c01464a60350034141c8843d8000e06040c0120282d6000f050f114401c1145202880c00c00e5000b40b07117481c0b5071004a440c0442440c410704001412915040e0701007000c92441d202c0349141032501c4a01000c26501c648003e0b01ea08168807000e4006000e02643c0d4028924141012460105080d0042000081100001c01085020b021084498100c060008542d0300c110b0b130 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 836623291 1250 836622041 836622047
    0x130b0303070507090507020c15161e0606080c0102160306090f020d06050405060106050a0522080703030206010e01140a0e04020d0818031608070b030a06080106330206130201 76
    0x28111000c0c10320f004003a000508046503800262041350194241c81d060349203281080240350f00001e40c0a07440318280301042c143c54401c4003005015000d030403a1003a4480018403054092a00381d4200c40c1d02d510f80f80c0030400b07407a04020b000b140180900280030b6503c035018502d003090388180702c090400e43c3c80300f00b450180892007181290850f000b4200c0034240c070141c20528060070007038604a41038400c040001a03064420ba086c4d079040c3c6013a9549524104804118800000c200c0004503120441038000183e40f400c10081d0400540c0300341c0140c4055894450008075282c41644401403d1281c000c000c902039541690840541c5e41e0760f405088191124000720301c42c1d9201c60401402c501001410401002403c104400b100004804403402022803034100b44160300580b01d440415800402e060081d1488400510b0348544509800035103259145030a50a4076425840034502c59030781003492031680306050362100380c0355045100c003080c0740c040c4c4d100075541c8400030200000f24800424440c1160b01c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 836624541 1250 836623291 836623297
    0x807120f0c08011701051501030c030b060d0c020d03020903030a0302070503120108010e0f0a050a0b071403010f0509131205090f0a1d0708011a090d0b070305040203010b03030702130b0303 82
    0xc14680411001d4280400901891003e01441c030344100004140e200201e41401841c0c480d00c0007001c107025074402c10005401616908610308145078540d440850a81c83e8070025000801c9034510100e500c24169001a00740080a8082c1040500400807016652000401c07103420303500502e0010395070052400d1644c01c5000da07074580c03020019544000140f251054009000c480c821100384c600b0003100074001c036a202e841d040005c00755041540e0724408548448043c070b602c00103a061080c01d582c4070368040440c0b0361090b00b01452000b400f241c10f00c81c5081c0400000d50024606042008440c8540c542c00e512402c035003d44010001c0c001010583c9454050182c080c1010240100007035540300d2101e22800b1070848402d2480a1001000541c0c1030302c9541018104e40e1700d82a5090414042d4601c0c0c4083e038030400300c1d681c11002c44000c550008980010262003100c1d9a0340008182c03d00388100350a40d020f149442d8425802446a2009640d4000042c40c43c040200340c0050340d0b100c0300001c20b003180 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 836625791 1250 836624541 836624561
    0x206270607020c03070801090308040b2a0a02150c071101050d02070602031501030615050a0309020a060806010212030c0d0b030709020301030c1e06120906061512050109020901080712 80
    0xc06000c0620810035000140514404070403801c1d1801c040c0c851880781c3c202d94101d10081c00140d9000c0100d800315210400c3e45400a00c0d000303901001480e803400300210641c1d113000010005200050070301520740e06011072200d046034201d001c940e41c24400a00100da00500c0c00240001c0cac20f6188041c82a4300500845402500907802075480e2a124101400250422248006581303403898003881e2a41c0310f481000183c1c1da8111b00041030400e5201d085401e90000580b003c2415a604154000740e540c10031120000c1081d5070f1910707024074080000a060044103880903004400c140180f25191500c48152980e190141c100015250000f400007850200c1c0756001d5040b0a02c000004410b000c0d55041c0714081e0f454480754107411903004903030120542500c1c81514001a140210300184020540008000c503010b1600400c0071521440101c13500084d0300e0403540030549459200d02030581c0d41c0201030040c440328004500744111140082d203201030007000f80041040010015201c100940e0016800e1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 836627041 1250 836625791 836625793
    0x20904060e0c030f240c070308150409080a0e010807020606150d0510060f05090d0807020f040c0207150219080f0c0102040603061d13060218060f03101203020627 71
    0x401201010f91904842c04401e040d0b02c0c0d9840c1c0c0c50b071401401d180301707500808290300100d1400c0368a49040380c4101001d011b02100d400e021400c20015034550007504810340c0601511070f920b40e041c0001428600100c0300182c18002c2311410400039036008510107600032025540c4210700360910280345150700c40d020201c440d0318980000e10582292020300c00d42501c04640302d00711502c030143c6050b1058000c00c500300d0380c4401c0d0104080c00042124014010251011700803030105115100040d05441b5071205120040e40a1401003080300c4034510014806000d60014003040c0c0c15420380048521001c020181ca14040062804101d8003844100d03000442d0840003107448684030350004014200c05e03c14400d005c0a00a024101c1200fa2000c080c0200c406010404825039070b0b5032440e010350801d8543c0d1034580c515500003051501c030305c4001c01904008285e050340d64940001000345031000390b088200755603800941c1500103900021456007111a0072901180100102a0103c01b07941006c101000c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 836628291 1250 836627041 836627053
    0x5210f01020307030605090103051b01121409010b0a080c0402180604080f060a020301080303071202091002210306061b0a120f12051603020706060509010b18090103020904060e0c03 79
    0x1019040d4041c60050106940511000d0b03510030030888281c0c2c0030f0001505a40041180d1a18445100b0705101c0b005c40605050342403240b00c2043d14121340325400d000c030401804c2ca0400005003800c1c0316440040c202201d140901a00740b1f0f28450707540f51034400d590f0140703500003a0402d0743e4100304244510500000c1c2015031751500e4146080e1030341440102c60790b2500c0307a90049010100c00340203481c1a940c54000541c00c40e9a120011180d509042c1c00c0c482e0250303800c00c8210500e0700d0743d210002099140e40c0050084190a04c1d4001e0905608000041000d0041c0300307005840d501c00c030480c0c2e840151050000000c00c1001c025030705020502c94001d014102011920030100d4000d0101101c025050300c074546254241c00340348060320400c907851000e04030100d902c444a14000c0d070180c075035140181c034000756503030301ca801055501c0800e070082d07a9406030200b501030f0503501c01400890880c1040e10410390b103515540c0481c004c0348018000400322911800300c841645010031080032070940050844039 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 836629541 1250 836628291 836628313
    0x609090804030b1b03060f010903060219090f0602190c05040504060c0806090f19090519140109051207080d0515040f0522031b29060a0521 61
    0xa8964042d1000711a2901d40000160320201e41e0026001c070080c81142d140d14680d01e100810140d12020603180e07052041d284070100114603144080c0c044c03401d004210200303550071804040c016041c241d0082ca00100b01171301c14040564086801200d9603410b00e450190086149010942460310b9082282c010b032804040109000c1c0541003030f10060783c44d171150140d036240d020038069001800c845c00c0301601c0d803a1010a0001e0801d00c066280c1e5021200c002464521950f501400d003007422641c82e02844450058070300b03100d004180da51029817a20000c001e0348100c0d41e29030781c07213a2501c0c092269a40d80810510f0a009401d0f04170754100100c180308002c00d02c6c0c58046140c052201050540c01070741f44c20182691180f9a00caaa4051002040e8523028141040401d0f000e0400c418422420895000701c4c0d15064030004c00b5000c40d0b64840e00c841d031140642c104e44100200000078002c544200c001d414448151956541901a170700140e8008100540412280c4080880c1035802c0900340303e6444184 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 836630791 1250 836629541 836629553
    0x302131710110306030a15020705060103050f190b06060f0705010e06101707050d020105071a01080d091203110313120c05040905030a03480f020c13060909 68
    0x1094040d1030010000520b440b9001000790004403030307082d0141c0c00100088007151246400da07544d00c07204200907182c183c4580d0f5070390801c0d0b020b0b40b0484040d80241d01082c0c081800307200040c42c2d40c00c45107481c500c045007501c40203070174400601110b024040004280c03504603c0c21381185e00769a0850001e00076060702e044910303924041252007e40350011401c01040313900b400341c028820041d03400d0040030700754201005c0000709401044220705110701042620f000a1603441a6100f0a9a040040e0f5281d0300d045c600600703280d500107104040100450041c050304030b07000b0040d000540c00d854a490740135022140c080c81c1d4807030340c0c40b0308000741e415460010725940c080100780741540c0b20b012441e40081d600c10074001980d000311300040c416001840364520241c13290f0b02c40ca8011409416040100c00c903a604c80c00c0c01888421045103e00103102d41c0d56510640e030540c1c1244c000320749089207850158082c02034031841c00c070552038030036a40941225000c1b882c64206c0320281080c22010000698685041 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 836632041 1250 836630791 836630803
    0xa030c1404080312060a08030703180f080304090b010810030b1801050a0b0f1905060309100c030c03141009021b101d1b06091f0e030106170a0303021317 67
    0x1040341c07001900003d602410310b1b081003821109034100071420690b099a054031f00c6c014010000d11190b080c40f40003da8a6001107281d80100004c01c0916601c0d400d04c0c001500742c400341a44581801034102c140110841e094805070100e0303030005401140342e100c139100c06401c2f80342d050701a2078640c06c1c5801d004080b07516074010594a0f501300c607440820040342042c01601e40d06030030032050b151509070040201d41450300046510107140025101d0050b1601260411502840071800c0003941d1120590076441e010f22036030355002c5d107036518036081e46040a8210300200250003a203c0091b0045140d49214100114641c0c52914500603201c1c1010341c2c410743e20080c00e0f108210070f40f80c0711640100c0541180811030031205039090b52410400d080d0383c8180101c030b500420070181c0220040100700c00000f06400600b044600a640c0d400c40e60184400b007509490440e0403454003800d44104890104c0c00001e900300802d03a05084c0540c480c580c81d8481c080141c116802900c82c100c0300c0464910181c00403c40c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 836633291 1250 836632041 836632057
    0x3181b0a0503011104060e030a0b090c041107020a06050d0921090b0a05030c070c03080307030b0a060311090906040b120604031211090108092802090f0c0a030c14040803 74
    0x403014100d0791001094203076440100e2034000c0031010001407141510400b07074401060f0000c1c045400120140d07580004441c41141c02c0d148a821000c4243e0b01882d044c050340240e84079114007a4145411500043d9501d10548039001c14048000b408000b1407201c2d4010044207a00040c40300c50b14401d1080c0f408600e14940351810008116200104064810a0070754181041e41d0380c4480c02e5550b0607440108035800303203030300b552047c8415400000240c841801107204e00c02c15500416105003020601500410076000441814184070400340b2201009003581c0303481004540c58100c0741c5820012038024403c1a17001c40d081000b02d402c00d20343c039400190060180d44641d6500c1e0035548a05440b204071440d2100c150000b2a0030891312030340d588641c0318180c01c80703085c106441954a0b0300903240761408400035000020040000004258900075a905a0001d2251440d49031403a00c201242070328401d00c8403017800e0690310b90440d500b091090240d00b40e42070402403d03940d1a61191140e0b40e4a40020301 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 836634541 1250 836633291 836633299
    0xf0b090f0102030c1e070f090f060b030106020d05030a0b0a030f1a010e0a05072106030302150432120910110d051c0903030204150903080405040203181b 67
    0x140c0c104941d4030000407580d0410884001d8480341c00d02140740d01d000e201d40c9000c1d090910620202107941882d0810038401004443c10014404072407032076010681c4d00e07981c0b001c040e41e80c00f40f00401905802041d01d05c000d402d01d01d0456901d81d01c0b190000300070090f20a900e60071503002d40010040125001403203c2c6980185200f058010f4801025200c4103424003d01d403105a460003c2800400260001e581090303a505100390030b088400d0801d0b2078135100a01c0030184980f1500700700203054042c4010b0040441c00d0b611f0300e02c1854162941c940300e40f14406d07007044000c1c85021000c030700c40d001104d2044861002c0d0699808410008040c0c40b1b81c0c100e0f12006101c4c8012200507442d26000720428aa0300c05050054405202d44c81015100c40e08106008070300706041903200d155840452180c10380d06031094800503121410f000300e415034600c644480c1014401c850354140041100241a101120f004603009603481d503c440c0d080301001c0102c100103c0600c904c8000303210045030719500300c2c640041a2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 836635791 1250 836634541 836634559
    0x3030f2208090d0f17130819030f020c042406030608030702191d180a32030f070302060f011a0f04050d0501060314010b1c0317040615061d0904020a0f0b09 68
    0x107c00940304c081c0e000381440c00615040705a000030340585d035500d03146c2a850050301c002c031100e0ba000c01c0c180c41050740000030300d030070140c0304108240e1a10341c0e03000500903900c1d040104078181010503075a8410080060300c1040c01421b901140100e400d0040c006d004803a400001002d8003541921388400c058414504442460042c8001c0710303070008454004a400c00c108801c01d00701d4150a2405a0600031000e290900400c001031041030100300400d0814081c4020030f81e40d150909000741031a5000d04143c002c20030f014010411000c5002d204034401881e03554840e0355500083c1c14000d10b00c21039001c1500100300c40340c41c0d403c0c800194400c8049a003d012002d00356003026654034202d40707403141d401b40d02420381c08565096004010603065903034400c1c2441c104480f06100c02d07071035003e41183e08a034001e8a030700403140510080380c241401007143d42051034405544034030302c0e6040054002100c1c0540010000102950b0322424210300030100000c1c2e03c8000e5880b040d107580c00c0d42c41440e600340600010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 836637041 1250 836635791 836635799
    0x6230406050d02093603090901090504081c0b090106120f2f0d020c1c050703050301060f0e1201020c07050603040209012603030f2208090d0f1713 64
    0x40b0942602d1a5000380004860760701c4420668049500c4603030001104a214501d402c0a04d15102198503078011800654541d0071710b80420102c00350581241d0300507810a820310000030ba01e042034a002c6000c4511544107040c0c403214500080c072003140c4150348a10301100008209410800d07000001e1079140d0148543d42c80c0c4103540095400c1d0001980c80e02c080440c440014520300721410280d03411840d0342d00c0ca008810f54182c0183e81090703640101c10341083d8090110449096a021641001401c0403800d0800075200a840c90105100d000c0c280404103900501c00351240b0106000003074011b01b541c4994000b1f01c003d074000d42012510311403078030800801283d203142440a0360300c5580c0c02400c801c0e0503800d000049540c44d80d0b02240707041d50013400041c0e4044800a0000d507204480c00101b042c0503145c10341c0e050700c6c0000b50007281c518224131350035550040b07a0108102c8140740010f54000c03050b51590710b04541251030025015000301003200c0100d41c01d402000084c141405000e03039010b41143c031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 836638291 1250 836637041 836637049
    0x171917071107120201020a020d140d0905011205061801090225170f120109020909010b1305040b1314060111070e06090c04080a0605190e0c060c010623040605 69
    0x341c2551140c0ca5000403000c020851041400319a0184103105075141c01496a001c100c040000384c00c1141c0302101d00140380c200c4042009070101d0300b901450812551441c00d80068408482007101c04001625480003801640325684a480442a0a5450049503a40d10000002508441002c5000100030045c481010002c20440c8460b503401c03400503900c0260350a01c2041da607000880e1103184010074482c2e100194141d0f09980d000303020034000507a885180383c0c1044149001600107800c200710a0016041e00444104424103071401036800080010300ba00000d4050300d80b20b600c440791241442c020311840383c241407515000d21800c0c0c07599482e2606103440b5a458440c3c40c001c0180500c450303400241181341030302380e00c0d0300410149030017842d25440b00c0e500c0d4113040b011003050707401688910131321035464660307551045107441d004d20810000c440c4030402d61b140c0c4600e0003914840c1d6000705064003401c40030b43c0250000d00300140755416140c0348070b082160080480c0c4003d84a1403034910300044c1824 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 836639541 1250 836638291 836638307
    0x510021f090332030106020a02030c040903080f040201020c0d080d050601050c03030a0218060f1321022209030918050c040b0715050c0d050108070b0717191707 70
    0x541a251007035200a4041801d103034401d00c00c03407858644604103c60110040302c10085001e424030744d001d8451341050740141440c00c140c0c61801401030b8904004100030980c00b000c0540c000c0c01003d40240941c0352400102d20340200012000e500004500015003005815030081400d6400c02001388025a10240156100d0181d2807200b80150820000100c19045c50f0340286500f0a20b003031404c0580301d0303041c04105c964110307070070011200ca00007807182c0d003401e0300082510003043e40f072070500903140d50b429280d90020f1440e0300c000d00520b942003013902c040d8064012050040b0701c0c0d41082040000d1401e00505509440c801c0c158094140e09400402000e40c0c001ea6106107980c110316843c0a142c1492042e41d0350102005588041051320006240c519501500f4000d155040045403185400c0d05520f0850f03806905c807800780d500c505010407244600f50165040c06070042c00072142c100c81304404601030303c6803407003034420205000c5010208542181624078107d20010b8018200d40c2c90030819a003042d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 836640791 1250 836639541 836639543
    0x30901050708070f0f080403030206060d021e0102120310030b0106140405091509090601210b0a151e06030c02010911091f080a050c09010608040206070206040510021f09 74
    0x200100481c0d03010802c0c4100a0485911603410344004030aa51110201014208011a5951400202002416410440f01c0d400030b00860310441d07404c00780e90010310b1762012241c5840a8107082e0341e201c03656038001c0c00001d09018004026656070301d0300710340c11100212640001c4a081d4521300000c1021481609610b1481804000291410b810a401c001358454000c15030000031000520b000516202c00240d0350007200d0200084c13680b5414030751440e20240301811000441201c420b5a00d000c0b64080c0c01d010341101d4240340000f142070303c0359045018180d00b41c00c03190400000d032900300180074102160000b141d8590386c08010040e20810300700c0c261031181300c02a0141140d83e00060340c0d4940b03810340c207402842c0490300e09400c0b14800c01003000f2540703c0d440084140c0080c20010305201040c07111400d0010200e0b42c0302070944c10700101602014010b0070190145002141f25011074988508075400f03403a00030b000d150300c03506019009546103403e1560380c18041001c25140010075541c01500521 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 836642041 1250 836640791 836640797
    0x708070804170c031204050f0d020a080915040f091406030318060d240e0103031d06070c140a0f140915280b120402040b1f090314030901 60
    0x15100c685502902c649055902400c01c10200039a8800c441d080009108034225100100321904c0c250a160b42810240e05c500141d640141e01d11824055012801454281e8070840450f1036006c4070b408070711085000369290320300980000d4007054614040550000302c0d10802030a1001d07044248640c880d006007078900c0d81d0550b00c2400324215898190680440c6203402600c401d052030555401e1509440717031408440c1041c4030350244d00122101030803050001e0040d060b010520b5516590300208030f0901c012072004204103003010b9078815a944011182a190480c944c083e02d9a201d01c2420b01e00c0726040c1e0346501c80d0796000300001d0141a14071208084170148c02c404d06100181d0000d2041003000100007038048200621540c03c2540c0c2c100720030140c03c4000f117440304803802c401e02408842903140c0105440d42028029a503118091145075640300360b0503640420040103901c00301e060f100039403120740309601c802000c0c01d90300c60340059040c04882c051212040c8210b8201600368580c46041c0c009800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 836643291 1250 836642041 836642057
    0x30206071412040308250b010f4205071b18060e0705160602130501080703140106050f0d0e0f100203090601050f0d061a010e010809150c0903061e070807 67
    0x11609131020500c0701e50803074030700340ca07061b9240c4e0700c0a14420090f0025018203132a0b0400388811000c02e45072504910070f2000f06401040003000303840c01011030386030f150801844444581041c0d40308200703440e20158400c10b418903092051184a00c40000d5020380050704040190314081e140700d90042c0e20840b14040c00305a1144c0f15014119a258880240c0e58084002c2d104803200249142c03009050000a01e400c045030b060904000505404c0040d1240301050308065040d140c030366080c1492811103440c1e00701140d5483c1401c01041c000c1c0500400008a240380c0780300920030300c401060040404088400b51004040308100039822404241c2e429400c582c01840184003e00b0041c501c03000040000b807001c401d4408540d00e02081d0b401002d2a05038201e01c508040c1c0403560052804c6401c50003d08140c0381900e0010b012564500f0303122409501c039041c8402251000100314115035540307501400303440f0646400d00c06000c200500b60250b1403041c1c1c5d90700001c0d0600b8803502441e0300540003035079201c02c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 836644541 1250 836643291 836643307
    0x405010806061201030b13140102031e0906010b0d09020d05060709050301140a0b03030c1b01091202090406270b0613111903230609090c030d18030206071412040308 72
    0x31b8480c07401030044e00800c2e008129180450301c8030f6600380c010f40c1320703a0000d0307500d241429003003074000440d0b10a5521192201d042c841144c2c0045400e034191203040c040380d6200c40707003424183e015011840c4069001508841c06005020703000c602c82d403007080320b62036a00c2c045a4070408e0600300c030050b200d0940c3c05056000032450485680d00700e001d84080040499050404440300603041888080220500e0744054040241d556000380c1594010714008a55900340031068000c51031300b0b60f0041004040c140c6c0c410308052802d03260400c0ca902c840101409004150a514250340c0320390060310468425203170445860042e201070b008045040c100480074504040c265880500742c10b4081440d241450703142c50150300c0300f03034144241c2c0040a03442000905075042030014880509409001c0c180c4a4002c2e8040b00c005072030000d00c2e40c1c07a001d410310b44078641c0390506801402c182d2240d00001d500c000d000070100c080c0221214441c003103284150641d20310715068400b03911184904e1100030325640301408030b00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 836645791 1250 836644541 836644553
    0x609060501140609210d050a030b150a08041406280903140c07090f0605210c13020c01050408031608040f03032c24060a0e0c0f0a05040501080606120103 67
    0x280d00c5c00d81100f103042800a04498039403c3c011b007011000001000400c0186881d58075002e41c4d00168815100024041e04001c0d01419034469100214107108481010030308112040f080810034011800070345401e420640d40440361403410b0f0a0845078201d0a0a0788844004503120b80082e143e40358490108040c0804201d503c05e07003002081c1a180c1c01140400501d0381c1c4039010700aa004060200025081d040c08208000d403a0300c440401c0c1408914807801c0c102e148001490f6600c0e002c2100c0c50010a44400c948001901c1a0303d503c6900b942003070240410003801e10091030103043c0380c4000481302d41ca01c0c0c0045426180031100500341c10044540e04010a0295220310000e0301c031290600c04d80c21608460900407407004614441c240e01c803030149840301c0300c80452012001c95a1400c4286410b0041c00141541030700d0003001041c1fa040ba0204901c01c8903c2c08454101c244052001d4072000c10101c050050b0708207109040c0031900a00c005a10352a1034022180d04030400e41070022164250785400d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 836647041 1250 836645791 836645809
    0x4050a060c020316080105060109090c120515030a050c0f12030d020d090615090e0c13020a030b1302040f050d1e0512040b03040c05040203040302190305070b040609060501140609 78
    0x82c2e0b01405525209140304030f4410801e0013401c045000030605050000c001000c075952030b84030410903858407018021040d032050780d1158405882001103819111a0f8a038643d984140b02034507498400c601c41401040303804160a00085821240c3c50450709210041c482c02e28100c9000d03120a8008006040252203540c1c0030741824a01100c00059240c1141e99020840e89550078449002400280800c251a5a801980c40c085c004001400e8500700b00c1d030204401c6d0b020f400441d07286039004a0111829846a486000d480030300402e912100001458480000c0d40107000c1d007503001081480204075400d001c00d001201941c000310052445084044004d2284404a02140e250141940b04601c3c1b0101c07c1c003400180a08002040d81c80c10305e0302d00310000040781e1b4840c5020b2801441040042900401c8400e5141c40320414042840b46500d070803a1309100b9100010070074200c0c0b10900003400155404501310a01c01d40c010481642c070f0340c00e0ba18030400c030f00c40e81c10780c045030400492003035041100304 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 836648291 1250 836647041 836647043
    0x40803040c0b04080303040203010b0406210812010b0a031401060c0803130819030f0606050a050d0e01050c2203020f040f0f050403081f24021e030c011104050a060c 72
    0x4500c0c0c1c90340c9411000c0c07119030141c1d020032072560000c000c0c082546000c1c030400004031800c480c01c108148c58864102d50a08907181207803940c41000528000b0b0050b46411034000e1200b0902c4030656684610041c181c54100c0f5a240b00047d292040c40c100200102c2c1085068400a445440d820b001640d241020307580010803a02d0040f06045600c40010741c0e44024040c000170040c005603100280720001001c07144d00b0450b040d00f4906042082141c203030030030300b260789011642c80d00542d1500d22102c9080a03100c020509902980b0384010040f20341c002001604002c3c20359031040a42e9628005004400d45441c003000e5440204140c044031180780170b501101c0e03603200441001c40d0b005800304c07031141101d508072015030110b0901010050300030905c1f12041c1d0705030322485652404c24100041c2d0150310304403025001d4001980160060024000c1203028141082c07040c01c1c05440c002070240e50f8032134015420343c0b061384d82460501c10110003680241d4040d650050a100e6065113401c500311445d91800c64 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 836649541 1250 836648291 836648303
    0x203090c100e030a0b0a0e19030c02061611010807020d08150f0315040606240e0a03121805030a08090f06120901020406020c0d030c0204200c060a2304080304 69
    0x307449843c0c0c4003800504200d5000e078a05164510301218440199410602c0e10060351700803288030040321040d40c034500d030425010700d0090b007819401e20100d0b582d48030b007040700c8080da03641800c26410010300e0306099500180a9884008903200c0e00e600342da0b290007940501011840960004070700e441400c900f529100780043c00c109404070108046070420802c40e003080d008048040070070090140a004400040142c1216507a0201070104820310500e00b603a0300d9001c20070720804400c0e255591904c0302c000b039a00207000440b02484500041c00c40e005030780000c030f10f00001c4c03900062240342c013082d1034000b5038000b2090f81c0b814881100300700000000d2056a80d016509104507410038000d01052445510800c1c00107903202c1c108a806440e24214440e81d521611010548000103a8804086c0c0345243c5c0c182c8012030751860384011030340000c50320f403107071561848e008c1200c40b0f03030860004d03031103006038200c2c90208046448040708501540c20414088040c3c400341d004100001d003500005c560180c0a04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 836650791 1250 836649541 836649557
    0x1060e090415240b0301030206030106051309020a020d09080607020a1506080703050d02010e0706090b0703030b1e0906030d02031b07080307060504150b13020c0f03030f010f090203090c10 82
    0x14807018222102c80b080d50080386404403c0000b02410412250080e000c503c01090071985590300051842c4814002e0404214020603601004400e83c401c51010300b041510564881042c814029950103d0040010008640c01400248001c010441c28012031603980989500d09042d2608204002c001c1520124640d50b4034001400090070b0101101a500c07500103046800000300c0024295041e004403105135402c06841000100c0d00310110b0011516a050b0864441d9160f050650007411002591a00003040c945181b121035060500b0350b44e010401c03130300501c40351030b410f042c10369500500e4000d00c05a4020000030310240030740c400300406607040400300c03045c00e921030b49410300f10780100004a49030750302d070000d2004000e102c95000344095540300742009154001d0f00044d01403a03c1c0144c0351f00040d40000c5102500c0014800b5450f9040800101c03030782c0b401c1054240d40146000d01c10810b0300e0005c04c3c2e011680c81001d000301d07170149514200400f80200c0000401c0400021803e001080c42094 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 836652041 1250 836650791 836650823
    0x230909060109020903100c090303090e070813031b24020f090603041e0b0a05090a0210030b0d020603010f06031d070e18100e0d0207061e0c021e041401060e0904 70
    0x10b0301032011f143c0300c3d40d600e884009207989005003141c03116400c084001d000402c2000407940d07000420a030b102c8080d40110413100050f040940781002c0704019604803020148030201400603214540d000414504644080484540700400c120f001d40b020314840c80b00c04004513901498090099900103000300100320b60019610301e1040c8040590341c0854003125600c040100b90503051048035440380b44d4801030002c000183e40000d0f4800b105088600600d662182d06040a0711041d0300518141c2e0b029041d03e50301e50319050601d07078140c45481040c00003800c025003030608424484180304144d01030001001024209003800403503440040064003200ca180d18244854030081104c480d00303440300b0500084e400070540e500c9040c80200c44000d4107551080c01d0802c406680945908090040a6102035500c0c0b03007000c0450344407090041c040d5010110030140c0103032411104110945040448007000a1010360700c809108400900c07500d40071800803103c0c03042509007142465031162003410054a01209 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 836653291 1250 836652041 836652073
    0x70b04080105040b01092a0201020d0c0309021306030206040909060219180b04060c081317281e03022814010603080f130e01230909060109020903 64
    0x180d444004180c2d150307818070061104440609000d00080030003480141000d44507070b080f05202c49419000d90441c9000c03203550318400e42c180d60015500450030b001c02c1d012007200801405111006901c6031407094032540382d01c13500d03120341c008032a4054541401c2c6480c1034000b000800000c0001d8580c03980811840d0010050b03035031110b858504030745a50700d1141c07914100d10070f402041d4020f00440c0b00100000d020454100c0c2d442d50100d0741c0815560780c1e50019800403043e81ca860351203001c290160707031100b204085010540e007000c0850136110054810380b542c0a03915206c88450090002d4185400700381d040390a80312a011000d00034011103d100e1198013249607042c3c0c6074450041404070ba01c1d0440100301107070081003440b8007000000c0c050203003181c480c407199104001e440a2500d40001d24007424010427201078004000c0740701003154070740e52034011104021a0314140001c1c4004000034800c2480d10140060040f03071704400030640c607820300d01610003d501c16100103038507100e45501b000c0b070040c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 836654541 1250 836653291 836653297
    0x15020a0609140610030b06040b03070f0303170a1814010b1f1223131b093903020f13090e0607020d1b080c0a1205070b010b0705070b 58
    0x4071450302c00d07948a06081c045420018042e014001c400d1004504002081d2a070800c10380014003224009018003101c400a8500340860f4005480c0102e2144000306054001c0181c204250390501c6184032030fa180360070b11081f1340c2405241c903d11110050000c01090344625040c41d03190020307000142c500c00d820002005800100076081885000d00d444891056101c0c0000140307001c00700c0e050020450014031420f0300f02c403a011400fa401c4c40c080001d0b840740135405001d041142c00c0003006c80d000803040b05c0600052014060148218103100344103260b52482445442108076a841125a4414429040819144095800782015001d100c0c00398000241c8009020610b1280c40e4070744520700c0e0282c440d003a544803440d1031855170800710401c10320b2600401d030700c00d03904076514020781d607552465030b145100e80241030041c004090104130005443c10019402c42030358069003c0c2c000ea1404018216414031a060002b080c02c1740c2d2600421941040b0707c0540583e41c800c00541d180291103020580e5560 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 836655791 1250 836654541 836654543
    0x160303171e100911130e070311070309031a0610030506060f0d320f04020d0b010305062703120a0906020a0c15020a08270f0304051e0a15020a0609 64
    0x442c29a000c1204a030b040c440c1d00310507000c13520701c0c5003803525240610a0069151149103040e424880000f0f82e994400d50140740e145007916451925030a003410010110000c5000c103c0d801c181301c940e00c0301c400e170b260b0824a103e07040040031705040220440040740030708800303050ba64106c5070a01481080b0300c4a10b001c4c0c402d4965840c0005127070b401c9640102304188425401c601032058251030644800c441030003050b4490400f18416100d6103c038404500009800d5101901000c0c6020011081090200c0c24900035085046940c4131041c3c00c0520112040156420720591f5000304120b0900520200383c09900043c5403000056546664a032082a80d02c44c80550303000a2142d84401c0401c02035811521901d00e2860301103040040613900503080c0c0c40c000e0440508c41c111080b03020500c8480403241c601c88001c41085d154001401420140d4070b40048c01002c1c814103800043c810404419140710000c00001050360354520710f031004281c150601200502e08600910300d07036001050007409141a91 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 836657041 1250 836655791 836655811
    0x4031b03080a2601150e040c0f0516080d020a020c01080f070315090504110a0824040602270f120a0f0314030f060a080a0209040816050618160303171e 66
    0xa07412170035000b81082c2500c24000d1042c0d160038801c81555612801c0c0c2c0240307500c281040c69a0b081411400040703540100401012041c000400180601c3d6a4000c1c0c40d011441e9004c480c5d0114500d801900c1000d0129040c0d0b041d40e542000203039040b48290443c50088882d01c0b81090b00c0c5859440810a84608032802c0e100f01c45981090091402e200140340c0042c6015409440c080141c444427280d1003284111100f15450050089400d0204981c112585c40d19911964501442c0820355080f48081111038140325021569000d413150400c50348426280590300040d20070360640c0d84d40e00c007482c100d00100380e040003901c143e203203c0440700c04000c60282010b00c0044501d03241200400901030190341008003030b9081000b0712001602c4043c823060300290301528041d11480210003801c462104000060b01c148128001d000c807150300c6951034583c200e80700d4141d402e0f540b504030b041101141d140c80010001540b00340980d981030520030350785070001c154002405090340c8002584241440580d441030203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 836658291 1250 836657041 836657069
    0x1051c020306100207060c06020d0222050307140901090c0c0b01030302060f0c071e03030e030703050702090f07080a050c130e06012304050d0c1a04031b03080a2601 72
    0x690f10b05116900018085440102065030411130000d00c0700ea0380724001400203802040c5100d004403150140c0d041510521024031110120b409109410b0b00c0740d2140740d00902070a0340105500c05c0c910342c200d11507c80501081100d92800040304000c00c443c035111010008140700c0040010044100c0034001d601036402000c16081c45941030001010152003d10a100f003000450b000030320140b0f035030441c0300d01c601251405180900b400e5019210901a607070281c040003502c00c082503000006082c2031402518541c4050f40e0f0050350f0040c54000740c507044041001c0800040c080c0700c80350413056000400c5420141811220388450700c0c0080181c00001940810100300281942c0c0100da004410071030038009200700d405440c40400ea84168065030b8080c2e00304100d42c0013485070b00031480c001030184a554a0740301c007031401030b0007594100c0e000481c0c40101030020548291851040e00d02640d402409640c54001403d60540b0007120000c2010b6051100080c403010400c499400c80340200a0072003c841 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 836659541 1250 836658291 836658301
    0x1030b0108010504150e0c0a17061003050601030b1503010203010605120f04020a120f050d020304030201090e160e13110d1d0303010302060f040f080a06050108010c140901051c0203 79
    0x1518058000c0400340c1e16080030040850162071a003071240c0c0307444038000740c5840611113007800c01400c081155044402c444000a0100400da428500583c480c815100592980d03490240384540360b01c00a4400d038040c00c01440480c2d00703000d2a80d000907445d00302031407400d0441c02003403c0ea0401d9000ca00440c5021422981c20b100040b075041c1d00c05d001c41c146280928080d400251400c03610f01518dc000500e2a44140401030131101c1500500c1c2c00000301c468082c00110000d5403940035003c12030010300750542c009010000c40c02e09900454044000811038034110008468558a4035051035203c103070001c82c65400b440e2885011140824075501603034a4003440171540942d01403074100501307001002015402850040300b038074107503a41215900d907601c3c0c0715030010001c1d019540101c92503400390b03540069005000101e445010380701d08400d1055a0341c4192003401c8918511110010a0800440000c1c080d1004000c000400c4141001c605059156605c0300d0f8055460440305900d50740003051003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 836660791 1250 836659541 836659553
    0xe09070f0617060d05060403050d1103130c050901141c0204021204380403170f0703051509072709060503060105030c1f02070510030c12020f0403260708030103 70
    0x903800403054130340c0031301c040c890b44e56260744220040c4003030200980414050380070381d205d80140c00c0704031f22010740548030301342501c1c0031b80c602260310411510401e0f50f00300015507040160701c080c12201c1c452803840c071041c00001444240e441c1e8000c3c0b80c2107008401400c40040e40d8038405014100300440e6a04c110340b0306031600d9644009408004041d94001610304662004c0c400e07040401840070003070340c42d0035403a580b030f041e20000c01905490106ca040841007080d80c0d40704c09883e5105001070340d4140259145d5450000201655074240c40c0c00021001c00a0308060042490b052060b03400c7c001c00d407012806144800c2504401d801007110103032030302d10800103494204529805000c00310040c2c01e04d0402240091f0384140b1850740c1300c1d40c42c0054070010f080c0c0c0b0300030312856000b80409401e43d454050300c07220007001811540b481d180440c005090b000d81da00400d1017502c000101090001c3d20b41400c54a4030f03141c0c00c8143d40964208441281c00b1f1000c1c10300d8801801c01103108665860b160b504500e040c1d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 836662041 1250 836660791 836660837
    0x408040509330d080f04030605071115010e01050f0102070f0f080c04022b0204030c03060b040e01090314071103100b120c09150d2102160e010e09070f06 67
    0x9612102c00d006564000b03941e280d03420608035900161541d92049000001215401781d5480038000c50314141c204030131150441460400049100280c8003000070324060064011020300541003521a100c0050020f800e00c4020400003d105004813184150b48841c100c0c440c0000b0b401110078850815405c00200d682041a22180042114154108003102c5220030000300094281d42c04100718080d030110000807a070403a0007a6400c00a1041429100c0c00d100014054204850f409140b80000b4a60802810721a80344802d90541d1648840034110002c4861508101401c6e03d45074a25224002d142c1d80401411420b41e01c40c0748081581c1c94840308000301e6421600b4516225003009443e216580d40345045258880c00701151040040e0f02100858082c00a40000402c00c8000ea00c84103500c0d03d0b051529070350b440030ba5007151a1003600509a906006240c880d001511480d01c006119030044910440d41c0401004116860941d8550300b9054a80e09603009602189162806080301080120303d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 836663291 1250 836662041 836662111
    0xe100302070503090409020d062405120a080c03040f0e06030d0203040807060f1707170105041404060e0109050d111e0a060e030d0911180f010e0408040509 68
    0x411414204180c4500d80c983c480d480210348170b1581d800c05041190384482451131501c0e00071404011001081c0040503544c40b01e410085120000350170b00085926184100c07060344101000030b8100b05242d43c0e02c0c940c007034012408000b01400103200c0803611003003121481c4000d00d00301f00c1c0b6942c181415424141080418200f002c110f410801050091803000580742c01215030601d004060001044002c44900c41c0001101c2602c02d054400c2c480c40960002c070b00c1e002030030910f8611805980e140100011501c10503402540c05130390b0800640424007543c0200d04484640002040361038890b40c845d030900c1001424540401d50031081c26400340c0c403c2141d0685144154800511081c200d02d91594a00340c0a000601240d190461181c004101b130099950041c0c01250a102d010f0143c60050850740b000c1c61680e011381d9000c10000003c410105009000d88048441482039900300340095852800041042d20700031070400c0000390030340724025500c4c401c0c540b0341a01c0789460b165901c0e450103214038400c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 836664541 1250 836663291 836663297
    0x180a090213090b040e06011203021507020c132d090203030f070606080a02150a020f01180614010506030f1e04080405120a05031804110d36150e0d0e10 66
    0x20445c1d00e40540000c00324191110059600340d44440f0307190403840d014000d01c824072482c01d42c00501403100d400090754042e008003111030302c0608040511035000c452002022651407407104511280ca0060544e0000704c00b8000f0f00f010554034101e4002c203107540c1c003000341d803917500d800001c0a00a1213454802c1c034000e440d05c0c40290444091075000200740e10705041e0000010180001c441441c58000c00c110b0510300054002485840c04504543d00700308800303401582c805041008050a0842a0141c40e051700d800900741c0d42591a0050b1510204a00500c1c00d140d008024074220341c10a440420340703200314401c04101c0c3c1d4480c20503061140d00c52030000103031301c0c55101003e10b100090002c03099980898108010340500c0014400040141284030039288004000113480c02c02560250010640c0c1c00a0011002a42080b142a003840d15180c01412180050141c0c171880000c50490542030005500c450100b141b400b1000000d00f040c4011401c030340490100c0c010303000d0608000c051002e000c08242 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 836665791 1250 836664541 836664551
    0x302060f0a0c050a0e030c0a0632030106140403300e150c01110c010e07120c05040b01030207140114090102070b010510020a05030318160803180a090213090b04 70
    0x8100070f0030b00d000b50903030281446642e0400b14150b40f0100400c00c00088001c0124492070f13034518014065020a800ca00c03946c03200401c1d80c246c201810340495481d0180d160415107582e10300b00307048071070501380c42c40985120340030000007012850b403000c5000540c841c806892200601089200c064400b0080a1310501c0401100118965079100c0f45004c0841340400c1103a803003014010080c0146500b55036042904000304100e6805041503000c05620380c91035084855a81e200d1540c81e21079045484001c110507a15442804981840c0c1c01c5a260180c045c1005800e061003a0b40b800411603210203d555036a40d01c00041c2488201002c00c01e0304595030728021071178204151600c0c141c440050080c1070191200c9a0003c0320140308010780702207540c01206aa88a06009501040f404400103c0c1d1140380b080c6042c003110820310181220480712454001c0d4603102c3c47da88600c5051b0f48103a107142c2e22865065000031060028002842c0405c0418064030006040003031000880b10b00c00225401140b40c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 836667041 1250 836665791 836665811
    0x15030c1e050d2705010b030708012a17070512150d0f150908041d10210212010204060207091b1d031501081c080c07020a050406030302060f0a 62
    0x1003021500c221190b024081a504a202075203d02c160b10b0342d10000c030215448192505103c2d06600038074034080201c0954081d50394510300c02d426609050043e000641c80210882041c941603d071400800341a810045584007510210b40b90204040f1885004204000384141001c15044501c2d644082c48c0400340c2c0e1002070742e90200c1e505c1811104021300c0010381100050a1142845e48080441c80858081c01400e68900e0840301c10b420502c01d8840410407880d804a5002181308181d100322114900c56100503e802c002072000360b03d501d1150441da081d001d61038050b0b00d920342c3d26015010303408000341e40e40b841c268009142491541c440b0300d03924070b08070fc54040038003404841c0740300c200c1c18038141e03e0b8862942c40745803804042d1000a0790500c12400da04581600c0700941d24100e92036a0181e55a000400b4840d450009616500e18001501c010008000d007041d84042c2440600141509942c151030390049001c03501150010f4001d80d1110781000000d8a40807141e941c82801e244041c4084490 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 836668291 1250 836667041 836667047
    0x6050a0305100f09020a0e030a03050c07060302040e0c212409060609010522090903110604032705040203090f060601021609110f0d050105041d0606150415030c1e 71
    0x2c980100d10102e600011044c6006c0c3c45441c0280300c0c0036004095079030102d130601e0043c1c1241d002c1b01d141c6c0c8580c011307201c0014203d0302a10941d802c452280401c0b80d0280e0720100104030030f6000008525000000e5044191000e101c00d043d0740c0b1942c2c070007102d9029020308252032001c1403010000240301e403003820208010340d2100f005072603c1210038200030b038481e9568844904407101080102c9400c02e03070190000340a1704680c00c1034400030b01a0701e940707954000c1030b811661186000c45019000c100d40ca54031030f03401c1d81d50072254080182e140b824a80b6080e203c1c0006800e0740c0c025070341d0725151742c80131403010184002401482c3d0800b800340001d1000c072210707407010812030880380b04200d00140d030f60317103001c1e40c8100d81c9085401d4035120600c407a41d20f809080d5060010035080c080d150080e46440041003415425130714a0019201c1c440080109594810411956a074216010f0794221401d010008051072001d60780503410650b0784010590701107038400241007112160740b4460400c0c20315111803590360 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 836669541 1250 836668291 836668319
    0x10c08062403070e09040507060f03020304030c0f06230603010b01050909070f120606020105090601051507020d05010e07080718060b03010b03090a020303030702011e0204031109150a06050a030510 86
    0x8464078595440c0c0e500c1240c1580c0005401c0741407030b00000c1040c00c10040000200c0c11009440d501d07150f0541101c94520700f14104d010032540100031699045c0000c011913200041603c41c18825440801c0c00b0310310803845c0d500c90401300c1807260b0610495003409910300d000c0c0284101c008003840c0c028202220070000440c880030251002050144019002081038401c4202080c82e0b14041c1c01480095134401000303000b041d0468400380140540c1002060070f02d4140e507058a238200c035802d81070074996030713800300f0010700f0240204803200d65a0740300b07450301d40301c0c140044401060003002425881d4a02140340b501c440805084009483c44c2007014040e4001980070303a4190f9141e400115225500c52210a01c0c0a490f000f01035454480401007081d0740350f05401031138904001c401d102c40070b403103407600071400da00035400000d00074451555103c4080c204040081c0d03010359100c015000d80300c0b2003000320b007030f040c003a420442c00100002415078145805d8003606030002c0548420001c0c4070300e0a0755400703280c0c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 836670791 1250 836669541 836669599
    0xc0b0f070308070215040311010b010819181a060907020606030319050d09060f11070c030609080d1404060b030607090e0c0d11030103060b150a0c080f0705010c0806 72
    0x200b25000420501442000441007007807117440608079600705818081d040031800303c000c081c65030034400e8001495200f03100c440e0094000440b40e1b59038400040100c4050020000448841c0c41404c3d90000845d51503c0c0041c048244240c010060781420f10a104203084000d00840565000209026450301c0000440300c0400b030890802c40c1040f10410100e426200d024034003081c2e6801c0003520070030b01582d507001086c45a0303101400c000d0340d110910451b146002d125809000b41c4590302c0f0401c085916504404500c1d48110313181842e005d10a00300f60204c031188214150303a01905070400c02003081610031b45541c41d00803401011107283c0b5800c02490081c441c0a10120074100601182e07540b0464810f42c2c4600b1014081840091030103002d180c01608244001d49120b42040062030b1300d070030100e07412011035000150700f602d4003959020a42d0983d8400c0d1040701c0000c0c04218141c052020580a00b400390b1140d400444d841c0a600380041c43c002025015520414024000741d00c5600c0d4107602c02040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 836672041 1250 836670791 836670797
    0x4030b0c0304020f030d030f0e070302010203120703020f0c010b150304211206120203060109020309030a0f20061503060610031a040617120405130b0f030111070c0b0f0703 75
    0x1039036403840840c413699030380c000054151003403c0d007080e800340d056000450b903000424020043c9100030304805a50b4004d61001030b0140c1c004008071550310035061400c5502c82900d08001d0f01c0c206e43c0d458888495446500f600b10b203070b50f444086507034902c1e103e46d000b4004404c140d910360650401e40c03510032941d5802d014a4600011055821600e28014034210400c20103500c0c040040c1a42d8050320195000ca08000301e110f406000004104180300c0e10075a801981d9071801035003007184064094500c42099a5680c040c0808808800c0905144130004200c0b000b1000240005080c800c010860a261104a0b1071107600200d08011540d298400907904130011031601044400710f1401003078054100302c03030003500035081c09800b00e08414004150360748010a00116041b00ca800b01581500d0300443c001e455100420405840103290035820448412000074402515105410b001900b184c010290752450304101040c00c00038098004d0722000288462552145410242d800c80b981d0361180440c02014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 836673291 1250 836672041 836672047
    0x71404020d0609111803030a05160503070f0809030d0212090d06060308120f0c090901050f1324060306050f040e2e0c0309030c060e150c04060201050c04030b0c 70
    0x1000080c1d0084001000b840104018400d03d580384c0c0983c07544054030400c0c108945414103291403e001045441d010003540e0703100d05104040b06070394503030407002c04141c0d0107220074000c00780030035000c12500800d90700c905080b41e07544c941d0000341814550320b45074580035908080d504401040c1d4050440d00307818000c880351152202e641c0340c100020090342d00b0142840402085c030f0b01189a84111550180d00b041810031099600c4046035180e5120b0340c02c038180c200c11100c004101c1420048034081c940080100410503485180035440201d940400b609075100000c002c98058011183c07600d8800f2f4a4070f4907003803100d40d0800c404500c1507920a00500d01580e6580d04c0504013960178009130003406a00300031541040d40798501d05041031002600b584195180c40d2848100f54000d00c91404000d41c142c5a4450402d42a02c03048003d100d88640080e081c0075491102d403000e82c01c0380701c4a00c00d58203142125181c0d400c1c614024211030340148604010f01d010882840840c5c43e984c0d4503a40085201c115a0b5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 836674541 1250 836673291 836673307
    0xf060b0a03050102120915091207170a09140a2103050c0703060501030204050133050c1f05102301020c040c03090515060d03030207060902120d080907140402 69
    0x109a03103560788054115480441c5910004e020f030700045010b481e202044441402c80460769500a0405a44c405d0813580065602e10f40104143c000d419254055600241182d2148d020b01d2a41d500000c013100005035208014040f000c8004c0c1c03240b4048105407821200c1d2800c1c5004120356001180b08201404296582e010416200b2421262210904410f5418490780ca241c1500582800e00080f4465405c10002180c40138541ca81104d01c1d0344c001e07240390100788451040104a01c441ea00210820604200c001024441007191620001148104048850100c0100000c560000d0303e1080015400700c4204008140c24001900302c03407508022240c044c03501001030389801c00b644503298101d82801c0c40088003030380603030145001c1130055080d5007040d8451030540521100c00c50f841070340802c501100b440420701c6076001e420b20794440c070310010b00c1254a40004e03150f03058142e074550090327026070788a07a1500da011120580084400000341203260500200c203400f500c034690100d010b580d0205400c0303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 836675791 1250 836674541 836674549
    0xd0c0503040b04060504080d030c0816030b1e03011d0703080a090312031b0903030503010b13090e03030414060103050d03050a0f050103080a0f1b06090201090305060703020d0501060c0f060b 83
    0x800400580310700d01d40d00c1c4c3d9142400b80140e042807003031001e28015170104494041c005c2c00790301d003045a25600d0603079036680d128101044840c0400351108140d0340d010004015156081c100154004201c05001c081002d0000c15003550070300704400111520078140004c400c2000100c59090b41d41c40381c25903886044074541103130440c9030b540c4003030200842030340d00d1a11036030903911658a800711941d5403004611159000e440007521440000e0001ea01000100203203d6100f014045400746200b4844c5a6a038070f400c0300741607a6400d17030440c0040d00000144820440049905d800c0700040d00060801903241d0f484603501c0390550203941c0700341500d0303900240d004a900d9000c07102e042c0d10340c41c0400403542c6a0074443c0e12074001100940c08200c101c03009820080c021981e0f50454000851001d00014096407003501030a40d884040b414410004800700004406000d1240b0032569650010b803100902000c0100382e6006a010900740302c90f4406c40000300c0d80e494a803091b800c1c0c01c01004100020701c00042 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 836677041 1250 836675791 836675797
    0x605030718030b0627150d061103011d040f030503061f0e01180b0304200a0321050708070219080a080309150c0a0305070c0804091e0b030d0c0503 64
    0x940c01d008002404810858030201da54014031050320701040601913010004944441c4070090600984041c000030800d00c161040640508805800d10040d030070a81d403030303000350b038400e02c45519030480100c010f0100c5040008101e681e0b88000381c8054407401c0c140c4a0414511082c0c00203020000d0000004180707444121103c002818000900300240080210041c400860028400e0020702c100541414410800400c001030300c92940e1102e1030341c0c50701c0d0340d0f00216080e403501e41c800c03014604503094015555800c0100056020301954409035161109244011501408103014400f0500c502d0000c50115800da035038007070f8141c8014000003242185418001c40c2a40540b19a10800c01e0f071078100b0900380041d601030002d0301d04031000000b07084505206400b046030240100d0600380014147c40c1d1013608159000311185c2020031a000e0320740c541c40c169a1003500041002e0b515503c0c12a49400d142e15504600c0c0d283c2c034001c00010402c4800a902d42c8a40b505a8080050740c0c080039040c05014421 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 836678291 1250 836677041 836677067
    0x3081303210e01020c030d08061f0f02070504060e010e04050a060c0509120d080c0f04350109150b121b0a17030d0f0e010f150605040e0106050307 64
    0x280560341c2100844a8411100039801a00044001030300103199400040c5041014030002c000d0100c40071028001c4074403a10041415074000f101c082960302100f00d80c3c000c20340d40c0200ea41d95112412214070041e150180940c001e601030751030701c401041001d030000c2d44c6a06481200900c5405500c460a145140000941002d014140f60041c29861036401c48014640460306a60b008981300108a400d80c0b54010328a039140030600e2500001c040c440e0080082c8122000b080c61a03040946940c100c0074082206c0c80d0301c000440c481822510010001c403a690000c012040007400b0360441da03a06c1c8508540c14410700d6243e6626240485410741d00d140d00201700704164801c03039401c205403182c28241001e41e091998002c0e8130320200420307402c0d1504200030620071020000d5113442200c013110740081c1041035161002a603500041c0010f1442030282d483d04041411b004511003000400c1075242c04e4055218034140300c0200003c000000110601e203044405c80e0509a4071fa54503804180c0303480310410a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 836679541 1250 836678291 836678303
    0x1090c0603021804020c0709051906030b070305150f1c06022d070302190201030b06130305120a1b06060506031f05010c02030a0b041704030b16030207030903081303 72
    0x200104850341d1590160a03014040501a8403584034002480100c0c4200d103c0038080e07800c040010301c4034000a400007504100300318941c10002d00302445003000c403026034000711034190220040c050a180e040c0201d41e0040d8034002c0c1c40d100b800d1244009600318590000d00e0340034013031007540314541745501c5d1110725003030f03800c00c030295035450310b041c07544041070003c22038540848041c12400721402040001e641c0c0b0304d98560000c1030103c41090360300ba0303401c40c000c1c4101d04050320b0f21940203540e200e402c0502003201484503010007150840c68042d0408002161031a1481c00c203014285040b0750214802e14050003007100001111080c4c1405400740806400283d00500c0000c18041c00c85e19011300306000481c1007001c2c5103036685410044402c0001c04034060f5050b4170034024000401d0321400035036001881450003500381410151804400d800a5006a540061000400c000c20f4100c0c07644143e80183d5107002c500e05a016074014001c200d1500024100450220384402c9810090f10080c0107950084 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 836680791 1250 836679541 836679563
    0x60105190302131d01090e10020d02070b01271d01060f1e0b09060a170a0603030e090f07050f091f02300a2d020712050c010f020109 58
    0x100034000e0740c04800700c0c112443e281c103800540c0d250100c075150f0704842e41240c0040140d192040300e101405051884480c9030043c4250a401c07070001e44010315800d65506000f580320302c51401c1c81605190142d2160396012034408047d01158000700e00765020805402e400140a43d242d2003840400b03001c1840c044040d841c0c04030100325201151220340c01c559111104414044018210710800011880b83c4c4102a006001c04050751900c1405451050007520301954410340c058158442540d0a80300021111781c2c0700c07014800e15510043d44e81c5583c1040e1845081c03070400451803d01610002d01850400601240020112603800c007112200540140748605002a444c5c1925404040300b925401501c103031070ba40c0f04036082c5107003140142941c007680c03414418801c030300d003510030b521084a203030400a1122040080384141000b4018907408003080c52158205a400a4900321080d0032881181c0c141c0c90345480090400140b1055003102882c0000440d890700d9002c1c2d01421800070002c010070601 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 836682041 1250 836680791 836680837
    0x1d0904080301030b09030c03031618060929160314030403080a0b01020118021009030803040c031419030e1c060c02071d0109020f070b07050a03050703020a17060105 72
    0xc0c030040c0d41a00c0c0101034030f4480d074440d1003400d5030368031441d4a040e01e45e400c2400000c0d0081002d10202440d00c8050a080c0b040d03110101c9400a0340c2c4139904803001181c14441c082c07040c000aa254007001e00d074041d040c3d4403403085464210816003d03001031458030590800c0440101407291405045c00031480d41c0b03030380e201d0503d8500a4074980c03048600740f04c41403038050020515031050040d031610507a001c40e081d004124507024407849442800c00c507014081c2e00d0324000300052260f0020b5111324001c3c01010400c604514000074008400c04041c22550f2008401c20550300d1909290700c41568507040c24000d20440303e000c50300d20010034806030200004103502d901805155000850180c0d5607a0070b9a0010b619000e045403c50b070710559483c101c41c80030b40180300c0701003560f006047c1e00ea48005401d040c40d40710380e0303080c1e0704600440700030001642c0481c44080007600350140b990002d0389800c0a41c103000d10100001d0110385c03408440300c2e410420801040c01a4000c201703d80580105075078005203d110307 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 836683291 1250 836682041 836682053
    0x14030c07080c1009030213090c170f0c090712020a09031a090d0207060207031b0302210606041a04200c1e01090302060f040624050f030604121d0904 65
    0x40b40c000303405118156030000d02075225030548001c0ea41d00410418000d000034441100a04458904490310078900d0000f00d603100201c0d901c14089481c14000f011111080d1603210b00704403040d040e09000e040404c081c0328800350000c200356102c5040200058a07180c144000b00d6403850503520117003c00381030052020300c900e10034480ba48101201d0049070b0116203584022642e8060900c03400c0016001860113000007029111183c00c903211820300c07031803c991a600043d15401c425000d10107501d501d01c0001c11021000c0c0103895203c03508490410124051680c94456003004a29881c400d0381c0e05c0d80c0e1707045c4140001900820020035948660f07151a01e000e5180d0b610481810b141900d4030200a40940c1c501050041490b140e40c55806082e058a88003028030408078003402c1211031079180c10b04400040b80420f14079003500351510140b580180f0b08018051000141004d00d80a0f1300020100004201a40d0640001c00d035180b0300070001c0e01d126000c010401c0060a40c03541e00086c0d4401348024000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 836684541 1250 836683291 836683303
    0x1150611010e06152110090c0e09190305070b010b0a090902070809010806130e28030c023105010306110c060708061f020709110408030714030c0708 65
    0x2891000b00581c2d0304076214140e0b6080d088450641030594000d0111450503d416130019001d04481000e22100d40d00300d40d642801e000326000c116090303881080e98103108206920000500040c11042210300b030001d010707071702d03941000b101045083d540001ca40405220781e0845840e41d41200392002c0650b181c000c040d00950180510790300080c01400d010902d1809271003240c40300c80c1c0c802e60441ca04035500005403000782000300191f900403148070050b5020b18407402408021200ca0025220380c04400c0c0c1803a032540f20302124182628400b1080d440001d411500c1c48040310f03011240a00503403015200c5107045080240180d04801142c1016918010107400840c1170704c0c0300784800c4c400840045c000150314004d0f84281c2d41d20781e1084022030401d5005044080d00284050056402c1d103c1d05216a401800042e001c100140c0c0f00b00b0003009500600d202d010300c0d211060351000d1520303140c0b030910707580d078020340c0c1c1e000d081045003405018000c6400c0046a0300c0440d05002d0310903013580e5900c5161568 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 836685791 1250 836684541 836684567
    0x190e0c03010b1e21120301050a060c0521040506040f0305060c1c0b04020d02180a0603111e04050405130605010806060d030305060117090c130c20011506 67
    0x9030030405042030a203003034200d550850110103d42d42c1690043e42c1000300e441200800c401810059204120f540b0200380021000d200d5850f8030f65569502d444240100000c440e4007200130882c102d640a40000c80105082071401c03801010310341070343c280f2280d109184c0f046600c050b07444000042c0014000e440e080b80f00341200e0245040e603a040d981c1c00c1240b1700303033700c500844070001c1e00340103500411a80c19039100c00c0100740050001400c0401c207000c00270407a030007200018505052185036450503e0003000002c080c203024541448019044d00580d0034502131544010f441107080c49403d10800c4c2013030241c50083c04028814005030030810700505221610307990a555060a01c4004115041c00181017805981d0181c2403d08402042e00c0803002454044e24031030402c08001080c034008140303105010300840400000d44114100c0b0740801490404000f440400c01c2d0904d201c1c4c5602c0c40c0c003c840c43e2024544014400071005400700c08500428020702605000a20b004002c07840d20341c0080c2e84240c01d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 836687041 1250 836685791 836685793
    0x206030c0706062607051c02100521061f020606041d34030201020d0806011101050103110102010f0509070b0307110106141503090c060d020d050103060e0d0c03090e190e0c03 76
    0xa62101d09100031961103001b000d107d0450440c1d038100504151152400c1c140c8a80740140c1801c58a100c803501840c014107010f000c01c4036800a11010785400c103280742014200310010741a005144030b01a49070117006080e54415580c40300320300ba0b02080700d0300c250b210408840507100d02c49600b40c000c01d41c40003420840035100d1000c0d848445060240900c00054035016002040480e140450440d4031000c028421410400c2502070302c8140c9009000d414081e501c42e613a240c000e162200002800c69202841c8840000d09040a200b83e140c00840c940094070070401e000e60344c0b503550b4001a107040144901c0d440aa41c030b0804001002c90b40d1a02c0501c4008040307071800141c40c00030204102600081d64090300c150403100c8043c00900c1d10000500000a2111000d0305100b0040d0042c001c4400903030080c0c9810b903c59032141405141480110100810b90900c007502240c6130301c2c0144045058064405102544d80c04a080080d50f09040700001c90450400d0209248100c0c500752541130f0740e0301c9180a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 836688291 1250 836687041 836687053
    0x1003030f11071e12140613020a0b0307021f2a0e01210e0c0f19030809030a02040e15090601060212450306040206030c07060626 56
    0x1410344650340e44846400c0d16401892520f040019191050005401e05a200d0b218610009808031002c081d58201c6401480d502d0084800070040070305090380100750724482100308265200603034580840c081070700c0040c85a07503202c1d81c2d0f10704164030b841494240740400340b0f1032407032420031052103400582c80e0080350030200c1002d0651026000c00340c44408803240200e40380030146211548200e201c000100c950f1302d101981e0412200b503400440702c884000c111250807140480280c1e051418820050320000d59489040c0d9007850a03880300136070b40b070000509103034000400350103a6504005070b946e4541c00410810004074038032411540e84640c4404442c004903c080060745154004c11194101c981d03a8000d0300707511000d14000a1568850782d01c4a06000c44491a104400c207644002012141018101d143d0f0b0a49415034802004182385000e2080c0d201104000c0183c0300c21080e2900300000c4445540c0f10344181c074201018040903041403488070351036075000ca290303804000c4107480440620240c3c2d40c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 836689541 1250 836688291 836688317
    0xd0b071101020307050a1b06020a020309030111090d1203090501050a05070f0f020d0513171608030711010c05010b10050a0e0301090b060111030c030a050901030c021501030b0604020909100303 84
    0x200b070303010032213045020807001e014420400380207514112000400c43e0052521254981e1400c0407a080362210310010b038070200300c80c00076045c24807490065010362001d50341890202000100d80040128000f055030481402c2c21f04054080d802200e50990703c00028000b40ca8200900d90042400700c904400041d80c29640c0440540038001003521b1280903030140c007a456000c0700c1500d055011000700c4100c001c0706d520000d450207070b12003012011030f01c1c040508208151800a031040c54034940000b04e154000b080007000141e407a00c0b002c0001c1c81e00b801c0a403401c01160030240d006012506e00981c01807101c03040688816800b42c0142400c1c18543c80c0d078000103400303d050501300e812040c0000c040c044640042800341d0300620304040000c1c4401d08592070021040380603415500045d00c0240402d50104500ca080e43e0540501c20342c1085900c02044ca0300c4410304030012010381844043d0070107030110041102915103404817083d1080c06015003e060804842260001049110640000305440b040c90 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 836690647 1106 836689541 836689543
    0xa110411030609070521100e010b0f0a031e180b100501020a08090409050a030503010f0b09030a02040b0a05151c0b0117060a050d15050f071b020f0d0b0711 68
    0x10b89060318080c008c0302503c0d0103800c0001000c0d4240003d5030300d840c419094840540310b51a0124141c4188207010301d00071201c00d286007800e400c1c060006081c42380b642480c0d005902c500e049081e41d03565610903002c00c9501e40521070041e0444031051001c1380f01d003000303004001801000080d5855440d0344141c80d200000c102203010070030100042007840200400351000701003910082d450302d0341480c0041d444208202c0024402d40c5d403080c41c1c501e9500c48240c0600940400313411074910100042d80e05075650848607802401100034801a4240340c142e004107100b2003410f031100313040074070441d660b0841000010310098002c49540c4001981ba507814003140d141500a40002008024403011003003a1140100006511442e00c000e11502e05d80c00300701c44036508901900411522078510004075840446501d299001549507000c20902000c1e00000b0301402241c0c407129050ba00000170b807 = true := by decide +kernel

theorem cover : BRFrame.Cov 836510791 836690647 := by
  have h0 := BRFrame.cov_init 836510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 836510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 836510791 ≤ n) (h2 : n < 836690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
