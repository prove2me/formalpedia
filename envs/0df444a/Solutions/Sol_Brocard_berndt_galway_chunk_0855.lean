-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0855
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:11:24.144331+00:00
-- url     : https://prove2.me/submissions/5aa31d4a-acd4-44a7-9ca7-83033b70e631

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 153597122 ≤ n < 153776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 153598372 1250 153597122 153597131
    0x1005010b030417030613140f1f090b0103060e07030f0f0603030207032019050112020c0d0e03030903070b0706060e0705030a0f062106060603020f0708091306030803100801 75
    0xc200c810f40c2200c0300610744034425560361100c200280c1c808019100d0a090a42440080c4003d0140d5484503070007100c1c142604405512690002c0d00e03a4201250016044000b2500c20002c110442d000202201c1d0103040c0007500a403510004160b25408560a002080e252602c3e01290038a40c42040c2ca514502c0804100650640d0780094698499100c003414184003181c0401c200b582c0a911480d04040003418001c000c15000c1801510010038800ca48c08548400c0744020b240380d50f4021900d40d00340c45c0340a8500041c54000a03030354151140401c80d010712062203400655141007002c2406409a1428280c4803a40c524000041c1c90303003a0082d00b2040105002d02c00714542080617a42c114040500c041a01880569200024440c0e40c0c065680c14506801185510960401c4909024084c400502445841c1d50065040c0d100700180902c10404c200000c0d0302150341c0e00e0240408030001803d5404406182030001d00341c482c00d0700161462480082407060b0a001b00e00c6960041007070000900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 153599622 1250 153598372 153598381
    0x3010312120e07031b082406011b0b070306031e050c0d0c050d0f080703051b06010302090619090203150307080105010b0723060a0e1b06030a1d010c021005010b03 71
    0x50b2030308801c4c400100500e00d9a4101c00c0c0303100c100001c071005450018102c0c1e690b010700c2c000000701401d00c008180f140c4108200032609951290800905c2d10791480c3c4401c44c03015035907544c0c0c041010010144820540d40300300101c005070030004000e014000e030300b42e5032159020a052003070500c0d03140311081327100d103054407480d100060100320358100f110340484c0e20b1220307403406081c0003400c07501ca10401010445c00041410030150800301174502d8000d06103491414090901e0055a41c010178000a580704150600080c05031608441c54105112400300c00740c14660b81d089140140d0708266244505406450704050003810b00b040140010154400240020351511000080c581700342c803000b4000700306212a050346120480021840b0082d02c2003250528039110a500e0010540c11403464024064162038140141210429108800d002130166141d5240e01720510020f1603000e091a060464250150720a80400c0c4079546020403d50003400e1801c015448210440b50160400740310b13043c0500901 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 153600872 1250 153599622 153599651
    0x110d1119201801151701060503011a0a20010e01150501031b0e0f061603030603110d0b0c16020303040b03010614071101140405120a050607030c0804061505060301031212 74
    0xc5046404040d491102011407103000c0b12080c17000904202c2d200780702400001c14941c402d000707504aa0b2481e0042001240030318110f0036600c110100100003810000ca451840450380c0821940300c2c0384200009150322a0068135429101d8405445846440c1e141c000c21903541c040c01150390600d40d4210304403115000c00c0300500701904400002d0302900000292031001c1d00c8400844048458007106074410001350315005020309140e000440b500310301803d4010540c1050300145662592108500440d9600c050001d03c00b9080861400c0e1104401d00058015840900082014095034425187e49604000c0d001c2d101d5034040c6c5c44040024001c016034000b0131314800266050742400d10344201c030100109a40e41c00c900440d009280c1c0800030720020100004005810071850384074030240ca0540d5500302c010317011614108103441c081400c8100081c00240f031036001c2e0403050b501c8511300d410540c90304c0101d41c440d00260000c0f80e81507080303100840d00700d030000e04141d40400860002c1c0051020400c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 153602122 1250 153600872 153600919
    0x6030b011205071d06011d010507030e0d0606120308060307030201051b160f0824060d0f0b0709051e03121602030a05070e07110d111920 60
    0x960491401c0316664034100102071100100030a40001881940d050303080d42c103001d4280a035041d9002c51800e0303a0500388100c0c010384030040c00c103058440904010044c0c074140d9008107040302c440d511000c1100e407540003903043e124100242941d454502d48015044c0b81c054504030000e00400d1003030384034150400050b81c0c0101100c3c0109000214001c0101400d5503051400d20340401c05d1004003542d081c0410601220300d400c05c102d480c104d00b1541e11014451035400703207013490420807071000c01c86000a9480d007803588488401074420010b8002c2c04d041c40e203c0048120003a16084002240200100b040e850044080e581d40c0340f40401090501504000190b91801e42c6884410304240101d0929480c2c6100c5a2881c0c20303d8010b8140c1e034500000303181040c0c490807071f4042c500c80c008856000c07500842c824070075a6200e0b07582c0c030014031066903140e4056a5500302c001030613203184a001c42c040e840c2810242c4d403040c03162240b01060500000c0c10020000401c1030034000e4040d81c041031440002440b038404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 153603372 1250 153602122 153602129
    0x6020c1201050c07061107020d0b06030127060221041a0106020f06060436060c1b1b050d05100f0c05160f12020d030b060c0a1203020d0608100e0106030b01 68
    0x1c00041d088604d5400c84520b00403100e0195015807a058203005020241280603c074030811002004080848103607031104100f480302d000ec100d48802c10500001c0d007141d00404c240000e5550460700c1e070350b40564100138124121011200288204020407034001c0303800030303140541040d00140203c1a0a01c1d2001d0396144000c10f040d00c2a611a074000c0c1c425010707070100d5071090001005807003d1034011003a420411041c0b080880780c59107801401041c86208880501a00010711020742c03c1c40081d031030b458040708140c2c08180320030b000110005110769a4207604860350740705901030403015508006d403208841c038180c078408a16007044110282190702204555549401c03203010030900da840e0030b080e4602040644002c28591881c0038684d41583c00064404909035556000d02c421002c8200703018a500038400700400a5000c081d000740020036003140d4030031000203032900609200750410301e281918102c1c1d20800740c1d034110307414084403241070303000d856003070314840000f845460f20b19510010306460512 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 153604622 1250 153603372 153603383
    0x1305090c160c05060c0109110f011e0201111908100b07081806160507050a0f030311010906060b09041a0f060a020c0d0c050f03160b0901020a0b0106020c1201050c07 72
    0x18010070810031540440e00c0a0b00300602020785800c0500e818600031f01c1329070381c05d032108204d5070307800c0240746049440107000440603580d840120f503c121000118a04640308a0295501c80400200803089000580706102c60050050f142c100c001f0300140204070b002d000f110780341600c61004d101c010700f40f4044404980e40410710b9995041c14a0440d07441c011001070003644a4800150501500030441d401c80059000300156138a042d40c07281048608109846164840d966000040020034003d2241c64109404000081403144140d0340e5102100c0c4260407854504002090032106070600d0700c24042a490105999136100e801e201c001400858401101441820000b840700301c410310a010716030045001400c40c1021440318078103810b016849d40134041c05809000c240f0a45841e0002e100780078100c0203c1034003042814150401b00713545c04400c945d410340c032680e5504e00000d140d1415050003001c0b550b000d401044210410020503400340e00d04240560304041c01d001c401c4044400302e0744560742c000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 153605872 1250 153604622 153604657
    0x40308070f021c14070b0108120a08073608071413050c040b030f04060c020102070f0212030405090a051008070f0e1005040e0604050f0312130321021305090c 69
    0x5502c210f94044d0582c21200302c810740407070740008010760304e641681a00c00210603981040f19061440c001f43c0140100d6500103003007080812100f60044950400d03444960703030702c900400b40c0010010002503004070a1040041104000c00000038244010f00c0035001407110907000718140000036540b9074114050b00c0246940b80041060450501c0c211001000c65001071503c03481c042603075241c0e4110496065680c1070800501d043c1c414418800c50311540d510448450182c41c9503000e0181001102d400a0454441040701040603607402c0b080501c42c404940c00421b40380340840c8000000078130395100c1102944a04c805025284054400005071444068030f05003a5442c01ca9602d404a8560721031900320b4580742050507544400f08000d4450381c010804ca80410b04041103c1da030302c0c402d464100381c2d41100a0301158003400042400340300a070091906804c00c0120303070b00c64110b08016241e0310f80f4042d40011070384d140d40100c00840c402040308031440e1041d49801e408100407407090104059440c540fa = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 153607122 1250 153605872 153605923
    0xf0509070e0a090204031b051c06020f0c0102030a06060905060a0e041e0506010e090910050901020c0114010e010509070503010506090102010e01020f1c05010518070306031a040308070f02 82
    0x52284915181c8000b0710b01c461003550f03280b0f484000e5200380015203040c0c0c444030b10860a01c4021070f503507007180c0e00941412450304000340b26050201030070303074215006a020002800e40c07200f620042d00c054240e940006071380e820301d02809821144c00e50b00290034801c41540c00c000a980b484140d0350042403070304203078111640d4040000d00070b000000304809200f035101911503001c900e035886580f10b00001c0e25800c40840940c810442c0f034140449014203540d000142c154410340721134201c0c540089040317001500304100b8000c25804d50b2421041c0c0c601e5002050300401003a601302c83c0c042d0041006540f040c2490800ca04001c0c180e102c14001c05010f0f100000c0d0840069200358020b000c1081a4402151500d0700e40002c0702d074561003c03200240a140c40c207000b2074154a03610490381261002400190508810344109003e80d2005101500307142e0350341e400102080c030300c018103064035107070000b050715600c3e10f0719014040c4007000e0030000401c0325601c0c00c041c0e000d8000850071080d41c240440100da01c0b14 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 153608372 1250 153607122 153607127
    0xd06120210112b0e0405010503030406050a03020906120613090209010905070203130609090c0918110f0409020706050c070b0609090102070c0b0301050a05030d170a180b0403030c090f050907 83
    0x1d40c55900d84000c0c081c83c0c0c0000442c00040c60640316866a032119050000e140811060754801e000d10759054008110421056000b000241040704c041c0c20090300781000c520000d44150408038812011350541e1f0108980b515000011401da20700e0b40000704400d00c1c4503000b1810080e014023030310200641d10800f048195000300306403008520301d407114002440c0c48004c02400c040c190311600d83d0203818607a02c5040d131070050540d2010388040000d0705095000e2805007401401c1151549000c144003003051600a01c9000000d10142c11540c4002d643c41c0c0292a000c8120b85c4010200c40e0468000e0042c000000c04041225410080c2242c0c800c00c9030300d910104074024800d0f0000241143c00a5000003030344c4440b800614100d07501240c64030756071035888003410346400c070342d038148000540d101c0d13645a015601100001c0c0c001518000015600c060f5040c00b12008001c00402c1d100c4081e0001004101a4903014450f5181c00d5850f01240305442c1204103008503a49015039032165800d0070020341900d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 153609622 1250 153608372 153608383
    0x10206130b280f0b0405090c010804080a09030203070e07021603080a030c020c03011d060601050f1c090b042006090f21070f1a0a0801051207030b0703020d0612021011 73
    0x82c0015020041298007840307000c010240c0c648060700850408001440345480840c1011441c0c1c0182c464100c2c40d0b441380d4903100c07a98055100301040c00034200020dc0540c400300040000b50401c0314010550f03041902d40a0715041440f0b80030740351030f200700809200241000c000c1d0b410880c4a030034041102d02c484507069051100075144030390598030b032107018a8a490443d03d0406801526030903165240c854600444403807082d4090784040740000c000c000f0107513103541100c10f0304010044000829203555030b030f03540c0000c000b902d0a4940140201440c000c0403044c0380126580041107841074035000b2003401090311007410803649407080000d10031456109331000e40c1d2a11290280d0152072490f502d074070143c58201f071342d4010030140914901e658603449440008a03004012541c0b201c0351a6131074201003025003101490f5200c4d03640604000000041d05036a40180280850746001d600c0c2c0c04140c03c0801198801d501c2840300c1c01c0040020300142c1c03107d004000704180c05190801075890302501151501 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 153610872 1250 153609622 153609691
    0x10605060f2a060103020d150c0807020c1002060a1808040806010608070507020f100c0c090516080f070806031507030906050703090b0705031e010f05010206130b 71
    0x204000344005201c520440103010305030030ba2102210446614000021010401150114503031202005101518000e030784142168411030b8044142c07460415180159070b03078203a0045c04603440b20144078403150144001012180241c542032a0000b8008009503a1000075208001c0301c0d650700e640045a030403807456094055044a88669507a42d01c0111a548003400d1259100080503c3e01042a442c0f24000300c560709a0024442c052075002c0e01c2c1041250390003e0a64000d0102d240c900c074000a4203400448000c0003003640001f850700e005081541d04071040c400c28000c010b070301010400791042c0d01c81c40e140c02103010724140c500b80d698640801d00d842c000c01c01c40003290015200300122247d0680041044a101d00030a100c1900c13071440c140d082d82e6407090005c041134068400210400d10981c080c41d8040001d000c601d07582d0781840040014072000780c00016140320030781400d04c0196010040c00da0041072170040103010400d2a107a00a01140c0a0189464070741030003025548040202e8800541 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 153612122 1250 153610872 153610879
    0x30901120e0325030305070801030f0b07030f0f060821030c03130b0406200c0a02010f05091005040f0f0b0a0e01030209040507171014040f0e0303010b03010306060b03040f080705010605 81
    0x406620503115400050700f4542180040e0911001a840500c42c030442c80c120b0740c2c031200c0c0464000a590386c075100390340300034240310815a9491140001200e40c3c051001c07018030103600003500d5070030103039124280758400c0641040c08200e101108001d0020a01b1254024a1060065181d440310207400c0500d511110001d403c040b0410248001d201c501d0340000349882c00c11a402000b14036140301d002d0f050150f0a9401c0d03841e08001c00400c00741d40914070340010401c480c5004da10b020359100020340d02c42e503620441c41c00100c002c1418426951421044e00113010700a075000c031150700e0b042c211000e62040c0f55000041280d001c07a50705d0b007a402501602c4050b90028014449441d1003400103104003d40e0202c0c003c40214040411060000078010105a400404003c0c0c00c00c6100010301014010300c9240003101d9a41c1c0142258024040c00603602801d1741c2d2403903564a5156041c140c017a20001d400440240100300706200020701401c080710b0000f0740c050003103034840c45141803003401014a503000580 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 153613372 1250 153612122 153612157
    0x1050903031e040b0c0d02160506040b09040f060902090102010e0a051903170a1a010e010806040207140703240507020606120c040f06150c02330a03050103110102030901120e03 77
    0x81000202d00640200199401c03503c42300d1200580c03204048040c491030f44c005100300024803201542400811a00e40044d1002c66204929613485044900a07440103004980c007054010030344d03078203000d040200d04020008206207503503503c3d419260020070070300400e0070b2000121482050300801d041c1d2220b202c4030540c04018541000d512020340382a00c0d0120403214404da510704150f00604424682d0501a520004a580c0d8103042c00025404480155080e540c2656030f81d03080c541c200a10340285209401205214100d20003c51155061000300000f09045c40e0401c62110b9001403d1548880c0403030700c940098152459840c140b1710701e541b0b01c80d001418090780e0307a01341324180c000c101228800d40500716650304e480c030115104a89040000e61103012200301e1000e40c0329400d0b662200000100d600108404500b0081146601405030180401e8461004109006000b440200e00403801c1c0061443d2110020008050500039150421656503400200c809460100144d900101000b04483c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 153614622 1250 153613372 153613387
    0x70f06090b0708060d0b1605040b041509080708060f13140c01021c020a06090614010f0f06050702030a14120a080f090109050316051002070f02030c01050903031e040b 73
    0x2500701126600c01207841400810014100480310485454000000d0140d039128246150140d1032401e44440800c0418400443d2440e0b03218000c20040000c0540309164151103640940b071a106940030000366000304208000516010036510740c40080c403a040711007541d030f2024030843c007410b281014008a400309003030800070000080542c0a00c0090b02180c1d1002244000412039100003540b1100503000203580c0c00004e03110307030407021007644688004100e030040b0034248840342800340e01c02c10451140c0c44040105940c0d40d480391002d010203162a616052040d00429600c0d0582480241b100002c1c0381d1a0f1106001400750105000c070454415039141c002e1040203201480607280c0c00c101310840c0c40411801c01d414455580010b601c14082c40c14260b16040048240200d042d050795030b4011940c070822003198510040200c24419501da419021550040c54035243c1e0000c1103a060040c00c0054003500e40e8000151101c030501c02c2d5035507a94400211030100303280566800318402c1c54003c02d820 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 153615872 1250 153614622 153614633
    0x60608030703030f050105030c13091b14010c17030a0e1b040e01050720120310062705040b04020c03070b180705010906080a0b0d03020c010e01050c0d05070f0609 71
    0x107128080c0a0755040c0007204c0d0008031001214020300c075180d03255000034a04003035401d048645003083c050401e000142a0055140d000c80340c00790700c005600c0130102c02014040f400720001c0da052412001c0c1f07010065100b10b1740d9071020401200811445603c07000c00003a616403155003117120707550f58070008d6500034003a890348040c0f40107101400301d204a0816200d045041c40501c5000c3c0301d04816595904058803d070100c00a030310700d00401c40a00c1c028601910001181c0d0380045001d0030200b441809245d10f0324500408122189400388280c1081d03c0c50f6208024071803840c502942c0e0200c0f00007c4140b60741001500a10441c40008290300020400b5030034800c6c20080184100240040003564880d1400140c0e103802d094010075012541c101d9080c41040e00c0307486400e5001203803090004240c52035600050083c9140b01d412001a84181c50f40740741944d1081c10b2019072002820601e0400424042d21500c5030307031a0075500e00700403000c107100b402d011500021545540e00450108420a41804c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 153617122 1250 153615872 153615877
    0x50306032e110f0f0705030408060c0910030c0f0e13060311360a0605090907091107030509040903050717040905070804150e0f0f10060602010207080304030c02060706060803 76
    0x1a00601c070b180084901d100041c100860704410f80b52040c50b07151440304038040c0201d410048003a5514401803002050749003040103900c1c002e4100d41050354640c0710610400072040d0f8030b100eaa504045c200301f4140f0502c2d4000120380d06910860401c07000344140280801c40c020b41800410b03440c40d0030410300005000005407680e8440c0e2041e240f030b280c0101e5414040c000924a0090041d05140319103000c81c400c4040310545801501100b0003003010b95442c00040c00d030b15416101e031a20741d0094030081221400a20138000800140c1510134100100d54a0180a60181203481070107291070b0540f10040510410455130b4a50307101007969412444682c043d0305a41140c042c81305258075010116403001d00940846208551000c03043c02d11022403030b20344024101c0601d5600c01d070300c0740000c80f00d201c81040c01100d001c210200b0007009429a615420340680d0010340c400b00659104002d140e0104004804895029403d42000803410005102082d282d10032800d0140c031980c42d25101040700e9602000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 153618372 1250 153617122 153617203
    0xf0c170f1908040b04060504050c100f020601140a0302011206050d031d0405131e1e11060301060522090204140907110606130e0d020c0306100308090105030603 70
    0x4254107255811003003038580303407003c1e600036007185541c01c0020001040c0303411966000d44140165900b4034084070108051015828001c0041448004200001541004000e00409045210860300412100418900140da02000c0d04100a030486150281000d070071140040c0000f0f042d4800c02e142c01e080040c904c00618a20400c030800101c040d601303501c0c1900413907006040341002e2400541041d650b40b8002200c001c0418916100c10110b40c020846c0b070780c03044d510000100e02d451b1104442e442e0002200380101c110500c0740b1028401400b59682c40001d44940d1901c0402310140140030200b0008010700d40e034009058240005000b280d200c045100c0c06280c41410b60300d01d80d190300c0c0c2c0c2209907071940d16075000c91166448040012158030301036080080300c104400000038191271aa000d9420400c0c01c1840c1400f60b40b0069100d02c0300d00b41008500d920699188078030450509650740c5101c2c520a40042c1c81c104000440401c059039401d03c10015410042940842904030514404189151109 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 153619622 1250 153618372 153618397
    0xb0f010e01060203041401030b04060608011403010614010e1206040f03080a0902100e0114040b070b2503050c0405061207090812040b070c05100306050906040902010f0c170f 76
    0x1000050160440304000d05030380e5140c01a600701400d080e615140c44502d9203400d4100344d2144a50300650300c9511400018120a5481080c60740c10200d200c207221090308249c500030ba1400c5010443d80c0c0014000303070603100d404d103060b09a0020081c0000ca001482c20540700c2d06000350000e020411582180b00040d45200303440c0d080450391000c03001011515942d601170341100c2909800099140304002d120310048050401c0d011000c078900c401035042e0031a80002440b14170014841d0144085140b280e64402c06a589002203011500668209071480840d52000e050715a004210b4801c42401030340d010b0070000d00100e46547c819001440700410a407034220128518290101e10010f020603840341120010b076020340361615203100d80340c40c0c0c2e1000000380c94070103a00601280720394486401c5c03e1044c0b05960041100390511080013240c04015021900c5649424940b1780141d0300070144a041c80d66a00f45400084d0103814021241c0c0b0210040c040846000587d00c0d44081c54200500030228001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 153620872 1250 153619622 153619651
    0x40e1e070305090c010e0d030809070f0314070b16060908090607050c043804090606060c1205040e160e0307080106030521040b07030207050907080103031715040207020303070b040b 79
    0x10741b81700302414021600845004c501c070001ca4001c0d44002c3d04094418210340c0e001b555110700c400500c4e20f5410071180c0007070145425822a41c1080080d019003c54440b0528106c20703241029420003508400508654444038200c0511543e102620001003010301195511415071403c1c5484e9071b00344c1803062056191a01000800094082490b1a40c40c801083d1000140b110b030380e011000c44102001d94001d0b03c841018001850b940140802003600f6210b0060002c0d12d46841101342207850b201c3e404005051108002c0d8114001341c5c40c0c1c11082201c124500301c1c18508085030f4520705000c0441e090b03c41c1440018030400158090341c100d9001340288c0d0b5195104600250000d214041c02c00c0011500703200500000040300f00030b2080d5071203401151800da07586c42c00b2910702c00701142ca000228120741e0041062603040301c1c0b1035080a842100100c8a460f000c0c0c1c48041d9000030013a224003596011400900b15101001102c1e1202d400c00d40c1f104540c50b0500d05101119030071a0354800d82c8049 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 153622122 1250 153620872 153620893
    0x315060301051014010c0516060302040303021b01020a111908070611011a1009090f05060a0b120103030305100e090d110a03020a0206090a4106040e1e07030509 70
    0x5084200044d1622901120045480c0500440310080054416142d078091001242c00c0000080c00040040402d07880241e107403031035410040d045c2050b8203003601b10602e40a0580c0640d03a408600150318a620034029041c40c0e01c0400882d101d00c00c03035800c2c040440c03841e240100d428200018003204680c0d40341e0391000c030300c0c51400840d82038610805c684c0170400348003e91894a8a003101e03004211002510746180c00561329441c00c0c003a28520301d010040617540d03105110f01c900b0f00300c0200c000342801e0f03890286030450580500d0030b40d17a014400981090303500c002240c0c140f04030711652001010050040030107803c0c215152a1a00903a08400020a070604032442c41e115001c01c54003806074050700038104010590b028003005501c21002a40c4c00300c42d03401c0102d200420441e2040040c40c0021480040a00c0b140c030720b001d614090500450108280d24032990f2594030b0030102c500303503400c9810078042a03d40301c5100c99400c00e603945500c4140f8042d41003200c81c50f1f040c4d200d00c0c42920300700e0488680c44034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 153623372 1250 153622122 153622141
    0xb0a180905072c01170a1118040c090303020d0e04020904060b0c0705120d1409280602011b03020903211206100801090c09170c03060901020c03040302130209031506030105 75
    0x20340c3d80303945001c260b902840e04100f15543d22680d81c080b462180200d0b0366090055280180d07404504840c4c80019850f0b410301d85402c042c0704240ea5a15617040c4004a10308648002e0f646004111100d010030281002101e6583c40e40c1d01560703c0040301410521003951242022592a001111503a030140f0806400003054506584940d900c42d948a010385200341d01da1008980c11114880c07103142d1100d00300002a490349131404a400c1410307400e0807110140c2e80300c43c0280d1613400c580d03008404580c180080c09046003c005414600d850f0745050050760307864020b003c241011030104014103807448078503c40020000da44000c140031666000e4582c4c0e999a9442007213810303a1100109070000d0b00303140042c04400d095031b1000d40106098189807003140e0f611940301d068070544c80d40755002034120586503005820100700d0142c10101001c02541002c3c0f2078869959240601e05c03001c0e2003210b02c400c04101d40e1350700b070f411294040b8026017600c4140484002001018405403800c0d4003039843e10300000c62414 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 153624622 1250 153623372 153623447
    0x3110301150303320403050f010b091317030903030f0703020a0f030504030e0d06020c0f010501050907180803030a15061b0b1b0d090218010b0a18090507 67
    0x4000d01d0301003030507608588040710440304a855080201804a501405200c0c00301c040e0255980044081341e03445046140c0700e402c1400303040c80c003e0b80d82e04058020036607a4401040301c0c0e101000d008080804480fa00380031000081d501c901e0f0f1000c240001c1031010144012000310302c51005811441388588546404404074810683d50b40001044019500b000b00c3c829040540c009009140c81c1d929044d001c40050780b03440b001030048442d558000f50381e4040e0310303042c0041450b1440c00c1c002048190314160100799a440000c107800100200d059002550003d40d0a0020282101e141101e032245010f8000070010001d070f26508411503403400000900703610900002a404800540e80c0300006c40641e01c0d9030381d456026141c1d008440003c5948500c01c020000541503c0c0070b544000b040340314207801440f02500300400a410009503107001440000101c2089405001b014540341a6004008a0388614002560080301a941c180301c03c2c054419800fa40c50200c460540a0420b4082045072104c00e140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 153625872 1250 153624622 153624641
    0x702210301141302160314090a050f1f02070302152803021c0b040e0105040b0c09030c12030a080106030e070501110703061107050c0a050f0d0c0e07030603110301 71
    0x1a00420040c0201c0002010340295104040c0c02c06810742c0000000400340e80007103000351401800c0c80007983c28075a1119402e1824480711b0b0140d443c012100020070742181035406494000c20700d8160440d2907031210740c4070302140111610301101d035013000b4a00a403100003e20080e407080d02e09501150095031035100301d0300c0c1050307680140890810030595461a007450800100c0c1456070a01c0904c05841104d420144c852030300340c600041020015007084129070b00720080540b50307032501d01003200058100c13001e640c000c2c0c9810149900c5d1452100003920b1301e07801d020a59006400c080c008540c040c0c0000150500525607202c0140aa0329074804508440482c400301e45140d0000904200c4e41d4000c2005120742000c200658101680720303241c030000e66103c0000071420420026000d1706211050100300d19003201200d900002500c0e05001030b604e4162074032924444c0017050111400c100041c1d0180006002503100903e5a10b449030300600201045c0c88240c0790540c2c1b01d4401c0c08145010321854041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 153627122 1250 153625872 153625933
    0xf0606060415020a0804080706080108070e06090c071506092a0f1101020309030301150302030c0a030b040207240b010e060304260f0405040c020303060d0602250b0702 73
    0x41c50310309007100380c0729451000182c0a5000b14513504020400e804001c0010b0140080148406458804000c0500805a004c04101e0304289070600038000c0468403c0e0b0080c00c01c03120b003602511101c400450500c0b404c400241001801c0740444007844098001508646c010603081100040031452002c050314051400c03105d4141d9018036210341d030b004481a0b400b45540d4a02281c0c1422080c00307250880c2c0c4155a8a0748580c0044010080d109140d203c1c0c81a485c1c0322300d41907056040030072200da0315005045e10031062584403207040080f5112070f030541b58015000841000080381506a00d000c80c4c4080740d0101034a400d00e143c6a80ad54040c0e610303041d1002c4094100c074555503079519110801c002000079400c0c03a015108100c402d88014001400150020320042a511840c01c0200700880701400200c0007550018810048142d8403004c0c050b84017900300c5405a5150140c41c0041240704044101c0c00214901e11080018856a998101e210380030903000c94205146e00314000c0c3d0700007a445c00c6804e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 153628372 1250 153627122 153627127
    0x302090c030f0613020f0c0601170f070b0a110303070906080a140406050406090c061214090606130609020403060e060c0f031f031203020d0501050406080a02060f040e0405060403020f060606 83
    0x1102d0400032110a1008a004c4005003064070400845030b040d4800c0b00188807a52003c80103000144070015540031541d682e00040c0130521a080c2895103d0740c040c0300f481c40ea03400c082240030255025500400602c0b0100c4241c3c0e42e24507004101034420080c0707008400c00148200c001600507030301031081c030304803107202607240a065171540e03a10005041d000340700300d9115841c1c1c802c020020f82c08a8003030015000c2600c5400c00c8014030b07075500003261500f1700201c0c50b03105080e041c0b05e400c0e20302081031500b1240540340d002c03a0850f032091140c0074040386d0b4411103040740b0020707000003405210303402050785244103400d0f05d4541e107503031100a003580941c2c040000b040c2020008034165128003000341340d90b07000b00c070131000c0d200743d403174454400300d0168480507004203400244400950010b4421640905030486081040500380030a5641d10600120028010f03d800500f2025954000096038001e00404cc1588994503082c80d01d00e481c0e26080d5011409441007001c2024042400300d110380c03003940301400c51070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 153629622 1250 153628372 153628381
    0x1080f010b03030c030d20040305150c070c0b030601030e101e02030403050a0c0c09020403080304110a06020d050f0d0c05071401020304021807030902040906060501021501030c270c090302090c030f 86
    0x20001c25460312030382d030f0400c0110140c504030480380c7c014100641c01a0041c205040608102c0b640c12040204101c5011030200304060008412100480580342d2401c3d1842d1242d4401700143c000f80460182110a403190141c80d0003003a505402003689d1003944621140c1600182070107500340e01058070b008010503000c0c00760701185803007200c1010000340641002c01c3c200c0d5549400704101c1c3c1c400d400644440c0400401c000074099560030300c41e43d402040d90310346209440c10a00035144c880d101c80420030840009100d01c0e00f0104c080030307240d2a61200d4810440034511500c040e080f41d0068004131034484202660618601062090328452500540740f0010f038458078070304500c01440281514203040c0e845040c28056103e03881404003403403040b035002a4640c20103001916000c955400d091460040000610000c0c01040d40306080750f039001554880141d0302340c0a140300d01020800e01c0d05440c40c00315440d0196500080a80c1220b009890102c400d44445681c944180300484054202902100101c3c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 153630872 1250 153629622 153629647
    0x803030a0507090e0405010504030e0f0901050120061501030501230103020a090320150c1e011e0c030c050304030c0312020f0f0403060b01110a031b080301080f010b03030c03 76
    0x403a4412150719183c2c1c28651601005041c038002900d0685440e0b5599082200701a0064100720116600f05e5800e000e2958100002e801100d050261604200c410108005400d02a003076a52900c910642640d107a89840740780c10140c003003070001e89400242414000680052669084115821110350b841c3c4010f4080005401a5014500b51000c1218021002000c141d14000b0056820b0327004000d840070003456802c2040716031103001c0c0d40d01c1011040001d202d5031180000c00c031901100c01031001c0109c1814100342c41c0108400010a20180c00301d800000c6181d03070940c040d030341d801c40c0c0352405c2116555400c0b08850600080302c0080c08550195010700100340100b00c0c003001070300140b101500d40681c00300c0f05c5445030440123106014010102c0d0500400000d800f5036102c401007842c03e036412440407100681e855548500107024440140030074541c880c3e00103000c000c0700ea08401280d9403035a4a0285076550301964030001c11952034101c0200e494079000c411a031502541c240290b0030905d003903a02 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 153632122 1250 153630872 153630881
    0x1b090906010308160b0708090c010e3d18080705060901210609020913200307030b030115050319030f0f0c0c080715050405090705070f0506010305061509010803030a 72
    0x80c400c404003401d8138006803400c0000d51051a0035a2103015509041e0011132400c0103254600c2d0600440745c1d0b181005464402202d241e04054800c40d48145010000c1d04081c8550080c1c4410f55959458502640c035410503004520340b1900800301c1401c0c0d40d40c00131203403603c146016166200a04001d00d1401d5849421081801d40806501e85c682c07024032540401121002c1d070010b44034640100d0081e1952502e1078500f100c4052064080c03010751030410740f25442a024003c0c0c2007400c000440820615886580080c200480c064002c200c82e003a041d11100c0d601c0b030507100d0a4824420518900140c03c10700011091056058031041d07108039a03002c042c2e0f641d03183c04098100300901c4003aa840030643d008100c80082003070801030510907003048034400c107041fa4201c0030340500204101c200040d8641480e070607400441890034580340c40b00d500d042600c0c0f0000240151242c45214004418010086055801586020f80026510303200d03c09105091500340b1034002103400610019484100a801 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 153633372 1250 153632122 153632137
    0xc090a03061a0d140d0201020408031e040315050a0c0302211e0406020d0c1b030c0821060f01020a0b01030f02060702090103080901031a060a0c02040e07081b090906010308 75
    0x10140d1074054110101d140c0e60280d58007a984204e84001c0014032074000c3c0a03014403402a403000350700d40303820500074590302d01c54101101c900382071000301e040e40005d10400341c4000d07580c00b210074031f94090483e00180c0031301001d5070410b0015141514981d4071601a10865803200b00703074078002524041c0580c4603140b00b40300408404441152000c9002c100c039409020354030492280c0c50058581c103081701150100c4602c501781009004d00f504003141c3c0f40c88440c0e09114040d50500d0042d9400c019460021b02900804801d85802c45060f004810f501807206140c91145030b040d200c1c56104400c00f001281c0d91480032300060200140d80b0300610105122541c65140d0314000b4020928003035003030340802c0d0301a209034000c0d200700f100800c6d100815a80b41c05050443e046d800d907602c16501150300060301520400403c0c03014048254007010454a40ea0000000c840460003642c0c481da68802009840340e0820524100311400c07496003c01ca440c144101a00079210000208600e0b800d5640701f1587e58019a0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 153634622 1250 153633372 153633401
    0xa060906230f040e0a0b0f010f060903060507201b01020303190e0c060a020304081504150c02010b040f02120606030405060420041b0e090903160201050405120606090c090a0306 77
    0x4490b01c02450410000c1011707803042043c030101d4500349005000043c0184c00041c80751049850821295a103d0201404c0e00d421140021307482d140c0039015542000300074100d0150142603240d685900303c0114000b84100024072140f4001c0100d0001245c03684412682030400c0780140010b58181c00999000c0c44201006d2400c88000200c1c0c800002c01c0323604107104410040e40009014840d000301440b5104841d4880c58038010303113040654415500000d5040c003e100503a07503504c03d4090b18800d401826500c0e0024008000510090382c3c0d8001940c0807880c0100c0740301c448800b05015080c8030040340d10407504080500b03500d496654401051142c0c8a81c1c90901e8100241c050f02140c0e614410030b190b1a1004100500311028183e02404080c41012001d100d0f91150707041041c4404040100d4040028601c0740c0c070008842407005a41318042c54110715000000f502030960400000100540515003c0300d16100e030f50755250020303034140f003403005180d0400c8984008000296a94000030020b101c40d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 153635872 1250 153634622 153634631
    0x303090303040e160c0f02012a140d020a0c0506070804030813050a0b130e0603030f0705060619030302031804020c0f071505040e04121103030a060906230f04 69
    0x20000a455034205030402d400794500b03c4240710461000140d10b280c0d8800608280d00310088540740c5401d96814441c0182c14440e04110000b0710b09540c1e41407851614455410201204c0e250030421141c400c00c100d81d41c014810b144c01041480e000107804c8150b40d6015035007806403030910080c000c0c103030041030044982030382c280004800164200d0140103820503845540014605d80410081840299071207800c4182c0704002c0500c4e245850b40c800e905944080203003c0e102d07107413032010030304e588190900d150b0766140114000b420003802280c07480c0640402c44014218407010240703001c54040e548001009a0b0007080440c0425081103500800c108008000600b400d40c95622213041c400c85103241c401c2c039040a001423086000981e10f6142045030761424504103030424804581501c0043d2000d8103c01e44400009405881580002544e500510540f0786904104c940310010f0900d80c000c0e4404542806d0000c14003003001e40340c849000c60300017a550540c3c2da0604c01c2c41005403805a510350819207e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 153637122 1250 153635872 153635887
    0x11030604150e04050a17070818031c020a020414100911040f03030804170c15040203010908070f1104270201021c020d0905060405090708070201180f03030f051b090303 73
    0x540407110710a1340a600500b466001a1800c5040d1510034442410030080a0195002044503142941c5102400c105000750084c02c12001a10300716040109440e2002560041c5c000c4550120b0940b0b01288260307070a1002d850101c081503494582140d01c1c0c26405001541000110151b07003041712400380d40c940c80c0343307043c1d00c983c0703900101c41c500d42064003c0740c01c0f50180410003801c0c2c105428984804040d05041030342c5101c295884a0042242e1100840c0c1d181c041030656500b1750003003a1460f4480f50080c0d0781c00641c5840c0201d00403810003614140203a50050202e800d260280c2c010a2802e1914190302c56524014280010344941c002c0c1c1c1144034416922185001d101c440b48440ca80c00d8004110100745102d0041503030320b045d08024002c60b0180803c00054580043c101c1c1c10030032a0409102654812808030b0040c8407102d00b01030301b802801580000d07c40101129602140a590f060142102c6261244286e49040c2d904801c0840141c0c00380c4001943c80000d0300c4840801400d50340392481c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 153638372 1250 153637122 153637139
    0x40b1807030b01080f010507140a090b120708090606090a09032601080708010615030207171306121803050c030c10020a03180512090a03021020011103060415 69
    0x1103a40044541d100200e005124041040010520440f2900001d01841c602000020444045c0c9884a800e6845c040f40407003507a4041d00050380a42200c21915841d070290303400741444000305031180c41c04103110b8000700e1000b00d004600c040c460440a07080300c98075100d0009000c0206a001c5064042000d5001011440e41c0403951401901c0103401c10040d455041490041c20440950700c15011685441800c00591032081a808030215035810300584071016030030040f08001e24000c407030138203c400241e4455540d1520075418155840c6649020300501e12041281c1110360002010b280100414040c0c0c0019214400078005810040256814001034542c550707e407a50581400e8110741d00031031314000d569414410702084206030076084560107001d44500c3d0300e0714800c49026030080b4001130341c0d107030725200d2450005c0219806080501100f44100c4014a0b051680c884c006000c0700b2020b00000c400c105006803501510b01c000000d1441d107940003000010010100700051140322003200040292 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 153639622 1250 153638372 153638383
    0x7030207080d0506030f070e15010302040308130305010c081e0712090308010509070c171305100203030a0b0609060909100305060424050c0403020103090302010605030607050904180b040b18 83
    0x250b00d5004181420000c04150400d8400001060107511402c0c0400149801342d1000c4e41104040f20701c2400d50401e81d0040300a44699040605a00000130b00c84100c04140905942100d000e00c00806c84000290811202d941003500c0029800e203022034041000c107891602e4075007002c41800c01040c0100b401c0c0701d01060b144241c4013900414604401041035040c00084c05e544034190b440e0040540301640c3e00c8010410b401c00c4013a40b04040401c1e240e025502c0f514840001c4c01d4014084020060013400007076a0790b0040310b14031525070801c8980541405c00905458008000070451410320040c00c09000228100900d10881d140000c0b8001000c07490520006025600552083d414400d000406020000c2044010103e00e460402044039406981082d281a40c1d424a00031880882500b8201d001d00290340000c0c0c0e06000c0d48040c445802d8104004061400c004d070350a0041c1404440309800501120340080d0000b45034100140001d03044102c0103a004400ca54603600c140c0c0188051450036 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 153640872 1250 153639622 153639637
    0x3100e0a0b0105100503010608040503090d08180a0b040501030908040b03070e010f0806092d100501030609050c0a030e0f070b07111f1404080f07030b0907060c08030703020708 77
    0x25041090694148190701c0301c100c1c090901a01e00d0740203002075031001002480148594010170074002d000c42c0401200f0310460300000340c020169551110703203003403505041e441524146003d102401c1040914180043c1d10021280d003288101d081c02d2800004ad0080c0503540300842d0300d88400c22021404034103801c003441c003518543da658058225420300241928001030002014003580008204a550f90080084d900428100c0e0b01c0308111031640780390a110002224100c100000e500402c10680d40c24a40d14044520982c1c00b0f01500790f5861400e000c81c3d00580e101d00c1603041c10000b03034840600036004a28504424006c0700c18102c2c1c2c480d41d031030502e9800d40150080356000500c0703d0601030002458a03c1c42c204855500242c40380640d9411204102c26a100030f1004900b0851034001d11103050720001d1042a003a2040f1170b031070102032902c81c0c1150200726138400304a004105643c100160310801d503140c82d00c41d0f55100000ba298103506e500010b104030f04041d003c001d410009004030300500446c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 153642122 1250 153640872 153640901
    0x705030d050c0301150c0201111506010909060b1204050c030d030b01080f0105060706090204021e04050a06030506010207090f0204090c26090a020909190b01170d0509040b0310 77
    0x3511144000d9005861000e400d8140041c0140018400700e454440d000348250807605090800c0c041c1c0d0720040c0c1d00e05150b2201e185603801a011100c00403010b1030410352103584240d84000b1032a4507500b68400325903e502034050008410700c540c40301040b21800303440e0401d0141040350603900b004030000340b13003043d0644d200380020707100e0044091658200c10803e81200000801860541c1000049203c500030000040c1c04161034203891030a5444a0741220000c000a03d040c0d035004005284d0512994820700c1000d005800004000505900c241b00d03d40c05111705a000c2c0c001c0916202903031010345404c0c00c80b094455800c000000d210655803040611502c1076484d010304024220994a4424122a42c54102c40001504000d0807142c08030b91203441075411100341c00076441e410140380c0b401008601d10420003070340310440d10900000d00304080c129100d01544102c0f040304008401d4a072001c20300400c01280d4140010080e038541504130040c200390103411034504180c0e8a58120a807208076280942 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 153643372 1250 153642122 153642127
    0x40b0c0714060a0c06021c0f0903020f0105011401051e0a080150040603080304021e030a02040509150414010b0105070b0f06030f060903030114010e0a0b09030a0602070503 75
    0x104240a180100801d085a101e400d208501d6000703003000c9403440740108090340c001a09442080c100c03410200241030b5501c00c10240c1591802600100000103094001d8032404801200d801c405000b440c1c162800c10100407040b03a40c000065495070011288071480100303500050149030005800b5088001042d070b1182c0441d4584040e800708280d032900c1303003c15041e00d031700810303400501e884604650060039404c0c1c01c1c034003a0207024012010850f1401d243c0c07143c1082000424040054091801280211102042c002e001404030f41070b00094000c10380c06810200c18040503142540c4030700d50007807088040d14012140e8011a541f426403c4904440941524048103080c0509124440d440e0740c0a0a2031458403000340c60300c02d03d21500400c1d03000c89105040000e82c882e00e052104140d01c04031002103640303604140605580300d8100b401401c40701e80e080300c07028240e9807041c0081c90a880b8045c0001d903c0714100325280d0f41e294450201150544110003080b4001a0b1502c000c0c10900d000303030040c68 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 153644622 1250 153643372 153643379
    0x20307020a061415030d02073501060303091512051e07081b0c0604080a050f0a0309020906040605090a05060f0616050f010504050d03050402010c0602030f04020103060e090d14040b0c07 81
    0x2000c400354103c0140179500016185502540024410069802c1c0c8503c1e284205400d605005c0d980e8100034001071f4100e610410300c0070310401500610241d07842911001ca07241c1d213410003510800261a10100040c2042d0718003106011543d0040707401030004c00489101098900c40f01585510686044001640390340812034918401c820040c0e0801c0c001d04600e140c58225400d0310341c2c5603c041c0010384201c07000106108514001e4080702c1107124220511502c803c00210090020302800b1420380c0590b501d10001501c03482e25109450640e4801846540c042c0c0320960380c1c40040c00c000300b8040e00040c1c2c818400000749c0d0340e14050030303460000850030b9071141c0380c03494010b0a0003900144400c0d16030508080c400050b5001c90f80c8842802c162030001901d903141d00040b240141000805041c0718800401e00500189020780184110300030b8074180401d9603680b0005009050032a00c0029a4000c60b0140d10143d219a41060050001820803801c041c2c44d14120f803401c2e44079079070010032a40611001c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 153645872 1250 153644622 153644641
    0xa0f0b0c060f09070323160f0f0b0307030e0f011a01090e040515041109010306141501080606070c030204021b0f0c0a0902220e060a0f031203020307020a0614 69
    0x99000340144000d6240d810000f203450758500d400d000081500e69491320400c0c40da0141840720810036403100c104d40e810403440c440601c045040c1e0240c403240d03012029000c200d02242c29200740481e5420001c080c6150340c0c042c401c90040009040120850103071049249052000340200e02d605001000c0ca0b010f00000c882c00540790040700d910907170a01070f9001c100404684041018032a41130a2030300798802c0c0c1d4031481d1042000c400307002417690200b5203000100901070305901c1003d030040c0f110340050003521011900c002c100b500c1d190703050000c0e140000241c480c0c00c00c1c0000d0100343d482400000320a545980c0050142d802480e10071001c4000b50340144e100c440100a9034500144e84406044044c515402250040c0268010003943c10340005034450f9100001c509800400070301200868882c1c3c458025041601c802d039852849007103202c0001c82c91042c50303003154045903030040d0328415010000c081900650001012001075006d00302d4800d01085560007151401c00c1c00b40d46840240c0340c000d503003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 153647122 1250 153645872 153645883
    0xf03060102100c2012040311031e101d0c12010b04090809030715080a0b0a0302131506030614090624040302030d0c02010c020409020303090a060302030a0605010201020918060a0f0b0c 80
    0x401d41c0e951013175801051160000702114141da030002101141c1d247c0340b80c08646011640450b07030942c9400200703007005010003c2140d00700c1c400ca41805024180703208003483c440c1c0392020300c2100241c01107583c0b9a19448d1132070740500070f92065400450486c00c02000034040b20402c40d020754201000103104403542c5070074804ca0b000f50004182c05080340c0112500244040ea005140d101c0095a441c011003ca54540445000841d8014410000d00f2100c4003944050f2418080281021640c132201151160103402604d003500c4001e00241000b0600300c0070402d01c1d05015000b40d40240c216449450181c80d101c002c0c0c3c0300344140319030441d604c62851061500d800159500e0740108171030318400c000180ea00c18000b102c6590100e5010442c1000e9000190440c8142d8480561180107500006451750701600654400c91300202e040181c03030354400041e8240c1c8600e0100756071110041d298101018002403070160001e401900103c0c05589400d840c0c0c0510205400c10112480c000ca1002c0303641804004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 153648372 1250 153647122 153647177
    0x70314030a0f0e06070204051f0f150309060209030303070917030702060306040c030e010510060207122607082107090b03011404021210080706020d02030f03060102100c 74
    0x1503190110040c4010010301e24041c2d090200034058031180001ea4a03881a0383c0d850307030002c000700000c0c188407202801c0c002d0604241074807880240c100040614603844490700301da00144110343e8100c50010203c00400035440200c51130740c0e0074032200070151400c0010318032a00340c0703440e04440c16041c003100c401d100f8025040b943c0140d004020450060302c4440aaa400c41d0056074046914011110241c0c06885480e0030705015600e0710003040303229500a41e101e0212003613902960803860b2500e03004540c03280c03410700180240250b400c16141180e100b055414136240203ea4603070810a259032811440c1d8441e0560701004256440c1c1107041003032409000b90030041e6410480d040901c0c0c500ca104941c041480f6a1a0942d20561007414030345a2784c0448038840c2d1150254105498110355a0420b1321480c0a4401c0c0c5108200c00424001d0002800c0e03100c82040b0340085081071314000003016994030041529046024181101020022038045d81d07103401a96220921244c3d105075030798030421200715 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 153649622 1250 153648372 153648413
    0xb03010503060a0c0e31020301050f090411061303080403051501060309020a14010c06020301031401051819150504030e030607050403150b01030e06010b040515030405150a06080f0703 80
    0x60000d00b191741c10410019641c10182d45014401003040903181c4000140d06858042c0140c0c507070000020364466000758143c4504907161518640c100c824400308034000c4070028200300d241040d02c819440c1c980c02500d4030700503151001011907105c1d030f18048150043c0e8812141940049566a011030a08000c640035016a103410403101d83c05030001080802e0310710600800303c08140c05003040703910a1584c03000300c0b508080103640c0d950f500e10b0a40045110303404e0314a00380d481c02e0082a0040750142224000d25925401010480480c0e5600d419000390003130704542c520510000b0a41910007401294402c078040d03150040c0d01580081403504101c401011081041410041440018114a060404c12036500c1000410300c49400041e0001d0090000b030b028179111344c0d4000900c85001d40010b00583e082a5031070803280b1100f0315000000d0005490080c101e1700324401d09181d4903000b0528982c0b0088076100400d0340e135a00e00c034250600c240122210003980160006100f405145070302c5140c641c00b0103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 153650872 1250 153649622 153649631
    0x40305010906140c0d0f0b0d140705010201060b0403060209041803020c090105060910050c100908030709090501030206030402121c02071403030a0e0d1a0c0304030318050d180e010b03010503060a 85
    0x5110100803480f0720381704a007295580b08080c040680c0980d102a0402c032019050f030b4090b02141c102029805800c0c0c1008000b803045a40100d810752060007003d00721030306210250304260459444030041e40015450b41d030810382e54900000d0303600001144404184c00384c0c004d0f018240340e6105100c400c800503041b2501507541041600702ea0307203444c40c0fa800c0c0d04070140b402c07589400c8195441c40c2840f80c0c1849596415082c60380071001c5c80000030040d40921115243d4280040e5075826041c140c54007488040e40c4980280300160140c10140708030200340c46c0100685040b600d0040c031460300401d80155003001039211203411301420001d021035402c0b4210440c001c5040a140260042001d41c0640e80c0c64002d070a020280300c20002da0284c14890300881d104c0240f51342c50084400d10b8190801c4a080d4002804c124110490380c01c445034003c1e210742c121020b05288096204c3c02c0c0c0e080215403d421103181e40c034100016281c0114881c00303011b810001c854a40c1c03941740104061800e24041c16500390517240 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 153652122 1250 153650872 153650881
    0xd11030a061d0708060c1303020306010e09062a0f07020405011509080606130b151c0f090f1101090b0c061f1202010806060d051302030f0f1005040c05030304030501090614 75
    0x100e0070350045051070074507522a01c030011100047c00343e510080d0035104030710001c01c01d241e100010394401c402c081d0441e0466520700c0302c1c40c2d0401c00d2420780840c914560381c4920001c0c00704600241007840c4000300c8903203001c00a501150841c2c0c0f00360300094100f110070b0400034866a00c0840c202c000c110501c02400701b0705044000500c0803a110261030340995803225036140b9900d4070380408402d207904030034050b10340c2990202402ca000d40c2c0c0c04160b114616140c103d00d40401c036482038091540d0403c81c03402528a0f10340d1a03107040c41e4203c107850b050000b968000202051084002c1a1843c0c1c4407014205500700640300459a136105400141a10710001d000d01000c1d01d1740402c00070311a02442d05042a89885021a078103101d410341000c0c220741406d0030402c101e50559000e2051074400d801b203138000260f00310802d440c0da2206074410000c2d00408041c0c9060350702c6802882d0080e000e0107032414900c1d9a44002440c5502c503500488147c2d44911135007090112500c213280c01051010765801243c5070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 153653372 1250 153652122 153652139
    0x3050a0209060d0207060b12030304121106040b092503290703020307030b12010e060709061209020f060406021e0109030e12010f0c0c0b0a110403020d11030a061d07 72
    0x600000518195404240c8800303206c020781041020f044040c0c4401990140b801c0b503943ca0360300803102525200c10400c288010a440b445c00c2c0010088044058000c64403680c0d20070380c6920016280010343d00c074199841003044800c4804900c8c03a8008d09040064610394502040e140307007203289501948003c00c085003200004200080c0d40f04e072031480c0042e41c13070350740c944164003e1140d410700030740040310709014251501055120f00208000641280d40d60b0340c43c1c1ea0101c807a080b09001d0403000600704800418007040d50313001900400c2c40106002d41707400100000c221680c0065200304016032040f4840000340c65070240b43c68a030f42d064402444075450741e0710094484611b1042c218000c02c03022402c0c00c0b01c1e40b004e40c030000f0340c502c0a0b007042c480140488802001340440742c4007500e69850341e201180704204144292600c64a100c60650308145c6142c0801000714400c940030748036881d0070840c5846650301800041c0619104901c001140c2c85107052039000c058801450740440d40c0100418001c0b10b6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 153654622 1250 153653372 153653377
    0x20307080307020a0b040c090b0d0210032012011e0b090f01030e0f03030610051908060111072c0f010e0c0405150c0114070503040303020711030f070603050a020906 72
    0x603042059155261201c0030100d1030425002d401a00013041c3e5001d1000304000c500300401101c2c0150703824040010b801040140c43e07210007200a600c0b52014905002d541c1c0645c01c061885007440781c800c5901c4d000c001800d510b9501c840c0741103444070150401807155000f5003d80c200000300c1642c11503c05401e081c1d941000340702d07003030b20f00344500d00c1100c7c02c0c08141e20a4015541d45080350b81603031444062130201995982040c0c50f41449183d0002c0785422003441902603a1114076202c0c0b8540c40910307240c2d4192102d084c040d00690400007c0031080329811000c105510042c041c40ba0000940000450103451040fa4040590b1095903076805011003010b1139141c007030641d4103540c41a180c41c0c64103c0b0044c030501c181d41c0200d03000b01c41660f54200780c0e0005005090764203100e800030300c030441c521507500c84905400c40703054022400603c08500800e101c0d0340039103c0288507507207050980503944000b91404448403c1940f0320fa10604050101c41c4d410f00816400c494004e00c29800c0800070300c0010380d02d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 153655872 1250 153654622 153654637
    0x20405132004020f1603260615070b10060e01140a18090e03180d0507090b01120e0f011a01120f0902040510091104121119060504030c0905070203 64
    0x551240341c1c00c0065a495030b040f1103410b15105441a0744285203994005180c4200a0603000f01c1c0f201140080d25981c840d2401c60101c80200200f021942d400c0c1c201b004801ca03565400c07e4025040c80301c06c00082c80812614050200400c04d440d03840e00d00000185406468404641040000d4444460051400003610b0303c81c02d13507041040165640c81614906003c0603806070103170b01c0c2007800d81e0104280100c010440e030f01d07043c100108000e10200c140100d158141000404d60f5100510130403122800754400310081c401458411260b1524000c04030668850040d0600c09030403d0702e840701c041d40300344034140d03041e459403400d0341c100303e030a0b000a030508280a030782c8209262644950401600e9550081401d84da00034800c11490402c44603072070700c0c00480d003d81c91100b4907208050701c00f010880d050720200c6840980c6411a01508c0ea07400541c280391054041c1c01407000c0000d04901c03071001c5203400c0903001035035800361981d2031824010141c000591088602c07c0c40d090a001c0181c1d8080b0840d07002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 153657122 1250 153655872 153655913
    0xf090e1c08130204060b09030c0307060203030c0706060f0611061302010e010e010201090803090618060f0402010c080d0c05090f0109030c030b07170103060c0f0503070c0212070b070b0402040513 85
    0x1560b42c0c00088042c16181c006000394401d00d08803000c142040c15801038004c0d2078007038088554902042c0f05040c0c0d203840500a035030150b07000340001405001040024001544141804122a983c130b5102d1a03031201607812841c0403030aa16248809260f00b0407205501002d10a44802a0840c0c1e80000c1c0009410501043c1044442c40d10041d0a0b4000d4004074000795001b14880d64924103e02d165481380c1d4207075212040d99400391014021850300049480c011143d0b41d100a155445941c019a0442c15507034048035400000d1000082d01402c511800049100300d443d09a9141c072481c0c200082d824070a02c030756060280760720007171010960b1120ba40c3c0c00d130b076400801c080003511900001d440940034400c00752989250980080104806604001d00c4080c1584441c05072800f0040d09803614041140c1c610300060700d0341c07660740141c54400d00d00103a410303949040d21602926442c40010a030711543d420780745075483d8001d20085007098801d007a03020500d81e144101901c11551000c078140b504050917640d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 153658372 1250 153657122 153657137
    0x20712081005040c020f0f1c050301081203060a03081c05092d031612170105060d09080d0903050306120a020108070324060804050f010c0f0c1104060f090e1c 69
    0x803070080090f1b019981d800d80c100c840041d5041c3c280c0e503407101e0086508440010000c400c400940c0100c0035241a9001c03803020700740320782c0e400c2c040b12481d4100808465201c0d03031903903001010448440c010640e11807401090815034611010760004d03100f014008120740d0307007c0180c4d1400801c009202400b420410310b8445601d04003000b41d02d03e98011030f00000c206095200454040043c192900502c0c0c10307171502c502c1600c400c2914245090407003441403540180003000b0100c0b0551050740070010303843c8500c03086803c2007800c0440c20229551210304802080001041c0040d83c03806042840b04803410800500440c00c003a400201980340282105091584900701c0c44c51100a400561300b0401100001c011003580d00c2e0801800d40741c00760380a941c5030080700304000a041e010f002d4044007121940742c50b02810b088080c215150f00c04003030309444440400d903030580e00f036980d80100c2005010385190118081d08085c01c0c03a0868a500c2031800c1240d002d100b1003603244c40b0b2821001c209110034104440e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 153659622 1250 153658372 153658391
    0x204090b2b0f060b0a0e0906060405010e0c1606060b0c1209030304050108090f0d080a0506030607140703020f031617130902070609021306090606020c060414010c05010c0302071208100504 82
    0x3000c0c00f589113500b070b4031800880010502c3c05402c1c10007489640d01c1e808172001511240d0500c01290001c2c09681505204540010002d0000100505140e241c1840103d190700054403000d08035030080d08070420885c070000303003002c1810b0100083c2d580c0d28090400c4030710300f00000300026924861446200e0502000100241000b2070501030303603040e403001c041622070b4140d209a00829071344044485148562414002c14081d00300040d10310301c500b5490300e4009940c002c05480c0c00745904507910850461040140c0030300011018405007500401041d01200645151729098400c00c001c4107044200450a0140d510040d81c040d508000325070f02601c0040e5110210305050001c2c00d00e22002a42000c1240d50010040103d5440101290190a02000429103030381c0100d8036140d121244a6100c1380c09e2100f44005003018000c081d401a0505041c004410aa56070b00d080d039031100c0003000440c0d40840c1c0c15080c4800c400381c0544008481c900503466161110414a800e200d03800307030034040d940e181481c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 153660872 1250 153659622 153659633
    0xe010501030e0a0611090108010b160209101a0406111b1905060a0c02030c04020408060f130c0b03010312080106020a0f110612090c040207020907080403120204090b2b0f 74
    0x11110f07603401941c2488511060901c40b036040c0c4c04000424000f540940000948002680945840302000b8907a40c0c103440c51902046524200506921a0f800504200049481244581e0b00c608040f040c0f2542e00c0d61b00e030070005003041015040140b00303600002400f12100340708a101c0c00c03543c0e034200c0e0700300f0790075040100321405040b0796027000741c1000f0b0003d8070364061038015a2015070030344210101c41002c034110081c80300340d02491003019020b60049001c10980d911800d80380703a001c2e01602c99828283d043d521041071701c03400d40d4411901c041001005100340001c0140b880c40b90b41c0107040100b400d51402d0b000954520500d080030b00007070f0008840604001d5500c60f0900240d100070034540d02c3c2e02814840200038801910b5601181c490342c007008403941018001d4825070303a001021f50303071203030b03608102910000c8005004508119100241030031807c40c0380302401c041c064030100000d02c070544500780640c41c04c1801d400c0501c2010008119030180c21000003a507186d13445501d500040c0c4051524 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 153662122 1250 153660872 153660883
    0x7030c0c151b1e050c0c06090303090607230114070c05120a0e0906031b131b0c060507020a02060406030f3306050304150b12060405010501140a0e010501030e 69
    0x24544101420b90304520707069100050700d0a001c00c03600808035014060700c0030340300d81c031912801d014a50041691240340e860000040d06a240c005001d9928019603140080d90a50024400b110744100215036241c1ca54000f40300450f0400101000f000403c1d03084184c003c2c2c030780004001c601004a000c8403081000701c00d02003000d00c51000051032b6224203030004090400b5001d003095500a48004000810038500065158000c402100b21520385910711310511803a4030200d8480c0c00c01c1034560102030651031030081142e941006541d1501540c81031444c01c40c0c1035a0340505070f0800c540c81400103c015a46040855044404038100040c00126101107140540085c00b81d1403881919200301410294140840380060f5480302e0412220303946034203003070b151404150742c09808c8c0b00c1803c8119644800c0e69212520b4042c004154900c20100c44002d10315000d400c4608807020b9465000401445e003035400c00750380403039040314a44209420710300b40240e0600144217071030415403500903442d0f054406101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 153663372 1250 153662122 153662141
    0x60306040b0d05070812090a17070b030112060e03070203060604020a03061802030a0c0504060e0d03030204121506051017060d02130209090105040209030337120507030c0c15 76
    0x140140010380f420a181c8800c080d21443c022130280d04545449a21090200c51240500501c2c801c0740c541491108015070100040e0384100d84a02e80012400c0c10407000514001c020120603155600c85514101d803c0d95181541e048199109021040c010303903021070402d40c450030139100140c5827500710408601410f8268001c2080e0080301444107000c0c08590005d602c603591601e0107114200b0121000c403003074801d501c0340030000380c801d10101e6621718003401c3c2c55840074080e1502500746a02c4002c03018284152040807501d004400b0524241c030700541c01240002c01c01181c921249085544000e8000325203035130200c0380c501505001420958603405800781058018203a6001d10519a120000030740c44071081a100f20440c41c00041e45103024001c4850044000e8051030800c816034001102c12100002841e4800b00d0300401000c09204035114200000301c07913580c2000142c0090034840403960090150340c10141000c2c8290b030301e540c12290b0380714a59840301c642e0450003400841c1c0c00c01052140c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 153664622 1250 153663372 153663379
    0xe0f0f1b0d14100605120a020d06060302130f0b070f140a050304060806030705010c080c1e01021c06080a12170709050f01020d020606010e060d02121009050903030402060306040b 78
    0x9208007600c502688003801400880d042104682c9440c440014001854404c2d103001410401c0148030361080610050b402c00e007000c1c005401c0c1406072900d8001d84119400c15000a54082000b40c61482803060403401084900b1781e0740340c1c00b070174a8011040c52040140207002d85904070725207410484a01c81c80c0c0003803860034003526013401c46c0f40b8025850358000d11902000907510f0022420500d404690041140c905840d00d8440c0d000e180d03126102d6400114000f00180115001180003144100301034015045031000142d984541b450000640c4196000031001d540c0744c001c5c2448030382c90000300c10302c030a1340040d00d0080c12105c690003140c5541060304c010702030385000018060b006803c24400c1c019072300119249204804402d00481c3d54842ca507441c40016807105000c101c03254082c1a40300079082d07014098520705051040042c0c11383c0d2081690316118483c20b0100103484200841c0b18000d000c070144140140d0409816084d5217010180029124450010104600d40d40e140d0000c584000081c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 153665872 1250 153664622 153664627
    0x5010b0304050601090b010c0605180f030c01110903070522021314041404030e0a120b070201110a0c060f02090301141b0717030a0212010b130e0f0f1b 66
    0x4616600454105480842c0c2900c00c140000c1a05c22650060480b59003042c0c1d1003000800550700c80b00050403014009da0071480d001c04a2480915050101240121651005562769402c6402c00c07401c580c2c40c800b82c000354101c01d00554980d950003080a4046031000c4400c1510080445d0070034030030000d01042030900b140700080780010860b8440c0d05100f19204040902c50504568060106407240c2c4214030902005000004000030700072407100c0c1a00401a02c90901980c580c2c045c1c1d1118100c6407000d0300d06100c00020482110340c24055980306428019041d03081035100a4060416804010700074240b030349560910140d880c02ea81a2045d00000400910a00c2080520900380d0b90301621090051f8004c08070700341560400c5001c40300f0042c1d01c00c64a40c0841000010020b00e42c0004d0040d40f0712580070490f01b4904d40310f0441c514045d049010b50701d56161030100ca010186c09240e40981c034891015420400f981149084150b40180c20030f204c0f510720382c0c0e04503810326511141910b014440300c02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 153667122 1250 153665872 153665879
    0x3080c03091c02040c08040b040f0c090c02070e10080a080a03090807080304030201110301050f210d1110091101030504050106030506190b040b0d021504030507032a050108060607150501 81
    0x81c80c800c100707034004d079002c1101155940c0c0c1110284070407140135003014101400b040000d1154000e56040c58010340086200035120842801994058861240160b01c030b10014007445a074400c3c41313a00b08603c41200c44e00503240003001605c81c1c00e000000b601103800400c15a0b4402d000390844544503a01c550751541c0e03450300c6d01e4400d815402c00c4e1000d90041d0b103440182c100390b901c480120384c1030b1407008083c41d442e225001300b000011001225903043c810074000980c0c514078000c1110381031400c283d8448500044040f07030403a24000a42448010150522014001080c404c2c40d20160030300082c40c02041e0303035a80b03040c4a0b0241003e64801065841107008200803038050307060821350400000418401e2502c1c0004100c19a0604a80b02d540042d1450303050006240056840201c1c1c0074034a1098203059480e00c1e03072402c10310745600a49540103601c40d04907810450350180035114001d10030703200c181d13404c100c00240040d40050410340104400039880c0c09101c403400d500002075080640600c40c641c0c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 153668372 1250 153667122 153667159
    0x1212030c12070e0109150203070f050631030c081b07080d02011401050d020a0312051b1b0111120c010204050109080a0b0606090d050a0b040212011503080c0309 70
    0x7105004111280c03034880401c0c00c961188020844909059540840060818a100c07085008000410082d480700b0065000080c0b0b0444800109a016030003404042c0340c0380070300d0b0980c4150208000c1c4020017180d0100b42060500c1c41c005070341c40d0589005035036a40c03030b4a4039419510030045082e050b4520441592403498000580340e094070f0307200741610314034010640140e00741c91941c078a605840b003070302e40180301303034140421030745080c0b8001011440d0301541c9450f40124142d4441c001c0700042c00000c0c040082c0000034410002c00403480b402005807141104650007144140a8864100615003802010f006020041c0c901e031501c0d00401c080d510400014054001d5000b8401c440c0880c20740c1e44001081c240c04039240d40c8050f000300d500c40c0d8640d0340c201080346541c000b24072507500141d0016800040b4908200221400e40720b101c01e40e490b82814010071040041e4480906120f82c1080d0720b5001410b8010002400c99600044180d00d40320b40f91001c504501407409160707003120000c0200580c01c50b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 153669622 1250 153668372 153668377
    0x60d0501021c0b0607031e020c1804031709030307080406020c0316121106010b090d08030a1e020c03040b130302221a0603040f030e090106030b1c111212030c 69
    0x340030100402041d0360083c103004080c000d00b00d0103001314107229003540c58040d020b04011000c000b02c0c4140c0b24000c00c0400002c01c028460301c0117845e038030504402c1000b00741d00302201c00e0f007820440b50f170141035280c44440a0394900c0001d201c14200851100030904202d0b0540603240206010b90640341c968100c0302d121884140c20031019500748008407001000302c0e00988030810405907150260000d68200008454a5400100d449030415080452540818807800165000300341151000c51312010b0703030184010fa401c0401582070840e00c1007240c1030488100100301c4045a02481c542d5889100c051000f184504544e8006508098042100091950f1100c001c011003540101c08022400d0010b02e64401100c1030007900b074000030204041004200c1e00080c0c00d040342d1003440c01010410014000c900714003020307442840865203a030620040d52622020040f401c0296003001c0c2a6a0b0441e113030a041405078140c4180507003113240c14514544003c2c032000d80d03a09052826181e880c14004600350055 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 153670872 1250 153669622 153669667
    0x4090b010b0c070e1509071e0e040f0614010e0d0f030305070210020301030519020d05010e10061a0d110708040303020619090203070b0c012009010e06030f0a0203060d050102 76
    0x1070090500100381910130007012805407a10040c020020b04031601400442540506102c00780401c0080c00311010714208030f4100e0091031a41d51581c10030f070b408240070a0301c241c0c40200e070049060040c280045280f2540c000c80d90b407000d1030454001180700d00464a640b94845000d808101940354460905405420071802801d003517007118004010919820200c2c0400c7c007000300380c2d41045910440203c41c0c820621469400103004002d840746540e20316003165142c00040d20550000b002520b0150320300d00c241c000412443d81690101d0440c1000e010603481088460103d03e0395602d122584c1000c443c007540d40784c680c40031b03141c0d0380ea50300c0341006036030b0303640c02c0300d50a840080681c944000c0d100036000c1c60489d00d40c0940201101d41c01d04450300200c3e00403104000c0300350b50b60071000d000314103205404442c4000e5000455a100000800104184003410990b4080c0c1c0d82007043c0281068800102036210309030400058680e160100000c104c0304401e18090000c2d800450136860061014540b801da1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 153672122 1250 153670872 153670897
    0x18060b0a05010503010312080a1409160f14040f1e0b040501150503040209060f04060308070b010e0705071209050d150b1002100506041d070306050c16030e04090b010b 73
    0x41c1e8560044900340700900001b0813060494080f460110b01841c2c43c1c0c1d411081d00d94011483c1f00a00720031075000d140c200d41c1b410300790707004002600103aa100d61000e0b010344480e445080c8041d00300100b0b102164940c00d00503001e150b5501c940e8003207000503440700001031600340c42295031400c4000380802508820380080c0c450382ca004000104441d174100040c403600c00f140c46a500303507950b80d0200101a8802807281da00440d1914000c001030381d0f035204801c061449500c00325100d080310304001502090503080410704101a0040c8100c081c1c100065500351680403036031100b0402c1e4031a040b500c3c200d0590050740c001e90004040810024480d50030503290f03105c00740c1004034080c2c2004111141d0320340380841e000b40e0802041051404d0b00c5030032280e40420080c001050152100600d6803003900484d24420f03c2e500a440d0900c1048940d00803c0c3c1c01c80d01f142e1019040131316150055041c0e0109540040038018440480a03c0fa2101d41194444540050800740d9942e035811304100341ba03007e180403101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 153673372 1250 153672122 153672139
    0x50d03050601030b0f040b1201021603080c0721050409021b010b010e0f0d050717010203040c0603050c0307080a2406020c010929040e0a0902090606070506040308060418060b 76
    0x300e502c84e104102682038000c000072000c0d0421800e00c001051810f10340c0790851210351140b0700000c002d000401c030545503841c1641c0407442c541002021990060324071105030804229100120300e9000100703040c20b46100d0343d0403522900c040252040d01c181d5000303209940c00422026218800c1c0c1c003110101024101c000d001c500b408030011128040f81e001c3d000d510440c0c0c241e8075446801d051500350f011310f11550071601c4154848244d2000b0084040304000305a400008100030441082418801071840342000e200c20b04200c10210300310300000b800d10082288540000d121008281c02c00b0f91003040702e01c51210b400460040c003001100c200d006800141c8a020545405035104201c84c1c404c840074001205034180b01054601030045015610a151103400c1c000402c480480164050007500402c0700000c241c9444d106000504100402d024483c0703c1c18403e100c040340c8040340165010703a05103480519643c905000a0041c41c0c80c03030b4501c1068424003849000c100c4940c0c054030244404139440403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 153674622 1250 153673372 153673381
    0x21c052502010c1706040f0203090604031e120b01031d0a021f050403080a0201020f120603100e06040212190308101e030f0f02060f09040608300d050103050d0305 71
    0x20300782c40c0220081400580d80c44000094a0001c010315604208000c00c0810f00403281025901649c109071070000e20740d00714500744810075070030003038a101c07070300708410750b5000349440f2a0301620341d00c040120824032681320f01d10006268840c1d4440e07002c18102031076030784841c02c004145590f074a1546e0412805114404480c140864090903004450401651103a00d49400d698800c0c9c2039400c000401c0d0155034003480b41030203048000014241403c0c80e44142c50480c54060704240c50494824030703032103070289808810001e0326400700790a036000b03806440c0d10390000381d01080140f07040c207440008403804000701200d03030402d980040721360301400101d550412030984407407901d102410640e00e82c0a5802d0780c40000c02c00a01c10a60b6142001c1c020030802d502c031903003600032500c1540b0020131110110390000f050000740c5001e02c41e9030060b02142c401820f80c1003010382c085405c3c210300a0300d8103030300600130500040c0d04e14603401c40b0340a1100a00030720583d65a0302d001680c0344200c050708000300e0f08100004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 153675872 1250 153674622 153674627
    0x100f110325021b010e03010f0203180127140c04060602030a030b0a0f060f110718050f04030509041d0a030e100f120c0513080708120c07050103021c0525 67
    0x41c1d0b43c0e03001c03861040701500704100117590044403040d1443d019500c4201c0d915885485101540c8686060071043c4100380038940c543c1d0841d4512902021614140d6012401450003164408a0150f00403400c0040c80384035400e8529000d188014650f106092030f001003001580840a04101852900c080c000d0918040405c9409003080c000e60707030034006840c030030004144125002410407036942015808051500c01b03040c1040e0203a003200c45900290b882c14034403000d00d840f850342d00000c03041404510342040c1d58018114844d2018091080d519109541e00c0c2d00080030001004100700c408a441903941490080c0c010400c122943c0d104660907080046501e005036185045034802e56070f00504000203c14000003000549a880200081030040d001d64404101280740035111000c010483e2a20f031040161a05103d802d105810420910099880030000111038064950900700544c07076407882e0018202c01e8211902e07060300347e400e040a010304001c07042650001d01d01034410a20070200c64580c10b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 153677122 1250 153675872 153675883
    0x61305010f05042a0f0903050f0a031d09070509030309030613020a0609060503060105070606030203060a05010f270515060d0c170603030304110f04020f09041d100f11032502 76
    0x49851054448031580c0f13400e803054100c40c0b00c0005600748400415184d44540d4640000d41c80f050041d6400b0060b820203041d040107410041548194103e441402d01e0000719900c280054810300a00c800401c00c0b41c1c80f56024000d0700c44140c0b0150841e0528980350520715401c0c00041007e9018811440000c10714900c0f6824003000d58034142c99851460f121007004403601e500181090300c0c3c0950314280400181c0d014042980030b000b50032404565541000924401100030b42d015a040c0f1507030301031000c0342c07a090801c0e440c1030706c00883c0006010ba50f4a0074201d54201098800c681c48500040d01000309141a48524030300500d640d074002c9610300c0244550003041c42603e806525910070310004001540da030000180328440034000010001149001c60207982201c6924014044041100c440500f42842804031000c412900009019443d0b035003d07480300c411200040c00c403074882c81a0008108643c002e0403101d55042100f81d40ca180c004800740d91003080d0402d026203003041e1084050040d1002a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 153678372 1250 153677122 153677171
    0xd02031c23071a100f0e040308061c020909100e16091404080c0106090c0e191d100515030712090b180c0303040303020a03020f0607090e061305010f0504 67
    0xc40c1c0c065081c003610701c5441c0e82000b881e9040c205480c0c41c000c17685402e8000901c00070401c02c0c2801c0b0280c01c1031b2902510391013009282c00e00a003042101d6541101500d103618141d03d0301610045132586611034400e0a01220301005803003d8281480310b50070b080d000403201c1c2c1070100c1603c00894183c40720403200035110742514500b4800c400b00041070104020000070012444160000038810f40d842a50a0907141c054403070303034080b44403181c02445900b4280c0303a001d80700c5501c06c0f40302c6185042042c940d2405540c030036142200138152000800c16808262444080c080040245401c403103004480d2010307178401c44110002a580d0050024180700c1401803802241d4849552602da554142c001d002091407804507031110b110380400a00d250318148000d101130340c060381c00782c842c0409604000c0e1601c45514030b80c40c12030340000d080155003640480070009548aa24249440f038540c14000383c400d00d160045d0007202803908000240c0c40c2180000c1800711001a5010720050310020140b503880e032850313607 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 153679622 1250 153678372 153678383
    0x501090f0c090e1513081b0c01023f070f03120c020a080f0a020a0b01090218030d140a091d0f0f100603050411030313140a03020618010302070807080301061403150d02031c2307 77
    0x2096885040c14100e2104032442f000316585042c140c0c95290000c400401640903000b0a0b5408100241803000c1d00034014201e110340010f002d4104641d4910340e0714840c04005241810010481c40211842401000c0019801c002540110358442c01134078029441604520744664095111007040d06012908000091250715641d0380c5480c1d0030303940c21041e0b0011147c40108402040c0c0441c0403490b0301000c00c421883e050200545140c04049200703d18805850034224040c1102002400e0742134080320003d5800303519020865840e10b01d400c3c200400d80801807941404086420032403040c00c5e401e044203c0701e00c030030f43c2c010741c8542e0301c00d114084400e8080031350418410001d00c01081520032140092003810b25005280107025203d1084642200b90304480b000ca002004200d80c0390b00400c001036140340802c2c01842c60510b80c4031600c11020b608031031401352200b13007184000d56406100d03840382000819056095880300302001800224103c00d240b40003074450f034a03020100c00030400d450307580c0d0380300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 153680872 1250 153679622 153679693
    0xf07090e0a0507090f09020c0706030603080d09030201020d0e030702090c0a0c03030e0c0301090503270d23010606020d17010303020c09040501090f0c090e1513081b0c0102 75
    0x219481d00030340401070101c1e050052054000070000b00da40020002088086001600c03000481c3d40d0764180010365003c00d01309801d118040c40818541e40890b0407450007078a0000e0810b0072440c09902901400084c000c0e82841c10a20284221012008241d464070071a40494180d403261200c1d01c03207000e040f19801c00a10441442d0340041c0c0654800522203044100b01c4030030204400010703080d111001c00031241900301080220505214030000402406100c400d0340181d0780b04404503056810000c0c1c0980850004d1210341445003115035011007408680e0000c1c05415141e0034065a5001c41602460008203e0381d402205100240070b240d06913603055024000c2200322904100a03072101400944e05075503a6500301001800172096020a01d00c1118040c40380c4d840c0004080c1150103002d02002903400c00483e0180c0d486c2585101075001c4079044100c07018100b41c1c20a07503014040c1c01031a14000c000c00845d8079010b8400181680321400176070845280d03103508103244c8070036892190000c2004400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 153682122 1250 153680872 153680881
    0x606120b040504031d1f030c021603020d02090c090d0c080d0219030806130204091d1516050405030a05010504020f0105120105060d0207060f054c0503070308030f07090e 74
    0x11a80e507840015001040c240f105c446d40e0042040c0c4101e500e00150120b42d591034444038a41c0c040c040c1d03501d4001010350341c03000c962564000c601082c400502c001d20075044600001c45400d040c1d4147d80f880b04003e0050072601e0070134549a4856801c1c0d000c1c1c1c5816105140303100b080c00c2e1002846940c101160900e8203000f080c10781d01591b8404000e802e0300c1d4801c2c4141c1036131504121070700c0604000d102c5488045058820000e8803d80503113850f240021030740100c061040d900c0c480307103101d540002d43d400c1412100000c2c01c10840d01c038010341c2c104641c18001c0e000f45506005054000c50f00450003128440d207884ca10380d0056609104900ea000881200040100708500e8101c0103028071409001d009131502c2d0b010340d20181142d4540800c003030341d81c1d039032011700988480c1303202035581a00101c020034030903003003030425010040007078885c40c500ca09078405080c3c0d1418403181040000c1c0b070050100c914040d101d01c0d0084c2650401c0f00c505400905620014146610921500080b0f401c1c241100e002e9444 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 153683372 1250 153682122 153682157
    0xa09060212040b18030319030902181311121501080c0405040b0a020304050102091309030212040807090504050c0a08060103140601050906060d090b090705041a010f0c0c090606120b04050403 83
    0x4140021792601007800405502c0120118411040d282940c0000e408059441005040c001105448580703d0b201c40410a1000240c0114a1032a4009488030b203802003c2c400124541c50300c01000c002030103081030030910b0342d4408030001d050304e40c018240c0d0740300e40183c400d100498504541c0070740703490164030118500907131650046030014098030001d0b24080b070200c00f06040d010f842ca0428001a134540106046c554180a400803113260b02c0030ba2490540f41105195070f4007074500071604000c0e030314408101000000c00000900d07140140c40c040304c0310b81d18403001c3d454140920058680c40d284896041e0070720340104103117060f6080206620a0350316004240301d500e0700301004081c0e0190359943c104021a070221002c510400c1c580d00100030041c01d0005000503250210005820241c6800c5442c2c1180e03000740141000b0130701e514040c89800400c0c00c040e910b040a50b40050202850b21102040090384001401615052103106100c01c6180c40244012a2401c80d0040e001501001d540c3d1a0440d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 153684622 1250 153683372 153683407
    0xb03070e0118090524030609030409110403150b100903080a0f03021308030405100e100503101a03240d02040e0f01020d020309070e0c0307081b0a09060212040b 70
    0x100c1400c640e0750320f5114201c50049038410742c0c4c046483c0c10f50085200300c9014080c0e020b15220400d03005040d00d0704042c00c0f0160b03a03005900992421644900885a019621005030b0b0015070b0401e0f401c0700c001c1d9540301490014000711051a008880300d03810000014000d0a06008403a808007500e4600203101c00201c90302594284e900d81010b4080060790b41c0310201c9a0140042d1002d540515511890801084003c004200546041c826948002015541d030312200600c0c0c602d29003000c07a541e6542c0b00103442e00e03100540041144075905425040c0d44002c00707000d18813651025818001c901c0d001b40030445041c041000c526808950009080c0040c1030581000704004001e0341160210320303108184a003603070000610640c105501204004042404210500050403004107a44182c100b8005640c210b100080c1810140300b05d41000c18079400c40c00d4510070340d01515144080d200d5209540080402001c1d01c1541d005201d17402d1200c0413500001c00b01c60480794003109403460261985258007810 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 153685872 1250 153684622 153684647
    0x100518071b0614010602010b0103140121050a0627120c08040f030b0a0b101d0105070b01060503040302251214030301030c080d050403021503150a09020a08010b03070e01 74
    0x450341d00c00400d0014041e4080c45400b8a505100005203606120000303013103820320145241018141519521154038003d02d4505440803038074440c059503801c640243c1310015010009045100d6180b6140500c0300c1544881c144034a03c24051744828440c2002a17215100400082c119041c2d0a418074121406409880c07a01c5115991050416540b0717250303c003020865600503265400c42d102002051a000d114032401f840d021507000e0b806042c0c04030010107840b8265800044a142c41d80703445081e1b0b001d0303429030f405030754403850f01800b56031503080c0203150b43c1065034124050700c078200582c010f01103a003c001034650013100402d1400c600c0d05094071080d08200400703460a058440444610020600c0110702035402588880501031170100b0070307032030094242850300401030b09000074001603484000d2603103000d0442081503243d07217035030780b9461803000c00c8001558802126000002c0e07440891b000703003216405035140c10505a9036410700c01414402140e0300400030b40141078105071903001d2808603444 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 153687122 1250 153685872 153685907
    0x30090f0f040c090602010b031203060616020603040609050d08061e010507150c14030f0a0905012c150907030807150c050403140a021f020309030a0b10051807 69
    0x403006400c0890111606000200d00084007100c2c03d00000c0d409020f0842c60703983c280c0043c1410521f4001807211400007410f020b1182724009042d031401400b0302650743c04990000d000c0f6990b4185854030100815085500b220140210303584e40c1103081c012040e0300c0c0306500242226651030b103c2001d2207481a40e1134501c1e41032210905c20341003c150301c3c2440e8101c0c22191000010040280c00000d400c1015030141c60300090800c0082008001c0c080c1640d5811482064020034080081d18015001d000090980306049501e000000558010003185131040004601a140f060034186041521081e00700c48404040e8003220081000540030310041c1882030013543d8400b4101110304001060f05d050040700c000254006c80c0501c1440000c5555003d488141c00040145181ca90f0110790081091010350860a900344018083e1074002d00449001c0032006044c0c4006030520715080d5203100044d180a03601305100c10020a0b0744c200340300c01d00401c007920240c82008c0c0c1e1344d0b80300407185580d180769100c00c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 153688372 1250 153687122 153687139
    0x71407080409150b0a020304140d12020a021f02030403020d06090f030f030c03141303140a1206090b06030a15030f21080c090d0503040302090930090f 66
    0x204010320003910140869a801048400070303240c00c10300481241e000001d02000c00c001c0c868400740c00104480441c0e00141c007500f1215036490000d00340720341c42500030301500c00ca0822134030504d40c04a02420711502c00c4a5201c0c002a07204003e50145d2000d0b030917140503a200f08001d0015250060a1840b420712414010420102556807030341000e0003c102200881c581c40b2003070200325014000d110892610b841c04000c4540201d0000c03c4004016111016001861500d40c0500d40b044100801e10f541c0c04141c540d036140c100703800170003c5810207180d803402c520301000890741041501444003056002062182103031104d80d104801010b04031802d03850201e00810020011301094050764043d03005040343c01052800c3c503550114180310b40340d00c20030009400d041014216851040e100e014009548600c01c0f001c0924000745548902d0300b02179030011002003003147c01000021400411101c10745d2103180a101c20107401500404030390006900070090141d52000d040c5081c25400c8000014914078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 153689622 1250 153688372 153688387
    0x90706020a0f11060a050324011409011404061d120604081303021305060405090d050d0f1409010c0f09030201120b041803020d0f08010b03010b03100801110306090f09060714 76
    0x10340e20307170003190a580407640100c00c01c626010701c5524281400c00e00344240c0c1c1c41c4144440000c10500d00c0d040044010170000c11140000e07480390f206c0740200f00f079103110941e45d035445910141c42c021900d9145c04030103c6180388110582400c4880b0850300e06210300801c0386444e96501c00c0c0b456080450b0003d0907060307403800000960b607850252804144010400200c0d814110240404e95400408240b12940700d28081c2c500e0b10f034000c0840c1c0503450040000074900301210031f01805021070101e100c03007a00280050069219040d4426688528070752030304075800d26001401d9a8900d45448042d012640744034156480c1c81643d080f01d1000440104005800c2d080001d00b94803500484c00c1c190016031100501c4c9030300b50303080380c481003140d116400c040d09150725180b1381c101c10384014003803240e0400c030200115103031115207209200a41040c0009200042d8804201204e50b002118014810b088980c082010444111000da000300700c800d0150000d0340d20500165260450040040c00c044010050304 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 153690872 1250 153689622 153689629
    0xf0501032003070c0c15080403110c180702070608090d030c0306090f0b0907090b07230a050a031704051903180b041508090a0b040512190206090706020a0f11 69
    0x42d8850890f944a4004111050034000d440028603085200e00c540100024059990860b400359800340e070600d031100b05d05034148202c9080000310303003095807c8031520a4800070711881c1c0048a11507111503080b2400e043e0f0300c030340444400105889003607407034000c00c6100d86220707c00e81282c48001043d040208039540d40308030900403102c44508a0b88000c1d626000d8142d0b80c40c04d0b401c155009101d520344204118100032070b100c0507110341d00c4005c040c964403185030051241c83c298161003440142003030380c804521909206485c2d80c0a03c50840001d05502c070041880500d42d01218040e6420070b0041a003140c01203141e03030344900407580640502284517941912044503800280c003800e40744c24a151130710715000c2a1900042010744481c00d0003011010402400310026090103903a030800c40038101629541041414500e45420103180803400041b0080c0c0d00d40080d4040c18500e10560071610300369114a54180c55050a005460060f009500c555010986000f00356400764011040130b51258440d4000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 153692122 1250 153690872 153690877
    0x901120320060402041a0102070512070e0403050d0f0615080405011e020c06010905060105031603110a050408160f171c0c020913021f0210060e150303040f05010320 72
    0x1d612036a01150400007141410f0050364081c2c04402000b004840c015000070f9141d900c40d010307880c040c01c1e0000b403c44003c0f004004420042c0060703000d0380c0580c100b5040003401540702900280c11241050be103c206403800384503a90032030305002010250b6801d21902142d1032540900166115900c07190048407910b450440034030a81e811400046e43c0f01c14514156017003c2d0140c6c40100040d01d00001c1119a90704003080b46e0788449903004100b104070340481c1c10380040000c014203078076141c00403800041031500400140180d601400454840c00d0490480f40c2c40580b03940900c00d1814602c0004001020407401200660240c20b000c0e284407002a10740d90013410088102840080c151080d59010360038240e0786944c11403280350402c055024030341c000c55181268050401511034600c00c040030003620030b00481c80c4d0615440c80c2480001d580b0302d030081c050202951a00c0e00f0004aa8452000385000000c4404845030030301441c0c4a1450b1200540042c40c002005514510355030782c140c111120710500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 153693372 1250 153692122 153692177
    0xf0615010f1b080702130501060c06060902180108070c020d210c17030613090506061e1e030c0901090e10020f07060510171507020106030209011203 65
    0x609800221084001040c000550702440c080c001c0c18214030545030340000200d007225400260165542840b440401c6203242152109240c651501d0300100c0d405900200d2490380c1406840180b10103a140c441c24405c074880c4900c0c0da003e101d03401c0c80c081c03017075405441419030080380307130804c1d0304201036540106883c204106001c0760001e1001003070111183d04580350310315060141c94040400c5107565a0301030f0400c140c2070000c0e40890040009043c940d10048083c11441e6145424001d0a58030b1402a640b8881521a41d00c55180161324421800f010034030034007903040c014280c0207081c0c0010000001c420154a00c29050b028141000081d52078454046000380511440010003001040c1041e00b0b0080700403401201c0b43c010803085a80f0300398501a101031a40200c1c0016542d11000c1141070700940d82d5128851a110705c1034680c16400021445900304804240000700c266a0054103d0881c0c1c46030000039403041034074005000b8241c010702c9260105120f41000101003002e441c040c0b40303080001d41d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 153694622 1250 153693372 153693391
    0x40e060d150f02130e0606030403110c040e031305150d090f0501020a02030318030304020a0306020901030b04060609050a0b03061f02010212151201050c0a141e03010302091003020a05010509030f06 86
    0x42d4003860340c50700541038002040b80c040c817090607003001c0d0006000b43c07002400c098100305800700c0170085118144000613155000400c104900588400015201d4103c2c000e211140d03034900400241c1d5042c460405903202125200052908038821084401040b40344010b0b565801003040c88400980700348020952030006400854681c6440214140da0142c104180c4049410900a0200681310801c02a040d240e016201503118941400128010143c0e04100380d44242881c0001131543d401c000004169038040d0750306122980c03907202c4050b00d44400c0d02c4c0c0c103030071552003000c44a40461000c80307040300805c107100152803d8800c2c002d42000000c2030350900540c111300e111021084c40c02c410fa0344242d0700807200901c150700e402150320070140201c058010600c80c100000d046030541c0b5100319240641750b01665650850080700d045080d8009000407400f0760020b0003c00c001c10703010b80c2a42c0840b50300070130a801081c208001150039030400d1070290341511829550381e445030818050b45101c2c0d880382 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 153695872 1250 153694622 153694627
    0x11104060c0b151f0309020307230a0311010302071e0515130b0412090905010e0f06030304121e02031c0f0302040302010e210d020f0106050105040e060d150f02 70
    0x103090034800c054015000240f45081e4000d116040e8480340c0f0403121942e843c03402ca10760200603c0c07043d07020f0308001030000e50600480b031000c500b81500c14181e00c400c502c0c4c1081070001d680b610003403110640c0a0301000e8000320000000d42500d41c420340083c048a4030501f410000e1400103413480d4903d01050200310303415045050f2160b02c0c11b00d0300d030031107511455018042051031143e40304d04240110161014000000840f50300080d14000d40f0150020040c07080d0400456a44000100c00d00c0300030344416440b40326480124580c0d2030b0000c1568240d8014041d401104881960340425070000000090942d000c4061100c0160b0b07400d01940300c21030b00c1c041c03a20450240f0030200030b2040005810724400d140c414001440980d038000c1400b00700c1c0c2c4064031409149184c8940c43c0c80c48142003441e588041c4540114080c0184d408121090301c40341d00c0c0002e007c200e44500064503540194040c41e844075440500054462410401c00d42046008950301c4440c05e103102c600400b611203500414182c213800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 153697122 1250 153695872 153695897
    0x2040b131806060c0b06060412050109020f0d03080a020c1903030c0801050429030c0a0f1503140a020315040e030406110606060703080a150609030303201b01110406 72
    0x1011036050401d480100c01c020803818101e02600e800006500a4268914100000e826444a4040b10081c3c454030140b0765100040d480c00602a14070484201d0169002c81d665042074141210712030314140d85600c4404c1b035545d42901c0d80001350001c0d00c400d0300c0c0c0d21800c503500001c000301d1803942c0343c0c2d1030203507901088030060040c019000f201c069110f24010ba160120b02840280c0584612414051841880f4fc00d07000c490000b91810114196143e4021400640050b039088484945407c46511030784420102c6105a41a411600d001e06849c0e01d04070f44400195942030a58011070340034010b44040040d011402e8041411074140030a8020f0030b910000301809440d802045000000540c40014802880c014010450030300500d00010140a030391408160004299000f200c0031381030a403903114140e5900e0b01d0040560301d9034801540402d10345084c10450301d50030500008150480000103140400a0085d1a40c0310041103003048695138411050500000406c000c000620440e40c550910518 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 153698372 1250 153697122 153697139
    0x30403030603020d0c24050d0b030703080c0303040b070203070c0515071202060a15140d03050d141b0c060115090819020103060e070206010b070614090d020106060c0302030d05070302040b13 83
    0x4501d1b019184070081103000c1c0c40450740704040b80e840400c044408900314490b580881e00e014890303000107007100004030b880c180e05000000910701c142d000341c054210b20b4850000070f90b10392141660140064901c401c0520090400b201d2210440404c060030710701e400340c1030f22003144140c0550036000050f04030700184124150140105004403400381030103410390740703858903100781d1042d80f030956801a81410070034428903000d0022b444400044100a01c03141480040b03144074803000719180f04000880030580e500c070b40d000c041035910429100c1c005129076404d2511400d51448500002c200308015400b001c0752280050084283c440c804031314a0404c1c00741c0d480090b055a074141c0140c905c10341020b08020600340d00160b20360458410000d01030b641e554605041c0040c046403c240f0101c5010f01003801200040020302c1c078002c500c02e500802041d0345960b000c4501010b045800fa0050341b0070722032000d4440d141d903c1a50001c031141001817030265511107610042c4c100740c7c1184038002502108000c80311 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 153699622 1250 153698372 153698399
    0x7080415120507020f0319030603080705010e061e06010815060403050708060f190209030c09040b0a0e0105100506030a06080114070201110a0c080d0902310e12030403030603020d0c 79
    0x100d80e0019201c440d035403176201c5a6074054240070740140303010042c1c0191001c1c002c0d40040301540e08058229950022820001c5c0608038550034041c240c810301000a07692154140c44024800116480509070f4135007000440e24030384040d01145441220740040311150742c0b140d00a00c01107104002401c0e4203444d0040050518a0050403901c5c14940081007045c1042c510740c0040340c10031203a900603220002d0f4400700f80303440000c1014a8106c100d12043c4418040c41c40d00700d500c2001004010b110014502910760309880080e101082c01440070740042c41140b42040145901c03140700500000c00d5540c68400ca429243d00000c07030b46c900c070907200500c10301950a00808103c034494007202d51a107a84098010f105291702100075141c55808a1a0b00f070303804036500309600031500102040740014000c40f001c03035205000e404600e0b942029a00000001025000f403c003041091409008820091700c2400560b50004104900301541c0d40d402100694818078803402003402100340803e810300341b101288444 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 153700872 1250 153699622 153699631
    0xf03020a05060a080105011404090603030509091303230919051009030201020703020909031909050118050d030809100c030b040501080a050a0314120103050c03120f03060402070804151205 82
    0x42c2d20800082e000d01e50801401da044450a1070150a00842030f410444c05000f55002104078504001c00041810380c000050403442c00216805400f82d2111800342c80303046108103000340820f100c0c90038845404a91b1005403588031001c02594a00905800011070442958034080c1c1c0310640308500b40a50300303040310140003606180c10901e0840e800d6030000707560340b001444000d1061508000081d4030308014820390781034641c1618801c14917103400f0b102422820042c00b40c50300082460100c01680c100591150044540250101d4880300e0552400c48203c0c10007040c40a66108540500d1040b8049104d01100049641d4000804006c0350703040001366401039005a00960017900e40c0d03000725030f010030682201c2c0d0349030600701001e40f5885908a524003c07000c0e84014503d8540001081c8800410b050780c8114040342599541c00340102102050700500c81006480101070000569905084d802000210300880607981401d80c0e03900c00300440c80300701e0b000f58006205986e261840b12214002d65821 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 153702122 1250 153700872 153700879
    0xf0604060f030503041e0e13030e031515030102180f030f0a060c031103071d12010e15010e0f01140301020f1b0105060f0d0f110a030807140115060507020f0a0f03020a05 74
    0x1241c1c5403503075640311b07108094123004070f2041a07058401058001c3c000640b22510103800d0f19075a507842c009051541da011207064242118000d461619850306100b160900300103c412148100081800e06c0f02d005041140c690301031003416000c0740d4907081080384d0b04402d44038190109091422590007015642c0204000d54202014028054a0368110900001c1c00c004209010000081813001400c0c05410805803c120751030040308009034080031070b40c404624032201c4800296645e5002d0700349421012658118800c91050042c031800c0a0015206180c0070010005405c4c40c2800c4102d01156001c00300f049001002e11110046036007007801072690241080b82e1400000a00320041440f502d080f80c00141b44102c0d54000008000e07040403106002e4801820000c0c0441e101d19042a0b13075801000252130003407200034840303044481400382d141d042d00c50501d000081072a00c00250b50310b4200181c100c0e403149407017482c0000c1c0d40391008804010004040924011741c5103005100d04444641c101a00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 153703372 1250 153702122 153702179
    0xd1d0c0a0303080c03040f12050705011811060a020102040305030d09120e01050306130e010c02030c1527010b12031b070f1715130210080402090f0604060f03050304 72
    0x2080c2c03c0307620281e2042080390503541e40c1e5203d141100030512241c030300512a06079010a0021658080c02400c0c005206030000c1118500d1340910f00c03614804080000c1070344104032004480e5080a0000d80f056500a00026003805d40741e03a601411074001c600d820f103080d43d8610041f018040201681c6c5407001d51414904001c00820b00001c0c09407000400503409450740703000c0c0000c41e0f513041d03018030103a114680080020303100c060703402900da501045049140b0305c01c26500392070040c0d5050003540a51101031050002600440c030300602e5a8459046084955070350401c0807050700d6021184107000c00e0840550341d00d210310018281d0b804000ca40300301180d44204824443c4ca1550401201176940c1c6a03010380800c0c103240350f8149013031008005480044003500502681202d01c00350300d070405100301c9001c00c0c40441e001c411540c2c0f000407140654401001303004161381010034410160000e2020b040400c15545a204240c2554540d500807076a65000040c10012401c4149480b041c1da4000a007400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 153704622 1250 153703372 153703379
    0x16050a121403190b0613120309081c0c020a0320011805010c1103011b05030f1e13031e02031b0c0604060302090103020d06080a0204060503010e19080d1d0c0a 69
    0x24011240b26002e0308803d84e1030030410140c0d51003006403101640c174400d45500c046d031100c5c01401000901c40c0c00b200070600c3c0b00c1c80800c1102c0042400f400d914204083c000c241d0110321011030f40440e5a0701c2c1a600700f90001804400304a11010b0708150810800c0e03049a2150140f00042c1640d60b541100340500d205a442440b141e07034046c649581c0f072034000b104512200c1d03007000080d004108812600c0b2404828080907009590404095403003100884000340060f554070b003404500d214404820020740200740002502c10300042040b40d40075000e45442144440d0035068024003846181316000981e0001c0340b0320001000d541240d0070704440403005445210b10400118190f4007660190000380341d000315449180b40d10035030588406030107401c000c0c005a640e074100591203071b001c014107a020340d040920205203824140240204151190010f040481016202882c0d901040340b04845640041015581e400a14014501f6210b00d0700c1c140340c0080000e807121403404252102c20b9010f4a120b14040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 153705872 1250 153704622 153704641
    0xf0c0810050a030206073f03110a050c07030203120c0c0f0603061003020c01020d02040509090c0108061c1b06020f070302090a050702010e010e01050106090b09130216050a121403 78
    0xc0c00710307581030318400d0712003c052a00d08501d01541c45200d559819440d905421031441060340e0710050b0101440040c0103043c01c00c22001d07280c8103109c44190900070440c200e0043c1c4100014401c40214a055801d9584c60340e000900302441e8400c5a00145000309040c40180070600400c100a10211010002d04543d03a011070381d0b03404000c246512880d50303800707d8000c1c1c070700a4044030700b50500003008564a002c203070700d450002e4102e8010140100d410784d000641e8402c1c000b800c0c949403e0141c6a41100d50f40310381c10040120f101c1850300f103c019419103d440051041400701c085188906410320519040010080c5084105042c1f41402da00c041c2041002da01e031041684d8001d5007030750001c50702d9910104240d000d4419070411a905610304024071071001d0040d44560f050700c00075034508410b2070796083e01a45502804e254150b00c00680172a603015841e8540c01803581c258408183e20303900c0506d0301d8030317810308206400991b4440508510203048030b0740120301d0480141164002ea00b94180751009 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 153707122 1250 153705872 153705889
    0x20d110301180b01050d06030b01170c030a060f090611070506090307150f180303060f0f06020c040c09030b090c0307060c1110021606090e07050406050313150f0c081005 74
    0x1510540c1d03071070041d142940d1003175049550548400100f48813841d0b030380c40c10703441c942e00900c0b401d00f980c118a030b0022001c0700049422003201c40000e0040c14454031640300c50b0002c00d072128541d00110f41d20286940007401600503080c000510046a9440b4111400c00e10306207c1e0040910006030410066100018080c44014141c2105c0e40000186200b01040c2800140005103810b07401a402d006030328200740c0e258014409407403122035113400e0107584400b50050b51a0a0181c440541c03c5001d540109081c81d074041c13400840340f481c00385041e40e9617451f0165900c8054540c0d80c0c25800c403042c000050708007007000400900c1e05143c0fa945048071030300c401044c1107030041e030144541061003940e034205200b042061450103207070703511003901a035807040a00607009502c81d921f040300101000601c1640540161000c0f03c4954071000c2ca180e9a030708081c000b5003000f210131101400c6140f40a240300740c0921500c0c1c0b440101c41000030341c6000440014041c2e41c40245043c2c03519003202c03402e00803a242c1056 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 153708372 1250 153707122 153707159
    0xc0f0305060c0c0c04021801020c0a080a0b0c0f04060c0309060e0d1407030206030c0c07050f0d140f07090902030c1219060f1404030908070e1302040915020d110301 72
    0xea03180c43e95801d01603241000c03040000c01d0b40c020300208850702500c2200c00b1086150303034260201c40c001c144e02010300546000074803500c265a008a42c006c404541100740c50740c0d0021581d01024900240c58610800e0707034010390000702c00110022020340401d500300b1441c00241c11107080c14a0a012464000f40742021807120040101e40d14400300565610f0410103040910340c018000f940320301c0d0919500b54a900001c841e451300f84202e0b140040c0e41d081c080340c1c3c0b1001d964090a0007460790000c0e110b000c01c07041580350b803090078892984800074510003401828060a00c40760045500380a03801010704d4540c0c081c40c5644207500c038154001d061080010050820180c00a5540d510308140c01c203100140702004018100a040864888803040784c0c1d4000c52240748282ca40d0742c202c80c0c4801c14070b59184240e00503c29102c0030a404500023901505130f0000c4584000e10120700454140d94003d60100c042c207000743c40e02d4004c0b50515490703040e809484840d061001c000c40c110340c03400c000340c84403080006 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 153709622 1250 153708372 153708391
    0xc0806010f120f0f02040c050c070905090606040207021507050102031504150e1b040f0f0b030403020c09130f0c0501080105030a0308130c050907080403020c2e030e0f01090c0f030506 80
    0xb403640208010200c03010199600104104a0540c0c809070140c496400b0140c1000140074a0001080c20bc2682c13082c10b001e10340440041415554a5041c00029441000180c2e40b24141c14174440703c900540006100c2c16200360005a101e043c194610181241c0e40c0c1c00b004c2c0300b40e041aa040000054156407981118440d2105041e5501c0e1a4101c48222040d070140c403c00c45070000b40800d52800070340d03803d800c8800103802c100765265184420840785c0019100180140c100b050441294a041000b040c0c000321994500e0402480c1995210310500c110b0304c00325900d41801c5070801040da04481c1150042005402505900f042c03660014400940107010406102c881c942078014001d40d0320f1003001521004c0c024500300d0a1000000d820307294102e40c114010311550031041c01d42d00702000c104000c0300c1403103800d114031400901000c003404441444d03402019a00c40170381c16203c100300612504241510000a00881181000403400c80940c0041c0722400050ba800c2001900001c0c075207500c2900407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 153710872 1250 153709622 153709643
    0x60c151b080403030f090303090b07050406050f030621010507030e060108070306050912070812010506071101110a05010513020a05031513060605060d0609180215070812040c0806010f12 81
    0x1450250004c00d4045d004240403890110f90204060b050392008001d180030743d4191341141d5608104440912441c000c00d00000c1c01404519120038400c4003850b0844801800c841010b99205070031018410540050388940c0c3d150006d2060b000c0c1c251007440303000500711010707000d0b035814802e40c16543c4150744801846180c0e078000103a000315050001340156081003101d5a6140c07118100706010340c00402c1c100d50b01038006c4000081c0c5180100843c1d03034996201c0051030141582900540c0c5c036408141548450703005004209000074028071410b4814030000c100c00012044500501401500350340246010354030038804038030090380c569121a031199031102007006001d0149040d60107000142d10851304014049020914000147c0090050301c07100c6000b00512801c8000304802c02c070781e060009c0e410001080c1655000107402c0700500c0210b0241c03000c01d2605031401d610040f00c05040741c080d01c0c491410402405450b10510120740180381000a4105140c1481c413540a03041e0950b034002c0059001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 153712122 1250 153710872 153710881
    0x6010f1209020432061e04180c0f0b03040510051509090102041505030603071401020703050601090b010318020d081e03010b030405010e0d0e010f12020307030504060e0d02100e01090507060c151b08 86
    0x240d4000c00423444242025481d1004945030010705810b007400750324180b44c010400804d418158405580c410f84d0001c0c01000c0e910b01c48610074005000140c1100074168081b48003c1140e00c031f041199002d680308100041ea41d6150070104101c815511041d9000c00404209200f8244c2c0c0c0042c03003030245c0d4002d12256004c1c4c134a050060740791014540c8001c100c0d010325000011128017680c03110035102c0e002e072801d010010040791a100402002c4100a40c08000307240c85801082113070025060342c10403205000c841802c003031030340c2c0030a4000341d000020642c4004108810428280140c0c04070501c250300a1500401c840307400b07440c2184c840c030124100304404a4151406109413a00030510400d05c0d002c564030308154000a02514080705c0c20b5074010b05000c100c8801a600050440ca00d001d164090a040350310304e00c03214094520b01400031559901c9615030b90100e281400448000e200c545c803200c4405405280c040c00c5540d01c0c03e408100c0d14980b5007000d00900a100c0b5074079420350545402d01e90741e943c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 153713372 1250 153712122 153712129
    0x60c16050f01122304050c030d050a02151503100f06090204050a0902030601050d0603050f0f0d230909010b031902091c050709051003150506010f1209020432061e 71
    0x4c040c624111041c04a0144024040d0100358103941c1d82051381940c040140c43c01b025100740c880c1e500c2c1c3c3c40050388601c022450007080842403a4001c070b6a000341c0080c0e1300c1704a002a00e170440c0c07121041000e03695030340340c00c0644055104590007440600ca045d07041a01d000300007205c181242c480c00c105180c0000010b02c0c10380c030443c1112171800740031104000c165181d080240c0d5030002200c803071141d88100300b4003500c8148002401d000c50030740307513990380014202d0200201c600d440c040200b0440d4907083c0b0062142c2e5841a02c1c90b8060010143c1c3c0c2600ca1a00800001d4240144160030301c1c810720400840c19262150f801854110100f029042b0501c0c16529256141800550010402e14a044c080c07051405448107401c040302e00074905546888044010101200c405489980c007003035905124207100c60080c00b80080b0716500580000e400d0040d0f401180695144210484810280905203407421aa294100a100f83c0140a000e8980b1300000800e90804d030314101c10b0540718095102070400c0c1d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 153714622 1250 153713372 153713411
    0x60f050304050a0209181005062d03030a0203090102100c0e060703110109050c0f04020c070e04020d08040623090904110d050a08130501320405060c16050f0112 70
    0x13503001d80708000030300d4801d40b221007098172145a9003182c017600b5003803048182c00340141806500000c11150f003003032802000d440300d00401c20740c0e101c011003c1c4501040c1a42e0610240c00072a0b25900a5640ca41c541000207040c201d00e0780c04c03000f80e0f030300e084001a0700c0ca0b40110003a088900c03d6030f4140d5030351a1400c0c29100c0c1907020110b03100340c0d82031400034000c11002092103440d8800c251403a00a01c16900100426801103142c07030055a4003041e4204244584900015085400504040b5542c410b07529200c0f0f01d640541c2000d07000c0390801c0c040301c0641424240c181c01c24407280d0400e038280350806000545921018001428020861100307403041c0e40c0300d440107400c1d41d52002c01c98110f00d10510f0605e8881e0403440030382018007401c0d00000f0b01c41d401078141541c00b10b2540140f1268100103c01e0580200448031041c4001109202c0801c040d2200c000038a2019030f10b10042c4071040158031808814202070700418041c030607400c010074142c6d1300040c407104c100780485004268202090032249142e03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 153715872 1250 153714622 153714643
    0x120307050a1e140a03020106050604180906022515050103150b0301060b040f1d01060807120b0a061806110a030e030c090f182d01060806070314060901060f05030405 72
    0x1800e5050b2000034075400004c000000900c03c2e0001d1140d2551501088064000d1780f01d698030649200c01c0c150392210144c1d0005c40034034418000141002e00718100601c0c42540000701940d0240d09010380028404801403445c0014017000c414000b03903045507100c00c950f1032211a1241107a4441400c445586e07000c3d006600500841d96105031a40d40d5407002ca00c00820340d10442001000e00c0d1181011401000c44441c187c0c1c555481c0c4511a481e402d104840b258030880d801d2580d40e03a100c005c038000c1d581b1400304900805440d030b078900394103604009003c082e028560145060000b0b05002482d072000118034030301d540c0d81504028500d03540140c086802c10100d45d0006a001e1890b00030020340c0c045501c0c5241c011044241c00174500701c256a1003c0d030b60b130f01022009002c682c580c07000544207800c4103c0002d01d42404d07400401d80d107644511140c034140050300d035240825201c11032003151060040c2455881340d000c803145200b80d450420f0241c0b541610310150300801c100000081c0c140001009100b441 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 153717122 1250 153715872 153715883
    0x122d0b07030609051005010801050d03050904050f06041505030d1b05010f0203100602010c0c0602030a09021302090f030a0b0604050907080607020c0103050112030806040b03010b04021602120307050a1e 88
    0x1a25000358010020322041c010748450b58946008950351a0740d481c0b00c8000c2d508187c55141850f400c1c07800704400c4040c00d440131410030400304401042d50701c1e83c1c09180d02a0b044044942010b0508c5c0c400c02040d58a410200300e2a0722220302c041049941c0014524807011071810b1401c0d141c1d2080070f540b156140a1100500742d0340c2004005d000e02c1e0081e500551140ca0115486030030191120012400e031090000c0107400180d842543d100401c00f254019a000aa800000140401d003540480d0403480440709082c00c0e641d010030a2074490600034045008070100300d010341080ba42c56600c810b0100b0300a0040c500490307494000a21180d01000390401070300c030f2042103400c3c524046100964503160501d240380081e041c0303000020319035040001100780c1e0b68940c44000c0e0b2035236070509110007484e203003602646c10740d01c884c0c11082c181c41d90b10003010080301c1c02101000b0404140148001511800625855030380308004441c00706501107404860f199221960010300070004020402881e1040c001421 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 153718372 1250 153717122 153717143
    0x20915030610210506011802071209140613031502072010030c08060103090201021f020705010b01110d1d09010b030f090102090a0302012312010f122d 66
    0x202006095074100884075a241880f00e0840407240340076000c0d4980360028001e5209030b0041c0415090192201010314900740014244566a180c0340c071140003020794400868445d800501014428804000031aa003d80d0140d1400200b810404410b6803035200c081c10f01039121000301800c15064048a1071660000030340131452a08052200720082ea8403041ca12608901c1d40080220b0701074010550404a1030304c1e104011358500b001900604818002241140901581e020204c45858030400c10106050001030b10388000f0b10b002c1e405c4403003e1101c28140b006d5001008042e00c0c00080c51109059245081416400445100b0704a1607010012a900107498000801d0403129000074601c81c04010505946507101e0b00400c608038411111001d8101e651f004041c000765000d9600ca0110120010310360000c042a50030a000b40d41200241e4080c0041c203100401c005040c401012010301000c1514012558450ba501180040142080030303140003100d070400c650b0f000d0424a0341815800208086 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 153719622 1250 153718372 153718381
    0xb160219081c0305010e04110103140106020703030306080304141215040f0b1003020a060315090c0c031103040f0e04030c050a03080a0c0806030a140709140601120e0a0209150306 78
    0x703440b409502d88491040c0d8680500d00c40640c0b1034000c1504940c81c0940219854445440b403071228a050940141403584800101300750800c45440c450007070007207034060704200d07045160050548891760310980c0198014001030000290300c0080038020a4120f0300841d085241151150820702c0c2c074050b0010702c580e0f202c200410b00c41c80f0706046a040707110368400c059940d2140240d034010101030001179004000301e10244040c501a43c060310380421508e221560003940c850020060361145201c10000404241d251030170590441c0d500c1c500c0602c803401a50030603081c440d105400003514812120307021004c0c000701c1e00381030254101a4440350007205443d1520f6803400d02034802c00003604c0d26900d00307140c046080f0103039201d11583d90280e94018081d1654850540307170380380c01d0170b21183c540d07840e80180580001c4058040c81044815641d40b0f9081c83d40f0300e418000509000c044116032a078060821404030401c0c1d401040c00306080e80e04855442440d02d4004058010384610100d030340d0544280d00500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 153720872 1250 153719622 153719639
    0xc0102030f090a03081f0f0b0c061b09100e0d0c0e0a020403030c0206032203020115050109030206090907031808030604110c0d0c030e06040303050909010501020102040b160219 77
    0x55101d000207012801c1503403240e4110743d50754032400d440900000c0041d00400d01078140242c1000c0840c00102c000115103844910511603c802644140c40850001441c00f10030841803140716804001030301c04403a00030311451030140903c5100c1001d032242000c072078441940c90155500c020403000191411200b88600d190014404810b400b41c5014480c0da10005102040d0500888094030390544d101c050f0711115509020490300082c150201740a06096041003061404011082c035500039400400d5011034000717034060340e420a800c0241040140c8400344003581b0303100200c1d180b032901602c4040e190b030380d1010128024080b10b00c0304042d0140e680c001d1404c4c050030401a40c0549411903042158091000d0800600e10031a4003e90558100c0310240000d2802103540855141c001e082040c80c2c00c1000c0001074042e0b2040e081100072590209000407581000380f480d40c00340c44280021480d16003004102c032214010500c00700740c00b00201950404644400824070754509516800880243d101c0303640 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 153722122 1250 153720872 153720877
    0x30d2d051b0901140d0908160c05240705071a2502010801120303110310091505010c0f05070302030109060c11150c0f09030f010501150c110d060b09010303090f090e030909060d05030c0102 82
    0x56030391502140003c00c040c40c00d001810200e850342d20710740cbc9010800e00c030b4840c41c94201d550107546034003c0e01d50005140440308002c001c2008032011440d41c40043e074550075a201125a181c001c403280c0b40b000302c80140d8209000e941554108804001000f9240c50101c026064607500d424401e8008020301c45001300c1284a142502e440800502840d01c10384156907400c203540c407a15000401c03501ea4980454558091992924000c130150b45600e074890b00802d00703661414400310f030115510281c40f081141d20400c0035180002c0d1402516500901419040707141001511002100c000060045520711500d0202c0c1c480a8001d01903480d10301c48081013600030882442080481c0000e1074052900c1482205500e0754240e200400460000811341444461444c42c44115a41a5114002d080c50b541c0d1160807030085209540d030740d01c01410051040d400e200580e000342031490034803401d200fa580011081e510001e00c103440d0324080399220000590800980a806040c1340000900111a110107400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 153723372 1250 153722122 153722167
    0x7020d03180602010212060d080c060c0918061005130e0f04060c0c030915090905091b01020a050a0f020d02060a0f0e01050903030d2d051b0901140d0908 67
    0x1441c142090703903580182c1c01d038801d680d03403012242d11346000581d0f90b203406045400818000d10f031a504104100800f18600380040e0358081240c100410002c07000e15002c0024450014803440b14003080c00c0940c08103c005194101c401d091010126044102c0c1f040b0035100300c000c100e13aa8070024075080408061440e070700d064400362083e0f400c0007101801c003409660721800007541a6142c00e04030746844031254040e20100c80300000c0000010f0009a441c1380750055130701400000024003100c813a084d40f00040600a01c1406042d50480f000032800311b00081902c08041c0e07000408028402d1092000400e40380038894020f41c409001300706042601e03840540084c41d008130351070703000880c0000c0b030064803a80601310080c1d40c150700800000d0190300054110300754650000380c0c8000d0702114003403448229164a000e400c420780c3e44604000c047c0140391452540d80c02110013903803900c80c101e40020018480712010410740000081d200001c42d0059201da40c0701c0c0d0304030f45619180c40e240c1c100000815070007203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 153724622 1250 153723372 153723407
    0x30405070906060f03020307030204090204140108060f01231603020a050601241209060c170a05010305060705030411100806090709180b0f0a120c090603020f041107020d03 75
    0x4030003240000591150805980507515100e054141c602001c40296000801c0c034002c054007032100144052907800500040e00300f02c42c5212100200c0b500060003004002c02291046160980d000d40740d90700300403d40702c05002c14120f80d6290741c004c0e4081007140302c2c052802d80d00f03540312228841895404561403003000d2241c0e081c0c0e51683d907145003003001c0c410140150f043c81a221620084007501418804000b60395a200204590001da01c6100c101c840b00c0c1e4000011a00da071022906122011072807c0e842000280708003c294115225141e580c48002c100005001c1c000012400348458000c080515400003810350a207000711050007481d000c0180d40c3d8a000d81c1881010a035203500400b2a6800c1e80c038505001c106080001c04841c026003035400c0e2803034114410011000075034440c908000003401c02205110303407801051902c1140048540d1103e090246807031018001a65020045008018111804aa1340a65040c42201d500c5000d600035800000c035214101059007020380c07030400d031500e130 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 153725872 1250 153724622 153724633
    0x305010807120b0a0203060301200d0f0504080f030402060d060909020a0806090604060c200312060613030204020a030b041406090c040602060f04030504081b04150503031222030302030405 82
    0x5068124a0182c1ca40006020b0070307081e0005000c2c1641540516440700c4014004a03900c5020001ca8840110046428003c80e200141c510442003880c052011203803840c80341003080746420b80303914605008404a00c100ba241c00000708040d0740e18003082d1034901c9400203080102550301d801da44020000000101d000324044e000003c0c50a0300071403050b00c61119040545480da66036a2024020710003078043d1014006001d00d52034a50760181079105418040100851ba0f81c20048901180760340010104e52003100c0410100d21540c9080d11140c003265815280580c036040d88032019005402280c075050b4100d41f4060340c0402c10f40c00788050b5406000c054441c01e016403240301d00300b10188924091503000d60320600225504c0749201c9805035115011b490064101900c41c02038a040c20702102014041217078001d20f4403e1880c15202d800e081c00c0f0204480540d8a180c4408aa100d000f44821004900140400a1407028003a43e41d504081001070034801e01d61080d00d4040d000350000e45041d1160b1158 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 153727122 1250 153725872 153725879
    0x3070b030601051b030c03072906180a020403061e050c04051e13020a0c0c0506040e06010809280c090204030c03120309050706090519060504170102040302100305010807 74
    0x2904036400381006035120b80c541035481c0c0c0d0900f0700d8822584285918441000142d8900c042440580000e41c8280032254810030408521205044003443c09441215440e06001c1d59550301030441180c004001c11103421983c4100f4158024044d662000c3d041604103695410442c080d000c10000020340140e003006651103802680030b180c001c038082c2c90f41060848480307140b600700b041600c0c0100e01004000720110b103110081202641c001d030040202241242c0f00400c00c201210b20144044c0509580881c00c1902d4a454004400d80150505041c0601d05020405810b410300aa9103560000c1c0115400001c030000c0040941d0480309044e220074442c4c0c00c0c08100050a4001c49080300d401c442c0a804032030450300e0b0340300780d541001500d00c01c1c55503405034a0300045007801000f00038075080e29000262890031060080441c400c084410300c1c0070340c52406202440d04501600c0a544884054203503441d119400c1600a10403074102a40c852442c01c501d400c500c2d8150841e905031808881a01d80f05588c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 153728372 1250 153727122 153727139
    0x603050f0a051005010302090f04110a0206011202060403020f010c0614150d0b04081b07060203071e050d1101090501110406090f03030c1b030803040f0201090501090602060f041407140307 82
    0x90a5a20b1040c45840d070f00108503a602c40d80140c48103482c0203010117124044d14002608580c0c01d201c800a610202081072502e658040c0102c40c0100290044c8560200c4a6400207095109602001740b003104641c00c00f00c003d92141503040c4809910001c204840030710031200522017032003110070700c00c0c500c1105094181c41c1002194040303250f0340100000703c541c840d5a96040315401645407000c0202881321003c164070020801600203100c1c5401440ea102e50a04041540b82c4140d40004400c60b40a10000001000059581891021807800c00c424854202015015050b2600c000c2c0171503081c0349004040e14072400c001c008440f516190190055611103520040d4103035440301602140046000c5404103103504511070102c5801220b00940b26200c1d503c0401c0354100b507800791800051038071140c045580240402000e400d0908210340c0032403500c0d600a6a541004204298034282760b00442e080280c00140860020750a006686e0410748a11350250017408840b6030b28864861044001000715 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 153729622 1250 153728372 153728381
    0x1b01050114030a06050603031309090203060f0f0604110d0911030c0102010e030412030509040f0504061109150d020d05040b0a2f0a0c050d030f05011d060111070f0603050f0a 76
    0x340142c00303490200c649444010044c00e00812540d01800100010702004000291300400342000b1000098582442e0060628141d00100041030302c003003003001e1100c10b41c440c2806a500400032240824044040301e51828140205500f00307000c241042482010055685164044a80160200d45614458000490907102250034405290300100401d21414100d040060032040c081d0508500d001e04240204040f100c41c50346450003246d0b107078284000c006207030181d03842d03081280107403d083c0480d420000312480c10007031404030001c400003216210307141141c066514034110344404101515150a144850300c104481c510741141c900b032512074241149016145001c240c107100f0490100c1300c010401025403000c180441444102c20003c030000d48100711142401c40310356800319103075100d42d010005403403041e0000c90300c0755240c103000700648001e8480340307078440400d10700804291044403d043c10481b06800000b0380032000da002055185c1c0582091b0302401040700304d52041d41d10707281c4080445 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 153730872 1250 153729622 153729659
    0x20301090e0606030c0105090d0309080d0302190c050d0318050312070212041202010e0102150a02190503010305031e12010608040b06010e0f1e060d0b010201051e06040c090302061b010501 82
    0x400a2000320b256051030703c0c54070f00007803003420079040d0bc1d620b4110b054500070361007414500098000444030071500903aa01855203000d1810075a80c0001541c0d80d035030325a00911000010541d860306120503845541e161480d15503000001d807592496400890918030800721442400b40c0302d04100c0c0d0a071813503040c0450b41143c009003035041d400c0e4050b07401100c11341202a81941141b01d54a9014110104400760703a00404400350016514101c800182c0c0000540031040000d0040500040010450200403104203030a50303003100140384140c0c0250f00301c03800354003100d0545092940000c01c801e908594150300403030003040403050aa4985004440300d0b24401101904103280c050111510b040008000320060312a030340e41d0010754140c50104000d5008510041c0320300da100c056a90055030284074071500174038442c0c20040c0c0324008801d034584222010f030495016554a900000007141701d909102c018550050105507100404032811001c00c80a078149000380d443c20300005141d207004000746003003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 153732122 1250 153730872 153730877
    0x50408030307031802120c1c08030105090405160905150627060d2406031103040305160213021801050c0d0518030d1205090c0a1401090306020301090e0606030c01 71
    0xd59880b000128098881c1c0b4100101c20000c3c03060400050740c50900002039440c2102c000c2c000555180100a01800751417007603a40c1980e07180092000c83d034248212070540e4000d50341405562903601c3c1441c0740031004800d41415040040700440c80b001582c00140c0100c1c40c45d641103003000d614108000e001e1180942c070040c5001020100702d40946100442c45624600814160078250940000c1055034070007103c403454030032038610304400c107001c00000a02a152515041198480b60b01201040d8440584060144000410740c4001c0000c051854074815501034040610369031074005032406500a0000360707411421071200754910b07500c507005880210200a000f010707a60b5180030f00341c038031307a2083c0d0029010041c00350072031009031020400c00440070240d9a5040441e1320b1503d0000886130701604022543c2c01c502060951642c0e508142025138010126101d0f810410034016140041140e09c0280454004000011140714641c00000d084440b0010b032440c5a0786c080402d030300d542e00310750484e02 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 153733372 1250 153732122 153732127
    0x40312090906091a040b040608030a051e0309070e0a020705070e01060f020c1e0a05030307080702090106020106080d08071808010e07050604030b22050a0503031b030f1503070906080c040c05040803 86
    0x40d6142c11b800044103020090400a0321030b4031092450300310342c0101d4842000c60000241401c4030440d02103452900079a01c2c03c40c03415403e0800032203403140700309d208001944454201150030083e459049900307990b8494112401280c3e80c0686441c455000d200c1c2c07001048035207034000300b494004501c0c22a010780040c640c140d80404c041d180d0103100ca460b41520307008910303003802050548081000307181650040140949901e090300c100031002c48140c2009045904185003040000030004036440000d91a041ca000030342c0d81c4a0303085901e80244c60203080042c1c072042001440d0303030040d0311049120301c0000c25980d400352100705110325403041d0320004001882400c0010080c1540300400340d0404041400000441c0140d03c0e100d02c1c0006c0d0940c01c0c2d40e20307000002882016840d0800d5145031074a54801103046107007400442010100042000d54800e0440901c614640d80034010b400c044c3c0250b000800c6100d45450940c2d90344c00c003883d90103005600e898007401d81c1ca80a401600d040f207614800452 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 153734622 1250 153733372 153733421
    0x702010f140c240f060621130606170303010909030e04090b04050709150b0708070c03080306040515030a0b09010e070803031f080a08090307030602190306061404170304031209090609 80
    0x1075988071900c0d90880700d1083c1900c0b107d151141e00158011007105120301603c814a0400b0300071601c459001d0031650340c003241071004100c00031050b241140c64a040028440005080c01d0321140c41d44d04400360300c00c0c94017450300f003040520b621090240b4005d804070f8074180d480c1c00da581d04488002550902c1c02103035400800903021102d0050581900c01c4c40d08500b0540703950754801b0010000d80048a1100d0b0110400c485d5040a00c5203542c001c102003200c2040c140303070700017280e1120640c0501425a483c00000a91040400d41004085543d91030450702596070740d1080070344903042501d0440843c5049203003c80b09642c110450402d964061015000b084825aa0703682d80c1d0f880f409407560940100500000415420302c0900040490941144c0c811100c40d00e0040407500039800c00014051000d80070310018004c401540c0903904c5085020803061125520355265020316400100250503204160030401e60042d4a1411600c00d2003051114940701c048100c10340351240400300c0013180c00361051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 153735872 1250 153734622 153734629
    0x100c0803040f0507060f0e030703110d020d051b0102010f112209050a020406110d140903030c030f0403050f0a0f03030f09020406170c09010b0702010f140c240f06 71
    0x11500a0711030b52501c55611069540c807414412070f0790041011031601c6400c0c0814581000e060800e004041303019103149d9003140e40c7c040686080e1001c01d801380700035801441c11900c0d401c4045071459040401c40d071410007426102600a00d070b13032615500550a106e022042c10000d80a580024185100b880b410140d441c800e03204211103c081d08101401c086c040021010400e102d4180260707045040980c0d60ba04008000d040100e142480c44200d0b481842094070240c0d12640303026030494494242a6500401d10000e440e500405590b050940400034060031075500703110003081103a1140c42135074400100c045241d5100c03603800c00d010f04010712018002000a103c3da1258034400310f000400103040d8a103801244c110f44103504800125103c445980b503c5007030821250801c1360702180c0212103903044c0002d105040c014400c00a0511450744410000c0a0240340d156910704a1104081d4440c500d24049955800081c031120b225056040c008640c40190881e10034828903210040e01c45640b11001071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 153737122 1250 153735872 153735877
    0x2409060907080c040e0910060b0c06070f0306030b190b0105120c070609051e01060504150b071e1101080109020304020607030c1103030f0d23040b07120c03020d0506100c08 75
    0x122107108504004c0480e54001d44c4004a00820700c000c000c09156604003141c0c0200d03042500174000b00c40c0d081c00240491003000841503803048451601c0c00602810302801d40241c070158100400100c00001044040000c400c81c22040c102d03105e400b032000381401d20041d00c052160500440752011024001a40a20380b9002054010302c205000169580645c44a9003445004a01250b82c40140002d0b002c07030304400d0141401070302d0200e908200042605821a16054040c80384180c40c6a000c13640d0024031001c207540308265645240c00046022091501480341c0300700803250360224440c1c2c40081808881c134800e4910885e8040d22403860020300391001e48442000020881d002240e400c010041601c084c0b01614500346050040c0313445001116629050350a2007680808070b031041490100240c071001100d68002d904454160748584910b48101d880ca08040c3d01c41c201c642c1070441d82e50303140b1b0f030613802410000c8900300c042184d5140c0000f0050610b100020401c002400e260450300424504d500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 153738372 1250 153737122 153737131
    0x6050109290a030506090708071b0507170312090a030c0209151306060215161b0210050d2307050a02030c0a0b07090911030106050703030e06240906090708 68
    0x442114600d160400300c4020351150390242d001a40700ca0a1103211304001d10f42c190002a18207281103d403406000003806254050744950b002d407084c00068040c040f0a2040101030a140302d0181c01040000780314664980c03000e60700200d500d600700700065050030086040300000d43e240c1c0d50510500459000c0040c00e44001e01500554400d82007a140d8660381d035180c10b038031200c2c1c0c200c01003601803030031802034200340300a4401c1c40600007200420000301802110804285860705010340000e014201000c1c4509850705c00035000301313011008902154020002d0208854003940600c885c10b1740702c0042d0340c48991540c1850040704094003041c15903005001a2246e0710546c0304032030030000f40f03495861401e4511007081d1504c0202c00180701049510050705c0010b49200403050101c18001d030014003044c4014442d40341000303004a034100c10540300c0d400589206884804a510500f0a2101131031283e85411141600c1d40365400c101083d810070031040c5104c0c28006280038480d558000381654240f600a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 153739622 1250 153738372 153738419
    0x305070e13081c060f050f1f0c051c05122d06030a0b0f04021005130320061207030c020a020102060118140a0504121d0d06060b0a1d010306050109 64
    0x205880f64645103200d460000c05102101c48070b9a0b02e00018800c1940e4906800c40c000c0300385c511082081100c042c036411100d01a4904190071007810700b0002d0500742020220882d00f419212214030b00369200003c0c2000e5040d10ba100c24107900c600e10160307103806107210b07092640d44030345400b00411490480b20079441280a001d54501d80710f2a40da11800c4d680444000307a4a500950a002c1503090810708420000002c1c10804c1c50302000040704144000c4030322000300003000003110103110b602611001100040301400540d11036041554030510068102d5030300d80001d00c0c15180380c18051000a01401168060b00906211b034213104101880143d51400900e2260301c0740c000c5400c84502081051080243c2140003800d42001e10307020031200c205902c60810400070b0480c0c61062101d40303c01e0211010100e07440c070303100712151605c813002d041c055000d40c8000b0404518044001c0e00000564280e00030b2950080a08a18000640440d44540206400a1072a01c401d008034900d0801e204890085038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 153740872 1250 153739622 153739657
    0xf030b0a0902120703060f140a0e0a020a030b0a0b0f0903191202070e06090123030706090303080a090b0f0c0904051003030813050c0415120c0305070e1308 68
    0x60082010002680c0c084030309240d001034407a43d10f00c0d03003010081d007007009464180001031030b200401c0000c02441c0903420460f81030281d4140c9a60740d040c0d40000030144040780b00c5a902c0c01c4070181000350488100c64001c2800c10b64628418a003c00030003040c0d800f100f03119803c12422040d00100c0340c220804050b00740c41841c104104207000002d080060134803410710f8020010449100905225040e8000e0410440000c1403083d41e58481b1495030644850082c2c00706a0419480081815280440c81517014020f035503021a4465120b121441580c0c040c1d11408c2c0f070b075204d00c507091080f683c0801000d09107100001c082100d10342040211900704044144140c106034800d00060110b40094940c0f074908002c0150420806401860140c3d05c80002100690305010548802c3d031035103c42c80105206c0d60b9142002c5c610713a01001001c1d0f02030321015007042289180c0b498092682c021500068815225180340011108446103c9500c034140c002442c1807040c10940d24060160031000000703d030780500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 153742122 1250 153740872 153740891
    0x3030d02070f0b040f210210020703120e010507031d19020a03060f050f0c0a0206010b09010909020c0303180304061407060e1605040f0207020d0f0204020708030406020a030606030b0d02010f03 84
    0x10b50000380c02103001c5c2c0d515050807031440c036120906688484421004480c1850301c048815000300d0b84500803c00c041d4090399810b00c9103400c551081000b00080400c07031030450910507040c0150f02262140c00d25480802c00c1441401e40c0448040003903403034090990010612080f0a1504014040380310b202806001040d903d0303036121025280404210310344195150104040000c400d14125002100c40c804c00d444c11241006c000d488880501030205620340c0040c01c8281644a060100010400321204644401302c861809441350700c180e8a85040310a41c00101c80701034804001c40e0100c80d4151502c9000c180034666043c1e0740d17001080f0039202156680a840350500c4144519003c51404001001c4003d00b030508000449580f061000308042c81840160b00503115030090b0034801e50407002c040000030b11480000d029100b0103c0c000c2c20101d010041c4800c200a54016140c0840580c41c20700180b0313110103003141156441d95406070b01000480810000d54000c0503036008001c030511300854400301 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 153743372 1250 153742122 153742133
    0x911061204030915020d210c02070905010b09060a030e0118050c120102041d06060d0c09060806060f030705031e09030c0106090612031809320603030d02070f 69
    0x20008403448050600104401c240c0d0041c0c100000d00741141100c8413074100d07010001c1d500c0510a210b0414081c550f1507050043c102d0107104000a8102282030004d051107005c0291151594440c1b080380604002c00800e030b40c003010302070710381045000e09000d0410360090340c100c001e0800035140b03400340d56076150301e5110340107031100351564940148000d12154000800384100540b054903030218591052106202c4030321542c0072403a0921042c1d88104050f12400006401446007110191070b051902419011440c2c000018030200d4100340c5803c5030f25900c035414000716200f00082807090000420000e040d040c0100302942d0000390320344a600c2c0013500301500241a0354207980d0b0402070b80c008511039540820074062342020380f103444424450f4503c4c041038101c480d600d02c140101800303072220800c0c410f600c4035800b00000306003041080c030080030344006070b40b2600c151500a010060120305542901803040310082c2c020702d0040d0086181141140301040250402c6800f02c030030f0480f19103070310082507 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 153744622 1250 153743372 153743377
    0x30c2116060506090f07080612070803040f060906020304050a03060f0b0d030509040f230403110706030c030b040e070b1605030d0c02150405030406080408040510091e0513091106 78
    0xa108210000b42800d08208100340b13104d00034080342810140500b00300700710782e001035038035040201600c0c42501c482c9044002d90810312503401105003840302040c005416541144240212100f9403502c03040300b5159142280c0740c2c812070081c1e41d00490941c07401c000107840365005c0300c40042c1401000034000c06910009100686094041e40012008207202c0c1080c40c2602c501d41c82402039420401403001e04002031140d850568242c000c14042913000241814098444d0000c0d2101640549040700c1e00c1d408054002d181c101c410100082c5091040e08140c02c080c4943d400d8283e007071009094080c46e05415001ca80c1c000d03e03190003035040001d07a00780042c0040001e001030f80c41001c000700740c82c40103080c003c2c40c20a4081e103845024182c8400d100206030301008903000c9d6203042c680700c2916a40c2d030030708004910480c0c2c401600a44400802035085902084c064240d60445042c01002804180c41911240c03c9000340c0b0f9004442c3c160540b81e80c4d01c0c4d90721100d050b40c89541ea1400254001c0300140c03e54 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 153745872 1250 153744622 153744667
    0x60a03030815041e0c020d1b02090702010207080a1707090b1b07080304090b1503010e130201090e070503040201090801020901050f160506011701140106050d05070924030e030c21 78
    0x842d1a030b03503000805d80d0140051340001c81c82d450240143c6007c40301d80d500110030f070840603000d03505060108000c50f00c00e40499606e00d400035020365450441d25001041610002c1004030741c40390f0003000c0f1300d00794400c00540048914042600f0b0403e240b8000c41281071100c0c007103045580c81400e1001585041c1070020348000c0c40030300070000b80d002c940000c1c0160b61102000f507103480c00c000c000511000010842d699080036866400e16420415440161400c18080e00701c101079603241810040500e6121340114840c0d4401e80e11010150390f5490140d09034041c40020a02080c010f0107590340420703a55000c2c0c80c0d174569011244003003d109898086c01c041c020b030440800e010400c00c3740d0403003542c00d0145105c0038000c11001c240540c136041f402001070040c8a064044180c441d40803919840c825100d14018105001d00d10164520f01c030050ba1404e114281c0480120342003034240c445100c804400d540016001c0d0f8040c204003804003c0613003005c1d0300f441c0c103424045000e015203924510a0540c1c0c7c540c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 153747122 1250 153745872 153745931
    0x607020318370503010518150a0e060a09030e01020c01080106050d0906052a0304150902030f070e060406050306130807140d0c1703040c09050613050903040905060a0303081504 77
    0x42c142020281429a0380061208030f007448410000701101a0001c1c00c00040040c48810b160551101d5041d0005042c2c00748005843e80729140c18802252002e6000809144c460f840c1d007207500100000598666118900103030205103041e004100807402040100390309840030800003000140c0b5900d1000311041594070403002d06007143c01105110007000c0d06040c20321500680b46c00e51401d95605004902c50a034122503103502c4498110071510b08020138070703025000c401643d41c810744031805400e8800c2c0490b809031140381400303400942070030302041183c019904030700074403042c1426498207001e40d4000802201d88002c0000214044602070000c001e090704613948454410340f050604d403111804245105805003410410720001400c0c0e8100345c8100c81c072100b0b000c20295541c02c00501e00b10f8039071041081d6142404100f100110002c801002a200303404001c00068444130140048082180001004100040045050080f41d040c110540c0700008001040c03003084044225004820080120007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 153748372 1250 153747122 153747229
    0xa0f080f0f0c160b1503120d020706091e170408190f1e0b0106030501050108041407050d0b04050d0507050a060f09080a0f0f020f12030604020f1b0607020318 69
    0x508000d17004c140101102c0441c000c0400300016a10620117100d8680c0d00140304e0303400034195040100e6600418030068010b90210309600c400b8072814183c1b02044021143d5026107400c50030401041010344d000e90307403000c00401040c01c44288880da01c02501c003080d509020001d81200000b00202d4800f1298500c2d41f0340311500ba13410746091600ba40b4180c006d101071508000052007280d911040d100c0c0d025811600c0c0c0c01c50204e400c1041070402c5601e4211139001180800c0710010301c0000390300d00b4007030ba200da022500d41d510300d0981121306000382a002011604446184004248036801075510500340c0500052110855640c6040d1940303c8441d09010490208500140a0b0400f0413082054501e0000e0803a000e0400c01081d2544084048010641c00210110b221611141d0540700300d01201d52504e541c1d40da94009044c0c84403161851000d40344a0607000400c154030210646500000f01030340301c8400c50000041110184050307031400314181400740340d10030602081d49000c3d4601c04d142d4034446c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 153749622 1250 153748372 153748381
    0x140c0703081617060a090e0102070203190203031c02040f091a090403051c060503030304060b03070b0a141804050411040c02070f0e060d14030a0f080f0f0c160b 70
    0x24842003006128040610b0202071a511980e0030520b0f2098190302c00e1140306550351a0741c0000c458410302e4200401c41484c0400884038100150700401c0300c0d034001c5003102e03102031248891032900c100c109002034160f0803e025440d4400303803103224988103c4981e070025041c9a2511a189641005e0b9404031a8064482e0011240741001c9074407040351000a0781c004210b0310b09078030060068414000840c80c4514440c0741d90800d21060390100c0040c20004054075640e0410f414a503014224a50071644203016a1f03074000345090f04c40b011590480b640707840e40c4422415403c10300078241c1022030000c44040c517400380e52807650740728400e08e8802c500c5041c178072100f050f03200240000c40d06011301e9081554032242c02841031165000e401c00c1203a01140c01c400040d602c17880858076010064000400e440e03c1030781144010310000c005840700d002d1036503801100210300e09084445003016200442c0a85c00c1902045900310a21002c81d0321404860040d86441c12103c5a840ca40b0100c00d01518110380c400b040c003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 153750872 1250 153749622 153749627
    0xd03110f18011b051b0a0305070f080601060f09030303090204060b0a0315080304141002010902030a1401140c0a03050406020f04170d020105100e07022a0f010908070504050a140c0703 80
    0xb071007880e85084241c0700442e000c0ea2801d5441d0000c2022042a0303101c5e078284146951a01181030145034042e0130754540c25642c1c0c901c01003207005405415000c2c000c1d4400030510038172070050010403e00c1d5550324011203195490030f0300200580c44050360400e44580c40420102c2e45040284510301d01550002811983c01300d0070f19882000d90450b080c180c0041104100d040d000c003034403d11440040b43e0000a6040c0c1c0103041e40140302c604d100075010300429414600340051410351440880080f8000d000c44042104020320740300049404000420b824000c4c2ea00c00b504c02e50105510900c10b040c014a8480070340490301c00c43e08a6486050074a43c4030764100c501540a118002c0b8025142c0000d0100381068450113100c40e210340030310036207a0b42c2180000c000c2882048415600b5035401d02e0341c80e02416070703004480c9500941142078002c20480100c40040d51060190350704880940c800f90035018148010070001d080041c00b4600344603100d501c4c240c41480d072160018001c0036291420b542d43d04041c03401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 153752122 1250 153750872 153750887
    0x30c0f0a1d040e0c040e03070c030503190905010c23060109020406032702060f0d0f0f0e060108030a1404090e0705100c0803010b0309030d0e0f120c0d03110f1801 71
    0x80c02d020314101500015860f1000a120a0074070382180e0105130b04803030140d001c0c07460040f0301c8040d00841c1b03000000028000040001c0c04070230403020000002100e20745c070a031501d4006200d868000380030890b2400105601e1030a202000d03a5140c50f00030108000d500007407500f90283c00c5550b1103940010100403031a0548500e00106044e201501c008164810040340f41c070381c07541130190103a00001044504184500700304c03681800603000030494a41c1210f0780390700500700c80c10042c4600d444d107100072030100e01c00214a41210750000c015071800800c4d800840b040740380220107998a450510012800c150503000c0c128240d25000000c142e407920745800c02480c6104c44c04c2101c18000003007030b030601080200c070440781900d41400d0782c25600d80350301f01c046285105140049008514020420b02c100c0000328503030703182580d100129061130305030710381c40407182c40b0b01058040a40e2100d0201c8042d18000d400402c01880340c501070a05042000000208503408400705440e01510305a1000c07803503810100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 153753372 1250 153752122 153752177
    0x80406030e0c030a03030b03121c0608010b03120d1508010c091505040303030213180603020a050f01020304090c0c0b160305070e1e120d050304110d17030c0f0a 70
    0x40101500d402e0101c3e0700d4210042000d030030140c5030706d443c01298400308189000c0b14090400182d03511440415002e10950306103401c41d0083c200a4001854001401643e5582100601821608024117041c62040e440104180c10140c0c40320700510300c0116401c3c0400c001d000c180000300300006400d00c0202350b40d06030740140c1103a619a16000e15695407002c29038060300d80c141001a40e541400d200c210354049568450801300001004209075014190031540440c0e03c2540c009020720b0b110420840100c168181e07c0b0b00690081c4802c10019603560400241d40c95941058004040f00e80c81d12804079004640d03842584000404000c0b58a500d44030b41d0394400c0e034919207100243c807001d002030410b600d00d000f02441c46082c4403514009617102207a5405902d450022106840d014040151180d0422034040c1c54011500c651982c45d0b05010341c1a040071544040b8070138140341100c0600410317400160416085110611002e055502484010500090651140e4020981408403206016040070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 153754622 1250 153753372 153753401
    0x31c030e0c090c07030503040507050603070c0302070e070c062f13060e010f180801020a02070617010e04080c0f01090c140301090b01120204020c03040b040315050f04240908040603 79
    0x7020000030301614404d403080c459140c540681e51b6207450030b09500d014203503000305900c82c03000000e01a203150400340d0301034890312903000d46001d0380d5074020b51521104225000d4010840c06e80f948000518680e03c030b00b5001c030500c3e5200c800048480a00201a00b0284074526805400107080c03400080c41c8049070001c08441c41d002803070950840000b48140c922902c500300317028041510f65440d905041d000805485004009c64859030264002540c0d600c8030f109000215403e01401340c2ea0500444405050700c2c1542f2541e405520b95603100d40300fa5215410203e514060000f0004e070154081c080e00514601034201142c1160400c03035600d8140240728040742c442c3c0e140c03200309000a00700141d0b1504481d0000843d0305003000e03900100e006403040540f0154240400140841d4205030640604103580c0554101c030a403d070100d208404940b4140c441241140c0c0803400240000c0b80c0c01103814030300d809403420011441d012034070380068136000b120031508940c0100d014003899500d88189450385039900d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 153755872 1250 153754622 153754639
    0x1030f140307020d02130e0609010204061206030c0e0c0409020408030301060e1c140a0807080301170f0703020d0602040506031008010b0a14090c04080f010606030c140a0e031c030e0c 80
    0x15400100c252000000090050b48000c1c0403c50b07500c1c00e03034040451f513014841074440b14605682001e000b58030034042d08001c2114201d610410307a245204484c26203510400c0030402c5420322295210304a4021b0140580f0001004041030841040c0042c0000701201c2008546079410003d0180251684082c45405081c81c00216491174942c0e54088a126402c060b0300d8480310f038501426802c1042d408809040442c000403400200000080254100da101c0c2c07002c2042840002e055613150900b50752405030a5021600c140050f00d0407007554800c05200303440040c50555100003080c56904102c030340300480c5240704020429031900b80503060801408880040700705080000c2d0f11076902c3c10b07103401070042c0b45c2c0400040c54004c00c2c000301e034050090340044441c143e10700d0401902800c018051000080d05080a403200310740124042141001c0450580e03060403034012089610002d00c049007503141c40703941c0c02a64000c00028910018041d0b6541c049042c8952900f80d62500411603001070042180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 153757122 1250 153755872 153755887
    0x9050f101401060c0b131103010c0804050d020a03090b030603070302040f0506010e0f0604180f0e24010f090b0409020a23060403030206060112020408060c09010809060601021e010e030301030f1403 86
    0x82d0001103500c0354483c041c05400b144641000b00c91f0720400c08410340c01d0f41c41d024103041d81c01e03003108c6400e10440c4152f088038409010754104036110507680e8402800300c0d00640040c004d04050002640d444007001d000c6a13034240c0e583e00007400391a4000d81100102c0d942d1801d00050f5640504c00c0031580c5010344252071a81020000700702c0c144500d100e03a84080740e81d11420500c0100c950860f0900c01140d80d0140101d500c00c00c01e407615440c0203540c0f40c1034847c04a40900c213014090200504840820f07000110346440c18402d00041e200c08441994402e0340d0b010131100580d03a0300084000b40600d900824120107003040c401031f51441c4840c44070710030342040c001040000d50001c2d09541c030840a2a15030082411710200001900480c1c00c200c0650041008000c15042100b02a01d0a440700360b8401c02076454102015440700d100380c48090058010b806240311407088086002c48680c2da2500000350348100c0c96040e03086410a0300200c03450810b05481d407080c880e90040c2d001102c43d4540140d8a451407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 153758372 1250 153757122 153757133
    0x2d030207120914040b0f090903130608090303150d1b06020c12070504110c0706030c030b040203090a0b09150c0c010c08010608040308041e050a260304020409050f101401060c 76
    0x3200040b0f500c00c685441d04000a600c600040d504008006018044141028070b640e41d00d0b6000001c0d008110004500006003441c81400c025002e4400c17800075500d10740328540c00015074010001c40741e821100c0105c004d030008060b0102c10400180703070100361000a0510000a0a10052040c150b22500588002c2404000d01050000898108980004441d082e1903010b21950148003032150440c060780d90002606a00b6402207507803040035a50800c51180348104000403030105030fa05004541c4103000380e4000441440185400a007190b0898400c0310104003d0300e041c1000715140104e8480c04502a00710260074028203240d00d5650610841541c10507000911080d40208040c0800c58101c01107004d00490f900810202c400050004000350140d003001035450310003070000c0f01d260317020700203451700000412000c1240304102c582d000d107151603035020000a04034549040d160380c02030f03400d400520141041415451040941c000c20002004202c80c035a88505038441014402c02d071104000141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 153759622 1250 153758372 153758399
    0x4050f06011e330806010e04060b1903150f15021c05030c0405060408250605071403090a0f0303030c020102281403011e0b0901050a2d0302071209 64
    0x880b1100102c0d1058a801501d01c030203c903855003101144000c2110500d0540d000e54031a105483c282c07562112054100d00384400c40d140c91240d10307035400003403080020840c1c11560701042840c99240c040748080d6400c0c590585031b402503010002c100c9c1c1c1400d041007081c100d03502d54000001c440c005044416090041c840d002111618004104000000080e2681d140c6105440150801030a01a116a1104030b07141d80d400619840080644e076520104070790200218810f002d40d00e80c0d60310b140c200761460351407584441440c4c02c800d400c0d00062014850641754002101c0040c8055840c40b0b40e084c4c61401c014048508011403001103900400581c10b43c0d0102d10b8a06408415450f6201d41c04920f070f510480f0b411028206048840300e0000000505074441c068105440c000c032010ad0544950700c508181d00b5110350420140822001e120310440c1500a02c040c0b608001c02a22902440d009480055491070350240b040000c40c0d03001c0303516400d101050f01c00300c0302034500d424007440842c1005038248811 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 153760872 1250 153759622 153759629
    0x1150813030c081209010e010e120f0702030f151501080105010e0414010905060a050d0c0306020c0a05010908070b0601030b01020616020c040f0f0c0c110405040303060e04050f06011e 80
    0x20445a2469080500c500b804000d859005485a900d40c1c600700c20542c0281d00946030344002c0c0d82000320029580d0010b2040d001c4e072452103c002d14103503540030a2410a41c011500041c2e00b00e0301480140090b0700c1c24800b2101d8108950060700e0b0480c220084006840c0c00508911007100b0300e007203181804c0c0d8101382c550741952024200141e420407490000f8014064812903100c00324450800009c7c0c5026541016006e02411180351001d5500c45c4107110303800740e02c1003014000b1010041c0420128080c1d500602007402c1e2003064500c031881319200c0ca8251440c225044032445000202c800600c0a883c02c001c2e040712003481e080c482040b0400000f580c400d0302034202651141c0d01500603803814001c03c10000c84040140040c0704106008225500410800b840400c5543c20103800c1c0500a10800f03022102035030042d2082005480f140504c801007000600403000d065450388042800c0c502e02900034800c0e480341c4000c1030000c0207090310500b041c4044e404511000900d1940300b0107420030304c40d03080a4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 153762122 1250 153760872 153760891
    0x1704030c060c06290a0602030f090603040507170d080a050112060b040e160911031902070c0e010902090a050301020901120b0301180b09010b06070c050d0303150807030209011508 78
    0x341e030700e43c3c10305800030201d80814400400001903a2200c002e8188509500c50300100c94801082d84e951005a0703c034400d540d02c1130a0a45c0c00c00a07504d0603c1c0500180d6005070040f41115102ca480c1d0081450084500e0000c40c69039100c22040f0202542c421502603125040b0001400594900300c05101c01c031001150090100da00c130540d1248e5034446601504c40c030b0300b122048801c4148080404005050640a0100c45504014205000c95025001c8a00881c40515940048000c0c40b090a0003508510000c5030046006840010341c8944000b03018064116aa030044e5100014001c2094604141c0d100500907401481072048982e004134204441c1d01c5522004a0004200800030b8010800504250112805803108905001d0202042e41c454190710008012940a0104000c014001d1040007014510121001c0c425402c0c0b180000f04190722a0070041a40d212901161070180895044080c5940c0610420001d51903d4440300b8010310000611418505070144020318200c0f005082030300 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 153763372 1250 153762122 153762137
    0x9060406111603020105030403030f090b010b04060332040512040605190c0c0b0f130905040203160e0c07050115030813060509091302010912061b0206090d110111161704030c06 77
    0xbc1c0b40115800984400e03130311002900242d0707141d501c071380001c0e08036000340b000284c5403902c107240249200c1080a444248a030180e4134024142c3c0304481e4800c40240100c0385030207075840b400c501c03811070000340001e081e0311344415845055511301c0c244002041c0c8400d0b410011410003030008241c84c482d001d01944d80208905980303141036a0150000c1c03054401c00e180c1c4000c1070780300040b8240f44e640664040c40c401c60640343c03900c0c4020028030f2240a18000c0200e68034859001c0788541c0003543c010804140303c1d900220b140b801d02607c0310404122988141c5055034005803036060703544808413080c06005507080c103d0404807048045401c83c0c40040002c50045240e813500025a030141117002d000703116000c4050545900c0340b4154003c2c0080290002894401800c9041054008102c0d5881800254028003000c4403c030300480300ba48001c000d1a01c0d40d5038030101d403103107803401c07400504045070820300b120940803091030000c5d11078010327070b440c540c101c00305000900000b80000c1303007107080300d1143c5001d51 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 153764622 1250 153763372 153763391
    0x90f0a1214190f2a0c05030a0b010b07030908010921031401090b06040510030e060f0603060403031a0a030f1103030901021f14090d020c0103050907030f080906040611160302010503040303 82
    0x560f5184c1009141c501c0e40341c42510380740051241c0304003000881c0b0424a44444075602c1090580e00c0000c00300061091443c0801441081c862402411a66002c2c3c80c103200c1042d60307810b40c00c0c01c444030018107940e00c0131404000c103d4280d041c640381003044030a190400501d51300008c00c850500c8180180d110290303e41040b10f07165620003040d2405041c0c010261000d02d002908080d00410140e103500b2511b00805000880c007108450100e4030811016001e0100380d6110f0390308030f0080480b150500f2480e45c0440318406107444068400d40a14400c9225180380b10b124140310340780d601d442d41183d00c00c9d0f200b00001c0c1d50342e03680400d400d603000c03040303200c46600e1105c03070050071000d00001594010108261170400c0f440400c0091880100c8865809544038030369814011400d0b20f000f100c407014140c0c00300104100140408602880a0f4040d0908074248400d0000144003503010b5070010000030b0042ca1800310740e04080c4580401c01440340b282218031031450780043e00358000280080c080c19074410150 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 153765872 1250 153764622 153764627
    0x411032e08010c0203040f050406050f0103092607050c120d1d06030c0702122109010201182306040210030f020c010c0306080d0305040c0e090f0a1214190f 68
    0x8000781c0004002803040008184009640b80c105209402008076102e40024003400c0600c140410b0715400742c007400c0706510940055001e440c010a00b25120440d034980c00500d2540703d0b0001000c0c501d13038407005948500508045d450300d160080a0340c03251221300409441c0820001c0d100b0343c03281035420b000d110204401800a080c9445584c9550411400400c218046501e00001d040452003214401002440d111405982d034803a4616058440300000020100404410141c0003402e41480003003078691001c0e40c51110440c00400807204038004c09150300740d03654000360f03020341c010800000b08650b1606400142c84901d200031a001895074034101c4511940054040f10035940912009015840740d041006000f03200d00e201d0360a00c2d0090380e546000e02e51090244900454002400e80c03010703414500340c0f400380140940b08094031302c41d110f00414012010300c500741f10b0314050380c0980900303001ca0202500340d50f40300e00e5a0030f40c0102005100303c0c030385405200001c801150714022014040d9071006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 153767122 1250 153765872 153765961
    0x20a090f081b12010e100c03020a020a031404180e0d0c080304080d1404120e0d1a0703022701020c04110a0f27090605040b090403080c0706050f0402041103 68
    0x3c10050b9401c152190404100000c0c803070b051028108400c01071601544400c40c22805400746c1d002c01030b082a1103400200344903078030311030b40380c0ca111403d54a881d80e665140b55484910f84a018130032a201c4e803158940130409c0c4035a00b03011b855030429800a00c500da803000c81911000f8001002018041164401c9060f8ae41c403040304801000107403191070a090518001a042807404100001c480d0801f0200750300f0031b0319011001550100d692805a07800010500d0340c440c00030443d00c00c00d54284501245040070710540c3c6242d000300050541d50b00800d4000900341810f5035065805141080e03880c2804502d103500312000e0380a44d00d800001d80704012000c40c0c41e100603652407120000701101255030004034200400480351003000070400599107905100954261f42000d5a010700d41200050100307000b400c0c2541e0042d40d03854124a071070f00039074845003240e07401d69800da51310036003070104001c5040520070032003030105504001741589000e00030004055804540145450100c180c20800241581c54 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 153768372 1250 153767122 153767149
    0x516050c090a0509070510120f021213050c0d030c20040c02010b1207060203070308150307030f1b0b04090902040f050f070207060c051e100f020a090f081b 68
    0x29890341840b103030328006400f040c1d491010742e024060000450340f81007010100d013000b003902c0d155100c200009240d401480842d000310b9480c1e0302005161459041c8041d8184580100300440d103084126080c02c51403c00c010281502402103802400040790b00600505501507105054403032500030181d14141d2a0b000d5003566401c2400c100c0308012036074064001c0c22040405980300c15400d071082100e165074111610039903000da001004200d0201c0d108d80ca4140d40001c2d00e032500d8003c15002004a0724010303440d80301396028100308880108000c0149002c4112941d840c0001210302d080c0008120710f0310640c860003441b0741d0b5030b000850441d1900d411850f40c107041803070700304898a40f001c500750704c260040741c4100040c083c600c0c010030864014000c0c0a10560040c000b03280040840020040c0030664107412004c070311a00841b0340304100e15010700b150b20445684090380301c003001000076001c0b00980c1c010001d018000201400301c0036000880f16440c3d0135001d05200003182001c0400d030f00da83d00c041c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 153769622 1250 153768372 153768379
    0x70f0608161206230102060105060307030b12100c081501020c0f220204050a05030a0c0501030b0604090e0d12021c0506012601030b060d05061506130608040606050306070516050c 78
    0x30000600354640a04c96140c00c03401107103403110312148000498440200f4000c03141c1c80035003070012500c1d0724800d51120100c018054030184c01c2c3c403d516802498010f004181c000e40d07980b6031800d01c1d41664444600c43d0004488800c0119442440740081e40311030301c2030a42405082e640c202c0c1c5d1a0b82d902c02a24070411400c0c03948505030191545208406540113000c0d0034010003085c1c034005480c0c200020144140b54100c400c2c40c21b110300300001100130741942c848966004100780130200ba0400700d441140056a03190000b0b003150b0910f030001a1500411001100d1f0540c4123012000341d40d803168254500d0510f0403200017413103681c0c85006850031028010b11020303450181104400240165290306e058034001c2d4030b4003802d07503100400c0180c1610140c400801580260010030446164400c41d80d4800700000c0045043c030b82c0d040f00c5413200c08416401400043c6c4404144400d0020074880c44015120a4024240601d048e06002d0882d1046030b05e80000d5044074128403052220501c080e056050004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 153770872 1250 153769622 153769631
    0x9051f02040f12050c01140711030c13021206060a141312050709140606120601110321010e04210504031a06010e03010b09061009080109050f070f06081612 68
    0x11483d030300c011034450300221220312820101d1181766010701c4903104807807044124a071805500b0b594011100702801003164240c40345108016066840ca4050703d202c0d4200000181c46e001014100c103410b18000d0718507401030604112500320680d00801c0c42c140311a07441001035480c1e0854142031006401d9600c80c2c14400c0c202040c101c200003012501d003089448030307102881040760928507104848170030342c0c61551084007000b2901107030101d0b42c24035a00c641d0504020481c403030030f8060a801d65110f054000c0c2c050344005c0300d00100344007007610140940200021141c06140c165210a206428185c50ad038441a844a84043d1548614201e40141d54040001c07103030007000e2081205050800c1d5402808140c1c40500c00069040c140309500c10504d00030b01c081d26a07110784050100c01000701d4180b50030480d42d0a008901c0f802e007409a1075046e4842d030700500c8400101101c030340c01c10185070022407001088070b000b0030085500180a9401c107120380c0d28601c582c5104581541c504484090054945080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 153772122 1250 153770872 153770879
    0x3100b0d020622060503100909020102010f052a090a030b2203020c040b1e06030601030603020a0803090102010c082e181b050c120c0102090a0306050603010c0309051f02040f 76
    0xd0000035241c0e180c1040f034070004075150345042d07445010440b07103c0e2455007003003010084070800790001c0c06503600600000440c16110b2092109944c81101ca6481407010855410100004418488115207000c1625030074844540c0c005200b01b1401d100207000060741e403020a6060803654481c40307106905140c2c1d03101e80e03c941e1602944404100c154544200e190047e0104c0350308120500c140a085020f11041c0c00c001d19500b00503a0746c20203481941016a82d00020005031500b5140102403e00382d001161200d80d024002801d44241169000c02c210003401070100071605510401003840706a00b1090070700103401800b01c2003442580c0107105042001400e02640002503100031803200104c09544040d0015501c166181c1c0304900017100e16a00c0800c4442d41c290140014204c900c04403400946442c0c071850004161a15a0700103450300381d581c005006180c030f424451605441e146060510804800b5100c07a62503416840b44c9010080d01a04410b401d8091a4120760103046ca240e180700300c01e0384 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 153773372 1250 153772122 153772147
    0x3090b0a0206040c0e040305030414070504060806010311041811010c0614070206070201022506060305060c0a08060411090d0f0506010b0909090309060304080703020a050d170604090203100b0d0206 86
    0x40c1c8054400401481d804284440190301091065070548c1310f482c0345864030f54600861004181c3c460b131185c050400040740301d585500a038401001da00000300010750660a2a90401e04403006180c4a00d240820000000043e140c480c0d02140d000020701054082100045c0c80200c80310000600407450150b00b01c8001c1c0104070001c0c051750381642103e03e5170f540e02100ba802c0f407041195800604251614041c40d401c41c0e01c0349860f00d54031444000c22141d035aa51030760b15018090301c0c60407a8040201d00d5114095000c0c0c9442d900102c12203051010652250701c0302d0091240c0f9a00c18085c0320806516403e0041c4c24075010340f25540007040b5082c942c0e4683c1c501c2c2071600420002c1c0d1055806001040152314000b0644429020081040340346841d2030352040856444120110305502400882c1008104180458801195a51180000256601840a503541c8000c200034030441c41e0003100c00c0583c8001503500c440f80300310340d230005034001018005401107211800003540820006a007103403a94 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 153774622 1250 153773372 153773383
    0x14090901030b090d0c0305030621061503100c09050616200411090312090a1a0a1205090c130b060c0f010b031920041a030709140109020703090b0a02 65
    0x5a0b240507130f4a0208141400c8901c000030000280018000740045281460b00040400c955200310340802c0b01d22440b101003604000c000c9402c1c400300c5c03080044041c04d41c24188000d514650500300d00300103007021441d02a1514119000e45401070744045100b1002402200171b4051171a04005080300b080d0000100001c60b1221003032981c051400d1a26103e0b24074410001d8800d04000213001d8140ca18403c5940b0306c60ba084440c0a1b42d00000b5800300003405803000c0c2c01600900a82110160760f41d6424078080c0031075680e10001081c003882c02040103240b44010904d1001840c080701d961020341020b90418014000302850b2a41c00700340003480c10500307036001a100c0c0010389600d000f8054420603401305521035413562000ea4960407540f42c01c400040002c07071035260b04c04550038400c4007400a0b0b0b01007821070f4401c2d29580f450109000c0b4200301c0e480d00300028801807a0381c0d01d040c40f825403003801c084003155040c440d40c5003590300070601e501050300075140c0001a00901c5411034480a450000950310b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 153775872 1250 153774622 153774631
    0x70609030e0d050604060c0302090a031110050f09010e01140f031f03050a0f021807020a020909070b040b0c010612030c06061505070803070c0b13060b030a03020c0114090901030b 78
    0x1c0e0140840d2401e50a001d0441c00c0c4480d0000003500300c03607846440d01006882c0361442c4004056003004000020380d036200e41c2401840c020040f80344400b105400b444040d00b9010700400038030500b800524105801c0c102101c800843c2882e1070310b0303412039a0300144c500c003110003000c0d14504008225050030042080280d4410710700c42a140d8035072029481110740c4042e40c0c0c01f0182140e08041400d0000c21182d01c0343c0d05010744007406d0005400c4122040903070700c11003a00e245005070002071001c070030351078403a5407503402c2407004018000107485c1004081303052082d40718888131b01201081c03840c00390f24294030400081c100021008400003152600800851007010103c4142d0b00d0301e03102041c9413030340382d541e50f4640c05503446151074480c146d00d8145250700020101d9081010340345c070401c00101704581c424082c45103102000c00744101c83c607042042c1c40c000c0399254020f5203c41100d0001c43d90000381520b40034070a08040c54144488010000b092061f120351a42190340b6a00000c10010941d1149218 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 153776978 1106 153775872 153775877
    0x9150506090a1a04120b01030308090622062a14181e040e06090106120b0105090408041505040f05040b0f06030a0603020409060603030201050c0c03031b090607060903 73
    0x18000c117441112070900c000010401c240d0403003407550300700c0d00060141a00c0c1c5410401e80720982c00310200762240a1026844c801403180c10781c03004400700b40e03204944c4a0300c1c046450072040458803c401c60300040c1c0b01d2000000b00042031003695504204518148100d5140000300b0007242c0495100f0822001d4458603200290b91701e208520b440781c81d400103072040f0f107007403207500d402c448940e442001c80e68a0007882d00300294607800d070f0f01d043d01d1048803152011703201d82c00c2c00c07465801107420080141c0403c0b20789403e2960000050412220b6619003410466107610621080e10340900609422441200505000b441e000001c0c507449105280000f0340c41e030366a0000b8042ea442041c00b84c82180e59404184103160b8280903035a449028018102e14003030280441c07555900c402006119800814510f250031007a28800325090b0550007070405466140c2da0800c200200702c8014203c02 = true := by decide +kernel

theorem cover : BRFrame.Cov 153597122 153776978 := by
  have h0 := BRFrame.cov_init 153597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 153597122 ≤ n) (h2 : n < 153776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
