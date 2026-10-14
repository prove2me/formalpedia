-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0022
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:24:36.874591+00:00
-- url     : https://prove2.me/submissions/d4f40b08-c086-4a40-8526-e8f08198e456

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 3776986 ≤ n < 3956842 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 3778236 1250 3776986 3776999
    0x180c0b1606020a02191203050c030106080402100504080102070b040b0105010206070212090307050a0e1902160602030a0b0405010b040306050106020c0a090506011205010603020c0f0a02030303010605070602090406090501080c090907 101
    0x1880846484d00c12210780c0c50300302c0d1042c00302c403441c8041116501000040c103d0700c1034143c010264840310100c4400d041d0741c901030000e800800018802481002068169003441d0300440955002e407071110700840d200c07030041c40d059160f07000680702511440f5644000003171542c07001070400d1080c5160ba01810f015149640f000e0030347d402030300010390b00d4000e0f000b02161355120040008020041440300e0b000070300f05103c5141031782d65840d5002408900400040318480e0030408003c202c0e5901420040e90b0755241c0204000421081c203034103031700906240c00041c1050307a500c05001503d014100820580e641c1d040e041c0e0b514100c014406401c8801c845080001c43c07900c0c1d00036640480103050030600680d0441842089034000d82008001c80d90201d20010080350400024613000320040050492200640009649000503c980c41c100240069a101044095015220100806041070001c0754130340071400050102406001e005101b5046038044c00d2410314261401810b0242c040d103206ca0900c0c6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 3779486 1250 3778236 3778241
    0x14030309120304030501020a0f080603060402010806010c0302010609090501090b010e0f0f07020a060903050c07050f06120c070f0b01051005120106030507050c060103061407090f050103020901030b04180c0b1606 92
    0xd00344412408140300c0003005c10f200780010003900314a0b6941340000d07410078401504500d00a8007031030080e40101c041000607600324210a401c6042420b094810441790318040b80502800e802c041d2a19080608020070054150490f0307204034800c50004640340e0325001343d441d0745031085440086c00c80b100d20100e28030108404406401400c1031041c1c4420740025280c610568003034a0048000400010b54002c90302014801d0101914080b50b0b80e135007560400c1e0004183d40541062000d050f82e500e4042841002c81504039000c0035400082c440c0c042c840350808000044092041c035000e50710000c5403220103031148044034900e00340c5000083d51070342022401c80081400600d030400744034080080700c2210208001c511b0096209140200ba80d007110809080f504001415000922040344002d01c01317403401460940903982e0038130f00180c4030714850b001200a001030700742458005182c242c601ca10f07260800c0da046605401070242072040765179204104942d01c41ca07101c4143c05002a10070400007000d58 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 3780736 1250 3779486 3779509
    0x3030c0901030b1c1104020405030c090a0603020a03140d05030106051803100f0218030105060901030f0f02060301030501020a2c040f09050303010e01031104050103170a09030507081614030309 84
    0x10b250002e0b4078030000740418030440400340305074842c1d00c01161000030000428000c0d03690400503201907003443d03c0d140110f5a6045412015440b138041034002a41a1141e503001030010360f001406520115a04d0a0075001c00c6030200018401c0d009252010102034044e01c102d90484215558161401100c02400e0358010602d00c191945800fa81c0072440c12585c150145054400800d240140d03511051003500003070036000901e950099041c05d040150980d105900070341143d03046402846031052301d203440700340405c200c400203500580c0400048240941580a480965410703220b1100c4a087c8055008070409000101e1080d2109401c00940c642044d0b0081c2015000910f804103800c0072a80e00e035815600241c015009a400c0d00d8010010301a5850702e07103a4180003540e08210b20750554507099080240c00074140c10103080080c0c0c0316022172083c040c0c1300080d900503003550300e03150f2900d05103501ca00000701c40c0c1c81840d41c035403004218041000f00c00864420018001d40c50011401c0c2402a07060300c9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 3781986 1250 3780736 3780739
    0x20a09050910051503010e0703020a05090a0209060a080a0b030703021e0604080d050306100507050a080a1b05010c0e030304080c0111030d020f042409090506040204120b010303090806070203030c09 86
    0x1082c10101100016001c3d02e4050203064020000003040503042c1821200c03041450029980030100802c09a02c50400d101c040e110140e0710001a9036070516214068852070740480e0708030000280740c00e446544442e00600031003c4040c107100c0e40e003a03407041558621440c08081e5001c1c16030340ba016621410201e4410560f0f9005d4075540c1002d640740c400504085080d800440801e600008100c1c4034604500100c1400900381085401e1082c80c1e02c0e03032036444001c0e050081c4200c0c00042e40a40031402207070007402880c0c0721303458003c1448044c94180e010b802034003010004140280c00e412042d150100030f841c2903804d0340300185840000640110b030500b08280d02c41c020350001f008141549034050009000784100c10414944d55490041d5811000240e46407100c2a00c00d10004181200d600039401011295095030100e01511200d0003d002441035500c82d80e1440030403011202000907411810b412a8041d459070741c42d603a035600320aa240d51044440c6070050b00704000203a5440340c014080e0210440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 3783236 1250 3781986 3781993
    0x10608180d021f140f1f030c030f020103110318070501030c020c1903050f250503030a0e060d060303030905010506010206060108010303050a02030f0301080a0c06021204030f060b040203040f03030c030603020a090509 94
    0x4840c5066001850180d41d0000408128003c200040342c0c0c0c040300e0716050620300c8054070140e01e1f40d11213914048160000800d41101d490b0720342c0640e882908419480c4403009503e0780c2d40d04205000000c0803a0740d6280c000d02c0d000746000020998024803c2038805000707130b006001c2d1408040c0421810300034900c0382e00d1202d0310f001004000f00e00f0410148281102201c014201040044018480c0f03032000640811126021803060020f601e01206840c440036003400c4c00d400016012000404030f0290b80000100746241100003c00d043d45034000740039081c0100000c2100751565401281c44034012554280032691807001007001074882c1006240030300c3c591042d05e0414650300625142da500a13030041d400d07a4040c104d10700074400248581001001140010305649244140000c80c5000b14840074105d0030702c0060b05814001e580c3c1180c1040038005104642c0d80ca003620b414182a43c0c042c80c2540024035090300040601e02030b06c21402130f02d40007841da0501c01c0c030340b80c40c000c007910000340103540c03501 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 3784486 1250 3783236 3783251
    0xe0d12050606040306090305030403080609040305070605061201020d090c050a03020904030c0f05030307090503060703050907050d020f03010606030c1d0102030702060a030b090114130501150302070302070806010608180d021f 98
    0x5c0c003a1181500c014880e030b40303440d5641010304000300741070b070041c1c041403045031244103000019070030208440fa010350081c0f02040c243c0c1d4110000f080a041c05402440650000940360b0b02c0103030b550301c408801446003401110081d250814080324113480c1c04000d40001c0c9200104010074003401080343c004c4d00c0f440510304096081e60b80c6909542013502c000011031407401061140b45410310500303071300504500d8104014a03100920f5941d810a80c418070313005542c0c0c0da0300c8005544a001c21001843c8000e00203005032135031102e004005107188041c040029a1710001a1070312034040d0761400700c600c0140d006500f040c2c1281c0801c100b90344071f40242024550f4074403040f0642c0e02c44402660003005504c0c5980c040124640511515100f00c0400704035481c41d020040c40840c41003e2000b17112801403500580f15445403905034a000500d0700000c03002e00c0f502000203211a03100d1074542c802c2d0180c2816090001c40c040c1c09a640b103049003c00800360b0806146d0000a042141c0c40c601d1441303071000003080d00c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 3785736 1250 3784486 3784493
    0x402090d210306090506031b0a05040212060406051008040b07050c0a050105010306050c070209040f02031e06090c04050c07030c0804090e0606120a03050a0503040510020f070203010e0d120506060403 87
    0x641042098152521404070280780d9103405104942c0206041d84c81404149001d100007600c840460000a0140d08004480b1081e0340700d0b9940e58001d40b1006d001107548083c00c1084101c046803c1324194440c905056020583e4244081c1e050300c0e220312500d6240550300da80c0e45040114034000c00800070000280304d8807241c107100308040040540110300000d001c1d419400c054094a90042940200c0310741040300c0001600c5964107140e0182e0413040883c203542c01480040d041640b000200304c0f9103003040403949a00b81020a0081c080c514050455a41c00a01e13014013003603c0044601030300e008814048600840d0182c00c103501c030390340300762285031501d921016090101c51400411602076403020703041000a08200240802c519000c0f030003030410200c1650000c020f0b110f9040c0000c108a404800300f01040010000b8031229008a507066441d01c00b10114600750340c0124105078480d43c20701c00c1103024180e0102e07240c4041d0000c0e1742c03140c81203100a10703008050701000d0941da4001c2c100f0040040407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 3786986 1250 3785736 3785753
    0xf050d1512110a1401050904090b010e0117070605030106030e0a06020301080703060501080609071205010216030509040c0305060306060d02010e06030a020405090703020405011209030c050706020609010f020310050402090d 97
    0x241c1004003454442003040d06209040400b00e0020b1405031400003030521000c0e22102450400d0f541c02d1074001ea462060001040150050394001840e9111890010900c02d40c0404400d060b1a000210403409120341e40780b0036030702e610b248034840115000b0801401443e2007600004200907911301140d0040d9107580e1442c04981c000d07480628103421040d020310030001d4070b00030b0500400070080141007506103810b2890300e608103880703401d811100e0403911904203c000e4041c0d90400960034601903540b81c45050113461540a03010a500c120b1500000018980c001d118a5010345800303001400e443e5264403d01a02010080090303050000c0703400e410445a580000840c40f038a585a00075898034680800d0214a641c040d000600349130050105203e207980c44544c6c0100103100304070110f8031483c00d042c20740c2e140340c1045015042c1c0c02130074801300e451600010b44501452690008106040c07000001504a010943d40002100c2040d00100b03c3c17031500307401a1040f594003c10f1030405181a03544c08d00d5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 3788236 1250 3786986 3786989
    0xb0103080301051915031e0203040807030806010309030207150c05100603060605010c0510020f040308120f07090302030303040b1b0d0b010305010e010b030609070504050d050a050f0304060f050d15 86
    0x14031050000c010701c800d0924940c1e07101a910320040c624003a42c02d0144044919600c8007200c401c25682c0c0c0e0440030a4068001c3e851b0705210142400c644d282041e0030b02201c03560003c0d1040d4041170040c0c021415652003442105084c580543c00f400701e050030100722240860780c64481c1410040d01c001c50038040394003480304010074071035144e0014895245150060680781c681e0701649c1801464486440071a00102c0d2000244c14032520040e900c480300f819441013805150805003c440010840c10000600c40074502d005003450841004a9590900b0489009805000094041c0c0050010500007504004480d802405031140810420b0498003030240701c2d0003840b100300015889121002c020358052040703078050003107010214103d60510341551410b00c0007505190240c0c50540028100600c075000723580c0607000042c00302c0301d8641c1174140503a503604038000a44050090764048120030500108850848a0355200d04011254070749083d1480d8014020745407006441311000384402c1d1a6414110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 3789486 1250 3788236 3788243
    0x15030d0809060c070c060302030c04030f03050a0801090c020a0f0204020405030f0313080c0a03110d150902031b10050c010e07030c03060c0c051b0303070c030b040203060919020405040f0b0103 84
    0x1040d0320349441860329051002d000703400800010000680030030452406502580c03000d00b809641c079120583d4403001d1340b01e2a400608401840090700d02010f0340540109501c2d10a82d03034105103070b41c07901001022a000030700ba45001d1ba0220388030384005000e1500401c40540000c00c0141001c3d6158042800c120096081e20b08540000402007004000750f14210040e00e184801072000904c0e050100d100014280800703046c90541104007141c2da950b0491005036140c1c00004220a040c002d10000b0180c00d6114040b8804d00030403000740b50280c03601420262031180203003190742e424001d0f8002e9070303a6030100030200f059548031003c52850b5070040020b00e0045103c1d0301c0000d030503455820154100d0301402240000c0040e00c400d02000b0550000b12500b8914114443e41e940c0d08001001a1451294500c000d04a042900c80001400100400c07175204500a40580318180c0d1180c4030f982e1141d103480c841331000308600d0307505005824684d001c40c0e413041c81540d000c146180e26440721035840c1026030048 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 3790736 1250 3789486 3789497
    0x1030302060105100f080f1306060602030307020d02060603030304140a0c080c0a05030d091521091101051c0f090803100302030c0102070b03010b09040207020d0302012c0604060515030d 81
    0x1042542008510010121501c1c58201c205111700e0500070098130001c0c01c404400032604010511420203000b0402001e50320200402919035680e034042d48a41003207403102d002d4024540404e900714000300c0e850344110b9004000d14919661a5509a82c0280800c51400688906514100041c600860302005894181e0040843e4402c1c0c0781004001c009640002d800b9401c00c0c011100244d23000f80315102500c050040201914000c120200d41c0f0309942502803030250001108105000e1803a8014600c443c0188010224540b40030015181441900300d2162000c4014443d0424550141d00901018a074000b02041004450301c5410361a08255408484510500c1040086207802c00021007480d2003030001e051514a42654840d45001c144107080c14010300007480001c5540b581d04403401d0075802040300e8068825410001e00810b02030110701c550041042060070381d16545440100000318620083c03a82c1d035203591b688005801e001d0001011060300d0030f030a21040d40c05001c0c005041c1d410340c2d2034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 3791986 1250 3790736 3790739
    0x9090f0706120b0d030804020d05010f0c0801180b01080703020a030227030601140607020d020a0302100203030f010906030f06090501060302060408031e0304030903020d030e0301050a05060306102909030105010303020601 96
    0x3854221030f0114081441800310144c2c441c0000d4124003404d44c0241c0440e05502950102c1c2040c81c090905441140982031a1420720040a9040f480890588019050315407560300701d80c26600880e60140209404500100e000400303291194004041d402c295203009414500c1a2100d1503046e10807542480c5280c43c001c0824026040400007140104407081210300d803405148080f601034400d02c07102a0040d1081100c03142551990081c01004503409403c2e41c411401425000392641c0042e1800c014001d01c00c0f00004444080340107035002c1e00d030482c450240700111641d82c0002000c7d4240b0445e815500e5000000141e902ca401510080590001841e070b00e03100c040b4000c030b016501440d9044140303010b005000109a001d145002540d070305450307007003010710303c1c3c10282c88400d08401101d5144d801e20081002c844925004140500320070f9086444544034122280200381c414054600200281c24111003011941036071030aa20710040401da14060f220008207094520980007030703002d41d000300c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 3793236 1250 3791986 3792017
    0xc0f090f060b1606020f0301090b0901080109020102030405100e030604030f030608010501030f02040203061201050a02040f050619080604021608030f0c12070507060b0301090302010608070504060e010509090f0706 93
    0x21040000c204250400401d8203000b03000c081ca004200c80030612074070038070754001082640d50407144124942c01d0056141d69403030882d00042d20810320300c140514507a00000502060500601c554664142c014505145c01c0509107d060001c800d1084200070b1514a03284180e20240002d901441c02030b945c0306640d144005020701075031015403000340d6681c036100c010008211b058401c844d400d58112005650703030702c4080004580e12100c10880c102ea529203000c2c002800c0040d4002c0003102e1403914850440c5555038100310160117030050661a941d01c180300c0e94207440c0700c1c00c4003540c440d000900c0107007030814aa0b407407101909000401c039088ac90000521411154192440758070500c0080094641110411220903000001e000b141c140034010030a03404108044e0044d240e445070240080116580501f0000d001e00040d11510310f250050030b1000c40c19040c94050708054900d101c0c0d50003440d91801e0203104150398002e00101c218003517060b403a041c9c03c1092101a00030400750399483c9120407a0300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 3794486 1250 3793236 3793241
    0x50420181f0807021612021509030303010b04050a05060f0a1211070305030901050a0204120f0c090203091b06090303090d0503070525080304030f060506150a030603030e031504080c0a0c0f09 83
    0x1c002c101e018410940400540c0c0e44820040c3c0007c0e4152100d94055840102d0980c06004503019294103001c040004500b00c41f0441c041d00444400305d4206a0941d0b4038014021a8490a400342901140c104900d02980d80105540000448580700000300d203040d96801030407a8200e2041100001d4000041c040284024080c0310380040504504602d0503180c5900400700100c04280202802c42c60a040c4045c00b181d602e092008051403403080d9500c1c13801c040040d03110b1000c1c40b50801038452501c00a40281400d00070382da01a00c01070010761522940b2410040301c1c6001080485681c8010007107034000883c00e03c11207540000c00389883c0c04941c001c81144000750a550044c01450f80284001c0010880c02c4064061950b000b280c009401c0c0c46c1c1c0f00110380c001510740c00c0302228001c0081c841403160382c10b078803510443c2d00942d06c00c101c29004800b016200c8585d50840c0880400780030204020a8501d07005040c050180801c035101c0d400c080c2d80b00200d83c2240c0c4d0040ca0000c005000420480d050350 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 3795736 1250 3794486 3794503
    0x6111c0c0c17030307080903090d0303060305010509010504020f0607020604090c02030a1d01020a060f2003011d090303010e09030c010504050105100501030c021b0a080102070507050420181f080702 86
    0x180c0c018240100c50b00c07001d540d00c1c0002050302c0100300101012400d00b50302407048400d80744001c2c02d1101c200942c1d0038043c02405651008030749a40c81d0000065510006106060145034020424541c0807690020400c403508030610070381e840103080000244a2200e4414403072103ca0720780245440342801100540000548440c0b03c420350406081141d0301d1b0703400700d03d01400582c002c5001440e1140c88219000a0400d84a6000d181046182c890810000c3d04003a504803900504140b4441d0303207110620481c482c00361501c0c13010798018401406004410b49849501100074000c070790512070240710860948009603000d5a490b5036500603c020f501c082001c02d005400c00b030805018008030408002d540c4c0303844681d0f862125203020031881290b985c2e140c6000c010240c0900940d185e80d22400c0040d150200c505c9030a120758030b040b41c0404850907443c1d2101e8600c2d81c00b04140e050034a040c00b0b001103952030342d503059031106000681681c10000ca01c01800c0d140c2542d51801060b02c0c141d84040d14003034a9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 3796986 1250 3795736 3795749
    0x402030f090d1106060603070e030607020f010608030c07030b07020a0c0e0105030706050c03030f04030908011a04060602070302100309020112090303050405250501050c01020d020c0a03090b030403050406111c0c0c 93
    0xf4031a15000d900c00007902c80d80008080d41d085a4941d00c1180458402400c4900c4603454094a001e2000c0107a000680701c621000590080140c603995005065891045130b02c0442d0b00e80002ca01080820f0034510b0640d070010060054407105030142e654803480321030b550043e112200019005214506042010101800142c02c140c0d1415202c3c07007180d40e4030f00008040c095604000d400190826103d00090030003801072000a200e50808005106c40d44a002110180558681600000e00503c0024880c045903009030441d40e0660921500320041d1400d40c43c01e0f414000d14210f4800d5100e0603100e0841c82030301a80c0d00040710300340389c44c09508001c0380c41e0f400195050342840c481000200b0301259030885009080059544e15542030b041e019003c1d903031621503c1c42c808140c01842500101f0300321007041c4682e0380c107000a619602d00989a0005540c00380006d0004e00080c00224000c00c80d20085292a004403083c20500c8054034003482281203920000400c0d09142000304002c20070724a000e07010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 3798236 1250 3796986 3796997
    0x30d090810061a0304020a09050705090102010b06030601080412030908040f0303020d0905061b0a060603030206060108090604030f0503060609040501150306050f030303070f170f010f080606090a0c02010b0402030f090d 95
    0x502520801c0031580f5070ba84451407007000010404559440d0700d850000e05403a04240001d19040780082c0040e0044901c0780c2c059428084c00361001d18107001201c0c81404140c40719200c0fa1999140c60205500c3c044880d8107150356a10020041403004015100900e58a400584103908620740241442e03480c0400100b84070401e002030105640b084241c1741c1c0c0503440583d0201c0c050808440914010180310003400ba42c1c5016400320902d0b0f80130030310b1440b03494280c0b00c814040e11001d4460340e80300002c64014000a04102e00e012049104100440c2c00490080055085c2560704c40003d08461081c1d12190045c1070070350140b10402c0c1c05009101c01420101d811612108600d00443d40b00e10000700020104008000c0c181c85980c05601c80018400c03403105884201d207881009410211302c01e0248919155038804001036001000402da4850000902082a40e4558005500180040c0240305040d55200c2d008014282c6861015620406001d0019149418295903480c200260794200308100304 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 3799486 1250 3798236 3798239
    0x90606110c0a0b0a09030c0f060215090d030902010c0b07020c010305060109060206040206070f0b0405010504020f060901020c1201110a021c0306050303030112020301060b040306021206010807090303050c010209030d09081006 98
    0xb0b9a038110740c1d0850780700b100e083ea07440030100c60031225010b4940008005080b4100f001c10610304a03049a01622860780840b40c9141c8a41440294807408607101c0c1020f03881140d00b554032a100f5080740e0707a2270344181050406903859943e0750000311404c580c8140181d0220219126660b89401940d80100e42801c055881c14180f03040291070b124003c0c000b078000d0034001001010442000d03408407126400c6006003929041c0703880d1481c040e010a8500b40d1280d4804141001d55152840c111407146805800620003034140c0020701400384207801c262086950381c2c5000c00451440c09004104d1000c00ea07000d000b1041280c8680c0301c0d111001c007804801c041c40e00c0c0040c041b0f600c001003200d040d1021403491003a01800c610019015020540024408401c0440c0000800400d60040c00c007070700100201000c01d60751500111154802140c2c40000074020700341c10400710340103000605001004800251502c61001c001c00d2918401c419007600242c1c0058003000512014801600c0118601905201c040e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 3800736 1250 3799486 3799489
    0xc080c07110a0b07050304080105010f0e0a0507020c0307120308010b03100b030405030f04030609030e0f03030d090203010f180b0a02040b07031409030105010609051005040302090a09140304090606110c 88
    0x60003800300041031a0789050940d0010b07a00ea101000c0103140c5011821381d80d02c024a4169240d40052007194125030030840003081d1303940803581110a59825810750344281d41c035080d20340c0291602800400550060443e41d1807036032000d000c42000341c400702001c0740c6501c0b00b505e0300030b014880581c8120b041e180300340305022440000f0a6900704031810760720303040e4680e1a507040c0305080d031103020f03948414800c1c0090700108001c080d07002003032014001d496281e9180c00c604107214149840780155503140d0420440a005940180d1141380110700180001034030045404104044030340011040607d0001191034008021041a0b080d40c044070300e00007075050a00d00005841980a00324004041c08400d5490b888002c883c44241d8091640c000d000b403140307581d50080038060717060031b02030540910360b0700400c04522400f4070101c0301100d0740a40403403510360310340c07001000a01c00c8030401c03a030a522003155440511010009000034055031100025642d240000c017500f03094140c8190903954000b19101c1107507 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 3801986 1250 3800736 3800761
    0x16050c0a030c02061308070609060c0201020705060d0b1302030f06010908060f040f05030d0603020406080d02030301090510080a0302030306030105100302030a03140c0307050106090612080f0f0d0219030c08 90
    0xa15031500b00011a019684000340c0c50740680c040380465010f40d03c00c0012003100000703580041320810707101c2c02e001e02c0e101c0408480f2601c0746c10004c0e02503440080100f01c0340c240b040c01030001150404000a24092000000302c02407942804400b2003034000c014020b8401140f01c00c2c42c3c22001c2400c0c071807840f5183c03a08594407000010320b80e60000620348002018010b00a9500500301e500c442529074840400e4211070090449000c140c2c082c40c5010808526003e0000d00c000c04094150000c50030b582ca043c0f0410040c001c020085410704183c42c800140d00711040040d0a8110301c00d401542c0c5902d041c070241421980000c11031500c1d081c0100c000c1001da140482d5101c219034040c03514012204003001180308500c514089985144400030b030850034840b042d40079006450b0030f0340f418000302d5030b51070304000c0c04d40040b03102808168040018140b070300040b100810b1500ca01442060a103940e10b00707400102e8108010200c0003441c07140b04080040d60500c60a0369180150038100d500c1d04103803031556031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 3803236 1250 3801986 3802003
    0x409020405091e0a0b03030d050406050702120f0906090307050402040f031502030c1902070302031b03060906010e070c1505010306090501051b0d0b030a05060112150608030703080a0902120616050c 86
    0x1c04c1a590300c00700302161030610440381107203a05981840181070628003c0c0040c5011910440140602810741040504c80b000700c1e88a004003206203801d04901d4000c020380c60303001c00c070115414480c03800c0020b01c7d501c0343e002070401000540100c0c0303195842c600300040300c2e015045070000110f204008100590404609980200780400410503101c0d40c070310b40c2a442c0400316080658544110114000134455501941e10310003800e2301035504903107441c00100d607180028095000104035100c006207416128170000c0324142e006102d0445000748600740c81c000c4500030381055415a4039a400b507000e10509004650304003001e034410086410b06400d1030700550240c1942401466103500f0504400e6408002040c042034004007038640d42e5a6030841032021810b00b48040342e20307004411121074882e07000e1185134122100400613500c0c1c404140d40803100e010009144403140da41d6038610401503100c048005900e4407040c0000c1125007403600200e440807c24040100400c50100105161090040358814 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 3804486 1250 3803236 3803251
    0x20703050d09080c06010b0c1002030105090f04020d060203070504050a0608040b010306020c0709060801020d0509060c0406030f020f071115090609060c010204030206030a02030411010503090a11150409020405091e 93
    0x103010401450660f1280c840c0c080300c2829807141d5800850680c01c0d90004020650000080301c90700300e020030b0301c1401d03030009200c0c043e0701680503800980710507910a0000ea005e032008000004212055031800d003240c205075442e00025070041410710190410034242303006014141040302c4685041c1e660030704501da05000061480746c0100f06030704c10030350800904000e04052036090000350f4407295500d000f508500c0140000c541000c000c00c140c400c2c003141250007030003503400c25841d02d03083c00742c00d030082c1c407502d11000d04040e03081080b806854008005408024031480c2801e03200b00f0048100410740003070f891001d8502c80b0400007070b07010340e440c0c40c2200d980300c1040d2555a15581030040450081c010782e4000f0790030078030000400441102590080d445148141c10034440409582e00440b1240811207100c0c60030340c400124000411001c0c0310b00c40a1103001443c0091130b03103c0140701c10448c1c001e41d1020700701e03a8001c01c1c14010740c034112614560000f08804030501381021000350412070348002c0d0189 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 3805736 1250 3804486 3804491
    0x209010501032706020f0403050c09180d0503100509010323010605010516020a05030703080304060e06060d060b040b03030a1206120201020304050105070606051806010f020604020108060103150305070305010209011101020703050d 100
    0x10f0411440341c06481840c0210300c1e142e46c81e681d03242090340c0c4510b0340b145124456010b110010700c0d401c100280380e5030383d1551840200007541d200142900e641d440030701795500715810441300242035079601411a020358480d01141c01200d515500c002503543d4079031600c0e0340c5030b41001c03410b1060303990090940d103440e42c0c0100303018220781c1c050011810b142c1064000c05d405000780c00e0040240183c00c0000c500032442204200081e00155000c10348441d0305030ba159600040b02c080c18404200190000244a04020000560b0360781001c0040c3c5141c1c4600480303804034004080e81c4543d80c0051042d407004100855030010311928541c0000d48901c142c1c05081e06125002c901801402001da101c4005032401800b208407101d07000d08101021441103801a00203072041c42071122951001c18503500850307041c7c6541502d52180c10064003e42640304885540344600940040031800030010b42d0001d60050b4001643c1e000f1000c00100b641400541c0784180da03004004010010741e01c04100c4a2440740341000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 3806986 1250 3805736 3805811
    0x204140103241b020601031208010302012309040f050601020c0306010b040504020a05040b0a031b050726070609060203180d05030106051602040905100b010306030206040e09030c03040e04020901050103 88
    0x1c80004100e00c0c249180204003c09028020036000101c05050700d0103801050041ea043e280d00302d80d40c481c00d000081c0024040c1d4420301c08580b10720043c01100c0340951440e410811064049400c41b06040d030341000e03454450080c0b041d1541c0501041813208015005030950390704280400600344924410503000e83d40c0000e26403660f911840c00d40d0080c0c10303441c450b15034401c608840140504092858150403c035480007032980103001e0422582516440f800c498500c9455400e00c04080d4031a586103040f01030700300007940004040c2d109154a0500c10400141c176405c106c6040650698241804165640a410750103000d54101003076a0441d51949400c03560384014044110488030300a6009401904200c1e14104210012a0524076920300c500100a440301010045056500e01c2c0700107034002e0001c120500403148000c1c10380340e1214500d011680752800081280f4030390f512540c07008a03200040c6060004502e40b01c0b840500500b0240703000d0009000160600c14801d0085104a40b02080e060702e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 3808236 1250 3806986 3807053
    0x405010603170702010801060912060e010f1509050a0203060303030406090323030403030b04050114011b02060c070303020606041104090504110a090c020c040c0e01050f071b030204140103 82
    0x200095036001d00107911a50000001c0561904070710f4040380030a61100000c01e505100301590400c4030200c81d00703c0f585a0541c3c4551004200c400d0801c0515502d0342c194150761319581c080c1c401114092000c002d80c0303501e0003640104692020f00080503050041080c00020399001003940c0d04690070100c0021000218a0150740340c107445242c01d004200c48442d180c880b5050500510310507402900c0c20320468200b0030400c4116640bd0003851018001d03906100310551049050a001c0c55034122a841000032903000034109802034001c0c80c00d2a4003404040c01015030500c00b20380c0100066809100b102d40c107442445190180c0d00407400034550301c5000074213200c480b1100c82e120b850081c01c3c0348803064503865070030068085100300c18098410440140700a08080c41030000501172580d80141d5030020400458540d8000390090204103414001c4c0404a4001500d118141c25000580c0034003a10b10b10621041d295020b001849217141400100080342558a00c68200051100c181c0284540e042 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 3809486 1250 3808236 3808241
    0x30212010609050f04120201060e01090c090b031f090203010302060304080904020d1a0307060219031b05010608060402100314011526060a05120d051809040320030a0c0803040501 78
    0x80c40006903d00b040c0c1800005200d40c0309060090380155800c00c0409050719042c0c2c203862952140740074211685004100c1c001d09c5910038014180540380480c07046640d1011001241c1040c3c41130401f18100d1002c071085000f410b55840d0007407440007800d41c01c1d50f00d5900019001c0c003000308003601502d80002d4080855a4a030304070f03011515132150400c0f0b00e100c54009595100319090055019204042001c40c13014000590311030500001519108010781ca40d4080340d0900e110a6804107078903002250100042003801707482d000c1c00310000200728030300e00750040040441c041c00c03100c0c0a061800181281400c00c0e602c84a0558482d100740a03ca0021a0000c07031f11b0380d80da14090b0050004219101c40c00855451aa60040004854801c80f264803981003000d404003030003a488580e40721881400b6000d00070b1028016a203801100803401b029068049582004112000c80001741210310031900c254040340740c6103403200598001e500f0502128406004501782e184085c020800100c00a82044000d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 3810736 1250 3809486 3809489
    0x10302070203030307030b090903071106070201020c0303030103030206090114010302030a020d02030c0a030804090b04050609040308040302070b0703030c08070f020307020105030c040306110406030b0306070c0206030402040609020c07080c03010c08010302120106 114
    0x24040383d1340d074035000c01d00500034110303184054441d0b804900410705000d07002007940d16494100b05a03290218014040090743e41c0144801c0341540500c41d0b0001003a41d050000d0760003140a50060180752a00002e440e007150701c903400c0b4102c0c4071685401440075131400600c042400d41d0550300c0017034818031400000e29150460304070715400030710030a01104009030503028100320b45442206000305152407042006079581281c409810804000000e00030030303c80c0341207e401c1400380c01640e80c1d0711f8548030a440c1990120304c041d008262101f2145030226030114110781d000040c1d10304600d048403444c2d0002e46901c500480a410440c001c404110341242040880c0c004644c00407041010403081c0c40208103e4220f40302e40000329291180b0350f881824007141c054401c400b035945014055400e40e080010a0b0030150060b0b80041d0b07a00804180c0211900c000c00c0d21034081c03030041104070301e002d0106141c00c402445840c00399040c41c00d5404499084001c490540754102c42420549030510841c50040409 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 3811986 1250 3810736 3810739
    0x5041103060d051606090509060901061e1106040b040b0f06060d021305100306030b0709080a03080c07021305090705030a12050304020d0803010603020909090316030e18101d090304060e0103020702 86
    0x1c3d680005c2154201e0f07000c4084a0341a200c040031991064200300221000344200808540103820b0030b0004500c0c204054070b103400c2418681004000b0300c040610341842160201c52180310b0800780020b204000400f9644111b09420740d00d020700d085400700e459409120300c10a4129000305d03081d030542c541070b0340c0e0901400b0080c210300c0c2e45070a61180140170788514402a5040ca0f41304020413002d43c400d402080036074504074010f02c00f2440ca6601181e641e04018070482580d0000c2c0004801651289610f076003046004c0000300b0b0600b08111018104103065008074803076804a03618000103101401100030812090030000c0d141e0303a6900101e08258a0040d00400e215030020001c6029500340c0d000e49030902c401c1e82e074601c559448510407035603445400b90b04441480906540c20000c0e00c10411055603030000703000c0b04070f10f4001299003c501c0c0c800b6524442c04e00381d4000284040707071700d860106000070804490745443c0c4c1010440346480703200b00d006410400c01a0144c2070712590080d0102c1d40c0c841e50 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 3813236 1250 3811986 3812023
    0x60d020d030302091c050105150a030f080f160506060102100e06061c020a06030203090709020405060304020d0303020c030708030612010207120c06150602010504031814040213030204050103030c0c05041103060d05 93
    0x14034607065000744800c803509c0801d4034803103240420a0900900076016258003486203100c0d80361036100e0482640212501c7d00c0d0150f002c1060990b04420b000004402c144170302e004061038280600060b013480c10745007804400c00d00d4040d0031100c0c068002200c40d0000010b450800c210001d40700241910404104040d4204180341000115580d05500961081240009540c0d4454a0300c0e203000691140d88280d59005000b1700208001d440c01c1034401c80b0461103410300600d04000d04908071b00f15042118107640852001c0208182030424031407404040b0b80840c004c601c1e0464079906e05069541c11041c2c0d804000443c0000f504001a070f9009451000012140c82aa1940c035080207000e400d04540c1180003510316039940281c80101c40c904010740340c0c0c000031900f8100c6600c040c00300035080ba078000203008280e00400005601c9501c56240a1400382e0340f054500e84803410850700241541e800719009903e03020046803645400401c1e80d0b0000d50071241d4290308445130a2007854418019900c20040c0c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 3814486 1250 3813236 3813289
    0x5070e0405160501020307030503040605060109030204110715020c1c02010e0102030a09050c0d0c05040e0a0b010b121302060324030d0206060103060902031009020702030f011103010905060d020d03030209 89
    0x40001114035001400b01071030404030b6103e2004985a0042c000001e000c56010300205000602b00d80211764018418034284022550300e8001030103a0307094a021500946000603140244850610404548686590158680307a015407903180d4803440d02c031032801c010340801441f194051007034010020000078000255101c2c100742c01041c0080005050448851041403c0060ba60074035204c3d60003e1500015540c3c100c1d0f1505c3c041c0300242060f0020700500c0c2c050301c081400024a0354842a010b0305854030415110802c248401c403040001070f2410f90114900380302d110041c0e07124001c40364042c0f680c94100c0c080100c1d10200324240d441410101c3d905000d6110041e40407a400181141314400980e801c1c003c403595907814000321703c000da1b02c400c40720700c0802d010320055100390000c2c0245807000d01103480c203e01d40c26501e82181c61522240c0d2150b840000100880c4001e40100342e08408c00b21080c0101c0c0d61290700092040801701402018950003195000b0180e5660811002d4282c1884041805d413 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 3815736 1250 3814486 3814493
    0xd02030c09040c02010e0601060f090503030408030306030f0304030b040809040207060f0906050709030b06060906041805070201060603051608040501020d0e1f0e070303050309010605040204030302010c0e0102030306010c0b0405070e04 102
    0x1e0300441041c901852422107030f070203102c0c8140180300e0409500406854240d003044812a0041310704907499060200030b520000b03070307914104010001402c01d1000b554490a09004042c00d242c0050341c204404c0c0d00c107100510100d540c1c004050b41041d80501001c0d03403a10504c011401a000f0f420300030f0210740c540025048004459000301940521401003001140c2e02c4110556420030540005020300b4941b10000342c03a41400d0004090018000342414101a91072203d9916900e4001300e00043e5915142840040c0d07409009680241003d0700382404103150422104c000d940041a01c5020000180045010f01000303604440d07142c00880c00600c0450f40021030140d40307920b00080040c51040e0894115140c00e940c1c890740c22141a0a4082c25603186182c400301c80035000585945182d540e5041c00003115035880c4010001103100b60008070301c900d8100310103072400d0000e01e04141990005c00c01c1013950703030340f00e0380c89084564442024101506c840c00e0042ca402c5d1207820040c04250b10700d0a03c000e1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 3816986 1250 3815736 3815761
    0x30503180c1e03100e030d0207081204050d020d020a08030601050a0306030b01090902010914010e010f03021201030321060605160f0602070309080d02070803090906030118030f0207080106050d0f0201050d0203 91
    0x40071041c2c1c211014136000c8089402280c210300c020140580061090440d101d005800520045000e030303030380710700b0030f955031100300903060081d030341107849034400f9910140454040c03007030718541e08483c00500703002181c60b12601c0040c800185900e040010005020640d103000e503101b00c01668002c40340100940e12040010000c0410500580c0411b83e074903000260048220008115000117a40f107a8006240300015520380aa0031002402d15809000e0700120001c20781160f402140655500b500d1181d00380003001100c0d0100c040c0015079410028207005258101c421604103440c4414204040c60f02420024544461440d00801180c0005405070601da8411022000d6401000a0702c812800076002a80c0d039060074400c41209401c1446410b05510700172124036401000a40045200f504040480d03002542c00c01c4120041009640000c0865a0400844001c0c002d208000c100c800d00f81400102e00003628240205116600c2d070b10355045912403000d460388003200d10000d648a0920b00d0300281c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 3818236 1250 3816986 3817039
    0x30c030605040b1503040f0803040c030201030b06030601020c1002070f0f050102010b03030a020709020d02040b12070e030703050a06051b1902010506090103020d06050601020705060a020109020406050607030503180c 94
    0x40d05051000c035007850a480b034100c2c103000c01060107001074207546039100150030041050300c03003240e110546e00100b070340f510007140f0903413040c3d00507802c0c41d08504c00542100c180301e5115000c0c1c40e041c0201318150b40c0000381040c40000c1203c030302030001404481240383c000076802156001405010011346400c1c01314060007924030036002400b0490a000604d90340f07010324410000142e11011081202d42e00315401050402c8a03003170094501030f00c0d480214480e501000850082e0700d1001c08200c4126800382801895800460190044a00e9501c03401c0d80e407020280c01801c860b60342c070301080301c01001e0700d01294104001e003829612680044948018085c00241c05805542880c001840500d001007049058a5004000028480c240d0b1508801807800414681c158861604d0120b0540e40d80700140c105814107500105515a8510600c0306680705603005601500c41801070100007074222050b6a80f00000070380d910308210450a100303140101d01c1c451540c000c007a484404000b41e2942100c0c0c807 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 3819486 1250 3818236 3818261
    0x201050f09011415040207060203090610050f01020c0105160219030302070902030c0f0705010b06040b04050f040e120d0605060a030f0513080d0903020307060e0607080c07020a0504050402060c010c03 87
    0x100c80740d40381607410742a18049020101c018820300000346440d2407070002890803a80141c07006090202d603544060480c0d00035121840c0303aa11001c1000b40c044040940a400b82901780c41100352440d02c440081e544207207074920541405001310300f41c0c1c400c40450b5025110a0303001070002440e140700649a80000c11355000c240c005009030701c0301003a4000203008480c0100b0400042520b060719521000145410507201160a9500e880e80e03c04150740c1c210152001e443d282040664031072030401080f100101041403140620300708940710303c40e6000400c0004a9030f502d480c0c10355443c202c040c505801040541c1000b903204402281e05801e5981c0355100e0015121021420041038640b11160800040041d0004004a8041040101100301070700820b200d184640112414020141c3d036200a4401024441c5a9580004200041c048e40061f2a9801807001c100841c6031208640207d0045a86801070324003403522100850215120113003118500c00600d802000341212100e0014080c000c0c0b000c0c00d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 3820736 1250 3819486 3819511
    0xe010606090302100801120b0c0c0601090209030d0201060b0a050306031006080303040b01080c0a03081c0203090a02010801060f050304060b060702120a0b010b0a020a0605070c080d0b01080a050f07110c10020105 92
    0x1441905d0040d150241646c003920b011020010055030b40400002008011002240083c46280c0c03901900700085400303003400000260315400d003001030615082c007000c0490110780c101031080000114820403900480303c1c03450300d143c3e41c0c0d0302c4d603002c40e103081600040324411034a46440020b6803403020001d1030255228580104499030f030380503c59030303501c08805496804803100108100040030140103114880385506003058440c0780610071400c980084034800015084000c50004669105c0111405882241000c4044085a4900500d64000100020030035541d641f10150700d56901025580242e5000b002c4030b405081031a0300315101c0424403001c80b0000101c6e80007240303003e4500191042105941e00410544685850301c4028101c080e00c0c0c0814801155607030004554000014000c9000b000000b040301040300b4001811084002c080c0748240d4a00030900c584c20588400241c1c116030345240039011140c09442580c100030f180716089901c41032100602d0211a0103401241c030505102c40da4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 3821986 1250 3820736 3820759
    0x303020301061205040503090904050f0d05040302030105010911030103110103060b0403031701081908030417070804061202090105160201020c040501080a03020111030402010915180303050c0f15010902070201030e010606090302 99
    0x20310084da0800c1e00c004140340c0050050100354140880f05940c802d01072811540801c0c00d5008407400d04540001c08000640001014015070600b4010f890040400c04e400b0400501d0038103002c4450300040c08020803800c41d000038442d19a10a81040011300040c8140c1c540d84c903560f00e00900074089000c2003040e45141e0a00019003900d0119030074240d043c1050700c0205120b182ea0b1100315030750004008441840c00e0074111007480443c1c8002e400c01620443d459070340c0368209007014050040270869100c0041c010415008183d0b440001c1e5000c094209540201869551005030f04013400107081340d0f00203180030000120700c0000920215298020340003005001c0310318800480521080350080d0208502032401c02985040701c032808001c42d52484d107280c15100c0e03241c141d0300395181d641c400d40024002003041e10f5414014041c40407040070b140003c240c0221074001204501405104002519501050103400d590203a084207800341c040c6070007004541c0c2c07603400291031a40c00c0c1c003050b4080c1c2c0140d0903 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 3823236 1250 3821986 3822017
    0x30606030e0109020303030705070204060b0703030b01120c140a030b030f07090e01051005060a050d090b0402090603060402010215060102070801091a0105010507080910030b04020309010509100c05090f01020f0a030302030106 98
    0xc3c4188250003801440c5141d44240c0c05480e9030b480080d00700e80181d950b510005420003143c3c0941461446640c0100380c1c1d841c3c1c4400140100d01c0340451890003803030451030441c0039410040804541844200c41c0c1c0e210003449034240e00500b291040c05415015040365520b82c9200415010151044441c041061006003881242290003c50300303503610710b401c804148094607151000e0312041950b860300318074003d041219402510720ad0202220741c00c0c1000c061104600e01002c4469000784150000d010620381600001d540e440314103c0845440e1414000c281180d00c24007038400a07100040007440000882d25058008084400799000018117580c000324840d84950210b52525800542c0344c2d0a008000d02003025148191044805042c1e840e00441d6040d00c0740d001561142d000c01000103030f05d207442560103041100c0459101c3c51589404c0300007210b507401a05890a0010994290400303d032440c0041c4e180c5020144041c207584101a800c10402d5072540065050310b83c661394041c1e004a5002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 3824486 1250 3823236 3823241
    0x908030901080a0e2107050d08070c060c09080d0507050c03070602120d090b0901020d06050103021c0506060c0304030503030712060b09060a090314011a090103020906190f06030606030e01 82
    0x9400c0e40000c1000021640d2080f0035044458041c1405050310704c2c502900d83c5c018101d44804680350b108107400300b4101c1c207100c0c0900c1140c2c9000c02605200c8414600b41500615a10084c00c3c010851a0750741c00700c505042c40381d101c500150444100321454800c81090241468103c3d0008030341d20311880940004a050101d008400c0f5080e580003000303a9254003003218099002001e03051851903940b00c02801050000801c0e6008910704400142d480b01c3c4101820280e480035002103061600400c64145044200d00940c0759250048100048036102c0c54006882c81c401c0c568108003a20000c6030100c1400408401103025800c10b480d4040c0325400030f01000300b5250b00707200d51001a0824005803034141030442c0248648440e52514a0205442e9501c034400865100d83d00030180e03545180c920714212000188884c140011a48940150326590000d040709100030480743c05036240281662601d821170a4002c0a0005a01d50b4901c41d030b04e5090040c001e006601c42c03900000c0c1090703e142040081803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 3825736 1250 3824486 3824497
    0x30c06130209040b0403030b0303070c14010c020901120503090603040602090307060207080601030605070e030708010501061d03060103020d02031006031b0603150501030c051c06030606080f06010306050c0904090b07090803 97
    0x150030040e03143d403982c8071400000c0b00180150249a107401c6100c0c06650240000d080300e41c481e01c000c4009509100841a0b04010301c25aa41803041c03400440c1c002d41d89240803141115200c2c0c8108031940c0803483d0032400c60041031801604a0350100a020030080b140d0007400d0942c5081d41200c40d0b455403080204d0740c0e000180300ea5107058100702c0c01440440c0c0315402169010389039080102d002c840c50300c0842c0c5028030076801a10182d544200500c074090b44128040d011030300010f03110004140d5400040e8840c0010b2100038403840d140c2c04640b0440d101070201d01c09030322994404006c03030382d40e0b8240400c050700c40340c52180c10700c00d0010000c01c4d0b00303010388a503440d50704202081c1241345040100560013404450020400e1240034040780c030300c0441810b944002030088046c0841e01a00d5841c0050603185150000c0322680c03c100c0f6019001c9100062460440f5007091002c1420349a12306445c0e198420a041107801c1414141c071441440051b1505e640074002c5d9550751955599900d40d800d4890249 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 3826986 1250 3825736 3825739
    0x190b06030c0d12080406110a08010821040e060301090f060b04050a020705100c09090e070f05030a030f0c0807020a1410050a4506030b0d020108040206070c08010c02030c061302 77
    0x292103c0c00000d4420004039501500c00d920000311040714104034410354002c0044a000901d4480040c417060070148070340c030a148060350905c41e18040c102d5a5070010b00071030041071300001e400f20000701d891b07600350465001c2541100c3e0b41c040c034081508100014041c0102c255000700d04000124543c41c0c958401c80c0c1405400c81c0c06494601c4025078058060008410184101b05000740d020902e0500d51040310140c0180c2d41c01841300618104203903c5803001684800d100b40c10805045001c82d80240016528048034a070400201d1080d203007485450055035800b070340041c0b440101140902c103030b050020321058100c45400c440c0004a600b105c05204181a0b0700002d0b64185170b00e80320a00b6151a0743d0749140b0103415000701050584801003001c0c4244014030050b544020401c442c941620540b031140c031041e280c0204d80310752500081c2c09010301510007801040006104014800c0010190b805417500c000240516060000020740e641c001c0305848840e4051030010400003c403203000040001da0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 3828236 1250 3826986 3827003
    0x903020a050618090907030209060303030103020607080d020c0304060e010206060d050c0d080904090b040b070302040605030609040501150f05130204050904060c050415020a0c09050601081503190b06030c0d 90
    0x702001e02c000364020000e009400c0d8510140309840350b44082641e803081402000408007a40303113004001c448640609114040d400030030060016071500d0048a05c01d0f9006a8040c0c0d8580d48860020020b204183d1480841d010109002c124aa03000341d0b00041048242d003140c1d016210241001801168410001c107550300000b030307500690400392013640c411400381050b5403c0500300c2011a00750b50340d0601c129524440c1e4010807041010701c1101e10b0700103596207011070030141840d10182c9184409004184100342c0003000604028094112814010703420500c90300a660382c40500310b84090f41d02509106910890312513120703040c3e5200761400c983d402024040786844a4841d1402440d4a00c0352500300442000085050401c01855240328032113680100803403c0c1d20300b04120381d00c0c0e0301d41040f00002c1c28407040c010103030b0740081c0c0c55400a45d5908082250fa00380300c0007070310317009842e1300304500c5810508896092203504000c481c85220113405807000c020910080149614582400820485 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 3829486 1250 3828236 3828239
    0x100302010e060702130501030b0906070801030609080403021201050106080105030109080301350a030305060108070f12230103050709090506010b0d06050918010605010f02070603090602040504050108100c0903020a 93
    0x10311800306601208000b81426180540700e402140c4c03000b0782200b0300041a07464070010070421050622495016070000c02a00303050510003401007840e4010320000d04142d44400c26807080c0005001114002c0d1707170051001800503a81d411160180c2002d10850010a6011000041509042c011a01c6441d8030000e81e41c0380d41e0078000d05c2040480c03203c80e8034a000c220403d04000381c00d0868082e0304444030040080804146074030703008098940c010682810003802909110701107402005904900800c0d0030a010010400754040c0010521000407400003244502c1c4982c550100d94a0f6506a80c012070580300706540b5030412800340d07242442d0013400b5920040041280500d0310700034142c0464107410204d1599502c1c8000741e1071240507038010b06140c10104104400b10000d01c54140209005c0c2061088035422010207519161288220020f0649440450f0704001c1c0c268111006030000500800141d43c44011240c1c0d12508101980c040c585440c441100c0135000c1d010302411243d0003881c481c0000d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 3830736 1250 3829486 3829489
    0x90706050309010b0a17060601090b04030201030207021801090608060c0307050a05070f02030a060c1701050105030604090312090302030703020709060b04090207050a0506010303050309010c0309021305040309080a050102130e100302 101
    0x6500080042c4a00d550f510032450860365650100002002d0044d00b0300180f02d41700801504040c8060030031414052540c0f4204901c07a4500e0a8404403030302401d005884584a0001c1032021401e030328030301e206d58000d100214081c03140307074044815183c0d414201c45203907550301551a520f01c4141e4036440402d070148000700a240c4984014690703688151f143d1124076030382e0341c0440e107419081e5804940c0f075901c030320501c409a075005a4503450300e0710180d1b66007200e5240c00c0c0082c1841c40050400b0340120f403607101c0d00b01450300450007280c1850454008200b010320f07070300703000303403203030403100003107006020f842000250510340c0e010307c0083d550381d00d44032850146002c40040080d4800c00040344c050141000220100d80c05008888c020343c0292039465907450400c1604d42101c8820512105040c0742c0400c201c0942c40b000210030600050000015094880c2d04082e41e9518044e404070700c09124810f01c080030400190040c00c03402d11860005034038961501d011800111084401d01106499042e00300050b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 3831986 1250 3830736 3830747
    0x315050420040303020102090916080f070c050303010e010e06030a0c0605030711030c0a030905010507111905090711100b090601120609020f0c0c060f04031209090507020a0c0806090706 81
    0x144400c001518500c1078506401e2290350450b901c00d5001d40d50201362030340b41d800d1001906078081c82c81300000d03854484040000d05012000b402201ca941d01090000312664040e540c03200f04290884112a1251794400480d103004d4002d005070802e02d00301c4400304055080c0000c1407181c0980c48500e171820a81048801c82d800d400003000c010802092244403c003604050004200d41041b9030084e0003c07565a00740034142e0b01241d031090741006001c00020b07001c00c402801840c001d0038112800040d0040f20110340301c0b40350311740c0c00013036100c10b000c0d05008000380c01c44100240720034014240e801c000600403c0c00115044690b0075a00002c548000444030341c42a1a01010038800c0040013130417507103a4080200701d81280705001900d81c00000c201c5022401041040ca22034403c841091a028021261a405001380c0c84020251001c0c4070030ba40e030b410f0061008401404441c43c08000318680510000e56681a000040e10074440c02000840c0c012008100584104c1d03010005003215490814115403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 3833236 1250 3831986 3832001
    0x60a0209030c0402070f0c0b030106090506070c0503120406030501080c010c0b0a0e0d0e0312040803070305070503092205060103200702011704030f020609030702010c02060c0307020d060507090603150504 89
    0x1070500401900314407558542c03000c4c140580c001d01c825521801c583c680202e081e5456040320307002e82400e20041001d41da00c4002c4006076441620082c1e00e500991a002d084995190411541401480c1c801c0444030b08000c040d100702c640582e4188556603907010444c2d107880009140a0002c2e046000e03410105144031549500a8074440000500c94420801d040c1000c01c08180d0310009248100031a407185010810403078a0000802c2c91840c041c586000c0c80d50320700c54000020309014010920b4000c0c04428815a4020039020b001c411200700340321034800b50790000c1081c1c60303c80340c504000b064155100c0d11400103054442d0702d410034001456010040e594002c075030304904124050034011762066400c01864000c85c802d46421400d4807444030301a041501c0105040c60947c01070100001503a489100c8011a540544001e591040f19411090842c0318204019410a40358101c85007082056400180300f10500e42c0c0350701c240b64030740c0c80407001e88000b01c45044d18042e00e640d090240b45003ea00c80203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 3834486 1250 3833236 3833239
    0x3030103020f0d0b0702010c0f2607020f010c02010f0c030209090609060a03050a050c0916090501080403111c0f05040302060301180209130b01140723010b03011401050a050111060a0209 81
    0xb000343c84540c1d550111300c0c8104c8010303005075110240b4a42c19500501c0b107171040310181c10b15884118070403920b41701001c01c80014064800b41c000104405e01d00030300004450148070b400030302940c0881c80029000e00a0707603a02d541080e107407240c400310840c801d00c00e9541c0c00c08024012200c540340c96042154890b0068601d0750b00c0050001c1c0000090380400202003800e203d0340c050100c40d030440c81003000e503a00003040292006034812030030310400e078011000002c2d1002400c1084d2661114141118007030303840140280584191254034041080e40b1085804401207565200400c0551300001c54050007a0321000390485010700051201d40c0101134041005000c40000504082000c00080c400c460b00f6104051455650420b045507560300c08500850340922140d110318142c555980c6103180c1e041d60341c2d04002c801041d0842c1c1a0040290401180124000d000703000a040c030600c00c9441440070f1040d80d00c240b02482c0c0009940d40504500c030800b00e0344402600b803d948003030030140658810109503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 3835736 1250 3834486 3834499
    0x40201030219030506090a05040302030a050a0e0907021501140a030303090204090501050c030108010510060f11070f0603020409050a0504080403080c03040315050402102f1903080603060c0a0203030103020f 90
    0x80e95002d81103840141e04541550740071410b81401004d00045c0c0e100540340c82d5559003400f04000c0403980001c1102c4203041c00b0325040340d885180803000c0760a40c1a07a03002e00d40c00514001406800da40c002404401504582d0010380141d0ba01c5698403160314960100580110307001c072041001c03d00a9004000090026101040f01e01d195514235003151030849400d62200d03004401406409024410954810b43d000071203119103080c2036000c0c2502e42c07481c00950400c880c0c8600a040044281722042c0104070301d8a00d921070320384400015011390080e001c8c030004a8604000284d20b012540142400381e6000860113161034195102c1051562016661000d1407001308000000903102100a114070188104009110b080a104009100300b681c0b12140c00c00201e500d11045030903415030f101400058140c0e10072120399152000d103042512409022607404a5002c0c1c0e07105054014010354444d0340c04400f40c500a9a43c0c2c0096409402400c4034600140c1c010710050006082081020351000b0004129 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 3836986 1250 3835736 3835747
    0xb0f10020f030a080711010209010804060209040f0e0105180106030c050d0822030606090b090f0601020a02090a020c0106060203070807110409050f160b1c0902060906030403020a0302060f1e0402010302 88
    0x803442c503845841802c000031102010044940ea2040f021100c030600c0c0c0000b5840c18105e400001e282400160000d84410760001c0c01200c00d0741d0300d500c000201c5001c0350080c0101041850710900800007102c50300100c00c1c1120450070243e4042c41208280c95000791043c000c5401d040600c0340006090900307c6810008100c44030702e8442e070304a100980883c3ea01d8030b111140c2540707000e034203031151644000001e41c18072080c6040c994581d42055404030a45400104507601c2400403864580401c001039040348014050001c91034041d001015a40046002440040e03a5960100d0b074a01c11040080c0c103078241480120001244da010100800c0001840441c0c0b4000c40d44403142010a4075443c00c555a000f0800320440417119168030004100428186090108925402c81c00b800b00d880050b64856489a03190115a0b800c0142d0b1003030740010b0280c0344c030303850301c0e00d0069a1404d84410a9015209820000301ca58103000c03800e0340f055075082c14140002d81c0c885120b000c410f40280081b030501d9001d015 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 3838236 1250 3836986 3837013
    0x18190c030b090607020d0905030303040201230706020301050f0d03080c03040201020120130501050309070e0405071a0406021506010e0108060111010c030b01080105040b010c08030c04050604060804020102010e010b0f1002 96
    0x401500a02c0444040c01d0390b4101420041d00e0281038024034002c0c00f1040808010555002c000e40e94420b40a00702403130644501485059109507118208180d5900403a2580511041c1d070f02940c1a0b0740152585907812800004200070010602c000038009803100e0300042160300307960081e5410901c10700005c121690410701642c2404081040b2114002000c0343c5c11007640508201240202001c1c00c0207403071420300c0c43c0d0264039411a8020401098004404201000300402010000f0b1003141b074401d82c80c010b40456204658024424000103100700da907500100e076030309610305000720016150546088040801034070f1a61004104034180f043c20034046107185000c2c05040741842150fa00082c00c5c00000001402c1168180c1010340182d00e0083d42c0c10306a6000540300d044560080002c0c1c1c2c483d610b15880c001580b066420150b01324502040026a19821840250055100740c0090100c80d082d0400a03080354001030341c1c19403049900901d0b070320909003107501c03042c0703049a0700c1a0f0745070460408 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 3839486 1250 3838236 3838253
    0x14070503100b0f01180504020a05040503100b01020609010c0c0b091f02040501020f0601030b07050309030708040306050a050c031509190212010302090f1005060f1204050706030518190c03 82
    0x8030a0340700a40390480380d2001d1512181000d00d029003405c144801d65450f035030140d0380d60140e0054500503540018806810341c05041a03c004003001022650091003142e0014084d20015044a01500c91280445c211000c18001c1200d1044140e507180074032829a1203028600300050401c1900740140c4e0540d0300605055560301d0403070000010056901d51402d0002450402210021081a00064010700c001180042d020f50062200d02d0016265252101c401c2d041d8401c0c3e860081040900180000400040e50407035071044141e54803c0195580e040071644862004032032140308040e54102c0b1845900c0c100e54042d070804c1202e00344180c5014120100c001700d91000c50351070340742c480700d00c010421868114a0a98802c2141400091504082d21003505040b240d001d600e210301d80c04200d03000c030110488140c40041025030100d02044c102800c2032510b918450050200003420721000a04402c02c0c00b4540032288140002000c44403101c0c03041035542d050100003280c440f0354400c00040840d4080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 3840736 1250 3839486 3839503
    0xd0c080103050709020901171b0304050a0b01050a14040510050a08030306090601020d0804060902030309060a0807080108030a0504060c02040b03061e06030a020d030f110102030901020d060801050903040314070503 93
    0x2622000000d50450520b50700d000310540c02010142e004200d98a07060364402561410900d50040540c0c50740c680c1d1410300c41c8194040c42c4807040d10000300401c801e004000070b0381020240a4007030700902e070740c0b1502440b1441106010344400009444a1000581016884650711a84400700511216120800180d442c505548196030035031000c4288207041c8ac01d1050f60740c204e13109000030101c3c50601e210160080c10001c0015040743c0d503c200b03440964130103000301c0703041003402400907544845051024010000640309400001d090b10004035000c600041110701c002c00b607442d490300313040c60b04100311000c01a2690491700141c1301c1002510944080080c18000d414030000001e9800d1030750f0741045081801002d00e48241d0181c418070016880301d4200e290495090700c1c05080c1d014002a00f6100000440c110102641c400010482c1c03c0784194050141034010320402d0200f641c0d624016070a8480039104481148c00c100010800240151095201505010241d50209540304000f90815068 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 3841986 1250 3840736 3840761
    0x6061809070201090611040302010903080c070b0a05070302010b0a0806010b0d0204080f0303010e07090f060c020d02030604030305060f01030504080301060507020a090e0601050103050a020705070506091305040f05011d0c040f020d 100
    0x48008803000c2117045c0c003c405d5011950300d8083d0919185400080c02c5d0900b03440013824225001a0301004144d0510886000e050030700350b42d036502c088050000300940e008080079001540303400030074601e500c3d1102084040315016002030040d41d007041d2440520740c3c041c44456038815070801c40000c0340b510a010031100450035201441d101d61500d6950707a1400c100400d020108840d41000b80300503242e8a5603802a100c5078548501c511300980701154400181c500b010b58103110b244100002c1550540100d4410002a01e410008208240040d001e985065500400d0484180010300441d441035028141d5030b40000c0400d20403d66a100d00e50850340303024030745181c0e43c10990041c09107503010300601e608148807107002c61620080d62209500c440c014040c00c0e1184000003603110f240d0340e441484018169100c002040181401d1900c1d1040381c00402045441d03500f081c0d10000c0a24622810010841c1c00c3c41c00341c42d6103000b071740411009000a629a0b40665408c0c091104019a40d105401c0010320 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 3843236 1250 3841986 3841991
    0x70f02011d01020c010b0108011503020307050f0d0501030c050409030503060d0206070b04060b03010b010905060a030b010504150c020f060301050a060c1a0a050a06080d0507020603061302070807030e01021506061809070201 97
    0x703444d40c0142951140311100d4140700006004005813515030028810800c1540741c0107890703071140041141e841c420640e501024a902240b2000510000e42c041e034100c0340705404507403d060b5a0f40a01c002e481c503180000d0b012036010700000d8554101010321080c034502c028040307850000d10f9940c103419000240c4042d50103941c2d8035003410903030500b4483c0391003801003400c01e800c07110301e03000000d2500c0c400c0c5400601007544130341003004107902540070303503010703041c111040031807682c140f075004208001010b001e07407003503800d1641500541005000c0341d06842028013408070301c41c1084000d03220202407940843e07003068591413050350715807036844050285170902404120b60030301440500076074070990040c40301038202503c02c20350181c02004407090320707505030b842c00d403295a43c000140c413250010641c00da04a00024650b41001003c7c1c008088403131103502c41031020010710004903030360b880b150440d154860745c0700b001c5400783c58110081c3c0030032a07042600d030080c91200b40110302d01031800d50315280980e4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 3844486 1250 3843236 3843247
    0x4060b0402220f030c09180203010c02010c0210060f061b0602030106090501170115030e01020702030f010b090915040f02030109060c081006031103070309210810060e09070f02011d0102 81
    0x10b14640c6144010200d035a107080720103080d61a04088540c032403003420980b40d07442031054820a070540178a82540d8004000b00310b0514074000c040d001e026000469001070043c10540652086988104025601c6401c50103c00c00e00b484c00c1544c1ca1003441c240004544520b014010000d83c032800110302070041035031284802c600e0034002500c040c02c0080b6844c04150f50310014000601d0000c100f000f4100720b49000701c1c0c904a100344d00d43c0280b050100182d01805400410b41031440705412150358200d0540c0d42100c0707561400e50040c2c5408560060000800100012601240c01c44820000c1d440c00140001050031082e41c0da14200c0c0c41100700d000100b031050701000043e0201540b980700424903401c052080010601c42c02d8500c0c80014030748000c0c0766442852a0901c500044c400034000c1039400110825110804040e0001004a624a0780c00c155200c02040b41e07072061040542c0040d01828050103612228800d4070f240c0514603100d01190b43e2203a980c201040100340c0210100c5c1c4900c00140d684 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 3845736 1250 3844486 3844537
    0xc2a03030c08040f061d07080304050114040608010504110904090303050601030507020102040305060f130507080a02031c080402010e060c030403080306040c080702070308030c0d020f0a0f0207060504030b04060b0402 94
    0x15800c80001ca81440140d5041001058407409104000c41e8440d20024581e0004090b03055000303640100e0a002d403185501c04140300c500040140240c42c400d032121060341070019000d14032813113035014650028520f1001045681040e40200054215544881e400e080030040480c045400d071500039400213403a070080c0840355030180300380c5801c09054402503150030b082d070301c4241d0344410181044644040740400a0b954401d010003801c40e036030340801998030315991003c106a80d40d12225090384a40101403111040c0e9550f04040100100307240c9508406a43d240c00544100c14541c9210760020360401680001000078002000038612408a0b40d4680c18280144400c440044480c1d1042c04040024040c042e03400181d0b40c41141d6005c042e599407581c4107402c0c4921805400310b0b0705400b0f030020800e01108900c40014180300162580d41c0490024030a504a98548092280c1804184100014004110030080e4907600502504001c01c2d40344042c00441c040fa071101034501c907004944171969400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 3846986 1250 3845736 3845741
    0x7090c08040b0f09070614070b042001030516030509070302030706020a0b0f0603070506030702010b0904080408010c081501030209010504050303040303030e07080309032802030a0302010213050406030807060c2a0303 94
    0x4040d02ca078114809103490310301940d039800140034040030711000c9a1000220004001108d80305a0f0045080310386007070601c0c00b0034102440c4200c042d06c104070303200882d00325446440340f98440d2100041d4820341417040c00c0150001c240181c20942030340560400400541c80400030f4400820040d40207002c50341c0e150400c1a10300d4005010a2001410082842629030700040d0102c10750390704030744450b901e803145e003c10703401042d0300100144c00c075032a10204018009032001a0041301c40306002031046084040782241e01c0e6008490054100b840051814400d51096001e4140040c0c181051450180c075607001034919081540203c0000c3c0c0c03111180d402c601d0052207840300401d1000015828400ea00000944403000e0000d03000e2012030505426080008040070b094286401900380e801012580c20000c6c0070b0f40c40507131000142c402c4a10001032900309481020220b0780c01403041030609205ea0394139805010a8a198020003021000482c6051020812290800d81155514848102d1807401509 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 3848236 1250 3846986 3846991
    0x602010b06030705031e01080c010e04022704020f0c010204050a060908031c1107050606010801080703030c021905060301090603060606140315030f010e0102121501050a1107090c08040b 81
    0x116410300c9045800d54a803042075940128082c01c1c041c1d202c1c2e40300c1c5248110150306010342c810100091000240240001c01e5484031903a007a07a0f600072070400301060109a02c103204030f541c0103c203200003a098160808038611075084005201526083c00502044030a400c00d05410b607550b54000307410081e91510800c148001c00082c1001c20590340b80c110101c0e00c9001d00c0d070a1080c0380800c0c0142007006022039000e0f4681210118101c1e44800103414040c0d076a510407910540481c41100002c25070103000545041100e071303d0340d01d4440a00242d406d00c5043c3c4c000d5004403030f0802c16031502003004c3d658007024502034940500006207141c514204072041d03503215444041400300740707661006800c00300400c603544070018102d40000b0841100100349070011120866049502e820031528804006400410340d000c0c000912403882d072206003d2030517200803800194081441000703114541c50065080e0741a81d10a81e0644850750784d5049504141d81e80030110300c00140344001000100111000c0894 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 3849486 1250 3848236 3848249
    0x6060406060f080604020403020a090b0a09061214031201030302030703080f0f01030318090203010909060506040c0203030402091312050406080702010608070501030902030c0402070803090d050901120b010516050309030106 97
    0xc401460208042c04030702074044444200460600000d56584864040720000c59000c0c0c5040012640d44010383c0041a11003000c44c0f065015003000030301c030072079402200c1c1900c070394032011340c2805515507640006d0700c01a83c00820f0f50106012840f000035400c251113000314080d4001c0c40e42d41089203070051007000010b203000810000e9105024030780c0c2d840e45810b41580d62508140c0030403800004245103415140d442904140d0002001244110040c3c0141240b40d1189200780226141e000412003640c107038800a0005900034800500541344c141c0c0f0780d6400c085035007141c000c80c10703040c0ca54a00c5d04282507807080101e20001410481c9586c0005510350100d000d10082100703605000302c01c1e4941400c0c0c80342c54105a16681e0090640d9410b020010a48100400456440f81d0341e19000c0c00a402c11103008240340600040c49080c240104116209110140d50313402e00300340620b18240041c0002c1e0032850420000780310000c1c41180200b0801d06c064010390044d6100c5580da003c1600b912882c0d000390 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 3850736 1250 3849486 3849491
    0x30108012c0a0213020c0610090c14090402070213090501020711120d03020a0302090a1403010b180406090f0203030a0e0307140d0803060102010e030a0507030f0c020d121101060e0603060604 83
    0x807041034001042240344941e048680b114413448284042001e0f00404140080300c0c0903010601805250701000b8804850072440280140095040b051f60120f0307845540407011103080102104529092340200306462004040c03021214480340c40030304443d60040c003220980c2d4001550001c0c068a44100c40e2881000c0340c0300c0d0018176400005a841d4000011060181500030868008041c080e8051740c40042020b40701d041d0a9648a040c00d4080e54074404260095180802e02e003118105442e00603c11484d40006400c2c1d500d40b95122002845001d40c01c3e61940450086000107070b8040c00203001c0c024650341c45c0d6011001c5001010b0420055a00c0401c9051000a80000e2900d411014602480e00402c010780c0b680d9484005034058001c010100200f800700141d003804258214003e400707814041d54448201d944541002d941501c0a0710b406513121845c80c0110002540c0d2a83c51413800c8018600b4100b00c00f40c2c1c46545003500d130365400800300c2c041404104542400d080040561007001260207 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 3851986 1250 3850736 3850811
    0x4050402061b03090d0503090a060302040506030106110c060d050f060102034008060103050705010503010302150706062111030c0117070203070206030c03010e0702070608060d150203010801 83
    0x10a00e00c19200301e6104100c0c4942c01403001242441601c2d251003002c3c001041d00d0741e00d4a8043d403070703074080d8148500c01c20802034007213462403103407007654107868014120f01c0c42d603401d2074001c0c1e40a5860840e2083c2038030408030511200d4981402503e042c00301288003184e1402c100544000480c4000c0c40306045501c140803c15150003800d2140c42c003000301010301c80800b2584a0a081c0c6030821902c4411102c0b40c0307040015414000050b428100e80c000c0040d60307c0540c0304c6004460030f2000f80300c00b07548588425140071361724403407000a140441c4603010002d0029600c0051081051644102001222500e040d200501140001344001c0c154202d01410840c0340a50029100400c0c0a00113124440101c00140c0a14001c000711041c00f07400906080d2a03240201007111303103500c01d0180c034900d592483c1c04200001d00000710007080c1c03082a140c1c640310b82e6580f014408180d1039004240c44003038488160142e00300703162000314040c100b244000b0030100b40c1a040134980665141d131109802285500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 3853236 1250 3851986 3851989
    0xb0906011209050a06050f0702060114010e01050c0c0d0302030904240b0307110a05030301030311060f0a0b030304120503120c040e0606030703020705060f04030210061d04020301020c0a030504050f04050402 90
    0x700001c0c45070900200054965003420000d140c2900c3e1000140440c1c0b400040c4103c000344180ca40744501c9007a401c07034046a0700d6021007450b50480d0b40c4c24a0101d1018400c076900d40d80a00e01a102484500c03045031540d002d03072000031384204560740080d400358100081e241c0071420140144103083c124441002103c1d034a01c6004101010f0f58800e4442024020011404007881446a01e44102c804801c4440c041c2150802e00c0d04c0750300030310085000c41d034050203001520602140cc02d02c034900210a44c4040e58566090602810015203182d6150008210109103010745d441d0340701003640280e0086032140c1035030140d0015a03501810340c0c1c0a1840c180300821a44100d1690154000025101243c484c0c07640042035004c0d0103003040080c42402004104100c0c408544252881140030744e00b207443e01c1218006d208121155800743d0001c003090040c0d0702c0320007198010a650043d01c094001450301102d10f080c642807440d45a4101d0024900143c00c100c0342c07a100000703103e8040211000c11450030103a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 3854486 1250 3853236 3853247
    0x71407060207020a15170f0708040b0403030e030d020403050c01020106050303071101020a061803020c120a03110a0f030206070801060203090a030b04020a03080406050409051014010503040c1d04060b090601 90
    0x210040c45550005140030854a8010008000700120b01d40350080c488000000341c00302d00802d40440c0058096000649900e03a5845900c1c0a280c0940719015262075540712952132400040041c2d06058031460170225402c3c0802c02420303080500500140c4480c25440d003181000c04002d200c0c2d04582c1811414016581d0210860f100319a0018039907891b540030030010303800e042c4000400b504039440c01101c01e1b1510b0402c3e00b002a414407980c2a15855035455040250354003070036241c1d65030f940c8006080d4000034040e24510911a14a00880d08007118958a010580c85820401c50043e080030082c0304405402020780e03405400680090350901c2040e00100d190782c0304510000d4045102d800101e002e642341c0c01000350207035800100595455498400281695005200303058100d440c1900051141c15544100020f07a039900c5440c1120001800c011103072600042c1094500340d40e0354500141c6c2520098105002c8100f004940c501072a190402400f1900e40440260250b6100390420502d0713a8800d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 3855736 1250 3854486 3854497
    0x60105061b120a0c15050705030112030207051306051503010e0412180803030709050405010305031204150603050c0a06050703020c011b080f070b06060403030c06020315041401030b0714 81
    0x8030814141c41c0700c1c80c0a16182a0590344800303884980003440c1c1e00025800440700c0360b07890040c0114200e05245181500c2100ca00322181000114240018010700300c0c0c03030341540902c50107441282c1401d40ca40c0e00107403800e040d40d2820a04160f659504108030304081d1345007100392041040d4a41150f03d0010f85031200d0000a00003404010955050403005000d56401188031400c0c052000140c1d4a0304541590390b0301c00e0311540040750305a10001180d140c24000c0a0590398003202075801c01603081c1030690b039a400548100c0b44050042407585c800b040038482d120045000d14020400d0089000500004255680055042220030000440429000a07040c03841500a02c1c151000000560a40c203544c8042a002041d0031f4000807100200d000c2a0080d05110f4050401030f107094440c0b000300990792185100040120300c00002040100d50715a001e1076001d1481030105d0032410311400040c089400c01c10b46410590700341c0005000380411400101d610020a04005203c07800035008020140540d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 3856986 1250 3855736 3855757
    0x201050703090e0702060702060c07050a0807060902060712030f0903050306090606090301060b0409150305060106030222080303040506090706140304020307150f020d0306030201050304020609031c030b0f0306010506 94
    0x1003100405104141000082080540c03d0b495410580c000030b49036801134940c000188540700115082190030700c2101c5d02a50711400900c11b01c402c5a50f1610b55400405040d00c00c642d88640713000168580d00d00130240a4818100124403451281c405000c503440140c84030025441c10000f000043d0304101100d810850468540f08265104c00004180380b040b4a803154055080203000909425418090010f41e0700707080d0280014040c55180e0040d480f440d100c09840341d84680d004000030360103a4000c1010f07081c114015440c54020001c80c0892a440c0d50020301540d200104000a00005000342900040e204002d040c001d03180c20b000400d1610345074820310034124004003207411942c0400c1841d0060545130031500b00804400303009840a100074582e20094000e1004007110b9902c039218110a480e0f05843e401d08544442d020700003160400303019103400d07101e020f500840942c9907012a10f0380c1c0c00c46940c007040784402082400890301e44209824005d501640050103643c0e80d060030741d12041754 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 3858236 1250 3856986 3856997
    0x5010e04091103010e03071406060d080a03090203150a050a0902030c0f03010e0607020a02011101090b0a051504060306060f0803040503070611070e01060801060f020f0d0e060706020f0d0e0706020a0201 88
    0xa0700e0514014103410411102e60541c41c0440c2c0010240000c4050120540074403080d80c008111a20300940760082160096446044503800e81c000034406000307881e048026143c0000c4180b1a84d022038a4580d1800c1c840a102d940d0404100d40c031400d60150b940d1011f84d240080c85203402d15030210783d952485500d0a03114904038005110f841c1c0f404d51000f000340b41c100c1c04072485410301980c00b81d21086850401c1c2e0000d4505500c42c50212014010055a03a50000003580941c2d03405505800504003e4115030604240d408030601036603e5019402c06140640c0c03000810610b084d0134620111142e5202c0c144a4205110801040c1d6000c035200003104c20500b0710b0b2115000800f045030801420b0b0308081820310b0203000200e0380c85e500480e400d040e11100d440703408000c0d00700131040c0d9031303503c0000e504541980203040b0020340911601070031907200b401600c8a81840025034408043e41c00c9200e40c460301c0071000c518201c0714003140c000d00c0c2c00d00c0300000142c0300a5003050300080d01c60080c507602905001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 3859486 1250 3858236 3858251
    0xe1803130603050901020f040e0603061803030103020f0109030506090606030105070306060e09040309050604060203030a0c030501030b060f04060b0c0105090106060503011802130b0705011a030601050102030d0f020c011119050405010e04 103
    0x410a404860170150203207c1140d4503030303c6003489420700300242d850754000d200344070000701d540902c48080c0c205c02d2107241c001c0d402c0d43e2a5608019000341c00602c910304100d52032100200241d020030440d405400a03001900843c42c05400381400c484004203450b0400d03040c04010400c1c20740040420752200010f8800b0480381d6541e04082c1c03065a007650100b600403c00040015090368040702450060040c82810b0010b260008030807400c0e00c500380406480d40c1ca01c0c10200d40c03145072014400071110f10103400418040e6441c51455056044444240c1c070740d94444041200b500c00c00e204030f002811030340c20040d06550400c40c0f030310985100e07201c000005950000711080328120541c0418002c241c40321007517650360034500e8094040c2c40c002086c1654060b1003004152039150100307000e0f040c0c55041e030007103003860403080406024103c1e0364004241369038208a10541d100c028004e51190307105100ca11035841d00400c014a440020300b003030040400030140002c1c003d50381e00401c070306076860707040300d001c07601c0b4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 3860736 1250 3859486 3859501
    0x1203070f140403120c0308010e0c0d020a1206091416020705010507080702030105070f0305060a03120507030507051501030203070807080c0402181009050f0102060105210a0c0e180313060305 83
    0xd21680e04040d04000c10707400c2c0d013104298040c200c504110310a59402010f03903692100120081c2040c1c0341c1d5002858103020503011062168058140c1c07019038500740144c0d00705c4118082c11250150060b04510f9101c2e1203108071020312034070083d00075a20014015001900328002500d91020780522070400c88001303004d4081c03000d01820b0300d00c491703001402089a0b0030081006424034010190000110b0305020004801e80b0303060641004486d0000e003078560305e90045208503002c0e8840c58080303040c040103100c408007040e401c00c401c0d1000c04110a001006504500415141a10540c00400180e020b030a082c85500b001092100d10540140e6004d40c031420014440303030920f08001d0000c2c0e0403402e28111a821030381e00140240c200c54054581c02031801043d4012a287d0009024180d0080c103400c04921030300c05219100c01c820346071301007903078818082c69860fa580d06150794090880700ca988030074814141c1001c0000d40c203030801070300114900301441c070010795400094406c8005250759400004d041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 3861986 1250 3860736 3860777
    0xc0601050d0302070308031009060504020703080a02031e040b010302191a070201030906020d1d0106050307030f1103030a0c020a050405040506040f0318030f0507090c0507110303040b07050c01021203070f 89
    0x180d1b07031240a0035200c2ca001f0f0380100d02c41c5000d00c40c0242d09810120002407038107040c422105442d4066071080d25035130316000030300081c1d84047c190481031840c0c0b01b458080002000b4502d40194416000f000a07035155004001d0605180c00f640082c01202c00c80411560105d11030442054442e00c2e207072900e448160005030001c11050384050a03280c0000340f007811102c07032a07101d0608250351440007800d0800000c0241d00700c504500031290035600119090003c030f070055501c481100d204413012144400c0840200342107411030b90421001c40e001442007000c501d4404484405048180c0d01040301e4a4213407200c658404d0041c101409440d840e0f00c0f0001454451b2001078901d0903005100f102036696171400c0301d42c10107080426109400b52304408180340c07602d0b00441e8003040c21940d0303070707410708900361900c068103103440300c0455040c8010000040c410341a00d001d0310b00c1c1d80c05140a400180c2d9001c00290070146554800010150704000300444641c00c0170603086103460350f1900d55805400180c0c113401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 3863236 1250 3861986 3861989
    0x206070212010905212d040602031803060f0f040201030f0c02070e010b0301050d200901060905091302060f07030306030f0501091a010501050708090d020406080102030a0605060c0601050d030207 85
    0x400504009140d001d1060541000114500c03c40464800e10001200c440405400301c0f403070203845208012400040712440024540380c40c0492084c140d89052403041c0d091035001307034420400b580020070501e50700710300c1d0001d01213109000e0b4041c091500c0d2607401822401c50081c814046030708040081000d69101e548550181da00d03141040054150052019599181074030922044040c1ca400210b042c85c84481901d0486d44058541185422f443d99810b07036a03442c114503030400c400700740b030132419603030300c11424134020b20950b103031b6030103a508000501c2a030340c800070138031201d400211042800503150101212402d4400394101902c40c60207150441c003a028a074005000500d20074094400d0101c19400040c2070b83c401d003c200008110035076403900380c0c00248078150202c0c4061201d140401da504008000340e28009143e0343c662103843c1e0006040341d10303541003905a40e602004200c00550240702d40e00243c04221002401c2c050140d994554072541405054020154200e60f0010517000f00142070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 3864486 1250 3863236 3863239
    0x20d03050a0b0a0305010501080c01021b0108060303130b07120201021801030f02040f0b0910081e04080c0102070302010e070801060b1902010221040605060a080604060c020f0a030302040317040b03010303030902060702 95
    0x7010f135a20b0400c0360107420300b8040c11030580550303c082062580001a0400900164108064000c14100044d505800014240368040c04200b040e4030b00480e481e02824040c0c4824003605031140340740d00344500c00808960201e015a17204111110410b080c801c0000340140c02480d010504500444025020380103d0f0711042a0742c44502012030b2200d80e84e80030381406c4400b503e600b040d0f802000b41c1103500060980b04400108a900a104c014501021500350702a0040e503015140c403e241004508980c8030342d0050b00140d5503415203103c0320b2000c0c08902d00802d0310000074130506040c4000e041c2030344507c030420081d040384c40481d075901034001e406172410448142224160415480e40c81c0c1d01074407049500315011864600002d24600d8403419003015550100c005090030341e659a1100001c240410000c0154403850320124a184410400240c00700c1c86640c0c0540c88038954900310b004040c5480e80328201d85814401403007240c0303240e01a2070442ea050300e400f050681040c00801c820384200c8401a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 3865736 1250 3864486 3864499
    0x30e090c040b07150e0d12050705070c0303021006060509210106080105100312020601150f020a05030c0708160302010e010c06060e0f0f06010305040503030718050303030405010e070b0406020d03050a0b 88
    0xf003801421814150140350003003007417184940e0181103070780700d60610b2411008100144044058041d456101039480102d0f03043c005d141200644601c0300602c1d0951040300103a001e80a20400c1c0c40c2c1e10301900000740b00303908149083c00031800000310715500c04a006500c600040020740300c501400d40000d4000d00308040200321364144a80060000d00f900e02040c3c034282020b45403c2cad0018400542c0c1c034129440100211041400d00c881295151001c0004030118883e120808021030801c0c40141900301c0c820f0001c00c03040f450a01c01034100741d91180c203110f000602c0501040580d0301b2aa919080c0701e02441e00000120752440d21100808042d00080d0050300ca81d420085410008030070a806140300780241082c81d40c0d054011002d5480807180100250000d2011a5186008224452022070b00264600d00a0f4079000842e1654004540558181e9140d0341080e40040c800d211420240c05440d0440c2c4c030302410701301c005c0c1d80c84c400003000c2420155074500048031140c042d4050340c001240180700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 3866986 1250 3865736 3865747
    0xd02010c08070f120509030403030f020303040b01050105090f09070509040b01021f020a0203040e13200d0602090a031e1703090a031209060c02010c090915030b09010b03030304050a030906050403030e090c040b 91
    0x81c7e82d290040e01085010400e401d00b00003210b4000000d030ad1256070300c1800b0049580c03d123001100d058002c0e40c0003070b81100883c00b0801855607450442c034030441050344d59039200c1041c00204801c2d83c0c084400e140c107640020140006103100e003005100c56403511800940c0d01d000e952000c03469442254030040d803841d45107007403000356101e00002c540498013078100c207000180d680c0b4400328403030221101640e0200c05045660001803503034000d0544128014550030f0302980d2038550510000394072036800c80040030410500100010748860601a64079640c0a90551401e01c0803107175950007058000c0c0c18041904004010995207800040350320754407003028004141d9051001e80a800038031000c1010405070b0700c001c02c05038458480c250313249ca0400340900e83c60703107507480c1c682c03250700c000d440407240b5520340d1808070660314200000c501441c400d100030310f44100c860500400900d035580159041000401080011917806008060300003802c1703400c0c0020b602d030159220001d105950182c00300e070601140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 3868236 1250 3866986 3867001
    0x50c070209010303020c0306070504050904060c02070b0706050103051507050304060b040b061603090501020309030a030804020f0a030b01060f08040f06051305060a060905010506071a0403090302030106090506030d02010c08070f1205 101
    0x74090412481a42148d07582d407502c0c1c20541d42402507010301c40c0c11020751000035000c41c09581140c8140345880c01911003072521068510300ea5803100400b91111515000100200441001454038080c240c0d11408140e040044000300103100c0540007510f5180c40da84844c180350340b80c0d4000300518000610385961106400c0c860300c030041c249001640800c20030600081c00c4e50000c01120007541c4018050581e00100703680c01c0d0703000c9030060310a0781c1064040030031103025295030741c80c40d0180d4040c2d41065a55890140c0042110b082120001c04001000d4140300004030140f50310151141d20480119890f51503c03000c00011349000405003061040d1783c24011034015a0f0f006006442e03907000d0034885030317072141e0622007035200f880c00040c003680305551141c5c82c0b0b1003803544480d0010701c40d00d0300344403955403a0000780c06c0d20042c0d042051125036910034051640b40401008140904c2c0340001d00c50003200c020f026003030200040020050100788030b8034501c584d00c00d003c03245018107288070404c0306080150 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 3869486 1250 3868236 3868243
    0x6040b04061e0e061609180b0405071110090803010b070f0501051006030b03070506030406020a02100218010f0309020d060b0402090a0f0f0e0c09040c0c050102070b070e150d050c07020901030302 85
    0xa00f2038140506070115800421249041640200c01c0d250741c0c0142d4582040003a8006c418202c14000503a00c41440c01c8550b03490161070300803496a5628000c4901001100b8141054441584100351602e050070000542c11016641156141460642c032140d40d170408002c1190f1081c401000c035440d10302003201100f814000d4805039003255400300201c0e51014113166a804150181a0b40030340140700283c00a0310507002020000c0a91040c3d460804110309000103a81003d070302200400710072129001156403060107581c019407a03107814451118140c01045c0104820040030341074640f280035101c016111501141d04e924000b038004000680c1e60383d8840c2e03003030b80b642c021400e043d00d04500010b64560240314103070281d0506003c41e07241281e181e08000c000c0c40d08502d41414802103c42210109000f807018180607800348081d0200c600e000790004003800c07403900c0c07550701c0303807504030a01c11689401000341c82c01810600000203030307a200c481c002c2e5600e0190102c020f40c0001444004020540e020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 3870736 1250 3869486 3869501
    0x50a03080f01050303040b070209060102071203030c0e0a05010509010c062013080c060406080601020703080424020706050d0504020f15120a0204150503100305010615020f03030105010206040b04061e 87
    0x7450721112039803030350100750710792081d84518044960140308203405071400804581d080b0300140111140f00d035450803514151a07401348140d010a68a195040ca001d070810724100b18100122024981c150904001074864025081454100080e601c51141002503a920400103116181e501e1007844c080000741c401203500c903086016a0812449002540f0580003841c00d0964200a20590426007043d070700f2282c000f40240402c0c11072061500000100300e500c0c00802c003612803008000d50040303000590640e2405c2940803a4110340c0000c20030007106034810b003034540c103411491000c07030651030b1400092a854880e084065114007040c031146a0309801d07800800f5601990507130111242d4844080c0c200300e024621541444110307005070b80c29010311440080d81d220f0913200c0382444081c0c581d20391f2800c6481c65005000715401809404040c590104a003040c46143da000552030756041000003512404007410043c9445541f2001c80c040203003c1c1c1002866241a615422603600c640c3c00e13040107817004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 3871986 1250 3870736 3870751
    0x603090318041401050d060f050403030c02010b220b0301021306020109021005070b01091107050d0305090c04050108101e050c030604060509040b04110d020d0c0303030608070f03080a0309050a0308 86
    0x2441640030034105030084810203643d1041c0615035070310b08030038040340240502d81100d1103561140c16025121841c40f500780240e001e55000581c0c443c4414000c0d003180e41e8524040d118800c5101e0255000501ca0310000e07007d4241c901c0441c03e4014403011902a0069000400b900f51300304002242240c1d0541c00a00d01d580220b41044400d10382940541e00362041c40006441c0040320b00060044044603000300c0d0140d10000d60551901c480c40d26107904042c01d000781b04001944800034001000c401300003260014408850410280d4176083c0b8050351058466802c10f0601e4480710300034035041c00f280b0044070000c03481d02c0030301c02442c2c10003001030580e00844070309105600d44200441c0504007081c10b5442283e200c0510800c81d112500c4000036001944555139004203000580c1c80182c481b044800000c80c4242c44035481c1a0540c13401030280c844540101e081588140410003140300085002c0d82200d812044180d03451074020070442c098001c03050060014070520011f2010035921008481c0709040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 3873236 1250 3871986 3872017
    0x30507090c090f08070b0319050a050a0f020f030103020d0206090303070b06030d050a0203030f1902040b1c020a0c080307021612030e01030b0f0609030102070c0608070201180c0e1506030903 83
    0x1c0f91511440c1d41480380c09001c540d039101440c103101841a100040d0340201e031170325801148179440903658040c1e547c01c90f00750402d0368950050000f00e90180c0540710740d40e07007040300940c141412034083c24154001444003034071640700e1243c40b00c01e64480c00100d91400d00d016040d40d94650711420589007103203054903094001d129030765500300402d01c035406450414101e9805945181c035060340c0c03207145803005401407484045440c81d40b900003240d84010f2009080440b0402d45401e2100c170481e608481c1c0080c08002e00780100241e0140750b9001c2c0740c011280b584059000c0e1203444a03030342245000043c020006021980d440080750314003c0440703c0002074402d0741d50751060340c0107000440540d00301071f80e115041a14542c2c01c8075240740c050080d01c2401e001400043c14903281d07468044010f030750b13a48601c000c21a5034091241d0554207005400d00004000410220107640350380348503004000d44195007624210201040b04100710010454142c40c004003029241d050040e007564907548070301404030300110b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 3874486 1250 3873236 3873239
    0x80906100e0103080c010605040c020714120303010509041401090b010302030d1409060715050a05040b0c040302060301050906010c0606030305030601090608011a1e0406030204090c0302070b04020402090307030507090c09 96
    0x114001502068900d8408415107607440e580c3c4101c120f400c0a00c1004443d520307000701242d00e464038031900015102c598000c0001030700d0704d030324a0000600340000d40e0143c1501080551862800000c03a411548181d50b40002c44d234660510700640d042695906e0115420309a090051102a0f200c01e410703030780210709444101c094510291028030020140c2162110107028032601d41c07034180c01821243d0300401d070203e0107007418036030034080700c8044a0f000c410301e955000307110500642c00c036001d074080004940c5500e0141150000740f403901051003194170a480b80c00000380b142e44603031004204150311020a111642e242d240c007a01540085a90070300248032183e000070748a1050403c07a040700c0580b44c004040040c0c3c10032404040d0300001907151001041001c0342c01c50b0100800600051800c1d607001a1550b0401c940701c000d55041100e07040400d2700520101004c11a0030704c440c0c0c2c20641c1100c0050b0345070030746c4000c0380c02c0c042c0740c0c6d0010b4a14001c2c28800a10f8120942140344840b869a89000409 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 3875736 1250 3874486 3874501
    0x319020115030605090c030307060c08010501230703090b030702010603020f030102040e040f021f02060108011406010f03051b040b0903070e010605070803040804120503070506070207050f1c0203010507080906 91
    0x25444810440e01060204034100003041d43c941c041d540010002c0140c910300800040802d1841e848460111001c0765158100316a842e4007003155400b40000b480d01d8454481026200074154200641c3e8403d000000100c2604150240b2039030001040140c98868403440c1030301001e8001c10840c84107030300030203c599200a851030103100301c0d030603941401d07044c580341e85450310703007801030101e4035800c0344c00041100c2d1050075210042441c10081c02c0c107500800f151741c1010116820f543c1c0b81e1355400d07100040e85007030104a0b038000e50152801250351400062550f500408145007000540f01610800070014007c1003d03054440140f100380c03005e8080300c5070942c1d501424402c03140c00f44180000284140001400100f5900080d60040d006a01007814a51140d07a61090500a440308507013030b0b40000ba500c2d00b0040d00b403014560054050024000c650716000c040780c02c00c0051b9024a1281ea40ca9030b4040d50700c00f05091565285d60050b008110a2801030341c090544601075031a082c0605c101c90000d9030031b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 3876986 1250 3875736 3875741
    0x70512030603070603020c030d061511030304110f010e0901090b0109080304060915030b0a1205100c09050103020a050408190c0909110103050603150a020a0f030204030206041202150c03190201 84
    0x1d5071016000700161840c10004400a41000b004010107000410a240800140e802410058685c6083d5203182c400640d07000b800e2040f03140c00c502c40c250000c0c0108004500a4040468011030613102c1e0450f03400c81c9001250254410791040783e2150b0002d0012405003810342c0b007200010400c0c0c0300c20b26010f4a0300317141640e81c0203610a0343d00003000003905208004502500c1c181c6410a03007400f0a001000c48001a00c0480d5900700c1c1c203040c18014000d07014400104010400350202c00001c001c1c405003124010460385841c06281e040c9038000a403041510720900c1100d005012045c29140310f000803020318180408038007002da480c49811500810401090b220b46803445601c05044030700d01c5841d900540c013030400200b07155491b01030f1040040c03001c0d08600c006846800580001030741c03480c50103009440120303202d041504042c8140401d00042e01c50808031000e5503084012559081801d200003a110401390f0b441c9032260340007042e20340180e50000041d180302d100100305009104640c0d8000c908 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 3878236 1250 3876986 3876991
    0x306050102150105010c0311030c0303041518020616080d0203010501030b060a020601050405040f0f0b040201020f010902030304090e120a0201020d050c07030c060b0103180c080c0f130e160305010207051203 90
    0x1520a10b075401005070351301904903a0f031158402d08006400e040e903840d8460554109540903101d5400002c1000304000108002d12814000404100003566174041c101c00800d44218000b4003d00300081c4007010805803810741111250b010050340d0b0b50307040c06440c00010b90801e10510340400c1c18100e800d1850b2400b1426202c071b1001c03590050a0316880c02c810807000d810080d0040c1d40005501560401060402c1c806003e0301d0f009070146007030b03401c00744002840d10f80340310b2041c0300316403401c4017000040e64048200c60032152080741c0426460074910507681041058030104c1c40c0c1800c00201800c90503010340180c03e8956415904120381e6403800ba030081c1134840d4140c002c1c0018141040712000803c0c1d940881101c0c0410314001034980000e0041c0d08800801e240c0075070321b04001039405c000185080141c00d0850405643d1440034032440400300364620f94144145a0341600c0d182c0c0c002c1c07001010002040440d2046883c05290750307aa0400768003d60040c2000d0742c95005001a400c1851091002c0300d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 3879486 1250 3878236 3878263
    0x60e060105042414120403090504020c0304030201120b030607020601030b01091109010c0f06110c010b0307060c1e0503030103060e0607030c02030904020a1206030b010e15010c0b060f120d0306050102 87
    0x14000f030900819183c3c0c5280840d00d0000340440d00c90030103280c0d4020005001c038401001a80e0115003014100038251015942c0308a114900400c00c030400308134040140d40880b682030070014030707100e9080381740b0000e1702400c2e84480d00b6110b500100101903500040441c100d034021240d03080703681d80303509101d400c1c0c0c0c2505000e1104440c081060401c0e1b94454420340301000d02411510002e51070079a0b4100a807003c62140100945001c103241c4440c49003881036903040941100103010051a1450140c210851803e0240043c0040b1025075038100489130113030915640082544d036a90384900d84680203003c0344144504510940c400954414080e10030b03080007038003d40045061400d2101040083d40c00010904c0070010b071240c0307404948030140201c0c00603600c0f581c2c28289641c1401c1200410880003031021070060824440c220a80c0d8005840d0025590807140d0b4608550310400490042140b120856800c600d1a0200c00079211001c40d040255159036a818014590365100485e5601d1b100c2c045103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 3880736 1250 3879486 3879509
    0x504030c0221010e01020c01060b0304050d051b0102030a050f0a090327050409080702040b010504060e040b0103020403050d020703020a080a0201021e010605060a020a0b0105010503010b0306040f110706060e06010504 94
    0x380549001440c0c08081074240c00d800280c148980c1040782512240356521100e6074001c190503211480c01c0c025a409098804801404d41c03078036841e040d990300307070070320a20043c054005440a001603142d010b02140c41e070b048000355945d040a03060342000b40300131505041d03040462000300305490b19601030b8102154043d0349180e60b0301c004400440c202000076013280c56003004070310300081d6030300d07140039990a842c040e0010648401b2280180300668079140b6109040010402003408401d802c54036401d00404152030000350b190b11540164002d208541014042d40300380e0800303840c41e03030b0f002800030141c034820703500c55461a81c4c0c0c2283c0c540c3c0302c0003048000d016800014201031441e001210704941d0500850000c40c200c0e5030352000c62040d600400c40240181c101c0030400b41400303000540e16006150a1070660b29643c5442c00516040c04080c0485119544420465541d00d60940107034900c00c0019504540c0c840042c0341600c0281590300c203405120f0908030008080f98040c2c42514100c0d048161030303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 3881986 1250 3880736 3880757
    0x1050609010e03012007020307060f021e010906060e0618010605070f11150309010506030307030c02040504050a020415050906030d02060708090a08030103030e01030b190b0a030204090504030f080a050403 89
    0x191120030961440d90340640d6100c112075000505c80c42d201d80d2440f0501c2c01680c1c0c0d0321007070041c14200394560300440103020840c2081d54000782e000607010410300d00b031040406134040c41c504044c007420b03056001a1040d41001c80101e4051003015076a8050313002181d0254401c2041a88040004802d22419010070b006018480c003003014014401c14291040c1e10b8180c2003a440340c00182000300510344950954000301c1000b100c8402403140b240c2010b0102c0055041c410580e90042c0019030300b2400074091b5844201044c1040010007080c500b451f40204280300090000d03607921030451091140603c075500b0324022441508020800400d10100c9601500c0c03e50307141071064440c2c032005440d010007403140c6e40300000402c0b8070354061400b8600c40da640c210008032200004007a82c80001d0820302c561600c4025040031241910854110f41c0c0c000c42280c1c40d48851542503009006540c000c00b08542000108010135900647c4401461025100c00440751203220b45c18089503411a00180441c048454 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 3883236 1250 3881986 3881989
    0x50c010c020301020903030301120308010f0305060703020d150603020c010605010302030f150607050d0206040b0606030603150709030203030408150f0f070302070807050f012703120e03040806070905041401050609 93
    0x418400c014005800586000c4505002c00e00e5980260701040e8811401d180e1201099401040640101044800c00e603003142551110b90321200003070200b409040e0f001940021000c01c0c0c0e0814202020380c40d1240d030500380e039500d018019511901c20400e45501e003d00102c1d40f58000d01c2928059081c0c030b41c9207186a554a50b0003007010b042851159440741d0184a400d00107030041090341501101307540903040c0c506103403820410303202c000707051203114580900030070403507071400201c142e5800c05455144c025910303140d070140c443c3e000d1600040d406000015021401c1c080c0040c503600044003829081d042a42c0d00e5160b128000c1084c2d5015004002c00d20120b010b007480f07900a4211240200c21082c94400607a85140c6002402c2511882c5651600c070800d420b60013a88144120031005011160891000d5500804500c010302d4010903242d81c690080e00101420003e50f4040c100131411203071541130a15000c2d02c0d000301d81c2f1415101e04e0070320490480344540160760f94102e8001138035041c10700c0d030f80e00c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 3884486 1250 3883236 3883247
    0x91b02120c1501090204051c0b0a0c030b0d050a0b0109050403090306050406021215010206070206091e0703062a0c020a050f011202030a060501030b0901030218040302030c07170c01030504050c01 85
    0x200c112040e0b1080000c16803001070515080c0b40281400a00140c0c2ca501d010144103d81080b0b030200400040c41100300d0b400f0070084d858807030f80265090030005155003004002d4000300311000c0125040306899516104000c8001440d068031405002c880110b680d88003030344029601c080300e004001804e1030400300005405600410341080c841e010150a000ca078940f200e04268049440502c02000a400c008082d40c0500400b904104188041d0440345005004142c3d1030780c103082d59010a402c0c01c0060308000f5824000500610342c4003005204c11109000e14280079020154241c03100712110b00031410040c010b036501800f40307501138100307005a890202041001681600001d052000085e9041c1e05040c480c401544900c014060004100b0304120004003150348002002d4000c080400060002d41d80344018000303d150854080049543c2c1e03441d00300e00354001c5001c0103165105494004c140044055808a203401020701101c00143c0203200440036168199006040e6800040d2100500e51094 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 3885736 1250 3884486 3884497
    0x4060804030203040b0307050703030b0a0b0412060b060d0e06090c0306070503060d060f020309011103100b030601020f010c03050601080606180609031905010606140a0801060507020f19091b0212 85
    0x780141c90404e41c1d112a1a501755108a42120020314005295001c05805109150065200383c4d82c0603866800e1048520b007503c1350380529201d4020000c0c090082010301c1d04907503110b000c003610326501c544041d82180050040c20355062481c0c02000d0020b03007c4030001920882d80c0340b00400511254a82040c196043d50001e800e02c3e400042400884e00440c00e28014011109200c02006a44c0d00e031036a115806c41e07110a00186d2801010000d003c000315a1a02d05426544105110b95583c1c0703924005038a01038009809215135400d01c07914001d503e425600441c810301c401c0e00c40c61002d80d0388404100441c85080440c0483c010700d660344500e1802c0078005042215000350481c0e252010803103400c0d03911407003600300311016034484006000956104003d96240b040f0f00a4050a25882080180002005000b5002048804280c01056581d0f40b0040e5400d0000036121090103501c80b17803e84c045100314001c00f041309080c0b20300d4001d544c61540a0000c407454030742c007508000a10240c20700960303214 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 3886986 1250 3885736 3885743
    0x30d020304061407090f0b0a0203070209060105040e04050304050a09050403120c02070b1c0b01020a0203030703030f0207020907020604051203010f03030806040f020408070801060603020f03010308030a29090a090804060804 97
    0x707030304400c440301140d40c000c02d00031324a945401880780d240800303068094070715400480203650144103000046800100f030b182c070380d64102c0f85111107985503070040341c0601480d4000155289600b0600c400e00c513000c00100150f6200392124800d054491704401c0648805950050000c0c800e4010625407140035031200100c001144103889105a4405a484041d08074800d68105034a017a41245440b0a46209a403001d000c20300203031040c0349458001039200c0c01091405800d01d92240c03080d05210a166040b1058264010445680340c2403c00f0002e6580754103c4044036944143d129900f2a01118010340303040f01c41000240f041c81d82190703070440320a80080d1180c1d810075200d44190640f010fa034000740c000fa10300c1000030214103150108843c20b42c1e0b50303503101e0818184100107842126241c03030101c0341501d811017001642d907200c0d03001420040c0104a815800302e414a114020044002d0400008040f0203c0d000221621100480c00807101090f000411000741040b0800c00d1074012580103500c10300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 3888236 1250 3886986 3886991
    0x31203021c05091e0f0601150804080a0903050304030b040218040203060703090204150303030902090c0c06060108091504030201020301090608060108030304021903050d170702010515060f0c010213090e0d02030d02030406 96
    0x880000d500384c14000b80c81e810321160020303da00c90300b2079070400a1714010a070110722900c61807410440900182405400903080620015201c80c116008400c42c00046a103c81265582c80d501e0400f02921001901c00b01d10800743c1c1e500c20110146282580750195070014040c005981b5040c01c158010a580c20382203070002c0d2078202550740c46108049140041d801381c0c0300881c20861a2041001d860002000d074100444240701e02c1200034800605a50305c4102800c14070303000c0c1c9400091600d000014243d0344044a00c0c202008105035064000e14100c807412607050001644803a2029100c0c0c109006900b8a948180001b5002d0702e8a4126820f0800806a110720a0740e00d036180c81e4200903180c84000c1c041100284207013603908012940c1a400980e03880200501c0c240821440505561048010300c1401b02042507030512003400103c49400c240708008542e541c1c0b04c18074801d00c0031000c2c4221807805240c6041c600c0f09850203d8541e0048100741e01075032030803540c0341c0400c000b900064015103940340e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 3889486 1250 3888236 3888253
    0x81b090d021206070206060105070b010603090c050904060c08010501020703020127080d0302070201080c1204030c020112020c1e011401030f0f0c0902070b09010606050403141005040804031203021c0509 88
    0x202d4400741001050026006003050b4544040b01928150001e403d5904004c0200044404181da02c40c503641519014940400e8000460800501a400a800081e80052444140000c0001540c010801d0320041c0d15038041036a038890045e030b01e401641c840640869081d410f034401d0809641c50960307030710580d00c01503807080c0e03110f103c650f24128001101d6400b0071360018108044d0740e000300350190701c1626080c1c0685000c40800c3c05900c0c0500151001302400803103104030045a0191007090644100c074802152102650207075540c2d1500164031890007a904907003014004d07481070041c802c02c0d07101c1300305485107a440c581e20201d4070b544160066035000c0311500b90100190700c4411201c010300b8605800f50f00c41240b03040640b00820003502410460703240c03104c20094103402c0304c15541200d400c01b001d0710b0400d54003088141405100d003070f0180054039000c1000200040ca1004d0025a03020b847e0701c050700501013200780c00308c3c03150103600c00480c0300007100222081076581185910800800c252030194 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 3890736 1250 3889486 3889489
    0x305030c060103110406030c090509010908030702240103030f050a02010207020303030115030b0a0e0105040b0a0503010e060403020d0305090c0f01020a06050c04080d05030c07020d020118060504090507081b090d02 93
    0x5400c00c800300106504900010030034030840c949400520740044500300f04441c034590b10500d810003140b242c86450340d1900000b5142c800f0030742c0721590468010340702c60365034585802c8c0251243c0910414850080410480981d040305805007241070304d601d0f4172104020751160070248c4160700180c0458085640030040600161002c2c0060741c0206180420010c00a04482d4040c058944036100c06e03003c0e002039542080042c4034030005504445c01904c0020701c0b03898020109402403259003110740c01d582080c05044540c1b030000394462046010780d017500d02c0389042210480036100191354945003603011061703240840c0381004180c00704840500440e440039043d60750321390580c0c000720b508100d14074001c14100300d03c240a003d1504800c1b02c41c6002407440c9001c841c10041e5018924019018511441c410b20459005050a90200980004c026a915a40c2c80014240e90142c0a1104103504010104800030b0049080500400788009100380160418008500344e4110002c9142e00900121440025 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 3891986 1250 3890736 3890743
    0x60408090906060d0c031b02030705060103030302030a090b0103050304030506070903030207210b0a0507110c010801090e0703020a03050604120c020603060d0312020a030e0d080402061c0603060c18080601080718060305 95
    0x410500e40300402c400c0041c00c1f6401104490815040540d0001c024080001e10041606415250306080c01030312034942c0c1d41e80303100404244900802400c0610004418400f001010304200c8e4446c0e0100d4500383c0d103150044801c6481c921000340981d11012091043c1c03030f00011030005821030700c10002414403003a140c0030301d110300940b403070140d4558540a02100550254100c00710051410043c00d24400300000200b44500520031441d07a00d035108880e400d4100c00380320344001190010550494940c42e41003a03a11501c0a4508880c03419944bc905040c03140604cc6c0c190704503400800a03411590380744280b010761865030b00304808200f000400203401c4840c502c040c0440c070107a40d40c0000c0880703135603020b640f400d910104110244540340d4100030040c0c1e038860890b015181c00b80080e045803442103842402510701a00014030444c149035041806a0b03100d08441600030500c040b1b401e226940380d0010792545400e000720b06003a000380c28280100307004205041411443d0741c6001400700d41d02e4480c5400d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 3893236 1250 3891986 3892001
    0x20604030f02010806030102040b0d020304020a0302030d02160504050402090403050a0e0405010609051201051614040902030106030e011a1302070201170903040611010b0f040506010e0a0305010b040e060408090906060d 95
    0x764031901191503030555030720405140d070016055008600c1d1078181001d000340350254158288401d60008005811500c071441c030700f001580d006d070441d075100000f0b0360069100d884061903061640342c4d688002440d403170540601405181c014007840410b44171628102e500d1742c45444410b0500182003910799650b1602c1c80b9041c001e01540d500c041c0c00d04e0500040041044c0940c0d03100f46076a06000503c588040c0340520365043e00003d0409001d8a80403100e0300c0028003039030744038040151002c000028855010f4014000700c0c0070b100c000b000401c812145036840c400b110034200b90410301201c5840d0900196600070300465005050208403104076012051442c6800c84040c0305030341000c101000300c2038100420540c2d14590b10700a00026a8840c045060141007004840c0709036119404203900d6400744070301c0303040d070300c0003034a1130001d6a124140305d80a8011450790034043c0d442d08100c1c00080390081000e5001e546e100b58240e10340540002042400303640500080d40c40041041740d40c404101e1032107402c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 3894486 1250 3893236 3893243
    0xd020108070e03060f061201060509130201090b130f05010203030403020606010503090106030501090f020102010605030609030306010c03090504050901060f1e0302040b060c06070c0c06090602030706110405041406100306030203120904020702060403 108
    0x224548103050024030180f03410b40700088d0703060000500007a81c2c0d01c0d000c0381d13200402c038444844291907400121340a01c62a44110b070382e050b00150026903000580d04c0c8000392000340500781d4023603540b803004903038032702c01101c02030016084017004c10322940c03244005503040400c00d400400e400340c1b207480321802c4411507042212403a1510006004558082c010480100383c201c0140c010f618007500300c142c81340300082006041058840000c010140100075030405010045c208000e60300d41391300c6441c000c1100f4058040c201c0c44403940028200222032040c00c540302189680e00d0a14516820b21002c1c10001c0003440e400302003070206041d0170308c08120a6119800c0c6507070b00301826500e030402c00c8030b41c142c43d003080003080308070391003842059000021038460300c3d0300000c0064003004e1000e00c2000d034001d5400c000c1d0b11905140c40b0300d110612800e0140d000c0e0b82c00b1a460503145191100642c1210385a1000070341541010b1040606c40c8043c4000c2c004c240f1000c0c10152405015a000400b130b94455041203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 3895736 1250 3894486 3894511
    0x20f070204060905010303200307060509060a0f0b030a0303090602040e040317011d1807080706050a090e010302011707020c0d0c0305010b010c230f0d020303010812090d020108070e0306 81
    0x50003035103400d0082c2402481c6582040080d54119240203040490301042588560702e0040c040f455003204208139180703250010010001410070764a40d50325208281c5610072213034240303800155030000c9032007017881c01c190050040a003ca0aa6019405019001401c0d0b44065003800009101130600501500c518403990f1001c11001803403908400041d030680000300c1d502e41682c80e44a04401120841d5080880c103040c1c0c210382e0040300c4509180c500d07140c0010203603004e80c020018a00b60024003030209007500b03444140c0c0e50703a120003079140c0e400000d22019000400105003d261110001030380d0f5004001031054600082200380440d100c4c1e07050080454020066000c204180607003803140e154030501c02d1910510b5000d807501c030038070110320071880c89502c2d04500300c02192500007001071201c40e070b8004c0c0940c0c01c10f01e800600071b52203401c00d12403e0498007400301105009000c0d1422505000401054110208051307001100c00074001400032007802098800c1c1040c41d81c0070003e9a11410740d0b000328 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 3896986 1250 3895736 3895747
    0x10303090b0306030a080d0f0606030c1112040b0a18060c0204180b010b030601020f100501030303050105030307080f0904060810050a060f03020f0603060102030702090702070e060904080a11070504020f 88
    0x20300e00009944808480c0d001441401600d5a0100e02c1d804d2994100c10101d44a45800958100500345041112242482c3c20400115287c15030841d80008030152035800c400811001d565856244203081c8045080e01000203225403c1040090000d1156a16000c00884000009038007040540e410a0010800a0b44040114506070161012190040c2d034161007100c03013680c5007055103c040c02034100258000c400907407940d100b040f205170010b4a80c8115440300c504602000300074442804150002410030b400805c250400104031040c40e03911644080c036001d0700d07400d03c6009801c000000350340140c0780e00c0c0c00035146404000b441200303880e19800103051704002101a040700c001d580303d1411517071040700c20405a55144ca02408040054070056078035581d4500403429031103171600081d40a1910800d004034194001410400d4400c1500c00c6046a00d0715003c105a030380c0c045078010400c000c1044601d2026101d00c68561100318905c0494102a4403000010144d03082108a030b13403980c0000c05d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 3898236 1250 3896986 3896993
    0x510080618120c030714100207080706060602010e030d0213050603090607020c0118050603090a06060308030a0c030b130b011107140103060f0303081f0302090c040306050a0506091302030717060103 86
    0x144042e0041e101e407034600c1c02c1d41c043c08440e02e0f409820b03405440d1a0018508078490340c014080c81803034040d030b00411541c4204524201d02260420181911028604400410b0705030051103010901c10f1078000450030076040d1a0058060f500c03091180c00f901c00f150301c000590392204ca0107507000e2071405010380414500094000c0c581150245168100007403003070082c0303d010011005005682c800d803034403550b903520700d1540303458034404000081000785030040c00428003c035070000d54010034400200b40100c0078408001c4090300e484020280d0310076160900392004c7c07401c84c0e200c03011208060400507451618101010301f010819402041403145080340c2c6006503034944142d5014004000d8918404c1d030458400503d491001009130040c07807141074041034000c2512203078400642e40204460316a00d8100f00840c1950407920044492908120204401115902600c2d00c030315001b42c00c141d00b84e43c0f80000c0e0a0300d5042c42c0070603a050b005000000caa00c92200e0103118070043c0c08402450254990701c1c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 3899486 1250 3898236 3898243
    0xe040f020a0b070312090c09020c010e030406030605010912080405040507020a0506070816020a0b0a050c07080403030905040f230703020f21060102070b040e060103020c01020a020a02040f020408070302040510080618 94
    0xf25262103180100c258000b90107c182881500c5a6810058a4810207485d41c0c0c014003490b8041c0d07030750344000700d000550f059054000c0c8082d02e4007130740c4040001c1d956010441464201020080a0b440180710900c07044c249544034039806a500d00c1100c2e02039600703840780d40c00d2910560b00c020015a500c005c00220031003044900c010f40905100905203a61540c9a4a04100f8003a05100703040d5100c0020a01d41c141d01c900b5070b0100344d04218a90b40e01d03580c91502a14a08503403082034011030403c210704104991600c10200c8041b094451452500d5003509a100ca41c40004d0801c0d0034160309020392a401c40020f409448000d10908601ca00300001610581c1c40e42802480c56046500c41c00c01440540104400d076800c465080000924944583d001600640654080034049600c0424641c0d209540051641045802503400700f002181c4044808181c0c0314500401900c0d5110392010401030415500c100c0d4080c00034040649016120317a629401d00005442ca0200f10318910302d0405641400d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 3900736 1250 3899486 3899507
    0x6130f06020d0503060f0d140106031704050d020f03120f04050301050109020a05041203020c1012050c0f2703010207030503071403070c02060702040e0102030705131502070e040f020a0b0703 83
    0x70300080c0a808100310004141c0e200003090940101a8810141c0e0142c03544030400d4985a41b014500c64026810092a402031141c3d10060b100b0320340c005d16040c1c1807403141741141d003658006000710b225420f0503001c0c070807034075800c42c42d0a406100b4102c500c10800e591101800c1c120f00385007006035031180b9080c02c042c00d40340181c204914251041101c0d19600f038004080303508a46000403021501105420203906002c00c3c4c1e040300e038000c03c4244007188003a0344400f00c064214840b80c0d08210f19100c60440d195180120310201042c040104080d0380c4000c825070301c542070b1415045249841d001240c0c003083c00d80e000407801b1804a9804414004120b4012660304407401b03561041600750b207401800201054003c0d00c010340200000180d0900395161750b0880c01490350981c00a5560303051070301e8024281e50280d00c920880c03803030204010a00304842440c14078011000d600078030106003400309401d05114094002c0300c044c3c7c942c42c020001030b242c0003185c5009001002103a516000241401350010034007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 3901986 1250 3900736 3900749
    0x7030c05090705030412030f02070602040509070f0807050c0703060204140a090504050604060c030905070608070e0102060910150f030308010611030a080408090d050106030c170303010b0703030c05040506130f 91
    0x2001c200200c02e9440002d036544203800502000d10422001c10543c002c0861003d0708035503600020b101c0c4148162900100115203040e1002a0305540e240803c4548081d004910740018503000c0c04510100d116030040d08180300b00c00d0581c1d0081d6680c1d615134040b030380a6805684240901e5000d6289464401d82c03480c02480d15440c180218502951102d0300e13902c1c0207000404d1996126132781480d00d442544501a05940304003150145030721003030080c00d004412140b030700009002c482845025480400c03064041c0c3d003083c008001c910101c509807005440b18541001364000207000026a201c0340411a02c0210702a4460b0006035040140c0101103a1140d16121201d50040001403442a40400c0581e4802c3d000160755442e007450f80001001d40956880250030b0358280b90000c001d21620314028401c0310b0104595865201003801143d440780000d21544804030b50620401012a010780c000f21482e03095458441e281940354170000f0055004601000003000d0a10702c00d21101c105400c1400c0585031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 3903236 1250 3901986 3901999
    0x605010b07050a06021606020d0e011b050324150301090506060403050a0210110d050d05100f03080d14010602010504060b01090b0409020f0d0e0a03090515090402210907030c05 77
    0x40c1ca484070360340d5160003540108502d90024140340340da40c04480b0084c510303174449401c2d9624044800c00ba4003404100840180b203501e0003003101c1c500c4203101e42502d503841180d00d5081c00c603600d00305050030150413403002c80309000510f01c41c0784039941c0b03c5808000d4101c6d200191030700e039410001c4c01720481300c00a11250050004000c00c0c00410000207800d5803003a0704580c0087c0b4010003405c01ca078407a00554104400d441101c840c03824458000b00034040139401e0380410411681c03a4000b50048003684e22400041d402c0b188400d0020401c4040203020340606a4400b0424410820117982d0700c2009a00050050351760300144801c20030345020303c2c4d00818003464130b60402ca00b4082d400c01d44d032059204180401d5400550f0b07480c0004d0000950f204048c2c04801007003c0300c12134040300e494843c00d2200701c0000b1144580030a00e46403240783d40c52080301080440b4102405c01e401d0000070760007000c0c00f115074800e581c901442602c1201d00544220050005086800e00c1c40c6004c0e51144250f800031849000d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 3904486 1250 3903236 3903247
    0x40e0303160f08040305040b130b040f0806060a030b06100e180702060f0c0306040e010e0d05040608010801020307091a090a17070801020903030304020d0206070804030b0f0109020703020a060e120310030605010b 92
    0x1ba0712100380c2c0e094a1041d540c070781d0f0b64442e0400920441e2050b42c0810a15140440c0009080c40e4425242048516001c141c801d42c0d983c0c18100015514a0700006118130711004c00318201c0c0c00c1100340c12aa2442906108000080d0308000560320944c804251082d00038120401148990521500313411500342d8100b820107081c0b030211080540401082c0700c2c0295611358030403000c24801d4000000849000d42900c00708008071300c0c010300c01c0d0300900a29012540c00070000421600c1403086034400e012940c2c80d0403025050281d080c01407034010710003545c1c40300300748580e0f00d19a460300713128801800e558000c0d00c0d00c00c00d06407805050604d16406038010780d105103c14100d40c0c80110440340d010f5411203c0303a25030702c200e100003207250040d02c2c4054604500890080308204030511814000e0240301c4000310560381e100600016803049080013001070700300c00345d828002507464000c0100440c0c000150780100e140c0c030491008540003280d1280340402020010000d0104522a85000d0040e40840c40e2614 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 3905736 1250 3904486 3904493
    0x7050c0a060c12030c0504030605151c05030706050703020903010c020f0d030b01020c0d05150109020307020c0f030318120a0308041401050103020102030a180e15010206070e0d08030402040e0303160f0804 89
    0x11081c041c04030f814581c0310000f071117980384240210f502a560104042209003000009034000d105081c241754041c40000d6013004a1180c15804001c0b0158004015443c00003155206000303081d01038179140a05409101c2035030550390a0051105200c4254024080402040c10103480c1400010081c0b0078107181c401c02c203203c3d99001c50142c0b1130000654100141640c58900f003480d046030f01c0f110881040e041000071640500f150019030081c0e2041c0d0031a0300d50010501040008410300c015190f140e401000025000c0e000360008200c1c01c440141454145841400000d007002d81004040300021040003c00040100440803000c2000580000300065811680080e5591091140d200c00b48104101003940c448414025a0050064000b42c0d4180d418040c4a15140261f5004258003500071100010b25091052010b410408002021521010f0054940300700c15840600140e030072648603050107c0c5040100b000b14051a41c00e0a4814881c2045000900350500d00181c64100700c2d0400511010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 3906986 1250 3905736 3905753
    0x105030d0c020f04020c0a03090608010609050909010b0402030c0403060e010203011202010503180703030f02010c030e030313020607050703081e070209070e03011401080d0906110a0b10090207050c0a060c 89
    0x40c059600300004484201c0c000038904111000c1500e038094000505400d001001003104004107100f516010031091b12013806680010b0240500400500103020030002480c00da02e242d500b103032030074000259903504400860700b6a030044614041e090000142001001201e20442c001070451400860075075060440c540111100c03e00080c1c104039003c004034107007960802c80700406422210440b0b440c60b56900d40542103902a000000165280000b80c4e4800d5001e070146d896101d032a03402075899581c400940c80103040038410b090f40c1020042c0504000104108007000246004180203604c43c1d90200c54400d2420050070310950039001400b464005031a041d114a40096860030480c00020041d07002c80e0041101015001c42c00c0d00010000500403004500c01804040b81d5941e1303c15281c48600507540c02899514007540342d48443c203045d02040b0043d1005400c41040c001e0740301c0c1265980d003094180c3e000b80c84262070680101e980e50300d00d8074215240c1300050040342058562459a81c440000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 3908236 1250 3906986 3907003
    0x90218010c031107030b060f030105060f01050d02040803030108030403140d080703050402040216030e030d03060e01030609061104030c0603140c07140106050607030206041109060607030e030a060c03050601030501060305010503 99
    0x6015210302060304040c021500750ba40d00d40208110303641c4d1581e03800e001c4590703101a24694010141201c4c100764609060050500c501c4014010030304900c00f0380011126540500c0c06840c1c00c40d400c0c440030400c02c80900003107008044401c0116240c86c1941040d68210340228801d100c0d9a004500c841c010980002450b40d101490703040014050380e544c000f00e40030707100f1492a0102c44004603031210816820155a0945820540490300c1808180344160200c402900900b001443c006004000003492604215805032080d40c020808841100c58800c041e000ba40007118161510f450502209a252140440d0642c444510151904240c0201c22a0340314400028050311140d5282d8510f4079002d42001e0000c0502410160340d03460a0300f4002e46440c01a2011156110340c1c00d000c40c0f1510b4101c80071070080c03100500440c40c10f6440d58058450a80324100305406000f044428004100179201c0c2c030135042600e4601068600e40707040014200d6405030444030a1601c0e04d401417040ba00c00154891 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 3909486 1250 3908236 3908239
    0x6070302070905060102120d0212010801061202060304050102070605010f1a0a080411030a02310509030901050a031e02030406050a0504030e0f06040b030901060302011101020307050d090f060501030c050a090218 92
    0xf000c0e216640100d090021412003428000070010300d580d51200c0c10703801800e00304540001c01540780d80300c1210038284c98040c481d0070365400c04c4070078070800b51030114021030300b080c441d40c001441c02d40a591544141d0b54241d11844491071110f408201c0d50f0000c2030038201c40344184010503c0e025610320f01409040000c0d1000c0c01b050b00681080880741c60030000d4095040e00102003014040911642c80303580b084400440d8080e1070105e043d01d12820303440c05180d004032005406542400303401401103c040e00004203010403d9103414221a20005444d868943c0941c046000343c0d6901c1c0c83e09200086d541c0251000078074518100400c0042035104468001d049001c44142c894501d008001840d140926044000000000030502900c00c2d01540080200c0e4400c2c3c0340e240c0002546030107103080340000c44010740861010454150011140d501c00c0304454818180c10381070084545a080488400342c02c1101c0340c3d250300c0320038800c03403130502401c4c0010040084103501e0b1641100e041a52441240c4409 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 3910736 1250 3909486 3909491
    0xc080703050c010f050a110c07030b0603030f040905060108070807020601050112020f03090102040e0c03010b030406050703020408030706060503010b0604080a06020912120702010e01030605030c01080a020d0c020a020f060703020709 101
    0x281094810350031646a096000001d01880c042c02d01c203480140400c0d11820b5505152904c500c3d44440c041e4241c03030750004a10050201c1a20715210f0300c03002007008010542c9030108200520310b002e03500d0060030290040c600300080914108002401c00900502150144500c0c0000c00194650000e03c0350f040d6182882c2600c40d1840445a041c06030003100c0d25011036080c04001c100b00620150701070030840b042001c610700161070f409510380080c80b080c001c15031005820400100400d415800503074000e0124600145087c3d542d000850443d00401d9085400c580c54203000c2020b031500f4010044d02800864125292601e00410305e41d07541d8071100000c0c10b070368001c1144840755580103805154100400c0688030a00d0503ca816031031544209412030100c5c5070052100321340d520030302c913074425a11702034000c0c102004018019035900c00001c1400b05516004c10036100c10600500034000740ca001500144181000c174410020181e1000c05000c1c05560203000a03c0440e074009208c0c01100c0c00203900 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 3911986 1250 3910736 3910747
    0x9180c030714130602060f0109060e070c02030309040f0902040e030a020316050a0209010605130e0103032106180603050105010b030906060d0c0306060605040501120605010206071803021806031c0c08 87
    0x1c1a855000f102c1c40c1850074540c007540003484d1500030544138031804006142041c00c0e80c82e03146000031a40180500c035189480d00740040c040341d014001c0401101e00040c1100c0c00c0085290014003501c1c40c9401c41c00f9180d4803080c0c00c0c411420a80540c0101603900c1010b10704020b01c3d0300780250707680160900c00c2c1c1d404042c41e0404c41448003c0c440c2c16440c64001d8a14003180d82c54542c0540a6070098125440d46a10340000117070384001c90f404241a258596031b4a4100207036101c640300400c521512840700160799010004e1a1810700001c06a00d810084003c203100d4a90b091190071940d0590101a400c42d0800c104029400b001c41c03c198410b40803611820a5480c50800300790800e40340e04000d088a10f0300e2004030700c10350044040d00c110741090747c0300c4c18040807100781070307060f10702030302c201400340e4401000b0a03111070145644200f01da60384480170007919560380004400d2103660303814608800e100313418000242402d0116110520f084541301d403880fa07100b10000c00783c8441d65009441480041007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 3913236 1250 3911986 3912017
    0x5100e0613030605060a06030603050d0305090316050706020c09010308090d030203040e0903040e0114030d1202130902120106050309030304020d060b06181c08040504020306220209180c0307 83
    0x159554403141c5110000000d480340390403402001c00303485071841111010800501c10b13100303010b60000c1d66403120242604903040a000d40281c00301402444035400709000f40b40031070300100099411030f40590f00800e4018640701002e8148460140c503203008000b005c0061002c030748944108e41c80d00a0179184806917402ca070030202c0c01d6014036005011740d0341a05081c40301c03004000000c2c0007a1240701138900c7c06642e03100c0040b650040e94003034140c3c05410120035024801e004400c031b0310b81080306007409860000f0f400082c400030f2005801c079181a42d80450007020035400d0300e407424050441030400604d1030030400310b044c0d560f0000800c001c0c410000441520b040120640050303030404070142440340c54002103120000348030b00c03503d0210300440d407882c041c205100300c1140e0310011580090781289402c1c10038084c0b0029600c014181500410807007900d421040b1008501c000c01580741c03900586481200d0f042210182104041c000d04581c3c2ca82400400b0840404070303130300b0200c01d040c01c803615501d016 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 3914486 1250 3913236 3913249
    0xa1403120301030606080d050901020c010309050106050303040e090106051207090209010203041d0405010b031c230f0a080c0a050a05070201110313030b09010509060105220c030b130605100e 83
    0x500e030414200800004100040d640062050703d4000040e190a10100542241d86001d041c0009005034004242800c5550199028401d410300810002c42c166440c1c1d000300b480d50340240c2c4550300f281c80a2040106c0311400388240d06c05803204440011415000b0584190703200b50f50300070149519030002d0300000e160b000700b0445004107100ac081c40000c070328070b503020600c44000700e60940d106e5090449241c100c0ca4007040385140d280107200f0b100c0020701400d10840d0f0b9240034542c1120555240b0344c402c0c1c9400800d5001d0005204c48520707469036154200001418030310701a0480080340418021401155081382c1a207040c1d480c03901d0a45d44400701400100d40c40300c4084490b414900000510f59261040c0d41e0b030400035a40107030540c5100c0c1e120710b0300590885c2c10031140c0044c5a081580144080d2410200c0f0030010b152031036140300c00701b0280300340b103040b20390800c0401c012070795503000316140b404c0000e0941c440300440501080b090303280a020032880006e0400660400c0701d800c044007100d03a40d07030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 3915736 1250 3914486 3914503
    0xb0a0b040603030504031a010e16020a060504080403021203030108030d0509011808090103061a0901050702060d0c02060708090d020d080901090602070503030708011211010c0c050904150c0207050a1403 88
    0xc00034403680341d40b0700b00905207911034007042c0d6030b1170140400c5942180c1d103259010704841d5000300c0c400060750344c00e1080c00302c80d20b144070060441c0076020a000105185004e000d0203140540c9205544515610403c0040e1803000044280d0b03030418401008614001300c00c2d034911903151000400c0c5980e035000179900400d60784220740f0380400101c0c040801d01130b800015144e41482030300c0801440d42c607110740c0024002c8400038030b51305003001c100700340c8254030034800f0345044c510182c03801c0c0c106004c01031000300340c9140f00700001c0164060001c010041e03a0080000d504400f108014050009410744029150030b041d00030501401084008140484000d520610206400490464030b9400b186003182d143d40c41030380c2e1900040c41c080000309042ca41c1e40d4005032099131201d0f14110904e1031200545174641e401e10251507401140b8000036860b02d680710464410740c80742d02d9030304010b984003a40e44122101114980215803025070180260785541c440c840070340f14082507003020400b00b040081c0c50661034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 3916986 1250 3915736 3915739
    0xc0803040c0e1e09010207020f1201061809060f0903020a020103050621070f0906050307030b040602070f0803040203010f1512050304081c0306060509010503010b090406030602030c07031107080304030b0a0b 90
    0x380000c00c9022505000c442ca910b04595101000f00d44031211450300743d0040501c0a98008040d05244201d8901054403c60054608001040484e80c644070100c14000248943d030000b61510002e03800c03c07402d8030841c040410882020004c940294400070b46c4d810404500a06059a8030003041082d903402400c40d503070020390309510201d09004c0c0102520742034284210071203111441008031343c1c00014001c000503140040e004000b1070745584c03110410f030440604150303100782c0e0800140b00480c00300c0a800000030300414200390341e030070144141400c643d800b0000e40d481038030b842100246002c0b0044254100c0c4c1e81004501e2800c0c200e42406d508500c9507501105c6544607a0000013825840c0240101c102d2409440c10410320381d45040c103407101e100d00201ca03400101f00300014800c0c0100c941c040c01d0b085030701400000d540c03078617551041c0c100d83c0180c54600b05510301003021010943e00184e4bd40c44102c884000d03250442c44c0c0200181d9a01450100801090301c25001942240709688408c000240 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 3918236 1250 3916986 3917009
    0x40501060504150602070b03010501051c0207050304090b2107170f030d050f010b03010609091d070b0d060b120103020402030414012c0d0807031a030106030803060906030604030c0803040c 82
    0x1002480c41040540c44c2c85800e015000307185000907043c0401c41a00c2c100c8606859051600340c00e1100c407400055010003000000340c0c2880441c1c04120200045c0000d018400c400083c2440340208000d0782c05952444072024592401d880e030101e010104082c0308940010240d03441a00b80303c40d0242c10b02c2c580100300c01035440007048400c80c02500d034005c24054203001b0320a081598030b84005648509c000d01440303004c01d41c40c141c200400807540c0d012000815038036100c000308074000c9042c1410064140e0240d009201e001c280845c14092a2040c80b0040c07241d400f0f034600c1c0c070000345801c46c500c00051101034800d0f5800b00006080c400c8080d600c0928400c002c0003048002c11960300159100e44401042400403c0480e403070001e0f460010b00e40d1a182044c1d1220559a0340d101412030190840d0040c1d400c80021459800000b46c40074012000038510a54440b6102d25261003031049040005040307600c241e02007818840426004000000030710b800107416503072070340d0f6402c082880e000e856000103171428 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 3919486 1250 3918236 3918251
    0x3010902090a0903080c03070203030615040510080105010201060501020106080601120c050603010b04060206070c110d020307090608010b100212030417040b0d0e0c0102060106020705090a180f0605060109030f0605040501060504 99
    0x4003030350043c4180c41c07003510340103403684564824039400e000441e03042001d6070041021580c60700e880c0000703017042c0c80704100c4070b464140c8030f0021450b80c6d200010000041229840144855a02070052401800080c80204001441d110f041c41d60ba50040c1704014242c801d18000c0014010700c0c07800b05014140140017140d0320350391200100042d070700604c540748c0180038a40c08102071512400d2003040c03c5030481d54148840080c0403c00039192010042203034944100000041d070008503010340d40c001c001d00302c0000b5582405c0c02c24480c5a5201c801da02c0f0440d0008040c80542182d001c1c00d82c1e81040d0026410864103c5018041c0c501d442250080c080c01040880e100f006c10105403c03041103a0001780a80f169200c0c1600103a03510350080c02040096000700409005600301085482d130310503000d91011880014074800c1026070170618400f41c610200c10b021400174418907008040e000103007860a11076591654840c54500c000701d40d0010017040d00c500100303003445003d4105c0d00207000001c00800561 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 3920736 1250 3919486 3919501
    0x7171306020304140103021822051302130204030b0106080903091804020f030a02030309040209010c060515010801060e0904020d060912050408070f03050309010302030417030c040614030403020a030e0301090209 92
    0x1d030020720130140d2aa0402c20702400a5100b4020380c4d041640c1029200110783d10301e000c00141c101100e03c0704482c581e80d0242e02455083d0360151901481d60f040c0018101600c50061100c00200d4880301240303140100410030000700b100d41441e0454445292551142d107031300520600314410440e0413584800f621210070200c0c2c01510b17220f8000c51084840886480034481456104d440090020358075800a021070541410142c0003000c4568051402c000d032404107907a1607040310000d40e15081004420740f0601c91550b00000258054461400e252908401d44c900040b6640c06c0280020301401c00340c0b440c0c0c4201300c807640100e225154060349800d4042c6042c800205240c20912a2070045e00c11081c0c0001d01d50b00480328001980d0b00f1401a52812180c01c0041d400f0f07610141c01102d91101002e03007100042d240324003031409544002d4405036560325060000f054079885c00b0322540640010001d0000290300040d2024a0341e5060501c2c540030176601d800640108040580a50007846030030802c00030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 3921986 1250 3920736 3920743
    0x203030a0605040b030a060209040e030d0b0414010f03030e061215040b0409020117130f03050a021506011e0504080106030609020910050a0b071104020a0503040203070510050717130602 81
    0x140d000d4041040242c0d0740d8810003081d40d034200d15075070b090381090b504000450116001000e2a401c050404580701c010307480c1d8549564045100c140450390307501c030040302030700e0b15000344070b00c1c0c45089001c14225410044051a14400c5100c01030911442201c042116100c40054035054020076404d00c026103400340219107284104d0710071512861420025068070301d41441440d054a070180e680200020b4030a151080e0050f024040400354140c004052001614a102c851b09103446599426220f0a000001a140025400c210b01d5402c142d14200111642d200360180c6003210903501000d005801c100050f030f1148580e0700030840315404c0900100903c0310030341080150510a848000752540c800044004200150140720790200c4101010820f0b20616000342c0607142c010403400600f0601d1000042c12079001b032401c00003040c0701104101c00e5280c140700b010f0042809807403d030348580a0380e2000781319204820004203500b40500b030454691350800b05458180210700300c1182000d07115a8069035 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 3923236 1250 3921986 3921991
    0x50d0908030108010e0f0708071e050303030c120108060103030e040b01120e0c130608030306060d110307080103060b01080103050c060a0c020a030507031205040b070210020309090c0a0906020f07050907020f010903020303 96
    0x17a280305d0307080e620080010010782c820450b442c08014000244c01c05500000c40c0c5120f483d0302000c4006c903030f130210342561309000941c080c0400e0340d10a982d650b001c168101c0c400d1416480441c1d01d4200200410120781c100030880f4000208490025203107841038010784408109009044150389081010307100103c00041114030050219a0101c1904d02440e01d10f00340c41c0c61340544142a00b060011421508226010341b40300d03000380c0c2d0017044200b656450410740782c0084511000180c0244010824083c1c140305280580c4401c1c41c001d41c8560568070f5017581c071a8414003850040d031b0006040460b45105102912017607034024112980c1c540e403400c005984035920b0005848403080000030450540c00303071341281d080300c2801070054240b1041340c00300880300d4400001d4500b5070004102616541d075800d43c030b03584918210501251613414140000f480340015811500030b540c004801c103261481c2c0040c883c001c452041710ba50405540f401c0e41241400da000b00506410b42c2000824000c06402102239032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 3924486 1250 3923236 3923261
    0x5090112020301030f021c0501020d02070201030e030a0801050603090c0901030501020702040c0903030c06020304170307020d020c010512010504050c0712030608060601080105100e06160303150605030115050d090803010801 97
    0x5041103003103000001c0b44000e103c01014851080c401c10014280804030050403180c60110200561258503243c0c00d82e80210401092554005041401c40d0f0b01441580c00f102050310040d42455000b0b00c01404182d018010144030301c0d000f20000380c4030142007203034401e00200503040c5031982d650781c035015020790001c5100b00c2c03065040402c500b11a5100d85035070380480b07405540301440c030039a54030390f500254800351040c0c4540c2006070131150b8840100d401140642c21682c0101f04003640048001d0602c400041c0782810428100f100c92004041911a00d05542e0111800a103a0704c6501c6407166502c902c90005016940d101103203c1d1036a0940d00c50740440300b82509880c100c2e6500401110190f009015880d070200a140004d28020b2081540c0000071802800031071400f526490242142c05441d0012000261510285008141c8010704e0000509450600c14203550400d50445240251143c0e024204a40803d115580d2007007a040440b01a400144240e525612045007501a100c2c0301e0300700 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 3925736 1250 3924486 3924497
    0xf0501050609030d0f03090b040f02041a030c13090606030818010302090108040f050a08030a0905070902090d0305071b030803010e090604050304060c03050409020d05010f060e10030906150303050901 87
    0x30311818190100c640985004001d001681140f0409a8144c182c145d0064105541c03071002c2030009922680140c00345002e800070031410801e030300c100004e036400002d49a980142c044064861510300084005078580c0c2180e0801c60540700c40c610500034580340c1c001500860070450000b042c400100010408990131810f151040000f0300010f40580c860009540d00080e50000040c01040c407021040b440148190709460450703491381c542101940064488410007541c44001e4420000100440c000404104d0303015410500000000703044607105e02806014003400140b080304126103002449040620300c0c803103808868036420a5041600309001d8051000003c6001c2810311200149003489158848006e40c5002d00b45807080742c0803d00d000e4103d00f803020074000446c0c61011800074000b00c0b07000d030000140e40e61500c0010700498800c0c1c2d00031002e0003009039884002e5210a41c2000f030b076007221f00b00400c16440a00d80300b801400e42c0b45a40160b445102d20203c2056072140c01071100c00002d80c1c54 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 3926986 1250 3925736 3925739
    0x6050903190201080408030405010b0a0b1309060b030105061c0501030501091104090213020904020d050421050309060703150801020705100c050408060402150c030c06040201090b0c030a1101060b0c010f0501 90
    0x905514103400741c080c0c04180010005030003d0340200041d40e012348581e001003404815000400d0308440c2c5900724550001001c20845500031401e52100001c00c3d01100078000c151810105da40b552106000c2d203401401c2c0041c80c3c00032221400c2d002107040c400500100000d603900c1c01c00343e0023402010401c50342c18a0b080b2030b001d410720300341c0103641400745c00424103440f0656400d0808000c1d480718603c242c01640920010360114540d105813880345008042d00c0101408142030f0301d00104619016100b404000d0040c04041080052803540c0301074a03090000d4400e003410815014202290b000000660000514008000005c1044040c41c6980c01c424802c0c001d08540c252445d00490289056942c0048005030141c50000000d02d403400040501c6031070000000301c01c5080d64040380d40e101c8580c0c0048188011035911040001c000d00001c00748606280d04004200c0c2c45c1d02c903010816040107001602904442029030003c00100400071203c0d03610004103440c01c2c040c06068030038402e03841ca0b0500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 3928236 1250 3926986 3927013
    0x506010609140d0201030e0706030b0a05060403080d02030901060506070305130501021b04050606070204050c0a1205040f02040b031606020706090510020607050f04030b0106031a011d0105070201050705030406050903 94
    0x60100035600c82403403400c5401903842c14015040c8100340d0036410191038001d81c0f054200f083c0300390f10207090150340125062003400300f400091a40c581c0400d000d0340c0104400c00200700443c007910104c0314451000b590341c1d20b03190000390140410b6040940c0c46000083c00f4410990004001d140c0543c900d41303480c20003569500107984420460141d084030030041003411001e0f20b02a4400d5501a00013040b281c1412aa500403034211a4100d400485001d40050742c8001650007228071815141802014009450140e45916128143d03c5009002e941c80300703c84100ca070307801e024400c1c082041e10601c165240e5600760003981c03800a0720404001c01c0010710f0100b01d07401c002201c041c40c40c0e103d4000704400e443d82c0350200d4860b8401100e055038200c06000c0400080d444812403802805644d0380480c14002c070043d414003480003114800d0522400410b054041d0074040d8001c02e5154007420400c0c0c680101e4001a6140d02c600c4400034817501000402080701034100d005021120016022241683c00b001d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 3929486 1250 3928236 3928247
    0x3050603010b01080610051306030c020601090b01090e0402040905060f0106091205030a0503070903060c0309200306040303020c0f07030606030b06010206070801150c1e0311010209060904050403031503050a05060106 94
    0x18800f80050080000549141041c44007020340401034a40549441c00781441c500f070303425854003c0d00006c0d84801c40c03c5200c950400829000d064404401c00544c541d050020746500c0c0346220366140c10842074005020341d0340301ea201c00c8220f60410103a40403450a000f458003010f8003402500082250f6960218040402501201c802d6500c00000c502d001194801958541c0005190b10208030303091002000140f2240150200d081c00c80d200800c49a07860315080e011038803d20903224403519030006610059030000380c2c2641040d014203005965100030b48030541400d102100b81c440910a0b008000700b0014554400401c590141201d04901c1d00c0d400300490301c803441600e00c400003d22030720040c020301075040302250310b000e07190500d5000715281c0d507a4000c0e0041c902c01500c2c0c4035019040420181504041d100906201d4640214900180040001c02c40e005880c3c1040c0519981d60010381094000d81c400425040d41e2402c80e60744603501d01d001c1c1d9503800004070840b92070142100000b149809807 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 3930736 1250 3929486 3929501
    0x10020109030503060d0609080c0102030406050105090601050a03050702010b18010801050c0304020105070b06010e040606031a270c070b0c0406030c0203130b070501110c0a02010306050604060206070c060608060c0304030305060301 100
    0x5070b40d40c82c80d5449030410041c42c2c0d05a042c00f91034955032403606030005189580104103c1602200242c1c40b440e29062110884005910450103007416404011650380d00c241268268022410001400d440d03040d000ca00403c02c04001da608100302c8100d03100e4030402125624121100c03607000b0302407543c41a58140c1c20740002d031002400708405200c9880080c04906502d60300100600d000c241780b010040010b000d0340e5007a4032800c0465600e501458082140c0c000c2e141d80050207a40b01c0e40a83c04100744c81506210003114013400c000e100001c41c202034aa40200c40c2a03d0b0021201c41107030915491011855005110324804203241c0421408003a001200f41c1d4083c0c9203040110000c01e151a00340040341d401007004855555842c0e4000c00000b0210002d0300c554030075080280040ca01c0d81c8005411991541c0141d4400c40007031104008899001828070340c089003600c0c0c00020484640f8000014010b1a003051b0102d000c0c14040100040845000e10304c110b0283c0e6060000d07495130b00500d422580398 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 3931986 1250 3930736 3930743
    0x70909030e0d0503120f07080702060106020d0509040e030a030605190b07030309020112060303091403030403050304090c0c0506010603051b09210312010b0d0608190210090e07080610020109 83
    0x1c031829410a450034140034040740703000d002a03d16021084c100345081c264101d036001101c0700341d8001d0107150380e800070340d06e9400800e41c0010407155050200c06035803000c90b1142c100411000041d50722094450341c000c00c04150700c42c0101d85e25038030721050142c0584414000c0b01d0003000600a108170400a44406000f110300d18580e040ca0700c081c0b510110080c2c44114030503814000050890380c1e1914241c881c80d0003d40c000c2d9500e40143d8100030200412031450101a880781d40240014070204001204583c201d5100303c0000403005000e0406440b40148420082c080380181c0000003400740d01a00b08511031030310a0345d5280001011106514940501d078819a003240210040c05031054640d0140500d0300d162108807400c00c20036142c5c10b402c0d03450980003001c04100100b03400b500500b847c02101c0c09404841c0103001030f80000e0a000e15011040c034000b038440d1004404482c801e50044514401038031055001c0c0b00c03246041ea002500101040e13401c2c0c0d000340b589400d1842200d03c107105501030280d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 3933236 1250 3931986 3931997
    0xc04060c0303090201170406060509090109080d090c03020303030703020a0e041107060902040b03010903020309040b010503041a040f0b090a050d110706050f13030b15010e010e06070309050a0b07020307090903 91
    0x34a85088004251009040b07040c070031030f4019a48600c45901c2c2d442d02c0ba40c0b003290301140e918100414020300043c09800200c4c1c90b81031a004500143d8404c043c1c0390f100c1e1044070002458541d9040070407a0310388980c4007035010302000050010880d4190003d01c0f5191903522802d100102071014001181c2c2c80341c2040d005c003d0305000c00e00c00514107420a20242d80021300205503d003035400000d084801c1c62204601503480040c2d0400203003001e00401c00700040c00d00f441801c602d00f1307480f40b02040c40401d010600d410025400034003000200e4450052080d0451219407241c035151203030b581d0300d60030410b01707131010700c9005421420240324101c03881d108565076016018107454200c1c02c0c0c175180c0200945140705041400540ca100e150010b614000398002c0814a40c80c4c14140c0d8150000310061861a0402244aa190101e640c0100702c0d000341300f0040c0e42403641c0d06d07182c1c00c6c11113106900d1f804c1980d018001c2240064501070040c060007015008809444140c0d42e210481012504241c00c000c01149 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 3934486 1250 3933236 3933257
    0x7031707020604030803090109061802010206060f0a0b031b030711160305030f0c0a0204020a020105010f0b0307080601080910050403110142030503040605040f080105060f041a060c03120c0406 84
    0x101d000e0090340c7c0006240c0d0000c1846095070751030100392131203414900240c008184081003035603810000c00381c011600f541c20940c029898400305a5042c0680551456008000701040c0b42c2c02000100061082d80380101c5601ea00705203c0c01000c0484619188040b44114a024900b900c0c0202d90b000c201c991190046140080c9045132000d65080212a81c04034000c2014110150f02d0310f00040100303001590002886604041491403e02c81d01e400c8112441030030b00400c4200d41e000b4505d039030051404d003040004d0740e550080b20b5240c440010040350600741401d081c0001c058220004410390342e9036000901c0110400001c4040b071882201e01d69840040d001c0e90804040000742c061841c501c100c10196003080c0d143e07180c052540d84164001f02c00104005400c004e05030380b9250305030180040c2c0c40203000c3c174202240000d000c140340c81c0c5201e00c6641d4a0045950350310404607680d0000c200940029140c940060031541c99422028010800401c04070004541a058008543c246d406c55140c1d103a440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 3935736 1250 3934486 3934493
    0x90103110a08100b01090b07050c09060402090409050a03030b030a0f0b07030207081306020c0904110108061f02060405010606020a150c0203090d050f1005010605180f0405090703170702060403 84
    0xc810210650449031501c40455041414403124079518040e0f10b0125120780543c000520f050182d5106100b42541440b242c07000940c08140c18088550407189900207450714800078009100d035031841940585041915401c001020506103181c5001e07840c20003c00d80d007482455143d03544424010502c42c4441114000680306000c0e0703e030001d58a01e0018280069687c40340a01d6201145000c1072a03501081040140d50410205203c20b6003950440c40d14145583d07001d400e4800d0740780003814002e032480040c6040c5c9801d5480c507030346032411100c1c4014000c20030029448031070940341900c86509010011030041c0c000140c01080340c1d40541c030f104010140d81082001001071080b81411800b08100103166641da0036101d0700f000f03003e60040d100070300c0065600d6150800da90a40d1015a0902004100c41500001035071380b456006050746560130403c200045580c5a040c006540c49807414040c4115a40c000500d001901e01c02d00c4189629124152101d202d030040d010f00070742c003038010041031000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 3936986 1250 3935736 3935753
    0x203060a0b0c03130303020708070f03030806040b12010216140105040c030201051b070e090d2a0c080303040b0f010602030f0307030b010309051e0c040203010513020f0f04090b010801050609090103 86
    0x400160009032420805100d01c0e69004403105e038019001603110b00e00074044c0c440103000950040946a080350516450760764044c0c180790005248501c22a03541c08540c1207030303e808000514000480d4021507460482e900c0856018000000a407405408014202d411580501c85c05000d60341003071403004114038507801150107a00220104400d0704e542285148120390400a03403010b058401c400c1c2ca07052609000c600e00c0c09440b16614010043c051000c039540154082200c1d260075902811036808030f456040094949903140d010060030302c0000300300820b100c44a181c3e24011a1080540d0180b66038800c400c980e24020103480c0038003001e0070004691306034040e502101d1141010b04020a8201d401d440e22400c00720020b4100f81984907640c080c0c0c2d24000180140d0a03150b4080340c046085505110218103803c1541101d80001076000401100780000c14040d20b2a2441403184c142d035550b01c1d8607240024140c1e003590503001c10207400c00810246070520950308096030140c07260b640c50303185403101c100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 3938236 1250 3936986 3936997
    0x4090b0408031b0f07060b010509010c030e12060f01030c080d080609060f030102030702010f06060306030f060507110303010b0c0601060302041d06010e03030a0809060108030304020a0e070302040506040e0402010906030203060a0b 100
    0x3803412240302102c50f20b8505014110040640036005e0300c5402d1030a225050320185050141044001c12035500d550380c00c12000c2d03103140d416141c4800784211407000309048400c4406820b07800d20030390082081c0a6080203260b4180c030b10480c0f03002c0006544421840d920051040d400c40411080b00018406090004113542d0044005120108441c102c2c40405c1c2243d1080c0d95180060351108040f1070010000d0040c1390043c90381c2d00e02001610700d15180c480c0d140c4500300004060f03075165404900a039102c1e24541500c41c01d000e06a070741c1d81d41e440c56100d6417a400009807003410b02030980000b4070107000e44240d40c02c54000410340d410350075500701c0b9a1060f4000030142030521920440600d02c90314100003410070103400b5100d0b035145082040206251100503848500710360b008000b0000140c584a58a608842c5400188201ba45501d01d0941c0a40119004140c0104000c0740024501c0118444a0b0086000303880c0c2c800780d2034413040c0440503403100312a042c0d000401407500300320ba040c080d0300401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 3939486 1250 3938236 3938251
    0x1090b010c02060705061503030306061e040509070903060510270608061009050f0106020a031d06030f0103060e060403050415020703020a030516090203040c06030b01051605010507030b04090b040803 87
    0x300d10035410b82c002259600000401c1c0e45030ba012108110240c01d0100d010703001d29100f00c0042d815480c0010000f1818490b04891000360068602d18100c00406803060740c02034000108540030328074201000170001c1200744000d60307009080c0f1012070500b600031000b10050303e181c06001003140790128070000403051100c08090f000366071024001000601841094040c0f8210802428040d1400b0140c10a07268081c00a0440078840801000900d0300040d0101d50181d05090001d01c40050140154050310310110243d0822000420004815154542241a40d204102c01c10030014a298071540e503401c1101e001300420000c200a10107100030b0303255450000c035244100e400c89900c0350301107085440310307074400c0765075900003ca121710f40c2c0703610320131030020b402e810a00f1802c529168a90910550b001d2180c071080c19503940c0000c80f180d00c964201c0d1000644030f515110208038030701d40fa50091604940d0030300080e00d84104441540341c03600036210140d800882802c3e01c2c1d2181d803107850741580050a850b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 3940736 1250 3939486 3939497
    0x30807080d0c02010606020d030b0604050108040f05030406020d030606080708040201081005030106080102070201080702030f0306060a030209040e0f060606040f030b0601050418050105090a02030103020d0b0414010f0b0f0a0e01090b01 102
    0x7840400c91600815600c04615800464424a4044040e01e071055800b40c18007810b044c0401c1d025035850b80003d541c1200d00928041483d6181c0381018403c4003080a4040c2c80c0717020004010840c190006a00354030503510350742c00c00155030381e05000c8464180542e07807140010110004035003d50701c2000a250032900b241d500ca08010307542d000103801c65030268801c2c4208c1c0d4005c52000159030300004c0c9280e0124a60000c0c40c0792440b10080311110b03200c0140194401c104c085015820a8440e81c1075036407201c006413041256aa4011119076940700d58440103102d84500c0d40060302604003d000d480c11644507100103026282195500300800b100180302138104041840002903080a0010401518140e080300080070f5040c0350612506540003840343e80268010001000143c49404811a409030041c40082140c0c5541c0382502c00721140b0b40580399150308002511005d0081039104a0740800202d410781c007044c485405002515950344034403903408500740f004114222107904810000350051409 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 3941986 1250 3940736 3940747
    0x70309081303030c05100219030e011e0b040b0109080a02091e070f11010b01050d0f06030215090319050c0d0c0b0a03020408010c02070506030c09010c020301141902070b0103080708 79
    0x1600707601d100340e1040d4009003169010206010081c02000350807070b5a184254500001101d080595440e04104841010f80d10498846000000c4d07101c3c580703410704200005200301e950703035042001d402a17010300d6101d0391622405820560060450800310b0f0100c5000d4104000240c08004d883d000c01410070308104c10315800f2b412070f03510120388a0311500ca1034546203000600c0140c01411b110400500c500140c1c54114011466a001000d60304c0f6070785800303c046080303080303c250f0001805040c2d0000f500a4000c1540b0300f1010070b0f8030054119402d0035401c880390030a505012165903410183c01805582028442100c2414032007030700c00a490088600541240c1c0c0c40707580c03008a60100d2080340001c0e03030108050121100078050003a007a140b40c801040941e003044001602d511000d40030748070300ca9002a245400d039016107024446503800070001c101c401042e080d03048885070200c03401c54141c203491001500d010071a1080d40c0395550010500e4045d0b0b030a550f1080803c0d407012509a618003010703c03a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 3943236 1250 3941986 3942007
    0x60309080405031002070308090705030303010306020d14010609060f03050402060909101d04020108060603160807020c1302030108010c0903050705011b02030102070302070302090a0207030e0907050424080c040b0307030908 97
    0x551a142d14500700040e070350340c3c060500a20040003e00927240a421401c4108030329900001503e06603500f15900607580c40041d031301400181161000c0c0300b58207020400018005400180c16807c40744c0a448401c20076640003802c40441c3c0045a0003907014000740308100040c10408039003a80b100360008421801c64480707004410245000b4203005254050208100c2156489085590032400550b0824154280040140d21501051101a040101200c0050a002d1007080403032200c900140c03200944d0040d000c50400070354001d0043c00b810750300708010201d05c507224100070300450b82c00c40f000d02030103414030004440d12000c3c0e2008800300882c0150007005a034082c070041101c18401e030020000c0030b10790710622440100040a003807480f071040c400200030941140034038504040440d150394407551400d106072140c2c051500301f29210707900c1c1c55605403140d915801442504501b80c549128075920340e00e10b441e2511a501521282e0345090002c280440e010741c0000c184244174071300e42402c00c01e030b07d030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 3944486 1250 3943236 3943243
    0x20303070b06040609020405010806040b0a1a030109060f030510050c21040b0105030d0509010305130501060305070f0b040303120207060905010507020102070b10060206010303120f0c090302010f1806030908040503 93
    0x3405a4039a44140244141880d05100d1800102a0380f0019420680b41c04006814020020b04480c041d54644003982555500c85800074003030001823208030001050000303c1c141d507030424014100018a03098010488148007042c074000c4a6219005060703907103a44186031701800c80a010b900e803c2e50107102074140d01e2803c8400013000f5400d03c1721401a86810306045030000011792016010360881944007500d00e070f00c801110b514000a080200380740e00c2d404030103401c0c0c1042110152242d4a007003404001c115000c660034040300c0400900c0d40b402501c4440c07446143c4203d208c01804200302445020044030700d038014101c114003d090024000f400c680b54182515011580d100040c0d50001c0e100381005a401d102e06e4202d51f1108540104a0500201075036640040c0005000d00406000420007914550001c85200c1040c1c3c0090003090031002010301801190b001c100d0100b00b0041d0000101481000c015044c1d801e02141c2c1d41010703180040640c000d00c841581510503100c100000304840e103040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 3945736 1250 3944486 3944497
    0x20f151315020d020c010c03050106080c281e05040b070b0c0702040603050601061b0f14030f0406030b0109060807020706110a0605010e0402040b0603040308010b13090e0601150302090102060c09010c020303 90
    0x442c005680c1341c40c5d2401d07050854158080b680c1c14545020014040d6943c00310b00315903c12110600e0f181e54201280c52803140055191140c50900410160384015607407251508007608031100417001c0f03821501200361064041c5000d0710294807000e02c40304001c10041122030760030401074a8807520303240240d00480c0c1501d800d80c000b6103d17940004010840c1540c02503400104903840320b01c00911241907520030005688401e40940443c4a81c6a20320684006204882501c9400180d41e0740d1140d4414000c0d002e0562210400d02046a244000034410701400f555071241006501038840141010010388003110054252901c5114003030080000400610406028040b108007a1078030b40350510401c002da038840741d2810700860b4180140400203030844202410344090b03a101c00e807540b482c0740718464000e0713140d44101221800c100d50a4000341c0c0116641d41070f107283d11029200c0d600d0980b0150240c4c82282400c9005900c4000050b400d80e031998090700c40010145000c002c68109a000a4a150000f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 3946986 1250 3945736 3945757
    0x30a0201051501020a110d0503040e01030f0201080105010314040f1704090b040f0207020303040308090103090204020301140114040f05010503040203010e030a08010824060105160512070201020f15131502 89
    0x110000d02c50300c801c00207403100c50980244014404121541d9aa100791078070204014003e110740890201040008d10603034014203010000100d456a4a081c100c840301150201a40401d0660002003155442405500300851404140111340c0d02d5990f81c110004441c02c0040d60500b03002c015041003c4078040c000c2000f003021a0000c6502c1007254100800c440039280d80544407407040106a0040e2804001c1d201101d4000e0b031010340310049140143e02600c10420020343c40340c170000c004195522040f00c09151a0b1081c0e8680800360300703680364511144030394001c0702054401d05100b04415807142d0015648a88040d0002c201121081c000d00e242d5000314a0074400300d170403031f4014400c2040070007010503545070002c1c0002c00010304490600c409040649004c0c108040042c0d40000c0068012202c1085684942140c3c6000403c22500401c1d03005070504034014050311a0b041034010000401c003580c48070072907d031001ca44403440f80e40001c004000e0101d861880100c6c0880003130b00144050003c0c4c980 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 3948236 1250 3946986 3946991
    0x2030a02090312040305060106080a0e012a08040b0109090201030f050405010b01120603031b0f020a06020d030605040204080d030506030a0b0903031008010c08010501200313080d0206090606010806040e030a0201 92
    0xc00c607007003508000c000d11215140002c1404200007095000411504503142070400d0308054841c0211003000d8a03006841c41046d6081940000800903c00100218290101800d40400e05440030840780d90070f042d40c0151215822000620601c10944d0003400a144141000140900741401c2d40041c0c8000703c4094a0070b0359291300503005541c000e2500c40100500000c10004103013903035005801140ba07500717040d6425561034400d604120110740480e548a40003441c1000760381d42c2c2c14000396148124000a00003030b040213000980f5082c07a001380c0d41614a034101a100311a40914210000d202c010178003075062049020940c046111410154003c480706c3d4091aa2071034a984000a1071000d5440000c640e1301d4905041c0001c1d5010340080c1c1501c0003460300d0101c034041c80600d008801d1640b1034200b40c5000000b8082646c00049100360111180041564100d500303c4909036110030f42219040440c0c0c005c400000c02030742c803030202a03500030300080002654a2881c0c20b45450350b0480403245015030b6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 3949486 1250 3948236 3948247
    0x1305010e0709050306040b01090c050405030a060509010c030c020703080a051201060507020301050601050703021915020a02010b0307090204030b19060902040305030711030c03030409020304060e03070302101808030412030902030102030a02 104
    0x354428904400fa0805a009040500300359484500100c01481195003c42d0b8801849450520500803100200f10090844420305d000d400c00300c00810041e01c03c401302d0361034510844903560107070080580c0986640c002d048140e285850701419980300080150420800300603400c004602c1482980c040e1034903582d1203441d42041d20616007101c0000d8280ba0600106200240c00640d00003101c1038600d8082c3c00d4400061000e250010020900b400b41c0743e80385002040001801741d0541c02210400700403012210020380e181415000c034466408080c1500c5c1060700021908500a00d4401c40c00c5007266000170f0603036683c400d503030407a00140c000700c4007508001000070501816101e0003407001c0e411000381c4420824480066a81d100310f120b8060340607008400a0140801540015911170101d01500d0340c507100703403400035141c000500d89400f5081c03900741400044c0211502c6048000e910507407075407035500d41d51140420102190307480410142c54100a90040e10b0a0018600480f002c040c05621031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 3950736 1250 3949486 3949501
    0x100504030b0f0411010e010c02120f0c0402130510090302030a0c06030f0c020316030201020403020306010609030308011d0103021e04150807060302090f0d1e050604110603040c050f1305010e 83
    0x4500607080382c4078050795400f0710010640140184103d40c0c000d091410042d00c81d02c0043e903071500f1201019600400022900b0400b18000c83d181000d1a55282035030308200740d08081004078016801844c6442e891040d00340000c0c1410103400d0041003580c01e21701d030031507560f9001038901102e0301012540200d01200030800c4a80501896040058140c1c0501164501e00070080d602c0c0504000041c040f1100005141070600030350440d405950043d05540d40b41da183d900c00340010801d0b100c2100001c0c80300c000013400596601035135404a0700340f0403021540e4603680801c4134840900780d0008008010050bc02615615407090b0015a5030140301c0c3e41d101450800d000d070411009034070000a04d4010401120135586d180c4000c0c0303072040202d5200e200c2660700d0404aa00700507c1061000300d91124a2050500c040090b51603c103e124402108200704180300740a00307408260713002015141a054113111905d0020b4000b0510b240141015584801c00150036040e601d00f0391000b01c40100c0507040c00a075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 3951986 1250 3950736 3950753
    0x4020a120305090a06050a0c080a0306030b0f0702060709060906300c0e0102011104030b0a0908030103060506040c0c0206030a090501021306050403020405060301020304020d06180b1905010501080603031e070210050403 95
    0x701014242103061404016000e0300c608e090740001040d041c00003680b01e6a040c0a542f080b0080c1d0b8003d02c56410f5481c0c02404448000c100351060030240c82143d000809040c4204d11140994410b0340d20202c009190400983d0700842010076950700c581c3c0c003009034101c8464500005034030309a810003c5081c81000350043c11210511070340c00e0459041202030264130240904907403c903540410010f68030341d0b605080d40010081c40700020241381300007000005205081d04520b00400046400300f15400a05078261014200c0f04002908040240002076190046034042009140104005072130010300d2281c064045096400010101d003010400b402982018031030140d01c018150021442d5003455000200e04021040000308040e84031400b80e414182c07901c44e840e000e6548082514030905200f008582401d01c00c03422540e50526210001489601c140203940c002c0303001034087e5240090040e1290031a80040d602805161010050040161141071800d40311f40030315581c26442d142185003d500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 3953236 1250 3951986 3951989
    0x7050606010908160e060312070b0a1103010608070f0905121e1504020d15060e0108100908030606090409020607050f0f0102190302030601031d0c010905040912030504020a120305090a 80
    0xc2d0341c404115030304200e6403020104c05480141041060b16030b18030002a140c62003180c03e0440e440f2011500208001e501603005004111801c0c06000540c00ca80788a80140800d100d214005a816000706820a010715400254aa1186402d05110784c44001240c0103590640c01c0b0f514075403012120060501c1d280011040e06600781016020204107007107442d22020000e003010780308691120300041000103902502d0841d926003807081c001c1aa4803041507281400901c20511103000700011113595003007a01c00d041d10103510000e090f066031261403e22201c2e822040c0c905800c86c1da1001703503901590700c03c40070b0302d10140b1850080c10280031000b44103081c0351f121251001c00b41e005005419906a8044181c00840203e02d40180c490365008012000f400042d09007174803282100007007a212840c0400c0f0b19105503009e132510b0030442e40c0d0b1f2081c40221040d404001d0002c10000c41410000387c801d40040d9085400140320322011500c41d502644545028481200801d40020311208603082110282c0d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 3954486 1250 3953236 3953249
    0x60408090f0306040f03140c01050f0711010b0102060406050622020d0c0c12050304210201060f06020705060403060203060a05100801050a1401050a03051b0403080301050312161412070506060109 85
    0x614113055540042a07891349800a00f8818040050500c000c20001580c080e049a20024082424020260002c2d001c0c1036078408009031216a000403d410140950308000f04180c3c0102a540e889440300001040c000d0310f2158021a80000b0b0003c0140d1259050040a18080016926103286161f00c04540980103070740d05000405103000701280148000071102c26541c2003855507a51545400312884070440d911100c003032541c8070280700b90b03941544000c0543c2c20030b4000454981e11010305036910a050701c2501d5020320200030510008035903030007464000c0405450111060b48a400050000445603241000a00c124004002c0c0d858070440250003000350a540074403003020000000d20034400d0290240505840b03d02041508109018100c1881c0001e0512602c1d56128505103c140e03000303207d407600c030340b08404405250b04208030440310f580d41904039200a0380d0b45540c03801e040c1115021441128090038030349002400340d400007030601903c580080d2132645040c00014200300c03800d81186 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 3955736 1250 3954486 3954493
    0x30a03020304030609050304030b09030909100f0311060702040207081c06030201080601050c1c05070302010501080102040b04050d08070204020d0501230603060409050a021008010f06050711060703030e060408090f03 94
    0x11010a40120031181a6900b000010801c40790a0805606e035115a9000403e00ca050390100400381e01c0c0480500302c000d40444006050ba1140f0300501100c60040c080c4208268044108000041c0b90441c0500c4081d00600810308004203900003030201d81003a402074070300c9070b00007404981c00c045024004144019107c0200070050441d00003c280000082550b030500800164101d926003041041c11000304040140006d148006a002000e9801c103070030403005907007000300100d0070b0344060007510195070000c04104c0c103041c03030b00d400c01400310300003407044c0c0c0d013150f0070020b034009a201d60006000398a441040440c107549030000301c60002c200c1c400e01204489506c500794100340ea0344011260804012070b03010030304e02c845003001810301c03c410341d00035840092840600049600550350078100d0b59000f2816102555a103c15192845460f100901104111203049040c3c0752401c060a007a070700a14000990340030500849191441c159825500349c40c01003600f200502d03050311000d540d4101503001d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 3956842 1106 3955736 3955753
    0x80c120702030c010e0a020f04021c0203040602041a03060a0311040f090c050918030a080705040503010e0601080c040603050c090a0b09070e0307050a0b0910091205070e0603 76
    0x515403c0d50819029240300e070700104501c074106401800103115210300e13000f004001e41c0050464140c02c400b0054026440176948013440c0f085120b910010794550505012207400b840d0400c419984240800403c0916190407400d5421268814a040003986507200010040c004050541034828980650380702400389142020045032001d031148600d07034032903214003a01481080b40004130756000b001044180d038491040117501840c0352500398105526040040e007903407910f1006452a0b4000d8006001c019001c0c0038030400b100c03044a081015070f196a550903101c4594101c40b81c8103544130000034140034181d1300488041c60004240080c41d00d80708002130504011441114005c1c8036208000c6180d046c2112240262888155a642800c540307404001c003140c058584001040040e5400061040403d0707caa00040d02c41c0029240c02c9003003142c0c60388003110007440d852080e80f05440 = true := by decide +kernel

theorem cover : BRFrame.Cov 3776986 3956842 := by
  have h0 := BRFrame.cov_init 3776986
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3776986 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 3776986 ≤ n) (h2 : n < 3956842) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
