-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2230
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:04:05.291755+00:00
-- url     : https://prove2.me/submissions/7c5320a2-8443-41d1-91dc-ccc01c0f75e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 400899280 ≤ n < 401079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 400900530 1250 400899280 400899311
    0x9031e031103070f120501060c1a010b0706020703030b030604050f070e010b030619030b0a02090907020c013207080d0e060903070816140606030c0d030e100203040806070e010f14070321 81
    0x8814068807071900c00d284000e0052b07101150b1605841c0d082e00b01c5070500c895551144041e40042c80d0413014103441c1c2226a20548081007102d10540c0624000d1001c4400180141e00f440c00940100300110b103100010303c051103140044980100040d40ca1000001600e940981c15040541004000c0350035035052001c640203d8010b800e40f805c04507031507144d64990f8241642d41312400b010850220b407081515490010140184105100f1b1032000500342c1034021010028691040d002260342043c041100c1d51807090700d11601105650780310085c03103142400c01c015503a80c06a680003c280500018034810840d071107031414400c21390b000030002d0200d1202c004050321100c0840f4918003c0c402d1840c090b01c80d10346a50801500c60f0152518401b0500c40750074440a400d0580120044d48010000041c1d035120070132002c0c0c424921a500d5018414140c07000501c04440c50001a0810681e68028510b52222034111003045a0505000c00c1103500803400581c10607103001b8082c1e0151800c009502d61700003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 400901780 1250 400900530 400900547
    0x60503060a090209100e040f0204091d06060102070e0403020c1e040b030c0a090e0109020d0807030305060a06050406210608010605030c15070b0c07020409031e031103070f12050106 79
    0x800c88848120039141c042d030000700e00444042a5000f2044a60f0b640c0045c001c490f00c4040c8030000d032021605010802d074502c240c4e0f00c04e03886194000d50381c060054900d41c000050400100c90070018041900342800000e540c4d14050280c10b455403442c03070210301094000c000c00c4040720000ba0075081100003c016918004202496980c0180e052156101152501050045584070002c012885441c00c100e03c0c240141003150327400701c43e50b46e81c810a00160751582d0169400c58441d0240555480c0740d0720b802001c0d2000030705564054184140d0500407140c1000548064070071504d84540d209800c20b400c3c003a20001c1c0020003d04524107240030400c031206401c0740b01680e40503000c40e51140b20303000c00d004070f4008000840a07800020302c0404d0010300408115038200300101300307850405500d0b0700094202d0342d901c441203010585080642e5045503203c5081c2e1400d1f0401d01f403c100d00010043c0c0b80c030013840020401000c01081c0351200d1003a81c003480c2414078804481030208a15a10361070003801145 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 400903030 1250 400901780 400901791
    0xf010918061a0301081b01051c11030a091506060807030f20041a2a07090219170405060612070806010b0a0206011a0a050304030c020d0c060806061614010e07060503 72
    0x141e24160503020444100303092a80010394426240411603950b003009e0041078038400e001d468446070341d490030490b0b40000d10302480b2107000c000b60300320092500e4083c110240404e02d80f401e0629800f0030189803c546a0b540c40811800c01042c02d0040f40002c400402900e4035903020b4103c40c2e4a41c48840c08180051b10903505004034840d4141510f018003003003030082141610704949100ca02c03503c0700c0d0740504543c0702c0441c0c20b421603802548400810b41640c01894400720381145542031501110760082d040c1d85040c3d4403204c08011130030242c80d4142c035079a00901890140c0c00c271007610f007845842000b01d00010042482030f075100356120070460302d555000d99602c01c01441650000b00301112000c003103038542c40913140c00610b02101400291400c4d040100190705105036881d0413800b41c0c8900003400700062242014841207070030054060701041c1c0291035540141401d20204125190003a01c0d8100590080950601e0ba400c0843c4d407409410800c1303101d502801441d000040d102d4000c0003460040c0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 400904280 1250 400903030 400903033
    0x70f1b08030f07020105071d100512090f10140f060109090e03030a0b010503070518030102070c0303030b0a170a1104090203030403122303060603190203160306050f010918061a030108 80
    0x9841d1450210b40b00d010984110099002340031281c2c009140515070700d144c0103001d00706582058845500060074a41c105e82820281d0046071030030441d02818800d078000004030220810004101c8040a18142c0300244a90b80311010003021920980c02002c0d60002880c001d50300f8491004c5003220241c51b03030425503044034070b64105010802150b0127a41a24070810095640d681481203500c4e490b9040301c0090916078065608001d0726000c00e0240305e0b034501450094602103202016241031180401c001d81c048852a001d121170072011100c042040c0000d0364000b1940306a40d01e0520010b0001c00d141d100003989440001000801c00c101083c00c1c0c0c01d00703501238840d42140815180c1240c07880c0010160b00c9004842040028a40c0c07600001440e009201ca40d80c0146048003a4428812a0b009503002500041414880d2545a88c5402000c001c0e150613280b901400c44000001780410345140502e0f824800c81e010b0300c04001c421580705000810812030740e946640c0c0c09a01e143c865500c280100d1415 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 400905530 1250 400904280 400904291
    0x100305010e06090a0f030306080726012007060609091b080c0f040c111002040f050301022d0d09030e09072c010c0b090321070f1b08030f070201 63
    0x864408120b8030b1242c00e032840039000d50302c055916000d800c44001c0742181419070f10880414201010404034001d40080b0400003000d280083c80f000380030b011625075001f07070b85c140101c4c041d440e00c4450407214800342402200d901c82c4c9091410f14058442504990703006480d00c1044024004084490035915254083c02c0c04011380b50100203440d17030709e04840e064000d011281c4803191802c150703010322410340103458038000da02d020b01700030703802c01c0c00401220817500d40124081c00100855140480204003c8008600d08041c001c1360079201d81c02c0c806a00f0001e103040b83c1008503101d9690886e0030315400f0070802c004031174283c030b4040c0c03030a03075840030007030240c4009000a60246c0c0200c0d020203070002c0c0300e070100309002c0d01070040303040700e007915a0890304000c4240c0701d0b02c002641c00d00340e850003802240c0165032240109105400140c52100e0f010400c10241d50900400c035130403a04184a4000524042c01582a142800003044601d01300003841c5840000c2042070b151415002c0c180103c80300d6009015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 400906780 1250 400905530 400905551
    0x2030405010f0b061e0a0323010302031c020618121306030c0912020d05011b0809160b04060c1e0b1801051603090204060e013b072610030501 62
    0x1130240c0f4001d03514004011724443d0261040c4009005800c03201c1c0303004240d40c402142045000682e551140844c111850010700031450300348062030090301840c41c80c0000002034000203580d4940034102ca40b41e0200108081400c200c140a03000b80e041040e0440b6a940403074070b611055200c814860140000d1a04071320500c1188100e42c0c200864243c02520311403110103400b00200c07000c001c44100c0340c96580380c1c01070203880031003210300218410a071543e000074506008401e0030300440310354915180c01c0d60403050041c1140c110668040d240c0c03a14150601060504d44100c2280d811300e07a200d80030014184101c10090181401c41c45002c082424051003d1004092800d9400956040d10b240b00e41d49800c0700c40c0c5100342d0081c14000c2c00200080b85080d9a803c20040c4090300381c01c14000c4150401c1d845580780901d481c040910035160700c904025441451160881c403a015200408004110007030080003030514468503410402c0782e20040280c14054801d031820482840112800e5080400307050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 400908030 1250 400906780 400906789
    0x6070507060f0605011706191508011a070b07090806151002070b090402090604120b04022706010f0c1704150e0d0b090a05060103030305040c0e060a15110102030405010f0b 75
    0x1d04541041c0c40c6c0c05164002c513040d040c40002c1c02003040b9000f420301c1d200d000b021180340700e0003802000150380440c80340d00082e6004151b4034050b0080d2052502c06a03650148440080803242040e030400240f90341501c60f0344040310004041c0d4015011445046c0601c00c0301041e501701000c004004580d59813100e604498180d86609042c400c1d803821311300500c100e2100e42040d030004d0200d201c0040c13404c1c3c40c1c140c44101264189442c40380580e0402c0b080000c0004504001038a03483c60900601103101001e281c2088166881d4020326a50401110381c0f01c21800354050718141030903903440702d1a0b4520480302014408550402c0c4170301320301f00548002c1350760302078014031510030103000c054000642001c0c0354417070015002c405096511284285d03121000071950600c1407a0195100740d130041068206030030f04002d140f4460b0804c0d0800c40ca1102888004c0d601c1e1040507007102d0f051051041c00202d0600240c7d001a1051034070b0716554000004c100070042c040d48041410312061104002c0f8096000911 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 400909280 1250 400908030 400908041
    0x2206080610020d050f040f080c010e1f0e04090b0a05150a140603040203070e010807031703190c050d060b03180c010903031202130303081503030c030f0c0a0506070507060f 75
    0x6405a00080c48401609105100a013964400740440031b18182d55150900d0303500c2c14030f91000342580c1003160080e506683c0a0b1105105240c01c84451035180d900c00780c05003408213034010400a006d4001080140fa40740c0f5000078420540210b80151107240204124015040403201c0c144000381d49258502e580c0382c4800e10f5001e88840c442c88581107181c2c882441000d0340040c0050b07a061040e0a030028003490500d5215010300303850310103880024950314104400300c905040646209400f0700810141490000540890680718140441c00c0c5542c0942a1160310070f65050340f080c64109003000c24607080b80c000450151311200e1207400f42c14428010283c4414200c20140d00103100c0210800109108619200903801c100300010b14040300910080c2c1500b0301035100f2004584101d00b0410400f0001c41c0141c01003400303501840c07030448400007140d2a4400e100c5000301008000c188200340c0b240801c580c5084030b03031080c2184c004d4142600090082c0c2c01a0f0f5044680350b0502d220080e0069903409036 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 400910530 1250 400909280 400909309
    0x507030c092102032a0301021c09060603060510031106031b0703090b0412110a0302010905040f0f0507021507030c05120a02120c040501091a0d09020622060806 70
    0x809500d0380c201010390484810300b0a40007a40b0580c0c0501c2c4002d660300303002c4035248008040301c01d8610550328084000c070001c44c9101502c281d2040c804400343c3c0c20b01c051074080d8080c110000107450345551070520014104c5c0e410241031189003101700b000c2d0290300b48004056038000c4900c161810f00280c1044018441119074082c49030418010380d55403d0f804000d454014031a05212282d29110a525041c540182e803004031b1180905030a83d051005462041840600542c3d90001c010705580010741200001e00c5681c2c0115a00c6400b0000c818195001300c0c00c41100d0316043c0014140008000e55400032151103401140460000c42c458a000c4c1c4502c400d00d0080c1d40b90242841110151902d1050000b400741d6402c607000c00c1500e1441005103a440d1045410303030051500d803410400014881241a041004103000112036200401420001ea41d0100b1486001040102961011542038001ca50908030004618440b034660308202c041c0b0001a1001541e9a42c0c9942d5100c080218070740b4a40781 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 400911780 1250 400910530 400910537
    0x11d0705041d19050312090106140904051e030f031509060612010302012105071107061103041203090308030406020304060f061401081503030706020316050408070b0c01090b0405100507030c 83
    0x2148119655983c1c14424041d0044058a080c00519a00c0f01c000030130884140c10f1a9544030310a001111002d009006502001e40d00f0104a14142d0340e11a607070070003040c0c0305051010705032252074141403c00440c0e008500c7c0c411416124140102715a541403007001e1003920903041c5800048203410322000b519000c808840b69255140d103160015104119107000760b0a02000fa400d6810749000c440c011607001d851187d031482c4074032038402e02d01414080d00f900000c0c00c01141107503260020000009541c140c8035004c1148a003007941d071505544240781daa00003085000080100b009010140d4041c40c4140e00510b41030141501e0303050007001300c030032a00454010103900f103d06c58a0b5480b59100c55481051100c80c150f4058404002a207560040e840c221117044d0000108040cc3c513285681e5a0400ca840c10f00030b05250400f500581c03200014040c0421640300800d00801e002401d4010f104805d4100030200030364245410040c0d200d0618040d003505203420700010500c0d4911034410204005800e58 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 400913030 1250 400911780 400911793
    0x90e0606151c0b0a0b0403111912140102040e071d03060c03040b06040f021903181a0408090a0603020c01050f01052d06030f0708010f030b0711011d0705041d 69
    0x1100b401442c6010305550000d010b490007280442039a0300500203180680e46040e95030300e900b0104007521a941c0c200b490081d42e44001044240035894101078017551140100c1070b00400d00f02c249009028031380c07003615100240014841c08581048034100d0000b00c0f42e0440b030a0000c00c500303040c4d541c00d0030b50318a10b02480403c00070300826850100c8503000300c001000032640c21008030042c020ba8009040b1040780741c0315524860181c5400d03105800c0d819031b01c000441d441c41660b03113500c4120381001440c1140001030500050070040f206045520ba844020148428142c41d94070060083d0010803034281c1c5507107040046003621001858190403114010708118800c1c56010440d00d03023800940c144544034a00105440482c1d607010041d41c030035646031031b00c0c3c0c00b1481c0454009000c08410303807042c0151540e0b8001840800c0004940d1944400300e03080800800c0d0701d2054483c01002487c01c5425182c4079802a07110100010461008813070080760248030f00201002100c82d8a82074280c00381d010303845034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 400914280 1250 400913030 400913077
    0x3030d05010e090a2121050703060503060c0d0c0516080301031a10051e15070618031e0e03030c1f0c090306092301021314030606010315090e060615 65
    0x4031640b12245c0034902d00071540d04001200d10300074038030078401c12a04580ba40d04115010380d25101d01002030000f28010005030814540c404614420008132010030380d101c0c20302000c6d09024204130783c00010f44100308490303d50141085021600280400c031202c403707980c8000e201000c1c649116016402804080013018540003c0050940340c00c100310f260392008004041f6156641d1b1000c1d80c1c290b56a060403641c424030303450500115002d480c0240400d101901300d44003c00d0748031401c20008614401013a10a40001405413044c50f003003c5415818400080c500b44d242034082904001c03400c5c0310158000200e45114a202910061045400022010241080422032580040740c24502a00c041c11100c400d004808950508491080090f40c0d000202d001c0c120405032480c00003001210803080f00c00841c400020303101c10f8050032841c10552960710701051240d8142403003009288091040251016000d82740784c540400300c41281c0700d484003100c0e0082c01707002c0c0d404565100c10240c250001d41c0484 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 400915530 1250 400914280 400914323
    0x2010f0e030f03040609080c0306010609091a100c0605090c030c040908041a22180507200f150108120309071a070605280b030c03030d05010e090a 64
    0x2102015030601ca807940568030100300344021310181c51250f4440c00c682d070070518503614000101110740d009900403c01000019848000132003504d0148a0100e40b1410750390b03919040344d044185c0164011310038a5003042d0107410180d0048082e11544040c0710598584e0300040d01d80d50f011040a405403c2402c0c16005454554030000e900b40c0b04840e018102030325810508070150b4882049410224009080000b0742000340009454042034004401a036041c0211380c1d800d4014495440140e64503600031070b44490090b0751303411100c0d04a40c0c10910310044840710303542e00c40c140352282d00300d0f01444040001d40d080150240b4161a0b481c00100021b004498000d01c1e43d80c8000d01d2202d050044c11004103107406601039a805441502c50303215118611800d14504968015104903100081c01900192140407105d0703900003881c0765100010900850008281442400340001e5414040060319600a154aa00c000c0c180c0c1c5007000429074641c0c4400300c040c0e0b90340603400c000d803071140041080d40c3e04541 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 400916780 1250 400915530 400915547
    0x71e0f120207140706080a02041202040b01120f0f0c02120708071407030501051008191e08030c0d0c0c030215041a040c060f2307230303010302090a020702010f 70
    0x35400515241003a00c03002d070074283d0b21040c52201e8004075000c1001030303403040d0b03020303044010701004600d403515044880850141c0c0c0c240c001d0086403070b082d0003c856800f40c24010040702d040c000a110120b44804290010181070050440b02842c180504070510b200180000202c20802651841c101107904c5004c51508802d90440d24046c2030710300c1d420300d402d080c0416001148620004107103400e01090100380d0354980e0308504035903031140380715540c28a6030b20000391700c841d00407840500781c4884508046940d464407002400c4c140000062140e9441e03102e006121110300c0040810559030641c000f02d89450640304003030010f900000a5146400600d04010b400502c5081d0090000342c0c0300c9076110f9803041c110f40558001e00c0d915020002c95412802025040074180750032000e1410100c0c403009a150409110351624101003082c03010440542c1d15a46840c8051186158044038416015038035442400202d000701ba04201041c00440701c3c0c0240d4881c140d058581010b4411001d6007290b0941 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 400918030 1250 400916780 400916807
    0xf092313090b1f08030c1006150503040f0c05060f0702030c060304080d0f18050c100905060f1c06080703030f0504151d0a121a070e10030b03011103071e0f 68
    0x150b40fa500064a440420082005019000141640381c2010040d2411141d55500c5868608155046200340c55800070032694410340c801030148040a0f1401d02c006002881c4c0c0055801c504002100c16070003500801824100e4400c501b224010705885d420303c1418003040d10f008001c0502489001c951281a0700410b100c4804902c0000c0d5041d8a80905282c030041510b042d02da54000d04040201c5042c42d0002681340b04407810710f2071031035280074041401481554075803c050715000c075036000c113240342c07801c0248094580b90007803202907101d00d101ca4403aa440e20088001c940030416000003540103d081d2400c4032110103407004222121103094038020168421a2016421844211780c02c0d0703110515840a8a1900c10340c0d070800e64036213824840401000b202440550849041004403648850224503480044e5400221100009025000307000307031440c5142d140d401d040180000c0e030044000b4610540050b5039616022030586c07a40b211180300020400c0000342d50503001c82502c0d010b44800078481 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 400919280 1250 400918030 400918081
    0x70501090f03050c1606050a0315050604060513080706020c010e030a060e1c0e0d240903020d080c090315130516141905010f092313090b 60
    0x9036a55428a079503002400700e012a01c0401c8041e6122801c200c07540107200135407420381080b814204040c0c100d002d000143c00405480740c1c113455900036040c848000400f00075115a0f01c0c0c50711048050400e82103d40040202050300d40000784000001500804441158000d0703c5182244001119540382c0c46820941500c80c005103400081c05510429001001b130304042d2403881d045110b00311140c1a02c51440701081104164040e0030f9540c0c0044400071030b0f01c45103e11220255580c00d0f086644920611801c0b18640840c2c0c10074140c0104101d1400b00f499035070040159501103d00c4203d02422098942650000300c00f848030a291900454100b0001d42c0d04852480e6a9607402d0316052034100c40079583c20003a4010000d4000c1c030030841c542400b0071911a04408040303100c07502c1e0001070b0311070704d81088800c02c1d501c040580561080006070100c42820040340c181005c07030b0b9400c4d0302002e603250702a100c0545a00c0c1c102c1101c2c0320b0100d10720b500c01503a0350301d5128011030981842807910b82e011072 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 400920530 1250 400919280 400919291
    0x9060507060c11060a090c05011d04091412090a050604080d0e0102010f021b1506060a08060409020a0801091a1512010609090b0f0105271008070f0812091005070501 72
    0x100c030f00401a06214544801d00420415103500e00b20031440010341c00b1506100641c2a01094224281c600b03100507441502c0019110a5a050810741040c20043d40c2c0b510f03015840c3d0360120000d41030010440078000b500d4088920b95180240200ba2065100b86003c42c0c2107030803103869081c40b4003121f00740c0e4041407001281450b0b9000d515000c0780d00a409901402c2207251007803400c2d000501c0408003208034003410b85c0551800602040711449106031071001c2202d0880002c00c0c4c0c0e9569880020350342d802502c1505020307141d00d50f8078002d004030030090b04c2c1c0790300e000d66081c0070000560040e88a80b415668001080030f012040c000e1040e8006c3c01d114095403681c0c404a0b01c0446803190000072401221000c2d0281400390002d02c8ac400103030001402056000314100001050841e0b5603031482550200d0105651007108141118189170401140c90040910000389664000c0320907054400400954181c101d1081e80b0240d00c0c4a5202581d41150540c005400094040d10282c2060390003600003082 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 400921780 1250 400920530 400920557
    0xf06090301200d0501050d05071e0b0301030b07022a0f011709011b0509031c03090501090302030315010504030b0106050a180803070c0b030402030a080306060906160b0709060507060c 80
    0x508441e440300000701a080800d030f0301e6042c40a8010b00740100070a80d00c0783c04420036a1102522050203010314541c0c0d807140da00d01401a40d594500000400319100b91949a50b1070f803610a2502074182d8a130341c014820f682c9181e010368500464200b46190303500c1c151100505034010b203c003100d0310030002c60600041000b0f07002c44007080d000c441c0c401d014071000003a0345005070f000312103000c19069201e01008800d00401825840c00518410003500f0b203007c0340c03a82507940034210081e0a402100400035420070300400c0400d42c00102a60050800c1c0c1d07070041c000c902200045816008600c0040c02c03a44114004010160050000b000208450315041100301e02400b000000d0f5100d9910400b019400042c00d02c003441302c034110450140407401c600b5481c608140e00020f81e00d404050002d40144800004200e2595402c030480395903480240803a901c81c00d800c0080b4100141c0e00c1700554104420100045003a4412005001511110b8450a0900e401034031408001c0520700c400006000d00c0b50070800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 400923030 1250 400921780 400921811
    0x1120c050c120304022b0605061f0206091b0a090203041b0321050403030e0f011e0806090603190b090703060603150e07060914131107110a050f06090301 67
    0x5000030040038605640b404c01e481402000710104210811084800e11060b00c900d10030142844225000100851640c0302d40001507908103980400f100d0128840c0b003076062064001c01c810784166861400d45072040024080c080018405101c2a60f1040510400340031030000b41d40959005030240c1d40001803000c1002400c8400c1009070070a82e40711100c1d42e281581c0384808041e10f280d07141e40380750440c02c0030b1450303901400038200640300501c9034400700f0288500d40d208244071483d4005001003172002c01540c07a4041e00482082e01d03154003c090759070011340c440c01d001030002c2c00401d610a00711030b080c0d0940c80e030508400019200c6101402900000800710301c0900a2402850041000a191059241c00c010441700303a01011007942d003012804100d00d58001c00c40c0d2007100d0010710b000c01c0050101c000200c03686904501c0012903444c04901407894251000504021032089280041911242080000f900c10a206095000d0040c0c141c05e0070b2400d0801c00707030048900141c000b160301c00c411020b00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 400924280 1250 400923030 400923043
    0x60204050612010f0519060309021906090603060510050910030b060a03050105011214070e13021803070b040b1c0b090702240c030601030c140304061505010e01120c050c 74
    0xe0161000c1000103026100000c013030100189400c80b81e9464110b880c1000d4000a4184d21906c014542c0d5035002c0b1083d910350318001103040d070403604620582ea840b0350002d8020b041d20301801d000240361035404a07a50424501c01956501c058a0350b030b0801840000300500311444030700300410551598005900c1d40c0310000034244291907600d0100701981030400040c650700a029040010320700744600b41206c0055406a15000f81c01858400f0b030000d8542c0101d8500130003010035549042c80011030041d150316a6040c41040c60085058500031aa41e8240c0310985c02280035001c2c0900c000c00102c40d00f0001003000801d51401c40c80046001e18500c2c002405002049070201c002da000402c5440c840e5a1202d0090b001103210300c0b0704501c0d0f01b40080ea0700380c0c50000034480d40c1810f6071003030b51298040c0541c0030512401d003003120381c41d0f4031303d000d2a0081c050844c2c4550240c5aa8511601042d01e600400b074503041c01c4c0041e5a841d0074a00400382c1500900007107940c0e5018007404105844507400d0900c41c2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 400925530 1250 400924280 400924297
    0x3041704150903151a060904090209040b010503061b040501080a063503040e010b030403030b0a06050c15090604150f0c0e030c120613030219031206090e030a05070602040506 76
    0x6242c841e510f1414440b41440140d00e9a5086074a840c101200c88200d0082c0202c04040644119071038042000104006080c04440a5400107a450400c402c0026600320345050350000e40c2034603610b85a0083c440d40480c401c0c8070f0011506400e01c418451540f01345c0c50289e00031300e44240465036a40d43e51400c4000700100c1440207107407484c9140d84016844520640204c0140349004601d818034206265024880c10f01034041112000408034040c1440b940244680d01c5004004510a60b0b8400c0d01600b954444209410107004d07164402c2051082240b800b032290542c83c01514071070b51950b6030340504481e03002d12060072680d035108000d0b04c11032600c10117611460382d851300315050f550203041510b08a0748030076407449081300e035a1000c109207011645a0300680444501040007840e072030181c4c20820308100040305240041d001c502410703844100c0c0c4041844220301041015240e150142c19164580760041f1658010442a10018444d20003041094040c440060609440c1d50002c3c5265101041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 400926780 1250 400925530 400925537
    0x11d030313050c0d080a030b12031812011d010e15040b0901150f090e010510030b040503040b0f07021206040b010b210406021c2705030d14070207050609060304170415 73
    0x15080d200b6600352080b00c83c03034103003200c00327881026141407410340c0e9100310041c4a184d016000031000080c1c40d1054406070340b4240e8402032200103c02c0e2501030200d042c42c0d0003c902d540c00c0c01c06100d42c0300c10200f82ca4200c0c13418100748800790341d95a00d901c600c0321000781a400302c6650741c40030080e80e4414203038807001400d000c041f030000f0305d0718000d81d00003540e031003e01d60034030b1f82d01d858103100980c54a074101c502200e901030000c10040d51542412400c50159034824408200c0016000e0780010362031008006051003140d01044c82c43c1980880c41da1075004803001000c21826500501050b03540001509042c41c0003003d5580ca600208204911084165401c175100c81c0c01040740307891344400c0d01c800e0106000001702040b0b58586418100c1c905410300e0718500c14542e2401000b000c0c80414411560603910001b410300240c1751021444100d20340803140390006000e0340c800400c081c94100d0482d05241c00082c9000e0441e200c94480400349024010704e4245500b0400002175220405400407941891907203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 400928030 1250 400926780 400926787
    0x906032e050109050909030a0809191514040b04080d020408010e06040b090d0f0311090415031101050903120d06030b090d08220311070f0e0405011d030313050c0d08 72
    0x15280ca40c00d44c018078031401d4444200000c807100002541c084a5413440d00044036120002d00e1400d04104c0c15110000c40b000346101802c1c842c444032204c0105580c1e03502085510301d038203000003605038141e40042190014001040c00b0401a070050000c0b1814030400624043d07594010f28212898083e10030070f941c01c010204020710400500d4a81e002903840040e01300020304e2100204081081654401070552301d4050000c2601034400b80c56025502030010800d26005284030180d8445a100403135690408039040245548a202611000d100150091940070303800007089903036070071603814150440da4409002020400a01c2818051102c18000c0c00e03185410000003045003100800036141d03114141d640841d80c03a046440c1b500c217981c00d403a002402d002a441104e04141250340204140c0c0c0c40d0172f134049031900721f40e40d009004d40d00c644020050038980300d04034045c807010a1050100c1da0014000114014100c0036a0030704240b14406668072083d030200090150b68590100365100da4020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 400929280 1250 400928030 400928039
    0xe031c110c060610170117010914010207050708010b180a14010605030915010501090506211006020105010906050901050d0302010f0c0503150306100b0a18090903230906032e 76
    0xf807081d2031340074039a0325100c100051400c055442c100410b20801001c44440121501746000c207500000c1c079242d01c028200031650b2040c1086020b0b4000e80c2c4103071018001c8500000340d40c801489228551000903000105813064400a08010b94008289601c5103803a0001d50700c140300e14551a40c080c000c03c0d110070b500c0e8100002500c0c41e01311a0f01e60100911000301c014056070303801c0000c00007269001c0ba5400c0e078440d095200d460b4101c0c3c20056448a100700c507418408000c00c4c0d4031144007502d205a0007001586e030b891340c80e86c0030b80e0414842d01f80c2100c1502d0040c0010b04100c800e103003015000e400049540c1c001044414111004503e144000500120a2000e1040d1150740300403900d808030700500c020704005090340c04001591085045a10000460240700c600810704004240130603050404041d990321461000b51a0303000c012400620320a407000081320080054a4040355152000d03420004072005002560340b01420061000d9480280402c40308800010b00300101c0d404e20a15400c5480c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 400930530 1250 400929280 400929289
    0xb0a08060f040c09020306060f0f070c030305090102010e010204050a0311060c0601060509040501120b150111251a07060902040f0e07030201020705010201140f1015110d030e031c110c0606 82
    0xf0b9030420000702d4010824803281f951603006440c0c07a04946103416a84540c41c4940050512600b003000741818240807001090507013110180c40804000e070028084407125a0710340d402c0b885180281031340268414000c2c40820807041c440d08080c032000d00b0843c9491640f44c8664a080300036404000090000038019000b424180030f0140140011460903201800a550714801c0b03200060644400704002d4103110b106038400c2c01c075104a00198016074451035000c510840a61020100d038441102103000300086501d5142d4440000a1841d951642481030641d124009000707c4901071b42d016407540f10000c403a0720746106070015840039000808805295100280c01c10f00564005415a454820703903001382da000b820402d6112040b160004029078425008041192898101c00c100e0901d03041e0001e0301c9174100c40700004c4c4100200841d0402c83c6204030440990700300c601c1c01c560139001404080314540c1c00c91020f4041408503c00480c940503a10321040140c0c10000c0701510b42d030311800510625040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 400931780 1250 400930530 400930553
    0x306050103020703050a0c1b060503040b070239060c0a1a070905060d090501020a0206010801050f0106090323010e010f06090e0307080a1106041a10180b0a08060f04 72
    0x1801e0030290f0a0800e9900d000c0e101c0d000b4071070341c0414012404032400800450072070071089014010800304d007031603c070304008089801c1290119460860040814016400010f0424490200d1001ca060380561581c0c110070074a01d00390045021a0305800b404202e95070080504125040b92009084030080d40c1460b81c100002d045003180b0b00785104003030200307095202c0c01c15026130f1800d4901c40e80ea5007c15017200d00600b10003a0213012944046104000580e010a50904a40d0001300034044d6440d480041c0703105203000e2140201064803240c0800008200ba0b03006002c00d0b01a0104400115003240e20a003503458901804881c3d9540340110580e02001d84a00c001038202d400041202510150040307650344558540030b0592507010401600701481811480c0d07440c007402c025070b98141464907096001c80c1c500c1400c25620703c03008000404019285074404225001c00100d134840701ca1004d02080145007200714144c02c01540c01000c1002c140401070b00f402041440440c22440c03034030342850181c0c0c10303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 400933030 1250 400931780 400931789
    0x1103060102060714031b070b0f010807080d02030306090619060203040602160b0d091b080102041404020702090615121f12080304080a110618240f0604060e0c07030306 73
    0x4444d040300b1030070820f02c00549610180d0a046e11800d20144101d4040300d00541500030701c12000a01003045101d4000c414038102c80b400c50440d090941c0304c0e07032626251038119580c0d0005078020f20018a0360300e000c1d01140c0d04410040c000901140c52040404080840c0d0b4000202590000808202295040060300d242641c2c002e60400e4050805d0300c08030944c480d40e01001c60082d00d80c45440203105a003122a140346444e44440075241d80d44944080c040d401c07600c0341d81081e80c00d4040c00030701803c10780225021140d004080008580e00c0c2400c004e02e000e80d40c0c6600f03030300079402e01c490100ea403048405580912243c110854041e01c203002000c0000780550016101028903264120004003e0b600392508a075014100c942c4070f004001040741c4048031a1080c2e00180301c0c038409c2c81803031017001c85440003c4400700107603070f948188400f69020b1204442819203080c240e80000401d803600c41f100b03450b08014010404034115130790b0b4040030050320082e16080200c1a0005408041541511441c001007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 400934280 1250 400933030 400933037
    0x3030b0108070e0117100803041202031005040209040f030921020f150f0d0219030209090105061312020607050307050d020709050c0306010309051e100b180c0a0c0611030601020607 79
    0x20400100003d0010189914411050a80c6800b080c00001c038185406d0241128004490710f0301d980d0502640c04000b0504207078080c1c0260241801c0804041c01030034031460300a815284075803115070340c1708030400c81c0354002d40410103017541c04100829502007090750043e1014030500c100c0414010410b108410041c01c034480e920107415480307480303104004c2d01c00910403031003826100c3e1138030b20802e4041d200d0440490080c0416602c2000d140c2d4142e40540b84880341904e800146a03201c03400d011443c8945140c050703100090700c1d0200003a154211440000f10310251001c3d090000d240e0f582d0389180c001d101c044406400c44581c1540140e41046902d0060401d1401403050341000c0a14103c40c4c40083c1185041507282c00c0c4140034001c04005c48019050359500d0116088010421240c50b0a050401c4962a41c1003071801040f330b20345605614421842c0009000c51a1913034440680c2560210301d03010140034070148504082980c1d0311420000c440246561607407481c05000090400303000800c100c050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 400935530 1250 400934280 400934297
    0xb220f0204051807170115021006050f06070302030702040203090a0b1312080c0c060406020405041d070504020a350c0c150c370203250204020903010903030b010807 72
    0x50f561200f01440c0d00060114070102551105007080b9071181e00c01d002ea4040076443c00000a003070340642c10300380c81c4c04002c0d400e407044ca51a025031182550007500c030f40c941c8408d1b0b0024010a6141000c02006040d00c079004880c41c280741039022038182d800032546050a40c1000200e002444103508000303500c5442040000c5880c0600c0d40c810802100961218041000e40030000d450542c248045540f011000021185070380741a05c0c000300658800e01803507004505006442c1c804118040f18030740d030410104040c140d55420b000a0200075008045001d0402150410011010000e00303000c840741012a501c240354040c20303165000c0501000b1381468446c4100b00703c0d01c2042100031038540b0086502401580154440f00c1550341c060188100c12030580413002404102d962200401180001d2030080500b04441440e0050362240601000790064120442080c10880b4480c9202c05009100038401802c000b45007011900f1203401d02d00c11000720b82d6400402d40b596030881d036a06d5025010340741500300c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 400936780 1250 400935530 400935539
    0x7030614071b06020f07051e160303080a0f1e0c090b040e0a0c02120c07080712080a140706020a050d0b040506030a02040207020301060915090509030412030c060b220f0204 75
    0x1000d0b02910300688099400310b003015a09410800b110745407504076003101c0c1080581145444000e262410150880c8901950410305e14544209402229055140c88440343d88903180b8101030000503c5400c2c2c030ba962007060305044203044500740050583c04600051040c00c0d00d002505040d039540000c08415000e000420100f00d4035502c4640c480c010b0040810402401402640752104000088040d5000410000c096290000d805022a4201c0c01100d10540d0341d4118001c92400104002c4c100c0401084181c071045e000709900788183d60348500d000c0c40c2ca40291150412a0000c00c5100d00280e40002d818200503031034080d050003480111000c009600300f0341c000a0740c07012078a40003170040c0c3e00810342c00155502035101c1c4005291200301801a9800d9804002c080941070207210400c0e8a02004100321483c0081a01d080c1d45404005c018100441d46064546880e0160201c3d01c00741c444600c903181e0348030740a100c084001c02d003004801d018960301000007910810383c2c445804a01c140300802 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 400938030 1250 400936780 400936817
    0x20f1809070605251106040b0a0e181f0b0703030c08090f030405010c0c03060c030e0f03070302070608060415080303181c0309020d06050112020f091510050c0703061407 74
    0x3c40034108104c0c0507842c41005e142080c05000022a82036210700d0100b400219444a800189601c2000ea9280301c0142e0748501040010000c110140000c001c100e4001f450300401d200e551444600308004022080d40d07160101c00311540304160441c0020b46a1010822a40d00310084a030040140300182054601440c0025034900030743c030403941001442122079040c03010a180000103150070140074404507003c1d10001e00548000442c00e1698800c44600d01d5502d403008c0b094429035945a0301402095107801001c4481c03c1d03000c1e1245600c80d81e241c501489038005042640001d15025004c0c5440b854052110a8941c440c620401e14941240d41502082d11241ca80316905000c10f0070001480386107400403d00c1024206c00092980c0d07d00400851560405014100c0c01407084401d80b42c0301128006000b0a40c0050390020740510f01041001c002d841d0610300c1c0300100285240450800c60b28000c4280340c44515072050f01e8055441110321002c081215000d40e11002c2800c003054022507046502 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 400939280 1250 400938030 400938067
    0x15270a0506040b07090b0403120e220506130e06040312062402150403051305040b010e040f02130b03040b0c120a200406050319051302010804020f1809070605 69
    0x20f0100144500160384a406201841c000e00300400701540c40d1a00d9140c0615404200c0c03501c0004100048258200380c640107900c1944250b04102c032180052844c880c4078041c00c4007904069200c12501c814840641852240328154248800281414100f40c10081c01c1c1205030046070300ea10341016420f02c03c0300203003c0601d0042c0b48030f503820441140c0d0b14100301e043c603000801241c05c04000100380418142e00c5001742030010710302c84a40d15400da403042004101c60b0441d035024085034551450803207529007903211512200d05a10054985451032401c0c0c2d40868650b00046601900031081c0010b00113800701c103070350084032490744600d440c1d9004d40c1080c0204008045540741e42d1902c0c1d942440c1501c06845140205080c0c90303482d25030351282400b401c107400403500c481214003120108003a412060041e240280460741d459580001907400440d03000c20010001c1c3d0f000312203081c00b40555264980440007144810305280c50b0760802c2041c0d603082240ca9031040e002c1110034000320801ca41d90326034a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 400940530 1250 400939280 400939283
    0x80c030901110102130302240f03011707030f03200d031e0504020d0f0507030c0e0a0f1e0e03070c06022407021e010b04090302030408070501080c0403080c15270a050604 74
    0x3200c0849239503400c600414041003c01284100441c00b02c00003074028020394140d80d20141098008020030801540e104210302c000b03060103c000d1420382c0403d006180141c1c92102d88a2007180d4024880001d07490801e100c0703038940c002913459003100d064100346150b2601b0204030b404140720900785500001c8802c03802d564064540007100d0f1200b01040000c00c65400251f80c84890014a00c0d03030b624168032250b000700d03445000b00381401e01d46400b80d8550310903505151030340070741c0342040017036996414001c3c45d40104010992104101020201b03445003801c20041000e6802040590110599106801003410100d0302c50311040302130140c142e8002c00e810816103e0102019610710807240b1143c00752001d03411680e0001e16055400c424103034040000c0043c0c0c2c0b005001c80b213003181e99a004483d0103100b100c80e6581e583c41404140000754901c0010007128602204aa074501000101d20004030025103117040c00040811654206465281d8a99403082000b009401e9008a5480d080d881d034000510 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 400941780 1250 400940530 400940539
    0xe07120e0717190b04030e01051309020a0302040315020409140c220e18070b0c030412080405100323011202010305101a041e06020a060203060409080c030901110102130302 75
    0x482d8801007420003c0c250810b0001c40d5001d54041e040c18552881d003070580c0c041e00050940c800ca1749607540100c04442c0307075804108600d8042841c10600d0f02c000e405c541c3c0410101502000008003181c1940202e00c107500b94001e00503550b03450304090204852289001000c0c03034090307c0400c5050707007100f810360702a074500c0d1250f003d17445a110044281c0002e29003080c0c0f83c280000061008502d800100307a103506003183c0071100c440d611043c3c001e440303009001c56007130036a104003c2444480e003c00000b041c0903100d0350066007443d81312000181c054102444000c0029961401d5080d20401c054221041e541c9d80f1511030070315418039042c484c0d504201c13803005c0d05054503000411585c10314100f40b00c1c014203090201c88686901c8040c1d808031940188a402e00504070700310205442a003002506048801c99002040c4005542d95502c0103034000810165015648202002c04541c842c0003d025010394240550342d0703881032a00160014104031403280d100c0c0e10500840c141c0001840c1402c058940440c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 400943030 1250 400941780 400941809
    0x501080d09051f03110304060b040e060121060f0c08070905010504440c010e03010606021e01150b0405311d10090317070c200a0e07120e07 61
    0xa03c20f078098004802c010400620010404c400c2c0300c51a4400c4880b0034003101c09001800d6641e090b6a0703100b03000c0c00744200c200780d6041020001203019040404280c0b2034100421251042810542100c0300301d4a5440443c0b1038004122581c2c0d4002c00e42d402400742402c19908043c1840c8088200540c445401d81c001c007406004080107480b14425803145210354101c1c5a608030980d0480d171b40700c84002020601107181416490f002d0303d030601508041d504158002c092a10a54600c045404008203011030695a5190f00340b01c469134900c1c2000103030820643c0c0c03d030741d1850b0000b44090716088100886c500102d9625049496281c509a581c5482e850302c4042a0142c44007640c2844507001c410482c1c1d5440340350b28020410359541c019562050090701c500240003640481c44120350401ca850200060440d090b0500140401d44c07060071032144000340340d515140c6400852105a03464000311801c82c000001c000143e9400040b010106107a4034080c42140b03012142c0351364401081c06001c03c407003180b8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 400944280 1250 400943030 400943089
    0x1801050a020c0a260606180c190e0a2102010311040914041110021911120f010c020c0604050f0301150306140a11030406110409020d0501080d0905 64
    0x1c002d681d002503001485490002c2c1e445400c240c604452019018418444084070400c0140c0820807511443e0081c0940d102c2e1005602440069a401451f400158409000303588903803c280c403509912240d25140c0d07440c0e092804007000380784400c1d1740c40b07644003000804c4101615190710f41e8a400c0141e083c00c000c100c4560030078071401035004580100295919006030308080c04000c0680c207008600900131026080036050601a2a10f500c44500002d0b0b40b2044168400140303000444001a000303a0000080c2c0c074850000a42081e003100104506a010703c03000f140c100800c0c8074964005d0000d000402081d41018007040050141c0d2017003a00c45c80d841c01d00846181c80c01e410041d000f0000e20403a4001c2c030346a00d031031002004801c1e549540c80d00d9403000a540452184280d000103c0700788601070456070359070740b4a400303092140d0744812400f1042c04002060050b90010b0500802c02c5503012500c0d40c1401009454003d150801d00100080b20104101c3e94566410411103d440362289400c4c240c6607 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 400945530 1250 400944280 400944283
    0x1c0203062e0c03030f0e060109060902040303021902040209090f0601030507033b010504150c08100311211b0d0308040b2203030212070305040c1404110a0201060512031801050a02 78
    0x400b00c5c600a19818112101841a004a6500c0c184c6194990811025440303200050803801a0300008015a2000080410803840d00340c0d2007408503c003c2c80035140c0b544e680041443c4c25400c2e9800e46600d0500c40038083c8079a018082c240d030214540c07a04008889054100c400300300070324404414034281904002c0c2c482c400b0981d14012007201c0c0c500a2000b42002c2c03a080040483d00c101c034103280352405d005036544500c10300f50240503407641c66842841908580759003000d05508400030303074054400807910003a914a040c00400a4007502c003d0300c041503016003032038282007005d122a446290410140c0300000e802c10a00c80c0c00c07036003086c920300303496841031000e00b070390303034800c1e130f000c00b002d80102c85490801d54981c0007045000c180f02c1c4109219190b0364815030654070196001022045da185091001101d102c00d9080c003c50020800318425245540505403640000c1341040140d45413842400282041d1488600180d50031009629003107001d0385049031460a5200340b41040701c006a14041c4510 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 400946780 1250 400945530 400945541
    0x12020a03060e03040509010b0915090d0501050f0604270803060109080307061a011b060b012105010906051009061b061407030b040204050112090201051c0203062e0c0303 74
    0x1e1080c03040003101501036255540360844d1082c0e42c86009203a001103441c0d00340005a82c6031002c0a46108d00e1031909002800031500815606904200c0400003080403032401d0140d103004110f00c0f01ca80e40b043c1060400e110695440c100460704511550540d0078100e5801c0a6140c0c0c040d4001215948948560004a585102d281d22400031880080348503814889103074069211040304c07022005100c4103039001507c2c01c0c180b1030712511000c5003504a200c08102290005045500305251a03d40c05010b54070008564500038003180010b0f42d10b50040c01950118403034400505000c40d8180e9010f0f12a000c001c083c242140200c90400c40031800d90480e800da04002c024045074002014449084a9040400a10811512000000d00304111466142000d2084030165071040c0c0d240b45e841c104600000d03029004021040341040001c00140c200d90b42518288402402d85c03400150303130307030a00008016105020200c4155482c0019184115107500d140829282c000f02d0300b001d1204c0740351802c05400514 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 400948030 1250 400946780 400946783
    0xb09070b04080105070206010e04030f080912070317010b070b0408070507050d150506060c0a080306060403061b0201050a0b060a110a0618031107260a080d0203060111010e060112020a03 81
    0x880410080b9208a064006610030707a290780c21252541e0742e8001b20712608800340c03000b8010464824000302150f04c0340015660090404040301e42008002c81d80b080142c0c000d41068000504101d00d403d03100490781204e5004041a110340d03130038034078a0703142c0e109600d1010b000149014000103086003040020b100715401400001c000000d419514140b00001c503040d8543c0e020070601d8a000203903a80380040c15030344804601c0c0c00070f20b5003411076903540e00700e980050041a4410410311000001861074099601000748650010400d800b520784d010b030a540c00a01070b01e8465040c0300c0c01180507124141500d90000003468a0180300034140c85450a0800415001e0b20b0b8034207281d40280d59024084444c10ba4170310a503248a414001d0000c81038507200d0a021b60030100800b00d404240708104420b03481107060448042e5440e0000f1780e9030720386c0b1a902003601e15268540110404c601980c001c2941019401108020300c48e04001061203a00e0702030500400b448010104d074a0020354551400c40030145 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 400949280 1250 400948030 400948049
    0x21212031801091a0a0516020606010e01020f10140a0c050702130212090c010e0108060307030b100806091b040b091b1b1b03030c06040f0f08030f01060f03090f0b0907 73
    0x4000440003401540c00448901742d9580c1404049410701c221600d5924031005540d0240071261a50401120002098003c240c1184a030030180c00da1020240511207455200d80400560010031644050529a009000c0352255290102002d8215000400c8800c003a6044a80484910240b5411002805021903014074045200c08102440400140c0030718080e400340c0f2021143d42407400111441002220a1034058010340810000201c03c111070613004071240c8020841c00c5d407180306882c9010001c0f0780c80d00b055844506611540344002481158021095600f804500c051201042c0c021401825400c2c50007250401210803803810f0090350701d00411002c0302c0b04a0b914814100707a440d40001d5500311680c81089044405d031400008960f018030380c820280000303565a8460118103581640c040d640000c200328500c00003002a001076101c0c42541608100035410001c008204012010540041c5840c0c4544040880c0c0102c2e0b904100355030114813450f42d41c0d128a0390900700ac603c2e03400781018 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 400950530 1250 400949280 400949303
    0xc060f03020d0c0c0506130f02060318030c0601090507111506060906040603020d060e040c0b03270105070e0603070207090f0605030115061d090126071202121203180109 74
    0x3e455120340d04888850041d000c0b40c1103901c13140581ea4a030844d43c0001442c9a203201c03031100050034048099a0b11021805181e2402d20300b58200c14110380c40030141c500349412110050000f0b82d40741c458240c02000da0b29041d10380704000b4013020740d61100300e1345400c2c038a01d25000013074540d07881c0011105880005404652942c0d40c4050280103508403d800c044003d050803000304443c0c480280f00761059070400c21a0131340341c2c640380c00914103030710250040c001070340070300480402c032032a61445048000200c000000c1501d40800d0003415406c485803058801c96081050018440e8002030010a480700c0b044001100c41080080c40010103540d440260954200020088405c040c001c0e010304031402c64860b0003d9040d440c0c0c9022465401040d031980c0f08140c4801441589080c4801000242c5901030b8407141031345502c0a141340841a034800099000740059200c2141080d044a04d0441641c034010000b181681e50f0388056800014111101d11541c550762808141c025000a00c074113400c43c104400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 400951780 1250 400950530 400950551
    0x61e0f0617060613052107050607050a12022406030105091f110706060f05031207020625061d010b09040b040206160c081b010e1e0a18020a0305060d0c060f03020d 71
    0x700705001b05400d8000b4080e0700c20019143c02c100003200c12007581f0a0280a03030100a603140700d83c6280301625903003184944003621080c110001102d00d25601e0041000000e403804908146c00d540b00145011076540156014035294401c110380b41c1702c25000d200010603203842007014000319008600019001c60b043c03c400007503007119060303848182e400a4065448100001c15481c1d0750344603441d8000e40021003001a403102d0b5405d0180c0d00c103101ca4400c1c03440a008050b888040c1598050b4640c8403c120707602050815101d82407248010b03416061700e001c005490700b6120b80444c0980244003034041ca0f4002400701e120f01030307108100c0d0402e501c005030341003480d220110380343c8d03c0e0b0800420034055540340d144400190f0013502400443c001c01424811400c0c43e504000c2c0e08901c07812002c907040540c085012422041c1d00040103c111a403200040e203a00000d2001010354401518581c06522215102c1022500080346003082d40c1841c1414002c5451700d070401c070024070440408a00da0b40c0303420400302 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 400953030 1250 400951780 400951819
    0xf08182404050c03070605071e051501180605060d090f0213140601031a04090201211e110f3412090807060c06061e0f061706061305 58
    0x501640c0110101c4040f640740c40189503458850340202d00104074240034400029040319402282c0a58004850807212000c0d034400d03107040780d5840103d86a62400005020850b400c04852017903c01407141442011710f00000315030755200d018106148551900020014002500c80b01c0c65440d6000c2d19407400340c0358607035001004000e00400c07551150068400f188131036201c1d010320940c41ea1600c512400c0d00c8550707006c03c002012200f8040f411321515a1783c0681d28900c40f2309940c05134010250210310880001030f2103502d98a6041661000d600d0f103123814001d490448162040440e1000c2e032984d03501c0318031b0007041d0500e4076201200440078260050a18044400b220842e000e0300c00d4250703084154290b6800c1e28000c000c0d0003000707810b6000c004200061403003103456041c80c5004100c0020346503141c00d02250345092403040140f07241c1d0614803c015081540b40c505004200d030b4904840040c000d8104412102c1014010500c204000305041c0b0b003032186201803000822008001e807032144c111440300f0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 400954280 1250 400953030 400953103
    0x40b03010207021810060315060f09091506080112080708070305070215070b0604090b0613020c0601081f05070c08090f090106030c02070621020a0504090e07090c0f0818 74
    0x350000c51105c800a4540d01a0150300905802d40081600d005d041c072100320b401c3e11002c1e16400400c107400038000b03441455071081c900e600188800c001080d03424079070003501c4000d06a111900c42d800a44140c404502e95005842c2c1080c2d010803c941d4034a55810106e9481c00350180107907201d180c01101e000c000a1500c000c000880c0320300c44240c11a80c8100402088454031000940400d41e103200159462500315110000700c5a49080117007800b00050f00145000005d800031480c65021803c04035480c410001d003022840103403c028400340c54940c1e0000e00f0380c406c00100070240b40c0080703800045552262001500314202402c0c0b03040e690b0351000000d01420161201c0c201501840d03801141082c80b4417a5030954002d203072081880061030900803002540804500000c0140620000c601f01c1224001c1c501d03265103ca0007041014102845030003129400b00c000014482c00d02ca41c0c8400c203030000c1080341d04c0140940343c2032411243c0c90916043c42843c510f030080c03403040700b103e00d210b6642105a1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 400955530 1250 400954280 400954291
    0x3162007060e1503090a03050306060d0510080c030304060e0d080c060a0f180209010e04020102031b0a0c090606080a0f0f0c2a03020307060506011808030c2109040b030102070218 78
    0x102c0000f289803401c2400c2444180c689a40b1038021030700300004240174000440d009080902460b1a000c0201d08200c00c880c000d50b820701001000000800107181c2c02c006491846904901075031809251020140914a00040b414081c090030f811440a000c192400d5a655200f10402e5803140e10305103500500030001e81d10704a582c94500b00d40340002e070f8601c0b42650000c0743c0c0030f40030354916401c12054440c10f01c00144201e0451104114280c0803205c4141030342d0040d51328000510a480e02c51801c0880d00344c06400c041d61082c58110200401130b0300c0b00034107030000e2020900040416915441c0d902901d1400303840d080f02402c106808005c10752016008043c1d007011001c0c003100c0306c0103203000403001c0d0314440c001e001030b0301c00e0182c00041641f90b8050703074001c001414241a43c041e0003000051412443c0d003e103283d03400c007103006596203006004100d1980d52190b24042c0010910703041c4a0107000349a200707401180d54420b4100d10340c40940c12200c101d13400500e1001c0e80c5c5102005114a010201e50 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 400956780 1250 400955530 400955539
    0x90902030c09010f0905030c012106080d08250c02030f061f0e04020303040303050d02040e0a02031e0405061311040e07030210030504021c030c12020c0301060b03162007060e 76
    0x5003514070520417070400302030310001005044140c00c4080115100c08a0302c804e0502816003818200c40030296205110003000302002500020401d03440240507604d00500360044403a6000d070400810320015142d6000800e242840581b052140c0003186c5407608100d4016602d1041506000300c43c5c011a41594002508500b501c803038544400240e45500c0043d98001d405a00500003407000030b000e0710140502c812981c500500f030540c1c588018aa40e0416502e48140603400028040c13800030000c00714030107a2100b03c603848641050780c0c0d115603905004062a691f410120725071020408600000391f6880700061040c0300c40b400700b1200d81e40303520861100f00c1c420800d00c1003d10001d4028003c1d644500d80090035940d0304030682d80b151503e000d2555088040001201e201000901d0300b820740b48098010fa4002c105481c030190500d42101c0c1560060344c80c1d48024810011903072008064452280044d2404c41140040e442c0e405c6944400030304803000d14001d800d0b000c1600c0c0c0d8006812200f0b010b0444 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 400958030 1250 400956780 400956797
    0x110c0a210207081005091501030b010302090c070b01050f0a170c010822060f0e030703232b060305150f07050405010e092a0c060108030f0712090902030c0901 69
    0x480c166910801d80c0f040b5409500402c4040c070b1920140e90000350f00141460a80d9187d803031000812040140c260002c9802d20041801072080d030030b084c00303c15031100070601e07260318010403a114660410341c14030a01c1d200d4000a5043d00e51f6895810400c0000c2c040349284041140b920b444d1252280303e44440c3d02d002030600400950074020407604040790210054003000f40a40684a02b000743c5140111a04040e803a040b11110202f030410051000034066075448948142180d02c5802c0700600c2140728070004414845c0040c11484225110241041ca11445404d50b00c4401b01202600c0c00354030241250081005d12025030140804c1c40d84a081c44111415140d9100c0c0c009644a01450150900023001c00d8888285810a102480e0b000b421100e1150000e115181c9c200354041c44840b07408010701400719055460220821150b0302600107100507504020f12195400e01c140210bc2000d08203101300e103d140015401040328034040c2c451420203550340d20b40b00700718100c158440340f5418000340009 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 400959280 1250 400958030 400958093
    0x70f1205030f0705090a210c1a0909060409061407090f06050910090902030901090b06100e0d2609010806030c150a14210a0905060604110c0a 62
    0x40c41207901c20061596082059194807030229140d402c0912855040090400c022912885802a400c01d5401d02c100000100d0309a10300000002040d510000008001e01001540ba08080040e01d248d15030a5032011a2a0b8400c0e00041c06440240c01c0604450725001c0c43c6060502d02c12600361007600c264680122060741c8601c0c1c4148440c4c0352103004001142030210242c43d01c1c02c1500c40032030700c010317103040b10829880f01d84840803030b8030580300000681e549907982c00801164042d050350001c000c4038ac6403015012114043c003861100102c044c41b039010300300c0c110100304001c00384a0a01c2085440109a40c0a05048080d580e1011050a000c41d112100080d8207140005902c031040382c0c050650380d00c040c0ba1070f0154070103401842c0070100703000403500103103400b00b444006003c0c0c0034484040c003c00c400c0410b0b1a40c51020000d17003140038031030611814001044000070700d00d4010310b00f07a0b400102c014020044040c2805010050a1103008494105042c48098043d0705007401d6003103801c1c203880c0c0a9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 400960530 1250 400959280 400959287
    0xb03151f02030711060702040e1e060606040909080c0d17010801020316080604091502180102120a181701050106020601080d1e020304050303030a020d0c210f0b0402070f12 75
    0x2030000400042c1d10402c01c07000003a00500c041d44882c28040e02c000d05140055002a00780e034245400140d0741da00000e08807514580412011264014110141c010390034036602081040c4201d0140d109040d03150140d4a04102e0700c54111102150134205136611200310040041c800750b00d52030b11098080403100003141a00040c4201c0780940a044400da043c403250700c0d815030f1522001040389600c20390b2a9128000b1804c0d540101701c0300032058000507581c201c01030600150072103110300d040c1190301440009941c4840c0f10221030340c600d8241018010b6802c2c10307030a00100d4555401c4a80d00240d0184601000c60b41504042e05075540c0340c003074a8445c0e883d00308296035002e07081036101c000303441c1410b40000748042c80d45443d01c40c5910301c156490951074102082c030b99481a0b64451480c2e90000310071001d8900c52280e01005d54583c5800003510042175001140c0303950548860503040c3c0c0d210b1040000002ea540500e600c504040c0042d9260600d5040a040c507989109040e102c4550290080328000e11 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 400961780 1250 400960530 400960579
    0x3020c150c030423070e041218030303090615090207060e1b0402030a09080309071707060f0f021606170a090c0e04060e1e1e06010b0706060b0315 64
    0xa0410381411a40c640e210a140305958440b40310842da00c213641c202c40c2000900c101c0018001e0540030840030f040c01d14100802244114840c0c0402c984800c0c0004c44070301e007520800489405250218003200b036410100c0081c281180b2008960240c4d0100088100c61500908071890180341c0801c0240964003c0f0364a0f4030310700142c0b06030f22851400030300c26890280e0145030484251080021415915982c0324200c3d03000f5250350030036500212040141c1c5000006880f141100600a800c4403031400c0d8000e402d80c03100358516404d10084144c00c40007035108000e0512981d0420100c0d40d0362503607442018110000100c104207107400c1000c0050504070050082c2170455a0184254403a980740c4070a2000c1035a015004841e91511400c0d00c00d0041c03401c110301e98600c000302042c41d1703848210040d02440d12200c0b01c011003040d030614000907509c500100f024ae045400700e04501e552040c00d460103000a0001d600015a07c0c14040b0a0102d444006c1c2c40301d880d0345000703403200c01040443d0441d0828015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 400963030 1250 400961780 400961791
    0x50f090c1003090204150305070603020a050304030e0d05062a1c090c0f1e170a020f03031309051006110c040c0e0402120f13021503100b0a03020c15 65
    0xa00c2880c2062a074102100c1c104001481c525002400501d40c1e8002400c1d14296918580c4030401e03840b080c02406818030211009100034142180350442d07508014050b40001071024060100b000045142c586a07115944803d550090a07150700f442c0c00580740c0344400f480c0d0021000c413500400e160b042118400101c60000e040c071210240001ca8000004015182c007400031142296140b600084000c01460340e800034000342905440c1c1440410032a03400d24001e64041c482501d800e181003480c1501c085905480550142c540050f201680404203103540b02d80d00c1501c0f40c11100481c0082e69100c00d91005001d0252410501c1040d696007078125a514812003000c0080d401075408414140360544c010007180b032541c01c00041500048000904980011864401007204201002a960202990280d01400310100303580d00c503a540d004a1a91071010580080007400007021520038480300d02c22200030545030b0009561040d16840060180d0011910b5203110b1141b601040003802c2084d9100c0c0c440c8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 400964280 1250 400963030 400963033
    0x603020603010506030a0b130b031006031e0c0510020a2003030f0c01061505090f06030112110607080c070e01091b03020a090f06021506030c0f131b08010306050f09 72
    0x5900f8201004501e510103062980020ba0b50310640201da12103000e00070389110305000c0000c481554409050400c03c0030038040041078a05001440044d071840580c014284104420083c0b01c0c0880c54183c21a8001d900126444500321200302d2507150700090b25690a4890035504400b4901010100003104488140c2c0da41600180046040c1ca61400c01038254001c2e22000440d070190b4500207445d02c44110016000000c0b4005440c1c180380c01c3c1501000a04002640c10318030b19807508005800d40003046038000c0c40f107983c04144146543d95001038881484e000300e4020303520110718600e20f54451091040760620003813a000003411104a22407203510106000907490f8981020307008038002d6008000350414000c27440c1c00421407080450b0b400d009001c003900181442d040c92244864103c4005103e18440d034060031860071261a1030406880b4440251a903401c18804401040041c01607030048030800041c4280b9403512680c0308007094100c1b40120010046511034800015000200719841000d5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 400965530 1250 400964280 400964287
    0x4020a080c07060902060d020c160812130e1e1b0d0905160b03061914010e150708190809070302060c16080c04060608010f03170714061906030206 64
    0x201d05500000b420744922410000806190036800581503400600643d501c5030790214509480d07403020861854002c00c2d0240c0f00005900d8403048541d601200d02095920400c0403032a982284050a0800045c00c60302c08540359038500030f4109202c01681d0552001e152a214002c030b041e61482281c00c10700780030340c3d0303068902e41030481105c00003400e00c8210403182441981c45007900003d251003900040c080040b1840c0daa41002c2d42081007041d00704000701814059104200102928200d89500281c002e08006e01c0e4403000800003402071a00e0074050f50502d4000422004001000f4014805000d43d000305814100c4035990488009000701c4940700d09a002c0340051000d883d108001c4c102070820314007111030700e8a0401c03c2d000c05a55a90003012a544081b81c4170b2100d00d4540241009040c0510701000e5541c5451004000e000c8503100181c803200c4c010302c0b8403001e40b090340300700d860f0160400c0f032003400702c1805551103660b42ea040b01c08035120080e0400d6100f5225250151030f0440c0d0f0000c00c40c508 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 400966780 1250 400965530 400965541
    0xe0106090c09051912140109030206090106051c120221040305070b0306060d0b030c0d051506030a0308010608190504030f08180307060e07050d0804170d2c04050c0904060504020a08 79
    0x52402148505440383c181018140e031b4010024000d4041e600c8c86a0701408080c20050360ba90f09480c4240c200c50301c80c400c080c1c0b120130700c16181038125403015003040210064400c81082a0b09011060b540d10140a4403540c0500b6900803850081007220300c40c03012541060b41e0341c156910035000540300b0b150711043c00c0200000650068001454a4500a00b1b42c0d010300305000000360b025280701400c4403150000c0b0304068014851044443c0d0014040d40034016412855400805561050107800f00b40007108001c20103954401800c0e000c03103c031800003009541050708002d0300c4002e00114080009031000c000404603600e0100307950040300e480000f5414445580c0d1801c1c080c01c07282205034502c1c41149000202a51008920440240105099941c890410211001c2c4940359402400c240d84450320705a05a5801000d01440001e40b0304488901e50341e141e21500c0c0c810525a507154424104070500084e1f0b00c0340c4006000c0c00b0821603040085664403001d20080e40240340e040000308450000080703 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 400968030 1250 400966780 400966799
    0x705160308040501290a0e0f060108070915110c03010903080615070507060305090f01050907060503090312250c02130504020d05071e0e060310020d0e0106090c090519 73
    0x41c2c20a00c168008180c024081c403100c07001c488400181e0f2021451030800000c1402e01130031440c05041106201d4034646058158092100805041581080710410008510f20b20400000c0d0150030821482c9405018004004140010701080c0720300c54000c20f044c1d019a40341c144030304400240d054030f5100440d5a03060030020314400701108011120340400c034010004005202482c081e0000f80c40010302424244062441c002c140b14407030040da0715010a0282d0b000c400109801222039625009a5076a514a2803a065006620880440c062070b181449140068510351140400c18808102c00703006c0800c10448044080c00c00103504880602103a8084e5080740e00595072090026117090700e050307480d55589184c034169a10044032040c0703183d6010048440f0200a00c01850b802401f0300351420840c000a0f1181da004904000840e0b001510021509032a08400070b9070400708020410309a89000082c00b5182c00074415001640403100480c251038902c081c068000700c81d0442d003102608001c41078 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 400969280 1250 400968030 400968047
    0xb03040b0a0c0e03070e0714040b120403050d2a091d100512060609060604061b0c09110903010c020d120b011b0809090f010501050904150506041d07051603 68
    0x1042003c8540620360703101002220002d000b0303014420b445142401008011550f060410600740408100410988034103000b03640b0591100c0e502110a41c40d140b40a44984c03047d00008049a8244580408e500c040c011807401e00c0b9a61b90303020b500c3c250031404115108601d501809940307000907603581000d20010400140d0080c0b103e00b40361142c5480f80005604c0320300307901e12000e00d40d0182040059a050140c1c2180d0030610075030702c440c1094144200640140920803080c500014481003100920036592903450082140500c100320115041b0b000303500c50350107003001354000c0d0f081200140c821880020302c410f881101e5035a481409210036464006061403400315410011911030818290f848000c4d0410100c1c4a0030056503947c10400910441c1c030310040007010307900f60724401003040341d0f08181180e44807142201e0019100d0422502425051143c0d001a0341111011a0100b0b840ca00c081d41e20080c880401038166244d55007802c01ca5051064016454850000b1348031040000d0241110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 400970530 1250 400969280 400969301
    0x4061b0504170a0503030c041403190b0a060b190e06090a05060a0302120a0209030d180b070c150c03090918020114090405072102031b210910060b03040b0a 68
    0xd59103c0c2800351111440d44c1c00a8480c11103001000804010517801066030380001c60055014004000d0030690f2504c10181d41000940315a2034040040c40d1001c0992040717004e801200a4030382c88210700f2040c2010708030381d0305002d004078410404007130b8140780440640f081c445008111a1486041c14240201c03600503202d004141902804580351000000304001c0c85100e840d080141c407035410000301445e1150030100320007400a410076030002d00303c48011010030760340b080700525920b0070545001c07031060007117520040f65000340800d07140c01c03d41d120722444207036400380d901c184070151200e1028086407506032100d0b104164207500000194010784009000552901c00d21741820b070218045000d60f8401c503054400520003013080d42840e42035030802c841407000c0031811804c504c2d00350040c01c01006140503040c441c0002058031a1900d03070320060514540c410140070180c0d41032410740d05075540c028040e0345800328142040031039042200c10650b07115580005443c403141d2076130281c2c000141481c041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 400971780 1250 400970530 400970533
    0x9050a0303090f470c0c0705040f051f0f03021009030f030807080c090a0b09040213030c0f060809030d0e1e060a110301060203070305090d02040509010504061b050417 73
    0x400c2c004541200307805040c01c000b00007504000704c41050780500c2002c260303041d50b1104800c0b0216100142c0307080341e81342c0d100c040c807281940c0d82c0416018180c9840301035804698810308005080102d68034903080503008440b9a281c80d0300811150088100d45181030140c00d01d00121214100301600d0b00c00c0c0184483c0c016400d02850080e141d032946a1200240030b006d5020174245024804001d90007106903600000e0b03682c406007054140c10003d130180071940300c3c442041501044840c0113a80b550304491496081801d0b1503601030703891414111501c528810350003054244c1000003889400b07100124400d00214014600d400030101c001d50091480058a0389103120300f090010b45008460921040280e000b00100342e5490003100c0d030029074214001e4403d100c00b00340010805a44c00205403101c0c03590500701151291410030105100e28410a00a988a8185428000032040c10f5004a000305c0c0070785018000340784512210f5403101c15200102001920810082146102140d8006480c050100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 400973030 1250 400971780 400971803
    0x101206050405090307030e0613121a07020607020f0606060313051227030703050601060c05100513150c140c0106180c020d1e080a1508010501081009050a030309 70
    0x14040303000c80e02c0480700d001c00d641c00082c4a0b003e068000d01c0072500b02c10b04072031182ca40120191126003404a61107015614a10b90312000d01b0018240e8800690710a10742980703849160100c0020340d078400607035443c40540a00c40080d145c0b1303c40468540e2041101410291a43c5c90b0321031079500818126005a555002d404d400c8001c2d080d041c4010710040000e807504401c0803205620b260345000d40c2808840c0310350b01c2598104002032000c186c541c11a0910300f412190011941401420041c0d444802e0b91440c1c40d00007040070b1041902d40c000b80c4907000781c0c000f01988402c0400d070001c4801100c1418086980c0709005c420500110f03008140440c14031001260b90307661640d8a40030b8030448100ca900c40c0e40c641041d48142a03042008001211f5a0310f08942c01c000c0c070b544040040e03d4044031340720030000d05d000011a9247c1795086030303e0800710400f40040c410b40e101d000758001e020a000d11009400b5080300000c840c02d46004600d07105401c1005008001550340c3c3c180c00500600004450381d41111 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 400974280 1250 400973030 400973039
    0x703020118110406120b16260f010602030a0815060405030102031e0c18040b040605091807140102031c1e0e070b0a0c0201030903210219030b101206 65
    0x40d8140940c2502c42c002c90866030040d0802c000503541c6035002046540c071108201c1d80801c82243d05140c0080c510785000b150222134172801c07a00d1744001c03201d9102a504010302c882c0c0c0207400400051040c4600b600c6200e050740ca4a40403600c0e03114030b200c840f0000e0241404506030980300d04c07040c80070250080215245c0380d0f413240400d0990300101e414007029a664412000419401c0990542c00031189020a1800c15444800c2224283d048036513401250341c0c5507000c001c0e440e20f0b840403002d48001400040540752280340e0b0b00300c1400c20340f0140000d000e030090016107101c403203060300c82c0b5040c160091400c0c40c2411700454030300180008083c4035552182c0b1608030559403500320500780c0003003180110340c0c40d40c0d03c0d10051038980181e01400011008110042010758001c03280356665034240b0380824910b0701c2c0d040440303508030241d40c240c810f82802d070380120741d100d840e40c02000140c041b80d80c2c20060104119081e012216505070054001740910341c0d504400d446084540314200341c4140004803183c48 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 400975530 1250 400974280 400974311
    0x302070812073908030712030902010c03030509241e06011202070503130303020304061b020a050d0f020927160308160807080a0315050a06230a02070f0602010c0206060607030201 78
    0x20350b100c0999170300300007124405d00040d50380c241c5c0f841c55a410300344403030f000c280c0c002401500034903006000c00d65034030089001000144598440000e40c11030344030700c1c1c03481c02c1c00c10355410105581601d00c0700990441164010500d072401d0340300f41c805841d0000711000070a40a40a580b052a04a134a0b0100b007180c002017a4090040401841c004e500941e1200d04222010300000381310a02d003aa91000000703c14016510400d040050f00c40c15100f1850041143c40c0c26160196055070003584058020104040b411011000600754680c03020b80c003c418110304070064585000c581604140500b03103200b400800c150300c006181c032803c3d40c021540c92010585420605030003c042c201c0b0440030000c2c3e1040751982c14001c0484132407500200c034440074505000584410000d1080300240104160b01000500b00d940314a0403185c3c900402d00d83e15010780c00000e440700428050400e0340480c8800100e0300c1c600c1403289a000010a800070201070711204200030f50f640001d0022002c56403100c1d0411404ea55 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 400976780 1250 400975530 400975643
    0x30a060507091701050118090812010902180a050306040b13080c0706080901022a0111040b0307110f030a030902060903150a0b0d0b04060b1c030207081207 68
    0x4180c0c0c0300d0800d42e080004169243e0746640b100c0503540e05050050002403103884001c0324500c844807002412250601c0e09000f1400389041c01000b031541c41000240703a04164000704400079a840060341554614030402111203540c2c020709405034402c200182c0081d10765882c140d0480004199551245420307035032000f090748540c40455540d0031688003001a16007103100180c21441c040000d6041070385101080d4982c0e0f0140030380e00c10000113140d400120000a500c040498001604000d9903142c0342c041e4240399a006540e4680040c10007034a14980f02d1000c1091020103c062000d98600121081e02324094041341c603050f071740850200300d8204191380c10420071940707201d0124403c20501d4640d010302c084812030a080c80c01401c00e0060b00b00003d0840d40b0366039100d80d0203480011240d2098003c0b80078140d600c2c0e81842491350700f0303400300289030f0009164401c03100a101250380c0f0003410112003070b2901850200518041800c801015071030075203c03441d41110344a4855028080f0100500d400781030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 400978030 1250 400976780 400976791
    0xc060304080706150e0a1d030c03090a0b070c140604090e1c18032003011e06060513030b0424060302120111190c0b01060f0e10090501030209030a0605 66
    0x1000400b541007000e80d00413225849002d00101d4259403a21102070100000100000312440d80d0b00c840703c0010891240078044401541c1c1200e841d0019802c2c020746e40d60052040921501304e00b40300007044601c16040303a0125900000e007582d110301e0f2448014081d400d104d1025800f40b41800701282112a40c0304440814041070024421302c08034050303c449a020700004c120030040881c010107010080340da0004200c0b54000396091484035448940d0070144c089038003160781035080c10150601e12010650510303034064460410000690748030390a80f02d03881044d403400242c0ba18003c00b00702146c00c126445902c41d01455410307501d4208510480036240c0300d07503608150f50340d030780a00340150b0900f118003c019819803c02040b8540344c0280102e40e43c0202025150010b98841c182d0440d20310868440f1007490344900f00300e8041d610380f50090144000621801c1c001a103034032610703190385000f1001e0b10744002c007525001030a41c24440118007a44c4a2030881b0b4051250303020700c100142c4e10f8441c035480340d0b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 400979280 1250 400978030 400978043
    0x30204051905060307030305090f0a03080c01021b0a050d0806011803060f110c03090d05190605060114192a050607030b090106021f0f1b090b0711120c060304 69
    0x40300081c0050040360b1000d450f4a001c1e600c654400d100098002c0100c513854a4115551142c030b9250400140076907040350001801d15a0100b0f041d184080c054010b002d054040c02c1e010200b0210701031805949280840e00502164450814650054055420603030044810314040f2041c001b04888110f903141260300c22218903a850b02803a01c00803840c40b5080881900304001132a0215185440307503039020b1451040d11521882e280c5404201c02046030210425215001110301960f13030620f14018241120300c1ca01140e000e1030f2060a091410301100c2c01ca445403a010a14001003290464441580d0825280010001000c26000c00040080c0b5131034503100c1c0004241030700c2c0c0940000d0656400000450003240391000503c01190003040c801d555148851030a0545a00f250f0785001401c00c0b440e28002040c41d0028100800c407d617541805180495141d2101c100d6582e0315800c100d02c54458081d00e0018240020100d502d4410101d1b4052030904003141e8140c0901c07000035a0a920a0302d00301c031708 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 400980530 1250 400979280 400979311
    0x8120709090c020307150c050c0d0503010906120237030c0801060509040210270801090507081b04090c0504020f0d060902031608071106011d0a200c010603020405 71
    0x100d90703580201d030107180192018500b0503160b0360b42c40d0b629500c0746170195000d0f03442d518032080c024031410565803006840d900f141e1030b1200c81c0d44046d03c1a8403e01640c4146070800c1404510315999002c980f5544d50b01502d0008007210304500010688400010328044843c0954110020300c4842c14000c0994021174075114180e01c0c20300c4441c00c4602541c4100e00030b00c0a24200b1000d6900c6000b18649040c0b14240169954006802c80c810007040489212000841201c040f41100055002103901845881110a1b450300c405100365100baa41e071060009502003c980042e50400c0d4001d00d5141348610b00824515807070f0000202682c00031840f0300c84882000c141020908054000c0c8001014882c45c01c5145043c50200e6480d400c003146164018484801c001c14122071144c0540704103142810156800c0d96181c0c81d2002880e11031160349a8000c02a00100c2e40380421403241d6140c00c80a0070821414001d040403a450a410200251406558a19001002d030b00c42c2e003d410b00c0380d280e44d00113520 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 400981780 1250 400980530 400980539
    0xf13140f0f15010303051b0c0a0b0c1011090f06040b070b0f01060c02010e010c140f0d030b01021617070810020a1205040209060402030910090503090907180e0408120709 74
    0x203007203216560580004030b0307000100007194011044a40750700c000300e85c41c0c0c100c0c106420840d00c0c126540c2040d40c2c0180030881c0000c4d5880f607203030280c40d000c00d14205030380304185107071011002e68460813511a0041c00821004080e80340c0310f0903111a1a2000d00f0b0107003495550b141c03d10242e000801c0a890007044281004000d0124804240c050000350400e004c280d8042c6e00000d101445101e01c5505001c0503800060602c0f441c01c03405000316403241e08642c000d03560004007079100c810b800001f10100382070641c0c0b18032940c00070600201320b107214004012614601003060a1700100c50848600d1070240807070200d0030b03131340511480b2803210b00c40c080507030f86005004c070003068910101c05201900e85010240001072ba110207050b030700803104450141c2c0304e86522860074206082c54041c2c461951411001608001010001e00a100800c0f14120348039030310b0b15030a40740d060b0041c260084032035044005005a000001c140c81d000f5028214440c28505c420710805402482554a0800305404081c10030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 400983030 1250 400981780 400981783
    0xa1505040b0603120f090406170703230a060513080304030801060905011418060c0703240504080f0a0203040909031707032903150106120c02060f13140f0f 68
    0x103400580650080c01d000800e0b0300131000d180508211209a484000303154403496941e03411200c0504881d40d08140304803a812011561070f0700612080f102207010343d420030f900725503400014420b0740260000c0c3c003000c0303040d90324080181001020741c1c2142429450745004034012358065031040c2d10a0b2074071240e035410000080c0402c44c49034040350410041118001001d5450010758542d0329885401d6a1410300d50750008800c0d0140c1c003010581c1e03120f20f01b8000244603900070707c905501c1066180311a4031071001c2d036000640b5002c66000d80302001c2003100701d008520480c0100b003e1003607441030781d042644511031031041d00e8a0b00320130b50000c3c62003008040849021f0424a0b0071052a04003004075551485150070340400d0707101ea4510480c061124440f81e5103040c0401d401d060002a241d070744641c1c6842028115200891030310f5a09071170001000221b500018843e0b01402c2000850905640c800e031b81041100010345088603103c0c0000a01c05040600300302012110342d00d50081c2040420401c0c049 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 400984280 1250 400983030 400983053
    0x304031e0f050a0c0e2214030a030b010806150307080406020403020303040b0901030c03060501021902151b160806060d1407032405040c031704180b01030506010503190e0a150504 78
    0x4485c000b8940300307204070180150010440d40c0032031740c002402008a400c11514a0816044402c1c1d140000980003449a80c1648110395050098881110030b40311002400956201c0301400341c4440030400204007924050003049070b005204001c0540340c00d41b2503000ca81150415800300740f0075103010411880d603680601804000100600e0200075031840c110000395121070000d154040745440e000c0580564803010300001c0d0302940c0c42c0d40d1030742c0c501c002401e106030340304032469601641c010360450b58904511465003900f21a03481c0000c00346500c3c1e070000c0003281e254281e07088030408420548541020414042c2034001c60081d12004403a541580448600c1000c0014503803c5034906810000000c5524a2440c00c1c3c03908101c2640c50a444003400d012180b16a42203900c0f40000103c1c0c0c52095003c0d038101c25a030300001e0340e050140e5200d0a0055420340029144a801200c0c00404030038600c405a01082c00840c00300d080302c0d41c4108546690020221400f296250151100f04000c14001ba02141 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 400985530 1250 400984280 400984289
    0x4303050a050f0c0d15081c0903120f0c14070f1517150a0305030a03060b030c03040f0201030b180103051605010507061a130f0b030f0304031e0f050a0c 66
    0x9101c0352810040c07003411a07074010710f20520401d000c41d1800080c22103601101020401070091400c10b42ca81c201d0795540c41c03440304075403840103d4601ea114494446e16120f400c42e0b07807040c03c19220300800c0405540e52821a4212004c02400703510f84008201d00300024030002400348007030107a06090101c10350b848900358000074081d500034400c107808190720560454105914804807074541d100c944100400d10090340006a0107a2014008000d000020005040c24001a1020401c45075079145491050008484112180101b840014040750b120f413404600f6520516000541290301c40010740345404a032500303080460007130014000c0280c108213049419510070b00c41e040702c516000008005200b2200c00510380381d115407102003055410f240c003032000342c001810001c682c0403070460b2a0040106240ca4a01c0c14140754010b8000c2c00c000c20581056014503014514003411500c03103074000381122000400e62010144801c01266006030040d0400b03102d00c0c058412a07d841c1030400f0100d000b80c01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 400986780 1250 400985530 400985551
    0x90c020111040803070f0c24020c0a1a03040f1407030201020f1203010b0c0f01110919030b1303020f010f1b08070c0b0402010e03010c09080708030909430305 69
    0x41032000c180c00000b505c6910350302c0244200c00001514083d0040003496200c410702e1200c0e1109826030700e070785030408841d045c01075007160307216031441c0104000303000144107109000624001454504c9003481c011076026018614000a0600380d50746c407100840d8024207400d464105807028800c569052114400180241c4000c0c86a011190f503c40e80c1c40c4018450894050b4001401a803442c1051203c01810000240204400c02c001c18080c4030303a13403240d446144201c0d04112481602004405c00c082500c0e08190710034580c1e03aa90151900c0007110a4042e000c2d44912800c0300c0014000f40103105901e0704820300071400c140c0d0f103e00d03080d40400c0800c00c50240700c01c020030400c0181d40443c4201c1a0b54000c2c000761003d454500060f181c5021001c01c0c5505942080140c004854108050000320f0346d0040480f85541d0366040b10a40b82d00070308034400e5102090b5004030f21013002155400804a00e640010403c2070340c500b079010031504100600083c0890a40b0b403400b1080d406100309640301c04a001e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 400988030 1250 400986780 400986787
    0x16020312150109080303010b040f05042c0109230607050a020a021c021833040203090f0a0308160914040f0f020c0601030b13080a1d0604090c020111 65
    0x4651010100041401d401c1000d0540c1c6403419a10402842c03005241d8001629941e58403884109042e510902403040314003003d180c0011582424480d1028140304c40301c004000c802d24140502406031000e0864441d0340d212126180451002903140c401041c00300c080520107004000ca103030400c1c50080c54002408000d0011819260300800d0344640700d40e04444c410740340c4c0c2e4043c001c1341c1c48503000171000e900000304c3e1b100700c400c019184000a0041000c030600e4051407030b5a0340c444552080c0160a140e1109540744221a50b040c80c2d0040c580003040c070815030b102810f420061038508a1601e6003900091000c20a02c07890310140c20805010100e280741c415140d60070000031025450132504220b000706c1d80e4548000d0090501c0e400348200380c1500d0429551240b01ca918240d40304d10a000c242c0d91340f0301d40004034031010b91107141e10b059954080030403030409034850710640304000c0c0506031242a440c0d0a100140d2551001c0c0204040c240c06800040d42042c258402401c5900b4589440d03940340040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 400989280 1250 400988030 400988047
    0x1902130503010522031b060e010c1103090604051c02030a081c14070503100b030c0715060e040b0c0f0d0c08070c0b01090c2105160302030c0a0c0f120305160203 70
    0x80c003607007109030300343c101800c10b0030303410840650007006c02d20060724030782c60812480e0034040190001c25030100c0c40e564240440c3c0d80c01072520303103a2007181c040300d41c0250108010481400d007502c07980c1402e050005108119007194010a0030f1104184040740d0340c010010340210810f0005143c2155a0440d8400700000d1202e06030980750328070040d00410a02c0004070000c0d0182c0101d60314140075110041c640d9450741042507036101950000f60b401c0301c40c4090001d01051102c40c40c40b9101c201c405104600d1200d440b40d03107512135183c40141c1596031044041103014203032002c8ac030040074803104080b40011954400c0340f0003448403801620440401031850801004a840c40d4121419144506070000711066854020749100ca894142103044825804410000b84040d910082c42801c1141d080f6224400b010011800c074807045540c000d002d20144012201e403481407402ca1462481802c906102c846561104540302041d040b00d00c000a03201c00400c08521803483c1c0c01c0300d604409000460500210 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 400990530 1250 400989280 400989331
    0xb010e010f060c020301230a291504030f030518010c02181005130c02120a0f050a052106210304090b03070e040c0e1302010503040b19021305030105 65
    0x840c80744004000c500c500303d500b595000e601c004100b9101d28100c800040c0f5031505c9400d48041181d8070340d0070628184040c24605c0303003401e1080070360692415021009120404001e80c103040320445200065041c840170002442d07145030042402d0007a1540d030740b500d608c0e00201c0310744079061b41514100701c100346414006031600544101200c0316021010099655001e000c00801d030203602142d40400c95001d00c68054465070301000d0b01407020340c00d80b84c02c4610140c014044d80f064100880000d90000c500b200c3c0903100368054007410701180b41243c0780480c81200c9101016114012880d20400711041c03012070324010090310341e07801c012071225030000c801110740354481c0103e100b90082c041e04d6100c00b1006a50a002d0340b805030291811031150f90415050204442e54640100c05100c84034a020482184600c040e013201984d059440b149507568541e0b841c085081c02902401c0400040c1c020b00210201038009400151211603540307923214500785c02c042c00e445014111172490b00441c144507683c603130b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 400991780 1250 400990530 400990559
    0x11b0203030f0c0904110c10140c03040c26010e0105071409150703080103050c220b0a08031914090a06142205010e010906082404180b010e01 62
    0x10100c8a0700c81030f5503200c214807141d1181d0215039501c907180a050680c401000806030102164000071184210320340240d0390111780780801c0d880008802100090b82003a540c0e001143c1c4a0311600b100500e440c2d40303400d0040840d00b201303981c0a100b5001003102104000c24440c1103c0c1601030802400141018000136140b401800780201d024000080c41460640b15800785204d6401d84011166030b030421802d0050018200380000c840c40d016240082480c0d2800080c02440100c009118900c81c04102c90b0820003002c0380f184254126841010018041500340003600007040c01450480c600f010ba602d00a0600b5040c0000704500301040c41442c4850f1204841e0741c00303443c02070030504030f500c3c0318400c058a98001c00402881800e00d01d45a80c5000e07201d200c0300e00c11140c013030303c80004103001000103454105850240c8000540e20703d00040c000464070300444001030302080d0005541d410000418151180c0c2d0f01600070048558100d541045100440c090041030b5101890315107504040075000041d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 400993030 1250 400991780 400991791
    0x1150e130f06030c03060219140a081f0b13060503040f0816080f040f05030309100f17040503090a06090e070536090915060d0303140a0608011b020303 66
    0x580d1805036070141009980008080c54002468030400c0d90b9918007078002e5800100d080220808401d240700546d80681d40d0082c05206c580801801c015445108903058000105003415400f081881940039840c0c1903820390140c040e030383c16241ea4482648000c0551903295101c03004001c0200204008652038090101d60103600402a565a00307007009c00b0035204c840b0020140003500b00080b503c0740c8400180c000c01c100d0b411200f28152a66441080540380c2c01106034013034110700d51100010001d031040460070341100003420080309410b40e105040100320400c031000c407100d50000402e2541c0346000c02c5454014600c03813501d020418101001a80d0440c8050b06500a0160116100800a4a0103101e41130745074080c04080701000b40c440307071180c444101280b1500803a0b901c1e02203030114101040c04100030111aa035100182c69180c1400705114115000b1b9003015038900f03100c010303a00089034030740c010b860103540814400d0412341902d003114004200f0704c5c05490203c201071f12150700401238941c440e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 400994280 1250 400993030 400993069
    0x1020c0d03080a020f090a080c09010b09090f0a110a05040302150307090b0a02030912010c0810080a110301180302061603020a1d04060f060203070c09270312090b01150e 74
    0x80c1e861008171040c034000e0b00b5200780c3c05041100003064401000428000c40c19007250864001d0741d94800c00c804501c42c3e001410341140c1148001410720341d003841d00a0b00810030701c20004081102d00c94a6441e60404205d81000440c00101001986005070040741c11140c8050aa031540c1040c02c00900384036120310403a6401e02d8003242100e201b41c000e00030340e40320200c050f00d200c801c40c040c940e0b520f00130031001c100c0f203000c46c3d144d1010840c0303014100344160584000e50010400380d0016214940381074000d0550316030540d00c0c2c4170b455075180ca124503504591480790b002082c090400c4a81454010824000e48003018818060010280e6000145586801c5d002515000032007001c4041006885540c0003140c00448001c0006540e03a800802002c1260051406500c2d0075113b405103c10746100c84032003400542d84103c202c40e100c240020010050748070341412030703002d0054483e110640320340007829580c1c03a1100004101c5032141c0390560760035a005140900001034804009001801d1644403540750 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 400995530 1250 400994280 400994287
    0x170412020f063c030106080a0518030405010e0a180506011d030309121e0d11070e161e0309030e03010c080705030604061a0a170c0913020f0307080601020c0d03080a02 73
    0x83c60003c80c0000451620540b900d81d25a182d20010f04405415030340703041802d190500040c50aa08640b85d085409542d00c0a5840c1915000044440214520074650b01800c180c10005d464101081c00d680100034204002c10a45000700c00500291691061325104d0980e03088450340301d55003c01203840010302119005080d50b00f25180d50303d031152003205a03e501021011502154000040301c058001480d43d50f8045c840501e0b020b55100d805903c00c1890706030031302e000320744084010542210703118024031303042c601d18a030950101c1840d007001c030042c0c0c046a07403a000c0c42e0606a01641d0300b902403000754000c3c050180d00c0b40e001001071000030000b03c204440031010880a40c0c0d42e82007030380206030a002c80f0280984528903500c541e80304a101d40045046402050242d28400c50107030321961640b04482d080503002020700c540000c0322010040c0343c95080003140c0f080040800698010059503489494519141002903e400c91542000d442107940151000009901c0600d690344115070460245e01d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 400996780 1250 400995530 400995607
    0xe01170408070f061802100c0c0b0309011e0c020105010b0c0a121101060303081801050103030215040f08030a15081f02070c08010c270b0a0c170412020f06 68
    0x41c40d103d401e00042c005400e280315800240c030904d804029590084604103100f205569040e01c01030743c1c044d0024149020708500b00144400d04010303541c001c1c02400080355201c96140320401c82d078003c0804c520b4040c2d440c050407009580c248146405440703a00076152030701d660040300c00e94520700514000e10801150140c0a0224454900d5070710800b0410024442c1c240c40b8500600007200464030300307010b54070303110040740c1000c81401147e04880c0c258024001c0b0b00b03403805102c42e66442c02401901c440c000028018001030b50000194410022804001550301e685480e2401152240e0300060160748460381b5420b005480c004040070072003030b000700141d41c0c0c8518503203101d036489180c3c0041d01c203520b0303d6005222550490b4814520034011411002001c516841000365440d0398007900d0760182092090300784e8140a4050b812070640901c505010306407080160f8100c0d640940c2003c00364006900040045040c007140c9071502c00c01c02c42d18070b420000380c1e40411744090000a11342184c046121034401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 400998030 1250 400996780 400996793
    0x71809020306010e040f06080c1903200904060e0c150a05131a031803070302060105010c23010b0102120702060a0c02060417010b01080a1e050a0e100c0e0117040807 72
    0x500d0b0078094000d100690486d6103801c020309030351040110038000c44415050038640360f0344c86d561400c444030701c00c461030b41180c039503055610044842250001304020361007555035400a219120354800c18005c1204102480030701e00b01144c0b10341c0c40f402034810038400c40806071038130141c0300e402c41d803484d065441c1c10b440d41d010403903103010354041140010711010003d00d8148280086128091510000d0032504000d40d0481d560303c100079000d001604014014085507200e4400e07521490301805944041215160300704c15104c1c0c200c40c0b15030541c1c0d980c000f041950f51301400a0640c1d078200882035820600142c01090542c441c1c0c2c02c0c0c000400c0301d441e060354215650701041e20301a1941070501d0020642c14450580241440c42041c1d020a030700000103800c10f00c4500802d02d03014fd00390748225040002e61748850182101501380042151110809040c9400800030350704508041040801c0c01d0f201c050025212001060229041109040401c441c1a408000c6181c000350301c210107966500e240d04006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 400999280 1250 400998030 400998047
    0x8090f0d02011d0402070606081c0801030b01030f060f15170f030301120203120a030b19050d06051504090309030b0f0105151e0304111807141e041d07180902030601 72
    0x100500c2c50a03001142031240007903980380a80f002542b103038411800c40025516038409110091100c5196801880010105840741500c28460000480c100743c0107001030040c0c50342c100d043d880c0070072025410000c0049034258410100c941c84050803600b004110401c0d103a1205000e40803101c1c09802911003151810807110001c1030200301880d07180c8080c0c00004015101ca03c903150b118030310447c611076076004010524000c603400100010050300d03186e0740e0b44e0302400d0300424044680c00b0100310414642c84c0c502070301e00900e2190355410042c03403d518080900c800003803c41c595215445006001586545501c00349100e6065003c2d40c07100d40c850591286201c1500c6146910007000c014441008000402e00000c4c2c0801c07a04d14201e54030342803000300f119604586440024100e941c1c0260a81412001029a03e4142c040d1600c07400c1d9924034114954066031101602c0008000040450501112642d070402140e180108500c225007800d0040303000e5078010303061070f66400030100c2c03180c0c2c0c0540c404 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 401000530 1250 400999280 400999283
    0xf081b0f012304080a080a0e030d091202040b0a2904080d110a05150604140603120702030f0f0a0308010e0f040b19050703021b0a0b220b0408090f0d02011d040207 71
    0x481e0340e410b00600e4018051381142c401800890300c5c8c0c1c030f861102c034075000ca84440c40b040180e590910481c42c0c8110800452621a020f982050351a01481401d0f02c13102c00c0240940a0068440d05a41d0016503070f186010742c8902c04c90111100380014404080040b40750b0070304000b03900d001850810744010b040e040c481c5107540142140300ea03807100502d6400c01780036103100d107004803001c0010000c0e40e40007218004003118003e5250300107072611203e04600002900245001800326030114400c589810b02e09115051140104c1d40040550000c02d98030810403809400612414551401c000c1c00000409801030801440c0c0c200400020341d00e0304990112414881e10741000b440b540c05c02d890050002d6004040380100707040444210b400c60800041d1158009a00100d4101c540da01c6855400b4500f9110407498240101c1d06c0f6280086034005181d18042c80c012030300c071640c403c50b00041110034110059036038003071200c02e090400583e030488684e0f41020124024800a10b10150008000b8490500c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 401001780 1250 401000530 401000533
    0x60117010905010303090e07090504022a03030402040e0d021506010327021201061a0c2406240909070207051003141b04060311040f081b0f01230408 65
    0x2804000710781216049038001d44640e404039848191b04207091a040341d0002c00b142007004100980d0500d6802801610a10714800d42007900032034485120184011444003030390310110034001585818031941418141034401812045000e000c065103840788108802140301c2c107600020402e074081e030840200c0441141500e00e5407070240102503d103011000b0143c0c09401c4101d5641c210079014410ba605498a03440e00901540c21600b03114526882328810032094003800e5034845204402171072440c0c5d2070b407020205800a00e030500600449003000c112843e42280864640f042c00c0000700101e611842c801c1d01d00074441e030f5543e902649012100da10064004170340385000c0702c840f0f6056218540155011003090615111f11170f070309900002104205003920000c200070401e543c026880b03c5003011002d40424207040e9913007100c10303844081b644120500c0d040b99106010b00020681c1603910084126000216405001c0009002e41510091400c02d07502050803a142000301c102070318000c0c90312a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 401003030 1250 401001780 401001827
    0x100c1403160f05160206030c0705011407140426210c100b03061f120c06020f12190318080c0f03041a0306010507021e10031808030601 59
    0x99400d9510010301042030000302c090b001c4058880c80b42084500c4c01203222507002643c0e41507001c12005500181000aa0b01010842c941c001407081c0a50400210741d03034a604541d02d04040e01418080058160b556406030800040c40103040300103060355076206021540f6010b00301d40701c00500d00141d8444a044207182e00b03880e5610918118018000032403007909840e50f09860b54550f00a49031403c05450741504500b000034045004036034525800d200702c1c0744410724030b551038507614082507011000307440c414000c400600069804104400300b4650001c024046480e0308607000c012800348046a4208100c09803101e1021442074014007a1050a01d03080c0c1c80b101c1d401e14000301181d010f0011524180100301c0e0700800340f003011041d9001c407500ca43c5d25042c1c1c55035444e034814103540300800d0f5605202c0180100f2000d030f280e00c03035603000c1c039140200341101d58900030f010000c0106105c208642010308151000171003840085040002c1035110400b40c0c3c594440c0d10052b03401038110400000b84000781c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 401004280 1250 401003030 401003041
    0x421020a0b1b0a050604060c18080a0b0f0f04080c0f03030a0209030c0a0806040803071b1a0c0a050702131121012c07090f0603051602010608100c1403 66
    0x103800030040c00484524001804692410103a21400820f4024200790000320000d800308003203070404000d072041880c142d03400314104d006800e5880e280790048612507000014000410012810b0540c10182041102d40c103407805292181c598540100010009400494000d010b00380c20031084c100002079409607a181c5c0f40c242ea041d0002e42210145a03c280b0607a402d840ea203003031401103a802d0715803050142549036200e442d603c9541d40050241d00400c083e0358514800b40b2407040309820400d00c80d08100200442040600400309409456041e40382000c01c0141401c0390010b003120386160b0b040d20300c100c942980b840800300600c1c0d103015080c5540030000d041e91000340300090320002040300506081c0d070f5988a480381140083c0e4451003032901c0035180301300326000c500f40103403a038400b0071403134040c100b551544d104000115003035100402098590051201082407208d244810000c00e20003002000d180c0900300755103001c141d0356407007199a10004820282d110f4048a00c1c1000440c100560f41d0420 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 401005530 1250 401004280 401004299
    0x1110a080a0b1f080415020a03020304020102160b0d0509070506030133090e060f150d1802010f0f03020405060a09050102061f0b18030613020306090d050421020a 71
    0x200d88101e001c0b0724281080c0102c1c6001c0b030440d02c0281d00c00300c20000c0741403651001d81d0b4004025005031800740310983d00f64100c41c050300040282c240c3c141d03009a00d0342003030f10000e480d02c1030000c1d21803070f0482e01e01e60600c000d0001c2c01c2501c51803c0806e60205441e1200004a81800c00c1904802d404c81c00000000c14104190304c16210480610442c0700070000c00840743c2d42c035079000e2810400015030f44880800607070050060658106400034059881c44400700002400e1741500d04078040e1030200401d10361140754092084441e10200b19503c1c0c4244402a40005c04642d03810903801c0500544c15101c2d038180303100354180c6002c0c140c00b400450b80c0d06c82001d0040e01c4901240309490061164100003402503501a0346140a00400303940c2617206800c1100035011074010940b068000c3d188a4000f40803540c0810950340100b40d20408826282e407107005050400d600244005020351000c4403007041194000111804c4401014140b2900745035407113600ca0410303011030040e6210289050104104c040c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 401006780 1250 401005530 401005547
    0x30203030402120304060e040e1c08101212030e0a0507030506010e150d1101050d11030a060506070309140f0907030c0306061107090b06120103030201020903010f0621030201110a 78
    0x300d8003c20000d1401d60610780da4070803801100d00103003026241d8203040c1460781202a4140c9803105660281c9513a140300c4500c0c1c41c010460000292900e01807024820000200c0c4015110b80c4084902880d960b84400c92080181d441280c2016070324154525520010f000306032850368000e00b44c5101e1075490a00554504003801a404010031203008242c074400652103501c03503240e0241800050010384e48860303202c4845800f98505101c0204120b031481d01c494862134510070f1004807075035180d040c1001d003c0c01b00d4070542c224900030102001810040fa0302f092480d01101c070f221240201590190003c1001c84403041000da4115a41d00140016150150420b20042c0e040b5502088000d54420080b1a54918040020b629400003202840b0b01905038116224400d409031005140690480011141034001d92007580180d502051010070740c9401c1c06070210300d120b144001c0c0050750410005414000c0380c01a00448003403881da108081500079001800c0c03604518001d01c1d10745d880284007402400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 401008030 1250 401006780 401006783
    0x801050402010e010306050f01030e0c1003090b0604090201140903010204032328031808070f0911070210030c020c09100611011a06030a0605060406050a030b18060d0c0f030302030304 80
    0x490300a0290f12a5110388102811200e0060140c51003100150054008001d107103141c2c1010701410b03001014603202c5a0101055500c165400207044415050044094501a099034070450400f295000940c0e070228003060300030b58108080c1d558a1188001a009206a0780001c050400400701240d8080040808030442c09940c001d40d420b00703000c0c21042074101400d52801c2070141e0410f05500c0070034410385980b98403600e401c5000d02c005440e04070903440d06240754440f01148007480c00910644070580540318a2440410b15a410b04c81076500003080c804401c40740c081015503d200c0e40301c006108000411405102420903442424503801031078500c6018060350021440e8100f132608050b505220745004114403440340500c0710b1606040004640c0f000e8034141c0d455450354001b09282da501c0000308010200c84c1c441d15a02e28140340040c0c107540d40403084522a201c00c50180382181c0410421a5202070304648407114110320b031401c0c1c0508942e40c1c0140400b046210004820580c00000a60285 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 401009280 1250 401008030 401008037
    0x15160306030c06030212070306061202131d04050d02032805120f0702010c02030f0a080405160906060914030c0616050f03092b02010806310c03020708030103170702030601080105040201 81
    0x19500c03001d0030303415032740c46104560004144203031003030940c040e60340641142c60348a507a88280c0c40e980d15003050b40340850f15070281031a0704c41e814442008410010200c2030300b000d001450030030300d40315800b1014100809070594885040d06c201c0803910b00c942d045941039076020002d18007505003030300c541d50031210448041d00550702c0e1000700682103000000740c9028035002c4003080d1800c000c400084032001005001180e00c0d00c40c8032402002d408003d0100c001510291000103140703440c1150003440ca54203684041074107016048035041c3e645021030010610f0905542c103c0e5544105403423038042c4400b0160145c41d500844120340140f010120052000440442d06501d2105011000d407406001d407044507610740d004e4003584030065000312030701170780904018111100e40c5400c01c0c0d06038851802d03000349000b85c80c0580c810318203081e092080754442c4083e85800c60070100d51b5500d4500038441800040d0189602d642c0f202c4504804500f2505d625501a00f950f5065070345044c83d41c042d04c01a203089010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 401010530 1250 401009280 401009317
    0x9010b0f060403080f1e0304260c06160210060807050a050901080d030e030d0911010801090608070605070c0305010e070329010501030b0f03161715160306030c060302 73
    0x2850090107031010f5980201290b40307000a07000000030740d548194542001e10b40f404460300038408903000510302c101d0040310180751402810001c0c06031001c0101039103210b180c3c244001c20814400250013075000303000201a200e90352a180b01603103812103101d1075100c1182402000300d019000801d1040c210f500c1510406182505d441c01c000c0b108109000d0941198480701520140c00c3c480e0304520100712f20b61b400d80c0d1419454007401015920412000d840c4490040d0882d12196401300c0d07071500400c00034000b00811414168419243d100c1071259000f0040003003007d4040c800941d02d072200566000c402007280007410503d0307a803540754600c001d58000050010390001c101e070070040200d00341d000d5112650305a00300001034008160082030f542d0071003402900400d05d6141000031410550003010321585c1d080c038111071a010000b801581c0c0300f468201138121599440c1c2410456041380c50b40b029a000c0610080c004c400414042d440506818a05140002c420382c0590041058688030f88000c02e4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 401011780 1250 401010530 401010559
    0x40b070606083007020a0306020901020d020604030e15041211030d0507020d03050a1205091c030614060307050f0a05040918030903030516020a0830040302091005030609010b 76
    0x102c80440f0240700b14070580101840382401080f204460030f254202120301d007072003c1600414600c0249030012143c00ba40080c1c210501e40c3c04015050340b010851004004601e0703d980c1c000c0015480103511070060200040308401000304905071405070044400b80500707c0c078541826051801c8030780e401c0b03000340540300c001110544103504a68616030080e01c5500c03504c41594085500e83c1c441c1809104004580c41d201c3d100b03405c00d000b054040e01c404402490f60452850001024540032065801410b10f001400c10040c007034280d0101e24804201d410030b84a0341c0300724040e0346500c154416142403010029035040b48a410101a0082e900c42082c1008010440c40b60311244041410000d40451300c02041040000e2089000f440308011101d02c090140915030701246ca08444e0344c20800e02ca03044202507801101151890164094800a40d1051850101e0703049005225a0201900901024001903919600306144500404000d012101d0501d000c14566000b8648121400e2159080540508 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 401013030 1250 401011780 401011783
    0x1b0415120b04020907051207080a02070221010501050402041a07300807050c0c210a060209040f02090a0603090503281e0f0c05120a0c150920030c06040b07060608 71
    0x128120b41120b1f4401d055180d01c20181d581d158024407d003803080d000c00801005854002120200100f0305103004052000360588500f51001600058040d42c4140703c104109011004908280c810460459955034000d0515200e2060000e80f140c07401c03858220740032001c00c15858205200c100030307924079040c1d4541c9002103440344208540f0030000c2d413145c4104611490444030405551100c151110303603504200400c541040004282600c080d0303808640340e00d9904043c0074005101141202c2140b404a8be040001ca00c1d55181c0500f50816586261041c1001070400440e080c854481e078600340788891a95526958011040c28600042d00c0c10304100d15400300061a05400700c07651310340d201e0002280d03108449030451302034103031650300c00e1204619074200008014070424150f943c07000441042414840280c0750b00d0b21000805618080380c80b400701c0c0c02071026401003111032070311b00701014841f00060300d051303c194a4070340d10440000307002940701e480500401c41148140002c3c8000ca45e00c01596 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 401014280 1250 401013030 401013037
    0xb160203071a07121b0e0a030203210d02040e0117070e1b0706020f0403020a1403060c0f130b09040b041b0f11011803030e1b0415120b0402090705 64
    0xc240318403085607803610b04900c5070502da001585140c070920f08000a4000002d03100500d0109103100542c4401c424501e13800204072a00000075034410741d8043c510740c00310760b5481e4610443c520b0700c1e04901480082c2d0200004807400404909025034843e03894002c40d0650a2007842020002882d4004070502d4000c08600f60b130403114074200d01041d56807003010300f601103a0b400117840200f041c10000500020000d00c00b8004a1030315091982c1c640d0b082d8030521444513066006025501400d0001842c55580041c001d40d000640350400da44503a030004c1502d0440c00303200c441c08054849480045040c0e4114030141c8110181214280112280401071004039004e5100c0304605072503098410400078003441d00a1101c60b001c0ca4120070031f1314041c0c407882c2101c05183d1440040b4001600010906615010b5840781c05d2461001e04050030401d0130444002c0c01203a081b6000351703100d09102c4055868803d65200418890b812405154020b2030200b014810443e402c030b1161610751b010810481c403a000307a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 401015530 1250 401014280 401014283
    0x60908030a2711010c0203010624111b01051b0a02011b030215091501030309090c110a030e04060902390a0f0c031a0f010e070903060f060306090b16020307 68
    0xc2041c030b0095803180d0280500844038503062100300b05500d001070f1424400c20004003240b4500c0f083c45104074030035018140818058070100301c004840302d0140c003000324101d11407921014020340b015480000685460103907540c07250484032040d01c540c02c0040081080c18005100340c0c6c0f4081d04600001000403000b021203070250060303100c849800c444010110a59410820000c01c41d030041404034bd64107840c01090301b00302c0c0042c020080c00c10540009001e4403001c150345041207000810320101d03c5d076070780b00071100240030072100c0040c40701c80b03840b1035200700e0143c200c5a409654071503c4445045d1409514001c2c1c5c0812006100310300a05001045139040c10488c1c40e000e811143c0d2280c850ba0b5084a0b04201503510f01e480c0320300080013130a9031180741580c20f09040000d100c0d00d0141c20080c0440c905070301802203440c6035001c10070034a50100c5400140d0b544080006001000c8024183c0207010540000703000d94a0044032201340000749990358030444861003d14550302517000c0417a141d0003004030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 401016780 1250 401015530 401015591
    0x1030c0e0f13020a0903030f0c0b07180306020313021318032303160e010201051006030207030215041a01141509121b041a1503060607060908030a 64
    0x8403000c451818801598581000070201402c03814a0360080c400c0382d1110010070040b55007803508100b016007040508548140c2400e01c4000785983d030b1511090500000e1041e010002645081144a003a012059001e1504201c08646900d85004c2c51101c28a0010082c0e120329602010b05034114414068070100140d0300c80c209240060700d50381074489515564182d00091446401510402611000345224504580f03010240420451019000188583e5800e045904000c100401d402d0437461343c3e012600d03d40f90060350b0f02e400e410201d091600340c24480b18407101903000e000600a58020051a0840002c0c00b03c0f91a603a07043d4041c3c1400001480607002001e44014108084601c0d0240c04000c07000b0701800c42d501941e00c2480d00f45400d000100600501d21a5a604641402e2040c4c8401c0429003598080180c00d10000600c800c50b21140003800308000000104580c440c00f041d1298194000d1003440710b210686060310352504115110700d00d80d8600b40c503900e910622841d01800d030021444 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 401018030 1250 401016780 401016797
    0xa141f15060e03030d11270d110d020301060e0702060f070915090504151712030f0a09020a0314120301180c090b1218011413020a05040c0206090c01030c 67
    0x40140d0b0b242c00e008001076410b001c240140001c407520781c041e10021030507008036140e40710030114601d5800c41c101c1d40d002126a45096400200d512600f49031003030309402400c3c18500001080c0020200e140030b071802905542407160004044841c40540c9001d030960f03400b40d400503603a1125041c400350040302d580c4001501d40310108025229405035603c2200c9501c3c02c0300070a0b0b1540089400d40d0500031081049881c400e100304200201459588800c141d05409040081083c8030509141e00001e4000384101e0060340c041000c4010359031000008981c0502040c0c021542d9041544c50b14042224400b8640107504250090010850440f4165894018100e008000824101008081011081d010300c4943c40000c540c0e8560100a0319000f003050503d801a481d2501c1c0c8009901a800c0388565030380e06000303e05042d54142010142c2c4003058030a1000b490144d0b00015400041540c009500f052404811042c2d169010074054800e2440200302e403e88110a40110100c3d8118444000090b1206 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 401019280 1250 401018030 401018039
    0x1050f04050706054e06010e0127080f011407050a111f020d0b100516170d02030601180609170304030812040b010603110f0a020a141f15 60
    0x200041c142240301703485915501302d802c000c0714581c85500502011032288440c880107a904070a5501d00654404ca001c411080c04c1020000e404111080c812506010b6907070802101d40000b880440c22a030401d00d03402182d0341e1342c3e94807151140c0d254641150a94205044003411280b4035065030b0050030140d44191900540d1034084520200d003983c084618080c149a20b20820746e0b00f000580c0c1030702003e1005035503241500c040070440b003044201c80d0003044411329519029804c6401c2d603400b00c081c20309450007640c9514240c005c0684807120030038144d1001c070305400c1400c100d9000d507101d00c1d803e803030700440711840c1c0b80d004c4e44002c130b035204201c00106070072000c0c030569078144000f03c030181c1401c080742e0400b502d958900c840364000003c1010594a500204000d015603420f500d8010315240c00c0410981110828801c45031003010340e8100107400000300380091501c00c010a84615802a0410244091410400d0b88071003200c681c0e13920350340004521011900081c86280c0c1401006441c0024207880c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 401020530 1250 401019280 401019287
    0x1504061d030307170c100e03030103060c050f0706060504050603010b0f06130e0103060c020706230307140c070303031a180408041d1b041409040c05030d020f01050f04050706 76
    0xc0404554160006000110004841c3d4030080e0561400200b5161680001c2c241e42c4c6c60202800701014082c2d0404500700002240032046a06594110b6400321700e58400003000c0e52030348600c1144500c451070001e8402c090113000c1d4400030070744000711018010780d1a440109801e071002125256889154030716810000d25100e40100010302802103129a03541ea501c400c6000710800340e10a4501c151980040c011280d418040d02014004030306050214005031218260480c1c403410641043d078500002055071140200c01103c034014a14a500d5039424a2840c40c0780c40b01580c0c4070880219060040b13030400420611224800310001a1444403588440d0164a910f03040c050020303541d00380e0402c070214501850030383c24482807901d28070ba8a0a8246802140281840f0b400c0c10742c580341d020b001c10304c6104280c10f40350000c04801c84101e480f0307890361300346501556815440564144200b2003041603150300441d081421051100013003095903240f0000900032201110010301d00d410200003071014500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 401021780 1250 401020530 401020577
    0x4020102061f17030c0114090a030f05300a1824020a110d0801051e040e010204090f0b0402040308040b03070302090a1409100b0901120e01020f09150406 67
    0x54040c0300100c0c0035680c000c99100d1022a0f07810710320344d80000803130310304001d42405401c41948200a102c0b4070f9140414483d512040207082c01401c00c05102c0381c1c0d4080c58403441c02d40340e0410f840e0900d201d60302248621580b045483e02003034611018030000003030303055680d03104140c0e400c01c0c079084080746019140d84200c03655501014400307145c64120280c00242c5c400e0301c041d10a01c1503603190306c8540d620782c503134036480e0034100344c41207081240c1480148690b841c1d2600b0740e204a030b0940090100b07802d1120000700900380046054186620101e000a4a0013268000c40415880307031000b0442c811040c01484160311603400007074400a002c11040110b010000c0085901c81400e280040c1001d80705d43c0004c44080b21540100026112586d090100c5d15045503425088010b500302d10119610740007860311180a42e0400505000b01c0905124030443e00e500403801b0145a040210b60300c0720100802a03064122451050060304000c101d04010441d8000304c07410340e0043d4844d11982038903203100114a01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 401023030 1250 401021780 401021821
    0x2030406210c03050916060c3f1706060a0f0c08070f0c050907020a110a03051501091d0705090406020d0e071502010209090423060705030106170402010206 68
    0x1049421840c5003a51142c074021550950b00030a4500b0010400c03450014501c454441c1c41c000d003081003003141e42000d180218194480300c4421224222034201441500000e8900b0960441c000e9140382040c0740b080c0b0b03854010250325880d14040e08501c041d0310224003101d5850300312504000510a5078050001c48080089624180d6080c0c840b070750300c0c058603411041d0708480385080711126104020030700302a60042d15080d20f0280c1580b410a0000390f4a082120303000d003500400c40e001030701780e84640d09030f04051a00901195004008000d4003445e0712824403c1800709443c050b104223101401c0c0340303a1031240078107000404284e810203040241c280405801182c840781d00f00100d01c1402c141d0b02815102e0406280640100742c41c21203664030a40304014620116481000000190ba58054105030000e8010080c2084000509200313501d40389105070b2586c5510820007001402640075000354107a452039910101c2c04140c0048615204400303403030007800b41c3c0114002800b286d010400c00d04042 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 401024280 1250 401023030 401023067
    0x9170307140c030f071503110d0f0b060a05040905010b03010b0304031803060c0203030f010e0105061605010b061317031306050a0309200901140127081507020d03060602030406 77
    0x2204940081c3c50010046030000c0b0310381050004010303500c18034441b0324003000e544c02c091140b146070000000e89445000c022170421070381da640044020310250700400725060f000e0314455031104114405441c1d9007151188454860031700002248207180f04003640e04982c0039007141d03030454450342d80544404480120415a82000002c00404034525009014014020340c0103103030b0321306080030300d80b000d1101608226400007502004212903119074084814041149072140b074240c82c2417134001e01400d02924996480400810000a88021200c518041743d000d12441c00c3c3ca60b50300c0c844107489020b41e03110f80340d40300b07801d90301082000d010710001d108040e258600002c80f034030390751f48800b520152000f40d84c2d00313080404458950390501a140c10b0141039601d01540c800304a24000909040c10a06203843c213003039500c008000d1080d81c2280c403001c1d000c034105480710965001010a44840b0840c0c1c000b0041c40b80100d00800c1c01d000380304150030b903100365014515041c107285040c0d55461050050030400d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 401025530 1250 401024280 401024293
    0x60c17091207120215130317090705040f02131d010608060604090b03030d0609020901020d020a051c0c0c03060519051b1303140d17091005040f050a050d0917030714 72
    0x52170801041e10780325000400000b40c0303101d62824020500400140c849024801200510101203400960031049820888002c100110203040c0c61003c1d0003044803d071203402c100c0c0e0012400d4007500c10040e50025403041c40a049a0340c072001121061401da401c980c11213003c00c000d1210071983e4202081d140750180407246032800170242d1908484295000c80c0c480755010412140039070781401b007200c00d0a010701c0244080c00307898484540b5000360080c4d11138034000300005001c86601501e10fa611982c2c12901e1501c40e0380d44c03170a248010b4101112000d0f00c2105000b0741403c1c4500300e208203070041040c02e0100918441c5d80e0b488001703951103403c1031141d0107803290b000400540b07840c42c2c008000b0b0320040a415000c0003554040c081c040c80f001100c41003100c0800b00720f862003001484c074000c0307040d80c3c80c007080c0c544903801d00d640585441b03840038205015070f03001d801c144000040d55054604103a41ca031855555a46104542c00f000c0c8a20110160410098100442d54403926618003e2810041d24207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 401026780 1250 401025530 401025553
    0xa090503030d0905010c020708030417010e0a05010b01030b01090e0601080a0f06140f04021c0b01050f0706020a0e031f02071509030903060c0302090604090216060c170912071202 78
    0x185802c00c220780040c1c541c84110714420000300b070003046101d0150b4001440c1361818240d04503100d008500034176000b124003243c81480c00a094110381094852032064680c01003040c20600d0103482e40e001280d020030300302014505c4951248048008a40f60101010001d89078140112840c0c1000b40900300001d80314540040110402d1040c940145014021040e0b400d2010007485103512003c40d18510851046c8003902ca0603011940a00b4048111000000c0034440d440c0161054000d07840041e012910100d0403c0c00c0000b01d600600702320700740b5100c08201c031425404144d51a02d04202d00c0e80c8039501c4440f04600e00344903401911001d4410300c107641440c201c0c215000201d070190072083c1e0009504030010024090b492107141c078041020700d015464682407001090b014450713842080f4010303034002001410070a0544900c080e440c0e1212081c040701e410038500601104518100811003882c103008a1aa038000190785003101c200718480e6400e141c0a030700d03403000b0003842c1c0c101801580290000000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 401028030 1250 401026780 401026783
    0x1030f20040503010b0312030f0c04030b010b03011701090818011e031407020318010e01120f06170303040203070506480c010903080d02040e0a060812160204020a090503 74
    0x8404008000040c0d1590b151000301401e494410a116009800c9081c110030300b01142d0040700d910040e0006d11000039221247d04211511440e40302034032100701d12001280e41c80300000114100d444002d80000b030051407101c11802c03100031000c0101548020010b840040c980c4c140b4481d180700050402010000e69403010741004031026901a0010382d642940b19038040c01400c1e410341107005440114140039500648018507100c01400384e0500c8000e5290b0050baa2044000318000d80c0c0060303090140003a42da074050090315032801191807100c4184c0c50020342c0080081560b02c119001001004a0351500041c0a05940700041d05400d111100c0d983d1a805105c0800c0040e054140e00008000c400b4509000d805070b80b25a009481e00ea00800b003442e6041e030303002a8120541780c100036070942e101001400c410082c03081d075010303450414a6408010101e2119803011080312400c0341990201c00115085410b0f078400e100504034000e40d4800803102500b0960701415540c54641010f01e00c290302c4c0c00019 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 401029280 1250 401028030 401028071
    0x90417040911030423030f1b0a1208070311090609010309020909030706050c040311040b120703030503010503071706010b0d140c090f040e0a0b042307031a070e01030f 73
    0x51444400041031104101d4416002c1d40305c1c5007030441d800034012001420580324403416814001c1003501003181c505100aa0303000307600342d143c0882214861006494608018078510185c2008a200e4400207402da038004d0141c0280c58031410102490050b07403908000e1260085c1c0300306410156a0610280181c60300d40d1403c0c0100207050003540c540b17489103080c0050b644c00804035420064140001c0000455980300d400c00b12200f00c034081142c017100c90100308265411480064039200e5400000f041c10740180065069550980035071300090f403a015080481a07000904104603840100108858103c075405002498100c42c0c1c0070401c07018080301055840412350700074100260000b09544140327028132a968140c102901d01340300c0300d0058640103888205404020b4008803011000078200322240d0008203012030903a05024411003668452a174030030b02030004071080c10322004a580c00d4080c0c0100c1c0d1b0310489141d91603412542d208401180500325941e1707285805900c2c0d0011101d007112200c0740 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 401030530 1250 401029280 401029301
    0x510091d0312090c0607030509130912051b0d0905061e04091b090e06060c03070812040213090b0a0903020c0301091118040f06110d0e0a020117060904170409 69
    0x6401d035042c81c10f0b605040100c01c260300b510a101c00c02002000a4100056813450101228002c00081903800c01c4400b034005000000c0283c510f01c52044090380d081400b034a21551194030403c440038941e043e07203540d20480b08207500410b00f2900100291310340704009108080c40d11000600310841000030f00040d070015004000301d1a1a04c00300e0104420034001a2150b2195140618406143c4000e0b0000260302a0506018407000aa900540d90b070400403140c1c0c00c0e50052185a45041c994102003c880003504c0880c8601101440c00d40c3c003048034080d020b0f400d9006084000c194a41f03001d4400105001c5504078194090982080300e60b0b50700780b1451040c0d42c0520b210500307800200040215180c40520101560322091092202182c8a1406a401d1980c081800030368000e1082c11071403035000e01e660748072138141400410f409107400420380b0562b15200707881d0555030904070f0f110301d681d203042140d030950011800c00c00140030807000032903541320b14034840f4120f18098580310340100740d42c4101e04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 401031780 1250 401030530 401030557
    0x609041e060501080a031704031e14040b04090605030a0308070521130b07090f21080301060908010b0405010e070315180524030a0f08040509150307090510091d03 71
    0x140b00180341e0007c0c4078024813000c800b0704086501c0c1c0340d80c020b08158005225100d2400d4400c3c4c0c03040c03116001e415140004442a6201a296035403101c4e0600300764840c1c003e8400c03290070100005201c0c1070000f1012202640b5859854956441d40800c4405400c0399880c0d15040007400040942440d040301901e014031043c1a00c1c03c881c208606044400c0780024101504101007641e0401c00c00c902440c0701c3c819680c54240c04400c1c01440340700324904800f8182c029140300c400100018001c1e41100041048807101300c020b0040c50403803c00c00040303d2007489001d203031022400028032070074803075441485940708140030364a5032600c88405014034400e41200200d041d0341d503000e120601400820312a074007014190340c90024503020380401c0e11881c111708003c01c01d04c1080b1f00e6000f084002016a8041c0c40b001e01383e0482c2c1d14040b0302e40c149900c061441d10b4000d000f8007001060a0340300c1e005c0c5601c28003081c1c2c443c0c0ca41614040c0703400c004014000084c0c9007440c0d107290f40540d080060005000401c00583d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 401033030 1250 401031780 401031793
    0x18010e07020d09140d051624020102040b030609090a0611070308011203140715050403030603201e0607020d03090e01120201020733030c0909050609041e06050108 71
    0x158041d14201c1c031114480240240b21000708030562114440d182c24600517038074104040814581341c1c0c1791142c0041d510980c030340503c1d00801d00301c5034191400d03e90360341d201b403070700d55088001000c0e402c0b0b100314041c04400380f200700001201780c00d0500c109a082136151044400e05049510b48604840078080901d1031000c1c009100d03410f1580c0140114090b0100a00d5040340302203641e0701402ea0a0703002c240803200304004c60010107010010424560010088900703000d24641450014014002c5020441d1100300f8480a004182d0343d40380d1540711008080e01c0204050708402202c1b0b007503c00107164541c40036040041c0030041c0c9407940404800c610030303101c06500390300703180890721206016004401c2902000784200090707a40003603000c04541841d10800c45412001d8901507040b10303900310070fa42c6210515030700c050035130341540003078104041c035942cac40b84244e1214a80415100e09440e00d9501c003d540e408100400c0900c010601085072054020780044201c2c0d860b02d00303030b83c0700340d000303081139001342 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 401034280 1250 401033030 401033041
    0x405120c190c05120106210c08070612140708040809130f200316050a0e1809010506030328020c0d0506061305040b040f15020408010b04110f0a050918010e 68
    0xc06038403e42011009100301400c0c1601c0300140032500b40305481fa0f40c3c1e440d00c03900a00c0304104c0200043c0401a09450b8002c1e1a02c801404050394404000700703245c80c00b12000c442441185800f4010681c6075240440d9840300d441c4c0c604250802148140e00c55203031101104424094407502c95103018141001c280700300d110b00070740b24160103500e00341e400318020020068801f6010303403403031240d901909041e500c0e0401100c08852000c0307c003080641081c3d043e161030001980d103540061103418010000d00c001e60b01e4506040d2a0b01071070700380b840c2203180c0400e040d0b064103c0345002c800300501841222103084a52000803101c052000c01603a141d0814005c4c09641c0c1040c03240f120070300350881c00601c6036040c00ea80e0300c0c0c480240100041c0240c0f9103501d1a03020014440c1d030328007140c43d0481055403078544520301c450090900628135403259140078140340b0b80c0b01c1c0d90002d888248034200f203101e080101104060740c031548402e070031660083c1d880307003009014a444030009018042100b4100c0e03940c50302 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 401035530 1250 401034280 401034289
    0x81f09090c06030c090b0d020906030c09210c040f11040314060603011a06070201090308030c0d200406180302180910050c09010309020f0603090105061005030405120c190c05 76
    0x710340003801010309004070110300303070341114041045034541c0454594407240030106c1002401050140c40e40703c4400801c1c07020b41081d650103400300e10b204481034016038942e24081606800200108009500109085c0e030f214506a80f10221004030b100c40450701041c00903454689a1086c0c104072005111038440c00f0148004110640d803000042d0300800444588501900c800245848400d10a600000d0281c04591045002c44011903010181750b40300e051090701801035800269081d00e4291034620f544035607c04440c40303500100c50686105141c90304080003144e80042d000d06803040c8002000c000401600c2e810341b1801005000941600b40703050810b00c2c0d500702118880f0324058241400140111845a1411a084003009080015803041c152021580005840c41d40c2c5620290101c100284000d041d040345110348022200c481e40c8988510040e00e4501007900d0280582e40300210300c00300892203100401e4400c86600c101e8800700100c0703204203d00b10410a040f1007007142504200b080381070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 401036780 1250 401035530 401035553
    0x9020d120f0314180f060c0315010504030f08071a071d041b0806031212040b060d03020a0320060a060503070f0b0909101814100302010807081f0909 65
    0x2a841c003031103200689004800911000740c03040d46460103005018004020070000b122540b0318a205a40303140c0317004480340440ea08102c0b0040b01a029891027540300e58400c904890a495001c51019076800c80b41d02e5070038030354005d824211262902d407011f00030b509814460300e510800e1113a49043c5207480c10540104441c2d0451001c1c1e0043e424091451040a00c0305490510503003a441c0c144900e6a550300001e14080c041d442c001e8901000080d400310070003515031a01c2c81580100b00344d1001d40c5802013400b4220541c0030010f00160031003203110000902c108141518070702407101145031845010300807820b001007602d0178031035140d445c001042581402c2c403a40c0020018524001c01075481c240c81032003144910248107101d500c848000070000989a8509009402003840e4a00c2c0034032040c040d0340040050802c8250780c00041c8002914594402000d241940d80c1a503603122981c5600400f51002130303001d4950010003c1005e0f4600743d40c21100750000040ca000e44010030740c0903090402c1600e4a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 401038030 1250 401036780 401036807
    0xf09030c0f030d08040606120807020f10050403061515030504050705100f030b060c0d051305061603030515040f09171801110f01090c0302091e060409050109020d12 72
    0x80c510a1018070740d60700424450341c0d41840b418000502e94907032405000500030360f0445510000d1144040c010f2203894800b600560303200750b515048041d4240104400011400004400280c0401042c40050b20541040d4003d21410f1000300249888500081d2904c116500303240c0040e654071f0800c402d1000401c04940145020b0f00ca40054454001c0010190407215401e002030503181d10011b80b41d600d441c42224024a00d450a0b1203040c142020020705983c008c070083c280061789444042030f2881e00d10304440310f1240d40c69a406503201e44d686c098000d00350081c03807059141c00c100ca003050180c80f1030250300c0007101c0e405000038081d01c2610380386440482c4100201070840d400c0c001c5895051f4501705918120009080008072150100141841d05d0421803c0b19115420250210100310f0f00345000f0040d2031088035140d160390340350045ca86206206030b0310901140400d44c049103031820160302080f560b9003d0000400d50407910703000b050aa00529104803802d1070148400075803036900c03260704260364 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 401039280 1250 401038030 401038039
    0x106031103011503212a2003070e190509030a02190b0f040f08190e0315061e180103061112010b09131d070902130306110408030f09030c 60
    0x4900350b440f40004101e40c645500d00c1400c542c50483c9040c1d01a40112286d0f1400e44030f640240c4000e00d8001442c60380480086815401501e25601100d1015040c40c82035403004d40245074140c908900201d00e911b001e0445900345403200c040e91119050390180d40d1194102070000d60382e4100d0308100a03e4922150f8400b030002d0100741c0420005a0700c0000b540e084010481d528909132680d042000a0729051280108880800246107190048106021000d101103482c1c80f4260b240320018140c4070150815005200b40c059000181e1600d401030060110511100c8012031009119001c40c0c0c0140350004030520404c40040108100f0016007d825029080c5011043c1840340b10511411002418000c18800700d01c003003030081c503e40f1a148854400d201900c0d0500a0280115005a00110100000c261400303280300200b00d20170b150003201d140040c000c512450039031a48c0c85500c01450441016003a48804000028041000700050480d40300340b0030358030b5502c00d004010945080544100c0c0c9014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 401040530 1250 401039280 401039321
    0xa17090120030901020f1809061507230106030b012d0308070f1a19061505030a02130f0e01050312030406020c1c02030405130204080d0c05070503010603110301 70
    0x101090301c0c440c014030010710148a038883d10741d411810b01a0040c202d84903401800030410ba0a8982580c10f030300c008800541c1c00042c0c80d2200c4c5c0601c4104010402d001c000c5c10010080c803000640f4590285020140b580803004003003086699441c2505c01c66401681c940c100e080060001c281c01030001040d81c4450070309200020003c1803802c02c41d80c011312001c0e0002c140481c501c4140a00c440c014407000d9840540040c518000c0748807030b401d5100c2500c0f8074900c850124041e000030748203072288000b59081c24003d1103210b540040700700e1303481d07000a240f1400240c0a202154811080355180c4015050340c0200a01da03601305201394449080590050b440f0703610a05d495600c4c0c1c0c280800700d0350401d4002d000565100781c0c02100f00e03d858804498a04104202c20f007511186a010000d4000d8030340440d08801d602c280d158044080c0d001d10b0140e000c91740c020360705c207814050041c0d00050300644100182d4003126540c82c0000c0c03c44009900a0380e21140410852800d441c0a10038144518032103a11200b4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 401041780 1250 401040530 401040551
    0x34081b15040f031103040b030c030414010e03041e09020415110c060a0807110a0c0501030e0609070506071716060b030d1d0307050a080f0105090615040507140a170901 73
    0x3102030507507405401e1044c84040e01c203030300e6824030440740a000303100b04056503800e24030240e91407a481181c0940701020400d213904c41f120018000d0302c0300202c603c00107500f050f0600a042446141e080e0221043e0000c3c100001078151307160016000900440d80e4a01030f0744039031500500b040c0c81c0031b0410580d90704065961485940c4502c151225410a071034040c40c9aa0b03400d6090756104240d14040c1040e1103480118010001e01c0c190181c283c6001780e03018032401c1241c0400503610401034980b10420380050105008509000000d425480e00558aa2100a00450b0780360341d02c0c0d01a150b1080918445aa0740062141c14010f05104000680040030b00f000c907154000d000740190515003846c3c2d0074207522040c456030300700208405007030020844034069695580032580c0714450984080194200000220941004240e8500c20034103030000301c00d440c10000410000b010010701c01e600703001014024114585078200070f010000a5a2106502c0004140c00c5445400c0000d21050b0141c1c1022032002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 401043030 1250 401041780 401041793
    0xa06181b080709090c030b030109051c0513030b0402030c120a03020706080c0306040b12121c050f071202040f0b0a09090c0c08131a04090605040234081b1504 69
    0x1041320961400090501106201140900030605106a066092000388424072001141565030800912215a024031658a040c2c609001c2c031f892117101c03e2190081000072521813100e496102e41300400361a4141c4100c1c00140300b100e81807a03051102e5005c500d51a00f01a0100002e801410941c00d00b0843c901c0c0c1049441100d01c401410180181e0701c4000440741070710381010880d4170b4030391642522104d0101d04101c0c04560421400b801403003a107001100c00d00c2d10240300e80e41c0103604030f407a9076849946030003003558003403000c0c6106290540e017000001130724001004010043d00303618140e80c2d0f40d0041042c00901203005078111002031032900c041d260300700d9000070303540f0001c681c4018101e441d42c83c000e500c43d04080a56004031503060f400781004c50b04100d500014030940c4e181180410110340ca541c144022401442040150f000c80802d100e40501e601100c1c0d800c84e0140c0c1d442c0e043e441201592440c0050300100000709420302c0844c80171849030001d21201e50000310000c0e080d00740345081d84824 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 401044280 1250 401043030 401043047
    0x5060303070c090e0f0f03092409011d1509041d0c010c0f060c08043305040204150605030627010611070b040303020a11041e050a06181b0807 62
    0x109400f55440c2c2400701c03084020700481585184600660740400d0304c4016140d280d91141c0d420b14410000d40314040013900a481800d4481d105418101d8105000c00e00191910044441c1500b40d0b142c498031134078115a903000244100724071340746419803a510761406010540d4000103441d83c1c1215003084000f03240174009920200318500b46002c240a01407070821000c05c901000d070151245062003940d080a50300f10341703602e0055200e550740b00d4503401c00c3c0d11780c220003038000c2010038980c0a046c01c0c2c170108550305422071a013042c0001c0001801005540d5103580d0300c08180d10140110f03d0100402507146030510b115035000804d0f6481100c1b5004c0008108020981405010f060203148501003c0d442400c202c00400350581401e4035603215142d013006550b4041c14042141c1001c501113a0003013070300b000d001d1445803200c00c81c50340340c0003244118004040e19005000e540c8040e82c071400010b001c3e0f01d03d40b003880019001340c0001820021082e60302c419828000225061001c41c02c240150180d0100e803d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 401045530 1250 401044280 401044289
    0x60b040b0402070b06040b1302031806010e10062d08060901080a05060105040509010b031204050915030d030e010216060e0f0a021c0609080d0c090501140a05090f0a0b0c0105060303070c 81
    0x10140704040000340032071808e134042c402003031000c42003190b00e89400090310807000080c4121a600e82c0d9400340e4501d4440c00b211510a40100442e040002600a190f0003928085c1d03111800325102031941d503110741d180c05400381c6001540e904140015405c219207100c1c054010711000d0480c201d500c0d180d00e0b40c3e405042c494030b4000c1c0d80e40e000140e0004429400401086001000c1d16070f49091140c1c1c94500d40c1003802102d01c0340f42c845001c01d540c0b040780e170220f0070010070203005445a20309160060f002400000c00716001d1355001c00072400c622031144c2003075034401c2c41244000f840f0119206142c0c981014852034182c0b55004a030000090782c2c035110007508110302036880c6440c41540f031034848041d000354000184072400204070707001480e52541040c40a024541da40b1900070380e44100450b000303100f11041d445d000701c00300290506030340700350000e21404d0400350074032211100000115104c9041c1e940580300003480454840310a000c00c4c0035003034001c4000c90055083c02e0309900c0e08147c450750381c0709 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 401046780 1250 401045530 401045539
    0x101e05460c0f020a08010e060114010302090109151205070906090f0501200a0501060b07030e010804020108060d11100504060909051e0406140c1e04080d11030f07060b040b0402070b06 80
    0x30000111354405002402400b01113000740802c180074480c40740d075800207005071130780c803103034070f046810f80394070034400da0301c0460059440c188041e1400551406500092501d41c08000d855081c04503d032285008883c040e519940c0c50071400c0745804d4000780703062265040b903240c1103480c900411041e03030b0109024802e0f0a0300f107107042c18100c1400d42d1902e41075018000070030650030030000145904800014003021030003500c9241c1d01c0c2401000454596008490085c045085880410b4080c1803242600202034862800d5801481e021000141680d400100f0400000e80001c0c0501c0225441500da0b001446030303d1061016003405d0b45101050340d444000511000e84100004082c00680c6d0003041001c02c5460020756582080320021000da0304c460511170726000680c500300040c0b000c03132007150202e54100010300303c400a6004201e58012440c902500c052009014809010380174100901e00f6501c5544c00141450050080c0070a94603402c030342512540c4103001450205500290300c9900480c100c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 401048030 1250 401046780 401046803
    0xf062918091e09160e060d060f090209010b04061713021003020d09110301050106090308091018060c05060709030f0209061302041d06101e05460c 64
    0x4201400c0700798880ea8590104907041803044a10000c940d81c00741303403200d0107a0300d2031944640300c070041600c0582d00280c0200410340118003142240d8002e125044501c13401148980d010740000d581041c0a070030070310610000260800005400c4404903801049141e012107403803401803c042d480c250f2149029005a0b00d00144d03900c601e101e54100c80c4030200c0b0704001c000b01c010034240b0181101d00b400c4003500a42c600800420f03414040e9201900301e0342c0c840145881d0a6101d410302c070300128529071050038030210048941d66500d000e15604064461950765440103105403c120b40340401c0580440e00303000c00740100707101141c1585800052140c0544c2c1c1e00c102e5031100400b05468003003124140c14218400300e800f013507030100d4a8000d50781c02040c003150b441544a840402c24040070502000b4089051909024100c2640454100c820640e600309075040078000c40f4402030038803a50302183d000c036800240c50b0481821841001441480d140c0300c002d0026000c58014002080c86500a0700180312036 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 401049280 1250 401048030 401048041
    0x20f030f0f22020117091e030c0a150b120609010b100801060c033f0b0a030209070311030a06080618060a020903010b1c031407080d0e010f06291809 65
    0x2011024004441a002c09005e072400500840d2540302d18800884903c84003140c03a0b2102c0c1002040d645100c803890043c1035032005564504030b00000c002c80d4a9402901d80c01e008090b580d0b00d01e4210390140e0f00001070481868550b6179a421079403061441449070b0360f103210701c41c0c0c1968407404990540d81c0d5824100c2c02c0322410304003070781c084106488a109030880d458580302c00015400d454a108480301c0c2e000c1c0400d0158440c9501902c11000410750014800542000503152180b1104d4100d0000d00380003d40c231031020302c450306680c0708668001ca441d0702c03040c0810101c0c2d010001140d100c030b40380440d2125828003136a500c1d11214007074900420f41e600803482075829a4207602172142004014280400d000c06009e43c4081080c225034150046405030f00c0c0c07282004008411200340692051a040c5000021080c1c0d0008141c1c07401c006d50203660f506038864401490344141d42c00380485081e00c2c00055200303140800c05001a03030a840c0b05280c240031041d450344020701d10440501080394041c00d280d888 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 401050530 1250 401049280 401049287
    0x30d0b0117040309150305060915060408011406130b01021209031626160b0703030f022b090b150d0b040308013201031e020f030f0f220201 61
    0x50900881e03101d01c1c1002031008242d007100e001c00c11190489102d12200b407101034107408548044540c2a00a80c603e40082d04680c894110342c01c410342c004048a042c00c2d1121105800c64034202c800c0e50703603140d0850a0282c14500380c0460603418030710060a100e80c01c007800000b5100d8036008000c0041d04404100d282c01590180003a80158500145e9160701640c0c80c500c140c8540003002c3c0c0005910308000d4074803c81d0703002040d004180040e0001500d503441c50314420043c10b0788441e000360b041654a02c100100368a050004010240030030410031403400340b030050000b502200341c3c240700880b407078001d2040010301200a060b600c8400131403000c0301c20b5584004a03600b80080748000740741c40052000c00040581003540d080c1618003041e400066907940ea245100d5a907024144015518542460b015103076209410201e0007007002c8070030300c01102400c1c1811041c0d030003410041484c21004010003251000300c80d03801e45c0c4945421420509402c0240c00b80710741001d030301203642e44c0c007001d01d1030102503901 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 401051780 1250 401050530 401050547
    0xc0204020c010f091a041e0602040e01030f05010629031e040f14030715200a020a0204050f010e011208210718030b010902090f06040303021f0e030d0b01 67
    0x1c1c40e40280024410104008010f02039500211440314050466643c40b400c03c82c0481d100da80d201030700c60400e94028007658180c4c03003d020200c0746d41350204800b2500070a503800e524000c510442e8002c81e562031030f1900e1400d640b0035800845080c980300290a40c0305400503408200f5001c01c921b21566034076021281d01000c46441000c02e5021510010300c000c0207040004034044602510808034500055907030345859100e41c03100034207803040c038076075070080c50845510103141d41155507005005412070040400050300b0902604002d600009410703015400c0034025035600400c941a00182581050801200c180040c002c20f18110228606e41082106010440b500f0359035060329180e005d0800c41c00300d40300c2841100c2080006405001700e10030418034541074001d886e801000321500303a081c540004001c0d00a0303035206500007914400d100507501c41d54014405507000e98040c5c0024000e0b80f280603690164903400100c9180717400c48040c8014404070603031f128200781801c0800d0314800308004940d40a03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 401053030 1250 401051780 401051797
    0x106030215030118020a3e0607030c05070f080a0c080d090c08010902030c011119080406090602030415030b060904020307020a0b060303090108190905030d15140f010c020402 76
    0x40d00c01c00d510349008014020b14101d41034818070300042c07030440303803200c05074001d0400340301c04500c1c1d0420303100100703a0f9030b00340d581d0485018140044140c115500400860904040034120350468414842c02c00c0d41801640c6503084103041046c5442c90590b9904580c10306031002421088000c108030302c01e0f910400d05401150b402c00ca20507204d9104200d40d03070007010101d50440f40c0c1031006000049141040c02040010740e0001e0180001c00c0710f010040d00c00308605420811a405407904028850551079603c01b000c034014800790340c480e403c0110113801461550801d4055500c180b000704101d451084007111a081c09181c0800c0111151000c9415401240d608903407160000c01040f140f19400a619a030f00c600461012819458071400e0546902c60b034094507000404810010b858a90a4603c0d0071103034015506c00918074000d034642c903045400424544981e140c03244000b0855a207505039020240c01a1100c4264500d18400003070118600400c0c0306060000f0b081000055580d6941075075100b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 401054280 1250 401053030 401053039
    0x605031b12071805010c0201050d050601121a0307062c010e04091b0605030118020f0f03090d080a0212180f01020c0a14010515060714070b030105041a09010504020c01060302 76
    0x10b0414100c090100c00301c405948407806042c410004681d8882e0030140c140c0d540685419151050342c01040c8003401004007101d061207104181201580c086215500280c0e8802e1881071040c10a0000c050074285240d000030b040214064801201414585030340000d0312072081044131010764540161380048170000b40540c41403034030304030809004030180c1c110010b0700c2c0c2114a00c8003540303541d004d5232180028000d101d41208140fa5010341483c141d030043c016400c803180c0349424140900e510324495401100c00e007402d41c2000c0084240c154014903083e0704001030210941c1441521104180102001006231180c244202c94074940d0030381c1030140402000d958002036560b8107000003240d6540c04c60740000c9800f00c20071407180d81d0410041c0b00707440c042c00998030100c0e103802c42001000311940240381c0590720051080181d095550702000640f00a0080d4404180c582d07140a0030003007140e0700351078208140007040c0c455000d29990350074441d040d02c10031140140c45529001d00c80380140420b40009410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 401055530 1250 401054280 401054317
    0x602060f220b0a0f0504030e0d02010207030204060906051809030702010e0112050106030c0f111002030601110a120e06030f060108130c0b031510050901200a150b01090605031b 77
    0x14014050340780751080b0030b002004e000803580030348140d040385c04c11500a000100c410582c0100740c0b4010013011600b130b00503c100c98859403243c001804880b0194403150002c0d03642c0c001040a4100b000710032000201040c5403448074038003510480c1e1070344600ba2009040204030002c41005a001c0c2101c48450902c5080800442da11006c01400070b180080c400c50200f402c0107017078140303a4410503810501e10307000805450b2206000c0b2086000e50005005581440078231118400c1000c4100484008140030710b021564010803404003810318044400c03010700400b0304104120032102140751454000c1401c1c6070100d00c0307551b00034010324940e802c2e1000601c0d4400c44540041c0a0101a01450140362a4852804115400c408100c4c84400c040c12000c0480c80c1409038001540c068007c00070005ea6004c4c0d854404240d041c90749051940036002121202d00164103c80904070a21604009040a00709a80024180b07100981240001070004020701115075000002e22000016a681401c0c03d5044040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 401056780 1250 401055530 401055533
    0x15160507050f0d02010614130c0203070f20090603030319020f210106022d0c06041203081005030304090e01140c031614070201030f112a070602060f22 66
    0x860301c2001c3e43d410010f60800c4804144900b0310712018404020040c0512880242c0c4a41c002c050701343d1105200a600080c0003400210380085410f043c564890f000c0140c8902480c80000032100c0116086c0340500503640401899480000449400002c060b0070300041803101709104000e071007803c0b0100b10301040422075094a52482c0d150784000c07444024901096a2518000c99a0b50404200c40c03040c1d8154425484890750405107011b5038030130030019692014500400304400d9441680b100c10343ca503440303004034241544035501d036800c115a4418071081e20318040010f030340c0c2c1c010303030240c504019954200c3c8510107009501940170340b03c3c045001d0003545821000000e594000b00d400d1144000d02c401c154204500c108894030413405c01c00e03495410240c00b03400440082007042a440f908981d90740103100d0340b29450000d05510b0030011003205c065011402004000200212641080e501c1400148902070b0041041540310052003803418443c1e03551071840c0c13201342001c4d403207030700304004401d04c45d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 401058030 1250 401056780 401056783
    0x17011a0708031302150a03113c19020115300507090606020f07050d12022505040c0e060706091a04110a1715091e0307030f0215160507050f 61
    0xc2511710303450030400f9540d007940071101da01c00c8195036414220085c018000c00301d401d02c09c45105c90588120002140900c42030f0344140d074861407030034140f100c014582c1280d441e8240581c420880300305041c0359880d803501d1407003906d0410051040095614400c40c49103100408008800c016820000300c0d0340c495030750386107100186824040c8500500a4682c2c11000754030008140301102d0028000c005030300f089446090080d4841586001180641152004500d03200040e904058440c40e4803078119924080802c421100600030718001d2046014071031885540e04016240c0d02a08640042608203592502210000d03c0f8550340810358544c0046c08240000e0f44a40541c8101c01e0303600c41c000d00d0b00c4010320108e00107034043d80c901603402024026000760011404940190ba0b14045944003007000042c62114891448081c0c0d0542c40407176001c0c28103034041d443c001d96000c180054580e400d0310b80600c0040a000a000342503400800700d5021902c0d1040040701d200c40c2d0800c06035500b0303a04010995 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 401059280 1250 401058030 401058037
    0x90206070c080106061803060c050c0a06320f04060e0601090903080c0c0307140c0a06020309031519360b0c03011d06041b17011a070803130215 63
    0x146003d40c640fa8021070312038000d244030b64400750004144a02103286540715005022450610700412a09000802e04000d04000040e031252081780701142c054844001c549102a18034408007515103699400300c1007540ca003100580010700860704c0c120941c0d0700e0034280c02400300c41180060034460309000207524480c95200d100c00c1803090f0f43c1d68070b42c1d031240d040c0812207004040000c04141c200f00302c208001004103001240100c103807802e503220030340c10100050403003813158410740c09a000028503590a2405201041d01a20994074905043c24940002d19900b80300468524041d5901d440f01e4084501c02c50200000c5082441c102c030491015141021200d02c1e0320034116103014088020440500000082c0d90580c1d45545039000b03054884d04900701c82c0a0080d022942066451903903c440340c5d18451028001409610380300050110488a03083c081d205a10948904184401a8012014a03400c480019070841c500d9900d03901d076400c58910046d84600001d5100d030285009000320318820015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 401060530 1250 401059280 401059289
    0xa030209062418010f0e1c0203100605120102121321050403030f14030a090804030203060103211107030311011515020c04050408090d03020a150b0901050102151603090206070c 77
    0x3030003101c3d841c000055800b40f00020344980405c3d0760b44544800303410104084a5402c91840300c1d001404280c0d00881e0500d4108041100d466851315402d03c41d0707040400441d801d0098030380085141215802d01c619a202021304030110400841c10050184450390444400200300b21010100c0051940d0010f0a20790051200306c01281032003641e1000c03a8010440c02d41c82a044031040c03841c43d80d950242c2c0c0000c201041d001c8800c0101800040b000d030318100f08840c0a944070f43c0d410140f4030b4000d03100c1451107410700410f03410404000c444c030a40c084041030110403650f15041c241030211001d134409002d051146807100c43e10000c5100044c09030018040d51402d03c40540030f540c0211611380510050b1402110080c0c4225820402900c02e810103d0481000602074810354606441d80d0762500c0751040a2112151260384448010702c00e80303045840140100802d0005003c1030780518190724000c9401452821001d1198038260000da020343c004d480c0b4182d00401c0c2c1070b0f4603403030392a00c000a000f07507001c1e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 401061780 1250 401060530 401060557
    0x406030507090611060a0203100f0807030605090604050718020421020405150622030c090b09010e0103030c1506082505010e06040e06010219140f0102090a0302090624 73
    0x40082d405004180e1904c10141d41c001518042d5151140d0320b0281d44044d0507100b403040e001d8400200b581ea01c2903e0809022810098681e540c95400c140d41511400790105045410400501c00000c4001a4040854441c08640c114484403044404001d001d00c0c0e101111000d144151511f004241801c8040107a00c00c036001c02550304c514102d42c0000b01c86c0350420360010300400441803010b0100c00220b85400542242c9903296840390390b001e40180c442d81c0140d00254590050503014035114282501426003190100010345c90354170000d0529140d4040a8648070b107100005050160387e40104c0054003890085551519281904401403180025800300e081341c410030110b00d03503100707081a004201000f842e45007041c5c00c00800c000e0b2102c029180605500c580c281030464000c1110b010340f9510f00a017014070584182200c954101912140e03004c2150748104140da00c01e40d0f66116042c19643c054881807441d07500c11001c2211410310140c5030f4a011000b12140c54044503100080266400040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 401063030 1250 401061780 401061797
    0xc020d06360b06210304060908030f0301060c0c0f171b0904121209080c0d090f090c0215090d1403011d0a0b040608060114090f07080711030406030507 66
    0x718502441005040340034515600c85001c80d0102d00604030141e004000240f80c441c1c48520641c01c649010185890007515030800b050400c07540d5003140c20b22000380f001402a600c3d0182c41c20301d8a4041c40140202400d00080342503480c00c0c4881c40004502a1940c007010b209140d465003003082d454020361180c0e925071f2241078940b02003c800114943c520710b5024002c4807040e2290703130310000e0902e111400c00007000b82c91261800b00e0806405669089030158200d5559448021165420101c0303100340003091142011082040b140420451000c5980c0c0c03440000d503c1582034400ca0400202c0c51143c09020450303010300000c0314012801d400801804c0d11a0300c0001030030502044180000d2180c0e0b070584000d18507a401e54081410881d0307100b1012040000c2d00f80d5034a00140440f040b80d0000301203503203c04010b000594a0318103940c1040e1007181d402c00145400700c8003401c42c01300240110100600e000c0401c41050081207440001260801600d460b50340b0340400070b0041c9021140d8100064541c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 401064280 1250 401063030 401063081
    0x1a10030b0a0f050a1418010e07110c030a17040e0c031f0e070804030c1b060e1c0f081204050a02011202031521010f020d0606140a08070c020d06 63
    0x1a54000803514090300d9804142d1910004c241c035042500300058102000c010403c2945100304203441c0a0260300342c8c01045401e000384000c0c100340c03501c0c00b00c14081d030110300040b0390303070f43c00180c0c2c0e5980c0caa0040a07510a05044040c0102d203004a5020303000302c60b4000c05118a504010b006948100380620141420140c00307860342941940d18070a00c10004900804a0317006031040e0403d42e4014000c0c24013001ea098243d4070030302c01c40030090780c107061484898014800366501c00f0301c043c1348040480c1d454018201d8103540f00c00c1181011401072011240d030f4080010030006000b914110101e501e456038440c81e16080044d10703510b0005080780000c034444000391310f0100900c280d130f01401d8102e407400c41d000c1c0044103100c110b4038a204000d10005906500d5544103100f40104800703c10fa116001d41c5070f1002c0008401a580c540c1c100e4014080a81045845145c03024140d444644481c03510302095120a4810361380d001c01070310003a40001030445000117220140d04030200550100c584142c044150 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 401065530 1250 401064280 401064299
    0x402030c060405010807050c01270209074404230304030309050f040b12030c0c0a050612130c0303110c010e0906010e0f0d0308010302090f040503030106031a10030b0a 73
    0x82e802118089141c40d00450744440c07080c0003402d0600f4141c0d0000803201403081505480d0004a0301c1880a803c0581000c011401c00018061300300d1201d0400b5003008840c81e07805101d0000c55502083c12818030001c4403210000c0203045542c0381d401d64a034250908050406402808010020350603404a2003c10310400b04004200e5003100d8140d44c0e50301e0b010303081c10701b004448603503d203115510540b24102c1850a030f40d000581e01c801c0040340d000f15075035401d50942c241040c207000c08040c810914000c0801c0b45807101403c80b045845041c018100d29500c41c030702412001c03082c1201400003181c14030007004164114010840c1410b0386000c4405c2082e032400110b4500d1400d00c400b41d0091084000304a04d0b5000704070013001d00f00700925403004a512680403400d089000780c0180c000402060040095043c400c2d0b0040e00700303285c22201d8035a85883d44506a8911040c400d44082540d500c14040041c40021160b5841c114000c0405051500080d0b004002d0f004850310b152080c000c0d5600003278500c08 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 401066780 1250 401065530 401065537
    0xf0d1a040506090d0c1410050f061002061501030b01021e1b091003110109120f1205071a060a0810060e01060203070c0b030c0c0303131a0103020d140f030c060402030c06 74
    0x2207642d217050303440744550342d1116610048a201240f900c2821054010704c5e00078001d451061a4404d01d0444500d040000c114151801d049a10300395001041884003c0e810300085410362002030030042040c07155800103d01c3c006034100c2c49032020f201c6465a0300300b1100440d00710140d0703041010542c0305205850401c840d0303542c140d4120000340038800013040001e5040100382c1c035423030701418902c0809940e01d6104d0140542440111a2a48400c0100003005000500080341d03c1c0f141c5802410300314a0755a41c0d40081203400e03550840e0040c42d0006206030b454003e21405014520b0968440c0c85030780754944003502c0e150040c0c00d0800b540c0400441c040d407001042e00c400903008100400f0301490000640f0b0f10b540041c002d0a61f514040002e5140002c003080114015041f05251007078242060401c1d1001035200c4608101850604c401080540d5400c4080700b1040e4000007448090b41244418510380b40c090280800d082c000070074240c100060208100b44aa4025002d403990390300c1403402c000e034910 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 401068030 1250 401066780 401066803
    0x3030b0a1d0a0507300f0204030b010b070c0b0f0309010506030609030d0209040f02070c030302150f061002010f051e060901030515150319020415050108060f0d1a04050609 75
    0x720004001841e545154201e0780e0088042d0909041c52640040f41090030854500784600b03840105400c804651010300c0b450300c200108040860515007996600300b448a010700c20000884004600c100502109112a0b8010038101400701d6641c00d0065103044260022100c285865103001c0000b00d0604000c5075180c8204401409503181c0012842ca03c002500801c03411750300a03a4608040c2c40081251000384612405000b150f10480d01d1841c3c004d181040000f40c3c0004815048180020910340c09220758101004039007508041030303030301412401040d01017803448800e4103000070b00c03101c604060b51120b10000f4103000e002642d81d4400500c070580000388001425588090280140941c80c0e0313a240d40c000b0f1182d0b17562845030034070380700103480c0641d940e240c03c1031450b01c0300c4074008518042c4100c01c5503000c5216204000751a1600180007a040203002c45e0148506520121103551075140c911640c030b500c0600e50446010b038031601d1820b108203d0b01191248142404204189070008901602e01c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 401069280 1250 401068030 401068079
    0x1170c0915010f0e031207050f07150c02030a060911030c0d0515040201051903020909090a17160b0406020c06070504121707060e0c100f0c020f1206010303030b0a 71
    0x1d007a190011140b007048100450100072010f04a90005e0343d0500a03e400780d09030001c2603403035124908145040082ca02c0c0c40d41d480b6800080104261480c00e08001004822410103a0409546002003030030000308220041c010741c13400070500d041041c00c1c101032010100a8007259401040b2078188510035203180000352840e417000720030034480d84410100c00e034000d1040c98a14207120344004661003100e101b10b09400420f4000c505c651440c1013004400368855545e60080850300180d440d1441c180c03c034025042c0c000d44001994007841003105002c1840a60f110061400320710f414103058009420801161203e405a50b02003a0468402c1040e10240c5c0c10700a01c0781da40c1c8502d40c2d148034407030401300c540f410050f06c20711189020510070310035510166003050160000d58024010048a010341001707413004e00c11090b0b01e015a40d82d2055400c0b104035816200100c100711204005998101101050f0000e0300c03504001004065241c0c001d41c1d07451100ba6022804d881d00d07140c507a0719000c624a1000484c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 401070530 1250 401069280 401069311
    0x5031c0f0e0d1101200102030106020606151207020f0a030503060a0e010f090911040c031e0204061205040203030c19030815011b11090106050403051b0d020d11040501170c09 76
    0xc0f0fa0100ca00350021001410808410124101040b1421015900070541a54013100403c50340b9010300100b075100c007048580420107060078400c45140d0003507071401c0780c00340011800100ba0742d008000c140981210201220528005032400401d2648200c40c1c1502605040b540055000d296080c124141c0750013104440c900d5040000302d00040c0054a41941c104203000003038855511075200746c0586201c00d035400329400144203080a5501c40055078a07102070b204100411032940e0054400c05200c201400200303403a01d903800001e00d14064054200102c2c0901800c002c442e2028900030a1000e200703455000d266a20350010703400d184041c814840c0402c3d082c003268000004000c0c11060034921071803e4100710401030001c1040404242c10003c04900001070610500200704494031009011094034425100c000001c16131a48941000038082c601240f003c0b000c0005911b90004d031400c02803c10441d0b90303036074040070300301e440c40500e40c0d0003502403070480b060582050f00e0103034810141800319400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 401071780 1250 401070530 401070533
    0xe0f300a0804050a1a04060506010c0506060f0f060301060f0f020f0606010509011b153218160302040c0507050607080c07020306041208010e07020a1b05031c0f0e0d 72
    0x1003444009104451601852213440000740d82801c2c07280f40c9003089250604603103000d1405004442c000741c0317900e041c882c0701410728001800020301681d11900a880840001d112407001c1403a8034021201540e001002000101d655036000340d4160042c401a52a10461012008280d8590380d06c880c0044507504079200007070695004c0e6006003400301c41890110528800303018080c220a56406048641118080850b121000c10b030007403030080c1c40452004415030400ca1400002140000505481d0742c0044000801c0c080b12090840b0901000c04143e44045180c00d000d50071441040c00220711607442e000c0c007104854820b1042d54002d0780d120300103001544400006403400d0200500d0100691010400200103031014060503008600c102d01052400c1600341000d0041c06058001d03991000011003000980d40e80010f44542e41500704802002c1c0001070561010106a6070700103a0701807086c0b1400f400e49a10400c08881d00034080c0e5902800312407441d03021215150707040c41c95039101c410800d841d030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 401073030 1250 401071780 401071787
    0x110a0507110a051801140105090f130b1c05160e0f04080d0e010209090901020a0206220f0503070b0903040501050406030b06220e0709031203050a0e0f300a 68
    0xd840c0c58000d011550443d0380d40c00080d5440c078050750328600c000c1d071500104500700240c0c644001c05a000d00b082810a0005800303d42c000a5901d1803d104905280d1640c58060040c0c0c013000040d0000b82c03185c00c80911110041c400c48184050803140d901c60010b403202150b05041042e003d45a03c0c480690007034560060500c07280074060002c0e01c4500041000840f100503a11800803000340903c00503032521100e00410000d104010008001c69004000b514002503010668a42c40044c11801d540880030f0800050072003000400000c08200c00c0800d840d0500030000040d281251040c0074006043d61746000b0703e44c8901592042c2030110380207102c284030b624003d401101c50010301a00031410000e40010009090112b0a0000103d040514041c41441143c2900769800070b45820150351651540c4e50760001030340c00654040800d07580b40c0c040f68280415800c83d0260000a0084170950888004526243c04417864011041c194000c14680c80b18010016180314444a103c0c1c2030404c005042c054 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 401074280 1250 401073030 401073053
    0x1803030b01300609090f080d0204050303120a0c11061b0c1005040212010b0604170312090c040b03060c0301060f110f0c0a060c0f150f021804110a0507 66
    0x107050024064445089000395048031024400d100b00386044480202c03035603000c80d1641e821142005045c0b03082000840c04a4200014807540031608039518041207040d90000d00854100d16814000056011002100308411a020726100e01c0304000407000c00320180d5120152071107459003904031200045840300901c1818003610f02c2c1c0044103103464107075240b0500700000c2c0c40c140810199a40103200a6023000450a4510031150008010012480000031524040c5202e80803c18003c1c94010401910500036252030003d40e628a2250f82481040c5070744a0445011f100d0040345000d00341d4001f0b140000c0d01d18080d0b0709202d592451a400c0000850761450003401a90500c91404650f6080074410412a0041c2205402426204c0000000c114007114107612500c00c001d43c204005001c60a1a030301000c00a4bc003600c010008442d42c10074a010b0062040d013030b02e45a201056021107113011010340e01c3c0c10035049404220040c061a108a000d0096001c0e603000920140014000100301d810079 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 401075530 1250 401074280 401074301
    0x9050d03020a03021b0105040b09070621020c01020706050a0b06040b0f1b0f0d1706010219030e0301060605130501171f15020a0501060603020903152e080d03180303 72
    0x25117000711160300c0c03481c50400441d0038401d03690b45030104000d02c00300f54606a040107078080501480ca240150040c00340d0340d141002910000c44101e10541011240d044803107001c02c8070700030754032400241440c41c0204003c8540e01480c60901e20181d14a207403880c2107a0990303401420550801440c0700c4514111f400140c0c2c460100d5189580044454408000083c03242502600a000001c46404014000080071501d081c1d004004000d109003030307170045175500c003568a1040c11120f2414505044507910650015660594a031200104005500100802461035689a41c421640e40c43d40119461420300f40e818003000f04480200e8000c903c40032048100c886c00c0210b24200a0302e4580f800c140701c0710307480090050f84c44042c41504200f000e014038002001c0c2410304600340101d040220380c1b508600152004020014000184e00990350135100b4a41c0310344034540140545814102c058122a50154160a00c107411a03014428805d0242c0040190707042e440d61583c50041e5000e90140c001c0c07040c1c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 401076780 1250 401075530 401075537
    0x10609020f04091d01090f050d0c1e15020f07020109052407110915030c03010b0f010c0816050c0a0e01030317090a021801141804031b06020c0c0f010309050d03020a 72
    0x800a580c0500b4041c001041d4003c0d40210387c129100d180c942c2c6001c030804402c002784103451140402107290300350713804003160801402e00400b581ca807804084d00982150b801c1d01a620210301032500301c10240c007a003103262003a25200400c54030f401c2080b0000a031082040803083c6440074641c2a00001d401030503803144621851801880e0240002c3c41a4508480460140c880300b900082070340b80402c02c1c4c2d000d40c40260001c2201c2000c210100c3c61100c882c0e1145814841c0000c00c0000300301c2c2d81340803620101f42940c43da200c00714007480d0040e1100300c0c0c0c0c29180c1c464450804080303001c4490080e210704a81c0d2503101c02c03141080446080440e044c00421400c0e9038007484044e003016864150760b2410985940d450140c46605110510074000040040c85020b150302240001b107101e000c13a0815081a01801c084002c0085c03821341d01032044481d000209480d002051442d070004002500040c00c610031104a6802c524143c011000c0300e10302c21002c0c0c41503000200c180d41d180d000e58014104401c6a24 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 401078030 1250 401076780 401076821
    0x5040816051009032604020d0b06032a041401060804110f10170108030702010206040f020f2d04230402060405060c03040807060302030c07060506010507021e03010609020f0409 77
    0x2001d10302100d6841c0001c0d40803d85c051602421060302036280b10b00640e81402041050409801181c9951002d180c018121201000440c545a608002c804040c580d2192004c0310000455400340d0b0f0070410099240c0502e051040325020f00040c1002981640e0b0340307a46516440e5100d0b22680740020000342041e40002d0b106008107215124031010444c1d1810a485c1e841c1076402004480c580107005074065011501b0a120031030040c2c3c7d0200300107400680005034100e9031302e0b0a00000d20500820b4a006d98400d03140456003004000285641040c0552040c64200c481421030511050b02d060645102200d1010b640c01c060710f40b900000b10741c1050014044504080e11040491000e90150141d40010303800450100000c490030000c15014010501d0258114145185030983c43d00803480001d0540e1344030340000384540d1280050318096600103022a00d00c0f25820716404000481482060081d401d080b00401c09404a008450440c0b40c80d04009250918000e0f03a44001e00c0c4070350508184142e0403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 401079136 1106 401078030 401078053
    0xa0c11040b10030f0612051e070303050409050a060b0d060f12081c0e0604060e010e0c09180a0206071407061b02061c05090d020f010504081605 63
    0x6082c00b05a044c000c0241d02c025002540041e0a40c983c903003503000a01000040c142008200329810f224a86501d503402c0791920072a01010740400c000300010420007541e64043c5a01c5010494000f50a40d2194a0407006901010441a40a071112010300c500b44160f00c04400a018030501503110071095680c0840c035008294005541d4500200c40044110541d0055a40802c42e1016101c0a1900b403030f14034024003a811042110b5841c00301b40080300800019035100e10100285400301980e589140f49a07050004041035005010b40710070440140c076400040c00030342d80301d041c50001c4040c40098440c60509180d10150400241441540928816104003413500350152010390303480c0fa106505907454a81c200304901460314000400102c0e410128450303101c1c20080e03083d121101d0780c4145013400d8510a4038042c000c48802c010850300905001c01c8040e450340302da000d035895940c22 = true := by decide +kernel

theorem cover : BRFrame.Cov 400899280 401079136 := by
  have h0 := BRFrame.cov_init 400899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 400899280 ≤ n) (h2 : n < 401079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
