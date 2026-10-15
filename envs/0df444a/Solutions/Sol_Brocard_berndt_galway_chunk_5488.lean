-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5488
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:01:32.958146+00:00
-- url     : https://prove2.me/submissions/a09acf29-9262-4d72-b644-ec84ddb76498

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 986870503 ≤ n < 987050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 986871753 1250 986870503 986870527
    0x105190e0c1b1519060305030d0c11010b0f0411090904030306060f03050c04030b07023406020319051e0a080f0601031b11010b0301060306061d040c05040908 69
    0x5180207192910700a507440d10341c01c0c0080010040400401200e0388204000d0031540c01d04038180e50800155200240708500301c400c0640907000c0c1d900701800307a02000605110030b0303002b0341c070003480d006541c2c40c1c2c00320400c50388490340e00701c401044001390000e1808025504603e40303580300c00410200b070094141440c3c500008141583c60403034003100482d40c0e4601c20b220f402d8000e00c00106c0620686010f20040c500500204500e00441c8002000f03070081e20f000c42d004600038001018044903525118005100041c0c0102203030394081000c0e1079801412002195807403011044408801119400c1442500c5000d4105c6280d48900301500904840b0010b560034640007100800c0f80303803c980e0720038480703040c0011500c0c104000900b045040c5850015111100005200b0082c1c442c03615040491140b00150702031809051054071880e455403a185000c000c11a5030750107442503400340c030f100520230110170350384071003020003980c02400c8080340b203008118034607090b04110718003440b031140942010003401007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 986873003 1250 986871753 986871779
    0x201050d0f061701050c03090714040212250201060b1603020a050d050705010b100e1327050c01020a0b2d04050c03010e030a0c2d0b040b1608010519 65
    0x102d1201d00f0485141c0e1844070074002c65410100c080b03a00c41c55130074101017940e603ca003d0700c100002d4903c510100111a50784d0380c141c500700000c0c2c4070150200d107443d00c2c4100d032a1088103024000e5034a01707604228818414440c4000340d4149540c45441d1020003484500700081a14049003188100e15a000c00202d0a2122100300d54154843c20b4030703000186400c1d403e40b24401e8a0314010207240c403440d040c1b0384d8000640f400f03800082c0d0302c480784402080c050f08094030103002d10f0b00d00364181508070480c50042441003500180140165491041600012602c1c4c1c0501d1001401840c821408501f411110040444036503c827640000f00c6201c084291136039140d8102c074180c405030010050310380700741000e008078540d82201101441c98840640006404030841401c0030b00f036180c0c80030070030005103040e5461650001b140c00e50050302c91070303a15060010302812034044402d140c4180100340b0781107c0341c4803601502c0301da403181e40c81a0308007070034000342c0e440044150480ca074404900040b02c14150403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 986874253 1250 986873003 986873009
    0x40608030c1b011e0807110d09060905030a0b0c0c010905120a083d080133080a080c0a0f0302070807123527030f0601030201050d0f06 59
    0x1030000c440508400302e04140c03140100c0c40c18040154840030030034031840c07580c0b04251440d0504020176103400e40103c0710741c178203c0329a1003540725010031141c400e9041180c1d6811202242d44155100741c541061588441d54804028920a07219001c2448400b502d009040c03411024400000d6440840c0c84d01d5140905440b078802203030b0800611011440e0780101c5a40d8850032907509085180118210752100c80038000d000a82295120740c01300d01d203c10b040010004181120090041c4031015000500424108610301c44540520880c0b01d0321114001000080701d204502601201d4410f071501a8607038010f130b400b240b407030080d100d4070400508001065000c07036009900501e41c20782480411447c1c2520354004920420b11a44205c0019003096009207900e105444241c901c100e604003d5440914003400e0103a169002040402003c28000c041a246000180041940b14000420b0644034402000c000d081600300d4001400954064401000023409844002441c0f400072100c1000329440c0d50 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 986875503 1250 986874253 986874277
    0x110312060f04290a0e01090c09120f0b220b0a0506010c05100b010207050a08010c02240a09140a05060115020d08010e0702160905060a09050108070302040b04060803 72
    0x100a22009080c401841c40391840309650800c901001009030341e07a0b40070503110342c40780440090f802c0c140c0b42c0c40e41c904141c01040a00c000a00c0d55850b0a1041c1c050007407101e90300001080d040340000c803141680c0c0e04004440c0c0025806590800b152600702641800829000981c229042d045000c42d000480108826025020341d100301d0802081c52419500c029110504000c440031034403001c19404030b10086d444204030800a44801800e00513410300c02194007241c2d101e072402d44c0c00280280190855901ca002c2c0383c3c01d4482c1d44241d805a130140c00003a20400b541c16a40300006044004258422000c039801803e013420341703070b000459280c03512060882c1203801d904200d0041103010920b84000201e07001700d0010705000d02c05014000c003e40c00511071403161592410100703c5e00c500038807108084c19075010024a070251203084901c09072805803030a5003d500c80a1002414002d14440e45051300d82c000c0c09851494619000c005c090440c24104690007a90b881000513034500030802005011165 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 986876753 1250 986875503 986875537
    0x150c02030f0c1507030c1215030515092e1a0301060f0f2408130c091a0312090f012c0a121722030b16090e0402101103 52
    0x10442d400350440904550217040c107110240e0b0b0310a400c00701c09081c400215400061003501c6102d085600c8007198400f5249025a43e8480490f0300300c1d9215511500d0000c0865012003514050343e01c10341c0750700d003051607100780c58440c1222080c030a0b0410744e00c1010314031510659001010000b07007140c205512018917040040e804020049503110808010030081e031255400948180c4804d0302c1440400748802081044000071369080c221348000c03500306800403a6900e1880e210310000d40207004440501040799800f100c0f84c1c101c0c2c640020325000c0c500a101c019414050100c01f8001c100e901416004e05000d9141e0b603003400c004900041398544132a540d40c40c9201d200101c00d2080400c020381003005045d00c1c640c08a000b0a04842a40111048205509986113410a10138041481103101d00d40b030b410903d0000070601600302e10003400303200201d103868a50088581d06856280036442004049220a8001400362410140440a013400c509001c0429420304000302e0442e80500b42c3c0d51110042 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 986878003 1250 986876753 986876773
    0x3041b06110d020601180c1b1b0806060d060e0f010203040c050118061403130f140c0d0f110a17010501060e010309030804020409020a12081b0a150c02030f0c 69
    0x2040000c4501c2c10260300150400b541400001400ca03560845800d180544034001c0109142c4145070060110004d525003613404141803030492454403141c190b180c1849131101b0701044000011660b540103000060002c0207450107580d4260150041c58821401c5000361000e404c40c018007030004600c1a845035060810707190404001408000c0b140408407200d003080381003400801c0e00302541481e000c040381d24481e00c903031303544100040d812a4044003d144442250900c010010100044001107128005560412a9140074007001c3c508c0d8ce88040c0440005021000200702ea04211818000001d08805415900c0307000a2030181c17149616242c80740c0d900c80c01003000a600c040d64140d100d030300346014001e004441c0c4000b0080200071784081d22940c0e54440300000c660720301075544010311426100d5502d500c041d01b032510302c0d40c000f1580c14204003000500c01444040210301840d071154055a0011403d210032207030001000c011410307109620041140e200341d500d520000d0017000c2ea080b4014581c001c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 986879253 1250 986878003 986878037
    0x2030f0705030408150f150a0b12040b0a0b03030703050c10060f06020c0349170f06060412030903051902041506050d0e0109020d1b1203020307030503041b06 69
    0x30704405103c85030185c0000d12844034100c424154010500c0042012081094030014050071000c1e440040c21410001d0640c00c21a900c281c1030f0301c22805040110043c0d502c0311820404e640d8103a030300690580007000080300181c05003001c1d0161140f19012121a02c4e040314000084408540201c0231003c1441001c0100c41c0e8104201450b40c0000d4001e41140c0c0c0f106011104180f00c240702805401c81c82182104444030310158041c20360120507203070740d0715410008001d41b1000301100f035440301006010000d1041e0464074800e0b40120b80107003031586454078040d000c81601545100440802c243c4400010114a04205d5010740321102040e4100711030f0240f0402044842e10406681c0d06241140d0800116401500b0761b0002c00001d48081040100c004040c0c1c010062910000e40c44500440110244442200c0602c00740c0c8000f034200045a40703402441541c50510000140181e00402c0700748006841040a0341d00075210310080138154414240c15030800d0225000400040d00380c45050001007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 986880503 1250 986879253 986879263
    0x20d050f120c0927070e0112060f140102070503070603111903062d050120010f0c03060b0f0703180e0f090c0a0e01030f17030703020a0e181602030f0705030408 70
    0x14003c11030082c0c490702ca000344e010709401040041400a425502c54140e4087d11204941c0a1100400c0107003c1d03c4025402e508605030042c80002d11060240c42e400f035000168038401e07200c005005081e55483c0013411400791485041c0954880800c4c410503c08102000100c0c4a2501d503480204181e400c0c0003a40d0903140b012081427804c01010103556003070004500c10391040d9102031800411101d0040720301001c12001c80d04800d050361a082802e000d0484d41d520180361009903950134405c0c26959422303d1194060a0007100e4203840801900340064020f141103010070545070350715440c42e540c0f40b000303050242c03045031904060000d0400300b00c0740a40a1010f4020000211aa81140d605000340141c00f000f050000402102003a8052000d0041601080d40b401c2c0c298000b0a981c3c1c0390020f0001c0194120b50791000100b442918060040c9c6400503d5410400300b10408100907a00d5070f00060541600b40310301000e601080002c0c4210b0000308004100d4075010303a00460303850f450710030014500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 986881753 1250 986880503 986880529
    0x8030c1c0804110906030c0303120402130c05120712061e0819061e0608030703090b090108040318150c0506010f0303020a030503070e030703120e030d020d050f120c09 73
    0x7250010040090404054101d81c2c000c10744403882c5550340c50021030b1030519404400d03503040c8008181c200d207000740c40380c15034030540c07081d40c000000c01c0120161b2401c1d60010694580403440900000c00085d0600800780d910640900c1c24488684403101c4042c22100960080c010721b400000c000f4402095029991005001200081003c5441003903800c07108043e03008010300c07160711403681d0b512030082810030010042802c0c0c401c1041a6540d800241e49034454282107000c204000c00000300c3d20000d00907103000c110183c49100084e950f82c0d80480c2e041c2c03984143d04004034401a00841d04580c040e0038011101c149881e4200d09000c0e40c203001e880c00304164001e103c8002d008034107100095011502c0ca080c69414100151291a280400c1c3d0740318640550f0160141b040c41c40010510040b1a250460701005880f1080d000750000e007899100c17210402400d0140c6c2c00540003030222442000105880b07030482814506043d10910202c2840b10103503840f1500d11000f152140c174601c0c24000352814 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 986883003 1250 986881753 986881757
    0x4050904411609150509012402030304030818030c06091e0c13020705120c0303100e13030f1403130b010e0f01050f0d0b090a0c05060a0c060209010908030c1c 69
    0x61040052148140d0b80780a00507090b00f2a1a041c1104992460640140c050000104502e54035030711014035a81440824010002d401c01701d101c8002c02500200849014940694500203036540c1c107074000d03410b021041c850ba1100c2c442005107901d10304040c00594061002c180142c4800c00780101ca000d10301c4450404200950400c2303c0c0904c2c5561826100c5000a0912401607201c0b42c1c5800c3c41401c0000c08172903410402c0d0000b486040020001c0000c45c890711000001341c820702c0d02c0c0d00303503001022011200c0b111f1200701d0803801c4002c203000d0505c180c00d422480c64034942450201c6410083c0c0d4000740c410400d184a00701d480c00c100b261042e402400743c82d1421000c80d803840c2000b13401e81e0794001803007650b002d83c416460902d40380d10349500c03081109401491868490422455036984c440704000150360420302e00b4800b080900c1c00c01e0031078060180f241d0701c1c00340c0403402d138032104001d40c003c7c40018140949950300080d0f260b001c0c030241501210020107841002c40f80194080082501c4440303600f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 986884253 1250 986883003 986883013
    0x61605060a0641190306020715020715050a020d0e030304150b03070b0a0504050a0303051e040b0a11010921121118010c0819030e03030c0405090441 65
    0xd000305503ca20b028400c0841e6440300112140c0c6400304070b43c505280612000715009030000b00c107102258008002c0305200e42400c00b540483c400e440c0e0100d001d003e000501008809215006411854008070381100c4030301c50052070408805441c1c000c03181260b008059540001c401c0000b030201c0a03c108150f007503246400c0c805918840002a141c5002d030140c90002c4601040d1004951301c5841600c1c0a0700300a499840003a40300d00340603055420048000d00e100725002c0d02c0b0035852290310199012240b1000c002400e10002c0034069407803001850b900030340d5669664a0b0342c040f07800c02e0000700100e20011a0b8885040321414020310201540c500e01d42d01c641030284041e000d0180400320340280410b003002000000803000101d400114110008e084408086200b00810f00031190510507042252400c10120b500c6080741500ea00044415004003013081c8010840303403c0411126500a03ca9401007882041d43c0d920089a02d034504880805900c140664007034030b144490a441040c801d18000708 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 986885503 1250 986884253 986884319
    0xd09050108100e040f0c0803030f150f0105090607020301020c0a03030c12051e07030b150406020f06130f0812040507061b170c010b1503070f090b0306061605060a06 72
    0x403000f840107400108066104c150701024050070589980182541c04150b9030303281010740401c0c0c50040300b40c500300d14500f07c600089503d032502e80b0b00301400040684405040020140c00c1100642120f0b4051360507540802022400d510280710070184a13120740c84c00100240341c00342c000c000e001400c4448040614103804d11400110a4884419800411550004a640d403103001c5000d460028030250b0804240081a0f1903d50644054000d64065500f03d50913020340501d42039071118180c038600300c601c807000300480200d1801e90350b810040b405100e03450b29103186140e130524030394000c40c1c0c20b49040c1c024450a1009a900403c101401079440f200c1071001c041544038003801400005000c41c03108400034000c884076200790885400200018494441d00c042c21a500b02107a00858649000030740d00341141c00d600e4098031169056441d8004030a0850303558030140300301580400107000315000c8400c00e0000007501040601c0c811400c107440401c45c42d1404030b441010103c0581040d00702448060382c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 986886753 1250 986885503 986885519
    0x1005030a200d110d0201050c010914120f03011502010b15070507060f1704030e03030c01021c0509030a030b03101b0914031b0d1a07081e040809010e030d0905010810 72
    0x196010f040448035107514407014401640e10384070b1100512015400c0c805900e00340031008032149208061882a00c0740010020042403240c407400c101d01d0186034090006000c80c48a501d40b039840e0000500001440340701c514001800100300c02150700404000060000400c14188103000c0249006e05058140a40044010700741c0505411202400e010310000901070511921041049100203015259180005421103020323501c00c2c0000c00954007041030030054200c1512480f482000140d01a504104130124210040d158240d030150b454404c21030000003841c0c0c036100c1c10b00c1c580240310b0841900412164080e00002c1694007600309840f07940b0010300c140d01c020405d03214401c001c600160700d05094100181000302c1c0201c0243c81c44c402c140000a0b040b000d00556070040480fa01d511469a8881920040301c100e07100c0b032484040c2c48080840d000641280180c580c0f0401410070b40684100d200c00b280ca0410343d180725000040781c0e144200303d696081290190003d82c55440700000b01d08100340 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 986888003 1250 986886753 986886773
    0x5070e10090b090d230f011b2601180b030d02070302011d0a120b091b0f010201090b0f0f01120f06020c032b062108030c0705030406230712081005030a200d 68
    0x2884042c27111540044120890311460644421405c9420070040d503190490790036900030098403001075070b20303044662030030b887d0018010103906400d0b8014000c450440e401162101d241149048a80008d0100020282e85110f844005000c0140d4010012051800c03d401102000703444410b003508013510060601c0300706581380c0c200c400183c1c0c805444180c1000100e0042c984401d024100510342018451545461010f13a4002d800d50713a409116640c03580c01103030490700300c1c000c0207040c06401201000003c2c050b40103014880c2a440589060620140c10704c0904412103201003000c0881280000800445101d00c0c805488281d50310190000440d1001c0100f00c16141c01030981400400018140100201107540c0c0b181e0210941e502c440d561030b4080c1c003111030f000800c401c0310400494061840e00000503a8821504a03410004929503240d0550364030402401808240c460180f010030142c8080188a07080c621440303001d9030901c9c01c0c40320003c000c005c1d04039543c0300e54118641c1001041141071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 986889253 1250 986888003 986888051
    0x807140921030409051005040b0114160f2306010603090c140307031a0103020a1202130504052e15030201090b0904091505070e10090b090d230f01 64
    0x580411203a1007481c000703145001d0781d4000c244030303420801040140c20400807800304807402581c041c410341117041c005441001c0c0c401c03488614a0402d1001d031161505029914070700c540210394401540440d6100c1115850f5402c0002052246c43ea4000a6059040140034010308140c6403c02c8184420340d680c80342d408003403150f14000c4690900c1d0780819034080c01000025944000541e20080041074600001a400d10040e80306003010b4100060410303a0348131180c0d00a03402880c0010011109103200c5c001c0c40c02a000380c41510a1040300000e5140c1d40325882003904044071002048102c0c4c03410f44081d9003440c0410141192195410401030740c0144c0c51409498219443c1034464091501003001000f49400c05004070040410740000300c0015800580200c5c0035035150502c100c2e010043c800c413405551400e100180500d0810024003580700098114400e00800030700c112240da8441420020303105043d4000b07101d54207030102509000304500f6103106603140080c088451100c0d001e105101c0550 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 986890503 1250 986889253 986889289
    0x30f10060c03051b0604030f0909050606030c071406070c02041d060c030c281d09062103040f061b120c1401050f10050913061805060708071409 63
    0x4c50703400e0024407016098000c06031001c0c200c810524144c02c1c0103003003601904000d00031481501000c140c0c0c4240b030090a1081c81c001e44104d16644034a03d00c0c04450b07001c0300040d00c2000700300880d000b960030700340406400398645036610b5181207c1401004200c0d00d0060200350440000e5190203000400485d40390343c0445a21107442c0c0302c5d0368000c82042a0b10503000810040e000741c100001e0111400059404280c21a60b10041d040c806544800c10080041040c16400f515080000c1e02c145400d400c4030b2500c196a024036800080c0c4200d4052950304980c000201b401c0c0240f0080c07080c107600c000c400c0121070000c00186842d214580700c0840034050f058001007000030580109051021030011049044c58410007000680780020300c0712620b52090380c1030705403401d55280002c1e00380b034403200d042d00032844010380c04440691540e4640003007040d104803c401440c50484c41d40440c006029540c407500c4c1c03d03103690245290008005028030f502102e0402015414000d15815484407100907509650b20 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 986891753 1250 986890503 986890507
    0x1d0a140a0b310308040905070f020f070302041a041a1804031b0f02062701180b090114041409070836190510020405031207061808030f10060c0305 64
    0x4040b040100c0540c0c001500074000040e000942d03071581d901452040300c044d5100742c1040000182240c848800582e032440c95071001c0001c0c4058503056102c0e041360b10b01e404001c0d440d0050300f008501560f010300038045160740602944046130401200601e130300c10142403a0041071410340c1c1d02801130301001c0c03c0d110810396071095a40030042e0b15890a800103800505032600d40c0e526041e40621509428402110641400307807150301d0354003076040146060050303200c240d01e4606005880319241c100410490400c0342c0c42440c8018909400010001b426160b80e00540c0541c01070248440110301600b908100494031341040400b011a655106c00201703c85251269040a108205032414040511810b14090164005c0c810681c2c500b0f4001d440740300743c080e0391911b08a80191030803801544105500360300001882d14840c1c00c40d47c020190702c1e203e80c0c40040c0e10135004050b04000c00c0180c10450701c0d15400014042542059009590300c404103c0d0042d0b405030405c10001c1503010385440080a0142c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 986893003 1250 986891753 986891827
    0x2030a050d2f1b0f030403030503060d06020c0a1713060e030c1c020901090c0f050f07120c03121e021315090e15030d1d0a140a0b 57
    0x182c00b1041082c404820140c1041c06014a00190b40e4000da071003640600440e609038540e0a008501903164400c101d003e18140780c13658134103554692009280d5944074140888240014146101800380e45a03480c0007070218440c0c9213483c041d40001041d40d0010400244603e160760744a10f00031005031a031170325046803140400004a89856039146506c0e52101940110030003281c142032404d0301c490300803100c40e01c0c542d903034501c600d04803401100d80900051140384490071407401100204490016001420300e0041030351a41e00e0002c080070b03414000180461085030605070300031000c142c0904480d4013081400a5041100c20b07800134084030ba400780760045210071001c03803e03502c00c000815001c68032417040b50100c400105010868001e216201928902083e003107000f01c908105040000b0380100112010707454140e5415500601c1c80c0401c5400c1082c80000342c840203400b000525080107a045181135202c20032030b07510390f0340e0041000140e0501c000c000344410300001282211a00251184400c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 986894253 1250 986893003 986893031
    0x1a040503031b0118120f03021602090601090e1501031a09010509070306080a05031e040311011404031e0507151409120a050a1b080a02040f0f0f0204080106050102030a050d 75
    0x4800d44e00d034101001d200c072094080c045242c1039402c011005544042070524074900c145d08074020200200708010307182c41000010b0038041c100c5504a0300c14103041c03c599036180403100c00390701c044401650014011843c20403558050064940e060507110001c1003108488000c0342c103130b510511405114141403004185094001d600050140c00c9810a0362a200498100740303a40e40c4c480303c2040c01001d80ca185001440d01c406c426030307050346e5010308015102103120004441c41405c1142c064500001008000b0010f8490141c01240d44203110030581c1c841d0007070826074102842c9a116440c042009410804810743c404804e2004151030101c294695403003030003140382c3c040c0c4000c860f040d07032091003650700501030005246400e040c400c068880f01c143c1c2c1d509004045000f2803154641076480128100300501d41504030182c00711360310500246a8450350800f40030755211507400608540e00050a01400800f8013030311019002c280019407418814000c010064402c0480700c081c003603650140d540f4860 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 986895503 1250 986894253 986894261
    0x1006090b330c070837170f070303090203060c0a05121e0c0d1116060e0a120f1115011e0f061d102007050607050102041a040503031b01 59
    0x111034404546100341c9030190181e070303064034104a100010840d802080e4580d0003083e16005d0140d616041040745445a954800030890b103141054649010b02550b410320300c8010240030950b0290354045600291401414180440a00303111074000080011003c01a00700c0125100107800140d1001d035540e074104020300191519154900038101442400010f18001010344603000c4102070802c41c0021138942d21007140b0030b072588402c6c140541c0031020081141984152100440f1006860212101d0341e140c0200c4061284a030b008910803c1e00e40c11105c0d4007801c0c00d004061060020048810314880307004020405100d60141800c002007000c00103180381c0c00340c1009110031000c0c00036003919840c000e800b4980030341c41d00d0007019821110441610b0002ca42e019101850345034001c2c0e0740700b10010550145594007036090148030300b580c0051907440300c500130400d080c0510001178650742000c0c94070140c0114010f100c2d010074003e000078400c9590110881e54600b0323012800b2400010214100c0d8054 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 986896753 1250 986895503 986895517
    0x6040506040e09070902040f06080604020c0f010c171e13061503020f090601081504140414072403050a0f0203240604060516141006090b33 61
    0x80040401e00180c0d80c0c14940079180240d654030284c408440d02c40340400120b001d940b260040000141400b044020302455006801c62009030016103041e44812050345040e8040f01410480d0b03564103602c200c030a038006500325070b030201d01c2d86000c114104107a40c07212504007403411101e6230200202141090240c0704440c02d00e10390000060010741040b0000305c40c58403051109902800b5011682411840d0104040c0e21032801612082c010b80c1b10440c03a92013003041080300503001965a090362105500701000c01c0c2c8954855840c10615507901c008007402c100701944104800620450b8980560114200d004840e6040b840d00049a9a8540c0720b0000780184060242450f407000040c405455135461145041131814001003e440404500788002403050b0b01c0b86100141050164000c0030305e031381d100d95039034900401c5607c2c042012260918180001c0a6500b100d9980e10181008055028050a002e019045070020346011001100e4000100c401304c0c0d03412600800d648a00c01400030300d0981d418 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 986898003 1250 986896753 986896759
    0xa05030616200f120403080d09060605190f1d340f02010c09050d2003010518010b06090f10170c130b1603050d02070204050a0b13050601020303011202060405 69
    0x5240040c1c0b115919004204285403c5014902400300202c8500301160100d80d030190000d46008104690b41005100c51a41241d100b40c44510004280d03540c02c680c1c1d81541602c944146110303250142c2d60403403115a610800301900754104003420340701031010301607006403a0201480c1c2290000c080b08190b40354000304900481000c241d0701c1e90b0561041c240b81c0400b2803038000b0005401000c105031603620b058404c1b942e01403203024070300d0001210036500c489020441d904249014003c0c0740001d00b900d004880c001030010f2002018403001e5003d01070501c691b0401e880c0720786086480d40210b000c10801508640c052103210a68840403481128080400b0401c041490380c10709091840540541c010044518a070f14110804071f4080065401c81c0c08a40c1204c0030780901c1c08040e41d06480e0b581011074443c04081e424000708016071100c1c05510300c01d0b4090b40b00040c000301540100905071900380001da119910b8002000622b9800004690641d040701740d10400781904d6100040e02803040783c2001d50 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 986899253 1250 986898003 986898047
    0x62b02040902030403110610060c17030711070e0c0a0302030c09040c1d1c060905031c14150d0209090c040e030702010e012303131a01030c050a05030616 67
    0x89076403099000d5030141e80b09940e42501041510782c0c1e039545140c01e480c8500100c8200e2020420300e4004e01a4107210307885a1200034281040d9549038140d500f04407406800715500c1c003682d00c503114050241c4400b4004160f801c0c9220305107210b03014114010161741c18241540007020415002c0c3c5d04094500e5008010710621650400d4100109910040340d103031040603201c4101c0c2c842e189001c2c481d5074aa0808803030520300890b010b8803900017600107524241c0c1d25001c00c0295074501c038140400124054100d910116401c158150790420303d54004110580c3d00540515400c0955a40340200c0b102c260106d940d41041e0305c424107140c1c10300b01511610380e449858420320300c2c0c0b004c0300031024018580c000d0700c0780d0540c41a00401501c4480d24040a01000b10500860000f089006805141c0241444140080c031721016a039205a1012809100807650582d0004004010032030031980701a0900341c602840c114075100103e507440602038801282c0000b401002441180700340d000113094010840030700 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 986900503 1250 986899253 986899259
    0xc010309110306091e0a0b1f050312031611031c0f020d06030204060e0f070c0620191803080705190b010807080313030b1f0603020d0515062b0204 64
    0x11350303aa1000f025810050398170f0b640c500e141100131401c01a83e540202e01032190b41c0e00d81d020b40840f2040c1c4003980c5a50407000c3c60200c0c094a040201a140d0700e80791050759640d0500c40c401910301e056440d1003074200511003c90700e00361070703000c42900c0000c2d64a5a1001e510209010701c1009000e6004e21441c44910100f08041c1041c0143c100d03404490080d42e00f000415113403410407184170402c940c081141c68045021807041446442d094540b28007800c0002111a686469808007600704000090b0310940414548402c02200b10200c2d00d00403141400d09410f04413000c9c1c0a5481503500c0040e00484020610303034140003040c810b0440b210752808075a40c40c000310b460140100ca8083c060340341d0500c50618040b81c081d000104641c00d1200c0c1d4244030102071310395503400c16945d2005096001d1b000480d092200c030078400c01c500001404540e1030142c0c484403c0d100403800c9a00040c41440c41c1d02e0601660b6a0607100c5e0403c44803101c034900301e00d050040c00c0340740045142c000b110700c002e00a0702c005000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 986901753 1250 986900503 986900521
    0x4051806030a05121c05270c0d081207090305070b0c070807030c0810090b010b0703030f14070e1c081b030d060f0b03060a061b020603040516050d050c010309110306 72
    0x10030490072179113490202c9014036410341c07003180d104646072411400310009100070441ba106803a140525058112800702d01d11030045411840844000c030391201c1c010a007540100c0042d01c203658007040a161200d103451640e06e0b204c3d954944d034812900b82c8d840004007001615000e01c840d0010300914002c45080c19a00d2806803c0840d1500c40c0c12118041c1d200d0280c0c0c00000d501400d00003d030000e00b000b034203908001482540c1d07400802c1c12020b150303552944c0c1e50341d100a801341e16510034041d20501c8981c07a200c640504009030014506208000040d00344460016901510080c2504084010340b6818990702c256014000403c55102921000c1285400740480ea040402034404124010050950351b95a449090106460003640080e2641c81030010920030b02c1c613084c162001c3d6040c00e8a0b005e40d40c0200c1e0565000750703010385d0359400c040c040725910070f035003a007120082005880201c10403030380b030300c5958540203581c4e507850400da00c640d40d00f01402403280000a00134401000e50303015007040300c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 986903003 1250 986901753 986901757
    0x10b0c0307200a150c02040f0204051c051b090a090303090b0a200418110d11071109100e0702100f0516090b0f03060d080f03040506090304051806030a0512 68
    0xb1600c190a40c2d0780110380020b0255100c0c50801c101e458000d928401da40c2040701031b0490b0080341a80550130700000556503601c03040742e54542e000035800558900340381001801d09040c211043c1c1a10803147e40480d550701c1c0c1c0c12540ba800050b00740002810001450220b024000078600a170501201c8010300200381078552001c10100d86c1142c00c07074051441c1002c0c04140d8000d6110310340400320306c10642c01082c1182c0e0001340a440360b00005918140a29040500320b80300d4681245c1000c0e00850030304101701d82100e2540c0e481c2c07022107107024103140c615244014103110b4042c1c038440c02c0900001c04c203014020480300e030002c5491b00302441140030810101009010450380c0c01070000d01a828100c0460050446005403444141c1091810f00301b10390380c0242d580040e02c110303004010014000c004c520b07001c010b89141e081c40c0703071120342e28201410312074030706803000d00f130012150410030042100f07940d5001c440c8034001e0380113250080f0313941303460000741010035952002d0018003e540c001e001c90280200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 986904253 1250 986903003 986903063
    0x140709060305061507060b091f0504060f180e12032203021e120a02031911030702280f050a320d120804110303070506010b0c0307 57
    0x1840450156462a0403000c0c2c0e0740666907160402c1402d5010b400015196004104280c01400003143d030340b40003408103540b480111107140d25034070359242145021080c07008100041c40101c806104681c03c0c00c2c8201c0d000951442102c00c03089048244450728080c035001040d03c8028070040d5445d1141420390741c1e5551b03200300c8080c3d4901c451100b20244010740040303004982c0d85c05500804001c0544a05015022a0100651980d228041c941c1020780c50000c003d0102c50b0a82d4081d40c3c40c0c0071850707070b200f0301c200000040d5004d10440c00b0050f50310003000001d031010030b03404554545180041180d282c802001d92002034003d1499203401007600040310100c501181c0065510050305590fa0411001c1c80c0503000c3c100a03030716112801a081c0301c00302011141c03241d1300246030b06000b602c07985d540358051b09113a002c10003080d4908204030611142100784548914280d01552402000b65602a10303654140100311032200086100035915000f0020b950702c04d54028080f5045058039220910307180c00200c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 986905503 1250 986904253 986904257
    0x15050c041404090512161e1109221104050f0f130b0f060f0d050609120a050901080403180e15010f081b130b092805190302041407 57
    0x10a03850340c1c034100752045000d15038100e409403400386011440c0d4540c0e070307124000e001201c05444680f0000725050300a95500c1e440d4550711034884428500d81103c01c2c44402c098540301c4e201240070003940001d03000340c588a082c640140046100498582581d41d600540b50458029161804100714004000002402200103206641d0259990700c00701c0032980c00007000900480d01000461007c0e44040041078000c03c00822174052803084601044043e05c0f0b0200590381540004d00b44080c2850901c101803010145440881c609078000001425520600010504010b80c080003d0240b602c07039620701c428070340d0b59a01040c01c1507907481b890304514016a45a10707040172490b550742d1158064510021452002d0b06d0b04950b55664000644462040b120a01503c860030000d0822515100030920080c090401003551600c11410510108106005e01d0710004419a460001c054114114000441c1c00450f5500c000706640301104e50112101c0e80001c0d0040e090100701101e6000351010f00784030b82425 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 986906753 1250 986905503 986905529
    0x40605030d02152211041a1e040912090303030b0f10110106050402040b130e010e070c05010b090a060e0f0106080612030d151a0a05032412240610050715050c04 70
    0x1c0c00381c510f02207c82c1c141154031125449481c6501c81c900b081e07015400000500000b0b09142645401003605c00000d04a400220b4080060040641500c2044103603030741a12003c584001400100392000740440c1c0030030a100c0101d0705281460401d4001a0190401400c155121650784124040c2c580100b00c0d205901d000f03050001c01e1099203411064121114101042c4c0a5100c4545c240c1b00c5038110701080e5515502ca014062041e107078280003034001c0c1c1200100048072441c240e101c1e030454a0182035203403a200c815004108071030348031501d03e8004d401140c1d0280c3c9080740f00f000c64a144640340c5840c003550f0400c603039034200a080004410480c0c0c12204100c5d0062a4181c640c03226106640c20030780810f1040c0082010115540554415130790a0350410229617040310010300d808101c906041401e5120318861425404040c3e80080d0302032840142c19140c0c00d151002419449200fa06602089804125101030042e040808000c030b0f40038241c108510304100c500a4501d6225000c2d0080c41030b01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 986908003 1250 986906753 986906771
    0xc13060e031f090c090c030e1b121203040b01060305070e0108040b070903050f0303070807020a05030f0f040806180c01111906111305040c111b040605031209040605030d0215221104 79
    0x30108916055003942d54008270200a048104a40607101440310801c2c1c1c403c0e4490804c140d1003090066000745e0140d030f03201d0341540c5458030050640e03000500d424200503440000603566600440c890703411552050700c3c40c08079584d08004881140740e650003c5c0c4144102840f44200d900084000d6000e036007565600b030034079501d1810a0360b0341c0020460040040e8001c000034101806010060108071911800c4203203084d0740c0e8400189003040980c0d462482c202d5401c0107a8010000300030b1108000d8080c2032030a42d0b40d8120750f0058480c40b100580864031030106c200c040c01c10485e98000e41d880b071080d0303145036201d100b101100c55410000b030041038000c83c42e284600c0403560207514140d1005900c40000c003201c3c043d0314400d00c903c1660100407600543c42f07200203e00b0366000d1105980e01d0110680c841c0c2c40b490140100401e03903c1c942c2c4070320f0183e0007120070244041c0d8045030008120312025a04055901c400d4805106c0b002c000d841d04101d03c000c0c0301401c2c05c00c0010020362610020840f014004005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 986909253 1250 986908003 986908031
    0x20191209030806041a131e0905010b0a290f0d0504050d020d1d010c0c09060b0d06050d050705090c090d080c060a110316090308030c13060e031f090c090c03 68
    0x6190103900c0d910004801c044603402620347c03c0010080c10102c40078003030790001c2c0c10440648481c85c4041f1100d94440064030b00a0400b084054003c0141400c2c01502940b201d8280e04145403801c4100000d500001c0e0340c4076503840000440b05101d08040f410801031601e03081150715080b01c6810000140103485e0204d5031540300d840c1c00300404559030046491f5041000040d541441480004c6401c3e0544007000a04c200c0079104220040c5130302403200d076840f15a01041800c54901c0d4004030b101d200d484010501040c80024240d0955174160340180f060b840300a40d000f410b002c4d0390304980e4001c1803120107004000c9450040e00000c01e20350304548103919442950016182c03154041039170f16505000041c03120003801e401c104062480e040120865442c0c1d246c0c040b66510484912140c01d500040300e41120b501203103240000c041d10714181d840c5032038000000307450302440350313203004615102484000300d03d405078803201015604c2002c0714860f40c4d43d43c4550340a0003080d0140d0000c00c3c0740480c0c000b8451 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 986910503 1250 986909253 986909291
    0xc070c0b0c1b1c0c05010e010314070305040c120c090f0509150612030c030901090605040e0f0a0b0d0b070e0a0609050d03020313182019120903080604 66
    0x40d005002038220a10140003616003031030b2a4441a511400d408106091025002019140c050081d0b00600c08182024005888140ca9103215030402d403400c0c1c1002400c3d046a070001e508401c1c607240200d200e40b6039040803c030b00441504405c0c41c506407140071104101020017100200c989081c0c05100c030b850702d0007072541114000c03110500a42c10138000140060301041e150382d40144000d200ca004002c403172903014903681010f041866035904c0040d244003150b801c540c00800500d89454101c0c501420010303070500128020740103d40107243d050100312800116002950705100140c0480910701050502160900702503034600c000c03410010403c00d55080050303d20080d0b640648815481c0fa00d441c045c8111415035034420f80c1107004c00d20500000d043c0c004610401841d1000f00300d00300c85480105d00c0202e41441003044581d014051802c8681036402040d500c04000c079455080301041400b0055a81d9050084d210500710300d01000305003019080702c4454081c400c04d0f078081001c4444504665175113 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 986911753 1250 986910503 986910517
    0xb07020a060912020918030403060b0a09050103150903090510021e0606010507030819060b0a08071701050f030a0534030807140a080a0305090f0714061602090c070c0b 73
    0x10341d80f1581e026041501081d50403020440701142024103e1081500b590420341086502c69103c111403e0b544c5000600d000150052402c03c06c000e515507176821409081d01c02c1e00120b034907117845052041c58043e07150600103001c003410100e183c1c2c0003c80002d444084000c0380040c0746c0c02e180d41c10b1a04140000751031b8400d180613110b4510301501c5441c16520504000e02c111000c002803124000f40c1403180c0140001800030440c250f4484210040c0984010002170545040145c0290780b09000400c2e04052811100300b0f4030a908140c0b0b00c4c40100f410a404403801400900c03030380505c50000d000e844c00b00c8800b40141a00c01006844520300000c051ba11848040c004440620904010030300250602c664404110212008068a561500142d802c000114804640d555041114049042c0f050800346c1c200d24000d000030030b06041103804044070b1018081d01511001c0b50084500c607140c08500041500104600e07401d01d45400d03211250340c041842264840580c02000481500e103609840704 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 986913003 1250 986911753 986911769
    0x8010c030e1018061503300806180f011e0b0d02030c07050601120b0609070c081c0e01020c0c01050a09050d0218090c100507030518040908040b07020a0609 68
    0x29000c411101018048440707203c880c082c0c0c07021070b9a0001d880ca20407480d4980d84414641142c52035405c100e4000c911161442035141114a020708480c5e018440e8052170302c4107400c040341c650b21600301051031500c0b580142000c1305058014012801100404603040b1a0b0106c1e60142007512540e40001c00e03843d0f48100d4031400020300c02c2ca41d030710307616801640e800040d009000b41451b05507154640b070803200b81d100e015003e51480b41c0358103004071202507075403180081c0c0d806e528500780b4010040c0342c0649500d0147c0204000700c0c8200001c0b111341440d0f0b1021000b41c60030302181500e509118003d42c046008894603108415000c00c56500400607900840ca40352166501d00b8907000906c581c0d0382801808070fa000084090880c0c805044058282c0285084d0780180943e00d60304091080c00700042c04440140141845141e0000b075008044441c90300003082180d10080d038240c0400e0140015490003440210f021a02082c600c2907c005000001d00032242640441e998500603180d1589900800d48 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 986914253 1250 986913003 986913013
    0x30215040b030a0c0311071a0609190b0301020c0d082403030316140d360f060b0604120c0608041a04030215160914061e0904021308010c030e 62
    0x180a0320154031100844c000e504000c0380001210314130b0f901c568003141c0122200285954110050130100b4002c0340d000b401960941c45a040085004441040f6441c0c051000b07506d5103204415130f202901600c0c415040c0000319005c00785110f40141c41c10504440462600c0240d8015a030042034445210000840145c041d603d1501d4400050700704c0080e4103031000511003041d501700342c180211401008400c00032800080ca40c0c50310207160094007002c441d401586a5204112201e020a120016202561000d1040c020300c8691030f0110141c1f06040ba8240d0040f8089400070b4040c55030786141c101c1c248100010581c00392203000580d040c680c103413000f900814840300c181140c00350480c045da4126000780122516851031030300b6901145412100351140070782103410040b541d504020090054030341d1182a00307404128002144403401000542062180140034500c440c05c50101116550100a0819551245a41c1131003007070540912442e5440c3d03180074a4903914900c02c1c815902c0c1c440b41140648 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 986915503 1250 986914253 986914261
    0x60f0609051513212f090402030c04090618030e010f08010b0406050f1e18030c0f0f0607061a1c020307140a080723011110090312020a020106030215040b03 68
    0x8681c0440c5031504944d50300701c11550780115000c580f07048190301c500b040300301005c4800c0e801c40302401503080149003c0c0c0ca50009020041e9404690800f61030010703100042c4500e550f0602501801c102c00800c07001c500a000507505140d0701c030300c2d6104080c1003a01c9664080d0120f0804a6550f40d00348520200310000b40000d0100d14843c50040800d07071031700c3c8589410710218005203c3c407040d001d61101880c00002901d5000c41c0003c0c03400103484601140502000e00c0c41d100400e04130b982c00c0c0f054502c98648071100741180e55424068400e0701e03420410030000305203003a2605482c481c0b001074482c401c035000c1c1030005600d40714011440e0542d60240180c40c1461070924500405c0703018000a50b40000d54400c0414401000c01c428001803604003041c004c45142d030708551070b0744d07070682e1800d0741008091a9824004100010b24a000d507104002c0080d0344400c604044a50286007003281500354000144d91420310b5054100c00300f42c900854444d103192400e1610000c0d10b100f684204082c40300180005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 986916753 1250 986915503 986915519
    0x3080d020d27060510080615030321090c09010b0a121b0203040f091b0e130908090307060e0a03020d080d11190c08030a0f060f0609051513 61
    0x54111049600c002091642404003481000c2c0e200b4488414500e103403504820510400307006503508102c200e840750000d0b904007011217464010041031103c007600030001c0b140c0c0c05d4a0420444428560007800b418582c1e0104021800c00001038030f030a403a80c41003013400d03060f80c40d060400d58100d03142038500d10324042c3c0390941604e02a00404000e4a050303070f18101c564680070071b4800b1046142c80b5602541ea0b46003010f07114030b0300d00110f4000826040c64440c80714075400e204800040094001c0c1003400802c0c1d541e0000496408000c0b61844605041c5103a10b01005100380140500002c00c500780ea211584803001194600404420284e1040802c6002c00260400d6101c9100a0b800354206500e0030749945040340079036034a580c241c00c48990010741204840c1220324248010151403034803145c20101030700c420540b8080980500348141e540c084280b40c3c80841e80c001c80041c5114100749054a640d280003800881292103007038060310a803210414101e4410088884d0310070100e1018172150700346110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 986918003 1250 986916753 986916757
    0x906040e070918050f010501030503120406020f04061707020d1b021f09030b090c150903160e011a07020a030602070213093e01050d0902040e0303061903080d02 70
    0x644042401003003400704255980e07001d45a2440d000c1c4140f07456200f2149465490444c04507242da03141c1c1d14100c0103000148002c801c6076008000c0c50f0b05200c2a445604000e07001384940007021090071000a800210a90000300383c1d0039102c048294507071307503540300358050761991034140107000003036410054010200128a14064054001362611515066030b10020301c00c410380301001c4001c038280d03038420000c0290031402c19038040d40490141040c00c1c0c58401103041e030700f84891900c448840218001c240380d1010006603034070041c0080704114085d5558842e00d501482130260790704615032442a41303607406121084454107540940401007440c91903e80c10000c0d0043da104a078801080c80310b2487c0750946006d044442d03800307800c510038450b940154007460722400940c00e043c02d480c200501610500c1c0c01203240c685640a00709a59a5060141030000400e10036070300950007490300c06000390441c030002c095840760a0548003c401e000103100402d00340101480001d050311010000d03c3d000880c1900 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 986919253 1250 986918003 986918021
    0x120c081e130212010b09010e06030f0304080a020f120a030c15060609032901090c030b040515010807020c06040b0c0d0903020303071e0b0f190213050d0f0b0c070c090b090604 76
    0x5d1304036180c01c0083c01028003a03006410781c20000303003404614501440380841807070b444002103242a1900001c142c5404c030f4210081c2c491900489100c485442d400108141221540152440c4007058900a49000c0ba40d501c242c1d0620345001c403440302201c00348510010340d101d81d02c480815030700e983c1d200b8001503551685003903e0401c801c0108014010030180703901030920b40780c0c04038129035414070060403250a0b2002034412030400c424042c080c07084c1c040c8021038140c00e190041081c0e5800c94142d150001d000405604200c00060010f640c2c02504094494035040000359095040e0011003203903842c0c054000a94540c00400c26100080c03c82d00501c081045a9003901e41c802032151a1a481c0c99400c441500c00540302c113080042c1710081c46030100c40c03500101021800c04140c181498040c039024060540140e0000348031000b1b01c51156180001181e001003032140502d0513a210703000075044940115014401d030301c004106450036004140345640080d01500d001d6545a0402002d444101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 986920503 1250 986919253 986919289
    0x507091a032502150603070b0d0504060b1504032307061b050a11100c0c090f1e0b0a09061421070b0315030703081603120c081e1302 58
    0x2e0428110482000c502c02008026500a403861000241c50041a000020a098420303040b61030305010541460043e0740200b00220000141ca603900c1c90800014100501c1d1140e00013200380e07061050788044401882542d10803c02d407001e80144c201c0860300320030300303440c04032480e00314807003e109892080345a1180e044a0613403000790881d1944405040c203000d80070903211442d18001003841d074108810721040c9241280b61581c50710307655072a22410901c0c075001d034681c100e40300d0741c070a0300f0ba80d07003038000348612041c00210a40e022090b1078000000c1c40046c200b1030260000120000d61018148100c1d0216a80d0259010300302c6902400c124140481000e2031240012f0740c40d0328540000104800c001410005440a683e0701f0901250003080240031545442940210014000100880259925002840d180c0704c0c3c102d40a00d81900c04528a001a044140c50076074003025180c1c1c00800c0600412410400f681d464101c15854403e0100c1218103464400750018817100500300705e010700d2080385543c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 986921753 1250 986920503 986920531
    0x90f060708072a060314090a02010c020111151f0501080903192708070f12060c031413020108060f09040b0612010606030603021008090a0308100504140a0507091a03 72
    0x1c40d44000e401c00f09034100703100090381c3d0281c4103800440003080c2500300c02110018458250703980e000800101c031748100207040102441420b14021010094814020b02100c400c0c01589010020070010000003003048010260301d0b900000c565001389881030081a401000c0c52a00090415a5040d0900329036070b00200701d000302d4503807412a0f4540c4905541e040c2e00003003c00c80b524040445142c051a40c00c540841d510340101001402d60956000f40324950180001c980d00c802640107a00400c03014001c400c800e0106420003100d041d86507070040c982071003601c6640e41d688941042c03092101411100b40d40221042010401017070008910f2640403c1c001e10040703031075042c84109803c3d80e40300e50044022a84422040c4110b1420301e001241c040c125141154440c82c141010950300d400411019007805005008075610203404852030000d008060814410110407074600343e14401c080320308403905464180403801c20fa06c18010f65041307617508000b6007144d160082c4581d0055201400707902c2003501d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 986923003 1250 986921753 986921813
    0xe04080409020307020c03150603030a140f07120315030b010b0309160815090a0302070b03130c06050315090f01061b05060403020f0706050f0a12090611090f06070807 73
    0x707a00040d441160f56501070450000c541d070515103071181001c0d50459401c40f46c401c010058600006603500e80400b85480c158401d0a0540c1030324900c50581448049100068010141f140f400c242e45484241603908001c450b14540c00718003032501c00c2c04000c04410025004110f4200030202943d0440985015a02090a07406001d40100491350118100750041c0e55542d80021811a4550340120b2170301c0589070140b003541d0000c1d200c1000380221503c103900070011911468400541c030396025400414110102c1e15200050015001100c110b00254401504c00b440d90516014035800740382c8e1807101001c940d09180e0141c41d5030080009030072544406880720300100b030040104501842c040e801424000f4440c200490070040703242c22501c14372030200309088085940e07208461000c00c6610b808091a0081d1080e000038080014000e4010b500b4800815004900c80c8000d2081c0c0e9421101c184411100c0c0301071141e40d009040c80500815000d00018020500c074404010b44044580441c04403411 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 986924253 1250 986923003 986923019
    0x10c06050c1c0c0f05090a0303111f0f05130b0105040506010e041802100c030c020d03110f060a0f060305071e0e090d090f0506030403030c02011d01140f0708010e040804 74
    0x100c0c050b8824240d070340740d4041e004820341111100e600c088152402e1391034000d009006c1036281c0440d1200900708100c1071000d0050304402e01502190707900245031741c00310740d41d0000103502600740c2c1101112110301e004045264904210311001100764040c2d20120513a2034081080010500100b8050601503981c5e51844c00b5641c41c0304049055a0410561694040500600c6040c0c1120038248040c0004600454007107031b04155401e0040b5170440d041d012801652404036031501b1041400049881100e010303d6089038003052092050591000c01c011003010352200d20b00351241803002800f03d030801e00d01405119500004681c9800d034281c040705c140c91b516010144140400c50352545a90401e100b10000c41e03a102462200a28120032451070403420070f0000751141c880a840227081c19a2404005110f43c002e4000404000004041a001401c00c0300610b0290452003844041e55000b000042c406440c0f040e0360705e008d24290f940d0394071540c2c03e108100d89840d00c05001520608814040061141 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 986925503 1250 986924253 986924287
    0x5090310050f0138090a170c0603070f0c02030f030c07031106090a090213090c0c0605100e0c0f090a09060503010507020d14180a030b040c1202010c06050c 68
    0x540c850015061030900c0d8214000441a0040309040c1c84071803510403614419040603600404405041c000d8070303241c0c40100c041d0f22a00303003107503004106100002250a50a0715100000b050001960704c00c15542d02040054402101c003900469407041103c00c0341d0780305080d14400a4406800c540c07a5840c00601c440ca150031016001c145584805d00c280300700400c0b400d0322813210070240c03801420507943c1d00c001031000c40305004070100960302103040c803900c15170401864001c02c10b4210400880c20b55810051107845400d80607201241418045880713102c0140200d404c691910103802c04589440041e010145d1001a0807540c0980a0010840c01c0da510030107070005100302071001510758505000d260a66000502c02025500220b010385030140e003000c04a515100908107090307983e58059a194403070700850021680264010002008111b82910000c3c0114043c080140403569035286403410400c2d540402800503c0e059610320000c0e0340c41e00060340061441c0361940c14498000d000d02c82407 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 986926753 1250 986925503 986925523
    0xf0c10180306052e08100b2701080c06091f051306020c010329060c0712080304050616021023070f11010603020f1c0203030708030702060112051c050903 67
    0x100c802da8690548240411000325030090705243d40514036403030042c80300c6e103c0c00303100701d000c005649800d0340504a0f504c50f2005100403c036030042d2084101c80b003411016001c024080c1c0042da00c039201920120340b51900641d01c09a900a00e0140c07a41c01c85c0e0201c00d080a0851500c00900c43c0921400c1000e201280009000e0010390f8001c0c42040d07654400101030343c9410040b864124128041000595103000c03d86801600c20381b415a611804081758a1611006074072100300405020311000800044000941c02035020b60202c48031610b401da0009040307034100b0034440241c3d000f00f64810100c0001d40021038100d90020240f40e02024807194000c003440c0880e098070004038442c0e01c540e0303915001503500340d0151011000700038085c1107034003040d07040b40b0000d540e038411141100c1c1e00d9400f96000c40c90180e910b40c06025a80c68031010b25008009400582d01c1c1c40c05801101c0001c102c0f40741104506483c2508500280030b6480c000850540205080c0a0a42004070411401c1d2007502d00700614520 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 986928003 1250 986926753 986926771
    0xf1e060f180a060f050a0807050d14060a08030301050d120314070e120105060a090207080c01060e0f01060201090b0402010309020118122109030201050c032a0f0c1018030605 76
    0x1c01184a0422003000ca95400840603c001852030030301042e071080559130540b0301401e020302c031521240020b0702c13a80102004039180e6410441e50340c01045008810b1030040700700b80c13581381550340c99042c00d640307a000034050280c100c4400085500800d0b0300000006034404282000200c800c60601003000c620340480d820800304403401a020b0f11414031011464510315408000c01043c14a0000200114103d00c03034160803d4000c6212000e0084040c120355262910348020400343e640e80d9030705448940101c0d441c040d03078041c4800005a40380180201c049256100c20720680b0b9a4455006400401d0b246030180c0c100a910b051a445030030845085402428004161030041c2c0c0131450300d0444200329403107100c041c6005544d803900550700544030741d0540313a09090084d15031001440291441c01103500c05417641041101e10041c20710b400041050ba040c01205072a180800c608805aa8120800100f6081050750b41e916800511815010b03107904111003440074465540c0d00c0c0c0d07074240d81c426240160 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 986929253 1250 986928003 986928037
    0x1030b01080c090103052517010c0906030e0304060516050105011e090e0c090705120c1308150a0510092c12030412030912031a0f1e060f 60
    0x10203020204a00009080216045280f0358110303136505484040201c4206000d403101c0a04142600c52401000040c00c041c407440100101d500820350301038824040341c1004621641408180c2e10b100e406030a2003164440019882c03d40f80103000c84166001c01184116582c5009401000900030f004e201c3c008c00c010544d801c1c4042d04414400e00e6040301c0c2d03014110080c0b0301411050107140c04242c0000c000c00441d813180140d0340c0d58000390b03401d00c40e40300f901180c003901c0c10400c6840c2041d1800303402500003481d80242c005469411980d41c8000e40044000504c0141d000150204c0043e04411342c080d9041242200c030366995502e042c20f4a008501c0f03000d15a150301e02c00442c510900001c8104040403400501c0050260401c2003054030025001030b002e0f148907580d440741c407802604842205544264000740208103020700070001c2c20545240405140007154140d9107140ca45106400740c81700507c07400882c0c40c510700005171004030280042d00700400740020f01c0f80b22400300107002c1c21002480820 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 986930503 1250 986929253 986929259
    0x27061701060e0603340f0305070602071d0a090201030605040908070506070306210303060e0405100615090b07020f0607120801060c0b04020913020307063c0503041a01030b01 76
    0x103904000010081402a0b000c1c14a04074180390170700c1c811000d80d0030309098a0b120a1810801400b804280d080740e5211034030040b00100300000050b009040711900c3d401c6d5450b298440089081c1c034000b80d04d40e20a5005d110303003c20280c1c2c8241d0301080c030042c814180010003c1d915000300f015500311120503601c011010440405115040c089541d01030710605d42001201e04281030307a1200c085600080300c0405e0000f040508041c020740c840c1000d03040c0019030b0b40e05440d2514109540d00c07860000c1c01145030810303a00088103280c0030302ea80044401515809617050a220f03014907980c1016500340d0748141802007240898803a2001482501c0c00365a0700901c0d00481c0e0390180884c1c82c1030b030003002001805004000810740040300c20750030582c103c13410f47c881c0e08c43c5070401010721001c04019606004400b000281a9000310410880516141e01800c40078270001c800c008c200b181c08640d0000c03901e0180c0541c10207119400565001f440744a0200401900c1800484031031002d130012140c41c04204018 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 986931753 1250 986930503 986930519
    0x9050601230301090302060c032802070201201f1e02090102060f0402130504050c12030a02070509041a130501020d021806031b091c0f1205042706170106 67
    0x760503040c0180e0091020015580d170007540c40d04001d00040302c070b21005c40456940b09001c0001000144030488030341c080280a829a07000350b001a8089001c100e203c542c810300009084521000c1c042e0000c044c24104046181000316512201c01d416140741c1d982c20008201a40d01402050703039180e0341801a240c0791440c001a20708940506169030700c1511304200001680d48140f101d80315110408085001e8485142c85d43c0740c290005080da07800500c400c881400c0f60300c00009001d2141a44e802c5504080e0384005000e8500c00594010300896150102009145c3c01e540045402c104540044440544161120381c22a040501c02c559210340001d001100d00842d280c0710302d034040d02250382500d1400c10b49080c6030303a6991043e50342100faa020914400a588001118685c80d80340c4070b10008001207803510400d41040b00d00700b19140c0400c03d00d155203503403184003910240c400103400d000e9250500c00d07220080a011000c01c4c0a019110345001c5200c020070b40c88041603019a90010030000e044c03a4007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 986933003 1250 986931753 986931809
    0xf1401140312280509061803061e1501020a0f0503040306050703110d090203070513090501050c0310211505090c01021b28030309140a0e01031509050601 67
    0x7119808070140051400c0d59a80c0c400d0f420060002c0000c50b012071007115055446002e0207541580c04600404d5040f40044903100508081c0703030441c203490b000e80d1004846c0f0644180180c1442c100d04481d40000c0c4180e043c82001c007034403201401290300490081c1d558006000480c4d40403070b19a0408202002040540d0041030380104440c05c0510001c00d010041d40c40c80d008001142c07080540300d440c0041591424030200000d044050305120f4076100180245001e03014002045500390b00c1d0038002903142108405681c0142520804003580300d1502c14044140000c8030b0700149003500f030031030038800210081304c20b00751040c5c0d07894045090724010424500b4284039034801c80c190b401c042c86d85062102c81d80e0b0b640c0c4440c00100e030020710074000c88210542c0f0343c0d0340311901903500c425020013205143e080303105030303045075011141c071010a0700c40c10502402440d54843e8600d445020f400500020701c2d000304014145507907100000b1042451744505240680030f0348071140c4204e009e804090514a0030b40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 986934253 1250 986933003 986933023
    0x30912031c11090405040606050603070e011d010509091e04030c1a0f011e0506040906180605030a020108040f0c06080108070602010207120516080711040e0109030e040f14011403 78
    0x10300b00014080c0141d5109503108600d1404e216a40d01c0d8001400c000041d8445006040082c00d0b20b0703100e2601c0700c00940101100e06010b03011611220144204031002858440300140694603981041035200901006034400741420116030030300f40c070100c0544003165029101d0741c02644e541014413424141104140112245412074900030810005022030449290741141e281c81c400c0c06032512812000c000b034268540040780e0140c400940025500c80b2500314000341c8500301420b41e0b144045241c80ca04542040c442c9680580040c00003201641c0a00c2019520502801d003400b4a40e00a076200701c1405000d81100011484000c01441600c1c4104050320160685000841c41d0002c680c4035954210038040001e02041000101040c0740d1400701314504c80254010601e50700c8200914005a5000e8890f0740980620310b8804010380c02c0105010f20045560142c41d030b9620f0820030028480134140c003030090351400d5201c00c0c4894400c0c81e607405581c000c01c5481c640103050703110303d030402d42030004c044 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 986935503 1250 986934253 986934307
    0xa0c0c120807110315181608060103061d0c040c12021201090f1a0904031e0e09070504120215090a08060901050f01050114031b1215150a050c03091203 66
    0x12a400618461701d10380c0d5005520070311904059a054035200c2e14152071aa2104081e003425070000407800000621241628410401400b280c0300c1203807444103950018108003096070140101d00c09505086e0b100202102d004c0c5041e04414410522240c20791707008900c604010500c0034010420404244034654440701312110a201108015681c0514000c2041480d031150308228086002c0500030802441c0404540c1450301424070b0907040a04040c0710405114000c8000c1d00001c1d0304075103d1350454054411901924440154617003e0000c40031107810050903000c002c100d00c048540c0c55414110051543d20010305036450310411041c207540e0b0107003010700b54424040040c0100d0f0f810241c4c00a1450407909040c0c0c0300d0f500e40010200c0998991411072480c08002680f450b06001500c0d200c1c890014510b090030340e0700b981e60034015440c1039002ea15401c81002e2000d8400c841c820401031181202c0c0f041100e0601e210903001410a260810b4480016400000c881d94074049190508801c40688 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 986936753 1250 986935503 986935513
    0x80a0b19110328180b0a090506040b01290d0c0e0301180213090b04080f0f070b0115021203061509060d0606080a09050c0d03122f0408030a0c0c1208071103 68
    0x3c4050000030380503404020142175485000445402082e80140c1c03119401200325080c42c02c29040c8421061420b0107524040c9042c102e80303400901c0941c03103820003800d000008900d000f104074014001402046000760801c00354040071581c503a024081d40c4083c80454036061100311162041002e0642e0407a11118180d00f800c07a41008178141d00030b82c65000b5040898103903251006003e04032103120b181031107410342102084c002c0a01026030005416500110070f41090035860b40301c01e81c5e079a224032090210710030040002480f141444c0a000322010f00b900005800d016549000501c1504041c0c0000240c5075606000c02c0300c503511400f4a608048009401c0003584e0710382d160161100c3c04110520f0050340d034403001e94200f5208680c21142000211410080c604045180c423a100c24900319a0540d14400701d002844032054400b1203048600d044021860420085402c1c1d918840d40103090341d030070b00d50b5980080d01d00035000c2c2c0c4141c190720480403140d607101c4a18004804022010840e402a400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 986938003 1250 986936753 986936771
    0x1b050409060504150b090a0317040905090336120c040b010f121104030803070f0f030b031b01051b06040c0f05060702041517030c07080a0b19110328 65
    0x141901e4113040e42d180d1807400c3d640303102502c00704040540651000340390040c0c00034488074040746100500141e602410061249403905214980d89002b8110307141c4441415190340218601c1100241042843c124a901c2014140e0ba0000b440f404803d1b10b014100d402400192020f8074203803080c20300080c404d09080000f00c1488900038060000060398140c041e550340b0071840209892015100150750010160340d40b0300c0c00c107000030080344134120420085800d048a0b25203150084c007460541c50307005402010702012004103004059060b801c0981400b204000c501440c1d4034002c418000c15032460002c1981c0e0500d40f0341a50402440e602440c20041c1c4000d0070300042c1d4840c0c00f299031032501214041928007000e5000f03001d41605038001001609a4202d00c1540100070020b000d04102400c103841009903105131403a10307410f0481e8028465a001000102000c1c084074a6803d52918603500041c612480c881c2d040d0b03194400d8441d00e00a07091801c005190340a405100107004c96400008c0c04203c1d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 986939253 1250 986938003 986938031
    0x307060605011e0327080703030525200303100e0a051e0718090b04110306010207030b04031101090803010806091b04090f0602070308180106050108060103050a1b050409060504 77
    0x188024020801d17441d03001040800981c8079500e500a040303034041000702c0c1010304c1c16110542c00800c04801180c100400a01020b00c548a00c3c410352009015501c03000204400c01c4403445d4510551411068510030401c140034400c101031841207030340a03400041581884a0444c810707034014001c82c4118203041c100101001c0d40c2d40381c506007503141106400640c441001c103a03650510f03100707407656820141d40c00140a084a40100300d074200151000c001c03501001e070207580103110443e049805640324500401c0090100140140c0c802d00a1824600400c03400100c0c60a5444864098a0200c404070050210903404d04c819900007103858010154000d5050314183c60b081c012200078072841e6a00050700a01416168800d0308540c800380c11540c03481c05140191003220261059803607051984104c00698030305129034000c0c4c2d08141c5075890305a4503500110090980204608095510b0707aa4584182e0410b07582519040425110715881e641400303804001c5031070301ea02a501c07072414828071035205c032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 986940503 1250 986939253 986939297
    0x80114010f1119051f02071a19090c1503090c1701020c0303180c0109140922060903081308030c0d022a0c0604180f0b03010c02030706060501 62
    0x1d602410300110001c2c081c11441c2c244800c140c09620b0758490b84441408011021a2a817982205602c41044402c99894003000301d000b8610010a1050000007204900203c044d03441c1d40300007034410180d04c4560041140d01501c0c1640da0848484c5080c10301030140100c148102070340c6154901c3c0407c1046103079113131490701a039184100501c00100d0116607c042e02d080d0111200810000101d966034200b0040380c0014101c0000700507240d004105031407010790b11903642d10b0216511007003020f08060a55040000c8074901810751092442e29090b00041e4441035030100488900440d40020048114140503004120080c0707176091807c241d42e803900004069005403600120261002a150b42040600200078030642e103019003001da0a03851350100743c543d0302407034904000b0b14041d1101c170140481070120341d02070381c001c40e9180b05440c00240030004003030344170000c01811480046800b0800c0382c0840d084400901e50140160070004000c002d10189005801c01400300707191454940ba40c03040410f90003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 986941753 1250 986940503 986940527
    0x7050d05070203121206090403020f07060801050f010c05100b0105090a060e190f06270f08010e010c0c030e150f040e010e280e060a0504050d0f1e050403081908011401 73
    0x2450a0502080505208000314100e410bca501195000da0300c07118058140c00091141c40e00c83c02406034a903d041d4810080c440e28584e02c40001e0052441000d0400c02400b00d10100a0400009204500850fa1141401c0c401030016840d0b11581207810307c1800070a1074044400960045000420000131081400c19002c854a516181350301ca482a00c41d184030300401144000482c2105002203001c1010118807011110220000c1000907081140e031402e03121060020808a0040300c21500800c0c003404240000703100090001880f807030611541c20040d049068240c01e041c40204007444070001a4020a02400202c44486200d10744200015480c0030980c84c02c12000846500300300c00e1081e0350f00304813070001c03011050380e071180f40442c1041c000701421141903038144500c10401450382d010f86140042c0b401e440d5100407451881e201020060248001c1e1041002020003001001c200e1240150175041001c03400d04041d40078401e03000b0072404040c3c00c40c510300881c624140846a810820f40256 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 986943003 1250 986941753 986941759
    0x20d020c130603050a080910110c10030e010c0f030e030c1e030415170f100b0a270f08070b220e07020106080601170601030b060607050d05070203121206 67
    0x540a0741d1030300c0040d241580c0003c14501c1612110350811403410090250a1000d80e40c01c03608c1e400c2d68000f110082400c0c0d00800b2686c01a4070031031114204062100559025402d0218480e050750486a0840310784045400005084510450314658980100c4100b0400c0782d00443c10308004600c0991038400c444141e540d480c2c1c07a2071605085030f10900680d402440c00000c205618014038a025001a40c82d02c900080401c0c0da80c000369249151760f080314002d03400400200250350820048c038180d94071005070f1a09214802d520350421000c008284c4500700410b00304258907515201000c0c22a0546400c042c0b226000304106100c1d40c8034420646c1d42e040c0d10014102d00d00100501c15442900d0140c01911200d000101040419501500701004030342002c01220b61907039a91081440403054041111040e8118000410102e074141011755000440200b4a40c508002c9540d900c0c40c040b10800950301040c40030841d001035203810700001154a0010300e01600c0c00351840c1403080ca001d0001e2003144 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 986944253 1250 986943003 986943019
    0xe0105120a0209090607081012140c310b1e0607120804020f01020619091712040b0a05041a070e04020c07051f020a0f330b01020d020c 59
    0x254500341002480507082d000340901c0014100f00b10119101e00049502d0b40c00700e040b0001148036215080c0b45c40c0121983c051403420408030b5a035905501c0b50050030704c094580b14803100c4601c10303a40c0217001c1102c400c201d50403642d15000412450b28480c3c0000c4031203502c1d03103000c1e04032140740c41d003005501101d0030a5800200d40d80074000012040c0c000d424014005061368054040826000703112a4041c034002c13103000241e030b29183c00481e030350311080302d0030204d02082d400c52014016580c4c1000382001c0c45400c61aa98540c800c1c00446990401d422080543c0782031024001804070032421a500180e48100c00d00103490b20b0b4488043e60600301c194070068405140000c0d035058499240000b071900d0003041550f1b1b5040e01070020380d41d400c5070301a6601c1544d416001c40452044040000d0504a89130054001000d1a440c1e0741181c49074000142c90111903141b08088100108005419a034200f40004034189102010301086508002d00c0a041d035120311684240705400041c003514418040b64244 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 986945503 1250 986944253 986944279
    0x11150118020f030a050a1a1e0d0503070615080d0212070516180c05122a070602070c06020d02060a0b01020f011b18031e02180a0509160e0105 62
    0x1038001d200310a01c02990700c0340402880014a01d0740c1109000f02d4140d038041c4003100115070b000340b4000c0500c642d9a40070000709085e1540c0c4100f2042c0000101d802400204001100c0c0c441c18159802a40d040b501c070b03641d90108d0a2407800701041c0c0805040200c0041c0381043e03841102039034950350141c44046420004c100001089002c00600421407404d80d6407050090f6070782c1d1030200403400305994491050400c884070f00c01b1807140341510094801c6844442d100e4503442a6810844000000310b101036a042c2001094038405400403c41d481c440e0100681c0c418007420800004203154110b5802c5400a51900c050141c1c005882600034078620800601ea4800600503403510258010750001d075400c007244007242e207861940700150a0201d8580c4280300c00b00070380094100259000041200a51440c08001400480191030500d44007415406020708181c41003003507e5022258403510644480400c0340c03a101c10700400d451481b01303140510070b0606041c40c80030721450501407903018801811901c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 986946753 1250 986945503 986945549
    0xa050604021c030509041109120601030302010509030c0303151f09080c06090603070809070816030507050a06020a0b06220c12050702071a1306270b1603090504110a111501 75
    0x1140132040003000340c2d515203512764034103403124402d220541c050f500e44000a80d84030380100480d0103000c00c107805540756079105040c041011440340d81e00b036044410070800728010500c240303400000075043d445090b00b283c070342202c00c0c1c505815105194061581400124141c0e160b06007a44e402110301d08125216554030681d05181c1642c50740800d007031340b1901142820280340c000d1400144c0340982c081d00c1850b91140c05000b12a82944903140050380135160a40c0480c801308030341a0003040042022451240e0104040c1c500c0d101c1c503010840b016a9111f505401582290100001121028080c03015240c0400f0294692308030788262200c94200405c9811062009011107a00032460b1070040c1c0416180e0b04000c4c018001c0703031700030b2444e2036921800c00c003c00c00c0540e42070103e8090b003085602d404280c400d9040d2004515404405214041d0008106955039004510290214404807901c0b1200c1400051820a00c1c042c0b8181a03000005006112546400c100341510150584401124205605 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 986948003 1250 986946753 986946757
    0xa0b0d02060417100501031227060e100801050f120c120a0203160b0d020d0b1810060306031a070c06020307021f0c0806011d030a050604021c0305090411 67
    0x2009510400000700400d0f0b14441e1804201525040e03421142c00da00c20a0b451011103200b0700000d88050f2001c848020158403946001c0020100314405024203188c1400002c8991500d400c041c011403071703c0d860541e050034400400b1460204e2460a40c0300b0394948130111341a1510781c001680900518184402d2240042013174082c04007020702052003240e0134010160312000240001c91190150389400c15802c0c11649203801620f2008040b1840c100c034a600f1b40000398030005d00c600d5132a40b6046005680d0b40d5041b0045500e07040b241441c41c05241110102c81e2403081e41e00310005140c41c0c8601400403403a11402e90850030700c240c14804c61900c4044003a6030404034168020300c054000810003d5050f070104144581d8081d0050902c21250141d8821040d10080c0007080001620b00c0c0015100e51301c01c0f6680402240d115859010515958010a003004400300068407590b004000f40001c5040c4050003880310440040c4c1c2c4220390703e007950300810360700ca15200284103c0d25100d8044070007e103102 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 986949253 1250 986948003 986948029
    0x5032712041806240e040b030a0b010f1a07120912140706080f0f10120809130b0604060c081b01050603100605010c0b0c0c0303010e090c10080a0b 64
    0x1019031502d55880b000a01100700c0300110120908110740019400403410b120700205144520301005021000c3d0102d440c8402d0251003907100c0d80f2028a107409880a100c0308031400d0240c031241030383e5814400c88005c000840d6002c1c20200e51b00704003000d091659101611310742d80d4060400b40c402195280c0440300c8031019009211500115120441008411001d405400c5a03480603100099541c440c03e65800d201240d080d880423103044c00050548000f00b84540d80040c07802010042984ca58202d0f9221000a1004580ea180000350503282031521360164000c280200c0003c2c480d240f2046d0102d002c40c080c82c4251401d00030796004a0f001c210b808030681702641e0141054050380030a892905000c0c00050380c51501078020000c43d0740207001140500002d403241a101c4441d44482a0340b880303281ca0008000c280707820000d00a01c0c044207028802180200141d03c02280182450500d640c10070b4002a076081c419198404400f007580d42240c2610b9015415000010b5035800c42c0d404181c60140a40c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 986950503 1250 986949253 986949283
    0x4060b04110d060f0e0c0c0f0f1b0303160b09071d07030b15030106050d1401030309080715090b2505010c030e0a02030a060e15070507030f050327 64
    0x8481560003148101030400c0603021602400b1440d0ba82130741ca400c40c02c003402400b00c007405940014060458550017040f620071604205d881103241d040c4450309080300e2028250303441c1c011f04e03410a0300d01c0761140c0b007403450790044010b545000f00d80406265103a5001d10000d00d80b02030a4009000d0b80000e00225009148250040362081e8a611404030080400c031004400319140c0400b80c0c409062082d034203000d4201411004d0b01e142d01349003060340c17550420b00720002c0044c5c40b07149091031140c1c0001168000c601c03c1d190030a84600340b0104a05212094012040202040060031a41d65109658004440316002d50a07038889508001184e9500c3c858084d0030040f849078040c00801405511842802d50503550400840c5841c070180364840c0c01d103280c082d606a1060340e862020550fa03078040c441c0c0c03041d18811104580c180c020941130142c1d0464480004c1b80780490444d0900d80c000341680511607451410514501e4941c0d1b40c2214040000100319071901c0ba0b18154001c00d50401007005181412 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 986951753 1250 986950503 986950511
    0x90b18090a0b040f0b090a03090e090109290106210b0f03060f180a083a0f0b0406030b1612061211030303010b0a081b070506040b0622020304060b04 65
    0x103420030300460004c1000c2250302008820004019802c007140348010981c0c142e0b1041501480e12900c1842c004e0040c0001210355a5204108001048119400000c04422003448a04c0c41c0c01d00c110b20411005903c80c4090105640c0c2142a4030710058a141a4012003000000c039094990301003000c5031100e000081c3c05106601c28000007a03004458941700e0343c02d500e03a40c0e141c0201601410384503041003400034000c100c10700c4441079400110011f028102105c02c9442c489071840c0d0780130711010800c0320ba0420304550701c240c140420b43c090700800640243c10384040c84038924590340d040c0301103c0100000c901c186a000e11a600c0d40c40750440070348085295500340869034a40200b1440e0014201c1d08550b03594030907804030f096007808020343c1c7c12100603118080c10001d203160143d41c0e050f030007441c0381a1906c51800c001100c8800e1409408918010001040d82d0b142c01d281240d40000060f01d5284a46050b1491012170210005881d56405006401586a442d0303850980c01400014042c80d50240c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 986953003 1250 986951753 986951761
    0x409050c09040b061c02030a020c250e1b07110306100611210d02090414042f0f01020708011a031501050609010e06070b041407090b18090a0b 62
    0x2898024000e0303440211000c00c94a00700030104482803040c02171460450406500d40300c4814003560155500c5605c070b1401526042d0000d00791030a24400540315000940a070305030005010084060502400c2000d40c495001d041180da1072101d605049502080c441f000070324001085180700641c000407e0103000c403100e6041451400721024101d001702e000140d14015400348941d4002103035180104015100c00341d00b80113403c00059a071105090440140c0c0810160f01a42c5540c07184484103a280036401c08182005d140c6160280060003416644080030003440d8140ca00c01580b903601c2002c111281d030741a2801c400140d0511000d680491190f500e4001d0030b200410145c200018001e00403001e550050320080b0025102500a008460300002c4c144840c06103035016089a90035280001d00860a01c241c60b0b40d0000086011202100c94100c00c1c40310483c0f68100708540e2024103024803003400960440b5001c1070000358107414440107003d1038004030f034032240b040c001c00100f01d402208000c81850 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 986954253 1250 986953003 986953021
    0xc040e030301060e152a1b0f04090c062304170f031305100306091505040b03030c0604060b040e100e0d0807120c0216060c050c031603080a05040905 65
    0x1c240f0810002c503100c00b003500b0582c600001100e14103203081100700d081607045104901030302e0b0701d00010300d0403000d410b42c4000001e00405c409400700c81c0c0c01284080d10343c0e0f8141400080f080080c0b100b40600e040000c000c0c002102d91f610302d01a40d426141c07408090003090401c0010390410540172241d01030004011a901418000d450790100d6203100b110b4591003c2c00d410b543c1c038411105000c11441234000144054509070030b450070103d86918020400c00d032210044400c549003030080d2210300c101d40c0c1c2c040100341090700a04108010071404bc500f462190000c4a0b1180801000200349581e1405810800e58555110019100200c402c031400c02400804403401455003141c2009a0b2142c1e207140c4016601c911442c1d071088020317a8030b8450f6041c400b0010f42c0500f40510070380301580030305821074401d4030091410ba001007016581d29807100b003649c1001c900f4095040c560a0203500090410506c5940c41c01101040b241d000c04601d42c0e5124041c42141c1d1030003141c20003042a41400107208440b1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 986955503 1250 986954253 986954257
    0x160b09071d060f01091d060118080a03080105031209010302030a15031a011a0f0c0715020709060f3b0114130c0822020303040308130e0c04090c020c040e03 68
    0x40b4059030a1084401508015113480c00740e807260025400c3c210131280040842075110541111040c10b010041c52145600403080c2c00c0603400c942410f92120030f182c4189640a06040e0042c0401d401801c0900681813001610f81304840c0000c0c1810b800001107400200d00307034041c040358440e071591b210b806900d0b40380502c4905100040301410345820000814203a60107003803945032910041d5410b20b403210181c0300600a4000c116803d00c41d0240500000e00804e4411000a44083c207a02400b0041e0410491104940076500040c2c80c0820410060200502020201d40c5002d00701410001043c2d03458150000c804455440c1d248100b041c80001034000001d18031002c4940d01181c10741c4100100d8010b81085809a1400e07600107004d00010034040000b0038031100400100c20041c134045000c3d500881d01d103900960080f108800002440c4240410307001101024101611f41d903100340c104240f14a400f40100d0150b51010b42da03078107020100c05c2c004c11001c00c4090010380309108090681c18203580b29 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 986956753 1250 986955503 986955511
    0x12030c020f010e0c22060902090418050d0804020a0f06182301080603100513020901050d0b360c04051b03041712040503040614160b09071d 61
    0x50700c500d09000c0c0320380e80c060182c42c1c00b041001000b40180380d5403800b082204c058040324140c580d042d0b85403180701181030f40941d4003c1c0480c4440035a40c0c2d44000c0c14401114580b100100c1d9071640588800005003004c0ac014500945c24600f4121a4a940c0001002400d560f4881e9450124029002035041d41000703601c011020148000102203545031405003400c401c8080002c603980740b00701140030320b60090807895000000501100c5504405000c01c0c400c489080d0f4402c4080c05180d0039110852405007070741800350401361104003031000540d079041c101d40d502030b001503800520320b0340502d100c00c60040da00e03008240b0a01c030707441c0c4044c0100c007142d242d40d0680303130700c074021401c0c1000180001e50542031020400b0380444280e24541d100c2d00c43d0544030444d400c04c40c0304400d0411240c1e4500d010141c80301c6c040c1d4061805075a0741c0303143c5803016051004145048405050500c44210813020504041107207a4000c01201c0791591540d0b496400c02445410181c08480e52040c55100d42d14205280ba1003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 986958003 1250 986956753 986956757
    0x604020f01050408030a030e07090c02060f01050d021c0807021f11071a09030742051603170a060806010e060d0f2d051e06070f05040312030c 62
    0x900c6010300455592042e8001c90a140c0d100b0040005a640719a002004060044081e65203c580b2001e402081e5104031803401d006034400380c14854190755148140f4014881200c002d017120403e640070800260101c0301c03451034000710025082c00d000e001822501c3c6070307a008100020a0188210100240400a880380d002802900c090700c14044009021000c2e181d014807020b5069441701c42d810840d5024400194240c00750f171000207107407000d90000441c04400c01d0f8401702d221080c5100c0003803c1d01d4000a010f6642900500508216008411106014402204a10f0300001030a09441030070f26600319004003003051040000035031466212400f0307165807005880c0300c4d980c0d4580340c0b80c501109881035544006e80b68422400030b0314409094080c1e6208062a0107480c42003140682c003da100b6041c403003d003440400e0202041014010410300c152211b0f43e107841c0562225000740d40c3c010082c1010240104020b00394450ba0140007580c00031640b2004002c061502d06c40002c0c064002c141c0d203640 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 986959253 1250 986958003 986958019
    0x3210e010b010801292218090c1418360706030c02070b0408010b040516080105060d021608040f06080c030708060d02041b14120f2502060402 62
    0x540c4208105812110032500c1e03c60207688a41a02c4a003000b03125400104403410826840c01b800c0c103003c15804130401c000c15210030ba1800050b0500c2d1000300340d0003000c2d645001841300000c0c400c1702500c000d075540d0f00d107141034201a040100f209050b0891840500b40e1202c4200701c0340a07469a03812044840342003448901031075500c10f90380340b500301c000400c0390b50300284810300c0b55070310a0b488907101c004140704441074196241c88144150f806a00300c001030f0b9441c5c0c0c8583e6242c1c1094060786400041180412a04503011400100703103000602440d40b1078480080d00c059114416010f0390907050f0341c3c2421450035681440e0002c80340e44103100d04c000d14120b00c00c0c001001405509824482c480d08000d80d484e541d5003810071038002c00300500389a444610841c240d000360304d407449000743c1ba0228903260740700b18030440c41c040e00e40c1c601d91507a00c0000d08100f040c500002005900c841e001908035002d000540ca032254030328160403019201600c0c440c4c1c10386c0c01c0c1901d50b5000821a000320300036a1041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 986960503 1250 986959253 986959271
    0x280e06150111030a080f070302040e01120c0e060916021014160903020d03050d1506120e0f0a0303050615160b09010203312108010504021201060c03210e01 68
    0x5880303018004000340400c0005000480d28040391900c180d01c87d4180c0fa00604d0161030b1801800c41840c2038101c46844840000b0304420822202a22005003030108407002c03451400c000044d00d42c000c003c003240750744c410441042501e18020040c111002800c41000c2c04001c1d0310880d41c0d030101501329145040c2c0c0700302c0c1d810b820380c15008021102c240d9402401a603800405914107490031342c0309514006290756215010000005c6d50100500a0038441d034bd00544007148107520808d0307a030600c4481070710307410100c007c000c09200001e9070000c5551500700402d46a07601e02c001800d5203a0a501a80300e00303400240b200700803400002d10041544208111482a195542c0f11400c03400100c2e0300d44d210704501071340d01145403c0e5400303d1005510202003009008046daa03000c40054040c4d890072441c40e00300301c4000c1c0142d0080449400360909440450074410107521002d80414103101e04428007507021070001c141440740703038009005400380032942d4110859801a500a11100c080c03204903510303240d121 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 986961753 1250 986960503 986960537
    0x150a020d0e0904020109050910051509030c04050f07030e0106050303040605120a05130b09190c0515070203121b071d01050405060d020103050622051b03280e061501 72
    0x80c0303000b507130181e681d484043c2c03c0c4821f0240b4034001030071803000c03c1c0e40c0b07110000e20b540d45e03c81d04d1414a041c0600c0252540c1105040c1460580940e049d940f080b1700700810020011002c01c94160b00206503c0c000c10303503458982c0720328010309540e0040fa416010000700400d006402134010413a0641e1048a90780e281d807500b02c228100d0b2030556044041c110080440701c0818400341d07910750000b88003000d5810921b0099120100000b420004031070491034510100000e00c1c080001800380c18083c0c207414601504c0b980020f468952006104000c8417010844400300c0c4582d51828103885004021140204d0b2100a891807403408041607140c0030010a00110b554105805400d02a04010f040d44030780c0c0d80c5541c0190082c1600070040e58000403e485400e01c03245481c280884600b01d00e03240020b40f03082a00a1078103441040003541320000e01082031001c1d1554101d8101050355261000d00009024454175401411000c0380f4080b4510983c0280445541500c003090f038019400d803a14484000e5003401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 986963003 1250 986961753 986961769
    0x309011103160f0825051923071707030506061e0f012703120807020709050c090405090c0a090c02030d0f0603020603040c0614091509150a020d0e 64
    0x2c014940700c460035058001844185080035141d1040c81842d08280c0b5500700c4000002d40d0110f01e41829040c0d94002e814010240100c4c001c800d00d018840860010340d0b1100c00038080400d8681d490511020040e200307540d02408150b01034903006a0041c24040f500492941d01c0c921404192098003410011032010f2030400391143d1010000b26520240400f100208000c081e4a03049080c140b00c44d104c100a20782c071540700c81000b858828035a11250b541142025003205d080c025023641404081814454510380008000088500c6110003003081c0c1e44500c2543300034084d00b22107070740290501007405440c00000c41e00313940b0004103540010f0807c1d990030100f8107031001800070102680040011485944040d0400342280d0940c000114501e540c96011030382a1340100c8061b6040b0004140c24030009500c04a1400c40504440500e802e295914000603404940510110200c00001070007001c80d4480101d601c034480d030b014623050f455003140d182c06522501010031a1002a0000641169500d45601 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 986964253 1250 986963003 986963017
    0x2070504060312051e030a02130b0306090c0c070308160218061f0c08041d240d061b080108070b04030b0a02030402120303010b0a0806220c031503050309011103 70
    0x2400340e8034a202d0711010b685035800103003441e01420170102c1c114140307503400000354041c401081005a440300c00406c40702e1800c0e0140c01014401c1c10400c140001c41d9158071b051900035105580c4907544110001c50b082c9481d18940c8001c0444e0008144180144201d0140480d028002d075800d04800200105041e040d44040707a280e540490340b00039081c460214150752040c0c5601d242803a00d4000001d84034840d050f04580c0c1b18081840c01c40981e4002c140e0602400340d001300110300da00c8a4400d00b141168260142c4504242c018200001113400740005900110010b01030040d030385500c2600c518005205000c24080d4082e140f249840014568042100b103800b102d070802c40d40451a142ca00460f4040d40c400391050b60302c030710184e46d6405280c0c403d20040d0b000b4480702c41e0151b900d1001c0e0401030020701d0000c0c480c501c10040e8621003403005001c0d03000d85082c0001c01000051091344140300b41c00401140d01c828a0070788030410040208680080105101e24003601c1d49036000c1d2566088583e1703449248 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 986965503 1250 986964253 986964263
    0x1060807080408030703180f050f03040b160804123806190e011502060105040b030a1b0b0418110306150702060715021830010608060412020705040603 66
    0x90081100f0501454000100b40340c0411011000f00b807031364105203d20416140c07007022000c0c450030803104005a504500c0d210780a1414185020040d14443c0212060310456500b203280c160104440304045802518100c13071102040041030070200300c031120310190309054482640c1c0c0c207881da08126289488410740030707881100341d40e91301c81445401c03030690a8215070458003060200d06580451120341c06403440041c503184c40100400c00038034105040e0f00c81402546818054007a07500d01144035151250041c0102a100c441e40c075070314044928607404060720303060206000c910500d40c03203d90b4500b103802180a2040b580110400200b41c03005860f03103948052245141d418200c0003001510a040c0014006e03400c20311a61500e400c205002661500800e90000d900714070200d000310031b00101c42043d21402d05000720000c00036074104400c11003030721000d03070400110001c0c44250000c0004d401004252030290408d031402078042052500e905000d80111200800e03241040d10802c01101c1e000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 986966753 1250 986965503 986965517
    0xc0c081f020c0a050a0f030f1803030e19061d0f03060106110309041d0d0f050901050d0f0207060c1e020706030f02160803060a0603110d0c02030c07060e0901060807 72
    0x80c1103800003584903080a001c54090680d2240200e90f0520211017a1802029040b01a9100b0f1400904140e5219074910a102c074446c80070001c0810a032412007078036818100b903140075000a0000d02c0c407440c4503040c26013501e210700c0d010403a0b80c0e00c00c800e1755800c050006140c000702d24207070401c042c0314200c80405800d98800c000402016214600c0301e0420700820040d2031a0401007004607050311000280600c4640d907808030a103805008000c0d5040c8010b2a02d0311005007510380c1002080c0d4461820164104000802c1c00070102419130b004440c1c644d071040086550b102507140ca64068500c2509100103c2d01c988500c0c241c110004c00340d400302c00e441f40c1c041e04000d410300380c06400030045a200513186076804c1c004400d4160312070700c0382c4082c3c40c002ca040380d441c0c1c9441c0c001c00c150114150049001c041c1042c185401e414441c400351a040079000001280c1c1100d048800c92071409800d121103410b2158110003d01d003508000f0300f1111200c2a1060403c41e0389803041070b202e60a041e00c0c1140080c142c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 986968003 1250 986966753 986966803
    0xd021e0303090309041104030b0a0c120213030b07180f0e011e0603020d090b070c17090307211b14100f12021b06060406050901030f03080a1b0c0c08 65
    0xc0d03210b80216006c046580b82042e8581d102e003d40310008441400d649503440c030b0391216039a044040e00d099145040019850940004a08144448984030041c800200c000104010300e001c2c00d0100448001d4603147c00c41c2d0340d41c542c010b250400740c51080c014528486000822008202c10180050320101000c8011a51401800b02c00075132000d50501c00865403840000001410407081c10b009020301e40d55201e043e4050b00b800740006520b00d80c100d0035200c0801c8204440e48001c00e408080360801c010b800c1d980018132021078040301a84500402d8102c6000200d0705c1c400e0081c0d00301341558140d40b40700d40e18410070018882003d85450068001c11842240c5544452180300ba103500300c482c080b009410070701074010402141da031004182e140c1d90040001c100090900e80700b0701e8000c0404541c407200c95407454803005005070800e000941040640c500085141c1c820750042c0e954003070304103007900401d4101d40380107000020031001140e42c807103188030026181d0b0000403100c1600501c1e0300c0a401280d0703 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 986969253 1250 986968003 986968009
    0x30405070b0a200d0810050f0609030f151608071209021203030703240f0b0705010905061501031b02030a050903010e240c0a050d0e0c030d021e0303090309 68
    0x440c081d104108082e031425408800e00c607001c090324903d0f20348010048052442405070040d20024800480ca414a4108021a60b190140a50301030390a0358896a10035125001c40e04180b03134401480aa07100d5a07805240c0322002d40000f42c451801c01c2105040240c0f0503108880108050341d0303240c00203164072501d00740c4c240513500003c08188028042c0c03b05907c0c0b154a603003140c101320b490202096580c440c440b0111100b0b00600400420390901511440c10b15008100c0441640645903c030040071400f002001004d5102d40701d03141d0080d0844006291030444428051403902c0700780d00080c10000e0800c80d240b1600d82c0f02d01c00f43d000d41c01031400c00c40b1081e0125200c0e08440070301d03a455900c6230f03640c20001c0801d01125204250048164498442c40305c240140c0380d101400f41070ba074440c201310b074101e2964000140d074920360380d80001003540d000048006203042e591004207581030003041c84030690250000b4442502c8480280d00c1020f030b5410420013030300c03130108541300700d100d810402901c50249 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 986970503 1250 986969253 986969257
    0x309090c021f050109060f2409031a010311121203190f090302120301031a13080a081501030b060301090e160f140922050309060f0702090c030405070b 66
    0x6203031071048426030044954031010ba914140b500c14551035903940140711002c414015000030f000200780304800300785800c4039014007078000080c084040000c090401c0390548110344040c02107810450500015502040710101104280b008850495247c401c045240c10603464102048019401621103440c0c880201622940f001b40854101d10810f44a40e0788502c0704d10440c600d180b011400015181b400e40790181c9400c2035401d00c280300901c00e00041002400e40c2c0443e40c1c0035249540b0403100741e200e05110031002f840100000f412080302007046000203074824440c43c820743c410110054004111340c015811101040c0b0b002d03800400c10001849088240e4010f19014026041207401d03d503641042d554900e0300603000840306c854155803c104140c90150500c4400d04200e948001c10306000740741036002d124101981504d4078207100546d085c021b06200f51485d072a03008d84050340d01c003401040800c1c40c2c1c1c0208001c904c02d502150104080030005000e8910035076107c0010070b031440c248100d8542715 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 986971753 1250 986970503 986970521
    0xa0b07020f040e0f01090c060c081b010902060307031a04110702040b03250e0f1627060306050909150f091603210804030203040506130e090f0d0507030909 68
    0x1050300c941c0314200d1050704009100c11200c084d800001c0c40300320b91403c068514081e47c0240c0405c040c110f10b0501143c1d848040754540b070404056500707000181114580075084645019500c2503000c02004526a0075401c2140004103240c1910038841c52101000300b10b56091004105a40003484140018200b0750310042000c0001003c541184460140c1401d210340902120740300c000c0840020020f214152600d1a004010825024400e150200b0900303040362068041004010701f622800d07031014804006119400d010340c4000101f00d489620141c094a00c81c8a800c0c083d040b18000100810004650721030903201d1040990010303114034142014160b00a0082900783c01010040781000526030301c80c600a52061040c5504401c0c407404104848415600381c0e014082d4000403c00000c2c1e01104a5059417404c60b0364503125800c0d4042c65660381c54581219683d04242401d106001c1d0002880051a80e080c000301c40d0488050b090464481c05403900007004500c91308003e110543d003a40040c032007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 986973003 1250 986971753 986971759
    0x80a0c030b030f07152a1b0f080d030e0303070c1b14100c0209010b13120501200f030c18060a170106020a03080c0c010902060408100501050a0b07020f 66
    0x64504940700003800d0240386800e10820b913200500c100300f0516145400c110190003801d02418150311680408400d00d0550001000310301d041e8400020007240c001400101e003a20240310342040e84514821203002d2590081d20581d11404134a03410603407203405480c0101810101850441d168204c1c20380310031502c45811250031000d50503504450700540381c090000c090403014518404030035030510100b03030b5003103540c20304210400d16080d0258448a001a04441c02419029612048103400000160450300701c61900c42d903055017041071040542141c0c0890703024410781c1d000ea4803100d201103d984a50881c410b41d00b4130620005000810101c081c5c4040225068111402c803070302300026910f54040503403c2c01007440c0e41300281424a02c21a128054000c0740002e0440c0d002c140c0700a40071580051922002000000310607288607003c1d00041c150f140c3c05416552515103580302647c4641d04400988a8213181c04000981d5207842140007003190709085140d4036080f00354003841003505038203181c960 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 986974253 1250 986973003 986973011
    0x609050c030a051b03030f0c01021806090319060e0a080403060f021c0c05161401050708010815061c03050408010b060301050a050405062b03030f111b0a2012010903080a0c03 76
    0x4504c0c7c001d003004010b046005c0c0001682d4184c046d80e2030081c21340e823a001900648080c050313200b454500240712009039001c0041810600c034180b900350064655441c90a10a008820101e020402000701030820349114440501051940c80d85503001c030b00450306400803000810a001c0358140c86503002c1c41a00383d89240441c42d10030401c0080118107c4500c044031221610101c00811200070b10855030009000d2814503965454441d0312642c6225556440f14524a8880411204d69036a884004404d50352030078144140c0301c50030f02a1254000d4480c8100c103509081560045103441030480781642c00c000c0820b00801d040c02c00b40b1005040062800c0d401c402d419100ca03282a405c40203040800700c0f00176010070780e03542a02d401429104a4901e000406040a04800c0c242070040c0035039414031a58060044081000c0072450718012028070081e11007000d9201000e016404078000914600d0143c50701070031a00c540140d5401c035051035070302800050154021400030086c0782c010040c03005452401003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 986975503 1250 986974253 986974267
    0xb0f1614120c09040e07030209010504150e0106032f07031d130b01030b01030524060d020a030f0501080c0d08030c13121101110a0305070f08070609050c030a051b0303 73
    0x124a01ca0588415589800204041c00f092a050185503c0886000c014007207151841d03010500d1a001802001d00c00c1d91650309612680c1070101313044000309620611014596510103001d8000d245046001c00031406a410341e00c0f0b564055010b51104a41081040d0701e0440552411580c1e030700003811125000600d10340c041216611441004000316a40000099028030140050201d6046000841c145801c100400a60f401c4810040062780004101d2040c03850070386001a14502c201c100100c2c1642c408180350030101d40c1513020407203440780250104000d91301e840c01d1603629242e2949842d8010281803800300080c0f1524007458000510699042c10110f426003100164105508131505583e201c1d801c91041c052008800c071040402030801441401102d041c281e15901c85450180905c40d001900404010704881d00d04040c0d030b00a5001601c400461070030002500c1a240203036254400c8103e20391644c80c009c44c01c0592540d00c50004c1c9001c1070a03600000703d00584291403030741030205101036 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 986976753 1250 986975503 986975527
    0x807080c041e080708010e06010b0d0618060302040605120c010e030c18160810030b04051207080909240d0f020a240201060501120504061b020a0b0f1614 67
    0x1100b499105042d980c00141400b15080c03030301c0415800341105130704008500d5034000f030101c0c0c042c0c1503450a82480c0c0d070713a050006030303080075144552000034244d10f0a255003015200c964025026241300711000d114196039002004003501c8200c0e00402c1c580c022603c250040d40c06051511480c2e02c0140c141c07650b41c0360700000a40c0a42c04d00781c81c802d022050304100132100380310840c40400306815042141d0036084c40c14aa194100303190000803ea0041c00d0f0200c0c091090030440a410701c00c218480e60b81d150700a1411095179084001064000c8000b480482c4813600501000c1041c8200c0701c1e081d10000b40c040e81003240001540d0000e80350b18031900d01d84000362b16285580d05c00303485403085050389100d070382c413540081c4480c8690882c21a49002010302c110381c0e00020070038400240384000b280b10385650030300c0801010381c603200399000281082d1a00025801007043c403d010702032009468165030305800e0510b900812179401e07001d00f110140c02d074140b50240100e031040010a4900c6402c2059403458 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 986978003 1250 986976753 986976779
    0x9040b12010f0e070e0424060e070e090907030b0a020a030f0903031512211209030e10110d03111207201f020d2d0e0d0807080c04 57
    0x2540c00b4035454000c01041080108070f51001069810314140c91491b1645460a418100343c2d40c0c1d1085c1d10701c24007241315202c0a84c02c00b5016060503035200407681030040ac00303850021003030fa02d94080c1c96400001405000007090f1007044941121220b04d0075901e141204000b9800100042e05041e640c0d4242c5441036540d01c07803c801c40f0700c40e840003e900b05003820b285801c00c1990340004032100703400741580c0000740107032421403001001ea200300c0d000070900003055880700c4811507001c814078a00744003901810742c4107000c010441825540e01c03c1d00d02240ca001c07100800790701100e410b136511212006055903c41c2e4401c440200c40e01d0344260030705905c2440345803884810f41e01076000440b201100050b0440c56141c0a805595500046c0503010461500c84040d048a4450035007160380400c0242c401c4c1c101c0e41012401c40150b54810b08081000e02d030301400445101c0c1100c04051400310440052640001c0311004088251a032880d16510322008407140800242005900c4006100c00a1065283d10f4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 986979253 1250 986978003 986978021
    0x90d0f05030f0a200f0405120a030e04090c0302060d0501060801050301180212031b0709050a0e0d030b010905030a0506181f090206090604120b06011e0521071107080c0609040b1201 79
    0xd00759100d1416041008c2c40400300388411003508280000c000181d0041c01c41d901844c0213036030216031703115039080c0111407852aa0002e50440d10000d08040c0c2207a440e0700643c1601d8480d00c1e00003040c2d803590185800c030f070300615002c09a100a40710301c4025180140f01074800000d4102101d262180342040303030f01030b0403800b01d040401c0d9004001c207200c04451409510342c41300c4080d0b402c01075200402c45a40c0d60701500243c0009040c1e9901d9114000e91080401002030180174007110b1841c012494001d40e104002c441510045149101c072403c20900400d030210004180e000307944908840c6900300c0000c11911000300d90161041041e88541d0315544040c0004001c950209028101c0d1070402645038080208410f040040c0005080d00150007100220790704a02450040d880b2035000c4518526011821a10b40000208000304821154082c15400d000007018040d40c1c1e6080d42c1e011420f903520344580c0c1d4a90302860a1218064504042d442200b004000130209041000780c000c0c06070031624010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 986980503 1250 986979253 986979277
    0x12020103020d0612080c0c0f0906092a0a1706060712050c070f1509050924030105010f051008090c09060d020a0308030a0b0a1a0f040e090d0f05030f0a20 67
    0x5c202c644044400b4411a840b21005032031502340c03d0040c5001400080300182010b1142d062840442c09031400403180d0003140f244c1c00307501141d80c205401500c60075041240706a001810000c0215401e810490005000e55000340c0b0f00ba05100c8242c1d684101102c50412001c03c210044c006101c100100b044214002c0c00f061550840702401c01000e408021214056001440301c0d0342d0080008d80c0b41c075000954010b401c5041c0c847d001c0c403500740041450295402c0141d1642c2001c00100e1030f0034075010b2102c1200c1c0b040301c0901600705020342c01d6480700d200319882c3c40c0541000140207002d041c601f48440d8454001030040700c0020300303a800900c4c010080e400c151179015002c000c101d61340544e03220f2440f10350021581110624a01444848525261682c02c2120310001c914801c090301d5810569000c2e000c0381c1c00c1c2c205140f80203090507644002c05107800c400034464008155115000700e00f268016151490098020f588543c40318001d0a610f0001100244d040000103901c42c2c4201c02a21174000c0030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 986981753 1250 986980503 986980507
    0x3091e0b0118020c07210602070809091f050f01140304030306090b01050909010b16050f240411010f02100e010207020301060e16180f0b070204140112020103020d061208 74
    0x4200c1c800c1211602094a000a43c03040010a0390040d002403080d0489841e00201d03004902030402c0341c000ca1030810b0000301a2400814110b0030440d014002d0245010203a0320403805950b110840100042104181440700c00001c030240914180105604000a018140054000100b452428446c0d108843c25000130342c0d500002e12140700031380203940e201d10091815a041c100300070300140c1d60700c3c018400d40c460072400142c4a04001c28000c1c1107907a042d0000c098508814002c00c0e06610351408446842100c6504403404c1845004107034280e0259400c80c074000f1900c0301c3d00b401034801e030b030f40402c003c01540714004019099072128020913010551500001d0385480032881818291009504204015000241080344041680d0080890142245801c000321244588a245500703601e4201802d0a01c0c21078002c90402912802010040c0c03081e201042003542d4003401a003010001e003c1e802c0300e440c00501d1080035600c00e03000381c044480c50b0744c2e00050540d03443d41100b0001302d002004072190800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 986983003 1250 986981753 986981759
    0x51c1e0c0e030d050a1b0807050601030c050402190302030604092f030a03050a050a0302040e01120b060a210507090507080412110a02120c04110d0f0e0a0303091e0b01 73
    0x480241c0c1d955500080e00200441030030000003401a02507201c00c1020013001c514805600f009007001e055196401c035103410350703c40b0ba41c03c0441d00c03a082404240c6131001d04210020752802c00f071003120901c00c1d00d803001c00290580400110702951015010f183d01c60f0301c60744064003180d000300709030062504030180c004e00c40c2042040740e140300750908103452182d0050040c0e1004250040101c80e6040700c2c07843c15a60300c001c40c3c84140c0c000d0003590400020b01d1000c00000c1200020b0b140000592400355840e4440d56403840c040003030042550140740000401e47c4003940b54a814080d991801c00d1007002502c20303035600d6080d0007080711000c88040700000c4a110034402481198503015612100910300601602c20301c0e4440f0340d58412589000b400350380c40540c50080d4180030b0003141e20001c8000c005200e60195500309103a02e030031100e540d1004a00e048882089544c0c00c0c4aa81140484807001d4401e6503a01e4806a00030501980151a03645004407400255414807059074210340c03003284030a4107941 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 986984253 1250 986983003 986983007
    0x50d032606030c150a0311041a040e090a0c180e19020906030d0c020913141b0d0f06020c0c0a03060c1805090f0709090c0309021f051c1e0c 61
    0x142020301c16014080301a030045020448001701d17600100603041c0820403803260810b9440d144684c1d400000101e0342d510b41c401c02c001e54400100202d0314070704c900a09a03241c64403000c2c2c650312220b42c014142482000700b00302c00400c0c481c9a0707889403841c510018800030000d59032800c042601164048508442c0034980440c5402c0c2c5410350030110503001004000140e19010f0203244001002038422200b403400144000825940a100d480d072041c440540c000742111207a031399614000b540700302c803070450340da4a0450070814a0750300f105401c000308030b10b020b00766228000203502400a411540c00350011005581c0c0352140001d000314410b550001c0c0d84c1050910081115030110154081c604940c80c0401c0700e5955041000d801100d00c078005001505e5800d0152000c44203075000c410300c03505003d40000f07450303050342c4107a8045000751400070078124286100704014007010341500110714184412248000e03850b91390040c0e03d485500000e407458000d040006100383d0712080301400c0344c480031b00c040b010b5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 986985503 1250 986984253 986984263
    0x301020c0709110306130222090b01020f01110d110403050a031d030712060e2b1e020d0f0e03011802190b03070309051f0516090b04050d03260603 64
    0x80f11119064254140b110004600d10721080d0f144058580105111344142d0301080c400076101303460600d0f4814590b40e400440042c002d4802c80c540907000d07554452501c1c0c1c0e1306004d2100c13800110181207240165400302940140400000515200820720001c400a0303001c000380c0c014180652680080100fa036400040b0203801d103000c680c0242c0003d403007000740783e2814802e03002850b8801804204c10340344040451800402d2032003450f842200541c40c84240c00741340303004180001c2540d038841052102103020b070400d00051100d08010381c81b400e01e44c0a560311410082d02a040070703282040d07808058800190070b540e619060004200d40226021045103441e154021030301c0907509000c40005e00d01005101c070703070000a007900145070300d5120303070007c0180520035800104c1c01c587d004d1082a603901207103c010700c81100d125408d1401d9039a0946414014101e04046a58140c220707450942450b062181012400c5000c6051003003000c1042105441ca5049224007421050f00480030b2034003008161503c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 986986753 1250 986985503 986985521
    0x150106181815060912150207020409060c0f030203010302100f0215090304090e0d08180f060c0702040b0a080c2403180601140105030402040e030403170406020606150d0c0203090301020c0709 83
    0x101c611303090100702c4454280b00c4610050340004284901d0340031214240040d111f00c14000313500614049800b020000d480d400030308801480d56410310341501d8010168100d200c00e0102070350140c101c2003a518618400c181240040006d403054640c003050900ca000c002c01c0040c0c0703140705c607a040410305100180152141c0f800c01e00c011802040ca01c028000058240c0001a020320107100c0b400d10740d04035000c001c0007190380b000179550860b500740c90705800040081d04280c02c2248036600b8140032402c245002d11031142918940d801400c0c844014004100030303080c0ca520000742140d00c500d202610030b40801c2c09180305071031500c64665940c0c103030341203030b420701c00140c11418640c5510507170103013140da002c4296580541d040d5400070f41c00b401500313020718500803580010448070100c100ba80c0940c1104001d84122120b0ba0219011921850304200050f0441004102e110b0402c0c0840d084005103030700004000b985a006407842c0c014128042400c0e81e02c8942c1c580c465030b0110801b00035401c035500c0340c0814 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 986988003 1250 986986753 986986757
    0xa1d06040e1305030c0f010609050a06050315090a0204061203141c11040e07180e0c0909070311040602030c0c04061406130504090b06040e15010618181506 68
    0xd000c0c101103800c5450000940004545600082a50200038040040325075040718901100c20005001952a001e806a4003401c4015400e002c041003440703c00f03008540907210028003038408c00e65014050041181c000b06007074050300c83c1805400160300c4a1080700050205000300020301c0d07650b420050050800507d042400c400c0030017940c101800c00e00886a1407248100000c14a0f440351a220b210034000c5400141d01c0c4003010091040c8240c006140b1204141540d482c1144a40d0300c20010401c108201c6016910350f0040183c104180341c140030b00b9500c21401d090025003900f00700865802604036400090241c0e200040304100500200014840000122810f01c200c609040b401c3c200c6100841046000b0031022540b210010081310141004e04409481000569068100304030030301c105a90442c001c0303141002000d0703c201c010900da920301610031050b8440c0d0340780010448a149a0b92200c0141c1c00d4800740201d9080a0f0f507960108511038450042018640b01d00c4200b2400c48980c40340d01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 986989253 1250 986988003 986988007
    0x8060915151303050105010b0c100e060c0c01140406050601020f0109020a0302012006190507020a030c0809060f0c01050601082508071209062f04030b040212030a1d06 73
    0x580d192640c910300c01d45001000d07515490b81c0c0c040701e42920400e801c020019400d007030001c1201c460520103048d400b10142e0455940e50102007860084804012040280303030815400074114214103c0204010fa0940b400000e845a80460f10283c00c01c05840c00ca420a4980042c04131079a070400001c04d1450b55a00200403800540c8d0025410300007503c4000d05001c4000326901d040403402d01c85c0400507042e04162000c905d044500c140c0746401d02d80b0b00050140c90302011903615803002924004d07036a070580b20401044031540b01c424054014001c5154061400c009055a00701c030780016105c450145000031450b81025000503190040041c07101c2c0d02a03110f58150a1721a002007064401404035007040056134440070401c880c0d00300790403540d640040c01c0c00743c80020400340d540709910440c580c0d03d07050003c00c4540d46e0b02d082a80402e0b51f400d40705000f0311051010510b4000d406400c98401055003072111441242103085030008200103020904110404600003107903140001001c1301114124 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 986990503 1250 986989253 986989291
    0x5040c0c020d1a1032101205010b0c0a06090212031b070504140c0d0b100215010504060b1209031b0d0906020c0901031101120e0f0c030c0f0d03030605040c080609 71
    0xc01454205140c2e40a00020422030b103800003141d00451117400701038100715018041c6d040207001c1c0d602c5880c000c04494a403d00025105000c1c4064440400a280c05404060701944608001d003080481c1680d0003820800203d41d010703800c10040000c500101000130045480304005418140168862401030742007100000f07202d0003071000b885c1d10603400705d01da580b16400c0c01d00400051140000b0160010030303000441034403a400049501d0201e2007030312180c2c00d41ea01d80003071009407045442807202481d424030549074100f40f120100b55114015a0841e410402021811441c4045510b43c04000d9042142ca070600d540d846954003005d071420740010030f01070b03c680d008100d40445c14803001e040c04100201c1072180707070306c9480c5440111080e84002d002c2050940c000b1622440408402d6016125201074078940b420b022901946000000b4914203401d01d04500340044e01c1440c80003213080603134030840402c44c0ea4880c030034129040f1250340ca6a45524244050086102c4040c21070510b000740b4414007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 986991753 1250 986990503 986990519
    0x61a03010501081f0e04021c030212071a070309140309060301090e1507020f071409070f0c14060717090a0210030b030709090b01061805040c0c020d1a10 67
    0x12811640d0030b03e08a1200c1c0d5030100500c250342e070350031949601c080c0c1103500020303501d158100444c050750003210f14140040b107a4039618032500707002d500200541c001000320b0b601d07458041701506805000314050003060b081a181c501c07a0303800c21900500400d40c0c0e0b1034480140201c41e54804010108000107600d0203c014000500c9800144112120343d0385683d0004902d07a07050040300180455180701030024100030101a48481d503070704400015200700d44002844a01d400d180407035a110191240840d900c03041012111041c001551100340500a004100055070714a0041e00c410500809004c06007130a01009022410b4000e0325801d080000c0240801c2490200d6080c000e2541110442044600707040c1c2070300644101042503038140103d000028030a00341c1e4010341c0c035052240028940c00d0303803508420344014240c080c2084000460b02418409030400c1e0340509060010f034140701c1035212295000400c504503a0b00b0495450b030051884500c03080007500055003254401080e50301441c1002c0741c0b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 986993003 1250 986991753 986991757
    0x106082512020f0103020412061d0111070b041b03080a031515030f061d0109050901020705060a0e031917152416050d020d081302090a14090d0201061a 66
    0x4041d00c907800c1e0783e2041c0c000ba03009504807002059405214540541281401401031092a04228250b0074441e0500d91028040c4250070003050071121081c10449075880346c0c1c281cac100041044a540c4192038414191094100307128009510400c10143e48202c201d000030192138280802040c1105034690901118421290b0b6803043c1803540f40c002080000d20102d24050700c5d06034800300380350300041c1d814250280301401c00350580340411700c28041c03620703100c44090807889803007005451034000c1d0010076850380c50b6030800030702203e86c3c400701c0703081031012008a03001c9000001c0d4100404ea1505007100c4014124100540c000201c00da413131108440d40c0081809501c0e420b140564040c0c4900c4150880712100c42030f104c10300a400000d40c910700a034503200303596200c0b075503d80015100e03145503071161074800c0001c20300c84c04e6100f02049408035142d091002d01d001c040c0000d501e0310703182c101c44090b00001001070f511503d00880141902000c0301c00190841e001030b0400503010b01424030034000e43c902c0f030301 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 986994253 1250 986993003 986993039
    0xc0c030e010807030b060a050c011109010915020703080f0a0806010e1f050c01020f071703010f05060a111501050f03010501140d0503070c090606110109121d0301060825 74
    0x80540d25983e403180120010021400003030750241e00411410700460380700015100804558000304100d20007841482c07801d001c0d1446150004002450510001c0b1014501d8148038426004507100f8980b41d90b40d1502607080b03440c0d60101c1001c041030403a42c05502c2001d00b50030400a00707060412584127004906205002c01001030210f01520107010030f40e02c190100c60f20400040e00854407032903c0e40102803143e0102c10103844291403c02410300025508045078101e07010f650b266207615103003800b440742c40e4000c000104240201307070761803240c125002e00a451004407000075a11003903042c401006003916002c0300c09030003130b032501005100003c41038040e4200c850080301e5141060700b0354640380e4914400d800f00100901c2c481440061003212941000050321032980700c6040850307103035480d03508a6101c1d54004d402011602d801018040c01001c0c1c41e21003d681c0540e11080700c40301d00c00329003901c11542c0300e0364555000520b904d41f0f1040000b8000300c0c07240d03503007031000c440c43ca015100740f1a805826 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 986995503 1250 986994253 986994257
    0x121a01031b0e13030318080c010207030809032b0f15060306170307020d0507120c14010f17041707051f02071a060d1a041b151404030204050903030a0c0c030e01 70
    0x5180e00e0201c1c02c1c50120951079805441e660f41e0780366001c8024040d40141d039033100401c50310000324030040d01c040300f55038240404920070a55502d0501100140b4006c018103c460181d07124041c410190340c40c0070301503801101041c0300000d5840e0040c01800c0f00c90b00c0c1d014541e600d030f20b0500c1750b25400001c8102c5141f542c04131400942c9a0690520034207051150f8044940d02e60039040b0641080106208a011079071a0014410402140001510b11509000b160000150000060b1a0302100f0056242d081400394004041d034510ba009281141d62109105413200d52050340c10000100728000880b05940310b0000540c100801c554500005100754084600d9083d40440000d4050712014000f2402a410034001c1c10015045610f9258161003924251144003c5515040c07144561540076011144620340018482c041020112680c03421400506c60701c22080100001503921400703071b14000c0001034040c60ba80d0800b40d200300200c5000040d150280442d101c044004030b60014100904200d0038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 986996753 1250 986995503 986995511
    0x2901050d150b0c10182a05030f0c0405010f0b25020301060314210a0c050a1218120503070f02030f07060e040e16121a01031b0e130303 59
    0x1040c0200d0780c00160b005400002c0011031006030369200018030103980414850200800c02d168000d903a01111204400b4045a03204180c10300084202240d80c6001c1c1203103408192080e403182c0000f0704090087c21070800d107a000360b241d400c1502e000c2c030407103004014032030001c9001d511b000001c0d9014004d1542c1c525030100c04001c11100350000384250000300343d0041c02041946c1e180c0c0b42ca40c030740b05001700c1c2c090240d203d1030b40300007084034000c1000ca24000c5034501c0c090030600c40c1c88d07040380e0070111804100c2e1580103400b6020300280814044c40e40b4030240752284440d51002140d015480150f65210161403422110100c0200304003100300c0b64071940000148070440b80900201c1d103000700b010721102091150000000b5000e03404250400c9020049400340280b4524040341541e901542001100035000c21008201e1001c44041042c00c01d44940c1000b4000f80f11800c6038403007004264825210741403091010045032030442c980c03001925110200b20680c0c2003460b84c03541c000b16020401818141c2d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 986998003 1250 986996753 986996771
    0x305090d0f020a080d0504200117100b0c030307030507020a0b241002010c02010f0e06061009030804060c0302070e04120c1b2601060e04030309061e2901050d 69
    0xc02e00c0f107101c0c4903420490031965150000c56035401004121400d944c1072403511419400180c02103c01e621400b016500d2800b000c140b4640a0480d1001415503c0100204840003030011103000282040707207000c8c0061900d82c501400083c040d03403001040d81d4110f4010f400c810380003800c40000590007845078009010846402e190f0140d10103a10600300b80d00a042421521650f581500407240e1800140d000340705582110045100390740282c0000c102d95006000014214144000300006001080c584141381c5030382c07501c40940360b603c10b030880c500140584d8080c009154040011200401144510086503e0161240010943d40c1d2019070200011005810240070028210560015404048115081d9501c2d0120300506585500401c505201580c4d00c11044040c80f40704102c0310311314003c0400f0b540380da03405c0f402000d140c8022034900ba42c9500300d01030075442e00500718940591100001da00c44031461144d8504006040c41108004461302d04072072664007a041c0c402c580ea81c143c000c511500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 986999253 1250 986998003 986998007
    0xc1407120905060c0c0a050a0518040812010305061015050a0c051e070512010504080406200105040309051201050709050103180b130c2103082508070207060305090d0f 73
    0x4154442c5038020f1000c80c11403225603021414032022803040341e01c100f6081c2d65034240500113070302e40329075039100c0030000820040801e00603109601c03500c45d50040cac1c5041070400800d000342200ba0000d49040e0b21450400a181d1b501c04500e0003e014000c0f005001c0400c080c00080191141e41e11000410076010072035020440c003000710b03103c1e528403082802c4a80000e2041c1c45d86d00e0b2410f11a491098549d03402c0c805121106104bd0b5020750b0700710000300d140c1414220306564105100140c480a1119240b061000a10038070402d4003070343c401e03031f601d56038140351204101c404104403002c80c03240d0345420300340110650003a00600c210349080c200800c1b20b150118400e4030458a4003405400c02c0b014100f0001c002e0039140303407002011b00c2030003016581d54850101300c0b134000b403669150452000050008010a0051003c00ea10501d088a0368600c0d03013000302c02c01e014080384624480492100e20500007060f406000401c06447c07a45030030411460074103011075139010b5500e060400d100c1c001c1002400c40d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 987000503 1250 986999253 986999267
    0x70206040206192d0e010306150e060715050a050903120411010903140a0309060206190b0604090207030f090911070605180a03021b09070824180a0c140712 68
    0x1328150070040720100070080c0d030043c050821104c0c0d13000140b0b904e510035400d600a1061f50282c4640e0311860305500c0b800402030f10303181820700400758007031805d000e44000034043e20440243d000d00e000f00800c00703003071006200d401d45102804c0c800142c1c205004800b20300d5400c011240d80950403107503030144680030300d00603200142075070405020492170b40c6050810120028403005510f10a6881030002c595400d02207854610544207070f400080c24800d450460381c1240c200403c020001000e551509590304070f020201c2e44140341c1100030801c2011007102054021002400610200000b8030000410340b140400500c540200107024a07915404070380d4801d11494000c108541100c1102c0c201e40c5c00e424040d54410003142409903400481c6054210340c100000f2840c0200031944402409859501e18144424901d010034010050003481d0700c0d00d85e50392001d00411519004214254505208d01068103542441c40410301b4055070585103144092000101c0d10b11f030750410419a101d04031240304489072 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 987001753 1250 987000503 987000527
    0x4060506120d0804121403130c120614010e06010207061d280b0a050403081605031813050405032d0d0c02010b01020a1e0303020409090f0b07020604020619 68
    0xd21840b207841c0034403a0001041c9018500500d200c540d481100c9400325121440c5441c5a900b500003070010524900045500c7d4200510855106c403040da106c001409901070b103140305561060b2200044500780c00800c21181c0074120075aa50561445d1010001c0c0d0b483c4641d102d640200441010110302840d18552811030078080100000e03650407800c0c00f402d0703056190000e80ca64459000d440026100950000c9498140c815243e050500b8034507103404d0500d800c07011181c00100d403081340300310000700180010006c03074940404003441198044284545068003d071040e40f654602010312010a50000c00d43d554410124090302c440c20040005c3c18891818162241028070085071030b076040d0546401800c0009950381c0200104400720004a80c7ca10b00000b000e48400742d11070002005c16044c0c08400300282c001c3c18090701e01a0360b440242c8c102c034000b61003600e44030458555a8104080e9a070f0181d08402188001d00441c2441c3d00056118401c9049609040c0040e424040006000341c02c81820 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 987003003 1250 987001753 987001789
    0x1050a05180d061b020703030e060703020f0d030e15010f05040209153402010f080c040b04081b0a0f150903050607270e010b0315060a020a0201090504090b04060506 72
    0x40c2ea889450301c80c004c1d083c60200621409541151130030424030005034101100d81541d942c46010394280c0a2204507400f080f0142c085018000340c81703201d090100701940404505c0d60300004e0680b010b240c07582c1400300d08841c040380001100010001000364840b05010740c1c81c01c66005a40705581c000140c00c64148086c840e1040d680490716000360100b082c240d108041145040a5420060381020b01c1c8506241e00001d0200712b0580020685505c10401c40c0c1c1c1c048889070646113059114500901c4c60340059002d0000f69103e91018911207844107070140040c00140c2d000c0030b0003402c03c030b011410070030b4a01500c06109613900308011402e01c188601d00045070407105464180c04c100000408040030b0401d108440f034565481c00500562107200e038001c07100b600d0401119642010b441c0b44a592000c3d055142c0b64076600d9030f900c0c0c503540708002403c10b14503580040180d00300c544000b41042d0300d82d5100c14481e5107003480260225440804142d4090f501c8840040c840d611074000440800e80f0b01c180d01c00c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 987004253 1250 987003003 987003019
    0x90e0a0b0901061706060405060a0c0203010f2a050309030307110102040b0301060309050111030610122703090905010b041205160801020703231605070503150a0507030b01050a0518 79
    0x425135046650614104031140b6400407070f6a415007070041500c218442e00b500042d0401102803410b114480401146100800202e41c0c03144124000303080d07416000004082d40c070088105003142c0504960680c1450003800c2c03c1c0e0079440c00b07480b51916808014000c0d000d10901c0100c2c2400d4840a50448000d441c0102e0601c1d182d5858040040040c608d42c0c4049850398a81050400240034101c19a482680010010f071800d0750041c004aa0604445202d154402c0d202c0d0744144c3e42829080c41c00c1440e50008002107200c0d00175040c01454100668413034030030540b40c00c5c010300c2004800c2c1e0407142607841e247d52030240310001d442c0c080d1420105001d11b5000400ca1100851060010340042094501940d20108114400060a0030024500030071012400003000180080548409240c41c070314001c000f0345404555460102c0d007011551051a41004a0b90b010030030710303180710301c540b90300b1048171700e401c000318500800040c2140c031034411450244500826210001a0494000c44003690007400481c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 987005503 1250 987004253 987004259
    0x3090f1215101d070e030715120618021210050901030b07020c0307060e1e06090d15020304051606050a020601230a080f010518061603020f030411030706050a090e0a0b0901 75
    0x10402c401a902c0e80300042c145c6005260a14002502c00705603000e070707070031207005000444090751480e0302001281c034250b8941e00000385030741c003041c410003c256003220007603902c004810100040d54402811600c8540c40f085090042d07461b5a03900c24150390744041288001d4854950582c98200c800c447c51750b05104000b404201a075010b140805690b500b500c0304030801d1640d907103a0b01c0400c07081c8ac2d9240c000c40244490000c5240412074518031a008960900f4401c0c8449056010307644112015200c55020300d4100e4114020101c0c103800504151030801c0c20f140c404c102c000e4031071006106542184849210848035081010190b003043c4e90010440c00310166110640c945503d200195041507510302800182c1c0f241250200760b405420b110003600e82590b810440603001c00141c0b1002e01007541c00d0104c103a0038104240114092401091641750380741e07103c0304040ca40040380e0400c908200c000d200008903030303400510310001d80301c7d4081814610790741e40d02940c00038658143d0483c0e011129070000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 987006753 1250 987005503 987005549
    0x3040b2a0a061a13110f0406081906060f08060a0503030409090501060503030a170702160308070c0b13170c0d0308090105160c020622060203090f121510 67
    0x30070403075841210280091107a44007a903907040c10920000703401440c1100c0d10320f00307546154041641d2644640e081030401ca85c0d5060001c071904a50040c101007650362051040766a19020380310001d100d451420310209041c000300800c010784008615080c0a0310b500842c15550b1164810b401034000501101e858a0761245108054440343c641030b2860351800001203002e00b00030003101d1716281d0310b0303c0c0d50100c60b00e8922194401880281402d0444c0a10b101030198010743e40d984200440c0510045074960070141400360b06007001d40d21244401008001c0b100c00807140c120801700310b841d176004405010011581190400451180082e400b0140400e100704058000381020701591041c0e000f003210b503885002d000d106400010340307407000c03d03520f0490302c00501d0080002d1840d130318074291481d154032402601d250104040e07000080540c0010600701030341c0c04e01c000200d20b4a081111143e04002c0c40c01d9450b522a01b03d42001800c0c03840c20800926209520034003e4000c042c081c00c00c480075400d500c04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 987008003 1250 987006753 987006763
    0xe0118020d260a1106070203120a06120c05010216060e150706090614160503042a06080a0f1401090e0f0d0c02010e0108040506070503070c020904050a03031d03040b2a 73
    0x403c8000c00c090802c0c0888070400010b026214a0703854009500d0802c514022000800009100000e140c0e1a940e01003403a076411120102c01d58450b80c1e040c10170a042100190402c5120001d07021054886030040000d00c0c2d003d00005082ca10503900c41c504035506c26510703206445280400f412203400c3c440003c00300101d680c030061448840b030f07450341100d8540c82c5407500e00b00e20b03480c002c070000343d410302c0410081801e1641c036150444e040110303168603007507585201120b02d0040d4000e402061069040011490142c0a68940040c0c1d9490401042801d1880f45860b08010b004d03d00c412503440c5000c0c0c250a02c2001380100b480c07440821a0300ba42e0f81401d00070026440e10030124005460a403d0450fd5406804540d0003680d000003c0c00f06680c07001c0080f10550001040034040110303143c10320015072100354606000d0b81c041c2001d4882a0784508001c0d042e00c858401d90b4a034030b480040000103404000c001c0d03405a032544418550f4484040320403004000b0000d0a410a00400c80042c0c0001c980020b1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 987009253 1250 987008003 987008017
    0x120a0f05010e0d050f13120c090f0c140c01060b0d06080d03180f03180801020408160305100911060c060609070323040c031211010e0118020d26 63
    0x340b1010106a0240b03466150200900011610500c082c0740010025030181c54081807000d21401c2250303aa1f55000041443c1c008162103c400e03042091054408078021504101e000d100140080304a80c20001c00101c010900141080b82c04500c0002040b0290001c0d4001c003406550079440721300c0714030404020011403041d0780451007001c4040c123215000f03011f450030080340d14151440092642d101c01c6120601c1c01021420000342050000080804060340f1025181071800103071501e0030320034550b00c0c003100c940d00c7c1d8201c410410020000210b000920034840c2e900c1c018042020485032500c0f40126103414265507204034046110034031003a00082403171181d00c00300c42004503616003840c1a801c59203160816540701b160580c800700c10200c040840341e04a84a1040c1d08191503480d140c55051903082d9102000185022000030180c07403003405080403000b040c0008100b4101d100f0105400900d250000900620500b04c501c001c2c0511f11004000c9088100810288030740f9144c0d0401d42036000d61 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 987010503 1250 987009253 987009263
    0xf090a151706130902040905030a09030b01120b07050c0a02181501110304064407080f060405041b0b031905100306090c0f081c05120411120a0f 63
    0xa0700518803694624035010310409000c881540002070003440160001e0341c1c2c00d83c1c000d5203544400001400c100000c0c020b01000baa241060a4150314281c504104180e111074190030b040c1e209000441c220f0050300b03070021214100213542d0301d0b410318191304003251118041c2d071000e17201c0c044140d41500481c01ea44030382c80e100c0294100281c01f40040d140500041c52010440d4400c0c442448401d015074001c4044d82c401224031075051074020046040442904032540781340103400481814040111480358003c41c05003060522031510414802e520f07400246818404c43d205c801145c24007a181c031101c3c401d0305c400302d0030b88401074441404002a40c010b40c1e103100000901900c4c3d20110049201e83e81c000c0102c0106107c8171071440c0c40f2500984242002695902d0221a00150848400d00d1580042030303560080d0000040810007241481110008601404030170440f88240032070003a551507200b03a0101a03d0920400c05010031124020002d80b048181300303079100002070205c00c00a403004603100b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 987011753 1250 987010503 987010517
    0x9030e010f02070e151504091b050d05040f08071208090111070609060e07120b070e1c061e020d1104060807140904050f1005190501050f090a15 63
    0x801140d262401d40310090060700600d1013800200e03000c40c200d075008441d900203400b031113003090005070b04240407002c000324815000404000190345401119101c100c040e174900c1910a180e10041d0482c0f04560200c0d05a0b039070340c0c0008041288003566121400d400c650001e03107803100f51402c00704007400d0500300d1010403604400036907003c0c2e05008010381100824449410440c96541300b00c00741c10409000c0704c0041d03e44102d504918020007003c80108200000d003161103070b4506007040f200348040c0c10340041007a01c40c600141c0c0d480d2045a0b5995090180600583c4038481c21325500400d4580206801e04016008181100000390040c100d5603141050811055013141030003c4544194400c940208102400180245000e403444140402c030300d120301c602e4401405d000a044407021a608601450b041c414000c45003508610034002d40303819210b07041311306d4281852010b03c0030540305407410803200154080c094800070301582c001c1c41000e040308004c5601c40d404030314541d41e101138041c001001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 987013003 1250 987011753 987011777
    0x3102010201050903040609170c1021020717070f02090115080112050c190305010204121b08030405060904090b07020a020907050405060d1d15060a0f031112120c010903 73
    0x302200715412140b45850f100030b240d00d08014480104d12923060521a80107000c603021064882c84040620007050b5a030791184440c03441034800c0d001c05200420068a44103211400000399091065500d044007410b003d500c2d500d141c0742c540200e0b002c002e4002c0d0401480b0740006045968800c4d142c000c4800c6171291807c5a880e01048504c0d000c41850161250b400400440141e0404064039922036010751903031020142c032600d5050a90b0f00603840000000c0c141d009031000d0204444081c12828880c51110540d01e20f40301d1590380d42c1c003c0f802a644240710000d52000f42d659150b001c281001c2d07000310070206510300480b02075201d400d2000103901450b1420001f4100900c180115026510018001c43c20000c01e594018000c01c40f00305200c405040d1858001d030500401c00801105404050712222680f9011050241d40c0c0901c3d03120318140741203c401800003800c04002034113043c030b0981c1c030700c1e4a100000d07003490f20300013141480d004100800546a02c15580640081600034007e071038010b24514 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 987014253 1250 987013003 987013021
    0xa0e0111070302040b03030d0e030910050901020a080a09031b030b06010c1709060f031501020f240603160303020d0e01210c022d070906030206070605310201020105 72
    0x400340c0391400d4150050002400189803942c400e60f402840a8112420007034030316520320031a0900030840c0c03490790000c1100c49041c07070030034011144940d0303900e051401e014450001035503a05001800814021001c00c04410311407090f2407150045411140303010318007540030141180500c0360b0100b6500d1300c94076000a0000d50154410f1b4110740e40c0030340d80030403640b01911041d082e600801c241d5940703c5401c100c8407000e41c80d4500658052110314410340b42e40840c041c006407030840d00f8221041145c0181e880c00309101210780000100360200c1d4003050060740c40f240040c0c18084020665240426603120110a06600184464811400d03446003c0c00e10020001900c10b1070345480011906d14000d0076800000c517503a000700d2981002070040320b4031441c0c40242e26915a80c5c400601040b04100c5e60b441444410402c2050700900e8980c2040101605607004540c0e24400d018024040a40b180041049502200c0f0190640030048524103d9a00282c0c06031066038401501030340150300300404141012 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 987015503 1250 987014253 987014267
    0x240e061003090b07050304030201110d141008120d02090415030309050a03021005070510180c0b03010806040201050c0703051203251e0c050d0207170712020904050c04110a0e01 77
    0xc0c0c000f2101d64141c0c2e141441110241d000500c101c00710754030b0384250380c65200828040d03c601190140c011440c1c44900348601c000c07182c010702c16005107000b0741c420040010040390350303a00c290180340c000b681c441c0501400300c040c0c4100400303590080d18210310940c80040c03450000e03083d240b00f0b545010b61165544200150002d03580006035100040f183d0ba0509140140024107420740700c0d90640341b9104090990404a90740358014007000d1380700d41041c404101070400c01d08041c00480c0000c034290b50504045960300c2100410080c18000e000401103201d200402c0003000840c1e2000449180c10003400d074804050308240d8500d001c0d15181c002e83d19110903200d1140751480c0042c1d8600340355038104800000342d41d95209149080c80704920034640894001e00040790f0081030f680080020b18540060030755449070182d281640c1e5080710780c0522041000411100c2c030103404030344034011901c460400e02e082c1000061500d130f10a103040405401c550040024264006654031410a400381c414012360b294 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 987016753 1250 987015503 987015521
    0x1b0e010501081509061011120405010f030204080604110a090608210a120b040902090a05090c010f05030a020f160f050c010c030c0b04050a0f0609020306060a0e0a240e061003 76
    0x400d0190029200d4109141c0c3d400c004e600501d0507d00d00202c01000354105085602c0700c2000c0c0c0d0001400344010758215801d004840340e240b03411132406242010140d00c03581d000d00020041411307200804610b03510481c0b4070b03010301200c0d002004040d030344030000740d80c0b800c0050660340007800d44403020042d602100f0969035003a41a440d18564003540d80420b0b402005a0320380715601640e41c458600c056124480042c0c862800d40800007070506040b013a082c546a00e54410070304004256100e816010792200640c3d400c918000c2c1c0243e150642d06600282c280074074140c48001402c0150000e0a0003a070880030500702e4091000d5948042401d001120031950580010780130488000101c800203012583c502e5103d03006009a070000802550b030510210040282511569243c0c0b1641080d8a810301c03815401160444000c0e1030680780100900030780034002d050b0b0f040182d07150240c03208800c08040d84c2c0000f00840d4181040315865041004901c0c8054440c5801034400103059280c0e18028880d204403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 987018003 1250 987016753 987016759
    0x70f090602100e250306050127020904060e040305070611030105030a0f0203030c03070b162102070f0506131505010b12040804120632060d1b0e0105010815 68
    0x104503160b00318050803200004455500c152004040d07283c40b9004030360700342189003480c04440c42c59401e06005880f81a00200d860302c0f003a4210b03060010740d203901c0d220f40c100ca07544056241ca0f240703c005002001315920008046580e14100010143d0090040958030310480f4100708116110312882c2181c0400d000e015010380c0182001c0c0042428007080104040c401400c0701d151030110844c49095400090040ba0380101c0c4600344220022403960007000345080c0d1030304805101303050100210071002220880201540050102c00b48004007942c00002074005040715003504002524003290b0601070b000303a50350018030144011840c414090340e070496600c0303820075080000f80c609504502c100039004a41d0b81e0740802001503041018030194414500843c000180220f014000d85030542c510640c5c2544010046030700342249140900042e0010703030943c0d030b01c804943d0a10b8805c2301110b10030408074424106000000e2400300381842581603032802e0b41e0f8503030b164440c0341441c1c41010400f80001e80c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 987019253 1250 987018003 987018013
    0x50129150c070f0f09090f1e14030a020d09030c03170409051003060b040b24090607120e030703030c03081923150901170a08040e070f090602 62
    0x108514104064191a14018031101d01d852541036400d45000030030362298901032840501040354240c4108441c00800341c407541440340c0100c0e5550069400f4010703030010b1a4141d140d600600003900541d0740b0b01c00e81d40c0221600b04001c00000e02e0755598000590810051103403a50307843c5454420159142101e07401740400901e40d080d07666a854058140c610304968203002c1c080000c04075a64050b01d800b411040010851190030b5041880c169080040b00501072403d00307500c10216112a440c8040c6e00c0d0a014110910811280140c0d041344a90200140e02c1136002c5a540140566512034071141e030035540794148200c800f0410715441c4c3e40340e03100140201d0701030303203500003c2400f404441ea840418030300d031302e0010310100740301d2021180044840e150f80d011015a03056103d020818040c0c0021110b060300c0e104041c8a0001032000005021f410364a40d800c0c1c68500c0c62903400c05c40039410540c440c0e501e548594071a9404c1c01030060031140c4000060031141c15600050140072a50152043d81c0e014007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 987020503 1250 987019253 987019331
    0x20a02061b070b0105130221091b0603070c061803030f050609130b0603070f0305010c02060c0c07030305070c0906030f0b060f01050a03230702070e011d070c06060810090501 76
    0x441d01d42039042103021300580070007080c8d03900461250a00106000030120110741d00f41826080d140c08482040b20b5002c0c000b0a0505030f050380c0d041d054a520540c1d601e0000c0010140b071402c40f024100508500100360100310400c410107400d50400340c0800c9003030f003042009a13114020410b03141000e6805101e6140e4140640c40030036440307100b03143e200401400f101d44040e03071581d980c8100145640140c07200c1e55108c00664002d41e040c400c00e50031580070001075003400070110b00e280d120016031100400340700c0c00040020810680c081520000c0038040c500300901c541c0c0f810100c00d10f41e050f42c0126800040c0c040020086c5c42d014140406005069407680c0c01c3c20002c9205400801e008410403180c07401c01c0003602440e4140361012441002598040c000c41480d1000d0710030701c503006801c280070f8030441c0e18511014003032070801c2a51041e0b03186428914000340742440401020a80c0241c2c3e96800f5500740d0343c402200300d0700040c40c180c1c03041c07008008284006c4041a0f0040314012147d040d190981c44071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 987021753 1250 987020503 987020509
    0xc0106081b0f060f0912151806060a061b0519060c0f02010216020d05010f1a0102010b1f0e0d150c0e190311010e03010513050d1404050121020a02061b070b0105 70
    0x40c800c050746d10002c840b00921440c400082d294001c49a200080d0443c4518844080051004640158042d10801e55a03810f0104c0680103084040e0705c00228002c580c0032505012040080602ca603c18a446c0c001440d040d00701007010b056420040340109044210441c4643c0c814405c40320354594918810103004a25802c0040101244209075130035034840c0c41c0059144901c1c442c1c02c4514481010000340c46601c80006402e681c0e250a07024410151001040c11b00d826900c0c070800e10010301e103000c25811aa070030000701450075120700904a07100300342200f090782c6103030784c4007000c5e40305681c650204080342d0301d0030400e03586a89005071480300d0141c4800c00001d02c030425190640740050502c02d198540d241c010038211001140c02c88255103138104000d052207001c1c04100d058001618000b5443c1c0200c8000c0c0890703109d0361081c281005108007584065402804c5040c02d180000c038400d41d507a0300641e20080d07031104242d410186080c1c61070303103404419140c50116811b0580c400c0406234240c0c40d000030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 987023003 1250 987021753 987021769
    0x807050706090b1311040c02030304020d1b0806010f170a141014160f080411010512011e0602070614031317030403030f0b0f060c0106081b0f060f09 65
    0x82110031a0b01c89400704001681c02c5100c5124482c02841d035403015110f420f229903064540c07950980a00c0c40c0040e9018001da0100031294000d0301a5512080e0011503d0001d0008510005402106030342c035201045a900210f8028101d40708040071401c05525003d14400040b800009503a043e88840340e0a030000e040f14824440e00c0200c0d6084d22081c416029124085d030f07400c00c68041e501c043c0002006180006150b0b07c40080405140501c8101c015041c040d02200f40600040d00c9041490311460785680316108844010503114810803580d40d60b07140e1402c10040b00c100c004242400c1d98070115100b440003500c1c904403040c1da91102d65500766020007042950000c4c1501c498120249c4282000c60703049490300e00c00c140304085190f503900c0d09080050880b0300f00030600c8066410161007820556542c0707009040717400200e5100d0703901c40306035041c68014249680061058000c2000c40c041e4501c3c59110034420b00ca003956416110045035003000316034815071013240744070702060204064504056074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 987024253 1250 987023003 987023017
    0xd09030e03071e080c0a03080d0906020a05040303021b150f0f0a02030c10020c0c01030b030a0203070f06120626031e130b090f01111e0705091006080705 67
    0x519001244042010908101e5190888404010b000380c01440f4019400d03200d00003400c4100240c00b04000380c00000360f00c030f24180b10283c4070010200e91500604580d6000c410025403121045641303c8020401511903007141c4815005030050785031550b0340506c1c4904030700c082e11004003070342101c061221035544290050156101030b07200501c1400316200c000001041410810380003035403113803d00d100392031910f00030b05030081920380140412080c480e4001424004401d007424042650302c2020080b80c6402d0f1007210180d4144202d40340041d504402d06c2c01a420742c4ea096030360f0745205403140c440344199803440c42041c00307031074803000903100d070160780c0c150302461200440903a494010000328005400c02200c8615070114800a00310341901c6001c05844002c2c409003020038100354041000540040180804034107001030800c40a01800051024900044005e80da80c80b260100b441134659465640c00b0315800307604c1c8100410603040303242124070300700d581690b00c0054968905404640c2600104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 987025503 1250 987024253 987024257
    0x80402041a06070501060f0807061d060d140103030906020109022b080c070819020609010c03050405030a030c050105150306011a04241e050d15030b19200d0903 70
    0x74a0122564071440200600c9000764000301b51242012415000d0f0451603001c8a86079001c240b0400c210703900111864559640645c0c241c0c1400030000c04684544180380900f10490720b030118850350900180300070b41c1664001c3e50b61108107034541e40c09a082f94807040019600a020300044d102c041151100c04120500e03556610314021090703520203030550401868201150481c1d41c0078810314804000459100902c0b028400000001c0e40101c1c443d0322070101d00504011a03850300304203140c001d0741182c3c01858081c1c1292131007400390500524420301c03020111019428600400c0c0c4040c07458203902540400280030700001d91903d020402c120106801050030703880e050100196802102952841c8150442e8a02c0401403000b14000d01c0710701c8891848507205481c0c030b03861103490740c800103a4081c180741860025070300c01d51164a64000601d5840200407540180400c19495407050a607002e44140706418880d4030341c0100e1034195110540c006000690b01444a03410381891030b005404850300074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 987026753 1250 987025503 987025541
    0xd05071b15060b0703020708060601020a12050a02280218090c061b0a032d0504181d0a02150c060609060111060c030621072603030f0f0c03040308040204 67
    0x588640fa415004500c082d40541c004000402003040c2c103100c0203500850174030190001084596844000300c003c2100309003000808984400c600f40200044a403821200c0c81813880c820038143c61789150010700c50b0803401640c04030b106900c50180c001c1d682d40a55003c5010f85100d00304141800095000b40c4444110030040410980101c0b40070301c41003500e1402a59425009002c3d0407804800340c5542c0300c1e12030649070152000c1409942701098030240d481c002040084001d02c010044050100c201426280b581d10b002e0490258900088850380301c3c0c8203907a00c60820b0010f81100400c0d01440551481c01c0d0095030002c0d0072031515a94140c1c0c00201418080102160496132510384007044882100c036003400030a001c1c0390b2500c00c054144000300d0b981ca440d20000600042f0751070707041910420036502c05541040d400d004054201c484902061401c894480c60200b8090340005030540d8080402d0038104c1c0411800b41c1c0302030841380b0582d0161602001610349600740700c0100802c04003030703c1c0a0302c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 987028003 1250 987026753 987026759
    0x20c12040e0f060603090a0b0615031005190608070e04020d1506080c18090403021c05040915030b070e030309150d0506011b0308041112030d05071b1506 67
    0x50000d840600940d003103010091410a1010200c0100074000ca03210320304c00d1040041c001800541210b2803548950a0030083d01ca01021841c3ca400400041140540110030000d03e1110010214102e6004030341c0e054100040401d02d0000d80058011000028452000584210b000344110844507401610040c5441c2c038a002c1c0138122503140d8003107001c1e103130020810845143d10404281e080300e40030000301d260259100f01656480c81503025035014141010000c0c00f03050007481060940325041000d600600442c0000030502e621501600380034a1408400d10741d00c280b402074038801d0306e602c030b82c40d680181c9901d001503d012840081e401c1e8984801c00196129494502c5d114034454040701015460380010345219042e104010042c0e130411010080044141c14082031f10003c490b00740c00c200d030f01a1540e042c41007290790b0038040640c004404003030005004a0010090640410030b00041003507440b90802100c800ba01a5071b42c60002610503d0302020038208000088061511040007c00703d503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 987029253 1250 987028003 987028033
    0x1d0906371401030507081e06130e1609110307031a0307081e19120c060510030312050c0306040f090605010b12090304082d0f0607090b030408070204020c 67
    0x40640c009140c0601035840000072560140205504900c480c1484c0755245044c0001070600d0601c20b00b80200c0300505404900c058490005074210001d203c031052090920003581c59950b003040c5103c812110310780f042d00103120f00e41403051203000300c2000c0c1d0880c80d540301c200c000c074042d03e010145007421a0961940721034035942000741a000341600f8002c1c0c5010b1160245904244911200014040e000503c0c0c544c1000e00c1144030300303101c690080b40c03102c60200a00301203400030003541c0700400061a003010320840180c0e020440d0210b9129503500907490301802d40d0001500e000340e030176007145e900c01d10100e032961800d90045551483e00100000b04d0ac40035413100c0b41990800e0b4040d01144030001071342e05141e0b03001e132b4641d40c0c010b850000462a103454860700a58444440350301519541c495102c1082d1200c0c0180c1d0208100c0c240e208840c400c41e00040819111182a00c80c280800c102c1c02300084c810b0340d0b203400d0300d1049421003402410441e06400740400303580280e5042205004035100b81c41d01507 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 987030503 1250 987029253 987029359
    0x70e09150702010f0c030603080307051308010212250e2101020d1b1404030303020d060503010515031e03340807020102010c030501030803040f020f030d1d0906 70
    0x1811aa0001c40d020484c0b41e820380441c0c61040c251401c16052a0042c4041280780c0b0460713811282a140c29130307132001549803211a940c1240c000001c1c6500010301e600c1d070202c8039a1018014904905d1028243d4200000d003540b01000085030000318410091442091910328031810f0000e01c00840100454070001c4a5800ca9021050603941160b50711840881d1161100e8141103120803824079288209a80c10400702c0e03809148001004c05400007030101c019840707034110794000d18000c5c000f4840c50030940390000307500041c155170074000e100703041c4101b0312003440303a0340901c2045040001c1c40ca000c140c501d8100d418844541c10760b000c0c24816400c800f040b0707600a50312103000d014140d01c6881e040030344002420745842c0d81206080500300300c01800841c1052080b01d0f005940b00d14410940149072002c00d041d09800c0612030341c0350094001c2108410f4101e41d0340c451200c010855801d1440710351003008103000042d9007198104030150155000246145400c0c5c581c031031285000008842114243c450710 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 987031753 1250 987030503 987030511
    0x130b040501110a031b1404171c030504060e030f0909091905070e0f060907050c120406050904051b091e1c1a0106050a0c030e090a022802070e0915 64
    0x80d070f5103003400311141d41d24007240035620551800d900704c0000407011030161f01690207036126a03a003440c105100c1e04c104001441a00390108480319034000c0141d000780003080103c409a03410350600d031080921000110444014510002ca59410070300000180f181454000301440a58400c45c0d13141070321680f4145100070414450001850001d040c4a2000c201402c0544410f000c10745440900a540e5100b00386030b0391050007484c2040d2100c0014613294a490b0b0080d18450002200080206015900c94010550039005071800e00c4541c9034480c00381240b00c084445007402c0b200500c03160186140c00450005a48100000d4860000e0840001812400c0c3c001d401001c1e02e02a075804410803607007204114000d140030300c81d242d00f0f601d0490007030058440d40001104128284480108050050340552400784000c0c103048254601a00400d0080d0b02c10810d85400022900f07100044c1400200445816076140d4040e0840724036064401310b01c84005402450240240039a680749a00002d201a1003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 987033003 1250 987031753 987031757
    0x6010c05070b180303131d0f1902120c1e070f0f260a08070f2f16060e061c0504060b030109030f1412011e030f03020d08010b03130b040501110a 63
    0x264920313105803595240402540317152074403003400c00c101090703008d415142e500221f0312402c00b91f82c888210810000340b1401d55007501d03c114004c01d1045c000200b1000e08271120741d90854030303025010a84001130070f0181c0c0d4401000718081445d42d200140d03030b0086a2724080c0c0328000780307088003071002d0b6800c5110f00d51045640102201040c408030712503012140f44c0c0c1050140c00c10107000000c880004204032590041100101d040882c90391200d801c0510102d0400c030320a0540d0000340b41c80c0810700e1614200d114580018550f071100707034000c1c40d009089400203500910b2005040340d030a094040903100c01001503071401d6451080c1a52600c083c01070812082c0b0a070345001c0c026049001c081e20300e0b50940000348030444144641e9180342d011000841c1540c3c407000c0c02070368004044018900601c0b05400081400351900280c00405400080d60707040d000750390322240ca85a0320755a41203010f01007110750140207100501c0e00c0000c950800c1c500e54015000b40c00101e03148032900007003000b0b40d001582c9240 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 987034253 1250 987033003 987033037
    0x4060e0a0c0903020d030f0e090105031b06041d06030d09121212050a05100608070f050903070803040b0c06070c020a050f03160f0e0108011401062703080c0606010c05070b180303 78
    0x420541c0008140014442103e55552719418a00440d9807907071a15100d40803031600c000c03040c0302c60351640c040c0d4005006074481c1195079810141c00501e00d10003540e240d07009204082803504860300406614054031a0440700c58000c458036100c807030038100d0200014007030006085a1502c203244502906204030078040c1c02180b58206040c164480505c03591103081086810700a02100561000d1001e62810041c41d04c00e0302c82d5081c2c0b00017420010107a11851540c840000c00042074001007001c0e0a02e0069041581c1e1103a40380803040d0b60710302c88100000d6120103c400203000501e0400c0f0745d000314074030180c1180c183c40e07070781e080d4680d983da00e54108494043c03552030104600242080c0040c0508800c80c02840b1250160118114070700041c051401804850390785130f64082003000381c03000c2108400461501d801d039203052000c40d036800403e0305646070081900080095000340c007140b0009510400030729600303251910300000ca400c4528040140040074501040556040000e002c0c0b954404203901 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 987035503 1250 987034253 987034277
    0x5030406030615180618051215070e03030412081318060602120d02250b0406061e060e04020c07031406101203030506060706090303140604060e0a0c0903020d03 70
    0x55501ca00c03000744000c001c410105004904130300090741040f21118100907000d034030300c200401003d07640c0c0d41150b03070440b00007040180c0c803100018240568038804c101108560f2181101102e000c02005002c9815510030001003101d00c40e1500c28110321801228840d041035401d0200301c51803c2180e00000390241c0e0f041e07800004114520a04000701501c0c001000700b0400500108a0f0340901464000d10641c0071407000c0c02e0149101401d0036040c40d42d102c44c0307510301a07841c1c0030400741350a560a0b80c183d40f03811000302e0100c1d0078510220304418083d0b9015507140c60400d00b124941100e00e25560015000d2041e512010f4042080d00069403040004404880402a071103161000080c2800402c448090003045004c4001554000c0785d50140b40115035660303200d0214200e886030705c0008003500e00e44a519001d040c0d03d6800352072803001d00100d1410710f0300e8001c1003105451031401036000d960b9a40010944a034030305c1d8011951410039003024801555690002086044501030680220380c02c4e2000b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 987036753 1250 987035503 987035519
    0x403080402030609010b090a0f150e09010f0203060f04360501110703170601031d1b040209131d01050108030309060a06030c06031a0301050a091407080604030807030207050304060306 80
    0x4141c4c40041e04000300104c1d0203203000224012005040c8100340da90fa10f08c1c0c031140800d10b07044181c42201c04403086006039590055002400d104864801c01946003c0b160422000180203c90090780020030b00070302112000100001840000c42c9607511002100c0d00e80c8040b441c040361603507440d47c13442900c0302103074240c10142c1c2940c00300e8842114049007000b54100003074216070350f00c01d918141c07040404190746141c0140d006011014192410320548540b407600c00100042c4d034032902c0591401d101c0a0581c80c001e01003a802030300c40d42948505a10b1002c1e2000d02c2541c822070320404510408400c11041c000c1d83d0342102c9080c0c00c0074000da0000010414890800c014190b0007006045040020500d1510340009144040c0586030405446070240505907480701102c44a00b00020020002030411081c02c0c00244080307030045a00c54a0b90070348280490700840e2003c110746060700504220380d62598101d071030640003016001407643c28400c0c0c4c000319900f0005030000c0c0010341c5000812900341228 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 987038003 1250 987036753 987036763
    0x2010b040b04050c0301030818031605100c031d04090b091e07081e010914010b0307050f18130f0605010e0a090c090e031c020a0305160f180e040308040203 68
    0x207002c0e504140c24041d0010180c81140c2c11a0303000026152201003401c0c000400188090b100c903454071442005001c9402c1e030b26800001c80f039040f0390401018102400c15070f001d9400c003d02074041070036420400c601c254942d11120401c1401440025030402c580d4504100f44401d488104240c0e0080700d4000c6418807240f2424156050440101402e07460a90495a2889e8014070300c8032814410301d01031410042500070149080e880845a01d030b11004000c0c0381d0003041910b5042d0300c41e03c04d01900089600303020910f4085d803007007d04805034200c0064a440f00130070018101d40c5108803001e40c080701203600c5a072500c5040b442210b01040765403628000c6050020080d244161203840c00750810005514002480300311040c802c1d01048041558005a09502602d000043d4004d13808140100d580c90b2a8001e180d681c0c0345403020005615450703c064410440383c641c0c100840c0c20782118841c5907005800907002c160004020304802519554a90413051060740d00b2070111303007500207201c218581401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 987039253 1250 987038003 987038021
    0x2007080c06070503090c060d110a2f0318010207030c0806102111120d110f0c033016050f061017010e07081014011a13051002010b04 58
    0x980682903040540c0b01584481b56182c04902c0741d080000c01040f60001c0b0380180f00b410043c10355080d01d500d59141c0c06049040700d00c1101110744035465044401040e0124140d04400020317005500340b0038140c0c2d0b1317590180c5400c6805810f41c0b00c1e8100020019200c0c2001d800038288100181850341004444e500381130072a50010040c1c0014070b48064107020381c803041400c1254001040d80380c4d00c3c5c0c0c800302045010401c00c0452030140269503103850210303080a0000c0c402e02c100b4044650740c07114568015218400034801d03927419086218001011070b0612000201c00c1c1240c105071096804039804030307440340e1040c801901e0040202403c401880000d024034112541c4000103848289800c0040c400c01e50694010403070884010040308082c08000d42c00b0b45240e584550031107100b1900c80443e42e5640d03030303804040741d401400c200107031007240c450180c8181216240000701e442d04074521015405174200c011403914252841000003010f070b8401c41100a490300341c1c7c000181d03050008080c4815602a64 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 987040503 1250 987039253 987039257
    0x3061119120e12180a0801050903090114040303050f1b0a0f05010c0905100f030b09070903020a06030615110109060504121d0901050d02191d010602010c0f032007080c0607 75
    0x124142ca100c0d843c9004565220060004070310b80d8410300d40c0054415013030340d005051158079110800000e582c0000c02803501d0300090f00c030903e5070350030801560128440c0740001070004600348050405c58007010058440580780b004947c8007031503040d16031450710620301c1f0159214495240884c05201c0280304094070043c0501c1e21900c1d55040c8408504c6403008000107004020020441821b4184250b00122810700010000e08007030030030b42c00042041c8013501059100c0c509035200001c0d000e00034415401103c22003050703612440c160340c0041d0b4011170851301c0c44543d5502c034029440000c1d00391185602c07551043c1c000083c08000c240d0010004045101b204005480110f031140c2d0720360702d41d00c24504580b412100e09011002c0740c8041080100021076074000340c001401c020070346144d4000741c020ac020207001211104e80c0d0b0303114200c0c203803544404d00c000890394252485000a11a070891008102da054000182d46604010703510702e0350201d00140e4458801085440034a0700034800c554100d4403038 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 987041753 1250 987040503 987040513
    0x3060f0c0e01050c0321040201030c0503130f0804030f051506030309030622080708040e0a0920150a02010203060a0e190b0a050907050304020a06110703061119120e 72
    0xa2001400d9001c565440c541480400700d80e00c03681010810445808640140c80f42c1d07000040d004001c1081d03138090741c0480c08281003a14486441c0d00c24403d072445289000c00544000c601074540c8181e103282c0707440648080c8030030040400462503080034040b5a620842c010030308003020842a80700040003031301c590701c60703002006402529900040c2480c1c2210a4410b0010092034070f283c103031903031401000c0090200c117020400384280303d540005031044030004010743c4100c0d9682c4400388216601028004c0c00484804220b03c400d0504070403440c00303848083c20b5803114600743c054508068201010100050f034000003002200e041401911009044940ca150102c2c00c006a6180e82c40790b008103550100c07a40c80000100c103036605410302c0000c05002d40004558100484010003071f50048405034003c4000c070708002250303840390000d001d40c0308181000c0d0140304d040d55034a8014045200d480d060340c007403c0c040340104249491503a070168449403102000c0c01e501805080c20b50345650321525180d004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 987043003 1250 987041753 987041771
    0x30207080613060e071203180f0b07240614030f031e0a0504030f030e010305060f06031618060917060c0a050903030c06071d0f1507030c050d050403060f 67
    0xa485030b00c03a880782c0d01810205450080f00c00345441c0496562048003e0760444001c02c00703050300710341001c250f034198032105003040391034650341000c044e00da04c10440d030b6090802a80d0003189250310180950740c180f040548622201c810502d00f41c40440d040b0080d801e100041315155840c2c03c2000040140c0504040d6080c40c074001450094003003480c84558103060300040008501c0d109008841c090341e4016101002c200701424020000d03881c03018500e000c00e260002081e01c51804401d00444900010041c92550b0740390b00f507481c4621009203030802070083c2c1660340d1a41000e080b0b54000a80280d5540d403d07170615020000403070b20000700c04801c15410180c240013045240f070701203904110040c2050359031000c080c4007080c5188500c560705212401628227000b0070590100f04042d008424444800f00031b02001c0400c9501034a200b00103520000e204494925219400003820450340281041d0404850503101e40713080141340c02d0980b00041c1c001a05204110151160703140060304503004001c1c0d400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 987044253 1250 987043003 987043021
    0x20415080303150111061303090812090108090118081804110307081006080105060702060c06070c02130b01170a1d0a0c090b211e0703110609211e06040302070806 71
    0x40d002e0a580b00422042d1f08120906020b00c509100074028001190710b10504170b2102001a040400710500140280011402d15841405503150b4801d022144100000f419940c0700d86175404903c030ba080d002c42ca03070a4401d10769554880c0906906040e0301166503031078100002040b60f0b40090100b010144422020301c04aa80910010b0549000f6524141d0b1140300b03000081c0c89008002081680b88600c0e4104440d00e0382c003500b4040414400c0d2048214507480101160503074034882115400101e180d0071450228050883c0076801008003200082e04070038070402d030403100c00059400c030380c13a61140b04ea03042000b807110703802001044214000c200e00354108000590601c0c0c0703400f82040b01e1400c02c1151700540414030581c0104c488540c0101100c14060b10340e03580b5842e240c402607503162005038071000542484021258100c8005082e8500c82c0108010b4080240070004454014030511a02c00020050104442c031900c9000000742140e2074146002071802c0082c3d008407895400c40b00600c04a88 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 987045503 1250 987044253 987044263
    0x60111190b220b04050a151d07180216020301141b03070f03020315210f120403080d0f0609021c0c02032a0a140d020a02060a030504020415080303150111 67
    0x1c2d400607420260391545d0409910300840f001028265041c1c100c0028041d4800e60b005404050300c0f034200703045007001c1c0d0611a84510301d40c424400c2d5508038100620490040368000d2400501500f00170740328940c1a0042070031501c4410020100502c0407061094a0000340075211369800b00101142c03a42c40c06c844002c05c0071440952030303030600d0b0700400414900c2c0034810301190031000143c801d001d1aa03000300f158011640c150f440600300c0c0140305105018560205442642303c40c111107091500b46103903a9404245c0c4410300002c1800d0755641c0d40c00000340d150188000a20386010050384503808400e400174001621441506d0300b600c0d102c140307003080d900881505c030500104121b02c1c81b00c410328160300601c0c4d802104c843c0d11901070001c00008100d101c0d483c1c0020a4610f00407507041840d80d100603a80c4500074100654040002c0c4044a0068803d8100316070081c400b41000c034071544200c0e64004460510381120006400202c1086030045000b0301c0c0c84052102481c0200078420042c02035500c83c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 987046753 1250 987045503 987045571
    0x601140406020a0f020607020301050c0414040e0d080601090905090a03030b01021908030a0f020708131502060f0406290f0402090612040317040f0519030512060111190b 74
    0x2d201c0e03400d0b2045d9982e080566112503000760003440340d89030200d0f40304180d034040c1c068014030440c0440c1c000d00c04e003050300c942c9207130719044001030611009d004001d84042c540100094100142c400b008134241030140a07050103118860001c1120b9955454040d058480d1401e19904550008094250b880b056003031122a864000340781d0780d500c1e01d5604070040a070031503000c2e107400e0f41d00024100040105001c000d00c55200c000c4980d50315691540c011440280d6040c004c0d000591101c4045000483c3c150035060f000b0f8403030280020740040c0040c04075400070fa0748002c590090241400d5013540e06200319100038210003210118984401a00082c220780104031900b000e94036000c000070200340c0194425410880c0d080140f190301c0c036280c42e00da21b038440300c0c0d802110036024601c10182104101480881020b1381a25901d060030000600da0340d102400030000350400114000084003101c0500505103044e001700031103117610243e81040b002c0c800000d004441640c00d66000b03041801d004c0c800034005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 987048003 1250 987046753 987046763
    0x60135060402030c010816031a04180c1a0d021303020d050c130b06070f0203241b0325030615020a050f030304080a14070803240d0b07030b01260601140406020a 70
    0x100e0007485810b00c0f07500b27550050f5a41c00c113107083d4032400fa220319564040309180c0320f442d20784481d64a0b090740480760050440c1c4a0828042400344a110b01b02540181540310712191080c0f21030741c1d4a40005040d131210480c04c0c0d80f40d0704030b00700451356814624080e00c51002c3d401400d0058034081d2020501d2842200d202400360304861003040115901848140d00f60200d40d0050441c0700d001c0d60800b10030800c181c0311034034110842107000d980050031400740c0713103d82a055202100752104240d00032119240d01c80c5401010760b50303403001c604d8011650102c86815010350040079055914546a40762040030220344406510a00c00c020000700081d0496420500034500480c1c148098241c000643c0500d44000b04a101c01108020001d100000c0c5580b1b00700b45460840c461032006414401e01d1982142c000c2c0c6404003040c00549080c1c0260401d483c0d042041c5810714803100410fa0041005103007080758500300d03c0000600210390780c8003207040c41014402c144985424038141000e5a1000e1031600101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 987049253 1250 987048003 987048011
    0x60f040e0f160c0303060e010b0c1c091202030307050f010b12011107020402130f0602011406010c15050c0d110a0206091603111c0501060f17060135060402030c01081603 74
    0x8101342c440e4200340c0042c2401150f0108a58540e070101c00c56800488a80071a889180d80e441d0000780c0310345860f600d14031243c407940c40c01c0b41402a40d64a451862030203030b030148010403e60000a004000b44a001c00f190000007a2541641c400c006090030b40d045081f07200e81c105222034240c0d00e0410300701da041d55130450f00140d850300c00d28864400340c40c0641c80710060b1585444002034054064002d11144049800c801165503540401501d054410345000351200034807018889181c4c80a07400507400c103c240040d50b0514030101c080509a03982d0400141d1011f9001c00d1041070240c0411406030401a610081c01d1000b040f442d981d1004001c0d03120190400e00e40e0850a669522904a4016441d4900a860344400780c1420458043d2403144628204003003115000941c510701c41510a46581080c40509800d034a0026042c1032880c094101c1441040f001c0f0303010b251070401b4010203016140c0a00940410f28160040600b0401020442814400d40108101906101c1000340039210743c6030074005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 987050359 1106 987049253 987049277
    0x70311010807080c031501031b090f0b0301030f0b04030c08030c03071d0a0b07110d05100c08070807030507020a05030c070f0506070f0b0a0b060f040e0f16 68
    0x5030044e041407010550480c1100315030310303c0810500d40800c2c0015941d00c0041905881c0c028040426170790720080112880c10200c0714000c8c484003008a06542c03442e00c0b203001180036078100600d0a4400c000040c10140500303100d07161160402001c1740c8a1070b0100d40001c490b80706903818000b007a200740c84003101644100b14a0341d02003010b40491a03152403d914020650000380080715128109642c03480c8688a0852603503250740210010700c4042c1103401e00d80100c82da4818582d04208001082001031508460f0450b0008100e20700014a80c0d9404412403c205104000030414000080d014100040000d400d20a6416901c0011045542c2c1c60400420b481502c44c001c0480c4181d540c5940030441003e009135100c1c011000105601240c0400242240e0080118100b500e03000311303090207209044423526a1110b0b201c1008001e6040000c144890301810403040010029044000 = true := by decide +kernel

theorem cover : BRFrame.Cov 986870503 987050359 := by
  have h0 := BRFrame.cov_init 986870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 986870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 986870503 ≤ n) (h2 : n < 987050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
