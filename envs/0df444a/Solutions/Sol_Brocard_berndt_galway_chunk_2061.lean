-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2061
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:34:08.212036+00:00
-- url     : https://prove2.me/submissions/9c245554-45c2-4218-b78e-5102a2d14584

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 370503597 ≤ n < 370683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 370504847 1250 370503597 370503643
    0x1b0f0f05060606041d04030309050a061e0c051606020403050d0509090a11092413050414090d05090307030803010801090c0b181905040216050105071e110c0301020a03060503 76
    0x5099000701034102030f1701d14036840345070b655410250058210fa480003070880c0a801141c804111607a13024442d800d01d100080c80c45000c621040d0403c9941075070004011a01c00d1003181c0c20221011609001203115200260405942e5955149403000449540b0041403010820400e01d003046c45420358403415050b41030002c0818a02c0925244c030494101600804c02c0c90b40317880c40040e560030714a6000c000d520850355580350355201c3e1044100700e402510721460a19494420310240d00c5031881c0503c0d0400040c004056800d10284c9456100c4107019405005034940003012549007000785000305240320010942001c0ea2038049034065603a080181918801c0c46200d9150b040c40340e01e000070f0380003910780e482600442100c084261010303900841c2e000f4000036502003608541c8904581151051000740301a44a4901c1520031803403035000300000c072668a21181c40e0714031440800140e41510025a500d080c401400f0a007682e0280c1c4641011945411040021b41010020401030140c2d1340d10030a01701c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 370506097 1250 370504847 370504859
    0x1a031c0e0a0f0b0c0f0709090201110105070f0819050106030e06070c110103020a11070b090a12080906090d0212032d030106030507020f010608010c200d1b0f0f0506060604 75
    0x820034500886400950200c0c003045400b60404c222101e8179070100445824aa0b03940c0c00c6000f50405082c2240000d4140b00f41848095050090306d000c1d43c0291500340c22100070003422203081c100205802d003000c40900b4031442030302c01c41c401c40d8064152079501142c0d0703420100346140707880c801034065000c02c8181403e100229082d0300300b81004550034a00035981e140503410459000b02d00e10700303e0045000d50100010414045c400402c2c4002068907899951560b554070725480d1510408041c146000c200700281f03040c41c1c91401852191401044900021750580118003981003844181c0e24640c00040d40d01c82d804400250015059290a40e841c03084c1215001b210440c00107201f180185612603000c1a00e8500902c01c0c09190181e04000304030a030368072100107018103a11038406010403403031854038100c036002c0a841d529645500c0c00401054442010494180c02c0c0400000c8480115003100e5000030740d4418400310190154005600c100c66504182e410040081c101d5445218100410440 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 370507347 1250 370506097 370506119
    0xa05060d0f06020c01020c010e030a020706181809150603150e1b0102070803030c030412090506120603010204180b0a05100804110d0b0c1e09131a031c0e0a 68
    0x1910b0350040c40540c84c0d18038030b80804d01a00070310b0072000a81d420200300000e003180010160110110940c202c0740940e40e00c50080d6008440006032440011400105200808902c007440102d9202040000b500e48081d40781c8035004045094400c5e11741d520ba1404000b80140c41c0000c2d40030128060042000d0340c1240142580c0c0d450862154031040c0d01000d84201c1a8002c3c08040001c00341d22058079034030300c0d00d0403c0440c241d204075421039007150355201b1000014407907403205d000c0d01c2011b400c1c42d1402103d0360319428959030007454180d05640070000031481c8080c2ca9003140c020214180045480f00001041041c200c5850b0400e500401c85080700d8913102d40d100b21816001a00078200b07801810308803020a40350080140090011034046080c01070004210004180030000c04415191314244d50401040038420250040d0b4028042c05881324001c0544c0e120b82003a0074800d01ca00c0996900001180c10300c0c039040c1c4801e95503014000511900b6411450032003803a0001c850100c00d0ba0705018080503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 370508597 1250 370507347 370507373
    0x306041103090a020d1407080d0305090a0f02040914070b04090e01050c120c0904090b160801060f18090f14071803030f170108010e0c0a0e06010c02010504031a0a05060d 74
    0x4460b405e100d84034801d1060301e20038040044121010713144c905841e5500d107039a81100b0042d2000091410000a00d508004141c040c0c80650000303091007102c101c0e400b04400740c240c1080036a111401ca0a407500c00502c01c2080790020103a0b03400850700d4038030308401c040032245107082800559040c50200300d200b8102c841255881016180400440d80321f155140c002c90180171011354103e40342ca4044c0042c0842402014403d0303024180c4d000b400c2199440403640d2903020b10a900104140b1280d07007e1050091003031050072900040401211662510b0341780036100083e0f01c1125081e500d0301c0700381040d001d0032142503101409042881ca046600b040c1c896080c860f910015080110040f0070800e40c5104a6680703158501178617418076503503140d204250003840b0885a401c41c80c4941c02205d10141040041602190226100c04403140c4d40c1c100103407000341d2400d5040341084030400c00440043c1c03200e0709002d032041806110103c64039003855045d04a072000740445204c0e001c200036101c00070300c2c0700b8450300e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 370509847 1250 370508597 370508599
    0x2010f050414150c040b0a090f0608060a12150c0e0a030b04060b0d05100b0a170d02060106031107021017010b03060307060309050604020f04060f17012711030a12050306041103090a02 80
    0x41c7d034071841d400d412901440540c01c81c560303600c0048000103105a010110314040d0004494078644c0c140c0d1200c41c0740d404402c40c20000c22103550540c0c0c40000d104d02c1d5000000c0404a420100a1000c401c0c00144585c5529003044614450010031301051020314800c0c01541d003025940c0d000b0360300709911000e50b6058807440e071000300380d11821203100700c2d19003031450f400a00f6401c02441c03645c0b10180a164980c801285020014494480001740340c3c0d12901138124940c0360341c81110701c3c128060f02880840c0741d0407086c00c0c00780440c5150580301001421105802070002c80340307583c1c6a051003800c00d800c0410750703403040d4101401c1c040b0b0000070440129120350000e0f41140d1000707111002e00041000340c0465841201c2800d552040055400514820b6802d4191000d00801c0700380e044002010354241c050210304421104608140d001030748280840c0d8140030002d049803240c060329600c0110200c5040d085d040000c6001c0b0074040c0381e06141c06410945041441c60604500d48800c08550b034030312964000e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 370511097 1250 370509847 370509869
    0x306010306091a090102071205030118111207050703032d0203060d050d030b040b061303030c03030b04050703060501020d03110a0309170a0e09010e070219020102010f050414150c04 79
    0x580420050404989611400f41d841c80c1a61400400990003504502c5098401e4030405581c2e1640501c20800c40b81680e070300054584011300c4040380325005001000c6c1c003480b03c1c0300030041c59403000002103545100b045a59031300c03a0303103490701c1c40c005066070301c00014017090080e0301600701601088885824418110b482006840c0d550741c1002a0100b400020081d22500541e280b1624240d8940c00c09229002c00340e03414400e2015207000e004052040024001107103035501c10a000280c1b0a0b4a5400190701a2901181c1094040c0019045900a8a4240100396540c00c01c0140d560140030780099031030a401c0421a000b29800c2c0d1001c10b1081d500c100041541d00e14505040029081f041f6000c800d44952668544231500e6010b88182c02c508220341c403e04192000260001c0c040d0140f40c070854030b0380d0180c110102d0504e240a211300c1000e004034103654035403c510300c0f03081480c841c441c45140190319600c024001e14410324100140604841c0807150705400304101801c1d803008480898518200c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 370512347 1250 370511097 370511111
    0x40e04032601080d09060e06090d1b0905150603090a0b060112060906090e030a05040905100b0304050a140d0c11190b04061803020904061a040608030706060806060306010306 76
    0xc90010306503500c01c0c00c1c0840c039040040707084070000a02c001c4d03991241d280e0b01d01854840405455000302c0201482d480300c010030035190642002860100300503c203d00340007a180a01e0052180f000f03640e00320005159451041000381000d0642c640c0a215041e41e0b9a0321f5401c000543c1510382001441c00340602c51002d002c240164030078054828840c0b503035141008001d403a80b00e048050003413440345418081c1810308072034914202000b210740d0629252a442c1c5045c0c501080000030f41130080c21495981010300c0001680ca61a1004500c1140b05102402c00d03000e41d8901000940c1d62680c0c2071042c0d81c080450f01e610281c0023121102c640d60880103404d14030080c2c20000e80620003440382840d580012100c0081c450340384030040c0c003c0d20711540701c048502d40e1740d040030100c6c40340c0f030b00c00658480c04c800c01080c0801d595034480d8404c124056091411040030401050503292554040c1d4866480042d0501c14084140301d180302800380203001d070205042500c0021f6030b512040c00701401a40c0d90f034503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 370513597 1250 370512347 370512377
    0xb0a05040201140c071a0415031104032a061407030305060303070606030506040510020708030a0f0603021018090605011e0201020d1a120c010801060c0c0806040b1b040e0403 76
    0x3815a410309503003012130391105004072450715502e0b60701c00c2607400201d00d0541003600020000b03840950351b40f00e0000c10086146007040703029001045440c11100d804110201c041401c02c0160442c86440d503080130454212034450110a00850b0300c440b00b0004030284403508a08100225404180c151801040703070b0300c603480001d00303500c40d85400603c0c1c145401000000c001011031407500c070724059415510201d085c0e860082c03c0e4803441c6070007480c02000304000343c2606025031040415035004000010620b0b101c0d408505912010a900c4000ca1980080030322682003251a00c005010004e2091126615000c00a003800b00110340344140c80c0b0381081c00340c0a0a20135419580462071600d4107100042605241d0450071b841c0011036030180c48032419a8000d81400115400031070070694030303041242e283c1402110045441c0e001225015079000340003800304020000540518004c44032401ca500b411180e46507514a808080420f402c0e0a0100300300506203442002c0d03000d07805050480c03a0740e1070b0754 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 370514847 1250 370513597 370513607
    0x16051b0102210f0f09070927060e0d09120605041a0408070b060301050601020d05090303041d07032a03021b15040507141309080c070b090109120b0a05040201 69
    0xd42c40ca074081a0301c0200d580c400d20305034400760107122824503800c11500d40c2c00311110071500c1110302103c0c56104040800180c80980c0c40303807174040003000e1165100743c60501c00030454511b0000c00d541150f19441d468400740c000f408100000e03a41424006401031a0040342c03e0000c25030540035040b0b5070b9030030010f03051181c4a8000321000c030154000000a26041c40c000045030040c00d000d0351004010320004129080520505010b042d050f00109243c8442c988202d496074407008a40c1d425010038440000c0d8900f02e003034104201181da041109251401410040440da02c0c401401688078041e2200040e40311042c0c10b40015443c18a000b40e039480c0740084010070760303007030319520030342ca2061038021204402c2d410503180c0110310075003d03650b907940e40ba510902d442141c100e14645c400807403c000c1c0300381c209980c04900745512941c0712608041800e5519810018694020400450f0010701c030f405030342e80a01d80300060240014030540044517511128824107000b0503805a8507501c101007402d681c018 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 370516097 1250 370514847 370514857
    0x18030c12060f0c04170f070e0c1b0f010e01053903090a0c0e0a1b05120a060306090c030c15050301170a0203010c0509040e120304080310120b0f16051b0102 68
    0x2030301c075010b0307050403a0b000c1545d12000301030f4543c001c0c02121800702c1c484048c00d510030f004101030804207040c85201042031441602d50084c50000d072240503101800e03c582030040c4030038244500c0000411745404c00d032a040560101c5140e82501889440e8801c92161030707916002c0a90440d0103c6480b9070b1010429880c103c4e43c00401380010800303020000e1180b003980400e5214110040c008d02004440c04205543c240e10500440302146d82030020000b80702c007030b01855070300c8060714901040d10780d9a500d4000c04c0311034080701540d42e4540316070309005000d401c5074101d0061080c03030302d0b0003038942e500203004110b40018040c4590002c240f45031161702c128108040750341c1c0d9400038020408450381c968044d001d6800b086c80a80940e042064890b41d0710b1021400400d2541c40e019501d18550301c596500032103501c002d00c00800281c41290200c1c141d8580c0116210341d030b103d1805101d00c0d0500517240030303080e000101810500042850f012080035884001c1c1d4081503000c0720007213954020001410b01a00032 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 370517347 1250 370516097 370516109
    0x8041104052e030b06010311070606080f120712210e161208070327090c0e0906010e0405090129010f050717031003060218030c12060f0c04 61
    0x5060500c414520303112032a1500031140004850000665004805102c0d101e100c054030400800b000140b2030750007a0010311104c101100c3c4039140220340d41d6605c040301d41c20703000801d080e4807460304601d0640d020400d070b60444000c440380d6420300325550344234000021290200c0c41044418100354149900001d030004842c0907060003801107000a0081c6552800307100b0303041044a112100002e101816400407416103604113904a1a01c007464500751800c0c10310401c031b480b07818014001c81480c0b40030340c03524801a242c2c0546c0803450350003440c0700501048200c91824405c40e45e2500f445250b07030700142034000c8410306480115456443c098901c0c01080b429400c8480e50500c0300e0700300d908411b05c150010903408240c90304031002c1484035003200c040c012014018100c03c058150741c100c00cbc0040002e194442c440d00d4200d02c1c190b031240d403650b003a600071100c03038a00d40ea10700d040008107203401d10410340f10b4901502c0f094100036584076000d81e035103409040d40030049413100204409a03c03481c225005814 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 370518597 1250 370517347 370517351
    0x702040e0f06061309110d02030309100f0e0603070516050c1002070512030f1803070506041e0b09010203160c0e0907090f0c090302270a020703092408041104 69
    0xc40003164985490007241c0c454851408810300704004c0380c080c860f88408a070031606059446060505020094a00d40ca043e42d00d80704c140402a01503a034600042d040b41d841d50340d010403140313000e400a86992003021140b841840180308018215502c541500c21030340c031412141500b031590303080060420342c1040e00c254005c0c40b0f1020916049800080c1c1d50100c54064400c0e262001e0140300840c4ca81c0982c0d0500415040100b08214052414200043c91100003c00b5030f00542e03654030000310386601a5104003504403444060b028151000e10904000b03001c4140024a44024240000c2d220310070902e4000e042403a45115405006503580018060106520313402450b017010b10358540d40d03090354801c1d00c80c040d00340040030351811810f01031940c5001d03058452100d00d030300f03641c2041840c0b02c075600d1398040a00710700c248200803801c00c05c2c1e15001c0e8a0301400140e954415060090007a09646c12440754a58190306003000e460b6854071294594280c0c1c505406c10741c40320b1400c036080204901c0c680d54024 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 370519847 1250 370518597 370518613
    0x908030a1406030c010c0b0903212502030d0218030111030f0106020f031209010b0a06031509200a11030325081021061410050d1104020702040e 63
    0x103015510041401c10360408501041c2d031014101a135940b8000140ca000500554442d000100b038007203081e0700662010166424080400041e003c0c140e040d01d0303440c0a02c411903040c400703030f4890058280105074542d501403940d201d2212000c1d641e446074500782a0b1007540041c1209030418114092400480000c00902c401c1c042036031050095041541c010103054450000064180d000064031090f08010b6400755090a50a03c22240407281c01401c22985540701c601c51141a40c03110311900280c0003d450014141040c0f0b010401c4502e507035000b40c80c900d41750030071541801d0081e10001402c0c079403a04c6000d503039003030621040707403042c1d25200351a41c0e6110100900032a0001004c0500c2000b840c540c0a054185400383e00311040c03041a1100c100d05504000d0502221030301c54004400790f4044c50007090351104030750350702044603c0686001394140d00082409150b90f5603003903000003808200c924034068078864545080c0161410320341482a07500003061021501c880d048540c0404403581664421 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 370521097 1250 370519847 370519861
    0x5040f03060605010e0316061412160315060207030f05010b031009020913030804020d031803030801030615030c0605090d060501170105090f030a0810030204020304080c010507141c090803 82
    0x20b003440e80580e5000c150b4660b030740078250600103610854016000c10a02460303281160903903050300d0744e41014400450130003080b40110200940c0301d024105d000b001a5140340031001c01412501100c2daa0581d0a08040c1d08202da26800290070007503940100c0c0201c0c3c40746451401900403c131840003030fa05401446202d0348601c03c16808250000d0007914002007560702d08000302e03101c2000b110010b0200f49110045005803c0030340100c00c01c90f01c2070504062804000381c241000d610781e0ba00450004000c00c00620801c2150700500058030551080c1c1421103081d581c940807094898040c00040100100da84440e03a59011080594280c0040c02007000f5611440302c5000d00107102a808215030806011a11007503002036080d64004001c8061800e1501c0402d044801000c080c202100001c410704021002d03070780318401513016501c1114429940c2c1d400c0b0300c12a00b55a001060b19003032041e0440303403101d450010005c85e22582d862030145446201d841500100138401000f029010020110401a80c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 370522347 1250 370521097 370521101
    0x714011821060621030c050c060d0f060e04020603061311160302010e062208041d040209090703050d05030a0207050a0606050406270c2105071103030f06090705040f0306 74
    0x207603070300a0400b4001c2075102d0a910301040c0240841c54000c807100c40841c0302017803140c1c10b1110054442c40648054180900004000c5d810058414550755a10286150013107424829000244042c210750717140d40c90140c0001d8140d000041800303005425140522401800d60361100c03500c1c505112005440c1c0e45500700c00200451800f030118055841c04990320141d4070000b651503c1100b80319a81c110800042045d0440340d03c5a00003140c3c030710814031005c80c194003054503414441c0e842d102d01c80400d141174010003900c4400904012500c0e0000750044c004070f040400c100b188000c0c60305140f035681c2c540e103da10000388141003010b445402003180b07241c10820345802503011101c1c120307028854241c03544005520344007081c5149401400500b00b081d6071842580020544101601f4805c04051103010080c50900003141d504840310740c1d074410040181d405c1702030426038402540081d81075217005c0c82c04000c01c14018003207903c00c41c02180000e0146206401721006481c180f5804e540c460b580c1c0ca00800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 370523597 1250 370522347 370522409
    0x90415030c0f1a090306070e12010501090207231c170a061401030c020709050402010e0d050601291206270f010b0a14090409020d200307140118 63
    0x242a41c41c1e0883c0024122861041d90403218000f8058500c036110001d00b5a207208180e040e41c0c1c1c00050008041c4d0090740280304d094020200c00d100035075a42890320b03201d2500c1d00d009560122840c070161007103e4440380040e103400c46074541a2000d41a2207a144182c07400b51000d18041c125500110403c401d41c01d01d5000303141250244031108642c0b6034400019000d888c040b01d010801607001e51010810300700b10303070040c2e130704a4018103080860915903404620544600802035815602220041040c0b8500303040e40f02d013001e0200078010b00816101c0c4005005d1084941c0800b0359076400d40403c1d07542d0f031a07024603042c2c0c1d035428040e902e844006105072442c80300100c03000c104900110780000784072a0329008841400841c0e40c0c136000c0703900515010402d20742220001942080e40ca140da00700503181c0d2400100110f00070b007081001048100c8411004011018106000743c001d020108908005d034840300c1c204a02c01d007080e901446c0700602091440b0901d5010303401480d00b9005c0503c0488411841b08 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 370524847 1250 370523597 370523609
    0x70b0706150905150108041103013306090512071e0501090e01080607050307030905100519090809060a0212070f020114190804140111180d08090415030c0f 68
    0x40700710741c1c2c4a11030302c01c4803011240e02021210444400a440d8400c4e81c0c032a6000e07104250310006003c0c010b000c02d0840c2d080011081c41c1a00e180312105c81d1026041d0f0255109201c01d20141d425400d101c4024541c0c222441014050502c0c55900112840280702d6000034009075501c003444805900e044d001a10f500c0c0c8112404200040004550a904410751a060307810443c021b140350303196640304480d2944028035007800c0681d80c0841c1c00000b081400b50fa44102a420070104060402458821030f050f03e821031075100381d180c0b045c42d200007852442a50762030755049030381c0c0b6200c5031410700c00e9003041424440c070008039500042440400c8800032100801500070f9071907100d500359404c1c900b5000d1280400d100400b0300c6003882960217a00c00d051041c4e0083c481c1c0010341400b641d444a003030030f49003100c0e07c0340381046010030a455038808003c441068a4021070b0f121817518125200c80c4420300c1141a40b5000d20340f1407a14030903032612038500d140216070104111a0b00740d034402c00c0c02180d00c0c10340544 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 370526097 1250 370524847 370524881
    0x51504060503010902030319021507021c0302070201020a02010806040f020f19050a02030414060c010e0f010b0a03020603012303060429010e181f02090a0501090602061305070b0706 79
    0x10481d410b05119010011394068000d6140c039010300d542c0c0000500e003400c00c40c118800d00c2800e4050078403105401d030140e000740d0010b03c3c80200007455054901c61004d0803004062040c40300d140581e90000d0240c5031141c080c20301c0c07031007900c8410101c0c0240007203c0c01955807500000308480c980040740010b100d05440340e00620310030a8204c0c0101c0e15840349000780c0005901c180300a004a400503205120b040304020042071070898204000707429182c0280c1d014031550011550710b40708038800e00415010300001ca842c11117160840d40050001d02060184400c6c026a045e41720b8103012074942021502030000703080314800d16252400c1c3c802c03075010803c04541ca8562200300880d54104c0740805042e910103034418080380c1d8030119480034408038034a00981d14030a84c9040104c0040b50103001a01a480181c00b503a2658088244810344800d64807107810010400d0040068542c00700c2d87c0c6821100f9106090301c0c02590382007551410100c0d03000782c001500001352031010800e0720b42c8007043c0400da00b849c2d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 370527347 1250 370526097 370526099
    0xe010c030207052d0f0a0b03101d060406080d020a0303020c01060b0f2205100807020109060213031a0408120405030c030415031503120c022412090c03030d09110405150406 75
    0x83c0001403d8045d034117900006181c409101d00c0407883c0140d40d124502c201c281020503a07072107c02c140f200c00f0081c8603985101040c01d0141600741806050083d0040c940100000285840c000b5620160303100d0190415501042402c0910b00a420080081a45095064807130f019613460b0800c81c0c1c4400b04001030109594170308174200c40c0b140c1c1104119040100241c41051682c40f007079030620001031a180c115542e804000d000602c0030302c06440008042c031901d00d444d50440c5012007a03800d0725000c20550b00d1a0b07070704200000e60010b0445007405018002c45803191160328201d440e41c0030307151001895000100e40864580c81c041800140560f05079010b0156510700c528049898015000c0a0b0841003072894110020307008400d4080020702c00782101c13034419044c0c0e118104006101c1000191400c0001e92a1196040190155088010702018000c0c0340c0401e4002580c92044e00300c02d400032034840e807108003400501d5a860080940181c014403a6151110031b810b4840d40301c2c0c0c04a8072851900da8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 370528597 1250 370527347 370527349
    0x150a0504060f030e12030901020714010506030f06060d0f022434080f04120b04020328030f031b08061203090a05060d02040b18010318030e010c030207052d 68
    0x1c000100244101900000c402c0e45c000c82c005070300080c9154480d64007001610005280c403028540003e103200e00000d6079003002810141030801c2a039180131983d20403420b0081d03075500c68440060f41355206031081c0c808a010f1003c01c200b0070410784624080900d903064864140085070041c042411403a4007100803414002c2d016024442c0a5888101080c0d480c100600080c401c1005094503140140e0321400d0655a91120310b44001000e42190400700340011300007182010400030340101a0140310788a407121f8001c0c6480f021101c3c20b4054200306100140c2e5030081d000758410072540360348140d080c000204441c00078018800c240d0386c0ca80100c0b5400c803650186000802a100c5942d0000e203c0107000e8030b000204038050f0800340c3e455895545c20407001884803030400082030142e144424110795150795a0014007120040c000f460003074402c00040d11300117503104441702c5103003109003400120b2041c0750908900d40240b54008a400c00c002c1e030172090040c0c03003440c6004418241c09007905000d503501c40c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 370529847 1250 370528597 370528601
    0x30f0303040506101a180f061c0c05030610030f090209090a05070b04270f091505010b0306151c110418060602190512030705040e090a150902150a0504060f03 69
    0x1001d00c15450900c004007141010031b0410690481c014071400c01c2000c80070002c0c9059000c0c03003003401d042c0c080d40413150440415006040a510740d03810b00900354a80072011a40207805500c6010805035920300550040000b68000806240c0103403040f40646440051b01b9a20702184200303481e42e200385040003816100540c101c0702a100d40b420920050001d142102282c0b102c082c030200080f52f12480d0807280c010f02c0b44036070712005001e207181d40360345284034051380129074041e00140050316041041205030b49892000480380d40e6101c202580d115104407070800200c0180414001513420450708104a0400d2409001510703d40380100c160010b80700e113035904641c0b042c412040540c01411001080d00104141032080500444c161000b810268004000c2940100c80c944045500880d0a00007481c0f40c08c0800c1d80900341c60300070983c150b500d844098101d5004010719a039947c40b20031080441d221004035803107145107070460382d445041c19034014025030482d01400300090003414100c60b0a51283c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 370531097 1250 370529847 370529879
    0x406021c2a060c0806010f0311090f18041110050c06011e08030a030219110c060d06050301090605090118030c03030218030a11011407030815030f030304050610 70
    0x94550503420301d541c4000030070701c0019a28248500e50001d1038480852040e010700021041c00b03650b205080d2a240d07001602e070040c10300c030b0001050b1811041913600d8040702c0c03c07942060022074081106c1041840040c80000c00315140d546514115810b010401c40078400d41d455024044a43d251142218901101c0b240100304c0704001f1030744110010051624413182a00070042080b2002c050340e074031610128030710303844034120200090380000d000103640c2d00c020b42d420081740c0300c0c0b40c0400d100c0002060781d6504c940d01007c0700c0c800d690010300d0030443ca5850b480310005140c0038000f07000198160030940002e00040303401e40c3d0030b5400d0240c04d408101e0721081d062225645901c0f0700c02c0441890320224020b4100220804c01b5540c001564001c035601000410a8a84200782d0106016a070800040604501040100318a030090150300c0000e038202074030f282d21401c90003090380c8402c042d4001910300544104103481074080002440309010740402c8040c41042c00001d156203982c0d907584254001d0340c00c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 370532347 1250 370531097 370531153
    0x702030303010b0a0302090306010f0e360304150810080109030c080a0c06061202040614030307081e0310090c0503060d060b011e1106012405030a02040306020f040602 73
    0xc1000103000b142d800001410705603d040c64010f08103c240c03000319244c0300080c0c0040c900c1d05010f000400c00c10101041182d4400000c120700040c6007601d10344a00704007076103101c503811266a043e924582010400569000340254507007610150711184000e0845001039031024103440700010081a045014012011295459601c04107110b15030380301d50116800520b0201e0030090712600140c04100c06010f0580909025002d0819049640c41004102c03442c0d5404201950700780700d503589181e40c0c0402501d02494005511a0b41c0e50340103096900031040d00d06040c0c10003280841440106e80a6003030710000d45140c0328080020240411003a101400308444a41e03103c6100c042940001e11280c02c40441d0601c10305001805404500a4501d40d4600d07425060006000405c8103060b800104481401410748030074019001d020400c2e442035440050703d10703505004000000c514603219030742c12100251b402c05000c6440d95038a4118540365800341c820200144a4600b40200710f41c1146280e85907140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 370533597 1250 370532347 370532353
    0x60d0e0105091b010c260315010903020109050d0c030605130c060e0609040f180b070e0d050c060c03040801020d0b090f060121020c060c0403170f041a16030305100605070203 76
    0x30f03000112a441c00c1840200c071191208006d01d14012941c806503803585000425140d1640b42103003402144240e180f0b15a81004041c0f00c0c1000580d07000700c441d0042c2d90302a1045541100c050800e06104006a403008000700e00d06001c00840908030080241840d203c0d100440003e5a80c00084850310300071441c09501000030004034600d80b4240d8084050000c42d40c50110340d955020030002c0340b01401010595400d88190100b084255015254441c40c8004540340005e000796034540e15510312106071524090750b030008442440c15403c2054800500c200c0c1c0c000c3d5038582c0c0c079102a074068143d0f01200c6014050200c0410482c03810031040d14410701069440e468603543c47c0002800380f96248040117031841d420010f4120301c08003400003d00c50008654100d994070303d5032034203001724000b4107a16010701c18280141410000c03511304507011124000c03c07030a80f00d0303030495124006200c0c4000550b420410307075940794201a0550405486a118202c3c00c081890751003200343ca15210707500000b03515070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 370534847 1250 370533597 370533643
    0x80f01030b0a05222d0305090402090d12020c13060501020a02010c020a05042306060f070303051b03042307080a240e15070f0801091802060d0e010509 66
    0x15072991229500220079074141c803913585540490030b802d51042d84166101280c0d0070444120720b450700c000ca40c400550b411071014801d05604c0041c1640030310298940714036000129004565550f500304005c00c0d410001c049038500070400042c1d90345a510059500643d0044054044254140700310f004856040c2c015200c030f4110356004503a842c80c7e125040340d000c00b0810700801c1507122446080c8801c203000e0486140f03186a90b80c2144100d200400070f9226000c10060038a1019000c0183c1e0011341d41420042525165080844522911142c00030024400072042006100c044650300302c4040035119001008040701e411a42c94801034003c40c1c5c1e90741d0000c0c89034000504100161544074482909440500d284a08050300342d23202d071030003503885a2090960600d401a420072040d08a08241007402d01d0b0524020050103100301440342e410b015541e504c0c40003074114a4400135290b01e41c028109613641395204803900c014001c04040442d298603180008020440000c3e40b4a508400d01c039602040b8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 370536097 1250 370534847 370534861
    0x6030c0913030909022d03090706110a2906090705040b0d020f03091c080402010c02040506030a0b07030204091104030503070b07051605060103020f09100b0a030905150106080f01030b 80
    0x7141907910110204140d00400080d010b07005d1000c2e14144a0318070320030002e10150200041700d501c407940900c05c81d000800c01e1050b06800000c02c0400c0fa02141000307000d4044500300e00b8180400000054080b401d40c20400340e100030544218540c0c0b202030102d8140e6915000140000e80b0070480c0c0000118904000c248200d940010180200128050016103410b00600d021201600107507031581143c1d00c1111440100504240d05940802862070080b403540351580000380128071103040079000c3d07031f500c00200d600d588040c094994115040a50900d1605040000500a620510554220501c0d10001202002d80361f011141220781200045050060503201c80000b00710207001d001c1405010807100c1a03440306000080b1510380243d000d400c8540c03443c0180102c145800c42034074461200b80c002c004911440300380c2c41c0241c2c2c0a804580b0389410a58100783c000b043e40102c0a0528403c0d041599044240c20b50200d040e01d205035112000c9890308115000c0f54442030000504460140c07000a00c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 370537347 1250 370536097 370536121
    0x10b0a0f03181a091515010c060b0301020a0c020907090e0f22080c07090219030905010b06041413050402030604030807020c060712030e03091c0f020a08100506030c09 73
    0x1600c00c8441288000b007940d40d5501905506410031941d0b540f207003000728031481406418050100341a41243c81d180200121000400c928461418060803071220b00a2286503070001c038031200041c4c021543e411060401401031030080c05e0891090014500013180f4510440d080403c5800c40c80031840036807a41e04554648030401088050f140348100c0705502c1c07040c0030701c0b9031184941c0201d686568441050304202d0410080c0d4011481181c010802c031908041210f041c0413000480d0b240006030070600d8074000380500481021b568ac0281d0200300400d190603034074240400e1140c2182c13003100300e01a03140c5c031760b040d520704481c00303545a00218005001300e07000c1c001250340a1087e02c140c620283c400c0e00000c1050700501020b6582500c203e929404080d0140309001050441d40002d5003007410540c0060117040c08000c0603101030412407801d1013001100034000c600c080d070051002110700c1c3c5031450a9522032007200035032000c50800000ca08142000300c1c1c801c9091001804040303e40c2d80b4100788d000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 370538597 1250 370537347 370537361
    0x1021207150606050307020601050316050402030421090501021005040305031f050411030619080615150403110a0603150902250606080708060c030726090312010b0a0f03 74
    0x41d9549a070341d1414020102445100301501c42c070b850b055200d05100e08000d01c3e050051308510f009a00c2158800b0132060390400c06001c441c4c0444002d69250788914010350144400c58170241030121a002400b03119070090f0400c8141c500a07400c40d40207000d05102030301034402c20b4038007a0104104002051502c0380d0800f00c42c0c20541450403245000750f544c0d021808444e094424104041c43c08000e111083c5840034040c0400c0003d02c180240d86401d10642c10744519001d0050890304c0b1540b011800c640e16000241d4245508212300162540d9036402e0810180d03400c0d007580c500c40d018010300030404500a1103141400ba2160b0988030049081c40c80d110002e5102c0003461107804403000148a07824800d82c6140c00b02c1e4841c64000c80e00e5841c14400e0303483c0c050540c02c090380c00e0b0813082c204030780800713a48142d07a4098241d240980c0f84040044a18400e41e41015100ad02d000200f0304000f041078000000306083d1a8444403502c141e81e1703c08603000b00d80129984500010341910741c8107219031083e0024a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 370539847 1250 370538597 370538603
    0x30c08041505030114120c010305060a03020d230331090f06060206011403031210030f051b010509010f230a08090c010305040f0f051203070804020a060e01021207 71
    0x91500d6254000c81d1000c1c29801c1c030001c0080d80002c014006000c0b164110121064240c0c0c00c062144500d030806502d41604a110328101903441e4000b030700350364510350350000554000c0c0000c0390f041a03c0c00c1c0380c0080e0003441c03042400c070b80c24807600305100c0000000310f54492054071032043d45e01084a1800c241300c0c062080b000a1005c2c00d00700495084814400c0300700d0b5506060300094101d1502c50041e0400c00140e108041010450440c16407545010046407042c60344142410550356801e102d00c00750000c59000a04540030b44e520810800200064048003000d0030400c1c0d13410010f42100468441c800d1291007400101000c9003000d005d03018405001d4540055481c281005642d003003c0315885d041112004001684941030041a40c0c051100110f510404e280501042c07900b500d404640f07044509005018907076056141c03007400304c10300400104804e1002e41b9652820306003c010281c5000b620264800c4c848074200280e160f008030440b88100b00c068003d05030004800102c1c800c1900000426 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 370541097 1250 370539847 370539863
    0x30807030311210606090604030209041e05210a0507150b03100b0f0411030103331d010e060601030e010b0909031216080c03090c1e011416030c 63
    0xc0002c90b0020005091501442500d1040008000c0890410500050329141c02004100101641c40d20340728200e40c00c1d01e030181e8200300c854540b450190400b100ba0080a9149039000d10300e0310400c0000b040c8201d240c00e41705018414150407044410440c480c01131108003040080108c0000258050842c400e00c0303a06d4000041d04000e000b01084c1400d00ba0603100254a90b99030f43d261003403500c96981c00040340151010050f540704012066100d203c11b000103042c0000d041c20340c4103070b800d0856040603480701c0c01c80b84102c901f46280301c070b20140610788003e50305511060b0b903050309200148035032090344880380c0c000d094541320440194010315161803c0c0240707540b14500c8114645507180ea00340a60031600081d907503a14010700700c1e0313010341000c5c2c80a000110f9106900f00c85a03404000540c0003410b4489a5969481d12500039107001e08000285812002c4036001d2804c880701c100c40030007440c60a803103040303120202210383c81c00f0744180c203c156000300b156015400420311612208044908c00c0c800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 370542347 1250 370541097 370541111
    0x5191b121707080907060519081306020c030301030b01080d08070324080d14071a071710091a0a0e060a1706010306150b030f0c041703120108070605040308070303 71
    0x440001c20302122000041414101441902c07402040108000c0c00c0718035095013040400c0521014030800c500740b000c1000b808002164080b80301d1444010f000d503020008540d6100c4501981da281c0d04240b10954a40ca159000003501100211780300c0320400507951079100a9840311025002030900120124000d136440c4808034469403004203030b40c00f500c0500700400003400084002003203510f8110004c42da181080c460400000e044c1c035006903180188400007801a99108002c5030761014608140c1a44c8895806200e00031300e04401c2c84094030510001480800440050750160100980c00c882c0c2006181c0020494902c404041c650000c0c3c00a10942d94183c0e10a5002c0301c1814003010030040f504030340010803c000f0907100307440f8042c0f07401c01c05139520740c42c01a5a040c0c1c0c0c000142405862507070000041c0b807007003650049602800c6a200582e500005403c2403a540381c010102080070920300c500080340c00500000c101c1d08540103680c5d1a4945400c66460a109410410044061548039a6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 370543597 1250 370542347 370542377
    0x10c1205041d0402090c0c030d20040b0c0c0109180e1c02061504050c03060108060406051f0909062106150611010c080702030d0905120a05191b12 64
    0xc0440151502070341d0b45000d801c05004210b8903201c040e0501030041000c0001c2140e099012050b682d0800401000142115140540c00c00f41400002584424040020045100ca00700ea020300750007807043e012074031035441103001581c44641e103024900344056240b80740300502540d03411030480d180500c81690400c40702c0024030f0071201801107001d80544c0280081114480e441288c184001e00101c130280306a0810f21070303010082c0f1015010394104100100001c0041d11150041d60080c42c02410001c1520000c2c44240e00442c40f86d05040d000440d07003000046c071010700b8020901134079140c4444c10622240a4010f003540000158110784113521a0071030031018982e410450010809515001001401a82c1d06800c45800121031000d22104809121301a40c0c004141e0304081901349000440420500f0140d00c4d0000da04007041001e000040c4000b003c0c0d03885009454041103107052132000301a617460964001c90344403c484180102e15110390080f41c00200e40b10f13050005030074000078240d8900 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 370544847 1250 370543597 370543619
    0xf0b0c030417010204030b0a1e0914060405010203010504060b070b0f041a07030b01110f1b01030f020301080f0c0a03030c0209060a2d0f0b090d060e031308071202010c120504 76
    0x12401030342d00d9502050400034030125100d000e5004000700710400c034410711850604107800300d40c034188911070361303811014003041b60031082640c8041d00b040440d00c081c500f81c40c2043c00707036000340581ca000f82c1c10101e0006411250805558810381d0140003004280e0360020004010070f00204107642c00c46002e0210521003507a60992070241d451690003240300d07110a000076110076007181c2010000e0b44920a00c2001d1840810703103100d01003030440c0c40040001d0381300c0101c0c013070081800c4004080e80f000000048820001600318504050b1005452001c6860800c00c203500100d4440503000c180800918001403900c0280903520503401842c1e040030719240c0e00708000180d01c998a0302c0100c1c440f5441d0001c107440a00020004080c2c2100e0040e0741030921001402e58050120f03110b00500c120194481000794581115400307010010459413914880c8159070140d008a2262011901800306c0c04107000c9040381040e00c03c1c98061312003198584403942da00b06d00070302c1c5106903410400c00344008200c514010b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 370546097 1250 370544847 370544879
    0x90e09161509120f0f110303130806130519081201060e040f0614040905031605030a110102040b0906071a070302090405060a050d08071b0b0301080c0103060f0b0c0304 73
    0x2a0340c80610488401c030252198540d6085040000400392103000020060928a0702c0f0b6a40070f001c0303040003410391820050b100d94012215a15001c01b040100046c1443c8407480704440000d0200d403017a4850418882c074400704e501025005401040c0e0164031000210180e02044c0d00c580a030601e0000b1844031100078900c281c1141c4000381410314001c6a0340f81a000e09102c6003403858040041c1450203110100b102c4c0c0d8141014000e948030603002d42449001c0c402d43c0c015000ca04040302d682c0d1001e03d0a10780ba130384841e10030800f02d5000300d10084041014800e0341c096030300d108100340c9010040401c0040c0342d001f50030200d5810650403807007000f044800100b28007a04213a1409a1104c020408000640d20000c0559008241450302000280d542c81202c848991f006410b569840b0410708109012062001c200000c181030032600003800c0c0000d000541c101c03010301040c0c8612008102c0110f042e40c40610450340b00c00f1301046c0610003070045030002e2492a183d00100c0b0718196071602030710403442d01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 370547347 1250 370546097 370546109
    0x1060f0c08310e160e0402040e012c0601120915021903050606030f04140303130b0702060906010b030c0d06090b01020c1c080a031e0f1b090e0916 64
    0x2464955102c416401081020b4044509540e680e8941c02d00c1c07800c501c01240200003100300c9101440d56842c0c14058980d807280c404000d40195507079a103c11108207007540a11550056403065040d030040012901000500b0401c140419902ea4035100c004650340091048030740e4001d90b60f419540002010f003165106084407010002d85c55040c0310750b99030040e00030690366070149400c00f0300f00708166485208490340700703c070085112819115414080d5840b0500c4070340c40c01300d100000c10320810541003070345001c0041c401d0392115503e584001d4202d071604800c2d50304903840c2d0b00c40001800070110300b5020315448050b080a0504181c0d050301c010007600c0640c3c4c01850200d589a081c03005959052050b595a240141e4a106105036111280004101c0105001c0c2c01e554000c42c2c0041418480d41020540746a100b1071510340c0589010b5040c0106268462410460714141d00500c41c60400d039141e88034400b0075181d400c3c419150120700403a41000402162050044090f0b40101c0401036007403a0252503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 370548597 1250 370547347 370547377
    0xf0b1b12040b060102010911041d030a031a0d050a020d020301020c4e091f170f012102033f03011a1c050a09030201110a050301060f0c08 60
    0x1c0c0381c01d11022414010340154116410007001c0c001081510050129140066500180d55000c079000c2e80e0702d008948400e03a5a5000020f8003018059241d00044210f40030061038103401900001044101d61841138024096084801000090700e0b0a85e503e41410b0b0018002629200c2c155004900300841c2801400c075440c500050b001100311111003521b0f000d43d418500840c000c00c800141e00d0200410100756840d080d00003000112900c43d01200c0061740f41c1d40100100c0c2c58444903000e000c0f03500340d0a103d28018a400b0002e0807200c00b2a1100f4101c03072550081445000407a01c0b00c12107030b40040e0041e42c1600c50901c01c4080c1808561800d1072040c07a110020103048401591711540b2071040040d0400395105000500c6a04c3d20300c04540d1b0721001c400b5985507100300030405841c0f03c81035421050201440c0508004903903056030804c0d5103d6201c0d5000b00805846c1c031180c440c1074016400f44000080040c4018000301c1c0c0681c90b450942912424801000c810603039845040e5484129441d80000f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 370549847 1250 370548597 370548601
    0x7080a0302060a050433020d02040303120501060f0c0c08030301090e0f0c131a1005130803120103110d05030d020a110303190b1903081e0301030f0b1b12 67
    0x1903041c0041608800707800c0e8213104030f0a282c1c13660503501001100c40ca50b1092000c401d014202c808041900d00346c3d81e00e10341903480719280202da000940280c030003600030a119481a624400240c40b8081c103031030b0242c80c3c092001e10150003c8a4110352284126801089503c012a0300641080a1070081c9004400070801d106844500c1e0f0410940d8803112402c1c1e0301080307064825035904400750301d9405d01c0d100005105104c1c46081103015054006580d00a20388540b40c20700564800020140001c1406510728291741d1114031595130f1180f5480180c10242c40c400502c00114608180488520000c000c554076000b941c8401d411a4401e94a00142e9980010001011030300086180c09618049000d18114602120318042c091000307000035a03e181d0f90100400c0682d521061400f001c01689104502c09480346800d1701140d204141c010f01800c074001d00190b200d030540007240c0c10f0f00e50101d40c42440010036136941c0f12080b0090309005a40440744401e011600b401c1e80617024040c8800341000c114 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 370551097 1250 370549847 370549853
    0x90604030905090906060103020a03060302180402041a03030702060d06030c0b07020f0603150f04240e0901020702030d0c0201140d0506040b01022d0709091a0610080403030c0e0307080a 81
    0x1c144554403150007040c411041001e2120b003c82c14a50014081c02e0150355007003203a0040b401000d090300021b41c050307031480200d484031102500c0c45d44118426101008902c0d02c81030424958100380100030391650080003620700600303010000e0040000e20780d0011900688a41d070b100742c0ea08030754200f10100032000c1076a60030b525000882010403a07040e10f01740d1641c02c000100189075800d41c0c1d0f0050082d15008030076140368031198496607401c50b05054800211249040034081e8210f00d2013000500301c0208007190219406100b1201440e600400038003450604c408151040d0b040c8403030a0b0f0510060703102d4a42c04244d4000100b2240b0400e030300000e004d140800c01c00084483c142090360442d489032100001022040800c060102c03840c504480d0114095020346240141380c3d0008204036003809115810000701c044400f101c00c0800900c184556182e0003403001e20f485505408000400d404040750110740668009401205c0750710303250000c4d84120740071a190040c140e001000704e5020113481024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 370552347 1250 370551097 370551107
    0x118030c06050c15040803010302122a01021e150a200a0f020a03050915090612040218130b07120e0705030d1707080702100903031a030d090902090103110309060403 72
    0x402c0540c00d8804c1040c0c201070f251840d4a0005000c000d0207080003440414801030100002d0b00708543c406428104400c403407004100289038041c03070a0244c899119040051424050104001c00000b0000e00c03031440340114400c0d030b0b01f070044c205000440c0d542003440b04201d030b401340f144500c141000b2142d03501c02c00503030003c0235090590001c90071504101030840c0001d0340031048810664040341da00429242c00c0c1e50140003880385460503540014002407a02404201a0540c2d00c2a0300803036103240f20582c5c4107203048422504903180c50000307240c04e800100180301c0c2040180c01c10600d103011152070100094900484064000807413190b40301c00070070844c03450700f0028201205034600c2d0012064842c61410094060081d02050611034040006019a07100304541c040003c20300c4000c1c03051340542c0c1005030040c441024208944248210030b445103041c00581d81500070300c039984a1a00a1800691000a4010f59202d03410143c03500d0401c0c0000e00c1c55401340d40102d9241000c1c1a06041c03601d00900 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 370553597 1250 370552347 370552363
    0x105010f150e030d1d0a0e0603060112030f030c0e0d150c030c09050f0303121302100e030a140c060414030c040b0619030b0a0b030a0b0a12020118030c06050c 69
    0x800c01c10385815030030032034502041014984515080902400c8055414100316041800c045c0e50820541c07000041d9210201511500610060f01519404d91702d1740d456441c09110518013401280d00c0f01c002c40b02c42c030721950107121072501038a0f00e044048000d00c00224144140c25060345d82d00580b2440c2404450180720711160040c1d1800d0810800a00b000080c01c111260720409205095000308202185c405000300c800b0300e07001d2502868945401ca03000c1c41080070508003607004410300c40c410300760707240034490144590790014020141e0580301c0d80c4d4014408191030079480d841c014011181c999449803000b07800a03201d959140b40c02c18641d4002e00d031900c04001142c501c40d0341044102c0d0341d1a25107904032101541c4074100e2036642c40792048240c000c0c041d1080b490b604650040030008581c85c0381c00155018820166060091280c00c03c104110310b10240602ca101f2000071202c03000541c020440c162044a414017400c043c543c0e40d8075540c0160210354000f00204600091088070780b05d041c01644 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 370554847 1250 370553597 370553639
    0x712020d090518180f0d02010612021513170309042f030711030708180414180c04020d0903120c02030a112b11010509060406020313050105010f 63
    0x3407031031411000403c0d9806480f40540010014000301c1d42c04508003d891074410001812180061505c00c00706558228000f180350055107401004031b881c41400c03603a950180c0e0010303c203074030b1202101e030540165444414104186040b50310001010035034081c40d804c0c441c183e28040c54981d0812024002654500c12a1a40708040b00c642d0b48141c0e5004070049039014000541e180e1070380d0f641581590040c507444581c045a11001c680002040503d0300189251044080d45404624484091105582d03111850901e0b10f0091000205509004030740300d80c45000100445282050180120b01280c1c0405814401251901c040c001030603000b50990034000b00301d078020012260180f40084d124060001118108540d4944102008408000c40b000621031105000600d42000c4140341950f4107010114002c00d9040e80949045481842010b03c10800c6601802e0a0790710b0b075031181d0003981300038070041d01082c5044d0b541c00806d000741b003040d010341040000d01c030b580c90800a001c060107070400d80d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 370556097 1250 370554847 370554857
    0x618180603011508060c0a170103060c17161d1201060302040c0c030507060b1315150207080601051003110301030303050906060f0f0120011109100305090604110f04020712020d 77
    0x8020070360f40061607540c01b00d11007259544a402c141c004807414081007e845052209080001c418481d0700d41c1700d00000036564035070030a801c03000302c44114502401c45a885110038000130076100b0700e00503801c98140c54503030008040c10156003c002002c01d1030f50801c201190399a8181442142041d214906800400e81407080ca058025a1b00a01d80c3c4900c14008060319250f88442c960368841d90348071080743ca84030b0018040c11a40090507800c040c0c440c4034051045004030300c0c040882c0d0010520400b95880349001c4d1001e40c0c24401805042c48440810008150359010b00ca04182d4444010b10301940c400d0307a0110f00d030705268185e103240c00c00207001940315150013015401541d0340d40007105915a02800c1a0f103121451015224215056103008103541d42041d00040300c0714486401403a420b2001c60720209015610fa00403021200e00719000e01050380b040380400c005c81c0c02d40c6078001c04004000c214600320a07030000450b060360022941140d0140001140ba10859018080112002031910300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 370557347 1250 370556097 370556099
    0x30b0601050f1606021204030c05160f211415060402030f06010c0614011203120c210e0a230f07050409060b1f0206010801060e0606181806030115 64
    0x410b140703205034000520b0040f0f81c500c0c283c00300704058060b51040d21210900c14400d00c7c00b1708001c0c01c0c400551381d0071181030090310070f44d038054031081d05042e00b640d180b03210300080c143c14060090701c04001e86800b00d21400038450243c0000d9203541c661241c0d491b0000180c40f10000780b5540402c8604090650341c410742c01030080002084038001015417012007445e09580b40100e5041100080034814285550b100e2440008200b00300b60340c0c0400305161182e552400c07604102c00c0c0e058100c0e18031035045c90010340132194101010340c2140d00701510000e504030008520703c003042840e01e80180348070304607204501103220781801c1000c444210060700ea0a00944042d101582501e0348884050040074800c6136594000401d02440d6803100a6840002e404800361980c0e0000c140c0d40200d00340b90403401442080004030b40e0704c80c10b0041d04211282d00c80f894180307846030002c104a0707401c41101d89400300e0343c0703518503079060303460030075004030a50890300e40801c5003403940605007961003a6007403480c0c00c800e13460 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 370558597 1250 370557347 370557367
    0x80a0809010e19030e120c1509030a06090305040b04090c03060602010209030616050c03030903030103060506030a11012118020109060c03050403080f040f0602250506070b07120213030b060105 84
    0x2d03202c9080c0c0c2c0e0056450300c803901510b016150b0300e01411160b5084041840141b058081c009503e16510b8421541c0c0307002d020002c0c800362a80d102d840700385905908600c221000244040d0000340c442442030400f00c0c1804d86580140c002030f08030b81e01040c0b10035150034184044d160984903034405071060344029031800f003020b4042a51828042d0040d01c000c40036250034914544200709035503018181600b92980c1e41413441245a070780d0802c1c0400d0300c515141c48086611071400060004805034440b420b0400d2011503001900c01e0600300f012554000d0056044084481880c410151030300b0000d0b540c003200b401c3e680001420841c0ca60000f03410301908044c031001203600141610104c2c1d40c422061503560011014104180c0140d1303000d1082200720b10000f10b0f50f1a004144c802402181442c3e600703a41a8040d20b4155180c030034401d5036002a010001c04020035105040c055006040e404d0840f02d0f040000140e504036408042030600e1071041c00000e00400204140d140c0d0001d0092134444e0900d9901d103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 370559847 1250 370558597 370558603
    0x120c04030308040312060f06020109051e0a082206030c020c060a090e06030309062a030a080708060a082d0c0a060c0302010e160815010303050315010912080a0809010e 73
    0xfa1021303040c443e412483c042441015000350014020001590300642d5642e40041d01030b10755410120303001d01038003400200301036800030403600c8401c4800060600103020b4513800e443e0740c00203905110341c41000d901008074a10590043d801801c00da035000611a000703004c000d040070f41c0c030f40c1c583c0d01c00c1070200100144254000703000c00c15580c00814000141c1c1300c040011b0715622032903003581d800038004184001c1d480c02440d45290664540d210385202d14080c0240c0342d880e8440c0d0380240c1c0105101801080750f1031320980f561503000e04080c000c100f04c0b949401600d490105814225490840b20300c580b03040b50710800a01c19a40c80800000b070250140e118005a20801cdc503014500c1000001d030b0b034840515100350005038040400c013082c0d5054120071018582c035140c06005904072481810305d00c0c501c601b02552400d04903501a580c541c11358541d0244d01d0300d0608030710325480c10410710301d1002c40c00550703004141b11388610403d00b6507920703c0120005071880344000c0c1078240591401820780c40c80c2c0d4001c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 370561097 1250 370559847 370559851
    0x90b0105041a1017010909020603131401090606060e0f03280c1206060e040213180206210f0c070b1b030702010b010813150203090a02090c120c04030308 67
    0x484021800e91000560308003080c1070000b08a500294100740d0920454100c5440803d003000d0076200c0049030f8a40ca84038080d10b120b03000080d04000100001070b005c3d140720044055242c407560303450103010303400300c5418250b48180d0801c0d159580d0b0fa540810000390403060384150380c0340c00c0d251b8080c114650000603498840c54982e20709440180141031a003000c012980d4036030160f001c1c40d018150740d101e00d00e604200c002100c007103400078038081000c2406008140f825101d154000c066401009408030000c001e41300d000f507000082d41c08080910b00581da14809020a90444054455400d982c43d07400c1c00400806006841200c403080300348104000181c0441c0d00b819013003840110035450710402d800c010441c021942d040e0410104c01d000e01c466040d00000080b95099071781d400251100b40010100015000c00100791403144821160080d0554028641c060107220994850b4507043c3c0200d10b0040c02181c000c502084000390105142c601040c5194010000160355407c1070b040d40d03800380c042540 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 370562347 1250 370561097 370561099
    0x819050606040f15140114070b16090b04121502030405100b0a0e01030f0c081209011404030f0b010801150617100308040b040e060303070201140a0203091c05060a090b0105 75
    0x20f500320528014400e812204010900000c0f498401d80c5e04d407005801da205404003e0b000074a46000d406065000a06803181103801010040301a106d0801244460307040103001824000e15140001c3d036406824040e00c01040254005028803e0904d400e001e08100b06e000c440703450744107009120101c3c1c000505110340e08003030b40e4002000801900010034581c0143e214051407480e0400100c104070100480403400d40c0b1950881000c20307182c0c0401078440b14190080101010188014038481d8840c0447c0400b05a00307000c0140340030340303c3d1101c40030706403011000d643c1c9420400041042500034800c0c02512440c003412459800e003030645c001c0c1b03404808544442040010004900410113568860009507440701245642d141d071204200915000351080003581000c0c500025039500f0301008407000c40e94140d440d040e1032a48104440080d03080700170540c0c21403006001d48601070312040060114600a2680145400320f02c1c0f03481c1d40343c807030020607035407920341031462610004421400032815544 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 370563597 1250 370562347 370562351
    0x1b0a0807051017012c220c080106090203091603120e030c031506042003011e0b0313021018090b032112070c030503161103070606081905060604 63
    0x482040215240041003148801010f0310000000e5001c90440c40d0b017511100799488500044c011620f035665440341180ca031410035003c0c04480761080224010120703500e21500c40c7c40b008940380c005803030848041d5000300140550020910201907800c11409200c0340c2c2d2100003406403804c0d90765021084403450315180c1484801100301c803466405000c02c052000001e01194045142054640341c0000d00740c0d1080d010b2840c0c40e901c3c114000c101c401ca0030101d10400d5003640740d646090b44450080c4104040c9218940001c0c0c40418450820710082d4000c5a10348003440d080c607602e004020300f2000c0030850340248440302020002078000d20001e40300b211000100007510b0b100744030100f42494641140040300842d140e070144100e4180f00d0290554422010341700446a03901391050b5983c161880b00030300420b070180001000440c0c05400814001c100c0d1804d1402914450689481c41d0410311080398402e0300d40d0000e115810080203205070194074450001c1d00880c0c10b8403400d44980740035000c640919 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 370564847 1250 370563597 370563619
    0x41a01060914060d02160326221205040f0b090d06200a0c0506070201140a0504030306030c06031e1e050c04030813140301022107110d021b0a080705 65
    0x10fa1407000ba5050003c00b0071003035503035052400d0790440304a0003e000b180403a495001c850110b102c1491481c2086501001490440d04c580f0418a180c0c1c0501000c2e10485101c03841e02400503034805008180d9003416210030362120304150447c603050000b40c01081080209200310f110790f41c1d5014800c000d0581005001504510a68004140007503001c2c2a8460400001e1480d183c01e500040e4118181d0003613040e150292104801242030b01d4005070000d07182202c00000c40e40b4100d55a001c2e03030300948241000546c055481e41d80c0c0d05140f041e0b40c0900042036a40341038107402c090742e0307800340d0b026085403100300702c808407443c0c40c4030030500e02c850000c26041c2d8602c0082d0420304200c0848000c0c40e00842103684620307002c56082c441441c030703001d000503000382c40480743c00798101402034905841c0f00c041e00d040c0c10900700780001401080100074000b0402c2c03440f03606200300380a02000d071400009501800d665040200c042c88003a0300a2100c5000d00500001001802070201c0d034082910400c0302c00c8015030b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 370566097 1250 370564847 370564849
    0x105100b03070c080c07050a09020712050c030c06010611010507020a030504180608030301080313080303190203060609040f0204050102010b0f0a0b28050307030c05091012090f0b041a01060914 84
    0x46000c01c500512180300005c01211800c2d0020b03004044490840307044150f56260403c000903402580e00080003030580c40100e80d00c2d503000e80060503444594001f01c0e4200451542c00c0c40c94114203900107004111404030000b41d0010030302446503c000580001c2100700c0e143da0300200140b18500c141242c130b02114651054564803500042d00a048240880380c803541c50703d0341c1580326440b00d1084402c602d449407000070b8058000c01524403400c600c5100010001c03089050708040c0d80003c1046610940c10011406035940d28407505800440e0000c1c0161210b0030000060308441c4000205031007417061401211300c642d281c1000d08182c2d005004174689070f0000c0c0c81c1020707044182d10070310f43c00c960106004034117056000e80914411407496805011401000c070094605200d00c0b00200e030000d060005084255000345092242e185103100001600e07a01500e940f5100c18454000304d505002c3d4401744024401000c031030050030301c265480300c0203d516080c0054840105441030150148806a06001c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 370567347 1250 370566097 370566107
    0x31602040209011808060a051e04081b010504030c020a0504111602010c02032b0f020d0804150603051c020606030307140a06060905060a0803160605100f0b0703020f0105100b0307 78
    0x1074184c1000c00c0e4000364a030702a04d9251302048070124501d925080c0041c2c00901b031a011000344102c80100020319031140e03150030500b50f1012402202e0240402002500c4150074403400384100e00a035207045407880c940c81000021002c65004510460425a4610203124000708480741050134010107400c0c2e2400c0e00c01601d080c1800308000e07600d0f004034081200d103408501004200c038650019041318114140005813041c01240c80740c00c0c0141d0000515480c80d40c0107520b019001030007096000140d0400c1080c00c1c064600075041255503400c43c0542030034420420860020b629054005000240303881c0000c01e03564028040c003e80280810f0345c50b041100e40c103010150304940c1040042c01050740320003050b0041e14050b60510700030610610001903005000c0705a50038803445050b811281101500c43c0d002404000e400d0f0784602d01c403902d0001d6006d8008a212005003a4503d03e2500d0f03041da81006070405030304500c0c0030320076410007081010030f00502846409550032224910b0f100d88401d24200d030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 370568597 1250 370567347 370567367
    0xf1d0409050a060b0d1110140301120506010b092d0303030f01150e130e010f090c0513020c120315030f061503012a1b0303050103031103160204020901 66
    0xa041460486050144a00807801d09072850103070400740119200c003400d01000c07150144018103407080c02c01065025151205c0c0209150b03113a0319181404048984203911240d00a0388503140300090b513441d20b405c12005121071401008406862070600100700c0c0842c20382c2c500500e40e0303410462141d84004840c03091214a880d80710010382161303140e00c2c00c005200c0c4120400c0c06410a0b551140b90540ba90760f1188003100039426020744880d44503020b0040640180c010200c0780b2415549030280040341000610078040294010710291081c5d5140c030040c002590580b01c0c0c08400e181c0100302c910040c800000b01e0136280d000068045a40c0e550300c0ca074210040ca201141280d041c0202122204100d40014805004109000c5840180c0c090a8101400c0320000c208015010040101242c0829600082700d01829102d04040f00b0140440c13090005214030b042e000c0340483e40d80d01c0107006266010f0050002400c050300210300e08000c0852003a0480c0c0180c400a12841d0002903211081e4800e440c150 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 370569847 1250 370568597 370568599
    0x60f1401020f070e0f180a060b04060302120721080403030c020411031e010602011521020d120e01052704150b090312120f250f02010605060a0f1d 64
    0x20f50582d465801034091400c040d142111500302281c00305000c450003038182202091200020034540340540c5e10000540791110105500c140e4800c000030150321030041d66103a00002074040d025050503d91408099890403028000010011a00e1000507298a040300c0c103a03070705400e054201549510000c0d020300300c502108001000c000c07052014400180484070022840120361851580c2c0f2440103d003254000080e6507014200d904040110f40c18176014040d0a81c0e004c2e8035114450003e40101d034038070b00c400c84204c4081e442d500084402c1035102d500c2e408115801d203805440e2284807070038801e50720a001d0103d01d40500060740355945588039031140c1c002d0020b03000c02c00e40495035455515165040340710a81d0090240c5000102130300301c1281214900c032461f20f4010302c02d8031880651002020010201c1034006110599040c138104596040301003c03405603150f0380c210480c10002800c0d138015a11150040038280410240250851080d16009400d49421090749154072040c89080882101071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 370571097 1250 370569847 370569853
    0x2e020403030f030c02061003021210110d0b09040f03050d0e010c120b09040803131103030415121406010e01050d09060b09150319050c04051018060f1401020f 69
    0x3040540004012200c49a103441c1040755034401041641c5800701294900c03503040300000184018075110100010400d00d660484444010303050b1600304841c0c9608118003000f1020645c9615910302d0300a11000000c2503403140c4131030801c0d13901c121900415900003414801c010980403d82e1400b540024292511040240501c1c03070807000103800b007245840841c1c2d4079814240080841c0c107000c4c0020780110703403140c801855540d50020103494181e03541000c90307080c0712003c041d852568042000d4005400154001d841000c07500101801d40c007070718282031440c40e0500c250041d00f0740d0328200c4140d0004080c2000541c101130000120341d148198a030280b2080d14120340307001801125407290034114000d95464102d5210911f8111844603181041581a03200c1e07400d101c0900c108807880c0726214440d80880d000c074a0108001002c1d20070032600c0004100c1d036a5010000300040e51074880090f21442001c00c102d90a00c000300311005424000c03441d0040300980100d140d03074402c0245211984100b403c4d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 370572347 1250 370571097 370571099
    0x80706050a0c141f200d0c12060b12060103090b0622050a050a0606020f07050d02040b0d0b09010b190e0603120408010b01020d0912150b10020f070e0403022e0204 71
    0x604c9040289a0190412907440d000e0344251912010fa20740300600c914400613400d010903d4001e60282903801003060030071001240454121420b0b01500700a01891500b658854820840c00b8580c0740000300954101810b194803140403039210301c44260000c000b80c1e54095003e403101c40c12540c1540600c80051142e18080411070b100b0001e9110314003e030310380a01801103c0e82c0c3d0388226a1040342d00034001d007641280c00c00708044e00c0c00e02052003106d0b2001d040420110b0b098800640c1c544850101a680141c0d0502005942c880070b2060b00204481107840e8960800e20840e40c1641c2c01c1d9070701407510030380a100081402035404100340080003031089403507a903c0d138035810414068903290400501501c25041c152480d51f0051810340b043d00d14400000c1440000c6450300382c802d40c5600d81407200c8990b142624180c075141c00d40c021410300015002445103c50448080d403402505030310801c00b401d424018031001a03404201d0344000202560521980040030020854041c0382c020030001c5a440068 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 370573597 1250 370572347 370572373
    0x2090a2d1b0905060409050a09080c030309250b0c0f061819080d0c0309060608070632030a063b07210e03030a0203060a080706050a0c14 60
    0x80689000c0d081e03591a5081d40140140c03042d149902560f0380c0054107000600183c4080d0344000c2d8448107041c80840c000c98907466104450340404490f103425000001080b8007034004001056116040e2200b1911086240a040480e10480c0c0110b40d4225400205014410f408204559000108106460f01c41c2041d00c081440300048107041c24550103080003103185002c8102854070300329000340d00a071411003d203807540010321850b8181c0b8103041c4d41c0ea2a002c0428880e01c5420050b0503a81300070406a41070a1014118001499031000000030050411030f0103c42001140c400302440d0f21a01c0d200e4588070b0700072018040d2030f04400800210310800a0b817008411803180100f200e540c800f540d100804000300100303c00111244004030f118445002d0750001410300306e0012124240001550303420b400c0e006804c1d540290f07040304400d038000c400e00000d46030200c001c600821180303006107165403a00742c01a22600480d859002880005850398040c40f0846404074a090181d4003940c00e00c0301454 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 370574847 1250 370573597 370573601
    0x14090a020a06030903050702040c110105070908070504020408210d02070c05090c07240e03042606040323090301090b0403021c0509040e070e0103050106030312050402090a2d 76
    0x20180d1142140c1a07000a8050103032044150340ca8156803500d1900b055502404041c003c0702c1100010400099030812440000b07100e03050040ca4a55561148030307243c00560303032a007400c580000b84114030402c010080b4a800290340d41c011035000150b000780d120f54520301d40f20b43c003443c1209200c0600005003d020000f15800c0001560811500a14103031612480032005000710000141036540360085007034103020040c203004801c23003d071102007111944407441c0c07415a0402d5200724050070640740780850054000601c40310100051008161a28244d04c8c010440281780a400c605900c115102100d40c50801c41100c100200140090040c0002da10780000f40d0002150140c0050103038808003110461441050598405039a0b240d9003041220700410000f0090010411041d00c14600001030f04204027000500031409000000f40d280d01c0c40c02d01031309010444d046086a00e1801c0204001070b0340384452950024000800011010344100b07070801075045040b85000207000414503118010007e07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 370576097 1250 370574847 370574863
    0x130c050f0d09060c030b061b010f020c060402030d03020c03031f030605010b1c050702030f0c1606020601080d02010b0105042115020421050613060b0a0603061410021f1409 75
    0x514000c04c41d0102c840421021a010240350700d07807080b410042d906010038010000304410b40c0c3c42000154030300300507061104130f9019466408444e00070500b00019858140120001c0c450303036050a52400c074807130301e0392600c9220040c040c00025001c06090500d016045d04400302551b8003000820195071100d0065405403c285400d8480b5a00d0115044041040b03000740c0d4001c0c12150000c50402e25058900b40554201d8800c00110344920100045050301c0d040b100070081000e42c010b409954108010b0700d08105440004400390380c1445030044980e41c0c03280884040701c020120386010b00d00d000700181084018100301610340a00030800802405031540200109d905030100c20303140c0004030340c045102800644024045411110005200130104141c0d981c00520985c00011034905d1240000d418641e16040040000e5a41d40c0c14016112049500f2402080854035691016559a0001d5590184d607442c0d06400040c007060041c1220b458000707403a03490740ca500c914150300e401d4180d19629800c07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 370577347 1250 370576097 370576103
    0x7050406110a0611030a0e0a0c05010c02041814121603080702031b062403070b030c1b150a05060f12010b06030a0c081605030609102606010f05130c050f0d09 69
    0xb407e1340315100804002007100750560b1025400711420b01d4200151190f41500000782d030029210b00800c2c031403419000d1010341c01882024900d42800441034a6460112805080920b51100f00290002c42c807062604c10040c541c5071a02070b030642d4941608038118010000f000c0610100110308602d01f01012888601c00d241c11166560141b03058000905007000601c006500f58001c01e03024094440d190b001161b20640310440d040c43c049000000302c2940d039900c000144590024000541c054190f040c060760810002d075030502250511200003021520007242051007000e0a0303ca004c0000000c0d08044000d80380105030686901e8022501000381038120303d5a000503852000060141e116144940c21400301959654150740d1a0018440d0016003d064041007148a403c000380c603000001c2d00404a81c03617446c0403440501c0440d141481e201d010f130003041c42c802c07041c1c20a004039195044c451020300940100410a60103144081d10389128943d8440b005c4500002c401104041540211029500c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 370578597 1250 370577347 370577351
    0x21201050720120409020901053606030f0613200408071e06110709110c010617100209120d050c07080c0a0320040e210307050406110a0611030a 63
    0x20b032146020b922500303000e0000d4010303c014402406000101da002e410801c0c01030400d0351500b504030fa030f100d41c0d00481e003201030102009240700c1c2e88646402128240d0060f000d440c0c460a40c2411000c010801c10010b18440c001c0301c00384510076550025400c81104c1d250f402403840c60302d400e15846000300b0361281c064060310340709a41d00001e00b071105c0d0541c8060802540b4180d034240e81081c2044504034004540f030b0310b052252301e4011603222110302c00c0281910b954011190351f00101700e041030a41e81c1d2a80b21501e08041c007000040407142c0071910321400c40803418011307034541f050300c006030f00300d20041780030170f807074800c1c0700346045803a030418002d001900100003100ca05c140d444149941e102c031014600b41d0840a0060204002106900c51455103005242d5081c80750340c680020500300c803129400382801da48461040030020396000c07200300c00c001001d2900c13403552400c1d18010b0214804d070f2081000b04014024586044103051004015845e8060018480407889c1d04103040c050300f00f80c8401180074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 370579847 1250 370578597 370578647
    0x10050a110609060105210111090f0108010b040b0d060b030f1f12030c05030c0f070609080313050d230a031115011503060305030706020301031a0c0d02070212010507 72
    0x9000003986845158440c00a128503800c04050003505043d0360001c1b206178540840780c10602c1400e0192294629244d4490764480c1c04c3c3da81001300b480c101c0c0702041e041c040640014042500c0341000c8800303646119600960b40e1030942c1e41e940040086901920415401005005900c0c0609406034000c03540004090401014003481000c00d081e544070740100c0300182c04035040000c1c0500c29500002d401031060780e0902240e000381c1d60a1280b60380645503190460041403002a4003c40c502c0d0141000100560420170780380c0003410702c05003c0c00740c2d80c8074807400d509403010000000c1000d24a6100252a06182c10b00c0f02c3d200e0b9910280038030b0840208155002300780140c400091007096800889002030110b92070b014018400c064401c01c1035040503180c0d400400820410801003100c40e10403440160b40358954102154060500c0060032400c11481c001d000c055102c0744191140709002030401644d030005ca00c00100c010b03003040d03002300d51035081c01c0422445982100700800303840805400c1080301 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 370581097 1250 370579847 370579877
    0xa0b0303030c04150507050a030f0f030c05090d061b03060e010603020c0c010e120d170a1e050c04120f0c09020310060305090304030c24030603110d06060510050a 71
    0x2400115040d194500081c84104140c2981c0304050b14a04e146042c003a1504006031151070404520f03003410f40c04140301c412000c0b84140d114094081d0b1b1001442e08004601004400402d0361007011a0785119210740d00a0006100301a400b4440c08100044036102a1602c000050094030091040842030b8540c000000380c03c5000703008403202a119140a0111401e2000040d0b41031b003080529190052560f040044198030204078001882c24981c8400d079150103414902090a000107240950b0141001c000c81c020802d80341ca500580c40b04c0302c2022440703584581025445008981c000e01031109080c500909000d101051160220700039030b100625507845800c0d031070071392105840400c1c07401520340d810440c591080c2c1c49140c00070301480c240d23464280d99803142d20090020f03401c10b40b18212401c8000361b22614954070703107003a0002c42c2810b0004030301c0c58454145140c0040c8802c0c1c018007283c0318001c200443ca034000e4000c0c050040101d07104001e003460007450742c4c002e85022004181c4400c0c882c041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 370582347 1250 370581097 370581103
    0xd0c0b2d1501080114120c0307060e03010f0b06040b03180604030c0311010c05090402070203031c020c0d0206061503071b0b07031802090402010c03020a0f110f100e0405130501140a0b03 81
    0x1a1181098110115617844082c444250303040c0c0c1800c41359004402445e80d165900b4032000c0f00800659403110b040c8501e0200305421604000900003840d458075030b03c40c3c102d80303400c02036808561080d52480d883c0d50320700c2008442040e5101500700d0502648041201309508140c0c0782c41e00901940c0c514510814803400700b42220403075030305030011907800d0005100314030b00380c0c0003420f07110f1001e02034a0800845480b0364070390318401b0856890091f00418450800700c810800c180302036480348010301080c1080030100d555429025240140680000000b6142d680214035601510024290030040d00699040c446510501a01c503440041c0c2015010001481c561500180c200e0700246100140d844e198010748401000b42000c400f0f50244041030008225000341180003a4094840406040c5400d010498428050f00b102403003040d1581001508591211030440400e0003610006200c4e20360b11260f4030100d01c028402000e41d03003030640306101c058140d41c805d4014156041c0c140441c421003410551 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 370583597 1250 370582347 370582349
    0x417030306031c020a020432010e04060506040902060a02060106140721030603020a0305030702030c090f0703090309090e28050d180308030708090c030d0c0b2d15010801 74
    0x340c107600441c08004019114002d03c81e0a00c00e80c011149601072560214042d43e05001008005000908668440301c0f008081d0580c100b01c0c4032500c0d1403d604098061000706000341c005440140d84000140451f11164014044242c0080416403281404800255101002d015540001e80d10160864080411074241c030800346d4850b180407254a008050380b60003924140313110040540b5008000056110007a03c03401550103800a5580c03042c2d03c0c01031604c6c02d003102803c02e0080010200b0410790910409025030480c01a02e40842c0c000e445040c100c5c0c0130345aa4016080c407a00d4002881940380d00003544100300007141c2010f4841098a0485c000c0b81a405200a041a0040300f10100c00a2243c21203420982c43c40340440001d030f1303c136102c07400681c10840d81200443c2d11442801405603040201d81c109040840c020304200706455402496001403200080c0b1a2040c0c04c08644036481c0c040c80e807200036501c041c00c00182d842c64034078460b182e502912181990020202d070702405521480c14a8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 370584847 1250 370583597 370583599
    0xd0c020c031c05071b18060501020304060909050403111014060303031b0d1b1710030206040b0a05190206070f02060c1603050d050109150e160c08040f0602030417030306 74
    0x8850700b260400680d40303903100040c00c841e081d05144006904c0300c0c01d005560060620b03a1141c4061280c006100c0c001c807000342e0492419580b00b4003080240c164400c1054080c1e84c5190b1010519440710310701601c01d00352031b21a101040c041d080098404101c180c0c003000042010540c0b05406843d07880a040e12444180d85d004210825900000080c48180c0700404000755041000501400c0d5403002d96aa00c640c141c1c02030001d14a185d1048542d1040324503650001810441d0500191442e80061230601c264842c40480385804030f03801c401140510155000c0c0300d06000c00d00e201d0300d6405002074803041d0441d0300034045008180c4400c8110f20008000c0d1085260f280b1807490b1044510700c00143e403c034040218104007007040701072034024190080500800c55900041a080d55401c82c090f1400b413941c200c0f25500030300b602002820402c1d8a02803560001504000c4000750080c10300321924403682d00404108106108000762041d80040140112104807150491841000d41d029032280700580b074003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 370586097 1250 370584847 370584883
    0x6030108061303090e0c03010905010801021306030c05090a030f02180f0a11090607050d0206070e0303032418010305061501020d0e012a060605010504030f03030509010b060d0c020c03 80
    0x942000d030050320306007054060700704150155650104e240c04c005c0115450341320180040010000e840310b0340141409080c04100075401c200003c1e440caa40450140300714010035032610381525000780500102c407801c3c0303009025884aa6200e0074845503141d20783da0308034000c80044130000d100c441a882864001d101c4462041c00944454074440090503643e5a1419068000c01100340c0c555210b8006003400c51050740605032420041102a051400c0102240180710789a46180700340d96000c02141e600400020742a00c0351070080f1000d000b16000000301035000260302d921820712007202e08143e41243d110700201d071000d0b40c0d00400020158814800140135034040020701070178500a2998604003207040c9401120402d81d644064046036042910b030000404076042082400070502132180606070070b0030000e24043c510b0740c034940d201c40209006020180d4603008206202c400390046400544010107054660422112401c01441200756880261050f51980000c50401155103001d0042502103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 370587347 1250 370586097 370586101
    0xf0405010501091a191707080601051b0f01020403030503100b09090c09040912031524110a0803010315150302010206060609122e0b030a060218040501170c0603010806 73
    0x404d405152004642c0d503420140002c01d0042401045405801010b40e10300f80000c0204a0221144002608580402001c2020002d80366044000c0b22003038022424100c8626072a6650903042008802c5815015400054004103141d80480a5800b94901d40a0541c0103a941c10600d0f480d8465400c05079082500d61000683e04040d07040070345100400035001080c201c0f856644c5100d1003001c1100c0c030010079913500817140302c41600c00341440605414500c1a0441003a0560281c0c1c0628021501e400c10410341a036110816044c4146140181d0203c8015101d507100e00e00032a0054000800c1e001680c50302100c8003184140044140c1161b030107070003506c440e441d00c07410b1140c0c9500034040c05821888458629000313010800c41c08150082c1e042c0c0e1040c04031426042c0c0c2c0381e0000e080e1013404901e41055100d003800d51300487c184c04050b511950059990082c100d000c025070a105a24903401840d10000141c2c100c140b524603400c0ca0001015101441d07101010007056010a000c1c2c864030b6480702c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 370588597 1250 370587347 370587359
    0x3020610061b06380d02131107050d051207172e0e0403020d020f1504240b03010b01110a080906040803031f0e0601230f0a0e0f040501050109 62
    0x905400c00c14003c10000c60001c1c0d0080140e20f194032204002024080103210540000e2070009401038041d10450700410b4001042e00026403842d0541a014003180e80d441c07e40c1000144079003140c1a03154050240c60400d1040b45000e0150781005404400983c40d200c00921441d101d64800d12010600840700a603540301e400030f02e00e5404071081d1091440300114101c07030307019041201c040010217204009801d40d1a207450024213154510a183c02954000c04480c03d00302c2010419030b42000c1e10b01e400d540c01c0c0d601c600f03154030044490445041c08200780c0300c0102c06401150031110980205400038481e42864100454038144000c000e0030054101c0c1c8103880008038180000c00d2808001029941440e03110301c42c090555105560403184007032a00c0030520b40f10601c0c010078000704084200c01515140000001c0c22400c160900c804c81e0703c2e1980c610203012414102a50000000c1d03841423510340c00b407148081c000c0358580b50b20900c03600085290941c00d10f004e004041c162041a074624001500d042 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 370589847 1250 370588597 370588637
    0x218090106020a1205041707330806060d051302180c160501090203070807030605090705150c2d10050c0703050f040e04081c05151912050a0302061006 66
    0x24036003000c0200802001a1000700001c480c80100007c40c054843d07a4500031114a0904402c004111b615011800305040603014a4100048640b03a04003d001c0d650b52400084c001d200b241c0161100d81c0c42c000a10000000c035508400c0c800b0b100b558030513400c60800c896840715480c12240740e17445034001c0004164055203080d00195941c03090780007061030009a80080d040603000e030881d00130b55001000c00c1045c00118010650003400b003602804210b8107041c00301b2003001d00143d1055050302d00241c0c400e810301003001644030141788251000b4060802c1d219400526008951282c11840341c10500740c99400c0da40709080c003c541d4040c00b81d01e0600d0a5500703540caa00f0030708904c50176045c1030000050b004c4e5042c0c10740307110b03500c61444241e0300c5d890884140b005080c98a60142d075140b80400b086940203190108141c07482c0221202074660040c0c4500b02030315161508110028038501085000b00080040c0038002a03200340c0954000d80c0c0d0310080e001c1c00c200c06206100c009a600c04d1401c070126414 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 370591097 1250 370589847 370589873
    0x414010e03062703030703023006062802061b030f0f0402030a05030f130b07030801350c0a15020d031104050d0f0510020412110d020904060218090106020a 68
    0x40380c0d01035040790743d540780303a0079600120b91800c0841e80015844400120144268251110060300502c43c03244240314034000540040c5141d0103004000740000030b080346500c2c0d2540007884108600e00c00124800000c0d16040c0036100d17181c0880c0b002d0440c645602d900c1c0d0a0302d00ca02c205010b04c07000c55840c20008155480050010303038060040802c1c14000c200180000c001613484814119503601c02d00c2400f102c2010f02d0ba0140d00040c130107014500000c0e5000e100a411a08400754146030148071351030402c010844042c0d50885810b1240d201c1e0010100856002603240f0116420300c8110f5698905a001940351081c00d40141c00120703075003080030b0080d80805890311110310480c0c00d10b920742000ca68001e401400030703100c651201d01050100503080084200e411230001c810340c1081e02d05600c1440c00b0000d414010309504100403442c0550712185100d890040d0020140308a03410300b41081d10080d4001c0c5030540707681a01c5030f001c2486007001100d003412240e141d801060103154545498401d8401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 370592347 1250 370591097 370591141
    0x5040b030c151902010603020117250509060a090e0901090209040609030c020d080309162102030309030105010b03011706130201030e1204060f08180a15200414010e0306 74
    0x83c48401c8806030a12002403c202494000103034881c15400090400c15001e03840d5100b04d00900308109400c044041c10404001c498070070201800c225503000d4807113006101065420050105480c010b4651002143c806c54140f1140d0200c80d8680c540c1290030b07580c400b240650400b8048d03010500103040d540c01a083c80340280b800c01c04c10242c1e58002080c1e5028000191950040032040c441111814403044c2202a20b418800f056285400b840a00e440315108240200d00c070b002204000759181401254070307040004000300045e40e150002049580c00a0003111041000c0c10300c0a008600c0000d0164060080944401c81c0d80364a03a004501409600c3c20704a90f90141070000200ea080141c0504098400c94880101e0300c480701300000c01c64200200085268440d0990302c0180c03040c0402e601e0711403a0810240040344401c13100c404c0c0035090324000044880054400007255140079400340042d00c002000c1060300c2912040112010710b00711b0303443d0f0b03031680010340456401d0380d400f0100760074402 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 370593597 1250 370592347 370592389
    0x527061c020f0d0603020913021c0203030d060807060906050405180405150a0e0c010c0f0206070c15020307020f0301142a070c060e060c0706030c0c0602070c0f05040b030c 75
    0x1101055106500a082c10110341034844e101481103140c0050b0903035000e501e4000e840403114a6400142c140c103402e40901c48034241c441e1171001551003e00031074441090400701846615501c150b040c1d6241414030440000505031000802c106100c0d8080750300321034009064944840c2c141080e1b03003038400c010703108458034400e00070081540c594460b210340c8540f49e2240d00280740080c05029a0409e01c184044904100d0340030b11a00005084c0400c0d440b0103130b010703901240c484005c0d28000d0010b26203a0005004108a0356032803400b141d00100800c10075200751000114205c0c584185401d07142d2403000520603046100004110785102c0c003520110240258151007070b03080700c0e640d113011580010810345140100503018050f0940040140340c23001303800e4448515104240107402d440c0e14a0b40a224209a01c0314640d6040078807581080d001e0540207041150354000900e0141501c1d0014402e42d0840d00c040c0c1c1c4005030360b02d040d2192601c114000703005040404010000c01420046400c07000503080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 370594847 1250 370593597 370593607
    0x90d020723130504050c010e0f130b060705150108010609060803070204240308030a0608030403030206150406270c020c0a1208040f03150f02031012150c0527061c02 72
    0x10000e0040c14040c42c0910050601c500d2180001421030080048103805070f0362103000c0c0c0600d500c800b82b80c100300c01d036003041c002014216040040c895215841001e1700710300c07880d4a03c08045440d0b01800381204c50b500001c002c0740d65140301c0c6a082d14068400d0261540040c0948400f504040d0031542d09004000c000c3c46603910721541940c0442010380054075030750004820411840540d115182c050076141c0d004600305803465074001c0d0b4900c001094200d032011004284403080d00c442d00144007038140c2c883d0180c104040d015240c0c03c3c40c00103a032006699410022101040c60000c1788603044800043c001c00c1c1e681b03040c6403540c601d40c004494200c0d1805010840041c0c0e840c08807201002440c82200152101c02c03d001101083c2d0300c0403c0c030642110701c100280b00c65000030368490f000300d400c1c41d06a812070040e00d04000d50302d116041140c000036030620f680040020f5004001303243e0080700d0309052840e40e0a480c02540800a5018545d801c40302c01c00c402d615502c21011a41c140c401d4011001d403501c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 370596097 1250 370594847 370594879
    0x121106101809150c0e040b060f0d20030601080f09071203020309101107080c0f092203090602010e071a0306060706111e07020d020913020a030b090d020723 68
    0x1103403480c682c0c11070060b980c1c4484c0d1030142e8000c3d0fa00086840031102400189403000006419120701e43d4407408074200080c8a01d080c0c0d0710340c2c009007400c0c0e06403200340400401c0e031580400254002c8039141d0025646100051030b1ba03460017803690003228181c006002d56401c06000e00d04600c6022410303001d6100a000e52070640d903800c1c0c2007420440e01c40d619000300e440d40c9428540f41c55901e0b04000340a070443c1070410282d884403041403032404404c4400c5081030b1110500c180a110040c07100d19841d6065100840070315401c4503251301151a198002c00076450b51069258440c009400b504e81c4034401850a14425144800615000b4400620940ca0120b580d5203c0046440b40c10910b014110040b5010a000311001040c030409004280d40c03924000d102d031300189607a00074280081c4a1018880400c00083c07011010060300e66016069800741038403400c08101c1e24404848100d114826451842c04180c408682c1d5411501040c22804c58205004004222810341590558200b40712200c05805 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 370597347 1250 370596097 370596113
    0x1107030203011b1404240306030501050f0f13020d061505030601080616140a030e07171006050114070b04020102210a08010f06050708071e121106101809 67
    0x2119080e90081e80242d070070011382164513004000700b5481060200300305001e00300f884031100007519481c103042c4001800d0190000c4c445900054060b610b003004006c4e800a040d0b83c4117004580501504400e42d40e042142c0c105038a5001e4002d402c01b951b480b2403800102c0756004504e000b00d14444c40025184c40e01c02282c50018242d0007100079034050382c240141031034000080310500c001450301c1401148111000541c070301c14482c14004140d5215031038280303803c0c10701803e4068000341010750101c3d50b00000301951281410781852080d0300e4280002103540c007030950144800e60424655080c0855074541d5602c0c040000c009a056004459440310300508000802d130017012601016610384e00c880000610014050f00704441c450403001c0184844e581100c2521003182d031048800380e50390980d180600700030246415010513800c901208804010707445518505000b46540d400d400d24202c200a10307500d450075903c03c0d02c155541070040c8151001c080100503024020701003c6240e21441c0d0340c0001c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 370598597 1250 370597347 370597361
    0x10c020301200d0b0102011a090703330905060f0910090f0603050105070905130c09050307060f02060c03160c112806050c060f040c0e040b0709090c080601110703020301 74
    0x14500100181c2d00f0140941d51080c2642e020007803000708000c00f07480e9030810140c0d964a8000d4403076049200043e4409100b504203101c0f111158010f410700c0f01e5501d01c3c2c80f403005d100700160041409000d038040741d4aa410b2080d1481160018102d030584c090441c1803185811018140c1301e4001108480800c02a90600440c490300d2540740000031814130794103000c2e007126000340016042020441d0100290342c0d407405000220841c0e20000a10205030b484252045038081d071145405010740440010364613005062408007207525000d40308140e65142450403d0b01c81210900905c0c5010314400c66428400c19040721003601c41d140c01d2034585400740000d9005000e00c3d4401c07122032009104209440c80c01c2c241c8000030860b6041490406480404940c0c41c0e11004004031071100e580301c0000c1c00d0001440d104802800c3e50342800c503503824241001c0c4800182281c40c0008941c03074400000300000e852152100403c01a0340b103240c1521181c0044410624100d0740101c2407190600100141e5800e00c5100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 370599847 1250 370598597 370598651
    0xb04030c0302090108011a0105161b150507083426070506010e15060a08011a0901050702190b040902091314040f0515090307020117060d02010c020301 66
    0x12120034075610400194030b105070090011070b41000366400c41c80311040000a25000d0909120340c0300c40c03208100343d0542503a400c01600118013050348902e441c0ca0050543c041e22103442000000a1144034240d516106206000340810420015002501002070301e84040711052607080154074412a03600c411300110300c0c0c081d0b41498116402000c1c0d20301c010940082c2c129441c0180c1d017080705c1a1210754540c04144520040c40714001d00141500702d42c51603205080c90010095500c4100b0b1020040c10030b0824042c1c160768980425000314019500410388140e013a0583d100e510303104440e400d100041c5402d41c440c180006e41c00c02e011660401c090003a10180800c10340040c3c4984480d010000d401d90f00020302c00c102e6140c0100f0b501a41e1034090f032181e005402103d081e10301d148500d000d6162490690f41c0070b442036003460a000940c0360100084c5221070003640c484c0c40d0b206007402074001c172801c15901e555200403102c0c2c81c0c40055028041074101980001c000041c020350402c071030304041022820380 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 370601097 1250 370599847 370599863
    0x120310050d1110092d1a0c060601090317160204061509050406080a0f050a020306101403010606020304051c05060c040314070f05010e040b220e010b1c0c0b0403 70
    0x1072905403c1c188491614900a4502000f9451030b20109410301d01c0c00c0c0340c2c0300b11500034078984180200940c00d00d40d402003c048104800c40c2034403240e546c0c0980c01010030356200f8000c5d280030841943c850a002010389422004288008500e0004001190320549e0309120413811915001c000da074661142d0b6004000c0036808120074080400014403103c40c54226600c507510382039081c00440300000d100003003d64000e0041e9645112420002c0c6001c004c014025807500c41c1034100052030050301000b20407507400d500140c940008001c00c15080c0d601c1802444c0060b0f10510040016190030320b0203c0061210075080422110076844031030811800b127411507480f2400080410401600b0281105805614006880201d0804203050700d4000b441c0b045904110150164002654595001d584403440007000c0d000340400b80010302d030020b480d504102c06218a0306511368041903040c0265019800000c2c00e400410080026100d1040d00c241002d40c2d2004c80101c0104170b480030f1400510280d8000c01103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 370602347 1250 370601097 370601123
    0x70c1208070f020303090a030c0f0b040606030605090a030807030b06040905010e07020f1903030b150d0f0f0e06040f0f0b0a0509100b1e040b0411131403120310050d 72
    0x2000c2c000090402c203034001c40d40100100305880e08042103020b0040d5061601900c030207001d050504905040c078001074072501900c07007400108106540610101d92240d2400c0c001a6034449065840c0d0502d070380064003150160300024212807080d80b0021100c040103011a00301503d6071500000c8403400d030420794a44e00c4807003d2021144e0100100b10140110074002d00380181d080312038105030030301c6020040616403038102d40030b9555210070f5800188030b525859a0744800c80240d0000c040c00d840040369000d03503d0001d080d41c010f04a0301915a020300c21100405154540c4d03905d0b0018031008840a94001210400c141d0002e090400c29038010302c00400c0120703260400c006020308180c8203107103146807980b40034000030564450b0103210400300c3c0d01d80c5c0300c414840314440120300a0308489100641c4140380c8000100c0c54807035503014044680c84500e00b4a5140d40341c2400c080401c0c6108480341e0300d980881c40341340c00c40c4c90400040d5071280050301706001855031100410022000f04004507011001181 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 370603597 1250 370602347 370602361
    0x20f12180d03060f0b04060909180210030504030314150105030a0f02031303110a030e040c11060106180e071b03030b180603011a01080105100201090c12171809070c1208 74
    0x1340c103000e85503064a0915091070088081e0049015201d0b006a050b256505410500c2d00400703116001c5070041e10401b840c07406503000070010501114100e01180ca441c082d000d040343c140b44034601c900c0c0c0640e050024406510015141070300000d06030ba100e203440700b668904000c2c43d4000380d4000c2800c4030100301c04006501d8003074802c1d0b1400e405a10b07154840321003000460760250107840324003815500000c0400325104212a070802540340f01c0c04512a0000000d150350707120080e07000d1410105140b414843d00c0c1e014a042c0b012049d5075103000510017640721842c0c00340da44040003060384a03040000c1d151aa1a01160480e006ea00c809039410b81c58004109084c1028002c0c2c181047c0d5230826102c080d4205030003e00744d06010b0207218010024007000036000e0b4000d510844000e42c002e100c5100d0581d40f00304d10f032414464040e08540752903c84c00e580c03501160000959161940044510800000070400d1010106008201c401048440b00c01100418030010012020603916901c004541c42c000c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 370604847 1250 370603597 370603619
    0xa0f0f0c06050a02070e180604080a03060603140f0c0c01060f05090601020309010c1e05062409011404090204020f0c01050f010501020a030c0f0507180204060f03020f12180d0306 78
    0x740c801428800100402100e0a502251000c2511252852540319445d24000442d41940b844c0700b6051601c506c8052100340151080500100000c84d9414000c850b21200201d040d02d45004201d0314004002010580c0340c18a40c0185d0760003083d00d82801e003000c610b00805400d460b45071740b10501003d1028424805030400d25841d82e4001d03802e0004600d0143e040380002d088104020b00600340c0c60288150454604040058100f055000800c540c510b041c1a80e0b050180782845290310003072240b4a800b42128100f54079110704a80070400c40c10f403501d03040001c3c04003030b007c2030308100d070f110781c0c01c210000c2e442105202400320750f6540d000010302d81c80c20116040d241401a000349055611201d0f0820010742d00c00001329a00354012118085c8480b613240c85031401c1082e400c500828005030001800740c44455001d00f00b02d5841e0341d15000c4203060f5070b006a08900c02d04a001589039004c00001c3c4004140f603503c20b401c0440080100010109500650704194440c0c03141c40009440c1e0004210301c103964 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 370606097 1250 370604847 370604849
    0x9040e030d051b071a150301061706090106081f0212010905060f0303090a0302041806110a0f090b0a031a030322171905150708071803170c0a0f0f0c 65
    0x10142c0c9469000d458031812001d000f4400a40310420000082001c0c1d21841b042c1d601d0700307010b0000e2103500c1d00d50518048180350340b1a03802039880307240005007106d0070500542040b40c1d40350025000c00800442d803210502c450310718103003800b0317020400c10308140c1c04110164000e084285001035907041840030400c0c124800ca59082c800d9105018001040d03440c0b21160003100d504440000c0c0d90000210010000301c0c0d4800050103192030100e500116030340d6100100111354aa6544102115601c14103a070490b4250050340c40d071000921460701e0a601035401100c224142035450412103101400007842c603400004c40040c1e00b0003d240d03510003680c2032032a0501400c0c508a9411243c454070402541d00e4055000d401030300950b05010400344103040c0311744d040702c0c605036995448034a0302041c0600340c0711041c0e0340d80d00002c3c10802c4011444c0c540c0c01c051000d581d8011092129509506000c030060741140090003814090310b000320300010b2207519464a940d1007282d036001079951324201128600d282d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 370607347 1250 370606097 370606141
    0x260c010e060405012703080a080c031e0a090b090c131e09020d080a051201060f0207090e1204031a01060c0317070c0f0b1f0e010b09040e030d05 63
    0x20203240d4003400d035a000103039802d8035001c0c40c010030040d821a00c0f215962210484003e01003901c0711010042c40400d00060162041e6603c82c554251039509070780080344000ca5807100c0403600c2441c0d00b4032010703428444c650000c3c0c1800c80850100241c0d12072114907001034880c2e011a500014029050307050240401410b00110801013200fa660320703021200400d010703489140840e13650041d000c00c41d500c3c0c0c8042402603402251264456050040280042c1e0000000805c21031000c3d00003c0e401d07100e20424004201154040c10711580790444580c003418044901e840140144030340034400c4442e600107400254014494014000708000c0c04090407841a0020400c0201741c5083d900800c3c0c000352002038000d40345141201d46e40e43e040084506082a001c024002c0d02c1d80c0b1640018400c1244038240607035985604040d0301c40360800c001d0801143da105141c1e94072485401000060b0380350003d40a244405440890166800f1140d1400c591100101042d066a41c0081c010341c000e851041c0c0c00b00f01c6c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 370608597 1250 370607347 370607357
    0xc110f0f031e0d0f21140717223002060103020414090303011701020706020f180102010e0c04050a1805030703030e210904090816060f020a050415020304260c01 70
    0x39140c0700040c86895102d10800d00540846040c942c030741e00c2c1b5030040c035044494000310015030074803100082010343c03025a01c1d0845036041c0041f94a8480320341c03c0c070f07203040c8689206284c8010301c0c0d5144404607002034070308148181c00b500380380e46503c01013584409561050f40509081d6040d80704005c210b03215034a0003030402401d0710812070100e800108490549401161403524159080c00f07035806071140c218011700441c00031480412800c1024090030300c070440b503040c2d00c0358080c10400480c00c0780c13422500c01c0d0184e40543c090700003900382507101030380084182101013078621503690000005d940300c110441d496070000840b00245a4184103400313404400358091704110b00a20310001c510656808001404034000a0810340b9994981c0904a030660150013039480d103041402030001112030b0b85003a50002c0c1840b580070001e00070f41c402c0b80c0f4940c9554a61702d080c50b00b414a1011030000601ca1403003503200800012403079584800d9200d00016900d00c02040c214000800e039420070740051400d0341802 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 370609847 1250 370608597 370608617
    0x41401030f03050d0e01020f0901020d08090c01050702120106080a0201110114010306050910050a0c09080304030206040905071205130c05010c0308150301060302150405100c110f0f031e0d 82
    0x107940016048074080d05441c015444508000011005122241c494a2a0761000940605002c000405060907440036001d965101000d4142500c07050411107481c0340940205c03a08403443d40c068009465602d00140180d018050703004c55107800c440e00c5410000c02c5500500c1d00004543c0d028080324003803143d120007802980700c0d101d400c406003601804004c03e01e90712500007461415040100c038181c98a500414090750620903485802800f2184e10140010800040031500c2c281c0001190708880d40644041d241074540481d4030b0040c000a4041c10400c0f02e02c1808040c42d85d60307401050b005800507581b90709040002c0c5410000c00c40e00c0d600c254140301da40b003107a101107034108800907400b003104101036401c8609500000c0c0180182c1d04000e510074151190340c100400d01f04068815254245c0748190400015070341030352041809a4020b01e03950b402c0840380c4007420445200c20ad500d001414010b840f80340540000d0400c11034050a903620204410000c54a140400c285000c0003185c2c14074145c44 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 370611097 1250 370609847 370609853
    0x803041719060b011b15060b0906160303060302211b0603193e03090a0f080403061e05070f120b030f0601030c061107051f14040b070204140103 63
    0x20425800c0042c003003a07514400107019034001e04104c030386220003c04c0702a004d05c41d45407441c903010f00002c02c40b00341ca01c1c0a01c0400c0190340c040032212040d0008041038240400c804030200c0006c81c0d40310440030151207500000043e2140c0c03224401c00401c504801c0d01940703032007030301500cad01140f00320281488200001080e10741d1140021a41c108181030b04640c403d07606110020094100104e00303240218500c0ac0c4e403044a11042f00740351014011f8020384442d6058090301c10320501090740c1202490704900d0119000413001c1d1100c00303140b84a84015400c060ba29103d00d0200c80d001aa00110750006074484130046410703114940c1e0040b89810104101082503800501c84002c09400700000365852511030100e940800504c0300140380c07034048884a42c1c60f0320303101506aa06104036408503140c3c42010b00f0284000c10240c040d07030405407003000c07901b00d001e00002c041d030b0700d81001000303020342c100d819044400f1070002070018191500046a88585502c144400c031940a04d400e401d0450a90040c000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 370612347 1250 370611097 370611133
    0x4091506090603051b040b0903190507050603070e030304170c04052520010204150906170a15030b01050f220b01110703120e01020607020d120204030501050108030417 73
    0x6072010b5140000303c1d9510340401c401800c038041404000c1d02070218002807010314400041c40014003e030242d13600304811340941d000c40341d05078000500640000e00140700301d04010b0080d65015100e40350041d4540d10600c0843e0550f8015000500d801152500000501804210107241c4140c1990300b0803107490311900c0780710181803a092810b40784812000000c0d003030744940d24007088400b008a8841c1000444582d040c000d40c001e1003181e42d20100d00c0c07408803465000314001c80481c0c1c1c103a1101b1400b000410b100c000030200082c01107001aa45002c3c1c40070070110046101d025500c217000380c10352541804104040044801c1c2d90603c41d041e582c4000a1880b144000c4040a80d120340d4041917220545005032a022600c00c50790034284143c600010230b2100306102040c040c4490f459060700196440012038840da0100c0750303d00564442031080c40018455807007011341c424007c1006040c140c03696100d07801d54100380d001070b038a9800860240254401652900f61100c0d07030342c0c018030002e4015822020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 370613597 1250 370612347 370612349
    0x708100605120610030f0213030c0b16380411030d0203090415050d060203160f17040c050406080105012105070b0310090903030e0f160315020c010c050409150609 71
    0x402056110484d4907002d009811007030100b95400300564440840300c3c0d1160044965100c20780b90381c2030b01d50b40054400c201004444503690000070f0101001d44075115014008140c40b0744508180c40d41c0d10980c041d044080b030000c3c0658440c00803c1140c1028280203030b41c0a0007005507482038210740740851415030004100c0f48030305010b4801288140030810901404200799010541019000000760200300c40b560055201e040401c0c0d8004024141d070034100e032030000b40d600300c40c0490f00c80e200000a040758810080c0d4014030034441e2042043c2c641000c541543c41651000303e2503911040140b10340030f814245200d21158045600c0d1000501d80c4403155107000c1441740d003a009500001158446100e92002000341501ca50180010744241c40c0c014010110001990254002c0f000c80d401e00f5903020604095402111407042c01c444d095854900350350701c2030101c2c21209a802c1000802465080c05080803013000354458507203940c43c0510700001d440a540c102c64036803102080a020031604140428 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 370614847 1250 370613597 370613599
    0xa17070c0201110c030d09080706090302011704060f0c050909060319080d0204030602070818042901051201032301090b070e030f1b120606060a051c0507081006051206 73
    0x50f080c80030b8020040c14010f101407200d426000310503650500c47e800c000d25000f10341d0030100b10b8803001e65690b411a03219485000090005510341d4030140700c10001855146c2040c098040015141401c1d482030046819002c090404560045000021480c3c01802650300001c15800780040c9201c01da00c3c101ca4840b0707504010000407011401141107101541a94055503200b0030440d9034032158180025907400083c1c0c1130040341c4c043c02c26046141080e0042d008520914001260100382c004102040d00c450010b40d141040814401c4800780c0d08840c842c20b00030360213210000b1040c0c0360059901c201c513900000304c905980c101b80415002848403c245540200d6524110410341c00440c0003034140107038090b0b42c81d12441488881d0030710503100b4001214503002190341c00c4021b07008a8685031078100441c1d10643c00310003803200c503400601502c010070604462914000710691150404003c46006072410070001e0349400030441480310280011001d04000e0401d81c3c203100041500c50f8030100001c0600d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 370616097 1250 370614847 370614857
    0x61b020a020616050a0803010b13061e05030702030904050f010626010302093d050102010c050405061605031b0c0a051f0908031b0706090806070e150d020a17070c0201 73
    0x90410700c0805e00c024212203510281003540c07965514408662500200c17081010b02c4809000003032a1400307015a407010291014000d01c5041b17080300259405c2c0c10040041049d400304001c503000c01d94403441002d10542d1001c070031101030b504041000f040c02000032117000c9422012440840100785050440f030440741e048032014071a546140c620003691921100c43c02540203406191015030100c500c40c54401c15018522503052a903a02c01282a6040c2101c1000401d000308420b110702d0038000c00130724607111403002c144030b0b24102d03588641c0345030700c40c0d0000035003484c3d48107280f00d403d841030041401c520411501114890f04000020701c5004001e0403d1200b110b0410030980036a0180000c0c0000740340c1101030b00e40b07032080d00130490380c8040e402e0f600f41054041c050b804103c00380105c0080007070311011402080302d0780c0d400c7c0041d2081c1d40c0460321782d0341c0948501400d0300d03101c0500d0002d21800100f0240036840b90502d40f00600342e9240408150301482401c410098602d81c41803848003401d80920304 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 370617347 1250 370616097 370616137
    0x306020a0504050409111e0a0b09210d03180206120601181203020606060304082a0106180e15070c0f12080709060f0807030e19061b020a0206 62
    0x1081d51507224952080b500f042c00e00c4c15803010301c40c0501d5030195a50b020b4940c04c103400a81c4640424040710740c03d00c542d0001500806000644c030010151a50407400740c021645140e28018030f509502844042e507190b548200c0294014940c94011442804200c0390f02c140c0d020099400100c45005030119002d800032031500242e000da1240618840789446d40a016481c643c4514a180380c0d03c401c0c100039405441000e0218201c0e050100481f8411504080001d0408410f0021005410099080d02c44840ca6452000c103440a00381724540c001d02d80094036442443c038510700b241c240c0c0c03d1034900c81d2084e045001b144980c0103400c41200c0c0d07c9079032840c164660102da860141c42081c0c1c00b142c00750034a03032103480072010707990001c0b40c1c18080c0301c141c0c5031401d40545d607117003c84407100340e000e942c4002103c050200398410f010341c11158140d40083e099541002c03410541c20342801e00d94001751081c548451081003000c01001d003500c03040405102411400300103401098107403084034483c00c003400341900 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 370618597 1250 370617347 370617367
    0x304060212040b240904020d03090308040b0301090e0f0c270a0f05130507151e030606120204050a14062109011d06130602090301060b120f10030602 65
    0x4101c9103003882600505505007801d007072000701c0d000212800c1d50700d40c0094012000f0031020300e215211030b0100410351150383c0d4a9070b090007011050060308a060101122001c00080ca48101900181c107a41070369948035031410510a00380ca065144d0b54203140c00c10320041c61001004207120f40742e044282d5290384060b5151180d09508000000b044a181008000344200a10346030403008549410400920094481c0d07000c100d0350703c60304c5200800b16449848100545170307000502094091180c02c01c410101181d5203044019010b120788200000d540340030500032a0f800084240d02048242000c500f05070a140100c0d80d40d81c003502407500140b0108544c101540d4440046600e8001481108a0014170003d481d4178651800c3e0303070801180d400d261042c6801c00c0020710600c0b1102440000300318a8072294010340c1c0d0345414074000e440950f000c0252100e03a807406d01840c8000d001041c4a01d1340d50669542c40d9034500380107010a080a890362051200d400c850306c0300e02e01aa13400240040c0d030f8005800c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 370619847 1250 370618597 370618601
    0xa06050a03120f1e08060906041503030806130614090a02030c040e2d01061713030e030f010c1821021012060902040503010b0103061a0c071a13060302031902030406 72
    0x107115130798240d00c2200d180c0145602c550900d01418042c0c0312410076449070340c100010b98414240342199035520701d204002180c821921184c0092014010540d0a01c00004820a48103150884001c0341c1e41c00c0c01995903420b100e481c80341d009a12880c21403d41c18620b42207041c5108030301c00c0e02c0c54400100d0101e02e040d5180030044219805055000300780002071001c415000e882441081e01251848810040780311360b407204107124040704008201150b40c1ca0744d0950300f10459202480c5c261046c08016070480c1401d215100580e61143c45050558280c0700398910b43d484140c01810901082e84a41826000d00e58501002598111201241c078584910115404030a010781e0302c0c000c1e4101030340018002c40c0d40e030061095a0b8180c009021903001040103409071049071103482c80b24215603000001016001000c0c4c040c00506605903512a0764682c542900c0d00030070071190b001e0324400181000da080f0245507001c0240924101941149420350b403840c40d50654045504a2070703000000501007003126 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 370621097 1250 370619847 370619867
    0x902032a281d0a06060c03080a02090a0b090f01110a0212030c070f050a05030a030e0918150a05090d080705030c04081b0906011704061a1005030a06050a03120f 70
    0x8148406015903a400c0900c0b0503480d00c280c400849206101150b800300c9240140010b98500740c41c0e000c00d440c0310b6078040341c01c0312000b40070780401a4203001d4084140ea0704242600140202001c00d034682d911642081000f82502221505000e070049012100b20004160484140e4044602080c01804000724504510400e000861240540030380420003500c0314214100391081a01e88100c1705072654149656019020390140114110f041030301034520700562105d80c004d031140281140701c180f9211355850a000342d4400c05c2e16003001c0c000c2000000e440e2045940c403e5401000381810001034101034810317200138096030b04000340080010740c01c1d0400421640104005022030341480300b030001c14100c0c500c1008016100f461008003003141e42d8450380131011441408074a120042d21542c4d1080000c046802e04c940407810440115112642c403005041c581480980f60f084c1d41c1d161681c06841103410541000c0d01c01e98925000340049a00040c40042401d050304107080c90303942004040e10b548001e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 370622347 1250 370621097 370621159
    0x130f080a0216090204030b130203030f0708070b090d12020c150906040506100501120e0c1009090f090f0f02041d0a0303060f0b1e07150902032a 63
    0x200042854803607900103942c0810480b00d2150140c815103030504807042e803186200113491601da840120310a41d0185048012032440242100e1910001940c8404030b50402103055034a01004181a410710410054041c1c1c07195080c0f018080d01c0c52102009401141070300f00f402c000079804100b84101c0c0304100024100f0500090b103010552410441c0560340d1a0225412540e40c0500300c0425040340d2540c0c038241c16120305844580000b516140b0f81c42c01030009014811051055010704400381c0c0f120030a4a103003d15596410701d2885c10098100c00b580c103c0c4c60340b01c030094a400c07e50380104242000d04c0d102c41d54031440108401000d130000502a00e001040300c1e11481140343c043c1a0341100081a0200b2803003a141802116501c1c1101007100d00c41d0300c20034044030790800a80e1307140d407051160301030800100c2c06058140b0b016611038261307a901d154005611150b440002005510b010001c40d00360480e46140900c0440c0c4480a04d07130311161207158a8040d400c11000ca201c0005080240514801 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 370623597 1250 370622347 370622363
    0xf030c090a030b04050d0c170c0709021305010f08010303090e060f090106050c010b090402090c030405210d060806061e01030902061204110a03080f0a09090c0f030605010302040e130f 80
    0x91030f402d0100710400159411a00d901c65400c0d031904c0c3c00c2c028030752407206981000320a0018030000310b0001d180e1b440f44002009501601c88081800c10081c4058082d44581581e46d0300e2450505001421008100e207107102880300517401040000d9010f0481810b54000d50a02c003070640b03030880416805110f01e11041d600c09a07a400109446500201400c05001000024803400d400c11050164102c001d560294011107400d0000318103403580d02c01140c04c54894811180391620308025207546510f1981d01c0f001907000010600c03c801098000e8501030050000548041d04210000440a54a0010a9003c0c5000d602d02c400700360301961290507680c0e000390070300796125405091410034450485045a07140b5000010401c20700f000d280d01c0c1c042d00c4c0e1010209207026000112181c140d000302081d04204100210040303a4400701380500505004603888140d0808801c00300542540e00d84d4004504152051200b0001c4030b80c100241a040a0301196004001c8d1040c1008070181482c8140600408 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 370624847 1250 370623597 370623599
    0xc0302030d030c091202030705060306061650030c030a0302030f0c03040201200c0a030609051005060d0308040f08120708010501020d0c02121c02031e0a02030f030c090a 74
    0x540641040c3c8030144182c1d600041c490310b4210000003c81c0c0301d940a501948501010300c03103070a20000a64000000400c0e032810400318140b5200d0b200341201c4211654102c10400b40c441d43d1501c601da065944000d081d21a1a2103100f02541c3c0c580048040310340c1e100340c09582e851061030180100d40e90041e038242503030394440401d03030043e010750300079918102d08494000001c2d240541001c00c0d20b0080f035050b0368422086507600580601c10184007482d07452401090044c240a568005c030804c02903104190104a803003003414a58209140c400c450400c2d1800e042c1001002e0b0350340ca030809031155140c200011755458500341b03c1c0ba080301c200c1c00201180c0300050301c049060072078004144501526641c0c40c50b0340c0c1e212001203031540c1f0705440354000314074900c2004005103400a48046c69000c50800c540c40c40c01c0321040304200724801412a005600001443e1511403000c24a0b034900c2c1d0f00320701c0d10515100c0e50f00307002960f174819000e0380134101a011011400f03041e103010441d16441c01c01030440380e035a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 370626097 1250 370624847 370624873
    0x3060a08011503140706020304170f0105010303080613060602031b010f0612020901120b0a09060912200601050306180703051b0a0603150501050d021204120206100e0a02070c030203 79
    0x150b07440c042941c10368400d0104a4813140001040070a03220307154003950801e890f00a583c150a02442ca0220382401200f03405803020234240305441c000d500940e24051141808400d2000902c00c5122040d199420074a050103607035000000c9410500342441c7c02c458044022450307500415820780011049810448000b8031103501c01c60035200c0030b00868400c00f450f60396190a06603486480401014030807883c000034142e511650045488070300403000810001210742c3c1e8104400c15180c01d00c1c01085c0c102408144a1303505229281489051100414465040000207a940c00006064800c985c01101c0c56640c5240c0520094005580c408100c42d80072036800c3d441c455400c26141d06a0180094800c00a82c85100c0d008503605407840980c810300a50402004541d994000540c8c0c411051b003c108020080314141480351140d07004648601d0202ea40c44002404c20002070400b180040c2c025000f44040508510140d40091103500c00607521052407038000b4844040340e2003e07500d400341d4400e80c481 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 370627347 1250 370626097 370626131
    0x15130b030618041112060907030f0c0302060d090c080304030b0408282c180403030b120f07050906060a0f12021c06170a0b04060f09080a02010c02060708040803060a0801 74
    0x1c01350494448203006402645036640c0c14085410b110a51300444080001c11422000151510300850b1108981e80d05c0e5004a0b66541c002c4107840701c0c1a0b6074110b820203200001e40c6040140074808040d62610b0f2441d1205580325002801c00360244c071000514016030b103030010140041c08181d46d20000d0113800c070000039020034a0442c003840e40d03112140c1880c654072110341103514095002000400716600600c003142071000c0050088051503039070300d8403041607035406092003840c9003e0001049641a40c40d1341e1410004198002409240034800780071003681c5d004240c4162b1100c40c42e2045d40c4615141086032022558848451200d20006800b0f00728a524001140b00141948040c01040d80e116250300c511603800e40600b6280d0064018030b0700141e02c00000940250190a001c2421062203d161086414002040b134083c2d0b0005541e1080540a0060078021615400901a0b0740b900d004c020305000350080000382040400000500c09943e4800094080d241d200c0080104004003000ca0340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 370628597 1250 370627347 370627373
    0x504060b0a08060306010506160303110c0714030307030c0f08120a05040201030e0c100e0102030409020a08060a0608090d030203091615120204030c150c05010905030915130b03061804 80
    0x1c00120000c00180d002c3c200007441504980300600b9851030281540d2010308100b810300411404c040d2a841454107a030002e1019054107080314003d04401443d01b00d104603078041c010395181c082d4009204d0000800e030800800c3d0040d03600068023840301c04092402180c68818200c41019081401c01400281c00e05540640c0c442c41c402e803010040f40003151501c95035a0406101d0b40c5c0c1c050402043d05810714031032030a10541c0c1a0600480b82426103501c940b40a070703009401a103001444020811200d4a46988802d004004500740000c041c1005407070300c0d03218a4003200600078150000007140c0322034420020300c1c0211991300180100a031302c6102e8250607034202521000051440c480e040e1491001d4801c40742140d5004180310326043c41c08008cc4031450600003c1e20031320201d0804400440c2007070007a5402180f01d2005903590360368200801c000014014441010003205110307101119070110000b8007642e01403c001920781e92964005103286c42c800950104035030f020000d1000b04640110200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 370629847 1250 370628597 370628617
    0xa03080d051506030910150e0a02070302010b010507030e01140f13050a080d1b020d0203060108060106140a02030a030f02090414040b090c0a150909020a020c030c03030301080a020f0301060504060b 86
    0x200341e000e10100f10450005030f0310302d01c107500100240b001ca98420ba01c841d0480c0111038203034003040d980d01c0e14507a9441088074002207103500010071204041e420b21401784052001d00700036042c00f001e0b4400600c0b15a070f410025041c0200a103e5800b0ba07500c01003518001032251080c943d03185c0c2c42d03090310301c050362640c0b1506002d101031807008182003401203030a11642c2155690086461809141104403d01020f42a600009154002c4002da1024000d5a0290260000904007945800002040c002c010f900d600d040d8001800458040c66021007180e1801086180103d070340204110003400074070420049a07802881c204288200034082c0d10202d220728000c010200990340c98030b5003140c48038040454036030301110084050020f00c9100e05d0440c00c0300c40e20310744001c059444d81c8400089a01001600025038005982ca107281c1c038042240e151a0072056002d141103515208009550304140c8000910954023541c0d80004c54a096020380010140100284400d07aa2102c81c0c803032a43c86902c0300d03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 370631097 1250 370629847 370629871
    0xa020f040b071203061514160b0408030106020c0102120d0b0307150210050a02040506040308160b1314070305070b0a02010209030a0b100f0303020c010f0c02030a0b270703030e0a03080d05 82
    0x11480e916490580c1c0c0b41001c1d1300c0e010160032051580305100d9200f200308100c544121070b2300d600442e014003200d41c416031260188036502c1d4104100039290411440707910b81103521500702d0306010020710701691400100e01101245140c14000002e003000201c0d0041180b01030103950030f030015580010300c4400600d01410811003600c0d000d034100700b80c0c8500d0140e40d0b0480020807003000061301800051003c00d4411500d105c24076916628001703910801e4600350a91000c1c0b48103002409202844525007081d0100105003281c95550b40a4843c40e05210309403040300d000c140301200600130340440d125008001c0c2070760b24003503680ca41040707190810b0382c0400b13041c80030100100d07007281000317402804e49404d0b4008000189004c00111560003e4036a12020044030083c0c020050724204102669140f1441f0320852914000303586804030003400142c1039546c1c48100280e02240380c007040f0301d800d81c0d4052400c0c68581110030007191002d051a40000d01080e000508113258000396403106010324030103564 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 370632347 1250 370631097 370631099
    0xc0d050304180b030d0f20010903030b03010506090106080c0c1e0c010c081e07080a030518011a0603040c0f0803040311060703020c21030d0f051e0a020f040b07120306 73
    0x40080f61280c00c45a901030303020042e0f4215080c060341a40300d070b107405850b10b243c401c400110589800c41c04000940e11607074403841880300300358160003400c0c07420006400801681c03404500040000740107220382400d11001e01c002c00c29a8880100710b03642107010100b11581e130a0000488444e01040c0304100c4c815014072084004507610a050401031a13400100c10313801c2940e5a0010710b09190050500c4682e04ca00b0043c1e2030002e40b01d407016181d110065280054285800295900920040d0742c5581999140c420060309040352204130140005080d522903880780e98500d046811144030743c010414207402284001015000003005006492007841c00c84450010301c0c0c00d00400e80030303c2c0c40040241e00807070b071541d02e9070070300c815482a040300c1c040040e01d6400050b0b40590842c1c1c85960341c16100340c0c0f2502d01d1028407050b400381d99000f000f0100015041100c081d8200e807140c0014140e0481c0a400061124a048201c0b0551b009880c001070384554031005464140c0c445a68010341e80003103070a01c08 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 370633597 1250 370632347 370632389
    0x10f02070c15081e2802030405160f090b040b0306010e1005030a0b0f130b0115080c09100c0809033306090705090d050102160b13031704050c0d050304 66
    0x10418050034101e070b49880c10503808420100c101c00001c02d80c8005c0702590b0003000c921001c40122041c544038101005a50313040508007a82423580902e0303001100c1c24820010030224000c1100c2d4421141a04800034540e5020000200544103070300c01d9540c14410f040010514680c0c8114486c0a4619014854882583c403c141078030703543c503c0e501a0001c101c0400182d6589695803055030300c840340c42603d000d8103c10b0b5a400640034400c0c1c0104038200c00c649010032100d9004202640c110200d1075069003012045400074024aa6041c03440003000790209a15007084101803d071120702400906880c8100c00040b03017582c500a1184a4030224808100c428048114048003940520400760031011581d680c0c41c401d464a50008000f550460140c00f5010f021441c2032010b00418242010011009180c0e03061034610500003420000110b40050301050009400c4002030320260611314200949036241d04250303061035580030070290040c58402000701080404802001580d5203d141c201c44510b02c58 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 370634847 1250 370633597 370633607
    0x10b03010f150c0609050a02100504140105040b180105120c030f0c0703092904080303010801110a0207050f13020307030e16060909022a01020403050105010b0f030414010f02070c15 79
    0x5078041d40070881e0903c0c5500030510a8100c0d11803580203400312001d40903036601145d244070403844540c00040000c50300748082c15801c20280d04048091074200d04041c180310029070b41780b040c040380d440b0108140c050346030164019001e070380303690002d09501c0c001840d00e194a018617900840d0f11458081681c1c0c0003480a81c0564180c51150307030559101c0c4800382c103200c0640611081c1c0aa600702c490341c948624404441c0c1d080050010b054113034017460f01c03549403404990a55507080032221000006101407041254005100c0048650484040005044003030110b200d802c030085448003010700000c10011a10f4142e00b042181841e00c2040300c00200c0c0605c03458605005a000d80000603050380720411001019402030680d08004140c011070400d90300c42c411038540000000883d099401040070000e20500380f244038010035008020f5480c011200d5080d801c103200007000141515048124007030320560940c40004480345e2448110350320a00390a100202c1c80c05446031820700b03130040ca81520154424 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 370636097 1250 370634847 370634879
    0x9050319030f060e180c1e18010806070305060409020603070f120c0c031412010e0108010507020309101d04180b0a090305271003020711090105150a02100203010b03010f 74
    0x1000d400b00f500c0d1a11410384c0e0400700d1703403180a141c0f07220703504414003196507500f5014104010803a51a00000c20358090003154651400302d0100284900700402401c0400704516a1002032464000b60681e22000050001c0c0202e0704040e40102000c400c00480b240c0014030001e000c101c503280c04034034168802034074081c0d821800c810300018000e5aa8000024020f1000c00070010f00d942c0d03100c5c203200f0303842c100b40c107024805d9100b0000d2140c0b40d001080124400c0c82002c0d049040d03031000c0d51a00c084039010500520540c4514803c10200e840c4c02000343c800000b201460501c010000d101e910002e200c034000d1201e440001340c8491509201103804d442041c45150001681a01c4050400300c554142c00b0011031100801001004411100200c56035500400c20b002011038134016106c01141c01d0408596042e258558040c081c42001802140e0700d941d54181d40c0303040215000d60b94a0744490890600503407240303080007140040000710703010701c1e904050740c1a225814500c0c5080c40e56005802000746071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 370637347 1250 370636097 370636109
    0x509130b030d050901050c0102071a090a0c05010503040321020306030111070b040611071a1015140c0f0703140111030112020d0204022101053f0109050319030f06 71
    0x4003500000c64180100c003c0c20134128141030003401d16201c2c1885500f039030700010041b07135240520059100d00d901d400c4100d03500111400020309803004030b070b6111444018140200e5040c0070300400020300309485495070713131000c402c48440905500360f0381d184000650030680345a44a5420085480602494001078440f481d4010503240450740716500d5081c000d25480020a03001441000390402241c0005211120300031411000c4141d4642850110345040c41c60300031030300c00c4403c8800840780c1c03503011005540351000b080046650301d0003101a54a8086401d00010483c01880c81c00014409030901080e000c50605000307201074181c52000a0051109006071b2601c035450700c0c82d5002606142d80031109072440070b00010700d0003031140501045501019411000c9401000050010381001c1c49214400c0700780701300f2000c145415144011840705440035090320515000e200c01d00d814000d400003240150804107580c1e1300c82d100850150340709a0030102d50086410903208003003184891117070b074003201c81d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 370638597 1250 370637347 370637353
    0x120a06060303080117101119020d1404061e030f0e03030a060e0f0103060c090f030f050d082202180c0408010e0304030c0b39060105040c05030609040c0b03070509130b03 74
    0x10200e02c21000b01a01d603010387e100d02e011311100301c00800460152508452035001085401c24500c0c0041030300290150314100741005010400116412a111102000300b2000d44c1d503513a102444202c0041c100146490315040c18818010b41c5914040000c50061001400c103000450b01c400d04000308581c20340318000f0b81e11180c80100041200f0f030380680c1400c8950f1400210540e9150002d82109130720703401c2580d0b0300154800c00c0040200400c96003001e101281885000391800c60482456240d9405c039402c003407840180707118110f42c1c800c1031204005c80c41807000030300da040448100c03a42d50018001c40c510b546c07800c61000e568040c0001541e00f101d512440300140d003428400d0b501c2e6a50060318000d02030441441000d8042c032105c500900312046280900d0ba14010f204516520f003500c10307070106004510305950041e490740c0c400c08a940c001025980c40140d03866514040e06640c90907030003490401c07404000c0c07080321a8800000e10480ca42183c0030340300c0f240c075100d10b0002c07100c4010718294154 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 370639847 1250 370638597 370638613
    0x40e0604020d03030f020307270e01060e0d0b0406050402030712080901210f0b010f050f07080901170712050117060a0b040e01090b10060908030a05030402120a06060303080117 77
    0xb2904410545031203109140116100460443d400f050b60000c0c3d80d0100400c00e155544074a400100c801c0c2e0402e80004500070141601d400410120041b06001c1d6004219092511401c00e8454842072010258030030a509501c0c038290a00d4001800c0030b40303080307209014095000415400c80f02010420390303008040359140201000043d20207841e6540111600c80195444160407045480307584a4454070007800f040b092031001c001003504030303a20760310700600000b0b00010100b52440c8054070140c0d5404420350340c2e21040c090040e15900da10080314214190113000b0003881a5100401c04035080740f00c0010f000a90302c544075001000702540340f10007160f220f04009081c1d081a50031900201c03201510014681c50005140c80c00c0d129248000e070348400300c0c582400040c00107002c0e8940144407a2a08104d0706040040e007503246e01c603010001c41008408030108003550368110802e0326011003402260302080c1d2501c0e0010150071640f0003a0081a104c40000403100440382600340101d0351700000d42041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 370641097 1250 370639847 370639849
    0x50a14090709080118060c05040b031807050d081903110a0804061d0a0b0109090c090f021308010912050c0c090408042d0501030218040c030e010f02040302040b040e060402 75
    0x158001c146504102000d040080d9410b07081c414404044c4002c988120203541501303044060304c0c4003411260400508200030488880c890042d250003401102180780d81d4814084514070b004200e40005a00140451040080066480050407543d19409a00c907501d441b03620164229032140d072141c50407003802c1050044080c8030324001030b44244111400190401c100302001c10000d1000041000303680301044550512446008175401440e0358141840707000450f039a20f00219845200300340201c0d4039403038410070341e0b10160103a900039603420343c4443c000d55903400c03143d019009100042d5120b1a40c00c0c0440482072041080303580c00e070785403c0204001c003c1841403011400c002042500d01100034000451030b84245012a10300107a5401c40e07041801541064803441c0040e9440241410310411540075001402a002204030004440000e4103c8600c5400e41c0036102c2c107400c00030366510346081d141068000c0e034080c1083c0c2e8020303141001181209014041103a0200c5242c4126500200c001401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 370642347 1250 370641097 370641109
    0x8010b04111b1e01150503190f05031603120e060709210503120601090b120c0a021903030501080c090f040b04150501030f2108060f030712081201050a14 67
    0x1444032240b0481d000400500d03602201040ea1200b85112a5140c4c3e251000c4803c60401c0c500182c00114090301089624480c01341803954110390007003108440e030b1308240910030300f03109503a0103060303081203126000b5031498014541420a0503c040fa58070b40081003644c00e4001170441c1c400c0721141c903541c1103141401000350b402401d2103201803021000c450418000b85051001d08080321320604885880c1c103041001516113a00e681214209180610450641096014a070b541091000c00c1483c1c2d40c0034084000ca0070044210410b80c05a1080380ca540c0030154182d001d07504995100050b18400e008420401a100c00151154291586000081000b1550071003915422910030b00101000001c006500426100264003e4510700300464480c1e052220081d00011050b0700c4e040e0350b000004030104040c2041401a26403400388070070461031240ba881c200301d0140a80302c10602484004001c0c030788080280d01070b85a80200d061103100005444c1000503401003691100741c1d40d4500000113006000c0703 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 370643597 1250 370642347 370642387
    0x20f0a03110102040801060b03431106071713080403060b030307020d0813050906060304060c27050a05010e060a05090d080d0902090c0a09060e0d0611030108010b0411 73
    0x41c155420800002d40000900c40d00004143c07003002c0c241c580ca0482d40c01c98244180641c01144a040950141d04080a46840400c118000401c2014510300c5c0d9008a070760056444915119102d0603040c420395580180c0181147c003450030f404d030f289544a641c81d4040c000040001032500078203000601c002011500004600d4401404072820b001d10b980001c5c0313407504600340681e41800d0000c4e000b030100205071030140142c0415a448140c2d4101400171800b03c0c03100400240440747c0e1100264405072154202070300d03e070034010803201c0803001da610b00d0000c503031607210f0548680013040300040d40394086d01c42900d04480081c109814039540c4441594554000010709600410941304180020b01940242030542840d510004000700701e8814411420006482c020704c0344803c0c00300154842e0f01400d0801500c2d002c0c80c16000c003070ba01030007244001502c204002d050508012032142440000740c05541258500002800300300c44240c140800c0703449054800d41080010000000100080c01880c9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 370644847 1250 370643597 370643627
    0xe07150302211617040c0e04060b030f24091c050c33010807051e0315060109061706150910050301050420030a05090307060905030d0606020f0a03 64
    0x284102d00900000a09008403244190b04101c0c810ba248070700e601020700510b4280714440c0d65440d0406032a00f25410303419125002c48010643d000408104264000040381c04010381102c0d5040610034501ea103a1103c01640c42003070b05c0450040340c4d01c0115022035030181c0800d60180ca40c184203580d80000c43c0280508650030300c5070070401f14030340c2c0f072042049102d1000b908401c118a5466000c001c60300e01e0f0700048411102d030144006014480010415104079441143e190a00c004400d4011650501010480d907050042c0140000021290160382e84140b000740e948500c29a101c02c5d080cdd03020607071080c0d803840007505140003841c05e00b0102210070364500106041420b12208000207000c411002c0c2000e00042c2c804401007240741818013445840c0c0803000909004003403028246140d902004080714101070b1200d0120340105400e008403816550881c406100c8013403070341800740e0350781e00280380800c0c40c40c903080000410900c08144904100c2c0001e029000010680d1402c40d4190103010800e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 370646097 1250 370644847 370644877
    0x10b01171324050f0609061320040801150e1027051e0c071104050a020f0d091203020301121119120203010e010e070b0715060303030506040e07150302 66
    0x1480c2d1419000e04031a00000c1003507010031249420010303c0250000a0301c041e004a035010240185940c0e009100e071340d802c6071a940050404e48181d6035080f50110482110080440084c001c00d0050040d040721407080c00301e2002c00807803542c0f82480550140221768209644240304018055600039a451403403480700d2003409001442490074240c1101d005442032101881c5c0c2070040c4206940c081142a8040d0380d034003103a401e0156030f0322030350704150b01c26440364402ca55580000702070003503640c141d821034080040e46940702c0d884801d03ca00204107580060700d1400d021000401018071a00031641070340c84c4800f0365001c48006640d10b19405009400300c40d070003440001822480281031085600619004400d07610815481c010705086500c41401d0510513410460400d10ba5003000520740210f4544200315541d940e010304107c120010943c1c118900e0504008001092507403542002c5c0c014101140c0c05c214807019101110b60b0b405081c07082d064a1020403c082d420b030340c02940504000c004507030788 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 370647347 1250 370646097 370646123
    0x60e0705041a04050603070c030806060412080d0e0102070804030606120f020105070201020f0105070c170a0f0c060b060a08041505190b04020c06011205100513060903031b11010b011713 81
    0x405d1034104540480016441d01c00070801d00d40d00c601c0064228005640051a2500341013621244a05000015001c281d000a130f109002040d580719040d5801028021901c800192a00c0c000644c4188030a45025081c000c011a180004000c10460103911a0311003100002030360064074140c0010070142d05500550003101d180321400e00441e4868100b954845140e0b420918044180c0d05041401006220003400b26030030a541011204110b10114109840d48206500e0500b0160031a2003001c2c1d000314001c901034103400e0700b011160380114441c0e0314403142e0300c00d441a00001c440048a04080c80d500140c0e41980600480e40a4108071001910240c03414402c8903645190170303402c0e80030048442c00e100c4d0701000c1c000d00b8000c8104034880c0c04401e00150428001503000000031010103014140c5d103943c460b0403d13019034001c070b440e203401d0344180c4044c904002c8080c100c85844640348001e5401c02d10501429031040421500d410901d40c0b0310109a1114042c1691003032460390111781500d03007052 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 370648597 1250 370647347 370647349
    0x5090d0906050702310f0c021b010e030a05070311010e040b0a030308130c031a0f0f01051003061d01241b020f090c0a09062d0504051012060e0705041a0405 68
    0x417503075950303500300b808512880006490011140403440308011500504003d01d952100c003160713411030501c246002240c0ca001000060308040e0f0901004041e8421804000300300310101003512801d000c02d03212200d81000c41d03014401a6511010320301c2d440142d14030180f001038000c2c5a0305411103c200c1d403404517401d040d9104903400c1d9460b0030540720600c4041000100180f00103520b44c2c0500c0742402c410b01420106580c0945100601449201c0d80000550b410407600c0707588104e0003442da100800b084e0443c2420700c0402201d00b03004802101e241d4116103407455481400c44550350b5410b0362003480551151803032212140c94071404aa21050307101110940d5500e0084042c0140c0b0240071140d60740e50042000361480c0c02c641d0000b400d11100803070410030100e4444050308c0451150043ea14a6807003007908682e144504e0f0006a8012581007100c00181d520040c4040307000c103a000104851511221306480f040800c8400000040b0200402c1c44041068925003150f414070000c03103810561114 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 370649847 1250 370648597 370648669
    0x31718060117030304030f050912060f010902120a0903050904050a0c08012403051e0903030f0907030c03080a0c0611040515040e0c070302030c070b1210060e0d031806020105090d0906050702 83
    0x14402b142c0c00d40c004c1003032204020b84511240d0040c21200c80840c60300001d045150302035080140548803050350348107101b045c14010720489210100080040103140b0349810240b0007000d19060350000210524000315448002c8090800c0c500107444501d00202d110700822000340000038003a5207000403410030740d05581195440e16005004541c050358481c03500c08035812004400030f00005055101000800107d00c50040c0031054030742180701e5981d58128282d06941c004407440700108400c0c940b2411030101000d01029005684045440142c4482d880c02d038900503004a0150703208040300303040810400e80f00708004214251181c01640c0c00c103944540003500380100380c4d10900441c42d000401160106800164550060f115005d000f146800c04d800182481c00317040c481030050318070740f25500c00e050040500c01d0b645c220303c1612040058a50400034041d183c1074520801d540702d002c044220040c020307080d4a094032029a81c840c141409502001750010006200c2585140b60344054900c540b900c2c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 370651097 1250 370649847 370649869
    0xc081b090a0b031602070e0c16020a06050c011a151b03130609090207032a0501180543092306010903020901050d031718060117030304030f0509 63
    0x2800d11030f03260f01d0915454601d03580c507001c242003103402018090140d000303121902a00170258405494460410095100c0e1030340003900080d500c80d807980340000d6560b07400402004280d40d01d4000b0f1105055450107a400c2c1c044403914035a001307010444910007188900050300b1071490344035800e1a8044072041903820b65100e614010949081c60030203108003a0004010401070500c03600031031806215450080540051030b407144512031428640143d0710f403034421001e1031142c004000300700e00850241100f0448032450000c941e035005500b6116140c4000c481040d04903440842c0320588441854141d82542d92020046060808400404034411010744991000c075003150504500540a0195448850710300424440c10010740200900058407101c08050440340c041e0b4640710b5000c554601520010039004e056a00ea071801301c10009035503030801c1c00915103041ca1007038411690f291a0f09900c843e0208540316000d6000f00041000284220055900701ca55490440c0c141503074400060084200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 370652347 1250 370651097 370651109
    0xf100e031801051201060e0906120c040e01021909050406080304050604152309090f01060e011815120609061a03060d020636010e0105031b0318060601030c081b090a 72
    0x480d03c4042403d0400494032508009d088881d4044040000c1ea181e81d82c00c2c003499a14015621415030380003140094058030f8800c2c42101266501035a141402031466030700c1d00c01c0358403039400c2c03040010380980003000725802c4c0e0b04060300b020310f00760920310545104c0603d44080b5081106105080203201000b9940c0002490005a000da841c075105c001c00902c0100a446800c3c040c0d0158010009150002001c1203812428248041400c0440300c01c1d03540c4141950005d4102811140d0150032a40d1040740d03c01441c1e104101006880e0b114120b05003110498041d503181c0c8a031016a4401100080780955400301c8018424040141e00d5030120705180c0001d916141c10400649083c10041c0170702d0350b0b031592900081446083d0402da000020200402551428140b204c0040420464480041c0340c0100410706100e407540c0b41440002e680c848480f000c90001c040c021107000c0b41c4558402d01440e2010a150b942d0600d00f1703210700301005100041600d403581001d4080241d44805d4446050603002024 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 370653597 1250 370652347 370652357
    0xc0f0a080606150d0924141306111b0f01020702010e060306030313150f140d0509030d060605070b1f1a0d0908090102120301060503040b06040e0f0f100e03180105120106 74
    0x40f50b06c0c3e50741c00348503140c101c401400d20a00250035180d80c41d465520001d00009036070420540e09141c401030400c4410f28603032100000f0304440c0301200341035043c0d6203080748080f200c0d8814403086817402c0b4011440020300042658100e10414030f00940610b420110007820b4901c0c060b03e0640710f12a80f072203030344a415014002c00c0d503c0002a00300c08181c0c0c803184e8600b05200607003194920b40400b80720310f940704a02c1c07070354440118100000070426512128241c0000300309690321040080c3c241c1c2c1041000b150441c440c0c00008400d042c0707070703079403505d00c0d400710040d402c20241401d0b2032504030400011800c4084806100c503044c0388030203000d0400294080c9449a580300810000281818281c980d002d040e224204010041c00b5804411a0303403040d0081624955034940d100028050481c200440c4428840c00c00414a02c04000c1000c00310380408004480303100380141280c00c2901c4030300101590a400612414801c1203403501184003011051414618041440709404481c2070280c0080d80064 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 370654847 1250 370653597 370653623
    0x1020316030b120325020904110a0603140a0e12070305070605090601030213021303020d0501020d1410060c05010f1d0f010203040b01061b140c0f0a080606150d09 71
    0x194251042c4800c0c0341d0191202c10140c600441915680d10502c20300502d5000c0d051000044451480703100d146450b0300500d81c24103030030941007240e031f454402c51166110300c080c80e10000d100c500030301c6401480b211406c070301e14140d911000100c0c000c02d00d01c3c0544210b0f0003003441e0038100c10014802001c000b84242c8070704d902e415040c10818112400140041000d50041d401440075941da00b00c44a000402041c01580e903020b1004d51317012181d0a80d0001750001c0003c07107240708010301900a000040780009003000312961840c2c0074940040140c032400d59020f43c01106104c000e2142e040c1c1180a4084c40c000b00301c50103030103401411a60a100c10300d00e20002d000344040041001d1182800108500009500350b00b09030301c0e01c6c07004e00410710524050202c000e010070b60700c068102002e45401e4101c041040040020140c140e11100e071407040c1446401d505100c00000e14010b49a00151411500104032070340d01d160504c40807410a0f2a9814030240c240420701001000b4000c2c40d0a507481500c4281240c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 370656097 1250 370654847 370654891
    0x2090709030605062403280c0e0603090304030221011e0506030a1205210106030b03060a02070305090609010c05010504050f0f0f0a0308060102031c0f1d06040b190608010608070611030a050d0e010203 87
    0x89c0c03071401810b601c100c80810a0015095001040c0c0c4d090f0307601216540741c0c502d0031914062406240400f404695420a003040c1203560b0540100d1901c044206810b20083c1e07503038804c042e1503500c181e80091100c4058401d0b0800584504040c1440403a40d03140444564565449003d038008240c0c0f0600000b40ca51211210508044c044603402c41c120940039414102c096802420a0082a000c24080c00021403156956842062010451a0024020410f60500303060581e220202c0b088494403034031612070300c4480110001808035198503607501030580316801ea601102d0711200540003504511040c442ca040700c46400180c42150b4085c8040003d0984a5180d02e03010707107100c0c9070b00d08c02c0c42d5181e045c032401e4000c02290099029502c010440626600d03010702078260442025045080c92508001103503c07001584181306441c0c40744203c1d550ad50f603c4c00110f504a40001c40303c80660000d000382ca082501880142100101d040004600e450a0311501c0d42240c0048070840781003541c5484d030142d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 370657347 1250 370656097 370656107
    0xc0a05030a18080a0204090c0302041503110303120f06040e0d020f01110304021e0105160605091e0d0e0604050607081b031306140702090709030605062403280c 70
    0x855030b296424004441c40c0044082d26142103010203805140c40701403080070400c08060803405981e008004001001e521205610014118001201e40000c0000703201440e29002003030340e01e20304450801c0301c1c03559100c040101004201501081d003068658402c591039410921803440030010300da0041218203103140304213003501c100b00c0c1d144403038820070014007001d03032608070554560840c0c00d6000b003003c582c60401259540b207103410080990034010350241c100540e07600490700409426040701d0f1030158844980c40c148070740f61034028155105410031220030780a44075081c0c0c04503000b824942050b0f035410210f10750790b006c0c00c01124020f1001030144d80e030b0416015190514200e6800441c100700072822a03000031455401907030305001c05402e009072901c414078129011540d014144800c2d60414640241c0517010a000c12240c40c1d06040004102d070802c0058041001c079446080100075080100c1410389a1016041103da0750220a2240071245181d254811795040c60700000b4019640c864002e02c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 370658597 1250 370657347 370657367
    0xf0a0305010915150b2b020307020d1706010c1214120106030e0a0201090603021b01020f2710030c0c02040e0c0a0f08030307180e0c030a050a050610080604020c0a05030a 74
    0x1910340180c3c041801744c1403400701030b0b0300b074170144546088011000d0428a03d4501ea241401c250480c00001086900341c1e0204446a210344a41c4800700c403c0c1480c807210340250310484405000412104104000c900160103c0e070040c9840d040c9881c200c1b80341f100044031580000034070300040712075a0040090603810700c56804000034020241411742d82da80d0000300303620780910803001010f802040d61841030000207007a289030060380000b15a0354010015451564200c06001d82602c142035801030b00b80030041000d034840302001031500148070f84206d0190300030044c8204940c02c000102404200580b154802d484489211400909010180c43c04000f1204550780009402119404042192510000c2030780c0d003000450515040d0b45198017102014001542d00840c40341d1078905c140808440284021402140700c0398046c841a51140d0b4498161801035030032035048107001c0360480201e03214030b07803803030f004440184054607001207014001c0ca031000705007040e10300f501300164100066030050a4a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 370659847 1250 370658597 370658621
    0x204120c1212030b041107050a0303050106081605070c12050714030109020d020925080a1119030506060c07030303021207020601060f1202130801020c0c06180f0a0305010915 76
    0x40c1c6041095450a81c00681c079060281899120599003202d9503ca130400d82050200e406002d441c1c05440c14030965996890720141d001c01d24142c00802c007207200c1c3c907100e84145007000a01540c2080f400d03080b1140d500550703094648102111012855031802805201000c0c001c4004000d624140b19a803410307261060141c0d880307689403410510042e298002032103421501100e169419541e80100c60040001c1a00724440b030b00540441c41207019009450180101401d18003040304820030303c00010117103d0203112801541c0c1c6100c000c0c090314802c1e0401c03503200c00d024000a0800c1a0000d03028900106508218080b0b03402240300b01900d480c040703500c0c0c0d000c1224801800154036121000c1d01c070440c000c010b10104070307a8072a40702c0d6110080e0100c600c14081c92201c00d846d10b0350381007440e000313401150a188190041407071500b0649404002d94402801001c01d02420995030000c206444102c16182030300003400f0500007012490030b216100245000b98042e8400c00705600780c050848542038004c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 370661097 1250 370659847 370659869
    0x2070c09570e030d120509011416020c0609061b07051e01020c0405100b0c0c1c11030a12030906090803010306020909010b0304031b060b2806050c0c100c060204120c 72
    0x50b046501c500003000302c241700940000e1546035038050341c2c05001c1c00e1042c01880140c0d03809014140c0b100381000b401e190150340c00d41d024200d0142c1009064071850306100d81c001c0c001e101c4d00103a03c1e000e00c220171100c9944022070700c01d503030380f100402c0400e5000c0e602e241242200130b0580d4090b58052048202c0d22004960070002032134020034500511803030303014401162002140d03a154000c02000001c8502500401c070f1240c58041c10410a0781a515000c2125200c201c64132150041c10001003c110280c1d121010480454508904030002c1c5000d0105440c3c03981c0380c2d400c03107012034080c3c00114003a60284402503075403000301e000d0150540040c2c0c0010107003642041007001107944903860040c004826003100115424078184400900700031252240d0002201d020480844446031410705401d001089103036961395200c40c155903a02400301000903d80000209400790310701281c0d804002d810303030304080100d0707049511070808903005600400588508455080c003802810408400203103d10080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 370662347 1250 370661097 370661113
    0x100609090c0b0333040c031401031b0308040b0909060d0b010902160b0f06030f01060302031c0203040e01140a0504020a02030904151802070c09570e03 66
    0xd00341440e0003a100e03504070b15101001080c2662400070b0400764411400a200d00b002011240c8001c441c204040114411483c003240199000d02901820040c0007110f103441420303a10b152613000200e40b1040c0300e0b181540c09100f0120020b068038000d08058421000001c0d1240c1c1d4841c140204000d0103440c2610400034040d00c18001480004001d0540302c0c0c544015031140140341f01c401380048640c0000f0300500c0c4034000c02c2034014001c10b50700e2046904600300e810305140785100500307c48440c000690076800400210b070650450280c1e23050035103514811030741342c65542c070480d8460340c80c00c0c0c0049595140c02e41d031340031003450801c1d5400007038a02140c0440c0ba164952201941c0c034803440d02c80502944d21600c1d80a47c492900038000000c3c5403110004441680b1040c00070025403140004541d0702c540e008001c10201150710400300140a074000d900080d0016000c20b4178200945510440f0000030f100400d01014150800303100400c4081210041000c07080201400300741c1c0c1818198041c0c2c2c40031039 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 370663597 1250 370662347 370662353
    0x605060705061902190c05010f150902220305060103051002031005190e0c0421120804050c150c0f010c050301092a05190c080304030509010309050d0210060909 70
    0x120b060b00a4046528400f129210390440d8001e4000d659008106503c0c0b8038060744007641020310b00150b603201300000c010084403080038608540007008030a0420403c164140205000c1e54010880381c2c3c0b1606080b41140c09a034800101401ca64000301c400750403a100400801400304400c4101c6d04507030074190300354542400340100d401c1451017583e2150046040c08894101035a03469009440007055001e000d00d01141c0c071000d17540c0700e44110340c0c5103001d0000b20101c0c3c642c242c04800400b940000c1c6210681c01001045545030700143c001d5600d80686001d000e0315036141d400c0b010000f08a030380b12545800c2c0b8080320a06180b0724448841c801d9045c03108000d103255000049034107541c49003100081d00c1541003040c0c420078580807007103000381032888040540d244d0044060a0660f10380d424010101a03c0a02190904c0c51101e00402c01001480401e0000340030b8405022801410715000442104d41c0d15880c0c0b4041c580a11500960801440c50f4003000c03480c001c0d40080c1c60407140c10305c80c024982d9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 370664847 1250 370663597 370663603
    0x3062414090406090201200d0210090c090b130f061a030f0f07050708040f09060f0b070308040f15090302010e190b0a020909010b0d0506010306140906150a0903060605060705 76
    0x30700c001e0043e41c1d030300d62140c02c5a002d40e21043c5915181000948418808201c460760b5031000c0e080080584101d40a03201c00302c647e800f4460030030b40c1c480518801d040c90064480c0142c84d074039090fa5804402d038036818070700107582c1c803400480c590441004200725250051081c02d030071900c523005e01461030403c10401d40050003565a50013812040a00f106540c0c0c04400321028000c20b100140f03020360000d400504141720b00303051401d8894a180070025250f0719248800c401c821031290302007012040c0000e01c0824041c1144a070311a0145107480b14902aa030b40703900452a03208803d244069a60b01d000c03081c150709114940c0d01895100c010905018209020055220040c80041c504c070280c100090414815805a51100c10007070003250803940c4030700501005400c190000b40b2050b2500c40019401c1d03110f4010281100c0f045040340b5881d2011205000034581e00801c0300341c0240301084198802d160000090075002e010381c0e5054503590541c03514000382c401940c4564440c101c18428500451004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 370666097 1250 370664847 370664851
    0x6061c050d0e01050d02070b0402030607081012030519020d032414030f0d050a0f02010b0a03110409020603010b0c07080a0b0726131202010603150f060306241409 71
    0x608224646a0b00b81004031a54480c01e2550384140380086107180c10020010421030081e8800c6060720705640d0f981d00100d401160032100885100b0300258100401c2c11009066103400c0c1c00303403400515020071401d00040c000076040342003006074884044140420792510030740045810b01480f1981101149040014151f424080c6c500310b03001104800f4856981008811711080d1410280d420004020034045c2c404e4010706803841c00304140750300300400742d481841850810b1310000c005544060458854030515091101c40942013603444548001580e6010041d5008000281c0c1650b5500c241c00125401c200c507030342c440c000310f60040e41d800c1c00145250994551040140c9004c80c0f241c03007000c1c8225071442e44330040d911a41c007000248500c1101844281e600390380103442030b084111403500304900304c070030500c03000c0c4c4200091480f5001035501c03a005062100b00116000c02d901c0c1e1240c4920b4100c450f188106540c0c81c0c44840c0040c000c00d4442e00035001030020b41c65641c41d03040f19034041040a180 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 370667347 1250 370666097 370666123
    0x1503010920060d05131a06010206010b0a1112030925030b060d06020c01151d240913030311040303050403020906060d022d0901050414030f03070506061c05 68
    0x7039101c1c0c078400340c1c540320160703030300040d9a000a1181d810030031044546014007071000c0d51101d40448280b4034900038540940d002e910103034010000d60381713000c10390039068001c003942d101003109281c400503200c01c081010060b100e2070640c801ea070f24103102c6a160306e4030012240001104540c03103440907000d56602d90032022682c01810f211810b903202c00004e00580b003d0080208110310110b0f01c03c9084c801503100301c043c0c1e80c43c000c10790b45c210384502903501e0381806150f10007a200402c80004103a40c1003500402c5041486041846892002074001440c2c5281200c4074500c0d44421030741101819414051041d10901e603945a501d09030842c3c600802e80d1150f400068059403214010882c1d5484a804a40360300440c00350864643c0042c0000c150303e00c5d01c081d00044500328040d215240d4110031421540f505805031922481d152400300c1c0c0381828148000d02035414010092a28408601400200080742c0b0410140c402e43c0b400b602000041001c1c542e040c07280074920094030000410008071800e036150 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 370668597 1250 370667347 370667393
    0x181f020313021e09100b030601110c0a06020619060506070303090503090904060515030705030d030f110c0d0210060605120a0b1c0311030f040302120705030703030815030109 76
    0x9507010314000ca1003031901e402900000c2c06100754072448900c001c400c400c42400c5519041070307101c061200300382403518007a4414541c000c101081056016441d509607148019007680d0a1340380420000c0d005688950001e80075800c0a002c2007845816450f10b203607010300182040010030304100116406000d8510010240766582c03020030140300c0d0400655895a00c010411200d80c646890000301415043c6ca0100c40006a0494050300e442d01242590aa40b009801810061509841100644510040001380a580b1a81c90220a15480081c0811112071000740321200b10108000d01d0803100c9003070032403800e207001e41c00d01003a94003c1c100c500d4040000040700103600e0300d080300c03001080a0007070554082e2542c821140d00c0c40d001d62690840c2e502030744802241c441059112612446a0307000e40d400c2d41c4080000384014030745100900c00c0b40c0d281c4c004494000382c80c0c001103890405a908180c0118520200708281003d50000184600c0003d8000f405245115900c041601072152156500c0d10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 370669847 1250 370668597 370668601
    0x170606060a0f0513150c11030703020f061e0d0b030d1803031214010807051207030b0619080102180906190905070e03011b1403040b070f0c050d08181f0203 68
    0x980c13000d1200c000d0142110340c102d0100c00901d02038151070286404590190b1b411070001c6a525012801d401202d8016240030b080121800400c4015844202e443c401d83c6280720086200041c2140604203040e4071000000303180394000101860071600c20701c1c42e001c210b0300d00b10701d40c03030340000d01840c400301c9a150911090030703503521544801404d410500d60240c03d100f43e000044900d40010048200d61082c0d512a01c500c071038125940d120501404003401e0700c04110007162480c100304003041c00920071710082000058480c0d00c103d0076688009444c0b41b06004010303070b4036000d180c0403014542001e012507a62050162058001003035205500c0364140040d541c1002980c440e0107600001d0444000a000300481c408440d80c0b0802c0c0c031001c014080016120801148460500c00100c80c0500c2e0041c140a95907600c2040454020076003401d80410844805040340c0022400c0207101011403258549200360710705a910740741b40ca040039607109243da02c85a180d600b403807840180d0050481030302501503601c1e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 370671097 1250 370669847 370669867
    0x9180c0d020a030618031103041202100201020f180a0f140d031b0b0108060105040b010507060902030712081209031314030c030d0f0206090a240b040501170606060a0f05 74
    0x12116aa00213011107062109030f2000c821080824205944282c440c1c207401d1000c940c010741d032401799001c2d41c6100e100132000400946048640f01100520903c00035103044d6001140604030b0300000202140101e55414410341072401d42850f1010b482c6400201c0c117120302c0c1900c0b040d0303200c0d8400855405002e01c40d90440a040c8280e81801c00304d40e44c40e000c000e00c2541c0f0f01c3c000002e06024407070031910340240c10010845103443e019111068205942e440d04081c01c079103481c402800c6450b02240d141c444d0f100700060403079240300324812030b82c0030303100c900d840742415800c04906e000024100119504100078085000240c0400c80054441d610a9401c20600000110b40342440021009900d07210341d070498206194007001d10b0300c0542da542e0030ba64076502c0e1a24041d68900c901c0c84020010340c98030050003203284002480722071000c29400085000f8241c6008581110302c20b80064103012004203010792030b030f20100b160a41080040c2c509920302120504003e04207400400420104030b800260015a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 370672347 1250 370671097 370671109
    0x2604060b03010c050a080a05090a02100203130f0501030c0903020a141203300601050a11010216050708011409070b031f0602012307021002030a0212090c09180c0d02 72
    0x100c8024000b04403003410780c40d0180894211094280008244400042190301180111405001c0d0f200042203102210340c00c204400210107a200d0462005110540e06c0b0b0198414200040112a0b117181c0b80504002c001419108110f42d041c3c24403443c5241080142c036003202c030004544a899550140321111800208003a4038403030716200501c00810031113407850400c11071080070b40440f030000348030184c1c0d0701500301c401c402211254040b42003401041c0e442d0b0301403401140c05500340000180b40c5442030b142d0107041403c1c040b0a544a81c84030303c0a1049403400d200b10580c2010001c59580c076807600091a0b6955001070080000300f10003c40400e19039074140080509403010030310840000c5031994002802003050401c400300da2104030207000417030015010118015141c40c2d028006500b03074000c210300a540081c1c80401c016508000c24110003803c21003460040c030303004014001e140700f940b0810480031006040c00d8a03000e41811402c3d5114800901c14110700300945980621170a24000a60 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 370673597 1250 370672347 370672361
    0x509010b100e151b190506191d2d190206040f14090a0902061603120608030d0608010b1e01090f030b1e240a1a0c010c260406 55
    0x810f410700411240306401e02180300320100351407002220810f0709181c2a40e204200b004201415a8202d4070105941240507815030100134088600800c3d00130001c11410080b0761070000e01e816a03001070100f54003524520004010880c9140648107006118100050f10740501075041c0c046401c41c10000011502d6120903500245120100900c107a9038495410240408007031050348118070f003000203980071059200c0c105450b80c01402c038905110070340a56083c9440303085411340a120b01034140450040d500e001d5140900b100c40d010315201e002003403145003a82d0864100d11040c0c2d0500c0110142c0f85c441c0c0084800a5501c02cbc1d950702d410040d9401a00e40302c80319008003980c0c916000000c82400141074440380500d2480003e410040891080c0a40030503095a080fa0300301c034a209451150003602000800040c802411a0115680c034020454060411180c0d91017603036001c901a14404028402c0b01300c554414203086040e110280005441680f00a00504000c41c6071800304051020030760000c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 370674847 1250 370673597 370673629
    0x60b060304050a05010c170a0207060609020a0e041d0a081e0a0e19080601171009030305011a0304030822020a0b0306040b030a050d030209180f04060509010b100e 71
    0x199aa04050030841e03151070b50b180090358070f903007003840c0900c00c640300700790032031f09100a84140c0d066600c400404170080e6210700070580310706841d0b40d000310f818945840248080c103044d450f581c2d240d0906000b84010f450284c40300611042d01d14807240c40305440820070302c6145900210095403605401d1340e96030950304860000414203000700e1600680ba8104500e00602001210107079040013046c410121a82114056000d580d00024010061000401b02c10380640700320710151000b8620039425802190b01012080e8006031315200100925010f80c5450320000e1145403900b03255240545000d803000002030034002071001c540003074400021000702c01c00c0025500420070301c41c1507510f03407003000ea50304165a41d0384a94507007610401c041c50001041e040a5900c10701401d507505400100b034009400c101e00382a04a101880b10404008222681d10b2044044105c1060231b0300f4241402411078400a0500c00b0320380c501080041d460ba02c10a98880b03200062802e100040d15001c042110325460041203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 370676097 1250 370674847 370674859
    0x1404020a140a120b06071a0a0b090f04022103030f041e060c1101021201031101050903060705120c0a23191214060603071404030b0910061a16060b 64
    0x1542c0055000c040414042c40c125010300204d00b21314100000c0e4801e145001b84400140d1200181c01407003504c80340e522104c6814002618000800410701c60b03a0b0440c0c010322009841c00c1080110300d4000754001c2104010394031202118076802e50f441d03a0b032001409031160070b03a0050010701049144844042500d01c1003100e15020b00d9149080000340c01581951008030340c0b040e03103020620368140b003034443d00e13403603101060b80c103900e0740d00e07183d540524000c07110341000010880740030070740c030708001c83e40c015042d0f40e0304c0f20f41e9004850280112007030054103104002004002d004105a4000200c5a101d2610485e400d07103601c00001400c2603202e008000f02640312020b0200d10643e4200c440d90900d00035540052240040c070030350205c5450022240356500000070700110b41020700c2011025002c4c810100c04a00d4182c91f521140c0d0200c030101e4803041da40e841000811803218907030003084020072141c04688000c10001038586074a01601c14800c54070100217006200f80442908101c00c10350025002d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 370677347 1250 370676097 370676107
    0xb0406090f060e1c0e0607150605150a09140a0e07020f2e1407080a060513050613090804053708070b1201060e032119091404020a14 58
    0x543d82c5800440e1000340b078a90300d07003800c524441e002d035406400b103043c0240140d250007502c0c1d807a030041844205950940b20307500c1c01c000c00e06403103a902c90100040e038801b03843e07124282000004c0c50155150031900b29200c101e4160031454840c000d44206664008200341d84a54a8a0703049160003180f190410700c501c1042920004920440129540300034010802141c0c45030841c1c0c6101a64121902c0e1200c441c0140006080300d4401c0211a404c180c240c80007103806641c0d100040d070961003280300c09000c165030768244100348c5002d078801c24407049900c20501500c4443e4681600034000ca11a00d40901038851100c003554400c0140800c25011003000300400c100c2c20f42c1c441603680e8450045c240d50b84030790b0b41c0c041085074015003079461420811410302000e03820088203c416a1014425035050300c12490384081a804108208004681c503d5005803030f80300743d102e9410f00070041e030809014460305141c14014440c04444c1000c0c201c0043c1c2e005613a43d40c0c2400304403001c059070000c0c03494810000c14 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 370678597 1250 370677347 370677371
    0x6050f010c02130f0b0a09020c100506030f06070206060108090f07030602221d070203130b0a050d020a0c0615030213110c06090a05070e010e070f090b04060323040b0406090f06 77
    0x10100300c00041c20b83e03403240c6c1c0f681c035082c80c0c000320701c121400056142c0c84485415034107046a000300c0d0344103201805807211408005806840c0c440300b07841100258014404012055901c41d0540d580000b40c840100741281c20014000d03103130310050001400294000900b00300d00f08082d034a803007043d15100d1081031036641c0c419441c4981208207100380b011201a202184481e840007080d100c0002c10309180c00311045c03905804112580c403481503c400d12006201d000c031030303801c03a1026141035022a02c0341c109204441c034140d02142c01c0300c00c05000102c1400c0d402d00160300d03000c40901c40900c0c0e5110000f64400712819240950054807120781552169400700081410049140801c040c032980440d0700c0c594840e11202481802401001c900f211510300180c1c02d5842002c0c602c0c1242e6450920000d148d40700c2d005a5020340c00354000a01003a21841440702c09080c004d000c04085907134420340c001500701030f81c07008145007014101910090712000d840060210928102c0600f9500a60410520491030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 370679847 1250 370678597 370678601
    0xa080105040218092e02030f090d18050625032001180204020d06050316030311010203010f060c0804090216051507210905060709031506050f010c02130f 67
    0x100d040307008408071641000003025650f40e00b8002e10000000d0480092111405a08028900c164840c004401c2c00c240d40c440c0c0080c802507001c0c0882c42d000842c1c03440c085500e1440c000e40a40b50004000d0752034150640d0b08540903912058a104a45007940d41069483c0018030791803c01c00704c22106050b6040d4010103421509007920440506c1c04044962502c0c0d00c01703800c890042825145c1c250a540204005140c19402000c23511910301c000103640303455001107484c04c034241500c03254800ca0008288185508500c1d08250310084400070b619560402d800200688030b50711902d001e002005141e074040240b041c5c2510b018004e42103045480d0340134104068560582200181c51a0050010702c51170000c44a505600ca90059143d1501c001c41d14424041c141251207000c6c18107941c0c9a141308002503040c04440e01440e00c0e959030529487c114105004094160200142d0082c0740c803070700300714a84610040402ca60002d0902d41040e15903400814a8850740c4040403c941c0c0c6013a282c04151a0a5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 370681097 1250 370679847 370679851
    0x729042105070218370902010c0b0c03090f061003020d0c03120807140a0804260706090b01060216092a0306150f050403060f06050d0302010509010c1407031d0a080105 73
    0x5c20b55201e00c401e00d500c0d000c40c1c440c0040100c400c41d0a2110910b0545250b03001503512a1061601005903a480e40780e40c641504252034182e10100f00106103c40780104100c00c02000c50010040c1045042c25031785600e0591480c40001d010301c1c07600c0034101c1400801160b004c01190403040c201102d0781040c1c4000d081000446010010950803000c6035020108401501d441205036224282a515680c9a40d0408581003100010b1840401c00c1e040c5000541030250031000d01c11074012804450720720785072603941c50507000401103600240c40c0d201c42c0c1299104480484400350300000f0000c0d0401001d0100c0d200b05500002c41c00320121550708803503816800001220350002034040303654043c00d01180d140c020742122400107407082c0828004503540d58000d040b010409600000c50070f640d040440c2882481d1179054026035955010040010020b0180b0311020110345850b0002c0144440c2041441c00b84410190801090b503040034650407401c018809a21401000700f000c956032200503501900f01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 370682347 1250 370681097 370681111
    0x2070302010f080415050c0903030708120105270907050a0e06010f0e0d110303090405010b071502070807081b1015050d0c06080c0f0729042105070218 66
    0xc1485000c202034070500500e40503981c80045c00012000c51042c10000c2d2001800407443c50b8010410300d802641c0c1003004100061151886603160403d0600074102100164072040c042d02040c02d1140d00310014070310610b100190b044a011446d1102a02c40e894600c85800c0160001000f100104a6104e07804c00284248800d83c1c0718101420b6000080f00c4140600b5086908032064101480014a650003004400b441c06001c07642000000000501512403c1c3c5c440582001c0010b14042440b5101e00420181690800154903080540d6101a80ca01c2010005011200c2c0801e20381d0040c010301501099010a03041141d8640120001c00ba0080c24801c504d44054980f40c0000665401c1c01e0502c00041c51300314507041c0c025880c00350700b510040c0c03000701944c800102c200202c0311850250405440c41a010705801d0702401c500c2c1d1903c0032000c60b2441000d004440450801000035120034041e103402441d40c115000052900764142e4260017910402584442d09651981800100d15012407241c04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 370683453 1106 370682347 370682357
    0x60a03090c0e041406070e0f041409010b0f0a03110103110c0102070f060c050702090a0c020102040513090c170715090503010f0c180b070f02030114070207030201 71
    0xe540d00412520b0018800f80403e002840c0120b8101405660081c511400c0c083e034054885a1349000162140805000864058882e5000034800940c101500b400606018a1280c0600ba50501043c014040c0d50318001f254903100100b030040701e07001040e01102060000046018000c50422044007043c10040200011000d100900b0300c60b014030515410180c0c2464070740255542e1942e083e0401005000c160056510b580401da04076034601070029400091382e1050b03000e401641d00c581d0b400280b84d90803528010103038024a03802407080160250f102c1e25a03044c40700202291030790001903403086400388540f00841e04440f0100905040111055540318002400c2d562994020710345a0380780e800e03007a545070f004500c2c600c1c220310394a84030741c0440c100245041c1c0b03030041d1040a003c20f06003030401002d545007980a00c00e00000e840340340b1031070b02c1c01010103075880d8014803049002034 = true := by decide +kernel

theorem cover : BRFrame.Cov 370503597 370683453 := by
  have h0 := BRFrame.cov_init 370503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 370503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 370503597 ≤ n) (h2 : n < 370683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
