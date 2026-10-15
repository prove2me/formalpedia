-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3930
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:05:35.714848+00:00
-- url     : https://prove2.me/submissions/0fdcd0d6-6445-4319-b212-a2f95ce0660d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 706654676 ≤ n < 706834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 706655926 1250 706654676 706654717
    0x80601180f11190f0905090a05090a0f0309081506010c03030f0b030a050109021c020603150f0901091409060106020d0c02040603080c070f050303040e011401030905060702030c060a020301060f1103 86
    0x2d040801c0c0c2c04540f4559401581c4054502c4c180e44122840c056650014450b4002826000a0760801303600551030b60300b20f55020032141c07606130105070184421400a1041c0108016402c010003000810555210b5584201c1c1001e4002030808541004000c00381a150f1100c00c5c580401d41e44a080820006010340c0c4401440c2c2c50020f009113641c4404034441d040c0f919903030096100c1d126619044a501a188501e9901d4848481c9802c1001d14561544114401240b6140d500c52092003402015425000b0444440d0701c1003118000030010602e010a51092004201190340040c010b4010181b0b81802954000380340046405044507030006000158001240604103100040310411101a4051144600d03252000c00d41c0780d1180c2d00c1100d141c0840b039401030144080440075509580b10504002030389001c0e6941d21400c11004441d150003503000030030040c0d2548014003205038004103200f421071540d81061030140000070750356108000c10092980c0c60501c014200b003119008960034130740d0a040d9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 706657176 1250 706655926 706655947
    0x1707082b1106070909200937060f0e06030a0c09080a03023009010807031d032221020a030512040f060f08010b03101208030a06080601180f11 62
    0x18600c03034841000d00d081d0b80c1001118141242004a008469043e494607140b1400c002400c40c8c010001c8403221440c14200e100c0203c02c41c820503c3c032000143d4018200d1070100d000e03081808894070707081072007030070480301c4115580e51080b0f035884000e4900c0026404500300c001c4a221034903400a0440b0300c120b84074030040c150005010400004179203c02d2441003041500c288800d079180c00d5000c5d8846050241460741e600910321658400e00c41d05e40010000460240e08128180b9a048c002503504005103019a1004011103606941800d0030b5460302185460001c0503100042c240140b446425030850380f0840d51000d9010000390342003401c51b100d00b00b1251785004168418072035200c440181c0840000c042d4011000019905070320741710100644c1c600004180e06600003004030030425210b81002c40c070408816003111201d40107010302c40d00ca14041c203140301110041d8100c0d0859522520042081c0d16818920b00d180304546200815480030b40301c1c19001800d07941000010501020034040c008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 706658426 1250 706657176 706657187
    0x4060b0907091d07030908132607030609110a03030e0f0a031a0604060504110414121c121b12020a090b07020a03020303041707082b110607 61
    0x21a1080300c0c5100c440e00e44580c2610010b04a1207501d50040d2071034100ca4001d00803808280d84110315003000701e81d59600c0c0e80c50164562090050010313450303e1071020b0000c4d614501042c48010808601030303005045400744a40e464144e8400100b090341c4900c4132008004c08140c40c001007200c043c10400303a11382c907458083c08000c02d000000e40608000002405180342c60322201040700e80003002800d0b6402d003408030710b4140c0c030002c0206401c281c40b68000903c2c1d496522840301400079291001e6200d500b403c2000100c201c022402c21700c02c00480640c200e00c8040804c070603001c0f0b01b064080c2e1504c662060401d82c1d100e096802100340d900c3c5032141c030718a01406903064500c4070500c0d40d20890340b01c0c45400c22000300d00580706004001a03180c20180301c1003580320010700601d0700041c10190447d41c0c07607000038035543c0140c11000404070144d0b1840b0912104006280c080d201c2d140207000c0c41c04145044a0164001c5c00c95640e41c1c017403050b4684102406404145958000b0205070b851510749000302a01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 706659676 1250 706658426 706658441
    0x21070b1b012d2307021b03010e072c0103030f0f030603050c1c050105010f051903080a141315021005010b04122307050f0f0f090a020c060406 62
    0x5650030180800c159038100034111500d001a08440c184080741e001c54180100241400001c01001d0341020280400d12030f481c3c1c91080d0030941c0284042d2502e000300041c103080c0d80c51000d01a031b060501802094101048960030740c0d10200700074540d402074034140e845c60920303c20300a054845040006c418180d01c004000d1070b0031144d4a4032a61170f2994a8101c046071003500c406003c5420541c1e4041a902d0000c082070050030803420b4000010700551101c500311442a44124036181556900b089075007002d08049041030f210204401d2003a02d1a00e4000c0c05220b100c00000030002c5013041740d04185c0e5240165406050541c1258032941e4842c0c00d031092024581540c28054801d20350242e0703000321240207042c1a1001401c0c028101468140c807035668a100440c11141e14003e0300e120783d0822400842c0203010040000101000792070442801071041a041c141401130f90360044035529501c42006107004010240c400000c20355a140210000b4080c0814191041c02210203210610000b90000003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 706660926 1250 706659676 706659727
    0x20a0201020a030617060f091609060501020c031c051e0a0e0406050402090307030b0a140f01051806011e1e030b030c0a050306040b151809070f0521070b 67
    0x700300340c1c40b01c0b00c00286178800c1035181d80b0360340910000340e1000950074100f50040c4c0c0d42c3c1c2c1140c0201c80c5989491880c0ca0194000390b9a1650380c40c010060f07907074100180303c15168140c01500250003581e04020b110b201c0c0749070100610800260406515440d00e0f003030f80c0e80d000540902a150001e03000b000b88107901841909201d1401c018001c1968a401d00c01c55500704030044c020420300d840d6907200803031901c0c028802d40b441540c512540c644400d40803071452007100c0c03d10790844103605060410007018014004884c03131200510030000c140c0d811500c903019141003400d0006d00d01c602c4010454007500e551080002c14039074100d0b140c08450b0540c0241c00041000c400b40c07001c0207580300c04d002d504030043c03040550580c8030342c0104000c05d04e0b040d002c41d04541c0202158141508020100780142d034030308444a0911202d00410100328070030310180d03000e00312040c1650400c40c03800c4009800e144034409800d5840100285403030780614100030036070040521100e81c50b1a540b1014041c50400700f10310810 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 706662176 1250 706660926 706660931
    0x309090a1b052b0204150c06050f060904140127031101090203030a11280515070e01140c012a0206071718100501090b060712030519020a0201020a03 65
    0x302607540254240e554526100103404a18541e0454111506043d80440000a83e0800c4045582040c0d0340c0307809190455915101800c062519081c0b046450091591840525010611405948480403070b9049a04410014880d49175101a140140103901411807007032240850325500d1303803000c0c021058175402501c0d009408111040a18241d8a030158000e6158004020700e25a040c0101040c4040c09104c03000c4071100000c1040d1781000c80810307282202c11414407104a02004030400401d440d0310708188102420703042c40000a0011000c0344151418090020603202c80c0302c20410584401e03000f800028801295441e2907920030f4400100340e002c0c1d001d180d082080406000040c0d943c01401640c1e151030010351055805040c4a00203040313080111104410076140b8a0308102501d54020300d968009100e514040c50b2104495072515140d001e044244030440120b1410340200d8440919802c000c00d4036a100640e43e440c01706464901f001c910710100e1541012a415800b4199140716070300c04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 706663426 1250 706662176 706662221
    0x60f09061706210106080303100b120c0a05070b181c020d03150306050f060f010309020117040c0806040503040311090126030405040f090c050607150b030309090a 71
    0x8079030600071801c007003265601c4100842c603a07042a020f00c0d580c2c022104407a000e00c0b4240982a4207603003c1d0ba100720036030303440841400070b00418680481c004050100c5403d01d00327107900300706103d0303548000c1c06100403030000300d14400800c0c007840880e08115400004424186080c00c440506000b403400515414811245010380c0800c04e40301d82c2041155940003040c00d5405298120060002d60400c10b00d00c0d1901080080010018000c05000300a0400512100d00c0c1c05800d00c1a0390300d441950364101800c10341c5000c0036036001822188040d1540200040039950703824030144101c0c2e00c1d0320440d61846080100021701c1800300150098030710540c03030941c0310340140c4200204000c0a000d0951104d801c0144898141d95060754505014551003d5074200380c1d50b03e00080860700c6080000f280c150316085a401000071032001034010304000c603012420042c8986030500c003444000c8008120070307510014182c456404200391944c1110003032824255250455000d409804040081c070014482d5100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 706664676 1250 706663426 706663439
    0x311090f0117210306040f2c0f0a03080906060102010b0a0e0a0618060501121401170304030b040c060215060915010c0203030a170c03060619110106060f09 68
    0x19424010292240601000e90808240040076142c8000703400c1984503000c0142d000140c2441c0f00600c155442103081d40700e1030103800b880142d07228151040a01ca1404201d10f40005461340210b0b4240c001c100580c01014081c00f00d07070318190307100000300210b1044403603a004056228a410f03101d008040140d81e1913131141d000580c00d9509080101c3e40c0081c07006824407168000502d2203a00180450010648581d00e420750071005410f031441c804240d465140910081d60000f014400001c0c4841c000c02004d00c10381030400c120350060003110084086030641c8102c0403800c1003640d01840e0011406201ca04091802c1ca19030403442c460140503001d152807440e0340c120441c01d48c41c81503001910104458ad0f910386c1c07080d211084a11020705200702d045410300036850030409800d00d03590585641c000c14480c0800314000380301c01020400c1c803074801c0040000c9a01d8190560310901d0641d449150032490f00c280070ba6002d00e90740c001c0c81e1590f00c2c0200001d0400d40c049400d08084e001178841d141020b441d8603 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 706665926 1250 706664676 706664689
    0x1d0106050a0501082d0106090611060a020c031201090207060b181501170108010f0b030f07050603060a120f0b1b120403090506040902040e0106110604150e0a050303010311 75
    0x1103000c0e804100c00e9030400c12540a020800c0d88070589043c0d00010300c190040792146040001c0c015554020a0780040c0001c1e900502d00d41d014102e09d041183d112466181e1051350340c640188a041c0e1160040b0b008882d00004000359403000c2440f201c0c44009686511a00000b90840c1c101651102d0074038032058064200125040740881c0d412404140603503d480c202c103025000d22076114100714440c0c5440f8014242045180d0181a070000007050000314100c0c50000e440000c050300307100c0e4102c4200341d06c49040010f001d50883d030b01562401e880e940c1e000c000486164043e48070702c6600100062110404c500312110914040c030800d00355825440348414038140c0c2c280b0a94403c41804100002d20380000c642c90031903405486850090b1840f501c900108050380c21603400b903158240c0101c0c0030301500341c604d41c02c0c501411103480c10301c40b451408941903a580c0c0000d00080d00d20b600725003004c0440f615940100e401020b078135040f9a501003140c58010340e2640248000e440000031201590603d14005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 706667176 1250 706665926 706665929
    0x10e0910020304050c0d11121515180403030b12030702030706030c090306200a230703171005101101050a0506031c030f09201002030d020717030a1d0106 67
    0x110082400c003900740e0506c0341400f210141aa50781840e07142c0aa1142d0382d0304040c019039095440030b01100c0100c0d03076081080d07007005042021411642d0213000115111014000552403080007000d946071250306066005201e44041160000300480700c0302e400e140c00000031700e2042d1081d4200d60380c16545442c04c80032a41c130880c10800281e0002400c0011076074981000f80703101c501010341108119940440383e6242e2000005101085590780160000c100c80d05a0760140714000c04900e1602c0c20761b0750000c0c0401d0788131040e0101110064049412541807400d810054180078081e440040e6248002408011030b64600e10b41c3e660802c40040e4120940f4040e4902032131018000b00031000c600d580b2001d0048001c0701050405948e000c1c4100030340341601400f5252400f440c014220281ca008032000308a8003010464010000800e070003031071aa0000840348000001580180c44103414905695500c449810000070340710080b0501200d142964084400a10031140e5010881d014140300c9098031041e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 706668426 1250 706667176 706667183
    0x8070b100f090906020d1404171602040504111305011401391a010302010807030b10030b0a090e1501080f0c010e060d0515101d1017010e0910020304 65
    0xe001c10400315000341c016107201c070b00c2180050b0401c132101a029040311081400a1820182c10082c042400a501801c1103000031150b5602e290580e580600c031001041924003e010700c0d80d51000a050052050301c00c80184002040c0c12000d40013a002c1802a050a0107080f0346c100d440c0c402202c2c958018044140018054000608106a128070003680c5c01001000c020800c0e66400320100081c43c00f602022602010800c0d0882030350440c00018500c01c40241408281858a064001e850b41c6a042503140c07006d00e40740200f1b005441001141c0074244540c040d007103403401d06165a6803210042100400b80120380420783c100da0313846c00c480d0390717462030103a10010f141c0000c80c0048a13540308203e10813030440c028103d540340100320a0314104441c400c40755203524cc400c000c0300c88070300d242802084008400c20f150010601e020002200c1c1ca07041d1091102e407082c070000b0760252142e03018143c00700070781440f400403e0a6681d076001401301a1421511605140200c020204054a15100303a03405181c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 706669676 1250 706668426 706668449
    0x130303050a0b0f100207150f0e0a030f0b04060f0e0705040b19060302030603070f03031e0809030417010b09040506070f05070305250804060306170706020d180e0408070b10 75
    0x1c20f68103000440b4030303e000d1801180070300c400116440410003208414038650303a4404400c0444002c001b4032807480c440c0040d114000043c0c042010510340d201214849802107000d00460311280341003001008801005403445040040301000d0460108828044600a40f0b040c00214108001c0110980c1245103203254200c0c400014412244240c0c042c5a0040d40603040321502507c4202001c0444110b0b80202c0c002004550203420b96521400c4048a840060410903620b040c294145e60300c0b03024074050260b852201002a000601d0250000d030148200038000e41c00034202410401e803a02e80c22124140403c100584140081e0b20840c100d0301529096a5200c0c203040e580e2485010f50a1040d030035a106290b03d0f40145c0100e0a510010002003203d80c500040e400d241803a814080115811452200c0e0000101080466008121210070700f0840c038005020341e107241050007400da40da130020400c80b502c000030042007000350002400182c1c05a10f21190542c0d81400c2420300030102d0107148d20208 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 706670926 1250 706669676 706669699
    0x1050409172506051f0b1c09140c090711070e13050607120c18141810031a070212030c041a0405180417090f09130303050a0b 55
    0x48500c0140c00c2c0004941d805111100c1491480ca8000c003145100303480a0360b482d024003c070341c040042040c032601c080c000f10102c3c161a2800125960085405a103c803441c0d8040040e00c01d0525848541380f42d52011200c880403980e4a01c80b503552840a0a40c1d001d4000c401c0812a00340c0104100581210050000c042090411142845108000d0059140c1145000054002420502040d882660b0958030a4452403110242e04280e4141010060600100c1d00012084059817403c0d8015194450481c3e00f00041981c0071a05812080001d560000b20b0348090140101204129104590003000d80700480e5540341d500c00e540d0350055440d0405640a815510300402041d0080c5034400c001440e0a030400d40e990a500c60300c404c1c0c040410700d484100150512091501c0d41c160f2142c2248044074800c60325041d65000e005030051440c03841400000300300c0f21196500c0038030004802d10302501c40807090600e031b6843c0c40060080e81045011a0601000035004c5080d0700c00c0911101c4020410078280 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 706672176 1250 706670926 706670963
    0x81605040c050f0712081f03080c0309060a03050405060f0105101d03010e060417070309090902060d11030a050916050105070f0209040f050601140a1401210b030601050409 75
    0x144000a081418458180f00c480000e680820281224138000e8504d4500d946103460000c20604004060202c900b0100c035075101c0d560b4556050401380c0342d203c4c0385c80707039148a00c0d214103245001b00c1c40030782c0d448600080c10b41c24031640741e000240910302c21007c88520707444010348045940004d000b51a08a01904e039451021032064200b0400c58102750400700f5142100000f0070f094810b80316106255178001800e100801c801400010304c07810780342076081e00b4441d00e0b542c002d0440384d0324820000b6440c0c84812802c1950f81e12022100c10460110303041004005036103403145940c004413500820702d860100003c0c510380005c40da91100c0308885c02c2c43c0115604110040d40c0940082038281e9640302d100381120010303110100c2e03107800745000d0819244500104d03e4280c0c41c06005030010001010030701005c0f03100703842d8000f8480a0380c0703110700003002c4803041100488069140c480d0031b00c001944a51413660706001944420b009035070a506036900c5030380311410311041c0c440101c2c000745103000310702901c40785 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 706673426 1250 706672176 706672181
    0x105041a09060a0f09090b09060c09010f050c2b1706040903030605041103160504051806180c0406120b0d1103150405010f0522080a09080a080405030708160504 70
    0x44002401c0321082504d642641c0701000450b0400c42506959411050070301001d00007c66015581e00b0040a062030651400500b90041e00280340c180308480c21000000c60054080d102601e5240c8200c80c42c1c3e001520311000e410444100c2c44840f0941100072904071031042070488032083c5a500810802d855800074040200a03018080d003c042d5900004101d980ea52b002c0c040c4100708100401e6160300702a0141155481812905028480708200801c1552620221118120425400030707100399507680c0800c000150304402c001401c2000820010301190850190041d290f40e641c1e00040f03082407407603840448815007003c42d4001d403008042000101c0314840103044e06005800d8030a0f51401c01c804641c2030303006a800704c925945900030f112502c0c44a224403644401000030407030700f00c0c441150018510403820f002074141440060120074803801225660000d0080100329451150b5609020500340c00c1405820310901903c14009045040040d240200001442c1401460740c9480d013003000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 706674676 1250 706673426 706673431
    0xc090603031204032703060902010806011e0309081218120f03011a09130f0f06061704110312031b0c1b040609050f06040b2215120c0306050105041a09 66
    0x5030b800c10080ca1703801d60300a0106500440c41514003080c5086544000b40200000a005a040221260f02c41d0031030b541611005103d050306050001d151031070b83c2004405481915810654140d603d028028120f07115080041042d061b0300070342c2d117004084002c402581c4564294144034900601c01808610540d40c036100118401004241c41d007207120001c281141404641010780300d40d180c18200040e0708501441d6241241d09008101e1a81030203009030000342d4010a171880d11110300001400c11074a10b1042c1e0020b40b0080440300d4041800c0c03121411680704407403e064040d1329000c02a4103280010588800300c10302c0c4058003840a003004030000b400d13b98540c240c0d0240e124140081c464010344103081c003800441c200000c2c0380c030f04401404240d8185511250141e19081d00d07000c0600040002428407580390103000c01d403041d42c50845008010a03402c48800211400014800c00c80b9032411001101d1003090140b000c2c1e031f60340c002c21045620022480d6140d08802c403048049107006500306a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 706675926 1250 706674676 706674707
    0x2408090724030507020102070309060518120102090f120d0c05032502010e090c090d02060904020c010c170702030706050c0d060f051c150b031005090c09060303120403 73
    0x104080d41e00c1103461001d80c002001014880000000c0311000da5160040b141d000c10140002d41c5441d42c5554001c0c40b031610b900c544800c110012813461b408036a0b420703245018450081110021480c207001c3c0b24000c0d80180100341c42404035511b03140040c200117420105001d090009420010002d04043d2a09003041d10f080702c1c940030800c596005c5411448400309042c90034195001c2501e0320f407001600418001031000e124030005002c005500700090121182140b0986141c0b1007544243f010503500d0180c42c081c01d40c001d0010840f000241b105510800d00c00c40320b81e4410b540b0348403018007212850b5080c0d47c00801a0030420454001c0341560f00401e400840f20540546400c920001c000c007122400e820640004162030b5007004103190440c00200f00c140c0c5801d203004ea131500c56559050203580012441e0006448254400b0a0fa4080c0b01c284074590600d0003d0089203085603c0d60f0300c1d488850380d41403103807620130041802401c0c008140c0e16524800d00f5210380544491314141c40c0d8501c21140780 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 706677176 1250 706675926 706675933
    0x7151409011b0515010509060d2004022b1401080316030908012f0405030a140a1515090608190c08030c1c050307020a06020c01060518070306240809 65
    0x1180083c004100319070490604041d0b424603075041030108018040003030a2a84140c3c5010081d84c04980413140203c107503003201003a105024041380100f4080d00035030310421420107502e2014800b82c000001002611440d40c0c8041101407104400c54041a40a000b03090b1340d90302c203005020848003d00c4038101c903280030742080000c1d0b07503a400c009420350300030260102030b04010400c0e901d0000c0000300d0351901c0303443c03c0050300d0805040c100460780d640295540680301c0c02d1003402042d1340f40b100f408452400c54100c5e028680740d1000200d0300c3e020700900101488511742d017140c000b81901240c4142030584000c0c5000d82580c2020780c41440e00c030500740c07005865041d1100c90002d00e04004100400380b0703e464801800d00d1145184c640502d081100201c20180304003001013010041d408209480c7c560f500c40c00040e1a11580d22045005144503001607802200182c02d08502c10f202d04101442007440e40c1d400d200003511a8500070b443c05407411820588044200d0f103500306801030010315071000001048 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 706678426 1250 706677176 706677227
    0x90a080403080f07061803030f230a022115010c08070b1b0a1d0d0b0f040303020f1803010c0e060f18060a051e071709040b0406080715140901 62
    0x5c860482e10468015002404141240020507406024175003002200210400c5080b04540b141e8403503165403ca1030510521302000120000074941c1951510a1603481101008003407180d014461541590f10f60b4601c0b5002510301103940c0300b942c100000551009803182400300640d140d0500e0400070301001e80185802d042443c0803c6010081d001304000d5503a990f1880d200d000055154501402a05002d0f41302c442011011440d0401c0c0980c010440d4049240f00750b680d424102d00900500c002030084940000c0d0480b001b80b100107140e20400c1c8118020001c1c41c00d9000700703641c0800307604003060700404140001c1c9c1d2084504005020249514002d240322a441180000c1c11a400103c110000c100089042c0344813410201c40b102c2001503061496140c800310341c9454210040501040a0615000414400e20303191a0003002018401802c1404000e845910050311008903001c2e80c0150080d85941d2105940300b0148070b40d140c039540d42d400e4500301000c0011076000f14070318000e40894840c082d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 706679676 1250 706678426 706678433
    0x8030a050c1903120b0316060e01090e0c03011a130311010e040203100806070c03020c0409030c140601060e22151a0a083d050a06090e090a080403080f07 67
    0xc49010040c03280d81c514441d50074014131042203a400c03100082c00390740400e5051900300d800021010942d0740078100b004140000d000100c40c206070a0704503200d600c0741c400074451000b40346c80280d4183c40c0031451f042c600500c044410080c1d4068030003040c08494181d0000c102090004451043c0440185000d42c000083e150104060b07900c1a201c00424030201503080041581c2400320342d03049501d0749400343c6c1c80301146c1c81c000e55a01000500c144147d555107010020140618001080c0315440400802c3c00307011580300e140c80e04000d100d403101041880d81d4400b55803031f0441c0511010302996000b81d42c00e01e41c15412100801c510031101140410403000401c9401c1d581c00c044d48403070103004140e640d9080d00c00005041100181151003903c0100600044050121610000d0039410000310305191510482c082c408124070350003603410008a25002c110760b503000c4485000e03110302d00808282625240100d568800c2e0f0081e0241c2000400d200c24000525140b0051140001400c1d80c10f04040040e04e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 706680926 1250 706679676 706679713
    0x9130f080c1207060b010e010203030f090114130c0f210507050d0503071b030201090311041b05070308011406041505041a0a032306011b0605040f0311060108030a050c 73
    0x1000300181d0140440c0c60f50420201780078072400f000080c07130000c2d0070510801c0081d669000190010000a114200080202209510100042c48001c00030100e60400f440525100000c5042c140d81940c02c404d400300b0f081e1000400d200840f00d56000691800c00f20707800340b003800555403004841e07074001c084000400c0d50b182404134141d50300840103182d0b1540285841e031501c00d101001030080300010b020400260b038120302c410b01203075080012031401a049600017801030070360141c0032110a000446d040c903041d07404170140c0711903442030326040766036625020890183c1c580905016445001040280101210006c51142c0d0b90010f050042c141501d60351119083d000414070202c0680c0301064003e491a454001c0030079100d0550805541c0d0018135000003050400108058140f00140c00916040f00340010031003c01d5402900030002da041070302e82503040810069060b40090729410350225400d9000c0703241412a180140103614000070500256000e80102e40320503440d02500c0203d031000541d04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 706682176 1250 706680926 706680943
    0x4110706060f181505060c16030311010608150402040c0207031a041505091b0303040302041509110315010c020105040b03090708190c0509060a08030a020a1109130f080c 74
    0x190115914182490792080c2d8010b055102c0e80c02040c241045106240381c0c1d0186070b000c5e07400548209640b0700d980300d101880d00c2e03100c20b410400d400e8503100010038181d0200c0002000a81c00000740002651814503135a00c00461000703002c1e00800030301140c0146029480b007494071900d4010b40e9801c079030f81d0b21a448064500205a40000d840e80c040000700010b41c02200f9960901c030004100900f09205943c0e913401ea400040b2112440c101e03240740540d6401c0060710f009647c020824485130207075000701d60108505114009120303040c1942c0314660b000c03103002d403482811858040c0200101000c01103032511006101a07050000410010400c152840000d42c030484500c4018030340305c1c2c5481480c9103040390b20550300c43c204410490a40005d002c0c1040101220012245000162622030002d440310215520091803031000080c0031040b660042840340c402801006c01405110101080c407840020403100c1c0c14031450a41c0c902000681350700307900c0e0345d06401103a800d81001d10040b010391074108030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 706683426 1250 706682176 706682189
    0x130e090a0b1b160c050d0311121e0f04032003060705040b040e0c04050a0303020f0c090411011112033409120f020a09090308060a0605090411070606 65
    0xa506039006210010000715004400d82d58500d01c0c00d0030540840740c15004522102003100540803480d000d010800b890301010700f800030425104000381c0c3c80c02a1015507542d01100b101e0040140c0340202e2400320080d074810000807050f281850440e01900c0c822580300c040d0380c860007802448003001090000d800400d02c020302100c0c2c002082d00c6401010f14252004064404100e020041801006c0c6020240da0855401020450300e03620b45105000c01400340c0d40246402030001074000050585c00201a02e2030011007080e100381100c1e417018000d4001d0704560103070002921072028002544103411901c0d850680b5010307201000340340c41047c0425030040da460761510025a0702400e040c1c1d1145104000c82c0011540203407040004440175005260300e02c90308513020381c0d080a0781d0501440394460140141e0007480845000d458001440040c510154142c00150100001a003d8102030310700740250f9900381c0b60281810590010403000d44011041760f00008000d120300c0300001c0243c011034000e001ca = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 706684676 1250 706683426 706683433
    0x7050f0a06020c0c101b020d021801150302030702120d09060504120e030c0306042d06050106030e010216080a0905030102030a06030b1608150109080d0c0203011503020306010506130e09 81
    0x1800541c5900c0c0450b071155445c0f04003102e20500124035000518801c3d84d01d0840c4100843d0398a500010b0880041c0c003001a4000003180341c1c1409842d02c202145058540081c90200a00040740c0d08070202d0000304c66070400b50b400302c0b54141141389207102800300c000542c880840e0020040d5200402c0d5101038804071440c4800303081202507141c000c1d0420518000650003400d0300c0c5490070000303581e02005880513000c980c0048065a100010b240e04204002c200c950303545000c482843c041c00103100034404c10000a1400a00303110400060085a1003a0350074603500024a005841d0208a54401940e820501c06d40c407000140c01d4800b0b001a500c40c0404200004000d4610305181016110007041c412810039a596105c07800d1350000d0169401c603e030000b407807504590500c016661000c080c3c001c0c456034440d07140001020365201c1c000354030283c03003a8004d015418020710440200e84e040c2c040250705800c420014001410005c02502c651000e089860707620b2580c488081e410340710140c5400348580c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 706685926 1250 706684676 706684687
    0x9070f12140f0d030c0c080301090e2109041d0a062a0e09180304150c0b1518100b090d0c0303170c091e0d12090e010b0c03030c07050f0a0602 62
    0x9401d0301c900445e1070702078104041c8480701e9907264209071105000d10002259100074403004044104400752014035241103002c46910038805050b03441d0003440c1820f20070707410090195500b4445e48401d130140c4001c0002000444803d0743c2d40e2001d496036540702001e08460b1503c1c015022010b00101c0030f5070803941c9076a0300b0343e4602001c0c4403e59200500c0f00c0300000400074110a413100c000211703001c65008107105c0818901c0400111984201c0d00405007140b420030044c4084c2021000b401c3d42084002c45080076000b41c0408041400f6604890002c040c100300c0c0b004201d0b5040c0c040040c1910080204911502c084940d200d030000c1c15581c00503400100400a43c15900d0244015180c000081d04001400c01c9023440024a111454031036411045003010020203031b64503880d0b1807031070503540400301b4404402c050382c00800c15030140c0f00d508a040c45a400000385060348408840407036071110f0107540755130303100500800c80e0b0f840b8000840c7c40d4819540100c28882d4280101180d40744a9240582d440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 706687176 1250 706685926 706685953
    0x16030b150a1403011202150909010b091f020318120d11060106030b091b1c0b1005090a03241812080907090e16081509070f12140f 57
    0x240503402c04400346040c100010f00105900200c81019543e0441c0d64203050b41042c500316210b4018206520f0700250108004201322504001502072170009852224540a801041e40d4000c4003003010a009030f0020403e10fd503100c038031001c044501001800100d01c25064410b4039140140c1d5210200008842402c0b080307107814280161401802580b8050054441d00000280c20b210041d12a440c05003440d6030248910007900c081e910b1100c2c4034805c0c403000700640d0b00000081d2007a42c644521507000c0039072403c1c1c1079018109232603006001070080d002203425030340d80d24de0640c0b0889202c0d003001944180e85003500d10320b00070012010240045040e42c0466072804c415114440e4038100140681c08040040d958000503910b011102c5400c008507800081091071820a001c00e81d2500c4441000c040114144d040018004480c1c5c803144000652070340e0303144590780c60b030201c0c0c000c5422262581d1020040700b111007203404074413406007805465100c581d01d002d92503e1b82d245071985140e08810204c8010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 706688426 1250 706687176 706687187
    0xa050105060a0b0304080a18031202100c110606060a0e0307060e0a0b03090d0c08041208040f05090103020d08030405100e1005010b040f06110c03011416020a02010816030b150a 77
    0x900210f01d4450841c20965189a0507000e80c4e00600c3c1044007078541c0d902c4081e1030821480066800625000b28640c11034002500c070030301d40b10300415482c1071043c09010984940082e1922040c0c0d6005403405481d42000c108083d4082252a403c011941800c0710f403556050205500601d007070f8944280540c10003092240c4035071940c0c007a81182e88280108150300300c010030740034518681803030124a8840a45403c103014007454110b1915441235080140400211000502c291803200c1d5401e030500c0d56500810210110900000350082c81140740c400001d24210040c540144c4130f14203980c103500e8000c1c800c0c81102d400203c542032581c4401100303c001c840304e10036203003d0f0202084161400b800c0007174007501201039204620030001f003498900343c1800d00307000403107003d00010020b00205420506010398840140c0da0300b1513682c5104803180ca91400004c204170045d5040e1540003141c0d65200207007008010044d400c80900d501d9a420354400d40d03546103030410340015000b50076114917441500a21 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 706689676 1250 706688426 706688429
    0x13031b0c1805012103030504051f020a08010f060c0f030c020d03210b150c0709020d09050f01061a0d0905010c02032104080724020705010209040b090f2202030a050105060a 75
    0x44c0e005121600e881c001e106000092005405050202e82500c9a01d00725240032807103040c3d0041c946e001b40352151400c119800900030f035107503565500000c2e41c80d1001c0c0c0107805081d00c50a4041594943e41d0700c000f5a2900a0462581c000d040c400b0981410345c0108081c0303441c041003100012440304c5406a0101b50b244902180e418520003084150940008500d200344400c0c107030700c007440000c900c0c61171480303042000101504040c00c0941d100d00b42e0300340d0701028003420340c01107502c2e014211182c2200a0148105006c440d001c1c050441003074950802c1240c10b601c0f0b062114002d60304c2d91082004140c00f4002c10500c05603503401955a01d4100d411115008a000100206c0f4000703007050202003880d0708141c4825a80100440f100b40081903440306400062100400136940085048828054103602a0581090070f440034408a82c0c0030013001a00139080b14060105140e00e80032800c20410381c81c00c4628907401361a4602110004c0c0c000a00d007014003030007115243e4403441045030b6410302200150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 706690926 1250 706689676 706689689
    0x11512020901090e03090d0605070905030a0c050103050411060c0d1d010c1506030212100f0c0c030e0102010b060f040f0501080610050703170f15030613031b0c180501 73
    0x1458648035400038100380c1062140b1403085844041280c500d54080c01203c845000060940d03c0d001d100c1c2c641003000c0c4c5030441e1080081000341000203413500380031440d541f0090740302c110020700604040066004103000340043da040c0181c00360b08203658444800400b0b1018804005080c400c192140044c2900101c46503800c0c50090100c07298550390700314076082196036011081540b002d51111008000b4120703540083d6101c11100a040705003036005c038440c4440c441c40c103c284044100c0ea846c2c2d009079555404c4413400900d504d0420710100f0320509002d044440e0520000c00d00c0030301640029170310b4100c010100400301c40018108401e2000f00c5900c0d0040c07100303080901d060f141c0000000c51130000c6060030020f01200140c440c0406105d0140c01d60391501d917203c00c19541c101a403006086c1402140e286c034040140445051407481c0005506100e030000f030503481d5a00741556400c854150074030384c0a811251070350302c6100009040e45405006045200211131105070350034091001d4440607801070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 706692176 1250 706690926 706690949
    0x709060b120703021813090c031406160c03051c020a0e0301060e0103030203070f150516030f050f010504020a0203090306041a0a050c03040605071115071710092c0115 73
    0x10301c85d80000690142c0d0002c4c11101c164124102c0c1c102c4902501e02024005c206454084002c003c101000c0741c08038119541c3c20450311a941d810005820305a441d18114000c100074907040c80010384900005d19200301c0740280c004a840e8611460307410b0782c0201801002164031128403031460700342485118024a007081c8030024a51458074065101d1080c4a800303010038034004c00c0f001c01d12840400d0400015085c0d00100715520705541600d086c03000142000d800a42403c0c402c1c04283d50501600e8001d0203580d1381c40710542d1030007003003000a501141c02501580400d02c10a1841d9074103100041c4034900826140410082c00110ad0f06940801050f2072503e81c80c240500101448803429654810340c030a0002629880c1c90105540d50003116112007014480c0025102141e0142201c3c14007842c9551141c01e10707043d801e171344602c2950080321640140d026009013000004419040f40442c001111011400c4440410803426241500003410b4a05e0f915007529403240d20404440030010182440c02 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 706693426 1250 706692176 706692187
    0x3060501060212120c0a180b07020a050303091315030c2418030615030b0a1d0a080706091a0c0304230d0f120e07050901050f0d12020709060b12070302 66
    0x50158030068402c40c078a11700420340516250181c02008180303115a60001035407941d55503480380c6030f405190100c0c040e481a000008440c2800420b031030224100034070005182d10b42d07068810081091403440d030985100601e002000c01c510741486006411030003901110307411032040d500703213508100e86041c040105540b659440c01000e2828013040ea40e02030804035903030804144110901c050364101424400f00d0380240300400300141c0c417901510340141c031074175079a2001c99501030712080024000703010840d0800000001495650181c4450b51183d00c1083d901d80140214601c0b850080b5125180c07030000000380020310005007001c9645110342e02607401c080303010441407070300c03500c06030f40740030174480400230000c0498000d2070b20038480ca080b8241005160a5418406e582d90050b108250045980c0c00000c01c0740c0c01c00c3c52020790000f0300645a6950781d40245d4428850010170446842180220b20011996807990b0041c80300902d549152252244501c404010303950724042c1c0203409041c410400c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 706694676 1250 706693426 706693447
    0xb01020c09070e060f030903071502040612050604020403060914070e0c040e04061b051b190f0f0b0f01090b090610030c0201060519210f0f02060904050103060501060212 74
    0x1400340c1e00c942c00c0d02d0310704415441d0001050301030080305840d503243d0001008016034000000b01400400303005040641d040102c000a0b00201c1c800d501605000440c2900014407009141d080540c0000c006003005280517903d03200d0b0411108000011602c01c20002112031221104101c1d0750050000ca001c2d1250500713008500000501c618032926805005200c0050140000b0340d111800e100e0b940022260140c1c05941c0007002035014100030842d001c0041d0552502140008002e801120f5807541e44c0f09000a13030f100c9100c8a14001c100f11068000c0c207203c2c000051066880902500e00c881c003003181c1d941048521402d82d0981c0307982d680112094ae0401125a95200d01d02102c4aa10b090000c0c910880c86c0080780036215a8001d41c2d00404500342205055100c14074040480c1e80c807d030340b40d109100d9025030b11008854010042c02000e640c070304000205d1504031300707100d0007440101040e03d0841ca020100c1c00741d8800368419134900e030303480700100503c0da014000f0515015100d03c0307440c0b8040c114103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 706695926 1250 706694676 706694689
    0x1d010509220203070b03091b03030d0e0307060618050a020306150a110a080c010501050d030c021c140109120e0310051b07240207030203090f040f06180b01020c 70
    0x1c0caa210440030300d44025912400200c00c0202042c0c01600303881c0304075142d50032440c10b64005c0d181c11407103200300e84882680400403035141540e12801400303985050b20741c18050002c0c0000c405600524041041041c002542c1032003910020440a0a200070f150083c046040803030304000d01c10320100f40100104130560743c0f14507c0c038803194081c41503192501d2040b08125181c201c0104440d48600c1b41080150901010313002030852004100024403c5a0301c0b41c4c20310610b031700c1c2404c000303010800840c0b038000145012048150026804540c400600074a40c980e42540160b0624411259655407070b0b807024414404440d1340c448505040000d034210049012a03629003540605048031030b91500445d901f0090b0395108409014200340c0b40391113541c103081508141004d0140e065402000b22200c01c41d91000e402560350042c1c140e00510b0800048106100e80c181c118010940d200c0e5950b10a4601c0002d54032528003e00813565100c0c3d501070314a48c4140846002d03000d000c0c190741c03201580405680d03500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 706697176 1250 706695926 706695931
    0xc0103020c0a02042c0c03010e150103080a020c0603010303031401051c02090408040b070305040f0501140a1d041d2a12030f03041a07110705040c110a08041d010509 72
    0x1594005032240d0030081701d000c00b0302c0142c0c0900803504402c940c98007150000416040040d0210020404035145003caa40d44051406641240c82003100040010030726110250420300104c0c010349411071084800030728954426001240401e99030710003042401d0300841818007400c5d0a55403081349408075800c2034400150000000d04c07549034840000d040000100984004180000c100e6484200a01d80544583c009001d002c06001c600710f00014103601c6020825840d040c151440380c17810a407107200b150301c610310048002d00d400c89164409426126807240405498580900c028410314203402c550405140114415101c83c200042c0c2124420b0700c40c0c425402c80080300d2001c042400c10502c1411405009000c1c25400f03000300c2004240032004007611038103603080d01c03048090345c0d60f0341082d41c0704468050800c0260340155420f00c15410142e001968003c0c4038186108003443d20b580322854602c4094040b6a0800c0c0407600b00700c60b50800d0841c1c6400510005194003540c104804590550f100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 706698426 1250 706697176 706697179
    0x160608090708061b1c090b1b030a0b030109021002070f050d020f040c02120304061b020609060a0513080d06080f070819030e100201061a0a08450c0103020c0a02 70
    0x818041d04c0b00003104800301c2d0404003903200030601e410420303d5004020500303044280c1d00002d00c000060111441011000c0b04480d00c036841c1030071501c5d00070380e41e0010321103401c078503030150b50f24154680541e5480090002d102107543c0145225800c00803088140401c9a0004e40150001d804040060380c0701c060710000c40c0000d650001d41d0300b0034031004074500a41030705041070f00c50b0300109200c00d2003100c0d0000d0004078000706247e6030040309800d04a17541e0400710380c520815000700d404603050030307903503044250095013650030640050504d44900b102036000d522442d07030456858a042000d001e0501405450900b04c1e40503200240c500342e41561503503100e0746484412540702e01607000301801040c0301030b500c81000d006c4d00142d14000002034000c0c9054007500082e02226100b004001166404644010000e5034841c04551603041c10304201d41c0f24291200702c2039810908402e0143c04204030b58040318008418a940c0d140001409800c0c4406600054109401007180c00c40400c1c0000e2140d01d00d0780d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 706699676 1250 706698426 706698451
    0x40b270f060d02031f0305030a020606090c180a090c030504051506010f12110d0e011109030a021c1e0b070203040608010e040f0203101508030403111002030c16060809070806 76
    0x598100348841705c094251100d6a014202c48044107100000024000c500c4298084422507112141000030804080319000075030070007001000e4084800c010766001c6680c1c0a05010720542d22403501c502a101059803040009581e030040005000c010400c6020b508203d007038070240b6040940009240b000504016804c1c040c0c4491120040d845641c000300d42c180c18031112545402100785040042c00007404903030015802c042e0091b08aa024504840b000a0003d000304101a085d07400d01409059584110100141c40040d000c08180d40044004ca091a19045a0381d10f0181e0301e001c001c4084060504400c551007400203010303071500a04000c0c1592500a1010010b03904ca00d45035a0300c0d154400000e400d03000d56007000d49150703100d4004a65030b1080180700c00c4100d845207280e559070701031403202030f02050001c0319683c864245100e50402c11010361040d0303803a15080c0030312903180c5464981010090124107208101a9500c2a02c003900300c070040f0007418070246448005a070729500900681141d40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 706700926 1250 706699676 706699681
    0x60b0418030c1e08040602061f1503060513020703090b16030e0d1401050604180b010909020a0b0703020a1101020303070c021c150e1212010303050d02040b270f060d0203 74
    0x400c510403603d2920205408000101c03444c81c1880c02a0032031311400d0090b21a41012072260000c8904101a220319045004191854101100400c004d01500441416070b40c8201190f180c40d001021550200140d90140c0d50f84024074000742214500c0d400160300d8030091290461b05070355210140f04840d0149802860401b5510009086a1000d540140b2918608001580429040d08550b06c1090210f0301048200d05800310001c0c03110032128020f00c40010b00340103101c403103090342c006000da0340003400b403140094540300d44000c640d102030b20540160f80801240400c1202c003400c4446130450a101543c194100110040d00001407003600a206501c5241148814403503203000002583d0045a03050700c84001d1000e420050403d00b11300c014601618031020780c0301022204072200c0440c000385820031a0b04e580c07011201ea400810319804074680801001541c00107503005000783d00b81c0101258201d48205105d901e04080e007904107070007401200c400908c030f90f271500300b507845080350300c803000d6582e6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 706702176 1250 706700926 706700933
    0x215060d0311150f0603030405011205270313090b06090d0512120405100504051b06090405040605311e050708030c070b130b0a03090c060c060b0418030c 67
    0x10788074820400080e02c2840104110008031a4005000c0c1041030030f002d04517255113060546903c500d0040d50b0200c0c17154404000400ca03940d101540c00b50401d40c5c217221048400b0b9500031100f0040d100184d4a910209000300400c50110080e030003495001c40400c03040040c98085002c03401040406441003240f403074003205115040c00070002d0749000a4030180c1e82d02442107041c80307621341500c064a00e07100308401404001c10504c12680140d030440700408640c1090b11800300aa441411000d80002e01844810040d45544c090301d801644126000315191801c25100c001d0344800b014a80504aa00da043ca2030b030710100c60b1100301054002c1c420003102480081f40015503034020000400703611441030b00288551020020b02441c0246030305a0b0940ca80c1c03010303800c7e4203000d01246900a4124030b40d0070818102c3c0103006105000442c03c011600344840e49980450741d045600600c04070341841c841108124003407081c0b0501142c225403c000b202914a0f044a890106100090510220f443c450060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 706703426 1250 706702176 706702187
    0x18020109060e240d050a020931060f050102160302060d020d06081014130b010b0d0f052d0c03040f15180209150f0910050904050a020a05010215060d03 66
    0x2083c00510940d503078160104202401d030350145120382c0c407080c80c1c100070418008a034002c890404400520071010108010900e6150307030724050301c840c1800c2d4a01c01e88020404540121001000c02c0c00d25004854500800a4240742c03420007140c6030100401002d000507920ba000399004550354441c01615140d90b403400d14001e02c030540040105d403003018503c2c21440380a4101400340700c1c084030501c100380c5034980d003e08a0014a20001c140400000062010341551000341101610098010601007042c000640c22140180c07800d2401006c60345c07660f47d815001d003070825070301c1c60101d103581c280c0c0c075101580c2c0a040c000504000c00c4051011850010701183e00084030080000c1d042c03c201c0c100d2801010400840420012401085804005104807811400c0358406040c0030b815a108407100302c00700100c1010080807444140d00001010900e6190042010b00c903910a60050021020b42c0c010062200c4881d4400760440d4040500094080e0496414640089041d580d004102c4041d01d0706441 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 706704676 1250 706703426 706703449
    0x8030703060b0706050103121404150c082101050d1e03031d06070314040302060a0504061811040e0d140d09060f0504120305090d08090f060705040918020109060e 71
    0x9089901083c40390610205070b1003e03041783e00c6080080100c01170907405507040c003a0000c4a114029017403004106510340d15251160808641c43c0500d0480380c1940c5c0c482e003642002d10340c2402c010720014400880943c03050102d015000440d03140610f1a05582d40e4200004600301051a0508003541201010b0181d00441c2205602000d403240c450711080300d10b41d550400f02ca890700001d08020181e01030003610501c40b80110b805d0390252803180d850000782c002030038025000f01c601c1903540101212102c250000c0124280c4500d0845000c2400001008141c440170506841c45400c40f604c0b40104580107640c0c03141c05410b580c5055152404264104002c01907074030054011400c0006a5401c0c006a03070085101c0d0344508100315104403000000c400300c500c00c075100120340d4803603100d14280602900302d440d8000c611108541811003010080c60030003806403858000b10710081001d00c0180c0050184d907200506280c1c20308841040c0e80c00007003400c80a885010b05201007482c480204d903c0c3e1b4000c420 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 706705926 1250 706704676 706704689
    0x15030603100929090c06040f0b1b010e0a050f06060f1005070c0e07120504050c011103130e101a040e2212120501030f020603091f0f0c020c0a030803070306 68
    0x19903820f0701590055401c4111503c180b14001c6200b2100645815820340b002d0742e0302d040641c00d440703003840c1c04285a40c0c8282100107030307486000c111074180c0600740200d414a68000380980300e200c03001d01d00503140242012007a0125041102007040c11b032101102500e510304101d1f0340d0703140142d01c228280e4a074414504090503d0651403400300d015524115614003401e115550100b40a180d003500f241158000c1d18010590f401043c1c110f25a5031040c0d640100d07603403951080da840d200001513144090030b00da078401e040c450558010042c84803059070a0030010480500e290608041c20b6140f08880c6c4581c2c001c000303090101ea004103d140c1e81c0c10141c80e00f180215a500c90503032081e8180411020381c034200410000d91311302415100007040b80902c0781200d41c0100c001200014075401c0241a0308024030b60611480f944200195000c2000002d0700c0d5041030400010700860b500c51800c2c1501c000c03a081c141954006072440801d40c0f240c40707800040b00d0f0480b190070384980312410200d001d400c9960051 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 706707176 1250 706705926 706705973
    0x18131e1202010b150a122003040f03032f0d0e0f0a0b01080115050d020d020306070302030f060105030106020318031f020d0c08070203160f0209010b09150306031009 72
    0xa9540381c1c0540c0002c6503280c2c1240e24030300c0c6507000c1022500c10300c90000710f0400501c0031000c411884883d50014001c010b402e65251241c0c0c0b60144640c41c2a803c1201c007920700c2446075507440c0525415100310200007800743c100f02491003086842400349462040d0028455100242c0c01000082a61050303010203500720507035403134440b880c01c4144d4600c412002a90b03c030b69407900000d80810148142c8144611740c00540307445602e4803042103185140341e4803e03031700180c1c0c1c06560801603070305201c080e1050020b40c50068503420705c0c2c081100200d0004004a0622400f00b0042c0a1207400100341c645031000312090020030000d11010078100001c10054981c440019a07001c203c285481c0c001e0101c41c01c40b28810001a03018800454480e407040d02d040c00560410007c484841e11198844041203020340c424040c2444254081840c2100c00d91198410507008504961240303031a074042050006000e00322411828610b0019803207030401c0345056032103a40d5103985401c10468803449100c03215491140f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 706708426 1250 706707176 706707203
    0x80a0f030e0d051f150b070c03120906090e04020112051005040c030b030c0f0f06220909030f0801230123030f0127020c0118080918131e 60
    0x41a0b590400060502c40213400840008080200d4401d140d00b5066820140269624124024072a9404490142c8441c0307101d0102001086452000c5c2c8100c040756074034240c0c007500e424402403440a1540006000d40544030600000d82c2c1d1150003042c03140751941001900d62608124948080103e60103550058107103518008440c0e090741c4540d95120003a000d680d40308a1503800c0000c1c40449040140c0c1c00440900341650a0030184041c00300001071300d42d0103104003031034401540301c2070441e4000c0301d0080e15034003444101356002041840c007d8090411502550500742c0f14100400d880904800e0000a5500600710b680b288401c40680d03641100c505051040b204400e85040d4011134500060084d000000980464091030000029120000307030746880841e06202c4001c0d600007440340302c0c19900c511b000d01130060b02c10030b0440024480c81320603941301e000e0000e00155100c030101d40d2040c41002d504002e00301450307032a6009070315844a000342064800035640780103200400005050f421070401d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 706709676 1250 706708426 706708433
    0x180c06091201050916090e030d150e100303030c08090706050d0204030c290316120b09090105070809030903070504020904020f1b1c02030a030b150a1d030304080a0f030e0d 75
    0x40b4111081000a5001030041d114517814060310059140c481907640304001c271520500055108034203041700c5243d44002c0d51340c1c403000e20002c0c400a5850890282d00d0b10010010189c041c490b40701000d00340c0c01c1104013440c260380410744408a500c11181404070010340301c3d030080d01c6541224007840c5d00000780c03140701741c60328034002088205004455041c95980d440400f9106501c0a59108409030081c3c41d4402e07503145021580c0100095000000d56120140705030296140b28035a03105e100f50030000603292408100003814500007905003000c0741c00400044100c0e880c04101c0f00151901038401582d904880400319000f803141180e27070f0000f048041030010392030909503105000c480700102120310b95240b281850042403400079040d005640200b20b240701050181e01f2668000304001c00c804505038424140070314076400f1121000001c1c0102210b445007014900f40380551040581c019030410b82060f00e6195a000700d040003901080302c1e04820400c062080c40510100749d005404010100031624 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 706710926 1250 706709676 706709683
    0x20d0f0525050a09020415030b03160314150601050a0c2613050a0e0a050a06030506090d1b0201050406271d070315060302070303111b06180c060912010509 68
    0x2030300c2c840c5402280c000b41e40300c40d07402920305440109400d91010b061680d0248c004107028848550140901c0d83d814a080c21a40140c5001310b0140d40701051419100381003070b0805403c0d4081485000a283c140260399034400140c4040c1d1910381000308101105050a1001c2421011090300801450945620a40101018148503240c01480c2c080403520748003040716010302801a20f184c1c4403803100241c0d01505c0c0b9002580c2110541d0310020300c1644a413501e07420b010003203070012640da0002070203c01d5103600050790b0511031201c82c1c0d44900c0b4451940001c100e44200d1003801c0c2000841c502207101107c0d2403621402d840d0174240710012a40d540c4502c128100b070300811005084080c1400200c0d1103010303020b0411905441d081401041c0d0404078123500a4100d0700084d801c0642e5403043e60301f021302080040c1400750844401485c4140c080f08054a0164010407204a00001c4442d91309040c0001450035011802240e6007034451003880d010600391010018101c40c07070b60a01c0140046400c010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 706712176 1250 706710926 706710929
    0x10f09110909030c06150f0409200103021c0e070803041203090909030c06110f04030b0a0e0f0a02010e0f0301020a0e010908030c060f0c090904030807080a050103020d0f0525 76
    0x1c1d07800201c0c80da0794a031080d40700d0040c0e05040c0c601c2c0d0404000117510b448151000c1c00e6901004000c20030000c0340380e01003801c9803800e0904070b50f1200d019440d07804601c80d4010011081c0401d01c0c00794602014502e0480000315009900d01859440f10308541c500c0209001d4480600102e0003120380f5260740c0c5812614040d0720550903404140c24400c0400c4002140c040d5004407038054072100303c0004696554030041c94801400180e0980512079801e50030b8401c4010001503000e0700031086a41002003180301124420009040654400e968524408001182080345d03160242014100e410188000c95001005100d01a90651001800020183d04076480d007905410070384e035921845483c2e440503566071180190030b6038a50320204c0011040c00c0864225503000180b0720446040000c1d070400305107041415070b01180810071000820015550200400e94090303d8076500744450351440d00132070b0800200d1003010380b800c4d80740f8403004c003403000400c6801c0380c1020b0102c1900c40188445041c0c11411243e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 706713426 1250 706712176 706712179
    0xa170307080109060806070f023c2e02040306020703110c100512220503040303080f041505090a1e0309080d0906180e0c0304031704050304120203010f0911 68
    0x712800843c001c205880740405403095000106601e44400b901a03508441c0b100350101184680c00c0d440b20380390f028083c0c886124811218052408035010740c9444095260004003045500c040040b03904150780c410705c2c0e10f4036400e20581d4a0303943c01c404548000b0344907607040030381694000a05d46c010560b000c5a250304076100201611005000201005900b0f180c1201c1c0c0300025406002290210161084403904004140300c88200103e0314600a03c18010605058903142c00104080043c0350b04118031581c01841070b1100d181030301e0240e03921001c1918030710320480e44942e60400508041c00402000001c50741201d03c00d0440c0030303c030054000350040308508070005403540c0e800041441e40050072aa500071203480e40b19007030f410b08008136554094403503581101203030740178002050008201c043e4082c00c12403118a036a807900b8100608040107207c2e20b101011a404100404038602009441c207440b04030f00500401034850000a0140064003101007405141c10074410400042914a5040480 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 706714676 1250 706713426 706713437
    0x18060c1018110406051f020106030c0603020c0d02070843051513060c0503070b0405030a03050903090a18060f0e070f0801080705010804020a081005060f0d050a060207050a170307 78
    0x20b420148410303074525208907070b00100b10354510380c3c5c240350000240030702c03080718400001c0c4280d03241c81e80300f034040c81d940c02180820390000d078825081500f8410001700941500042a44610342880640d80744a403441c400b10304c0340705809502c4040c04924800d466842d10f00030a40c00140e084030720030000c800358450b051281c06501040c5802d02428016070f000401050344c0943c0080c40d00f40141c4500b4a81c12003140d043c003080000c0c034001020344424601a0340910010b58031540e80c01030150880c0c0c0090003032a80b941c0207004200041d40e0307155155040d945401c0c901a5013052a400c000e018005640151940e03801c00e5102240b1a02c0700384039a48680342550b41d4200860900310140c58080084c09041c102d500900d50074806540941c04107600300c0e201a19a81d10240d50f002c00130304008207800e06000c055111001e02c982c61500100c0102d003402c04450000340e44443c1d85c1c0c0c10399203d4009100034101c5801003a40c0041c48402d111810019030090b5120351461418844200c01e80d00458000c0c000c00c2c1c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 706715926 1250 706714676 706714703
    0x9041a19090533060f0d06090c0905090417040f03050f120301050913170307080939040b030706120501080106031205090a083018060c1018 61
    0x10314550303e410300201001001a10b00c000949001901070901c401242c001008000b0801c42100c040020400c408001100003040d43c141907051007510107050500c8100700f5044401d100d9a41c40319000d40d0842c0c0d0003499100424480d21050301c50307000703e61152042e00203402e000001d211000c511390411091a0091310300c8044401e420300d0f1940001e015881c1c1085541c000907607843c89440c85952558050810343ca40c42e1804900500c081e402244c031500010400c1091050100040003542699081c00000c0d4107203a849030034440049070000c0900581e9106a094511561140d900c10400010041c0544209035242c0c1d8000d0b05201080f0410004149003c000041403441840703a0016170390f0111140c9803518000e00100e40d5500f000c3c1c9415031103520f0800018480108000321584c648101c00c4a0340150108040c0010042000c10078100c030420801c000d0301401c45841039034108510403100280c680300e0b41921189464501624910711350716084040d404400100002006148a01444039016 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 706717176 1250 706715926 706715941
    0x70b040b0c120a0c0305030a0906091202060708040209280504050105070216080705040b06090315011502011b0c4b020f060d111c18030509041a190905 66
    0x14828000f0a000107000c07145440d000034400e60003580c000402400219032130340940c40d500c1c00c5a01d80781d81201c5421401c1d409940184d014000b41d544880d960424900c0744c030b00364010070403c038001440d219000685000f881c204800c011440d41081210000820440c0b0b02440c1c420300900060360f43d03d001d84180a030031014000c40308000c00039501140040e11030030349460107100140403110496940038000f480300c404542c6003041062040300c0080c104948951522410403a80d60110509404590401c100c140141e0203840100094080030301d400011510b031410021041809107005481040c1e0240814a61001e0003040200090305107a0b050703107402d0704000428210101c00b80094000c401b02c502030081d460070b1805064040e081d06004111ba0104004000666011400c0702010810212101d90600c07028400e04030180f0815030181107041c00b64a001c0d0840c0601009140302c0c5031128600012503020140c07900c41c001e0003500014900d10529a05007501030640940c400051a000000c0e505 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 706718426 1250 706717176 706717213
    0xc0408011125051f09080705010c0306050a03021e01030b03160f090203090c090c09031207060e060405030d0f021201060509040f061203051303080325020d081305070b040b0c 76
    0x7007683c0030005052103040d15103814282e00051403660001a034800f2220080b03900c09009043c2c4511500000807404000b440c054101ca8150b000580520f01015041c0010b0303d5007400c0340780e054501c07044400140c000d0b0780103d002e0440411015050301a10701038a00c602008060181640c1c0305141c07664155403a900d81100b01d0104581007c159481900c9000450502c50300807a0801c5501c9010b504c5c0c90300302c1005c03916229141c0e081403007100d00010340c1c00910203a8807500c45401c43c207202800507030800d0703180e6650324015054060740083e40c421850f40320151f694100d821203014554000507540e5a040d01030001e030003116405000d1400d081003003098a078248181c1c01510f0802144600003d01510f040307481d500411100150211110b10120200d00240040c0d8810070f0810000640240c0d00e45c48109081e20202d440002d550280e981d9011050300400683c0d070002c1040800100b420150600d9860500903a21541e601c41000a0220f42044818000c101c0c03000c41008444446a218011015 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 706719676 1250 706718426 706718497
    0xc090a0b2809031103070905190515030715050408060a090308150a181e02070c08010e0615030a0209090c040605010e0f060c150112110d1a0c04080111 66
    0xd42c000d001440080d040a0041e40340e601c0150032510480d440c1c001d03200031204d0a0302e407540f10041c840720b8540d0802c950700a15900103201ca0072140010b5145003c42c2e6684a80e00640d03110300c06140303050360501d101da01a41d004000b1001244c4036810b14400000080c010644c0a40c00900f55400150035020001c1c600216000060030b5105018a8030740740f07521084154034007030100b6858417442c207092150105499400c07103503c3c01c01681e40d80b6030710781031805180d160302840305a41040d2104080700c0703001c00c2095002c1030480d150010b02c1c8150f80001e040c2400d40e84003d6200b40d50328240b22011200244900447c0015030713040150548580042d1482d030010340c01958040550080b24046042c00d0003c0c00c14403100a04803030303800e07402c0201215504826000300d225074142d01001018007590003003c4160340ca090f2110041c040081c0c50301d00c01c40d0000c01c502c241e50030240d400305030309020a001f210300509031a0001c01121060304c41540b45640080d0f01c010f161000c0107098104000406a40702 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 706720926 1250 706719676 706719757
    0x102916080d0912030e0a110d0f1406060a0608060609010e060316031112010b0d09140d020d0e030a02210318040e0705130f180b0a1406010c03080c090a0b 67
    0x46c9244980d54160440c1205080c05401c404845503d2001078920303010b1f28a0948624200c40c02031708002e25051400310002c0c950f500c242c4c6441e40400866800001141e0000070503250985e5503941c000059480000500d103058203e10700100704404107a00c28402d007008801c0d50740500820300d0602d100c002d00d0007500c841c210f42480d10030040000341d80003801403540d90b03800780d400708010b9825101c00100d070309111850241501b0ac0c15088880e0799042c0800340c5c880c0100d081c10490301c000341020940d90040d1440081c0117110407140e41507204d0804400400003040707401201d0780d5400d0320f01c0141109042807001406641030460442d111000071541b4400e4400c06450940d82090501441000c2c0c40c0d200302254240c0d40c1e030f07042c1150708921441c0c0b201c40c2c80d0040007034a00d10305041000324100e80c0d0030003400700e121883e8030902030703d81c2e40060151050354051400142c180c581c99540c0301148901280564444240c0e0000034055030f081014100c000400e00da664861201d400c030000c1c001c00032241c0003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 706722176 1250 706720926 706720933
    0x212011a040905060f0306090304060f1701060c030c14010213050418020607060905010f0b030f010501032a050406090608121e0304081b010203102916080d0912030e 72
    0x74444010b455000c1c95001100a00c0803014000b00c8021038101142500c60324001c0d080000c080c020a82c0003000c0e0300091780b0510380054070301c103205000818501e0601a94040100f1801c2c0705080c184a00b960000d15500510001c0c0d048140301c403028000e40c8518411140394101d07020000380d80c5003d2048191500c5d01c0030304000d4910181d07082040e141d0060030112070b090303618003c41000c21001d1080c09000c00c0c40400000308036610398101032801c0c03010802801c45a041000520014007454203006694910822520503c4160021344540c50200e03000280c01510b8070b080001c03e6030068028808441100e4140c4c0d00682c0a00e016042c0c0c0e00c50701e21059400e8500d8400c11801c4101e0307400542e445401110b0041c204400005d8108100c1041403441e03490360740100c10f00000a0b03115114000400c402d45442703028841020030711b40780482984280d442d810002c0b62120440d0101c44203080707240e600c40043c82d070f114015200c81340203040012064a12440300368100d9a098082d1048856504108004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 706723426 1250 706722176 706722179
    0x105011412030c060a050103020108010b0306131805250f230f04020d0902030c06120606090307121505010501081e060a0506211e13021507060212011a04 67
    0x74070100510100d03484000d44810880b0303035055242441880d015120300c01001c1203651450000500d50702040c1c202e00c1c01544100300744510f99507182c640c40107031030814001151402d650300c070500101c841071002030594020412051140d00c0d1111802c107181a0740c019080c100c2c0d40719020010503040c940141005000503003403100400da0f0a035806101b8600052075206c000303001c0000704050b81c00000f1100c0c00700d84c0321441c4074218230301070020150070311059030001d09000c4c0b40c80e00c403903080101401913401140001018070007601d00340091809061010001c0d07400e540d8603c0d0008241c0b04030381820b2034181c50a40003150541c820302005000e2100d5002040031703a01c007503028010005025051603801507134050001a039417100000f034625034841030008101a0340c1031101024096000f481143e83d5615524034580040c252000300b40c0007403100410710108600791004c04c498107107611142c144814003080d11400c00c907050b00200701885002d0105c0b41980d030b0798401c4680380b054a5902d0b9035143c006000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 706724676 1250 706723426 706723429
    0x10509060709031a1f08010209010f0219111201050c07060c0e18071205070909060914010b0a1115180c0321040504020a05030108120f0a08070509030d0216050301050114 74
    0x100710b0b400c00a803606445484010b8003401240071750580c4008403994002c81d00e21003641c2c22103600c0528002c0350005e043e001c203a501c0c20038401c07030f07240701c0c010983c0b241354a030032804e5211412198054820780e40200104c0c10000c1c4002c02d40d40040c101100d0241c01c0c4507182035802d104030b0010b110ba0801503c00f10080081c00031305210941c000f0228803c005d2903a20740d00350080f0a0044c0750003880e41d615240e4419080c64540342c191141038000078115410405180c24802c1000b1540741120b422065030750b01d8074000300007111406038400b45208036102d045003840d220540c0c2034426001d0000b07080c2c0040004010a4200d0f02c503501621a2070340b642040407858004c0000c212554440d20440d0700c2c4c0c034582a11100000d08076001030740708400168022006000601c0708124070740d000c1100800345800c0070240001202c0c50311402d03080d14100010200442d050a00841c00c0c2c9030aa98010252440385103205002035681ca1002c400320201c40d0b0389803001403941018407034039068600036441060361404190 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 706725926 1250 706724676 706724723
    0x304031b050706080105041103010803090402090102030408030f2107020c010f032003070e06071e15020d0504110d0c030605061804050705240a120b0d030201050906070903 75
    0x4000c1282100404014001071414030804003c0d24443e101d0fa2400d5040c00180011101b2900344d400074224104018020301400100b5281803c604813000750380c551400c0b0040f4218016548040800d1001280421054030100302400e00c40c0004003400a403c4050031200c0c51221094802c480543c000845e03011881d4491302001800c64070605004c103002404138122041c0b0050b52820714070101011051010369580f0498150724030600b01c42941c00e180854403940300100b00b01102c640c1d0b095409407030504010503100350524034030100c0021034075482c0300c81c0400054003040350121030b90842d1900c1e15183d840c2002031100200d410412841140e403d5989580040c0307405015203500110704003540304150f26240070188114801c1003d020f26501e0101130040c036514140400c078985200300d80305051062100b080d41d0000c011444c00c507031000c0c9100040001030401c0b40c0219002480c1712424030030b06405400c2079010f6480e0208803a9a0390740d4140454500240d8080140a9003180c00704139948440714 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 706727176 1250 706725926 706725947
    0x3020a0813080c030a05220602250b0c010902010801050625111f0f0207120618080f07020f1504030b04060b040504031716052505030301030b100911030403 68
    0x100700c0580340105004040f450743c1c128010000000704c0020792103440283e810f103041f214403441041c007040c4a00b41000a5101c90740741101203206180440c0c6c41501e91016071000d001404c1c80d444041c2e5420042c11610301030043d00c0380c180d011420603000003d4608040e000c49081d005000071000b43c8400c220015403200d03414841c1650108880c0341c210710156502d06000082c10342e50240b401c5555069000505000940c055100954214000030003002c03e40b480d1030710f020390b1701900000700c0a0019140c800511540f10010b050f0725404149a00001e1102c402040f80da4021030f000170b03003011000d040201c1042e082c01d40f000d0040007400304000013032000c1707541900030f88911408591442c4000105089410440d4241d000400c0f0580300000810786001c0c958001c5115209207506001f00310000c0e11510803100075203486508060344284001304c2002d403215076907009056940d00d581d00e013002c00d20090161100c144030500d010001481380103611a803d0030101c2e100c402c60039036649031015183c0d050344 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 706728426 1250 706727176 706727183
    0xa0f0b010504141611070b1b16061d0102150709081e070306020319150f12230c0d0803250f0f0c0602070605040302100b090417040e01060e030d03020a0813 68
    0x1880400308503947e03600c002c0c005d100703008001000c250b192071814914082c01007441c2140c40c45000401d01006a000f0131048010ba030fa902805101409800101d207041446000b40c04201411010300041943c40342c02d0b401200c078004200c9a030f10158154030501d5244a0001101a602c00841003000a400360080c6901284120000c46640f808260560654482c0c807441c0605611401042c8404141e1084660180c008182c269209070703a2561102c3c40d80030480f80341c9101445c171030301071180040200000d09003400c010b00802c100115501e04054281c006944200c015411400000315090041c003040c1d0110301940c3d80e0a80030744400006072030f03651130311401d60200940d070480240481c590b03000810042d80b041038009020714150400030b04091102190001040c01d041924150341d50305400c443d0090b80280701d03400c154003003001c02d08240c840c5a00022803110800700024806400030340c1496080000c2d401e5445400200d0011000c0f4401e20a500000c150340f440802e072004450a00900010320 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 706729676 1250 706728426 706728433
    0x6020c0d061d07090608070e19050901020d0c090f12030504060f0e04060b12010608011a092b05060606040b04090c020c0a0b0d0b0307080304030803090a0f0b010504141611 75
    0x10346020b003418515a508800c60954070391204218064080108200400046a0007030140c288504407047c05581e25400082c41e50f1500c000c03e83c010720a50440ba13543e0070340c0c2c004005007404803601034140d155500c100424842120030001e030049034000750300b05042c0e0656030355241c1418020207a0344104007810310030400070f200100e5262610395205003c040c050010b01c040d01c4444507001402d0600c0160080d03000c20003500c004000686061800e4401c0c10b20310308480703894009400120341851f10302041595644441d5000c0c0e104400b0719600d0f0900c040c0964143c0e95179545190500c8a903101e54801c601140104210400107141c07550700c40602e1143c00d1040d1a22200d8980000d0300907045600003400c402e030001000f81c940001885a112428001c1c0c010304003207454050744944170f01551102819080b40000010102c0f141031180310001382c1c2c0f04c1022140030720b25040c140003da0090144500035840c005c00c164851070b01100d001c1c070400f01003003000c002044440781111b48082003c04001c8620 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 706730926 1250 706729676 706729721
    0x910050603042d14100605061606090b01150908010203070e040903020c032b110c040902061306052a07030201110307050f0102180a1202060310030203030705010b0a06020c0d06 77
    0xd5403400f00e200142c001c54445540008121055003050740582c0201e94451400400b00103a80700c850a41d070030400d4020900c040e0454908004002d0210315000416620044001041c2483c0c4000ca4101c02100c0e40d032020100c58845013051b0803484180e660b8004280042402105440c040e045900351500c00d205980c000d0328008080703072429a4503031139150030403040900000355811010981100900c05d240c4040b810183e52143c1d13450b40180f444003405191500b01090640d191401100c001d030503c4040c4001c1e2681e1070b00000c2c02600b007040c000c110311101144103190100782400310066070182034050900e0914650054074241200d042c007040c0c600081c84044003040e418000001030001178400503a40d4040c1e004100001404c42c1003003072081068080a000c0402c43c0e2400400ba10790560b074441d0b803034a80c01e54012000305c10b070384000d506210001e50041042019048002e54110903280c181c100303078450800b603031205a002a5240c00c141c4651a11000c11640c1d044100c4d40d5208c40c0c01000c0f0038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 706732176 1250 706730926 706730993
    0xc060c0c1b08010b01020a0c030b090c0d0c0513092415030303050f0f07140307050f0c0a0b0f0610030906021306080f0f06102615091005060304 63
    0x2000041001d8005100140704101a0400f0302071140340792000d00c05050000d120f0380e21010030810500014080e10f0030b00c00001c11000041003680c00a000091105810120510300040d54039907a020780f0340240b0701c4e91680c502200140c01403041d103ea01c0b02d01c1810002d5003403129500703160044c0e64104c50340d8a07440407605a69201c43c900b03002d103002c1d65001c102842d018604003401900079244030315034200e51080041c003c0c1d0103100540500381c280449662a141c4150880301c40c080c080c100300b440f00d40000c500122400c001401454240700f003482e4200c84c0c0e03c400c0c0b180c403000b104a401c02d4000e5403031005910b401d80700790300903103910384100d40040c10400312000480c1c0b50302940d00464041120102444111701e048004035a206030b052070411742a01c4e201c8040b5481c0456000141c1c24030030101a40040250582800306500c2d1017001820510f10b031034200c1348004100b04c88968043e60070740300400c1e020500b0b41d08590556034040c00c001d04c1c41d1141c0e91411198115140600320b0b00e45144c0844004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 706733426 1250 706732176 706732193
    0x30c0212072c0112030c021e0f100905011407050102032a03060a050114211503030309070302011b050a0f03090e0709030b07030e030c0a060c050a0c060c0c 68
    0x50a60340107281850038038140854040d01a06041c0c07000303030100194403001101124003819525041c05501c190130b100c0c07038182d96081584400950100303540440c0150101d40f0f101c0007021180c102e400b2005a206a0706100d0710744030101d140c0c400508504002d01c01c0e5401400311015000c0e801e02d00b0f40c9450f0300354507843c0c02c981043c1d60b00d107a1759507203000c09a0700e60107128100c00e800001c41007140c03441c14003000041b10307001c4c6d41c42518140103269000740c4051490000ba2400a81342d4607064415050900742c004601000300e07a980090754584800601c541000001e4030301c01c004000080c030420b400c42e001550b41d100002405402e8800c00100e120004506100030044188240c2c09503907440b0980c5070140c84401103400c00754801d8059803c014099520100c602c00f202e4000340841c201c0d0b2206a4114042c100452002486100c00240002d0588000a0f180d11150160208210f04075104a0454103445482c1c05000098a138443c0000442c840c1e030f0011250030340a0400e110b0598807562140700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 706734676 1250 706733426 706733449
    0x903210306280605030601090f0e0a200d0b0d061401080f0d090905090330150f04050402041508100615020d0f0e10031b03050105030307030305100b0c0d020c03061b0304030c02 77
    0x4c01141002c00c1c082f41110902a9a070001c124010b034401d11040204401c0c030300d01511030240e00720703910360016180d2911032140c07111450307030840d40501042d200c4c50b1810403110404e01c120000b62041e0301c0b4400d000b030008902c21342a10590340e26021858074103100d81c000340c10041c4c002d8906e40001c04c52980c144140f1640ca213011210460225405070501541d0041c3e250300400c0351020400c200480c8415507501030a2103030a00088030300160a468600124005241715269a5034039140d072000803504400006e10207080d070600710000c1c0092610b0307510342100300104c0090300b009a40900000003500303000f05410a1001e5030b034505011050356080000d02e201508585020100f5643e41e5400c4440001c016403000840c83c500342400554904004243e40344140c60b400303000c065546001c5400910555400c600428020a00549070040001c50301e4a901d00c000c00f150140c811013802c9045421f01294441c03107044080c281010300070f4900c80c102e0b40c07036100400c2101000b258a41d1900140c1d1904051603 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 706735926 1250 706734676 706734689
    0xc090d050601080c0a1d18100e1b0109060c1b0603020403151b0509190b0c07080c0321120406020903070905040206040b0903210306280605030601090f 66
    0x1440d94503101c07919041c0044040740c0340c01040348140c00e0000342c001d4075200f0700f1442c0b402c00041c9542d847c04541c0c55000c1c0c8109000c0300034010301040400d016034940202c15030343c0e10807083c0c7d0060a580d24881240b2102c00d80050702043d2126404c0000c9409505a00d01310b6005405c44003507601c60708001003104415030001400304c0d038003180610a012007580d43c00e4108904c1c0030108044900b8407000700387c641c0302a01c0300b801c10a0009414102e030f1140341040009220103080000c0f03058803040d0380c2d503941d080401603021906c528000050080030024410120710006005040b480b620401007440c950071001d586070618008008840010398000c4003180301e1402194016100c403040004c16041c802980e00007111207080005000150341c031001118103c940301d900c965034800303848011a060801605c0030009550014050140b8030150100031071290b030003124038010040c0c407101006103140c240082050114810b05003408006e0042000356007104050500c281031650302c1c1c1510142121940203031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 706737176 1250 706735926 706735933
    0x30215040b01030c0602030705070b0313050601080d03051b0409050c071e0b15010504290a03050603010f0c2c030a0c0f0e0601021506010516080a0824090c090d05 71
    0x4000707000c1211001c4c0098031491004c0c504d485031607110030f55580c038940145101c0000001c003107015090400c5250107071550090a8442c250794a4407a25200c000e5a00c840c00882d06040005030b03403811001b0760584181800c6003041c2810301380b5420000a10b0300509140744000104042400700c0c140350ba0615809041101040c0c0c0060309207442c260041000d4413920140c0c201c400609403da0300031007540c055418280086c420740441101e280059410002c604054a200040351a030140e4180c001921480003034000b1b002035040c802c1c02000301d0328642410800555088030b440e5503105446a20031010b20301880b4400d8140e10030307001070305107070030561300305c07860303030700c150041000b080e0110700da8004000500c000b00c040d107052400030303485003240240500c2840c240344c0001c1c080d070b00900503120440030700c2a90b00c000e00b000d032a14440a501603546840070a6100c0006034840741c40102d80303442110003601004810a62005111001c01c0c081e014101c1841d05000700500d81d100e88aa2843c1c150052005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 706738426 1250 706737176 706737179
    0x50c01020d09060f0809100606020307051b1e0f041b09080105060102071703130b070b060a1809050c090a0204061805010507030e030c0406080105270c0d030215040b01 73
    0x68948201e0365980c0c0c051106001d41042415001051001c401205041650407aa6035580c41410000e1140020740d19526000c2e000c902d896000000d0410981718000712241100300805410040d00c0f00700c00160b01c44071052850118100a9a48200100e40542041e2032100d8010000301914210301600c8800c2002c0c5000d51010f50780140a1401081480c000304800e080c1500000d49600c40c9000b580d8822225840f645240d400801c00c40f104290000700c400145c603126040109940e01902060760f03d011a0000f1618628241e071645007113a2089414846080320504d00c24050000c3d854192417602400102954640b28805510b00c50075003038000594503401c118014090000c40710503220340460882080c002039812a080300c902c150035007005000d8021100c0003a2500c00362100c216003043c28010006450b1005401842c040c50855130f00d82c43c402c0f0012200a4001e0080d0011507265024242c078001c0c504115100d510158000d00c15106c1c854020b11400c949000140d500700c5004c03422100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 706739676 1250 706738426 706738429
    0x70902130e010b0712020703052e0c02061522020904110309030d02180d0b010602011b090b0a0306030803010e0f0a110d1a03120c060a15030314070b0103050c 69
    0x8418014020000d807124039941007051203481030003140340c010444a900c2031800c180b60b0080049800440c6d100e4100c45590f00c1584000080641911400b190040c030b09070b0205440c2b125010306510325071954000c0450360384502403081c0850110390002d810a082221004810040f80403040250310a800d0241c3d072196894140002c4a110103a800361980c010310a0007035803080481182ea0b40007020390090f881e10f04000302c0c60100c106114009031b0103100916084d0802000003112812203000703030000c1007000090039011010f04940c03c098400150b800f1014840c141c00d0f44090960100680341c0041c0240e12642c43c04599402038019040700044241000001d000c0070320f4060b413080005009011000b4045006503140c094550715109840d12103005103030103800a00300c035507007106c010100d03000f01001c1d0400200543c0b040386032a40f00c0c040d120024100c20040d0207000b42061404c00d20200d068a036480469150081c41c030481c6120740e0402c01030f404075583ca0005030203540540040c0038102801e60 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 706740926 1250 706739676 706739707
    0xc0206150402040e0a0510090504060510060908190501060909051c21020a02280303060e0907031211010911040510050303090d210e010801060c0b131103070902 70
    0xa14800e40c0104030604c600d200394512190050038084010510352100d1900402000e200d40018102c585460108010b101c01600640e004604080602046507107031a4100c035044981e000f944443e0f413040200180220500845240440c0280c0000940c50745450f082c40a5910f400740c1a035442d4040d4200c07162502503969420160549801c108003806125104000440c0780c9130b50b844e0500d035000c80c203070010718024410780358010b00d134004ea48000217131000719114005080c10140c0019180c010040341d800c801e8040c00780a0784160380107080c11851035681c038088007501c0c89841e01f00241c1c2c1000012101003400b0302c01c8a244078074400e601c0400b501c1c0030b0100b20340b0b0052620041c1c0ca40c1040802407074601001303c0c0c01c400c0050741c540c2e5000010b82809001002082080c0d03140c03600c442440740c15a41d10001301c0c4902202683d40c681c90340d903501012140e8030f6040502404224007000883c80c031b540107440f0000982c2c41170414005541c03949001a00301350207544814031054000400d00003240150 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 706742176 1250 706740926 706740961
    0x90806070305010e01090b010e031002030a0c08010b0f0705070b0d0203070305150d06050705091e0f0d030f031503021f0305010603060b030c0304060608030c03180907020a170408010c0206 82
    0x501d41084198900900c2d43d98109041c441c0c1c020b016030f5880a200b91381d200300040e04410784040c0460f0b140e070200302240c00003907004480700705510340f81040d0000300c1842094028101e680c0f030840d41703081540e05004584217a0040c003044900d44120301000034103080490261040c0d1070b00c1440140c1700d20382610090305a4800400c40d0043c070300070008846159840000c0001015041400003509650700f00301503680340715090909c0d51000c00c3c40520543c0c081070500f44490000252003511001c618a030074856940144440140480c40380b000c0540503900c03076401600c1100090001442d440d0380ca070003242c004e0490110210007000c001c4912547c441d094041c2d035004007c1131030304002c106c1c03521100c00c109010241002050f500c0002c045014024241c02c02030241845200381c035510f0302018030850741c076445001190310295111a64030418074241c181b4034403c810300d40240c00e030031106035aa4000a0100000e00b10899020300c404540400240304002c980d401c0c5400814560034030701d041c481d501804 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 706743426 1250 706742176 706742191
    0x2010206060f09130503090a12110301020f07110a0312030f0e031e1c15081b090703090f0b011401270e0a090501020f04031b080304060528090806 64
    0x2000345105a111a481c242e41308403450107081c002d01e0789107030580c1188114815542d002001c00302c08910805181400f00800d8481e03844810785c1d8800000341401c1c0e000384040c003030b8074550500040c00410104074894041e00d50040264000a03100e645045c040040640114000703070f502c400c0185000918370034544e41c0902c5800440c1080041042515540c003411070302c80d81084041030207442c0c01c0c10341c088806000001071060100000c1d000b0313082c404500c00e12032032179035110303041d40c510400c0c442103450350b01104003606003982e655a0240a82c0503048000088601074800c541c0100480e0540c04190701a228003402d8204a11a1a000420418020807140380b9401d03062040884101d1002c501000c68810035401c1c40d1990301e000012005020318030b0090040d500009161a40070320410041054034815580031508981200702e41d40452041c1c040d40c41f890b84204024070529001d403014117011081d60b13001510b07070904150545103001760704c1141d0340810300a132001c0c01092030078494164000b44 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 706744676 1250 706743426 706743439
    0xf0e1509010e0a15031a1603060609030308071b0501020406030b120316031e0f03111608031003200909160513140727050d080c070503070801090201020606 68
    0x40c003050809142c0040c01d5884400c0da6510b10311602041c808441000b140c00410104d020400100300e051800301c1200c600c950000042c40001d0142d02070f2145c030055038003079a21198494299038040d600301401501d00c6041c0b11540342240141c9070111440041244240000b5131503a19080000d02540c031003030002032181103044408405c0740d00000c03d480162034810400e00c0522190305080d600c0500c1c2075141c0148010855010700707150380140303901007e001d665138200318048040441485034017030f02610702c6403500f4894800c030104100c00050343d002010104011800f40c0c4d40c0d0b0301d0b05800383d130007042032101c072184136100140c914048242580c01f550301d001408001e044640344034a138003018010346206405880044510049030382c82001c20400e4032031500d00c14140040050f140c3d14081f010311490b40c01c041030800030100392500307010443e0b82c06048103c00380c44036941c0009076000107003888503030302c5003080000300e607034040020b00010710703051000154148070ba0000a00342400100036500401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 706745926 1250 706744676 706744679
    0x9050a020a1d0402090709170102030105030606060c060f091c0908010c0311030f0405010f0c030504050d031109131518140411010f02010605190518060f01050d060f0e150901 76
    0x40180b11981d00940c1101c50209603591080151503007051a002440002c0304a20041e25080055000b18140c0780110120344842e561070080045600c248460705000750490800b041d000c02c01c8601244c0c01ca107030392040e1550651219001061200101141400900d0309502044460001c0c41084900c104500e42030048d01454820040d4501c4060b2044c85e104160740001020310200794001403400324404d206201c100501da1004020b04420f440c1500c0174020f114011a03602d00901c81e50240004000d00141800780c0e40081046003444041c3d50401141c44080200072400b4107080d000181214159101b5030003a003201860441e001a600d01d04004210801e000c04141d1100c0c4200c40c8010901c0c2181a40d90300604c100e02420320303a4402ca0300040d118100c10300b5104480da031042606c00544400c10b01404009010181c0340e819906180c000550049201300d42d441500104400703242c07070502081c0c030ba9988801c45214150399200602c50603102007442005100201c80010005e002c84100c8400d5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 706747176 1250 706745926 706745969
    0x21f020a09080d0f050a05040f0b03010305010e0604110f01020f01050103050f12090a15050c100e010b0d0f11031f0c11160501050d09080d090201020616050406030c03020d09050a020a 80
    0xf40301310031340c0184400804c0746410644a481120084c1101b168600401980ca203441d0803540c10a0000f15142e5092406020b060b01d000100301d1300c12508440251a005611410301c14121404c000b001e0442c002d0030510041002d09008550086110b20001d26008851a880ca0706209518610546442e000c0041c154642c2d64010707a40c0c00e50310039080c3c2005102e02c1d40f2081e40d4901c9024005046402414003c250b41002035220000b06c880782d00082c0701d699181002c10007000101c6100070300d10803440c16a400400c40240040f035413024003400f20340b803d20003905440790646212081d11075003074440700d00290141c0e201c01d41500301c0e0403000c01002c0c109802050440144190f0003080d040100110b01c0c6e80c1008041d0f00150809a0800802651804001025005001010816030161142c3c07000728100d401c241c0c0000303c00d0342050391628205410070030114041d0084840c1d01c0c1c10513800303001d44a5410a140700700300c0c0040c030a40c014288514540b062003110400355100325030707042c136200894200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 706748426 1250 706747176 706747187
    0x4031a0115050d090f0c030309060903020d1205221406030103110d0203120703031401050a05130506060904051e0f06060a03090503160c08150c07020d03021f020a09080d 74
    0x10700654205162580c02c1212070300d0003000c1000c0040c14001e81c2482d150103004c84c0c0c0c4428400c0d00d0195907602c1d00310341c44841c00e5a540700caa103c0203400c0004c0aa5a402240104541d400211014035126260080d2420360300052841c0c03c12001c00404c1401d0b0402400000e02c60070448420165407280c1958034540700d401e10360b100d00201d5809460b15100304421544d06021003248a8002010303582c9aa40f1420000c0041030178121440d048468580041035501e000e00140702200c50040140b184203c500e900c0c01d0145c8005014141c10441c00d119070502c5903510302449103e071140d900381d80c881c4041c105101503401c2000d003140a1041948007884210b840b00c8046862401560401042140f2036181141c0385208040540c41042d008400f800100b001e1520550121103400c000c880f1400c1c87d078075010f08034020507140a5481c2c102040b0030350041c2481110589242e0190068680000c052601c4551140320319404070798640c2c1c006100d0210540140c1500042e0540740700801704da60418401808 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 706749676 1250 706748426 706748459
    0x11404050f0a0e07050a1803050d05071703010b0d0507030c020d1b0c1410080601020c011b0b04050f190b0a11160303020703030b030a0c0b0a09080f0304031a01 70
    0x1d8410310700070700003a00c03a122048001c040d24034548000740b6180c4401059600049032250010741c1c2003068a030103c5d1a4030f41e01d0141c81d0000f020748804508298240c03040da000369030440c2c01d42c04284201c0400340c0c186c0065402046c02416050751001d118002c40c0840e8402081c10701031504d0720041805555001507600203000f080d00b00384880480c0e500030b8aa40c6040030600500540060001180d0f8407042000c0c902001c4044d101160080d102400c00d0b69956022550f85005034407440b201c00079503206070a10784070b441d050171a42101d00c2d00780d15842002c4408442c16507950780b2241d41c41041800030040349402c102c140d83c1107103425055a407698050781c0064908583c0d00c0e19850b110007052041d8045986804030034120120b41780c0e5619016010f904845816004a032520364601c04500f004600912007513800148644440c1c00d001c20000280c000320165406c10283c090f02080300901003000d10f10030100c00d001180c0701c0d461460081c56220700f840c440003d09841780010491018486021203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 706750926 1250 706749676 706749679
    0x11415220b071518020306100303090510050d02031806072a03090b03071b050a020a090513021203091e040f0903120504032105070e01031a06030411270601140405 71
    0xc1ca02c00300c5076400301e22291802002c6e506018503c1071000c0313076840e084200304507803081d1240003640d0303552000c00c4542865204c5040109904110358500c0c100164000c41d44807400300d020198401e2074404551802c1e00860307407080410035500d0000d090320760400041c0c442e14120b1034500e07190b683c1a500240302244510034000c051401002180c110390141e035418010004100c4030b0001d0704c00320700b0526036400710040141e006200c030800202d1250303050b00071740e4419103102c0720601040e00070f9070911804103540a0051000c2c0428008000d03540c3e1107100400306c034004049c220030110700000402080b00d80f002c5030340007103a28080c210320000343c00002480c122019104002030607650750a00345d400d444030300000c81c610250380391146120003130380c0d100c03074003480250703a5001005003502c0c01501103600108a80d80f1074101c20000c805d45143c01801036510a12480030358499000d28030215003004000d4500707036400914200b0745d00e941c000350308920f54401b0003460540c50070040d14044e1140b900c941d00a45 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 706752176 1250 706750926 706750931
    0x1306080c01050f04150f0f0504030b04020f01030e011109010e0d0b0112210f02011b050417070b03092109061801030e06041103010606020312011415220b0715 69
    0x1403203d60741c40c0075a0001c004e40f44210058002103030000f0040c04d02d0400c41c40106420343c5024034031070301c20800c0c0d40030f40b0350000610850352550340030002a040c1443e0514101501c4150840c80c410080c010861540d103a810341c10b881d681301600150490791200502d40c02031610b0413400c8041a480b007003150440d810a034014988281070704005501c424440e038a0603040030420320307c0303108540c010003401103010654002c010300d105919810010001034003104000070400d01062150142d03040d04450f009120b0300441d12002d41d00d5a01861603003084958800c203810a405002400b039071240d84a0704c83c1000480c092809034907100154007401242d00100b030045000c80084070a901035408038400a03484c5007201d0143ca0689465140c1c82038004c425400b070b50910400003801400003080d00d04c100440c120b001c5042c0e080c00c50f419a0760b6681c0c0003180c0d00a40041c10600c0b8580c3d035500904006181c070041d0000c05120403010a01d0100c60b1380040c011402c01c01c20031002c1071810219001200402401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 706753426 1250 706752176 706752187
    0x29030f041b120b0603011b0e0a1d04020a0807060c0305180409061b0c080904050703060f0810060b0408030a0c150f0b1203090d060c1202181306080c0105 67
    0x808071440321001c4090110344680021440030501903032150203600c50f1107418441d0341d074802454280d40c030310f10103801404040810004040d00411120048400280c0010400d035580c02a8064821103154111030401e014000d1006600701031240c40c004c0d1030664010300ea42860128000c0a48000d504058104100491003c01c00c80407401c00145800c0b00520a12407001c545c06d00030010181c05000001d030b10219001d20101d107000e1202c2d51030075608020000c0c140000507040c0005014010649000c0690307a11010a0034411201d81304041d2040310020320030f25411540c2d42c42154015007000c145108140700400080c040001210060461352402450f0052286025a040c15442c0e030b01c002110b0901c4910404107005a00c82220050122030400030190350000b91a00c074030882000c0c07500941c42d207488102054558110b2000324401d440d050110406000c000c9040713800c0000017003408450b01c0c100400038680b290154140e005880001c00a0a25000505030740f41401042e0030b0500401080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 706754676 1250 706753426 706753433
    0x140303091c020627040f050c0a0c08040506070f0b0609060f01110c100302120c090922080307080a141006030e0313060f020601120f020904080d1529030f04 68
    0x19105610400c00350742d004c0140314441090885156a0254003851600c1074003c3c0501441c01503034041c8403040c07950740c0350440f070b03000c100d500c1c131683c45060751500000c000000c2e16407520001400b0032801403911014150380c1d0701c3c1034101410b0141100d8400d4016106021040c2d45058010000031024208034400c0d50340d1a41c02c40c109130f03858810a610102d00f034100c5664580540040c098081103038206229640d983c0d945182c5402100d18480e04880e641c1d000440c003001c4000007440c801e0310000e000001c24655030380c00000c0d600456a101c00181c0500603c104500c1d5401809002065140e1700507030f900e0700c14046d0803070161620894040545580030303078032102801d0086525001e15070540301155034484402601c0c01501e5241c510051040c0300002980790a205891950a035004411451020154080010034003002d0410fa458034410800c0d0101c0599920901c0505402400c003216183d2500e104680001601320000303031842d650482480c081250a002c507544440300c030a900c030b03c07501d6504 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 706755926 1250 706754676 706754689
    0x70f0513090203072c1b0c0a1b150e1005091203031e01120314070627030318050c04090305090312040e0a020903060a0c050906040f140303091c02 64
    0x10065018051910040307170800410400303491382c0380f0807000c44400500e0301e4040c29080c08211355000d0600c000c040a0382c044a84130700240110f15080086a4001d82c0d0380c4c490005400c440c0a031102d02c4042d840c41040031004062480180c210b043c105202c40c0684800030500301c0c00e8074001c845c104003001071415182c0d03441d0900400146111000c1301c0d1289040c40c050a40c01d03401d03514510031406203000000325081d50b030f6801c1252079450f40d00d800000d40d842c000c0f0006908004802c449003902c403141c000803c04080f850302070380340414010104d0502e45040180403180892040b00c2c04280786a00c060225100141c074140740c0d401034030b00003522589418121140d01510407040d6250041d01d518110035180d20014200b5100d100031914a15103401910100300c0c499008c00d560141c01660000b82c4030303c9560301c100d075001c406081540c9047d034071500007910f961098002001d00d248903201800009209940b0241200c016401186415038440005403209080c4c0c04041611000b60072400c1191a200c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 706757176 1250 706755926 706755941
    0x4e06060a050d122f060402040b0d02100315230907030b010507140102040905041b06020c011422290903031603020f01090605160305010b0906070204060e070e0a08070f0513 75
    0x20301d503d031034680103444c0d40f07500c840b41030302c09034441c50405c0300480311031400c02d07010102a54010007421080566082c00c1d0043c10048030003021170460b20000050310500c09040070200030070200b080702a040148100034041e880503045408061410702e2050469800008544a03540c0140840038202c1c48482d11a02911407074101c641c1540c140340500c810420040100002c1e1101d22100001c0c49440e49822030796a0014101d6030b000621000009103043d0031080205aa600d90070460304402c101180625140e070030b0303030380810a620070101c07103e00c00c02d101841c5040030071106200340d0700c1e20b42520300181d40c3e40541200305044040c4e2080383c0b01010300070405080c211800e84028010320023141030070401010702300e5140c02c02e642d044c01c0010142d4440d104283c180d4801d80895414000f0a1051109603000b03500100c0e001952404045500040180003078801d5500c0e0b9501c0329142c030007605000c442c1a5070307408105907900c400b5041c8a83c10700c01e01603c0544005031000c00e0f02c0001407040b0300107044130 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 706758426 1250 706757176 706757237
    0x30c090d060f02090a0603050603100b0f0a17190503070b06010c060501090203040c0806091c090803071b21290f04114e06060a050d12 59
    0x40111a604802054000e0101ea60017140d541041341e5541c2e0041d01035400480f070050b815004644145200c42003a80100080035002c0c040e00c40d81403d036000314203440c0e855040001c180464003a4141008001c00c201c030600108000b01d60303c03240150343c030300d5a203000c0c0e80401401510141e00058807644184d80400007113401038030510165035240c0c12100250700640302034580c0c034410030f008039a07000c3c00030f4503a006112020080c00d00380081c04118484002c4222540100042c02400050800c41040502a2940a90500300202030340e0914800c00f4041e035170200c8081d04103440c105901d4580003000c044483d401074540300054807090030703244460b04014003070881c1c0c00303808003409244021502060711452182000154400050040185001c507c2c4007a02000140016444140035207011300d0444000000d610001e04114810307800440810402c1c0541300e6201c40104281882d0804803680103010954a225240c04541c403102004d10140301c1c6981407041000120480310b078290303035000c100d00c003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 706759676 1250 706758426 706758431
    0x501140a0b0f09281e06031e081b06180c060d0c1803050c0102010f020906160f0614100b0301241403101a0a2a05011103041214030c090d06 61
    0x1102c00700800c40c0e062038041d6402408a400c45e5007925210351402d80f50411152914400003c1007086e28642c81e00c02103964007400e20152080340d040700d000d5241c03001d0450140819142c4610300303515001c1141c1080c40d1540c070452101c01c2a4448000b11068065516404592900305079415107800b102114802ca508580000c00001c3c4040800e03028201d5400341c0c000e003c190461443d802c00da0250242c0c00e580311404206024407410391103071221050f4442c14114520100688503072080788c0c0708400c0d14640126490030000603130401000c41000e0100d010010f030455041140502d5454601640e440d0f82c0c07100f03a04139410742c0e8003603005845080840056596603291440008013540041e1056000c80030507040e0034500c0e6040c040c151a1140000d560b401a1614540226a98810050405000480450101c0d0085034003802484011002402842c5c0e0302c0c01d1030300e40038502e000d1f19007101e4100b0802807003101c0103107107500440741c11207178000c0030343e0b1504410b00000e0080000590006e00051 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 706760926 1250 706759676 706759741
    0x10f05060d1e120c030305060406081002090a0906240c0803010603051512030a02010b0604150305180105071d1806060309070e0f040507120b0a1806090501140a0b0f09 73
    0x10303442521504d0003071007540c0602031070320b07980c1c28842038072014011007208d40c011442c1280350b10800e80c041c1103d04401440e0701c403240ea49003080c00440744136400034114001580d100510055101010ba0450003440c50700c2c0e03840203103980b5107140502040c003c0344100b58446011034040d40442c000d00301c404000511000203070540c521544e03070303a034802d0302c0b84d070095401c000201c1c0c03443c03416005940803561407100c480b008082001c011402454010480700c9405071b60343c00c0c01c484001c244620f03407040e507560704c2d90041354103101c10303982c404842d04d10712a101e0181200403400e1210718200454010b581500d2054490f100d09400b28200041c90700910f103840318510400552046844019001e5401402070f2411551101d811241e07015929502504a41d29500070440501c040d5200c081100b0740c90354030032a4401c1a0f030310b88058503415103094699139142c4240302018071078801c02c00c0e0040080301c41041104001c1c00842e032075810b40c8034814400c5003540001071183c020403650356044000441e00901c80c9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 706762176 1250 706760926 706760963
    0x1061701181d070618121203020f0c01020403060b061615020c031206090601020f07060c060603080f030a06050913030311220305060108030a08060d03180f08010f05060d1e 75
    0x241c01038810900010135172019001c000c0e040d981d16405079541504006590711407a244d210b0f5100841c03030b0034410542c4c20404100800840805000f0518482c000540e07103074078500304201560403056019105002c10403032440c90b010080c40c607039591940f25285040802180c0c450030000d0103506120038081c040045c052940b19148050544a190215081071090f11214012a80d034007400b0360801155000a03010f214042c050b101440d540344c45808085180c1d030701d0340d881680303981111024801501020043c0111000d003030203540301030003054401192030701d04040351044842807800042c4c18544c0d11a12000c201c50540215100480c0d005c00620403120104041c80c2c44013851301c070075101c0d0301800001085d0340c07501008a40c214801d5075141301c40303916110100071805940075021805d00035000300c4018201c002030840c42c000d0031240510141e01e4580b0175103500f03403190b020388600c0d0903180c0020008580d5444840760216904900f40390000c0c010761884071650044420041d000c40c64204a00034030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 706763426 1250 706762176 706762183
    0x40b0d180b011d010b07050307140c1329030304150908030c210702030c100c0501110a030b01020a02100509132441061b0601061701181d 60
    0x50b00f410590300741c403036a030301c0c03802c043e00c1c0c050448002e080384c00410050000c95000313464402c1c28550368050b107640f01e851400040e072519800780110403481c8c41e1203003180d140c05d040740141c00721070440d0b0000e01c95040f0140041c1c3c4910640c01030180346001c0c032043e401da03e84100084400f801d201011269541641442165903003508060844044084c140c60751600d6100c0f030954444d40c4e809401450b418291038104044443c88440d11030400401000c0e40c00481c20900400401c208480170007580d03928021802800c1c5c482c0804014195841001101c4c0141c4454001c21102101d0f80ba10f40c0e03c1307400c201e002400d94100d07039a00618850500340b003001d045900f200b9840344801140c480d270b215580d41e0800d42c0d60107042c0312110b02d00311403940c0b03032000515903490844024121541856418603103800006619400c154240d000ba1000402c4480c50a002000006d01500041c2400006541c01d0300c0c0c0c10706400c005004942541c0704012004440300c5198002e0088144466200c46d5150b00c44892181e4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 706764676 1250 706763426 706763459
    0x801060e011212080703020708130618440114060a0303051c0f06030c030209010906050604090b03160b09030c01090612090f0209040b091002040b0d180b01 68
    0x141000340000035600000c1940103100b1684050030b03110482d5060420765180a00a0a6005050f020892031001401a5000380042c81c0820700040b061418803900030038a000d411001d2022000c44c1c001404010f0454021300b207414116240300504000385d488010000e0040d061401100c0c594801c0c3e02103101c03040d000a0f020284801e99003d8650b80c0c0c0d0304000004046c1d110207808503008010164a28000c8482d00d003d00d20030440125503d2513080140e0221215580b06030b40d00502c0a40600071890110074030b5004141c0064140100d90509001801300d12441c072030040070ba503503a4080c2d202c0e0b40703044c003104001c10300402c006c1c80358075920140107070664040a101403003405901d03080c10b01980519014000d5038840d5540c0403c00302007801c0c0c100200f082101c1036a44418541d07502c0d0059944414003032065116a801c20600c0c00d010245624028400741d00039101801803009004084984059619021010724041407110700340c9504042c1c142003502c0039015410401c00800c0d60b10101000c5e65 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 706765926 1250 706764676 706764689
    0x3090c0f190803031504060b0403031b02090903070201030e0102090306060105070c08120702130507050a0c020402090d111804120c1109040620032e0b07030206040614040b01150e0307080106 83
    0x60080501c01040100d1f140c50092054610042c0000d00120f0b06c541125030104050303040030280002d26800140e10110708a075210301c0740e0b000081040031964140682000078410340003e50030f010610b40000d8542030010401410860042400420301403129024030003440510180d601d2a080010300f9811350b4071510050b03010340303800c0348090220400b5104843c8620141ea0b9141e003001c0c4020003c0385c10007900301c0241d901640900c0034945580e074982600c3c0d042880b590700c1c8041c0314500414040c0c4082904215050034510f082044045002807005580d11070440c603003440d608005140030714a0a032200700140e00600004108410800140c0c0540d2105500200d42d880e8181d4040050103e4030044400501042c1c00d500d04001503001d42d03c1701841f50001146401d109501c480348080103800aa1060f001640300354180b2003800703090b110320b01c51455151f01d080d061b0325054440100c0800188501000d0700e10180549904500c02c5880b4024040700809448071207599504440c043e286901409 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 706767176 1250 706765926 706765951
    0x302090105190b0904091b0504061e050f0d0609050a0501201e070203100f0b010504060e120133050a1206021318020a030608010203090c0f19080303 65
    0x108151030007030600a24103419000710080c01d41008150f0300e2580207406441e4000d622160760074000360112040410031043e1450f103c003024138080401041e01d01c0c680c88038021442d030031510301304614001009400d8590940c0c2d1205440309820104081c100d04140141000d403505000d242003010100d0200b00d200d00907802441404030450300c0c454072401e03c0031036882e0301d0320401a0001540cd122521030300400b00b940c07150705085041d0042410150114031035281d00da5591460402c000407841a8826005d0030710b409801d06040c02d4000d000c0080745c00003170b03224420101d42c442801c20b007500320b1030500f070b196082600250600040c00421405030802d803040b0700301241d03004c251400c01d9844001221581084807243e08015100d02000754088a03900c10680001400410005603080f0b80c108528505400166105100b40c80203044601c035822425660b401001884a0250000349085000c40b013103901c010304100190000340c0001c0c6045a140d0744503008080060803205c080042c5104401980c140c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 706768426 1250 706767176 706767179
    0x1030c02030901021e340f0f0e0406200a2a080c03090a06092409050f04020405090c03071404053703052409030301090c200703020901 59
    0x690700c034000c11500302d0059020203404020521600001c95044e507096050ba0100030301401c402d000100c1007001c0940c0403070012607072401e800740e00f48114014580c80c0c0c50768000034104880d4000c9602944280c0b0360710380c8401c0200c4c050001580c4046000c0401101c1042c150102c1040a40c117074100c00007003008203060602c0701c0da00580074140401850300c0000d410703215031080da4481800d5040804075644c0303880207000000c2d0b035880e00c102d41c0c009410140c40d00b1070900d24117002606805840828004007000c030303050920805401100880c1540d4080f03901d030b00348846101c0407800a0189511541d0f00010b814144502034034590010340c02800305a0381c0d14203202411000a4207071060f03104a80c2c010003145022800d542c4043c0040c1d0100907401c08181d100c1580755011009904203420540b213940000002e001e45054545c980041203400425a8a40e032610002c0c40341c032030005108a840c190f8880480b107141502c111441e00c10120918201c40300320300034002c45590342c01140012405100c40600 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 706769676 1250 706768426 706768451
    0x30928050303040e010902130f0609030605070f020a0210051c0b03010e0703110105030709080d1205010501020106081e010204030b09010e0c0f09070c02121212180a2a0e04020103 78
    0x440702913505000c1403044503440c00b86c60f40000d40c0901c0f20f02040c108103900100b480e01080f0402e000801d200c0d9602540b035411403c01504480f80600b450052200321507030401c4064001c00c10316841c0790100d49101c04000d000b40207550600c6481ca005100b4240d21442d0074030400079600a8154500940080004104844c0340507502c80d0540000b4000316400041001a90321440080d680119685810303950b00e0786e030b500d02501e414200085a00420004000700d41c080071240b00b001c3c01800c0034030092006902e0301820340d4580100001c4403054404100347c01600030307025011100156400200c0c5460740c54402010360007448401d241c000315004528502c1c2951800080780540d024008100d000141c859403000d03030300d0340302c0c4007003c81c2c02c040c1e04801c500b00600248144030100071054109650785201d5a030f002c903284801012100300415140385640c1107203000403801d0503e44c1c458041c40248216100400417924402a070000010340c040c800f1400300031690706980a24401e890500c0780951001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 706770926 1250 706769676 706769683
    0x807060201090305040e0a2007060c031109041a0306190507030908190314070201090c08030703052d0a0f0e040506240d0c020c01080a050405030d0903020309280503 72
    0x20b4000d00040c00502c000e0140400d520111504480c2c03031540003840c806100016a040540c0c1002d003070505802080c1c1c202805807074065200a00701900d000c02c40000c09002ca801e190095021482c0215a60b5403402180c0f1500c01c024509044000c00b114814907191f00c05101c02c1e500101004d280034188004940c46600074000c1d15035856010f284141085248010110f00c16154540c507400c0503140d0100b05608590206840d000340803540c00812280f2603410840d4100003141e00070b82c1a584100000300110f9402010b17541850007103c0071407850301c0502c2501d0380800401c10705074003104002030540281900600c0800000085441d9a0740b44002d0804000844000321041504070000c060000d09120300054240803c42e40e03901352901b02012481e105013100c80c95110900540d100e04174080751503070481d80ca607a11401106050205140079a1a240c4034042c00c4400a10310b5111070210b001c0600a0007036440341131015180b040036800c0f0001508003210741060712a502489004085a14100803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 706772176 1250 706770926 706770941
    0x2705100501050a05271f060203091c0215040b040f090207030c030806040f11090405060d0c1e0302040903030c081e04020f190f05030d050a1e090b0409060807060201 72
    0x82c00303104a10701c2c00d000c2c0b0962070380c0d2110080c030540c21002e900355031102c01803c5e10f0003076100014280f01c84480d2001104840400d401c9102035600500c50307460175561b240b203400d1003072026044e0400904a5440424010914102d050703968140108005c03513100501e001a00031a1400392003038404641d501e406008900c100703940980043c14101211300840c1c01500091b402c4100604002011100c010341c120466141107001020094000b8029826240c03a00031a42c00103011124108404000c0d07442601c40b000e01c1c494a030154180d500040e07000501ca04240c0021074018106010311002460020010541c503400d80001c209040701007102403c005400e0809440350b01140c20140c0c40365020071000551074100b480d0300446502103040d106980224040003410b0b4000082d01c0c150501007010f08011043c070408017041010710824076511b41c0503450141110340c0c1c0c40b54003186001110111140149070308854009640082c00003408006544481f048409210a031030031143c580500b02c0c241e41c00c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 706773426 1250 706772176 706772179
    0x130e180607030c0e2b080d0506100504030f050a14030706060803091e0307050414090c06030c0703050705120a0c110603010602060708090109020901091a121f270510050105 75
    0x440362011614240419000c0440d1030048444564030800c41000c0e100744174214040394080b4001c120300090100c24001c15400503c2101c11000000403500c0041c1240100c2c40040e141200820080741880f0060207402c1d006504008a00a0305d120130400c50b070b4a9000540c00ca40d510710381807000410440200030340306640c0000301004580b2901754001201842c00621499050281000000700d682e5580305503141d44c090604492aa843e040390030030b0500340c0250b44c841c00b48108000b08807040e02ca1008843e0215030504240e030325102d50742403c3c0d10b051007155009044400010318003c40f6604601d010030301500c50543d484140a0f140144500390001f8031900c40543e101c00042820f26001d5403056510101d44d034000034444003a50001403400744207130301c0f405480382c0d12801e00100034600041c4aa0700c4409850184440404045080e652186440d8007203103681c0c4800302d508401020381100c00140c90f4840c10305107440140c0032040c0e10518040c4211040c0c483c1d840011500052400340781d040360760 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 706774676 1250 706773426 706773437
    0x906090b06030724020f060703091e080405060f12100f05150702091801090606182d09060509030d0e06040f08030a020c100903030b030c06030a02130e180607030c 71
    0xd103139800c001d4006031030f001c0700039800f41d078845100b113010030080d09100d01545e54010860045030f0900c4000b0015143e41c440701a03400d06004008502000101d6080315070580c1c4450740d40c001c155120207103004001c0c2820101d000c107070601c0075100a410101c1c09a80741041400e44030342c0e482041006050b01301507080221342d4213000c0b000162600c4100240d010103140410514001a4442c0c42e0031107052110440d030311542c424044c0003100107420b0003081c058141030200024202c20076890881000001000065848002940c0700c10004e41c20081d0700548c405407c0c003060400c10401c5440b900b00500385e01001e403030a000120f1002c8001071040c007464004071403a8000120340c44005640d80010060607560341c00304514240103604000050802c14824400145041c0701c0c41d005041d40c10120282d4400e80c8000f041450f25035600c0b0407250001d10159005036140007100e540c441d41107690380004441000c02040005040e8541e000d8402040950700b662203d9881740001c4c3e0454110203040c000040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 706775926 1250 706774676 706774709
    0x602040b0705100513110405041110260106022e020d0b18041e0503090904050c01020c0316060309140d0c060f1505040b0109090507020a02090c181309060906090b060307 74
    0xd04d6402603403c20b000b0003040c0c6e1241c0cac180020915000a102121002038420142c0310716445503031030040e440244207401030340c8551501d0b00c000c0d030b5110104040c4c1c070300310301d840304418041d10340c0001c244030001000b800703644502c07407041c1001c000c0c0b2400c50228003c42001500076042c0e02c04188107481990b05c030900000c00d032245006650350518012007140c3c0e510007080454101e68540802ca80b049120300000c0c01c1d5450000002414858034420309400303a840702150702803222129072035105403000380c900004e6182d11814605c400700841481d24543d40160300b10201ca555125145c001014002c100902c2200d40b00040c2d84110b40c134000c94000aa450400140024034003900000c00301c4905141a50f882070300c80029004861050b241d080c0503074040c85591045081c001c00403035011080342021420301d5034480003c0300f22050038402a00c1035829051100904c1e910b60301420025400580030400c0c80420710b4000c00414940740152083d1558900191f10707450300040c00c105a40a0b4105080d240 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 706777176 1250 706775926 706775929
    0x106050d03091e050d0b06040e0f0c220e0c1905010909020d09021207090b030c0d0308070c051504060e030c100b1c3008130602040b070510051311 64
    0x3c5010b2003651640e1141c000000c0c0b1503460780a0b101c08140a54401202805d02901300011503202c030f04898020307045640f40c00498503011999441c400415030b070b868003084940d01080d100103001c0070032440c400c0c07400092445c1c41c8c50000f0b0303030781ca282c4094901d03607507006200c017064000820078801d140c00602c102c00240000a0340da0080d0140f070000e0b20300414280d030154006a4080100104203030903501030f1804000c100b00c40d000d60109107400b03402810002600d0008101c0c2c1000400002d018444010b004ca00854803c050380e07038005422074140d0707100c0801054150001e10041e5400d0b40e4803030402424601002004c0704031074a08c1d0340e440013801084580b0004201500c004c58085510a44100020301046081d181c080085403041900c0b01c00022070141c1070008803a050036420440781002e10069250340c2010f440740d04042405d8483d0f840b00141d180c1100a48160b400007400e041c0e010030342c0f00c2000b400203102d0060420f00d160902c1540d883e038004042d2004102009880f41380101c078401c0d042e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 706778426 1250 706777176 706777199
    0x2e0b03070e04020d0903080f01050411040e0c0f0d061d0f1602010f0212010e0a050609071103090a0626092503050d050c010c0e0121150807080106050d0309 68
    0x441c0300c0a080581010003141918049681c041000c1c3c012603030311000c210600310380210050150a0031101041046980e0401c00c40358003031801209030b186034581c0810003003040502607480f00100700a40e01d41d40c040310400300000c1d000380c8c420035203500320301ca040c0804c658841c020b15200d013044810400259440f00410340e0040c082c408900159540d400d6919410825400140246d50040c541c0300c4c0103514245440030305843c018180752507203291406005840e50b48030314540d001409450101d03400405d4582c05400e61007104071007603000342200800207030305401c45a1500c80300440740b405c0300e135103140c00d0145013032041c100c80d011115006000c81d0000081003620307120014104001c009483c07070720f03580d440c3d2900c0034025035503010840100d040c415484090107900d19180c26440c000c2c04012201c1d001070310484200480070403517036038040d400f991610290300c00e01d00b405003000308000342c0e070341d9540c0c00741c48401a0250020030350070f068020540742844c1c03044ca0106641503031030460643c40d20205285 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 706779676 1250 706778426 706778447
    0xb100c02190f050a08030915031e0a06030201030e010506030c0d06060f080c0a150c031b0204330506070803100f1508090a0b0a02090a05092e0b0307 65
    0x740104240c04007411140303445a8100039020598402d100c040c284010031000d00389036489080303d82c2c410407210949480d60400c1d9080c948100940d40d8407600c2e0991400c0c0c03190b101d07204040c0b907200c7e01400c0024880c1c0c140c1003442242d000707072402c01082c03200c046010300ba241c044031829010303800002c080c8040c1c10041462800180107440014800d92504068800b0301c0c1a82e110120036401845030300424542400e03214000c00ca510100d42c0300f0406c489000e003c0e18109a0b02800344603422424410310b1039860500000141d000700200200b11900444075801c5c0c103020100106410100102004550019454815202c0040810b402c05005580f107840c1548002c00c941452246a8000a8034654108160015040710088100d07110704071080180081001060803d01741c0c0b281000d64045150b840819404c200300030030269546054002140e108016a0301154104940408000034180305040d10540080c00d4a9520035a18005460900140081c02070403020007041010440c010f014511211 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 706780926 1250 706779676 706779679
    0x2090d08160204060909050c06030709050108041104051e0c040501080c07020402040f03051f1b180b0d060306050c0c030a1b0b04050f010e01150b030c0f0c030a030f0b100c02 76
    0x101c52440c00d6010900342c800341d61041c110030307071544080400c211061114800f00070068566904600d403410005000160314840c05040c0040e03040801c062100c54001201201009042030140b4108054001120300d80751083c01640d0107601c011583c50000324040300c1c1100d0f0305a551003c2510783d45080c0100354401c0307030b080360700580c20440060714005c00b0a65000450188000d002c0301c1403a48001c10000d260a001e5249540c074248460070219090700e90503203150b0092400782e00444241c039a000250050ba0858001c2003030225600500f42402c0d000726058910a010510050326880e503050418040c0c2c42880500f900280400245244240100c41500c00000e0b40c501751800c090310f40c0f455001d81900e0a07035568200005007807880b6402d015007002c024035a0020030041c52110882e0b845a03e29005049005d0400408503034a107481c4000e4860b03848140c2012341c0e403143d0f124640c80d5a607206613032507004241050002501c02c0054807468071400b4001c4d00701c0c0c0b16840c4182c0111031500640004030f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 706782176 1250 706780926 706780957
    0x1803010e0a0b06120607090e0604060302010c030c0f151a030d090509090a150c020f210a1404060207031b0b0702040e1504030809151b0306030a080703031a010302090d08 74
    0xc001c1c0c00200700d820300906140d201e001c047d5050081884001c0d100400b0790b40070f00d05100341000143da02c03080c03a43c055501440d10500701a40d9151140380d0966040e4080c000c0c2c00307030a0180755005210f86c0a40300448140c52128404640c150601d47c5445603e4030050126000c9a0204080d0801d0340090f42d2105400d804d83d004016203035540440c08460042d41c82e58a42d0f14219450100e4040140c4003030460800005c28803c180c1c80c1c0803281415005200a00c4136a0201e0541c11f00c901a210051544d015003514684a42e16040d000356514172030300c410f0340c540e85040c24489444051240310015114060308040ca401c0440c0c0170321000c0c18012509800500c1a94082000041303042d241a0149100c0c0c1e45004030360074020b00c07041c6440441402006482c824006000d0240405a01056501170400310a52203640d0000041d00384415010b018104c200c0000d400b008055059200755002241c801503602c0c081881e000460890041c0840e0396040869071412201007200c10020b00040100500c52 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 706783426 1250 706782176 706782199
    0x3031302010c0c0303030c09051f27030f061113030221010c0804020301112a0f0729071a2d0405010609050c030f04020a03060c051803010e0a0b06 64
    0x10144140703501e034005d45c0081d543e0030851071100ea011201d0300040404890120070f24410a044545810314140b41e601401180d00000f0f041c24440c4118000031148000e41d02c80d04d1740d41303041900d030540c0c0031642191036030b25101509038069450300a07548150b0300d001d074902240342564240700c000300000c0084901d1460911506441d81800d0243d108000d00c203984121060070b00f4418103081d42c400842d60245451300f0b1210200f030001c1c80054400005000041c3c41210498149a41c10415018a41416400740100104004c022280580f0106480c0c0b450318248883d011000007550040f108014080b80394200c06200200e0004095030704402c1c81c2040180c4070014294082c40801c0031020004030f0040001000305000c001e01c500d000400610205110a02e402001041203110041204c031241c0c07114000b0030159100d40644401455100b131040201d8100824003402c681c1101d10f04460790b90b841440e00380e00781410302503904105070b00c4005001c1c1c50300d15030300d803a044400244000c0d0015001c191 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 706784676 1250 706783426 706783433
    0x70c0b2805010602010911060c031c02040503070602030a020706020d0509130608061003020108060906010e10030906050c0301170c0310020f0c151609051e040923100501030503031302010c 82
    0x751600801e202d800000794200d81e4900318101200810300584514018404d1002e00b00c0040304459441a80443d000866450400c2c08070080c081c54000d241c0510070307100d000ca034407a0004010305109001e9022a043c542e5200c5080742d071000e0190204000482c01c1c000d15815042110b021076140c80380400100e80581c50300c0e00e5a01e001b05c100c8105581c0140306008000b9943c010151540003001620f0480322460090000307071070400c03035040b414001c94600e88140640d40c8241d01c00e440003a403101050005080107500c001450f0000e0007038400ca01006a030b480e90750440001c88402104024000e454030200c10340084d0000d402c05603100040f2902000300c054070110620041844042c1d42401103035504041a2083c00210013040d000144001500244090781d00e004490082c400560710768881c41c0820000309020702110b050041682040380ea802101d40b0115564103608030001d070855600001203460308060754820b104c091700a070020130201d8040690803841882c01401070506003580d050564 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 706785926 1250 706784676 706784681
    0x309020321090a08060907050607050a1205070b06030307024009051e0a110409060203090f10090b060f180c0409050109020418050615040801060e070c0b28 68
    0x1c1252100800901c0e01c03a68541081c444002d80608001010280380203080c1e95640e040c41e000e15440307400c02086000400604110000150382d0101507240c1018603050301400c290450b000c21100f80c101d14000506a050010130340340c0300c030780042c000942c1c00c03c850115040d0144006051529a0044111a11002c98220740204182481900250503a4036041c4107042c404c085040340ca125540003a025590385000903405041074001501c84000401c03140014024a06008020040e07400401049040003004c912085104448401d540d201c12000c102c2004540003184001e000070310240c041a034a00b42000c140c02d44038000303403460042c04810a01d0410006e0304444c25100c401000034140000304160040c07500501a041382903090500302001100d0882d080c40e01031804581d1400058543e40e500000004414482c80d060f903030707071516105250f001c0c003158010f54039020343d0720021408003031180f0400144203401001c5051740c1d4031215050783c1071191a0384502112888000000a03108061 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 706787176 1250 706785926 706785973
    0x4060b0418031806020118030503070302120106020a0203120301050a0e1308160c12020a1503061802130b09060a0f050c0715020c01023013060336020103090203 70
    0xc2c0c49082c001e1281404154a012030f54108808690400c0b80c0080000c0b40e01d100c11003200e41c1802e002d51a40e460700001c070024003070014010161010070780001ba00e1500400c0070007000e40250240c50301a04c03401018451880b080c070a554108080443c10041140d00c0300c101c40d004400b10702200400006502d50f041c1c142c00c4071514000b202080902101084140050f000060080c0c07401c0c071562aa468000440a82035445015029200c218440003a01d100c0c2c1e01803400340c00b0841c191402c1403c1a040344000350031004442048086600300480c040c1540d206071017480703400070110381c0b030310340141300403a10b80102d54404824010144814000d120082c8000d102034001000240f2012001c240024507050a802c281030564208103172600000220f014114807010000103800d07030011188000d80c2d2544141076026812801c00c03080031450030751540004030851008158010b12100d481d0051200b404044e00018046001e06903a00042d4003a4115265280c0002c09541000050041803032600820 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 706788426 1250 706787176 706787183
    0xc0f0f030c0504030204060e0108070f05090c03060102010b12010507020115080a0f170c03090406050409020f15090a0806010801060503030a17060d060f0507120204051c0c0f0902030a18050604060b0418 88
    0xd60f40140407215040bc200001803103000d2441070200d1919001c01d04009014042494400d0004001803450b4000d4201c03159080c00580207024040345000858002c01e026550a001542051440b42204942446010966034201d01030007900300c440d552280172448031201203484104002d042d0301d024580002802c244400607020355941c400210400003140d4990700040c1c81540341004081c09600d4400f10940844011341c2c00e55000d01544004a4580c01482c10055012043d400d005c919060045076040c126003458000784a41c90301c4d4801c041e03c0b4060502e201c40001c0103070b84440c03420b11462524940003080644440d04105003138440c030f419640c0740e4203440300c5543c4483c02d00c000d2592200300c0003d0890103071400c500f030a003020b0000d500f45030852001e4001030181d480341014840090040b8005007407030104407110545c1c0b0782481c00a0f40044500c5810180f034400c841d511042d030f00010031032241c0d0020141105a449541d500002d00180d2407003500300759039603110001050900d400c0304c00b0901 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 706789676 1250 706788426 706788449
    0x150703110f21131112011112071b060b0a0f0b19030e07060e060d021201030c0504090c05121006081b030c010504050d0305120c0c010c0f0f030c050403020406 69
    0x104002010060a00388403a042002d005040141e100c040c0c0f90b1031001070340c3c80344030080100c00800028801c036060707821101700742d440c091142030501e41d180004d00e44020008502c03034056842c100e0580f0341850405481c100c000c441400307500001c80c2580805c41d8803100410411505848065240104c48660000a140f050000304650001a202904098101145814030148241c824080d4849130300e403060381c040c0010346004000b903960361300c00c1d252580706045045440c1c081864000a816401f84001c0d108404004008116820540200f404668001a00c2a000c524000a000000c0b0014102c85050b019800b81c03004a105a40658002007090f640240b8560f81d40c02007080c0d50042840541d4030031f03800715081041c2d59800c0010b032811980200c0d003440182c0c21900b01641c1301e120329402e007400c0c035000f80c040007d140d68110150100c0c50a20008001c0f0030702c284015038660302d18411380780216075220390391160340d44240c0269000488a00d401801d155a99010806580440d040614002e8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 706790926 1250 706789676 706789687
    0x50306190f0b1209070506040618050d080a121103130f0c0303030b03010c02010b0d030c020a030b041a0f060d0b1918050d021605011412132102150703110f 68
    0x843c10031646800403100f0000d0142c0741c0c540305c0080d81034802c0f841400148400e804e9100135030250780c509003009180140280d00c411080b89444c801c0da17440114450041000b0360f508200743c003218441c10290001d040001403854445030b594240d52101403400321941d15240542d6400180544000c400851090700e02140d010306c400109800c3d1654040b04904582c50820b502d200d0b542e64600000d9801d42605003910740031141c0c0046a0006400d400c007400c942500c0083c00200181050030200a4845005040e01510b803481c2c034a903480c5058401716407000b44031500d1401300e42d07550451a00803600e200c10805140040a9401c01d44142e4101031044100c040c10060030f00505008020f000c50103440078048442d02c3ca080700200b502140111410854207000c0000307090010703001c4583ca0003241c0e514030041d00d0040d001540510a5030070480f0651050a00c030200e4150004010b242c42c3e9140d0050074202d54005407071580e250f0010161802c1545035401d4121000c00240248140b80d08030440c5036944 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 706792176 1250 706790926 706790947
    0xb04110c0c0306011202010504091821140304230c03010e0c09100614130506030f0a06090e0d05071104050c03070206240f040e010515090105040c050306190f0b 70
    0x1000503440318801070b01716201c0764010307a0f102040b1015030b401040009a500e03450801c000d20003201c840020808460a400c1381d884100003d5005000035241d503550b11455a0075000f100355001c04d40d0b00622910100c0c039611892220640b02c11261001c1a040b02c0200114000080c29510f03048aa000076802642501d407980c1490306800340e1103800c4050342440c052401d01d008140084041c400c05d400e59020401404040d203404861000b800000e060540341c0c204222074150905058490b6070300e94cc5801070000d40d001c80342c000d40861465010240406070341408040c1e440342c1c440301d421500800b50a03280211540d030f500c507081c061b07d215414151245030800000e8038107503000c1d104022607541a01c0001c4107883d44c40307403160304100a5a080c7c06004601020601a045842e1040e0165090500b086180b003200d2100022400d070480d61a200783e40d80c2d5051001300ca003071140c2500021001c10015084d410491307002c0310044095811146035076170b1103041d0460320704c564000c140424800140e51140d0f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 706793426 1250 706792176 706792183
    0xc09030105090a0f02010813080a0e04050a2706090f050303010e09162c0703050a150b03130503040e010602010c091508040308190e071518090b04110c0c03 68
    0x210101000341041c80e40c50b15070a01c0000701380002410448a540000d81d18044000142c05407580001d0254440b100c072000034200d0102c410515019501c0c20f400514200c03020f004205901204884604000b0499801040170801442e01552100d07110b03ca1301001803903a142e030343c4400d0301130300183d5125414031803000300041000e800080c069014800c240c0001d040010424211103170301c1c0350403048031070326074120003650380903104c0c081c0b803480c070508002e03000350990005842481304000401c040112148001d02508850003042c600c00400e10003d0410782000c80b0440c0b40f180a0401c5900382036803100e440c03541e124240c000300300607519000010301e80e0380c02002c01d4020384100c1300002d8540201c1310340149030300001000034040010340c4010a010985004d1042c10755101c1d00010b11104145062050f80d92165201e40410000e0070b074100c5244034414446142164058000e5a0311145402014005011a111200e0f8043c5d40c5d060358140d020314000041c100d010240003d84520100c80081506 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 706794676 1250 706793426 706793431
    0x30b030f060403200c0609042322080d0504170a090e010b0304150504020604080a0318060905030604030c0515040f1406150118030c0b0d0609060308040b03091002030c09030105 77
    0x500c482207200c4c1c64080d13680800c0d02e00802c00b040c0c41050301c3da565140017601508441070300c01c0640e0700748526545101120f9075800d1180c9400c0b585c40780246151204100f01a00381d000140c020142401031038114100c98200a400500407104840707185080c074003081d480e074000e02d00c5030b01052181100b04200b64107000d80c0342c0145107400c1e150b401c500d016100c00200d070074204c003440703e25660780b40000c08660b2840305071005001080100c82030010a03240103028401c1c0800c0e0680142c8050380c0005140d07200711442025210050050320003501e540d80e09a609206140d0122007900448454000c0300c2c408030003961045000e40000b81d400b01c00c904000780c021801c000040f070700342c00250801600d6840448040030000080c40c06000c0c0640c0c25880403080715182d04002e2010100200005201c035011020b0150401c0d403000820810742d075100128102d5029120080101c81c007072000300442c00140020310b601124200643d240311410700c0a1000300d0f8030849210130f202002041c21507040c21700748111903 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 706795926 1250 706794676 706794707
    0x6010e010f050105040e0402130f0b150313030f090e0709051807020d1d0a060e09090714100302190216060302030c09150c010207050a0b07050a081501030b030f060403 73
    0x41d001810080000c00920640c00f0300c803514060f0f0008501192a0000e01011111041074100001230000303082d9005400c841c04038600c20a41548115008034007403046901401100c4813000c08401c180e175085d02d5900442c40c82000703000c1c001d21b002940d924030044091150040391f917004207003414401000700c200807902071007001180402c200f00c0040d40000700071200031807501304551900078046904421044001c41c150300300d020100000356140c2c00c95107644004000f2206400c080e501c0b21480d6588120901c20724020408035150220382d410301c00407102d41004280b8025140c44007544074120694842c0c0300701e2005910010001801420f40009400a00340b10714055141d401c0441201c031a6028a413400d902c10403039203c2c1d01008000c564100d821443c143c400a6403211024102280c03140e14004040e04c0c00d44410000802407480340049510081046e00d5500d06500d5541044512009450342c01d414180c1d02d01d44070103d95010494101649401d8005000c2c40c5440c0c90001d0141c45616483c6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 706797176 1250 706795926 706795949
    0x9030905090c07051f020f07300e09060d0609050c03160b0f093706050f0327100204081213061d060d050423250b0c06010e01 55
    0x1d10001e04049107400040210102c0176107242c1d007400040c1d00034440e2440c2c070000368100045130403c01040b10103c0403058225510f10600040c5840d94094a001141c161310018452289480e8549004600c1d0b44e0019000382420340d25038020743c0d401c03080b5105d07040262401e6000c01d11525940c5000c1211510b5140a6003804024519225806075071740141552040c04560101c3c0c8040f148d01c0350303035a90380c60400c10070002d561a0691181c134403900c01a0003d410802c03c80030300c04102c0d54004d4088454100c0140181c514691750300d0841c260041074010300e10114070754440c4402e6210400c101076100c00304c5011006907100d140c21901c0c0e20b01500d1030300103100790106110340725980c920714003d503040b00c00c14145486441d000740b0f500c0c540541c5810f01c2a510003000b084980f8001c00645c4034501c41c1c3d11640f80c0e143c11500320b07400d00740a020305115640c92980f0817141454074110b6813003810035051100901004045d15085ca00000ea009800e500348681d100c040104801c3d0140d0b40740c0c0c1c1c01000c0c5503861 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 706798426 1250 706797176 706797187
    0xf0308070b0c1e030910060e042901060e040b060a0f1806020304170c060a1e0201090c17070302090a0b091503030a0f020309101d18040f05030d09030905090c 69
    0x710082d40f80c6118a240a00c00200005034145003e101e00a1082d042a004000944d00c81c0d80c0301c404544140e405560a11600c0c945060205081601031030013044030300c02801c56032070600d086078800807200e00f081d0071544454101a45440311405440e0440c1c0340e4030399400f1450382d58001480180414040001d0b140904002c01405401008039801d81f65080761a00b09004800251441c0100c85420a038100070009561955280d03c55144a00300c800c3d00c42810120820301802c1342601c90240b0301402da00c2070316104200c4081000351321984140c6040503035000694a0b0006541d0040c215000722540d600e0b00340d43c0faa20300e4507408056001040c4250440e03081d900001180d941c1c05810050014407101e0f4a621141500810650f500785a00418421070322900110040030031564202848d00c9039803d07008103081d81780c40000c0c40090741700031300144101e6072239466100d800300e0400005c0c0da0500003081400e20300e01c481c0c042e007030a15000342c450864151401c000d000404c00001d1210850705030130b029 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 706799676 1250 706798426 706798447
    0xe0d1d0d03050c030c15040201121b0f0c061a0910120201051812010c090803090303120709030b0a090302070e0603150403091806051302040605030a050703060f0308070b0c 75
    0x1a0505968251502a0b2107103100e4044510350700c501c000c0e01c3d0301031207040d28140c006c0ca2040c240612451003030340c5061500340b0502c410004e490554004102c0c02881c0c4a84e0b007003141c4205081c02d0840060301d052485402a604c802048946000c1142d2110350801b07191003032402d05400c016040b520a4170480c043c141f0f4500202d446040e4050003c2c1081000216565043e00d40d008a81010307070002c101880700000c181c0a58000c05c400750300171010420700c0c500010601000300035100890400703000b6501d0540d003126104140d0400808640900842c0c00c40031000c108030201d0319200c6e82410328001401d4800e800c02902d07206840d0302013481c03d03000c0800c006103500d022800e00000900c03080941c9054840e0319007540d16180c590040612078040d40104500149542c1014040310307015541a5204140c29100c50160700c258010400450405c0000c1416440c49030300c0341b61b01006510300015100c0d1190300b07110901ca110741c42a0780d605000300717580042c025104040c1c1d40240340b00c45001d180c990640d2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 706800926 1250 706799676 706799689
    0x80f010b010e0d08030c19030c0206060a0f0902030c121f050901030c14030a05030f09040b0a0e160207080a06050105131b030e030c0f15090d09050d050a060e0d1d 71
    0x198024130f1518048085034800300c0e8001510000b01d01c2036581801d010751000010700414203070220400500c0b8410119005041c4580d020301070320760100c001200c40e4144501080039500c040d100700c4410070f040140030300e2034003042002400780c0502c10b1075583d00001c61154540381004d90700300d030f8454400040100001140410b803e800c84e204109001061601c07072002909107030050201038201d01000070b215014980a0300105000c2108960802980d4082418010b40d610b4601400b403892546002244104c0d81c40203000b80c400203039104442d00c0340c1d19040c0031410280540c1c4c080307900c241c4841c014411890a11134400040510b00c2041114002002601b0690042003202d0024569140c0300040c21000030310845401580c004111160390040d049069500c202c105107012003c4601004560a801c022480c0c80101c146a0b5484400e2070400c0c00300301d82c042e0042c0045a0034072800d90001d00144040c00b6400b1040702010141800d43c080e14405010340fa00750040240300d4402d601e2028680c1c0c4c0e0b0301c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 706802176 1250 706800926 706800949
    0x70608010521010501291801080438090102092d06130f08060c0a03050c071b050306013002010306051c0201030b1c110316080f010b010e 60
    0x1c4800d44400d01c030b10040a4403611250400c120b0a500344000411410100c21504010704c04e0001c41e000071b242aa602141940a03948140b15103d0526420080030740c480c0741120381140c0110707041e660300754058150910462039000c4046610042940c00200700b0708610352141e111019070025031500c20480b001407400000111010344822958845d4426a800c1c04050300f8200b0024200641d5006c0d0f01000340e14a60091103a140440501d440102e0b01044c04100380b070048500480301800d00840c518160090040181100300d40317201440810040303507400c000300400f88034611440603010f0a00b400c0c9405d000050300944150782058400c1240c2d051030404e0703054a041c03403025000209010f031004a000d00003991087c0c0d44100d508808040d04d41c800c90084c203000f8401d0b00c0402025191205005d14440244010060481e140b1400b902044410034850348040340101500c0003003841c09522840501580c0000115510004403018400300c00d12400c030380c202007402c05900d1035584200145080c51036 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 706803426 1250 706802176 706802179
    0x6061b0506241c0605070c03082e0f03060f020703122f0a020c01020d02100f06030c080f01051003170a020f01150e130c181407030522020619050c0f03030403110706080105 75
    0x2240f01801140c1d00101040450618241c0940081d9074be0b4a00304840188a000507200c440c6040c0740e10300c80340f11900c210341c00705625484880080300f01070741e014020000d12072408844503142c403041c040c2406101c0d0310b0780c0011900201c1d42d295040c1d4074000340317003c030b01c41e007040c2c152350048448110003900000c0b60014007100703030808541d04805540190240000c1e82c00100038000440001c901c1b410040b480e003c06c1034110008002e641e0700c60700f4000c401000c07440080d01e290b400e00500241c5550b010021301e40c6000d280100d8202c48804848542180e000c81205d2113031000360403041c8943c10030b1340e0849030002000721054828107041c2d200c4a010f00c2e082e2140c1d001f50850b1200c00b02c40402c00390004d02c84040b0722121414a4034200c00090064a002c403001101e0985803055a843d402840c6000e1400c150043e00d15814864815615100496030000c24001d000f018400b603852100100682d2011a001c4005140caa09040c5000f13004215140003000f4580c20110060024651280300241141c80 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 706804676 1250 706803426 706803451
    0x6030c0e150108181e070303020609030a0c021e090a020306010f021c030b1f090608071806080c0f0f0918071b0c1806061b0506241c0605070c0308 64
    0x4c0c0c06001d42d1416160800340101c030704c0824500c051110011640750205c9000c0d03002d540c1a6512104940e03201c0c03164981d914042000020840050700380011220780e0100b1045040044121010014011980803a032294a00343c0020403c040d0356444250b45002e00d2140c0018840d105504401d04080c000b0000d1000425585200366280d80d03540035001c903241451810054200d0502d00c03c0100090160b001c2ca00209080c44041500d540c818040f404501602103501c456550501500702c0c3c20881c0078002180c00d070014001415220341c40c0c0c0007805401100f00000e65602039160500451040300d080400c0d00103000c03000c03c00ca0399000005459051305480e14001420810300d4003114098142d046284c001c902c0d034009803010401580282c003600d200d42c60712030210f80034884400034480c1e1034600505940080c4c021414848202d0380c3c18400501d4a42d011501100c1c542c00309500c0c5042e0345004402c00020160f244c04e112081c03140c2c6801603910714160100001b00d86020f451000060805010000e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 706805926 1250 706804676 706804711
    0x60b0d0615083f0a0206040606050108010503030a030f232403030a030203130b010e071101060b09120319082a0702090702071a0c2503081c06030c0e150108 68
    0x3020f02e9622221008031685848404100d8003c0d40da041c01c0f00d041340e20a140c501c02040ca50700503c162030498200038000c40c82d214401c2c00440140c01128000210a41c640c00c2c050111a43d4000d888420400802802440d1038940d26520580f4800080e46100120509803210251008400c42e028075902d402c015aa03a00c1d280ca41c124452400500505842c44190020504580c40007149004100c550750744000960600041802c890f90b82c400c4511401040000c81c025003410000110001700c414240c9041006010060302c8408104482d41c000480780c00070400003010504100d8013416012903e443c00122540c10306403180b0030705001034800c0c412800055074071803007048010094584a551005207221419030001c1e5a044004c0b6075181d40603411059a00c48600414a001c1000644904082e640343d5150161a0751240701000340ca0340921010103905081d0307008000095114090781d0b00b140b032600c6861200180d000d4410400e13650b0745904022070340e0b44000f000c1d40000007084c145401a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 706807176 1250 706805926 706806013
    0x2030411060f1620010809032b050406060f0602071206110d060b0a021902100e032a040f091109092113120302030f0304060b0d061508 59
    0x1405000424007400d105402424108031160381c0250940c0729400001c0d4031620b65030010b51b80e5010480c1c0c20300e841c0d4000c0c810360443d0013818500204455501b00c9025400c901110084140c40e001c071000d54619445410800444030408002d60040c07100307101030584c5a08000c014009018034080250405407129100d482295841d000c6545217840c0490030001181d071407952032402d41010485402601400c502569684210581b03400819402045a004202c0d1407100307541c070800200b01103030144180800b25048130116140001d40503600c4102c41903038003c07802000240c41d91403602c02c403144c0c2419407400000b964070f40680030030001180c2841c001d98409007110f241c0750400d44d0701c3c0c421507207006103407900d004041d008112100601005480c0180ca5611450000101d100c0c01401680100300c1d0400c1c200c0708101440d0000e200b50f84c04504007500c0c10001303084081269065594903500c042c003035011280010758900402418014028150035404c2c03411080140c244203000400aa06201010703 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 706808426 1250 706807176 706807207
    0x610290c030c010c0f03060807170c03030703080f0112031707142101050406030c12060b0d0b061009080705010309110402030408030108060901020720010c08041203030b040203041106 80
    0x4580040301200e4a581c07010026501a0640b0074080021501494030070f08034a01c03d0040340250740c4624024001d1603d0101c003001d8100402c9800c43c003d0140801c4c280440e50180001c08201c0e0080da15444903041c1000b91030020700040e40880c10300c0d00705584d082c001030740010511461415200c401d0b4495540c4917400d88208040b640b00400401d4005030030f90242c060765000602d8500c00400d5640c40c5c1c0e888800380411103010380000b5000480380e010800c40d03140220b0920361080e110b030302c0c04207000d22140081079450270424400ca41c0d84a0342c2042143e5810306103e8458180200d24201c420741c1d103041038013915000607000d494105603c4514071414010043c00e10711030400080d00031542c07413a1500f408a841e400a002c1d88000c0e00034440410b003820414001e403070041d90003189051300c203010740180d02d4075a18400d0700503040c860b120701c0c0781c404188480003a10090811862803c0c0e0620145402004c40d403113400b2840c4114814000e110200d00c4800300c801c1d50600540389182c0c0da808100704000c0d03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 706809676 1250 706808426 706808437
    0x90c0f0e0d0318061d0d020f0d030504050603250c030f0507061b11070902040303080f0603010905011416020703111027090b0103022106120f01060602061029 69
    0xf01d0000440000380d520b60000380c4443c44807190585621000c9000b0030484060122200070b0340c8840384015040c040d2509070001021944070342812803400f6510b4000c21020b0f0070440350050300c0940c6a180043c00c441407091104030084c58540100e03441c1c01344d41d02800c186011080c0c03008010000c140381e0100320b107a90140315600c0c4502c600411642600c40000c281504015840f5560302552038001a6600e090083e14140c0368035849426456444054902603028001c01c116815034803045084080340c402c1c40307151411114408503c44078a0201d100c5244980b0600b4802c003154020a000c10210340e807072400c0d189021040300c1024240d0b100e00812103413207140740750702110410402c080105841032031003580d0444518541c140900a24440190300301e02841c1d44007081c0f0300c2a02408001c480301040e0090780460b00526018400d250034a855140403140c6100d4800c580d551007040c02415010414151f000d01c40c80c00e45d60307041d41400e0140900d0075411443c5420304000c17007050407500d8904d1081c0c90 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 706810926 1250 706809676 706809707
    0x11e18180501090201021c0203040b090a170703061b140d0624020105070e0904060e010e07031b08010c050a110c0603040602072105120903130b04090c0f0e0d03 70
    0x100c2800140c10414002e100d800700880c003500c120030b108042c0c22801040b083c8001480d401444c1814500503004030240e10401119a01040c88003000c51103800b611503124861010000500205045103070020807035200c01e03402c101441a021200b04915400081d581142c030361034001580301c271038021003a009010240c01c0024281500030b46280400e4880c3c13030203d011001d0ba802401162500c0c50309442d40c654a2202d16000211400000c021078490740105e8410460172000041d80c030b14685890741050282d0300210798030341200000d1010b002c1c81e091000040d0400c98020001440001c00150007882544150002c1c054441000b40b10643c09108014000c0d0000d0070180d507900d41490300340c000354011030003210100c550f00180482e21f200c039004000c07404640d4403241c0c03030207004040301800200700801c5805144010055031010040701d041c610000d01c0c071148a241c0b21400c2060b410107450100c42c4040401c601a004240c1703950348a000c421045401762801400c20a4605080301c04295014150 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 706812176 1250 706810926 706810961
    0x61809020a09140405120301120206030603150c18030106080304030b0406020f070b0906180709020c010b0d03030207020102060c0f0d052d0106020c090f04241401030b011e18 76
    0xc15210101d11030081c4581c0c445d000340d600003030109503680450300080c0600882c25000104140050030a0310046421040c000c080320f60000100714404103d000846c0c4d410409400842ca40340050501114209d107250110300a01100d410003410595070b0140d44000751061300d240700443c06110b182d504503442c1d154105080d0303545815608011141c140203640c607a08511411f400a000c280800d4500000865240054041c2038640300300100a500a014500d2480d5680c0803041210741d1540c500c200004d1290300c001d80c952210f8000641001d01c0185040301d0000e00700014610a01c06504581c0146440000020503444040200e03101c4400701c108654541000010710709a980c40c4810315048510aa088661981d01d01d4113001c0514400c0d0780800714110f0b442c01250000340c4c0d500b00c910080c00c0343c141c030020076800502d5140941e1654080182070107014001403050240509085024100710b03400c1014101e60801c03514541012407141d414201c02c411224046400d8070341080c28902008580e4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 706813426 1250 706812176 706812191
    0x108030a0c2f09090a2442060219061821020a02181f0e040303051005010507060c140c0102040f08060408071209051f030b0103061809020a09 62
    0x10b40100600040c2180c0710303403607003000100c40440010b4031140c4998007a40502c04800040700c42d444140b03440030181c90180c2c49140c0680e84440c0032041d00074511882e102c5020f55000a2002035460f0032000d100c07020709610b00d20600045400098407080043d4000d042070000c80b05080c01c600500c0300b4150110440d0400d55050305002401c581c6180d00035204003c80c40d003401459040e6a19804482c1c02508004c000c2010030100307000300c1c0280c0e4000403c4c0001d61000f510300c0c2003060100f04942020742000d00300b0050105159040c41084d50002c1e00348456204503040800181031405903020040c440340e25800c002900d140b20344c4803510011102c2202e0b0f61249401100c450103908503015004401402c81c40000d40b0710000140580155000507003603290500035114100007c000070080001c0c002030040015a0b500c40791151f1f08800f004240340a21000c44001c010305450304ca00e4010704141c20004280b2640c40c16008020030501138a000090343e00051010a0341c520441c1d1245c20042d191168 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 706814676 1250 706813426 706813493
    0x1b08040b030709050f0a050922081213030509063915061c0609080d14060a05030631030806101e0f030e0604050f0c0402030108030a0c 59
    0x1071401424252940c0000e56240e00a1040511990000ba5400340c0922000c0143d070504a80050b00134512807000c0098094005072140b144600707204c122040721000030f0304880d041020700940c0c0c10182c0e00c0c03190806200f45440003006170051500c2240319600000d4a02c000b00c2070359002c040c9005111040300500e008503402c807540c08000c42042e039840d01500b41401c80c00c040d040c41c040e00c1036000502d00e545034090100041c00d003000c2420100d554661b41d0729100085444031001d840903031401c6101083c62444000d0702d400000d0017520084c01380c00e10103018056558045582503204000d803003c1c0c0c02050b400407214000590b450340c0303140c00b5021008240185075014207114410502034840000c1051120800c41c1d110240081c030000041303803500c1e890502486040d100808140da40f1b00480e014a2000700360b8102181035504807090351103607220300c00509043c0701011060000325011802d5614101c01d8584900c10f00043c40200098000080c080106060000500c0414030104840404220a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 706815926 1250 706814676 706814699
    0xa0c0f0e062107030c0e031e031c06150c2003070e01030f031724012106060905030a0b060f0118090605030601150c02150c0d020a0b0906010302010903031b0804 70
    0x883c0320000a050440010100740500c0314001e02e5080980100051440200415100c1c1e00b50805070440340002c0000f03040304e1017082d464100d82d101f0100d0004a50740f509010704c0b85081380070104000d00c008007a640000c01e9031003c10040b0b07042190070b194805c0b11098000b030b00b00300d047d4000d00c803001c04150000c0244200004181f00d018400c1c1c841c0e00c0d0300b50030308a400c242084110707000c0c4104008400703070342800b154414409191250604010401469031000d00004011044005240c01c2c0d5440040040e280d2000c44500145000d40c00b40c408030010b9200d21070902002010980030702c8281500300080d921402062042c0c5061214651007143c846078450080c00d468420648680709680000c9903003017680007152500d203410745828220f5501682070080ca20b045a0001401e9541405200740c1640300744494036502c12075501070f0502091134540055280409840160036501c410010700c01030340c000f5410825645c060400304415012a0f9008034480c170200401087c2070f4001c10002403928140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 706817176 1250 706815926 706815931
    0x60d090b040507120c031202030d020c030c0714150310030b040510050714070b0a060305010f060306200306060c160f1403010e19020d021905090a0c0f0e0621 69
    0x1141070342e141691392841006607003c01c40001e440744543d6802000014001d41d000b42e1014861700581c1e0801e2400e00c500f10890700195806020358000044581040800b0703c00000600503583d2191000c40300d10002c6410701d005c13140c1d00000140e0000105224900d110603880003160700504001c0940b501d4600261103a9416110900e001d04050100d010780380501442c41781306800751103c0d4101181c0f40c4940619600c003500804007a640ea0034080003242080c0071f403500540300048041a92031452401000b22910780180d04803414490005400b4122450704480d0804d90845125844094500c40c0c14100f808444100320890b0340b000340064101e5620310794208803102001c103205003040b40b90a05007601d040d19446006074000b0344c00f40d030b655080303141200702460000d801c501600a641d408035122221309640c001c441c00c0640c0c400c00c114038024468540c4108510820f1158520886010349001e40c81c0f02050103000300b04a64414540b580d50668010424801551140808020345072800800c20b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 706818426 1250 706817176 706817183
    0x20d120f020f21090d1416051507031106040b1b0708070b040203250e010e0405060105010318201005040609030f1e0f0314070506010312020313080304180501031a06060d090b04 77
    0x442e6900d46980b6034607c0d10701c08503a005409104106441155940c990303010001c101c043c04042c0b034801d0728020f404c104261049121340718210460400280c03000c01440b10350101d1100d140100600c0780051303841000c0c2c8202035407201070701c041a2114800039003881c9801110030400c99540360b00b1008049044040011200e601292003082e98844620042e200d400f10f0300508281e1040c80100647d51007a401142103540c03a005415001c1c20035910000e9184040d020348030407a01c1229580920b00d003070724424030184d205003401c41c5068a42003014004425500c80900100e100180c0a42031040741d00104035201c5503400d03e4070400409142c84203d03100040000da000541c0108a041c1942640d0300312182d2582200c01030029071300c0c0d5510480e418000500500440c001440007101e0000000705960107001c2f007a000e107844078200300d5130030310f02c021800c180190f85003061300400120f8064a040303070021207400100b204035034440000c941e05110f0f03007246034182481c154108042c040e03001c7c00207009520 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 706819676 1250 706818426 706818433
    0xc151c0b0d0c0911180d052d010c020303070804110607060c05130519030f0204020c0d020a0b06031524120709050f06012109020d120f020f21090d14 65
    0x802e6600301843c0c001c094034036140340007511100d4003a14100149100c1c0d148a07c045615034a21005081c1d51032402441074009460320440391000c1032001c4c0074541051b52248011825403502c1c24006014440160000d010035190145059990f11444100ea10303e43c0c00110520070310641070001400c9a201d40c090002c0e0600c071580102d403500d4804500e00000c0f04889914443c1400e5403100021a981c0c0d100c120ba000340d08020100d44800309000031085d0950f1900034010001241c14412280500285081d02c0382e00020748070900c10044a18180d0003020070110000c2c1005100e0100300242d280c140c0903680031240d0004038000c08070010390071003a544e441005001a4482c031b00c4c0c01c100303042c01f5940c86001c904520001443c001c1c0b0800c81007442d81d43d060300415201d580343c0204d00020841203059a040c071040300302c041500d4102c45400d100413403a10040585043c9a80700c1078990720301c90342031503031104030000c0c05aa01c181c05041d650030a0b40240703819498589880c00c103c2401a00d00300401e10b00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 706820926 1250 706819676 706819691
    0xa020c01081f031a0f0105010509010e0d0209010e090d0c150b060d1103090d02030403020901050d03090b0304120f021506061e0d0606090506180405040c03060207030806030c151c0b0d0c09 82
    0x1748544116049a006860740ca00b80030050006585200840d0590f68101e41d1440c15200966201c42c64079008050003c011591810030901460404014015030001d003e005000c5200142180b884006102010080058020078010000d5a40e11622150011440c01c0080c80c1140700703844002580120604000c0303541106da0b1100903030316806644000303036000da1180c00420080c00d0400c030340d0660303511034504540540d0f00c42d80080a40d400c1564151000c07081301c51080c5040ba00300e041c140724190903000070700380c6a00d0507809101c8040c00410030390142d00301280701600d0759042c09510030340d20180141d20361640800e055100c000d1900744511000246031f0000000c050a14800701c0c0c011b1f03c024100c014800e0f00800902000e41809041103c00039080100000031510074030290680e244650396180e03c5060081c10580303071140f586051840344140c101e242082502c43e8044610b944503002c020741c412203442c0d41404c0248072208110340c0085544090600b00010392030100290303030180344200001c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 706822176 1250 706820926 706820941
    0x607020d061d06100623041502010605100503060d11030c0301020d091b06080f1f060e01080105090903070b090f0f1c0e0607060e2d070b0a020c01081f031a 68
    0x3460700d05c00c210200e91540181280548072070088040340d80c804400d0352400d91b1b10403108075156556624540180d548941c01c0c003140c1f42085503101c11044c40d25100381035040140009901e0040c00800030240b07602204010601c0e00d084c4030361000f030039000b0002c54443c80c59800101c0a40784103901103800d1040c500e440c444401c1103020040030740300641e90b542203e03a01e40c1131001e6890300240500050026000415200503004d214007009040d169032401840b0040701c1c0054050b54068010600c103000c074808000340303458000309a842c11500040686140e4540100803030034208056003032146400b03080d44036040c6140008040f2000d1143d000d6500c01400c605100329a411030804400b68412810421203010801d070b03810144052403500d00b517589041d04407056408103c1c1140c413102c11a00200030410802c01d003800a0703401030020846046c9001d0500d1402910360f0b604160242c1842500d40108440054034039100c1e03403010003030350314156540d124282204103d6200c10b68071070703402c0b2000c00100d11 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 706823426 1250 706822176 706822201
    0xb0c0618030a08090a0507180b030a08221503090b0c0c060103030e27190905070b07140a110901090c20010e1b101d0607020d061d06 58
    0xc041003000c0c506022040100322031040c400303030144507503220300f25540b000b003402400f0900041c080210100e400316010800d500543c5c181c142d44034807035000140c1c11008601414100c0303420082e5040310f09200288071101c075810b0443ea41203815000e061030402410030b80c06910400000c1d000b00004420340c2e55231b1180041a20030311001100c4e0760058401080000c3c01254005580c8000401e140036040c030308203035126000110320303071414428810001e0104903004010308220400448034280441091070b03c94550381c1585120b411504040064804144501507400c1e1951030b4100d016681c40c80340d81d041c0110701d03c2032050002e02c5004244000500300d4041d10a00c81c030002c568407081410075020083d03403058417603601c022515548600e01f40010920034071005d0981043c40107940b1001c80e542c000e000d401c80d00a00c140e405d001862003251800d0389214500418050304441081e03940076140f0101e410658107a1004290900b0303e40060315481c481518000041c05142c2103856076511640c0040b00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 706824676 1250 706823426 706823461
    0xc0201050606070c09050a1b020105010623040e040c0f0f03061109010c02010c02040b0d0c0e150a3b090f01020f2a0304080d02100603020a06081b040b0c06 68
    0x14a08080d0100700d201c02c00d800c687c6d80955180c1c00054105000380030b520320b0860900d1a4030050350b41d64010300c0302c07a8001c52585038005000c130640e6403500c0080300d40c51641c82a030003941c0b10118507500240030083d00f00010005000003070242125943e48100d83c02c0840c0260008545c2c0301e0070048184480c0e04030400360780c10781a050f901c19000c84101d40054850661300c4a01b44c3c0c0158598181c485252270746443c08507014801d00440341d035207281201c40c201e281805445044118482071083d4690f81d01c0c0031700d0105603802300500c1c40301e001c2d0f030b5600240302110004511408101d048407ca54244c0181d0000f0301c0f0342e50714010303500c0307986076094058200c1c41101505481c1c1481400032400c110004002142010f549641c1d0001850a02403014a55001036010300940c2d0b000c07041000c100c56060010311034807844030f00244020f5003554000b03941940c141c0204020004d4150001c0e2884a030708a41000c41344042602903519070f25203441100c2030b4064200102948111000f04021040904c032a01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 706825926 1250 706824676 706824683
    0x30a1211130501030b0d0b1315021e0f0c070906030210170a0209060f160c15050306060703030b0d0305360f120f07090b0306131104020d0f0c020105060607 68
    0x2042c10040154018845199219049034035034031030900141400000ba03014160300c10301d94a5545892405220020480f40960000350060140c44100034bc0d003010750070841c00d9104565184d42181034140103900440c01e404400340302ea01c10014054945910143c1a80d009480070b11070101016070654001155881c1c41c0207844a4100040c1070034801e42c0542013010000f400039140c440903511224081e00006c01c012642d19420544404008041c0044002080414201e51144081440203006030000815040c05a9000111241010301c6a800b040c41d5440040c80c0030100345503400c005040e900800300c00038482d0b10354017803245002d40421040048075910140c02c1001c40a0509002d01d82d4030759491650000000d21051800120a00c0b5000e5004040402451045d150170b0701da5003521810b07600e140c000d421400030b01c0302070300e55000711114480e00944144858404500031600a03c2851400303904a03262506030041441aa0040d85218280b0390090000f80c13201000c0064510030440001c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 706827176 1250 706825926 706825957
    0x4020304030210020d0f060b042c0406050c0405030627011103010b0705010b2e0c0b0a270318060516030e01051c0e0708010c20070305030a1211 63
    0x89903d0b02d25800428900242c1c130004290140401c10742401d54019400849480134003081c00d00414440019004410301c1c14500781d04c80400c00028148107200242000d0403040e1900002600050f11204a800910f0090205c0e4a585402c00c8031482200440c0d0080c808a03a00547c08158000140120b840700420100c611785036900c1c2138151a900d50155004541c65500c946078a4402da66080d0801001e01d1241070b1240c1160704101c22408490111001e6001d1000c0d003110b41380070070004115030781e101c0c11a60740050000c201c6015851054440c40710070208640b010042003c043d48030301c1aa401c0c50510354401131007622483e05072007d02612103803681d03220440c4030004c0401d1243c00d02041c80441810140d2400350b1241415a0000789440c0100710faa4442c2c00d08049203104101550042802c00000c001142210000030403202000c10b03007984d2204042020780c1807590600c0904015540407003141d83c1d442c1c02c0030300640b1200001d10548200c40c917100c4042a459642022280c1c00303800081603 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 706828426 1250 706827176 706827193
    0x182301060e060705100507081602120301090b120f0a020102070e04030503070f121109030c0117011a0d0219020d050301030b1801091a1006410304060614040203040302 73
    0x9010240c1c1018100b95090305c5250500084030206200e1240101d03420358172001245080304101011a400601040440d4080003450340c2c114447c5003540c0c1580c00214002c20403130050383c000343d100882800201558019600310860f41400051082851403003038096601d059078460030240d511400f11005004918200b000480041c030602010031103e0850510300070751508020078030221040310f8414901c9850015056900d40303020091504200340034685890f00b070611950045e4171130018421041d0344010000e00c81d040244120076203446040d0154115264001610b40035000d5000a40800140c02901c41f03c90b0b000b440307031045906803504031805102644030700301c003d400303038041c0303c0140801d56945061000058051110401d0920030441402140c1800e03003407048111619400b9900b030044600c6611121006800a0008100078002100c134034400314003240562180810186503000c0000308000c10486198000400e40740b8428820004900e0102440120300c41900c01031301582c4035258 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 706829676 1250 706828426 706828429
    0x90e150d0b0106120b1c2d03090612021801030b0a0b0f030117191203060e07020a0b0105060c0a0212150109200f0702040506030c030109061a030106061d0604182301060e 74
    0x6404641a900700040030300150441fa42106000580d8022030018401100421000d54415040c1c040612754000841c0703842005508034405041c842c10070740c10702d83c5820001040e40e641802590040202c582520382d265201c1d00c420000d90300900a0000781d03140100524032050300041c0340ca4110000191440b00311115450348461076059000b81401c142c1c07500d00104103508c02c0c40403540500f00701e0f0010017408540d464104014101600300a00030042481840101c07a00043d0720b41c840f40d016074800d81e0007900002e01e1400c0009030035541c13001c0d5403544000114200300d03500005404401c019500404402d0041481c0144070321140d84040720428003a41c4c0240ca400c0d80260f80104005080700c0000750803c01103800c1d40c4041380309484440d525207818680004588501103c0c02e402c8008000d03503810580c02501164000c1d0041840100301c841e440307000d4540703000304c42c040d00d05141c41c0c03800c150a962000020f050b458042d0078509200d2100e0004104a515400d4160b42d069241d0310000b40d038000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 706830926 1250 706829676 706829693
    0x9140102031e040609021806041406061b013b0705090f0907050319020909070f061b080409050114010914010c2a03020a06090e150d0b0106120b1c 64
    0x81040d104c882c2d6a0000f0310040c0c0e00c0750000d0420850004011407185041303c100030403103082c880303882542d4a04100b0000742d1394842d0115000060003100009070000d508905600400340703c2e4660040c0480200307805d104c5c05900403902d01c2d000e522204070540000141e0102d171983d140b4403a06401c0f10341d40001c22039441c020350085070f00015640880d40e09603034400000c2c0ca491a49074141590504a00c260015030601a103100e5001400100400545150000c190200c0005205103800c00418110908012102e440172100f155005a5000d848545a506110003880c00b03110b80c0010002901c05032400354000c6416104582d401e100740610000c0341001136591080b002d40403034141c0d05201030008510045c403400c105490407000e2190701107045206008840d840c642212091120748041000b40c0c5400c4142c0503445102d10008109103c4560013150410b5000940202101c0b0745000200700940d202c3c2e0340c03107946040e42e10180b10103528402030104044221b41e502c0d00485000012101090644 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 706832176 1250 706830926 706830931
    0xb0306100306150e13050711121903020c1903051206010f0c02190b0c0c010912050c010309031b03030f11040501020723030706020f01050f090a110a170109140102031e 73
    0x14261701d83c200708041904040320022034800c40411803100c2105c210840400520115080c0842040e25100192110040f011803a041c602c00b09500050450340307540e01804402003ea60007060740298140516000d4481d0700668180f000c411203150001c0c00940c4901d01d1111a2039980c1c83d01c8421f45040e40038800d03800041c0c1e810315050b2940315000603640c2d1105000b0b010640c00c0700090044d1011010004191000c294407031544020ba11203960045800803651004e428001d003000141390215190907920450807008000d056040c41541d281855050b40290364601d80c448002c010a0340c401030b0003000360113140601401640185000c1c0986040c412081442c00c030828520040d00c05070400113031034261140c20400041c3c0044030410300241d4240103c03504014a0140c501c860314000728442d81e103114034200038280f803000c1c60115001d0344413000000702400520000629218490030518040c01c43c20904030303980c3da112800100b0300181807013070720301488060810051071424050144002c0310007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 706833426 1250 706832176 706832179
    0x3222103020903030c01020705010e07061209050c0904030305161b1e0501110c120301050d030807030b03011803180303081305010b06040306140f010f0501030c030e070b0306100306150e 81
    0x70001c0500b03568041005e082c00c40c20341000075a440d44280350023820359501f8050403400c0da11a4a09001e00342d00060100e550060162000459807103a007005481c020103041056004008541400141a4180c0041d8807556402e18011030fa25110481207441e0020703c001242c145480d01d2800e0009a03144409040c0fa802e41e1070500b10300700c01901c0301400c50700900c05541d100d12740011850b030340c00c41c1403080c400d12a0b802e00b41b82d401c5625200214140f0300385120010300f044240400104201d029501209100c10701400030440c030101260350401e544071816040c1c2c0810a4003851504040d072100c3c2c14016268560b81b035810030348a00385034011241d010ba004075001d54988225000c0358a0b9103001e4070040d80a60004240c200451000d034594482c06041001c00714403410060000c04002c03054201210000e1030002140c0c0e480c8202203006000c6102240b469024220001400c5688280a140520340172501d0300074540000078103804507582c1d841f031104410034000000070742500448459903203520 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 706834532 1106 706833426 706833431
    0xe0d0213140a111606020706060e091011040509190c0503160302070512130b0301081e03040312200f0604030f0e03060a0f02120c03222103 61
    0xa034214000100421584403405c101c00d0f42c1c111111607412007010042036841e05440c10700c446040e00d080d1003520401c0c44018850115210f001800e400400707120b40780c58a0503041c042841401004c0003074283c174246814003040c0040c02034403070748140c0e5034886a41c0d00d0b10008203a403481e51a1a5641050f01c14000500002d43c0001d03175262030644000450344420302c0c250715204488041c0c100d00304c80c20000c800040c44100c002040ac205025000b121900d0841d206085a0349010364440036009880e803c40304000c0c140207102c180301c0d400d1841c081c2c01d244140740b10000c1c0b81a10008076a075156220300300b000309143e80701d038030240031070004d2a0000c112103203030300040c1d40c800d0080c2481900941d40c01c0c18030541c0000b07a0440754000308156414011345011400d114490704100c802412003200c1c0741d01c0c0259040750141c03141c00d4541c0002d00f000070182d015101d010010810f00144245503 = true := by decide +kernel

theorem cover : BRFrame.Cov 706654676 706834532 := by
  have h0 := BRFrame.cov_init 706654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 706654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 706654676 ≤ n) (h2 : n < 706834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
