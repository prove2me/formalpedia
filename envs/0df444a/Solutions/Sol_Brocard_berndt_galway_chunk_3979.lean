-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3979
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:14:08.944988+00:00
-- url     : https://prove2.me/submissions/ebc0cd91-2f59-4f0b-88ee-7a67ed4bf633

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 715467625 ≤ n < 715647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 715468875 1250 715467625 715467637
    0x18081902130902090721050a0c020c090411090a020c0a0317150109050904050c0303040305150a0603081206030f15041b06050d05151002060a1a2b02060307081503070308 74
    0x1b0088020320212140799180c01030558001112410811844d00e500300100800086d080036000d0f20404040356028940b2101c001d1180b9401804012803001440600c03444407800b400c042816502800507411035981003150400302400f80c5c3d15210b0302c08040280d050b048202400c00000700c0c00302ca407202040e0740c00005503000c071407080c0c82003903a541e52400c0c0307030b81868803c0d00d050740e05d0b0000080000501c080007a071607502c1e540d0750b2003404107034982207410030490f0b04500c0000c05064041c00300017040c60000c0030b02e0394050400740680d0341c4408400405828400d2800958109521113028803050007100001e0480402c0b80300d080280707050401e5005030090084122100d40141ca8800162444144c044010b641240250020400e68507840021b52500c108403841c1c0c2c1c9280c5800b450f1034001107001100506107038060304d0421800407050310100c400d0381d041020007074005100d003e0b500603140c543c000c1d446440c0c40d6540f40744a041c4083c1c40c441650460454603c00d900a0700188042550001210b90b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 715470125 1250 715468875 715468877
    0x1b0302030a17060f1201020403021f0305102106060b0d15050301050601021c11061801050f040c14010302090613060801062a15050c04061808030703180819021309020907 74
    0x20750214250b60751b40684919040290450000c0094030036804c02c403116589124025242489959108810722000755420711443c010024455400e258403805c0289540e0400c0c0104004100c15480b003495520903805002c61050155442e01018081704900031454003400d01280240494101180000c0d80c030826207441a2038222003410300080381d8050b00c0320502d018465801d80b0a80d1074a0750801c044120000500c611039420840050000410086198415035000344040a070790300384149660543e2403000031a05042d801c00464032165180c10140c0000c18440165001060609000400c10a8103038031003810300028114080c20902498090004c107041021303503500f1074559050070003000c010b500d0340c0c800396441c1509004500340d5100c0100251402500c070389448003560301c0e044072104510700c14500c032034006209071800a80328810621600103e040000503440e114841c140c1071110103500c048800d00140c00040c21030900c0c1c540e10b0701842c002c4604104002554000c80c214190080c0104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 715471375 1250 715470125 715470139
    0xf1315030c11030f0325031506020d02070e072a1b060804110a0e0a05041127130510051f080309010f0210020a020c031006180c1b0302030a17060f 64
    0x186204c080d44203c9207001488074800416281c46c1324090010102082da0b00154000e0800c0420001c1c000140c60010040a13030040030101c0c5864004005800054407e00400452a41940d5500e090302940040213580c00f0714000d03e1642071510001c4125542c80107028035044484c1000041e806c5042d040d80550403d0b10800788801801c001344e1400a96041000c411044609100a200342e55110612562241d40302881142200c81007040516016110302d868514491521264140701c14446400c0041101640d18070304107641e401d07061140f1080c10b00200b80d40c410421000d8000182040c22305640e042203c42020f05001d0302c95100e1050140c1607050040d5034410b03100841c820003814440c110041d40031520f482907800025110402000740610a20038411240c5800403070340b040004450040c803018a083c881194080c0103816829284000e03c0fa03100b100e40410400e01e000d160005100b640038513920103250102a242d0501011555a100e0b200c1c81002400d48030b903c115242400100d03035807 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 715472625 1250 715471375 715471381
    0xe062208070f2301020c1209040b1c0303060f031a04031701080a02090903130e041704150305100b03130f05030409020903300f1315030c11030f03 64
    0x10604074070915000401c034207440c105620a00c021092840c0c1c50f401c095041031a0700141004a609078000e0f481c030130009400c001c4180002986c0c0b00003d0002203805840881c81c841c0e1240041c031051401c1d030621441c1c0031024a480100740e81440b508020b08141414904402c0c11a200d000c0c00c402150058015110f43c00085003d16000305004801c09908204100556860700c00c041d8843d26041c030220300030200d5030040380d1004004420f4070120325000840100d440d251164188040c103024000b501c24035000f16620b19800f5009004201070200303042c00e410031900f620002030480f6801000703111030000e0b141013403151180c6030003140d030440b07448501003c8001140c142500d1580001000070594400003c0000e98500360390040d0861400880c00d070340c05554824418249900d40101c2440081040441200003c400c50042d013000725540200508205144000000241c400d4000c010540800f03161422200c2d858003480c00c000c001883c14160052660801325900e01810030b2070781c2209404000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 715473875 1250 715472625 715472633
    0x80a150518071e06090e280905070311240a0212040f0627050103021803012c07030503030f04050f1f06050d0213050a0f1a040e0622 58
    0x444401c10311803040d141d01a581d030050862204103500e19030012042c048001408030300071000501241d2580c41211103035551a181403070301c2402035000d610202948175070210204018460010010b00c20b070014000f03d41142059001840d00e241c000d48605c40141030f06150300c240d4550115000d009400d270a840d031040d918280c0c00c04100c02001240104049070004d2044070740c038207a1080360f83e9a1145803581d0300701e03c1080c100c942081c2e103034120800042c40801c036070351003a401070500c0101e00300340e5020481d4400c0042d00391220349070030040b04a4540a0045501800c00b21000050300940007002c00510755640c05880c1d000c024a48014800b400c40000e081c802d0510014000d0b00c44003040e00c1c2541d4000510307074010300250010005d0680380c0900481c40e0300388903022002c000e40013030820014120111460001c0c04c0c0081c040c25415407144040c291002d420700494070410a400d2441c001001d641e8107210840d51010b0208069074401e400740208800a4420038a09540203018661100000d043c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 715475125 1250 715473875 715473901
    0x40b041d0a0525201b0409020d030c0f15050a0506010f0e09061f20120f03060a05120a05060f060108040213060b0a0e040e01060f05060919090e0601080a1505 69
    0x82c0c1c4c1e00444007000090742c040c4401045807071070100200040303211030010b201400704440c0d80204c029006403042d0580004a40529020881d1622580368502000d80030b0369035007003562a0324903c040850300c400a100394100103000e4158480700a28014141300c8600900800c140341c07100e01d850080318008041126511101601c500300200851404810000c0030001494091b1510f01c20003044094814140c00c4440800c003a801a2640d80c0c200d420300c02d80300e10340d01a991000c1c002c03651000342901d002910703850740020800348042c0e45001d0b162070182414000d08010700144185040c0c2c5694003009080d03a0800152908240c0546120f00e400d01800c407860020f102c25002412101c2022414908960b4000b03907040d0300000030f072028046d6426220805090321218051a11301e1040e2442c2485241803031005082d01503c010603441514250980410341015681c03c1500d0380d035100c1207900c02401c001c00405004000c0000200201d0005031186494a4105640303c0301860702c2d10003148201c0c2c0022 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 715476375 1250 715475125 715475147
    0x1504020616050102040b030405210a090608090f100606030c031103161b1112030c0c01051c050109060e01120b04030e060d14060406151b08040b041d0a0525 68
    0x940c2c0d40d40e41d00b0310741442d0ba070340c5d03040f10030500411000d59040300800700b1607012f4900034240b98a0b10007855007040026102540000c00e40c1b41e15200368541880542e100f00132610381203621010014610303050140c020103441c010032100003454208003410b4083c480040840c0d41c841c03050798424140d0a500310086840d00e980f5401900c00201038070ba03003024455070074030748540c6c0e41088425454004840c1015500d074080d102c24014140c11040112142e540202c000b489054105405842c0c55003000d00e2a104a0f0000c0e0042ea031178035038401c07092103040418103425014002c0316201310300180159940312451003004200400f0001600d1207451161908429544500f15420b03080c82519030310100000c0b09001100c0035817180382084c03c0080c0400345810256400c4629036034091034400a00c502500030440700d801181c01c81e00400c80018111b80f40c2d070260001d45214025040c41510303846e2119032142000d401a1421450903007070207120704078100078001d50320b40030002041e4002c5403181078030428104 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 715477625 1250 715476375 715476389
    0x20612040f0221100c05031609120302010f060b0702060f1309020a080402041407020c06090303070501060b03180c061b01090204181b0b09010c060e010f0e150402061605010204 77
    0x80007031400d083c1420200a01c2d4101d00c0084030500849211403500b9105140c1901000c103108001090700540c1c00548183c0b450014142011040e5039848503100501c16844c086d001030b50344038032404100d060b5015040080180010050628035290001255442000c03584844400009440360f0501d0700e0007046001004030740c4045448a91118000d001404110350882c0708030b04e40441d101600e0310300c5120700e0050f540c43d4028801c0c03e4028042c48003079440480042c5d85171209025500c00200240108405003103181c0c0501e48074244808200395207110301c1c030045070a80151401600d41e45401041d01d40340451b100d0005042464002501e006141e850300207900070b0f042090b20200302d003d021450b56128880c0315250085035980c17100c0d440210b4a40284500c2c1d40081142440030342c8280c01c3c0360580390042a002440c1034020694078216860180805c01c05c070307218030050344041e00501582c0b075048902003044040349130950006d9000e03c41e080e0001d40c01c0c604213800e80309000c000d6050b203002d8044 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 715478875 1250 715477625 715477639
    0x206090616080709031a0a0b0d05070b07030e03010509010b030f06070e0d0f060e011a040e031218060f0709081b1c060f06051912031d090a140a0207020612040f02 71
    0x84415075601400c0032038542042c035003894507240403400c044006010701c5400ae0040c00007203050840c0d21079a6489403a040e010061502101d051a9a0a102d403d00a40081000160781c0510205040c201002c824005000340c1142c000c210110790050000c40c0700314402c0b511140c036800589040f105109010001a00061502c1180f10782070310150b100d5038078060b400c40300c503028101074001c0100f0b4405295018000d600140710080b815080040810313080321546034400480a0715500780e900e01141241d41445040214050004158110070303048003030440c075000f40403112580c500c00700a070120200024010310510314079810300c1003031041410100b68400c1d820301484241080d002701800d00b03406998495035210400140084c100d0381505c044411417021401c09090584099840c10005d00c0c03561042026224041107a0341c4040340385103d0b40408400086042d1180660104140014a0780c1c0c0024410401000980c0d14901510610181d80340e103401141d90b10702d080b560600c00140000c1d00004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 715480125 1250 715478875 715478903
    0x11060d09050c01031a0f2710030b180a0b0916060206041a0f04030311040e0c0a020c0109060212071407230904021f020f100c020609061608070903 64
    0x1e0108040c150b1000907601401080e0000f2950044d11581c204225405541c24583c0080342c10030402440e8503505640000103410b00c24625224900811214100c280720148404d2080204205004ea00700c0000e803001490440182d14090340c03001b981401074804c03078180d0000360208074200a002d072000c150b444107c4200c0e60f207410181d03951109490403140c030b0011001241d1030071401028144503070030038080400d1548507a203003900105610b4481e400d91040c10840810035105240c082801160b0b00c9030364694030428884000d0074200440402410480e40540c01c000c0c407680000c1015000e031450100360741d940070504c1c2180c20f99100c105000328900880c40c0000701034041140d00200708090381280400c2ca41040300300135800c0b108690003544402540d505842400902e40703c447c8021160040340d443c81c125904181c41c25108501d01c1c138aa503200c0503045103840d41400002c0d0401000030040040c1d0425141c0500c3c040c9c1380b00e04a40820a07044001580c0e54170802c1500700864214030243e0b1210 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 715481375 1250 715480125 715480133
    0xf0b0a0603150b030405060609180604030e090f240a0e01080706020f01140a090807050703080c0d0206040809010f0c0f05010203390c01020d050a0903020105010b03040305040311060d09 81
    0x1103070100410708482002d401c001083c08041c81100d00c656806800381c2903c0d521441000701d51b020240083d44085050b029400b0503035001c200b0540118000e40343e0504140a08003000205c1d03400030700307407262071408c0010f00092a981c843d441805903940d42d044100398000c000030414600840c1c1c8100381c0c1c120315000005a0003070210f000c00a45d4400d6080c1e07003200c00790f40c02544c00d03078204003e28a6552174503400039544a4055024141e614400d03000d803454100b01b5200c00d440c0c00b410381c00c251441e03079001800b00e0102c2d0040000c00885c050a002070b000700e00d03150315000351500842c0c24170b505106002c1c01400405110300b90111400764010b854488281050411a000750000c848000d5080d040e6010103005560b000c150281080c04800440304004145540f1107968200515040c02903400b07002075034804409001c0d592107002c1445000035212958240203003540c0040e401045032039010414000440d90003011201941c0d040881c120900c890000403030040e105408440b441e243c90041c4110400c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 715482625 1250 715481375 715481381
    0x50a060503012304020d02040603050d08010906120b0105040504141203070e09010e060d060f060306020c070603140c09031014160e010914060c010e0a06061e0303030f0b0a0603 77
    0x503032000d800801070b904641403588400c5070f1511204419091640008005151244102c80d000c0c1c4050070200380c1c203549a85a518207a1890000700100302c0104c0180189c0c0309030300c0359000820546480c0301d090210750300c40f002c0c034402c1070003401e018584400005007030110064a194005a00703c04840e141100d180d2035030016081030b50042c00240460085658034642100d00506a5407982881041e80e12180100070020119000454890751a030340b250040401900c0340d60010750207028056640d0410100140c00c2c010103811220605140041e00c070740140e150705440341d00045510459694100710340000385006440b07240c1920460802c1c00701382e100000c0c4480d13103006100c040707918102d848880405840010712000701c1070001e02d011008214401c51101c10281c0400081d200a25108141c08403c1c00d44000141070400742d402540c0800401c603440c03040714010103012000e8460001c51402c0342c50100c0c458800a000c0581b07d400c81f540c0c049090340300f05000c00b001808003007465038500c00a009 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 715483875 1250 715482625 715482629
    0x332408060a140c0904050612010515120f0607050f040504020d021818070e0f06030a090c090b01020c09071701030c0501021209030d03050705120406060e061c03030507030b0301050a06 80
    0x40a030804100601003806900a103000d0180034403ca410006240b09200041a0080095521a41880604428410030f1181a02402204001074540042c190910482031080302c0c1c0d0094591290174041c0e291000462582c0c3c10404910702141d40d111000b182c2035039070041c0c1e00559806440000c6002020300c4580c028031350065480350b02c1940c01100700400c004024072003000a03042ca002000503003e98803c619410280b60003e01503c441c0502d003020840039042181d80205042d90f68010f0000e12440c01c00780401812010000d04c034401c8a100000e441d1380100b490305004550303400101d43e10500860710091007424040c0180400c8da524249000007100c0340c403402d07000d8083c00d4210b22003254079004a8032400300c06401004900d140050450003400010108400c03c60f06011650b641000a40c580303001c1c2d4040e49001c83c030541001c482d0ba12070900584407a2081455090814450030b00c92400301500d038150500140702d0f44c810000b600075010340400c2c164154646820072144401640c80302c81 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 715485125 1250 715483875 715483891
    0xa27060902070209010e10030b1e100b04180b0301050a0c08060a120f031b080a0905010e030d180906081b0a0509040b060411041233240806 61
    0x801103644400040032481660b02c0070b900645084018040c082100c1c4107143c009803101411848076590380c40d980c0c0c1c101401d403070020305000a01c60f96149207084422050300311001043e13200c010303850052807949503c00c034440c00b00e00313000e0448034803a04040b61340444d01262020b4000c0c0094902040c60200034013284140102050440303010820b06d04010b40250161000b24003103160156036502c034842107160703504084040080c00c035a0b49808501d0070f06d4a601c498840e4441c543c5907042c120700500010415000350f030404c03020301041051560001107212140d41d4906045409589030348841a40d2000343e084500302d00d08240c07000641c81c9000400f10000425048001c49144040c0d00b00a004032044c0309081d4000541000b080c00314208803078003030b08280000c0c800104010429046500b6802c00e600c01e1844041804001003801a83d980406d5002803c107035030f0080450010071010b440d603600840e090030540d00c0382d92584036a5441d10134130003030110300034440b10f4541d1035064030b0f6120b100b103d07100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 715486375 1250 715485125 715485131
    0x4090c0e1e1801060c02060d02070512070501050c070308040b060a0b2a030a0905060f0409110403020310053102060408031b0703020102070501030b041d03040501021e19020a27 77
    0x401d5030075084070b50740d058404540c3c5804804c83c0710340820007a0b0700400300385440c0c07990030440c6400081c01000b120855131030f0b41002a8486840e0705000307003141d50003000107400880070000b503400260300407035103a40a9408281e0038400c3c1c49a90229090015a81041100303040000c0c643d05c070728034055540605001070303500d180c0c00c0303040041070760341c5a01800304c44001007400d001c01403181c3d0ad404c0d0054a07138107200102c00750415540344810810f5076044840444014800030342031055090500403002032071041c580a01460804520848552000000c110100c5070400d010000805a2b180003200c0c00c1c2d00100070548883e20392044944a0307000d01c040e1503d0180100d0f850f5261000404c0d100c04598058000e807003101c0c903050054020b0315940e6141c1d0b5021350703114448006450401d00110324001c0110056403618148000a440c2038143d0044d40c0410002c45618140e152000400d01c1c994012540703800080401803002ca238816901d508081001d10440d501a101400b844009102a2000c00c1c0b040c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 715487625 1250 715486375 715486399
    0x182704060f0f050108032736010b211e0604020403060906020c010606020703170904110d060e0703020f04150e060c1513030e0405040213110405040f0203060604090c0e1e 74
    0x81a111158515940e402200104100301c454007100029201074030708c4074040c902902c500c0c0320300d100d00100341c0041c15850004614805e1500c550003000c0c031803540031114010ba90520b210b2800c1e041420400340f0f102241f24000150ba02d8940d034040c1c030000d50b4040020301071880145440c0c0c0280d08040c000140541c0f034400c000a940c2d1000448c030040703e41081002038101c4e542588103100d9803090302c0c1660070940720881003448803540e00040017494003080c800074045047c0148002d8118014100500f014018412038140703031296411a0300301d9820300303281f0849800e102d02c15120740801c0329403694850350218054421070000706d00c5080b8412007451100843e60b9840c03d0751028800d010020b000580340418404050030700754011900107000404d169103200d4040e1395071080d01c40001e0f03000103451020400b000141424061140c0c01260703001c0c15410340c5062008542c10340124410b440714a07498075001e4080030b000d001076100480b0082c0c421400c02203260b03440640c5040d9550300310b0103904100c800c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 715488875 1250 715487625 715487677
    0x40f1806021213201c03020114010603060f050409020a05060c0d090608271501080102090406050402280509030d0e0f0108041e0314182704060f0f05010803 68
    0x10082d1115070212001d1006802070303101083c4c044c40c501100d50070070071241c1d1008144081c00783d00903500e0b129a0000c500300b005c4c0f80358600f90301e406038010030905007480d80520074601c942045c0001d907034042d9070001e0b4020050002404154895001580046000841f01100320300400d162000d5245900c5800340359644520450703039203400f203070998190f804a441c1d01e040060709800c038920380c51400c1d040366101c484101500b882207070b0a9001c6004e980d80096254220f0509003e860000c0004036021400e013421080c62611412441c449d2810318000800035100c01070203842034695868000d0102c40d440c114080d00a4042c54258400512074209036100803100d41c07154600c20b00c13550340b100901c0300f10044070304620004600c2c001d00b1014031a6614816a0034480c3d94080c21040842c0080740f0a02800442408414040314005a5000f2030861002d90307a051088c1c0020703041a0301c2000050b1000320403c2181c0140501540744e071045040a000007441000000582030b881078145135100d400742d084007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 715490125 1250 715488875 715488901
    0x807030f080c0418020c0d0206160504030213052a070b0a180b1308160b0f01030b011221030519020c070509130f03020601060305012102040f18060212 66
    0xc219000e40003c02040c045402d158000c1e14400c02d8910015003003010205242d401d16030803495a400503070003401006020049844120b284201c40d0078020700d050b007982c01040120515823124107140d500c81300802d0400b020301d0a8011842c009203040200b01c0c41c080300c08100c0f903200780000e82d1002052408540808410b00c240300000981c055402e14250555a0703c5151805c0144510103141c0c03601118404142d801005190410710040c2d491049400f5141c80c459442015000785007800106006100042d02d114000341501c0d54680ca9a4140c003561070150756141510307025003508907034111042052905a004a400380c00c101b8000d06070200911a844100d00400c0d255074601d0b80400420402828410681900080180c50615001c034261700c89904064a0100460060740000010003000d80d2500c109400b401900b440c14444103424101c05500c800517202c00b034850380c0d0302d0032103070707898030b026408143c58280200058034a403101e801c1001c0250400e04103510100121000102e41d6a110f039 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 715491375 1250 715490125 715490131
    0x13030501050606040b1e0d060b0409060605030402101409101d030d05041802090d0b0f0609041703060d05160302040608030306010906110a0209180d0305060108060d031b0807030f08 79
    0x30308180c2071510000c1e906000c202c2c1c0601500200c2d004209070a81f40d0482d000e44005402010b2000303994a140403407600844103190320002c03c218043c0248001a9140711440e031000390545001111110351002054080c85243e040325400b140ea40ca8409019070800d942101c0054807030242c980c4410030303209140d00d80601040070000508200000d0054038507401c3c2d001c21100c0303070180040c00d003401c12020508200c81a541611070b020088104113164644c1000182d100e0003c4d6054aa9414182c1e10590404001509084400e4002c000580c081d1644c0e00503800703e6030018101c1c4d0300a1001c2c600c1800c061624042680500d04044010a140c6070003c1240d024020607507840c0c040901d4030200303c070010703c000324a6030301d1300800b000d4a0143e600c0714411400750105040c2580c0600201c501d09103848140070310a4141818801045826030b0009a09503100750140c50070807840042d0f01d41200d80c0307946803184c45108610740c41e4a00034441a24091b0548510a07251812018031080b0103541c480411 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 715492625 1250 715491375 715491389
    0x1406040e0c0919020409020c070819020d020d110a090b0a060507081206030a05100f06080a0b0c0a030608070b0309071a03060607060906140412411303050105060604 72
    0x34001190a50080c48010103034074141d03030b0b0010701701900c668a031010790f4400c24a010650340119002c1c00396003410701c0783c0c0101c41c291440031001c2441542c0810210b00510070080d209042200705441404032048800e000100700602030341d959902c43c81e1044c010f10325403d001d8014a0603500100b90385024104a590040d00305000790b003400001410301e2440b440050181c0d405001d9541e510002550801c07001009202a840114200d5000c160182c01c03078660f030f1320917056a48180b1070107020464804005800c1001850349a81d1144110400e0300901180e9010b40c8040c406c450700040c6064060015501540d820426200d403180d0b0b130704003000b00109203020201e0200c8200b011a00382d1034484003d0450920400001c24070420640f00c83c81100c8a4401101c45a03071500d040104002c90a0381242c00c440c241d043c0310044604441e20881658110600e105009850003007903200080340304076145180003401d04840da100d0800d1458150341d88180700c11aa95800c01002c10100d00d0001c080c2c4082e2511 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 715493875 1250 715492625 715492639
    0x61801020a0e04050603070806010609090c03020901050703200d0206090c032e15090209180c090d0804030206070503070605010f03120305041b0f06020f01060f0b1c1406040e0c 77
    0x11420402c00200005421707694980310702800024003010600c8030500070084c40d00c0d6006c0ca14030784076818094501c0c00410404043c41045092aa6a003180640700050b8140c0360400f64001c4101800e200e90b000b05091060520502d442514a01c0c2d001840c030b44500c01d04404e8030940c582d441e06241d038860354103100040c03840720f200c1140c905005600c07010402800701039012901100705071420131002c04903085034048a80004800501d410501d1907010302e01c1a845100d0303914608a12050304074068402d12920540b4900410030a10111409a03006150010003150340c902c0c5c54a0015a241e206140c00c585103414800000b481c0034000d1240300860385c008a80c0096807901840450041400070011148e01ea0b10310582d01c900000c00d1080c4024140084442004c2814060040c0c940800603540285982c142030b030911422403d00c456000310f035540c52000e61250060740004000c07072584c0030f1604403c0d00c0e08e103450020441700d13040319000e0242038904100145001c800c642d03e070600004041d4000729 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 715495125 1250 715493875 715493897
    0x309130510060809030706020a0f1704120c02060c0304090c081b0904020906071202030409061703040501030b030a06090807060b0f1005090d410703150914061801020a 73
    0x1003d141d41030340c0043c1450540c5d28081080e6600d07812a0000800341e800110304841c42c202568002890180204101c440503800b490995107410100d00540646420050010b88110031519040c0c01c3e10003000c0c103181038a886a440d04001300003004007441c2c400c0040e101c070011030b803144101d422140e5009440c0c035903a0301e001120320074000a58050818035401c003400300406008a46440c41c0c100b07d40100d0303806160b540749040b00d06e205407035480d04111909546803585142d038580001c00c031001c80710300382404a59108000002401c154000c01c001d0203003824410503008001320400100142d0f4440c402c104052104042070102450103030300d1154010180080f40c19401c1c0c01640900003001c401004035074030751220b5a42d0071070031001101b4180300010080121298120360406900c800540d401d01f104680f52890030035560300d14500c806800701a544080c0d000f5007000c4c2c3c2143c580b45812149200308001da00f146103030b90307000032a0308241003c00d03070031042c074018418000c45040344100d03950402590 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 715496375 1250 715495125 715495127
    0x8012408030f090a050907120f0e0a02120f060a050105011e05120c160b150d0b2d0106170f010b090f0a050d031e0f050304081b010e030913051006 64
    0x81d0101003d035922219002000540d030355000003140c0b1484641d55030700c80e818282000002501c01d010000200c0034100540040e0701040003500c01040317601110781135500c0300d04030700240c141002580034450b140510000c206d04001646c0020707048230003e980e00c05101d0050003a81b00c0301c0841040402c0025020000800c000280030a2141c1103110000d00a143c0f1121044038100f00d0181c00b82140c0c1720b00410200407240d00860554140e502c2d080d190400b00c2401a913610360120401041e085a9409200c000f40241602207031454640880346820203142d41c64102c050043caa114805403201100c1c0030014198030070172400e0b00c0c121040107034278078104107034042004400390744061207581009280900003025a22404680b02150207070703d8a005420038a0356040c00c030083c401003070003404114000034030100d60000480364440e82048c001903e03000d403014481c0c074101240c0f040080035802d0049041465101000404c41d000003140c035880040a542540e906450b402c450408003214041070822040e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 715497625 1250 715496375 715496377
    0x60a050d0506030c0a0f030212010b030304032306010608040203010507020d050406050a1205130506090304180c02010b0a0801050709050a150507050a0f083a1a090108012408030f 78
    0x4880010151122104c041c1c010524210140d40a80e01d2112290005c00a504151025208507440c0030003d110703010010021a40d02e12030352000624215003d0b8403903044001012034644100c14400650f1604d50750740c00000d10035001070b601039100c0d518101c0030031600d86c00001c0d0043d40ca05980c072500c1c00c1900c3e120f000c0d41ca40d00083c600e6014420500c40100460a56105003881745940481746160500c650030805d280510082225405901c1013005000c0d940720241c0807900c1d81014880440d0362402c100c0103d01500d488400c25402000341c58011944501c10340100c0d100c0c0610703036075801c070311b41c0d4403c02c000d034500591007424640100200c00780405407043d401055064016400c03a1143c0c0c20036980c03217000c20312011090f12003031808198a05080181071040308102071420b00210f1445c500500001050210303007100702c281c2e07030741d002c40d026001c0b4a0001541407070000b01222559a91010a00d018044004d0101c403440701899280c074040d903682da400c1d400d5170380f107400450030243c04804240c46 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 715498875 1250 715497625 715497631
    0x402120606032809140703030e060d020c030a0c020102010b01030b0d0b18160608010f05060d09050708010c050d0608070b040e13082701082202040b0303031f05060a050d05 75
    0x102250803034070464080c003007081940c000143c1c440042d00c400241005070399101a03140826083d00000710410100b58452400809003d00701c0d070301940c0d8007100640c2402131040d030a1070070f401c0c00007040210240341c1010307005900d907001380c000348410344c1204011011200c500401a900141d00c80c005404601c542e0f5506038000150007040400c5207030314488615009c3c40076901100b2070b124880a221041c2d0201491b401004ca09802441c401d0500c0005000c1e80203031691070005a80c0ca4400f0f0301440f0301005a90300414000d4020400c0c1c00501c00d008103030fa8801248414818100000043c020000190b01720403111580c05d440d051505028500c0b0300104040c02d60714441803207078507400100e64150300602da1210801302142107002d26404204140c1c480340b5480d41400040e41c01c1000106c0345074419110710342c0d4000c0b800c1c0c2e038180500c0003800901c50345002c2c40d018070003c401c01c0100304030300e0100402d107140001104034a1f0b82c0e40040014500c500801c050002c1e6050244140740800e5420041e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 715500125 1250 715498875 715498891
    0x702030a1b30080f0402040f110301120c0f03390e0f090f0c060904090b0a0e070e1302010e030a0f150c02010908180a0b04080d0e040212060603 63
    0x500503152202200740010b002000812419400182200a084030010400d07140c1400110f500d800494900c0f5000f004101074082d41e254072403440ba84800343e01c00c0d0f442c43e04d40e400ca0b6440756150b001506850a2510b400c0310703d09040c0002040d05ca02942803403085030750203007800c46444624440c2401040380304c101020f00e400301c1400d00c0d0000c805d9a20b43e002602450324000154581240b0304552844050130310f01c8107410003110755180c0100884c81c0f02e00128142c0300180e98001c1640032500900360598064517403004d00041c003100c03520581100c0c4450107940c4c1201c9040e9114580035100c00010344848503100f6101d280c03000154001c1151850808e0001d00b80c0380c0280d40780d203c40604a81c03940d42141c2000e0880c440f8650f5000c2403150000b40e81052008218200307003a940c03190548038485100010800c5000031582c2d980d162000348004e003081d450a591a0340e0ba038031402d03a0711404483c980f00454a030f50800038682c14141700755801c0b124a91a5058191502e8050264175400580032103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 715501375 1250 715500125 715500167
    0x50318060d02070303150510090b0f04180c020f190b070e040216020307080a0228080a05030d0b0f130b151809060402040605031902190e0a0902030702030a 68
    0x9500c1c10000e00c00340c482c10340251400324070321040b5000c1800c00107051704200e206000c8079165084a95104981c6400e0710740e540034036540d41c460411260800e0180c0d5010303a200d03481c0211050baa1680355000007185691940803a031017001e0702d1049684403001103044000b65610b10200c0300200e1b4410f1f03000760b00101d890800300c40408100001c01d00741d0f4080c0c0d05d04c98084081440610442c1020801503005042c01c00c060080000700c5d50005801541c000407980c08007134544031858a05810010110050284000710b40c0d20300880d00e851030b2250044441005464075058581500e07080104044012000051008801d501000701420007480c40445150700039120300001607408400b035000300b400001c54480301c3c80f18941c501c104042d02074020030b06c60007280140000c1200c143c00c001070b20342082c10552115014001c080441c4001e02541418000c1100b8030028154000d801c00c0c41c0f0181d03c40141c0f004447e25485092060a07403000b40e0380100160310410400380b05030700ca002404031060035485c040b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 715502625 1250 715501375 715501387
    0x110a0c080d1e0e121e0702041803020a05070f03021003020307270302040b0303090616111807120614041e050c040e07020601150c02030f100605041805031806 69
    0x341e410042014407400b5440c0d078540c030b070480c000300c2080940641c0b12006640e91400c14408142800d842c032101051512010108007801195500d4029901c058a0074103e0451b4842505009585040d0600d041ea80c078002c01c1d901003242e1340208403107001d51f500a0403644181c1c01941c0308400070341c0000c00c044204070007a00016050710b00050b035a01c0d400c03140c0f00311551b498190300400c030884195282c514425030007042001c06585403602500c100d41d200410010f113000e05400c0c64100c00c4e0300f0b60f0302c0660243c0e0036004540c1c0400425412802000075568450419101180e03c6040f940c0c2030185001400e40065402e2aa2809800665001064518004550901010f09003e5650540c0c81b61401d0710003203070600c807050004007010b13881050b0303100500c11545084d0300a1824041280c0c0d901c20840005122403d41d1400c100c0d502d2170340030140c200c456000001080300014544c50141c00e115170b0034503500c0b44100d41e540360000c0c4210f4102020710324040340344004072100c0c1b14256826030800424040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 715503875 1250 715502625 715502651
    0x2030714010c0f080a0e0d020c0414010f0902031e0a02040e0609040f0809040b0a09020703020606010c2d0503030f01030b1f1e0302180a112803180312110a0c080d 71
    0x8100091f038a140c0042072002d4844d020842600c1c400031000000201c050010410814202d482400b2101c4035800180c3d6074032404003003661011241041c4289515682c180021458241d00600407541d15800501e110789680003001301100040e03801509050341c0600340004100f00800416001500078000608002d045d4081f071403400c06a4044240b080c1d000c0f039400c0034540c0502081d540710300f0920341480860690b6550240c001c0c2040d409002440030300d040050a843e50702000344006c1c0d000002c507912894000b8420a94000900084620050701c10120700303045541d16001d22640b048408595946003807080c840b89e10802c0c034041c01e103042c510342c0001016807201c141400f403030807585161070703400d02c0d02a4005054900ca00101e201c0018100b141c10444025403490200780c854034440b2442c88290300d03004601030040120039014041c402d41c208020190000340282075000c0c01803040c0b0111806c0c2c28107200c10700540c1c00d0440030600a0035041c0c00580c5101c0240f10500c0b0f8244002100d10441003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 715505125 1250 715503875 715503883
    0x60406150207030b15100e06073302090a0603050c0909091509030f120612070603063002012303070905040e1b120109060c02030714010c0f080a0e 64
    0x109580140e040b8100600c2441000100b25030b00503011040c55501076007801c0401d01c0d41c2010114141001001011034030381c0e95400088444440e01302c4400d0321402000588002002d041c20080001b010030000ca0816440a500a94201160051003460098034001d0154040c140003040c2e110f20030390030845540030341e41d4503407613900886c40c5400520070941c3d443d65004003d480580f101c51280d00034465a4807004564044a502c0c400c4003000000341d4548402081007940f1f208001c1d0154040c5410100340c695041c0d11290807140012500c4a0355011404591440c0c00001903140c00802010350180255019003000c030024800942c180030001300525509000703400640d40d030400078202190400040c40e10b40146c00014207101c0182c0300a44403441500d1003504403a4503140691030554605d16101070031b6102e0383c1840e804c040240400040404002d490b580208011503150001c40300100349680140701c0d070050400d480c0c95031401c510b4002000d54a010000f010080b8071503c1e0b101b840c01e00038083c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 715506375 1250 715505125 715505159
    0xb0f0d0303060501020d1404140103090614240f04050718140a090c0905090709050a031505100b0f030c04120b25232505061302100305060406 62
    0x1030307400580203050800090414050424103010854104600c03d01d000c00c02c000c407022981b03860b107001c048a403c500141e029106040c00030784120b242003c005c400381d80d44410548201e607580070300d103042c5081480344410300655841054104c0001d528030348040c1410ba022641003200d50038103000910880d290420490b070b080d0030106501000408030f241c41d04101c601072010b8520305c40184003105090900402c8140710744500340c45440c0c540082450940602829005004064010305556441c2c0c00c10b0a400e0030750011a200182c40c0c040000e903c0c0000c62840d5040e41c01d0014410b01c0c001c08240780f005079400240c00c245035075000b040000f0b2104061001140158400e2003901c91510385082d045140001000c030060a0548031480703a0246503124038201803551300d070100360342d0414400140300d140f0f001e02030049840b03240800300034201c4100b00384e640c00001d2260040780c3c515612641034480605612000079008905c060010002c28025045103a0005020340005409030342c1e4511410201d00803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 715507625 1250 715506375 715506377
    0x18080a050c0909210d1811191503140a0e060403080c12150907020106080a0b130803012d0e060f031203160e03071406030a0e1e0c01090b09040b0f0d03 66
    0x41e400040001a001b400c8140d00c11100702c20080e2040c0c0c44054620080c80400b621801200708803009500b1008070385006080c99444a0380800c929041c0600140070080d4909000c868400015550741c100340681420143c0220181c000d684855600b40d07400c01004d80f9600d1030900500c440220710905c05040e51144048008610108001a040c41514000a455541164188441445249800544018115440740d00c040031560b650760042e4840c002c1500c0103009540000c000107030440031485241480742c41d040c00c050300301503512910b10b07480c08610406407036802220011f5518600080020000900038090381c1c3e107294112034200c1d0a078402c4074440306998140507100603c540c044464269180240c0003001c409092a0810640b02c07981c0d80154401d640001c002204841c894000800400c1010100c503a50241241c000f11050210100c510a82c4120412109150300c079100e44411500118516031505061400b8880504000007809070000310724829040291030310780c00c8410150107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 715508875 1250 715507625 715507627
    0x2010507080d0603060f0915090c05130b030a11030f010912050901120e01061701020c1015150207030201030c05030708040312090506040803060906012d1106040318080a050c090921 79
    0x80f03240c0170500042c3c0d8500031240074270700b1000d0000203250701d81840c140d800440301c003a19804009000c001810482101036010b001304030f1804204620441d640020020890548003441c500780d503031030300300c640030394018001040c0c260342c40100e80e001e0b8004044160040c50511034403240000b080c801d407802200c4020f4982c0d1f590100b000801d0841000a144140c00c200941c42d0400c2e1a020643d90b450902005441d030343d030b80725100c2c9003404d00042031004081081c2481d170001d8048002a40314600d40c0320690100782070072220641184604120b910134006500c0303810b41c40d125a10100c4082e012221000707017565071111540040b403000c0282c03d110f98411010b041ea24503244041c05801e02c00540348905000e428510340c8003110418001c141410f20131400e450790b03040d0003030003207078000c103015200071175070082c0c50a02050540c03200d00300c0b0500358009816003640790360303071000390707540c15000809040c41d0410a080842441d0100712203800415540481d4044051407603201e800e510031413031800d034801e8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 715510125 1250 715508875 715508891
    0x5071b0e0105150711040605030d03061a0304022110020f0d060602060108070902031315050411090118020d0b060a0203131a0706020d110d060e0903040302010507080d0603060f 77
    0x1042400450152509483e00405484548203c9595004044c001007400000382c843c200c654031303a41c2c8140002c4c031004007168a01c10388410050001c2c03c40e030040700c0400c1014140c1244418811044a01907a03000d000c0f4055000440700b600070b089a117101e00000342c051503915082ca64400e0026003a11325488035580d50307070100200300383c3c11150399601c0308055401000041080d054003080345411500701d124050703925502c20780e00306001104140010592240382444036601c0040fa404944110b110b1064071045841140410052450034424842d544641041c65400d0703084540150249030f001d0700c000b041000954000880c00d800c149600c01c0168000314181c04403003914601d00000b0324461403004140482040320808a206400c40504035035000500300300d0244040c1d211400ba5503580020a0b110303c181c02644020b0f161610501c000d010424021442c507500c080700b22811254140c4a0340c1c5003260716a2000c003540c0058049180300d079521030000000c12000d00415400880140001070805 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 715511375 1250 715510125 715510139
    0x5010510050c10050709080705180105010f020c15041e0311040b01030213120b18100b030f010606110f03040e0414160b1306110c0103020d1805030702010905090403020d080705071b 79
    0x8134007644801c0c410320ae89a80314100e40d81150025054460030b281046900c19459400d900e0004150b03041600601a4159016907041078130280040d0b4140e800300049411100740305100300d21650002400b0300b4185403e441d060324041d0b0201d06546c0060402600b4101800741074814081e00d58007540b2006400b445000400851400c5c1aa00c810350184d6000703131030380c507a01c0303165590b410070000e280607645d0306000d03001d40e60f00b0403000c03001e0340080e03000740600c03615648000c050006821040109100b40214101007443c08400c0c2c8003a515040304450301c030764443e140e5003022500072500b18414041c61140e00020f0100100340e50181a44941c05951664400005041d2050541c032010402406507905009010b010070340380001c140900c1d026842d0850705201c4001031654803000c003841a100007c00e010410048080d0042a001740c8074070254a0b903030018007562405c03c0300c00134010b800c03d0345401e004078040d00a66030001101d01e0540e0400c117059030358060f00c20352406031049403070643d44204502 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 715512625 1250 715511375 715511383
    0x30209040b0a140403090b070303020415020f0706020d1209080913020c0622020d06020c0f0c0a0e01180207061e0e12090303040605090d1212060905010510050c1005070908 75
    0xc0c88400592400f1803405032402001c41000303009008004000207000401d1500c290103076406401c20b010b202103a96544071002e0342d0b40e5050b0020000394010b404000070120300200707807580c0d044080d450344081c1e0b4102d12011b500034071039441c0468107110180540c144584440202c003001911001d00142e41e010510b0399a0303d01000200124035080c062644800c0e00c94203d019050b1041d130548452150401d81c1c6800d20190060103000c489074403880300c82d5516448009a40c1c03818450640e44040c0741601c4201d2291081c200340141c1c2101031403843c40310424240d65009103926400b0709000035280c180102c0b07110302c1c1e02464205410213516034013910581581403084260500a02017000d141a00443c0400c2e20303401170380301c0d0306d040c04008074070140c0b580c5500204404c441ea002120700c0c84198070702c0c40908003a951389400815117180c2880810b0083c00c6201e6207040c3d89005019600e030300300c000411295036103d003944031914021071064136800401d901616002e4a91502c500d405a401d0441307103850 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 715513875 1250 715512625 715512641
    0x3030f01050a18050907081b040518070b0a090305070e24100c170f0304120810030b06010302090405091014060a06030c0c08130603060803091315030209040b0a 70
    0x204000b0700d40200083e0480440050030660001c2c000f0030556a210040c43c14601145c2c4084420b0151040c07950000b002d094821901030350480301000075842c0c51503107194002500070203c00d150301102d8140102015000900104025450070050f019103a036a42420000941d0109094100300b80510602820103076000030300740304002d1809801c8880100058001200c01c02c80d600b8098500c0c182d07020311807080304401212020080903a51000004000004c6500132202076034803050a1400702d292a00c94240d15014101d1084546070441c2540c031010308a120240060b41450b40c04c0040000c0c3d40c980f0f000306841131400c0c2c0040c043d89205100d43c08196918881070000c06e00d810410005596100da0981054405502e4001140000102c003602c0c02b43c100c080180aa500c0401c10a000c41111400481501c16980d01405556030321002a07a41f4005c001525900901e885188220382c07200b03611120020760803088410300c2036078035004900c50740f205403001c0e2069540756040105a041c0c90040106e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 715515125 1250 715513875 715513879
    0xb0c0309100f06170a02242803141005040f0209191403030a0507080906041701090c051512092e0513120302030402030a060204080a151509020309160803030f0105 71
    0xb01440c030580c0000c0c03240d999081d01010031107c48400c1c080300c0ca00c2c5400d44121003019000d0450410010301c03210302d810a8550f0003c0003038103289090010040711f0003524095901ca44c8040102d41c1800c0030800a45003041400110780d40c00d000c20350066130740540303035480758036200a000320f0b00381440000882d80d000030560703030701036031003001301103003031035020701110409078202c1c900300c3d200c004103000100c652185620000407420b81c260511170980c810b500c210710952081080e0500195500207000c1e00144d0880005908a401d00100300d1411982605940c800200003e0300d0184102010061110040420b0191035000301c88040a00c1c21040c030555422085500000102c0c0c026903a410f05c40142c4160310008040d00400481e0464034204074040c195a0b000105640301e54407165034aa85081082040e5451014000802d0080005110700180d1130a524036110019043c04400c10103940041c2c2102c1b41d91250b0017480020034454040c0b0341c060400200619600e0420043d40c20882c14117801c094 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 715516375 1250 715515125 715515133
    0x807140619090f02030a080d0605030d0807030b03011b20030c190f2f1509010f0203040509071809060e0406050402041e06170a0b0c0309100f0617 64
    0x31003000e2030707400300071408010001050b10651460400007600c40e85a009400d0700c1403c0c8500c0401c100d01001c2d0448070900402040101d80c7c860405a6490201e401a4007142110011840e118865000103d1050000e0004038204c0020041d8048005000030303280300089060300180300b1080c40103140d43c0c01000500095050a0b0300324201a16400c03444581082c50400701010b800f0042c217007500010b4260802c0da071942116080e844100743e2a44110001010340040111a12514000004c3c01c5050343e126036071070902107140019945140030549910a620060000041940d82e90880302e204061030394541e05441c4c081d0005c8200d4044981109034681d003440018800c1c0d0440359809640980c1005001c2a2a1110700100f00142540c50789104070010802d5004031028294000904a800c86030031503a06509a481180c0c691b000281300030092140400807680c43c414041c00386800c046010142d400b0030524032108400c80e00c800007018031382c41d143c1104204400c41e1501002c90303821904050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 715517625 1250 715516375 715516381
    0xb07081501170a1e051e010504090c091a331c020927010501091a04050607030e030a11031204030302190615230d080a0809010f060308071406 62
    0x82c00880c070010241ca4140340d0f15181c5144203140c0511000c0394110212040200b4108000c00e503c0301c041203103040d00501d6211000040d00d040521491440c0c5802c29504074500d0b00f882481006403410002c41e421620701082c03d203c03d9501d10b6100403042d08084040885092001504106403200da540e09000b0701051000302600400c1b2555188282e480305001650307a0013000004940f40e0706241140100800d000390402c214080030b84c0725040c1d0300243c0760360035100c1e55604007000c1c50b14038411242582c00140000c12480c106907003c0c060f41d80c46801d02c2900c512008021910b0920450030646121503040000d12b00c0342000c2c02010304903091901210311382411070b100a543e810088a004040b2049100309a003800340950040e0700410580380350444280d0740b4103290303584108001c01d0900000000c0324031503903450042e01e103042450340900f031942031542d07100003a2070940c001442c140b1955207581c103010a01c00d56129100141d8442d031009a194400790034020a41049902540c0031a8400d40c28 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 715518875 1250 715517625 715517657
    0x2040b0607120c06110706050a0e0304050102150901020f1210080d082202090901021312110d03110304030f050d090602070b2805041e030c030209060402070b07081501 73
    0x40034007400070364180b8100d00f00329880d0450080030351040380031a9010205c1d0800800c0340c0c64002034020800d000007444001191440140c80384554490140940d10411407200d48a0120724480e600585500005081c11406410130400c6d13441200c0303241ea10f00d186420000350462682c5020701030160f03c2d00800d101d09011201400e8001c01500d001c60b0086a540f404d000e030344440000f10305403a40502840c6160801003040c5010350005510360703900b226000c2c00400c800aa0b01101040550020b40b41c001d800ca1103000c6c002c04500555040e410803502417005000f90b0710810040008611600b011080d040e05820318508000b201c01d00d110802c491103204124090780050b000d01a02c00e40c0119940d0755800061314002d0200d50007031a580701c0725401c03200c80003c0e0058041d004643d01e00b00079513202e101140c000c2c0051040d50100030030415401d02c1c144058205070002a40c08500684010304c0c0070b0701038a07122841e2004480b1000084e410004010300302c26000d0a90742c01e24002c0c21f00e00f5000a20b111 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 715520125 1250 715518875 715518893
    0xd020d050d18120f090e0f071803080415030f0e1f0212090601030b06030d02030a0806010905040219110f0309090c04030b0112020a0e06031b03161202040b0607 70
    0x858900019207400d684451500c15407242c0c01110340c080d03140e0800d00304483c4050140d040c1c2c043d00001044041d0000542d0320100760702c0740c1c411004801c042000f590742400c25612040b090310070b0418003c8a00c0003100180c0400000c1c03001d090034102020f19480713140b400809841d0102403655140d801e02802c1d40d54074000080b8214070007500180c08891010003003052000b402140221440f03000f4140c1403016038400400c800381601c4c01039207103241e070341e40d0b000c18183e40c0d580715440000141e004120400d1064440c0c90a543c0101c01498401103072070391000054140e070040a0440381102441c0034000040b50080b4038503841602e020050030100310309000064407070286c0e54820f8050211000011101c0c3c400c6412940030303690000c10b580d40340d61070301e4030044c42d10324001c002ca02680c40010040ba02d01498110b991203088001d0040920200341c40682d85103040c050345180d0103200d99043d0160485100403420060458001c1c401440849801000705a62040e09500e004500810000c4046800c0d04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 715521375 1250 715520125 715520137
    0xe0903030f0a0207150e0c300d083c06190f05010503190207050601030519021e040f0f02090114091c0f060c0509010e0a140d06060e010b0c0d020d05 65
    0x18200203101e441007030420341042e080c00c9032a03600945881d16400c0c250004014060070940d2344a01d800708041c040704841d9504070140404001c03540c00000907880360941001128910780c0340c2c51000d0301c0b01c82c0021407107a250b080c00003129071044200401c085414800881c07928036550740e800011091402e0804209032810780500b904100c0e00000103080c200048084000d804032660b8210740d50100b80c207109455040138041196540108400358555090030f0155460103900100090381001140714410f07000c003550306070140c00c5502c2c0c1d45a801c00e500707076104411801020b898050398801802000500c803840700c59030803d401500b13100a244c42d0329541c1c1d403681c1c2ca9a44141d1201c1c410902c1c10000140310304400018086400d04c00c0348100c030780e4080d010f0410f4050a88844002000310810003510912030f0040280d08051030300d220b009454104c01821089000e41e000148841e10748540c412034aa098201540d5080005003185000c101040a0415440944040c1c801d01030200d8006055224903 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 715522625 1250 715521375 715521413
    0x10c0e0a0b0d0b0d0f030f08090c010e010c0b0a1b050f041703190903030801080604050a0b0a020d230c040e010b07022d090105010903050604060903090e0903030f0a0207 74
    0x4120440b440496500810516400800c18440b8201c1854082c9200549640450009100d003030a007103603a018000e0b940c010306c008806000c01c01c03d810011141c08d42001d185504000c1d079910f209000c50038081c182405185154000719100c0c0c03100581c42480b40540c2c400008001d002c1004010162084c0c041d04c050741c603d182035005440705003034950700d1030180d103038283c001c8000781000d0584150002c945c2c81c01c1740c0c465150b0164a07a41c3c2c0f40e046495460807103010b415900041401c100003070304100e6a6038440d014010041c14860022007040031211030340180340080e00e589216001a4050402d035551000340140114501403c18420710403506040c4a90910010085804001c542d20103000c010b0001c0300340000c85c04040898030003c0013030071214085001e204100000b04865100d0b07180403090740c0c1c1010080a160704c5940e9480d0003403048280540800c074003c00013040b090001c540d030902604544000710340364240740c0300464034040041e1000740c0e407510401c1107000243c10744500d0790b100044 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 715523875 1250 715522625 715522627
    0x219030b010c151d1005090d1103090d0303020c0d090905060306012102010504031509020a0f1211031011070507080105100915080105090d11010203010b030408070804050d0c08010c0e0a0b 82
    0x541a084080a10308215130303880c2d405000d00c403160010441e44894404c0d040801250711588006106a070360b801c00015609541e0020880b450850905030707090140035100c0c1c50300501d48000180a1130030200a0034070100000d41c001000c100611050080c00d8202000301d018024a52608a00a850080071609a050f00700c3d8101e20009682c06441034400071a00702126a03401081c50600034014150460103c1c400c9401440110303181011218003c1900e07842c50380684070407520f850b2881960500c2075805d50502c100041078108405500445c501181220f00140d128061442c1c01ea040c14034980000f6078981c0341008200303496400c100c10304204c0300702e0200000d20301e02d455070703224000c4204e03003102109601305018403504080009802d40510b40720b5131144024100406c03018240d10081c82401c0c2c200105002142c00f241d181802044c1c654400c10140707142c0b0741d039100840e9009440000c10b980a1810440411107001c1c01c0c000c0010740c0c4001e103011900303a039500c00080c0c59020303c0e000e48101010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 715525125 1250 715523875 715523891
    0x61503010320130519050f061306030c0b0a081807050907110d050910170601030e0307060507052715130503030f0409060b0304121b02040219030b010c15 67
    0x4900010011402c4080c002c004101c0c002c54440024010907200e84400b00321410995181c0103680c420b00e402010303107841d880c0898446000700000c94008820b00354250765901800030001d03642d0410400107010710280f040d1104003555006c0d2220030010884d01070704007a19074014071702202040c0401510812917003400341d520713403400841b80c42007071920301559880780800030310785283c10001424901008980e98018184001000c445407a00105402080c0501602148281d03000f500b10030940e540e14011a0b041a1032500d40074140d0342c041d0b41e000042030000615403141c100c01900c00c400314200c001409044940303000422010450a5030b6210843c80c04910302c010210031210200040c80001c04880e02c40c40345100300261507215100381c644072464102c0001c0c1c0c082066007924817503030f00001d2000b525104000305507144a90207082d038803070880880540c00165202e10290400c0e0501d0f820080140c1e070150703005021166441071280c14404010000800100e1108250130220003a000105042c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 715526375 1250 715525125 715525163
    0x3020d1103010c0c1211192d05012702150405060d1407210c02070f032a0f090e0a0203030c0a03080c04060c110a090f060602060615030103 61
    0xc040340822560550a10082080150b84441041e44060080340d81e452500100c1405445201c0500e0600e251600400d5000010759017800201d20380c00e001d911445c005202c64248010b40c810b8811040f02894501036110041c440b007449140245000068010a94507c1000305110760403c0d5500038840c40451695003014207041e001e95008100c06041280ca03034808080b40b40241000c5500c1424032540c078400100014401c08072030b00950020715001c64841406001d80010f400120040815841b0705c2c080000e03e651031228030790085010b1000c1c0082c511504144036620100400301c0740c400c004a080500041400003150000c4601000000036041c0040111508083c100d24002c1e44c980800310700c5101c1d5610104518246602c03a03610702c0407030340e140c40c4500c816000e14094140002c840130752480004034404803140036010010302c00c0790130555498204003601c10490304540b403207031983d0003009050340400240d40c1140d811541e2881201c030918644402d03000511001d8803500303005482d20707151 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 715527625 1250 715526375 715526393
    0x2414060904020a0e01080c0405060a12150204050d0b01060f230703020c040c090f1a0a2604230109080724051f060c05060103121101020c0709200403020d 67
    0x10512909190a45d69503029056221180d00c820b00307001e1070420b4005102803030140d041c841a0f43d0b204e10140d0088074030b611444034816946007081d6074aa0f0801010640c2d41d00e2050380c203041c0d442490000b011f581800340042c00c20706550560b00501284407080c200648100e10360181142041c81c1260721440981002c0f4034001107085540e400c107251100512503031b640061110180c94002401101c510388c0e981c404e0650b80c240f07220448a4103402d01801541501c10a030000c925400e035603180d8142d41c4003648410004a0981e0102c0c1c6448440c4681000400c25183c00110004141c0081000c2e40c62034450007003c0c0301c0c1d40d074000d180310301300e4004070340701c80d400f060812110801e11710401503854481002d4038900e101d91085940d0201d80000090b00038412112100002c0d4004040d1400da480c541c1c410100b5213039070411f641480a038071000d0828090074800781c0303540c08100c80281441d6281044001c00c40398041c11000e40e003e5000707041c2443c0181d08040b50700301da038151102c0700c90161a0605020b5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 715528875 1250 715527625 715527629
    0x5011d101b06021603030b03031201091d0105090109021e090c0309070e010b0403020901150c0b0a1b09050a1d04030f0e06070819090f030311192414060904020a 70
    0x2c00b031003c01c0103a0750001c803085002269110f03071020407100d0302400c2003554902543c1e03000784160b00c12100500c590b8005400050780b4a803a070080d00f103070005809140d425110300321010190781c2c2d036441c40e01055103000c0307044142114101d01c102c040107010b8070110300303c1880140004050383c00080410495141002034100030300881d4042e80f01e65848040103041c590242c03009a100300c5074240003142c2c68511081d13810642401d80c40d002c400312803a5884811041c40140b003401060390340c0817030b03a862012408149280b1000ea942c0e07030852030708100c208510011280c000400000c1880151450010720646051b00603030141040d41b46003030216812984142c0680040d50000130201d0b40c1c4080110710000707005800010f158080e0b10501418048984c09028800c0c0c0b42c0c407a81482042021078000c00d0303218000001d0703038190352110000e5941130000c1c14000c02c040358103025008140d25584da80a2050382c03000003135882400702c1802a40c5585025401411080c840d200c1c22002c24110350710800c480b40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 715530125 1250 715528875 715528883
    0xa110709090c061106010e0610022109090109050127230108060609061e01021914060a050402131109130605011d090f0c1e030105011d101b 61
    0x1d0070003514010281c415280325078004036490458a4214100c0410564180e800418184400e65218000c002002a24008075004c1d030003100200c0400500030088076042d40340c100c0d1003903035a0101c6c4c001d2200c07100e8141d0142403042e18100060080301708505510441c0540c0b425030100d0279140c9a842c03002800c4502c8804d240860000174030000d441c0392400300341210700c00426a40181d4441091048014048440d00e600c60040030f0103ca101e02400411041100188102d41c40c040d4203a201002140c40d581003581d80c05903c01616840d00c00030403000303900c00150503050155050a0707021030407080304500b4240141f80c0741c2c695414004001020b0783d201620080401160110802050000701481d01450b4009507040c0d40d40218080c4031b651a80d1086400b90402c0540c1d03441006884138030b603016280031452502000b0300c4c0c503141c0e113158591080b0083d044035a03690b549030a0024100d101c1c0c0f420644645045c0320007078000b43d030325480145034a40e4241803685181802541c4001359040e2814010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 715531375 1250 715530125 715530131
    0x510180b03030f031b041d070c0317150d050a060605060a140d09020d0f0302011109010203041802090622060e062a160f1707060f02151608100602030a110709 69
    0x641f0701001e02c4106ca0820043c91003000c46d15200400c9502003200d50010b000700365002814000e0041032968581d02101c0d0040c0000d0040e40000040d12507111b5190a6442d503201c50f80000521245120300c1e00104000c481c0c16240100b4607002a0510400d1145d0640c1c0c82008140390610811079005220b41c1e56005048036803090b800d14040e1071040490380154010f42c80d0181030302d42c2d20801c030212042e06005030011400c081c40c0410003546072440e0050800c880707400740f00c40b44103070702c4143c05021801713051600c04001841c9581800c40700b440341d42c400001c1010040a020752a20740c0001c817a50f01e030240403407580700c00c4141e140801804d491040c07050b0398070031116620002ba04a04540f020303541054088d110440d62012070360701040c600603140c0e407190032141c4100f0142d8003e03103a2000c0c0c0d0103d401652003e002143c0c4021483c036080311030f0540a80f01c1d140c0d06000540c421411135100303a4480406101301e040c1400203642e03005100c0c568080c040b909884811102c0d0400840703004103101d041c18 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 715532625 1250 715531375 715531379
    0x19051009031d0301020406050909130203030406050304120f17060d0b10051809060f04110a0905070810180c030e0708010e060702010612031b05010510180b03030f031b04 74
    0x244502c240303402c0764a4203040c0810340c05103840c040c001c48040301c01d0ba581301401c052521040140f14600640900800900503841c0401038074188041c0000b070030717203494042c2c41c2e10705403c00c60f080030014407401042044001e822451650030600c0301140001491440c0d816030742d1003001c990617000305000a0030341030300c4400700040c007480400404c0035144150f501c4501043c04e10507400401d201500d958105e90400c1000a202a20120b99180c0c031a000301c94602e0030704c500ca0701007407241075540c10000546071100300b00f000c40354011103484e810003581c6a029003a640f81a514290001d60181001215601d440711030002d80d10035004a06c581002005075840c0035941d091080c020080c00803580058024440002c14541c010312a00c402c0302d441580c9280558000c0c0c1c1e044640c1741c081c030b4052400030010715415000c5902407080512032a0b40c4200d800002d0304111074070314100140c26103c0074240c00c0140301c07445501e000c0192056080b01c2500c09840e6100d4120001e4216010302150700008004500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 715533875 1250 715532625 715532627
    0x406090204080f0102160f020a0b0706020d0b06120c09030708030408010b010306052d0616060b130e0c0402090a03050316170304081905040f170d020c031905100903 72
    0x307104550184040350500d24034905064207038011264083c0340003418150b008042070a80304200c401384d100614804603151140d1003180241c00c4101c0c142c903604e41c0456221a04800d51056407804c1104031101818882000011150080c00500c100c03013840307001c40c0c0c8481d1354900708680b001418030603095984454070b440d0603034020440414440d00082c184200000c1a05100340c3e01c071040360349988042ca052070000c12030800e048090340c82c5030708040704104030030040f05d07284540c8100a00c0784201144100907101002018060b0085c0090440d00d0500c0c8081c1c1b00500159000380800c00f9507001d40c41d440458001400c2141c560310140260000042d400c20344480d42c050600035a01c2241d0b07a98028580c900300440602040724010f002c11010045901c0040300c03502804205d440a00d086490326450f03080701e21194025500c4003606454101244160340c2092144114200c1c1d9031005020798011000003a96415110a01e24805014800600148041440303072007034500c00c0300410b00c100542850 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 715535125 1250 715533875 715533877
    0xc02031609050a0f05010503120a09030609051e0309010f0c020d0c0602060f0c04050904081309020f0706111e031008030307050a18030b220609050d120603032c04060902 74
    0x2660f400040c0c6481054010103582d0310405050b1035002d40206070900b004007018485d54881c1010b00c003405000d000c0040040d145c0c0c050a6036180c4100094a000d40c1c45101c51411089079800d0481d45400620490301140d91107910034040c620185000c10b90410b103070010030411809840003a1690310500000320310f65800041140c05900034091109040d580d400c103038201d0380501d00410b58849504004100031402c0d0300c024200503524115103022540c0e6400036481280c1c020b00d00341881c0c07403021a42d81c06212807485007090703080104010a2603c940015101040c40200da00d0502029011001c1400400034000300405407941038100d130b40d00e0501200141058010000d00c0780024401c141803001c110b0200c1c010303801c4075840a41d81200340c070fa60710183c1d0b0a0351449a00c6501c241001a404041800c3d8051011442e00900140070b03103090301c03680180384010710300000704810b080c1082040000da00a00001906540310041e1014450145081e01d0f600d080340800b6078030504200340858041c203d94 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 715536375 1250 715535125 715535131
    0x9040e060f010b03040302100e010f0f0c020c0a0b0a0f020a0f0f020a061d100e030a06020301050f0d050c0d0206070b180f19110303160c030221030a0c0203160905 71
    0xa040c40d41c003aa41c403d000c0b41c0a220480b401401130b00000d48104204020750050700240061200200e608090b030407072401240d01c00d00c2000c03d05522404440503c0c0d405100481008209032102107400c0d080903c000f10600c170314002a010031006180155905100348920320650740e0000f081c41c0080201c0c1000d251400c1055016803144820361000146503004000090035010f004010901d4021072500b000032030508008c03401c0a00c080700c00d07001c1c0036036024400c24403628402c14006849504180500c8045150b83d00e1150054110b80150004103400007011441240704072164111f010451002c134809000d4080000e21424ac001e0134007481c1c07261a5000c8608a0200080b17507506803101300c0e610307555803800d199070080041d8181c02c4800f15051701c407008405440502120700c3c10b083e4034030b20703003241c0c00c000720a90340240500800e00840c82c11280300d118a00d0b0518031004a68002980641c6038802d10050205000e18a8024011514244881c80c0300c0740841000d103400960308e200300c0f40503141c11 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 715537625 1250 715536375 715536391
    0xa2702130e01051503090a030e01051306030509070503191203020f03040b0403030f0510051306150c030207080102131809020303220518070c081201090b010318170f09040e06 76
    0x91104c1c1d211022610f410f691045003903d00420048510342c4050301c102c0d072405946410071100b0810b14440300c4030110785500404a6650005481c5804141d060030003005804c55442900700084004207000c4003c1280981c54000740c1c5d180d204640210300750001e104543da2003101a40200800081c02441c100c80ca1169010740c400b8002000b541c2c02d140e003255000c54622014480c484005c2c002420007129602c1c0c0c20303030546c00c00204543c07655030326400480b4160020780041c40305054241099414044000244078420083d8240f030090641400010302034011a100c41201d00c400b10078003201034020044040e005420740e90703986489031182040e03103601a0a1365049215004c0055541801c0c40c00410700c000f541c800d0116610340d503504582c014046070003078031400310500c83c0000d500c200c10409402811901c1c0c00145030a4050009410f0340c0c801040d50307480000704a01200801c450006210100c52003038000c0c0d646010342100b8802901440c0484ad801618108170361024480c0002c0d00303805080c3e5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 715538875 1250 715537625 715537639
    0x503070201022218050606030c0706110d0603230c10020102070b0405062d040206130812031905090a060b01051e090f0a030809191707140a2702130e0105 67
    0x34241104003500c45c261407054000d40304200240703401c07903164090803000d403155001040c49036440c0200310030b07500441108100c49030340700820410040c64600c80110041488969010111a001c074103880342400c08410740600860350620804d14402c0d030407900e00f03642c0403180c8492410305040541d0f0b51101160743c02c0c6040d03040c01115a00d1625404800ba490089400c00c0c000c0740d48a9003481065005070410b00c030307030344c00a9034042100718050001010012601290688902d08103035907503512480d0303010a1960038609014400800400b054801c2955040b50707000c242d50b9a0500100c604d8400c4100803501d6880b4000245020b459520003001c603030a0841c0e652490a10003402c00c8015141880020806030741000901e40f5800d1503e461310038030131441e2200320342d1030b640c2d01c022221038840da00803145c2d5000010b092082c0b5481d192440c041c203400340d85821296040c81c1241c801d86d401c1101d01da1070005610717414903070002e00b0340441c0c00880e840010068900d44c1c3d803028503c0540280200d91080c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 715540125 1250 715538875 715538909
    0xe1507060c09080309240927060604081c2102090a0f29070c060807030501061d12030d090f0302010e061b07020f060a27030305070305030702010222 65
    0x2d40703420b018000c06031b83c035400e422442d44041c0d070040c0c3e0000b040480309000c441280e5481c0001c1711385540c80c88804a103200303600a1001c401c55002031940c0c0c8686014801440252000200741282d030f860701241d81c4485401c3ca074246d8441841c011140301094030000300440b01c0f81356030003905424401769003000d00d054907001c031813070148542e0186c071060511000c0d041c2140e0501a00300e941005d0001280d510f001e50781d40310b2079a96841a0401004204c0d43c0d001d00580952600c119030040c0305030f19005a84910010310300d0a101c601c818441d00c9100700b404042c101c4007040c0119404241210010003a011440c42c1c414684c081619003500554a0070000114002002c5215403203405500c0c4505030300696203285c08219086004240d8002c0e100184140703490b10b03070000500f484403440e129460b081c0c0c0058800500710904a59400601107070080400000ea004002d6a03555039150400e41c0e181d40d00d0a808070f0090080100b48000c8180612070a5012450321080300103030f4502c103c041042a07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 715541375 1250 715540125 715540139
    0x702120310061b030503060d03090509040f0b1315020d0f0e0d081506030403030c022505030f0708060601261e010b0a142101080616080c03070e1507060c09 68
    0x1e9440c640213404500b040001803d81e14021444650340b51290400014940d29031012500304c240c00c8070112085254890800c0c244000d0002c0c807a0701204041c121a00240030350341e01d1b0300340c0040c1c6480c200d0441d0040f9600f10341e000aa0004d06202d21448410041000300b580300c10340d01e090381700c0601d0200d032641c00452001d0303ca82d0031501740b50070060000c030b141d070325581d504600500a000c8144110301072410b0907031200d9500e011520260328003600040d007107407c05003054206004952031450039408400304001d03004000c18840e0b8404402d080641400020003640c485043c800c10028030300c1c500701e004000110014045040f2800c589403203007000c03a038a41c042030450307100c0c0401c8080494035441541c0c20086911004190401c460b1400d40791014603070081980802c02038000e030796260480010448844e01a4103001c900c480bc41c035150605003407204842c020351002a0080c82004079042241040340c4030546400c40c40f008a10344a0307907035801420110024490000444009a22a18001140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 715542625 1250 715541375 715541417
    0x1503031803050d0f09090c110d0e01140313021201050a060e07080a051b0403030e1504031a1510050d0c051327090b0411061c05070212031006 62
    0x1a80c2e2020050201441282c015103070180c00394010750400c41009008140100e250103000140801611074550180d100708034181006c1c11403002e14200840b104007108240e0384141c60780d6001490144041c0d40741c0b0b50901c501d11071641103e01942028000b004640300701c0c41580004d2154007456000c1024607241e0300c010108246c299003c0d400110b80c80d02084500a0380c0c3c0c090354020b2248400b0320440e03080300310b17a12640d4206600940c0851174002c00c0b41594200204280d200b9000a5880b5160030708556030382c007031407900000c0380825030000c0f40042c03103100d0a44060041118000c0170100b1007050701000501a070300c02c000e10b03000c942c1030034114100c0340d0040090320008806140b0569202c3c2c20011040b40440411005a0400007140ca4140b03034400280b0903154028021000392007182b50a082c842003540308141d915005480410640061000c0c05508086d00040b01c40d010800c1d40790461b04234504420f4040c00c090000c0000305024001c41d000541004881c0d03981c88113110700c0c41040c446181 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 715543875 1250 715542625 715542629
    0x50610030c14060d0c2a0605100803041806050406090504120207080d03180f06060e0c13032a09020c0706050f190c0606260d0f2115030318 61
    0x103051096113820f43c03064203c5456840ca5242030007040000e00000c01a0701003115140c942d641c49a4852000e0064034003500c1c0d0f118121100c10a100380c038001c0d005949208510a810003910921000c07000704900b43c00440052100407c03d1101035250000320f0300820742030390212189400000d04842980c00490304000701c42d414006003050701c03112401039015010918a03150040751481400000508408602240301d000c0c002c00240607043c520a0b0882c80d03c0900182403040c82400a0345620820320b080780c0580e54481c000e500121803104000310150200c00c0c00035100e5045841c0410002c0143c0c0c0a80004100324048860031903480e64162100d00c180320f00c0941c840c01c00c0012168506910307400007540726480c034064400300055210007044550076085210701d03082d4029140c8058241020203001b9a0b00080941000c428070f007405404000e100c502282400b040c3c81c0369442d85441420b80c90044071059400307201003049001030700d4041c1020b01046000c1191b0b6171078807052400c0c20300350000f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 715545125 1250 715543875 715543879
    0x1005060f010e0a2c2502070308030610350c070c090b210d02070b04050907030f0605060711030d08040b1503030f0d1407020102250609050610030c14 65
    0x4540b8200001481070003003c0c00b0103240c1c070600c503010ba00d6801c035058403984909011003800002c1c00e242d4006024000d6175401c0702c41190300c034000034000300744c07448110f80d046102120b02c0111030042071010749200030203007816581451a014429038841701c03038000e00061000c48110680c150740780c04e017401d1a4003a006014045050388201441000902c0c0d2001050740c2c070044c1500880d0005c1d400038a810018016500602c0d000300130360255254040108002504503244402c0c00c042c10700c4081015041c00400c043c04154a402814608403a554003500190be4041c04455645110341403100094440031900c134024403c035684014164850094140640c1d4050381150341c40d16040142e0030995680760344103606003c10013161000d96410b800520030309010110100d041354800c5400d511030b14000b00b040040d64010020510a400038050041c240071103580308020004141c01c0c81001080b00f031400501c1481510300b8407514042540c460000c03a807041c1001010760351607603102004428040a03503030f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 715546375 1250 715545125 715545139
    0x7120201021602130f02130807090204031205130806011e05030a02010507120e130e060a09030f030e0a020307060509030622121b060209030f0102090a030f0201111005060f010e 77
    0x1000621302043d8400058038580c8000c50110392801c0920100e9014020000c0646004002040600c2c41808103000074000e12500318141495074669008a0501401120420200040305108810340d00c0b0283c0c040c7c031070f8000312105585c4074203c2e24682850710b606e44004c929181d00002e9a85000180c1110066040c0e65040c100005581c80040f030900d001100c5042c441070025411707543c1c440d8000c0d00780e0b0a00d895404104554840b500e2400c1c001d000c1d0080300f07101c0c2000202e10221350032140e03030701030107105150000742e810103a00c0c0c280c148100d07810000d51500035082c0c0010680c0d401005041c00c09070860544c1c407035880310f0b40c280c2111004201e00380001280342e8080b10219202c010403000243d12410724011000f0f99105210119004850403100198045903400c2c0d44e0804000d06510b1008080003145440b440900140840e450b40c88000d015004510444046920039054000c104051004803034883c10801807500c05890200c500340d000d803000000034503481d84602c550800440c4003070241 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 715547625 1250 715546375 715546417
    0xa0c08010e0c2b2409060e0604020114090301020904020d150501050301060c0b0a111216180b09030c03030703090e0c07151a0604180e03030403050a260106050712020102 74
    0x10a40c0f501c01c054080d50500700700604d0088000a00040c0c00519500701000141c501c00c03441c18604481060240407000c1d03000c1c1e010040140d80004640b11510203900000e41c81d00410000680a441444807454101d130000c00d04003401706103504048604407100180c0010103854000454042c0824801c11001800222a060110300642e03802c0d5002042c511011440e0301c82611060030541c0308041512000308410304000c60f0451503070891008007054035002c800940b80343d90850000310381d4080c3c1c4c0f5614100040300744a540c5e0030801e1036030385240502901d41710011410040c11002c060f2061140041a40000440e4041c200040b41e007005e0b48800115019080d28401702e008141442c580c0035402080c801607001642c40781c4c0504020565000f101d88120160321a00041d07403101d1a86014030307031040c02480300203900241a218034030460b01d040c0c11112412410745c034403590510780d455401a4010700219259600000500c401802818440d1081d10402004c901f02d105e04802041030320503403100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 715548875 1250 715547625 715547689
    0x4090b0901060507080315150c1608010b0a05121006230d02010503040618051c1805090c0d060504050106030e06340210020a0807090902040806070c050a0c08010e0c 72
    0x8a074030b507e502401c0d001514400e240b00d600c15910400d24141d8580c8280d4141102074000c6811001606140c0000d000307004240340428184c807624018148511604201e0f41c1c1e28810820140411003a803e00502c0000e81c0c2340d08001800740140b1885c041c6080b0b040c41c189803824180440c041003603069481034231b5a81c3c1e58440303100811032001603a87c041d0980070300d4000304400300118240038001c240a01c50714050030038050a00e007031040388080241c0c10780380c0802c41c0d42e0346e8685150344840003010040d80d80001d034816038003d1407540c10150b4081e00d82000806c00640c10391100004280c1c1100703c030b0150b180c0c3c808200784081e0041070756103041c13148c44c0c60650280034104090044920340c0100c44601500c240d805007643c110000b50400980c84004010f0029840b11102c0000c1c004902c0c21441e160803d031800c0c1e140c0000030034a03004d10209050542c20000104a00018182c0280500510548400c0c0c1c040c040d1010f000203180c41d104440340d0100c00d2030500046000c280c0d551204103408020383c04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 715550125 1250 715548875 715548901
    0x908070603062102030307212010020f1303060501090b06181201020c060a2406051206060c0a0605041b0806190222230102190c050604090b09010605070803 68
    0xf404070b805000c10b03c494400544609000f010380581c0ba00401403903804080020000160104a1100004181140c00309000003162442d0b000400d040c01513501d921003010030009100b80c082d040ba6182d0101400400d0005541c0568140d0b81d01103801d102d0314501c04104100760107400e4062040414582c69405c00e8645001e00d1428510300100160602d07020060041c203028040340c484490325110341c4007090522450038030140d10210200120105820a10003d000c1e00614124039034078028600801d080d607440b001a80c001c603c2c05022246012010714181c00500400d6800321241c0040d80c10202900c86018030328016600040010311700795030b42401c51034400202c1c5240300c50181c0e003000003171b0444800d18480d05024400100341c48001c1e260146040f0071907442120110400c048006444c0d50f80e0340454501c0d22842c5620036010b555400b810041c005542d658422a441140007500181c14401500180c5201e50304648509590f030740e41d41c0a40da61310800c00f0003060140100300040a0000c400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 715551375 1250 715550125 715550189
    0x801050f1014071406061008010e060303090d1b06031e110d06032d0c05010c050106080f1b060c0c121f0203090f07050901090e120703090807060306 65
    0x440c2450b03a49607920a24000d03503210060a0790b002607454181120b42204100030380c1c202c0810380f4040c00d902456100140f410300c060290a5505810001154180d40c0070415141040c500401c5188415030034500170480c10a10351f1101202c0249050014070745019220b1071040a0200141c228010b0b00600000c1c0244600c2e280c48151000c1070180d003201c28194810000518401c100c84182101c4603031207002ca00408014900313007441c912451400240c228071702c40c5c003211404e0031700084410803490a103014000541008480c0d22a4401c003840081c0700043d130b01c1c803143c1c2401c5004076a60101041c03148c2403080c50035506d1980d100c1d911080300c43c240846000000c04a100c02c0c0c507075807042c40f400f2042b030141c01100210b03c26004024010641001d014100c004602640100016440d02c070200c0c172038100503c1501d2e002951004803240c1d00e901400050141c40909400580e54610b03803401900181c0301e0700607511144604080814054024425081620b8100e401403032070104d00300b200d6190398400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 715552625 1250 715551375 715551377
    0x7330c0c080a21110319050402130507030f0504120e030105010f0620010507020d0908010902090403140d050c280203031f0e0a06150201020403022115070903050d0801050f10 76
    0x2010082c1c001502d0303885180000440303050340039906e090041d80c0d9404c1803044199070070000d2414043c000141d0312003101d00008040e6034070100b1540c1d20f4800950040c40300308651042c2d14180010002008a41d03703400c1d0f1440160f0329042686000c1a080c542261005d0180ea00480e030028014040031b0f000b01b400d00c403a404818001d40c55101d850700d900d0b0a4440503070b030341009640301000700080250070000501c051b108200003004240d585030002612204090000f505008014104403a00b420fa20201c6010120140d0305001e2030802c1c00034010300c0d48c007008109001a03409801e000d0780c0509075603110080080359008504503114000781070309070011040c42400c5441005000110381403d446d445209020b4079000280c0301d0f00d452141c0003803a00c1d00212804592040009000594520082d088c1c05982090361307480c440c59090f442031420014540c00c001c68840f1204001140c0c2c1e0000412040c2ca04c03403025991103d010780401c1e01c403c1d0b401c0c01110360041111a107000c041c14003900d07030b000394051 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 715553875 1250 715552625 715552667
    0xb090c0a03020f0312040b03010501350c0904110301050907052a03041d0402120706051b010f181401050c07031805061308011104030201050f07330c0c080a 68
    0x170311404550710340c0580e01c1468801408001003046680200b135441c0607400d6000980d0f168940c60411501c8460035041003a440f04401000c5800403a10b070051741c6080740068002c1244540440055034a90801d20626120f002c14400044000384035500380c400e180c61100880070b900c032104001c40302d4001580740c050a644800e00001440240200ea131000418141c203241c03009040a00501030700306101d003403542d1075510101080120765030240171140c442c034403134100100e20402000c90902500d4019901089542025140c8a110090656a058042c41081c0480d041c0041b0b06440d4280d4008603018881c0070020702640000c0b038010032005420107080c441c00821503072581e00240c1e403900141e0a1203240c0407404428803c55000744581e031400454124081e0400d1f2956000034450311031514003109610021490342c00304a01034001c20032226240700d0803c24904040740441003051140e52020406060001c002d105901613220100ca4940080c3c01d54a0402c0782507003a01c1c8250091070002d66042 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 715555125 1250 715553875 715553893
    0x1002010e0a030309110102060412050c03040306050103030e01110105060102060c0a0c0f03090614280c080324090613050601090b0d020c0c01110c041107060e06040b090c0a03020f03 79
    0x24081c01945200e602c00c1e14009448141810103c1100c2d40c4034060350b0666000740240030208001e0007400c00d220040d8540590f556a12803401030035408ed91707100070106808d0500101c10560080d00000c07044400380e0310421000e120310038003826180162426409600160041200c80c004100203103c070700c220f0b04110315011030a65a40d81c1d1001005001d03000101e43c00c0f0305001c503c0c0e004440c5000190420b114504180002d075400010500040d99003000c41c242000054080b070080140141561b0001e0520703449103421f84503a000f100607110a000c03006c06020b01c207421894800125402401d0107082c00c003512100300c000d01c000301406081141401201c0c400085d0b402e00c0e0300010480c01e00e075007030003588072071020700c20525044500c80b500e4140400301c4100380c0024800140c1c035181c60703812500802c154030fa11406400702d00c82c03c2000b80c00182482c641c0c003044640050001d015500c01c1c1809407965540455944d15080401b40740c035405505c803181080945849509029410001420788030568 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 715556375 1250 715555125 715555151
    0x314250b04140d05061618050102060609040516080309040f0c0c0f110a0308091008010b12040c0e070f12050c0d09050309090f010e151522230d0c05100201 68
    0x21501030741850841b00c40000001c3d40514100c3d52100140c40103440141040000f0b03442d100300401050041e00418002800d108040040c3c5c1c24810004e16851003094841c000c5d95100e9019662407405941002141d0540c0d02592285080319003141e07641030031112060760780b0a01442c09040c10b9031002c5014050500c60343d104035030980103611400c041903031800ca510501141c0300c040303010401446081d500400400e207985040301c0750030383c0c0700408441a6440c2d2800420150054110142800d10b00b01006042ea0f001421030041403041e803600d240e258440302c208070503903008540b14a0403000034041c85e0040c6000760001c900d07007480342041d02c1c14500d455000c05d05440c4200c541803107100046004200e0300b805922540d401108140d070141d181003004000c2110000719065015080ca070000d038004411003c000d00c42c14142d91310b03801c03903403050380c50444c151040308403603561505000914a030040c5207070810040001d1940004014003082c0351800b003150606901e805c1e20306554907060110681c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 715557625 1250 715556375 715556383
    0x90c0117010510030b03030316030b03030702011b290910060b0405010509280e0a0516050304062c010e07030c0303050903030417011a030109050601050f01090314250b04140d05 77
    0x40022610313104080050310389c01016280e103400b000d40650010001e100250f64010300c1c00702281f50713281c146410760704945049000041c40c111505401c0b0303156076488020644881e03005000c1d00703100b0102c420040d48801c06c4c404807200e5210301c0d150754104010030002035000c2c44c0036182c01803000785002c000004013001c01c201030303400b07800075000360704000e0302440200400c2038003a402c042d403460100900c2c0341c00c1095080850304c00d040103081c0b00300400020100f0529030030004113400410b103000c0030070886801002c00d40502001c000744550800420a21994002a90100700da40010b10f9108031480d513241510680c1c000040983c041c0000c01c00452440343c403040c90204118000c0000032101310301a40e00700c0501005c404207100b0307410446007001280e4001049030548904560071040d0070740040059507503d481d940010701c41c0040d902c0c81d000014000c5203c60050541c10585101e00600303101c03c0500402501441d0041c14003400140300c1c082600041d440c4080c0b01510b8411941203580310a8a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 715558875 1250 715557625 715557631
    0x405070509031b030718061a03160309060e1c0306060c081c02120103030903060c0302030601201f050417090102150703022106030106090e1203041b030b090c0117010510030b030303 79
    0x71035078071040100300d00142c502c4208c6118005040b041c0c21401c15401c3d400011001d10a80820140c4440e80c204c1400026030151011085030411200e0780c00d00c0400c1d8a4001d104910b41402007880c003000022001c0c012492800aa603005e0102c5245c804017001c81c44810440d8086648050780c00d1000a1840d04a0034040340614004c0e225403070251b242d4070b8560240d40e100011541014010700c01e00c4101d0360054203c1c24a05014101549000082c0980c6850728800340308102d03881030038428002c0c0700340065000500882c000c0040494003a002612400b55205415800c0d0059000134900711310105101002900314160345409881c00011101c010b445404100c40d12a1080079402801420b250912031035005201c0241705005264000c10404d40b41c091031720309940340310000000074040000014040a09802c0c0302501c019140c0c807410829120003085498903200e200e10040481d0306d45c003414880410440f83c1d22809042d0f8203000500c0035514003989540c0a041d103c00090480d680c05002442c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 715560125 1250 715558875 715558919
    0x103050c0c121c0606080103020f010c1217011a071202070503100f24050f01140f07020102071a0a0309050a0f03051e2701110a110405070509031b0307 66
    0x91100e0031800c42001c103d1031050b182c07601c0c0e40f402c04d041140940201c0941e0450f50100c0b40b080e12105980300503202c136914140d0044c00310f450280103510703040d000901c0e600b003000b040c07000382c11507a00c444206030140038002001c1040701062002000149001903014403108092065908846c0c1d1000801e141400c1030025a0807151180f4941c4d622000c18440c3c01484203880c00003006601e4210700c202120702450203018000c10700400e490070281d0040c1d0010150303202590354160384200840e1260182c1d0000c01041380180580070001403015901d404030800143d0b4000c07900d242c4034241c40154000c3c0707482941100e05015442180c0d000c80d07100045000c410b07010f034640660b1091880041c05011511000c4107451580603c40108202c0d8103540b05162420300744444030208903088010380d880025650001c000384520b00340503040280316510f030300f044501079070309000036260141e0039161401805010703a0135030701c484000090001070101c0c12420784000707819a00e00c96145c00a0700c0080d0700c0307000301038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 715561375 1250 715560125 715560127
    0x810020711031606200609010902030f030703090b1e0706060806070f091509030c0324110319021902061501020102210702070906092301140103050c0c12 67
    0x250501800d004806007030364045024041240321240d07406403585031402580c0401c8a08100844842d400b040c5140e0301d420010304998492800008040c0a020710107002c0f800381c000c1b540302a0321580c002041e652280e13490b40300c0440c0725041502d40081d0380c111461201800d51241c01824544070f80400070f0500d1070040d4804940c0700d0074012716914040d0040c041408021403118000a219413103440401942d0a20960101c40070440301d0486022201ea000984040d8148500104100e0301d10030340340e5a800e101c0040ca03051125200004110b441208960802d90000c02c00168071a119005540500c0e805100060810f04010140012802c02401c01005640030790140152084d4080d10036440f00404d1009501d0705403611070076280c0620043c80070307105000c4100172510b02402405680701402c25000200f000e666603040760005405442607003250500c01400c104000b91f0740313400640c1601d40341d010b010400d0318000c00460041900618080d0000400e0041e405691401d118000b00c448071a0441 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 715562625 1250 715561375 715561387
    0x1020913050406050105060901120e070807060c050705032b1202030c070611090d030c030210050709060e012d050c030406030c1b020117040501150b030a0e0703020d1704081002 77
    0x50030843d44c0682060788075107c20703c2110600e80c2e020043c843c120a48a0b0003003030078004640181c0c54890f0a4210301c2e45030045840111744203501003800c119030b60144080b40d2880343c2e507805068455446214045100c01400d030018085c491035000c85403948072900d09811401e004c0b01c90b84040f40c00640d4140f8118a000a051082c403640e0300908242c1d03045411420724101102000520988007508010240802b40401209050090100032480301c03d591086c0518501000c0040007422140200404501421041846035218480c4141841a120070072621180104138560401c44082d441208001c02080f001105402c140054001441c1644021540901d92600079140d00d008410001103810300740850000f603a400510350005104030140c1c08199102c030308009001d000954074801103000780c070400050b034804050056114054692003000070a61070002d282e00c0e0815884027a5000040c03524050120702802449120b60748451525032401d03079240d203440e01b441e80c00f2001c03140c1c20f41c0c00b1500c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 715563875 1250 715562625 715562633
    0x9010c090806010f210f030216060e030709180510060509012408060f040219080c041a0a180801090c0b070203100e0321040203162105010209130504 65
    0x4400c001d04941800b802c1c840d030615540810341c020138811074003a000d4040800084c2c0d00d09180e404003003500290b800040020606000e583c56064075549801c1c0004440c0028425200300c03201c0d40c0d1140c0c014040c0242e585424402405030019804800000386440f00351400580204085017025841c10804201c0c2e52510781080034142050780500ca0110042100e0440006c03a5130b10052021000e061800694680c2804238203200c1740d803090240c1141c40000c15000070409031003419280d41c255981c0795115554403d10f1040360081e48039600c0945110403070301c05002c1d40354000c0c2460201030301d00b040b216101e03036001c0032401480b5401106030303940d10510304082c0048198010041c05205803c5480d01200b42e0100769901e070707560712403042c2035900c50754418046418001c80d003580b059122a800318991a40502210f540c0c1910100e100b0310445400e0381607540d949100404803468500c00e1100c00340e21421407900120824404c881d1954200422400ea9403100307030015050000100018042c0380c07a1034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 715565125 1250 715563875 715563887
    0x121e010608060c0a0503071704050303040c0b2a03090315010e09010204030309050622080d12090327030515061008100504090c0302040f020a0912081209030c0609010c 73
    0x71510360742210702000050004181103500c0b10301280b60065803992229400c032010a80c1035036140036044214107200c00c1c0703c0c0c0000038500450161285850055079101c0d100d186c0c1c801d04c0b040d400d9074102c661007109caa6400c448541804800801501d1038070880f200002e0800e42080c20122440c0d40341c10050069154102d10b040e8000845002186000c0c2180c0b40030f07021541c40d2164a104010000d2070740b99900020050359650020000440b482c00c0c0c5445e6201c0d02c60a00304070f0031000444148150281c2c55950080301880c40d015204c110001d080d42a0882640c0c000c81d5054001003240c0c0c00000001d0400c12401c00040314468216a00c0d044c4007040049184181203407008009a54003440550201c0516074030440f074080b1400203120b038003440c0004800701280d04c0070f54018605080202c20060580091506584595a2040c582c0e11021007001c032601c602405031030f0780010f01c00c3c1c5510384916100c103904019444122410128815411481c04200702c400e50040c2e511003079102d20700c42e0080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 715566375 1250 715565125 715565129
    0x2090c0403140f1b01030e0f1b041104060c03110f061008011a0f01030f09050102030604060f080703030503100e0717010902160609080702060a090e0105060a0518121e0106 75
    0xb80c060824407041034511691034482c0720841102186050b2520340f1607000381e20844000e060b910980c2d42c010105000c458a48003191000c4209180e1075600422a01c1d1501c644081d800b000c800b0242018100300c41100c0f2400106801c90501480d0324240f00f40000401040d130000304180010203c500c0d00031420381034421654001c2e14140c2c188191800c02c1d10146a0b204402d800c1912800240402240120081c0282001c40c08071145414001000d112040d0029803089006650034003da95031070300a491820554403801a4542124078180000381c071400040d45c0049005008220b85503c03000c8141e49000103441c84404240d201359145281124092440d0041010420840c100309003040071525413049944020401e80c0d80d8945070080000000a0318115900980031a45580c42d00034007034410240ca002e1214a070007190b0000956103007250464140c3c1e0665947da5080640000b140c1101d42521301c041070b40b2891144101d905504100311086860f604182c0015031500062100c03421205c0c16 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 715567625 1250 715566375 715566413
    0x41a0f1c06232e180807180f14010602030702100305070219020d050607180902090f01050306120102031e060d0c03020d08221409062b02090c0403 64
    0x8040038091800e60010302e110300072050390050b9031089401100340e1515001050f4061000c0d4008591000ca41c0c0000c0c0101d00c240c1e55201c0030500760701c4184065503841144a0010280428400b0409006503508900c50482c105100403a410f5900c900da5030100109820040041c1d00104040d000c2d880c100038041044091814208203d0400080081d1200340e1031020640324a4040200700840d150000f28809990300403007a9001420880d2000b02041d2060041010ba4040c10781c010841c0c0f8128401c481c1443c1c0018039102149101c00010744054000030015076000b13220740c1203000d82c04402c0c001544202400c146201d01058000030032610004041c1a8500032400396003071000194201c3d00143c00e8036012500b100d048000b40c94810400d225402555109801c1c9400342004100510a4202950700b00311002c070580b008002800301e07441040300c82035803000e5802c01e80f07410031260016100840c201c01ca00c04640e0182070b000f20381e6026050364044860f0400040400030311801c03009182401c031003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 715568875 1250 715567625 715567649
    0x6030f0c170a0209060c0613120f1704050c0307030b0711160b03060303070c062001051512030705031b0d022b0c0f030f0f09050303041a0f1c06 63
    0xa10300c40e1140c401c200502c540c00980d40000d4600c250740d03481040d980c0e26004142111100c0c5840010041c0900607a0002c40714a00404000c4005a0080b4420301d0440b000d9610041e4800b89000409516100a4001d43e0f83d4040c009140c2001d8400b8030000f00070358019040711442c0e00b010700c1c1c0180104441143c1c06031607000f460000d401486400411001c9134254031200d512a101d26000a04611440000500f0380d84420703400181c8035005440100642032105002034803000c000f07182401e80d0b0301160881c1403030140056861103450030060f49003d41180108a03424101030b0b540d02031440d4000701c812440c085c2d1071614585114030401202d078080b29544080e01080c0f2900e600450710600d5111282502c0c4011201001d00c58440c100300c80d000c40e00180e54400d03048807805d0140c01d21034441e50641c0098100c1c1040c001355802180701c5001c841000c0c00661810b071805110855036514501d0b82c2c14424001c01c00c007403801c000e610161160180b10004003400c40301e070b84400411660903038854015105 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 715570125 1250 715568875 715568897
    0xa020c190509011e0b042702090f1210020d02180402041802090f0a1503060609050a030b15041d1506060702041a0411090102060906060d032706030f0c 66
    0xc520401d03e04443d89480412a541c01c00d420062865440e500031030114000030600103602000b030072600b045004500780101c13080341c03010780d00000d0b07116000c1080d400c08041c10140703405081840203d00240550010350346040000d040102c140d80c041c801a91400ba00400d10000d48004042450030111040341e045241515244800b100d036a401c00701070428580c0460b0140480c3c07180701c220615450002d108420b006c0e02e951840719103007200440c3c00d000030f1a040c40880d845000346800c0007903a1004141c2c6030703c01e1442e034440409100c014500d00c410070b249202c1f86101e88441c000c2407041d80d083c01220b1f2003100007801e9540341c40c1740d0841c84c1d4048103448080c050181c1b140d0080703070580d41d0150b4011400d80710303803d0f080d071340c03030010600e403c1e041860056608400e00c0950050072000d10260309548032510b03841d050b555103000c00e0b903140307500200d0101000d00080c0100740c80206420b4180201d40f070560319803011070040c10f40e54803c0d004240c98000810580621b07103e0904a5551030915a521603 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 715571375 1250 715570125 715570129
    0x20a02041b081014270f040b060d050c130f060311100206010f031e1b05040b090f0c161202031b0a030c030503070306170a0203010c02030c10050403140a020c1905 71
    0x110044e00b409008144184001201c3d10300340904d40d00030490100600c14a040c44140e0302c003082c804840a46441c031420010841c01d02c0e05144021400b50020003c08545189004108049800050b4000b82d181e6915404581842c1c0740200c10045000b4600e02005a074100d043c0001250071540b4902150807050050004140c0040400d081c1ca42011420003c0d5494502c19085c110040e840034010b586c9550705030140404041180302a260160b405019402100c0140401003030144c84003070042000f040002d1481d003210010707200c8404814083c40c1690ba050b1510310030342e00f0803040400107030000545009640103510a0011101c101c60040841c0d2140e44c40050080109030802020020004007045980d4841e401c07449c05007189206004900d0740c44108142d8460f00250300300d00a500301841a06030500100650b04c0a14101e00540700d0b64103d01c03010002441c000b0001c800344001d041044c9069403014020300b03585000c58000b050100c10350801c002c0301c40096412900542c810200c1400b180d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 715572625 1250 715571375 715571399
    0xc0e031c050a41070f0209040203031c02090907110309041122050f0316090902010201021c05061207060c06020d020906070b010e011d0412020a02041b0810 68
    0x400828908691030300760b410400ca8501c20340b62000c00554401040c1e079014014980c0c1d1440070602004003940340001c0c0e400708407040c2d020300305001c1c0640c0030426102015081141c03610358091b1009050b01d1806040c0c140c40d5204001842c00c1482450f40403900150300c0c14055145a04000780f4140484896030300101c483c3d0768442e18000c50b005680303440c9404c50011040d010360703a8012508644418404070000840f2200c41d05116861248505101103c65814042484803001b0007035070103100074508280088000e0188a50120304565080000d095000341d50802e255020b400c44a01003800c0c20500c08100f864641d4590b6a003940e0081401084101d8001d001e1481481d400f9a002da01d40b601c1e80f00010082c0119428150000000078075034040001d0100414103903588074000802998a50070b0030b0310b04091100102c001042c0500109004c00d0001b415455200c07524411200c0b611f246038081b4083da8262303000b10342d0ba50380a007151035034550004030107544007c0c00700f009003070540703091001d00384 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 715573875 1250 715572625 715572673
    0x120b060304110120030901031410120c03020d2f1c0311030409140112080403080d0209220609140708040206040306020c0c04180b0402060318060108010c0e03 69
    0x1c03881e4042040c1d0100e900990007864200138603202c4100c000e25621200762268021300070540064907203c18500d000071a55000340c0107801b419548a083c80c00c029028001d2044142c0a9074188410400000140d0b80c4000c4603425034811001101009488419040e18051684d021208101c4031280000242c64031403104041800031040e4006419560070166040c180b00710b9102501d00000801281203a1640c00000682005a507414801d81e07035004403103981d290a44005169500810003000400d031180d0247c008072780ca07a50010310300000a40086c6000745155000110200c11242c0c2c95041d01c00c510401008144602082c0b0443d83c52102c0c0741c14a260040c040310503c04414041030035503d4810950b400b0b10740c001c804550f02d4044420182e650000c0000407882141090009501c0c040020041941c484d031007025448240c4131075003044110b800050614558841210000b00614020403210340282120000051a82c600c100d000b8400000001c0c01400b941c0b0003500800417003200064881 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 715575125 1250 715573875 715573883
    0x112e051b0d080718171b010212040320040c03060311010201060b0301090e1c03022a060415020d060603020c07090e03030403050a0e0402030403020d17090705062101080d120b060304 79
    0x140d48200c00b800c07908101681256040c4056085c3c12400c9003400180c0840c045c0d1a18001030180c011100126078500c41200300c108091800e2004100045400344024031744511600e20080c00c080d02400718045a100801e2580040d4450700200184a10100302380c60b000b8080c0b00a005890410a602400b84410f21580b80001e54400c1c000080700001c2c08410642d00322050000c4c58803045400c028003940105d405291144015111050820a07502803603000d02c4807000548001e503101e4840d510381541882481100d117408018640f5043c40c81c0c810070340948032f15200180c4900b00d03030046516128113600880591840d008800034002800019660b11503403500c2c129503245004002190308030120084250002d0020061100301078010500565801c43d90750f401c80074054412440300c4a22041e1080d000a4000c0319040c41349050400003001c3d1840101c0c84a585800781d0021041981c501b43e0046406402002c20030b40d0043d0b02c08509a03a80c0824a4140948001840028164400548018 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 715576375 1250 715575125 715575137
    0xc040b04140a0801110c06010801020306100c021809010c0228120509060315100c080405120c030a12110c090c0702190605090102010b0d112e051b0d0807 67
    0x54402d68504040034050300c1100024024010300710510b03041a000254407000d680103440010a4a0f2070500c2a6840380400910483c8071111080c0c056a40c804c20301005c1c3d0300070406040b5280807001440c9001e0084c210307280000b50044014400038100300c0344441031000c40d0903011149003110300600c001401349030841003448000003080d0083d1001e101d0401c0c7d0b01d0300f006000c03081044d0841c1502c40a1041203046d583c070340000c080304034200c681102244000703141c41000d1005201c00d0a11201420002c030788002103407041084440024030340021814216018074981d010070540686c451203135035010500d44000c19003440030400248108000401d80c00503204085020300030355680d00c4002114841942c40c030005a0389694005109501500d000d60140d03082440d8009513042c062490000a90003000c1d0306140382c1400704002141ea16500c1c0c0305940090001d28031b010b10541e54145120b10f82503120f06648440c8840075140701005509441e1319a0418401d080105400190050341300c1c00e41e1400d0b03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 715577625 1250 715576375 715576409
    0xa0623060c10090f1101020a0b040803060a08030d091a070504090f02041e090b18040b070c151b030507021902060f160c0b1c0b01021e0a020103050c040b04 68
    0x4034607107510340c01c0c030040c0582004521018003c03244104000e84c0c2c082c80c0c080800003080b8006a03990b00b42c490001b80703614135100024011070506d002440d0000780c0204640441d9a031109558515003100740e07407032a0944c2d5a0154400c201c00e0351351183c010450a81d0008251400260140483c0264800d0700e40140e110207400d03041e54400d50480d00a480594824800c401d4490008440c401041c061040700614107001e00015103881301e6000f04211000c842290a559242e490064084c00507042405010b1003031500000540081c10200b000700d0043c800041000028200c4c0c03924031402d00030002414030700000d2200403607000c40e000020301498191200580c90740c2c8041500c905c0341c103418a215403400301e81410031014140044080074040d00400700415142d40090305c0301c5c07003801c1c0202c00c43c0a8110030400035280c0758000d102e0141050041d00c01c0d20160700304801c2c00440421079810703d9002507021030210b6805108090b00700c420450a107081c00d04004d56402e241c400ea00843c04e00900070021 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 715578875 1250 715577625 715577647
    0x31c120f06180e0115080709181e170a05090f030c0901060509010e1009260a03030504051005070905131d07150804020303070f020f03070e0a062306 65
    0x1100062511602d440d180035200c03451100101000c000d500d64039400c06200c1d2079a00b02c0a4200019200f042001d009501d1510f0250300040c007a02c40049243c107802e1311220007081c0030f0202e0722540329034200c65141c0c59206203460205040d00b040b142c3c120300340501004000f550b1102c181c0d81000403e80e40c03408080c21250000b4a0010202e040950028014001045460f840000381180c007000fa22042c0701e200900b001c110007032080304002000030f5030303400303080100444201490141c3d50300c2140b141c0f0194080c03803c4074200b4883c51000d9020036128000e000402004000004031001e11080422803824100c10091114501713110721846110a44403222401e0780b681e00c07072010318000e007081801d40c1c90b10360307a10b40d00c5100030310031200c1d403100d00211105154044c0b42a540b045034000c000d1481c200c02ca6980c072451250030300e01070383c000c00b401e00c0190301600d04102041c050844117000d45481e02d00411000300b50382e03654102c699903020030a12829a4007040c0442441d285c000c590745074a83c008040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 715580125 1250 715578875 715578881
    0xa020703120b040b030d0504060912020607030806013c030219120e0703050601050108061e0108070306030501022209090f021219080a1e0c030f02010e0106060806031c120f 75
    0xe4217581760143c00c20130072010b90854001c20840307441d915911492581e440702d820075502c0110000e5007042d401c00c14040001c0c49902d10740d80c01001410300c503c1e5410f1400110000309240d012004c0c01e10b10001103c2a0410340085007980d0300110b00e010361500020160b04900f43c5c10000310314060240160103404030780240d0b003100452115100494480580c0c034204240d803020284070303d0307000c550302c40301080031b07420260140810529407c0301007a4003030007900116500080142014109640e078031000c00066020300080c54441082c101c04064094160360f268401003659202c00c1c03240c0d151440c0300340001e0b203d00511000d650101d6540c4094400c82447d58188070389800403070060070f18078071000c0400c0003000c0584103c80b06603a440924a00341c900b4500b01c021143c0740c080115001c1601280000e105100305c040a400302c0c400030907201500803d040c20741c0e84540182010402c46001c0000d00d08041042490009100000540d100c0c400000980001c64401002d41c0442d250781c3da40c2c0d0142c1e4a60 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 715581375 1250 715580125 715580141
    0x4051603110405130501090f0e0d0c020f04050c0306040621020609040b09010e090d092114011802040e01020f1606151d090106061b1403040801060e0a020703120b04 72
    0xd000004058000e0b009a00146000d01444d00803924011030185201c8a509c503001d40074030324100030414a69400c0c0300b03640d8070f000001c08030317840300407658400d06545490194a019519088005d80c80303040c8035081106032880b5812202c089044104d01420311051000d0f01c50900381c058501d95a10710051010078041c1103040002c3c5d820110f0040005404040848224450703254042a2461089800e8044074080a80e00c66040c40400c1400d034030108600140d1990b0740305204044103620080e0007a180740c08d68103c14044d0168070345141804003941424040e1032510220742c0002c40c9802890b6124403024001e041440a010008030890800c0101a5206400715858041495981c40d40c40041d0f0107400c000300d00c8400341c080813501260204805001c1c140540707907603407110b504120800c491070f4100da545801c140c0d180c081c14400030480303103024001000a440740d0b074004540f540c109982c8100049000c0d181410f4540304002d0038000c20343c070104c10313080c218500f03000ac1080540000094050680d078 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 715582625 1250 715581375 715581379
    0x60e010e030106120318030b010902090103020c0d08060102070e220c0e0a0b01030f0218011821030207061b02060a031112012315070302010603080a050d050604051603110405 76
    0xf10002060a46000c2610007000e4400d555200c0e0111416020f4111075942e07100040070b401d003090044c08840d580380c000e0325000c001031400506022005004610741a1001e500402141054081c4111541d0510185000d00900084161766051921035495841498001504880070300d41d55002005800c60350b5000130000151601002d003002e10900c0000c140c40c15005001c02e180655a030a4240c2500948601b12920020a48521f107124019110385000d100c00180244040c00007080042442002c0204d50341d403059121035860301454064500401c42e00100244100744104500d000c05a801d0f480800c0d90640e8426121070400e2000e502920704510360401c02c83c800300703560690b254071120b02c904841e01048440b0700b640e04d00c04036580003004009807a0f0032240c00b0b141a5201e440b400020401140f1030310001454984c0c0b51544522500802950000900e001641c01a141c4103800ba03180c1081089808024606003c0004aa52542100030f0f00a25444d610304581c09801070041d10300610300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 715583875 1250 715582625 715582631
    0x1801031b0813080c0d05030106031b080609040c23030c0f0312160c140414090d0503100506030403021027022403011404060911043f14060709060e010e0301 68
    0x5c0340d8400313841904240103000009180c80350506090160705640031041c3c001c0d8803440d00603103c11040c400301160050085e98101003416002034021034070b260f040300b44814600700c140c00301c2806e820503092091080740d041c071a50307080742103081a60b4081201840c454980d0600c9507210358103003500c1012025046c02070400d0840c070b000020050980042030b0903480781220b041006e1117510130700156414050721018016440039200171034043c00f40000319081031650000040103941c400010300140e00855049006801102001c7c445482c5402030b000350744905070104018481990348520310308480c80c8064403c036890f4486882240d6100d81d0036469401078003801d540d0350b8540d40d00d80600341800c419907000b0303450b0a1001030000218030801260108880b4800c0c94585098007003002c8845070602d84005900c0c4480c040e00e502c0302c0500714102100300000b01e21522a01e802c100c0100c0d80c031840c6031b070000d801032401c10511550003d1044d0940d00642040e070031404c00c40004070340c000310000b219505586 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 715585125 1250 715583875 715583893
    0xa140a12151404150e0709090f02030f1501090b0d030518030a050c0a140310110408060411120a1a07020114130c060207060e041a04021801031b0813080c 67
    0x200d071480a200f40c0c01a080d1102c201d49000d406000c65045600c0c60351550001c01051040c5041c41d00501207003801800c41911203c45a00001d04140e401c8815500c140d0104900540d03110701c0015079401000f104404104150311507010a02450902c0001010800000388a502410848a0140c00c140000c1c041300c207000c1e46441d000d47c0e0396604040704c2d4400c1210400020b00501c19041c55030583c40041c02510714100503040303080207045c60074040324481c4000e000100d411841002668800c5000c3d1401d045280052800c1c08229000990410120b030400581d1101041c04001a043c06804007095102c41e551516012401804605000600903510030180704c88091503140e8503809602a1105114083d42c0b08002eaa40e40e899100b1080424800500500740345041d51244040b002800802c83d006101c42002900701e92003a6074030009410b1030340e074003042568980f107050b40803400203507812810182108054030f0110018150200b000141102c3c5041091b444191028045200104c0700404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 715586375 1250 715585125 715585151
    0x6010302041205011a030d0e060318100906060e010608071101020423120d02250510020d020607051309050c070b0c030412050909072706030b0a140a1215 67
    0x540100301100c1e900303100c0b2100246c0c03070080f130002c07560f040c0f58981805070b8403100c091003040d82008060441502c020059401e92110920681812195071000010b40c007019291400031904590084030a100c010b40c0140100c40e0403240e001c1c0c20140c182083c0d00c0c0d5500c3d6074505400392045070410054010b00d080700c800e0b58011a200c840801f070003284c01d00782250302401015541c207a01c200c10401079100a52218081044140f00480d085a0354142d98a558031303070001c9406049203001c207a0050384220040e003c9940d060080d6500410340d8a855482c0840203c11b941e50090140034030f1a10b5652900030a40340c1c043c0c0d02c11141002d0380142403c46520300544001ca0300e81044a0540c0c0300c0303001c17a800c054120b220303030308440b55000c0041c980001074440702c0007111124070212134080c440d002c400c0c690b2041541c103600b0200811141e07402040c0c4030141c0d010b000325901e07994041e07982d0b007804060000740784d6900e20766035090700e80305011520401028100a007181044482c3d43d40d01505c2c0540c500414 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 715587625 1250 715586375 715586381
    0xb0912072312010b0d081c060f03030f0e0102031b0a020d110306130f0803041b0f1401080606040b03130b040f110303030402030615150d050106020606060a05120601030204120501 78
    0x1140803a0340041c044950b440c26803e807403421600340c0d401103a6030060300000e003074032024045c80b510071442ea074200101668048101e43c1d40d9002800040382000040080640c1f00e038010440c0c0b905440d020300c8480b10038001035130703e000d03240c00501c1d040b600380380384119a40d080040409041e002490040c010646041091b812501d54191030f001e80078110020301e004d803c4143c00400d082d803000031880e103088036486480740c541001d8021206604c291014407c1450f00708441400f600302a00c03000e044078a0b001300125800400c61059050000d600e08020f61541c90344151011541d481d186590b0302da841601050784c5a03a020700040511101a09200901006003607a44071a0b00c00c3d4400d855200c1140109070740d0340002c4174005c2d41a8080c82c0014904440e2520b5810380c104003a02c0d00c24901d06200d031076411908040e2221702482c0d5207100401500307074104820340d0040f0003900c843d0f1604803046d100030070718410700e40c0a030456220100031400ea03902c43e504440042c400742800904074900d901e40f141c0a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 715588875 1250 715587625 715587689
    0x21005070501050c210403020703030509270f0703060e1b04050d1103060a05130f03030605130e0714010c080f1b01020a0e04060b04050d17030f010609060206010b091207 74
    0x10b5031210417090301c1030102e000c50034000c43d010b4008050182c030710354084030b40d42d0090400030b411400c1c2c01411000c460b0420902254107a149848022925020145561414009008401b0581400d4040000c610841da116420581309010100041002c580c0030b1210b106590005030000c0310018a24207006851003d94061f240c11030a031801904d40314200025243d083d9128070030b0448004030400000c029240c194841c910034140440c10503560000101681c80141980c400c2c20b8a0f90f014800b0300000b88242000741031400c0f10300303044c16545c500003400c14465034001007014000150b02c1401c101d60805071511000c441c150224400244603031140030307400c04d0721804082003111010081c9403030030b03002c0c1c2420751300a030300c8450800745014108400d00100320000d4401e1a4120041c48404415100942c424002420380d072401e9458181d008201e10240c0d4849800c640101d00188400301c81002103484052040301c0ea03806140c48070a00500f00b009552000c0726215500d04810101d20f000c0c044800c0d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 715590125 1250 715588875 715588897
    0x70204091b2d090903111f1103070c080a11120a170613091502040f152a03171014060c0c01050f040b040b0423030a021005070501050c 59
    0xc19000e541031800b607030801c5074060304030540d62940910120180da8026141107020786001c05203104c0595026052007036003089404800318941c21260f02c08841e005072000a05140c503030724135500c2e21440060204000a100502502c400180c16020601c40c5222a8003d1300403020341e1415407a01c40f6980d0070380c0c0440240e4000c240102c03c042000004200c0c464840c1ca0301510008002d0050500d200007013002a10440340410340c0300c9815061800c40c8040d00c09004c0c0820103006160409802204005010000c40d0800100c5040c402010b20610390035240d241c801800150254003a260960b291045110b01c040c0503001d1104112110b801c0320080700890308940056410201e040c401d000503440350482d140f076107a020b0721a0125552065005244e849402c54110f401d2a4603540e8400881d813003030b4800001000082000e0051080314100700441080001d00410f0b98510030020940b80c100a04010b40f282c14901524900305019400300e40d1000da0000003000145070142c100c0c0b04c1030f084104e100c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 715591375 1250 715590125 715590149
    0xd0c05031e0c03042c06100f02032506051003113a1e1a0a0b030d020703150212062107080f06090609100b04061805071706010f05070204091b 62
    0x40e104410041c1d601d401074401402c100e007c4200c2e0501525107001e407005580451001b0000c821404604014502010300520060001f9140c0c03418010240c500140c08114900030038001000000c110386004003150310290f80818004c2c4491202c000d80c0c18511440b0000c2000b254400840022444104500c0512614030102c000d000c00c02101c0c400301c04038000821043c0c2283c52000303c50400152140e20100b1104003180b48940d80010905105086e2402c2000d41d1203018240100b00004c2d03410803410800d00b00440c10301d084070603107030030705d49001e00258001c07100d45254040000300000c80c0c40c01100388204450001d5a82c14185e580d45040c0c000a141601030000440d9440c60702245281c002c007019002440401003c0340c4407002440c00070b41a039803042d51500000341d810f840c10a640c05151012800003100d140c2004040c20380700d04421508110000302041146503030700700080d0504d81a5a2500a031507102c42d1000c1001007280072070143c100e450b00e42428442d0300740c48850b441a0b0300140300d80 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 715592625 1250 715591375 715591439
    0x15150706021c0c020318190308030f0609150409030905041109031c0c0b0c191e02070f140d060e011d0a0b221a0106020d0c05031e0c0304 60
    0x82c41240e01d007034422001078000700058464045d00d1060444100781c0103201000c0030244c0c807032842d030940706544100d500706404010404100c410598459015400f070303441c421180352903c03104020ba1100c00d81c040c031070f03546c400900c400e02d44106640009048064401c002e82c224a0071041040d80000b040244640b051a42d4180e150302c088402c2859440540c59241b03141d1566a03544101c2040200a032003007010520074010611070310000c2848110003030300c03a20030118807080c80e082060410f01c840c200b5944080b8040002c0d903101a40130301140c1060400c8408040c030714000070780103480088041d1503241049298014068107600c4a860308121a4420004042c101c07941900d0301c8400704060540280c110000d0748500b00001000d40d865041100d61070021801d07501c820928004440c0c410601d6190300042c446030380c0412402d40400d0041c28101401401c1d60b482176502d200c0c210400800758440840186100c98400589083c2c400720802d803504e842d180c2d0041840340901c00e10600410220b903500c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 715593875 1250 715592625 715592677
    0x90f271503210e0d0f02010c0f030f0905030606030d1103130e0603071d0f150303072625170c01050a0f09032c0315040b07020105010e1515070602 64
    0x708410400508035403241c84c682d44a10703c13003500201c800e9040c804445032420010300414440d0022900c2a141c0c140300301c0c01554010400591604446d02030fa001a0901c5402da4000842c01c0c102d184c02c0c41c1c019280901c03420f07800e04501131440e81d1144200b00c0600031800b0450201040d2142d03909070101d8000a6580e080c400f400347e29144040c1c0081d5820000c00c031600811540280d000c0031800384005422489408246150300001003580e41c24100d400303a000310fa80c1559010f42c00303c0c0c0c242c1840d0900740052034200f825451102002085440c8059003c100504581007013610700664858035181c010100301c0ca800303001d0449020155038a0944050030030821445a01500c07500341d030703510700c1e810440802290020000050301407111455415881581c3c0c3c00c0100010390407c2003201c0b41c440c181850044141e080c003400f01825a41424010301152202c5220568880071103541520090440008600f0b0450040300c06504c0410016030201480f9898004000300c1141d0f8103216809100441 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 715595125 1250 715593875 715593887
    0x7050d02010903140a03090c031103010c0311121008161502030a080406090606050301050c04060809030909041214030f06010f1e030b030f1903090f27150321 69
    0x1000401142200780341d03000300e810013006003c0344281c5003000601400c050b03c424407084080ea0086813813007103c881010240c1001e019811a00c8410304051104150080c4042054010503c1551070b13005044005a0b5a01c03c03014041c00521902c010765290100b22800c1080c3c1c40b403603029007030300c81101070303115030209200000300c0307110403140d60714000251296a10100601402c10b005c0d9045500d402020816990a2107114051401400c1f04c41d038840c5402409802c1c01c0c07000b00261813640003401050030645803c100a54041d40c0300c0498034501d14081000d8541400c110082d03000c407100072080282c61759000c403005000d20307801d03220031550901320f01003144c810600c2d81d915024141849418003050780a45c10030800f40300000c058407003140e030049074607103042d502c200c1048150030050b00307583c141501318034800d003d4000c01c1d0080841c541031032443d840c84c40c10b100c0341c00304075020a06002c030003141680c005d4608032400c041e0308411641e02e0500420483c110309140c0842001d030810fa40850f40104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 715596375 1250 715595125 715595141
    0x15090c01080a05090a020a0e060a0b0403050a06021c0f0c1e020705040c110109050a06060b0a0206070f03090209100825030809010311030c03090601050109080a02040b01030b1507050d0201 82
    0x40d607400280e5903550980805418050b00d1026540300301502032005a41d64402d06000c1e00d50400c007170815241a10400420320855400f4510f00744041009201186020610010a40c0c000d00c025964048031f07034290b04051307044144105c000c3d00c0c0c584c00c0034031410150440380c040425a52912144510058001c5202d001590a10056401444100320504098000c8052900c26003018400c0c00c0280039410300750b405402044600d42c004503212800c201d0948113201c00b814615031451705214441901940c1d800d000340140c01400b00311a0b00c071506a1080d0017481500d030380501800650300302005030034070500282c05440c2050080d00c0c8031030540c1000030108580c07581000c0d803080800d8550f40314401c1981c05907510714100354903480f601c0d40003003a250040d8090139580e900d660340c0b880d1a01c101418514183c002e00d04000c036450f0204a800e00c0081c81d031a400c2d8046030005001e06d44000107038001c01d84100e005801c072084104c60030703da00c142009400c0580c00341c07003940d480d000c09410880c22a2288 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 715597625 1250 715596375 715596377
    0x4501080708041101050c160801111309051302060a0f080c090d03050c011b08040c230105031504180302011503031b06020c1608010f09030503060d050c04090515090c01 73
    0x10100103008141c03800d0884200315030604001b46000c9610080a00300700040d015040b040d02000350400520509105103140300700004d60890404414a010240d0440703d441800c44881d12100030a00480444d4000c0c901d00340e00800443d55840b5002c40a40441c110803401000b20381c102d8006008200908115051000c00500c20500423025035070030b5910b40c2140c08040320700d6507610f05003200c2111071100300e0244080c903200e9052610780343c0340003000404039030040000c4202c8a07684402caa0003081002d5660102420000e803280c0d2a000200c40f91441101d0b020b81c81810310340111440c80f00b80fa03140c000d8501a034002e1140130520040d0200c100283e220060008141c02040c180e851001c01d80354521911a200140c5400b81118440340740003800d05010b1442011f120007000100030900c22580001401c3e0300921209a0350f44025003180001040c650080105810703540400105001000c89a44020010810400d035030618943c1e4030180070304460100c005d0700200e9514000083e450300304400c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 715598875 1250 715597625 715597637
    0x21204020906241b06071e020f0d031e05010303050d15080c06030603210405130507020624270609010b07030e0d050a030c060c051305040245010807 65
    0xf680100142503201d140391110603880002415000d10044c0300540c0501c000795146e04584210514a44400030b151a0700f105660124102c56919600070030030f13015001d40e03418001200d8582e1000001c03000c8503c2a035504051800001004041e0030030040e0040480044007001a000f4039402030503042024050384c60651301102c0003105628100c4c000b154006006010f842c1611440c040110400f04101c400d18030680005c1403c0c03086044c2002d0b160000185200c051085040800001c1d444407806485915801d100708c0c15101446034011a4a44040d0090724a0016400304400d443d10100d4110004203034012800c003086080c0381c8645698140d5905e42e03045480c0212959060726120001004150446102598040420800d00108420a000340c4564440780b0705458044102d40c1c0c4841c1c014140502480701d6010501c2d4141e245003641d2040c2d40040c0d840000c20383c10b4403175148460b003030044801e400d141c007840e404032041074001e00c0050540f42404034881c0c00040d00c00e07c0c4112004000200c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 715600125 1250 715598875 715598929
    0x19030203180a15030e0c1c0201350a0e010b101101060e0a0b03070806010b16150e030d0b040c0c0219050907020304050a0b030106050403120e0301021204020906 70
    0x70a0100402012004003a1248180d560301c0d910000d200352590000071a070f440c0070300398042d0741c140110545000200c40302e02ca0340802c1411b40080400b0140d010b03042101480c8c1e2525030b150450144403454061403100d00c284110907140c440390401c1110448100d0b407e040b520440d061050103000c5074004000c004e44c0744050380150440c0c00f4410306c001c801d603542d2100c500045007540c034031340b5a00880010310302060015a00c0c041c145031505a80c0000b0060340b000c4010400034030404140d4203011912031400081001a00309003102005520310b41030620719028203040031a00c00401400c51052000081c00712240030000c00040b40e0040c2500f03c00f05a5072288100145010404401a1050181180c8070385480c0d0010504151044440d0340160f070000806022502d8284640740c010075554480518542c10050020702c28001d43c8401400d00b040c2e038041d054041c1c010711504800d05c00240c000c5464100c00138011015000588050f4000e01c102000f04140382480c04440c01c0000100c040c10300502 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 715601375 1250 715600125 715600147
    0x41a2e080910020307030b21061302060c060106090e0a050c0304080f0d0c080618011809331a031e150a020315191e05120f19030203 58
    0x44001041c258240c095460488001d280c0c610145004650a640000b0602444030500070846450841d18085110031078503104054000100399602c00c00322010a0003d200910124942c0d000e1901c2d441410f000d02c1001040c1550700141c1c240448d803100341651481c2e1500c0079080d0860310203440015101c0000c0001034041904440102101140394a25614202d1b200c1c00303510441e41500c446000040c020710a100451510350240c400010101142c03d486516000d50130100445036852a07210a4840408000384901d800f0b440540f01f4000305054460204060031a103070a02c4010079903000751401908a544406103108907a58141c080e0003041c03c40e203044031414441c50b60284100c014401e840120907203070440d11009000b030700030034805038072400d081e41182c00014003c0340040c0038021810741c4038403502281c03e01c803040381e4580d01078017900028141c600c1200c2c03c85070021904450800d078030060361304c1c0004000b0314000c10101500c124a14500356068a80f18000c0041c0041e84103101c440c0581d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 715602625 1250 715601375 715601387
    0x20d0813121101020a02010c02120a0c0b04020d0b010b13170c01030905010f110c100908030a0b061608030f010506040810240611072111040b041a2e 65
    0xa040c107040c0b980a010301c0780100c50a980c4140f9600300180d45502c3d86851450301045a416820300e480100c1d070900340d00000050104008100152410f07120701c002c501503481d02803002442c0e0740c01c00343c52219980c64054120780d035408008040c41d041040c8000082c443e914504010700003003280042d090b41d00400d00110050140340f00251443e550700c1c25481003114043c440c41d45860792119036140c64039030300110342c2c0c100f0700160313104403549041901910000c2d03103043c2101c0c0c0c044000c0d000000e040b43e000012400c14040c81c03a42a62074a280c00b03c14050103d08006188140210b1a000031142e0b02c400500429020328440c402c602d500004290610402c640c1110b00d0358030442c103005e6092584480181030113000d50b800a804a141030100440c141000c0c000c0350082e00660301c680301c410341c18107181e840c94840d000380504003507407100c2c3d41e1510f40d485411034040c2101c003c0080c0240162100d45600c02088060002d10403028140044e00484e1101300c5071804c08042c4016004804c108002a654 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 715603875 1250 715602625 715602653
    0xc070b010e191a0103052a0a0908061005090702011406061602100c03021903020a02121504060225080702010f0513080309130207050c061605060a0c020d0813 69
    0x701c103502400100040082c0c440c203554070043e40b490340f415a0120001504403440070348504460010905150704003030b0f18900100501c05c004008541c0d900b09200122800035045e00081c05500410051040a5040d0b1010106a51007220302e00110345848400f60f08031814960044c80c03060600b0001103143c0703420400351003601e510b0050b440301c062a1340d000402040801c00840d0105a0302264601819070400032034262110901207045d1080705034030080d6584400c554000e01c110071000c07201000990922030440c9201004000b09036a0404e490008065000301c000448140800c08401d140c041d1034215182d845074101034164944a41e90700111500b000d900c04001c00e000b400c11010352120703900e0540b00010520500030b1900e84c1c81c90820840741d0954100d010407440d0051240201052001c103002001c11411a13042c1c0d41e828070031643c9800911110307000350642c00303554104020100720340c2112030048940d07429105441080c1c80c054441250540303440816030908640480091601402400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 715605125 1250 715603875 715603891
    0x903030e03270f13090b060102120909070302040801050403020717010b090c07060e06182b0e010909090b150406030c09020304021504140111030c28050102070c0e0c070b010e 76
    0x10500c3e00c035001180403100e10302d100404141da2443d183d401d101b402840c140d0000001d101905484d42107400c240a2400344060789445803902034080384001e40a981224010b2074000001e0141d4034160074041d454100070b11909115a041c120f022442c0031041c030072034613900340041c81070a042d1161b0007452099041808100d4820355140020884a03804204944c45500c450440421284000d502d0303604190100141c3c1c1c540030403905034a0718903e0700d42c81104c405801031814014060491004803003034003c0740d2107442c516250140c1039050092207103105120340008070030110f03114140010b100840708680b20160034024030800030b100c480d0303258009507005800117025102400780a4803041d040c0c1d01c1640810100d15014101e0301e002d58000f10a511144035000245043c4411211080e480326078805260049550002c1603400d404984410546980e030080021911001c4d149401c214070252400b03038001c1c0451030000101120801c608641c0350780e07032108030b0030300030703441e100d508151107a000e00544 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 715606375 1250 715605125 715605139
    0x706030902031504210203040501050712021219020105060603090304120305040f0e010303020c030a0803061c0c1e0b091807051e0a0311190c0507080706030903030e0327 74
    0x3c5001000011482c0214015000412925004200411403a900c058204103540087c8020852a13810500382d070b040e90b41008621003a0340c1e6a40c012800c0070740307040321030605d00030100d801c6800c040030921003d55892075400030002525284100f024502007120f05406aa0040206000d119500181d09540b1846820301d0b40c00c0c00d461300340d41c01004e8a2500000000201c0d80f00400603d03904020102071400c09501030021072800d41c41f03804247c070008180e1740c00b4001034489400303100384200782c54040e07035000305498078509d88076407807160404c1d02c03a4401c4102410409010411014241c00c44115000c000c144100010301e169504010740c0c00280400e06014050101026001d15000880c07440050030800c1903a070701da8004060b00322003250f641d10280c44014040e0410108240300300302341c0d55080c1d05019660b6201c626096140c003d803908280b4143c00307003c000166107074168001c58603462003070b201441818000304a4036505d0140041d440301c055040d12401e80322050505140403100c102400c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 715607625 1250 715606375 715606393
    0x904171209150c03040c05060306010c060f02030a0b030d0c03030b010c12020c03010c0c110f0402070c08010501030215400305240402150a03020409091a100503070603090203 76
    0x14100003181103441c881c035500200035070b21000c01c032103156a40c000243c5a0040c150305142d191110000303494060310780681400400700d1000da008110b40c03110a82d10503803d001c03144a05500c503020350025280740071140e040811b903050b00c0c6070108120340201c055555101c01c105940c0c404030003610701d101e031090502c0700e01d1104c400030501d002030800d1a900540c0080c00c0440050040c103084805101e0444200040f000d17210000403103160300503421000c03c4074448010240d0b000000c009109402000b002e5a8540307500180310441900464100c9000720b81d1103404040441480600744114000c0c500b0410301407001699058000500180e4002e03648081160f840744220900240ca2085d00180d0703d40d8000f07039807800c805541c12803440b03400c444822a004c09041c140c1c0420404280c0c1c0c0401c50380c400020958400840c0300340c4c10b840c000c20712181e040c8805102802d04c400c0c4500c040558403c0d0441038000a8112000b4040102c104d55000d80285403d40c94403004600402c04d440041703915020305180303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 715608875 1250 715607625 715607647
    0x30030e0a031a070810050102150c12460c1211120c0a1e11060109141e011404060f091e09231e1e060105090417 49
    0x40c00c0c502c21030003a010301d241d06104201504644004100601040c031010050000d40d03404114914592030480c034104407030b10383d6014440c03a4041c040e0341c40e203011924400c000175403c284100c002c1006160a942c0812040c66070329101320703509001e2501c1c510600440e40c1e62035a83c558010300c001c0394540b424504080d00c2044039801c0e128541751b07007a0344020104800c00c100b040f4200c030640080031040c00c4c51611000200181030f010b4042d1106001d02c14410040310b500303002e07a10303038620102c8110030350341d25684800b81c5200800e05600750001c03032521040010000d041c0500725845610240c07404c6401c0ea8a01601007071034100d19980e10b82c025850303c000141940c00826610081c148840c5c001c00c1442c07600385213003099140b0185410705a401c0c0342c1c500010507148000c000d100c50350081004105011584241d252840180181c0420500208008909003001c913942c000c058040340307540104140844800d613110300a001301988500c0c4440481d001903180920007000a02140b4042d00700085080 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 715610125 1250 715608875 715608893
    0x1e0501090311070501080609150d08040b03010608130203070311120109050f0f070608160c0b0f01050a0906030203061f051807120218010e03121330030e0a03 69
    0x1045022441500c1502c0307a5100512070080034010030310781031020380791010000b0584400034010a03810100310300a0007039515115a2020304e160810300595940e542c070768001c0000c0c0c0c801d04c01d4200082c203034408101904409400c4081040c0c00a004107045d80c00e540303400300c603d20074090343e5521080d2100d03040807401f0280648401c05000d80060702a56014060140c01c0988800e454802600075000600c1000c1c1c1209120b41c12024040d4108006810102d0179a10311030118409000c000d101020881101d072410902c038180c2d0002d45000c1146030b030f00c92210302030ba160b034000258103420110003e410507050141d800300c00941c3e07400100394640d070384011400e02c2c0294005400c4040025042001700c0b90040948029507070541011460003920300308540031003044000c01410030484400420295500b0030460148004200e02156519000c150034402d00308503100307101042d00d00e8608860b400c07a40c600b210411070700c9240d1031070030028203aa04440480b4409403203648151414808004101c1c010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 715611375 1250 715610125 715610141
    0x2210604060929180a050402012d0207210f020406170a0b06030334060f0608010f06030201050922061203110a0201140d06080313050a060f050301031e0501 68
    0x1500d01c0030520420010010018804124000d4040c0a90420318075052140c0540c04000170b14002060388552004072446149014610740c01d0801102c08041c2003c602071013008010180c00311042d0903503502c001c041501b920410b4562109440c901c4101150100c400f0104203440281700050950320340c180c4c0100c540390641190860380c800c020705802c1100300c2080540100b0114000c41c18848035026241e400d007500b2450350511300d00d000002080413060741d0f40d04205a031095041c001c044032210f22030000c4c5154402c1034015030901005c0c0c49c02c648644101c4007aa07070182d580d2454203410707406001000082c041501c03030000e40200c82c403c85030000d100d083c0c040d14401a4605c074200ba94140180044005100084260000091140181e030040f4400c0d03807088504061b940c03280c80c102001401098168440400ba0100245aa800d55007200010054643c11250011590344599048404800d91032828021402c01c100500c0421280c0500000d9200100c07103105030700009a80d090709540001d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 715612625 1250 715611375 715611401
    0x40302040207062906030115110105070f0215010326074e1b020901030f0209100b03011206090807031707020307081b0a0b040b0a050703022106040609 66
    0x90503401c803a200c8280c14a078032004c10324040704c44400d910000100c19200603c80d00001400240d9a694514041c114117440403141e4402000b19140003200500100c0c4100e038084014020f0604e0b14480d101e10042c0f5605a80c0c0101e110204502c69020304144251039403982c5401030001d05c10355000501140407100b84210740b03038a0f94146540c0000641c82c1c0300c94000303c5c100300d400c408616001c07424144414020360520b89003441d5910000b400c1c3d18880d001140001c0d402805020000c018807400041003081c1ca8425a494102c59490034600340001c40700d40520003280310204010080301d0543c80c4c0c03856205004480004543c0003c0d0748841090303001001c100c4c00700b19111030032281080704cd40c030542c0c4800107001035858140e0541d1010b9151140c1c0007004c40340d40815a0b07021110204102020b030640c0d100310207415030700740350400e4002c95004680f0402003d050000080b03105220b8001c0d17405000c058031107182110391264074401104001014107421990306d00b00091155014003640d0050026 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 715613875 1250 715612625 715612631
    0x1202070803130821120c09120309030d0c03020d0c170a110f030309070608041506030f0c05150706021c050a0b011103030c03010e070c050d171005150a02010204030204020706 76
    0x29042a15040a514100d00154180f1104c88561002d00210840d1802c0785400744011141da02d0521120302c600650849680012402c10030000c0c08034000010001d50404404030f030000d03079030321104070307100303418500020f0050b002035541c4c509840c02002d19000442c0b080842c1010f91100e1010309030306820480304040012038198005c0d0700c07480244a08001c951142300510301c0c500d407440c0103d1b41d41819200c0c0d10100010300000034144115910401021300b103580c028041583d890030211002c00408400303540785640b075040011070346480c1c0c00740c12103518105000b9080142588030035000790482c40c40040c0724402e511a00c404000c45119080c4140c070703420000118403460500050100c00420340d8100c2907803003041070052000c04841502c2c111504a610340d00d1582d610002107441250390407008000c0d128000614544a400c9885441180d55503101000c0340e035503d0449840040c0244544c039040384900c414142d084451100030b090303144013400090720b0103039a039010800300d0340902c44c242c1301e55603 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 715615125 1250 715613875 715613879
    0x60604050903120a240e2a07020a0f120c0f030f02010807020a0203070602070612060b03041101020a05150a1b0c03200712060b060406391a011d04120207080313 70
    0x2c0306d211a500202c41d03448000640c511081050011207124000e0158000041003110071541e81084c100050030902010350b108a40e5042d41130040910310f241111489500100803800140e07241c26001280c1e04080c2100750141c103074006441880001e4500c10842c00740c03a08074800f68500b00440d400610075a401000102d00e0090010510f050401380042450300b400350411a168140080d0382d04107800aa00d040500516030040c0d241c21003000c001402170007041c10280340001907000c0c50f4403030001d0100a01c0500206686c88070416501c422800c00b0607180c56089001c42e10500c090460000016807130440220712441e0585051950b80c8030b080060030359903c41d020041c0da03010b0b00000000c1031710360b5824542020400780103003003100c100d00c0c4120400030540002010b980c0300700640c40e0315103034030a001d1911814184030303034060000c1c0015100010400010600841001d0740040702580401c11169240c5a1b42c403201c503602c20812904510a0000101e01e05c11b013440181441182d40c642428214 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 715616375 1250 715615125 715615139
    0xa050d030b030d0c0b060a080f01020a14090102100e0708010f020c100b10230a050901090f12020913022814130506040e030c0f060604050903120a24 65
    0x20300501d541c50103500070480c500c22054010100c6081903074000060442c3d40d844101050365a9180c0d8081c854500c1550031207990b041042d4000d00c0f5503003003a50fa180062060b000c0d240002d200e0822060f005038400161400c1d0340c08103031700054000e03440c1341c10340d000b41d030740ca003003080c255100c030513294405a40c0083c410351402e004105201048a6100041c44200c8001e4005901c1804006046050000003080c0c0740b81620700c3c0703c0b41d0103003a42d00f10880351600304400c0021b2041d04081c01c0d16000c168038120108480e001420030300110b90410000d10403410a9030700b0f200c55101c0151002d0039100a43d03500c2d90040c0d03141a844c40c99003e0070010324a4075150018005181051544040b2036440003102415190704d0380c1c0c9603031001c194020404a000c1c5c0b100030120300148807400e07506150340404280303503d008002207601d50009280740129640c03501d54400b0441224000e4600001541c001c0018681101c1003440c4079a0080491500003007404040480240748030442d0301071102640c0c800c10a010007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 715617625 1250 715616375 715616381
    0x30415060617060d0b01030b070203040909080a180b0409180804090203040213050106020a02040b0319050609070605250f0c18050901020c150c040308131401020f0c01050a030e0a050d03 81
    0x4108407846802107280742c4817036050b958180400f030011083d8200058005000704111802045421030811804059003441e240e29003102c41c0d8000021599460b208034001c81e90850816115850300c0d42c0d00d0645440c031030344001e00c0140711031043c500c080ca01140215410001520007011038140160b031303e1130548100300e2010f850022050380e403072508005000407540050311001055065800040216800001a24200c914082c1025540d0406055030801c44041592800340d00d6090407103503d6604c4142c191403038080e0080402000700f0708040f902108103565030440ca040d0113803480d10584403198503240c40c00760312030f005000395881c00c110410880700c07288540d40d07002041c0c200860400c005680907588504200403045071000c20704011a81c2c01b1713140c500710390095038405080ea90382c2854540550182450384103070b04c20b40d03010300b2035401c19500110b01803641a4580e0007818141404e4001540c9980051290701c040599441d0725a40b00342c8100070049420380910001c20706050751800050039 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 715618875 1250 715617625 715617631
    0x9010f0e0a08070b060a03060f0b0f04060302010e060d14240f130f0b03160306140705030106120f0c02010b0a1e09020309030c070e1503060417030415060617 69
    0x801da111044050100b00218103441e8030f25480103d81e401a1200070008880440b00d0b003020b004185051002116445164010f001c608000d403011100e40c03550404100c02ca440c00d00c00a1701180403420482e2492811000400028008510004003a440c1c818540340d074100c03c80c2d000c2c0711070288640d5010f070f0340251208907841d00320895600080d1b041d86800715180e42040010120b020341c4030080480450709035001081c1d0028050200d40d0715900c250f5541c940350580c1c1c482520b00d20301c5c1076015494400b2503500d0310311903981910340502e1a480c01c1c100700e9014072554540500c80f82e41d0740385000410070350300600c01503e21710741c008a0582d0510042040c1c0380703a1a0300c0307100c3d80000c80080481c42e0450008480c22290007050058499a9030f903441c50861083c3c000400c02800307007038000300f020301e801884540561141030804044c500c4080500d5505c9409a5000d08010440550841145040ca0045a00503c1140d503004640d000c003800b402503a031103401007004601900c00520054991110480d8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 715620125 1250 715618875 715618901
    0xf0d061521021819080313230f0d26030103060e0a03093b160201020708120405100e07140406051003090c1e0513022803110309010f 58
    0x49045107115000041d440e6551109000f503040da0041c02c500e41c140c0d134070303100281858010f4940d90817840070302421202c003a005034040c01036100791400c1c1640d15190340050242014054071541b0462a0401180d60340f00d400841e0105144041d41c22100d40c0c508903070b00c400c0d10030703404142c4a5055107084001e0714100300d44000c42e580010011004030768000c5445044840305400320303000c4003068107803208071100300f0f0fa0250101040400b44169100d041021441282e0101d2018600c104410040b0300f0b0748610a0042c04200e02030010750340e0420403c0d141c540051041c0c040718202d484000030181900c100645045681c0c015640801c0f03001c80c4a10340e4101c10b101210100016814000091680011100c00d6010036540c1c3d00c5880030482101400c00184c030710325500d51000c0d22450910803e80b82c0f107001c0e0314011085507505c1d1503914003038000e940041001004243c8414000b428a13201e040903e000c0c002010b4490031034015040100c1c000b54041c07402e050012420341c2c2900d5022054a9650311009 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 715621375 1250 715620125 715620127
    0xe010804020a03031d0405180705030318040c030216110307080a020306150105090a08030c0d030b06070b22060e070b0406090b031e01060e040e120f0d06152102 70
    0x4030059440390106400e032a4541001600100c0d40c40400f41102490307649980c100c2d00c1c4c51309200300119003980032032112010320119040241c071101459101e001c0d071501441e0141110f202c0005918003030300400f010000c41d203001403c0000055a044951500000070390f1050410b1042c00250305050103104007900000004000600169002c40c2c0e9550380144a02d60440c2c1000c600740381607219108407036800b100140303202d810340d843c0c01d1203644a60001034980d02904c01c249028400074028064010b06090040409090003800e4441050120001780030501c242085003e016035044441c540c401414080c2000003030b84142ca022603490000039400c902800603061100b00856584400600700751030300003013000d40780c0c1c940070710010010f591a0180c1300110803000012400d20340c041010304010100300d03000d0081002ca0498507854140707070207507043e840740c08202e414980c40c241401082c0c5049540e0000425599901001b51103030130064944000541c20480c44081d140d0100c04000e001911007411 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 715622625 1250 715621375 715621381
    0xb0d1407030b1e0d060504050717150105030d0504120204200c070801020c0d0f17190b1e040903180303020a0215090a26150703060608041104020306030a0c03060203070e0108 76
    0x10f80001c010791340c001d0450341c8502c0050308006003400984010306421160882248032210990348401030710154100c9480400000105841d0000e85001d00003c503803191031400381024244003502003442b01c00e0703820646480f44c0000f88280b12040103955a030780b1440545030207001a0b81402d06115501c4104668018015481362030008034001503182e0b4641025408501000001d0303918908083c40f0303609200b400c00400080c44000c45a112002c0c0a0740d0082040982141c10481c440586c45d120380080c0c0c541400240729070820b030f03001460150090404440007004620141c3c900141070b0011401a0003205a0804504160740010310b00d4540c800224104800800440e941c040c06100c0c50440c810407488800317588410000c800c861480000c00c1c0c48055000350030540c00d1880684142c0c002a1070700f00300003540e500c00d00c440d0b030149500810030ba41000e24001048069000600b0303155060288030136031000103000d40d546100542c410040962680f8103c880644501550005541800800410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 715623875 1250 715622625 715622629
    0x16091b031a2b05010903110d0807110c06130306111c051803031f051e060c15012904120219050d030801090507020c0a0b0d1407030b1e 59
    0x41d030580c591094030310941c100300c50300007035802c10070352002c0300c00c0d04015a41c40300030b00c1010f402c50380d04140a0b072a07943d20000100c040554420b010900c0100103058500402c20b258070480d00d8203c0c442e4800100c0b00380507111000507219600800b444031703464003101420801c010700c5018a8801c1c0c1c1c11050002d080c0f046a541610740318061982919909942e0800154907591500202c51180480c008a83d220310380005080e494024058032030340312910260002449190240305185001c2c42245035203116070464003440b1654018001100040c0202610700383c034009071844c040e0081085005061034044032044218410a441c1a110542d10003080144001190005001101a815208aa1503d1541c074680c0149445608000c0d44510103806030f03c10300d54400b85003416540c0100c1c041001d52910941a84d99814210300203412100e1300d10100000c0e0b14500c0035240d01100c964020a4580c503164000c00e90620859034000031030b946083c0805c55040442070710406007480501d4000c030400c9000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 715625125 1250 715623875 715623911
    0x1150509040c031704090e01051b0901050a0305040c03080309100f0c050901050904060810020703120605030d0c0303090606270606140904060302091518011d0916091b03 74
    0x242040d500700048121021300001100c2c000c01c84c4d020100982000e400855020740801d03a01e040c0b511840307800034543c01e8513100c100c40c048501611040e00e00102c81d04c05070080c01004000b56682124090300101048882c0010362246030103501030840605034102d40003c941c0030080e404803003490310041c00402a0410304880c1c409009082c1240c40c2c40601c00090054202c68201d18040c0c0103480344c600c0d4101b8160060101240310b40c560881c2195481000300440b10036100c1e0390b41c10380c0b24140500c500c80c050142d0242c100e002c0d20f00419807c485890300c0c800c5d42c0d000e0340030000510807041c000040e03060311070140c181d200c129801030080500d0128010320700c64040d9024545a0800207071058a555a41d000c070700190760140111126190005100e903c440340e0200181c01817802e182c1c06100381400c1800117058070a900400307083c2c0c0380c07071039a402440c180003840b501081c0308581c199800c56801464a00080c07507101e4002c03802c4101d41800e981c101c41400c00d0341e000d2506040e5181c5026031124 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 715626375 1250 715625125 715625129
    0x606030604081b0a3c0f030c08160b0f0702060f09100501030809090c070309140609030f0706020706090612020a1407030309050c0a0e04061d0f01150509040c 69
    0x2484162a5031500f20007101106840d115142c1603c1414031481c10002440720044000d00403c0481d041e0b5141600c2030120344a64042c40d62403030304c4000603c3c0002e081c00811602d0f880c020303c0e021955030560740c0e030207285a0204075102010310303680c40e44204000c0356000c555400b080c0e102504510f420490f0b0083d56480001c2e0900000c3c0700c180703001a030808004c0004200d42d00300c1035014032444d696420040c0d520307800a41c0b0755003c1c10b000d500040840754800f08851030280e25036503242c0d58170704d0182d007220030811a19084c2e03807200040280d49060360b400c0001d0840440031001a0400343d2400001a2500900740e001405002030711008000c00d68010780d0307415015813114800b50b900d007107214088800c201e020440c1c40b03001e0008580700092680c994884c901c640e10450440d04803140c00d10421240805c18400c03003031030344581c400007000500d040d00026071004285480b03010416400030207a0500040300c810009580d91032002d840c800c4502c00c4031200610056030742d4580d80c00c0c00e46034240c1520040c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 715627625 1250 715626375 715626383
    0x31a0a1a010807110a031101240311060409060602060703151a160b0708150604030f11032811100903081803031c1a06091201020415020105040b01080606030604 70
    0x1150000d02e0042c000d80c0f604120801c0c080581d0118045c0e460080c00c0d07880e4181c3c03414015803a0000005480c494641015080c081100c104d0034110725543c0d828120202101d04a50802424400014500c034580141005080d494001e0038442c940780c00000c0458100c034002a50084441c50100b05031022019800c04018a1400d029540c0528085040f03c5003c0c108004280c41c041c5401c000c0b144da84034501f01d000d0000a04550820040c407002c121842c010780c000500060300804c40b640000310308000d0746903a070f84080d00391404110b100d61841c2004c0e240b9221810304840c0c03540e01c0410000c14508104a00a0440c0c15007505004c90030000d10508960000501003a40000c0c0e009510300da15004004801c0002d0031250b403001035881d03049604403c0c8041c01440c80c1440301c280c1101102c203400c104850b0f00500074909061824041103070041c02c9400c0c208040d58200004245c15101c0320384186144d03000d40000c200c905251801c800a148160700445c42c030740160b81070065a540c08200c0300c0d081604 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 715628875 1250 715627625 715627637
    0x602011a06090d1704060807020f0105160305060f0909010f0b15090402070c1a0d0507030b01080606090a0305010603060501080c0d05061302040b03030a03060e13050a0b130c031a0a1a01 81
    0x4a0301e499100004c400403182c030512000f00300004e445030300824a901c200255400da41081e200031602c203090700c40a48407012100642c4518200c1c0c2c6110380d1000d5804103004040c03040b030f03100d1840892042c040941308940d03203945404140c24890758600603240031400503901030303141d61a1003c6c008a01d0140c020205c0c4902d0300003420009202091020384060400d220203800003420315540d50420354031411035000003508080c000340980b80607205500c040d001c1030b10391011507642c80c4104112603011700f5516603c42c074007a03804030106209110381002b4512411000400b54140f5030f00c6440d11260030741141c46000d404800e0f000013800400c0041d0000c1c00480c050707500c180f440c40001c024200a90b400d41c1c00d03100204041c2c1c00c2540c1500000c0454812002408031038030303031010101040500c564041c10380c1e030158000380006103940d9030403503200052a4074040704045550301e00040040941c0103580c81c460080241d98840d40000344550081d20220003000201a1b82001580742103103108003a0502c44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 715630125 1250 715628875 715628899
    0x16090806161709060910060e13020a170a17090315040804050d03030f050f070c020105072109030b0a020a0c081b01050c040f0b04082113030c0602011a0609 68
    0xc050703080000025180c1c2150a064a04510499071342ca004403031002e04c600c80c03018405100341c21031240790309032605240070640d160350304070032010490748044007240c100130100030014070304c140c07aa100c010052440c800f030980c2c83c1c140c1c04c0c00000001e01c2010b001140c601000204c14a550000d00100c4490080c800e9504694031400d000407035000c0e9a100c00d401150b080e82103c10180e05500107044600501000c0000e83c0f40d080b01c001014500f00c4448000c90f48000d8203a0140d80210040c00c02e0622500c00b070100c10032240503130042c81e44090140c5011550f899418000c103c0f001030450350003160325008605041c41018000c02d02c02c1ea42d00d018140da40002420024500001a001603c0e00d6540081c04282042000c0c8c140b03581c420702c03603010391140c02e6a0101d003441c5210211003c650000000740408a443c1101529802000d041c9618240040161100c40c0c1c403241c0e0138600540c014a203200c901882c00c03401a0a41d0032040c0c14400c4009945600c0c3c1c07180e9600300c20b0786c1b1880c60544415043d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 715631375 1250 715630125 715630127
    0x11202090f1e130b010f05041d0c01051315020604050f010525050d09290103080d020a09030f03080403032717120108060a18050307021c0213051609080616 68
    0x10f11500090826449000042071801e940000e2030201d48007680d0030080c85c0300d240300c00901002c0050402c0d00f140c220490351002581f18001030700da4a030352036807400c8140f0369641da0840c0c0886d03030301d1071600540c204404000510000f0701c000003001c4d40305c100038807142c900026502c000000c1c050003600c0e030b11740d40003080101a1084098944d10505200108061038503810080b003103902000010074018810042c420000c000c540707155040f44d45c00701c1044d0402c042140c125001c2e4210f8500f420130030000d040b001001c14203900320482040c0c000e40316a00e0f1410f0905005068400c002d124034005413002c80b403424550400e8007a181784903000030420010364050200301006105480e4400c9070300140c5000812481d40c04200c00e03001d41030100041003146d0401e0603001034034048200141180d041408020b0150400c01d40b24080540f10130311114000c43c0645c0000c0c800c4500b0809400305517910300420048107544488080081414244815003a262441090f6200030082160703041740b043c922035905036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 715632625 1250 715631375 715631401
    0x30e070f0501230c07180b0f0f040e0a0f050d08070c06090c08010f1406010801030b0c0c2119050c030d1e0c050304030810051804050c0603011202090f1e 67
    0xf005660900ca0780ea0340c140c40507541e42d90098000c4a001c40b950300a8481e40301410700c500c3c14800d0024100c441c8100c2e80d0700800038101569580140c00c941c84000008000340b09001002d80d00380b0614070281140050708084e0b1414a14109983c103001e025000e002d1180e030840c03c9401100c0d8440004581c2100360700c2c01c810035081551000b0060341c00c0c00800740c905401d5820440d411010400c101c0c2195460300c0045801c08003c0c031018001c2a8140040b03150ad040c2c035001440c240d0403041c01c94198401023410200040c0e980310084d8181c3d14041520030b4641c1ca40b1030b600500340414601142007009c1a01c6043c4c90b44115224085210340d03a052705022141141c40d03800702c002c50580d0420504505d0000505680e004a604400003444440090020107541802d07105403000500706916144010480c0359072401c2c0a0000c2d581072050207800d588550360140214003130301c150584901238801034814850303644406019880c1001e000340400181d007181c103084411400d104c08072441541c442c501800d000d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 715633875 1250 715632625 715632677
    0x50c090a05061b120a1806051c0b15040914150f01020a050703030915020f0a0f032706020f0606030a0f03090f090231060e0a0e040b0601030e070f0501 66
    0x195010f41010b803800c0b01c4815014220044480d114069001000000c6c101c069019004034408518103100700baa40a405040350480b4a42c8084002600c40c1100000b644091072120385140c3c20500003001c0c025800700c0e000d480103101401d0031400b00c1e82015204070f0304a07880074594070300840811103c3c000d240e05c02c10000008542110540c1c0300300351a07090007410072000e409080e4500c43c440d10039102c10340c0700040c8400c500b1200d4001c0d00c0c4855981d0388050120307a8418007a030401103806035503680d015060a102401056800c108820f140c580f400103400c2c40c081040d0f40302260844420085283c6012a01c10080d503803017103c0c605a000185010780d13010740190400c0301710b40c402d100f01040405d0541e00800c0c40c41d03031000120300d8048407a07901e512006031030f280702d2074181041c4804124071402001c4181071018014070b8007a44680342c1342008014601181c003512a003008405101080d43c061058903550400c000140440c54100022405110b4880c4140d0b81000151548640c94000040007811 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 715635125 1250 715633875 715633927
    0x90301061d040b060d030903081e03090106090c09062015090d1407080717041802310608070318051c030203070f1b02150a03050c090a0506 61
    0xc285010700c000011048115421910000c03040040b42d001d1414803820313603082e9890342d910b0112500b907994521041c1c100229403148040d085490190700d80700d0502a521032612440006610ba2400c47c3d88410b03540b400f0100720034840309207405e02c082607029007101c44a00303a6070418906507110305042803601c0c40d0f000c0e544602e1501e880500240e242c5c08115031100318080d94501c2c245541400200d0924030070410f00134650001080108006066010009601c8001c51012410725030b5501d00f884074030318400070b0401955070004001144502140300c0004180a8007100c000e400c91050901c0400c0043c1d024100911000000040c0c80300d11940240c180f0011402580300040032502c3c1550b610552101011147c1e01c81c40f81c0101014443d2098920801c015502c5001521ba008001d4442d065242d010000156986034248003507160b2034000300308103401041003640c0e044200001011500d01514046102d0010000301c0c2003a9215540c500980380d0403071301c41d69201c2d0010820001803401003a480 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 715636375 1250 715635125 715635149
    0xa0209032a09040f0605010602031204150b060408010c080f043c0609051c0f1412040c05090a0b0d02011d0a0308090114040e04140f06010803090a0501022109030106 72
    0x4204010300a030484c10358030405040c401c0c1e90700c0308000c0c0d890780200f0000400b20380032600002c010403002019076000b0107010400003040140c400200e041c560142d040034006a4549206848190740568101d60001e13442001c4000350400359186c4003060400da004260202c00414800380340380a600013407640b05240344042400255504c3c0c818043c00170b01d0350955103406505948900e404107800120700152403540c03007031202800341030b090368400b81c0c10403481c0118005000010084035450720241c00b0360300480040303100c11710385410041b1440005020801d81c5052401d094100e4840030b05040c051617090900041341901b101c800020783c90000d00b480c1d40318003411000420f0113400f00081940b0300d001ea940c0804010505070018081c42640305800345c0703640c0c2d200010f02052451064200542401040e10000004c02c00a50716104003030b0031507a0f13144c2001a40301c1c0399140c612075040c02440c0a0000d8807c16481d2000c9800900710b82c0c05450444900207880c0c0030030368083d88120040c02e4030407160 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 715637625 1250 715636375 715636381
    0x20703051303210318080a0203070501050c030411030a0b0106030507120c090f0f05091b09090115020616050a121b0306090e031e0c010906180b0a0209032a09 69
    0x202c000384500680c0e00300d10480083d070a01d240700717001c0d4042c2c0204106821011110310341d40c4940a900000103103045000074001140012020700031a40950344c9079803c41d4482c1014100540f60711a044001e0348281c0c0803084050004070340c20941811501c25040009032680c070410240e03901000d40b58500e0205e45403e01988000e500020101c080d01c1914032010348058039107000040c159194010b0982c070290200c0003401002d1205110103211440042082c103080d14100800c1c4440e4007a040326150f0400222500626030b030401040c1c1e800b00c0c465149040f91800410301510380d1041260b03c1d820030000c030440000011068101190040c0c0c09140c141080c00001c1004000f4202801100c0545062040450040c40000161780b580d0996072002c0c4203446030320408240c030354842c01c3d1408465480702040c8022910500ca000600400e0340603510750203031145082404402c00030002c0454901c1031040070a1510001541050114815240c5c055241c1729180e800124001c1300c240d07580147c1903410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 715638875 1250 715637625 715637633
    0x5040f0b19082a070b090105060d06020d021b0a120804020a03030f090b0a020d021e150a0e0a0303020702031c02061f0801051302030706050408030f0f07060c0f020709090b0406020703051303 83
    0x44c82d21500804a94203113443d1080030300d0a03240156419a40000c0359a2a680815500e81c024407801d84120f400501d420880d0081c8480000d04400811184d04081405400c1c0801070341e50729011006854a0302480c50264006000f820040c04040c08111002c10362010950040300400060201104090780340d0408007070003543c1d0000c1000010050203119115961050702100c00c4660103504009400310070003500e10306861500c0100900031b03694943c10312040d031100a00003020001d009aa01507500c000900601d80b400843c0c0404400c11100781001861444e40424200d4009400070550182c4602d01a0f540c0560550358010601d15440c0c00180310001030544003a4590a200703409980409564031410340e10703070003580720310106600304005201101d80b41e100244041c0c454224100c0c1400c8650b1605422030303400901c1800030075008005141d40c15010890340000301100c050502c0308070815660748450300000344c00142155004100380c0c041602035000d68000d20000060056029586d040c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 715640125 1250 715638875 715638877
    0xc15050105120a020a1406220f05011704060c020f010e010606090b030103031e0504120303060302040608030c030f094c0509011202041505040f0b19082a 67
    0x45920300c107480c0011002440300b07000c02d0700e840d407540040c10441028a8205480041d1a0303e610310703980040708000c01c40070f819051410400c2e40e254581007210302402c00700c4404420846800507418400d42400d83c8001c008a4bc00199001d580400702140030400601c00b40d10780344060002081550074110703a01c4d408201540410202d490301d569201c540c0359540a2500c061000317000160000781c50400c04480d6401d86403d05036040d5541c50560314142d5a42c06884282d4084c040880000e40c07104020000c1d0701d05800b800300a4070f20710010714500924524103075941d22070b0104103220340c0c0b404150100207541704040c0c60200303038050f240140c0c1103004c1d00d4003596100340e840b01750001c2d8a07000caa80e001c0030610b400c07540c0c45002a4035514a02000040190303a5160b80002c5240c4c007580800c0b01060500090a103200c40300e40076124a51540d0611030481c0621407aa04181c00c1104c040c0442011500b0000c801c101d100501d040454040e00ca5503046030b010502d1002c0c5c10195602a00c903080c60b400c40d14 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 715641375 1250 715640125 715640129
    0x130609060e06150c0316110405010801050f090c03030a0c0215030106050307021c1b0c080d030209040e0c0d26070f11010f2724140a120902010c150501 66
    0x440707072410f1003a0303032441c480c0754051000048401da0042c01842c1c14101c24028a01c415401000800c9050380084000780c140e40c0242c200c03100e10b1351640103001b070b419160034480303401c03501c87d10103800c6192403d4046a628080d44660030200080c5a03ca1410740d180c1e14182038018007080c501540e81c0d80c40320b0015180340d0007176440c80300500c1604000d0f1000d00d80941d040748003080907500c01514611140034040d1828003028141c444400312440013461643c100000c2c160303c03890f6200980c880e0000d0301000f00302c40031820f0500e00e903002951004040daa8000072400c60300d41c000c80d0500c0325140c2c7d181c01c0c40045c981c6590a001c03207100041c0801407020600c4210300092040d030140f540030110070011203081d605145001c010a502101030040e0340b45090486035482c0c00d2602604d255503945c0c0740c2c0e00504134a180144121400c16000c0a040d65106c1c900521062000c4d04151a1112200300106010783d00005403402c203030740f6407000045a20a1904900140c2c210000710311a441e26503040c8000c0c5000c1c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 715642625 1250 715641375 715641379
    0x1407140c01120e06070822050106381303050703030518042d090611031006090b03010b07020a0e1e010f030b0a0911030703031218050c130609060e06 65
    0x400c1c03034124494820b020742842d038440d103c040d214030344940300c055030382400241151910b00b2040718060200c001480080c501c8a00a0001084292405954014080f048080c98440c2202c100d41e0124608400d8824044070b030514540a03901e0980c0c039840b180c061803030b800080c9280145940001416448009040f81003800c600da000340500c032074200011600000031543c01c000d0a4003042024603181e01d25128510601400400c1e2110141d80300800c445500308450500300020003404412203046041034003808050600c40403050500b04801d080c0d000c14031402d642440002018021074684032844001000102c20390809424480e07881004055181d00d11091230035020000910302d0075040c1e41100312504400d0701c02264442403440c00142c807201a00b500e051a0000b620802034170300b000f4050042d801ba03550a0100502800194103a034000f810380d60f82104c2029400e408034201003114002e41c4800c0360060090084903c101024041e282d00c00d070703012458000001401508070704c5441c854001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 715643875 1250 715642625 715642637
    0x4081612150504060e0118120201050423031b060711071a03040f05030a0f030f0606080703020c1006080309010201050121143c0a03020d1407140c01 65
    0x16240e0311030a00c0c414620150910a030822828461031a5a20042e0000c0c0528808102d141a0220b45070079180d54040368100e001c0c015500d40c06120b504020001e102520344000d00007420b040d240c62aa0700c194900401000d10707042840100200d0070000c9070000030102d007000400d4249418200d450303c00c00c80d010f2020581001840100030303008a51001918001407011440058080040d205900b00400840d00703a9111000c240101e00108003600c0102c10942d41e00b50f01c0d124144004013034031060003c00200604100c810b02c50b8940004005505c10900d19005031144040061030b860420030700c0c00410802e280500129513440301000901110fa000c0c0c00074007031641e8036190020500c0c010715070401820440c0481f40005441e4003942c80c0507010400447c0c800d801c46440e0080c910400d1a0800940d021802610881410200501d0040010040908883c40164a02a48400b544120581042062030380d0000c1680d282c0251040780e60440c080798290303110100c02c5952000044041d5002c154 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 715645125 1250 715643875 715643879
    0x1f050c0d09031103060f18010e06010e010303110102030906071d1806042009101101020f030f1e0a0c030603050616030b0d0c090903091707030c0602151503030708040816 74
    0x18000303402400f48514920124550b82c47d00302c0701e008500130f091030752269500c554240b9560b120804c40c0318080d003049190301315103515500e00a03181014840c501c0d58507074010f20400a0040010a604e6400016801d0400b888040494100400701c10700f15107a41c00080590301000002d0003452076031090200380c80800c42ca46811a03101044404002460004e040070414021503061183c0c002d04502094180200540c111002035401c5e6000040c1007522413030f0100c1006800c00b610008141c0015100351910002c02c889030321100d071120010516901651200114014980f090b07000c10b0080d0b410101340d40003030a280c0c1103502c1c007210003408a8002824042603108601d42220b83c00309a41d403092407500c07594601802e040282071521001d07014010b684200144101c120301c0e00246418000015045903811860070307441c5118640c0000e8210f510007442c15541d2040400b20030740101c3d040f00034003442e0892100103880c5120f1030388000c20007400814000346100000906c05210450200d401500603 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 715646375 1250 715645125 715645129
    0xf0c0209041a090c0312070507170a020a050103020a08280c1d01110d0305040303140705070501060b03011409061f0f021b0d030513240207090207021f050c0d090311 72
    0x160f0201113803603142d0020048801c4c604011401020700c0c07403049003038030071a80d03940400f848170524105081d00315400c1841c1d040c00714600011550003900c002d08007103060441030000100050780060640e1040b912210031103e40213291a0b526200040d800030900150201c4400281400510100004ca0440000400042d076000f43c03904080740d01da0303a0060441368070310f19040340039010140082d814180e89400d12540c008010b001244102c070a03455041c1e46424a26045084131341aa011100350354003400144483c01151502c0d50040d801113481c1141519080300060740e401c104203031003d100b540d15941100c44ca400c014102c0000f24250241c0703080c680f51901c0314080120004070568040b1804800c240064000c40107000c00ca914480c1c0f0701101e60704c41007603504504405141c200440500f0040d070303401c2c40d410801240507040e40181941404000c0d80840c1920200030070078641880d180c054481158810401e40b62142c2c4454110345945442e0725018041301400d000685041c0708500c0300c20014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 715647482 1107 715646375 715646383
    0xa060305060f0618190902030c0319050607030603080f07110a060305090106121a06010c08031905160f080c04090e0601090509120a0f0c0209041a09 65
    0x3420164104500ea44c001d44006003c05078000402c1102c141380c8000404000039900702286880c0c1510009080c80030000a20760140b040e08483c0200105940705000134600420035a603894841900c110b0598040d804050802c2504010406003101c080e8010404940101910f4030484024000a103611505900000020340c680341400040c0340c00f131149900800c254a03503030b2201e40295641031001e500d10403040c1000f0b003160b00000c1ca164042e050190f81154024681d170364a02d0100201d2005c00c41c19201c1c8013a00d450b0000003014182d202c1d0501e0794104a030b4907030ba0004100d0f01c5003140c14040041195540c910b0900002540d42002e0082a004075808409844c2d15030610005004941004107540d0241d4080c01111103407002c00c0049502441040c508090745641e40e04c4182c2c6d1015222130029040880d2500704410300941b4100c0052203034045211a0894844016059507 = true := by decide +kernel

theorem cover : BRFrame.Cov 715467625 715647482 := by
  have h0 := BRFrame.cov_init 715467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 715467625 ≤ n) (h2 : n < 715647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
