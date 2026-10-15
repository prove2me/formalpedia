-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3871
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:55:32.984118+00:00
-- url     : https://prove2.me/submissions/f92c4080-9b3a-429f-a282-05fa3b4d0cda

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 696043165 ≤ n < 696223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 696044415 1250 696043165 696043171
    0xf0a020c010b2d010311070b0712090302070f0e070f140d180b0606070f08091c0302072d0506091c030c21051b0102091203040312020d120f060e 63
    0x31064145800c0391202e021030350040f0076000c03410301d8a00004441d2222074481220ba802d5080100000f10b82c44804003164007035800340c09113400520b41007110082550215440c82212002129504040c0d22540c1d0102d0321b0800780c540c200407880d50040c0d901d030f0324000e450080c410048080d0310380c18641603400c058203aa4200b41581040b041048290082140034040b164001c4001d6810604220056448003108001510041c0201001003002c42c120fa41d07000b0700007003032070301100e00d03036018421490065a511058042c580d6602003a0050241040c40300f1384c12204941000203c550303480c500000e200d00c43e88080750b110b80200300080c6100c124000b0702e4481100500c203580d2480031080d0307410410550024080e48895100010140800840e8068140c96811424544c0c101c440803030385c890240284034802c82c46800a12610154000720f2020016200320780c09400704680c0340d051b145049031114140c0f00c1c03c40104c1d480c0052030794148001d91001e04850030f001c6000030043c0d11442e501f15082012 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 696045665 1250 696044415 696044449
    0x7020d0b040614071e0e121e010615080a06050409050102120718060315050303120108070503010b0d0b0604140a090501050906010e0106080405160f140a0f061202070b040506040c08060f0a020c010b 86
    0x8c4659400c40445214108a0341c402c0c50080061030f050680700e2185c1c800001c0c601040040b864081402004650705c01c000808004204100040003483d040707000c0d400c06502100f2548040000a07411802455460a032a40da44102c15500d4207020707043d001401100742600a80009240105481e282000240300091074154120a15890b00d40b0451400c0d503203811980c080c2e414585180c6550711070002641c40341c0e43c00001c0c42c001d49c3d80c020101e00206008181e1201c48070071081400007425050b03204120090045000744102e0342d400c400c41d80c0d07070300003846075588105080004001c264030408000e90424803410603202c1000c10042d800c80000100d0f01300790310468042504001c1b02803100c000000380c00b002d9426180040c94040e0b809003401c00da1194034241f003000004410340a109038100d9040315404070004505041505040d60344001c104c4089894080001d0003250880d00014a60700c244801c081440382036407403c10002c081e4001c504101490740d03d401c4c90701450360350b210ba80c4608000d6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 696046915 1250 696045665 696045673
    0x2070803010302240712260601090609050904170c03040603270b010902090f090f0604050906011a18090426090303041a07020d0b040614071e0e12 64
    0x542c0100892400c00c10242d503884e00080c00003406070800c410540d80c1040d008003e000650640035800d40740c4010310140364a405102c00103202400301c00c6110f01d80a004c081c0e0340c01420540302c0b10142c41c0030b50907001d8207a1143c00e560024001840c444030421030284c0d620480c0341443c03071000c02c00740380d81c10a41282e00130a84541c0d01084d000754401412080300784010304080e040300c07d13854881c0485010701806c0f85558000030001d82d5911351011400c8880000783c5160b54914094503a4003e11030240c5003581f0450914001c55625140000c202c0d060320403194200307080413002020402658010540c0c9240114000c021211603034074078054a20650047d002c0c8000c1d901144850650032540d600300340312b144000d0100801031b0324004141c60941c0c44144000b400340f540207440740d8032801100b9009611060442c440010442c0107426240580c0c800c0d0030503c07401001e4000084410750031154240041c208421002c0701c1200e2022904c3c60740e0840c10003042c1204100e0104203035211800600d00d003584 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 696048165 1250 696046915 696046919
    0x1103070b070c1b1406070809010f180905090111071a0a0609060e0a0c0503010f0e040203030c0f0d1d09060603060a0b04080a1a070f050a021009060e0606040b1315090207080301 77
    0xd1104403151131041141d0300343c40d0018554541c10b441c022880e0550401c000311482c0026a030086440b5003250740b0151281940c141d40e0703220b03000a03110840d0304500c207508100342d0703031500400902038a220301c0c0d11408980c030f07034240b0b4414a01c01c0070b170080041c02c207542c844000203183c90340d40c4201c10181442c100801c0d810318240300703448165203070007070004100041000100186250401c02c0415101e261703040c100b2544403400000d2940c003a0a40300030f6140603001c00c0c4955288005909203c811060f1140526407460044000041d5100104240c0200c81c030400640507140810085520000003011000d0789a2164404002c03034005400c05a1a035101c1101c01003031120129204942c8008081d084c40c2503c1e02c230f900201100e145206507014848040341c0711204c0c9000f40100c10205076241003c1014451500340600030304001c4444042ca400b0741c0011071a04e08281c086e4048803240074004403450249800c1041c02406ea28145002118029002180c040c0203070009215140c010340106840c1c2d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 696049415 1250 696048165 696048179
    0x20a06031b1403070507050313141201091716060501150306080a020f010c0819080f01080309032503051501030c06021b19030506130b071103070b070c1b 67
    0x2041d41c0e084042c040300b000d014400d903015500f10b0380d111080346402a01c0ea20207242162450080e061841c42009a5220114001c048440100001d04c000c0f155040040d01c1c5801d0103088440780f12000d480c02203c02c420405070b04d003250060000d00c20a40d020600010702d51505000c50303600380c12020301a880c0324110080b01d03602d4050080a046a1009402c070401c4550001d40c10152100300581400b880003c034106201078881a50802c0a568030710607034040e40d4000061034040101c0340d1581c40284c1c840041420440041501d1000c48058010644040c3d6140d400d441e28012429032a00d460300e00e800400040c80501c04d104d4807840c010406031944d4114076040f8585912a000501190300c1141016074804803da120040c404096a0000c03814880d08403a480004080d0070107842c510450007031000f501010540090464001c6201c94010303141c00004455041c1c03a00705015140e4814440100814110402a500040c40341010000d84e40c0950301c01000741030358603d2007007954501404101d80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 696050665 1250 696049415 696049451
    0xc030b0f03030406080402090a0902090406020307021204053016081b06040902091305040f06050106032f041511010e1203010b070c05041d120f040e0a09020a0603 71
    0x24101c015608080c2003010007020118000c102a10402d921000b00b000d007880c5501110300541c014222031600d00c0c0904021000e5031058031309100600c1900f41031203108092006a8003070304d100811060000105800710b0018034482d003c800c4d0400d02446040d440781c4401c1111041404c6a0568081c00d0b03032410003014207003940c85005402c819412a52603100d42e442008079070584140c001c2c01611407000d000070500c108036401031300400915007070911050012504501ca0550701c03895043c0902e0ba240c0c04118196004a05030b0400020261019040d24800c410019001c1104110650415558000c03905031031041501c810b0101c2c1140007002c3e00341d502806885019130a050040603c945c140c00c1c00c0c5c5082c03005202c0c0002114021070040c1c104103000489070300500c030081c400c1c0b194895840c00c80c02c1b42880c01e48034252171320a42804032007a4500200741d4800e40e014550140c20030b45080114040004004d00600642d5940c100c00740060b910039409001900c416a80000e01c003c640010780c041c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 696051915 1250 696050665 696050689
    0xc030d0e21070e070c0c060905091b03070e03010902040507090617061309050f0a110a080c0f060702030f0f07091413030e0321090a06080c04091e0c030b 67
    0x141c9880d4902040c0d600e03000078101003243d451207103c42003607131011012903201031480402860f020311300c0e0001a88a92010300c150580d2005c86100301c3c10f0311280000141e1410018005599880a0000541084c016816820601800390000c2100c1103194005000c8078000c07103070940450341c0914140003280c6d00500034984403200350007014072400c000000588030041074289150f02a111928403040110901501e0f660b0507080080310429242458115000340c6003802c403500420503c8000600070f4000030714503e0190000e40020400808882401126400703490262b806200e030300910510032808020050100040c035018065441c05e00003c1c0f0700f620004040c05401010103028440b8898003600310740c0000c0d526080114140716044080780c01d000324000b810301309180e20b00d4440051140703507008144005086440d814a19100c8a082d20503250a6808440c4540144400d0003484100d500ca040c3d40381882000112082009119200740c44c141d4210000181d1104a10071542c1814041c2000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 696053165 1250 696051915 696051949
    0xe040e0f011a01050403030c020f0619030603170a0831080304020418050309090403021609060e060a0b0f0702030102190c0c0f0815060f040e0a0309050603010e070507050c030d0e 78
    0x8a46455500e0081c000c90282302c02a01c11000b011031203a00c1c1c2c0d01c0c4000c448070852031101e025110031050f900a40240094482610540048030400501d554a10300b02c82e900ca40075101c1400c1d0307403907000c8040d00361802c0c1d01c106130724030740f00301780030b4480040301905220418803500c030159592500e44140016121130040c1c20015503203140b0030100154010040d161508070903070300c040b40b1790303101d040403407420f00010b010081d20b00d004d00c004a8100c2554000d0400d440c0034140010440d00c0303e80500034240c6851051880b142001e00c0030500420000e0300401d06240020000760800e003c200c0700c06080244803c1c088042541d003075064080048810103d0024418503800c4106180713052400c98458902c08c03001c080c254080c0b03000407d660307104504007014a0010707204103d5500c05c1185a81e550501e60400c0c1d0100b01400d0001615142c00000c0703030305a4602c5032603068552100102903485411605c42241d0b00c3c082c0340302101d42a113041000b1003a1180702d6031407884007414032007800300001006072407503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 696054415 1250 696053165 696053167
    0x6010801151406220f1e270608030a080c19050c0102120f06030d0e0102100c1e02070618030201020c010309060b040e0c0a14090714120108011b02010b0d030e040e0f011a0105 76
    0xf842c0c8151a0165808540403500c0c1c031f07000c503000503690591a0040143c506185440e05002054046000003c4c1070707900310a80340c4645075102c114540e1068050840c4001890700601c080c80181d034481c8001e0035130310380808000f43c10304d516107030f00000c0c0c00c41c12100e42c101d4003807140810159180030405404a140345040044005031507100003502d0f500000e040024850301c03a0a070142c01c1c2d118644091203001c0e800c3c0105448a41980c00035241d050031b114503000181d0308901c05030f440c15080700400c101c0b94141c0003070050058846c019009090503010588415586860417003a68071540901404506460042c1c18130328075201c20406e03c298a0740220070290040403011034145c07a5204a02d410410a080010005007410508034180c4102c0c160740480301d448000003d03490b10150400700b8502c214007524080300c100340008074222001825215400000200d9050229000781c025010b814805032001c544205c001c520a444e02d40000c900251507135440151229200e809500100d266000346011 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 696055665 1250 696054415 696054449
    0x1203030a1a09060d0b060d05070305010c08070807020303010e18060a29011407020a05030d050307020105060d02130b040e030a08011a07021530060306010801151406220f 74
    0x204e004075014010040040c511080814415601d90f900e468120303510404590005403a8074269010309400e158070004140c005000c2100c00740290081440307411076034000c5040d80c2c0b800c10342c0360000700040c0c000b6003024021034444c40c0b491030034403185101e82d024a10105101c5200380040c980030035014641c3c0754000700c1d0300ca54001a03070b010000540072014110110340702c001600004501c004950b00055243c4129421001c1c00c0d40c0200c003079803080900340c008102d103a40f8001805940c0070a160000e6012a10f008807042d04c0b06039034800d43c2c00850240c40015040c000c0e41c04140b07584d00250089004c181c0c1040100700417111102600780681d20f00c0009401c0c0450355000c2401e00d020320305204014070001c580400500340d10000501111541400040b0183c00d500410006100a66045000b40202400071820308014010b2039410020183e08140c4140f900142140da54100c201d0540c0c040c4040040700540110703c140502030220071a1103003607542c80d03d5502c41c00260161700980240c0c200c8010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 696056915 1250 696055665 696055669
    0xb040f02061b24010b1b28110102010902060304060c09030b0a0e1006030507062105010e040b070f050a14071a16030e0303150105071203021801030b1e1203030a1a0906 73
    0x55036000c900c980c021014044201251b039003080300446000aa030703034520302c0c4001140c0841e15103210b10340c01450082504190070004a099a280f00300181d00a8010000b0600046507540482c500d414145054050b894480e0b8481480c07000544061005d240c8800d200d002c02d8500780012020791003200720800200f07255540316526941584601018002c1c00d03c500513200340720025007000c5121181040029685410900100904c1642c0990b030300f0141d5000a40c1140c0540701c0e803452464a0303190350303050400c00c0408803090442d441014080800601c01360000950300e1181d130040d00e01065091249103000d1901e6100f08101c000198101070401c0d640140d94100801140c0c1c006210b084000c0705d82084100590380c5200f0010001d15072906100707240c9405506a01400ca0041010080c071610304641c0c00440584441982c001d52101c004900c0751160016901081c2a051000d000c04801c00703440f901d054211381048a00000f02900d8600120300d88003c400b820799240403c4480619601300000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 696058165 1250 696056915 696056917
    0x9130501032102030c0106061224030618050a0c030b09190b060f0612010f0f080c0f03010905340605090d08040810140f040b040f02061b24010b 63
    0x103060b038498115800002105807007030040383d51000d16400240442680c408004120144c2210303650b215529007040d04408449410000d8900091788001c0c0312110300390b442d444003d16500e880d004d00d00052059100c0010400d11400d4062400b0309500f6505501d541400320505800030840c3c040c9800003044050407161020001550396000100038060350f403100c000c80c11a8001040c034a60150300400c0f841d04603103219440034180c1d00580140f01466179a070720003040706811070280d0b43c1d8030380040c1c16409217030911240084090000400108100c00992621400c00d40072140001e001141d03440d1010481284018241507a8030100e6103241007468104000c2c0240205040140700f480105841000d020122054a01408030342007501c0d1001c815008110003089000c40c0301908c00441c0000404c0c1002c0d4601180c41a604a49100000d50740e0341e031846101c00c0d00750310483e40b016003404600041b01095000f1400039a413003005180002c5001c030310040c803500d1b10440c0070080321050014031040c002c81c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 696059415 1250 696058165 696058193
    0x2120c0f03040b040302070509090a0c0e060f040911061b012d0509160f170a0b04021507120e1206240105040b0d05041223090d060e030913050103 64
    0x180b41c103c02a11146000c030300b00b590a074080e5902c0494402800031008020888000c4a4030617410f005205a807001c6d8580349100445420707078000300c041005080c2e400c00f03400c80c0e100c091050300b8120426070300c6400148190020400844020304400c004040003009224a5481c00040719100343e214420b1451001440071040c1044141500c41c0d01040200408100002441c0400c02c0b4216115880b0b09103071584011501c102012008404d03031848030410007040705106150070082c0d640c100d940d04d8080c010310704598142010302100030080395010802c3c64205400400e5540d4801c2c885a44270001c2140b1800d1404c2e4144c15038201d00700340702e000c4c0d000201d586451103240303050031080381d0118010b8501b4015680190708000000403210007a2820340d200318820740c85490805c1c520160440101c0e011300606800d5100b0402d411811504410844050080103000130078007030b085400e641d0341c1d8040d20007100f16415140e00105074003405180080111459240d81c00c410005503141d91100103001c4451 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 696060665 1250 696059415 696059423
    0x40911302202120309100807170c07030f0c14010933050c12040b0915010b0a0c080d0e0a060e030901050d0506010c02121c05040e0703110c010f02120c0f0304 69
    0x900c907402c207900c0c184191090000000d01e40303040800a610082c28541f0f085032840d000820504c211400110703c40c2d00d80c2d00441c0c0c951405414889243d0f029520940d03541140800d20007500d214100040c40d0546500c0e050a8031000071448650900d09880c04500f40344590b64420006034031a10f0803410840000b40300484140049a03e4443c6411000c00748100c200841e103d0b1b54100400040c010708142c5a40150a120100c4100b0760f2044d02c0d001e0100e60138000e0712002c802c10400c59403001c0c8500e22807002203010b4803680b80340000c0703121600c0c1101c09640c00c0412940064030210180300003032082c1480c50115201961401c5c0003040000d0452140150304007009903240c003c21040d034420020680400c0c0c0c00340c40c1e150002d140c031000e1030380c40b50448580d10039a204080046040e601c1030090b1004c40d21712841c2e84640d6220048181c000c0d10015200b40001d2000f4444440c0c0307007a00340249502159051801603071030801c09480c40000c400102254080d08081200ba582403600300c0403a5482600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 696061915 1250 696060665 696060679
    0x3040e250804020118030501060314060c040e040c0506180a080706230705070b030a05220f1713030c05030a030228080a050910080705040911302202 65
    0x42d0320060303d0482407054860702000c0c2d50039001c010454150b21413000e4034080d01d00c4860601d800c0c4011a65020112204400b551091208100c0e00e10154690713504107204641d820003240d10b039004240681c02481c100c00c0c0b0710710040148a0141072010b60000982208070107000c0b294105040600b04e02c40c41900301c50b81110b081d0280364001d80032402d485080d036000c015501b49a58644400645410580d2090b2102e881c15010a000f103a8001c03108449000702599008044082c1c3c4130f008507120b00d55006d5844c01c00444c0508480d407a090000c1c255481940c1056000c0c6045040004081505030845802540310145540129400040159522a014001c89915030900b80401c94201c022500204505404030305040101e41200103071022120542d60f08400820300b91040390b02c0181035860a0101e0002c010510040d1683d82182600806000c1c119182504002c6402c4140364940d0901c80d128103a20b24042400c500c0030301c0540c02c0b9112040380c1904050204003c100794846000c002e104481d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 696063165 1250 696061915 696061921
    0x31303060b10050f1612030e16030b01060c05010212070206100b0c070b0313172701090308090f19060305010e160309020a050306040c05040b040903021222030503040e2508 75
    0x5c203007988291030680c07201d80038100e1007540c00040c0140a0040c1c080354503020f416180c00302c161a01c09900c045981003107100e5096441d1600568485041150595855408001c00004059401e040d1400384c0303400c3d80240540d1070822600e17000d01440d41c02810410104000c1c580341c141e00000d40da0b00703803448010311982d60380300d850400c0d4282954000c024080001012480482d4482c200540350400c0c040e140002c00500d0070385603454620309440040d0100740b010500740081402c00015024274203000e41420390b40c0d00440d00080c400401410b246240070303640c035401d1103090b5042c01440d00600c8a85ca048009040081076090002140019102003555840e140015503544803c03940040c000942551194100360519907080107180c0540f40c01542041a4100c103802c043c41203806140d01580a41012800c00e10080e44580c403600b41081608244012010300c004810a000c0041d803207880110390320740c40c008401c515148001e004031100c03102a00d910400010903155203000ca90103150080c2166 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 696064415 1250 696063165 696063187
    0x170a020d0b06120601180b01030c08131e06050a1805120a09090f090c08030a0215060406030b091b180c28090f080a0f021003060503031303060b10050f 66
    0x2540c041c83c80910384c440c010001a07014040400380108208121041c80700c2d1911100540035a500c48400000003084080061441101d08002419042c0b1070701c4104c9040130400c10400d80344074011420b682060b40c0e4020320200390b80610440031003041c003c52038490400c4640360340343c0760244240c400d54112800180448800e11030381d440b4014042d9000d00300311403030b0985000c5008108584040720510344121012032150301c00420b8030000385d2950f004081491711100d0f0344d003000390040c00c3d280d0086c2c2c8880000c40022211002a445040840000e05106c1035810402d140840100010b9000728a04404032000c540060180c81d801040d8034050717a51200000c190320031504204202214000d40030701c04800140e802084081120403041540e8840d81d12403950544409071382c2e4004011444003149200141007005902e103250406040010341540d985001c0380c10765000700070341c3d105091001418010060741d445598442c00c42501c5142200d11080300240142c07080d184400740141c80840d01841007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 696065665 1250 696064415 696064429
    0x302041a034e030a06060807020a051c1e030c090e0c09010e0319050601061103160f150f1b02030307020a060b030a08040b0403060606020a0807080a2007170a020d0b06 73
    0x440b62641e906903aa20b0406131500042c80d10740240310000324610080740b41144009407a800d0190000060202c004801c11455001442ca02c41d00040c409010f45004643e9141040c041a5030090b40740881c1070210040014581101a0410051003d00d802031014050640066641d000400c2c00c0035140900c2c4500003071310f05040345403840c00d042c00511107001048004200c8074101c90554407004805160500d00a0300c0f4002d054481580c900c0400401e804501e1140011000c240902c14003a84000c1d407041c06826280310b80200205d00b074450a00404030b20462b2080c0d813401d28503201031740c00c40c182400000c3d00c6004087c00a007242d0b8882c220820303a03070380038403016804940c0a2011030380c4903078981200a2070f41081c0303c00d940042c9803100009074a4000724050f40b022303501c88269403400390265121800f541109214070100081c60051296108806001840c08015000100700e038602d441c08100c81407405036698040e40c4c001c0c50010700103031100c2540022041d4081c0400c00c0c0ea50381c62001c6808 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 696066915 1250 696065665 696065803
    0xb0105071b0e0c04030519030309140303090c01030603020f121018050c0102010e03040303111c0c06060510120209030c06070c06090b070201050703180302041a03 71
    0x41c0c4480c1e030161031407850003880984215000100b008880e50780d042c1c6807807100d02992001a04a812090001d0300b980d0541c480b41c5a00c41c440d003400070301ca6200d0349503110444192202c604065100105202150720308100242c1e005001346000d0141d1819076010508400303032060894040c2c4035040b41e000f40b5007000d0040c03a541c1a280002004000240582c81c60b40c001900c006440304d01842003249140c1d44180207100100c1d000c8002035241c10b1440d9001c655810058103100e00500031900090a0051640d140148004059890010304511414241d04849041e0301080c40341c1000314110700b41a4000c0e0409120001e400401610350050401103030428131840c544a43c800b10024540c02041544e1041c1c1c019240e81e42d51b00900f182e150386100c4580d100d60140a17002c59410b00c401c100192092a11200c50003456001c0c0c0d00640e9240c4c003140984038030112090002003c01d119819500b002c100e008201b843c03000005281050122003000350b5400811003032440f00c91898120b2800d0806900035038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 696068165 1250 696066915 696066923
    0x5060a0c17060103091e0308090106060816051303080403120f2c030304061e0807020303160309020307180e070f0b130b0403060603030908030901081f05060309061012050c040b010507 80
    0x5a140c160014090f21a003501041f004100e0010200f890454148a4501a20407984500ea40c503252400e030300c00c81c05089a46442040401c008842c00c140449045000940c490b14407640c585041d4508291f00828080c440020001c0e00c1400c1a07140358006103d0300c054000369900c000c20200310103060149400c0e20300d074641600c40050002a6075500c525040900e071041c01c1c5600c80a220381c2012200480d0172740381040180d1082c008514904500d9070380c1e01c00b408041c1030020f8090704030f60220341400c0b0694024071010103074a014440c2e40c0c005004014040121a02500c6003606041e1800c06040c031a0144c2030018034041080c0960350045e8002801134005407a00320744450362854114058001800201d00090007000d00140c401800010b407005000c058442d04403668817a0320680307140c903000c900c03e94003415180c000103158031044020740c00b41c50701030003070080751926045074264045c02d6440081c00c1c03441701c802c4001182c2c0128407400c14440840300410181c00d42030040300c2c07070301139080d0180c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 696069415 1250 696068165 696068183
    0xc0509030d0f03141305010e0607050702060f04050d0f05061e040b0417040b0a091202010806121009150608030f03240a06080712020c071202131805060a0c1706010309 73
    0x12103030824045c884002d10303200c1c80c000c2c4650340700b6a039180e80314042a540000410030070700c4400700524103000036103040e5060384c40a50400c1da03600000b441400040c02e06a0704a600255050b083c080c0c1070002c41d44c0300c6115903409191130400306144125800c010b0000c1d003d00e078181d0100c1c0070040046505d0650440841c5d0403610755496451000320b41d84059414004200701b454001a080d2102552124161301616039251a6843ea002d000000c1007001e0245d1650148080d460001880d80c03292403030b403600a100d2401800400c90284048500a42260410354000e00482d20040c0b10101180d07404003410311aa024000c00404c044288081106402e03849084050040b6203140d0109240344a00079540d21170203581004034091080b441041c0400c485600005e81c00c0c003079050b8082d124022288081c2c901c091400191008004990384a6880030801801d8580002489002c0083c1a00300d5210702082000304403070113014180c19070300e0030401c10700340d0104000348043e8020f50110718040e0b0004524 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 696070665 1250 696069415 696069421
    0x904060b030d050301080d08070c0f1506140f0301110f070c05090a0203040308180705101407060b01081e0106030b0120070623070303110f0c0106090c0509030d0f0314 73
    0x3070f107181c100b40144481440340f03041c0d058216200c5d131003083c00780714540c44210709101c094441e41e600c03a200752015242200300d128940c090041e9807065000a244c4400e031620300d1000d1004201801401500c618401d130304000c44c3e0394402000307504541c070030340f900d250280d59140285410b241402040d8030059004c0900300c2040700540040e0000c600c0f41340700781e480d02c5465a44004041e9000101c1c0760070503455020410500c228101100310b481108103900f0700070200d01c40b2142062007a8000c41c0c0c00c0b900c040c0c1303e03101d040080d60055569a00502000810303500c005c911181c24041203014450300c010036407103400030090b69004108590454982d000c0000703496a01d030000540d01c0c0600e1003103400042a40000205e102081c440c60031040040301245858024103480403006407088a80b5030301c03000c40401c590b00c80c4100e04001402d1000c1140000b044d00c91405000c03504544c40d2054070303000c0c00380c200051460741d94003142001803980c403418020100e000c1d10408400030103101c148002c18420032400c1c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 696071915 1250 696070665 696070667
    0x16020714010c050a0c140a0530012702010f140906090f06030901090b0c0c070e07021c0f020d170f0421020f0705010c0c1217121008011a0904060b030d 66
    0x251744401c62068030107007c819034940c203108208400311076444091680900921125440c040c003048840034410001c152031441c050043c0c1403400b810b40c521500c0704500010781c00c41d6000900c2d01c030005218106210001d100c180f148845200d01c0700d09900c034a83c0020101701554414000e25080f40b800303400141c0ba442c081080c6ca009024000301078820801a00000b1110b07042c4800f141c55200008010304192444c140004001c1c020107002c0c030302980205201509540f40039001c0e6a01c060741541d5100c0950720b80c48002c2c6c1001e000903801802c02440b07107614040c1034441e01402e90402c4111100c440301d5610703810150041d142030030034501414030044c01c07a0f1416600082c10910450303a001179412050f40c0340015100c078038030700c60001c0264a400e1010881c20304520300310503160780260410121100703205540c2c2107582c003144000200c0d44065040c84410704c411060300d005080040001c20018448510900e5812514801103101e456664006010000d65802c07d14400c40098120f890340004014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 696073165 1250 696071915 696071939
    0x301090f06032315090309040e0f030310030b0105010503011d04111210061203020a12020c1305090f15060415090204090605100c030f0f0c150516020714010c050a0c 72
    0x4280551044030624110f1107080044c0e0380c01600940300841c07400c548441031001801034101a5545400f5050440c0d405850500003584942c2822400200c4d0a00350b16110328005010b13084141005020710041c8040c0c1c000070782044052110003003040195031036142040061020243d083c0e0400180c10368264207400009480d003031034034000d000b400616200c0301000c3c001c0260110242c01603004600140c0030550f00000c1c400340318058410394001145150101d5440c1007038143c200c1d90603556408100c611081408280450b040300000360015103011003a80140f004044c01c4c65200f26610740d0078031100c03061803000c0001403050742003d54561f43d5606402c40200358900c5001e0141001c5150f8850b0380307209954419001e0382c03544038011880b2612504941c0207030080c035140c080c40112003801010a020070302c10f9081c000c1c04440840c603403a156040101c2821944c01c40f106642c496482030100c4108580300078501c40c03080c42c09101605031421302e40c2c644040d62402800b5800e46660108650780011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 696074415 1250 696073165 696073223
    0x2030a0605041b0323120d050c0c240c031b0c031c09031403041e022716093002120601030b0c2703070f14090a110301090f0603 56
    0x200d848600700b4100d02c5d45e4031808a100c00c1a540c1904000c8008039074071710341c000e5420540c1204d00e42d040c8145000300e189045c01c003808200348160a14910705410300d00d4070b00c0e141d00000340780ae45c07411400c1c0080350740c10b0a40100b00b01c4512120204a43c0c06204041043c0c03205280210b161014441072540907000401e14020107500007254038601041c00380030002168082e030b5201c074500d600041c0007041c040305a14001d504907403002c80c203151690114030925610840c0d0300203001031003030b900f40042e14010000b20201d1200c1480a100800c1009007811400e1140c1e080000c11800140224040002c40d000c0325075070000d60090103013040c107414036000203503c1d040e01d00c07606051a60382c40781d101e407400318001c0e41005900c1c41d103040121290b04a40c0b010000440c140075023101e2026889074003100e498070150708014205104140300d07103010316010300310b260000801e00040101c0c80619a14a203144014042c1520035038403006940401c00c0705900180c011074020383d4414400044a28404001c0d1400b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 696075665 1250 696074415 696074453
    0x101d0a0f050d030605031203041502040e0702010b1903110d0c081b03120403020d030309050f01020702090604050601140c070806070e131a211b01110a02030a0605041b03 74
    0x451990501c43d0180c400c0d0000d03900c00500404803400103490000d81c41d0700c0108200c40900c0080200e80c00018280080c0026000030705c9100d2591415100082c00c4a11254500e8030642041004a0001d4500b0b48241c050304e80240182e0000c840e5040850050249035070010200c4100c80d40020368030324081650900f601c2c1040030a0700340d02406003010390702d00c0721003100440c51004001c200300500c0c0c41c091624605109080116a20b001a202d16043c00c4040442103041d0750006503030f404615201c240654071000845080100d41010400240900d21114489002c1900001e0200351003e040052000030702c025812221640350803000184424220882c14ac05000c0c0101c24900321106409950000903e00041411042c0b1210401c0a404085085040c07900042c680c0d030f0074020800e000b03a03601000264402a103400d54400010100203542d0301150060700140003202c011703074010854817a4542c101c503005c241381d150b5007007001c81074030300702907091807500058000410401400c4039500c110043c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 696076915 1250 696075665 696075673
    0xd0203070512030910091d091f051005180115020a08070c050112051902130f090515030a030c021512040311011b0804080d0b1e1504030302101d0a0f05 66
    0x5005d0a81d403802981c01051034885401c01581107010401c025141e020f01501e003141d52224481e911072194452100e000789400c0d80392010400e0580c95503109400038041520516203110b0015110001e141c0c06020f03c044015150a1481016200308a154440e6801481603950754006242c10303598080c1038440c460210380843c008000782d00291080c40e10940c80c150420401506d801002d10081d800240100d44031801c104000c01e0b08000d84407198041c0c211548001818202210442d110344a0b01024500c250b001500450000707503c50300c000340d8664151501d15003a1401c0c14049894010050301460040e001c03010030050603031000da180600354000f0001c10443c0ca80e001c00345500160141200c010070300d0702c0040f0300018102030040c03104104040300024074100780c6000841310300d01040480c40488812004d0b602c50300c3c1030306141e0204006844000e10b810301d16a8082d40b112038000c030f64590a5590880da031040c40000b50070600384601c20003070b03032550b0b0303003031b00d011046000c510b001943e041c40303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 696078165 1250 696076915 696076939
    0x9060c0b04020a0e0c0913020f2a070801021b1c030c030b041b080702010b030d0806030106091814070e07030b0d050d0f0809070302010801030f03030e010218011d0f0d02030705120309 80
    0x45d1920884007451448880c050ad0b0682c0c440c100b20b001c0c90b0b400036403201d00c0340c800603050450005101d07850141c07a403480056a100c01251707510200080d0640c0105080d00841c1180045500b103100440780c14075941004600d0f000c03021000d800614105480c16007085c1012100c2c5075412500a01640150075612100350301d40b50004100e00b01d480c2101d41a426034072098034600c009c1d0188088592000c002000810307910b84588043c010307640301031160382e60301d0f40902600e820000030140244501e0f030311038000d0007164641601e115500c08054070050516a03074002c031410a803191103c0250742600b01080340c031802030405000300031410860303102d070004485c5804504001c0c404a182c8013100e0b0140d45441c802e03400c50325034400c00310340404103c1c145641c036540107401040031300160036018040c001d0340c21011303060340015060b48812142c0309030b802005e02101c122982c84c0c0c0c500c140c0251068801741d000c01a548044ad140c00724a802c0076510110696200400842c0040184072080d001c0d83d0503d00071b1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 696079415 1250 696078165 696078199
    0x41a160602030703051e0a0b030f07090b010f080f0114130903090609050a0e040b190c0509010909050f0a0b030307050709061a031501260a060f0609060c0b04020a0e0c09 74
    0x30301c410581e42e4803103421b080454000403a54102d13988805009058400c0b070140d07184102e00c0c0000c541c0c07110b907a19403034003610841c1d5038201602d16900811814036003003501d0a464211003910301401420440d826541c10900e280d203849400b49060002010108810202420040c014441d00c1c0720701e4001507030f95030000c02c00342455040a0200c41d441d003040d0b6866180d80d030300d5010710300008161050007100b07003c43c1181040381c0e0007170740088d444030744619966007804000180007000e1a0848030030756040c50140314120162000440e84082e8407140007d0340350700c4800007802c500c903503240030345203101e2014041004004c1d43d00c035408444000c0e6180406034a10844941280030464038a102c40351000c001041550041c17040d5011041d400d4030041652190f000e0380b908102c8140e07083c05402e95252801d118091034017000001422311400c2c042415403904100401f21098a800102551b614802180031510741114150290610500707240c41c624014036802d0054120b0031030148515200000b00102e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 696080665 1250 696079415 696079441
    0x30c1a010558081e031e09031c0b0a060e03030d0b06131212140405060d020412031706091e07171e06030c06041a16060203070305 57
    0x10500c050142030b10042c503081d400c0c07140390a50b6010200c030700082a69a00d2007140746203660b514400e40b00252941c1240c0301c0072010310300b0201004003491081052003054030000b18020400308914a04800507919401e41d2801c6010702c40c01105c1c1000ca000c1d2a10550517140c011604540c000d072440d017141551402c0440d01c21440c01000c0360160010010110003004980162031245000b03040189010742c0c0e031005440301c214691240030303022043d1a282003001120044180307034295510701080359410b0508400c1d440d114520070207104213400112a4450407c80e01030f078000300740703010040c504042d0a0801a0020246000c291010700041c00010580c0c908408070b940201b0380c2c40702200e07207401040f0164140050142c904000c2c0122080180c070088404840c0030312a40801c1030612440c0070240400040620103044584240c012440f0040c240c1c40d00c0342076030100e61706020401000300d00c400a10320684540200142c98035100301c400c3e814881c403900154000e5143c0c1c0c0c1c1c1004280e07100240c42d942 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 696081915 1250 696080665 696080719
    0x310170d09051e060f09040e0c060301090c120504051e030a0504061103070b0c0904060b04052b0b0405060403080f091f15080a0c05030f0a020d030c1a0105 68
    0x81441c01d001404503080c010200150030b000181d0b48000c1e650090006640390304070007a0a030920100145010303150525002d0110320b88103140041007001c0c041c4000400030300050088a26240d0b032501c902c0290340c4501100c402e240e0315241d0800950401d82007581c4c980402c07141a0403042e00b0200b050240c1c210020884011024907a40c260a1504120b42254020301c1c807500420300303100601a4001040250100383c0c0a0640554195a40d5005005000540d186035000000c0100305100070401c68071207100c1480f040450561124074800d03a81a1070710f40c011503a001811140d1045c0801c020442d0014000f4041c600a4492030810764450b00024094141142c3c040c0c0d00b81c100080040b900c00b909002c42d40c81840f10700c808510700b14070754566586200310382e0000300258032511100d0240010400444e01500041e406480620f0310a074580742e403030f40c401400a0180d5411804441031501c601d444140c0345900040301e81d003c41c080416180f84c48000c3c010184544d80f42403460207040d403c1b02100705 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 696083165 1250 696081915 696081917
    0x3110a0801060c020406091a03070f0b090d021f0f030f0603020d141e0c040c050a0c08090328030810080703030e1f11010614060403080c01110310170d 66
    0x40d60360b08140c400c07140c009a040c022038010784c40f4000450b6505a50050401800b034129034101c11f20f004808240c6000c0e2645d00c54040c140034408248661040c1c4021200191400e60b00107140c032007188040b8065041d1440041c01601e40280c1407000f09501c15181c0d0318483c4071359410300200c01c100c0b9404040b5070300341c80700a6100f440044228000b50321103440600c1e128a00096560318042c00c0130030002b0005416a41c0400e400100c03e0000314981071140340c043c0500d07450043c0c10040b004030050310b618507030312026121620104158039981d804010306048202018400060072818058504081d0b41c212002c40104180c2000500e000440c00c039414101c0362200d0050019500d1030314240e420001c111006500710b501c1840344865106403800e41c81e4603d40a80d45c0c00c0401c1140e00c1541e003104ca054100014603200b0b840f0310400750b61900140c03801c1d680c020300d003243d840d190b0150b01401032048060b0204202e001008010740c40c146201e0076801c03101b01c10340302d514004858541036101c0642041c000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 696084415 1250 696083165 696083177
    0x72705010e04020405040204090204110c07080c0616080d1107050d0f080c16140a2609060d0b0d0b0106020f060402130c09090e060709080c0a050603070311130603110a 73
    0xb41c00342c0f521760021034100c0e00150000a801d0110740102d003e603800e40b1343c40d50a103000014410210402000084003c00798038000d07040c2c1188000004a59109000a400d02c24403d12002803e01c030300720044611521151720204049480840c2c502c5031600101d0068841707029418480740da040c0540c0c039070801030183c2d940d007407510b40e100c41118615402124000e40d5013104003800500048444c0d0b00514025204002080b6080f010b00d00000703103055007100d400e10303080120184898608028140c4070745440887d26191034442c010b4140c40240280f11030103a000c03810800020602c003c2150305410307208158241d071a8000301140c0300b0740c0e48038140c8000f908048040542e424216031341d4448204100d161030422030340c1e962040070a080e08d5802400040c01d800110038071065a40000e03818009041c004081c0141000100004040c54524440c85029890000000d0040d901ca64880307840751441507000c43d21844070451a4142018a0052602091405c0d45107400004070b80305a0303000c066560307182 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 696085665 1250 696084415 696084421
    0x140906010b13050a030b0603012306131404030c020f040209010504092703051801111f0b040c09050f0105041203030b1c0f0b0703020a0e041d072705010e 67
    0x140c52560209948050046501030082211382d18481200002c6025503210082030514004044c211045402c4201600c803402040c1034070082001081780c1c0c04082101c0c0e103090100131248110203060300082550704001e03e1000c102c10140c0020903411141e00940751030044c8881d4000b031000300d01c10f0820b460302050f01400204a0307241c064101c141640394006001040004090890700314040c0c0301412404120b02086144a0380e4200070380748116002443d00b03060311650701030490f032030344991a20382041c000319148000c608003076500b20b43c41d0040c016004101c103101d02800107017185003034014580b0440107a045d032240c03584282d0544055820000d401c903048045594150000e042e00c203e800d40010505401007900019000700a4100e402003140b40005c0c4200e181400412800900e0318091510500441d1440c3d036000740030f0100e14409860000c0c3c0c3d04907a00d1a05140c43c0002100c0c1218800c2c903201089929542d40403154000603550804241100c01e071070703241618000d005596000100e4000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 696086915 1250 696085665 696085679
    0x5030c060d0e0303040308190507140702010c02131a0604140d03021f0504030e0103051611100606020c03060a0903020a061d0604140d030b150304080408030301060801050414090601 79
    0x4118030404001e00080140c02181c41500f1500111410780108102c02c080140c8149024642203070005403180800c514030f0540005071903100d10040c05008001c3c00b2522000316400f84840301d842c00c1e0000d1404404040d0b03240e00c1c40140c0301000300c400455814107002c4134141088030540c0d0641d0400e0500700c040d007680205100e403030f040f041c0c0258114450030601590000d02c018900c4000f403451203003c195450141400f4110446407441c042c1014a0441000600a850307816904070410514140b00303110010030007146030900852060030341500c4c1100c00210160000341303d5038402000d40c151f030203e94a161b402d608894100e8400780c00341c1c0103020344d903002070000e038081c4030580c000003046c41c0c81c403c00070402c0380b80072000c40741200d2410034410302d06c40501c82004a2000b802040c81d06008050480300800c0c0e1300c2d500880101207540c030104c049410803c052051b01c01030412035044a48a40c0e40d0800142405401c2c03091314010fa18022850700804400d11040d031040c0c0e00a802854141d03e0441 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 696088165 1250 696086915 696086917
    0x8120c0a1209050d050f0415091a070c030b0601021518010e0f0307030f050d091101020132060402120f013b0c0c01020f04090609050601090303320c1605030c06 70
    0x41c040440c204104004200c0e10000215904024840d81e500743c0052b04210302c143e15800d145115202d000401d124840001d640e584644095a0340404012941c2d16a200143c0c50440c504002c1e10b00e200d690800c1091000d1203207203880427904054003d00046944010a9868495406440065400420500000c0381c007449080855490301e150031454110405402030842e403010030120365076000040006038a60342400f4900c1d50341d9849104081f00700d81240044c1280c40b035094074060420080c00050b007107944560588140d000d4601d0382085a00e40030020802c800024051b202074910841c5114a045c416070541d580001609502d803407001000d0301c040068504000e1040126900400440040710300c01e00152401400d00f0400326150307420480c8002c00d0300c000f5006840740c90710f02001c20001c0d80e884440c7c0d800700e0350182030482c1c03400e02400203803d691b440c0000110340240205145961034408000a0003269401000c0d1404030b8032200c1e0a14003440ca03403103800d03450390100c200c0d000b481c68100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 696089415 1250 696088165 696088177
    0x60f12090f0212010e010b090105280b030c0c0601060513030f050705030d030f050109091e0f080a0e041d0717070e070903020a060206040b0c0708120c0a1209050d05 72
    0x114808074100d9040d400a0b265403ca200e100300d080e51500d1040500c1d203403d000d880c4c140c3c042100c102119604100104204d40740d0030410350603841050343d03005900602050400040d1000c8403142e552890b08850344d100c65400902d611907148110400003500510903400e440d52403c0300381030340071064503540b40e1949241c451001500c107805850700008256804101d10b0040300f0064602098150581c1031031022504168400b80243d4101003016000074001c0c40c1c40d104485500788002501d1840d42002d00f03101d42405001002c500d00003070100d100c43e4003c15000b2460004560a10400391040c1c2001100c4101102c110031592104c0c406020591a150404d680d44000d40100c0701c800355600090014a074058514030f002c64401c070000e105500700005040043c1030b103070004040b2420143e480c50250341004000200282c2c0c042854020008080c6c11074562224040c0c01a0b110704001d00003030ba440e4455194000800c051040b080311415503801401034041c1c115024142c801d40443c2e00341d580e50f02c11 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 696090665 1250 696089415 696089423
    0x602060901020a0903060b0609030109030306060f050319020307051c02030103060b0d0c0320030a060603031e08060103020a050d0e0c04052208030c13030b0403030518060402010e0105130311030601060f1209 90
    0x14002712100d40c80900c104004c0d50f000c1d5502094003403030010301500c220901e00c2c080040100400800000c22816591700244000e4490b006940783c1e0344a104841d18000c0c80074010020808641034210f6030482e40185040c1c1e4010390b03040107211078450800c06150144000108100750504080000c0348a141d40c1044140c1ca82c8115141d110314000000e007008018074084032140d40da01e1003413003415030054490080061016000c0c0c4101c00519015000350700040c44541016000601c00c51072a124a040c0c5000c0c8c100e1100500061903501055503ca000c02c82806000301d00d0040000c034139510790361120039101480011018405a2901e511219510007403402c545401c0401441d0120b440c00c140520065009442c0204c807818a450b000701560000f8180f071451202c0a01c956a069002241054216a090030014944501c83c1c005a40501649095a4800d40816030000030701c80c5900034441c2d4030320124103071000c07680c231100c05880d5110361208110000744d01c50a01c0c1c508030441d5011402d103d0007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 696091915 1250 696090665 696090667
    0x80402011b060518010b0604090e03040e0a0c030515100e061905120c120c09040e0d0905120313060809070e040f05010f0b0f010c060e01020406090602060901020a0903060b06 76
    0x8600021121615040c1110b085690714200034200051409104200c49080300070303c2040340f103100103590760080340a460309c00340e502c00d80c952603544c003041180c0003000a204081968604403031120020a1000d4400380403d09000000b02d40420780841d045400c000241220342100340b2202c03c40c0c0001002803c150401001c0184040309500c0a588160260342641c3d05030340d43c144a01c09680c034034400340000103840b0003400040344240000d503449034404420050141c60745100400680900b100e1071084805000e00183c42118030741c450080d0081d510f0680e1100f40c1d10800c0b001c080d0740c03807285400104060800700814440244946034090b0414003001c111010140c4400c1d481e0450712080e181191150041034580041100a000d40d10b0b4404040004010f001000c201040f80000601c08050410180c0c6543d0020040290b21019200c4140760085441b26100d060150007417400b0b004640151084900065022a05000702d450131680b680e00c040200f1300d1030352440045c11031350706c081e82c1c4010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 696093165 1250 696091915 696091937
    0x200301020c01020d090203071d04020d02210f0c180601081b031e090109050c10021e06040317010f1a0c06070e100e0f090a1803020708071203020d08040201 68
    0x2400684902d0704d032031100140c0701206204051510300304e9030144c0003440100c61006154806517010b10b07032007601a500c142c2055400c0c070000b004064034120341c0101421091404070004c1001035000c1d4a803442c1ca049400135a46981089031f0940303010421014030700820001103080d40310340c8550b83c12040d410644500d6414481411909802c125a400514038244854440c4d00a640c1328250b00700b1400e5008218070b10345500d80d20344405160000034080d009150722485c449208200c3c030303074500030f103130644258402141a2140d150841640d080d0000755a8840c4003034844102c01c2000d04036441100c5103080b09180c5050404008204486408646e03c2440050074220085c0302d498402c1443d80c0c0d4401340c0c101c0a5007002a550066400c030b100300501e10310700e8112501c480102c2e00854004a801d502665280c2d1510006400000c03103a025150f014840fa104251700001c545083e0b03840801520308480c0c880e80342d50603240c8041e0f40030707005a0150341042d250364007402c0c50b290010700600d44802068 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 696094415 1250 696093165 696093187
    0x60a09021801030803060406050a050315040201050d02070c091113060e040212090321060d1509021008090f0a0b010605130e090717010204031106030c0d0c030902040b010c20030102 79
    0x39000342e2044d40c5590001003080080d01d00340c440c40e0080c0034122000d00300b860034030000ca5600c802060094141d10303420303030110f01135a000e5015039030300e01c45450041d50388441910380124901e01c14801c0c02d81090a02402080e0001140180da942101c456001702da403501e003c508850100c1e04801c196042a4204801650304074040301c954031030302048e0015680e8982086640780c200816540d40d00345030008500344082640c41510b40300d4020703044220b0b980d002031040031440040141200003503025030b0030b5000704021030300034030900d105500171019100d4030016042032545901441000400168000005002c2c44e40104064070181b0b516203104d800380d41d1920b5a00003444000d8a48040355806400c08000f003400e0400400d1142e8000300080d428145165030324800c074284402c0d00c520031000440003660b103100c910b09841c070a1090510602c09000b0b4001c0c0500285900303041031340079a042880c0455154050f0f1045910740e41c0c041f100e8041000301401038003c0b80c110018140d4555001c004a442d44 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 696095665 1250 696094415 696094459
    0x402091f140a0f11120d1a1314010e070e01120e010e060a1d0a1e05060c03010e07030902030d030f1808040801050601080c12040c170f01050601030e060a0902 69
    0x10b034000d6102c58403540c142030805405000e102660568a0384641c8140b080d81c4c1043c4152141c44240c500049000040f80114100e81d4200c00501500180180f226440440c51a084229040b4031084d0300d26151740c9640c00001507060449036440401c3d04e40c48210781d154811034030121400c202d190009010103040f01128255000d0301c0c54000c80c0e0b80902c0c20302202c8210740c49518441728454401c0d007200d4400400c010b850381c05c0941e000d000d44685200c03011042280ca240840190350280075140c0300c1c0351a844080b00c41e00207000e0074003070040070b0000a580c1c901921880c0e000340c0c2c004004040701419802c0442c058a030780003408010030748a03a168004100b403d003146581d10305c680b01407502c80e424404401d08464004000d141007040760800e1241032005c0d501241c1e080203012842049a56075428034030556006940152070524810200624180c1f0104401d10000b607000028003040d101d680044003035912140071618550001d00200d002d894035a8080307100c60388041c0a109500070030700190402 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 696096915 1250 696095665 696095677
    0x1080c0d090303060e37020f0301060504060914012c0310050f0a05100306050417210a050105060f0d091e0302070b03070518040b060c0106080c0402091f14 68
    0x209403500340174842a0142c0340d99a5101c0e02842c50024a900b41026000180c028041a41d84403201c02c040110300300d40b03580446d044003100c40d00e010703541c0d6500d68000744654890f124010008140780303008680c03588420703c26000000140d480003188000740242030048100c4d0324900c8200c2d10342c03408440c500e45007402801c105900803000000d29180c50a400d0401d0780e0010503400c0c409151000708030011800c40d51b084140c80d0403000c0012655280d00d041030300e940f243d0090125418001c5030400e04038000c0740520b41048001018440c03e51241c03440e440c16500300b0301910f40d2009091040800c850303507880103800962224140480e0b00082522191004800101344440c48040400e409040c1601040180c0081642d10005451440d1062000741503004102000007200400003041e070b090f50701d0f50002000301d04010107060f55000130002850090105204035012809419003044070751501d842600c08054000e011001c40e00c1c462420f02000900c584550382c1801802507034203076280f4083c000707402 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 696098165 1250 696096915 696096917
    0x1b06010906090b030f120a0302130b03010303030e0c0609040207081c06030203070f0302100806030c15130504020711040903180b0304110301050720190b0106180303050901080c0d0903 80
    0x180281c2822482c00a994070001070601a50040c10f050007040e00000c1c14481d0001701120007901d4141c42c0782e00310302910442c2d00c81e21454110110215880111400550413032b4442e44042210219403081144c598a031a81d1550780880180b241140c141415001000501c1c4079217007451802c8040c85414514012800501881c140d84040501c214141044250068468091100801860b43e400168440d403044a002e08201a61010442c04e03101000b0100c1d45800c000c129540000e460603106120703401c481f6a01c900404406400242c0b81400e00c2242c81090b04260303984242003401c0144000707072808460480411680070001e00304480c098000c0701c007500e441c00c5d01e86c4d62400c150070400f401d018881c00c0244286d2614050058444d0482080d01c03140d9030340703001c0c0040d0b9040e01d0515802c0c200308001c0c0c0c240c04c05040300c414041090750a00d42d0305980c020303181c1065030014824424074925030b5010080105404026915280d8018404541e2050360f9038440342c60513000002c0002540c10144040b8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 696099415 1250 696098165 696098171
    0x9060e030d11121308040510020c01021e03121b0c0d080705041202040c0224010f0e06030601090f0615030209040c1110180807200301201b060109 64
    0xc41c61080300c2c003946046807025412541800e07401e42d4148101c50340500307200200c0300e104207244200038051041e41d000f0200104200714400000c54060740b2001c0200c032183c0107004640300d550958500c003400c41c0c449044440110304224002446002002016107051000039400d00da142440118000800f84814180003a0955011886004e002c4003c0070303024006110091000b48040c0542d100380c07080070b5404903004a0f0300e156140b0103070b052445240c03001041c101420381001c00c00114800c0c003030403551a560391541310703503a50781d0101c640c50081c0d6100d42d00d81c01c4480104404805a008120340c1018a80c0000e030269448910618805d98004a0400300340c0101e24203031945094880c210708240503042503e141070312407240a854100c4900d09441c91a82c6041200502c140003070f100c1c51043e80820025900c40c3c90b810810001c100040c084445004101d043e041d080c10180111400030705483c5105c80040c07258181441d1941208030042c04400310b00402c0c90840208003c0e60b4000e1182607400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 696100665 1250 696099415 696099427
    0x1c1b3c050703170622060b180906031c121401170d091401051303080c1c170f060315041110030b0607080a0c0804080d08060f0307031509060e03 63
    0x1900711026a40c015050480f184200710003900e41c404650803820340108060040314046a0401c01002c4a4000610f0340e20042081240c618464054240c502c2c02110701803501d50300e500c02c06542e007503c800c3d141c0c07280e45000014158140981580200c040e1000307004241c0c0786811860711244103099004000041c0d400e540080041400d0121564079aa1450401d0f4140d041c818002507000f080d000182c10070800090107030701c0007a82d14a110155903c001d81c90354810682840a44d01c02c04042400104845900703c0d0301e15900959050703140c50200c440112003550380f00007004c0300d01802040c0a4260051845144004507406038192080c0c4c4500c1e011b124120303200c0d09010722003501c90a510706061034200c581043d40c0d03c00c000e94038825070000031720f0b5540303d2004c3c0468100400c4800106452004100480c0c00e010115800201e40e98694504003140d41350780401100310100d02c141e0b50190050401440850f07402000200704196540b0041100000780d694102120080700c00f02c1c10075000807840c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 696101915 1250 696100665 696100667
    0xe010902040b040c0207062f0109120512150109030b040606080c0a03080f0f040f03152307030c02013305060403170309121c1b3c050703 60
    0x81d01034094801e43d420840c4e45030a1070b01940c0c4196074051501070244490107030b140030603000c01001100c000c20001c0f80507024032198a034007a00a890003103881e1004660246012407080003610302c600d18060700c0c0400703511041c031499698100b2940751410001d5504000c400315012402c02d600a6108400000380186400070042c10981c01c50031043c8100d00e4850108040348090090f141c2451140499558900d10300b40c0c4544035114a03440b0242e80b100010001090044407854454078082c0e41c44140100d41c00c3d1100600004a00141c0a422005071004078004130300c2a80001c1d249401400000f0f04124481ca42d944443d50103261b82421342900303112000f400003c140d445000b0701058035510700b054255904c0d1a41540c00c9002040d400c90f000c40094501d103c1006820b150300485000b8650312001500b00d00e400b224403400c0040076030b0030035803c8021210240da00d50003141207544c4014400003100a0520402c0d0401c91094030390900c103070800c075007040165064a201109480713442c1c0d03800310703490 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 696103165 1250 696101915 696101921
    0x50114070810060f02101a090903130b09010504090f06090203010b04050411030c070f030504030813050906010e030607030c030603080313030807020303131101051c0203063a150e01090204 82
    0xc02010400c9001c4c0064810340c0010f00f020a9160041000c40c0c040d081d401d8590004000d07944166100701078000388420140044020300903001d044044039903241c1c0b41e4403600700d284290710f84035000440810041101c4a242c3c1c2c8003132503500c041040802c950b541c80d00c1c2170f0182d030000c1c1c01c402000c14001801b00f19078502031140031003503189030394451706518050011407440c1c0652070340070b4451403899544e002010f12400c2100c000d0355000c050240c43e29030b280d0f00800003c200d40034140c090040c240c0400c100e036004d4800c00000e4034000740108016501c80d0000c401510b90a25543c0916407510303030100000b40c2100285204082000c402c4803014002e00340100f640d4009000102550420402d2000e85038203441c0d00e515060308011201c0d00040d103040121001d1040110b1000b01c48400104051304035020b40045008502c216401200c800c586400402032065030320084e90313110b840c0302248800103070084044160a0160b660b03001061303410301700d6800f0748140d82e0800c84140d664081c07120840c0b410344 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 696104415 1250 696103165 696103169
    0xb070521090103141e1806070509010f170a020c1e060a060f082e020a08090f121902030705030c010609051608150a090c090e0114030712050114070810 66
    0x30000d80c030382e04040e4819200c80443d44920034100f102070b000540211000d41c6c240e0381c2d54165104603003040c54a142d000340944c0120041a00145144901d00e018902c1065000948412084154502c2c3c444185c01d030000c2d80b00582c060703424003e81840351019410684041d4108002c0c10250082c3c0c035005040c14110b44c05034010b6a50f04500907010300c20410006500c0760402d02c0ca545843c006200c00d007004131b18440c01c070440038100340000382c410016079002503403d000e0b09402003250455281c0c115640c1c0c60740006656204c0c0140309124403039500c414040c161002401a0051301d26140550700e406085a1129a00e40880c0e9110a001c00000c1054450294490070301048044049039000c402000d03420007500c040c52440480390a200d4030750301c13941018002d000d0010708001c4155145409011003034540300711466550354000000390b2102e10700450f80040d500401901405c0c0c01c2c2001982d800382500401e0b04d01c0e65035005041280120110514042c0046448408203490900c44500440340b41e9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 696105665 1250 696104415 696104441
    0x10f09050a06050901060f0b1206040b010f1b0b01030b07120c08070309020118090b030609160302092503060528140303070602030c0715060f0b070521090103 69
    0x450400404035102081e4210910780c4100d001c159511409106400340110307030408400c0814040b400034031805444010005414103443c48200c1c5c4c0d403580c08100481d60600d20550200304c0840034099a01d10414010100d0070780141d441418102a850b01030342c0c00c000b6001100c200300100148006a500020908841840c1d0001448002c400303040c0208145806420041450b40740c2ca402c004580c021b9041300d10f9103428a480c80200c0381d40304110f1010301002c802d045d000740a0100411108800441c03064224500d2464012241c0d00d15402c0c0a541d04009200c041d6041c0340200e980396800c00088183d0a00c030080d60042905800d18040105100ca03000d04400044500c16007081991248000d0004603000007404030b086003104001f2900310b00c10601c00030080c910010800003100d9000000c3e04005002e00001c4260200b42002e0340e085400600860504a88a6600700903204d1804014070740d0700d12690554141154a00316aa0322001d640e81c20164404007080042095925100e054415110307 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 696106915 1250 696105665 696105671
    0x2060c03060a14120111090a0f05060304020609060f0c0d260a0c0207080111030711070806150a170604061523030c061201230105091e21010f 62
    0x4000d0000c0d820090610401c01c10803d510043d032016900c9002c04194103040344000e0206d140d640130303002c965030b100d04200c61107848400008103140070311203440815100c02030031a510350345a07a003c1000903004502c2d403580c030040402907050840c00001c00f41c10301c104144000c203202911301030064502901040c590207041d1284804428220300d602c190b80e0040c881c0040000e40614442e0101d0402c40c480c0c000450030b44c20000500004041107004500c244c2c000d50f1265100248100240d841b2641d0b0302c109003050b4030500100f16040100c408442814600411080c003542d9620f40000d02c2400894440100380c200740100401d000a07802002150210107001804e01424561152941d12045104588020841d600140d80391005c22030440304400007003410391180b5600780d50f2450000c4c03d0081c3c00c0200e0b43c031100000e40d55540a16520599030507103a003414001c41c802840202014030815050455105802d0707160303a240e020100e60005010300341c0c01070034241100101c1c2502c0034201d440c2e4010b49 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 696108165 1250 696106915 696106921
    0x1009030503060d17070b01090509010e0a120e0a08150c0307090b2101080d020d05070f0206031902031807120305070f0312050c09190b04050f01020f0d0f02060c03 71
    0xd8068200e0782c0c00042103810511031403090804001e10742c0c1c4e03805035954032003000404905010821001da812a000300760240800d941c1c03801c216081c0d62070030305444006d520042180000070f90220410369400624a03004007110401c1000500c662519407060400b42c02410000304d00c4030a808443e5808941d2030481c5180d800c0c1100010410310303803071055010450010602c16800c803082d40c1d00311101640d800e038203075455840d980b02d20b840c0d074208100d08000d0300c5801c40009060703004006843e00e054021010321070b80802d68081c08003550004015009030803d00040007140031051010b14003c03161040c1c0ca511104c80050058030317107009500082d03000c001c0482000002a40902211800c40c2c0c400d030009640348a929050360062184510007680604103020030801c2c221010160403100b108580341e80300420349210f00d42c00d001e440d00400040d048100018021410b00801300a805c0038107204840c10030340d0f850340d9907040c06c154001e800300013141d07030790008410307941040b03002d80013080c09052600d181 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 696109415 1250 696108165 696108167
    0x20c1e0606120705011b05060405060619030b070503061906031a040203010b311203120e0604031d060708030402090108240411130c020d0203041406070204110d090302100903 76
    0xc3c03114402c85040080541c2e49101004401c0c0c4a40030132a4058110b0742ea905143c038103141c403018101e0784079002e601d850f5075030200101001840d40031640c1142012038036480d10381c400c442035131009101079006084a9580e04003040e00c801220b0081c2042e60303000980e07070712100b2410101c101144416104178010320040c00b49211020844e40d82c40c440c012828040389801c50a0fa0425071b100e41c4103102c02604080001c0e50304c031800c01102c02d41e4030079030702c40380305602c000c40a0085550041200f140d9074080030000300001d0141c90940c4806a01050034145040c040c000100c141c0e118200c111a50200072051000b142040b95146002d4290580901503400c2030250154440200740c2558400c12030a40216040c4441d04805106004c00501520200841c500301c51000e8492800190014031071404081407091020007a942559000c070180002d4500400410115402000c81039074091303a03428540b004c81c0603500080a52503206080403030b0058941c2030181c144001d1601c44520300b81042c00d00000a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 696110665 1250 696109415 696109423
    0x121406070e0f0f010c05070312080703050915070201110a0518120307060207020a0317071109011a0c120406021b030a0312020a03060302060d02041a09150d020c1e060612 74
    0xf9204800d044076200d004854403c1c1104014006016008004c0f043c4080d10034086000d8005440e003405549410908030100e0308101d50100c4141c2119460a00d05000a14203d801104910022a11044e203071680030096006003a4040030850008680e50b4641e445d42c040b81c0203203011070300e100705401c00344580340e00c07489841c00040035542c0c00500d030310440d0b603000b0040c4060b60300105c0862811070111800340c0242e100c4034060302c0c0001c0600c10980c0501e05011140c1c140c4005d4104007900d07103100c84210302ca5421120b504000b078065912506000402c180183c0f000300100c2d401480503607036041840d4410303004210041c0c0030360080000f07800440d411008030001242d100c8130040ea50840704504500404041e00020741c00040028420b5030784034250090800c0c0e41c103107001c1c07020482e4a040b0310f6000344039182079290441c541c411414807000e048405001e483d40c115201511b03001c86031045504115030a410384c1044107600107407440340c8004004081d409a000d640100c0d410081280b10380c1c1c1d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 696111915 1250 696110665 696110689
    0x126060709050d06090c0e06040e070332010e0d0f0219031103120a0e010c020c130e12040b0a09050609130e070905040609020906090f0103021504121406070e 69
    0x1942e41510384004c200540c1d001c5200c658000d4800104c03140c0f075801c100006541a202e0511075400c080c21403501e1980403c81004499100c941d04488160301c4d480b02c001d83c00490320700b450005004006954401e001e006402c480d24440001d040724414041000d000401e40320143c0d000c5610500301d041e444002044034102d0290942400c0040c400340c00c036005d06e1881040c0304d0b0b46092007043d0a015001103142c019445180c200c2b40288491030700c200003243d0b079458030759059520244143c1c4030789408003250300c00001c000d03d52044c0c520820709005080c0f000c0d071042c1e004010190f40003d00d000c44a601800d400c0203446d0403150a40340541d12400201c81820700c3c0526820365640d00c08013085c900040007044001c06030784130144403e2600d824081c4c004c00e0b84090690051500030001120741c503241c40381600c600316050003081c440e400c40d02480b00b0003500c50000c155104007040007103052a54201040070f41d1f44500520003180c204070221340e050450241908040c461108030641c035075a40e102c0e600720 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 696113165 1250 696111915 696111919
    0x150c030c08041212022a12090102100908121f0f03120f030f0903031a0306060109030803070309141c021609050907090c0f18031e03030b09012606070905 67
    0x10426280581c071364000d00c92009500e500707406a0800140c40c0c0e0501102c0d101820684003034078000c0500030804d5889100f0541181e0068215140b00e01d10345085a00c02c40c04103001d00c0c109410300d40f11000b10b00d424030040da0f0441c180d0315003101c49003203080707000f1516020b031a240118034070481c519922001c080d40c0c0101503500340308225a100b10182c2c402d603c034032182c03420b0480a0080e4081801c014009110350b18a6112025400284548900b0002800741c0104c0301a500c4003a105c1c511784824200d40c00181c0440101501d41c013005003c00c0051030744038841d0408a0141c8184480300400d286215115101017065401546000c075210070716582c0c4a048038812100031550369910f074001405c00b40540c202c45442031520078141019944030030603001542040d1241a018840891040e07202d4095110062160741c201c035004a101000c50000b5803d1886402c02044410103400000c08000007600408444c18201924103207038042c014100c919160b00c80b0203803845003055000100440240c0c01118 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 696114415 1250 696113165 696113177
    0x206010e060d02090a05070c1e061a01050304080a0207050301051816030201020d050714070603150b090303070f0f0f08030610050702030705090415060b03190e0c010e010507150c030c080412 83
    0x340c8010301400c83c01109a9001003500d00801802404080002d05403205680ac0340c0341103c04008003085145a03013400f6416100c0600b1540c960361072071500d500c512100c01c114043d40c50001495202405803900500c490b07000c440c01d107010f59040320715085140c50b01040c452485001000581d80105030416910002d180490760f902c0c01d0300b000ca03c0e168542c00718000c2c51260080000302c2c150f1550003410440740c1c1c904414442c03542c3d255050480c0c051481030300c0d49508200070b6400000c00404a400d5518820b00544000000b03644400d00c002ea08005c090310310410020801410b440c10780801180a110380c240a810041caa8005c603030359004a000d8103024400440210b1300740505001ea943d00010300c0d041c14044252100d24144082c2c2007507400e14452544420701d018442614000c0c0a04503401c80000c0c2188407101c0011182138020f01005814054100709000c08104041c61031482120142004100b041481c1c000404481c10903801604104060060200140004c03040d0381601c1e91602e419 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 696115665 1250 696114415 696114421
    0x61812140f070501090203190c0b18030607020706020106050a0303051608071202010e160e0a2a170a0203091b031c08190606170a060306020a0206010e060d02090a05 72
    0x400541d01c00c0c0010810707040c00202e0302c07008000d01508a040d41500c02e405031070007000c030001400380f09000107000414580c00c074141484120309a601500b6000c1058002c200d01e140d80c1404030b820240b065400f5001600619018464550240510401420143c03260402c051454400030140e0041e0f04103007610400c0406c255061050311000c0d00d0b2442e1b0841c0c02c401c01c00110903406402410314201e4128103024102010100c2d1030b010080c2e0080f0340040220a025680f00b25420000b411030000c5014480d0ba94403400429004605001d03001000035100e061070003404100c940c0e10404014250011240100200004000d0101d0314684c0c5940d44044462006400c100007400c01c4150489042540060010744025a80c080140ba00605039203c00d40048188500d9040070b1315083d0091402048001140200101c80000034aa0014405000145007078507070b40c61009a902c43c65402006900520040c022076082c03141041e00024210b030b0001121000741c1c0800c002c104020b0025038803e40d40d40c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 696116915 1250 696115665 696115697
    0xb10062c0406030c0f0e091903031d030406020d0e09101203020304180617012a170a290d0f02180f01150206090c06070804030816061812 60
    0xd5006541d010001308105074581325141c1d550303159881002080402d000c040317124540c022804074840c03090900e603a8480310480c1c400340c0c003520480d09429840f035101010441403c006201401c050600c42e4090310b040b0040c0d40005203600d03108002d036840341801c0e0081c082c0600e101c03100d413421680140400ca000a410313080980c15806a86e000610171a200900c1c54050301d00e40c3c1c0b1940642c1e071142072800400c40308018940c221031182c0300c2c0c00b0b00301c6400d02002d800090b00010040c4085214580b43e20b00103504154481241c1040d10007014440c2c03035405000b0118404843e4000280c02403c2c82000a2a0b102c005640190b507601c0c06031044d284400742030b00399120140c0c40c0380d10241c802803100c0300342442c41c01605a04801d106013507002e28075040741401c1510110307003d401025140c00900040e202c10b010811a98412601100d48a1040100000040d83c0c880074000e01580c44210341c084e030b101c90070180265140d420101a04900a000032000112080c00c40b00c1c41084524003c0200e03035250003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 696118165 1250 696116915 696116921
    0x1801090509190303060303110a0b1f0504020c07080601120503030109050c04260601090209091504090506041406062e0e1503190b01080106030c020a0f0b10062c04 71
    0x10716050042c03030018501092542541003601101d1080d1380e040840c104002c1d00548444020400801213804840850348100340500310810f45404a000c0005aa80d65000941280d000405103c002d801c1701c1401c00543c80280f014500403c0c41500d5009034503801c0d41c42d1912803205006140c20140d840300441d020300c11317071400d40b0054a6401c02a10071404503081d002d900c45500c5131556058800c860004c502100c060003038400d1107001900c11600d41d2151108181509558101aa00a650346660201040040261038012805100034804025117181d0302420201d00030f0488e8010951801e4001c28824602c401010440300d045132081031070708a58003150720303484000d00d5580c800144100a0b501c04e01480095001d11030b194815017004e0313240042030043c1c51403003000383e0104040100410245000e50041081c100d20352050315942c04580d524041c0ca40101d600a554110342c0004000b80c2e46494152007000d4601420000f800702030700c14400c00880b465084400704641040314050454407076030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 696119415 1250 696118165 696118183
    0xb07030b06030112060506101b1b0f080d0f0c02220e010b041a15030403230a0206090708340e1b130302060906070f11040b1801090509 59
    0x7040e4a55a5954102c010400030109105540c61450701d40850301d5460044012441c0d0816500c0c0c1080400740c2a00606080380c00100607180d81142405540300c0c000c01501c50009084100c1a4140d55403c0ca40386910f000384510045c414004001c0c041c8440c0c90304824030f0407110b80d0480f039154000e040c040c115040c030250f613808001d0807800c02c000c242c183c10040d005160740000980d010071448e10182d00d602a50340c000c440d000d800c050390b90030080b80e548020000b1030740f09029040104080d00c1c0003440200302d440c0ba94140901034000301e400e640d02c83e03040c050b6a0300031401c44010061142005500c030b40304c0080b8004100b603400c06551100c1c403400d000c0703400040b900401c5a01c50501d9502c449035600c01074116540800502074240c002020200d0b030003901d00c2854520359212042d4203650a10036141d000010f9540d12030800c0c4140c00004800c0c00c02024001e12800081123590b84c2603041c0300540b0380d1801440d2003800e2040f8010306884045140504450b051b0764080b0702600c548800c2404c009800b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 696120665 1250 696119415 696119419
    0xe0a060504081e04030b040624030f1502130b09272205061b04050d050a020901050604030f020f0d021c0c0e070c030e040e150f070302030903070b07030b 67
    0x301040000703101035a00541010004055001c900a81401e0000507911540c00300a208416032008100442c03407544c041c281c101404c118444100e400362103802d2070f2101d15070007141d50300002d500410810000c1400e030880136550000950408000310003042201d4007a0003200c03400300005c9542c00041d5161590110300000050400800003040c00510382a0b9404580b8140d101e03404c1443c0b0a0002c001003540c13184141c00a000d004a601c407504030103083d4210310040d49074000e081c0070101e02c9507181040384040c01e00c24030080042d07401b94410f02c00840c105900252003168240410000302d5074035003000203d83d90403514003143c20340c0000016218201907402a400400904d00300e07645211000300ba129160154442000e05903842c001d200d40380d901100d4003000200010509400a40155020700d82200010b002141e414407a005251515102d0ac50307003881c2610200a0014407460308000b04d80102882c50258514604a20215030343d109910b001084420614001000b1510a0b401400ca030100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 696121915 1250 696120665 696120671
    0x1081e010f060b090a14090103030318080f0a08070f12111e04140a03030e0904060f0e100612030503010b0c0a0804120b060109060e15130b040f0e070905040e0a06 71
    0x314403c903502c0c0e400c65003034507010f000a0500840c0d000c20000a0020300d03030740181014816801c550b001c43c05801d40310b40c4240c1000c162020800007644083c090b21081082420041d120742803600010560300002d40640103008201c0031210000e41e10540391070760150510404144c080d296554154103206400800256502031451903d000c665400180b0440e203182126100f011208020840300c280544401408100000c0c80740c03205081c180286a0700a0181200041801411880f0010340e47c515222600941003080d41450b400014803805000d00106040020700b4612540c1c058030912040c050302c60328403004121140080c808200450a941c0d00100081d222541c80f0b0f085c656000c02510b0407154980f003500003604179441000d1440031500550741c0d140003e0181c1091240b0340fa242c0c560030f103541c0070800c480991444d031000118001c0c02e15807200c036038941c40d14070b180c0234007209908a0003003010301c41d003440300c070030f50010390602030759011030700000d030302190b45813151910340214802040c183c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 696123165 1250 696121915 696121919
    0x30d0f0c081206130203101401022505010f0908030912031603050d0b0d2409020d0803060111060f22020d03030906050c0412080310030b0a09051501081e010f06 70
    0x1141c100b1401408140c840202c04203801e15042d042c2e02085030014030426598600304182d03031442d1801c2000382e00c10f0050b14400e43c100614414011128911204942d0300c1c268200910f50f4028031041ca802003614081c0e94203420002120f46074031806110034801d01d1822002e00e00c2c0034051003294501003008600c49200032142c60b000c1c0481c0c20001e00c500304149811151105801c15030404403019902200c1c819450080600e04031100d65849030010a8036510005c1e080140c481c1442c0d081c0260040700566102c0c07a08400040a000c5414111042500441e05005414003900c044907081501c00ca2450703c540c1c2e420380108c1d40b05a00c901d01a612800c810442001c2c542c0662010b500d450050005100681d180c10300301c24030b8421441205115104040d03040003040701e85000d15004031040d083c0040840d901c1d220ba1000320021f607500e500c2e0b1560f440f41d01003000b40802452002c0840070712020a50b40c5072150b440c1d100d130441a030b0b6007022244e030760030422414001c0d0720201e0a18940402041565 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 696124415 1250 696123165 696123187
    0xb0f101d070210020405030d120e0d0c060c0c020d08070204021215040e06010b04030f0807050d02060a0509120d0f06051c050c0a0e0103020d0c0b1603021605030d0f0c08 74
    0x5902075400c81d0141c00340e0807440026000c0c0340201c07401c0d100040e00404c0b0400040340111074088540070003601460740c0e06847d106850040c0b14080c100981c0ba900c840810b001414207408644509440b1010300001700305034401038840c00c18402210b074210300742e40e031100050b002081c0684100410100c0340400c1e00104503c680a001c101c42d078203c010f980c1007000411004041d81c3d030728020300520090120a010030400500641045104d10344203401007403d00d1020b507240e0b0f2030108100074010141e00036004001c03c2c0800c9106070750303000e10000d0040034030540072840812a8402e81e43c005c0c103400e881e00400150314809411801c02400d000e0069a07e42030840800c0000b44450b038800c803610b0150340740c1c1c7c0341c40c0e140404841d8180d1f81c4082601804c0d910350303401c00081d415038030070490f84000d1582e00021401e004101510021000002800b5040e010f072500a0400c515030900044c0303000c00320014081030b10001030048080e00c0030700b481003420b60807020544800010280082420000007080700f644 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 696125665 1250 696124415 696124469
    0x5160501140103121404170304050a141509010801060e19030809100905150a020f06010308070c06170609130c0b040e16020d08041109090d12090b0f10 66
    0xf240502d05540341400300d03134070880b5007400c0701c0d00802043d401800306200700010000d042032031403008000c0300c0c941075803000800c00e007032011350200c4100968000c0b0f1071306030700348011a4480191242049458503d0150000e42107036010b0241e041040a146600e40d01603c0b02e41d1070000d03401141d00c00080f03075503607840d048449500021a2a00a190308581c0f8100c040c060101c038030603a0300050031006440300f640c100c452140c000c18850800c600c142c901d40d4041c5030080c04014040c0d8082c800c00c6940e0203450408150703550300d942c0200c0804c1610080c000308004043c1d28940c201008848040c80c3d9140c205800000842412002e4162000040009202008200104212029400020403d07501c0c09003615641c5598a05000940c0040d55481c54031481821055401442210001600c2d8013080100c1e040617012078210f0713040c0d48145041d05504d50406e0003082d20710205c1c007091101c00300541d00c8400784440503010310079400c0e07203001041d02d50100301081d03c00341040880c000c2d41040703c0ba02410700b13 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 696126915 1250 696125665 696125669
    0x60406060302040b012c010306031209030203070b070206070209150312090a090b0a090207030201020d06090f1413110d0503070b0f0906040c1707050a0b0a03140405060403051605011401 81
    0x1240303140c413040383e6055001d64041480408a2141c00c1d0b100d50b200f03c050300c085082002d00705d04241d520390b00400010101601010b0400c403903680c4a61850540c8185441e20309140c01c41d0585010a2009200503595941190b62031903050301c440425407606240700788000700c007807411907160041c5070354240541c0c03501000e001000350031540c8180391561048228100d40707041e11215003100700700000b40035800c40c5030018080e0900c244001454945101508000c85442e80c000c5224180c031001080401400b60142d50240d44e00c80508015509110021036010304004200809500c0d071285d011071580c0c1e404d645041e846030040280c7e50740390306500e01a09406001c9078211b002442480100f490f0f444009185840780f58455800e409036400d10b14541044c0d10580846201c0d4840c424011030291a04442d00d03005010740d6010343d4860381042c401400382c40403500d0b0009103800c00030420000c50000190980c1054160610365500c2c0552040f070302041c40c4009000d80f0b40d600305040382c00a88506103500341 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 696128165 1250 696126915 696126919
    0x21080a02010c0912020102150c090901030f031707050a1407020d0308100902040320191814090a080705031b150705030402100806010e0306090303100b1e030403030e060406060302 78
    0x2031030f9130301e44607806000f070346041001c1e005074082e141240001d0040302d010340c0c010b065401c989091601003000182c000c0d400360030442d203203d0350400c0303070041580003202184420b000343e1810807140380c1755134020310358005d4400010421034a48965480400c9200881d405580c001d03280e08013100307190501030041001a40c8046551a80280005940b0598030075038003070703d600c000001a03040c40304487e42004d015220380c103035100342ea100014440950350b84011000300804150400b00c200889541021100318840c00080300b0808810001c0926011400100c1c00c0d42c001000c1ea00c800040c10800d103140100c50004202001d03221703104052120000d00107285590741c485d0102643d84c7d00f1307070807942400143c1d0300a40000c4c1030002440403d0103880101d5010710189019400941d80e88002850018260741c070400c203800000600040b489050b000c4e60240001c80903d0340f90407440b102c0f40b0646821050004584400030020404052190f08002d480146c0c49084070504d08060818000500b003900c0124 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 696129415 1250 696128165 696128177
    0x31003140a0309061d310f0b010914090a0615030b030d09260f0a0f02180405070603050604150308030f0105040605061605122b021321080a02010c 64
    0x7050f6119080c1c0498056545005200703080000c018032400b5a0296800040c02031b002c404041150076000c2c3d20300080b10b0b1040003241074040140e011080b200081e1105040200b03800b02842441c22803041d100b0486002e440000303441e41c60721001e40052800c2c4c2c00000c0f143e81c03240044044c1d2a07168021850a0b402141901c041d80075000040d0384500441c8120882100503410344400c03c500c410482154101041c1a2450b284201c401c0900342440030000311007010303440c0102015410000050b41d24180410b030740d15000c3c00d094136941c2e0740b07107a030384103a03003c050315040042c41e42e4032940c015850003c0205031501c0d600341c891600703041c01d4008842411031034070322000001c0c05160a00440040b180c0141400746043c418144070000c2810a00c0d003130341d151250040cac0042c0202080d004000e103000500c0315204644090700c0341840311080d1500740c1413490050004040006500440c00115185190011454408034407000c1a140100d08050041135000c40d50701d01032038041d003000c0a1080c081c1c0c2e0781 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 696130665 1250 696129415 696129419
    0xe010b040e130f0305040e2202100905060a053f15032409010b01091a0702090a090213020c1903020c030106080f0c062d0d02030a021215010c0305031003140a0309 71
    0x4026850a002010081064042c48c0c82015090030120f0f05c0c6100c140c2d00c0c0000302d1a03284d0012a00640c0001d23011800540001605a2192200366081c015039402071010141002c074411400d021888000c8403812800030715022604607490709404c403000200c040d05030381c450800030203425400102810256000f0142030001a290703a810320801801800503101d5403211403c006102c081c1308584400100c903a00100440d4016951350200d25104081003100131400f00e50383e205203c01c08002000c44444113005004d81c01c4032101c041046804082801c0d141d01d0458480e080803132400004082c03454041d4a40000490f40c540046003040c0c0f0200b003c0c0c01c0366010354101c010b21045105011001041c3d158000f03520000447c20750340200400d514205503410000f078001a00202c0e0710540700030300203e40c0040d0040b5160310440810381d0080210461160b84c20800b400a050190040c40003030401c00000001010340e52807803040d1000d91741044040075604d00041c00b15603286104102900424101200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 696131915 1250 696130665 696130681
    0x9023d05030604181a07090e0109021902070b071b09020d05010302030f0a02010203250c080d080c090310050a021303050109020a0b0a050a0309030c0803070f08010e010b040e130f0305040e 82
    0x903034604254000340394085c2400e81005e51a040001070304507020040c5a40c00001d4510642c00c915010308030340040182d03904040040440001a0380c81c5060564014203030070800d58051a083d2503142d03410414a00714a4075000140080912139004414036620100380681003001c698403c0b8140e034801d07421a00700d10907034520680c0c1c907080c0d61030090040e8030400c90f20500c01170356090000b141447c041184c014201d90743c0d416141c0c02d09174011990550124bc0358440c51035101d00390382d0300303c11407541842c503212001d00800c1e11742040c410194030302c0f611213011079901d5900782c0c11584034800303041002281c0703501c0b491306030b01a0044400036485403040003800704070b084454080b282010b0309600c40300c0c603050300c009003540505007610040d030070f104540d6003041c0070a041070020340c8038881995078401c2075513a01c000581903c0b0b068105014031240341005220840f0081c04031019a0b5550910450540d00d01030b16105451841e0801060180c4100c3d6604c02c041c0c003d40940305803000c052503500141e030f072152 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 696133165 1250 696131915 696131951
    0x6032a051c05151212040e07180f030b1306110711040c08061e040204031a0907050105041e15020c010807020f0a08030c0c16080c0409023d05030604 65
    0x5450581110100ca0068007490541c0c04005180304d500143c45000d01d08607400001504144d110054070f1340703603500300181551301c0038031056215410071101c0156410134003081450412030100412601549000c42e4a25001c04486102e0365404407041c08040030300c420a100b2a0450a41101c03c070f544081100618a014015484c0d08016540c1d0350149940f40c001700b00f61290603845909032318110344621500383d141c2e800100f001e140500c0c0c80780040721070fa05c85410f004100415a8600381c004200502040c0c0e8000c0c21182110791445d8000e8108400b1086580c5130145540f0044c40602c20000d4440c0c030540105141d06806801d8980e00015965100140d0f1101d00380703404100c068000041c10b500190558018541105501008a0600d9110300050b4070384081c0b00a4000515848101040740510401801040d1b9a081e20305204030f041031303804107503503100c07540032845200c1c0c0b1072007001c507520001182484a01f800c03801402d2181c1546c18081d07c941d0050390407034000c604080d400c00c1e100d11422 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 696134415 1250 696133165 696133171
    0x30513080d03183c03050301050f0d0b15030c03010204080109030e12100c031b1707020d17040212030f090406120807060506010909061d090f060106032a051c05 70
    0x607000581000001c1001ca07a02c0c100080c004d0303480001600e0811307442c9494000d1080d81c3c402d0700c1c2d40e03a495041c1410003401c806808201c071300c2899070301141c0c0006203c3c6001c0607000a40f080306040f00d00200000030b410318a000804541541c800318002a038200150040070043e07010b07441e140421000b860600031070789502d5030511429408410442c03210130301c1d64004a0242e010303180000b0001e0a00c0c1c0244000229800311800013a41c6215a41d106c44142098603007001441c0020702d0030000400d0302911030304010641680260340d40d00054155112001c20145100d1001c054a540740178240300030140c1d401170746074039020354a8004007150f41496034010340303100c60300084040c0c00d14070319aa4040151500500346410031202a000190840345801008050a0382250802e00c0c02c24102c104107441c58010702e86100c80d8846602040301b810302040840c1521010318001c540100511100030204d40c1d034421014004800101e0002059031040180c03290f11980c41402d40d00001035122042a5601a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 696135665 1250 696134415 696134423
    0x60c030518040209060309060601031406012c0405160332040f060c090317042103090b0a0c02011706030c04180501050c090a0801050103150207030513080d0318 70
    0x300312025441d0104885441001c10003030000d8584503e1001042c00b90b0015200c034606a0302080034003409603014012100f0710300244a405c1064a4281c3c0000c2400c2006402d42c00e0084020440c0501051000c6884130501d6000c4c1082c00941424203818241d5103e07140c43e103000900e8081030481c801802814510a0035440014900c0d11000200b0351001c2c40c8003400450745011010082c2c0001f03021805030301c8e526503003034441110a516504140c0c180f00403080b41c40301580300030007040c007000d03060a04912a40d560480c200c0c04001c564a01581c3c582c2e800d8010081050000c80c01020b42c1d944041c40e0403103240b00381c1c0c0340300c4490301c40c031681501030400743c4034241d25410000400c4000d0600764004074100307003404203010040015444060854000fa620b03484182c000050f240320074100b400082c80100410310080041d5807441d2941c501e11595070314801c9141c0d4002078402c060520842c00d49010320036410031200407070365419481e540c5030703840b00b07110700447d041c02d0f1003060301007420241d920400e801c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 696136915 1250 696135665 696135667
    0x215040b0114030c030f070f0b030c0d0504030c150504020109120b0c030c04050a09060e0906090304030b15040e0a05010c0e090604020f070812040516080a12140703020303040c060c0305 81
    0x80a42c84410080900011a0144160b6020707040940e0204000c200340d00421020300301c1c050425500d4004288150071402c0000c0040082c808803104da84c08070780c0c44403d01c2c40e00203007545480c5812650040150005481044142400e1910345403503800140120b00c01d0701c03000d60040d5182c00c2d401c15210f507180e016100310507c0000400ca1071211000351f030b2052000e1100b0786090b807070704d0000b102c1c00741c00d420002c08159039a000b413020302410713039009800c02d00050003800702d40307811100d89a4030311881c08000c0503440c0d000080340a15080c021007d0441a00500071b02141021240b01a512003240805980039803c21111030039440c011500b0f00503045020703081100c80c0e0380e402c090001070740c060540b24148000c1044280c0101c1c03200d50103845889020381800340d0320304040c1801c0385000c0707851100700180480c0746820400e0160016230301046540c824640120140390b09800c0c2d038010040f101d41800759030700050301000c01d81c2c007000442c07140e4442c0804400c2c890701e400702103d04070710084004010881c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 696138165 1250 696136915 696136919
    0x9010e090c1b160b1e040e0a200d051e0907050607020d1416140a090e0c03030412060e010b090106111f09060f050402060921011404030215040b01 64
    0x4a40074507100d40840b11000c42d00c1c030401c40d0300c1c200268140c0c1d41c0041d0b8148404141030b6502d0000321041c4006900c074100480c1420b0070004005080740b00170b00ba80015503950140d04980340800e0001c04c07a12032120903140e403180851486200900400c44803895121107921009850352000d03640720340600844001010010301706000d0020b154001c9800340d90010030340906400040001640541000010b4060001060344185040c400e51071a0011098001c1d416405041c42e156004c07601c08540e11107001003403200c4d400402c10304164600300300a0b0103010004011607919040051a003a41c0c0c1700e800c0030441c140c0049102802c0301c29411800b0360003080080104406807090303008490301e01800040e9084841c81d02a20603c011403070030301d01103c50f15000c41d401072119610944410b06048001400b4502e89903002841c0340c420b820407288112014900c0344150400c64803403245610001700200f0030240d41440300840490300316011801031140090201c40014542c0c8500d00940e8007004101c0164 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 696139415 1250 696138165 696138187
    0x6180f1502030706020d1b0503040302030a0e01030b0424080102040815041a04032c09010504180506011e1d060607060e2b0e0f06070204060b040b09010e090c 69
    0x692000304500c4240600000f0425501c01002e02d424002d00010b092010b409641500400f500d201505200c0c3c10300820010903004400c46400c089546081819442e600f00141c00400c40c42582c11b81042c585104100806c0c40030440c3c20b001c10030301f504200f000d43d40710301141c02d0b407166024694044e0404040030315580090030210703400510680c4040d111110150420f088040b0850f000e400040b42c5065030307400e50b6541e81044041c1e00d00616a040446400c0001c2400c2160610410f070140790b03603844140710040e051441c0038119500000380e400d15607550302110004c05400001015000c0301a4000814071441c0a10f4a194034140040c0c000d182c1d01c4c0b2007001015004005d06072001c03610307076445100c035550910801412a0f440025109140307807850825044107030202c04601402050f0381c018200d07554482c0900e181c201c003110003590b100b42c10b101142c00352100d5481481801004640403500c1c200880141206a41c281d07180d200c110548030401240c001e050303820300c11910040084040070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 696140665 1250 696139415 696139439
    0x3030605012714011b0f02010305060f0108070809030c0d05040311041407030b040209150a02010b09091002071a0103051b01020610030b0636100803042d03060606180f 73
    0x501410111280502c40f1105501c01c0002c0e8003c9421010441b10303582190b0f0507115640e0064020b649000454030b41c040042c0080c84041c001c4000c0c0000709000542800d810000c8601c14140001a4cc80c54030002d00050300c16000741c00129404e0682141e100c02c103042a10501050b0214460341301d110b501d4100c0241c00503d44140340e240c019800304a6843d0070f44451403603400681480880c0b03603032181807020003400c40e04000d120724425440102408001103000401d00d2880c651100d0069507801e00745800701c0714843c4081611210046400004107001010030314002864074411202c00c00803052004a0301c884040b00e0b0501c14140c510020700100d040c00c064668401c001074040b1007a100090306070810b58004101607041441744404c50b400c00f80f2031217426904808001d0301c101c256814030680a489018500940407812000b4800003008540c040500014001c5d051560a2841e10b030b0a001000e0000c030b000f00000f0800c003100c0f0820035410141204100e03004802c05070b20540c00d006001900d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 696141915 1250 696140665 696140699
    0x207030507152c03013605030f0904090c060903030207060f120e0a02220e01020702130207020a031415090c0a031103010b0a1401080714040509040f0807030306050127 73
    0x512611242c1c024441c0d01c00b40300b91100710840f0003207820000a421b102e100005400000c008488030044407100c00680c1c004160340784245004030342340d16452031901080c001e01042d107020302502c0d40e4240c00180150000e40400980740241c0c02c0e01d0740b02c0d80b40c190a0360007a54062500340000d2900b0f0340920110450350155400c3c50180e0107a80c5090041d80004004d4485424000c44203030322844012850b0026104500308080410f00940c100f000301d800007081e26001c0662101c52580005050046503140600c18000d15405810b404514080d010440e40c2d0380f04010003681e501e1104000324683c3e010000780c40c164520014201e601c0039080d81d840d285106e003031711040794142d925407070506213035652409460060301c040820043c0ca86108800102a040c0c05030050080c0030798140700c1145071034510100c800380c5030190340605080e281d80c6001c1c0c0410f0a4400040d00441c00401d5503410558140c0050f021660260b9030000400360320f250a44444900d00c2030444041c61a0300f04006602002c800580 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 696143165 1250 696141915 696141977
    0x60102072d23030f0111161a19050a2f04080a05030d150b0714100c0224090a240207150609050c0d020705100c020703050715 55
    0x80380e600e06505041c2a0081488241102d0004245120342001c201054149080d00002d00118800c0611207010340b0a65440c5190f10240080d070205000f0f030441d1200c1c0c2008004001d14091520703844100369400c1001e90305016504050203d00c0c00da4041c004e4480c10000107102c4000b1070ba800f2940444054254840c0c0340144050200088844003448050103440c050406160b03540707070700d840400031139180114000000c00c035020b041c02030ba11106c0c02e0b1482182c4c4001086540c07819580c002e0b2400300c850b5104071000b41028910001254041443c01081054002c0b02c03125054401010507028070884140802d0f50003c07c000e804a501d40c8040792804400d8030060300c4e410020134686040e80d000725001e07601045441c1001780300100c00d2080c90001c041c080341c104905e0801a03000401807055280482b1840c2c0c000c1030f02c3d000d0001c01d00513045980d480729000c10041144010203902c84501e0300c019900d40c006d40304000703025916400400c01c0442d065540701054640a0285084004c078185485 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 696144415 1250 696143165 696143249
    0x105070f02030d0903140613030f02011407030f0507020a030f0e1504030503031008061b030702101d0d0507080405010f050d091a130309060305060609130203010305010506010207 78
    0xa0090b85041c00011109240d550310144c542e4210700349041e80c56405090f030b01103a0300030000c11001c01e9100d2212482c0f40d41c0745c9040c0c04008900a022809408040f140d0b09009c006c0c48140b2080c660142e1282500d000407500a0000360f0740c08000b41d03211070304444d01601241c4400c0211071014444d0010b07001c40300340100fa50b03a03119400400d9004d1500f040d08101c4140d4000000d01c45402541c800b034900a00303105009041a107001301b940030640d11200300768160001e001c808030701c1242c0240080034010101c408100a8a41c006560029400a124440151380100d0361160b414a226000301e800140e00b00090340d2806103030200450b07940050742101c00411009004200745026540142021580107445503101c1792140c810254070910003801458010540407102000643c01c440701c90201c8055040010b0a641d600001c10024460251031035031280317500344098800242e55005d54141c80c01070000f003200d80d4070a4011381c0d42c3d44207400360340a40131901403409a12101d84420302054122480c1c49 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 696145665 1250 696144415 696144443
    0x30c0e0f07080c07050f060f0f1312090e09010b04050c09060313030504080607030c0305010f030b18010608010e0120070f1509080403050c100201060b30100911030411010507 76
    0x7172801c002c00040611141e40005081c08410440c2000c0c054022070820010005030800780301e100702c0308020040042a21400c03440040d040c81c011315200c4020a2204400f081c60321345110414001d1007103001c0184281d18140124500c503807980300b91004958090006480d5407a114152503011002050440400108120108021300c0a1011078000c1101d40c80206181c1820600036058401c160041401c140680c401040450001d00341c07250803440500c05016100c0040c0c02070f031301500e5140c01624240d0700b4103007041400481540712000070081806450300032641c010514046214010018140000b80c031283c4000c1075a40c3c602600d2210810390010b01e200607692200c800703030065401a40c00d030700b111040301002e0801441640c03110009100810180b0b040c00e000340b03441d001c0e40d03130b80c8061480c21164401100c0071004070b000c200100d0070011400781c9044460070100031528010070600c10309095039260030001038402d40e0f0003107600c007040c1000107c0344001142d0076005140309a032104140842 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 696146915 1250 696145665 696145673
    0x3030c110607080c0c1f032406180801060522090609060f0f050613200403110a061407111305010602010c02190f082d04030c0e0f07080c07 61
    0x814002c1c0c41550020346800d0b0125000c0d00309203100d68418041d0348514500303c03a50001c00c203600041c4071303d4200001c10200c1903113203a404078554a11030f0210300101c0e2000c43c0c01a000a4496103403041c0d400c59105503030300c600c410385c241e0b02c03c0d22646800076840003100c0c80c5050510416810002550f10014400c9541e40b5800706840001400b660310580d1410544015500d43c011805140c0307081d03c042c0700a0610b6404240306035081a100c5624555415041c100c10611044500886801800070b42c0c4460702c070709140c00c1c41d544c81c500040c41a0b9103a080054024002c50440a0031410410383d1400c01000b51500900c040501810340c3d40490030004200c06001c2e53b01c2600d000c7d00d45540001120300344040041d240440340c0421801040a880403580010700000c1c81c40e045540c003042d61510380e180c0601e0400b070f64030504108491905401912600b0365903640160048070302900058a50664814002507402c2d400e8a4000008440200040c58640030b00c180c0d43e04240c600140d1841d020307054803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 696148165 1250 696146915 696146917
    0x1060305090313091407031a1207031a07090618180f09030309060b0a030f020f0f0621131e210801030b011505070b060616030503160503060a03030c1106 67
    0x41c030150f03454817200401c9820300c1c070660348500399080400c00f00c1040000d00d07800410b0444031902c00c0400440e1342040240c2409400015a40450030881c0d49540300420b0200c944101c032804002260b4070000950300788580c040c041c0c00f01c0d1541d800c2c3c8a241c00c0800f044514603421084100b15074036a490400d402c0760360712a120b0503500a540004140c0c1280c50b1181c00e64040112a83c41400341c100207101260044011500c1650b04448000414407240d0100b11005090b003c0603a2160011a0f240401240f10034080040b8250211030540d590743e100240d9205c0c041c41001030084484c580c00211b80d01d004590500324103009070b41d1900d008280401e02e00500545080c08000242c045004104005440c800a1301401c2e41501c414102800c0e0384000b8030a000d864009070105030008080713003094880d001191240b0442084403807074070640f41400340c065402515100d0f402c00d4584118920f0f81d01c100107490240d48010205e820441c5591402c4803143c10302d40d004d903404212090420242d0361044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 696149415 1250 696148165 696148169
    0xd020a12030905120d1215080d08090a0f0f050a050f01060f1409060d21050703021902010e01210c02010506010909020c0a0b13020904060e210301060305090313 70
    0x954150641100da280080080d4503c3d0300c200e008400c0c0f68684992210302240261018600d0f03d04a043c00d2944c400500242140041c0421440342d00d03003011462440218080034070b4070f080d80315000c16886130b550741c0e0342d904210072010302a4102409543c000074800c0341801c1000303028101300c8041c2d0016071030701414140c02c1082d000f0345a40d1004104062004c2003215002007409000da40e012a01c81008900103540040006204136a600401020041d500307000f81c02c0c03080b40c3e201d5030b0032224400c4005131150b4040315083d0f015114001e400d00c00048800d0080203103940c11b0b5540760503401003000644600c03042e00342036604583c590402c0c507203120140c490442030525560001c140c9080200c0007412584450300301240319401040200003006000032000141036000e03c200d40b01d07981e4140300110020300000f00961001d40070041c08203000c42500b0806a03072251f01c00382c40100c184a00c07552810840e068094084580510040010038080c0c8d0050742e0041c40901940c1c5010aa18169080c0450315 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 696150665 1250 696149415 696149429
    0x19090f180b0310051915051305100b0a02010227100305060315130c0608010e01060e1c0317060a030506010302060a0e1008100902030f13021201060303050d140103020d0b060d020a 78
    0x2c2070100300b41c11880c05a00d071206c8003030f0842d140182c20300000c203444900924942d00b2840e255800700e0b00800300d0119160040541c03002d0903031106c2c6460802401f0f0b5009012840130039000c640b55241d010b060354842107c00c074000f40074151665914006070701800f0020525a0315019040848a2408165040c00d200300a040ca05a851b400b051034241d0407075072a6040003041044000041c4847c101c0c454515041d1941c1d42003922014503080c0010340a0030386880658008a00d0044100806070801082c030011480d044101505a5404080c00441d1a0300d2001070416407040c0c00410250038032100900d043c40b0300e4940408100c4031359010421a8640e03410441c00507071528104920100c02c2d00b9004043c03c001c01095103142400100000135203405024112240200349201c0704540d203100303680340c601031180001d104041d542e050191035600044d4a4040f518200f00103400c100e410105294142c96004017010190880b82e00c0352510032800805203034001904030344800240c0c0e1040c190000070450 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 696151915 1250 696150665 696150691
    0x3030f0c0709050c0a020a0b060604173901050f0f1207020607050315060c07080d0906031505010f08040f06050406020a0e100503060111070b19090f180b031005 70
    0x25009414046520081401080740401c5c44018441340d40403401c8080583c0102c25070328182c980200080c0c481c03246a01c004c1403d6a002040c400c1d03001d0105e1807141e600480362130141640c0403e1441030700e40d41e10900d00b0542c0204100111459030195002d84810700382101518103105240c0090850380d4440c041e400401380329102005503203036040054503841481480c046040d410826003c0400d04e4401e424139201389008030322540d17600000c20004000307058540071203d01f410f5444000d00007003c0b501078070f000281014021440e46032440608400c44806941e0340f025200c0e140e00441e0244006030088512041c100039100205103240a0f17140650b000b1500142e4440031044080d24408004054500036007100c540f1085150f00704040c2c84d4407500a003041d0084807000850740341080103c0c0c10031400a500032900f003003003000b031241d2174046d0355186d10352003c510b40380d480c00510040c0d644111100318011071090001141e07960411450300340d0290032034098141480100382a03a808030348078011448 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 696153165 1250 696151915 696151919
    0x6012d091e0b0a09020d0e01060608062701060516080703021501090b130f02070b0f0601140c120703031b0c0519050624060a02010f0c030506031b03030f0c07 69
    0x1110065001000507880100400c05108010aa072607800e0b100b12904c49038041404036156445400103418050391a00030848192110b0002e0320740002910400e004084412002d4900c2c108441c004602d058508548111a0710b0f14100322180d900002c17644406071081c05001c00050340420152410f035209801604e114000003801d4064010160311069180342000340040b000e413200d405040084c44a49004609403c0c0348003020040d01c10440f0080004c1404020421580f80396010b9600400c4241c0c5c40751700d941c041c00d0151f0035070300500e1344d48600c681046aa83d25140309400081800a1080c00c010440380c2000610011540c081e948860200344002c60302004c10102b8085440084900301d980040c41003151907036a600c0000400700c108649482c041414240c4614840c4588000000c00481c0d03540d030107890080c0a04101883d507090103060820513984e050090040520592018004041074802c02100003031003012400442c2d0540000c002081c5003824000c010a40c0c0301c0c0050003054124 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 696154415 1250 696153165 696153191
    0x106020d0912060c2f190b070c05070b04080309030f0706020d031e05070f1d010c02060a21060302090c0406080c0307210605010f0f0206012d09 63
    0x14029800881000110350040c000078244220340107807240c000700f002035140d0240e18180c40d1041000688116403036000180402c1c3c1d03e44254440d43c540d03c580035542d0444540d5003170221030f20200d1004040c0036441001490790740c03080d041c80880a0060b804c540c01c4560758400d85065911a0304400a140c1001a60030143d0034100129a40b41d02e1a20052003c540340c1500251078a0944002504140c0c47d80c41e4841d040e107110814440d6a800d036801003181d405c01c104080d241f00514810200403480b40c07a81b50f4103505804d07000300c0d540315041c0c403001960300c400c1d42007280c1d070f40c8254203800034881d104882d03004c048112601d0b690101c08034500010414110b004000b84064010845503202070100b0003480006d901802c6a500103501e8101c9544279100d0280640d04881002c500709500e41d40395600409054068001804607042a21031861401c1c05403804c0b1610714a0307601000c0964000c0c401000070040e01c241007000510420741c664800604502a461150300720360220380c4503521030880007500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 696155665 1250 696154415 696154423
    0x519060b30160512030702030709060302090906071202210118110c030a0c030c1b0906050123090f030a0c031109090a0201030b01140c060403020f01020702010806120c1206010602 78
    0xd0055080240300c48006800510780d5220340c0d004890107120142c544c0c0d610420100700382d441041e030080541b04031a85415580c4002d0042d840203a201d03400c0c103c0455251a40405c00c47d0295010717554284c0904d8241200001a5110403050072106000d0841502514008080617010b0322500003001c000840c4101000286e0f0500700d504180741d202080101682400001103a03600d0100b414507010650a034182581c5070010108080c00240700c0845000d2207403030410644042c0c6401a40403c405c80d00d4200448440e40720b0036100d80b0005c284420b41d2001c1400c0c90143c015034400a084d8220041a1808039007040c1c0790480464891208507800e20800c40728000007810300c0420348603a6003628000064030756071401c0d14006418180d860500582c03030b0744109025464100d543c0c081d40d54400c0148901a9548400c950550040c040d4564035041c3c0d003c1802125140d9405071344030885512503104014085665140c81e031854403814280000d50744941d400d55a0010400024000381c0d80b42240180c14 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 696156915 1250 696155665 696155749
    0x1150909150302031606120209180402041104080a03090e060904020405190c0309110108040302030a0807090e01030f020a050109051e030a02181012150e010618090516030519060b 78
    0x26140113101d0383c00d007070721554580b900304600300ac9510a0b0b074482d800401d000302a07a4a9000c41c07503a0008001c110300c14006802241c1910907907900910a5658000d144210300540301260700101810200d0007514241d0029504000304a80d440da082c880fa0301c8083c101c6a050340c1c070a02080c5c0350030490301440144c034051500c444085c202070500c1d1920b541c0081d01c1c5d1056280708401c0c0f19984021540051081d0072000203442441c1031030b074095849052000ca03c00740120128807030440b2413004202d5510a0150301b048450241c0100103050700600031035800380d686000c15400d442803003110b00150703482d00107008986c83d80c1d0300d003400e80c0d051051030300401e00015000b1824006440010000082580b003810991003403036803001852020106a0501519541d40300070504085040400041011944104005803040c004c5400086280f541e141805641d480094a40e0b0000c40c3d0000c8044001e01c4034a003086d10a200000308401c0707840005280702c0c4422141c468138880508281121183c0e0018034607 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 696158165 1250 696156915 696156947
    0x6080105040c1a0403021509131b0509011806030516110c270f07030c0c08090f0a1d0f01080f07060e0f03150f01150909150302031606 59
    0x4414603040d1141c0400820720b200d015440700c508810540f010080f8400d030f501443c2c0c01071898600d0200c071100214540c10100081e446140800e91807080e400140c401c0001c034060481001c614580060380a45864110808007410300011543e90110400442c8148014040351b440008407400c00000e0030034102141e112070f00520a40e00306c41c525803800012403501301c01e8119000710300c0ca240c0c0c0368140c10004080480311a804c2c2540107002c0f2903280459458850040344d40d0410200701141c504903282c144614028108002c02c1205c0d00d06d9040414072071a8118015102500c40e5a0303414200320350040690141580d01200e0701804000300501005500404d415401030181c100d1507035841f5240da40d103100708000c0c4245160b4512143d21140b80e860400c0e40000e068036030b41d101c52021018114000c071003004503078003150008143c1410000e000d802d0a07010707a0307401c0d00990030407205d90010603800040d0720b01c80742c10240010050f5010003c0034407202202c40d00d80800392038424068202c40c54903c001c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 696159415 1250 696158165 696158171
    0xa0b090d062a051c09080702040212070806030c0a0509150a0305070801060f0506120901110d0b040b0130060b0f09010f092315040e180307150902010e1012060801 71
    0x210080304521013800d101042c8020000d4002d405145c48606072040100007034205001150390030368004442e540c644a4402d680742c1c115039903529810140c41e84000b4690035030103410100184800c0c189800040d0f80030503402c2080100c020808002407000b81c055208858652110400b0312040c1c030203008070001000d103504003549032400c1800241071401940c400804a49030000000e6440c0405d410a0b140031000600d6107549101c40d0320403001030001d90123424016800d1060300c40342548110540ca2003a45052401c1907144400f0415000341401c1c07690b0303020700e1512075801080c180154801005001c060241095076102080009092000c0c000e9400c0d0030721406580800007502c540306030244216525227004680c030400c40028500c1103144614410020011501080c902c80d444410f501840242c411445080c00b80d2818a599108980c00180350103038042441c00b540341c9507081540281c0c17050405500307086c03421011943c1e01120003501c0e000100c0803100b065203041c09120301e201a1541310024 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 696160665 1250 696159415 696159427
    0x50d090b0304021201110a170f010305030307180503030406050c010c032d0908040e041e0809010804030c0609051b0102012a11070f091a0a0b090d062a05 67
    0x6500c450000802c003030f010703803600b540d0340d020542c0c2035004517524485010510303103415160030001c140355280040c843d5250014000305100d52030b103848403030489074414015032440d517404030115945241100341614550b000c0c0b101248954080c4044c0000e030404c4e548281d2a031034421100707425101100400c0b07080c18500405202d40d041c1c450403e00d031030a05144060300c5282c5805a00000708003084024004070780100e000300d01118106903207400f4601071040350007c100034400031400006c042000805d0300c0010815042c00d54094000d26078018003d041440740b8100f01d031a00001e07144400307411200764214214148214001c120045c9a00d8402e1008001e40800c89030707c034206407110f032140b52043c4400c00c8491a1a4880d61841083c1c0051009880d41103944000c80c40c2e03640b605004e50440d03181008100031480f0030700b800841100000515000195241047c0b0a155900100585030080c8488006c400030581900070081c1110484070501c80a4044110f070214051018100004200c020056 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 696161915 1250 696160665 696160679
    0x80114010207091a0a030807022b15020d1503050105090f1222091a06070206181c05160b0a0807030e0a060c0201090c290f160c03050d09 60
    0x2c100982c0e4034040005405030700e44d20040b190130b91020186500085051010013080500345c017408100b17209a03000f960041070344560424400c8492105051480e00507035042c0030421220720380c040d0301c908c03c000524010005940b08252102c120072a24203103100030f03041003040b0382445015408054103000d80090b445820b0f1440c0c03100c00201051004d0840411200000030300100c440503040f00c00c0b0020b61505907100d404401074028013148000346814040b141303503503003803a8049810f042d034010281031801520140500003400c0034800507800030907000501d0a40c00820f03451100050007200201650854030440f03151120090b00555165981405a04001038212107000e4210126044c04a405003e4120b01490300340d0064028000c141010b0461040d1038065003c01d10725030194164040c0701d601c524110280c4202064050000721024114500e0051514068400307139800003505494100c4140048540710002241503544049080d000c104200f0100101100302740036041001000d03240200d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 696163165 1250 696161915 696161923
    0xb1210050f13020702040b0612091204050a03120314090f0705151902030d1d010b0f011b0606081506091608160302070b0109050603010b04090c060302130905090c010801140102 77
    0x102c800000c1c1d8000c03410070110b50792034000e400040c00c090003150307c41e030451000344401d00007a10700042500443e8589070820f6201c03000c0341c083e030301c01401440f81585903542c0d1042d40031100320700d8002c0607070780c030205c2c120f01c00d080001900804041004010210407941245c2c180511517114901c070f03500c1c3e81c40d042102d0211509444046190514820607003940101c16410352040d00340710302c40c2d10701c0d00d1903601140c15680c03000c00100364050000c0009000c103400703100c00a000038180a011030003003090750040c490003c50034680c0304e11507840441c00a585d48100d42c540b100c44011480340c40c903000108051810300310005a48803602110030b19202d400c99101802055001c0d08580d80f0540800c101585a4001c4d011a44203e60000c1c00000d65a500d802e0100108000d66000b407003542000b0800800d032803c2c0c020104000c0c4c00401402d1124a0464260001d42c00403100d0701034040c08900c00207440107a4420b02d4032031a0100c0103403400103c400001081208141c0005602c4d0804807140d40c56640e00013 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 696164415 1250 696163165 696163189
    0xc07150e0f0a0b130b03040501060f0b1c020f0f0c03030106020607090e07080403031e0c0e0607110f0f090405031e040305100e0f190b0c040b16020a0b1210050f 70
    0x21602d966601184900c4d0510368075400080d03550700e0020600c403c2100540c8030400b150156001d0000c140d440d02d0030020117204075003401031400d04403040c130b080f04600d56000b03000c0f2007005c1a0803071034105003040c0c0845031780040c80e1104090704080010420a074041c410254401c03d1031803c1c2d0b4010307013848000140c0400c0503081d4400c00000b600041c0c2094041c1c0c2c810140c409555001c200f4005079081403a02900380710004000062800b00c041c0010b051020940d07100b00e50003491200c41050b410140400306060762940c640c0451384814102081d2125075009002c0c5010f01d01569603400719024200c50b02c0b48a400345c0700c00000070001040412004a600e034800d000340d040214410340701002e501d04e0a0010742c001c05141c019a1408107500380c411030b0050020b8411520201c4544e1103903c1600540110700c24038185407003c0050004004c1b0040d01c0025142c8010004401a5181e00301e10603503400503007982046240201c103000190802c2d030811300c0149011550115a8000a00810031060080d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 696165665 1250 696164415 696164429
    0x1a071505061504120201170601020703060b0d0209011805100510122901080f0709210b0703020a170408040612182d05030307140c07150e0f0a 62
    0x3000840d09075a60181181040b40120400944450322006022192204100100d0128004840c03041d5050851400c040c0700b454160040c04227a843c603290103003e0f040340e00700e69600010034003a1000607a55034544501801216040c1d103c0c0061410840c01140c1028148040d040d625413410020780c2d40e05064040000c2442c60110079002400c614180038046030f10407039040703882c00116042e00840202505602ca03c00b40c0e14036500b615607d1603c0741035038054510000080000744280550f03a9601001160b071501040100c22400f45500c8032818103000b5210f010000360002000380555a200040c5410030750000d08004c0c0c5410302d582d5070090742c8500e00c07642007400100174040740200e42507880b82c40c443c0c4c2154611200000c0c2c0e031074414445882d5045c9812030142d044680c0000702d0103c181c00e0039040e4450700031443e54590040903183c00707140300e040c822903d1301040954141c0710300b48140002070410503002d03100c040a0000c0540569100700d0118094401c2001100c46542c48200b00300480d050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 696166915 1250 696165665 696165671
    0x307020f060c1b0c0409120e010809030318030706022b0e0c150d020d0605210a02040b0402070f110a060f05190504030816150e060a0b011b0c1a0715 65
    0x300c40c1000f400e00e44d60a00c41a40145451002428480c0c00401c28181d005c2030f646150399903280c40010368440c03805440f105100c1d4001c2c800a0101d00710459000401d0f04803104907810254196200d0050368803070b80c100d61107196040ca0300188207030141c00204c01040382c0c1000b17012800702c6a0015684800c807211031071040203404000700d80e1a43c040c003282d5034046e010005564844d60150400090a024440c880c004d00641d40951444e84505680c01402c1d11040003510740c010454082001803e40060a254010342c01c000d0b020014800100c2c800c101c0e071154442003252441e010030805004e020b5408035040c4040091410081540942259030400c03202d6040d024201068500b200e0a00903600020300080002941c00325490320705511052440c401d60321305090380c00460701481a5203603c0c1d001c0c03110354002000310703540e407400d500803e500d51410b1405003199090300b1301c0100c01c042000720988400c40412014005202064200c031100f9011041d01032078082160b868220440c01e80303243c0a05207523 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 696168165 1250 696166915 696166957
    0x91f09110712050d0606110c040b0310020306011404061101150f06050f130b04080f0a02010905091504020a1116030b01030f03050412030302190e0a15020c03030a02030307020f060c 79
    0x4090b030280c4000a0100744e041041ca503c2c1c00c0b020700079003690190302d0014820254101e0b8a8503060107081d00511f8040c024081d00815155a00065000038002c02e043c0012248050010881180a000182000c3c1e0b20300c801414001c205078212002c41030410107205089100784071038559001c20a08486807440c2c1503950704c1c540c00c3d01c075509000d0002c080a1808440380001401c1e030724803018106441d0818143c4600542140805aa0b007040304802070104e0040501041245000310301107601c1000d0618290812800c00300041c220b0f03001c00c501d0004690000c0ba49003110a04101803401c100b4810f10503c8070905540310740040040500c030090208040304200010544500d05440051440b0715410140a20902c0c1c060040d4004101700791034582803640d50108588540303482032001902030b0500c1d03407950070711ba6803416894074501c4800035446030b064050900d4500300300130050405182e000c0c41e103d0516070b100a04004d582409180c2c1d581c4040203002d020010082101e00c40302144459003074001d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 696169415 1250 696168165 696168167
    0x402070219050907030c0f0302090303161b1d04020f12120a11010b2202070c03060603060509120d0506011b03020601090b0111031611091f09110712 65
    0x210850800a4000d0600110300e01810815081d810640700200c0300c0b01d040780ea58000071401c03503424007590400114500ca030450118082c1d401004140313000b9060b28607243e00d61405e040104005c4a00301d400b02c1c940c0a0414101811072550000f0b08101c50014943e160600b83c0c15130750343c001820182c441c1026500744500781d6600903480008800315403da50310040304030003d011503000b028064021803220203205036001010301c03440d508250f009121005603412014003904a4045520324401c4503400c00603080414503e51515000f14460799010174868250710301039041e943d010b89006002d80c01040380003211401802a00c86a80340c2010001d0381d81d49402c012504503c0401c0d0161104840c0c070050424154042659810303942103c1c130502003040321200441d200414039100000d1504280a03050300e8034800c802401d01c080c020000c800081d14020001200f4007000d0707030090444070010b50034141c80350400000034010a91185e040100305513005c0c640b4203e10407170400a008040c1850507008207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 696170665 1250 696169415 696169417
    0x605010f1218050a0f0203061522110d0614040b0a060e0d080f03090c01110a0b1b031603140c0405061e0309070f0b19050d06080a1109151c020402 64
    0x1441d0420b085a902101314200364a210130304410a0b4082c0c011100020f6011500c51044020910701030084200d04268039603501d41c2e00c2c05071103481ca0b00c0b501c0e40c109284412100700601805640312800140321403404160144506659400e140540d08110806d0741658070000b40308111040760600b22020004503001808034001d1540003803100c0c0c0b0100c0d02c1e080e4281000040c6200d076600004480d01c1200a06c0155014101c81200100e240e025481050000750440625a0450907428002c1180d42c00c00301c04142641044460100c0d03011001440e0321910b502d4000c442410300d0882c102460ba081090010780640b103a8043c4030301176100081c00c101202c15017000100310351310100c1550b4980c24250708240d2103505500c1407000e80c0d0b80c0d4410103d00b00d8083c404480b0050f410007800c00400b034026205a580d900a81c00d02c00896a0742c41e80001c40000500c40414058801c00014072001c880d907007007002201010340180c401410346c200e00c0440c2c1e00c031121801e10b00b4200d1007020f03c4155480c4000303006 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 696171915 1250 696170665 696170711
    0x3011a01081f0e04060b0409080316020f0105040f021807020a02040e030903010501092c0d08060a030f0501060f0e07020c1917010c0f020303070806041a040c08010501030605010f12 79
    0x2441e103450b8400151000302402050086104d00303802c0c4442407009040009403503000038080c15400081001c5110384080d52602403400d500c500640f06a0f4000b01e41c102d0845004507000e6a00103d048010700c00c503d4128255500b840010400e603205007011000255141519600240600e03510041410301c2501001034444207070008001303104070340c8c4800d04840501003603038210b00081d004808440c1c0c41660894158880b5010320700505211304a14000c8491307803005028550000c9a031030001c400704c0e4100c840842a94090400440e109140030703142c948218807940010700d501501c0b0244450a5400704190b203084100301c859198406401081c404c04450540c400300a0000000c0a140000c8040d0402001103507079840d071284d0740500d041c0c240c0e00c911040b545a80040c03070603c002199464954411004160a00c64142c24080d50340041000c903501840b00402042c0400e0040216690501440000e04001e01c1c06000c0030000060261070f04412501ca6801562902207410f10034200c0140345207 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 696173165 1250 696171915 696171961
    0x120702120609010b0411090d02060d0207080315030601060c051f0605040204180b030a020a2c090a020f0f0607080d1803050c06062b050c13140603011a0108 68
    0x81c403402c05880c0d82d40244040d05400c0e00450400d407814990758441d170199000a080034004801c520550340c00c11032164084030341e0a01c095403c4c0700030008110b914024510441007a107800d66055400e104041c03622405134807010400c2044a18800020b4021801c0c10094051000e00c241184410440401500c0650170090300140b0206000580300f115220302c403081100000100901d101c0701c02403507210a10020081e400c04070300078040040401c1d00400b07000000307a81d842c11300306001650280c01102e5094959a100750300c510300880651515800d0500030410858600401e030030b6060105620380585c14000c2d00c0c0c80380c00b00e002e034803104503600044c10784405491310080c6a8094079001c0c00c55004898035980c188545000168a424402d031818848500c1c1c1d1845514030011010004001d005400110354600400d1604080c54035804941c030040d0140c0b41d00440c14a92024080000c44070043c000303842a810007010b41e044265841c1c58010b411020b20700884190382c2c040c09000701f2982d01181c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 696174415 1250 696173165 696173173
    0x503072d03021012060b0327010912050919060206070f14161407050a090903031d030a0e0301050f0a15080a0605010e0117070b0d1410091b0212070212 66
    0x1244280d11080c420300c03001040341c0030005e50740c440300954a20702086540c0e24502e5a080f5501c2c00940c038580f5411b800c0f41c443c100200d81081c00c0d0340c540c40309000541c25440410000f184a184a00d0aa840e202c0fa070040c401d40a0545403511000070f5030b540e006490201031102c640030124500e44650104034414980c1d2508580c2c4d04400c0c4088100c2240c0401d0554209458440c013080e90107011602c03038103d400c028592031400d420b00262034010302071581c04405150342c5001a002e07004002100001003801c3d403014540700d510400c0060409841c990505209916003000c00401d090308620558100030501b00014022030b40c3ea410100440640d00540c1c2d880c41101d0121041000603042a4140d44007050030b8452030740c1e2411020b08212004007442e541d5080b40c0018030071040c20801404d0711626190021584031003040300e1b01500301041c1c5417020001031425040c049000d450080640c220800301d000780d40820005c00c000d4950420304c010f4882414005803120655036010480042c20180e44e0681e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 696175665 1250 696174415 696174439
    0x10c020a0b0c12040b0f0709060207091e050a09110d0b0a050702010e03190f0903020105180f0402040605041427040f080a0806101103090607050a060c020a03090503072d0302 76
    0x803040c10202260001d402c070b8021000247e64a10a069030422600d1580082c10301c00d0070080c2540242c07400747c0718048800c800190301e10300c00d00310380101d500980c00d031500081c0306000f030709041e061000b42041880c002d13400c2d044e0040005511740e26190340031080d030100182c00d485480080380544820000c00026100c00b04018000444094900703041c090240c68003051540411800d0382d500c61a8840a40810300030b2144500b80c071030080020001d0344c0003c003031500c4c5a03003010000d0101e0f003041e0010000110301140a00c07550300314800b1004014021900d090b10328a4080700986a020700d40000b680162100c0e010a04110044101207081540480056111079007040003c000590031101c0f5803107030300401c0c03c1d10002401084105460b5040384080c5281400034400d2000e80d03440810b040b203003031241884070008103003680314858881d0440d5000d4000f0490f6400c00400c1c20129803c0244290003403102003105610100d0514490400b455040700c250311400708030180402203900203500f14540b45c401c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 696176915 1250 696175665 696175673
    0x150315030f08040e0105220e0a0c090e011d03070210020a0b15040c031b030e070e01081510050a030605130501060f1d01140105090d060e010506040e010c020a0b0c1204 73
    0x98000d542188103003184c503a80e00c0040028403403400d900c0012000d200e80c080c060003d49600310070740c2480b4080c01c03a1205181c9a580404183d400c0d03015400321039a440c05902400f10a0283c28410303c12140c030030751040d40710224503480b403280c070300c0c001d10407405a40102c10a500900ca01000b864005110011a103894480303400c81da400094107502c01c521b492214551980284901c01c0252115042c0c0c000d0103260200a034018606032441118510544000240d2241082441400307811a42c003d844840d81c082c040e8a0465009008401e0381e407940786e02170009441d4420594100c2c1d07002100400c00383c44402000c1412522104090f02c81c0d402d115001c102055005901c800b00c0d00713514041441103101108030a00ca01081c05400000030640480f03000350340c0f00d54080e1400e03440051015140444c141c0d80c14017105d0b083d541601c0c0a0b5102e1080194620b805e100d20f08100d08520000d2010710f81d0418000d440701419038000b8044030076240420b003204071201c1030700d0300000042540c82c0d242c182414 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 696178165 1250 696176915 696176917
    0x1002070f020114130b0f0c03070f0c050d033207050c103b060c0d1403010305030a140408030d021803070605030a0509031e0a0f020106150315030f08 65
    0x1006034085880058000000c1c0030040132940b1041404c0c2c64080c1440c100b2014000c65800700403400d40091080c40000c200030010300c000d00d4424845d54403001500f42610b003603200e60206a12041c40303011582d140401007034000c105002c201401074070070003295008601e010f81691120002c2c0c1c0c8840d00100b0400208440007940b0920303400126080030010002e800c040b290100e0683c101c2d000d100c5401042c0b040101201d446101c07400754540401d4040400b103012a41a03001245482d4803607100380005201960841c1340d07544203c1c03c0320301b100c0ca15070440e103070705549102d4100b41c0000c200201859529242604042d03401070110030054030f9440b1a01e10504002c1c0d00800c54212688101080d000142c2c5400500c52003140e00e1900d5440c1540d44404200c0020240104201c11174042000381d801e00e60300c2c000452500c85985000c1039100d47c8500c000901c100580c9180409582c50002c0034402c6110009801c091900300740b802140c49101c103400310b07490403a6a84024030880b038242c883c004004030340d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 696179415 1250 696178165 696178193
    0x12060f08150604021c0506030a0209040804060f05090d141608010b0a0f0e0103120c0b0408030f07080919140111031b040b0403020d05010219030e010c031a090702100207 74
    0x8442441c5038a40c902008128810803103944507543d1960b2007020341daa8117800881d40300300c0090940c0d0000d46503801040f00d4400407101125000c4000405004c050703001440d01c014041a03141c250309190189000c550401d5003190051700c2071402c142400543c0104000c0350100c0c0640244120755181e0303074800035020b40400703c0c42038401d0007001d6003c1004607440c840344085590007083c0384a180d01c1d60703d030400ba0301a030760014410840e40e042c1c00400314040e5034503280158800da0200b5945d00c0c0c0200001d0071640054145020405524140b1420402c0000c103003003904802c107400125008640740520600c0c22080c50a2103550038420010300c041e000c1d074059032003480031503110301e0041c568070602580c0707100c1e6000702805160240418400746c2000e451120405210f400010315248555019000d03001e55081f5610020742c1b070340303a040300d002c40a018000c60781425080a101906240c07400120f070004680203035000b000b0002c00601c1aa20030003c050103540e66802c1195240b400d818031401065000d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 696180665 1250 696179415 696179443
    0xa150608070501020309030307110112090c140121020c0a021c03080609040b0705030705091918110d020f13080a0c06080106020c0d080f040f0f0906051012060f08 71
    0x381c0020381e54004004c0314000c0d07000401552424030541d94810a0310345e01e4030568104a900b131100c00f070703c2446100f03402c1c40d00d001d9031480d40542d00d84407820b018080c001220504014000d800c0d04400c0c02c5004040110f0300d00313080003607107881d580b456062400600100181d803040c00c1c6409103024480d48041d0b06000c40c0a075551070784030354604090144103c1c090742c0080203501000000390340760f0702c1280610b412411a10384907191000b1540080d0000c04046024051100b1a00c1c08015054980343c08111040103404188803480345d0b1325150416000c0c0d1a00707400100d800144c0366000407081310880c0d000d000390300c001c0910f407900d544101d0f0384c50380362001c00c4030350128a46d0081456400303440401d0480e003041d0300502014001c102031144181000b94125050740041c403500000303100b00000b410141c03005001301c100710f41c03511580c10301919980e4000d035105450014248080d40310030808082c150a2030a154065581e8607015500034840c3c0e81c0b20021503040382d10046401080410014699021 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 696181915 1250 696180665 696180673
    0x15030105031b09070c23150105101205190606021c0e1c17030c0c070b121f0e010b030a0b01020705010503011502071e03030212070201120506030a150608 67
    0x142d21848405005000509034064280c0d8006903500e44a0083d0700506849100c0055030302e1508078800380388100001a1480a42048041d01b4842401c09030041c0100402c5899a024810032003001c0c10380c03004049a40031203519680011000c6009144415010546050800c01c15680d840001e44500f4808070780d4540c00207040f156000d4074890402041c072414004c09280002c0040c00d1680030071413010004480000d84010390b4000c05c03a250014522034916000c0e40c580d1004510a13850601199801c04a000e1000b4003014540c03855110b01943d103c850101c0d140b40740203030083e05500e01e1215030721180d6240303004800402e1032040c1310051401a40e00e41070900c00394031194016600c1c1d11150003090300142060004111103418210690740c040d40e5030041e94002522041c000614508000900d6185600c8213000c004065040140010180151041e04d04200442c3d00080a0400b88904601500c0e110804510590b605004c200d20781a40160a00c1018408204000140c5403a1140e2695402 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 696183165 1250 696181915 696181933
    0xc03070303141b030c03190c020f0c01180608040c0305100618090f0201120212010f030b09160506090a090c090810060806040b09011b0c0b0c041d06030c1503010503 72
    0xc03d400100412610340720000c0e055540c0c40d9480d140d0b9400040c0301d18841145d044c003001120740300344941000900070303601a00082d07007880ca60910380007101542d0f0f0304000c000541030300c94600101c003286c04da40d21490652a0f030388480c1002a80c1c5500d170b800180690041450490b0b00c070906500150407224000350404480310542e40e14801c903440510040c0420b03070390404103001984200000c40d0100c00c1c410b001410f240400c0c00966160500342c202c1038a40c00300440030710a2003d098192075004e04c000c00140007000305d150601060f1242840b0710b0740910004074443c1c01c165541d500450140c03003540380070448249a01c0004007072401c0da00c15092607001c1c8580d090401c00042c0100b206499020006000e291134583d01c0e02c1091400401e14100d40d507848140a03401008044003880d02d0502d0754900d5122403007810300c1d1002d030b1400b42502e425008200801c001c5da4011010030300700025000306400d0181e80c0c03003000c282015501202158014103d50000e62010000710155058a1059007100c144803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 696184415 1250 696183165 696183181
    0x6050a09060f0f0c2301060e06040e0d0c031e1d0a05061e1b1b0102010c080403050703211a040b18090c0607030903290a110c0307030314 60
    0x302d08640b4041c00a041e014600150070300445007869401d202d400c4074040e2400d4250f010072070f0850504110300c0c0b40d440708030400c9080740b1081d595403c004200c0d001c11002010003007946e0707a050119442814410241e00000070b05000340e400c14246181341504d90180d400c00000200b4140c0500760900621034820440c00d52420b020410000b66440500007524015454014a410700e1003002e89540d1110104421070000340b030b101c90b5130f0301086004024100c035903507070000301c03108250f80122504580c0360031082001c060340129155045905400e04903566403035801e0807075400d41040400d21240b0340105000306100c40c00ea021003440c528441400120481a600300425103101c1591140e015403001c40e036200550b21014810340094a000842d0900c1440101081c2150011042903001c00d00702600bc10a00c800f1094018444d40d90090120103000d482c4c01003000c0c884c002d0f0840a600e965083e8110395018001c040707458013002d800c2160780300c000300d141c005c0160155141c6407003c800070b0008a1504 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 696185665 1250 696184415 696184427
    0x405100e190c081213080105090d05031302030615010914030304151b110a06020d36030c031202071203030218060d06030c1205060112030c05060106050a0906 69
    0x344642030040c00304600900300040789241e001030150340030300c015007000407022403c0228020f901001148140c03a40030464030101240c50f0390340300c49600c0e4100400c100703000b0320205d03807680d5021050402c683c40303071207120000c0d0060003c4c10313009409d40f140364140a0001c0e0704814401240c14242c0c0c40440d01500c4500350404a003003900110340640c01407100303202c000c2c00b03460240887e01d00d5260905e100b214001c0203611611000d801900c0c0408907041c80f00840c1807840b12400a4103060004218529540000401403802c02c501507121031070b8014244100d140d15a80c8204a524541245420540f00c1c1810302c03030741c1000d1008503202c0c00000e00b8801c0150021440d44119400c0340303120300402513582c5068011358840180c800c03107600d0a0b1300c0380203903554107c090121104400000074505096241880406500e038100f2068000d12625100000741c0000c1c0c021705403424590004603614461030143c400000350740c03000700301d4001e80001042055202d0040c180c1d030b02c001c1e900c4020007075580c0d00640d08 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 696186915 1250 696185665 696185681
    0x1e0f0e030a02060c1b0303070801051c08030718150503090106080a031704110a1403010507050405490516060f0509031c1110141603020c15040510 64
    0x240c1c018074005001340709200040c043d0001207812a0341881000745005045610403120352011643c0c0d4001031007a03040441008880082c00c0b2019012a4480d84030101d10b03000042501040000f64100c101c0404010540b0800070b042140310030246401500000d1b216400480700c81603958030346880095141c100040e0218544d8140d11200c540c2020040d45410868000300705031100c00c0b03168810030407519052184401440c800003810460f080d82c0c02010300350303400a401007080040070f00c0140025921012110012100e00c1492139030380710705000d980410454180e6040c03c030382ca108405d28076100180c8541e4441032240d02511800c5070041c0580142c0d650fa8003400300001c013000703010307080303c2d00400090601c4a4001e0440d07401040d0b107008120448000003c6500062800071031711840d000070464120031182d200010300141e6126416151301c60401440b401c100d03007101180b0400c0b94020b60464810703003002000c4d1401011106446c1219507001e0728210b80303c0c0b082580c601201b0b03a4601c5007400c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 696188165 1250 696186915 696186917
    0x1d06010902210609041403040f060923030622020603040305070c081203070c02040e0610080f0319270e1806040b04020118050405040605070e0d11060307031e0f0e030a 73
    0x52a2115106c07041c40d484550780c00000c0e0300c0300b0000800c07040460803803180284440d540b00140c83d0300b4000851301d41c000300360780c01d0a109941043c00341560390200726507032310040c04010341ca2124109880c5e842e0b204003120001e03400a100005101c01d15600c5402424894000d8901e880000d5075490540d684921413080340b4800c603820300206560603c1054014007443c0018404500417119001c2c65041520540302c2c680c41110b801c000300304d4684d040c424004294400005141020080e114481d4490082e8144404000300d58031042c20010341000c2841070204010780901030a911400405072105060314400080c0300c42240100040d0310024485100e1030b07003ca280d1f102d0352525401501c485040f400e0818000701c0d00400498a52954840c2e039100303034042c410106280c10400d6010f4044d0001e144c2080c000c1c0100403424007c90544d400242207008151081592a80d42c040304030001c200001111100b544045002c200c101e100e50054480e00380b00e10410003400324140005542c82c071520341400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 696189415 1250 696188165 696188179
    0x50315010e01050d020402040302030f060a180209010509040c0e0c0c070f0308120604060911030402090903070c031b030c0305031c020310210c060c0c0b0a121d060109022106 76
    0x200090130300e10749000c041c030301c05000581030a45a50000c0d0800000c0c060413030a551158081151031003e40c0290001d1b40c01d01070202da0b00090540106031505014050f190168807042c003c5010003604544500040032105c1101150b1b040400c4000d00c1d990210b01d1103c80e511a00b100454022903001c01101201c1c0c0c01040b852604000356a5082d09140081c038499000303680b1140004c1c90103090180d101806d02e061442039a83c5041c0c0304000c05500003902405240e40184892000102440881010340b03810180c4551000803078180701e40070300b249030001046c4001c0d8034000010000000050400e002d4003080884400035030720400c00c103e000c211500401c404150300c041041c1c0b0804c21080c14043e2044c0b003030150b48582d40c3c84855080303401c3c0d4001c0c4000351181c88040706001c1002e40341e01c040c01c6a061100c4ca80aa03c4600500d2014030266600b07280d55228056201603018541c8400d200b445039091311003544c0d56414940003500301108865854110100441d40c00703a1010040380301d1000103000c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 696190665 1250 696189415 696189419
    0x30c030204060909091412071439150a030b0d020a0603020a02340602030a1d190e01081e0604241107030f030e0a0803060a09110301050315010e01 64
    0x380c001e0700178104240c508001c61000b1074180f210500460310b001c048a04515a1560340e0b1a00c8103440746e03000646000c58228030720126400b010703400310550041d002e50303c002d8600002101c0042006000c1d0300700764420204656114152004405030458a20f540c07070410070540e048050182c40d0010708002940000c1d1100d0034803001c0d011b680a041c1060031441210300601600440b0f140c2c4c49154080000d581070107541c0b240003610300710f1004019106078400b540c1030100407000030301021a810002d1140310b05021452907140c44109841060960521340c5081e800ea491464144558080c000c3d6842e41c0540c00b54800390090860990740c1185040e002003110307035a1511081d0510510303a103814101d846088411130704825501407065490054611260358003664a07000e01454031201d540d01c1498142100c400044c1c01c04075808090703a0308841c2e49562540c407400040d41e8001c4540140207018a48055119580749200242d07040e15000ea04a6a03400814002004204801d224540d020b0000b4401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 696191915 1250 696190665 696190679
    0x6090606091602250506070c03020f030d231903060e06010912060507030902030f07060e0f0904021e120a05060c040b0f0a020106030c08061e1e1909030f030c0302040609 74
    0xd413400d01d1960740e0516001c591a000018030303d41c45698280ca500b208484180300794540000e00c803440601c00c500402c0032604070b0310090010704a010712440e8081005140702880d003103481c1210001d03085031828158414030203402a004015a0040c10019810341001440550040c000d20f42610042e006004404801e60784240150400034050310030541c40d5044200141c4041100c2611004203001410617582003100c0284000c40101a591080c8010010600162540103003030b41c01035019a9484049200b110040c101507103814140d6808c070006154030342c042600841e480c80028032410644400c0d0700c40500e07108a0380568040c0c050030240070041c802c022000c40d8020540304085000114440e0381e0394a2f039400010300c1703501c40c0501e030300008100080048121080b00e02030900310190000d0781000d900d1400b40d4903030b0380d00c00c0d400f441c0080b0104805d00d01c07120504a4140d039030a41801400303580d2600a090030301041551000c070341840300d0540c00718040e009440c01d8480c2552103580d40c6d413034584 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 696193165 1250 696191915 696191953
    0x50d05090105180a260f0105101404060b031008060610051b070e0106030222030c120303090203030a050a17060904022e030b030d0503040b0705030408040806090606091602 75
    0x1c04940d000c9101400007520130702d0140540385c0941c1d452078219140000b160780c86d080048002c0c0003103840c0d150600300310b440d80c84508008291109040e04182141000d0003190040000ba0000c2200c01c1d4080104007845c0b041d0301c0048181c48070b0031b042c0c9291343c69820502002080c0f0074030840c04120700780300e01c118424594140c032040030451012650700e0359455440c146403000c2a00504006a00000c5a00d4442d10001c4c8048505444c602c240c0c00144c503540350380305241e400d4002d02584824070602c01090510039005002a140c0040503a603540007030500c09441503101c040319002050b1800000011000280881d621614010703007100000c0d80c441d800c001c019140c0800e040391408001032514141301c000c508034044907030729072000076400a04004041c034101d01c0e40031080030000104100000920b402c3c40c03154125a86092407600d984962a03c602d1a01458004c0e40162086a04012044400080c013600507081031303c1c95a450b0700c07001d244482002c41034004c8000350b0b102646e490195103070b440c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 696194415 1250 696193165 696193207
    0x80f0c0306031f0515010e130c11010f050906071110050402060c0d020a030206131112030405060a031e05040f0210090815010312020f0d0c06020f0f0304050d05090105 73
    0x20b003500d40d64842030a0707080107800c0000d10f1040c810380c0c45042142481359940c0762400070300d09082c8401141c00900009030800000b00781c5400082d1100c854202180c081d030145a40b80040310003c0c4050802845e081c001000100c0c1c001201e44119170110300403501400440c0e02c1d40b4214800b402d00020400030a00103000080e10490b0413100c10010102e01d48401e10107821188603642c090800000103080c001c3c0740c06030241c0341543d00e0144840400003d103110340740080e120001c0d24004480381d180340d16070b411030045a00142c1c01c107200103683c6060350340c141d128001c0100300801c100c20a90320050340e1000c80b00200c5000b031440880e0700811003d4170f860a0b0358080d6104a02d001103020b91581440b83c1044054840001050703407003801882080188135104201003120310041c1901d00076400320303d50fa040c1040c448800d00c60210390f1081032091507011100c00c008606400c6036a01801c00040703d180d401140e0549031030081285080c60320b440360341240c071360100c16542c940c1014004148151100900 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 696195665 1250 696194415 696194419
    0x16080702030405042901020d20070e010e070305070311040902071716030e06131217120109140c0d0e15040516150801060c140a051b01080f0c0306 64
    0x34000014103903240c0c000c0c84240210041040a4440429a24a40045100c5c0c1c801e040d500300402c0b2410a0f5481828052103410200f140c00750800c618007200d0820704150001200140c2d682c00110300e50205025450081c0795517603007002180e4502408804540702a840e6401c84801003000f0080c0002c190040c0c44154000d6400454611060f241e442c0b99030b00c00c00016840794600e03000d40080c103401002c90805001e013907985d517203013002201603180c14480e1800751440380300d4030380392103c1406074026150704030302140c4800a07a54001207803e00c0700c4007000d00c0744010b1a4140242d8031410400d20b180c460240c0c0081c80c101c0d0030160032f243c0a0015112007071000700c0c1d030700c1801d400d50301e17541180d01401d002d140a84041c08180030314452040b2458009c1c0c0008401d5a0780322001c03070007035500c2108a03046800038a041d0701c20381001d02d41942c0c01920b81d80380005601c105030717a581c00d1107000300b4407084c0510f450000422001502c4015502180c0c00c88001c0a089580000580c46031071110040d9402080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 696196915 1250 696195665 696195667
    0x5030a020910030501180912051c050108010b0a120309090c0201020702190302150406020a06050408160b070207080c0604030807020d08041d33010e060a11151608070203 74
    0x200308042a6000002e0aa04000a0f1164010030503018405c000d00b501c241451000d2120007441e4036220040818040c0302c00402800095180603040506281d81d6a03200104091149503594003210f406486d644141d940b00b00c402580000d08400aa018048569419180c0c1400c0700e103082c0000000300340d5000180b05554081040e6130041ea0b80404c1507101050390f010b00c4501c54218018084041d041c1e0b030607030038042c00800c003d001103500050032503400da5100102081c1da0b9030f54500340005002e4076000d066000381c50a0701104110b240c504943c42403249508a0300d0303195031a960179607100880c0d2206504100100020b0000ca0b012600400720389001410801c0c0203840d030707500c0e00b40513401a03010624500c5590003a0b007102000b100d030660026110620b0b24808812600300d0302152080409601c0075045c0c070783d2001e1042e40250300840860500070a0a41c81d0841050082d0410708031298001c42c501410a00b072615201c6ca41d01c190040b0348050700050028640030043d15560000740120040d480 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 696198165 1250 696196915 696196927
    0x90f04051c090801050702010b0604031101050702041b110c100e0a1502030310060203030708060d060b09150a2306030a06051e09060d080f09060714030a0f02070e0705030a02 76
    0x3284141078111000141d6494080d185840007880c00c440c0c02420034011641041080c5540740d40d40010b49080d00e0704110300c840c0d5400004016203880c801c00c07000035002810410711307440c115011002000441110b888000032032100318800c54807180e16040640d4450310003c2450006d5104501aa140c01409083c0c8141140c45103045400032903c2d000100050f132000040010182c504c2021200516080c00150b0035400d0440010304801c1c0d0041550b80035100d1480100240700c65500301001c07000024103e0300040c2040184813210140740c0c0102c50241d074100340c0000da0107022480721000c882c0d03030041050210f11030303508016040e4030241c140d01281c1d0316004046504d6488204802070020525000b0036500001018899404402007103144110026041500802c8131102140c20365605103c5803130355815024000f400e80d00401074040e00910314414080c184520000c01020300486507160461a100004400ca07070b0780c047c1b030051244a60104010412143c0a01c010715000710313030340d00007501b404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 696199415 1250 696198165 696198193
    0x40804091d0102070f15060608070507030e1008270606040509070e0c270d030e030f1603060b0d03050901180b031306050c040b120c1324030209090f0405 67
    0x10f040307a00f045d034010703110142c80710800c400e410030308030840622101404402d1034030fa00904914001400e120500c200050340a04042c4511482c580a1600409039100480e00d15802000381c54211740611191007000101003141c40700d141e1030035110100e0b0004042e255660400d000c0039241c05404007500d486071240c00b061105590011502c5000500c01c170756211594031065403080104920419942a000580c000440e201c442ca8110440d0701401c04240303040c0e203040030900e00303503080c030b80d24180d4061012001940d0806100c0392048a0162805000c111241c508012040008810080200f401000024040c1d406000300300180e000c02c00c0d40f000c100d0b035178801a480e1580100d07240301c0300d0042c07804120100401d5204e819003280032100700134101420170003d144140b0400305c0490081030454002440584403204544502035941d1b0302156190751820f0b0000b8200503400111b84140007803086a0f034003440303803082e224a00b41c0100039490b1612050095052060040c0003070b1500d014240b6200160 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 696200665 1250 696199415 696199417
    0x1b030d110c1e0a06050a17160c02220204140f0a03151e14010807120311010e0f0708060f06060d0903030605060a0e120706080c0c160b070614040804091d0102 69
    0x100113a48a031646d905503048000d00c161351a4481454000d610400d000401c104400320207410b0f0000e08115450140c0d40c0001140d00400720001304440c07480081c0c4040140340768014108445091b069100d43d0420350040001002c002e40b07116800c50b52401040022540d00035280700b01582402d4002121a44450542c02d001c5003103040c90727002607d801112520305c4010b64101d004110a0001d094000d06000e86440c100c91910400b41c04c0048041850210510a500c40116880f20008590400341d038942c40c180c41e1141c41c400c0c070401e400b0300400104404c040c0810540300b0440200300700c0c5040f548000f0000204600d44050b01090341d142008030349031316140003e10300351290340c8941c03002034036001c00c020403c484200349088c00d07000081d042080c0791300908c52039040380c040c0c0d41150b22a038136a0005c0e460034400b032500304000140c100000401b20b4178040100603640c0140c038180482d86040c80303c032040e503005940042c24440104010081014150301268080d2450705a48200c40010301c400c5003a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 696201915 1250 696200665 696200669
    0x81903110a0609030834090e01080a140c130207030c021021091e14070902070b0705181210050c090108130804030f0c05031b030d110c1e0a 61
    0x382c41c0e5400c1020700703041d00542c8155004001c00404000c2030300c414000d86640007210f40310340e1407044452410311500c1c011800e180142c1482d5445960541c2d456810340d40d241c0e510007013545d1804444504c40c908071004101100c2140010f003000040b08002c1d140c06009600080c0194104a88000000c0042e940c01804048004482e80d90801c01000c12a40349801c01401000407141e6162211100002d0340e508042020403013418040e074500701e40381c00c024400084250610b1242d0064007408214424182d014000c041d00803440001d00790f555250075141c4e44501d941c50801004102d804591601c0c00b1866104090030705810394017600790703042801e4141c403800d44040081d100c020442901a503405071860380e000c9240d080f195072000c000c0d19032071158031880c0000b0b4200e44802c14210184001d840b0a90700800018003156061850340c501528071080400e0014444d000b0794245807100e41c0f0900d540c104c03005000c006007620020900c1000410100327905648003a942901030803d05944170513040300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 696203165 1250 696201915 696201923
    0x3040c0b0d0c030e0304031e080705030403080c010b0109050337030c06050c0f1803011107111504082e151a040f05220203180c0a081903110a 62
    0x141d0500d45000a404d40b0340c160a9000668404d00080000c54140182043c041442110901c4542d00d40c0c01c00b21014801c999000d8110b10002500004120000c4010084400090700810029000d8801140d0000303440c440c403989640001c06481c20805a8000882008507541d5803007207a403031000522030318044850050340412100d880100038400c050103140d0f0721002c001d105a103400110041107402d8050089454580d4403a00000e102c55202540f112011003402d9004030b0301c074a5a840c008030194039144200c0e000c0d0220050310b20b45506c440060318103541a50b00581a0361208140d013040c000183c00540d420f402c811703130354045010211311404140c0310f40070007503071259803e1030002861000e8102d0b8131102200100002c00451000406540940d04215036044640611041c1141d00c05140280b80b0b03c480e100009000c1d0988400400c0c203414640c14090700c0401c1109030411050181c144140c0010b504071030078244001c4048110a0b080d1803180c100b44500000542402e072405406c554121 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 696204415 1250 696203165 696203171
    0x80601200312010e0c0a0f020304030203060c04082a040b0a0302090f1f180c0201020d15080d02061003030e060c03070302010225050a1704030b1015050c070b03040c0b0d 74
    0x2c0c18007140d0a80d5602400c1c0000c0c42c2d0035507052400c0c9804c101d104605e4a101045078065000c48203d209000b29002143c005003107c00c10b0406004282c1d1680c0588030f100d180e4031079501200c0c441c0c0481c1401201218000c0d04190001984e0403d10018041c401d0b80e01c0e6200507040c50200040c0c1d103051b5058059847c1445600080c074014264003c21981c1c4900c20640322620300013080b2084415010b04460502d1100c00710b006c11103424180c2c0640550315844041c98180100c160982240f4038043c02195041070456040d0952258141e803100c500b07903150010b200c008841031011900a10108800c403c001d0050f40ca441d42c00180c0c503045410082c1d085005035000103040281441c1f603444a8a48403541c80058090703001e6a41d0b507941d81885804c002c00e1200101c041308a000c00280a640c0210303040031840040c1e02d0b0800090030b000c4031501801d00e51003507620201c5034151007601910b48814842e0005d2024900780710822603190002441150791512040d40441c1107165130015200603074001e1004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 696205665 1250 696204415 696204427
    0x3040203010501080609071206060503010207050a0c090c05030a05092803080c09030615242d0a0309020f0d0302060402030c09091506060f0a0c0618030f0806012003 72
    0x9030a42d80103901030a5039a0004013032048000c400300d251422286d0020041803484403614100003e05441d5000c180c1c554030100f0514103111001c1441c0703030664400c01f021054243c54540800403207403101a44800103006000040761400154081a04060b000040350480c00b00c1145180800e42c0b5442100e407000608035030765041580102d406074200d6035951800d07007048003c102080d41c0700c0c80144207030000c041c031584825a07615400c03c07440d5100302c030348180b100144a03658040503c1d4404c035035496020044c2040801c40900c03041c1103405100d4550328440c50203451138421005401c0e00318081e603222a84090005559546000541703001c0e00c69000340140e0300e02401054104940110401d010b00c4801d420440e4030140818000f241c4aaa0008000d50f80c0301c42c004034010f401000e5032450b02e07420025142e00225005400b101001d4461103050081e1404414101d040d581c0742c0348001c000c112601c4d1a40c4445014446440e070242041c9000c29182d540072000070034120b45440030a405030400181 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 696206915 1250 696205665 696205669
    0x50d0c1805012102010c02280905040812071710031101020a2109090e07050a090207050d052d0301090b040203040b0414152d2404020915030402 63
    0x291039002880c068108074941c5001c0c501c50040c01291000810888140e0702281103a00a4558801040d0041c0490300020b40c021069013070701c8034004004010a0414400040986240c003c0300d06c031303d5200c99054106082c50100c60791440b0b0240c02c4405210303502d0300f01c20b0b80e10807602c80c0074401c41404040c2000b40b403450510034001c03010f0f981c5181c11900807030301e254003090880522145500d2500450103512883c01000c540f584002d411600c030b000d0510b40c6160000100240c00c4054403c03c4940103112035583c5481000c911030382300001d0054105030101d00e1054060300151240d0744410108803030700c044403680c0d0085000b01c5034800c104540040010710139500c0c00e10a191241e282998118a5402e154841002d41e03e00104000c01c40c10003101e561101d0581807220441c001b00c0c0d480c0e00c00d207500b03104419440102820301e004207003034942c114480405a1a443c103d00500043c071b4003940c012000144881e032000800e81e1180c0154003000070084e0b50b02ea100304600e1242c2403080c402c0c1c41c0c1c02c1501c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 696208165 1250 696206915 696206939
    0x30406020a120216020f03120d020306011b0f0303021804140a0b01031401030206090f0a09090b0a2d06170a0212210a020c0d080712050a020c041104050d0c 68
    0xb00d0082118814410910b01500708020010380e15011035041d2000102500000e1915043c0b9000c44d403e070101040d6683c1c03000b49a00039501840090f02c810700020021140000001c45066014003098140414840868082da0080140c1410303c03c0303070031107121854082405c0d40c1d481148284280190703010411030074050711038128030075005d1805004004601d96010050301060101030300c40e240000d40e8030015980e0548000d24002d001e8055024a1740c1c450b03490700144000325042d00c2c2c4c2080e240c005461041c1522444019007500000c02e02c4a94a104040d0078046081c03a130248440e40e26000031030510041100c14041e041101e0042610715030350720600400703580f00380729051a540400820703d40300c00741e90000b4610001000d0300030707110702f18420124a1b0520b009a40c503042590083c0314400d00403414024034076140507031070604070480c0341747c011550351007840c0d940f000503082120000d240385095084444d8240702c2511013070510340c840b800a250160302d018200c44132014000c003003101202d160 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 696209415 1250 696208165 696208187
    0x6020105060d0b0603010209150703031802280806192a05071a180c0d020f0d05070e1609080a02010210051f09150509010515030417030406020a 63
    0x1100a005a09199010400d82c45005000901a035080c40010300b01c0d8a0943c1541e141220052524500c0c0c09504800f0149601c024415030000e420070060603202c0300c2556403540074590246c104030840b5004088108001d21140000344003170180344001901c65030801c901070007051505008203000a04a59280485002d007403d42001300c604c0c6a0040b40209002c200000c1441a080441d030701c071880d10b0304500b082014404088415800c81c14001c042c1d42c0784168400c1900d002049884002250042101c0c0d13501504009511a00c60581500d0b2814100c1c04408074500c00c0301125546500c9107914030001d10211201080703100c41e200040d5081e40e00000003002001030381c015006018103500000e40791070195041c050b045881e40c0c041050040c50510081052100020081085484104071030145c0102c210402c1071505a110218092800309052412144010301c0003546d48041c5000c50983c0c4c2005006941c490f020124041c26486050000e41c4150320a00c0c006959800419001d00792038484 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 696210665 1250 696209415 696209417
    0x60f0e0603062a18090a021602130e010603060e1c02071406040302061603030b0415150c0c0e010503060a1802040e03040515040f06030c021213030b0f1006 68
    0xa2000d00600d5100801c03540e421941e0038004810310780c02414000c058102c803500310400e00400007000300341001c20010220403000122a040600d03240c550310b25047c2c1c020b58104001a41014035034000600e02080001c426061501c40801c011000300901c07421a02c6c0f41d84161940c0752110562100c0960030701200f00e118548a2102d0003984030740900a50b60440e6008203c001c14a1003a541700b95503070607040d10021a801400079650b04d8030021b4280c0800c08508080340407900309030b2100f81500e400d00171000d4080200ca240c01c0c0040c42d0400d040c1c0300c3d5a041c201803050100d01c905030400301c0d01d0030340e4600280c1101244441c45502d40414986460402401c6909440c81c0c402c0b1040c800d0318050400705400d404a0b008100180c601112030300798403030743e4041513000820b00a042c800c044a40007a07c1150f0158407051029070340c507042582500c8508600c800103030003101f42a0044024440170303090303640070015024481c5490b6501c003102c2240030790302a0b00c000084020400d224400d242e9a901070062 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 696211915 1250 696210665 696210689
    0x51c020a0815040b04110904050d030608030f1602060c030a1d03010207030e0108071806020a03030b0402040e072105330a05040c050d05070302040807080607091422060f 74
    0x2980300b604605503024200604003140d40011400740641c1080805503460300500c02d440a081c50300e041507540c0c1c007001080011a09000000803041000300c2500d515400d040e84180c07503c0741c802d0f40054045845002280c0c414414032070005440010006000141d8240e1a007100a8140d1820b03501074010a0440b01e00c26801004031a00196101c1c0e0303003c00c42d100c00e00b041c0c20141c07140b9400381c9480203070400072011880340d6038000036003950005152100314040e40301000307400b41c2c04040c0b105038070542c019801c143e42e03040c022a031218420001c85092505078150241a0480d040c40a01681c5040e90282d0041081620007117408090b503031003595004810008070392014036400800d01005035440f030035100c3e95440400c5001e035401602152000c514a69003040b030f620700260090000d4001e4000d58110748a800301c04208080300089460003841c460311a8440c0620700038240c020f280c00d03910702170f0f0407110b0b038410700504410000340f03010802610070300802c8007414076031640f12880780382d444015890343c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 696213165 1250 696211915 696211933
    0x3111303300c020301092f01030501030c12080d050705090108060f0a050f0f030105090d020f0f100f1e1407030c050f0729090105060a0b12060a051c020a08 68
    0x1c00c02000301001c40060902402d001c03114000203004080500300688024200b0a04c0c2d14031412030640503448080888031040714004240044046800174007000b0155074900009024048900e0801d07807980d481409054038000c0e1000307940341661400d88444000c104081034040043da041503403584d01131000e640002244540300300141001045200746405900c02800b200080d0720391010070b230070041000e4002c0c009414106000d55a55106000d05001406001d00318907000d100031403000d4000c0000070061941c00b80000150004016031199052103507034500400c0174980d102000340d800241e50810008048042400a40c9032510082c40c280c101480d015844040940000959000b4442d4841860329404240380040000d00e021660000c0211741a61070062212110391036481808400c000f84080d0b03d0b05e005122040f08180115600164181f241601520746001c44641c86000100141c11199480e000300d0400081801603550201c050a02070302541099003001340104a50001400a00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 696214415 1250 696213165 696213233
    0x5070b2a0307060b0109090227090106090303050a09090c030506041a0105180a0509040b070201060504051b18060c0304090e0c06040b072d03030510080d0f03111303 72
    0x4842d442006114036a50070000d074013a44640ba180d0050001480f08541d41c130714038120300d240c6c80051b0b1440b215490a2514000c100d040c80c50181d4101d07502c0340c503060440d60459034190780781c2d000021900704121b1101c40001c0d84001d14010584013010360303140080d1604001e01844240d45c081d0b501108810074a90502c04203991020499034080350510f207032070407428031000003000305449901096101c13504e00300b40130500400c17150080c042da400d074000300300d816035840510081d20011541c04161010f0747c5210014511054010215a920392845c08815542c2c44000781c225000703481003078203962001c18144648010792140401d050103400044c240041c100300064401d10070703800f4a940b14403010030b1000c10064440140010180415901c1d803040722031143d10041419031311025000a0300b840041082041d1000003501510385003400b814a8000910041d204284913450050070550b8507181c2d111081c0f42c200c064940c605141c56450003031491030805840c0c003c10010426820f85058845024107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 696215665 1250 696214415 696214417
    0x80a030b2416030509060307030518071409130c08060117030f03040330050406110703020a0206030907050a0905150109080a020f0f0603041110030209030a11060705070b2a03 76
    0x10324150034030300e254802c5103021901d40c0181820290840008030901000300c0e01900814480c1243ca1a042c041d658450300e181d41c0d0300e015204004a80090030014502810403401081e0302126880c99154103082c01c4d0380c0c0c20325008850b804176032143c01c40b5006204003e00e620006900c00300407001182070568150901c802403002030401000e110203804102044007640c0f074810b5001c0c04180c0300004040c0a008000013400303044404031107840c641081d4010000d6041d094800307140d01a4010410707a404da60034000113500c0900061024410000c0c0054542d44950304400640b020030b00202c1e031400d05209040c0c0e0b41c2c01d60301d012814404a1403082c84941400601054041c0d01102c80e146003208003808070b6a803400f04020305802800001c00c0105000304203018410320f010030b6614000f0540c0342501107080303005202519038103801c101040408070b84144481850b550000384100e01e040100d949051a207081580079503000d41003caa001c3c019280c11407810308001d905030b0500d260880c0386030f0594036 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 696216915 1250 696215665 696215677
    0x30204151706011d060c16240804080703030f0b04020d0f150b07330b010f090b1e1210030311031204032304090e1e0a0816080a030b24 59
    0x91000400e00e81440d103010485c1f01c20114500c0c400c080307940c0e01d17100120f040300d51581141c4000c2c014040762303c03260352092400c07612a50700310305401d04200c1556821070144c121036040c001040c2e00c8074900c41c21655644001c0003403133008600001c4802140210200340e43d840164403000b8940003404010f1040d52404890001d0741c42041c101e00880c1d4210121a4000d980c8159001e8403200c200e20394103408594005200e41c0f00036201c450003a42d00c13090449452a0501568900d03103018014513800c030403120701c4c840300c0840340c9518904200000400ca00c201204980702200c1150190081083c590407070491074140c2c41e0000507500d0300e00d005042030700624003d00300030100086640b081410390b1090440381200d0180c001490741d100c0c0e80315600c6026007201e905407080c9001e6080c0d411802c2107468692649022004080d011451490f10f030b00050b500665810a00341e82c80e85400d0001540d9600103110240c9542c8000410b0129903091101c0b80301c0a940c4000c4c0148602071484407949440281d83c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 696218165 1250 696216915 696216919
    0x4021323100809280209090d1b02121209180408160326070215061503061c050d030507030c090905060a0f0801060503120f03060907030204151706011d 66
    0x20791500c8040c0701601d4503459280b0040440d07402100b03550f10b801380f65500f58903d030003100c8070b81168454140094580c618401c100d03022584034102d0186034020920b1110441c2d0006000003161301c5054440c03400c0c060301c241c1c0301c0401000004e0450141c5880202e200c1411031003007a60081d886c3c155180e95492181628030320b400360055201e50f013018422000004608170724004040c8420007005003a0602c4070603108140540281014004400c458003501131158200a0100c0b003000c10002d400303407060f400609802d4014840540320410003290140c1150b41512410040071040f40381c1900400b198409040c1c4020141460021500c82c0e51080840c010358110440028080d02d4120008446016580c4103000c225040c400018015a06600076412501d0603400c1d21101040281960400e20503034003040240c0f00244082601401c001f51103603408419402c00600d42512900c221803a404041e00740000640084000c0702e1003940c02c1300544d0400000c1c02e1107080445011125401001d200c00c2140c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 696219415 1250 696218165 696218177
    0x309030901031a0301020a0f0f020a051f141603060e011d060f120a110f01090b0306030a140610050109141512040c2108031f03020402132310 62
    0x10014000032480c070f9110207002002156542000d800181042c05910554404250008140021180003060460009034820090901980c20000b900f0095400b505015401070f51348045203600c1a101252900a040b001400c11803025115401805d880c00750b080800d20051400042014a01fa9001c0ca2204204041e0304449651070402240c515001d90850030b82c89100c0038101421000301066840003d4003400126040761075950038813024001d103061050000d400107030200201c119100c0615080310004040d281c1611458544c40800130070803903040016044901032040c00d420000c3c040b8010142828a600760a150040a0b1105104c4044036405891041690042c1c041502c0403100e91480b0b10f1112502410300307040108442c4c0322400740003e0a14034250344140140341c08a01e94009038040d1501d0710f141c2c0c4618502600b4040a401c0c803020390403c80001c0016a01c070b0015100702d00140800645c81d1380307442142c0f40c1c085034041041c0d022075050032401800340c42c1e462648241c060b80f03003048 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 696220665 1250 696219415 696219431
    0x1204031202120f160209070507230c2403191505060a0c0611030903031b0c03090f0d0b0901050702071a070303110717070b07020105240a0e09010e070b030903090103 72
    0x120052000132070000394894a041c0c20013590380e4005021749000ca000300313841d80301014000c4002141182c02c2c01003003060350141d042400070f0f00e4400c040e007951031088c072000c0b640031482400d41804d6402c143c444103082921080d0400d2003003800c0c8211040101d1205414250304d15140108042d481208007802c10004006106418400303a600011080b03900c0c48406c40d92071410801f456280e8206032441c40703030481452280d00c0c022203031009503800701e68848055450148904200407600d009400d1298010005610810105107841c1002e44034100780c0e0004142441c1880d0001c2c05e0140b02d400c04045609006d502c00c3c022240b035070689683c2d580c14200054603c1d07500c0e400010303034002c0c54001041c8014000361460f105042c00041c2c070a0902c203036240d040381e0306d402400f0b03420f8030b02c02c59803000c8419a04100744003058070303010141140b1002818000b0a1620782005a01c08102111441e066a454541c4d00022500800140005040d894036041c15030034488015500ea104010005041603100e13545 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 696221915 1250 696220665 696220687
    0xa270c170c0d0c031e0b1f080a0317070c0308040b150a0f0e0f130b0a0b0303210106020114070507030306180c030e010b0105070b181204031202120f 65
    0x8040740c040140381c405003940c6031070007000070b41241c08201d411488221002100c030310158009060150301c05451340844c1d43d00300c174140b07459041c10f003042c02e5075121020004208505005055055003c1d42d141461281c806810b2004802c001d01400304010101c110000440ea00c1076809400c240c0c8030700b401000707480d20304421944d510b0032516583d000d8401680001e949500511801c12144030140e141c0e4141e07901c00e003034100c1000403103001500802000d811070011b5107640a460784942c1c010800580a80e00c2c0300840c2c610341041d4043e0040c011021603920510210703d0360315006100b83c1c4000d0091505d113040443c4e0403400030b000801440307400714404003010b0080e00a44043c0c40034606c40122051100e080030068860000c8071302c04a4545a0035500805041c010701041c0300040e12100e281990680c1e90004410f070081040038124604911545035910600001071048010542d090b100c5065003060543c4102008907001994008403041c0c0c0915600c40c15107e035961586001c0f916085107641c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 696223021 1106 696221915 696221923
    0x3140715050a1b0f0b0c04080c031207120e09040c05041b08070f050705060f07110118170d150906090603150e0f01050a270c17 56
    0x10100c0c00703942c69940440fa0070780300711210b05003034140c4d0315481d1000c0320983d51130300340c00c00014040001c0142040324489124044018214107142161020258410a070005107150340741178603641668001d040301561b6603000307400040146001d1420903062000c0d809564071840c58800b01141c4032150728928000008941c44d008020f40380c0e60010f661140c00c0c0803921701080020069440011018806070b4082e01480115141900307209501401e0150f05800380d1205a24001080c0c00b1485030100d06024140c01103070451010945034210340301442110740c0f802c045801c0c40782012400202c4400c80046400c4500704110058540c90410291621407002030540d503c44008000025501d03880110003840c041d0440d01c0e814a1803801a0950b8011901a209555074002c0403003500028202012030500140b4490350f4044180d9404040030a02d000b055040803040e0480305282800704 = true := by decide +kernel

theorem cover : BRFrame.Cov 696043165 696223021 := by
  have h0 := BRFrame.cov_init 696043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 696043165 ≤ n) (h2 : n < 696223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
