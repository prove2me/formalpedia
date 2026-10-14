-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2253
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:08:23.47027+00:00
-- url     : https://prove2.me/submissions/9232ab7f-8732-44be-bd2a-a912d8284a3a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 405035971 ≤ n < 405215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 405037221 1250 405035971 405036031
    0x220b0d1b020c010e270f0a0c050c03030a150b0d06030309050d1113020f0408070f0b04080d08060f0612041e050a0f02010507120203070624140a1d0f 65
    0x2000b9074405c03155600170039403e00c00b0b004070310404205032280c10030301801800101c07110f441380000071820000000070030819030380b80c01980400191030348100300080c00b40180c2c0d0001c0094a0a010a80700801e4541e42140c041d50880c030366514000765120410000d140d80884d0810003050f050300c004810440c5500c8580b00043d58000700c42c02601c95000c088401002a811600ca41c9409409652902c0e103540c10940c40720414401c40c400c0c11443c0001041040e11076044804444210004201d00500c84c8026030314441c000300702e161300c052002c00c401ca25403101d4004201c48540c45265852a1030710f440c2c6074410b0301c3c8004460f28030784a002c581c140092000210300e0000c0350400507281c440c0502d84012111840760103401001109a00742d18620640c00002030702c070301445000c040c00884001280e1070b2600d84c1c0c0203209040491400740420482001c0d1801400040e00a0f101980301600c0300204600314503c8810021510944408c0194a1114011043d001450240c050184400340020410084 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 405038471 1250 405037221 405037247
    0xc2103120b03070501180b0712030b0103111206030a08041e090c0801030822060503010503100b0a050d030c0501020a020d09060c0809060d14090d0210060b220b0d1b020c01 75
    0x40b410b003081141c0005000e1600b0010007255030008d80d241074a2034117801c040b140b4407004001c039040000c640200c0d0700074000c000200b0380c0b801e40c45003400c0801018048000c000f601007501406541e17001c4010402c07800040026004071460701c030034404c01380c0c0f00c8201d0000c50380c0441509031a141c406004a98402c200d10f0440744c002d501507450b5460f80d64140c14039141c224039003c50007040a00051030340d40003400341d4125041101540c420258a0400a0603520001c58056005c4682d8405210614012240c0c40c0c00c03138000d152401024500b943c0d4682240d000700e140340051380c40002d0313004078603900c1180e25018245c90710780f02e062080d82d659180c01c0c50203903480702c2d07101d99008610030300d10b02c44903884482800145106480c090510000c1d1545400c00309003a04010700400f800f03442d801017039004a004990000008501d04000c1d00982d406040710304010503040852500d001590180800c044c194284000a000610203604050100c03911b403a025100150742044080c460240c1e000142c08501c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 405039721 1250 405038471 405038477
    0xa020f1f05060a081c0305011202030706200a0615060c0503091302161a090c030c0609011b0b01050405150609010f03230402040c1403040602070c2103120b03070501 72
    0xd40c80d0103001480025aa40000d1302c0c074801c40500c5240b415540701401c50b10002520304100c1643c80740d02c030b140c070480c2d1180e0180d01503016030020000240300e00b5040003440700c0200318010201e11688101d05000c1111401e60300300c0e4445840301425840102410010801c504051821011640d01c0c1901d038003a2180e0684102072818082c1d0180b501c5030100d945800140468880f100301600e4841080509809401d0383d80f04888001403100500080891031340000800801d085c258460800c030300c0760720001ea0141007006070b01500c0814500729011074184ca10a5019420540c1020b0038402241e200034959000507900700c00b0004035071204800c4441d014800c0c6840414010f4464003503000c1e140300c14024918070b486000303010042d80450709840c052442200e09000034851964110340d0b00011085d0350712080010004500050700350360003007200c40e10600d5404007595581202c80d01e150741c56840c141185200760503840806a1000c079282c08460005800c0001400d40800300756200d1260241d1418 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 405040971 1250 405039721 405039731
    0x3010e0c1e0109051003020c0706050a090e0a0f020a0504140307050d0b04030201090816020f06030c03192705010c080411191a0901020d020109110904080d110a020f1f 73
    0x180d9110f2003c41001d8640517026804426080000500030340c0402c0b0103c510340500340d0041601441a03088a850314015690f00601c02d003042c001007018100500483c01c155610403104030a8400c070700250100c1940d98440039200c4d440c0c071003061400420302001c40e200340c105140c107104940d80e00c01d6281c11a60032004040c1e0550719441c09a00400501d08090b09118001c100a1082c2090020782d861086c425201241c01021440038000c00307020a44000309410402d00004190341c1ca469040d110703295032000c004c2081790282c0c2c01401b64142a0ba00c140c08007114904000520000b4002e0074003641413450036405a107050749030010072418038545a4414a8130200144003611031000400190400c1d68046d60621030480c0c2e500055400207801d240075014441d0b440d030301781e8010300c1a04000e079004140210308645000402c046910024411950780384140300d003143c40c00395846590300504089034182d644140031203000c0d140c40784601c0c6169540d800702100111310340d1288203544c0d448078582c8001c12 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 405042221 1250 405040971 405041029
    0x91a0d090f020414071704050640140f06040305090102010603051c020f06010e0c0a03020f0d06080616050f0304050703020306041b09090201171f090b03010e0c 70
    0x450003802a0001c2c3d40a4101010002c4402c040e1122a0198413640c9079000410380400c01c90300c0c400c6c000c0f20040c03c40d0300800001104d05501018490011445181404580740004488501140405c8202010000003c24001004003051010040d151490000c180c3d00200910302a03684200400c0101000b40102c4c0c0c400c89039000350010b0024552100950301c2e140e2680c01e40082031040044e08000503c2201ea9007204000082500380c143c0c6d62a01c81000d0745d507500d4a201005500c69802c050806900300584c0c0c0c0400d072004098070400b0a04240447d00d903181030003e0340342100c05045074001e119202e014611041e0010112940f44141e8900240c40c3c0e038882c10014107003000e80d40081c2d01406000c0400c030030042c0c0c01c41c9140046501c5500408040d071035800e00d50494414010013404140c1c0c60300e402c50b210058031001c0382d0000751418000611b40c0301e0b240003140c100701c99000080c1503480b00740c20f241d586401c3c016408000410380041440307a12000c00070f85c2400d0b01040b0800c010508040c048 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 405043471 1250 405042221 405042233
    0x61803121d03010204090b03060c27221d2a180f0412020a020109050919111e09150304030509030d050c06090a080406031109130903091a0d09 62
    0x50070058001c0086458958680d145e030060054584614424064480005c100c09038603c10341e820340c8004a038030303907038050940a410b641e4044165665480b010101e45c40504841c40701120310480f0b048100891003040180d2690988030001040e40f103070780c11813143c0c144102c15852110045c170100f2681c202900c445000030800402ca480c402e1008507015804012004a60290041c01948100c900c050030000c00700003203032560380e1010b0003030000d4a030040c01c0205240145845410a5500600007241ca0320703c0101012540b80c01101c1004920200342c107219401692034030b089008801410903c1c0c1045032000403046240c4401003260703840044003160031f15100d8000d6504003540641100d616081c011800741190700700944068051045000164044001042070b1454980c400d08a904007400c005055018103041e04c82081181000d100340000303603869103070590b80110400703000201811a8200107000b407545803c80240070b80ca0002d0580085038010071201616015030300010505185c1ca020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 405044721 1250 405043471 405043517
    0x30c1514090d14060405060414011404201f0f051c090c0305030a051e072001030e0a0606170316020105070f06140906070c030801170309060708030106180312 69
    0x503060f03e1042404010400c080029013a025900801640400b0080d81c07100500b62104581100d04291014003c40c0019a0303034103100d0314840b56030200081e950481800300b00c1c1c120b082010303148049501c0c040c80d841c09800c0520039502d9856890070038034041da102881d990854851096907050365481d202c2406101146984201855125060b2562440c00c240020f000360006008885800c1c40e03070303aa0860210128044415461344000c405483c40344001c90003c0c9240142c448606040c1c607000c0008400350b050043c02d0501d44114400208182040d09141d0100d80038034051000c0d510070840725a5426101801c1d41c04680d092806569400742803070004611401d9080082165080c8664005d84c0020700d210340c4e100746002000c8564230740e1180c2c0200c5220160803809000b00b150400103011b80380c1446240c101c05400c22081740d01d818001404950140e01041d400d0758040d4011006028155010b82203040102c0e80c422070026003404d41e03d4100103100c0f0744540c042407150482d14198074582e0341c145 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 405045971 1250 405044721 405044753
    0x603021c030306080d050309010609180609081b1c080601080c18060301060309020301051b0715060e090601030b0f100e07090308212520030301030c1514090d 69
    0x195021117a0404010b00745400690b95840c00c2d508020001c00d000c1d4491140300e54048140c41310192526071512400003c0040020698421008220701318800001901c041000c0d2001001000e0b2407041c40c40804405110040300350402605905010310380c1e910003411600200c560881c6da41d1501c0310009800160000380030711360006404000014480e030907a00000f40f0600a0f0000c0c032481c2d48a0f0640d00c01940c582800d40031032882032001c90007144400b00c00c0ba613103010254002460720380f0f40d0039034110b88408568080c0c1d01e91000005004111850344402d400501c070303c400681da0305043c0c1c4c07086002185401041d0344036003084009100c0f05e11a840b4040115000b04806a85d40703600c05841c1400840760f0030b071025107405540440c1a0fa0b5580c200c3c00d1071000c00c2615841890703413005003283e60380207072010707003181e04000e44681c8050a41403000310b009601c618203d0445518102100d01c0d96503050042000340000d009964101030b500d80704446901030205c60b0241003140510f410704c402075080300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 405047221 1250 405045971 405045973
    0xc0b10090c050c01140115110106030605100810021e07061416030b0618040c0c06020d1505100c2d080c0624010c080904020703021b040603021c03030608 67
    0x30790703500190003030028800320120300000c2c060650b0105464030880420301c240c8880d80b80ca900c2068105204060183c05042500b00108655039292185001c1e02c10a440381b0b5071000d1090420005004c0c200541e041d80b000494007036092844003401452440d8012030005c80c48417002443c0d81c1000030740c1c0e2003e203100d104902038003a682068030300705004520004008011a1500100001626104080d114030140c00161041e03114040c1c0180005070003500d0080084c00f200b0300425000840c00e002400c95004080701c001258034901e4611309404840794481c500428200700000c00d410380c0416040d0556402944c0100c41c00c184071009403290304028a4030000c0c400603804c103401c00c00480001c2002001c56000ca0321030303840e01c2d00d00c50f65a15000b1903511044007082e0075280154054000300350100d004580b901c1c24820300740003103000d0f640440c00460041e000304e000450002c40c821603c0050003410f44080042e94210307408039941890f450694526445404402000c242c4282c10200203007420720 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 405048471 1250 405047221 405047231
    0xb1803030712030c030b03032d190206131a0601050904020f0408013b030d020a0c060510080d0e0312040f0f09140a020901110609160b0a0c0b1009 64
    0x30610036101a01c02d5600d2000a08003090001064800d0045281c0c4000040165142860031110810464000070400403003030f8041c0da0101d21281501e010b8444003940301d40702d402c500d2405200a081503401088907562545044c3c0801c042411884441c4248140450074481a119400161924012514482d60103800001c07441d034420b004002920890f0161030082c000c2200c0034450103c41b0300c0d106d10005913811604200a201140c8446000d21080a202a00d150110144070007040e64409807080b00401e0503103914204126480c4151a07208501d90035440096007003c0144c1e0700e490311030320700a0800c003003400300842c9660203008203420081c1e900c0c0750ba50f80e41e80c5c504071200601042e100d648a00d08484600007129042402009403405c454600424a0340d40c00311488000c0d04000203860422500800028520008001c041d0140020a0042c0f946a46804a03001c202c240d035008040c0361a01171103583d40c241c0d00881002d02d200c1d40b0400140c002c0da201c10700640d102285500c0300c01030f41d043c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 405049721 1250 405048471 405048473
    0x40b06030106030915092d020a03080a020f0a170f04050406080f060a0c0e1203070b0106020717010908090411070606300302060c0c070807080c0f10090b18030307 71
    0x690200c0700707103480b5910380c0c000100c4002005d03084580c1d100b8060712002c2c40c9a20301801c488104403039101c99480002650780b880c40c41e0040780d103908458200b11544100001d8040c0c10b203070100002500060050010080c80015986940000c030310381c13408001d5540c000c41c008980400300410344c1d000e00740c0503104000d2107035501a03e46d07a0f001940200780d094040c1c4c001003000b840080c000d46180c84100d80716841041d8085050207500c044203404200b0501007400180005403683c0d10550003000181d0042510609003c200c02c444104203007294000e030b250080c9180014000c00940c0c4003150115400100e006c0031000c4440f19116980c0300605a614100001c14168560005200c0102158601c9208049252505030500c080800041c0150340314800082104040900402e0441c0c100c0080d20398055542d010b040c9001016040301610b5048901d60250a041000d8107250500c02154024402c400b6228013400c0c05c880e034020000b03007220000304e100d100b150a43d11040d8401c0003034202c1b075440e03d20b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 405050971 1250 405049721 405049727
    0x4050c1b0a03051204020402040509150f01091d091606090f050f03030d0b060c030706060806090d440612010b010906030e0114010f0f0b030f0105040902040b06030106 73
    0x100395640003442158600c0c11503203210014200e10419071584416240c8000000380c2586520024000c0fa030007a002c10001c01d50b51900c1a0850245040100009418800d0010096001c0740a4015030410030031600c1080909000107048030500d240c40e44000140d1241070f843e46c02d092060f5042d0749010070008000803a42d5000500100725103400400410507503d03541006010740c64032039010f506a10510401070a05040d6001020351503004050314900045403440c1400c0d46c00000050318850b90301c1c0c82c00c10400342e081c040f882d4400084c201034809242050405048140024810900000f840350000c50000c0d8690088000c1e01d20b903c507201200181144402e031188040782c1c11401040d0000760500c0303034001401003802d1064140c40d00d070161414a0720440060900c03404002c4699212104450f0306102c1e0034600340a840c81008881815080c02d280d50f00b4050b0b550b2100c1e032080420410061080c030100c2161313064030f00846000c550303031086000280182c803103005041d601050000c000184150 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 405052221 1250 405050971 405050977
    0x9150d0303021308031b01060e0402060d050a1508031b03071e1401050a0e010b010903031b0305040e010e061503101205030c250501050315010522090209092401110c04050c 75
    0x5506c01c000e002d49074440000b419502c00a50f00290090024045861101c0c980e070003955018841c882d000525020550107112144010382c0601d507190000910170901482001c445807141807101c0c000c515080c1c15035298a85080d907404d00c04e02d0b100c0225004001c02282252103180505128020301440c01d00d01d10000c028401c80c031401600790300c5c3c004080e0180d409280340e07a04807505a100d00d0280c03415400ca00d01000041030084040050030000850303241d10400d25280644680c841d4011145440030500c40743e00364140150920b1813082c410406074460144180c0190341c0103a2060303240100c07520300b8034070b140140345894110340030b8509460710540c0401c940d070880c603245a500801c81e6955200541e0036120541d505031000070030a004400a501a10007800080c001d00b141a400a1179180d820326104950707000840e8144d00010b0080ea20702d806081150840011030301805001d0301c17021900c50f00c0300700060103810b0040c030101308030a10000f80300c6821080c0c00030340184200e2425128600703284d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 405053471 1250 405052221 405052267
    0x4120503090f09250c06020c030306040525050a0e0d03080601080c130506070203030c0a050303010321020a0624080703020a1a0f090d0f0303050609150d030302130803 73
    0x310403402c0d5022901e04051818058a030120b0704d0000c00c40002d1034011a210200c601009100d21601c4120000e0b04620003407081041c103074080e54503820f0440410058035030182c582c18600d50307035040c0c51125072119582112041c040d41841540c1d094411010f95000c50007203442a070010021200348289034028000303910a00c026078404915589440461070f45000d08c01d00303c0c1148002d0181400942401402400030034001812a803c002d00400384520f005c26120080f02d01d50030104c01041049110340601d01200c110315000301c043c2402e000001d58803414404081e0070719485403e0b11038000448001ca0364248044050341020544900348a541c0e40c2e0107100890180c00f400900042d01420320400d18203450740b0000c071030f103055418446550250450b011040e406500002e0600c0000c03404800400402c0c420340303010440e4a400d008002280800404a5400c0084074182e00c0580c1d54881c4840c0f041a454140182c403200c1c00c440c40701041301d11781c000c01c1d110320000441c1c042100b010b010403e564 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 405054721 1250 405053471 405053479
    0x6010306170c091b0711130e030c0706020d08070305100305010c02010903020f060105030a020d03140412060e0f0d050d0207021c0506011e0302010809010b0a06030204061803080904050c0412050309 86
    0xf500c44c07000409840c0032138140b18070500000c0c000100083e2601d551200b420750b00404041c40c80c600d42da4004c084420343d0b080450f9644c00040d40e0345001100b0b205840c010300c01c40c00506001850501e01508542e0000c1a1204056407000020071b00000030245002440c0c204000304000c4000c480040cac000c011030903040d03015108544e0000e2004100152003030580d070300a00945400101e560078400b03004518203085088c000d01d258600b200c0d140f0039001d800104482c40d203075003041c0e0450601d6030482e100d0a0034071800d07030044c03800740c2002c20001400c04492103551424981d9000a8500c0000030b0061103002075220380c404a41500405040044c50452070003142601c034280d98801815510880b101004620084107040410156010b8112168069454400440d18841c80d80004011841c25004000843e030302260500000e5407142801c0b2048250111001d001d03401c46e01d03110716500505035814032a503100c82c005060f0a0901050383c00a20080d03010507012822807400b0361712034101d85046030003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 405055971 1250 405054721 405054739
    0xa06051f060203180418030e031c031406060a02151801050901020a08090f0d050913090f0501051b031302180c03090d0503040209060d141207150204031a06010306170c 73
    0x86460280314046c000c88988800141c543c003507a9098500701207004c00306605001e66000b0300d5103e9903090f54045182030b2640c0001c0e45907804070040688040c0505001d024031020f020451031182c000483c8448207201444480d895036800000320764522000000700003550921042c1301c124101500988480c0400303460b0300103140e4602e0011562b541c1140424400c6600072217241040300e02490081c021140701404624001c4008000f0310143c6d40b2100044440c1146020300e042800000e00c0b800350402d4507102c0c100203030b00c40c000c2c0f9064907000c090320f010f14941308a55188210355a11100784039401d40150a45814641400c10201c182c00032200c407125801801c00119007984603004a034480c59008200c1895600c91038140050b02041c0201205c418100d481c00d060580005c000c0307a00d4501002403825690910791501c0d9483e11010400d040d030440c0140000d00c00160404800300d40d41126170764106803030b0348440048000c1c0540707900002c0114070084c29070003400c074086412030707949000782d6440b0301c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 405057221 1250 405055971 405056017
    0x150d060e0a0e0d09030611120108060f0f060102070303080a150602060411090c12060a090f020c070f0609060c050c190801051303052d0f09031209030a06051f060203 72
    0x203143c905440c14540003403a100c3c0c043c0006500c90340490309401e800384038182001c1c2900400c014009081c0c00845180d07000604003c401d0316140815980081d034001e90301514101a40042c0d034030401d03800003c00384401c00300040c03000310003a844140c440350242d4101c0b510503074590010351140c0e4250307000e46104401d062844072070b003071179007030680100001010300745401c020312103444005001a01c060f50050150760700003085039083c080d81400842c0a0001031341c400c0400c0020f482d100041e480842c0b02c2960a40401815401c20482c5040b1a010300b005640151103113051800c00c0c1c044031030568403c00500f040320207030506042c440d0a85490100800c002e0301c2d040c101118083c04a00c0080005004208004490b04031400310b1840780c40c2c0ba45c1d03422115540891113800f40d0802005030509281c013044903015442c0400c903e000041101204901d002d4040e40460b440741c1c90f07200050f0200740c9075008590b20020440440d2070030705418600c0e1892075242d032030003034680c1d00280e446103121103008030080c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 405058471 1250 405057221 405057223
    0x1120b07030e06060103020f1e0d150819020d050d020a060c02030c0706030f020f0714010c140904020a0e0316090501061407060f060b03130b1803030402150d060e0a0e 73
    0x101d80e1044000f40229a0ba400044000e58040207804012450072720074114940c0d0000840440c440010b2041074413200030b0307000c1d082203c1010030001d0105061800c2048015070100369100c14045810503a200c0416030300202d0624443c5000003802c5100f04017011200076408507081c00054420f05007442010065441280d8900a1691007170007078000c11020490507020782d220314002614410091b0800d410f03001d1b880b03907a400c100c2e01a201300c00407514894540d00c00b88250807505080b42414010503034001503401040c0030712109140110f41c00200ea05070240925010800008000c080f14440705c4050300003404c3d00700a2192040042c1440c00102c0c455005403050000341d070740c0d484147d00700329040d00c50300090803e5400d400d02242d5184000b090f480b8511000794880e00c0e40740744070150071300c5034034295185920091000044100c0c0006203010001e011049a0300541c0480da4001d03400e4030140244181d1040c00085007100389410800146400450701d10340c8603030310700e250800c42d0f40d4000251b2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 405059721 1250 405058471 405058481
    0x3030603112d011e0c050c0a0806130206040504062c13030c0c05090c040609060302090609120f0303150103060f030305030c1305040c0c12031416030209040501120b0703 74
    0x1a4004400c04002c020a40780300655422400c014501038241c868007082c0040701144e8400b0140000704413580c0081440350401c50701d040910151140700c0f0b01440c14070469100c00c0085c001c40400070741c030b14240c3c040d580d40106072805020014410403007190354034203160804946104003020803103502d128107001e0740c03610380c9944503010180c2460201905a6404c4a00a007480c0048031380200c5002d0114485c1c071580703040341c8901038683c401941c0d1801c01d040030b080d080f25070f4884400c060041200403102d85502c403d803103c4d103005480651907402864407150416000c5441200288000300400040101d02185100b903001f00380c03800c01c009602c616428132501881d00011380461801c2021840300035120000b01100740000105002c411788400004041d0346603c1706013000034039a14821030a100c003012044035116050300b010070005c1030b00001180c10001c001e0544025505941b203010743e05001e60101c80451000901c100702940e11a01b0100c40380c0c045400a80c1c450140900262543c0d000e4071070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 405060971 1250 405059721 405059749
    0xe0a0b01050306210601030b0708010e010803040501052809051002031e03180d0302030f1f032402070503030121050703020d11100905030f0a020d060222030303060311 73
    0x1910b245944107018000741c92955141c200b00118034800f181c1146009218042c0030b184180c0100700d0904107200c0c010324841741038001011071884900100442c900c00401c5804880c420308145494555031410004102c110f41200490180108001246540e0014000c03041d16801c48611020704101e0000303c2e524041d01d10480c5001046809904000140101455100800d01101c200f80ba0800c2d4030642030206188400020a4000c41405901414503000951000f076450301c840304a0b8070b044610458040521000d4180074564164940304141e0b80948044003040f080e0030343d5520081c0c03904c1940c0354002d00c2003007980b00ca001c60262001151080c401c0752250410020302c46142503408002c8000021041140e203c42111001004e64407801000b5501d0213440e00c1d65410549440c003850706158030403d00c0d01043d0041c24190005a4540c04990b06040e040b800041e290f07038281c003e170800500c4146807200c0c014542c0e1000010140d15812140981e80701c2c800300002c400c0d12200340030300380c250b07004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 405062221 1250 405060971 405060977
    0x100c021e060a051b04032114030604090839060408300702032218050903071703090712080a0c2102010905071e06050d150e010e0a0b01 59
    0x1000c14040d50003a0402500b22000101132224001580b019102d1580302d54011520a6001c1030078030b030821041c1c00c4030030501080703007000c080048a40510071202e200c001c0c1114031039aa41d451210071303c00110142e03182d041e03102070700c1c00080c80ca2080c3c640042d09400e42a000e0a1240504109809004114140a40e13400754140b41040601d40c0c01d445001c800000114255481d4a4000102034020030003602a1146402035030b51164140035580ca0421000000c401c00201d22404001c0720b0702c2d02c0002c0440d403850407000a020748804298504510070400301520803902004101c01d00020b4000444c040c507008801c80b9480d03503031114a040b44c0845110050849901072046020407801803028490141c0304410b40304d2456850740401e000d4400c1500034400607075503080381c1000c2003000c01c099406000440361800c40c003c0c40d20f112400f150704502a880c10484003107103183c03801000b50400c814a040807210294440d48038120000142000d00c2216000f14492000c40c4158016100e02e0709441030680d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 405063471 1250 405062221 405062233
    0x9052d180f1e0102090609150910080a1d100b1203030711060a050105030c0402030705090901030602180415050d14071d07031b0e0a0306050405030a0e01181214100c021e 74
    0x1f040116440c52030b51902d0a841c010441219241c1ea40960141d0a804a40380c0303d0850911281d1030045454000c500102c0300c09210004000c01d100281b003404444c1c8040012400d45101400705115800150050600e8800030080c80b039001d412426400c000d02d80c3c1400c4811950790b0820050039100c0a12481e901504002c00030881c60170150021a03002e11142403140c0343c4a0000c5c08592545c00076070055450b80c0d0702054004a18001d210900042041214180826050142401004003442c0304061103000341400910411680919000b0900700da40705984000e982c90b0705508540481c0c0700301500912251002901c0780c0d009101d2440d40d2280c2107140701e51200f49030701c180c9610b40b038546496801702c08404000300107651030240501c01e501ca00051074551902020240c2000065444141400b440540b00c2c0560882c401e00d010407940c1c0102507070002d0f002418455503038840040007142078022480b094103000225044843d680d0303095801c41c6c1c2680b1498504407580c1c0e80f80c44400035540c100d8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 405064721 1250 405063471 405063487
    0x6062a062a0a1b0c03030f02010b060909090703021003020702090c2a032b060b0913050601030902042c010606120510120b0109052d180f1e01020906 65
    0x40042c1484100509001e1020118801c03d040c90104260049a04880c082c03001e004055000c0c03201c4044440500003404441008400688070307000d8a504513000d060036100084031501c0400c9030178000e50300503003804202c0031143d800038045e6000940c207900403041c06000c20306094594080303450717080348011300d50a180440182125000969540500070b0304c820312501c0d6611410500103441f00d0b04079212002601d10354801041590f00720b500ca14088a01800a44a5911404400400318000002c00030362650b400006030002e01c143c01e00a90018a40318500f0420140c007a030181c40100014a003124245400d41c81a0907074055028000004150703841002c825080e54000035000b9039140300010405480340c00107520102849015070700c0e03000d10001001034600500c50141c0040c0100b00b1031140502400718840c0131480e015082020050800000c1d440c40f0300032004030305010f8000251050031084a0314140e44000040e141ca400145110428124a030144210750790100041e080c94181703a01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 405065971 1250 405064721 405064801
    0xb06040507030e0319030b0603010b0a050c01060906172a010c0c0b070c0e010b040b16030c0c0b180f240403060e0105010303170f0c0306062a06 63
    0x141a240c00e150b11920303891105078044c0054548402050709030880d10b07400000c000c081d24505000306004080410040c80450007040480700401c03d503041032940d40b8140620f442c0189819804031103402d00d4060081458005c1883d040d824141c01811a00345072200c282460310382c40342daa806925407106c81c1003410310303500034549404154015080e5070001a5103180a54407513001820450784544e10000912400303265024450140c141010801c0c00c050a09202c250144509072031440841380344a60881050300c906a4007210942c03240c5110111aa50b84200407a034004400018001101202d950101c4c2010002d81c42020802031210442040c10300030b1a280c8821140c0030450b01e83c1c00c002c0400810602c0c0038003a403003084040001415803650400408000e01c0d034082e5100c003c001c07018011400c10300c00c0c6140d04900a203041a03500d480e0303c00056030a12404c070030102c0fa00d03003d0392040c00580b0103894048a00160070305503403465079829200701100103020032400399882803000d81028107803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 405067221 1250 405065971 405065981
    0x503010c0c110f0904050106030201020d020d08040602030c090d0c060e1512060d051b13060e06130612030903020a050603040c0b090a0e09100e120a2111030f060901030b0604 76
    0x100a48150f000d507803104003058150004440c16180f9a4443c1390400031035070304125005007001c0510240005104203413004110b03030805440540960340100104030210180402c807a220040201040c40c0c907803003850309000614030751098030003140660143c03d90700e007000c1a200c45401001500c03140b078000e00b90024102a0340140000e40c00410380e0702c800c00000e0003000f0800c4034032240c04144d01e600c43e11030108001c0500a200d09101c05091610420010384902e0307055801044c22945500c0c4078640403101c400078201d0b580031051000c00292544203060700140c1000980f4020380e03610f001c00352110180811442305582c01000c13100c48010404c5485007a401410400c00000c26118103aa82c45008620084003950b03450707240e07003000071440035003003c4d071140ca10304a50160161a4490341010071507014010008ca80c000d21110700303400c581034100c0028891410340500c40800000a86005d4061250000c03105140c900c40c20001107180391400e11b140074103c0303a00c82d20b1000070b607440005202c081c1c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 405068471 1250 405067221 405067253
    0x60c050c040203130606060e01090603093002010605040903270b04090f0f050709050f01030f020d06080d0e13180218060103060e1603090302190602130503010c0c 71
    0x20140e0140c03450941e441d03000441c040e510038404448194181c5c14000308803825640124107000c0c403907695503d50b98014035820111032041c10005804c0703890341045c01002e1088140b040c1b41041610710209000c0c0381d00d6050850040580c000c0000c192124207000c21915100b80140c0030406039003c01da0f03080b90030321560302e4030788031100741410090b036030b2aa00c001d58015800038159140c03508080d5600c1d80c0701e845107140e40300e02c2020a0200d81800e50014200300068024180100c440c100c05140a90094000c00900d420000046645100c501c19550040c00c044c000d07038005008e504ca0600005100382d0f081c404000300185803007454100700c10f0030401400c80c4121034444811a1041c200580d880d800c404007801070018001644e031900030001411200542c10001000b01070900340041004074003034010048400b4200001c408005041c16813400503110301c142c0c1c0240f041d032030000402581c0c0e0060000c40800b90848a00240ca0714101401e0340c00600c4400001021010220301146244109000360b03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 405069721 1250 405068471 405068473
    0x20c1603022b300305150405150a090603050f0a080a0f030b031609050a090f11011713031805091306020415030204080c03060106050a111504060c0f1404060c05 70
    0x11403550382d205510085665103000c0034640c019100222000b809043d0310b2800918082215160015040e04442e08482480380125601d0001505080d54110301207008640148842c0c0b000e940c400c59003018040500044a141c0100e540041101c1000160140300c03603400b8000314248101450101d6041e810f040f4598101501c2382d40d5040b42d51801d100390950307410010252401c171030400301d924080c0c90015020f6003a0501d800d210401041c180f035402848540d200ba200281203000c0e0300102d86020701351a0703100d00c95140006104501c8206070441c3d00261282e01c0d0303824600302d004010050542c0b50300c5407540029000000403580c420600000710740301e210310801814551540018440c4a2500c0d000c400841c1d400138080c080150304200204141e10118018401581056402007442c043d03045c4d0081032200300b44414030310b00001d04c00310b2a5081000107061355427615007800300c050703d101003040d00854840c500020b41030b0b110b00201000c02c803204203401e00d41450309004a48180d0400001c2e501 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 405070971 1250 405069721 405069799
    0x2010503040308100306090b07030c02030a0e010806131107030f08040c06051614010b12010b0d0209130506041a09010b0a050d060f0609062d030807140d03020c160302 73
    0x154040c41220101e5000d50f1008c800c0345014000601141e4052840c41d003594001d02100907125807000c0403140c440802e20344a42c05d40c07554400308603600c412400401415081505500034003500700050f10a00d4022b941d201800e085d40402550011420b90300600302e4101c0700018880d0740d00500007010f2804103d002c0310300c2400c4544404003414862041d250b0603075180d06500307025141081f240007601704004001c211040741c1c40300140c40c4191035800207014a100900003200b43c20350031158000260000183c648034501031420000400c5241e81c840310260440c0d01003101c2c81414407880700d0110001e070442e000a808e1104020746003071041000c90300d02d52240b0807a03034206544c0c0650f00040103010404140c640c201780d6841300d131415a046805512607008184c0140d0303c06000c4060840e60842c0640759180c1140c01c11302d42caa250401c5600c1103105074804505003960550007031110005000540d01c500e6000f945100642c0c0b00c0d84006940581c85044854824119102c0080e80b81c40070310551803 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 405072221 1250 405070971 405070973
    0xe0103021c0605240109210201140408010b0109090b090705030a27030306080f0d03020a0c080711040f02040605180301140a05010e0c0702030a030305070e121e0604020105030403081003 81
    0x80d141c0444e242141d0066078007100700800d80d40d590405078404242030955060741016140314031305440d04007110580302e43c3c109810a40e400345407400440c0c003c03040c2d070035034860702d0b580440c0c080d0001c00d00c0140050002c4e4000101040c003817141d407100c408003c04a964a44403000201c1d07450308098446104540d40d40e40707461032441d610f5000c3c2c01c05071006400fa14081d00c58103000d0225422a0300000c0715420540030342c1c0c2810408a0b50041c00681428010380f40c01c1040c1084900c0201484020701c0c001001603602c050012412050881010484050141e500c1500540e8280e000701d108110220381e0602a0a00c10804007070300ea03620b1100034000003503002c10507205103200c4009840c0c00044540e10700c0140209940603c00c4ea40c003070444d40303a45140c46400e9010aa40d00f920300c502408040e80d4001049400744204000141c40e0001000940290904000785880390304480408510250043c41543c0c4000085040c2c4d201d150161203207400e40c0d8544c0c034240c501031002042c1c43e110503c0200040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 405073471 1250 405072221 405072233
    0x50312060a050f102703051f1401030f050106230a09060501090302091e01060f0e090103020f04050703060b0c03180a05060f0a03090602030a02030402101103040b0a020f011121010e0103021c 83
    0x65000d0b400a094004048c40510040036298030f18070300c0035040102640a913100294007504603a40619107080f00916410801d0040140c0d4010400d0a01500a0400c130301c0c42c0c080c40d141c8445421604503e859a450928604071840703882168042030b043d4a0030030151030609991035000340d10790211500150070300390f07500000d10240c101802142001c0b00e803120072030344070040000a00040c1e4003e006541940c0006504840c60302182e445580c0b0340c0002004284240c10000040079588551034440762540003442e03c0307070030074002c41070a60901a83d1152071720740100514125400a0885880e04840c281c10b03003180d600244e04002815200c049000001e0001d10003144514005600140c8031706207841000800100078444208011a6407400c40c0c82d01c401004450446801180d01a0303142a06041a810007441d401c00208651030500c040d000101004020110300c0e44130b21003186201705c0503900c400101740070300480840130300c000018030040c01e04400011008203280f400d0703810088155a40d07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 405074721 1250 405073471 405073547
    0x30a120309080705072c0c0433020c01020d1b03030b061201061e0e090a1a0909010f0e120406080705160515011205060f1003050312060a050f10 63
    0xc07107909031410140c844020280e18440c4400e1001401a0360912007505801070085000d001d008454150130080d809c041900c00c04030840449a4080da20503290384065202c07010385640c2805400303007502c0041494070403209102d001901c03819013030440e40b054030210001d045501045401c20010002e840c03035001e404003002d000700075998588100c07103107200d400700303001401d40001c00a008950400e10810740e204420705600c070868080014681d002400c5000d812210502c0c00303070b0490485814000b0300d03201034002c010840f000c45814010a60a82901a640d007401440c02d481410f00307010038441113104103a00d90f0031540c0d07460003038140610121207240c0302c0c03a42d103c200c95a40c0020391070340c609070542003550b0040c16414141140e0380c20316100c0315200d1307000400504000580f4400244a04480c00e540030203135402100710381d212510300ca01100b201105440861044980200c00a00c42c50403c2035194194005400007660b0440c92070306540c110003c2c2c200d0803007050410b00d03c1e5082070840c005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 405075971 1250 405074721 405074729
    0x70f08040e1b0412060e01060b1612080613051f06020d0e0616060b300106050f101d190e01090e0a02010c061401030b04050606030a12030908070507 65
    0x226569050000c0d1011001c6036111190700c012405001c100040b440004040030030b180c00c0400032480300d9038146998010441038001c627142c0c0c500810901c109081421740310490307a125103c0800900b04690059402103030441e0b4141e4032034400001c01c210110142c0001d9000415600a031000850101c41c0d102d2101c001d1b0098001a0300109944c0581c0d9880320903411400c070250740044c54003040c610020603514038420f000d004952a18001d45440e15062109286c4222503419541110701da2203803203201c0601103170195415820401c0120359864803000c441c2c4400701c010210300410b15611401e89101500c003813640c800800b9011104115103e540d5600c0030001003150f040101c0b42094480421004180c12840c91a881c1c00c074000b8500f00001604190035409080ca070104044500c4d03c81301506030361004a41007040301000004110a0500040c0103030710076802d960075951040300b41907441c2c100160151051540440a110b880d01036400107440c240641185440c10450703441c1c00b86400c00d20f501c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 405077221 1250 405075971 405075989
    0x50c0f0d050702101d01030c02030904141b03071e020109020a032603010b0427090c0303030b0102010212010608090f01110307030b060a021506011b0c0501030f090c0b070f0804 77
    0x2c040c401c516090413030a480b00c8032420540c1124440360000610804130b12100740c14983e4411041d202c05008109a0b004080c006000380181d07900860240b90740d076800e84440c0c0048a000740d030320000340c45440981c1e10500d03032542c2d050034074142c50b42c2d21130003848000f0074101555610300c111005600c40c08102300c0910700031113024640000400d5512505021401c1c110070001040c401130103070f5103401c4111070881d40c04406c600c01c1408940380034405c41d03410f40c0041c3c400a09e400d40740c0081010111800c4100d81c002c0d01c0400c0440c4180d801a400d03481130703041030082e028603070340103100d101e01031204140c00001100c2120246200480f01900b101d400f40006110444040304004c0020f906020b0190581826142c4c50f080480441002e503540046070704014400c0180400034003140d2041d140c2e8584000b01c110a506101d5990508888460142c01205d00081c1401ca821090718600d000d620070841d40075002940f030520f000d400344d01c1d503085504121041442042c8540114204a0103040505a0701c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 405078471 1250 405077221 405077227
    0x905090c0306060a0f05130e0303090106050f0409020f04090305190e0f03120304080307021903210204080a0308060f1216080a03120e0a0803010605040513090c06050c0f0d05 76
    0x200701841e061006110500c25403d0400500180a005500404541c8180c40020250016482d0840901480095982c2e00d102c040100000004150012003c50780309450f0040349140b03001c18403050b10740861001c3e40050380911840034905255101440381030192809034100801904083c459103603400c8500009440149030810628040c9100c40d50424110010300e000811903400030100d000003003020700281030200000d5100d60003408058082410601449201280c62601034000060f440c4050800b00307003809900159600d44c82154141e440f444001c0160f62510754040b1aa618000c00d0560049009940c0300c0c01920384003180030600c09200d0140200400440c041050102d0a500540c5180c1c040042800400d4005010005180744481e0100744101e0041005140c600c5141c00100750041c0000002240c99215000e0016280c084801024110a014a0b0019101881005800401500410003803c0c1c0204020f28070001c05009079140003c0c4030383c5a074200403500c4100800300f8000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 405079721 1250 405078471 405078493
    0x6010909060e0303061f02160603060303170606090d02130f06030b090c09130305160309050109090b0307091517010b04180507060e03071a2503050a05070606090509 72
    0x10b00450014000d4180110305520b001000100c0b8110403504c851680c1110702c5001e403501d4804d20510212810b903802d070058095681100400406140c4425030025030000700d042d210701e100702085400389100502460415000a0801c01c1d040305800d0100c1e0b00c51032541c10f850743d80e0542e00a800c20700c5641040041c200e842c1d820922020803004040c4402900703e101204459035130300c80001d410101d07054212a0000c95490300b0b94251164420714041404000d07107020415a100480c0c0c3c095403020ba0703d2401c000da43e414104140c51291000c5981034004120030700c08420240d00000c80d00008490030640e00e56200b10590b441a220002c481c6180d4480366030f115281004d005089a00341c20200d03c0c0111103940c5c0307501d5104c880c4cd00401040000b10015405e8580c0c0c00c110000140c032401403d48806100c907042048942e1050340b0480b54500b1098103211178807620301162022035010340300c2e64500907081004403040d44c000b0004035481640c0300c0011072102c92900c0b5640c802c2c0d15a0004181071007403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 405080971 1250 405079721 405079733
    0x118060c0e0a03030909020a050405030115091b0804060c02010b0a2903130f03110d0e091e130f0609030f0905090108120d180b01060306060801050d0212070806010909 73
    0x101c110a4010307451518200000307a40120540b040304e82e20130005849495001040751180700d6076010300d0307266085c44602407824050502850840304900e104100c5a120007203500c0c4407100214000012441900015000c0380d47c40e0009610714409200010f10b450300d0381c002035110000d81d0070424840c075205003100d030208528683c849002c505410b03410b00350310f0041e600c810000c01451008002030080c0c0e88040805004880e03880b801030780001035a20076400d4a400400c20440c0b2508548500d1040c808241158109600d0391100c1c0c01001c0844655521001100350420044d8002c580c1600e200035008003050341d9101c0c40200b28402d0303427041101041d8180051800202d07070800780c40303003d40b600108040200010074440702e9602025103502d8a400b80103450003072402080d0140c040c0f00040000040020b083c0346541640c00d43d40301000550f4641000b00c03281e14090007581d0300410300c200324001600d001000704481e90701000481d8907094403020701c0d42c240034081e0701002c0d03616140c02e03030b840400a07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 405082221 1250 405080971 405080987
    0x3010b0d0e571c0b010e13080706021b0c06090f0103090215071518020f13060603050a0c08090304030f081204051006080f100e0118060c 60
    0x74000c010600d84068801c0c00d038042000030642d60640d54011080ca00d8101c0c05034442c0348407060711000d08003600052104610001030901002c1c42a4403401d11203070118600001d40780d0700340e08080801d180741e007400e044800c1600e01a003000c0b10f01c000000c0304000100900000c0c440709200341e0000d80c48445103c00c111028681004100c4a03401c03502c0e1515658a400069031684401100c01400d80d242000059005062100000e03400c0071182c0c0e400392201c40c1c02c40091900e203129540d20000c9201c0d26000e682241ea8221429040d100c400c0340031400b600d0900700300f040c0c102c0024001c079400c0c9424500071040b1103040d4841c401090300c0d5420031003402400e10940c1d600c001076081400861411012072901ea105901000304070041c50003415040c020790405591189180015036040e506144c140b0315503c44c1c0880c0d1f81030440341000130200f0215404200310302000b2810008000404842452901900d04403600c03681035036944000c8a1900b580c5002194080c0c00303060f0005a03450350440040800e1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 405083471 1250 405082221 405082241
    0x30d0c020705040e06090a120504080a0b070e061201030204020906091003050f07021b0904051f050615090609040c020f070314070b0a0503010b0705030412141c020c09090a02030303010b0d 82
    0x180005c01001000c074008940c0c1c1c60383d0790303100480c40440415a01d0a690601860700a503105c3e00c00c00c0480c004220400401d54000e20f8952140c0e954200b02d481040f0051240c1001c0340d401029000c01080103040a402030440054000d0900b0b00f8120300d800800d207030308982548000060344074800d02140c0035841c004582c1008485c80a0111117076024482814554151000c6024400642c0002c0510009125160100c030144100e00c5003266501d043e500901019141d05200e00040200b20706c44500f003000700d410072000a42140d091001c200e04001c002c0c0881a03109081d80100381001003410405d202c6180514407034186c0a0065400c4072055142108503040715881440402820103d42d402400741e17811141e810490540d65a1149415800d5029031750041c44206a107411400400400c402000561074041048403100b0807850304141c40d0a41c21080000541c100035a034400c50704140c01c20795800307a03200c0c1c22110703c010503030701180c5107a009911442800704046000c04800714140900c1a1071 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 405084721 1250 405083471 405083473
    0x21b030903072709051606030c080a02160b0a02040e0c07020a030b042a05011b08030612010603020d0b18010603170d0f0507121107170a02030d0c020705040e 69
    0x8114400400c0e954031503802450451950300c0000f05002c250444980d0700329640c00014803d207901440d120b44d0b42d05d00c64070329120000d514503001c03440074464031500500c01c0055076444856140c05208000030340c003460310101e41102961016000c0340d26014401c1c09032808800c0160b90b94a8228120302c1020003400002c0c0600080240501580d1441145815280c102651482135240ca16000c88004465024007140c801d0083e01604c00f155015a150111031080e220b0004825035a80344040a0329090002009220144049080740c24103003801407070b12030300e41c0000821917220f40010340640e41049080704c0c034500940c20030090f01d1151003000b1111840c03031b000340007560a6070740d00001418003800c4400401c001048159020f0401d0700069092800c4000030006410000350051200b1648070902e0340950408844070f038103010b18421242010707048089029004c5054a4071001c070346c080440201148070500148040045510450350481c000d44c0083c1019498031048c04150344421800c1042 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 405085971 1250 405084721 405084727
    0x150a030b15060304080307050318070905071b0c060f0905030f0a020a0e1306090206120f01030302010e03040e0c0c01020408030409090b07050c030a0809070f090f0b04150605030603070b070501021b03 87
    0x1031070000699030032509a0424548170703618010300500c0741421242b4040c0d1482141c2c4001a008101c0d440709008407550398811001c100f008564811300910318900601c940115070040114034410800c11031008410714100003010f07502c6002914141e04030b00f02d004540c100f0100c400851515480d480d0090505030100c0ca4107140c202c0b51081071201d550006041283c807040c02c0d408540d00c01c002c03506144000e298070015400e042c0d030309206031982408114095841c0204290002000005a504940041603c0c2c04955a4a1200c0042d600481110050f664081c027000c52903030b9042c409000074000e44100041c241c21103090010400b42c02500031000e1110412a000400c180401116800096810b00c6505d0703850308000d0503e00b10461f8000014030070000b0001c0f0b01650180c00c00c3c80c100d207140e20103102168142007004200c40310500d03950402c0460003802c00c074070741c010006140e1201008081c0c07a942e60b0780d20484d005070780c0001c000310703801d0350300190a40114044003201c1040e54071840003981 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 405087221 1250 405085971 405085973
    0x5040e0a050d03090809040603110102100204260a05060c13140609012105070c05070f1d0c0c010c0f080a060b030109020d060b1902120c06070305150a030b15060304 72
    0x10700c41e408102d8140415840300c1200e802d0000c01000c4404003540038004000d003036074a080c600c1d44140d012a1007801409209051407460380c07c1d0080d00c041c0c40c202e24000e070200c0c400c0d581040459035211070a50a0703000f58106480031440c103201191207446804201036076161075034858101d0769100c1e0001007581c228900403002e01c0d00d509050b00d49941c02030801d00d115405404503003442c96410044103000071700704020001466400b00d9100d80152103481264000c54070740080c8078403003100780180414070080c003174290603090741d4250302a08240c4403003500f1301c1d11075458285400e49505040318004651a80bc81510459008070100c1d40312084080402113203040a0310502e00d0710042c441d245496801280c510844211640321400411030064aa5030360100c06801140541c0d14092080c050700401e0f4291049010030303021600b6801d030250203001d896442c0d00c07050300146805008041621940340d11400a9200c000c07035540a9405581400302c2c074a45a40b1503036038042801d092502500061003444 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 405088471 1250 405087221 405087223
    0x6091e0e0c010e040902190f05060c281a0415200903070b0706050a06061106160306330c030507080a17010b0310051c020f060f0409020405040e0a05 65
    0x40000c01c0920340185400401d10014001e80524a000303948501c030395100c20304290345414a0b01c1100c0d640b401210400f0345c0c40b0100141030140b1072595409030000c0003564141c1c0702a0740c0840105030700311312141c0c0c2d00380307107407903080e070701c0307104921140382c80701a0390a000501c400d42d201c44071a1071102c04244010201c40d5400601e100c0b40a050000340ca40106192105a070140042d40180086103c80c589889541c1400d8015040035201c403012180340000100d03469110b030fa90079422860400c002c111039125803040398000801d80d1099001c06a0b2080b021030401001220034410700082210801c00341c80c0d0b400c15940440030219500140301c0c0e0020102e00080d0044150f54500381c00c443e1040c0c03206500741013503580e0b1141120401c0000011000030400c20b00400295000300d01310944101016200d80901585e807414411030041c28250320003580061926026664110901422044c11300d080000c0d00c0b0126001900000f104640101301031090b420180705800704050804010505c0f10841c0e1507503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 405089721 1250 405088471 405088483
    0x90a0b180703021b010605130b010203071103031606020a020f0f0c010804060204090903121104060c12121a0102011103010e0123030307080301031b03050d030209120106091e0e 77
    0xc0c040d00c800c0c00003280503019605a86641d103600c1c0351902c2d1944880d000f20300800450083e64820800d02d00d080323a8118083c8260b014480c01a00258544001078503845405c040350007030b05505110400403e0101c060000c455002d01e44200405a112048000d01070708100b03070140e2007a482c0e449000328140461b0700092401c00e130131080c240f0030f241e515a810718102074411034000c0007499041100b628209079218041600e6120070030000c0004010312000030003280310b60f00c00c2a0005030700ea1260008a00001c4480303000c2d080030b0921140304200080004259182c100700320910445400b503035101540c0a00401c2000103000004910750341c1044162035540e5010f0041e01100c0312114415449003100610b018160a0000c00f100c1e122101c500d44503074941d01c01d0008407041d02b508505099142c00e2041d03144c041e664008081c264500c0385410450007504250700082c4e02a51750280254440400e110b11006000c500c200441d080000b00c2c2104102041d0b07008000c0ca040c580440500855030221311 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 405090971 1250 405089721 405089749
    0x60601120b120a0503190207050603061011120d150308161406160e030c010f12020d06170c100f030b13051006080108030c0712030c050304090902090a0b 67
    0x2002403081c0203a80800d00c880700642c2009118401d52890400b4000b0001c09008006000000605240c2140030700706d88882c10391203207603000300092010941a01e0042c8290340c00c1b1394540380c0b0038070180000f0300052600c821502964580440081c48120903c00d501804140701403100c0500c0e400780c91740d0707140d070740c0740c41010326603000c07400e050285808004c64030042c20b4124014004aa0b940d003000e422074041e10b18100307500004600c440e00200d60703904020600310201501611009a0100039601c16119070208550b6550300c81d40c00c015404050119128890141903c001580c110961540000c0c0c5441d00301a170051040b0081c2c03000300c510b1a405002c184034803460b031801080c0e01180700c02041525808162900050b41400104034400e03141800e00000c44465549071070f103590343c48103215180d00c9900302e00f03d01c6401008003840703a100d8012102103154480d00d03003000c0d0a061754445504603005a003015442130b4a84d08a001549010b9441c1a04000a01d00400c5000b0b40400041c07038414080071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 405092221 1250 405090971 405091007
    0x7061814030a05121206090618040507050d050c03010606090f092003240a0b0a180f120b010e0c0409090203010b030105070905011710050618060a051b060601 69
    0x605030039941c8041c8503058003154040e04540e16031100c50b100320310039044012400040b25204001402d10301d05051501e0043c034010340342c01e0802541d030015900c40d00006005490b0f030b201f81c1200083e161121040310142e0390051000d0b00001220300101829658941c2c044e008005484500b841283d50400d80001181d05040c400284480d0341c09080c0c41090342c07814100031155011080100d42d0021f200480352070017590081280340e04001d420000c2000b143d020f241d516180c00e0029001413401090074680c01c0500c1101d466909640b2220071514004540200c0045250340c1642c0702000407281d403941c05000c020707403001e0003032905040a0441d03020f10300c502c0341410344035201c070015502d007035220340c2c04100064007c0c0901c1c0341c01d20000c2c0c030316480351080900003400c2004200340d400d41c0c040100e001310300d40d01c981220240340504125454105010000c000628980e44800701d0390380d0402418001580d0311201d8a03650411b414003641c91190054000540200b004c021540ea4000d00000d09156901 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 405093471 1250 405092221 405092249
    0xf050913030e0a0306020403060e0609062403030307020127020612330f06090f010e0a09050403030c0813021302030c0d05010b072d0305030604110a030e070618 70
    0x2007000c8038052161408203800510704803000c028080903800410540f4050740c414841c0000c04e411465407680101c4029405402c0340b0042132010107a0b81042004207241c4411520070b102580002c0d0443e4001e45120014ac0e65441882c08124880c02c4c007025401c044c4605410390711525000f1444071320614501a040702008000112145182d15040b185003c511100c0c80c44242010400b450b090041c0d9402071040034622058211480e01c54119240c481010f0801c0c48404c03a8400191405410401d0080d40b00b07181c0403000c10403403614401c0070301c9580030f07035800310725444181009060044081c1221103040c00103000079016032038400500d02c4420745024010794940d244c03d20f502d60f40c0100f083c000c01081c10701000050084180303001d050321a00038025800514100b007040c545a881040c4440b62074044d185401c80460300542c0a543e218002900100e0580d0714071800c078071183c0c04410320b18082540c0b0714101944990070000b441c040c18003030401107021101e0400c40c1341708003003620408110300c000b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 405094721 1250 405093471 405093473
    0x31017060106051c0f0905060903090d17070203250509010303170c250b0a060305060f0408070812071206080705040f02040b0a120b030a020604030308250203040f0f050913 75
    0x4041d5001302805644c02000290728081142c1c02403d070003581075a4038030600b004143c80d81004011203c0f1050014580241c00c04907560341a00020b652060404c151401e204017809604c050208031600c0d1682010345042d24441c00110034040080e800560041841c1001270001941000490480302c02810b0408030903a0307a4140d4440901c14842d144401c1100200d0760761044110000c8203140c0e51098100440654594030080219441c1d44400b0f03120741d0003100810010240a40031a411a000d050711b03501c1d005840c1c441c0e001551094070f060b080c1c20348600403c203013a584203038052044903002c1002d00800b0f281030001c95403003207140142072240760303030399441061004154103d500421440d54500d40712144468060400d500d0442e81211090602c401d807109803501140c2c248410358002d00486c1032a0850300e0031111490024918212041215010700003c44000d401409600c2190f0045d40d5540c14401c0718001c0d460107a00403a8141881d0000740026621084807650091090640e000c8070006 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 405095971 1250 405094721 405094747
    0x6150e0906041506030204080f010221040804030b1014010c0201050307180e09160f03030c060b2206050102150f0c070206070803100906140f060c0703021503101706010605 75
    0x1e0f440c12803540207a1940000700180c0540285c411180030100b0760ba559000509201c3c240d00c2036104050460064000d141d800c0c01d01c054a1907001401182807038281a200c1d80d8840d01848183d40d01030003401170200400c909213034060091040c2c0800e1038450345000c01c80d80081d0841c000a0500030034415007642140b008205070001030000c01a06000d01e4503410086055030700c1e9100c01d042204c00810750807020843c0441401441c003201c0e0b050340c44000014a98481200404021104552184c0d140c41c40703a0303450741d00c0c020742c104030340c18600002469442c040c00645000054a003108000d160242003041907108685003640c001d580284091750b40d5403038800295244030b03003000140114404424480c4c250400d651b5801543c2c02008101300d05501c983e032800800d03074140030141d800f5800407624045800c003d800750180407101030840c2c52207a100e80c000344089081c1480014a4003010041060400200141c0c000a02d290680c4915680700904581c2d01c0d80014050041170040001d5102c0032004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 405097221 1250 405095971 405095981
    0x3120c06140604200a030507090b0712021605030a08030414030307020f070b030f0a0e0c0604090b0a0b0406021207050c04050405100c0f0e2209140106150e090604 71
    0x20344000100300c00d003100d0750150300e5808142c62840c002d51510840034400d00d00c1c00c90844c1c1003240c101e106420035000050450140800900365002c000c00c0020000b5544010006003032514490440030100980c5000028a85031561508041c7c40f228100f00304080e071000300d410b10b80c40340c2101485a580d035650400480c06401f03618442c04e80d1200008000c0c0d025800300b451810740c82403409a40030b65680e03c0f149201804140c0718031410440300b0010401b04805903002c0c00c0500005410ba920011011b00010007640085e480344009684070000c0105d580b030455800c1d40030b85000ea49081c1000e04101c0000c2d0307148140348800c60aaa0005040310a0100c00c001c120128040140241b010740b85c140340880c0c440b1007211060013010700344000d00b203026020703030302c9402c3c600704555410390400c0010741045040c101d403100c0c410f06140003030071642885141c0c0c0100c10307095001e44d11044480d11008107090031103405502448079030f1f00205158244a074403010510344c10b02c00700c80781e0031651107420002d00103103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 405098471 1250 405097221 405097223
    0x50105010f0309020a0b030c030711120306120a080c010b01080604020c1c0c0602160311010c020d1214100810180f02060c011b12180201140f0c07030b0603030a0903120c 74
    0x6c00044100f0881c00c07080c0c0015480703843d4560301c09441c088940103031f5a0b034940064204400000034000600c1c5801c010380c094103119909402c0701d4a4180e16111212194841c000a19a81c0d4603451260b40950300110459040241038074118980304490b0203250312010ac414444078a070b00095034a4484510a015001300c654201e80111340c0c44282c4006444c06480060f01140424103104160f0000d401c1071007000707001901a00600f0b40303411410401c0b21455020031606c2c4515590f036400f000c505414030082442450b00d902480c04290800780042d1618a07010300d14458141042d5003e43d460007400000080542e0001052410109620005215000da0600390300b6542c40e2614008110000f14000700380346055417200320941c0d080d482594251208007945e185140c02c0420040e006500c902039030403024034881d409905014800100703070310b40c2c8e1000030004080c1d40310440074400d11a1520075187c01c042e04600039440e0003403444020b03268018a200103003c1100801144c60854001c4000807181 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 405099721 1250 405098471 405098489
    0x60807021c050306040f0b152208010606090b040807051905030f0717010221040f0c08030309060c190e03070801020f0301080c03150a23130510050105010f0309020a 72
    0x1040305000002d18541046800c03905c0796052407071a984002091003400b1958078040c0c80c0071210510300f03119081a0b03101800c1d12603821201c0051702080e48080d10701d28080d10460300080341f000c0c600352004181e042c0c0b5030011101c035001044108040500002c0c100f08440003650300740040e01124051503203e0311603500645c0c040c007e0108401c11142c0109000081d5078194074510310130070032584140d00300e01800b4084100c00d001d180d210890354100402d1141c0c0f00b40324441c0002e508035165900c01c01030010b503019480503070000c8148010000b05105042d4800c0c8081161414074442154120094a07904221018000007540301095503c3c00e2121713001a10b2000d0007950344410b083e440d0900b03507009101c1d1107854040c4c1410301c111482e01080005449238081101c00c125140c540703848000b840204401c10910444c50001f100202c030600d201c0c0d12070481481c2d08a0b4203852401c0060a103035640007001c245ca4035000041c17007140c1c0c000d400c440c603d0809143c0020001a548045008101190000021 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 405100971 1250 405099721 405099763
    0xf0a1d040507230c030d05134806110a0b091e070e01210b160e04050f0a0e2104030212010b01050d0902131d0d0c050706080702 56
    0x2050b0420f003001c550500c40d0003a076415104260321029503015014104d24160001c001c445025140e6030002900180c1c00c0001041013500c3d070380c5803001d4400701c00600861220b8000181c425110b000582201420500030780140b4043d025881424804075000307070300900c1a0302d9841c2510715001c03c416030303042c0c1c1c0c002c22103212410a04241c0c1da41c2c0c503045c2034003281c03800854900342c1d9040021501030100c03400e151100c3c0396a4201110b01402c50044000004002000c00f2280c012500014200e402180b1402001d101d03000c500c4801080c0b01101c15101380160700340300c203120801031010101036202c10705001c001003510560540314181202301c14095144550328141c140180020340081088a01c01c468500c0d1502d032080216081c1d407045410340d0302059041c0110b222240a1380c01c100591403000701400701c80c1c0a101203200850324502c0c8444c0d2102c96544819145403000c0180b507090040505050007850341c03d40c0c0c0c040e6500603a0040d84100261000424451030081003548401c1080c00384c1584 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 405102221 1250 405100971 405100981
    0x30d0c1406090c0f0a03260c070b040906080105070f050a030e0708060906010e190c09050301020a120b01020a02090c070c03080c0609070603090503090d020604091404120201020f0a1d0405 82
    0x90380d1209020424403c91404d83c00845a1410324401c000b103079400b012005030340d4250101405646138540c5c0030015410304100b854151802407080d2805010306240603030316103050004510403030300d950f0401c10a030382c90311007070240250f00800001b440590a00d0704a0741c0d10f0800c6011005420654003080c039900c00d6040200e603403207021910350321820a000072550940ea840c4000302d44203006542030a2a26511081c18464044a13000301900b8a4a41043d0120f169608042070880e0701020312140007550003c0410703100802401603020104007403000b80807018803900040c042e12406018000355110006001d810445480418402107802544a68a400c421140ca6440704c1c003c0f150781000d40105500861824000d03c08c00b00e41c83e41040045041c00c02a200b0300800d0300140e0400c2e64448000d00c800684036040780507681890a20902d500024141450008800e11120200d0360569005000b540d8440d6028000e03501d08141620381212403016949111000c85142d4812640180c10201006 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 405103471 1250 405102221 405102223
    0x60d05100824100302010f0e210102030603010b03011b2f03030901060602070b030a0203090f070b07110307060e06070606032f010c0c0b0a030e0106120b070e030d0c140609 75
    0x1035120803075010b2803405556582d100040eaa1030f500000f4041a1001d2030301d2443c61050b2543c1c025514050880900e0000e04d50a94540100d0b0300304148207030703400000b003214508003070180d846421800d80c000c0c8a00028840440300901c5070840c81c0081090703002d407108101c90110003000f50403c80c40e141150808094070480c1e1650300817541c442096003400c1c0e00041e81d134400510390084800c0c41803800d06640300c201e800c0300030f0348c0054400c1030648168011600c0c04101030002d00018100d4440041c5e4802c1540352400d100c1c00301d00400c034800e41015004114141d0840d0240e0f0f52000110323912640c41003940390520040c4555000940b61003140901408500440200d0221000319021807094803a1000300440d0091101c000040a640391194100310200d0b105d005404148120305011600e000e01c0025035003162001d9002004e100c0811900710140b08502d201190000281e02d080c110150142000c203a458280842c0001002541c4030044180175480150b081e800b070303100f010b440490801c08945 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 405104721 1250 405103471 405103513
    0x216080c03121003020604030818031c020714101803060f020d060e040f150908070f1208010605190507150e0d0203070b06040b060f1201080601060905060d051008 71
    0x92030318410325010540c0340c0c10702003c2e4400c80350f008100625040c191307030324801d441d0012915014400300084101e12a07a40038025001801c1882903c503100414020000b4680000c7d40d010103102c00312a1000302c0d03da100c4003001505c00905060103085040340d011a000401016400507086034034010500005540b25002440c00e80000a03040c840292924040b003c00442035400400c00540170080d00c0000700b18114080c0c2e20000310740005200015501c5540e042d50147c00d084856803d440030762420000640250483c2101d28a441c260307660400304054140d01c00c0d00ba5001e00441d0111140582a22510403030b00c12981c007000c070203420240002e004002c2c00607248214268040c000030111240d04c000f00b600d80342034100b41c150301a510303003074280001052411501ca0b0000340401c102158286100001e101d42c00610741120110341c54240228104603040c0c004600b00010650100401d036614415554000c120700f0b000299503c404400780d52400490703011500314064164400d0360007450040d8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 405105971 1250 405104721 405104737
    0x3901110f0601050f01091203140c0f0307051603050d03020d060b04060203090a06020c0f060d0605040c0f02070503030a2c040c0509040f0207051e01020f070c060e0a03030807030216080c03 82
    0x101d0900380ca4140103540c0428180251142c7c4031503207100c000864800e25118502c1122904031503c0c01c0074410032641800701041041d102c0b0b510000e070703810420000300710070100509580103240d0882d056a41d076a844c0c0b030030310243c1401c05401190740c1902090710b41c0100b0007001720072a0195501d42d2490040d44940003503d07030610a801c1107070005070450000ca5030680710040204140c1d02500450200b25013500240903446c486640d03680e0110300c41d1128410710001d5079080d00d0f00d0650282d1404024600440d42e0041c078000d400501280d850ba03904040036010100314000500581c010703901110311141920004594800e060042c04601c003604035009120720392041c2d400b4807440c040c1032400d40030303440b4400c03000b40264070140301e0003000075003501d9000c0c0100c070384c038005442c0515500140095400411054440401c540f008206403034100c440c0e1020544180c030580c0c0a185103031406445084005e24103014181c00003503040103010b01a80704014294004c803180d482e5a440000c0350f689402800c6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 405107221 1250 405105971 405105979
    0x1606020d0911040509010e0322080604060203100b0403050c060c0c0310020a030e160b090303041d160804030c03080c070c03110924060d2c3901110f060105 68
    0x10102d58172000c18051800729852400095140203514450a08500200b12000e2000f0391914404200c030201030051a0080b40920320150307c908021202d042e901d5403907480900350800c00c11080000400218080411880488000e82c0700c004074030b00c0500345242c210342030351702d8081c4980d110301e1403001d47e010b030203001078580d410801946105000c0340d90b40d00000e0f00c140c601030455410810b80011100400440d41c000e01a40e09159135104114842c0300c4070413801203400300303182c00c108480f901044113441402042c640750000c0c0c1803c0d00d0203801e0005524028041050728400941c5090268040703a9031580d1000018040c0f5542e42001e0300300d11580501c961103004024045031241190320700b00344044440742000302c41c1c441000b040121652214050f600d0040d01d0311002c01d034228051088812620810094440c0c0c5071203150344505240c104071038442000d454014403001041c0f0030380490015140c90b424000c0744840e003401038900c0301d203804525044c2e02caa54a54040050082840740c12200207075 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 405108471 1250 405107221 405107231
    0x1b05011b030b0f0112020703030b030a0602040306050c030622060b1b060610120b0103090f1b090204080d080604090503190f02150c0a0905090a0603170309031606020d091104 76
    0x807080007495003050b1030303c50000c0c1c8810012440c07030049500401005110303040000e400f03602030001c00d080c01c00508041d1030055000c18100705001103030150542c800a0281304928601d0301a000401c0a000c048040380496207891071083c4610781a40090040c2c208821140e4498001c4440c0000803905800e038820b440c001e040100c2c10b5402d04020115a102040e150140b0340c0b00b071140e844000b4260700120504140c1c84541c00d01c0401c0e45410303c9041280a04600a444901200d01d1009065a584100c03000d0b481004100201d01000c940c407400110a49019012500c0344400100a0038200c0320207049070000095005448070348407600c0039401059210040e142420b90026601c0e0340c2c1d4a01114090b019500c00280140c01c2301e4002c100580f106d0800c41992911a808503590060440e2411580c6070f50b20300500c2441414610311030010b03c4c240c48a403951a141002680b2402805805000d149078140050100a0150143c50307501c40c507007504200c0028241080e143c01901c40c00034900441c070741 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 405109721 1250 405108471 405108491
    0xf1e020a0b09090708100f1d09060910020f04090204080105190c0903143408032701200a120f170c04030b0109020a020c030a050c011b05011b03 63
    0xc0740c1540d60751403008062030200d40d01c0c200d0640341d50f41700400800c026406440f0100303c00000148120151a0080240341c00303442c625000410400c011b48941110391004041200341040082c141c0e0142c400c0080c096250320745000c0b01d00b5140681d0301b01c41989800800d0200701c0040c158461407081d185d0304081c1419500b410318140484448406010000c0c404050a01c0460400305550b0071400c0b80d401102c80c1025a4460310720161109880f61070000384168407500e80801c0001004081e100d90b00203517140041803100c030f0100703940d010a407541001c02c203021900c580c0e00460b84038074400d1103003203050450384c82c4040300b03500c0300c1d9180d00451320803d20709502c0140a11640303106503410030a460301b81c2c41f0091540142d80c04003008140c850484000c000100003d000c80c40c104d8000e1510401c051b03240d107032092000e4104036003040303058043c1c2e1001000d60f01048000031030700700000087c02c001c14000030700440400c285012a202506560810f4401c20030700c2c0500103032340c41810040e170303003003101c1204 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 405110971 1250 405109721 405109739
    0x906050307080c030c0c01240506090a0e06040209130c170103021806040f0c03090b06220b2e0909020301060c031d03060903030f0f01210f1e020a 64
    0xc00d5840d80c000070800300000d03050301c40220085401140100701241401e80c01302856081da074001403032100300c3c0752444006e04020410f000c2580a0b1200302c8480d4180b0442c4404190001501d11401615070139003070210703549840f158125411b520014004038040c078074001c4680041c1c2440c04a41c1c00089400032950f041300030540300b440c1a40d03402480000701d002c20030940340700044060900fa81c8155030b01ca0003141c0303901d544030f41e138103019094070082580101803d123504005d9000b414075016520220042001030f402c1c1d4090b60040e0380149000030354001000110b00d10300d010701d810880c3c0717502c02507030b110008e00741032030201490781207988031240c1c00e49a03000503007640003e110300e00215000020410010340103050300300c0002d9208014031319604052000a10300700041d03034103403466013002042c84074030b40100c0e801c00e40c0242c1d110380600603035242c01005061070428100c8081071030fa0700c003008801c00c291070030803040e40c81d04450528040c0c070391000c0ea613810241400d41244580035904c80040c800360 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 405112221 1250 405110971 405110977
    0x1406070801230f04020a2d02060603010e0309102c0f01021c03020d23070f09050904171903020301080708150a0b03030d050103080702010306051206011a040b0301080a03090605 77
    0x1000740c504425400903d0600002c0c1d0817a01c1450709101107074002d041c2c003100d8611441e80088821400c0ca4620482c240040c1c2082c0002d4203040c026414122540c0c0020800411120b00c00810740d0303101a1118001c4007243d80c0460400302e020001800305040f82c540030a4550301000260440e01940540841c03001607a80e4100c140100340c0b140d00c200e001c0e6070800d000794060080104141c0f0301250055004000144c8000114400c440e030005e03200030300080d070f076200024292450007820b115020030b0030309000071094140140700a10000062110503030703152441081d074800c191130f413804064601e00ca01001c1c019420900030b0280b14480c4400005044000107680c030721141d08410400320f03580f201d4a042014280201c0181c1d018481042420a83c0245100d458000c501403100c80d40c85000d14400141a54003983c41180315021039400c6000140000c1840f6044032a880f1451606511031043c99116000725032102d007500c240840006461440425004003052090340e9000340d8544801e400d0726640 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 405113471 1250 405112221 405112289
    0x110907020604080c0c060c071e08150703020d0c031a04090c050906030309090106080a180209060103050402192603041203180b030403030e100c020a020603041406070801 74
    0x60700034004140030880300700c01031540084c20360543e240c2212107404541254403080c1d889805501c500010450b5240760101344440d403003a200301000c12458943c00503a689101041c840425400401186041c3d001e5412548159a0100700344200c9100b148098018040368220502c2e03050b02e526400480d203030920580d442e2543c810304802000341444180040d03414000c11071509844100001051a510719688a0081419070b441c40810325251a901040e51a40941d1032031000032002c0c0d00700107a03035421046e544a4001e00e03001402d55924000070b500300e02603c40c80303110b00140d203402046002e01000300000c000c000f4034114aa6030000850180e40380300760b102d050125440c0d16035120020f845402d5811500c81d15024111801d0344074904810700340d00c16182100840c3d5505410111141d0034420002d2802104200300032030409100080d4a6000310200280300d003800200040c00c000c2c82c1d40c1414900a8501d040300d41ca4905402c028141702028007a440c85403d050310784442c0c0c401984081c000b18 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 405114721 1250 405113471 405113473
    0x30a080718060e1816030b011b11011809021e04030507060c0c0e0a02070618021030020a17070c03050a02030c1c2312091f050411090702 60
    0x60780c5024400c440042c201e10000d0b07408400025040c100403201c0c0d0405014031507482030001005021000a002c440c8481c84280c144005404040b0081640c41e80c038545254000404c501d02074205070040300c07020001c400042d41103400340c00100e05203815601a14a80740340c084426407081d0000034098441c05240320040c00d030340c001501807200900c0b51007400c404500c1120046c030026102c883e0f40c64411411680c0c03003226540407030400113200f058000d0fa2400c0d0400030074090260b4650b004601e000c400524480c0500c0740c0030742010b040302403417042e0100b00b0141d4a10703803106170780301c41d00074002c0d5000d8105031002030004403e01c0e10001480c603020b806240b032915558001442940d0070740e4150484802070f800d6000034001984202011320039900001a01e56900800c01e170801e03000f410010680c42140b00708810384480c549141c02c030008486010742490b40c000016995814590302d40407104091852034100180c0c4040c1089154001900440c461032071035009007522410322282c0802281e1000c01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 405115971 1250 405114721 405114767
    0x50d18050d1707060e1c0305090709150504050f0a05010e0702060a05040f0204140613020405010503060607021906090905150112050709051504030605010b070c0e060303120108030a0807 81
    0xd0000c1009034004480d400e509030400034607460380c0d403c45c1d0400348074641c03e402c0849580031840044519090300000380c10100041c2c10503003200d42da00c000c40d000c1c200382607507141403025007401000e007590010701c1d004009000a00d045041e0107142c11b420703035640b804142800f0000c980303040b114140a10130840755004140d00e9840d01c018102a2401070019903881d6580ca400c440903840318010441101e0070f9030200340c414107111040c8020490341c401380f410a11b04c140000d005903a4003e00b141d41010080b00c07256150081c5000081c4411625051880900700c1c00d0030004489030011107003001c40310641c200b00095543c0404012140410401c1c10f0300150103003081d00b60960b20384d0712454200080345803500c205a203d070042481c0308610755000c140d50300d0100307007041081050301485d40940f82442d42c890904034a42e03100e00040b0450b0040440c2c10303198200107151034904000340e9807040c059403614203155964500c03031a01d030307444000c040c40003030302020000d42510300444a09100760a45c1041040c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 405117221 1250 405115971 405115973
    0x20d230c0702010e090a020304111e0f04060f180b04110708030a06030c0b071e0807020909011b0309120f1e03110a0314151f030e0a050d18050d 63
    0x409901c000c0080b814010000182d500780d4036510f86161098a10b40340040c0d484c203003070520f850400e11840e002441812091011510250b0141c14009000b20646600140c0075007040014042d14039070f04084a007000405001482164400c00c80c51002e01c141e0041040100250030b100070355a80700000803041204001480004041d5801164040700950380018829140d9840903500c500d10340c040103150750003040c81d000340520b0090840760564003075030115600844c0da031503c409000e1810007030300c00d40004000072070400003900310700306286101071842d507510002c0c4c8000d0010400c003c4241c504042d84401c0c481800c1c0500f20200542182da118150394030170180c101281e82401c000981c003010b0310f810240b0080c0302e203d005001190490340b0085074250036500031011820b4001c2001f00b080076544100d0f0036648440c01c00050460b01c0c48122207076040c1c00d0b81e0550243c040102502c01c0c81c410704a10302c090010200e01d203400102242d4070301e50344444c3c989c9407400c11300b61030046660205401103804 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 405118471 1250 405117221 405117241
    0x1090e0123010c05010501060e0f0a0503070303030e0f06040f060c02030a200c0607060204050907020616080406060b032a0403051906150f0801050f07050d0911040e01020d23 76
    0x5541e60070140b40480c591640d564039582951800c3e485180070990024010000c0d2801d24003601100174140d038141c0c004d9180c003000941c0c4454074400076051540d60701142d02240c0d402c0c007071302c0c1d4040009002c03174105041a1501c0000781031984006d82d031840c64024451041c0c0c1c808021114014050355512f18145c0040c80480401c0c5084180c01c0024460040b50003481c2e00c80c070303000d028404e02400380180c1b41c03403904c02404082039004010408541060041014103100309003044406101c1d450070441a6580c2c2c80e18030004d00d603541090801c40f2012042188106130710031402407200a0382c510381204018a4003a429601135400f005180313070032040d1200e0343c03080d00344180a0924054800407030002d10204203420010740980107a00d20440042d0248400d19090164030781280040c25005400c0c6410358005101d40640d82610503c10b8642c44c100c01440000b424000117000c00601c100840405141110f00035070041d0800007800d8145a80c14411400900c0d84640d418028565615a50f403120411 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 405119721 1250 405118471 405118529
    0x30d031b27060c06060e0717190e0c040b040501080c041a06190f02030304030509060904061a0a1d010504061b05030d020304110f031c121a01090e01 65
    0x18503118807100c126407200051440d00d140c000c0000d03490382d008040e101d04012054810607000349000c03a0400080c007852a45c400041c0601e80d4031840080800e44642100b0020030a03417036605080103040c000c010710f140d0408a611904c9507001c9904110b403c43c1ca40610094502c01d110701c100540081d192890b55003400c0e0402ea4105180c0f0a6058032441c40c1c1c00005c03a190040000c8454400c1e90320540700e0f2a03900400c8444110460340000c508519155500078051300c1040c241d1402841c01050344800798959400442c064030074070700340321280794006402d01c001e80c01802c10100001e0895244005c1c00400d2031350a0803034071043e5a0300e86050708040040c0da040d01503150f14081014101040c0c000b2400901c0502650700d0003220150b603d007000e0800410f21411168941d104400c1c040c00d040142d80d000600c000210288952400c241c00304450641d18000101c0342505500c0c20700071851a60045007200d201c0400c82626070f4591961100d0401400c04024010504000e00c21000c1c602150071107080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 405120971 1250 405119721 405119747
    0x3011e180b04020c01060806010501020d02010e071a0d11190504030218060321040f05100f0f030f1401030b180d031107051b03010507031a040504030507080a0e030d031b 74
    0xb0162400c4544040307142181c000d5071201341d040c0c01140041c401c5682c18800b00001406910017032102984108446480d801544a881c01000c9222200c0d114020440c1c169920030070b0a0100b0002c03030518000460542d8020405070f1482c42e500003440c90344a00440945040c0c9401900050103031350000022010300d2000f402d40f6505104031309824142c4005030882c10800e4a1060740d081c1c456180130407604000505410071445048071503103801e140c80d03120390404c0030725441c0d1414102d030003141e003070130340040211a6400501c10304040229040341c184001081c100c070f202e85601b41007641c649e6001c074951405164214881d40142500c81c0c0010700c6a000003c42d906032155051a000440e0b1313910385044851040c00c001400200084100381c6000e110312030b030100c080e040501190300021040042010b40444243c4220b5842d80810103151140303042d643e445a01c09080ca50ba0810750001500c132512084642d0320920411380000724080c828002c0911100c013540d1040445000000107850315a440e040c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 405122221 1250 405120971 405120979
    0x120203071a0402120a050d0807090e0610031e02040512070b121b0d0c030605060f040603020d0b0312030a0506010306120602030702120a09080601080313060f021009060203011e180b 79
    0x10000c04c48024003c96940b42d21030001002c1c82c0a0351b02c0007400e100002031100040c8212000c0030014042c1501806070f000703c0840d0904c001d1000b05c0340540c001c080200d2440c080794149900b5800c03540344c030b6000b80107460301143c003012611014800b141e0350b40030300e0282c54400344041c0500040d19a045c0451038004a010340027901007030026121351250f401c5850381801c101e8492452403c41368051103448040c0509680107880e0079007040762451148994402d0000700350740011b0300a000c0015a10000c5a50f00c01010354600c15209268500b40f50802d58008a0380781c174000200d145980248260700854008412218140655466050003500018150410750041030742c45a40c030340440000b400d0400c0584c65100d001c41c200b6413554a040e405820544441d802000681d1001d4000742ca11021158903160032034020241c6c110480c140074100f0750301ea003601c0c207140302141001f046030091816122601c0b0895914034080c122440031130382d140700d2022240c0b1006a02c40030342009400c0342855040243c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 405123471 1250 405122221 405122239
    0xf06051902120703051c090201020c0609040b090403022103071e051605030307021519050c12040c150c030806090c04080f010c03111e07020406170703120203071a0402 73
    0x811202c1c0076070001d00202c00150001514461900c804010b120f0b05c0c002a00301005071041a50000c0c1d40c403190112480c1c40b944012589001035074403a0040302c0b078031001078030080f854106450080e50310303003c640ca11144070781001c8580720050200d0094074421506540d851700c200c10391a24441a80a1910440f0100501040141d264031440c8405c0d00c0564800c100a40d031381e142c40c5500a04080c1c182c40303050200d40400051000c0f1518000807d5511420305800141d2601c0d5100100224400c52070303007160400d208010081446a08a44042110300c92000007040a0341d00b50b040b9821503801034011301080d521000704449003004544582c2c42100300140e80c1c41c242d101c0481d98074002100c1c9591a2a03034541000390103596041c041d950a900c1c0e440c0b1501c0c00c01c0110300f2807844806000c8400500d048020403a1030a5640c3d541081d8010305091103e0a216041081a192140111b000a40e4030040e141c4992043d548000219a6290742045007160b0303140d1601960f00210401400c1a64424841 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 405124721 1250 405123471 405123493
    0x1f0c050c01051602011503020604090f1803020705030c010f0804110a090e0106031a0402031203090312130201230f2a033004080702030f250f06051902 66
    0x2d2290600683c14070b5900b8142e030305690030003801e40300020481d06600440c400b0410050719640c05031402d55001030004a00c0e441004149070080020b64004060b0048081c4400c09064001ca54a81a41e005500384d542a202c1200151031a0200000a030002003109002402140d40a900c1084102d00203002d8002c15544010500540c0d4500300e000015135504c00d82003003004205075003851910480d0030a00e14900d030a40009844400a440d850900500040024030192044c800c55008180b040c40d03000c928100310190381c900940a002c12804510070741c2c40b0b041c940b1006070741d56007110724046c455840d1130102120440c07550400e000d0480340e006c1501c81402c0004085500501e442c203880c6c0110b0712900c1044800310400d842000e0508000e20404603522100819078205038055082807840c2d1751079240d880441e1910b810581c0301c0c00240500c0d0b030822a089105001250100c0500510000b00da172503101e0300b0204800f600c1810080b440810550f031040069810a0004e05518010355908070750b0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 405125971 1250 405124721 405124723
    0xb06070f050a0b070906030605030a1a04050705060d090302010b0f0f010e2e1d06030f0c1204030207060210050f0609060105070b0106030b0a080109030903060506030c030708100507021f0c050c 84
    0x803d1369a40081094004140f0403150b06100da100280001c42c01000e02d80842d4868010030040590f90880300c8411070002070900c0020010344d8014000605031694918a4968480c001c1030102d100b107006508041e4184a1880c19540c58495030600902d200c1c543c07148080152600b80b88200400d401203a10710080c0740c10141c9401d403039a0414120300c1e1960803044c54100901c5d1201000c0c10051944014401d040307980c5814013070300d600050215003a5295120710310707600094040c40e070844070303008900c0040104140c3c0c08204102110392039001c41d06103407007143c6c40e00242d030070407540c1c1003100480000086161400000d9290820f0301070502e140b8001841c1c032802c2d2031402c00d030000c201090b25644050014140103048400408a0710b0003005082129034000341a00c8252201809481d147c401144a42d0b505002083d05548010101e99000b076641000b2600d8105943d60388801601d000c000440c0c840c00410120400d07103520400921607505842070a000704442d114000410101f4003041070030240c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 405127221 1250 405125971 405125993
    0x30102030901051506030c07110a08010c03060509010b09061c140a0c0f2c04020405030703030c060e03090a06140910020f0f011b0507060f06031a0a0b06070f050a 71
    0x3100700100d0b0328a811491506000521038216001d0343c402c10811074640d02034010b0301c401e00c1d40164003243c58203804001442030701058100034800c0d440c000b41800035980650114084580075039076114182c0c0d0f50300000107107002d0001d00c580c004000b0460040004c0400d506e01c0a10107280038001124100860a50000c04080b44c10700021035440c0303905110150071010b02c12007600c05141402503185501c40304a0001e041090384c0000044499091145584a805541c044c00d405000c840c041942c0c1d00340204000d503002c034244d8210f40340060110502c1008001c503003500b03034058111810f4038030f09242110680b0100210a400c003005122601c45580d50003060404001e0030360081c44028000c2c1c507140c0c202148841c0c40141d030383c03401c0507850140506964140c80040c03c1e06046458000d582050350207043ea030703c45040b80a2510002000300856101c0050101c841c03000703e0511585c8200c290350481e00080f098650184042c444140082c840c102e29400d5188200c05580005101d6940d428100c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 405128471 1250 405127221 405127231
    0x607030c05190b04061b090509130203030c010b0f0f010903030c030908120319060303080112031808061b03060108010e090307060603120e0109050a0303180b0301031b05030a02091f0503010203 84
    0x2203003c188414400c00d4002c84541030325400500081e542c00318400380004040e4030900c1c0c081d10a490000704e2604d8810300e403526058015041c1d03580c0d442c141c80041d00a04250440f86e01c100800a40717039105040030021000d000754182c441368002e60030354800351480d0704583d034101c040221040000c0303441034080c8112003c2c0460100348070740f2070415040f03010f1110889581000d002c0d103420010800b01c2c0d84004c0060454200d50f0030000c0301100c6050032030349034805010302e885d4030b0f880c00d900150207400050180d1080c5050b0410f60441d03000c13504102c06520081d290240068215001032206544440d80b80303170815101012285400d495a07220003c1d52015401650310b80009170746800326541020f007002c080c4801346849900241410001051240c043c00003400b00490103680368921401e4076620800f511105018540b01c1d030303417841c001c03e5048080c0381411078035048000005d4a8140028503001d16540240400880e60750300b41e040e1048501a80800d548100d905d40002d9280c4080c0b001714014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 405129721 1250 405128471 405128483
    0x965130c03110f0607020307090b180f090c01020a1110030207021903020a0803040e010e090118051c0509010c1511120f070c05060a0509010605060a0c0506060f0607030c0519 76
    0x5042d400d001c1241d100c002003030981c01128100b1000006030b40102d000c8065981039540028112140d1021511100e13501d101c68030003400701c2080c8503042c0007c1640a10505410048400d08503c2c003004a03200d50200760000c20b40c0c1c0822060303100c1031070509040000c464441c0342c01070a000490700024001a0b02d05011080b0b10a000418000d41c11b0243c0307120094810340008524007460039102825000c0140300d170604510305140458084502034200da482035241e084204581000c030b0501903220a030300802410f0161020390480700042c0640180c50105d101611450300c2a022520b48282031080109084021507582210340d29407440075000d40036003160507240803610329190400038100d00d400341943d4140500d865103c00021400201158044103084000c14641c0340c00d41518050181a00302c564051404542140c030700340e02404003603107035008104aa2241d2540030034040120011258250001410444a00403a000d509440c802c1445070041700e403503000c0111510202400c001040f43c003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 405130971 1250 405129721 405129743
    0x5190501090222080a080708070215030108010b0103150b0c07080d0e01110106053007060f0206130302030409020715050106020309180105130965130c03 67
    0x1440c0074900803d19080541201e003002d00e040c03281050b52000f8900d4010005140003c5450400c00030100341e0b0142540034010f00450000b41c1200300e003036042401402c0d007642c40c2200c0b89030a50300c84d0181d101c442c1c200c06801030140b800c00c42c40b214039611148502103103128400c00000c00440400401c17454160030f07560840720300400000189080300803131a549c0241e050403014820741d595048840040400c500381d1449040221104661014003034030020454003c0c082d00044840d0060080300d00ea0702c069082d42c00e00d50302c64100c00380981e94081c0280040c0c1c0305110502103c01e166005080f5140610300d00004000882c5918058402c26004080142c0000c42c038049541401d5140c164584402c2421103203960400c0c0100f050000850106205c40d520780d1481000d004941c210150302c180412a08012004c00860442d140a07204c0f000307804403c00300c100d60009041011181c640940c64480c040203400d0003030aa4501c0701805000c03404a04004001d400c0050064007010004500c42c4040c500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 405132221 1250 405130971 405130987
    0x151008010503070504021801050a1101050c090f0603070e0f0616120201061508070c1e0f020306060105070b0f04050f060108060703050f07020d0c06020d0e0616050705060a051905010902 81
    0x814001d86604ca54021401404201102150351070b41080c055028030b0400d440704406c5a044030089582640030026520785011300c032041c803821004010702c2200380c4c0c1c1da002104620050003030300c1c80102e40740400204030780c081d68000d01d0010110814040c0003401e050410350360301d107240240b00814004446105000c1903202160b6020b00445005180381c40c140c0c110054480c20203401148028524420001030390150f000300f00b240102900c1c8888050b000401031025442c040c0c1d0300d05c04400d4140d11900c074103000251b46602c540202c4001d10740c07080201410b5190030094007104000604101d40030701481007112410801080064002c24901004020302d00b005040031b0700300c070009041450302c120310a00700b10105800061a200414a502c0c100355100e50364144070009001d8401c00c0c0341800c0c00c1c01e02403d03800c0d03000030700103010390050140c20ba041400c155013640c0e103108100006049801c20000180d02f0002c03030f40304541c00005880109903c4d0100c0c5422401c07644260000401c0075800700b9800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 405133471 1250 405132221 405132223
    0x6050d0c0903030815010504092f13050d0f17190207050a0302010807200c0906030102250302032b0509060105011d06070507080d170c0a08151008010503 67
    0x2400d029480c14214405811074034000c0801d10700910038000680c00c0442030f1380d10b900c1002141e00038000501c04010303100502001d4804200784256151110022422a102c8515040202c410070380788104002441c0cbe1a006c1403140440c41c0044c180c2e0741500802c54180810b51000d119003070311140c0c004803a5248284281034013641c4030360026000f10750010601b44010f843d031503c81d01c06e0b650242828501c90f600c01504a440c0c0c0409a1500c0c101c0700da0503a10750703090318002036004502d0347c11134030a0b20564602c01890700700e014030034a200f1b411030b003500700c496444034100e02d1558250003881903902d84054161001900d40d00d0340760781200d0700c03289070240301c0e0300016110f103a070061103610190142d540745c20002000400c031101c1b444c5e00164042d0711304240359200300482c3c40d1590b00a0642e42400d0303a0713040303540e11055103241c1600441d0200c8444195041c00b940d50303501c80d1020702900c50812603508030882e403002004210300035540010f51020030a030340354402c440700c000c1140c0d00d10030035604000a00d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 405134721 1250 405133471 405133481
    0x9141909022508030c0c031608270d03030b0114070f0b06091b090a032a0602071d06210604060c2a0804030f03110106060e090a09060b0a06050d 63
    0x2d10184400c0a564000100c0764004c42e40c00c0240081c11544840c0080350503070a5104080803241c00700801504a8100600000036181180f002c0f41c51210811042903207040c070301c40201042d903100794802c1203035000030702960202103990b4041c50058040d9290b0304801300d0799030000700d06444819002030320743c040020030045554001001c1c0c0c0c1c000c12a0510394560050481c101e580761180080c0440c4151440c0c403211224002580c005c080564022812801c2c10041c4170107860802d034110800c2d8000c55114000182401165030f00f20392314500c52045005158800d0000c0d20b0142c4c003c0c90321400d1400c01c1800e00b441c50701c13800c03400c0140410b8101440e20a00b200d0622207424148444403000a512940045011510102200003400140c03500d207441c926a1180d908003c00210400c00104117055014410250720b00540f0000c1100540701c40003541c400d42c4071800540d0140707045000413005812600170780c24040c45020701103121454140000c0a00c410303904250002440071603013081140c154054 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 405135971 1250 405134721 405134767
    0x50712021525020402090618040507030507021507021c030b030106080c0a03110f03010203041a10181d030a0c0221030a05030c0c071517070914190902 66
    0x3060b031030420182d50200d06900c0c580095000403162290800554956030103d8999400080a03141c0c0c44000c0466040507400c042c001600803460720780012100350103845803c1c00341324145c00404040725030350321020030120000c100204500603d100c00e00321022407420801c254140341c901007880311901c002d06007141e0711035001c040c4030351001114400c0d40d211203000105894200e511803070001e003408041800b4543c00740106801d980700000b04020702c04e02d4100f4401d14081c2500c443c2c542d88490702407510069072402065a01c0611050910325080e041e40300c070040380c2141c0c110110120f8984000303815604102d030084040313120001c1580851402540d220540b03070444c03c0240e00b201c80038451a0f030b02d00640610a0a0080000c081072801e40d443c2c3c10344802520110032268480d4a40a0580009039041400c50105510900c68004104000110b03842890700380c1d20350351940c1c50007403614070300c0d00c014144641186000b91f201e0207000348282c3c4140540048403001d41d803004080f10403440703074940001c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 405137221 1250 405135971 405136009
    0xd030507020420091c020603040b011806030812070c0209010f060f02120f07020a0f0f09110c150c0408100219021906091505090d0e18010e090a05071202 67
    0x2c0e00d00900700300f100360350b1841c6042d0303198404003c40080c00c9824400c40440a94003810210801c0200400f40d5102410384076040401603c481010b200001950b00c40d00004003504818055103034000300008984e5401000351502c000c40101070780200d01e02003801c0e040311003c0d000644050105540003801d00c1440403040c4000e1844c02014003c84415002c2c40c140a040010000ba0207820340d82d409200d1006004404465840c2d00d50301c0310300072070b07c130b880380710f156041c5080055903c24001a5000e59030781c9280480a8038100030a00000b500400004101252412080c00045000c1e801000008c2c110ad4071203c0050ba03c50304904800152800f10451008540c008a801d05280c1d11551006034600d50003a400318640441d4a0030002c0355240c0c190003c1070a11300402c01082e4040019002003190343da45890a14404120501c22402d0a58041e40100b06448004022030f03600701d030416a20041104c280c030104c00e40d680d07480742040005c2c1c2c4520b03010281035116000794a4110703100611540c2100c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 405138471 1250 405137221 405137261
    0x2060405061501171f0902090109140d02220e03070c15120c030906020a0309123002120403020733050307140301060215060a1a0706020403020d0305070204 68
    0x1030002010605059500715102088101042824551402d011602c05c000203180302855140d03ca000001c1d0009081e1a00280045c44005040241c072040e900911601800c02d000c0070500350240003110304000750071b18a01200b1010001961090302c10001004100740141d50758101c241840b1824586582100300c505202004241240f90844844566140781d03140103d44a940e08005900501200c080a003015000041c0000c1c010341c9075000c00b245a07c200e03070a5005000e00e5104a4000c004d055000030103107465408207038008400c0c000c2c544030041e0507501628014a010700c07100c8a48040c0da044001d40e00c0a04244011050078038140034003500210001b100b420292407030106031005011401c1441000070100b0390702d502c54410009a1001c680501d540c0b035a40750302c0290b0366401c40e088150318800c1d44003c07502170f140c8090000c0031100504041d4120802104101c038456001180031140305a00f044000010303140d1028bc1d01d0410b000c1d8031200d4913080c1d03e00511080d81c81101b00c48940524078 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 405139721 1250 405138471 405138511
    0x121c09080111120f040501060315052719050703080f0c1908071719081605070c0308031f0308040302040e0d09060503060409150b0a08030403050606150d0c0206040506 73
    0x14107407040d8801100d5000d0266034545046c801d00401c156007001d0402040004444200c0c0c1c0c00e500030710301841002c22007003080d12003a101c0c036085020741480904207810005144509030800c0b46d092400070700a0703042d114259030302c1d526001147d20a4100c0343c0e81200c00b080324000e102003804003d81a070300001c032821140c5460b0b0759802a03846201c038000d1400c08212121015026010b050364038244020361a14003084040c1c0c800713410041d0072101800c0b10324145280700304a43c81401a2070806603c50061083c03079007107030303103100c410b401c01003055942c2c02c4a820301b405143d0b19504d007440158010720340141d44130f0850043c0420380d040c10901c15004c0c0d1051007802c0903d0b84c0700d008041203c0c03007072070015101d485180000700076020307004014110800d1105100e0f06055907a10204598800b1240c3c07408550f2380d80a513584030b0185200140480c0c0011000401ca41801032035807035002c1000c3c07056843c2441c5881c0c0f2a0031645150907082c0168000300410040000c200030281e0070002d18066202c4400d90 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 405140971 1250 405139721 405139747
    0xc060203040b0904020a090b07050a110a0315050c07021809120c0a031d0406081e15010605090d06021204030314060d02190801050c0c012009121c09080111 68
    0x4070388803d0300540c0c0c0010340a46152140c8000000340c10791400c0750b9511025401c0050380c0d076003954000d1328500a03040c0c0c3d69a07a41340180e10441241c0c4d00500e00d04441e240e90320f00c88002e0500801445040004104040041e80d5954500f810035903c0b00c1000c189086c0108003c0c034061702590501301140003003102e01d0310010009000c00720154540380c03e452003030092250b00c0a0086030714401c1d411506101000c29902d1021403d60784c1501204212042c2450312056650740e403495501200303101805c0c0c0e0041c072580744500010030111700c000d08104582c1e41c0d40d60b1110101c0e40600d0003802a111164140020142e1500400d80c0003424118618000e007050000543d0100c07601d54028802c01d800001802901443e030010b0000300383d03c000030846031500c01440c80c45540407061800c103030f510b0004005104441c0c0c0d0740034800840200703002804c10741d01106009650b8001c1d240c107503851250051441ea61aa0780c0040310201c0700075510030720098500010a425120b82c001007800283c41400382c8004904 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 405142221 1250 405140971 405140977
    0xd11031c180603110f130e1e090105060105091e0d0b0a050601030614040f110301030c060809160501050912010c03061d04051203040c0308030106021f18120e06160c060203040b 77
    0x1d03c0e0042941d8400c0802c0440c840105648007d0881c0252400c2006448810440010248503050490100e648414005080710707030449400c1e003c0f9000f404840c205003080e1100300e86040360042554001c0c1d5504001480804607100d04542c1c03d0402d03002c10002298601605800c881c0a090034060b00b801c3c0066111481c2104103164041c03a92000b0b690060b180c0e41e08076080500f1219140c9070782e540c5904150104483e240503100201c1c45010100d080f055002561480c5148140e1204928609003401151640c0c80142d0740780d40300700c5940003003c1030300c0f00780b24406c40d100407500c00060381071130100004070403003404a281ca4019229820440410404a500400c0c21030080c00306550782e442e0b240c07505001506400182088102200105026400082804c40d40710400104502c5900c50060387e0700751280c1e2542c8c21045d0b960f0708200700000b10980000003142c20b0a0404191f40c1c404e00022490720307000700f0706508102e0a021450024485407500c40c1c40500100d00c00b071454541000706102c0148 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 405143471 1250 405142221 405142237
    0x40b071b20010203070804090b030c1210020a050f0a091a12061908030f042301020c0405040206040909050307021005090108011802090a0b1b0601050d11031c18060311 73
    0x1a46002201d640340c1e2013442192606a03000c0040b03901c55444120080080240c0b250090082c4100354055408e8030380441c181c8021b103034040041210f4507910244501a4000075440424440203005d80d074400c0c102e000152030502090760301c07132110600c1c010100314071703811440d0b0034074a00f0420003070201202d41c80c0714040d0340240c00790348600180a24810030b400302d1410340c2c0024110b01000c941d00c0c890440490041084500c0345880580c803021040000222440004525016903c0303068610baa07414242c1002e07038032030300091001303080503940c445a43c2a119201c0d0102c3d90b54000140304811440d110003201004005031800394140906c030b1f00007a181c05d8040c0130381c403c1844010702c0c40303504030311540480d070310700700041e00080384996910b0200c0704d107420001e01d5554680d0105202003800000180c494122a001003030046000540d072500440703c00b24142485d01401400103c0c01502d01106072003890302090303901d00f60704016843c0c110610702172036003010041504000709404482c0304501074030120 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 405144721 1250 405143471 405143513
    0x303071b030f39210b01060503092103130204090615080f030a141605010c0c03020c010c0506070e0307090e1f09030507201203040602010f06121202100203040b071b 72
    0x5041c600013510310011854500a01c0000d05000205041358441c01860040e0014401c480042e600102d41d11040b5002c100142180101480010185c2480b1038900d0180f84c00034100050010903a101e075020f854140c0c2001980500191042200090030419501e641c00d41c0b4014605007440b0550050a80760481310004007604045112251040601009407101d68018001c10981b41c00b1031024103c450702030800e80141c094500311120301e5000d201000240c55201c005403545070380f00c520581e4401da01d059403540600c10701401082949291041021101401004014003105200300c2e9030002c9140d03403091005420701c3c08200000f5000415609000c1d030041540c1c121501001494030240307075141e10a5402090018840b0f801e034004801030083d105d490f4000e03c2010381c46240c24041da4124401e0301c9810034500c0044020841412480342d0468042c41903070050300003908100c0581c3c0090340c050347c2007c1c81c43e0900180681144d818a240e9000320705070064071903c2c0d1a4200401e60b043e582500c1303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 405145971 1250 405144721 405144749
    0x91e0a050909100606031a03060f0c03100f0f030605093d141006020d050f090a0b040605210f04020d0201110a0501021306030204050303071b030f39 65
    0x90b201c2c00f807140c00001c0c0025501000450b41e500c0000340513180301070543c40815039480d0070070128200880c0e0103208800780c4c08050580d8881d11034510442d40010003030003410f0411038010400104a4071020002c06411040c42d0300c06095060400132110043d10306140e9600844801030780f0f13100c0b002e00c20340300015018000041d103401805c0400d0036007a1401408554a090380c2002c00031a6003404901075011140007080d211344860003030366a45000c008280108506218422085001400400180c18060060b20103d0317510414141e030740d04107811030004250003094511100290801c0c0d540038034008003582106081a00030b074114000041c101a0060845c82440420f590040c1b0480c007800c1550400ca458401250038040e000b900281c1d511484a401c0c1076001441d43d1085c0242c40136180300401840c80c00b542c50f0b485060380100d2144042c9409e18072500000451044150b0150702400307030085c003d4030003480d06101c0904061315110f40d140c80e04142c840e40158468100ba0f420f41e5000b44010603 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 405147221 1250 405145971 405145981
    0x2060714040b0318010c11070509060d05070b042301050f090d0816060501080c061c0f05070302071b0308090609180a06050918060c1803010f02091e0a0509 68
    0x3014030454101c244404400001e2040028955074600200140040200482220070710100d81e12102c20090003803941c030484043c041c52418000395604074000800020360b1510036039480381404580da1046d8030f55180404c04104072040240b143c940940b041099003640d0841e10000381c03d60241c3c0c1001e802c4054082410301240d181c98800001440d0008111926080d042d00c08030b54280713050900301e6031a8108000058501000a91755011010003080c0c1c60400007003080c10b08001032881d80580d8515141c13039400190b00d000344100e600403403090b9000b40e07588109080c03010603020318158007907460864000c100049140041600c004000856030665240302d502c000800d00100b00b4001400380f0b8807042030261681d81381d4040360488109a070108120356130068088031220003094825100d030040710002e5032120351039004058081c410841004603148200110b03003120060541e62400700ea001880014500d0700320040e01700203003d00d0401924504500200f4114640c6110780e5020703c10f0309010032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 405148471 1250 405147221 405147257
    0x16050f2514010c0209010e1008010509030a080403020a0b0f0f0117100f023f01082503052d0d0c06020f21010509180d0f02120a05030a06090c020607 65
    0x1c3e090740007001440e16584070580c56900c0f2000341e841c3c259461000b040001e942106000d41480390031094091401d00c44100c20070355120200074400c5045006001d030800015030702040c180c1c05a070b03003542401c40501e01100c0740e00c04480e040e00154010b9113190281c0c0c8240c0c40000361428840d40b40f08012030a403030700c0a0031002a00800040d862400d0210b240d480b03640d08a044103401140c0c4600851001404601d401c4981e080c0078002c480309034214481c6905010740031102220703c540d00b4080c50a2241c0e4035103401d4100390300605c404c2c003070702103079040804010030003a00700e010201c90101815115060f40805071101003a050300412007134012400030221480b400075188210529240e002070b000209011844141d02405003520680312440800d0441881902d10043d00e40d05100501c0c00c031110304da003900d0b041d50307104e030b08000c40c400c085540030b0820002000d009083e00580700c03c1d0320307400d16421440a4074000e40015201c41c0c64000000340072a4006041900807506040a00300c40303038403011030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 405149721 1250 405148471 405148487
    0x8090a0f031107090f0b1503010603020f07150203150406080d140d0509030d0c020601120f11040c0903050f030922020d060e01050120060c0a0516050f251401 69
    0x100503000302c3c000011015440d400a1046000e99030003041088100c0c405c0225103400c16801000b0100188014400c4601139030007840071100306040a41804080d07900d603004242c06404149159030080203110414801011005800300d086400340300071414107030720f59514001000c141d42084450280301c080342843e042208c104540c420300c24015440c0a040656523a4000b16510904901d001d040c0c0c101c40d440804c24505072082e079007408080c407207961100240350340507050588a8041400d04802540d545110740340740d009564030b5200ca103510f1410328500b42135412074044000d400c10004046981c2e030740003400007004440004c1c9403000f280d0382c0054000780600c00c80d140c803051400b5408070300e070321101c08428102c0380c09070307200380b40c843c44501c00e0000d440380000300d91003071740c090408178440c142c0d100b02403d1250303580d01d49141490602914a042803500c800284d40a400140ca0428450760603c1492040c000401720181c2d0702503450310a040d9501d441c800c07010f18002017101144503a20070301c51 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 405150971 1250 405149721 405149747
    0x20d020312070302160f1401050d090c0f09091220101b2c15070b010614030907140d05030d0b0109060c0206070b150a0605041508090a0f03 61
    0x111005055500700907030850703000701c81c1a40544a00c0300e10301d40780d03102c2030305100650b22410f400c0c0c0d18030392800102c0c21041100c1c2072480d0600000344005c0b4105012489000d10315401102c82c40002c40c80d00c8010919001583c000701e0300e03a41000700040208a134142d035400c0d1036205240075484070403a1200100c4071035089101d0061f070302504c0d8a885d0a91025009403201e02c0003103041c0b0406513001c490940b00c002101309113080e10035240741c0c41c141d041406000d07a01c4821024050340002c01021000e10300c19481204110742030898600140100303a0301407011a0305696011a540c0713142010f00c0f0681e40c41400e031107504900c1b15108102c250586448140d8101d03d070340242100e4039602c2c89402c0c4000f80c05141310403400110034400009500f4031901b1840142900079082a16282107a1600208580020b200000d0190b0341e8521030500c1c0c0303c4680001c010441136440d2501d6030305218040481c4810014014108010441030011380361340422000070245c0e100881c00500d006918080c1d60b00640a51 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 405152221 1250 405150971 405150973
    0x60a05090702060f0a061d1803220f05010c14010b1e01020c031f1508030f1c020f030f090a14070f05060f032802071a09010b01050a0c020d0203 63
    0x209114000d600019036600a003024914064141d4580c0170b000203c8840e17200e0034100904550308000c4003180c00c0e841640043c082041000461f1205190a14540c44050b440c600c1001c0c910700c640e00780000f484014058900916010100762070540000c14103408044003910340742c1d1003059282c581a0035407060321803e00140c84024011070014002c52031260007040383c1e025014050081c071103450045045e03c001c110340c40c00b19060040500910004000c40d01300000d03a01ca51080c08946001d080014200340b484010200d0b035a592004441d08100e106202200807207401803249810b400489801c0e207902046007404400607a0b15100c60625010f4445405002c901c01d018a03001600030208001c5c043d280c018a0300e0020a41d80e606100082c03040c0c81c1c6aa28640c01400814000000701950031008000b0481101440c0c9030701050400f2a84100c10072940c03d650540409558001000e0396540188080000c0000d003043d500083c18500c2402011410042c004118000319560307040c40c110034580185c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 405153471 1250 405152221 405152239
    0x1180f0b04030b161b1b0b0a090909120815150309010605150901030c0504170c010806010f0905041e02040305010903020c061e03100b0d0504031107080a0803060a05 72
    0x200c545095511a0009442e01c4100c0d8000840c2d0130328529000c941c05041da0b44032200c5181c04000740c00c00301d103028011944122080c4c0c51209041003e1904005072400d4154031b43d031500384174000b4100400742da005080c21400d265008001c50084403854800c1e00b41c90030940d60a075640d44694004801d400c4841e9400407114164104400040020303520a0550034000c205450b10388041002c00b900200c280b00940c40200300b11141540300b600308000c082c00030709003281003940b5282d105d0001981c0081c442d65552144882c50318941c0d0015850f41c01507400e0a0110803040540401422001c05010742c038080c03502c42d034000301d840d9014041d0403040000340d04d04545594881c038185c7e0291981603020780051155595a0815180280454110645a014010200002401280054000400e120000b1211540000301c106203500141100318030b400c5c5c0020b040c505858007030003a02682902d00c0c8a42e008550510480a002a8054075a82c01c0300034240c032562100e0001e50104a90307040590840610 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 405154721 1250 405153471 405153479
    0x50303160308060109051c030e1804031716030b0307170c0a0b03131e0b25080c0a080c09060705062d01051c21030e03160201180f 57
    0x80450050300d40300c0d40c2c40e00742c9902e070100115a800010f00541d0341c001e07114000e11071400036441000ba009032103400c2644095040b0740014110010203040d24000001c401d003004101648500c103507054005030078050009042c2050101e0103090b465424400781a40c84c03001c62815542044a40c000b402000600210724405c03030f48040d120001103c525000c0c00840101145080010090b03c1c480c0003a50000e412041d0152075003004607850422603041024805411004a415140d4151162242c921254070b0108240c0c0c0703c503070441c1c0003424202000b40c40000d20824481241c11150b40303444504d4401440c0d110114400994031642c03c00c694069000620b1a04119000c81c4c140d00c548464100603070195800a03038400342c1010044400a0842420014091454460149030064166002a032079504e210740e6580302000d130548440001c0c101f03210301c0e84221503042c0114400c00410074003440c1480c808002c030351007080c80d0100003410f0000d4042d582031000b42810b1185c0041c1501407441c0700c03040d6a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 405155971 1250 405154721 405154747
    0xa0b011d0a0605030c090709120c1412071401110a03080603061006050f07140a03021e0705090103110111010f0504030908030c0c0402031003080f19080f0a050709050303 74
    0x2006003028244100e100015060410500c5100100e0b8005000b0f00190040b40080096018004000105004503443d02140071038025403540c0300c05102d0344000d0240303410071060380d995040b1400729030b11400140601c400c81c1000800d0300d5080710a00c0459080301002140184e0344e841041c04170b242e03c5d100b068142d80c14580d002c4541070080d101075042d55516200c00c0c0400c840c2c4040f40c0681d00c041002003104030b40203130f01e4bd0700401c3d829010f2035600420700403402078503061688040e0b080d001688170f810b0a81d0351580c1c00007140510350048d4000c1c2445480c043c041110303044144030107400060070070000c0400c1e0740525500504621500c00030441405103078111001054140e40070350002d41c80240204180c240042112555801c61005004141812007040041e5100400720919040d2848002000070b041d00e01034960051800c02c11511151905100929001c030034030381c1e004200c05041440749111220301200d40010075118042201e984141003581c061051b90300407034043c48002884202410 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 405157221 1250 405155971 405155999
    0xd09080a0306060804050a0b25110607090f09020306060909090615040c0503130203011b0201020d0b030a0305040909081621080907060c0218041a13080a0807020a0b01 73
    0x1039032420031110383c65500c202c0320404201c2e001052507003d50400c802040c90044880c2d48040d03c861908140001094500105030078a80c024012443c1181c60108520b824091254004490b140c01d5610b20710703204100748150003600c25000d00c41d0340000441c0c8241c41c2c0c00d04403102030b40040c0c00b12170141040014690790b0744044450180c065a06145241d842c5090f000d80b084040060383d907141980c440d0060074606021400c0c00700e91640d030380e1840c0d02003080701c84445c001c140156000161076180c1c5528100982e81c1e0f0780c500c944290070101064002903040400d58050394a2104006402d19191500840798410800130515011080030741c0420881a418440f0039904000400381e0f025202920a0b035400c1d509598000d0b25800c54032050107950312540001d00c00034001404a0031039403242204d0405036506a8040d500f40f020031110b900e401d04441002074006040040078600c14551707480300b5183e409002034060030054040046204c16108000314000290070002c0441696560341c102c8419813 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 405158471 1250 405157221 405157237
    0x503070b0f071b020607060506010e090a1a06070816080c01060f080d08010e16021f05060a1202130f09140c0307050405011206020a02070e1005040b0306190f020d0908 73
    0x2500c007034407115141d0220806004181c4e4050039540c10280103640307000103820000c103183d04115003426500c0159548807440c0780110800080041c60658800c80c03001a07a003c8801c060107040b0420000b40003410030022200016000c3c05072200c1f00c8801d107814803603031240758801c4220707600741a00498501c00004010703080718040350071581c4078203e804040d1140c078001d2080c03503011540c48000801001aa03202071502038050b205642a500f010356400c9042d081c85c0b114140c40c503a4500c10410103003440750020f009403454111401000c2d6880e0300040c10002144030801d4000d4940b074031085540301580240d82403607446064840c4140301494495640c10040d02c2c85032003803281c50000246403e00b4482e8505030b81c8000f04030081d0506988811020358400c5802034114400e0010004541c00892000350049000c984c00ca50020316000411042d2143c12603c0c5100390001c0003480b040291218191607100e000d00c02c08295080310a00748030090040015407517055040810755020443d424008002d40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 405159721 1250 405158471 405158477
    0x5060a0e2419090b01060f0311031003020108131707150c02010f1107030e10020705090117011b0507020d0201030e031204020301050a0b060711150d0213080c13090503070b0f07 77
    0x2160030b03001c100141c0c1c481020241580310010300500090f4825141400d200340303d42000300c0c9600b00a900340d0303480d0b84101c40750000308200c8a014000c6692180f10580c01a0709468452200b62840d1a107d03c40203581c090a4210100000d144003005503090026511101001d4108a241400b11019001c0c104030318003800524540a0281c82c4003440701c0503205c6440c3c0694030010005a80014049a0318101d50700704154172803290001200e699151710a8082c080d128088144400c1c0002e21a003580c0c6d001c003c04c8200941c1c030410201d416842810740d85046d4040f00d03c0443c006646c001078000340341501041041703000000c1e17000e4485100800303072409544290000c01460703540b0241315084503030300152035500603000c004c06c0c2e002c141152480f8500c0380004181004651a070400ca290395405459465001078001c078406007041d680a0544c4002c1c003101015020a86020000a007007070203000e001c1e003c1581e1040f0100c1403040410554484942c810342d8070703040d400d05d80450011000119611000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 405160971 1250 405159721 405159751
    0xc080d1d0a18050f061203041a070f03120b030a0f12030f020c07030c05030606010206131403030103060902040e06060a0603090c0b0c070503060703020703080f13170409110705060a0e24 81
    0x151b0620220f5a8080c00030903029509003401c0400420112041d41c450211740f071000e000078400b04124080f5000b10500c6a02c6011161124650044c259841a051a4800e03040540707101d022400d4030303140076807266010001d41c00104ca403c00540050a901c16400d144c0c0780701051040d1544800104c10054034003400d2504961a07031881007590707030201140e00c3ca0058010001140b069040d01c5808a1854402e6501c000c584904020080c5103801c05d038026102c50f501c8500c01c00960625104501074020b540d0007034985031034000007184061782c50f40304500c101030340d50301c1030b030103100307003441c0c0000030302440c4581c0d40c0d0342d500500100d0f503169401d0103000e1090040f40c0100306503501a1080b6a06243d1680301c0c140360380d485400090380410000c02020141c0b403010b4040700024001e101421191407418501e50300c4a0401c4103542c100e039082c488034662041c041000308003060001850a41c4010f4492001c600800d20421080c1400106100003984500d0704090710b00040705100c00c0b61042d10300c4c100e0109 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 405162221 1250 405160971 405160981
    0x120a0e011d07093c020f040f0e040f15090606080607030606090602070510050405031504060c0e031e07080f0d081308070308091204120c080d1d0a18050f 67
    0x44511001d110300d0f4a111004c11102c101092184120440d00c0300a9001916101c5422050999101c00d448501902e030006040c00007420b0380360104080d2260b215207a246103032655400210803401e08001c0c08558114400d000d0016003a00283c441d694455001d21030141da68120964900e82076458501107402c244001c94414460f003004401c6880c10b50081000710b1400f0248151048090309102c1040070403c004107082e1810481c03901da505012420080724603050070184121140c2d80040000c0001c003244030740e566980091000250342440b01c12001c0b20300020700c00303442c005050b485502c41f405507215500c1c1e04000425001c480010b10345890400b603a407010594030552000300014003648080c0280c00100c1d03c2040000d501c014014116801400c001c002c902043c0c025521200b41e00d5520807500307081001801c0c00000621100e0001d0640300303c0084050301c004140c01d20856003c1205900012980c0c541a0880c0202950551310210300d03080709a00014050132a0fa800100380c0d0a40460 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 405163471 1250 405162221 405162239
    0x2710020312010303140d06060c030201060f12141005010b07050708060f0106180b0d1e020a05190e09160f020a1709011e030e070603050c120a0e011d07 66
    0x1000180c1d0340704090426800c669058607000d407416868081c0d00302c144800c001501080c4610400b915094441c16540c1c00761349030081c00c0d1020381c0c0205400c1003806004008030903081000030542d9910580350460055211011440c1014010f401c000b003a0400e0000100b41031000002c1c16107c2c000d505443c0070300d80720105170356100300648800c01c40c1c034089401000b45900c0b82c1400040d4001c0107500074005a5509951941500002c038401c40c510782e070710080c00e041014070100304606c0c5540c07002581001803101002e00349000b000d545510348941e45003124000f0740f107400c50000c1706400902c1d117942070802d241415051a054400c40700450f45840f05115054000680c29846907070010342003105c103049000b500c540c0e80010f43d03850306000c03c075500600c00f000034890017104840e1503500007071a0900507030740a251032541d0380070341c06051902051103000c4040300112200ea1030068004402904c503500880020061200010065441c2010000b80340a690603410030100d01d410444000b076494003200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 405164721 1250 405163471 405163477
    0x7061d030a0f050a0302090d14010c14031302060c03160c0503030313060c020123040c05060c0705010305130803041115090f0f011124010605270627100203 68
    0x44000b2403400d2104200302031080005107403140041c42c015040908050100300d000c0c8000208480a002c1c4510300520701c10244103516035100603240021801201051181d40c61202500342e009100704025003c00b99140c0c2c0003110903040001e01120358445643d15040741e444800d03182103481c242041000a120f01c0c001040c0c0303024100300151424807000b244d0300c10b00104607030903a0310195500c6442d403150071070b1020a1040003024aa50342d03056441c02d850b214803025500d4014600c81d800a0044007584000021981c0c1580c400b800c000480d600c5d685031004800c10406c20040001d04000100402c025480001144000040e124100201c90b030b041c003001c0ca40070b2084a00c0d000030768080501c101d45024070034841d1030041814240701440e0261102c9044c640c0581403101c03489140644881140c06128006004008524046040101c3c1020400a95a003120703107051104030181100702d150348040c200d5420a030312035245040484403402d88a180c03075001c18003a104402042d0306880c40c84c000710031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 405165971 1250 405164721 405164737
    0x10612020f0f120708010b040e0a0c0b07050316050a020405060108060f0f040e2407022a010905100207060210050c0a0f020f060f090610030825020607061d03 69
    0x101408000c50324140010240007400caa94044101d050418620340c0504c1440e000e024800d001041040c048010300064503100c212140041d80b00b94000404604c2c00711b0039a084d2865440030690320100c41c00c000e031440c05103c1c507030155405c0803100041000400a502c0e0b000714400c0e1024450b903070752400191455401101c04d40d4104031700030a6443c140c940500001502180140001001ea1441ca001c0746000202180c0c4480c000340701520b110710000b10404a68001d030a031004000021843c1481d8610705900200400854250005031100307a00074202207018020250211900341036140000f5030f201300c00d128580141c0100000e140f00c181c09802014854001078408500d01038440004803a099107a03524001140240c502c080580c03141448024014081442407140b24240385401d1802c0506c00b8001401d60031590004200244440d011764800c0c250549948211071400308a80741001e840390402948900700240b0070041160325840151090411901c43c3c0c20907000035100c59903031203070b080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 405167221 1250 405165971 405165979
    0x5100504290912030c0703060603021302090f040207020d020d05031903090c0308090a03060f05151f08130b0a021201050613120c0503030703200a113109030201061202 73
    0xa01c1401e41810051554031010550403139181150f444d86030307030500c0c249030001c48400382c50701020415850045541200700d0ba00ba48110f10b4100c0010000740c0100e40c00328080e0090780c0200384032080d0741d0f880c90008045500a007110841c000d2900e4183c3e04ca900840f61441d40d40843c20141c14018443c0c4190b04107243c0c17000c403d080843c290780b211000c58000c1c00c401e6912802d1018048001400e502420003e0801e02c1c5003c105070400000d080001e28440205a0249200882200b85a00c1d4019852002102410301c4070035921040e00300b00c00c8244040e00170b481c141341442404080031444d402080380c1d00c480d100d0641266203c00c00c00016103c0c509800042c502101070600c141d8180c0000703002143c0c4030f001c08008440c2e03220f01090031a00040c0c4207401145441e01c209484011404401c68404025009055601c0c500c1d41da07207000c0c44940100600a11780702813840500e11588640c1240d035139040700c80e00c2c61801c404c6091005840c110300101d0065081c41400648540c50703146802c0d04070350081c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 405168471 1250 405167221 405167227
    0x81504031b050a06020304240606021b0105030414121c050f04050307240603150501090b130515040e0607020c180f150a0f0608060619050a090510050429 67
    0x24a134000607400180040c0c03140d1020030f102e04015080308072210170740c141254020441c1854031101030305103003040e01d0741d2441c101c403c145044140e0741f00003126803003039100c10b00c040038892a4004034904204d00c02510640500040e10000c13000c819031030b00e1541603e0460030310180e42d4042e4006c40314881134500400301d40c030610040c3d00046002003091041842482845041c108241c5c0c3c0e0030598406034020b55040418001e06000500140280c0e4094215001300784004003084020034901b182c64003203010740c140e8130350100701c81e5803480d5000722604500500a011049040d02c226485000c2030740e00b00c01520886105c2c0010b03040440c1300d2050b03103154451841c003a90714074500d121b000500410050481000f40300b801c400c0d0351444404c1e006001c1011880780701c0c908020026001504c042c10f01840f614041c071103043c2c421070308559140b5032a524a4520380f62200910f01382ca551240d904030543c0414080640d410717a9903c18003820444d45107400c0000380e804003000700040710f08070a2040340303043e50030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 405169721 1250 405168471 405168473
    0xe01090e0a0b18070909050118020f040b0607060213050a08120a0c050a120809011104030b04080703120204080309040b092401090902040f06021204140d0606081504031b050a 76
    0x840e4070310341c4101020441060f0300c0d1940c1c83c19007003289076002561210303030b200319800c01d10409104404c50401d00703111041d58003a02d0340014412410101115200d00d841e20070b104003544072441030b2180b69074880d00c20754a60403a00807500742403080d405a02c1c001c110107c80051072003230024804d1080c1c6580c101d0107190081d54401105e00c1901610103a5007846603001d10400540e18000032400c20040d035507130b400c140c100729554500751003040a207060550130900090000c5209207040d117070480d40c00120740303960b15005c0c501a00d0058074010b10002e020310100740020301400c04401044020b004403010058507021004200d114901512109000c1802400c5940d489100740c10340d5107295414103007802410b54540c402e0050303030b1290b00044c1040b007890340c01300a0300d0340420110400c1202e001105003807a05110b0003036540c54031117541c00e03c1481414592001d2100075841000030b0705505082d200c120216030121580d1200980b0f00b20005080101400c0c1d8007007801c510140d002d0f503c24042c000d10340349 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 405170971 1250 405169721 405169733
    0x20120030609040c1211010212070804140109180615112a0d0501140601020102041a0a050d090f03090e0601050a05090f030f1c050316110c0405010603060e01090e0a 72
    0xb004004a40b810b00851010030381d1001419004e4000e4810008000109001d40009090188400028010070001e1045000046401003a50162200350441c0c8820380101001241d0300d43c0740741d015041590a20200c05411803a503040403013a10703416140c0c00302080700007000321400034121041a8050b00800420f26050f44090007054401140019031583c4507501e000103544141d00c00c00840362a95102e0110740600c01c030015031503003c3d2090008500f0203182c03d03040b0704407140803056100e1640c000030300c00007024040c505461104985440c1008408218a0070004030010210240c0200c1c26440c0001100c001d050000c51060304181d482a040c40c05218041e00c042c0c00c205201e030352240c5044190401520100814804101003200a01084601d4001c40104c00b0980301c82e1000c001080080100c05d07480070950031260305c05032074540303e80b1801043c2c42d414a14450b210703950040c00e005c000038290768503030000010788040070303000000350340d949441c0c004613a01d1241c0c0c02015001220341c440881c038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 405172221 1250 405170971 405170989
    0x3111c090303090204050c09030606040509250306020a0f18050a0b0a090302100f14090a0b030402010c0b1008010f06050a06110304270e1b041d06090d0201200306 71
    0x1c46820085031a8a00ea8006401d440d0308940400381c900740450380d1140d0f86010001c2c00c0d00400309031000c10660501074030150302e0301d801003d024105820580060340e59802c41341904c00a58108104544525044500901c4124207814020004e0340f0300c01c4111501e4000d00a5004980000700001d0030185080201012504800000401c0c440001400005601c62103000351110f4200e41d60380c1e642c1000031102529024030454000003280060162411903184d00100005641241c1c012540340e503500c0c40101c0b00440f00e1800100041000d605000140081c240c90009403589000244224800440d03a0070031a000d520425500c925281020032619008281888606106000b035a1400da00d811011101c1c8001e0101092580c20703220040849408a100c0e91141450440180403211110480c50701301d43d980e0514140710700d0380c034241c0da58075a8200104141403040101a24842c0c13505c011110344030b0500960141c00740d420003c60720f0280d0015201070001280320590181103440d60800e000b4052 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 405173471 1250 405172221 405172223
    0x5010e0f06030d080c0c070e0105090f01030b1504090602071406010501020f0601050f150307020a170f120a0b0d0c03150b10110a0b04080d1109010f030902040603021504030303111c09 80
    0x5c0410001e144d4603d0f424481c00d001f40c110511301000652400e0180089407070f0080019806450b49001400001d180344012900600310120b0f010700100c2180001e0700601036108018400b500c00141e4800b044a054484040c1820820235603c0c580c1ea00c200698840401146101300c642090006000b98540700c50f45030500b50b0040d04004204202c0d804039400c6510655084000d0785c0400060382c20403210b1980c82e81e0824020300c42c01c1c14111106190042400b43d0011640b000f09000005011011240d010350025600101003078440502800d0024580703c1a020688290040c2071422803880c846002c2c03a0b005101c0503000e800700c960b00400031200045002100800c0c1e00610300341c8003b055286003820700481c01446e5107565014054030720b04c12261a42c540007041c000038031590b845603810400890702680c49040c086034078615480082c00511064200950201c1201e44264007415040050429648682c42c01c00010f8031000c103581046c007450081e40f0051b02d0b01c108a511b14101904454016 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 405174721 1250 405173471 405173491
    0x90f041107050a08041e050913060912030c080903040e1612290312030705070503160317090a0203060402210d0e010f090b03010b0304030207030f050105010e0f06030d08 74
    0x7106407a070790641040490941513444180200d810701c0701845804000201d0200f415402140310320b040003090004000411120000302613404010a0160f141c010024441e0b10840e84040020004400740003004c40c1030401000a49110008481443c000119016903015400130301d82650b41d050b074201c44122407000c500402400c01c0c01d80c40781c5031150185c040e1000c0c0d84103c0500b11800402a0041d0b01720140e03016200394043e480500c140c086000403260894034a05d031866852803541880d80c61446820209403402140b10601c07010b2560201d05524204851800100310f80c03500f0216965440c036401010350705401c9440440c00501d0114070034030000b241741404031040d075540001c450503c062020b900010071004400b2003200e69011074a030744903900a0800e0300005e410010500030030f000500850441080000101c8d0515000308042002143c0c08041d0220210240c40c02502808003803040141c07941040c804107100c801c010401e54400c0ca00a401041c50300e00e86001101c0301c0c1c402400c1d100300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 405175971 1250 405174721 405174727
    0x903040306090f0501061d0721050c0702150310050904050606010f0c0506041407080304060804170c0d090e0a0507020a02010c0204180305071a041203050402041d0c01080c090f0411 79
    0x910030b0142c44014002e25604401206804d41f410300002c0c4002c160b14100301071807406244190100000d01c1000c004000e0000700f65454440800c8540304030f07080654092071900c440e008403081d02d0b0041d071082160354040604c640e0f035041400b01008060720000c045410400c000381080d4031408191050610306e00c1d006410b45420303181e090800700241d4003621180320400e503180e00010100b16080081111400440c41e0514244000b05091405007005100d01124a0400302c41401d01e0709850f1408545810b942c841031007031102a20b1500c107441122500440031000a1a0041070320a40c1c1c401c2481e90061f1810540350350044408d40b5080b03070308036441aa240c04422400c1001c9011b038421034825120699144010305190140136110b003910140d010700502007200180d80c1825a01e1403c1a5050100b1203842d18800100034040303460b020301c1c9881c000c10904061007030000740c1c55076440b000e8883c0040340d203404240704018480c88002da500010005903401140c10b10303038000c0400134a06804141 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 405177221 1250 405175971 405175973
    0x6070f030e03120430141c030501060507021908191506030309180b03010c03020d14010f0b0c07080a030c02033d090f120e090903040306090f 62
    0x1012006111040d00000c2200901c02203504042050552441c2081e5015042a00d4002054014a041545a5282403c20054112980d0045032011220303911079500e60480042010340c540e0f6405030841c0d00c1090141c103880380900c6001e0b00c600c605940c2240d54040c60890b0380c1d024080d040903000d49400704600c0d8440c0008803c80140610348407107204403404e6181e98040d0800c034040300004038003100d810786458020800290000941000c42e40804070b40d00389280c0007290100184241078075240c05500b020020040c0307590590040c4125075440d441004a20f41203072429010703120034085c582c2901d5240d0030600100384284c0207409c502001c1e4048814898031480e01c1d5082100d00e01d811800b0941c1854000c045242c103011540c0e885020300d44000b048241c0d04c92603481141000c0710f10480528540361170000c0c0d851508400100354100c2001d069002440c90034800d0b94100390381c044009030382e200c510542c82c50441001400340081800031030405045445000090081c044220b0f1030201c0c50300c201c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 405178471 1250 405177221 405177233
    0x5041a0306070f031a130504080d05040507030c0e06090718091d0c101b14060405210a020309041815021309020c03030f0601020717010501080c0a0e0a09020607 70
    0x1441800203940c2c83d040c40703201040107002d50304080d042d0700030280420b1030280e02d074440560b6145d00e107850300030104a0b51241d040503003c901c20b580b46054003609140030882400000108281102e02c296014801c0315642c0c80700181e006000c1c3c0c0e000391702c54150004140014401d03c140002134000036070483c0301c3c51307444500d141200d000c81558910f1515001c0710240141c4240700c2c5680224095910394007005800c10000d010040c804048034020700022220b005120b01d0100c64001c1040d403400700d4000307007480d081072940e54894000403230b10a465034840c0ca1555500b2011303106113250a400071030426644000300800b40c202c0880060070407804000c9030000c101c1c0360956198009001c10016951013203000d80c00541c5000740c011000e494010485800401000012254004054108a041030f1076000c0102c2c14040303241c3c4104854001205001d074102419031005048990490880d01d0141c950b10038000c1c3c01002d8482c40c41c11400100000311099401e4002c082d5040c40200141c0c50410035541d44 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 405179721 1250 405178471 405178483
    0x80102040e0109180b0a110403020a09090606090647041701200c07080111040806060f030718061503050a050f0c09010e0f180609070c03050405041a03 66
    0x503500301c20003000401841c4818030541c0c001c103402c1c1c1d01070111012a0f8403540000400504110002652415020710390f204003c01d0700d020310740c000c084000c41695420b5801c0500500070098400e2454600008ac0001c4203114910868a0180d510040c00c452540100180302c1c3c0f40c40c0f0b98119035100880c1d640c180054421508520590801c41c80d181c40c1040c681d078140d0055502c42a03a0703070b854000390100d0404d080c11030400b204018031070280d075108649101801d08003140d000060315824408644014400e03200500269842213007290a0f07980c1d00010410b071849070140d4903405801c01d08040c416120064001c2050507082000443c40c0780d5100040050000038030811000a540d42c8140300c180303c418041c10350000c4003c80618078600b030079800d1080d18460b00301701c1410b20480e01008a01c0d52101011461654401030140d521021507010300703500c001c001c032005445070b10814001002640240300b0100b2040c1c055131010b040604100500004026005040040e40750000120101e80d40070455 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 405180971 1250 405179721 405179729
    0x2030408060732040b0a0509031b04151a03090a0c091b051e0d0b12061006050c03070605040c0902030405100c050405010210050406020c0714031902010c150608010204 73
    0xf005a0b0559200c11000e0b2101c6200410980c1071140c241540c1c3c440d000c809032003d42e254442c542c0c3da038101c0914203a4031842041340c403030313098002c0c209500d20000840ca442c000c03048090f1820b020000032544400440391450080c03850020714003c2105d14811410302550b4031001e41000c5500095007511400324041d081e5010400c0c1c10340310300d0b20b054141d1991420181d03520381420230030b05103160f8030301a003e0819191040c0710715810214120081240303d4205420009005c1d000d0017202c0d00da035140540b90407040319100031014115100084061181040702d10841a000c051420318240e80d48800c05008084e00075180c111f0032540100d00783e0780610086d401144180000c1524031410046030064940c1305265005110081c041041305036000305d03404004520f1010000b50795515841c0c07410083c0130708411103a16210360800880c1c0d0b00d403010f5014440c69011012a403404105510060000c000c0c0c030380090000d90081240d80000300c07010301074000c1584241003c1411920307804140d08907085540 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 405182221 1250 405180971 405180977
    0x1704080c0c1e01020714010c06051f0b120903030708010e06040902040c170906010b1b03070503040308040602101107080a0c0203010f090201111506062107050702010305102301020304080607 83
    0x4282c000c5913030100803000040407524141000640c81000280c1004002c10f03004c2c0190703444d4000141b2990100d46c8011035220300d1805c4004407038403012100e8071608010f852216240021300425144c060004c2a68480d0020380d0360105607a007800444450fa800c0a003450760041e403201070300c00040e0f461b4001c001e0786084655a1060040348411810030a00026210b45855084040140480351405003221101d0a40c43c101740b440c900511f4005245125501015241d400301103004002c03c0300140003001160802d5080328402114489290105c88140410445202081040c04c0c0011101400b410792101a401e00102034841600800d00751645600c140e240c2c15583c0d1204011580c001d00701d07000001481c4010320600c2600904101280c20250510b44240c201280f164542c00842c8022044651005030500050808800103803482d0410341040b0702081c103200000d41d484811092540451741da03500c0c0508188100800001166000c2c02c0e03e03811400108404a025842000380c00c3c01010f03169 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 405183471 1250 405182221 405182269
    0x705100e040c050306040f09020120071a030f0109060b09220e0f0d0c0f0b0c040306091109130b150109120f030e190e0a021b0f010c1704080c0c 63
    0x5c02003004850602403404051840d16000c0742c0940d0340100100601519640b4205141d1480411189483c03040e9100001b0495640c1410030601d9500b4080c50084500f0307241340040c0c2e620f03408014103640d250f0003403c0030f104081c0b060000b42e180040c0c03000f0010001c0d050a41060342580c801c003094622010030341100e54424540f9220945040103d9252f0650510300f0105455942d91400844c0ea1010f0700601121180c07404119101460800c5800641e400b01d41000106054034208114150500700c1c1e52003010584005804182c00c023080307180c00d59020302c48a0081d03540d0001c244c00d0071804a0001d04001c034240010400c12442c80010952a001e00b030001d440c007805140043c20b20581451460180030300020810b180070400c8400b0781a108644504016a43d40420041c001e00807400c01d141000541c403801e184620300032400f0380c540d000c000c0090109031030300002075401d0130742c1d00e03038284485a1000c00680401d0007103014081022100d41a0b505000d1500e001900060b104010300050094031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 405184721 1250 405183471 405183481
    0x306050f04020406080408030c0c030307022505010210050a060f0803040801113c0d140703020a0e19030501020c100501050f010504151206080313080f0705100e040c0503 74
    0x811110318010012035080d40b070141030810003400c20202500080243c0c101002103240303089120151403609118030100ca481e490714110003035560484001080c1c1d6251448080400099060302d003006841068004101040c400707107611000b0080141880e5105540c3c48003c038081e0440b06640000f0000ea2006503120f0f41031240c000c2c04c4440d460b00c1d04007400020024004082c01001003201e544c280f24005410000c200305040100305044500c1e40b500c0240094502441421079004030b080600c4031105401e80c0da0365640070383c101d220b0240c81201189050000580605c0d0200703254141e85242c20700e04600036625640c15080e40c208051074801900400d44180115080d803250724010a812200c0502d0b0150f08000030745103110f40e0050a10069500a500500303078003403403004114403c186800c20402e45d9845540340c0766040503010340002c100070000003403510b50001e018481d54428070090b01d0a9880c00f0304100c01d2091051608050107003001f40d0301c03001c0d900c9100d40500b1788401d40b50103584e8649 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 405185971 1250 405184721 405184729
    0x7030b01120308010909020a05010c17040e0106030b0409260f040e0115091a0a0c1202030a12050f2e140411160b060f03060903070203011b350403030605 67
    0x145c0203174018510b8100500c0c003581d03e00b080802122001e003001c819040c00c5041620000320001c14484c40d584001a0010304e1902060f000da04984e0195020414240800c2c00c00c410740e1516a805007522080f03111004030a840e241218444210f00c0142600d001d826058540c0d00303420603408481080e002a0041210382240040070a1101c9145044035a0b241010784040408540c0c2204071500b441c003041003d1403d0140c03020240980e081132405940c0007140070000d5403540029000300000d8550300c00034124a00a001e1075014007252420213800340c4e5280700182c4034142c1c5413616007212950b0003c0109403001200f44002900c01e1202c0108991034100038003042d5070102c1c6000c9008003041000201032400c40301c1c40300c03c240e8400450a5952075a10000e1040a0201040c3e075150082e82c09000d18158004003c000e0307540700f98000d000f40da4943c0c01c81c002c400d007088204404113480032950040104603c01071807120304006600c0c0c1d0002500590703549102011a01140400c1d9100028491850 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 405187221 1250 405185971 405185987
    0x6050f060411030702030f0a03060b1c0b040e030f030601031404210903080a030c0201020c071806090e0d080915090a020102010e07260c030a03180b0f030c030907030b011203 76
    0xb011a03554a14102a0030084d034a00c60000f02d9140c880010501444891003034010030020b110914080d03460b8003a81c0c085042081c1d0340500120340034a00020a22a402d1038021082d0348581800139504003420304118101030340c80280090704141e035074041d102d40c3d190400d0400740580c0c000c50000c0760b214207400d030307441c0740195040c04e503800e201e02007800300001421101200d21240451401190b56403210000340e002e03001e68071001041e4060201b01160810394201d00c031500c040401001d12515a460004604481340c4217100c080f96007209501c0400980915403d0341c2219120b000c440310620100301070082d1b5101910030388c0d202e0700000c14003c00d561742405156600340c141c1010307081c0701d498604074444260385007004000da01042c0400380c465103002d003d0300d00c11820280a81b142c003c02440d000b4003001344683c0c20005152480390100341c07009078005503001540340f2003800d440d5071103c0c00110300b150001001800d140c49030090100000305848600d500038101c84070400110391461802900c061 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 405188471 1250 405187221 405187241
    0x16140706060315051308090f0f040c230a0507020907171e06041b0e0402070614060a0b03071d0f0a06031b081509180d0c02090703050f0c030601090306050f0604 70
    0x40e04445da0000c01c04034400c0341c002e0030341200c5d90200400101e0100d01c091390060441a071140c85d140d08580c5a94200202c4003e02d098444c07040340701c407510300b444d0b04540140c00c034580001da4280b120000600704094004d802c61118240840a008445d12810100000700c2e441d20001e5401d03295182403103e80100e49411020440f800d000341ca0a5034035041c44d03030b04041080001c00a2001107640c1030384480c0d040301c03e0701d5044a000c6c060308107800b5500d150440c099070080d000c0d500e03e00d0000313041c2c0d02410980303010700401e030f0301d0700c0600304619003e04900c80c006101d26403140d500760603408030790350f0100c075100100310707640300030540c44a110b000f0641100ca0600c0d8600340f01e002c104020081006d0340003035040c1e4000312039182d4035860f200546815a8110007200d2020701c14080c41081450304280e500f0f101034400c07207845003140c1e41c900e0118240c0d6030a039401354044c0762031004120400f1070000070b5580883d040c07520003610743e52307510342c5425100140d55004407100c4200030b00100742010b018000c44a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 405189721 1250 405188471 405188491
    0x31e14030a03111204080d0b03070e010f05030307080306130212070801241e020c120c100932041805010e01051b0903070f06030c0e0301051614070606031505 69
    0x3e00c01c2000fa040c20b94000b0070040003858001f4100322150340e598000311940c013000e01110a803e03128074143c5194a42030041092404a0100008c0c03c0d00c3c001048440c05c0380d03c290ba0780d046481700b00c24000d81c07140d4503414081c00c0ea0280807040840c026410040d1180c24aa42c802009524100519000040c00c14809580c400f000109521030740d0440c11410003c1c0916603000c030158180e090480c20160486201ca92200d8940d904c80d4403100c000840308100c9008641c0580b4541d1488400d94454049220703440e022100482031010200b04a512400cac9050f0469220a49120b220700003030413076001c5040c0b050780c8050410444107014007441500c00101d00c0300020002030510710900c00038143c5074940007021010000b040c000d5500c1c280040300050a20039849051036441c3c1d0f001402038533907109030a000940c6007084000c07a10b014019140200c00c00311011070000d2002d0b00c11680c002d002091020012000c00c41c07000014a148200d1006600850101a08600c15100301d030a8420181c510230f0341c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 405190971 1250 405189721 405189727
    0xe0114060f0102030412020604080d0503070f02061b0309012705011505010215040620070204180c0504020d020f0c071806050a050409050a0609030e0120030301031e14030a0311 77
    0x10740d0f0000201c809450324206182e41c0e00034148001899442190400c1d9220300500401c40713034003074100019502450194075840c0c296440c107001269541d13021030ba0315007520200c11004010f410050015070f0007512400c0049510041e03041c031440404506004624000780501044040c0042032084141e80c0c8070240181d042540742c00c00007580d0701040c04106003100c101c00c02260401005030300600000500410107030040c1c038003091600141d000703940300b64040c50400d242c2d543c0c04660103c01d501280d92129140843e242003905100080d00080c00d510702c041c1e401c000364441110030760041d0002d8012040281595800c014000f14900b4500c0340c0380303d03014109a024001359990a6208040e508140c40c0000c24682504080b80750006401c40030700001c1c84c0450603c285544000f000403508070a807103410f441011882000210304400024041c9a002840140005035001c50010055004544288a100103980710542a035400b2424100d95910000b1b4181c501e0350140a500781c2c4583c41059141 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 405192221 1250 405190971 405190999
    0x305041b082d070501031d0d0806041803270e010b0703020111040b03010302040b06041206150501090e040807061401090203010f0501090602030d200d020306041103070c1101120e011406 81
    0x10b07441000c2d00400d070515842e82c008100000e00b94074800c80242029045518a05200901400e1009c0c143c9000380190b050420f800c1041003640c0b055250554180d54500e100005241d030030310000e895500b030700003030020443c0c0026240041c0340072501811616514030f0303550517103245c041d08503070500a40303005c1c0060900c070812a04001c001607904584d0142c07000700b5862400320001d801d40c401c68026010700305400d11100240007040c1e00148082d4240440c0644082e12030006443c0c2d03240341d108035030340e040e590000100003c0380c2c0c0740036007440d0f441b80708040b40c1007104980010721440240c015402099012004000c081c0d100400c0000400c401c2c2003886900c0e041c240000c1d22485034008408140c1e4441c51514040d80e00d070501c000121100b2040a034480e20010a400007a60080c1d482a04c180d051041c6481842d550748101c0340030b080152500081d9413032655621001c60301e40f41e442c0f81400032242e03503c1c4441d0500c0c0101004160003000004a110381d035446920544005030005c0e025141c0006055 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 405193471 1250 405192221 405192223
    0x105040b040b042102010218030c060a03090807020d0b07020c04090f1b0812091905011e02070503010207031e0c0201021e100f02040608010e040804060305041b082d 72
    0x540203600b10704040075558490604600c1010000720110205286000310400140d040d40a42440e0030f205517500000c1c04030004140c1c2d10245000741c00e51202041087c1100b070b6003c0d44c841c50940b4482c1d001a0f0429210340c0010b580ea040035582a101c01e00f0070340400861507070600c080307240d80c0d10483c0c08100d1000380c0d071950b40c0015040580104401d021050708412403044600e8800100050320455008031500480b110350341e08214001d41c0074407121948170031442200030031102902c1c0103039620a5401d18410045030406039034844041036000f0804046801d840a00091030300c98069244c4003603c50600701c482d12100c1d00744080c179080220500034a80140c0e400304072000c000061140c5c440848001031a02030404007100d9442c41e11515004010b41c05502d9900680b045a515483c0c0003096a038900f11807151980448004241d20030802c4184040c0e03020758040c941090185000c0900c4a02504460901d65040e0700260069846941400c550440d00403038001d2082682240c14001d84050401c0c0e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 405194721 1250 405193471 405193493
    0x170708031b0c0a0b04050f070b0901090902091302090d0609030302190c030e040509010e070f0e100803120c0f16021f0504050f0f030d17010b04240e1002010501080c03010504 76
    0xe104d1420007003c102484000c01000480d54003010503076400584e1241c01d0034441d40021452800702d00341c50300020f04070605109580d402440900b1040420820070743c401f000394080082d03d6488212104c500000c1038907441559582c9210f500c0040e40c80300701408040c90080f0201c616810031000401e00c00c00030380d000740c0f0718500070380588020646840309000c8502501a02665140e2446407500006040b0007280141c42120001010803a05455074501d1001c08074050103652000d40c0200080d522032558224801c1d070140c0d507120024104100104402495440100c25840d401d01420051042d0325110310041080e2080031202d0040e840b00c1c960240450045114403803241041c0b55101145845041440301859001001d54484241d0f07103001600100c141300420b086e62702520004a0844074142c02c4409603a1000108610100c0d107000a01055041801c15020090180b0386403403981c440043c5140601800c0e00003180c0c6604003041d180c90711680400c4244203170705000511020900d1041c070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 405195971 1250 405194721 405194723
    0x40807020d05031908040b0708010605030115050d06090209030d0e0d14011b0504030302070506090a03060c12020c1b040612020114212203020c010507170708031b0c0a 73
    0x105144410060814070f0035809558010311040030080002400140c1c8854002c1c8601c0c07046c0240f26070794075900c1003283c0680d024020400840d004100601910300045200c0c00341c90460300c1c01910b44042140c402055a14682c444482e56401003441c2c0001d2a05102c070118400c513501e444040442c1d02400503104801000020b0504001c8181000000d07001390031160320648695442a0640e0321074200070403d900c14801030b4014001c0240108680c0741c80d40445e028920014040b480301c0e403d41d122080142002c0b10800240f10030101000012400c0380040c5c01d045056902401020503905840f40d4404021700105106900c1d184080c84400441c101d81d00c0c0c95030302132a290525400b0341e04140e00c5441480c10f03419901e00031503c40e5460100c2ca0400c0c1e8407031106400e44000f62084043c031000f24910550b002005604103a884410b02c3d4413450241018a01450080c0714400072071114004560219005548440000042001900440701482d00c3c180001d515586440d0484a2203505c80041201c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 405197221 1250 405195971 405195979
    0x60504151d10020709241a0910110d03061a0309070b030c070c080a020f030c18100e0103060c0e01021606030903050405060d0506120706081303031116060609020304080702 75
    0x1482c0c00040d00c2002408003415440070104080c0e0340c1044100902040641e07100d40b44000600045200302c4020b00418100032008126402e201c125410000500001c00d03201c0c0820210208084100c00200404100789045440c00240b040c00c000c02d40040114855403101c0c41171081040c0101d0b681d000a001045403400c04819440752511860b404041c81468000b400b038001c205804503c15802182c82ca01e1740e17108940d00c4012400030000d144d103600c1d14003520342d4858144200001c00100542c4000c1c0e011801880540410751296480050040d080c1c1040c0c8017241c0c1e80302d40a05298004000c0348203650240014411540403502d21038504400b809160308168607460503000701740c005d400b901c0203048010003003612200c1c4800d2541c000e1904983c8180f094070358401441492001082d10b9081e00c585039922002960303510005907a00308015001c0f810142c1d5420005200d924902c0905010012018013529807080c9003083e03070555809410141140c0d1040040c040051009812910081d47c151 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 405198471 1250 405197221 405197239
    0x306010506030403051614100b0603150f1305060a080a020a03080d09060f1e0e1e1002120f06010503010e0a0905070b1303031d0307170102090a060504151d 68
    0x300e82124039010310b0040111b11082c0c420383c241000b0710000e809024201110440c2c030071a64800c643c101382c8030000000e0380c01220802c0820182e41c20200d0500e00719401034a51403503100500f0101e8080e00c04070301c1d54020700d070742c40c028002d06260070b124402c014605507008040050594000034074100080c80001c0c0245c2c00000e483c01020016003094040c035030400420844040301501c084043e200710048024205a5910411000d04262003901d0050320100b0043c22108849100100c03641541184081180f003442c40d2081510020300081c5881c5400410150150410700d9070804d41d641c01401c0c940c14001c4c240700500542032071500560703102d00d114101003000401030412a0501a8907003080c00903000001d010340050a2080c12070701100e1280c0d844000e1284a07146400c81207800510150b85074110301d070204078071800d03114280101e100c02c000041c1750000820014403400400d42c03041c0040750000c07400b00706421410120503803910707030741c00d1104185900000208211010342e140e184602030b50 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 405199721 1250 405198471 405198473
    0x11a07030c051203011707031509030903020d1202060f04031d0f09090d020c15031b19031b110606090a060305070f15020703052802040207060e190203060105060304 72
    0x6084050701e2903800c0000d65007420741c40074140100344d200b40904c102c8102e801407943c0c0c00d801d000941c0b504aa4103c61907a41030a400300102c009070403805426010011416004005030742c41d04002e8a40510400d110302c038034841c10301c000c0c1c20250700030a250700f499005420080400c0e0000d110038000911140d45108804c40c0f080020382c8006451407050b04a04002d04000c884407000400500e541600e80072528811a21400c0086001450140c803801040034404102030030000c120700c80d060071000c070100742030a0030039807485541100910788600081d26070781c81603c0300e001710303845d00001d800c1c6140003c010b00e04034808030790b01d0b9409000c0b00e01524009000034190031840e0f000c100030b141d0003810b44004958030385540ba02c1c0c9800e4010004000508600c41604a00014802c021030760720501400e040001c0c40c8409082e000e01910740e005919400c882203005995078801040ba42c2d2042d04005080013840c80d86034a000c42c1030110080141c40c40c0c0004000d40e030005020b90440300304a03440381d600d95076 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 405200971 1250 405199721 405199727
    0x910031e090c050d030207140a05030319140301080a0f050c03010606031406060c070905041a09102f090a09110a0f030204060f050c011506050d14011a0703 68
    0x29041994400e4814840482210300c654201145407401060b45000300d40c2c881040000c51000710a005005d030348014020852090014801042032000804410b0016901d00c08607056074080901d18001c4201c1c603110090311078000e15101281c208108003103040d58101440325a484520708006401212002d0101c400c01404004030145040f0140007440f0f00b554401015005e002c040841211855001000410f94248503080d10020380b058070080010f0740c80c00720319000030140038000307030b40d00400c030300342040b205125185440c05000d049000b044c548046010000c2103c0e4408107031f5894802407420b204034403021400d0311921080f40740e1495500c4d048400003d001c0700095100076401c0d4140085455841185405045045e01c0f40d15410400245139004804900c2180200404030385240c20b1100140e2045001d0440c04184000004d6110300b00c080d0012a107203240c0c40f4400240001948000703500035070040c0b42101078801d28600103541820350072489030b6901d00e43c00b5408940446c0c10000c0c144 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 405202221 1250 405200971 405200981
    0x607050f0d0e0109170a09060903030e0904062c060606031e0405030c0d1e0e010915030f06090504020907020a03020a08030c12010b0409060501030b090a18060612111c02281409010614091003 83
    0x740f1540c010545940d9547c000300038411430041042c2d038040e440000310142481d1048074441d1100b0031600890001e41c042220900300c0243c010786041c4020300034580303c00d6041080a4a507004c0381c490480c00031b4002c6408480c00b460140000030098140080c0b4516604914a003085d03036100000c020502d51200006c50090221202440d182810300c0e0f40040c03111042d600150080f030023941c1e81c2e2510340d40c6003c2646d655000d0714000780180c0c030084505006c51401d50256800c40b004402452a042076803400d09400d68080c2c01c0588070703141c0000c1c01c011031606441baa02c01040d0a003401c0c000e5200803000541100e00c0105101d840301e49070074449061b00079100c01d0072501c0b036200000b00003140d100d190b03035446203e580904942d0300d54100c07081c100034541880d0541d9815807401040382c07110000d40c28459401c00c2c02c1030745410414112190300043c111203107402c002c2c050480101402880600411650074811f0b4080000e100d652000a083c10001000f02c032043e43c010340c2c0001c800561650100c00620b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 405203471 1250 405202221 405202241
    0x30507020115090606030b09131e1208070801080106180209031e0703020a0b0304200616080702030d17070c111806030607050f0d0e0109170a09060903030e090406 71
    0x501d2020542d24082e910400548480d03070f030204001c01141c0e09000303c508050f5001114091300400000002b500e071141e0015400d000c0000040c41440d0769a4504101c0415590502041c44441004131095014211034010301c0110020b00c00301d413404680c1c60307881c4441a18102c450390001210348a603241082580042500038590103152448002c00540398002400124403400130b1000c0081c0d85206881928016900b14850b091008030043e03030051030059503a6000e40143c1c040c4800404603440d6035481d080240103800c01e81c0e486110344100340c104072a41d5001003e0095404030004500c1c58100d40b40d600003c103003045a062403590500c050303510a8902a01d5210350000300880703452509019050040c0402c0d01242e200fa10391780c2c02640e135401451070028050344240083c1a086687d80c0162088804880002a0781282c90315030402c13224580e4114000c0003070002da4170b900c19034007001c150000c00c55407425810305400c580d0700030a82d038180d2203a9441406842c1c045030078440158811a640 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 405204721 1250 405203471 405203501
    0xa0e0d0b15330f0c0619020702060a1b06050c0d1b020a0b0c040306051302030d031b030b0d0807050a03080a0b0607060e0f0610050312030415020c0715080a0501061e0305070201 77
    0x1131621011050755940088800100500021145100004481c0269099540c1c0140010b0914040f81400c64800601c40640c9140520400d10000466003a101d003501030160700c1e038a1030707860a0b074507502d00540c0c0b4000b503c254015050708845d4900d69010400100300e0b076001d840c90302c1030384480c1410502809241c102803d1240b9000502002c204070360a442d44492003070f010f54080e110b18410982c101c500091845444003110500414000d01c01da000d03c0e1403050080a003070403c14a40c50f01c2506400c540c20444113548548000c405141d040306019601c9200d0800030b21038130300500c3c08500b5a0242c140700a00702070b00c0d040e0410707005400340488803a040d007490403070b141c0d450701c16404407000000e0b00c1150700a0140310b401c45600b0b09040b040305d100e0750b041803000d0502c000e003034228402944003001703194250103098030100b94500841c3c0124a003100c02d9807500d130141810011101202c3c07044c2e1209050103050189054080e40c10805800041d45e18100000d0b07c1d034030715006074050803155048aa038 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 405205971 1250 405204721 405204727
    0x5062b03050c25060909140a051905010e0a060f030305070b0a0b0306070206010f08031317010b03100e010c1b12140d09110d170a0e0d0b15330f 63
    0x94140404206000c41340a9036501c40b13000d983e000310718111624010180843c42c0844001070710001590001c80d04410581c100b07a2000000300420403c55000780c1201c80704801c03174024000c04140500454001e400021650702043c0e1544c1d40141540c807401c40e0080281f0000000244800b80684c0705500014014090f21143e20b8490310080d1508024052483d500001a40c0400d400c00004266008810b42010005543c0c0c2400ca41c0500f9054641c41d40c48999290440d00d8410703103007804405c10700c4481c1000032840c640c03502800e80c20f454000203001c5c10040761044007105002c0055111405030b0300421805c103a60719646003251b004007001c0000b440388000091002055810f0741c0301021580c010b04070060340c01d201c08100504007180700740141c1a2501c0039101c8c3d0308140305500405e00e80300e9606088082c208107001003850f20884010661359184140200400d940140e844c1084000b07048801204800308520112600040c010100100903009000b000d500144101100c0502903650341d2551 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 405207221 1250 405205971 405206023
    0x9091b09040911010311040f0335040f0509040b0103020105070f080c0c091501050306130e0a1a090d0503010909080c0a0803090f060403080a18020a0905062b03050c 72
    0x1072490203d210f03240004d14001c1c40a50b58540001a641500c00d044a84812a8915114410620300d0380b030f4804405061003540505441c0b010f0780b010010000b402520b520366207000e10f80c0c60000c250307034001070103100000c0030400001c1c0b81502482c1500c1d82424084d40f1400c46003840f46030031206010091080c24002448000c41c00c000540310040c5ca4112010102a0754801040c4541c4402410581c0860001e00c00318589147c09a070302c0d407401d24080703000150104e8400e41c06150095040c42500c0c0368a403490b40a4031080b501c503609900c0341949008140c125a200c0004125210521401d580e080c0c1d100341000400c1621400c40b10b8000201d02110810790140c2416101d913481919841c49510511450030746050020490f40c1c42150942c0b100300c2a41d40309109030019015110b9007401102c01a84c2800040c5da5407001d18020344001070380002d1a15080c3c007402442e40040a810405009510b020580c4082035114600c1c110344c10301c1d1594031203200640e11884c0c500c04040950485d5210b101031a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 405208471 1250 405207221 405207233
    0x50a0309051213120b0a0903020f1912030c020a030e04060803031f0e0103050a03030b01030617071403070302031b04021315020705010e1e03030c070e060307090209091b090409 77
    0x303202c950046600840320b40e90801180740702c2c0071307000090400c0700c00000940e00310302592011054901a0050303e25030421842810709065407a07240300359815003191000e0078841d454100408018607070408000200c00000082d569108131000101041b48007101c280c11a20340350001c100034400170046035100c0c100140e613045000d0b280d861900c020310b032800c03001645500040e001e80c100c94101c8050700c1d2060300b9072411000381c040d03c1c0030281450388a22000030142c404118010310a00040d02a020740d034204a035091244403c03010141c401d902000c01840543d40100d0303000506207202c031091240e0f584203000720740640114118940380309034142d000900108080c0c81e8203083d072456420b48807007544600064a078803100403c2a81c001021220407204011600540400b000d80142142d0030080d4650195150031503a03005401011803900600166080030802c14010f00401402542061080030104080c0c0c0f200429064001d2030081030710110240f0141210120b41c0090f0003484001c4940c2003032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 405209721 1250 405208471 405208477
    0x10020c01022706070803130f060507020609061009090501060902031003050705010305250e0909010c170903270d030503060f0406050a0b090f0d0b091e030307050a03090512 75
    0x844003900d984042c0e18840e240141c40010001003556040030300607100ca13606a000200100000191344080d44041511202c400c10128400d60022500d40340594000307040803c041c1203146150b00500902000810300600f01c401e44040c0040090f9211003800c1990141600e03504c42030001d4400824070000c1c0c0d5171001504140c900031012030340165907407001141250360842d01440c040002c0110b040111040060601500074140781c2451070014450004da07000009451400c0269518000c0c01c1106812013440d40e1750a80b0380110a00519100000035280d100b0310440c45103030040321240c0118950500c0300308080308400f5240d4285010240b5014006610968050384525040b01c0d042c55280350034007420003552009030411549a24000304807800b608805c11807940600036802019054070b40081c1a04924040c1d084160706050001c0d0301e6081515480110544600700c11104008482c00000c1b41d8000c1c1242c03800725511000b000b0114000c1c5000100101180150341e8000341c00c0c180038002d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 405210971 1250 405209721 405209737
    0x1d0402040f0f0f08060c160624051005041212140c0102280905360406060b070b0411060f07031d18010504090c05130e0606060703020a020f0310020c0102 67
    0x2501900c981c503038513250b9651030221004d410b01c00e070411011f806031000c075030500001031080c04040f07820040c40301007100d02103070b0381c1000007100d0700440100803c4c0b8200c0c006140400e45400c1582c6401d0030101c541d16052140c5002814010000c8180c0c10024840c1b600b40c4060040460a20b07240d100744c4003013601039448020200c945142d505a00603268504079240100c440c11a01c403003582c2840c01c0706006244442294141c174070880d10860304401071074080b0b10400c0c5c481c0c0c504806001d1400780f80c0b80044030b41c95005085031b1281405141c000840801c4006d40042c1c0005449036044002c1000074032601c505200901181c101140c40d10815410402400300c1c1800d0580030444d00c0300c0c00c0d040c8041c071013a500c03400c1e4400d01f40c0b2004104a080c1907000d90709050103482c5d40161140c49902103095108050181e080003070b5102d01140c03407001c2c00d11003503411060455045141c0f01c0e1380d8030002d64590181d04043e02c6489112001034055908020240d858805150155250000d01e80094000e4000600c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 405212221 1250 405210971 405210989
    0xb0a080303190f110a1101110c0c030106062606030a140d0806031f020912070b03090721150b04050a140a0908030f10030f060b0415061d0402040f0f 65
    0x803280f814403240510301240707014010703c0f4100f80c441202211411446800e040c50355580740d980c800d0181c0307030000402d42d84460100524909041005140c01c4402d00c0d0b02400400c52884c015030035070b2050540340304c1c00c4041c840c400700351920b41c80f00007070500c003042c41f0007800d01d2100d02000d040c83c40c000c00c862003985245d44a0024590300c00007419100c02c61f030b07840e2580c1101000b40a180e015010b902414228001400600f0409011000185015555004070794082d50200030042000d03030401841014007014061400f06181582d0318140340380c02000300038101b001d9800e1320004400c840c0c2c0070301e82905000f0414800e900b040e00d20800141200c80184003c00c0d1080002500c040b87c2d40030365645c090740030403460300e5550b07002622100448013410700380c041280f000300040480c440703070007400707406000b500001b0b0600ca0460800c02190103610b90380b0100d0b202030720f0030451550490700c0e45106030700c20f101d581d03044541d000000300240701d80c0d044081c1031080014045029402090140e00741c0b51060 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 405213471 1250 405212221 405212231
    0x150e090708060f031203060d06060302090a06030c090e0a03030c0302160602041508090606240705010b0a060e310608010b0103140405060103110a0312020a05070f060801090b0a08030319 81
    0x8000d15845d0408000550109074041002c03030704a06140120100c114014840000d44507103c0d80050f99800302074031100445031311640c051051001c2c030407a140041426400070491a100e128080341c0315441f0000103014565100d9070900014041c4c1c04a4454812107060403d08224614002009400502820a14040f40c10910784c2c064082d400707540c05051301c40700134420780e502c0070100400ca05c250329001034400361054108000b61000400341c48040c1c441c00c00400d0b0701d56040b0a0140c00304c0e0b143c2c0001c08200d100c03000250242c40c0c12140039102a03010541030b651484081c404045c2100102540c1d8542e1302d8071100040e20481035002001500c0243e806100c150101c3d021b04404080c25240903000f600b1240c01040007451004182880140182024000c2c0c2c0d42d81c1c8881703544160304226131002da00004c50f1642004401d00c0b14078050b084441400c41480c0c1171980c0202004e1050203091030031030341c8504007900307681c5003020780004021003c03c13a84d49141c5104840740b170403010120b120140c0c0c06c1c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 405214721 1250 405213471 405213499
    0x8060a020a0c060c020114040b01090507052809120b06031204050a140f04050103030305070215070e04020903010b04020301081f0506060d0f0b0a06021501091401150e09070806 77
    0xa40211105048035035034081c2d03160440d40b20200102604500c0400f0356580c0c0500300c0d40a0120180b6a101d83d0003040d400142d50b2619001c441a510028910000c200040104402aa490701940c026041d840c2e28000062505a2004c0d1031503503164206890104019180c1810070844207409841000283e00790740e80070310040390500e0207004038000d242e8090311240061003401681604840c0c60580140b02c10b407240c0029000c5021106d080c0c1041e00001d89400070030400580420bc01c003c1c2c850100c1440c00103103410340d0020844148400d905224503000a0540c0265a003500301e41a4420010411950395954505895540035100c1300e0542890441003540b2406003d4843e052180b600504242d181c41e12030980d4100608082d4900b8000326510003a00c00719860f80710039900503140070b4008103100035a9400342480c0e000140d0103040364a0030038001d55a003038203401000d030444690040c80c601c5100180c809840c0c9582c014251030b08022050304100c0701b242c0c412189402514255190b052909207 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 405215827 1106 405214721 405214741
    0x110d06061e031109091e030c07270204060c020136091a030a03180803030c1c0c0e120c030604060c0e030a11010f050d050406060806 58
    0x1d000c20300410001e039201410720f034000c4448909610309510b04e20394800640d03020300101060240c400d50003075010400da900c8aa00f08080d00d600a84036141541c0451035039195090b141d8070140941e56000c0184215410307580c01d599202108102600150703608100f9111050381c00f10b6002510601003107207418802c6015142000741083c0340750245c01800d540c05000700e034045402000002e00560360006550b50420307414100b031041586500300c00540314425600011040c040041080501d80901c801415020941c10048601d4102031129104481c0380d109040c0201b81544080b540600e40021211500f1003000f040307850f60f124040100c2d041207001e50b82100c04544502100c40300c95001818000c50708425001454074079400e446843c052941640d1050501c403c8511046807148a0340440710340e581e9114050006050034038003040140414403071176480740204000b140304422 = true := by decide +kernel

theorem cover : BRFrame.Cov 405035971 405215827 := by
  have h0 := BRFrame.cov_init 405035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 405035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 405035971 ≤ n) (h2 : n < 405215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
