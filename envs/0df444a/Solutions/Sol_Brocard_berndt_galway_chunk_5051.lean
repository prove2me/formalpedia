-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5051
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:35:08.59168+00:00
-- url     : https://prove2.me/submissions/87138b73-b932-45b6-857b-40a7f08ebb90

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 908273381 ≤ n < 908453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 908274631 1250 908273381 908273407
    0x30c330f20010c110105010503010915050402060f030a0207140c0307290705070609060813151d0a0b0a022b090203011103150f01020c0f0604080706081b03010509150303 74
    0x2a4804400d90303100204c54540010035400d481060b40071038001c0c0d2505040c2004508444104c1c03c02e40703c040404100303a103d52010414a10410840d40040076020051008103107840c1c000b403840900039540b01e2040d01d03503064003580322500003000c954503610644042240050060400e014091080c49603a403070540161000702070341c003c1c141202c080d04101b406001d10381d08002303060082c10192404040d5442c000d066803403403070026070002e031003140d0448100341c0742166904a1a4058019003040310b103291140c1d6515900c0c186042304031030300b4030402d000406400086c0b00750740c1c000140d521990740841c0762800600c1002c00c0304032382c0900c0e152145e0340703031000d0b071007d000e4920058003a4013569903d103001061180c40710040000c040c0702d02c3c142c003c0c4481d01d0381d0000b0003200d944811100064040e5820000a25030301c07035035200c0c00ca540603030200040ea064100101611440f421100020303181850307150299588403d0250304d90041800c40820084d5a00700010400150301030708991503d04515444 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 908275881 1250 908274631 908274641
    0xf0118231806180709111b01020a0201060b031303110703050303041101090602030a1e0e1509010f1107060c1505090610060e0603060402030907030c330f2001 69
    0x100080c1c64032012104811001040348907489105400d90984a4480102c0580c454645201d044051a250b18400d240c0b00c0c482c0c01120000c008500102c0505410070340114080d403c036000500c055440d140f40003a03488040300450f44125241081504a00340a54041e100c8503110b01540140c2d220b52003020000800c02c00042d806140600c2d00d09a00300c0900000406d115041d401107400c640041c4081e29a558000000c03c2e07c0501412100380c040315403140440f50a285508006e0b40a007070b01240d8004506140002c0c580001d00fa82c82c00d4603101c48943c00d866030400a84030702026800020200503091051480715000741c402e01c0c40b0002c02d80060307000c10503038500b50380380881500700c10b084c8a8013100c1b44251074010582070400305881940d40c0c000800364040100040c0c02640c00000042d01c627007003440441c010710707803114200b1001c54541c100b118007404020144407031041500d180d1500b102500d005d80080034095600c00e40700706c1841c2c07030844000c0300080102014070071011b5000304c841028050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 908277131 1250 908275881 908275891
    0x30903090f01050c1c03150306150915120f08041421101a0405070c0b060306150f030c090129040602061f08150f0f011823 54
    0x296252200582000301c0000c920281c01e040c800e0070806061040c00c04901c4440455010100012080341010f06401070120a0861800c00181c1e22020040180350b6004051982d40302c2851005c039600e41d0f100b4003c039031880310342c400c00501001c0d08100c85401d920417150154070909100d0103402441e511240a41c22540000301e4400c551107403000181080e45003616401003000c00140724412a1901c1c5460742d04101d01404400e845481c83d2601c060201611703005039030302130300801240c6403501d401001005c903410111343c2003000c80041110f03441d00183c290700074940c080a211050406100f004840b02c408028203425001c0d810b80e141a03607036050003081c005c001d416440d200d401e501e02c0c48252464825050740d450060705120910503580e0000341d15074026103251151014051b05031315440302e82c0c02c5510020f92446500501c0c90100040201d107801400c541142103181d071504c051142c00203400f409184004602c1c461010651059030b00100245000034800d400415000d191540e0455802c980e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 908278381 1250 908277131 908277133
    0x1202041202010806030a020105090130050106260f0a0f0e010c170f160507060203010b2a0d1206082b080708010e15130c0810030807260309 61
    0x2280c406550300400c650b0303804101100a00612840b80c1c2c00070300707107001d1030480078100308000d41001610075054410308000e03520b400c419198040c801c88404007401003400340c0300c000f032507489200415040c04900c208680051021090107943c41c24201070345544002d214949803078841e6100c101c100803501c00c0ca03050240603c0046429418260083c20242160040755007071540c0320104402a01c2e24981a03030815184403000d52a2404403000f1202030040c01005440207200000009440e40d11200800c0001841c0c001486411070103402c40172110300561114900c1e030130040e54803107118420401380e05a16031520001522684030030398186020480700c040d1550305106504a035080a100301414242036462400b41d543d0b10b409080105008818820340c91041c1501010982da07580182c413548107080d01178907034000414098803c8001e0004122402c000c107880d14007094600e802410340030240c98004040501e02407950741c0e00d090300c03455103900f00e0300c0d0f0281d4107012409084880080d40140180c0d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 908279631 1250 908278381 908278409
    0x712060b042406090501110601120f02180115170f0403231309020903073008030406240b300108100b130e21070506011205030712120204 60
    0x207480585501800e17041a41881200c0103004030102000480d607042d600b0a500c1036280081030700d400409401603000003903101090101b02c0e209a01810301c000d040b915004a0050201d09100080d60400041110001c00c000044005182a008107180755041407092803c0c02ca194822000610382000700418201e03a0350002800345480184804140b01409101134110300c1d183c600c0e40041c3d40d5840f50f202c0d10042d08040c803000003401104102003664004400c5007030348031600d50301d00407a440c0d02c00c4a045503540e1408400c40e48035115058400e21100d8050216660070b4100030200146030841c0d14100700680c0d42c000d0480d21001d504414803c6d54120201c41080b95050117101410a5403601d610303102246403400000d100d580e408003074500e060998000160050325100d802d4108011802218458140054848424001c00c40140350032401001a90010790b20303075103407250510140101812030350041c06414003042010f40081000c50090601b210b07010302568128099030442d030b001c2d0403000308113 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 908280881 1250 908279631 908279639
    0x1200f0601141201060f03031d0307060509040c020601030b0720120a0207080a0201080f09031b0c10020105090309010810081b15130b0c0703140703140712060b0424 72
    0x803034110f403c0500400028081e86060444450503031038244409001c0100d4039a59425041043e00d1040d4045801703429650401e48910000d44240d10901925004a107056242460340e403011034050306803540049211003549429000300c2e06540c01c106617007107940c244108000030207030400150364448808050282c44001c2c07008040e05190040d40305100c90b400c080740e50300c01030f80c1c8070143c1c0394800444408202641c50360030707001d4618080c02081c298214511100c0481001d00015011000751040300c0c030881500360702030102d00f40c03070054540c4010382e4018880d140c065805680c08981c0184844a9400040e5a65184034500740d49281c614569a81e01c1c1710000392420400d00c1d50032003000e0b110383e203803402c005c035528000c3c0e1083d588a9130448010100d500051100c00340400c030300550304101c0348148806500483c944501081c0300403614000d10769002a01c0301c00101d40001242d464640542103202c13540c40c3e9001400c56502d010b41d02580d550b0000d4502035091894203c20382080d00c40d1a849410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 908282131 1250 908280881 908280889
    0x31050703170a140a0e0909010b0910080703080a030207170a0914010f0e01030204080a3f050309010908030403021e0105090718060b071b06080601200f060114 69
    0x4004001c1125501040070a610580080c2505034009814401070358540821004a828444901401c0d41c0803102c0c0e021300441d21015001070030b41900485034420700d80c0f01d4003281302428126104000103a0081c24081001c1035010024040f9405141070151a194907581c40c82c801c06000141049034a602040c5010f403280d0240c409009000f001710b001c481c0b802d544002810ba280e001e0f00c01010050038030829910303644a50142c2d0018000300c0e0464070842c00d0361800640340c01d81410ba110301d4013a40c460070980400d20395408a4024840025001c652924200032610ba500c0207200c04041d6490305842d40000350418001c501c600d000e03901a0070403101588843c0d04451688032140b03503581c14002404000341d408110075080f2410013040030034040200c16008064482644000c0028030702141c040140b200304c1090a035003540314080020901d40314102a03520f2030059400c1d600140d1540c0c140026800d5490b48802c20414000442d10001140c41c011460420260001554201648207241c42410 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 908283381 1250 908282131 908282153
    0x341119030b0a0f181b0305030a0f0e0d03080c03040c0e011706070f050306040915020a0e090708010e1914041112030405150f0c010c0504061403090631050703 69
    0x4a410028001c0916403030b44c02400103071182d000b81012038042e607005040740403c00c02000a56101c02a00e407603000c1080003500e10b60740c10f40d510001c070340304910010851400c14039100e0703625410340b62070b90282c88a004242d125040248200d4810741c11420100d030303c07103003041264000c00e52a040b0424010035007000c0ca0501c00064012028003d030041c0c01861150054162a440312060f180000c00f050b0300d00b400812003d41d0608004490320010355005102c4d48011002004942520025003a4542100440c1d0180c002d02c9000340354803c41001c2001c541d407160b1045034031504600c000c20880301540700d0300c40c02d4000741d5044441c1e031401e070500c0030340b82041107002c2942041c22002d141841d2516000ca0900a010003c01d03003440e000040c0d049240190388182e8181d040030302c000700b0031600c84100c042d12a520601803403000c07407800d5500c0000d8000400c1260722501e20000070f4041520342c2c511445410001e41c100c1c03e00c0003160050f001410740010011780d0224059001001700790300c0c1d81041d9140310 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 908284631 1250 908283381 908283401
    0x103110303090f010e06040e010b0702030f0f0c0d02041b0305090c01051213061b0503010806010b030103080d05060a0b0c1e01090b040f020102030d05070302341119030b0a 75
    0x34100b030110801aa481d608444000745080c02c015489254200c000359140c07183d600100e203007441000000c0380c0300b0740401c042d180c138600c2682107a0928011000f00c95032214038960700b81c0300354080401d1550a04182000c2004184042e01c0410141d8200ca504000341c0c51180c1403200203a41c820401c691920200055259401c003030810310314104c0c0c0302140280ca09801030041c04013040c40726203034081150300da2141034101c44009041c0341030f815900c00104580d00078410b05000d88140000071501c1e410040c2140e04a82d03010080901e46a400b090100191000034051079201485882c00221403c2441c001c0c103000b003220019040c0c0c1c015152642c002600e1592801d1043e038035220b100700c00a618401c0f995003094101e54140117000712440101e1035445a10a020406810003040c01074030f5806401070103901014084a80c3d8010403103250844d201803002145480c0b40078010280041440c0812000310b0310f102514510071104d0040500702050310707990085031403001c0101040a03141d15445055624 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 908285881 1250 908284631 908284633
    0x6120a08132103030c0e100c05070b0c2a0f1e0301061203110c0a120602070206120f070e03031c0b030a081245071e0b03101511070e01031103 62
    0x3c10400c10200e00c10807954820082485042308410081c000c3c100407c100900d5401140341d07540c2c400311221030301c840188500070340c85043c940c60040014101001705c2a8544c0c050020400308007201c040041d5000a01d20300c68038038045100c0395a17682c5080c0528000742480c2d140c14101c0c140340380340080000105011640c3c280d0400b02c002c14103a6180c00d180c400322415103013520a46140790408030000e01c6a0f04000358010f1000036101c2d00e1582c861107031813050300c4210605074250350313000307054480f14041c0c0c00e003d905410400501d21020b4410441120b03008030003400003011401c4101103464001300541c01d41e842007000c0b0f101e10078189001404c6500182502c00f18155012801600d00400941d1860411220070301c0800c000703d10f410520398114880c00000c032150b055451011029954404480c103e201079145d01c00b00354603403103d01310790190742441100c1c007240e450100e9180702482e10b041a00c3c2002050710080340380e1751081160502500a14064410341d514500e0181d040401c803003225806 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 908287131 1250 908285881 908285897
    0x7170411030d05040e0a1e02070f12230d1805150601020703030c03030b131d01050a0b01120506010207030515190b060702100e040c020f0606120a08132103030c 70
    0x1105c4000c0e20340700d80000c07a038031011603a48052a028505401301c000c01c580820320214011061100c003e00c82401c240c0500e03605036013807101e02d03801c40300f4401d515141c4140c00100ba00d1610951643c100810200c2510f010004450340c4807600311929011780201900e556022400f904110490120050381081090000303060041c91658094a6034080c4030015086c15070b607030140d0180d906c54160400d560403501c5c404000b080c4d100061480c40080702d83d402d0350650700c0c000010702e1305001d510a00325034045c16101c40316050002d000c460041d020007040141107004090380040044c5040002c580c09440e01d05d5651070a01c0c11200701145c006008045000c0c0301c1c02c0a9003121140c54800884524039011f0b204400a114180b2081e0754009040c1c40c0c00340c100303280c982c00c4900c482c0d01040303243e4002842c40584005458110420ac6c0101600c8510078a542000c0109400181107900500301d8a9401c0083d600340c0390b9440c11f0704610710500c0c0042840b0030000d0348080405916100d034403219006400d16088c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 908288381 1250 908287131 908287139
    0x5040e0c0f010912060504032109111c150f02030f01080114061e040e0318041401030b220501021603170c03130201030b0a080a020123070b07170411030d0504 69
    0x40704003040780c02400343d5903644045820700d4401c01c3d02c54008400b0f244071442d0449c0d80351424000b84900c48043e50030b10781c080d54055151803c42035811240c2882120048180c030242c88100405082c110341c1e4100b255164801c8040c01070500155124139441d1460000340e6240103141c030b0a6401060845101000c0d03075080002a980d00c02c0c40c0b240381000b920014042d4511040490000e0a0700c1e0b00300c800c54400480c02c10b102600468000e001504140c0d0148034148060540c203141a000b800300400350490000058030392903860712085281444912400041d4040c0d8030340508a82c0611590600c5410f00c1000030306040d040500620810605a071909079484e020350110300c0e500010f0320700441d80c01c0c410344103025a80300303400554003d01c008003451740c11a650400c4d80e83c1c411402e4022804250180420341c2010640e840d4008200c01244c0c0b100d24000d6a41d0703824006440003400d00050242c1c00384641415103111030b2040c8224411400507a196044c2c500f09490300d00b11407003d0042020420041c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 908289631 1250 908288381 908288399
    0x203061008030d180f0803090c010207140108090a0803040c03020a080f06060103110d020d0f06050d0305030109110c0d080f1609050909150a09060c0806091f05040e0c0f0109 76
    0x107499400c403140024541c1503411070300c02c640508138405802001044800ca09010100f0015406144904100c5403213240560044e61941e10320310940c0004a0808183c00d00c550251540550005900c02070300c901141c03941e43c401091700140d90540e02240d00d000c0900131410205001030140c00c3d55402000c81c9040d00486560303031100140031904058541111000c0310390008103540400002100964450f10f1049194006000b01c0012100c15400c07e10000380c5420621100c81d416600f40d6a1685181c2c01c02000002609040c0b410840703001c410048440040001c1c00000d07105075082d518000182800901c07981c8044020f4602915240c400c98440413164000280c00100e84064425044075517a8a24490501600d40c000e8410483c4540401c00d010415520061201c6c0c811720080000b0140c0800c11070b141d08003260203a0b040120032010a500311a511500440505800b14400f58070b51541c010405031122001601d42c40d40c450380d5491a946442840920b10305420300e0511029490000d100c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 908290881 1250 908289631 908289637
    0x20414130609051e0321040309060e0d020607080703020d0e060a030e03070804151803080d0b0420130504051b0304080d0515090702010c0801180e0613020306100803 72
    0x2441c1c80da50380c2075002041800d118220b481c02200c0000412440402812a140e900400f030484140035421001908000c039040301600403501a556401c03554103100c03050350310703407400721805500c80b002048600c01a510034000b080c0c1e4070310a4010035150b40c490729019140210a00c210400d00c25801c01030b4001f6152201545c5101120385404180090f04d620b0b45800d501c111003000e0071100300010086083c440310120001c11111766540c01d40f86101d80031101c0d8202081d400010282c0004010b9560302c10701da0b0700700c1c4107199001800003034180c0da00d0040c0c11612202442c550606a0045900082c1d040384c441c1841c002c08065a017481a41b5141c41c8842150859441094081d0070100200b030501081070252049900640d01c100401c2c100600e002c0603100403034403060f100b40c244500250303180344107014100b240012500c0d28910f9900308400d14440c881c64480780c1103015540d4150f00f0b0b4441003000b00314000c510704001844081603a0040c1800c01c40024501c0500880d00c503002c020781c003000011 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 908292131 1250 908290881 908290883
    0x3040f05060a2703181202130b010207090c0e10030507111606260a020316020309030c13020f03100303020c0108090a0201030902041e0f1a01080402060304050f0708030702041413 78
    0xa0480c28801d21325040e240c0d141400340d083c220410400000c110f40840070741141685000310b821070403010b141440e0005860403140b105e8016000542c08014001460b00309026501c034134104140703010040b0022a082070400c40c44100080d0f19201800900d58005e00250f0350b0a0380b41000d01180c0501155419001941d4420001000348a8041d288500755400d03410f400340d07030a00700c803281d1400c203801f84402a4100303032011843e6501410700461001c2c000070444910b07100143c0a001d950340113600304000c07800100d000c0300041e03400700a60f00c4d0004203a0b00a51195030f910800003005170a50400a240c42004401c181c10300a440b4144401e42c600000c04503801d51742440c0116812190381b001c10080c10568480701598122444002161000758000444918a0860403c100c41d243c00c4400406000104c01c0c3d4045450f1202040140c10710000841d0b105018900b1101119900c2c0086032400096500102c100e802c0484c0250451034075005501d40a111030115003d00c2c2009d81c000c0846c4007403044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 908293381 1250 908292131 908292191
    0xf050f0f0c070812190804020d0609060b04020a020f0c030102070812090a0f0b040614060d020108041a0408030708010902090f120a1704090e070803270603040f05060a 73
    0x107502196031008000c554003078003803070055810064150740b1800198000d80d020201d41c13008114954000d61054120758492600109951000d0b41c007611904020303c0702e84ca040d1a40b80e11441c21b004181ca990004200d140002e0340101a0324803003424060800500c0030080d0300c66401008068040b54040065444c440c1507103288900780c0d11004a61380c03a0114041008020120542908040c00380c2190102e1240380503450500040c91140d00c040803224044500c9648100d5000842c00994400da02c030b554010f115034242c0c00c801c0ac103200c4504601504540407200c02c84000100f08032030341d00542450061416810560500340d003d0005a07101070010400c0d40504020074050605d0241000490b100c15000400e0350300c24101031001038955807040c0680b10225003130881d820318a00002800a003241d42c0340b0040d5082c00400400840c000b03003811650070140b11091040d48599071140000c50095200701c8134450f003541545002428080d00402c103a0b81d152a01448000f22101e9803001202000d21074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 908294631 1250 908293381 908293387
    0x90d0c02100504080d030e010e0708070b070804030c090902130209030d0c06290a051e011808101d16030212010f090c38090409020904030f0f050f0f 65
    0xc0802c442c079010715070014800f88103281c07484407001d1b09540f201404401000007802040c03a946503040d500c51952003014402d81c440e0400300502d800c00700240c80700d14030855000c3d00e4542da0f602d540340001c45541165024135a608422011894500c0c800c41001401740810340c14802580c1c0040d4540d8110b01c1007205128104018a042282541c402c1030040c1c03030f84403504035503140026500085800340200a00070456101d010465150802d00c40c00b04c107814041041d4500b003014011503584070308552014000008190110f0703c88020b1201110350003004000103086500c07071814860016000a640c1070603004040300801050110200d503003626019038003000c240a034002d90380c0c01045030204120100e0318202400d420808010035400c100d0b02d200c4400303140c401161404102e200003500841d0303074801e8402d14000f55520300c0703005000e80c0c1400520010700c1120a0300810340121080b1412030001d4441410420000c2d00300310758590301c0b0351916156051080d1100c80044c184124844144500804 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 908295881 1250 908294631 908294659
    0xd050a0b060304030206070e0103020717090604050d0f030306050603220c051801050301060b0307020714040902060a0507122a05011b0804050712020a0b030a0b0a140405090d0c02 78
    0xc0e0404032090344003806140e41c0c0e1506080094680d0340541311100041c1414400390859880b078000e0380c0b84035030040d801e0031101c541c5003403043c000e40c000160b058110400340000aa690344400038405a9401540d0641d42000c403480c00030203d40b025080a0321904040c03060080614a010301500d134104030a00c84080102c1904009020a0321030f03100d20762205070549014000c0320441403103030494006034024003100340c44003201000c5003c210380d041b00580c0050b008100004440b140ca1254242c00740c80002d440003180c01240f461741c801340070000800c1000980a0801004980c1e04002080d10300d08580802d41e00c1c4d10141524031881800c04001c100c0c12140e5051000a5002094112608070000404e500d5000d010b0140c0d2011501074601d8081c41000040c00e81c207081d4445980e550080492170494103110310001d0366040604440c1c41c00d66a59130761815520342454540107401c0e20247d0849011400d0108030540d6001088401c1c5904004d04103241c00782c01c000b042c1c44056040300c3ea89e07420185 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 908297131 1250 908295881 908295901
    0x40308100e010b1c02040e040f030c0606150e010e0f060d1e1b03050606030601030e1608030c161211031f050402090c1e0a050409111207140d05 63
    0xc0c0e600032046049000c1c000088043c10640104131240c0b50416100d414035805180804900aa1068947c0c00e079005c1c00050000f1a0103500306002440790038401d20101301611044211001a00301c513400c0060101006c4125800046815400400b403170321070b40710398808002c00c0c00001c40240f40c50003140d0108011425400b1a00b00d01201c100c0e20700c00140c102001c0c1c1000e0090302e01c1e058000c8035180c801d000e52898504c40d00401d84203010241003d851a03c40300b0045005055082e426840e500440d031071131582480f410550b900400701c02c0d00841d204c8a0703500d03802e03082c80d1031244411500c000c000c00c1000702007030b0002414200740c0c100580c02d042c032100f031020a083c8840303108881e401c403034a8458200b0300b042035444207020341e000740c070b40c03a4807548c801810a01a20403400000c12072240c00c2c110060741d072400300040580d02102e24146040c01d0341d45100e00300f07a441046405040c040080740c203102d040140b010b05540190030b854001c030284039021110328284070701030345400e15540390000680d140e51 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 908298381 1250 908297131 908297161
    0x509150d060302090f1b0a0e04151818111c0323030c07020906040b12010204031103030715020a03140a0b12120a1107090501061e17040308 61
    0x1146261159403642403148030001440e49000c100e1150281d0000705d50750951101c411340c0b10341054044002d0703914021610031420b42101003d6070030040b64407282d401c15200d6001d10000c404951045a000d03600b0000303900b40a108550f9101c115a107400850048417a081000521403504040c02c038030441c1812020a1500b1120340c4541c0c0041c513044500300406910001880c51860b015601d230055280140c2c040b1514402501e02000101c41071010304050319000340c580c0d070440e1b0001e1001134101e4904001c640d00035001011881644d502041c10001d100703000c88030300c0b071442040300518501039103662280a002c1c086c4904080319640810300c000c0c0c481c041d5004c40c3c5101c8841c09404c2003484c0141d000c0014102d000405805494001c1c0d81a1244030000b0708070104420310b5030902d060200c445000c80b041440074042c1c141c40c0c4504480000c030001c0b20302c01c083c0a44441c0e074400d6446400c440100805040210088082080700352084e100e508201c00001c1d0090360514028003641c941c4001601102 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 908299631 1250 908298381 908298409
    0x60c081306020604050c0a050a03020925031e1107080a02011107060c02010c0e011e02030f0705060609010605090105250c0f0501030605040515060714010f0b091609060509 75
    0x8000c801050860700010340601c514800c40c01c035101c400c000f0090141d030610511469400481e4000140700500d0300c2041d455010b03202800f8252288045e0500200030400c8339403000110f99607490359040c0c209104202c0700902240d140601c03072101a11234843d22440341c000b01600310000400c0180203075100703400407028a0b1810503c5502d55945040c070704010000707120350601540c130300750003c01400d0080c40e00100c0c0b4a01612580400311002030f6504440c4a440d81500440c042000741c0041700b4104400741c0001802a070042529140480a0105824042c1c10070000d12000f44841c042036a4440204c1d036140042c1050f40003030b082e80c2e403a0003030b080c0104000100f100f04a55004a0600f400c03d50020403182c0076a401d0200d16550014071044520651714440003042016040215081090082a6140c41032984140c1030340301001180c00c40c3c0d00f900d140805c0031340f41c0c01c2040061030702100c140d40002d4202601c550384058440060301641c9a44203040c1406404607541d2101c2c2e84483c0100907103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 908300881 1250 908299631 908299657
    0x30203070b040510061409010b0a090e040b0105190803030402010f0306080322090603051506060f0304080a030b100e150c030a110706030e300c06160203090a060c08 72
    0x141098980700380c469400c040d20018285c90002d0001d40d0f50144003600c0030301900500900016403d043c80303141642d00202c0404180442281c000a58141160002e4860b901542c01030324554100420041a4050b0703003e014011244800188003000c008000c480c0c000d40e0908002c05c0c9011900740075030150046506c540310074040425044203600d0b1040c42d120200786202e0751200b440d520f0b80004011141540001340c0b8551100403840144802d241c07040780c10010081406050011039000282158001c070380c05c031081400414900401901800b900d100804201d0300c4091640340243d006123106040008248103208031699050041071f0601103450108072103058a82e600d45182c0041c002c4075504500816601c036216001030214403912030010208004405000340c041211400000300380c200154618004640c0a001450300b0307942d000340100c5c0020000b07407803a841c00e01e154030198511200c2c0c007004d40d04100b001120680d250344028082d00c2280c1400c074001501400c2516150042c41c41030220 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 908302131 1250 908300881 908300903
    0xb15030a050402030106061e030f1503080a030f0603030518120f0c03160305030318100c2606060d180213090506010b0705030d050c121014040902091303020307 70
    0x80110366084284114001d90083c400a9039442048800c2c1c00708a00c040782d401107603500e2110542c800d80100030302c2e148916003c03c9004a40e45d0400300d03110294421558140002140081507405000d0241c9800003030300308104161464402030b00320721a69400002503040300080800c2c0b950359141c52110710002604545014041f50f200b01d40c0d0745141d0081c14403030f100d14007081e0b0840c00071401d82c0e02503035071010266042d515080c026220380140030320840440d01034034080201c2e0317024a01c07030100090355690380c141c0483c04001841a4141c0182c2000c400c161400c1c0030805580c03142001c541c01c210036800002000211400c0c54130f107030306080000075844129242988807030300e00ca03001010081e00680036520b10343da940c03110030703064403e00c28003c4c040d81060020b541108041c1c1c0c0a107a01c44025210b0902d80628461010042c1004a5114000d503001d1b180c184000803450321041164481640d08200c1d81800c0e80002e68140c1c4014180c600c5540d40e000350404241c405c4c000d0350340a43d03024150b508 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 908303381 1250 908302131 908302141
    0x2101107030b0a0605030601080a0809180c041a07120f02150f0103030801060224150d1b080102120f07051603030b0f040225020a08030d02030603070503010603080d0b1503 75
    0x3030401c000ba100c0f228001e052001c040b90505d0081480750480e004400242400d22143d0381d45403150300305414507640019201500040358620030140c40c07260043d400340b40d5850342002a440030000e410500e8144014052042d0350024800d00503080e15819103052104443da20b11070100d190621203900c9840c50390444040c00341c0750a00003c0c49050381e101e9140c0d04038982e250700e0100e945030308000c1c910491425101d581c248071032107008080c0e04848001d0007001002c40340f030003280c2c200d00c00d44400c455044080b11899840d001c0f9005110203440903500940c900f5240e07454218101d00080d1900034101c66040100301071a00400882d4802410403000c11074040050601070010207c0c1d008043c000c080b056070320004c901d00b6208803079803c0c03001c2d60b410b42d2420040203285410101064104e030044074100010030100420405480804203480015030359141c9030050500f015529440180280c3c14130100344001082381d419a00a201440b1000440c5500200040d014040301207160441040000c1440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 908304631 1250 908303381 908303393
    0x9100f051e0408101a030c0a2124051008120f0417100c0c0f030509040e191b0f05091005091005120a080a030e031909030302070e070c0210110703 64
    0x10780b00109036040c410355178840f4145900c075404403541c1a440010440c0034070820500e00b04584040700800048001280550f072000d040c0440d00740b00146078420401d070b82d440c08480d03004260303200e500401c40e01c00744c516241e02d06545110f002d03128400c40d0000f0030b0300b0240308000000d0380c004108000f604d0714071500440d601c60b00c0e5903441d400c0c106440d052080c1113044a0080b00e400d003185501081e41c181e1010181c13412a52500000700c0d19502986030200821078000c10002e4240d03a20104130418200c0d210352808024110307101201000c04400d69504000c50300c401c1a44104465040d200003140359110400a601c1a03929045554007141d00010f111000d1142c801902c1030702c60543e02000c40c618071410455550310685401481444104010001d0b07502c0390300211503c5030b080c02100d080c40011880c010900241d2500e000005000354010028076a042200710002e02040b1110081400c0c412001005d0300e120705c001a00925050010240252003014a0200122030400f614442501ea1800c6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 908305881 1250 908304631 908304641
    0x6261c1e030e06070f05070209070e0d050303090f0a0c05010305040f0c0e060a091803050d020702030a0b0708060105040806040f020a0e270d0914061e09100f051e040810 74
    0x7040d90b600c1400006602280221800860b041c05615241e080409075400c04c600c0d0341c0e004000340104081554001d132640c0b1802c03c0105803a106801450f00d034500319801d90705c0c200400010502c1584100b45480201700841850b03425240c003881d000c21141e495003441c3d108440c910400511140e04441d00080d03102820000318050340d8202c0f502075990740c1e2250480285d65010444071812442c0e5004c00700040d0140c0d004040146c804a4054200445900042d084c5844200140c80f50508203080021103503000006c59032015003400d101b810b090600d6540ca036660070043c0014503030605411000b082d0f565091303070300b8002c0001e01d00b41c04840c544030081444400f4004000002100742c1c003c0080d00410108642d2032422060303440000080c9000748070401c0c21444064290040360030030850700d102c41e0300c141c00d00c0003e02c440380840d954007054041c0050030b0302c1041001d08000d150030150410300d40c0001128820490070459100f205000c41c0c4418803482540c0c0f00404603c54144040c901c1c3c6140d13000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 908307131 1250 908305881 908305901
    0x318090106080106050d05090124140a08031c02091f11071d0a0b0301021303030810030206030c03041a011503060803131a090603070306261c1e03 64
    0x5480056640c0e24400d8a00c480c0a00548000c90000e0200860100c1d00341d10441e80413110780004140c002c040c1d04003102c0c0e0baa0866504c011441940350900c1108002c9240038030301b0341c055440100b024038050460f910303800f407403c0740040c5002910b1407001c040d550750140d846012000b0f101701c01820074050a00302202d10b4060050205254000c0041c107580d0104da502c0444000803202050150200d101188100008011103403c1d0703034600e0f1140c1551001d2020388a1410050440c0fa0160304600b8044c001c0c100040c500c00e006d1103a08000e200581b01c840a40b5040100002c0254403a115498210300c1c990704140040415503a4200000d4080d001c0c1202160318400c0303850801802e80c40300f502540320310032440003002e1480b0040c4100702c90305000005d07104003494042118100320015000603400e50055415a0002c1c4d07d4090600c82083c043d0f9542c000c4091103940001c00440000e4030548402c0e054040a0880c0942c4054110241c041c50b40c0e89a110001041c82c48194841c440290040c540000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 908308381 1250 908307131 908307139
    0x9012105010e01062c270a050609130f020603040201050d0f05061306050f1c1209181415120102040914090a032f0d09030203010e07060509061305030318 67
    0x668104000c0140318100e40b0160740b2015136034a500c0828440c407001c40010781440e06c3c561000c5000711148500d0340e14084c080020002c9100c0c00c2080800c41a103801070080c021320f000a4425400185024004008040d0705450342500e0b03684a000503600740c002c09810320201801c01501e02c05014240e44154400d4104403802420310104800542c02c5500a00515030048845002c4103024588218284844900482020324510003030fa110300548820713100e00741c042601910b060150381f50100c00ca41505d18042001c00010720b00c1d03032500c21010f00180a00b0000c0110307030151211902c50f0074030382c148402404001c3d0343d1240c0d00c41c0b0314030040c03030903521311000c2003401c00200340c0211003c02d02c5038225425507107065000c0d10088400c2081410108400d140c040c4125a6104165041c07001c00300e607041545620183c24614010b150944419000001c00b54200d10014000180c10400f5500000d006449003900c5400e988269901d00c0810f420540d40340c8000304003121541040d2802c4c01c503034282a1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 908309631 1250 908308381 908308397
    0x90507030b0d0b091b031e190f05120a12050406061d011409090a030e24130b090a0303030f0f090818010201270f15020705010b030303060609012105010e0106 69
    0x61740c12107454000c0024954560080000c211542000c8641524a13002400544030405031503034400420b014014422039118442d90814800d0102c1480085120003400709420701e80800941c00400d03103d0580c400c004200d03590b501140c1482181c3d84418080c0070480b44031140c000c084820720078955400d2190704412090302041507410f00707100030510b010f0b280300c4009000801896405075030010310903101036000000a051039208088180401d01140f0b4001e200640c1c4410500c01e10001e00f105400624003034600b0006214141c5802401804072901450f001030058511076070f0001522800304250b060509050083e020b2003100c100030000305002d0000620041502801a030a0721503038180040d2a08000044c01056080021142c28003480b0340c640352180f03000c0d41d80d00f0000c0c0f00145035803c2c440b98040707442d50400009200f50301c0303201d008500031425440c1c00030000c0c02510503901c2c0c01d8104100241100a010b10020700c03c0440701807440c00b400b99685581d03c0000b00103091050800254a01d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 908310881 1250 908309631 908309653
    0x9171b0f0f03120a0912090501020105150108070e01030624110c01090b070206090a15030b030a0b012c0702010207020423010302042d06091d030301090507030b0d0b09 73
    0x560404218200c40034608000c2400020060650004d261044094888044c58006a40b4200740302403001151644106141460002400c444000b040b07003190b00700c0d808034010b6a03a0499500780d803000031442c00c41031804407680100c01810580d807180c03100303042e81ca0344c8c1e541c2c0311014070400026a102c2d070344400404803135114551703403402c4c02443c142c00304001d1042481000c0f207410082030070f14005041245801c0030f401c080303034280d1080d03030050380a00d196003a50310b40264180520003001c04210024505e0075070035103a40300c224a0620500140001c24524040740400c203030020359521005c104002d00c02c0c82c0031040a8081e50002c042288920710b03220f001c4810002144428806410f84003a00c1c40b2613003180c0c28000105441c00c40d82c161145090b80c00d00402540700c8500700500800000890300c00c2c43d241d20b06041e46e003206130540b143c11102007007011806000080d681124001900400c064895000c140e00420444c81c185800c01241d11340300c0140244442310302c3c02000d050003214148460 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 908312131 1250 908310881 908310883
    0x904210e131b090e070815120a1104091a06031606110d090e1b0c0a06020408010c0f050f03041110020105180f25091e060504020708070609171b0f 64
    0x340d03019030710034500800c01180300b240c4107100040d8000141c85111f01414220b0002401c50070f07040030011400d50200d00d04504104480542a4000000740d80c18480310540369203000c000d0045951000f01e00e690711000035103c2c1c0d820801035030300040541b00c0142c9075458400007490046040840d00042c41040b00b1441c2c8588a5822039040b40e55030002032a8035115002069100240000f03008040c1e10180550701402000340a00441c25200e07500c016036a0746410307212420b40d00030410800500c4002c42c54070707007c07942203402c80d0004071803000301c6996540c49260440310100140a000e80000c0880100a02c4d181c05500540c0518110110039005807501100c04c3d0f0345600c0c0c811064515084640c003080c0101c580302100d1103d51030700110750000da071500444c800712001012082e80f051003001c03c03006000c03620712500029000c107035815460200c440c0c5a080b030360301c24480c1c001c0c9003da0b200d082c4030500c1039050b0070b2030402d0700c1c0c16071050703860080c424141440003204003124002c0c01032545407850220 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 908313381 1250 908312131 908312147
    0x91912081206061303080a020f030406020c011b0c03080d0f050103061409060601210e010c03060609060e01210b030a030207090e0307020d030509060d0e07140904210e131b 75
    0x4004da844002044c19680c808035907402107489642944101079000484600c20b1002c1c00c082c080030360051054a80720000104504038075060013080000c0402d030f00c0017050b81e0007840c0080c0c9030450500b5540d094601c100d50014412480006c1915203800000b20403c0f94640001c2c6490210680813144d41d01c07005800fa40340d0794150360190100f044450100503121a2200b0398802180c03100c2c0000b006901a4512402e4815402c41c01d00000e0340e841e8148166501301191101404c15490b00062240d81c290000e002c03417026042013010a044142540307108041d0f40c201d0090460042c043d00d031840510703d000f83d0ba5a40b1801444902d90030522000e0314a200001a11002e0350010224103034094687c03402e690640c40007080c1500400104a085582a070a0003110200841c000042400e17a10f00385040007036101880000344244e41e40c1051101103003009a04038000490040ba454203003541500c00e80380c0c0148070040c26042034200c826120800b030240c1c005014a011080c001d02d07203107031040b0101c0d0241 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 908314631 1250 908313381 908313397
    0x30325020a1203061d0405070b040e0a15030f11090114030606041505060f03070e010804261b0105160c080a03150b0708030a0c0e030309191208120606 66
    0x6032001d00600d0100d012829641c00012080c140001d0b4035850700645540b410061918801c0341c0104014801003040401000d8010308014403000e00b440c0c1400803040b0b00302800740140443d9138403201121003801c01c10b450040155404000305441d200c1a01c0c004a511451b80d064038482c25081c00002200c8250038110241840c0003000303004a513607840100001090109a4282d00380780c1c0c5c41010585880741c80050100c40d107000005602e0b0329101c00010f11120000c1804c5040103081402d0000245441d011051444508580310007480c2c0c40051001c5180104c868185a01801851980d100320041d8022401001c4100c0360311403e00f05644161000300d49508001d148050030007003803152501c03a42c08100d03d0000381104001c0155107080e0343c038442d04018000d4a5100001040c0306080c0101c1c46413502007030080c02e04104551207031000070b449001d40b80c4c04070f0043e840400321142c9201010032a10142c0340c6003510740d0b901c0d0b0160405104136042482e12180544a0320007140880c074014040c1c680030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 908315881 1250 908314631 908314633
    0x1a0a0f06020c040e03190206090105060f0a05040e010f02040f0f05030706080121050a080301140f0a26030a05190e0d03050c01021207020619021e030414010e03032502 73
    0x290642d8018480200003180b040c005a0005000d4080710042c3c8400c100c5030021540c3c014645030a181091a084580180069102d2000c9800781039940d26006205821601c0444000130308000b50340b4013a0151550389841c42100d480000d010030b03004c01d4a000c001c1920460341c0c9800c40c8544480c14903503a1a81802a0741c0421141401040200c0041c0320484065008000d00b41c2c03092110341e600c92a0900c00720b130840e052000440107001101020075070861000d8101e5000e0702d520303505004907909072254051100c541400807215041c0c845407101c91000401d040f811640c0d54412000014816001000e205128071246480d4030320580c81150360925401009105154180b0a50b905480b10340c0600307412420b1b55001d00c94102201c0d10424020300c600225000b41c041c92602e018071800c1c003102c6c1c8218251303482c8180b0004511112045a00301d1948404e211b02ea501d840b10b081c118903480c23070442156595801c003242c0c1b40c8880b0000c4090b41c02801c140c41101c06804c0c4240b800c0c141d180d801ca40031001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 908317131 1250 908315881 908315893
    0xe0108100b03100f090209090c09150111071203030506030610060503070306030b1303030c1b17040812040608100303080a0504030e060d0501180c0c140106091a0a0f0602 74
    0x180039103500c50301c030060005045505005084102c842620b20121100c1c5440c2d99585003001503003000b400481c1d02034010009003814100840004280032000380c901510001c40301c0703600e605c07a405900d80c090300c00000c1c01110321040d81d802c10b0146083e40500101c001a08107400329009040020743c4c1d0740681482c9003202c0301d25083c2401140c01c1e400c002c0c050000c050719030340c00002181041115500500000b515410700c0051410040c050704c210b03810600c10440c2c0070400c2c40903017401e860390501d410b6208084100407415201060310700d00440e00072140340c4c09000000c035029182070000f44103c554070345504e00d196444048114610255100280c0480c261400240c14215554002030b80710703100b420882044440440031400c10b400c040b000c5880d03295a1070040c40a8070500320b09407404102d00074280000071090100a00782a070007000245401030b901002460b4010030f420540c05800000402c0080801058404002c4049089280d01840501c0700108082d12000c0c1c40340d0030380c3d85603001088 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 908318381 1250 908317131 908317153
    0x1c0201021905070e07120b030316082808071e05040e0a2004050a0f080c150715050f060d120e0102150717090703020108130f1403040f0e0108 62
    0x450300049007012aa503005031a400316508000c9500c5500901e500d03030740d900c0700040c803103065022116910f1009100f50f00500804070744c0b01c2a016806516544001582d403a109450a080d50403c000325403844003580d444040c0541e00d80c44040e0500c242070701e035200114040c62032f070180a40801d130b440c510005101000188503e5003201001a040881400005001c00d0303007101c90f602c401501c03a210446541b000908024501c2d1403c0441c000e41505500c00354403070f10f031008647c0da810200d1100c6000f2141100740c245200b09002c1a6a621500113040302183c1403e040101e004120031104188044030080100b483e5040118a41c0b4949034019007901c50900b4080003503c0d10100400250704601c00e1000700324441041d00c96260040800783c450441d40045048407861140e8010001d02181e40001d2042001d0b0785d010000d12381000400e5603001c1c240105003400300c048560a24060415018441448030204000000b4001c403007400801a40c040d40303c1030007036040308081c80380000d203030301c8420456 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 908319631 1250 908318381 908318413
    0x60e21030606160203100f141003020904051e07030201030f140121080d0c0206011e0b0a05070614060102190c0312270f050a15030e01020c0312061c020102 68
    0x11600f01a0341d10b648802040700e038006480e060400c0346a91000d91074035821030350308290307004d10407084c0300200004101e480d12400c1d1590510b000e10019100da130f264404982402804d00c0001c4240100644001540090150700c035601c2c4181d10080340040d00c1c050104641100034402c00049150024070308807164a0710081c0d61120800d1051806101100d050160004603107030014002e64440d00b2001c40d00540100010b414000160300c81444420381c50561851030000321070200c02e1b07a16011070b0f540c55804420040781c6078010000020a600c1c504041c0703444241810740030512070b0200b40d00f1140c14907002c0c2c007040c0407494084c000a102103120201400003c942000c81121f00569280074010f95034046040020401ea00389460b013903125106052060000d00c5002c0c00103032900350303120121a481c04280e00d060f8411640064101546e80202e0b103504442901103c0901540c841100c1d2030343d40003620601c1341d05050710240d00c203412800091410300c420745125801070303405801a204034603810540b1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 908320881 1250 908319631 908319637
    0x150c200d1112010c0207050a050f0306041202010216050a02191208090301150f0312032009191401030e0d05040e040303060522150f06030e0a0807060e21030606 70
    0x10742d50190060742c81403022a0240301d08a0114203d40c024000c0503d44402e1100d0310507030303411041c016140c4210030f0605480c0020002c1d0842e03406081c003800700001c0f4000300e0080c014090040c4901d441913005a0a009000540c40015402103a4080f00c00c1013104010f003103020603100300c0010580428086000c82d0072000504a50003000d070020800c01425900400c91550b981c000b640110400903081c01032181460079114060000e0030100045000c044007222411040420810381d52000138210354180c440c00003001040c003003024600c5130b0a444016000900c80c0801c1910300281c606003102052040c0021410023460703194030351524260404a1103025808000d00c250141501d0f02d03070002d943d4031000f1901100c901004070001250b8404d1404800b0f45001045414080c60342c200180003094981e00007502302c503040e080000d41003404e41d48a6080c100c1402c0e024000110100b440002c2c0b0400d504103000d07a038981d0b01620403200420310182c19025001045602c001030503c000782c4641005801 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 908322131 1250 908320881 908320913
    0x12180306040803241c060f0203011d07050315220c02030a021009020a0b161a010612020903070b030703061a030702010c050403030c060207081606090b13020325150c200d 74
    0x7000c01c85031006507281050ba4000c1e0302c0840cbc1041c1400c80100c80c0d04203540c50a4126580d468621324605043c0c1c214160070499034800c0d441510b5002c0e41e080d0b184d00200c00c20054440342c0f582407000b1590b032200651603030051511170016001e00c480b0000c1030f9604d4882c00008550003020420010b0070311b0380240041e0400d03400317010030280019150001c0782d0400c00300f051010729190016081d6040100c0100040d54481d41d00141a0041c400600556404102903045e1424140c1280d100d0352201c004802401095004100c000060f5214281441c000c40003584141000d1b0000e029030110b80404948501c22440003500045c81c0c0c807044030000b40e0300e8008000b05402500c04034181004040e151002c201d90701401c07030300f2a40d111120020001081d00070f03584018010301700c81082006d034001c652202c1d018075158019400c14010b00b50100d002c502c100010300190740d111030101041c0c0502170724500140d54141c4089050450502c82d9100360b0440c0440781c40007619111219196554080c40b200c00e4101d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 908323381 1250 908322131 908322143
    0x10f05130e01020714032d0a030b1f0306030c121a04030513080c01031505010215061c03110115051e13150f1712180306040803241c 58
    0x68800490f10b0140f107282080505d502840d03903080b4102c100400d00c81c045070fa100c2d0031079650607006c107100341c0349007a9841070410b410086083c6a0000c0024a944440c8544484004404075000445a855130124050783d02c2810841f01d16503e0348035104c1e0b4a1039244009000044401c0c010245a803030003600c58020303102e410150308100b6000114403210300c0c02c1c4c210346425802107984440569260040903114090002d00c1140e060524000130340b1041c400d082e26020f40701d0200842c220b0f23290588c1404040f0031040e40b01c2a180002d1400812114103114030039030300d40c200208001031a0001180000b203d100510124001541113120044c001802078030507030040c0704d10a0a020482a03008071048004500350b414100e904084038030840030b0040c0c003d4240718044149840031a4000201217800c00303031110810b5150402e100e080c07a0310300310100c002e0740c1601602003804100f00c00a000313540200040c0300080b15026003040308910000b044085241c2c82052003100e42588070640c6e00181070940501 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 908324631 1250 908323381 908323387
    0x41a030d2d0f20070909081c0e0f1c26090d0f0203030c04120f080703171f0501080c0c0a110102060c03040c03020402030601030f23010f05130e0102 65
    0x54202944003400081c5200803440c2d69031003651056100c403c880d410302d640c41580084100782030f03610703503111403e000f10000c0c2035a49204800780400c680030b81d40c61080c142c09844401080501501c040e060070122048a032045004412117501c000c11180e4900342d0a1900411108209a046900c0741c210103403424544565400c2240681c2ca03282803521540341c0c03400521000b009860020b00c01491072030300b042190070a101b40404d00e001c030740484080315001095201180c03009d0401140f04c1482d81001880903a0006411080582083d2503220344c0a80c0e400c15120b03552400045c0e0100c140c0e405480105101d1040f09000b20340c007407188190485d118800240c1010700c0c0365105450f20400c501d040c0c52201340185d00c102c066a040000c1c0383d001a1b480c0300e440c2141400d66491204003140d0000901c6240c000c0002032060341720b58403041401c040d400d0144541c481c507030001c2c48500307007170039403000e00101410000c2a803031070008600040b1030010b40300f040603a5803152800010101040b040946540070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 908325881 1250 908324631 908324687
    0x303060d060f14060901060914090702011d06010f1a092e20010c1b03050904060b190f0e0d0606030506040c0602071a093c041a030d 58
    0x1403048000e02c0100190510f46801c0610412212110591108040040c4094180203540c4030030400b80b03030041e0594111001e911000d409a000d4010320b0b080d561030f642481e58035440e19000241d812304884a42e9082d191700f54880012007070400680c8020b00c010f0b00104600c801a007001c1d010001400140041d003200080f0300b400100c9402800060880000c03240081c201c0e0000c2e00307038142038450403810020020400c002402400ca0b005c43d0343c14a40074004498200c050601400071100034100040081240303545625078422650003400c011002e401c07040000300c000342d01031100c10454403a95201c1e00441c004020030403005420b03000040f9540d544840001000480821043e8002c4d4488e4140380754190500c00000c1c0340c40d2030340d4054040300c584001445a03000c45201268a586403c1c0d40091846416684216145c0c4521070101c206000e402c0031408091144050151040d000b240c040c00300f0400031040c0c242198003120a51f82c1a040404903921050003195858196101c1d80c500403184092 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 908327131 1250 908325881 908325911
    0x160201081b0309071a0315210106060809010e0d050412140307050303190c0804170c1b040c03091a04021503090a0212191202030f070804050a06110303060d06 69
    0x41564043c4080d44943e006204207110021a26039011203290514158904490701150000a004c1203e0291240c07a480c0c04600d2600b40004d102c003240350000303204840d40c5072801032103c00210783c0308040d0f510742281c0c1c00c1d0f001000701e041c1d00307012401d1b40d49600b0142804048101c0718003c01080314903a40c4c642003529850024070292445900a501441d140c2c6402c1d0341c4586800b1015610158007440c10640840c03064002600607041038100c00140c070b00c203050080c103608600c0761058003081c0344070311200703400030400b036030b8210030554810346007405240c45001d01602540d5101c1c1d00141920040041d40c0017052860046a43c80350004190900f0000d221420480682c42036851031540d030010021901503040420352481280e8140e0020720b020a8828241c2d804001c0c890f0009000304288040006605d2082040d508036008210361240c1d00d07003103807a00d0a030f258024410305002344a000c5000850b680210618210038250102841c43e540d02d40301002100098000202e07030040c4c2d55066040321141d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 908328381 1250 908327131 908327137
    0xa171c091d010e01050a031e020a2112030c020619061d040521071b3b060d030806040221040303052401080603071203090906050303160201081b 63
    0x540d00044072541080720b48494840160046802401c588104000142c0551415401448040a181141081440014000c02c00b5a00000300f402c1c0300580c50038215441e520340141248141158540d1414445064050391402c4014001680004000982c3c0170307a00780da500c441e03044680c0300240c00c940b145002e4281c00300500c1c42e0003402c0c1e1034504000070800f0400c0f02403c81000c40060614030f0099011b400400c1c4101c00004004140c1c04000d40384110880d51a24040c100140c0c1c03100040040101a1450400300c89410041c41042d98160990403c0e4003401030240300098035400303d07900552415966284041c00503504643c1c2040300ba1100600100800c1e00780b00c11500c68205130900e410001d0a44001400f10540f940082007018106c0c5004e510740011076400b0f0034151a150340d1100003a04240d00c03644912013000c001d0032007900301070b130061091040d200f4081e0200103d40d143e8084c541d5030b00402980094070244012a40c001d907000b0405a03a0101c02144031240400d80a000d03052150 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 908329631 1250 908328381 908328419
    0x509010b0910121115040b18150307200d0c0b0a0501030b1b1201170d09060828020d020a080f09031206040902100201061a07050331140a171c09 63
    0x140023103651380781000401d048401c2d064003141d090003020380e20342c0e090000c0c4c40007800c0302042c01162662900042d00ca4050428450901020307180100e501034809001c207480c1c1c0d14100e401a442c0400a0f01e844594452503040c1c1c0d03000714016915580d482524182c0c00300c680140c0002c1902440000700d11781140a405028143ea0034030081c40104c0c0048840c60903007072892202c01e1140510b81841201c5c1c1c4081080c1e44119130310205000d61425405211051421202031040a03000044131034245c2d034150010700340350029603a2403031103541e07180555801c124191590421904100b142c964043c0500c0e581c031b904420000d20000302c01c400d03580003400c80c3c001e10100c3c1001d40d440f06420011108100c28141c80400340084d05450301085030340341c940360f101e0002e0500b00e002e014006107a41c03040c01445a024030030006c0c590744009031103107003540c5110007503100e5a11600040e600400c18014180f00032445d001400010b106115641d00a40700b03032818542c68008109a148000411511484000d5040c0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 908330881 1250 908329631 908329649
    0x12010b071401020307120c050c010914060601050403170a2604110a29091c020f060a1b020f0d0b06030609031c020d06090509010b091012111504 63
    0x410107458030003200356145848500c10392040c0100400c0303940013220000d0318038068200040c6680c011600755228002d04048031507541c0b8114805080100003000d0181070451041201c241d55508801102c8c02d200d2408020100408142409080c00010015280801041c10844200c660b41c0441d444600c000220300784c0c189103804140014414108010100c041c030070740c3c0300712142c2d040060100c2884203458511494144040c1c00b1828495148241c52003148010044800b41070380035100464611040d00c164401e01086030b020070a86454011105801515207a003142c0d0203104030002c4060035070820a81c0c0100c4224043c0000b981c944012071520740c1724910038186030801100741460032100501410043d4000c210400c400d90a908100e1111003882d50f02698a2901c00034000c05400c2507480030300140e0030007062100120042d003090100b6141640c0406080d0b4031036036082100800d178412005568990941d00303010454602e015010403501034640c2d032044003410300c020b40c1170307005a03c41108 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 908332131 1250 908330881 908330887
    0x16021008190615050711120703060b010513170f0123060901030503030412030603080f220302060306010518120106080d0f17090f060702061506070804150512010b 71
    0x1045000001c103030208014040100820780c2086011070440c0ca0308034030305090201c04640030042202e00b4410b0418a07102400ca80c207203410340d40f8004d5503208140401c43c2c0c000e003003203440105544140c090350760840c55150900350861600c8440307a483d0040c0a064a054090030032550510f104c00d020340000710035000b0608500900168001e01591000f0f44800d02c07580c844001003000c100004192500300360000031402200d001d092041c0c0050032186e100500404000c1244000486104040c3c40c00740105003440004140e4958403440386d85041c00020f60182d01400454002d509c500080c04044002560481c160354030440001c0d84089480060082c03603442e68024080c03170405000e00055500c00c5c4c01d101032001c511000c040c180402109015400017078260019500c4c242c00c201c1220a00181c409680e1036003040c000003034581070111000b1011f640b289202d0342450034070b05c00b2183e21941100340c890605081406000a100c0030901e07407005c1020901000c840310040d500325038000d0030003541c0c3e240d07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 908333381 1250 908332131 908332141
    0x20616030815040605130b0d0c08030a0e0906030a060b03150a0905010b150d090215030717090c0108010b0a0905060f03091005091b041b09031a190216021008 69
    0xc04078800d521140d000e213084c208100415211a018143d207205a400007103038228030034003c038078030030050361300940b940c5209100040c600c40701000a0440390204d80d61182d0180a001c10700c00f4108043d9025509680100e000d82c001c100160700c04c1034041c0004041d910103462030701c410310100307005603042c0071081d1340d5170562020400c0034400d0031611202230700c10b00b114040558002d9858010b00038681d0165888401d14005c542c1ca58820303021000c0e034089030644900700440000c0201c0180b0b107200d05c8449501c0041103056400190344115418165036119143e8208200021607400c400d501e5000d101030540041845d41d41c0f04041c01140c25042c042545919040d8202860210215a245c2a01e0721781010b0242460022801d19a01c10400d00b030321406135555404180100610300c5413105907941d091800d00443d07404146002164020950030b00030903040202052080e10a907029500428192a0b0540c003c40c81c0e0040c144e00d1102c458440554031041d00401c650340f160155200000d0030000401c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 908334631 1250 908333381 908333401
    0x318170c16140907120b0604050d0809010807050f181f0807030b060310060c1416061116120f02060a0504030b091501050d0c12050a0b1e130206160308 66
    0x303030710341d003c903200c140c00d00384004040e00040c5400010380c0510b88810501c2a20b0700c0e00f0f4100ea0003000c0c0a0311a0140341c0141c105803959800030501d1500044034840442c8266115030305a03900b82c00020f20640c6001c00030303101e1890001e540140759800403584da040143c1c0b1408120300c196000003585400c603051030094030050845425142081c810300313003402442100c4040382445400c2e290035041115021041c0d0421003a90a48298022028030443d200c0305074540c41515650708445d0241c61760700c48805100031482d02d40301d600d010003034180d04d024000c1216000c1c0c10200300c1c01e07a000700b0514440000a03000b00b040307a8030a450000c04a040010304108111612019070390000c0c50601401c1c44c2c0d50707800058501c8510610a0350310a82c5100d200409110741594000018414500b02e180300c0e000c0740c642107494109a280542d844140c880c0050b0300d8995660b0001010355030405800810740d00c11010041d40302901009a82004060203e0708880d22403100514820b8025114440c0714a0807005003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 908335881 1250 908334631 908334659
    0xb13030c02060a0528050f03070507062a031109100908010f05070906170a0c050c011e0b03060717130605130c061103181507030c02030105070318170c16 67
    0x40150170444102050400307034010241d500031180d0400441d40c0740c80d1402c5c11182c81c06141e10242000b440d205041c1d0300c3c880b0781401d040152050501c050340180c4040c60135811500642da014403814010024203a00d40341c1b048a44641c200e2070300300a490a51940219400c4030301c54411824030980e203505209046800c44044001070003546010b04090f42d0001003644854409040341c1100303070710703032002f1211107000e60190780c00c018240000304803100b04807180d0245042c80c070301441034076442c0c02188501414042412442480d49868a00c01c608408141d4001c0c0c02008100c80340800401101400042c1e05008050090102640300354040e211420510b034000220f40c80401130103400021000322a10200c191544207401003000044070030100d01080d07082e076502c0c40300ca080e0384001412400300b503080082e200b0100e00a43c020001d681d141300040c1c0407100c40b411006c90007200030410f00d001402140e4103002e949200e808440c02c0c5084a180b007481c1c001c802ca40310800303c0d5085d00500800e14903140c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 908337131 1250 908335881 908335927
    0x31b080c061c0b040f021303020405130c210c06080609013c0305030c1f020f07080a0309020316090e0705010c1b031502070615030b13030c02060a05 65
    0x1c14a4404032900e1040c405481400000d50b00e501d5078a200d001c1da640d40d0100020f608108030641d95070340400c0c7c20308407000c19400124072072854000403400d501c084e14540940c0550040d900c160b8a0b082814500b244204945400118410409100000b0b10102861002803149489070312090600c1410004040d00c160485050040c1300591400d000341d490056055070303194824604030f420100e0103440c0114807150800780191000142081ea419000200b031001e41d0a45548070142e0000d102898003a0304c00d039484442420001d100308c101003034060008143d03010030b41c10700150300000c6902203400d005445030450740600301e4441c00c0100069a0183d200b103001c40202416019003420b0020f0050590100094804150403990038218034400c040c42c00699001f0002070300d0030b00e10301c6600c80a075100b041e0840c1e0290403c2e41400c8045100910141030b0f940c0034000300c00f03c1e95801e0450310b014030502c500f9410041911041c03005a1a1100100400318059603800d0ba100240c5100105104c00140707 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 908338381 1250 908337131 908337139
    0xf0b040602010c0e091b0702030304080f120c060408300a110705070b07082710050c100e030708040909030816050306042a0e040501050103020f120709031b080c 70
    0x42139692503a0301510309600a20080464102c1043c1040d507594500034190003e401d032100003008a51000000f6882000c440d100341115412031201110454a0003100f500102c0d65021a001c00c2c00607501c1d0000d0414159070604c540344120300403041b41d100341c140002891080740c0d0f42013480803600040c0100440100e00a42043c42c00d07100c0d903030b1990ba90303040e03118a02100c3c10204d402c404000c1020111000c04d05410b101c544100001400308048107010402148112412041c0049080c012815926501200006060000800380c00381019050030f8001450302e0108201990004405501400c044c05441c01c00080c0c4c80c8041c50003502c0900041e0075603018903044804c010f040c0b41e0020071a40e114006a40101c0c80c400c0008581c2c00f0398500782c1280c440c3d02816401d01d4101544100c0c103d4080f641243d0502950342d95a006400700e00c00c886841c24060f9080002440e1051942300c0b1035000011403400e2250340359280c0b1009031503100d2500701c1d468041c65420810464038100080403099030119 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 908339631 1250 908338381 908338397
    0x92b1119060b0f0a15050c0609010c0e1509150f0423180a0b01091d04030807030b0a03230d1d03070e040b04060617011509020c0c15040f0b040602010c 66
    0x40c00a8691076082c400c6030b03440b0204100c40031075544200103075480e1fa0310203400c0f52400e041691500380030301403001d01f000008480d040d1001e107c0c90038421008500c051040020b03d4880e00303100380402e0940d0b0100b100c10302142000800d0042710b4980041000341001020405c40403a514664450050400c2a035807140c0c28803940c0f40d04400003001d07010b41045d520300300001c00301a07000041e100001581c0c00000c51046108041e941c0c2546c0058442c4660b100ba40c541c16a50fa40341803d60865003010b4207642c000000100610004984462002170b42114030488101c0780360380400c0714608104202d40400040c4c020700c1505680022200e010b59030203046000d03000080c1030165480a8080040028000c2800d4501090502100d58805005030210815440d0501c0754001c01303d01030644120300c03101d9182104d000040185892003a105081010707000380100724001d01c10069030059403581d003440820204400114500950002c44c02800003060b0306840341c3c83e2541c082e08448003018150144a615 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 908340881 1250 908339631 908339659
    0xf030a050a0818070b040501030c0c03020619061e2108090402091f0f0f0809031e0d090f0b010902030f280e0105090105092b1119060b 59
    0x200340c0c0c00d84079440c40c200200e40d9944040460000c0040d00d01c00a0b4015028045900107001d0000c0090303079000e8a040c8070700d20750400c4c01c03601640385c640c01800680100d0082800500c201041681c401580314004c0b920540b203c01ea9207403102c4030740c0c01010b80380b0f850100f0090400c850f1f940e4015580c0d0004941900b100d262100682882070307601c01440b40d6800900030700d89645009134401d04070100301d40060102580030015010b002d500c5a008041000c5103401e180580c416103d003441540300c54060350602c10007003020313029a0151002c0404401c014004882d81040324421000c0c1c07103024442c034103084400d0f0304005080c141c0c10380209040600410400c40404145284140c00108020100298402401d401d41004140101c011106410a00040650712054102601482110dc02008180c44c1c00074416640e138440748801c02001500c000c08401d69000f03903120a90508030b424040018000c0c0480d05080000304100303030b141c5240f8804007005001440c031800c51000e0007950b46111610403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 908342131 1250 908340881 908340887
    0x21201060602210a0c03050c0105070249051b06040606170307021909180c06030b030d0302072117060303090d021215102c0f06030f030f09030f030a 65
    0x1c0c1c104d11505201c06000390100b0140300d03404480f0b0b115000c000822440c245032034002e4444816505810391917180720f00c41c2c190144419850a080c010801c0d49481e42000d80c07580703a8461821008000c1484400e00080c4107103070303c8980c0c04095561901c058200d078901460030b5411030307956820580c802c205240c40000000f800100312103032940c04a400000041103000c5d00300345600c081d048007003850b040c21411011080403902243d4a81d10a61000f089240c5604046040703941c01458035506621030380c808400350b8043e40c01030003824007070420103d018000c4102078402002d1086074000246030080c24040702d00300e505507507800650403800b45103408405c000040305000b8045029102d00d90403004c400e0802d008000b6000b1706103d01d09204558900346042e040c00050501ca080d03800b40340001c03800c1c81c08040310118610415030309142d5a16484411600c0007641c401002d0310307010f01ca8140850103c40040024245482e407580c401a035940036041850b003003e406001c444810b92080c84859940c0350 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 908343381 1250 908342131 908342137
    0x3030804020d02040e19020a090b1507210f0e04060e0106050d02041509060f2c0102190506010f0609032001020a06020d0609050708100e1302120106060221 68
    0x28040b00c14803078203021400058014180c0c111120603500c2902410034960510b459503c810328002c44904c200716580da10f2420903500c07400c10b2582c0c03040156204c92400381c0107102400a56001e200304c1080b080300d64140200d00703108142010701180c151006100c05175032081c82c06070714500545050280c1444e08102c0da01100e4103000302824003101180544480e00c466065900428140c1018241009142d20203085003d450081d40009070000110fa0321030b80c001c0780c800d00c42c04190190304145040016040d09011265030b511b034118081d8203040341005448440d0b030306005015102510881d454100030410005c0c40d07502010034080d1404080000c55000c40502e00f40645a0003217084440000380100d0600c01442c20040000780302103a0343c80da100f13655002006a801c1100700b00003e85854400740d400c400201c41480800701c42070070038043c0c1d5001082c4190030000180c070302410008940d001400c84006100000c6143e951039200300030340ca50400c80c00040c2c152800001031060068811803030144 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 908344631 1250 908343381 908343383
    0x2010c0201120e0a0b0105010801080f0c060a11150105030c030a0201170411120604032c24040e0f1f09050c0d05010602150709180902060f1b010e030403030804 70
    0x4412600310307100c540072039000780b400c650444041c1d60440c4413902d041080c40d40d081c002d160000394244004103290700c0014144c0ca0b41d0300d08500804207208002c6c1040203d5018528680800080014000810b4410401c40c0c50030440031441824a604190030b040c40d01c000c10036003500c00d9100101308400360360170903182c0420800140f085111a51a070800c8030000030703071031040c6810003444903002403106404600a4040c5210340e4480440a001c660303120480c44c22207179000030440503810707940c04504c0e00900d5070715042e154054803003500003140e4911030241c025038440c442101552040102060920a03800e0f80b00002e0301c000c655040303641e2055031035070195000e071168060380c40e0f010070145110032040d10301900c0c202c03006100543c0c40e810005c0d00c0b140e00a00320b0a0400c500340100302050301130b140c100b0503510185070780980390320421403074409000f0f07410703042c2d03040b250030040031903072136401d10062a00340328004420540001c4911803030b00311800b1f10300e84040c03034000348401d00009030700809440d042 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 908345881 1250 908344631 908344637
    0x90d030305040f0503030717010f0e0601110f0f010603060f0c090e180a062306090a15120308010f0e011503091407031101020c0306040b060409150e010b1c02010c0201 73
    0x59030b034074a03100100d2500001c01800ca84004000c000d0f0300c50340501000f0004203401c0c2140e44699a40b281c09500003c1d500401d10789500070300000c2e00652040745280074241e8800100e406881d1080c0c209801c04104241004490f51944820301c140107160180c0708001e80c601c0001c01c120984042c0090140003a409030348401400704000c036000030701e5500045801d00d0003001b035030403a1078640b403d8401440d4002c2458040d4980382e5445103001d0004440b03a00c1680c0107040e1449503503800721f04d03c00a01e08035102c2140300803459000701d041c0d082411000c40452180d120b00c20300d035042040420340c060f0b0981c030100601e00c18100500c0203108000c0c003001010002e04000c5582d803118038141003110905900407030140702e0000d0000502241041031a0442c10a80a603038034135030585d041c036450300e00c111030150030346150304086400c0d410540e00103c07075a402540d018030950055010300d02030b1011107942d240380d6034443c01048a84d00d0a9201f038009519181011a1601900e0340081d199080d02040a418 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 908347131 1250 908345881 908345891
    0x306060d050723090f060d03080a0608030f0a030e12090405100302130c09170c1c050d0509040b060a0206070309030e120604060f0203040c0311061b01020a14090d0303 73
    0x400100b00302c41e401801d15031500b14248242d2518111100c04552040da10482c3c0380000704004203103000140d0700440c1d01410b41d02100ca402c1e2801d40e036456025006510070341c4d403090001400c0c1c01c140b0141103145a01c000b130a50381c200c501c2e0014140c0306204075580c1c0e80d40001003035882c04520b1000715049040180e401244990b221281102007507041e80c03000c0d40090208840c0a003800003a4401083c80d10303e070f110030001d151502e414952240c621100140558001003a042c1c0c18517141641e4005503030100c524803081c0d4503955540b402c0048078610340700466400324800900c0d14050141500c000320a8a8903401c0412400c0001c2d91083c0c0685580c0034182d035101d07005c4c14544103420000d000301d1f000d4070010381d1100c050101641c850301110161441403a007001042c90034500e000710790007a5005070130a9041806d5032160014035150300d80c0154000020401080518440d240c0311132422102c9000607200c80c00d201014040d80b000d003240319070040b0100400e021a60303070b01c1b0340d40c080c00f43c040c540010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 908348381 1250 908347131 908347133
    0x1603170105030f0715140307030e3322030c120503070c031d0a120209060402090d02060f0909040308010608070903030207090c020709050109061706070e0d1505040302070f0e060306060d 81
    0x100041c40c1046e003100008000700b00000709030150414500494803078101c4000345003403003a030715800c1124400f04481c04425029040040783e450249500070410000442c0241da03288080d1089404124085000c1540075081c482070240f41c84007070b80e0300c07180307400c081d8076614010038014441c03a010b960007070907c0710019a4404640d400304441c4603004010f0400c0d04100e840d100360741c000054001c0100d21452400c4001107041c2446d00035102000340103030035042c580c0113590800ca0140c01185170301c0009041848181101e1b07035086c582d10700450103900d400c101035040c0b98006021460042c084002e11030b41c03000400c0020f90020f824401c40e0604180090b04840c04582241800c000c0ea101840403401e0400200c0d922140d41c1c000411544020090210007444280d0f40b615110119000400700302c10840720580c0741069442c0380b401d9803003000c0b0901c1d01e503548040c450485400380d1741600140d004590030322040902e80c4a06028245500702e00c0d001d46424000a50340323b0004003e14024032001f2400c81c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 908349631 1250 908348381 908348387
    0x100203070312090f0c08010e010b03010902030304050d030c0b0c0306040507020114011e0509090f06090d0c030c1403030702072c1803120a0507140f1e1603170105030f0715 75
    0x900180e000110185c4a5a03030185540038129028803c1029480c2420318113a40ca41441407240c85940a0091405d003494401041000d00c2140826424804900744690010b030501c02502e103da40301a6082c1e8482c20220103002c1101c03001000e01c004d44e80b41c0b2480440d009035806c102070444540f09001c00407000c1a040c1410140082e50009800505110601c07807441d202081c000e248071031550459003141d803449030b9607603900b804c00c2001b400308000c10a024007007445102c01c2c1c15400c0c06101410400c0340f8903c1030300c1c07079644100c61110040c0c2065400740407444020417040c07150700c1c40800003440d100b011450001d0b0f65070050f0103c0307200400710307104401c060b03018001d8410081041080e949140360a08616001c0d08040722254006a5980602207050032140700342c520301d9117a1b4555a0410010410308080c40b2910f40f0b03401d40d0b400d002d0109802e03c07422030001e2101035100369030700c038048001d8103000d252203a4107811183c402d410010200681d0070340042d00d00119400c5c800d10700e2540d00e203601c003a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 908350881 1250 908349631 908349653
    0x10503040f03091d010509070f080a0b030309060d050906070e1525030c03080907030c0b0304030e030303161803121809140906070f021b04060806010f0510020307031209 74
    0x14520312040b204c040d108295860881ea04881098a80607241d58500c841114034601e1115100003243e0b1403c0443d40985181d44404e80401029080f240381016030030004c0c4154201c2000d00c0c0f01c0c2c13a200c000300883c031030782444103d401c6066801c10300303064a90600091400340790748200d002c50030000306060b00440491a15110340b1068000f101c080101b042c18000d040f0001c00c1c1e410350104080c100481c61100c000140d000440c2d800a9507140601e080c00f078022115070028100760f007005102012440c4954080c8021400b8030407204c2441c005c004804005004c8100410003104030a200d07006c1040400e883c6c49640800d162070f840c014461804c2040554100349403038018070303102c80c81c1125102e04480d400e9440d0b4000c2041d601202c85c0e03a41d4180c07046805054105d01240160400e401500080740450095a0541402000030896549840c04103261000c02d0380122140402184104a98280307416032a10031001c1c0c3c4003071072400545440c060306080041c00903145080d034407000b001c284050160b007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 908352131 1250 908350881 908350889
    0x120c1509030f2a010506210a17071a060a050a0b092103070f171303080912011103010603110a0212030402040603020d0b18070e010e0901060b03041a0f0105010503040f0309 75
    0x1c10160400c40e403e0741402002d04441e41805050424191840c80a034000c54070380c0600a0030052140102903640c2003c403083d44518100c95510a00440b00052442078a4000307080e091205000685040b0381007200c50041070344514094501e401013170000f00f00600c03c98504510945070400360b02c0c0701140b01c003405015030300408894000492a1820002c0741c1c1c90113102c0602a041071002030402030860200c0b8030800b45800703109152040700308009001d00000d06401c08004101d54030400d0041511800c1d00d19801450a0f115000001401066098440e000e980c1e8141543c490a127006808084c1d6078140d202c80c00d0150800c0031000504540d40c50b0803400103142c0c0a40401c0c81f5403003a240c1a41e0040040d140c1e01d401c448242e844814003e00001c4200c101c1d0001203110190ba4a801d000d09121400070701a00c030707103540765280451641d0701000114092403155400c0c181e61001055011199103019001401c5024810b004228581c3e1160940b60040d40007403080380010024641942c0400080d80 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 908353381 1250 908352131 908352187
    0xc0e132c010207060b0906060712050c0102040905040b07031b212309120915070c0605040303090803040e0403112508010b030a021804050f120c1509030f 67
    0x300903022540c19000b603d6040d21914050009004210070014035000494100360005400c0c0096404107980e126490034001c0f0900f002842d0000c0c540103182603a1140d00080c54540e1210240320070003d10110095001076613250410101924130102d0340002c0400d0070407010030207045141d90000038400394148070440b50181c100a0b94100a1030724441040d078041d1036002030744020000f2220100410700a00101c00c6c90130651801011000f0003841c0b802400445880c0c400c2404010000303048501e800b0098865a00ea45441c0d6103940340003041041e01790402030103500240320804c00c14100003400342d00301ea850704080c10b00d800c1391461286480381c1d100d404d0341340c01003920314804004e44d00d49000040d1020880240706080000051580d25425460300942204101440d40303032003030050b0366160704070303106005460319a071181c80c40c40c3c0f60291032000078406040001e5546000d01c01000061030114400e0400070407407801c580d1854aa010340ea50380040c83c000000c00d036008451041e20040c404c01401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 908354631 1250 908353381 908353451
    0xb070203040f09060e060f03070b13090203100e07170c070f12030209030708010e1e070803040603020a0801092d060f09060602011103101217070f03030c0e13 69
    0x250420024010303501c1240d440b001400b000c104541071030040700342e0b43d07c80900148085e91810281d124107034440c89040b103000d0007221021a80f0101400114010004000154400c81c1855200b50052502038400707014880c45804840d10614a8200310b584a10072400e1035803909124106440100c06180d0003c3c04124111030031892a03405038007800f07180303070141c0840340d0b141d8548804500b200c0032030000c11002e51101c0c0b50350501d07001c10880154504240c000387c0b003000d90781d10071951464000f504000046a0042564244a54000349460042510355402d02a50851901815001c40401195944d040304249900381483c0550080070080459410340350816540307800d404028283da0043c18015420302c030003c805000c864059900440798070b015680400d140c81141d902c4a81c500900f114204c1100303182c04690403031400a004100c4c000c0c0d04904007059a40b0303000b402c94000b0705201040c4921508140c42940b80c07924452031541ea404000580c030100c080f2940d90401820100c1c410307824144d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 908355881 1250 908354631 908354639
    0x40506010b07080f1b0c010c0312022104030201060905061f0f02030c0d0210140f1f1508041112330c0a02060f070c02133c020909040b070203040f 64
    0x1208010300a445140251200c0900f1b000c0111810111b40e14084c000400016044890b150954001c2c01400d20440d00e10070340000c40d0360801c0c1500340442d020f50160750359140806c18031506014007540300c90101c83c05402c04c40340d58002c103902000341c0c04413030402c1450800882d0280c000c0045820700c0884208403580d4105081c0001d6807114800c07500e510450401004c0194004003003e0315008034001041419079950707000d407000c151190001e03140c2c104c141c040c0001030001040d158401913000b171950740000d40d01e0305041014840c7d1204488a00900f03c41684644084000c0351708444540303030700350450010b4981000000840c1007000c4018050030b103501409000785814000782802e401903002c1d503a280d910500881a00034046030011f020030801d102403001490184c0300d01303141d10840d603800209203d2210001c0c03c3c40403100d040c42442107850400485115810b102002c0c4020321f140d066203002540c40101b50b648001510007030061071400c0105548500030301c1513a001d0110080820505559 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 908357131 1250 908355881 908355907
    0x5070c1407050112270f0605011401180b1837080106150305040302010e0a1b0e01030804090b01020f012301050f030604080904060506040305100b09040506010b07080f 73
    0x5442064041218100c02e40c2c0c240602e40503504004c0740040150705400703402d482d5210317035800c807501c00ca03070403100303855114000f4072540309060183c1a520310000e403407100c000007d0320014080c820810b03220018141001074107100411a040c0140d03210030b05400a4052010400e0303060b0300c075110030211202c2c5140d003141d0b902c50b5060000ca00c518101c0c0341c4c049588c0703650705401c0300e0f200d02508400042075440f102c512030103a046503801038403900c00000c1c40c03c000d810340b038100071454000311008403070400c50a0824004a0a0302e01400d0300d40c40784000780d4550f9589184c40d00c280d02c101c3c6840d9858500c2c00b407181c1e0007400610440c400d00d000030f0044c10700d024250030102c0d42030460b911004040b030001107001c0c1010811842c2480c0042c00030409500d660302d4090445d0490b1400301d601c951102001306e4691683d8010300000c40c45a0b001b0a07001a00510300f80c1526010203c05000e02c0c240801c00c00842d50001d0310904584540c4150340c3e4030815402c1a12041c0310f108008452804002199034030050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 908358381 1250 908357131 908357143
    0xe1f0b1303021c02010e060a020607140c0f0c090a0c080126030f0301030510020f090108100506070516060503060604060534050714030c041505090f150402040e010905070c14 76
    0x1200b46d07922020301680904002541c00740d4242480164800000103046c0c90283c2207030030740d0382e0445142a061144082025241c0b00c0b40190f543c84035001060b038500e46082402006410400c103600c1840a0340c82d5100080220005200740040c0710703e501d01c0140d248426413200c06c6841d50140a032540c2d00c1c5908501c541c40d610a2000b2070b9981b0980340d1481c0e019410b4400c2d0340c071002c1e940c4285071500c0c08a4004484510000d02420b41c0b543c815000000c6581d601802869180e2066000d480b007072642c40c10020451110354840741c00d2000800070003000390380e80003c039000c1d9001c0e0f00704280c48500b01c0e6030494901d03801c039050041d803a24000d000440941e811014108003071040c811909190348038225981d1a000c050141a0954001c5d07500d0107041c80c20360440f900c2100d0003580800c40e0340d520b00000e1720502013620030715420001302d4288200c1e0140d000780118140020b840c154645480c00d24035034886101481460070080d914000300c1d0341d045c80340780c3c0b0b003802a800c0000c1c0c0c95451408012562204 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 908359631 1250 908358381 908358383
    0x1021234030e090c09060328140105030f0a080f361e0f010e030604121e050f031f08070501090603090507030602032d010e1f0b1303021c 60
    0x580076080c441d0103072600800c482d1013034000c070f110b250810a102d01804070941001d010071030400700401010301841c4c824050036402032041a03020407c07003c0c0c00403482e6100410f8028038065040004207000e102c400041000e00170750700c021029500d202005d00d081142c0200320304400d200d0190f4260b946412050030380115403900a000d2254410f50b04230810000c025a60b010304200c1505070f400341d040346400380001400c0c84060501880549101740002d0030260200d6017100d01d00c180f85036075100c203580a809481c14504a02058400d000c0a80c07028080b03020342080c28800c0e00001001820103200c40d6502641881040c62020807191501e4010303449d0300d4180030341800142c100900003021403003400343c00c0303040d6040400341c10034a0442d1580d00203580018914228404800060340b40c40c000d4403100a0714541060a940642d414642100101000940300c40703140c444560303d440030b8603010320502c0f04a5645001c01c59a50390807072440022500740e540f002c0d500c456800c00c40c00101c030a00d1002d00901d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 908360881 1250 908359631 908359637
    0x702010909021305010f0c02090f1008072103030b13050f060301061a0706150b0703020c04090506071d10021605040204031e020f06070305090306070e0102123403 71
    0x16511030003241c08074003499084003142d0243c207100304841e502801d5084490500d529142c01c004000f90003003104140151000d165006103002041108401038000354041d248a801804180d4980040010030a4100f4188100c00d40030b00e03141000c00d40a0b60203000945e07000780c0184500c84041c0c100000230241180d500c0700c0002c01c0b000007070740c9150602c207160a48680052142c055408a803200710150495803089400300c1e903542c00c80101e484d01d044480001d2044001440d502c0f0242c2c54020300b00141710094501032410b22084400044000c0b0b0b03402c1c1c1c00b202502c0d2450071070502980708102100300c84405031704003144440008110382d02140b0303008818180c401076103c442d1740b001400100c0c403803440080c02010440e65a490072074401400007004500080070000b5000300f5070001a0550f02c100400c6000c60ba00180440c0c1d02e04042c00103a500c028541080f030300b02e08194002035281c010140d11004200c500155003c1602c0c50b40d02d010003a2102c460f900079060628103000c45180b41e86d940d056001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 908362131 1250 908360881 908360897
    0x3090c041d0f012c070f080a05010f0b0d060c200705010935032a011a060405060904020c01091202070e22050a1a180f030301050d15050c070201 63
    0x30a541405010700e0304140e0004c605100d1844100c49800da4642e420700c00d000d0084c0c080000340c00b9040917600c000303407421074080d00010400b4a00182101c0c0d62801f036840140c144500c0c80301c90b585070209201004d801080104208144e0b0208890150b00e1001d03012414000c0701c0076031490100002c440d410340300280c8900303c0d0aa00c0c1e075084903013017040700109007940000071030b40000804140da03450102144581100c1c10b190b00d80501c10480e20050190380d0a0001b4070b9900b0381c049200740543c4420034810300741e040103103c0010224215120318061680241000074031719009440f10f40c11594060f8848000b0013181c81b29203082c6003001e070720880d0b010051240010114030b03208041c3c465800340f961803030f0441190003810f0090410b804001d41c26141401107100170000f04010201e410b20b040400005a00e2510380524904a007884104d0804081da00490040500c00380000450b81955000c43d035003080e80e82c0c1440c16001031b00c071541603151080d0411042c02003075401030340a400070074400d07214441 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 908363381 1250 908362131 908362153
    0x9031c051e120a180507030f0c0605180103020a09030204151508190903052b050106090302030705090402040e121e030403080402130e1605040e07180203090c041d 71
    0x2502d0207881c00c0041000c0c2244040340015406500043c00100c01c03002e0314103aa242a21080d0800d0315580c02601d50100100542e0100030741484000301815550802c5414010f810b164200c03443d40e160105070605a0005154400d140100d40d08001035038020820701059441d40c2845001e007025100718601d4a00078658150381600440e40d036031042001c050140c15080300101448013910848000b0b406000b42000348014201e101c0c2100c060000e1051105480900900b142c00c0031100705030300050411012800030700050b40d011440c0400c44a0881c0d80d0029070310340380002002440d0a440300641807160420728010040040e0140c50603440c8400c00f40703000c0c100d00405048078070003240d004000a8a480c00100140b828988140b15213102e9080000c0c1020410161481d294205400801e01054410104031516090149808061829002d40000c903d001c90781c1040d105510340410210b078011000500d005001c110003d04440001c0041c81200c1e2400741007840480d00c01721078441c900a03804122 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 908364631 1250 908363381 908363437
    0x20406020a02130b01080a0504170706020702030d140a14041706070e0d0b06060a020c0a12020f0406060e13090213050406050603062403030c06071e021209040209031c05 74
    0x1901402c0b0684441c806c40d030701c01c0b440c0c40050100810071101c0030054404641081d40c0706010b04200d80c0303e22401a41c841a5004140c50900c004901400f04864030042ca0360607003503581614441e0946003030140075001700280c210140d006503040a85260742c0c1d004082e03591040000c0d01402283e0607255101340300c3c807c0003449040c82c401c6001030301c1800c220b0045440c0d41408001030212060314419220b080c116100042e1004d125640402c682d00d07448030b0500158070703011648440c911411101007020a2804902801603010746c55494400c000307080403181244099000f881003990300400541b45114141d480d400241070a513010b842d91481e000000e0000d06001511900070030f80185410341100312824075801450400c00c50a416001c10b0000c0c4110342010800107010b09407a8840900d44813112200c240e600700145024421544500b000715000c8c44010304966aa81040d58007594580c94034020a203400251107181000000b81604241c0ba968064082c1c0009400504003212580c0195915 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 908365881 1250 908364631 908364641
    0xd200c21070305040e0705070c031212091e020a0b04080607030c02010b0307092301090b010e030d0e010806210f0712050601090203060a030f110907110a030819020406020a0213 77
    0x30b011520801041c040148401e2aa0b940705a0518106250a03001e55a480404029078011645441034103500c414a07900f000e0f86c0007c1401c400402c008003941d41e1140f00b011514200c40b003241403054020001036440d15400840034149601c0c3d1b00e60340300d649002150343c40000315468030012307141031802044a0b1060117500b031684070060003404400e0801c0340d244014601c200032120441c8410171381900321030160324194003c1c8013050000035881c0752180003500b01076100000354481d401c2404d885203c140c1101980128480130b1070040c04a40e035450202e0030801541c4a400800b007038000600c6030210f4001002014035028100b6200380341e0395005000d083d00c60303024004003c8d80100c0014400d940380c540c051588100010f2104042d1581c90b1038003042c4142142d42039036058440700003814981043e811040c0c0001e103d142080d10001e4036030b03915032210a00d420040030482107001044442072070710f2a0080450030420304547c0d5942c0e50301c0103551007108a000700d00601c0d50080074201c507403982c414 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 908367131 1250 908365881 908365883
    0x603010510080a0b0418060f0608030f03090a080324010f0207170307060204060f11070f03020108071707120e150c16080d0504020405090c01050d200c2107 68
    0x500ca2000c692640c00b5610054000e00200c0c5855a980003150305549a0140c1080c480b141b0300c1198510849091407000e840590703640c900301c9420400300300301c4090004125400c2581241d071054881c0c0398480d000d4205016040c0203055008040144064440742022080c5108140034111840b0718101c40103503810718100d05c4135001342c0c11000007000342c586616813013904900080140c074a0050960340b02d1080342c115801a030000341c58601040384003034005404e03d06c0800c944004202c09840c041e4505c50380e04250200a042000840100d0030b1076000d0000816001040c0d520303d03e00785084500103081d05041e0b4802311f43c0f02d00f8a02d804000c1c0c0702c0410019003204011041c064a6a50076261045a60101c8011034035550802d000f000490011006442c0040c400c1c0e102242c0c60805004100c2911006015080283c100424107099681c100e0121785c071240c540c05c8041035020f0000c0700c600c1c995144031500c1110b004006508a1540e01c0800c00c2090a20000c0c02034002100504d8540c5403406050f40c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 908368381 1250 908367131 908367139
    0xc0b1602010c0c08090f01020c030303010b1b07082812030e010b04060e06011407080414040608010c0c0308153d0c1506081f0b0f011b0c080f0601050f06030105 70
    0x10284185003011b101d0301c1807544043c0101c4001c0000d58020030315550003684020381030765000c01c0d601d850304a140112400300c00040c004201c000d00703101d0b07016260b80c11001c800b4601580c602c0880c0808100c80f8080c503485070030540da00c181722481003029010b040ca0f1004d41721154a414950800d610309441240706171021040305002955540b0010f4400c01d0240f030303030300b400700078240000c0000510b80350050010b845400c0c070340507214001f002408161002900b000149904180507054484d50100d070b4580207580601d40701529881d000801e8403055000310813540c00c010007104003c0341c1d480044400e070b05200c40041c845810000d07148080080300000c02e82d0000640005120404180f819500c10161103400310002030540d070310101c007403400c0101206003030b0b41201341070340654840c003505c1115403021003602c82609052122000034000c185242c050081048410198428015003400c0e041c007401e01c1c4030403503420880d10f201c03081e901c140c00d10855103c1c0706c524441284070704100c030075a0f040710701c0a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 908369631 1250 908368381 908368387
    0x150914060607060b0303040906080d0504060e0d14072303070f03110a12110130020f0409180b09120304030804140d210209010516030c0b1602010c0c08 66
    0x102040080e50140105403155921104c0b004010364040c4010802820b80c6c03074000404034600f450650510b15081505000d201003403104216103500140030007050501211f038442c00ea041464440d86610030503071800300c40d01c69210080344010b5050980001b4880c15002004101d600004050741e80909000702d00c9405a111010000655001c00c6000103000040086050300e44900070f000096010000a03100c41014103818000ba51b00b0140c071000d20b05c403c01007031301c0c8100b407600340641046113070040300c1c109580000d0f51220300302981e040c1c41c0980a00d813014044080044050b41445804041c280c1b13480c8000c0010602a01e000a40d9194100c02d05c5481420365440e40c07400c0d60000760080065030340780c842c81802e0a500c0010b0060b1080d10a5607210044d05102d0101070421010f80361400c1d070724141c0b0400141c0456038004040e40c00c07001503d406250441d01c680340459142e0001840201900b0701e00c01400b801036001e0015400300849076008210364001e0800031641412103402c090500b180070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 908370881 1250 908369631 908369641
    0x210c1602010c08040801020703050301090507090f0510020703060e0c100f0c110f0d200f0306040b1905011527090b15070605010806060111100203190f150914 69
    0x1d200c0b25041c5406041d0701d038140f6a580103820f09903840391804030b00044001006200004c418031500d500610149011a401c508004101c2d1015440d40101c62142e42411341220485108020f03d8001e1a8400404d01600c1400c10b00d1a1b40e6584c0750600d148181103232004031072a244201e100100303c000c0f40c1d444a11584484d201c0040e03030f00303a00105d207401c0303800c0c000d8a0303145403541c1010740c281521810b8100d8522010941c1c0d598400344000c000ea110b064031440380861607400103105600301c1d1300100b400f842034035840606201d400213803800c0300301c0c903017450000101c4018448101520014903240e00c0c5c00b030100c1244031180b03c81402d07000400002c210b1820f0006a10b07561000e20440400740864607031406542101281d074201050844105e07440300c0052102250a00c0540d07049002801d220f1781c200800c02040740c0384d50001110b011010b41c04800503064826940c981455900400000c00106804d60440d0000d03051070652002e00c016000740010b00b0703400c1c41c03240084004050965440c99160 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 908372131 1250 908370881 908370887
    0x6040e090715081306020f030708010512240702192f06191b0f060e0d0215090c0d0807060506012309040b041e06140a03032003210c160201 61
    0xf03a13042e52401d03030900580a045a1a030000d6004003565254010f566150408000007050602c0c200c8035103801c2015044d5201c840c103450404d051100188000c2c6e0355540190407032070309880c2045410907000e4940400207000c03032200d855442c40390140700350181c10030310000e120441003040a520f4101c50100a5052103002d0030312103103500f00142c5044000780300801c02d44a00ca1800361070540b101c80c4e008030b04200304130881c80b503000f81300c3c0755002400844030f02160203501d407141c0c00000c940c003044150001d4103e201c14000101520b000801903041d5005070b0a000d0417130f41044404580e883c1c0340801007035244d07016051f1201c0381001403002c42c04000d04000c4090258120f02812070304035444810024141d6690b01070900801b00842c0181444001c0000e41000e55605034004002005590746004440d1204070700300e000d41b038050600b50340c40c01c003210011390784141e100e65007141d44c0800f003a85582e0a80242d01300760000c038000c04185494403020408510341c4510082c01d0511030b8004510001540 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 908373381 1250 908372131 908372161
    0x6100f06110a050f1b040605010801060503100503012d050103082215110d05030411150d050c040f0501050f030714040b07051c0804020a090f02070206040e09071508 72
    0x1041c0d410b45050140315a1614908000352090500c99000682441d01c41d1809040d02072139802c044900740840f03898000040c11510040c050801040710020000b0391010240c0148802000c01900070005032140c1c9480040794680c8568440e4101d62204004149842c00e0141074182d90304000d109184c02400d405a00c0c105903006108103000e440d0031000100003041420106c071980990701c68034409141100c2c21800e00707030015445030034880103100f413001160007996180b400e4541907a20140d00248841210a203004018070302c1540c1e410030041110020440014000311110a448041016150b00065409000750b1041600b50301c800c1c40000c0300b942c402c08203081e0795031504161900e03183c0c503403141000355401a007003a20780d035000101d2009124085c41075150400c03031600e0002d0250515a0018402110a100b03007101103440d213445100303403a03075032381141c840340da000380070035a00d40c2d907860374116902080340c090240d40031f03400000440c80c580c04440100300640341e56404040e0380383c501c0f01481c61 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 908374631 1250 908373381 908373407
    0x52d04020c0106081f14070c0f020d02040911040f020c0325080406031e0501150e0415090902040606050a050a0f0c0f150606020c0a03022106010308030906100f06 71
    0x1640703500f400580710005014a00020104908003200d4040f00c05a004c01d56245070b10b903400242e0144100710000d6486517041c1c10480e07110804001c02c5c0068000214507198a10020303512503d0040c3c00303c2001141501c090340c1c00016131b010b120401181c070743c80080f80107180942c41ca603041045402464000c080701c44e00700d06d10b0540a24502c00305521920429002a003000011958614412980f419000f024030498824072074107211641c1402900c4c000462102c030b1100500041084802300c035502c0e504504205c460b2040450800d642c0c030708401e0058042c040c0168002c61801e0000700380d140c80307582100c030440350580b2014580000810300300e404d9807182c181942084081d1703a412001540d40c14070001e11030300400100c01850a032140c110229070180e4040015503000900d030b2605500c641c0d58041c2101e0b01144d0b00b0310030300c1640e0210074078086480780011040c0118030010040004a50140d8001d010075821101c9660703c07100d842001d0740e0745006401d8800c000100802450b0b1150180d0404d407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 908375881 1250 908374631 908374633
    0x6010f0302010e0a03060c0210050f04030c03030c030e1c03180803160c02130218010c0201081b1b0d02070b18041d06071d010801031a0c0c0313052d04020c 68
    0x84e65590700c6900803121601c0c002d90040c0c0102d100501d40c40c0660140907040b40800c0500c00c1a4205540c0241aa80c046e100c01018180c0380c20101030414060f500c03440c40003000c481510290021142c2400c3da04a40040d6280071a10300802062207800100411128661100034140f943e21110382d1101100d12603036440f010060028000c0005031a0346211501244500c5409030300c0b40100c01000d40680da8861007541004150020040542c2e4400c8055400180400700400b400d115126000700f240704083c0701400d400c0c45560f440008078030005140121104c55400e0754106511962100420700c035100381d002c01c4000c0b00f400b1007242d1a20390701c4200c0001c441c404090205501e49017150502c4401c581c0d04e004a01c1c0b00c0911662142c0740720001500b920f003441c0020f8150b05580d1011101700341082503204a014400009034514140401c5841c41002c440880382c9501702d00900480414441c011240100d902003400805400b00f41908070640c0941e200c1500c02c400785809200003508920085525 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 908377131 1250 908375881 908375899
    0x31a0607080f0403111c020102060601120b09090a210f030b0112090606090e0114011e030506010b090301181e11100801080c0d120503060a152006010f0302010e 70
    0x2d0300310720800a10065100c5d404010078a4004020031144201080e41a50311034003840c10800181c0e40881c0066002c80242400e0b40c010703c03441d0300d2100600c81018a5a00300c0814010711110003030024141207494400c071005040640003082140940c21000c82403404076503007189188c101402504003104800061612840e00d440b500381043c1aa00440c1043d1106940d4000601c0001c1d507900401c414914081c0081c80780c1001041002081c0700e0520400381200d09490605000c80211041100110f411400301c5241d540c4885004240340d201c600d007244698640000554044500c0060b001d0302038100d500345090003440781c02c00d00d210902e080119820042507181281d035039600192002d00d2400c0f6a83c10402d507042c117080c80d01d00014003140ca0b100f54211404100041c8144500e05040c000e0340c075000e5182c0d103800021a10b00840d0703820204055603841c201640c015440701d80c90440391b409002001115040c0103034a52201420b000307080c0c51000d261014000341d4021940c6400841000d042000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 908378381 1250 908377131 908377147
    0x1c0f0c05030a0c09240210020328060b07241b031503030903060e0c040f1505040b0306190f0c0f021510060c05190f140c03070509040203010b042a031a060708 69
    0xc200c0c0e0084030b22240803844441d02c121202048040442c803070300034032b204002690409000d00c1807402003843c001c00b13003071a1641051025803e56502031050100030b600b4003050300c0e00d0340300c0f040807e03a4900d46000030b0300d03204640362501203103800b403030440b505920388000c0300382541c59401c0900f200c1c0d00d40d1044c03481018001e0788035480354420380da804072085a00040000700a2070304d0421402a600292240f402c02c061408146e030003144c80364100c820302c0c0301800310310500c0308104050169007040f0b99206250040600d0780a8100d005101c403407149609071602280d15580c4000d09204c240c440d040114001041070101340c2c014001e0884090044003110214441c0d682c0201702c91100300001c1b0b600a146040380c07000c024400c0c8190219642c1c02001e428100600d00c0421359400c0b442c42418801d80c440804101503443c20340c004c090468010304140200d28581442100c4010311028840e0300c030041c1311021042900c2841540e41010908042c20074403a902c0081042135000340c1d20603070300b070740b02000010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 908379631 1250 908378381 908378413
    0xa0806010c0b0405010617161710050118060b0304110108090c06030a020406030e0d0503062421100e0103020906150313050d08010b1c0f0c05030a0c092402 68
    0xd00c190721804c000701d509070414000702400c0c01617070204a480e521020381031a05411100140041d205000001c2e2008008100305614141c407646503441d00914000c008941549107501544103000d103048184803d43d9a14007500c07080c401141d000c0c1149451801043c655032050940070b0f040180001124443c034140700006800e03600c1500d107902d407560300240c00c00010b40c060040c18009a100310181c0350b402c400c0702d0003900f14400104280c2c49416144074500800340003107050311721040e03141c8840741c8405100f417600c4980301881c80c0d0100c078500c1c40000619020300c0e012540c81503650700581c642d102d9186034248015410040c102c168400b10007250100040e0909002d1482140e014654055801c0141007690401107200c0481007002034000052110303040074411240724220410380c8280d00990742d021000108000400700c080c0d40c1c140424800482d501801460040c0114034042050340e1781c1c08401d0354600824440c4c802000350b403041c10b882901c5c01305030580f804c81c03160040d5582404050520 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 908380881 1250 908379631 908379653
    0x15070c0f08191d0a12150f0c020c18010f05121c020a1707120e120d030903081e0601080415060b0d05070906021e16030303060315020a050a0806010c 65
    0x5500250440302164070f800032540c405071100c0000e50b41c034000c00382820072a80b2000405400900390b82c841381007070303002d001319a0700c00362000b00f140a040103041c040c060000d454410540e1468859054034412104900c96080d07482d04848108603011207140c03422061007400d0440e03103620081d0740264044c51345400071802601c0c1d804103569028000208152408841003c519480c00215501c00c1c0041c1c000103101078801031800840c1c0c10300c81d45140c06900000d014031942c04801820303001d0050806003854054005410591098407580c4030f541e5000c080444942e0f1420f030040d0f010700480003003402540a0b10660b904140190080141003800011560035100c9a0384620007540e00000c40600014540c03103103541200d2146443e56104c5c0c40c040009503100a40304100b400d414040010583c512810040c64070624503610302c10031002c2c2c0d03a080c0a4020070a41c8402c0d904400f0103c10941c412017a4070864545140c2526940e0130320840312411550904010501414030000c00c980034003151210405e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 908382131 1250 908380881 908380927
    0x9020c030c0601090e030318030c01060f05040b030a0203211e190c0f0b090a150203060a05030a240e1009121b080a02160303020f15070c0f08 62
    0x25036654449003000791520030164009441c0078035082c01d5107000c00c4080200d030341100c11802d610400d940c0c1380e0416425031003503121600d000e40c81c0107800524200448046400c5542c1101d00b000070208290031325480f180e25141c000d42c035403c44500306002007410810300040c02d8407440e9a6040540b41503a442082d00408000c0403410404580200307a01204d800002c1040d141d031409411600035942d660300d03010342d0084003c00140c0f050b400038900c082c0803c8101d200b281c0040008059201103c0b0f40c20007035200380c40c2e444c0070754941440400c0c0c50600081010201ea0b111004040d420000c00c00c0701c00200b20707013081f8000c0e962a01946209804200101007000010f4000060156000e1500b80c0c100c8180e42996018011106030801350b08100c10348205c0d01503000070340c0650f03402083c801241088105050b80c581150b9070030002c42450b50000d489003491105000f1103400c00000c1800311100d08048134403400241b8034900c2c10001412000702011601d1054480c076041220180c8031000b07451407814 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 908383381 1250 908382131 908382133
    0xe010305070f050d0b0c0f0a0801140a0f060c05190b19110a080907031202070f06031a0d032102130e25090519031a06010504091509020c 60
    0x140180501801240000d0080340e60b15078519140c50045101010000400b9110403000000101c42e14049021110300c00c2c01071140319540e0b05048001fa01c20b50084c00360540071407404036007410074240881d543c1c00340d6100303034000e41d1400c1c9805011a484480403c0c00c99003402407500c2806030070403085081a9652144030809643c1c0740c44d001e21081e009075148000c45503404c148010b07025200d10b108881d0b038455a072502003804c0c1e4400a4652401265074401811251034401d400c224640c04603209050300c84080c10300d0403c4c2d55846d002c0f01a200742e24044001c0800305801c1c41c0d0385261040724074402c2440b900300598141041820103040c0101500e220302510740001d200f450369a034000155024068085c10105c0324109101440384800712008148003245465512030300d02802280c0440007010020b0841c0c00400300d15894040e008068481211842c034119140480b0003a07602806204900603560340d820146005202009014180001c4020581d4200081000701e10782c0020458510880 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 908384631 1250 908383381 908383409
    0x140a021009061e08220818090703020c0d050714070e0106170f0a09050a06020a0512060d030c171c0e060603030f07060203070509090f040204050601020c0a0b0c03040f 73
    0x341000d80000c0c107090000c01a20203403180c01c1031040d0130403415500b00c44400101814510b4100d01c4411100369064007410510300840c1403426050916406035801c2e5040da600c24603a01c1c0d80500790309a00aaa515044580050030660455032048029100d80c1d4040c81ca8410141410150742d030611119401032420340000302d0050001c140c11100240042050107004681840e0a54035400040c0018042e818a035441e44009800d11104002110009411010466030f40a011101400544c840b000840e136240c9040005072581c42c1211104d03a8182c3c00d5101c2c40c0948195a0300d2031780c4610214906010100300340070140030380c980a903c500c1d601680c141c00240c024a147c1c0c000d85080d80003042d01d8480d51041018200010040041d141c00135807180015882c1e4442d118292594040d800700702c0e8108000004006d40020340142245c081d0b40250390401c2603032210401241c4400c0410419608516000e008210410718040105141c034000c0341035900306501ca007005588080b90b5070190740240141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 908385881 1250 908384631 908384639
    0xf0507020106081e2104030b1504150302060706090203011d06060424060e04022b14070e090a0b03030307080f0c03011a09191517090703140a021009 65
    0x10081103001e006090601040d07203111341c1c101556030314224503008891007901200304000e5052004d40d0051030b4002c017040d22510700506a4051700150881c9244250309001c0d2000d2118042c241c40002c1d40c0d00a020540340c00000d8031001c01401d4600c1081703030150350722003c1305a01c030341762090b600340f4050090180145051030410881030305c10b5540c0c44e510059910900c4a0441d43c002c00708421603001d03003042003109401c2000074009009076040d0154202c90540b070364208000321030030b1241414491104000d0381c032500b10101d0b031b00041181d02c0c40110b800e0440c01611440c25020066102e200c80101048070720101c00401d045410503295200031504210a20003d0002034a606603c000341f035450700d00715072600400340c8005070710351524440c442000a204c1c48a449142040d2913180405142d8a00107686050401200032010b0400c3c002444108450018001c10140d4034002c004c503c00500d80281962a403001d103243c030b08000501b501c00c0844900c01602c500003041075105960b160843c2c07403460 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 908387131 1250 908385881 908385883
    0x411090a02180307050d022413060219080904021c0e0309090708040b01050409031818060e150f030703050d03020a031b090b09030a05030d0c09050a1202060703030f050702010608 78
    0x20000c0182d1013508110f030240308a85800b910a48441c0d0101c5402407003140e00c40e50707107a02c3c020b00000d640a6540000389441c00c3c0c10f200c0300c0c0d0411980681c1c00c50304901e0b0000d8082a1604070141c0051080b402000303141e21a28264001d04112292450b4040321141081040421641100990300564101040035140c0f49091000e042e400305660604560038549655912800d400500072103200d15a581c00d407005140c07080e0b19420742e0b801c41e0100741ca00c1d0782e02c40c01c0b01c070500c401440100740990704104020421000c00c1c2c5016006410b1610000c103000521400c00c000d00c410381c0a641e40512843c00000b001c40c40412940c0d210140c19140140d507401000e10080503030310100468410204000d004841060707100019504035509403003400d4581d1000000642492807014015080f403101051120b064102c5034810740c03096070b50342c45141900307981e0000d1000f4107085104030340400101c95200400342c10420b0003004030921034031340020086a805160340032508290f83c0000180c1d9181010302140748 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 908388381 1250 908387131 908387167
    0xc210f0c0c04061e090f0b270106230f09060a030b0418080a110115030b1501080115030e150405060601110c1c02060c0f061f0605030109050411090a02 66
    0x41c512a075404c00c580c02011000c90b140d424800d02480c05d5460b0010b00009940b680000d098400c010101c80c440c0d4440e409054450070701d00712800450410a00024400e40100c42c100c2c00500a01003a010910080416403115007200910b6108a0030801503540103694100c010049511075407000127400b51030100707000c12100d40311000c240f111000c1030000d010401880a440402209107480f43c4500801c6800300c1c05040d401c02c1d100303a207002500c0302004100c00c100c900c80c800d0810000312410141c0d0310004460b540420300c580d00301120014003040080c0e200e80c02000300800768004846020100c0c17140c03407502e44c1003201c0c20744140c0c000906202c01da60f0f11104880c00514400c0040c54800ca151000030011009a010a5031314040c000c4c4010031511440700b540c0240013400140e40180300120000c64481804960b240019001d415100290340748140c694010344107603030346050450b0700b003480700e500a080143c0203661580c03418140c1c403140d568442e4490b20402c0240e8016032110724601024010795 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 908389631 1250 908388381 908388389
    0x3050d060306020f030420010e190305030f0703020f0a0b0705070819170604050f060f0409020d0f030f05030405030a052a1006060311250f0f020909030c210f0c0c0406 73
    0x4c8950000507071581e4000c01900c2100270031030314502d102602c12814119556031381d0006000e40070108a031045608214098011980a0740a960303126405840454495440a800500300410725003c01c0702144540041c1042c0c600c2030015503d81010100c110850a490010500008485120440c2c010a041100301d80050050300c0901c46800c0022a14071341e0400200054000c1010f080346803000c0c0e4640d0000703c01d8a07000740804680301b03400c1c10300c1c0b000002582c1054000c40c0040000c4010640310310200c0b403140d50001c014504081c1d84120485850f48110110549095000c042807948900400321403680898203000f070080c9500c241d0402c05480703441d400082031524060310b200d03400c0311140407101c07510500701c07a1807607006064a00e18000c0350121400b03400c0441e241c10340020407405038040c040c124000c5941c01036030382ea0103100f10b40d01c1c400d40010b581d07a504043c0f211402c4480c18442900030320f091028a504200020756004501d41114021041d2035101500c501d103a81418440c00000e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 908390881 1250 908389631 908389673
    0x3061311030412110606040c0207091a03060610050304062d0c020f0706140d09080708090901091b030504140a08040f0f050303032a0a0e0306070f0c03050d060306020f0304 75
    0x4038140413480e488110003015580030316140e40c80d101c0200d20901c1410098400c00c141084622411020102c0740850355200702c1c001d200341030100300c5524110022002081c4180e80b01c0d46903607036030394400000c1c08030350110070b882c02d000005004004a0b0450706130740c107005078100040d020300f02c600c0086c40d01d604150015540c2d00942d0060101c01e80c00b00c50400c801d1030358035503595201d03c0c03088171400501a45202070250400810342004005011000f8411548112035200a0781d8031050303100d003115011100104528040c14280c1420b80c001d4000d16070141c02800b00d4030001c0524a4650f0420703100078000c6541440c002814404100c1c4150301c1c902030070303601903558040c0b8208004250f6910011b080f84403000030048100c1c0698902c050750540022320b00340c40d03e482e240600c070003034031110962a01c0c911074020300d000100200d200c0d2401038462245585e9100d2900b0403503c007500c542d4005030080b5600b40c1c4442022000c01d00c07030b000424440181c81111550b9280c6401c003209800400d458417604 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 908392131 1250 908390881 908390897
    0x501060906120609080d0509031e04120b0a0603051e1c0c140a0c030c061d03070b0a1205070c032706210608010501050406080105010e0c03061311030412 67
    0x40900d248602c2035103107501860003d80505203080054407030180f400d651101c40d04203020004400400300103400d01001e0701701c0101c074000620200030640c1c02103006201401d150b403036004000c11800903070078ad00503407004000200103440381c03900c508220b011100013240344d8415408040161003000740c0704c501c000045070705e80c6400a081d001000c814007100003404144940c2c0240c1d8801e00c0c1402451000fa5011300840c41c4950b607440c00101005181c8503803c0410a121411150318840000340c01740514001c0107000c240e4107243d07604059821002c40c0004000d0024000d14030510940f04180c024209504e814030711200c0b500c1d004200c12005800802d15442c510170908071100004181401d803500340c00c1004007c01c0850540112105401c40c1c01c1c0d5590806000041c810300c1944404c1c165003080d9018004191150300701420313a5401e100d00301c4030404602c0012112035600d000b45800c50030050404121003001d80302d202c19141044a0135040c0000001404100954070443e5042d0300400d044c2091 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 908393381 1250 908392131 908392139
    0x1120b01210501051525022e0905030a030e040c0521040c0501180e04170304030e010f050a0e0d02041e02090f010305040f17190507051b0307031709060c0a0501060906 73
    0x1400000c00007590f182c029583d1b049104568410340500c05280103685421190141c2401705584100f408190401003592080040340d681070106046072003d805445580060004009100c000c01c050100002080340c24004490100c244002d0003040c10310003c03a006007400c00b401c0c248000314031039100505001481b900700e00a40380303031441e0b20101c500784680045030356500d00781403100009200d46802c1070280001000205a04030f4090b5400743c03400c4e603403c405d100c034594098403144505030540003c101d103842e04118514014020130305d140d1000d8404102080300c0054000c25558a400b200b0402e40c022071200503500703140503138612515091906002509194546102001d14103201600c03000311004081800700f00201181d0f0010640c2007601049201440014a02c0d000704200701e80c24040c0300010792400c0300d9013280b02e41144004018003212440c603540c200d01c10100200d2101856800e0080308240c3c0d848401812802e00448003030300124026207003850854260380c2160013443d1810700144 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 908394631 1250 908393381 908393407
    0x506010504021c0902010504050d030519090f0b090d02031e0c0f0904060e0c0909070513020f0307180b0d06031401091e0807120915080601120b012105010515 69
    0x21643d9482160000306040c1c42c4c00101e50a104075007040f900309050444071410164401c0c0242690300d80c400081078101950762045400201600c16400d100040010034084140380c207000305449200200074074560354480d400709080168a00075000d180300d2080807460007140c24410b200742280100c40b0100074034103080004007810b0380540068102581c550180e48005002c00c04103010007002002d0610a2914461442c0d660079203000301800b9031440520069811094001e03102881e03003031000142555580c010480d91469414403144a4805503100007940600700e10050151801680012075442d045090903d650216152110300503031510000002013490003c0f1036242034102941440f080210b0f00b09000c00340920003020700404080554a000a50048021030465178030010460314042c0f003050588500390704540590214500205080c8080250761010001d824141040703141d00b446407801c107400500380d40b071400155a03100014030071b500e0101208404280d0142d51186044030340c0c0019 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 908395881 1250 908394631 908394667
    0x70c06050f041503180503180d02030312060303040f03201021021209070312050a090605090a03060c0804030201060510090909170a020109020f18190e0118050601050402 74
    0xc0f010f0001d00803c0800d200d00c20780014403502403140045849204501345152241d000152282d20040300300c1c0030740b245c2d00f0540f8046d000e2540080c0030b942440846005882403680051070664580000c21020031360a8100480703034040c40c001e500c0846c0340040c0004034449206c1c01488907110743d9003054403100450b03000586a00b0303040c5281c032503010441c000c0360340340180c000c00c0340043e44800c0300010008007041c0061410b04881c000c17404000303185006101529648220403034400041c05024003440014050001885002c50107408044c0c560303542c0c0c59290455045408640004140c0c0d014007082c95824007884001e0b203400c40710220340014247c00580000b0380c42c818850707640e46900c800000e0dc40786003846034040f0802600d980c0d4404803114003e0007009105401c0784140c1c01c42c0e01e2100700381000e41c1c0724103900503100044003003a15070041c60210010440283c60304c1d03e40700c01640f0117100f800c0c0242c01c1d942030030880044560703c4d146855810b10005800880c025031061110103038201210801d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 908397131 1250 908395881 908395889
    0x140106091518090e010203091204030b010b03090a0b0411010215012106091406041403040612020c0106030507060207032918070b03100513060b09060924070c06050f04 73
    0x10078060900322001800ca40c040c1940a000181d140003030f034040c4c2000640086104059160a0f80c240c001c103000a0820341c055400060f05001200f0010302030b90301c1c00070003503402c51581d104484a4503034580e11400100c104072000c681e160140345400301d25507010020342030340003015524010158141030031100c1408103e0003a1403071181c6248200180b00f0564480380c0c98a8004521610003680403080320307502e083c00d441c103d411802544510030618004003e0301d0946800e80d0b1610317080c00005400383ccc06908103a80440441d582c40c5000070004d0310810a101c001e00017500501003142c41c508101200002e1032400c01c14044c0d8000090304030030343c0100c44c590b1002c0c0740c1c1d07100d4824040e1140081c1c504411a0803034110040000184024036800d070300d814040712412108080441740d0781c040748066031a14440c095281900b40314228840c80c100d0081d0280310f40250400c00049012850003035003600b03400114840c2000019024140000e280c1c105018180505001d032400189c009003440f03510451107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 908398381 1250 908397131 908397137
    0x210601020607081302060d05010b0406021002070f060506011101060f060e06070f02060708120f0414160b03060d0807120f0c0807020907090e090714010c0809120a02030d02011401060915 81
    0x1360000c00c55a0f44d8058500407070414008000b2581c4a0041d2040307075000303000d000054801c102200300c03d0000d42c000c5640e0650b1006030f074868020f2551300c1d070028001c094490f905106400900d20741003d004d209400052011a0102d10510b140c0000944030104042440f80a5401000440c01107040d000c3d030010710319815107116540b81401d0401c03120701d01038243c00403000446441030104900c1c2989450780901c1c0a00581850741842c3e00403c0e030350381d200d0a03a80308600880310342040700d01150b030301035540114080d00004403170503541c1e940284c42d07001755401c071410482d0755030340c2610b0307688820b0440100004c0e00b010b804128168641001d54012540001e21030803801c0700041030b003841443e60b0320007480310b22103004003800c1850256403074075854001c80d0030031414401100721941c802c40d050b9007a9500708150b10710b000013100600c181001a44507090407481417200c1e10006031000c0201d2919072031994000242c0c00940b800d46000c800c4103038000001c01188401c00d03c0f036061422040901a00e5a003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 908399631 1250 908398381 908398411
    0x1203090206040b0d1119020d080403020d03050c300c04030507150e15091f0504060309171b01050f06010807122414090c0403121421060102060708 64
    0x42c036281c02400c0d51100210f1721940104201d0640300311200381803d90b40707054003076582a84590318212011001180d000e0010380c1701202510202c0c0c002d03171106170080c800219088c1361854056600e600a5501c44400b0a982d01188080f40e09212105420760003500700710206c0e103050b11750303100e50750760b03450600030407100001210415400c503000d860000b02c3e100c0068a0515980c14885281c50300790441b13031185001c0c1104802c004504105120310245540c61030301d9450409040801c00c400400c40800200c803454031351540c41c5903070300211014003d100b6440103040305071030000c02c903a404e540c400742400940451880a21200b80e030801c441e80d9104000b89412003420004450110241c4600751042d03070103a2045210700c604401c04c11402c1d05503403440d0800c625040014040c0440070404440d04110503005100520020b0320a1558681a16441c90b10030309101080c4040700f0141d00c44903451180d40c540d000c41c0103034001480312040d030000d024000b825592600000c05400740e030008040701a0041d240c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 908400881 1250 908399631 908399647
    0x1501050d0b22020306071d0904021f110102040b041a09030304060507050c0a0605030a060e010308030109150b0a0216090902090a0c2601080606090108031c020c0313031203090206040b 80
    0x501c100c50342c1503001000c0310f84038100a0006085000a07080d40302088502120a91183c05d00313124a40c021540074004034010f4560300300203500a0380081c0c0340720402035010181401038400b4005070015196112905541c2c80c500380c050801d11a031450000346021050008a600c3c5d41e02106540c1103500310b0a00030727911102454041d050030034104049601015101b0701059080e40316001d54895888602c04004407500c0c0e00e10f10303823602c030240310080c4a80820001409a00700c80d8000d51000460861829103d548036800343c1c100b03801024800005a01c02d84030070310203502ca40310240040c14241c4080281c0071581d000b0651a120042141040f40d4840d00c0c54902d0070312483e000b00919803074a04104a900c410806010440030a2146c4134040c8a8400458224600a4206d9040f60340306402949040c0301c0d01091084603141d038a80d500b10550074480340340010741c01e100401d0686038100c60456043e0440c9040c600b44120f000f002800c0514006048006071100e00c102ca003a03c00860031284c4074100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 908402131 1250 908400881 908400931
    0x10f0f06080405150402130207030c0657121407120c140a03020702030607021c0e010216180f020c0706030209041805060f0c0f09010e0d12021501050d0b 67
    0x640d540182509200041e90070a155000d0344070080d481c42a002070040400c84491502c61454944181160f801848400303440dd0031000700b034650413000b80342a581281c041d0503000c48034002804d1908081001c00d04040c0f9860164410403124072034841031010503013030680340182184018000343c0080303503a9181089000c1d02862035400707400803a01c03541d640ca1100c140010081d4002e182d0482c064401e03140881c88007400403e00b91881c6031560500c51006490600031207a2041804c01c246c1580a403040c08072045502140b0500942050040322b4541c05181c04039008403031182d048a20b43c1803051080e007400450203e603100807110145005a11003c001000400414111100b10b5034610142c0c000c0040040100301c10784505018002c4145a940d446201041407051400d080301c0d0a00410030000d0179030007024034000c3c0c45005000360320800b80d91307541e084d0b101100d0f01509026902c008164282c14088198007030142006844002c218111582c4142648402600035640700c8242c107152071034810 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 908403381 1250 908402131 908402149
    0x1202121002031f050a050306040206160b250201060807051917010b03150112020d03031407050d0b03030f030109020307110d17070e0a050f0d0605010f0f06080405150402 74
    0x80c0a6600319500d007003022030204006003400036000140e81c10000001e075071030400420700407194083e020309001da6840c0e08010345603005013000c540b01b140e0000c952002c80c3c1c5c2014010320415a51034003000380c0703040140ca10710080300320140c801103a040a005001255000c9055002ca03501070b24010307110b811015000070407030035903000030303810000240042140800540201c0ba02c2d240903010f6032101101244a000c2c2803200340035404d403d080910a4000600380b00102c5400c60340039113400108001d0703035420603041900988032080041c0d00070441c1340c110521442107110030103048008501e0701c001482c00c0c0685000510580d00c01035400320015030322500400e10000b41d104410150340510615050243c800d0164051480b64403542c040040c0260f8000c884081d40514010300301f007242c502c0c00c002c000301d02d02040b9001e0f42000c40c01000b100080d0301800303003e0190480c80c8200300c02d81d044c4001c1003484c00d1030740d0224003044100001c1c04040340340030406003095040c03422001c407560303502e0021442d524 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 908404631 1250 908403381 908403403
    0x30a0c02041d012c061012061b1205060a0305100203091c021501090b22060b0d050f060d0803011406070212100e010605011202030a0f020a020d120501120212 69
    0x5420040f0341d680708580072403810071305404001218404008003545a5484404881004810345001800e00602100e885100310b05445880e001c98400300486100d2403001510481d08041542c10b00701810f54403450159541c041d1054030140b1840749076071106540d800d20300c00030342074017940000450a0000c040c000e105c80c2d130b41c4006030920081e41d0080020764611000c00014009940040082810385040c0a104000c0c2c0000388402d0803003c058141d48440c01110000f040300300e5880000052708155000641b841c802c2681002030f00e0300c0c050b0042601200020402c520500d5407080c038800184054003524151800241c4e6030f1f54014004001c90b00a115040f4041d5100211080203404040c000414040c0c20701d051000340404e900c0c9107415800d81360a4000c85009c5030b4010284100c0944641c0515440300800b10041607040d00003030341b00103d13400b003420080141c0003c0c40c000c1c40c0340d4000034010100d41d0410000c04c0350358905a55000010b80c1154003c1c03050441d04002441d105040200400030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 908405881 1250 908404631 908404633
    0xc050d0b040e1c1715091009060906050301060b13150e1c03030e12030703020f07020406080102120709150f0c050106080f0c01050f030703050c0f03012303030a0c02041d 74
    0x40300c100340c08811103c1800d002840041c0b14151450780e0381c06400b1001c3d0203040000c0903201c0c0d800501c1c00b08010204000c251074100d8140003400110f503540e50084000400b80134000003034440c1400c09060944409402441080d4010084944224401540d9034119090050001208580030390225020180490303059030001c0b9100f41d03003280c910b914070303030340b40051007a01c081014145141005407680c003c5400d034140142c003400080c0d0070303070b001340c0082003540000004103103400b14603070000b421036400d6089404c190394017081141c030b00f50750204020b403c940709042c000d41c0701d4500a21040200f40003890b001c01c1064102044c2d24247c0108010100d0581c030a00074400141ca4940341035440702030034040d203000d20440908107030950042d02216074000040c5d4240e499070381ea4900540c05440080d0a0904480e800c01c68182c0c03c4491070083c40c003800805900030b4021140c2181545844c40030811180709030010801e902040e500000e01400740b96054401082c851080440d055115404480442003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 908407131 1250 908405881 908405893
    0x11401180803180a170a03030c170405031213050c060702041116051207030c1e050a06050106080601090e07030b0f0d11120303130b1015030f0e010c050d0b040e 70
    0xf65688605104440c0e0205844189110380d1785e12050070b1080c4010703040c0103a90000b08901020030b111703400c1205000f05509202c00c181c840d4048042e00c1c2542102c0c180c82540011416408191114250302e070404aa403205c190342c0c8907030340c80e2240c90b00088a0aa071295800194280840d12030fa00100d4903440e0440346640c458035000c026501080c90480211401d0117850350055007003030104165907065407d43d07100000200d04e0759a412911034800030703000704900f454694100040303080206204c024450324010800d0f500d08400a0180c3c0005003916042c0301403140c0c140002041c0d5182c080c4d01c80803d150210b03003c800d5a000c18101070300e036142203400402125400051000c042c84120714410b05a84200c280051421034507120301059400c450b203c0751900b01900800c1da40b2500307580010409050400b6141d0703c00360310100c911381030701c8040440e1b21203510010705402c911a106001426100034004d0750741c0440010a0b0344142100381e10350030b51300c041c450440e84440e03000d0302000e19000100e4003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 908408381 1250 908407131 908407147
    0xb03151309060b030316080309030c120a020f07060c080901030902060f0702130504050d0f110307062f19090e0108011e09050c040f0b0a0308030703060b03011401180803 74
    0x60712811005550381420148403aa440c00d00000303c1c1c41c01d00d101e0400b02901d001d00e5959003d90781c80a0108203a40c8018081401241c4007400402040d44481c9003080e520112003102900380321100040200320b4100741c07420000a078002d030010751500e1380710040f25a10706d0b030900160000d2144103000b940004011502c07a550000b848014608980201c03081041240c0d0050150160740d000c850003000c0b608256103003150107000710078280c134400d4242001c9130f2140fa0801c00c0741c559002034000390b804075150b020414144807031001581c1b40c241003c0a007149035540d21550089842216581607008424003004010984280b0901c4040d01c4c00c84910b21855079621215406440d21051101c50341020b9220f030342d42d401302d611400c2c0396903074018043d000d000d65110400c00204051380301003000c50741b903c804d80130650f900101d40340510b206d011803e80300e0511030801802c580790742c0c00c07008903100c0800c010702008420f04841d5190903000d29204640f010034060665190341554440d0419100c0420b40c0c0d5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 908409631 1250 908408381 908408419
    0xf1d06070f050d0c2d02010e01110409050903040308030f06090c1914130e06030c06070b070f0512040f0b0c09090c03040f0c063903030b030c0a09050a05130b010b0315 73
    0x2002c0185e8a80c001d001d07403a8040c05550894242802804a580081204200209071034009035800300c0080c041e281803994903100d05c405503004803826042680c600042100d82c0c58100e44040d04800000700084c1400304280c45591900034003424501131040b503880702d403a0358510900701d40c0e928448021200e00030b541e526001e2241d031020760b0000c4c031030f005101c900000c0d800c100e400c1d2148940c0103201074070142c07910042a6440040c4410346010041304104147e0006a80c242c0c4c203024034843d466019040b285800c15405800002e4058028940c0401c00641103685041d6020382100740c1d400003d035651698504048840b1861200401121510000245080d0804400d2054028412020640007032900f0009481c5c409240010f003641084100d40010903c641c2c4000308821000e0111510401c1010029400110a90180b12619260010082000301c507000d04c580050001c4150040c013205a610b81507007800501419608a0003c40010315140c448502c0034295100640480513180b00b0545903 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 908410881 1250 908409631 908409707
    0x20d1412090301110a020709020a0201020d0e0a060609020c1e0c0a08150609070f0e0316260105040b13031b03050406110f0316060f1d06070f050d0c 65
    0x105220b9441d11305411001c03485001203a161107603c0c0d000d40045401c0040b2107000350065910360f01150340c00d20030b030207403418181f04200070004101c6c01018810028074007402950801d800140c9a180180030400420800003044003003480d046100d80c00300c0004101480c640b000c01c400d4140d00200303101d0f000902172404140f008100d0310400b003207002d582da114240b1400d03e1b41528080b002440001603501501d2081594500c81c0e200241580c250040c0180c0102034102c050300002c0440074504502c1d03071040c90280882e0008170603140240f01501c0c05880704802c0301c07001007410782019000006031041500c030324060b02030490741c0020b9a0f06c50b0780c2818018000c1e08640112000700d410010100359040f000180e00418000f038070001c61402c07a503c003034020f104105d03190031100c3c0c0c0d881d48200b05000c641809036400341414516019142404551103d00d480d2019140d0400e0050f400320017405e950b840b00c200e17040e2086018000c10304410200d030480b20b480c0e0090003240c100786010700717070080c4103540528 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 908412131 1250 908410881 908410897
    0xd03050d06090912081611030d0906021b0a110f0105040803030c041502061b0d020409020408060405010b01090308030406150801090b07031d0303060d0303110c101413020d1412 77
    0x1312401071034588160744801d801c1c0c03551542111085400180f0070311031580c400e1528040000e803810001400300c20000d5442d120801c03240b1340d8002c41c0401500003031403a440c02600c0400001e01580a594656850102c0c42154242c0034009051340940c4076400784046400500c541421642d40746070a4229000070f4109001d00307100001808451580c4500c00640303031b80204080d081c202420302000c4003080c0254454503418100640a12001400c24030b50700c041c00c000c11030310000d4402440c080ca0413a085811001e07410f818000715040c1400811050b4041c0c9600c154041c000059841000a0340810b1407100c0e84034150940c20401081d08000c6001e49040c002d50b90307a2414401480344428003040803040800c1c0340c0300d60380107100213400c52500051589019000307081c00502090010724000c0c06600207040e108465100390b6442400552600c24000411003840c210704050401001c00046e40641d00000307403040d04c0021048040c0818403203203202c290641c2080f62160490070b2460001c07074000c584 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 908413381 1250 908412131 908412143
    0x10c020709062102190306090c060201140a0905010f020729070c06020906120c12010b130510021002031306050a1103040b13052a010c050c0d03050d060909 68
    0x20300203034100761800780c9000c0c1c1d00301200000014082d0035600c0e12049103a001a81e100300000b009441031080560341034043d40c0100e802140300c420350300b40f05401c00c45c2c0340c3c056070031a071500a140ca0716803410380440e50485154040401d140800b41004c138007500c0c610350605103403840002c0c81402c00185103000425480d43c452001075240e02045c406080d00f01c100c5101d0040380c0020001800100b80c1e90003082190390061142e802d0600d0207048103203a050455000300035880c00140c0c0881941c1d02a0ac0c140148044c01d4440d1400d000390f00c1d03508421001d44901409107000c000b06c1190a4002d01c81d640c40410058021901e9140007002c2d01842c002555041d1070070b078a403074003060303950b019401514410045200c400d46503072141c0c1c0c1d40e6080020002c001400103080c86442c2d10000300c003031120b0140c2d0007504c08a50045c8185020b13201d8200345003c009030500c000101c3c12000500046100d8030150390890303108080840e182000c0d50103104551200790402c0c6409004125112b140c1d001c5410180260 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 908414631 1250 908413381 908413393
    0x1350601030c0e0303090402130b0f03010611012c15070807090902120f04050a0f050105040212011e020a030e060c1902190b04020402071203091419140a14010c02 71
    0xa5043d90b070780a82080464054000300500951410b00d0780091031ba80481100d203565265a41c00040d8094000103115004480c000004102071613000a607000c158000000800100300d09801c0d14140c604400c6907035140040780000d2003800841440858054510003642c103500b440c24070001090240304607404800328a0401020405e0103491094030680e00544524a0a54071055007107801d44100400c01c40790381c450381c5110b0000682e41e620004034148118008525410b240c4100a071001d58031031345d0925a8500715800c030404650180c010641070300742d02c0040e9641c039000401c07130203805000c01c45981d80c8600f00500c6114a1440002d08070b500011b400d07605082080002280c132541103000c080642c2c0c000c41c01d080302050703d450300b2940061004200500e04031044e9075003d00504031805010100350b5888014081c00819002944ea491506003c1c1c80f46032001e0f03c20300a0209419000b40c54410f40c40c1c05502042c0c1c003000358805498116843d24029134140388810b02074040003020b400140651 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 908415881 1250 908414631 908414651
    0x1d0f0c19020f101a0f030703120201021e0a020c010e04060f080604060f0e030406141204031d150d090f05121305150a03020904140a150b09030c0135060103 68
    0x16125030480c140b00d2040718880144900f01704100205d2040d185a8075002e010000800141d114800c580445aa82c00158503140203055100b1148440c044031840f00c4420401000c803c0e034049511000d010090030114501007100700490000c0c2003941004420341940200461116000500184554415402480603002c000c0c81e03001600d00c0c0704208407030b0b580300b4003061041a010705420b140007c00c00f04c40078101079000f074030410b150038142c2e0142e0210304240072400c40c07028548070400c8086001e4801c556a070001c80f0138050030380300d644060000269036072101c50030050f1300c130944510301e5001780485e4054003441030070100c664881c0d4000094a0b40042c3c0000ba1810120400004090f08030340c85410301c20200401c0d80698420000181d00c69a0b442040f01c7e0000c01c1903c581c0114515100010710b801d0a1074480060005500032104d41441403004000c56074001540005090003841c1c0021103c01803c1c0255126402550090071120750000c400b60345e82025841c94030410090b60188224028 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 908417131 1250 908415881 908415913
    0x804271a031209150d020c031602100810060c0c0b03090c09070c05070e090c0a0902040611010203010b040323060a020a0e18012616050108011d0f0c19020f 68
    0x1003c5a09812071641c0c40310340584503061340074002d00703801d4140151800e5a00941182158029558008c0780809205001c0550610041c000100d410078241254203041c50007494401140b103114201c100f02143c0002d0040040c0700300803c00801c590003540c0c0c0c8a0511024032604d07408400503003405204d54800040103944a81805410290008040c2080d1801c18509266a820007096544035100302c00388807031913455000d03400008004041006071581d080240c024406243e19680d040f02d40c0c01400140480e1180380d0031107080326407041180e154a15605050030880041d440c60003420b01480302081540b040030b070002c1620b03846590f40c3c030b200c401206040002c00c0642004071802106001d0041c030880344c4500e60811040c003c501c80c0c202c80b01d4854019458040c988d5800c1c0042d48840d070080102d5604050b0302400340c0401c02d0604100320030740080540200009100b0520008404c01281d040821101118800400064000103085242c0c6c0040d688591680005c0c2442c481c80c030407081d002070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 908418381 1250 908417131 908417137
    0x31b010305091b09041a0f06120c03190f08070606080705090f0a09060b0a120606080a05030d05040809040603240b10030b0303092806020304030804271a0312 69
    0x69200f400e10500e88000c0248014100700034400c848103088200c01100103080c40010034855000c09000d0300b8203280c03600c103106441000d1450002d13154030150b20012160340110306014499052000c580b20b16066062601d200000640c000d0150a0001600024000150030075401d84401c0c100311504665194203204100b0021681c42070300032186004100c1d040091340190140b107005400104214030720900240301c001860784120340024520300080700300710440c000d0400800264001d03040c040200d0319915100c0c4100c0c00a5001e407691800040d0800c1808403d440c903540c4040d000f00609030300c1c2d01e00024001d03160400455086d00d940d011750151035090041c50749801e4090b0000d04e540c1c0c42010150003a20300e016159074903000a01ca0100c1e55100c0046035540303003c465001508600b00c40b8424058810241c0050f03086410030441800410b004000722402c550301401c410302e100701400c0f0081d221901d00e9481c0c410050a040f0140442c10081340381c1ca51030034044007952038032005401e90709001c0c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 908419631 1250 908418381 908418403
    0x40f0e01180b0f10020d080f1527070906020615060d20070f02011404080a150e0111090307290304030c061404110405040b15030c031b01030509 63
    0x800c48480c44900c15500c0d088500304190140c010b1500c48a8007001a010445284644c80140e001001c4240300c507900c21001500f19501c10b9101078203040002c041905140440c043d85c0c0034503040c89a0720074017080c4034184c0740e4940c01c0101034101414480002410581107102c0c143c0188134040200e00a0084c100c0e210040c08001002e50745094029140c0f40040c06c2e8850904240501486419911399560780003060124400c04911080040c244009002044d030400040032611061100707100940d000914801e4440e0441c00c10300e942c1460004920103441100161401c55007000c10404500800b180509003224040707081c0e0725815151075146520542d070b1802e82407001448280300014030368440085030403501a00d80201100b80344c0e03c441050f01d54900581840c460006c00b000103011110034001601481210184400e040c140c0322a1440138015204000000407001400159a0108120b4005040140c01d40300c0004000c0004e40703003415007442590220741480c001039142c4034089600701c180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 908420881 1250 908419631 908419649
    0x5120310060f0906030f09020306130501050f04080304110f030d0c0b0603012c0304031a0a110909160509190e0901061217040906140f09010f0303080426040f0e01 71
    0x4641352103000c501070f00c1020031901d182a42c0302d20200150b1420f00c0740520a10000242101c02c0350640341090841d43d00420b951048030480051000107144001181d80080e040954003400a00c00c9000030f42c4c081c04940390710b070705105c0e03501030140260b00120001c3e0090300401203000e5554a400c02c0c9404e85040140051124003070fa809058506c07000440c81194500c000104d0b401d282c2ca950711044541e04140d19540240c00d410100548021140a00d003141c9503404619801c01e4911008190305d004007408110181d040c0750380240c1c00c240304a0503103e000c4801014a40340f0030800b005000c450a541c040c40918000060020b8001a01409198111000c0144151304d00030307030781ca4072001c1407822050071000a00800c0001000c10b0b0b07901801004d8941c0c034040c01c070341c40fa2507010415030b9205081500d0061030540010050300000d0b2955000b201c0c0c041c242001c40e03030f03150301e049000e00507052207048040100265083c000020b80c4040c00c181c030b0441094650107500ca503504110307200d00340304604075 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 908422131 1250 908420881 908420897
    0x41a1305040813030c0e09070e0606211f05060c07030803100f0314150402061b15012603040803030c180a0e07090b03060904061805120310060f 63
    0x1201955804154031600400c555410030040b90800300702c0320030952044e1a0b40728142024080a100112a0364010b400071000340815443d00154200c0444000c044620400d804182c90f01e4008080c1c0e4841e000100e400001046460003859141e66032100041403041d01040b84400b2809052800488a0ba0b01081008046075891681c900c059940010201c4000c400c12400c0001e0140c40e80032080065480340d50811003d20303080a035145024222003d1107080401403045c0400341e00d40104803800301c41c948480d03408a0340140c980340c2c5002c1c00c0d000842801d2001400000341250b00401c1b9580c41500310032030007040a42100b00b203030344e405a8003404806410030000714400880c540010500d080d9903120880d2070b030003450001183e80a6580c00080321500398070410840e40c3d84101010040c2015204a509608080d00030540d054001040100416501c03ca241c055031301152140121980c40011030300c4211117041d94103d503070029900400480d5017404003003000c90189182c100140c3c11580d410f50 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 908423381 1250 908422131 908422159
    0xc0c17070201110304120b06060304020f06131e14010518012f010b0102010b1008010b210c19090602211c051501020705100c080d140402041a 62
    0x265110000403414000d41d001218015141800a0401050750000d440300c0f05400382060310791309000038407075845241d00b0810400169105c02c1c3d40000000151290340d2103450000502c0000c20300e64110000ca03190102940d43c40000b141c6819055551001212255001000c0150b80d2401851000d180c440003003a0a42160f5124100e8094205c5450000b0000340c80368040e0000141b00090310746255945980c580001541c090003000d8045406442c21601039505c45402840007006019000d00108009603000501d00c001000161600d04a0080c2e1907c0c20444040201944510231000b00078103003150302503400c1c0c0101e540004458454000c3c001440d4000b92f0071001e101151544514208140000315942d01102a6440c054881100000d21402c2c04250340c0005041500f0080c110b40c00b0907403c4c0201e80f00c6840f580b02d04201400d250652900a2414034182e00506092501d0701d880c0441240c4900c05840c030b090b0080e07000b9a41040341d204400b03011091500f517907081607003064034400105 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 908424631 1250 908423381 908423423
    0x605070b04060c1205090a0606150c03031d030c0f0706080c0901031d011b0207050a1d070311030f040b13050627070609030b010807060e040e032b0c0c 66
    0x5103200840b4501040100560411300f4102c420541e034640d0707280d100044e09010880c4e2842080040d0100d4800714007500b900039001003445040b002d0050415480d00d26034001c8000c20700390303628a072803240c0507a42c990601d90103041d5100402902d1070250710642000103030ba1030003200f44034003c0340300d642a10310300300d2000010b4001d040c0810603a410b50407180f400d038100100a201d0300351612a02c02e84021351016202e8000c0c40c040282e0001c51045003180401c01036558883c0b00c411140e501c1c0c1507a00383c2c1d992086400c0c1d0081c181d40384002c40214002007040382400f150f0b00c4c83e81c4541e100300707000c010a03241c00100c00c0900540d00c9004015a101501040400030161443d80720106103201070612403500c880e030350342402100d900400114a0911041c020440c1c0b03131941501610101c0c0007041028a80a030082050382e02643d41409665580d40d500c0d021041881241d164044011500594105200c0108840200c1e60028181903180181c11400c0c1403107400440e094036009017407003d064903004c030743c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 908425881 1250 908424631 908424641
    0xf050d02281128050a090203090703020904020a08030409060501030c1d130e03040b18010c032114280605180916121509030c1704050604080a06060605070b0406 70
    0xd240c0c00f07060440d4072405840104007240301c14440303c400004540c504004d00c15050416048041c5030b0380103004000c0b8404001501c0030840e901102c4000c0ca507241d60000c140443c51980100c0000d0000007070106030011305403c00d41c1160381c2070b80d041150440342c520440348240c3c01241c00d100017550a14040451500700401203440c907000c28002083c3d1040300c4200c5ca19442940043c841070804100341d881851000040c202040007800c004040381c0007030754014142c08541d040c084603400800b081c0303c402c803a80d07480b80584010004180700542020700d00300030006400501070204400004143d0f2482c0d010380605c00480e00042d103007407150b41c01ca420018085c1c000402100c42c82c411101c0203458201000d1569009002104424034a24110300344450403a518030b4003142c4541c14403102000095000c004c0f035292070740062010460080255104102c3d1050790b203c1588000c012034007003260140807601c04c1d03099109440030085a560360b50250380c0c0c0c0c05580005000c81800000081c04a102d41d046 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 908427131 1250 908425881 908425913
    0x1031505070e0301021605011508060f07030b040e0c1306290708070b1905071d01020a12260f13060b0a0b190306030819020a0f050d0228 60
    0x1ca008482e8030b0000c03e08a8100e1071042e0005a03030006600240003080c40f4007150080c0d00744081550034205814030f0b07907900d030282c0306004001c0b04800051ba031522035402036041c044018804c1c42601a404140c070f59039a4203149044c4034030f035804861440300c800d40c4500000c8600007400701c0032881e5840d0000f942d200c224110815101c408200d02c1000600981c01012103600c40d4000d0000b0782840681c5106500c030058005800078a0401031000154010031180105a102111001c4d90351031040101d01301400440024044c15035803030100e88031a0801c0c014450040d902140502c142d40c5034200c0c1171903100c02e44d41d1071a000801c2e030100c0c40c640e140c0c1e03061481d640d02604004c18083d048402151145075107901c20001c92070003050382002d142c2010218070341c0100610b030901500c1d085456003031803407084046e089c000ca43d860407500d0a150091283c508090f420002000d0082054105a900c0300348400c010700c018007500c0c42003c1542c203058010320501c40a50848041a0a030baa0341625280500700 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 908428381 1250 908427131 908427137
    0x40501111f180f060c090801060302060d090f0501050115020d091203080403020a0b0a020d0b030a05070b0c0c04051f0503070609181d150c07150f0e0d080405150103150507 75
    0x2c5039404101001c000c03c522904c143d4001500d6000004024400c1600340c1010700aa410401d081000d80d450009503451803290020004c0c2500341342c40c003d600303503140e118000c00650806000260740c00700c0e508182c00040c055000d6034504400800122400354281c090030401d43e03002184280401e00c24021140e1152103801144c00030400c0fa142c0d003002c407a08032154503055400240c14203680c9050f0041c110710b5602680104409403496840c0d9480da050f41c002e8640e2010082004a1042003c0042c07050065016008100c1400e107003c08403900b8860800c0f4680400b0380d104000303403908001070510203c401c00e0391006a0141080d28400c4080035001138440c00d03d854001d12520b6960400f111401c1c0c0c40203100400070001802044070001100508c08402c00501f8881038000c1205598010580d001864000452042c5500200018103d00c01c0c2110b4600c41d0109466002d60048001c82c0224003a01c21121186124060a04a01401d000003415600c8603070010170701d00d02c00d17081143c010703d00342 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 908429631 1250 908428381 908428421
    0x50d02180a093008090d1101060914060913020306011e0f080c09010e240d0b070c0c150c0206180306090a142d01020909010b040501111f 60
    0x148a0862039410040501d03d00e450316448403140b102c20b0b82c180c80c0d0828041c18201c0e40d40c5448181182c03940301000c078180612200c00c0507881080029407102c3e000c0c042c078400400c00d003030983c204443c0b8130703034110b0f0160b0080c0d030b083d000f1642c101c14040da00740e8010350040007400c0c0c03a824444001c00b0300f03101144002050741c40c008086011102c0030640030103080580300070700300c00794083e0400010010603400081010034500520400c101c030144840300d120364403c1ca604203005882c002c201016441d10b000b4295114000901c180305a000d450140c4c401d020b150004103441e00da000301102100b50303003511800300340451340150040c18000d014240800041074284c2d25252550003007410300000f100c042c04070390015038812040100840441d400769806400408646905d8440140c88000030320402d0180714015400c0f104c0201c09404036482c6044c0908001c10342c0d65140c14981c0ea54005001e00c6010842824241c1755100300090203041d18031800040d40c100c0c601074920400113104401e000d031465042c1c0c0f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 908430881 1250 908429631 908429633
    0xb0a0b0a0c0204021615050402210f01050108210c0c040906021b01150906030b0a110d020d1b081009020306010e0d0b070314330d0609020a050d02180a09 67
    0x5071000d0200d030600310500c440240910b10300441c11b14a00d28070703081c40c0c0e03207060240009170300c590315030006038420181c6110908800121003441d12070603055602d255801d0000210301050049644070b059a4801400c01c080c418a05240c841c1e0b01448150161036442200e2007000703072130190800c05099004810040c58400d221342454080d074800405041c07269180c000000c1400c03e03c00b610001040149003c2025600b55982d061603420080c29241c8000d490b107103d041c40303140b60000c5801400740c0e08011590b0300498015070020b4109001c00007401d140b050955035256000e1000144540410101d0035091410140c114000350005410203040212500e4840300079110040e60740880c9000d00441940b519003034000500ba5294050300350b51443d40b04d0b00340026503403410705126554414407090300c6c403001c3e44120100e410302600da4003a40b194000b0418000c0c48402c1d03008480e00760082e5940441c090300c031420300815504540000b50000ca8000001404001c01a20a60400c084000100300d40c801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 908432131 1250 908430881 908430889
    0x50c102307060f0c081515031503070509040f030807031406011148030d0e0409120f02060705030603100209040917040905091603060b03070320040f0b0a0b0a0c02 71
    0x42c10003100819400414042c08401d02914400b42c0101221062204084107081400301e000c050127110f41402441c0700c00f1941d5500b0700036a0013800018215803084c0c03070b06081160803020380f43c0096000ca04038601240c02148a40514010365240c818a10010388a50340116032000708608044024001d4002e0340c0c4940e00010000c810810360612441d25140307840d121095031080c40c90544e08210301c448481e451a8601040d0810381501508160ba00d090300c0703c01250240c4400540101040600300b26200d80766000581c0d2101c88225600700c039840d6803880c034191002e01c0b099a5190703055004080e1030541c100d050300240000c1c88003400104c1d21484070b03a01c07001c0718510900488400b000c0031a0600190413107110325944000c0440091010220b421621610800540005448580c844111807495202003000d00c00031603000c0149000c010002c2150000954407000c014442c0382084044054241d0780d000303101c0190802089642514600201c8070341d41c0d40440260020b00c40012401d50250756 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 908433381 1250 908432131 908432141
    0x2090a110c0c1504030b06060c0109050604120815150c0c060c03042c010b030402450f15010c050f0303100611101d0307050c102307060f 60
    0x80840200321000b025030800c1070140800035201111401400200041094601155001801603e800e592040801c402c1801362010460203009031080105010401103640e140d10141440c55890145540b0362950188650807240c40f2581d102d215412082084c00baa00c000780854401241200c0d1000c41e5000441c000360400c0281480640002ca000c00030a60b0088250459820b407040103010200b02c0c0100780300804043c0101121424044009000c54a4801c4a1018440c4241b0020f103051121000109001000e0380e6800780030311282c41074240c0180c4d1048030760089080c0c4400b42c6055540440c540418801010054100004181c0d5000482c00c10300280d080780001c240555035900e060304418001c0c5541e48c0c4501c003040854181c0011641002c0f94490b00003031100004501c0003d4000300004508a011184003140800035040c01002400201e07000f400b0340989403005102c264a5064810a00e244103034130140e50b6100003138105007400c0005228152050702d0000b1040c00003641389040b0740d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 908434631 1250 908433381 908433397
    0xb03101d060a0605030c031b07051e0c0f030a0b07141c0605090103030c0b07050d18060b030a0f03030b0604170d0908190b060f100c0b0a1802090a11 65
    0x203040005011181c102040e408020748440e0800510710300703054000401d03510004040f8000000003001c40001c26015104940f81d00d904042115a0940b0302d0899a45048081c60000d002d40309591000b40c00342003144605961718801000303000345054a03103070b0000c000002080e6070200328603021006140d170a01005020b00601107c0203005249103403a8070811210035400113440386001200402c000303540003440049890f800507085c132050301ca50b0000d489600502c1040a001400c6c501e03001c00d24501a25020410b0b4080c040c144003042001e814980c030348540043c0034014050010300d0502080c0240c20804104401800652400e59a1445000041c0d6207040050443e00302d074001060003540002c02c1806030409401824410801140e085a03e0381d164500500c614511400a000f0359141c944078011000e015060000424140740e00800752140b988003218415030880c04030341d00031030768440e0b00c0c0c0e00c81072172001a0a01142c0d80030404000c000400009100c0d403600c0010041c0c0880f00050230902d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 908435881 1250 908434631 908434679
    0xc120106050a12060b0901051e1606060e04230f03030f04030f020c30010c0302190504030b060d0f12020105100b0c030301090504030c061803270b0310 66
    0x400380060010148000003070201c40071030401c0828401c170b8881070304850f100b907000d08105560b410032074800a9400c041015110440c003002c900740d030700c400102e10131302d60151291004010340c90300c1c2c4c055410884d00a0728043c0c04064526200300700f501c204c40c0003080c07188543c81241c4c09118801041c4d49981d00848002844502002c244070030580c00c265041045942800079200b5107400710b010400303403030034000d1400e42c0700c2060382041e4210400c6011a018186403200900108003000d0f800b801a602c00103034041c81004000c141c0c0d0519101d903040ea4240ea43c441c0d00c500039034454904010401e001d000b41a1603850140c0003041c00144180c603610612156900007003104c0c50f200d401c0301d10760000f6502100301124100440504102d020080720f054483c22500010310781c032103040407907422440d035100500041c603201c5c0030b00100c030b0750442410380c0030301c2a603610110400c21917440d0405698441c1040003074482030000c3c4001003a40028680c0406d0703440d6140c0c5036684d11103d4200c602d400d15100003017 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 908437131 1250 908435881 908435887
    0x8300c0d0c020f010c02010c1520030709050a060e0f061b010b01020d030e0307350d1104060f080c0906070c0512070302090103110103060b04090c02010e12070602030c12010605 77
    0x440c14001d0b01183c4a00090070481c82c2c1200e1030700060100700010500912800ca00402000c51030b403107610003541182c0e00e1484405842c0c824400c0c1901e81d00c242d46800c00b081d010140000d940c80e220107600159289036440d22140d06100f000c0c4003c4180d003400081d84850140480741c01c03402c000240031182521980081844240c1c08006802c08a100c1910b504041c140701050411040000498a5065000540040c1d00313100240203402900e40800080b440200390380c4084803c101103010b00203040c40e00008209009880e03050706118440d522498000c680c000440f00c01450180c0b0804d41c0c4190b0f209130f410b10b040003010028100c1e5100003002c4440c080c0c00c802c10702950038087c4001614940810003041c0071821600041c17101c54051100511802c521210b10b10582d200e43c1110b00180b041c258540d0321a5107450040c40a85103115620005601e01000680300c0e0000086090380301c00310721001441c10700d4640356100698402404100090403c00c80c000001c0c04513580301d4001d1040b80d0300c2a031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 908438381 1250 908437131 908437133
    0xf020901030c030b0d08070204020708070f0b060d020d12210204030614152e03050402030c1912080c10021312020a060f03180c050a08300c0d0c 63
    0x104842880709040c0801d440c0c5100c101098440542010413940c021300c285403071f011a0b100040c00303842009001400c6c0503000c00e8180403c08412000e54405102c0c698125699440009200b40030030103100181d486100500c00ac4080303400015000210312207032515100d1458141391050610881800c00d0280c2a8005010428054607124104061064446c02802410015813600145441c4440c0c1c0e4850310728054401408030795004044034140c5410f120340540c0050b0540035004120860b8242c2c024018840900d0139440d1001c0c03814810300d006009a22910704240c00e85089882110007111015401c204010592108004005c5111121280075940c0c1c42c80300c00100307101596a0049098075210307041340d80142d840c6e8a0f40c401b0741d0000c0c6084801f03540070380c0d8120086d268440072042c0c5c89401c4419002407082c8040d41c5401d862041d02c94020382640c40c401a41d6503084071082c0280c0310129a0a41546101181e1054801c040350700c2d260f00344181031070154145400641b20380d02058646175020 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 908439631 1250 908438381 908438387
    0xf0b0f1b03060a0302090c0d06030c03031d010816020a02090c0c0d110309090a0b090f07031109031c02070e0a0e0d0318170c0d1809050108150a0b040f020901 69
    0x5491010031030016030075400c003400415900182404000d10407050710000901042804054403035410802400380300341e507541d00340001c84060300c0c0001e40010700c80b0304018248905000e50340e0a0715106950351411540e035051b641c20050801502c22046000e0f010f4041c001d42c1d034102c20340d40101c035855074140d03585500045140c90003041510b000d0074003220365a24910200c001c01507502850b002d51340c091640c1c1e552214180142003031003071154000d61040900030509011b1044034400d000d991800c0000c001d803a013102c00700e8015000150b078140e0104001e0464501e030701c801c0c0480042980101d03000aa100c00390401401c1c0121100c100c1d50340e80d0025040d039064100400d020a4070a070404101d0320150560380c0c4c1e1245200800034041c003120088149152103181c0440d206541040b0580b480315000740001003d18204000c00e0004c0c08083e000400c911445214150413a450391004081c08503420f04d01ca2503800c0010241e15119030340d07007810350381603ea50042204608681c400141c0d24680c0c00c0001d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 908440881 1250 908439631 908439661
    0x4050c033301061d030316060903030c0513090f0b0402040e0415020f040b0a021c0203040501120b0609150702100903061b05031504060506072d030203070308040f0b0f 73
    0x95050701c8024004000c11a00054620401d40100394560440701c20030021924601c03640e028814070110110b110b00520600390b110140041c841d40d0240101403030170004844138007070319135002c070100c0f00324034104003c1c04164014039114041c0139001c41c2004c503550000c6c0880e0490307031008aa08180004000c104011441001d522285c00b040c00c5050001404c1c1102290085000320840603070300080d030390b000c2e070300800c03640b00d0501c89100c484800e05180c00c8025100e030003d00c590741c013140300d0307000d401c0e10055240118401c001004e080320342458050340030803800305440a00401c54000400980026850b10b8480c2045858151502085149117252600440c1c0e2898803981c408800614080780da507178040110380c0c01180e00480c00f510300c0c4607030300000c000b4401544000d50104d00004c090f0700304500104020808043d4010031061540418000450034040003001001a0001c124800009004100c903d03001800b44844020707061640c1c0d5003801c56039040d1900c1d11081004000c010542101c0100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 908442131 1250 908440881 908440963
    0x6030c071511070f0320010b030f2a0a0f0f050906010f02070510030f0f1b020604050709050a0b0d150c02210706021213020405010b03010b090904050c03 67
    0x200300301d442c440d6544407145000b0204001c10b100711340c03e03107101414440d42801d182d4401501060040354215582e00c0d0003820444092030081c0561400082c05c500007141d10820751400028040301880c0007140582c00c9149034000c60340c031500300d4030081201d004141c810005003039000c080c0c090190501c0c00704028010024149410404200c4545100c0c903404281ca104445c0f0941c0c003580d41e81d62000c1c0c260302030004c0385028043c10b07280c841415140c0c103075600310780c0b140c81c82280c208511000b01101241c0312402102c020b0055404201c040091a19951001d42e001c440c00e0380004103064184001146171301c801e60241c1e550000036010304861445032003840b94074005070005010302000072080c24040030a14400310000f44020a4035401e001c1541c0440308802034103034283e00d05141015030460b00002501080c3c1c003d074a490004a040307604102180e0586183c441e1143c00c04034503c04000c22000002c0c812a07031070082081d009581d03101023007294100001c0c55540d04030640044c825520202c241d10b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 908443381 1250 908442131 908442173
    0x2070503010f0e15091903080f16080c09010c08070b04031206080d030f0e1603030314060d021201060b040b09130203041e170a0512090715030c020a0206030c07 70
    0x200301c0f104003400228508402c0600c611541207a50346400d640c1803c42d41c00d0840f40d1008044130358010940c1c0159928030410301c1524014203600d03000304800b5102035284060021030014000700c0c0c8403010100c007508000005144c011004e030441d50701d200b09904948011201c1c41d0118040c03100b01500725000c00c42c1061000420841e01b40f811034215565a081002c55040c180d072102512800201c0303401c032865080090040b00d44071450701900c48071034200351000341c00181c544200d804a400300c0720f145a0088000614048000c42c480e001c001d010406800c481d95250340e902d40c006040454500074000030210080380680300d03c0000b0900503804c00c00805080c205204204010009100e420f1200c900e07800981481700071002d51030f08041c1a5180a40038000d44401f08413120f07040e9003c001099001d004480c0041c25841d595802e030f50b210b040380901c013101c040220103024014880d03030110246107400d1049403414405034010580a43c4203032658501d410303000402a00b4422840365004c0040b903020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 908444631 1250 908443381 908443391
    0x90c0d06030c06121b0c030c0503040f03170304050c0621010602010c260a020309121215030a050a030327051b18010e060105120a060f0b280201021902070503010f 71
    0x2a200085c406849500082800b08558a290906115a440c80c00155005044951703480d111240354818000501c001c540300c1480104212440c80c2c9002034902070350b0301100034142000e0280400c005a0012075a022110350045003110a10442640690080c903454000050705110341c1801000c0c40344d40011441c41c014001c3c1002a01384000c000380350f0203050b010340140c9a07104c2c0517140d0709201201040c911040d40101c0c0d403504089601060723034090310324642d40f10001400041815240c428100008d00349070003400340500802c1c020b4102c4154610501c4244442a64000080c01c03012074441d01581d0701d0f07002e0700d0780c10610880790703802d0503002004450200000350480c1d5488000001400b0311300d0803151020100d100781c0d01070001d80e9480c900d41c0c060102d151401c1e0003d10011301d0340784901500104118070000b6400310070004c0300c01124041c1c001d0817102c2c03504618909604102d0484004542d8208400503085040e900815601026036001c0c1c43d455180404150940b58210030300100c240c940 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 908445881 1250 908444631 908444651
    0x90503030114010203041205010b010e040b06030f27151e1605070f060b040c0f0e0405060a0e070807080903040b070f021302030c1215090105090c0d06030c0612 70
    0x42500d0445600d101150100322003000100e085d801355501909a400354190420100074040d004010031130803c0c0d0b070b03001c3e4030046113007004251881c0e0510250440c00c100007080303514244800440c0d204020030716940d00c404a44114140301d1424210706102604075117003c0c208100c0d0298100d801203c22000b4403502200c2003070480e4441d0000c1c02507a400360700c07494211900d40c0610b090f00d000f247c01420400f04600c9130305085000e01302001581c0e02c2103203008602010725005000160316184c043d52000d04003881c40c8180001444094651640401d00034400202010031010b280e20464456a0710740ca94240b280002e412440c0c040c0c0007a2040c0c2060000f40244c0000100356001e10b03402c1000d2400100d80c41c001300f4140c07200940c0071200180000208402000c2641c010600f00309250004481030381d03035032280e5501c01452003059900070410f100402c40352800c004202d0700141c2c2d15035401c2c03628030341540c0178007140c41c01d82c821200c0c04421601001859009040100c01041c0303a041804403100c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 908447131 1250 908445881 908445883
    0x51003091b1a0a0315092309030307110717010b0108100e0628082410151e0207170604120503070e0d060501050415120321050f0106120905 61
    0x42c0c6040110000c000f25614402911076008008000804003500343d1290b100e400710406819503402c0101906090346c0302c9221043c5111550b44183e08100185046484004d0100c3d45001040402c6815114031030f8045440800c0800f0451a194000000165104020005024500c0003400107a08001c107a1040041c031409100603a40204c2c11641c800c50340e0b0100006260160b500e41c1160700400e9440c10106071050005108070008041d0020140003000c02c020f49400751000700d0340d040c605507059804008c58000300c6240d021565090038084444150718030340200c0d5456140a88006a02a540c10001d48610142614a80d03a02d000074102e1881c00e43c50b0300f10f001110140c0c10040080c00000a040281b092070500c4c003810b030041103003030398842034244407010308420f0294610852600c030000310b08240110040048036001c0710741c412011400d40b400d0310034022506140103414001803046000000c3d0748100352180c402010074074940c1d4101f9200a218031031204140e2092450031aa200110b20 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 908448381 1250 908447131 908447159
    0x608060409030c14060405060a02041a0a091a030105100306031a040c050d0803011703040f0e0a0b040f0203041101051606050603070801060303110d0c110607020a051003091b 76
    0x8815103010603215424902203d40e2511600058002140b03104c000006000101d025409107000c0c00c00c554941d1140e9144504901c0b480c8203d8000e038511a51052100e5400030241c40d007c840c81c240201c40555030b064403400222b1960000c00207403800401800549803d410140351722103a40b8041080d01c0c299510240c080c000450300c203801c510550001010001c008242402501028041d604020001e18001600d60403c0c098280c03044480e01203d0840000041981c040b20701511443c014145031102030019520081c01541d1050f23214242501c032501c50380214400901580c0700144c0e28582410111490078030003c0c040c2c100402085009001d6580c00901580c803030304540c0004046d11410002072a14110b688120019401e00c00c0010606400c01c1e0307c00e21001c1903000380c84800010520071a02c003600c1442c0142501d40c0152494002d041003009400380c1031000d4424400e07a61100005140e85901002c48000280c40303c3c02d010800060400c00207192a640d155810160300304080460f0742e407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 908449631 1250 908448381 908448391
    0xb21070509041a0a06051b0c030606010807050f03040c0608130213020a0905100c050609030306010f110109151b050306090417071b170f0c0f011404080c18010608 71
    0x3d031140c00c1401c00ba940074024500c6184000d0a403110f0a0b900c09014090350000d07998402d490410840352800f203240400c11481806c03004003c3c0c200d81d51010015504040c0c058540c1003000018003140c4454183c9c10003c1d40954010841902e540d0b01d01080200b080c2e100070031031070301d0a0700c100720800161229603441d41c0f5591511005611120358050441c0d90340901d600c1164418500c111400c02c031500110300e00411409542982c1140c0d80e0300d2000d0b03669101c02d542c1c1a0000d0342c45600e00121038440c106400100c140c41d8004039443c0500e803241540c09208407042110241d0714490000042d4400c603e24080c0099401c2c018154a0325030b0000b200f190000340040c00c4405028496030500d480700003211159a03000240003210381b41d0480c201200240f0b4060380524803401a10741c10300100020b81aa007130000d0b20014898910301c0400c1c010040d140004884c113000d198008504007035800f074050302c060f001581c010315002c50b802080182106020341c081c4d20311216480180205544002865484 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 908450881 1250 908449631 908449639
    0xa090c0c060b01030f05040b06100f0203070618240c020705030c0d0c030c03050606090708040b04120509060f190f0f14090a03080c060604020306030c0111010e01060b21070509 77
    0x40c42d541c00043c3c016050b10401030300741500c1c0201700030800140040702c9014100503120840104141d60342911501d025242d00e8002d03920601c86800000c205410840340d84204040350083d51140d41d403410000b01418400540c04044e04a40000d50f461a1040c6d6010000b00c0c4001c090052411001c1707500c400001c4004c070300071340a107020780d402e101c540004140190360110800d00072070764034100a516020705030341003440380c011040403403696449413400c0b42c040c9070803c00440c600d45403a1749942d0b942548107440c1e014001c1c1400322888540e0742801408a05440074505980c80b108224540e0701400b018840406116128000440041d40301800403080b00090400050b000030404200016000c0c460f101a440b0300c1c0704901208101d0298052f2271000c8485003241ea007512000c0400061b400102c4000d50540e210940039100c541c411200312240301141c6000061180d02d1400441c00c2d240c0580242084c640300203840d0604070500346100d03071000c0211380140002d0400080c01021849099002803107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 908452131 1250 908450881 908450891
    0x11404030f0c0807080a03020d0e1c0510021b06060307030f0311031909030605071d0f0619020109050d0302040308040e0606090d0605150a121b08060103080403020a090c0c06 76
    0xc000001642c9000741c0541000c5032800d82d560003210745e6800d00940100c0c0180100345148801d01c3c0604d4807081151801000d102e02605c0d01204410392011030981914184a030001e00400e18150784002e101d100da04084c403041124540950918162020307003514000c0d07020900400200e074164800300e20311581460100b150006c4624001d10358040e4400c50008406901c03201a80f60b0b411500c0c1100716403140105022654400d070050b80c0043e84c0c05413150101580f00c044806501c0d248005860301c3c0801000c10f0305200c100060061b02c0814484860050703035540198105102c0304000f048000c40b07240c58252b1400d81950b88000c03071405184514421404070710f0100781e8603540d00040c1c03540000e01070b0032450f000c003103814034002608040d9440040001c507403070940302030b0400b4a05003065070b04a80c1d00907200c0000365503038140ca160003900c00072445601c0c04007041c00c460600c11140294024a40300303494a01303500410810010344c1d8054035015141045440e0b1442e0000c004c00c06242c4c101c01c0011f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 908453237 1106 908452131 908452133
    0x30d0509010207120e1912030806090c040302010c0f0b0a0605010e030c0d150b030d030b01120b1806011808060109060b070f061104050607110f011404030f 68
    0x100700d403502160a03144c00c1c0038031030304985100040c040854098450700003602081c850341000d5492a44807020005255101101a0300481c0495401005042203d40c3c580706100302d100c001e040c4040c2a0301c0e5810302c1100002d0545194001010904910744040c010000302040c2c0200c90200e9804c000702103c60400040e0601c03c1000600544044409901da00461552050a1140060311403580406a480c140407400b00380322651030100e044140b0b400050303e109410041108428a840788219042c1e0302c403d0081503030a47c0b05400f80b03030390b240c2200407a84003260582c0ca0910740007001c1c0002c1c0036000020610304030303004003030108416034840e0000d000038481d40380c001d480040c074049902c010655070351143d41c0c0001c0400c01d103850660b43c1c001040392a0040708003502c0c0d038400881049120300b840c0c04c0e80509442c003403804800302d2280002c0606240500d010150042c5a007240b040 = true := by decide +kernel

theorem cover : BRFrame.Cov 908273381 908453237 := by
  have h0 := BRFrame.cov_init 908273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 908273381 ≤ n) (h2 : n < 908453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
