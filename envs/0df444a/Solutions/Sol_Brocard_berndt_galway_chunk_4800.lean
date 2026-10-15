-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4800
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:46:11.231227+00:00
-- url     : https://prove2.me/submissions/58ddefcf-584c-487a-9439-523761e8ce84

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 863129496 ≤ n < 863309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 863130746 1250 863129496 863129503
    0x17070608060d020301050708060310090308060904030912031d180403033605011a0603071d04061e0501030605060a11121303150605060f0c121602031c020618 69
    0xd258013500a1020b41480f401c00f6103a2070085680901034030422081802442c818042d00c103095405480b41da8690b16080b0502002110041c4142c09201030480700045070a003100f41c80c251341d4042d0742d580d00f62000d203400d0070382d03014010654640b082c1914180250341c04115144d1540041c0d15050000350750346261007a0000c080c00030607103003c54100020308000a259030310841001c0c0e210300c000700f10f80d045860000c02d184e149211901e4125400f80f001600c0607004620040030591300c101301c1b14810151400040c1a603d01f5000b80340c181c00542d26070070032400142ca03d0b50150009003800c3c030100e030410010440b40c0c001c1003041c0c01080503291001312100b1041c0411900c40c40c5942650303a0346c50251040d02204081d03484116401e41001c0e0407020040132030706c80c10098900c0140310901c0e264612560105640102e0048400c0b80181040305030364952072002056071401448144040740c0c2c01d40101424120004080810554a0301d400d0092541c00306c0c450b0360221412112800b00250103580924 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 863131996 1250 863130746 863130769
    0x501080723010315080f010b0316060c060608060c04142b0f020303211e180102090907020d0905010534170316110d0f030f14070305011707060806 64
    0x104c40c80f1440108200d2004030340ea5800560781d0b0000c3c0103d01c1004185030ba40d0614030542d4035020101c0d10103010b898070a004c1c4480b02d6000e41e5011815580b9518a18281001501c5a0172012000a02001903402c042c1488591220844036140000611040850760350740c12203001000c600c00c8003020041001440705411003e0f0050126515140000c0140041c0d0181c03002c003003803003d08074002442c200d003640c2c80a90612106104d5070070342c1d11510800c5584021440074010b040d50223008414858031800f8200e407250f05664010300c554012020040d0007801c6a13044941040410040d250740400f50030780b000c00010b40c3c050000b11400c483c0d405401004c1010f4002050f84040e80f00b0210b00c2480000610301465012012040c03001c05480140c65926a484000030290011a0303a0110a80240303445000c1428a0174046480c003050b0b01480103c4240c0310414030b0b2407404009000c5801d600d84107a902408084804074022000d18150f0380d40e03040c1c140705900410012200040711034946045031070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 863133246 1250 863131996 863132021
    0x2030c0105040f0c0515070611040816170106080703120c0203030f03160c0f020910081608070f08070b0d0605120309010e01031803080c040b07080a0305010807230103 73
    0xd508051424071206200c682084d1003102d00400701150a140a801e44c0c07021072404040b0a140030000c1d61401c01401d17400e1000c0f643c60310140000190302105004e02251050b0314442d0601e00c50520103a540940780092481c42180e14041d000c4c002200b0002d0440c007917a070400440030b8805080541100d0044076010000d400d800302082201c10356041d0000380d40150115088003000100b001c8044528104072000a0414002c5181260250408007504c40d04218522050b840301c9440303110082c90409440c8001d140d1070303842d42c0d00b000b201e04240225000b0306240503221207600c1c0742c000c0700c603981c03001405800360f01400050091004074240e0f1165004100c003070644480071040060700d0f501c03604500110350110341c001c4ea04030010341c0320340306044898110300c54201c1101c1036030301d04480b6108000d03c0c1e8000340c58100700c046a000310210151141903c9030300100e69988038084002c09441042c1d002d117000c2d6202070810300550310131040c1080420b0b20310441000e101014001200a0b040303e81008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 863134496 1250 863133246 863133251
    0x1090509092103011508040b0406050604110a0f08090c2103090d06021b160b0a02150a05071436120303061011060414031c1406040e0607080702030c01 66
    0x18026074030700c0050750407202c289240c40c00c2004000380c06d480440b000c580c000c200440040000300046d5a0707512403900000b001c0c0002448210720000c5c14000c3d402000c8100224141d0702466890382c1c1d10510150b4448900b101614120359000b003c92059649040d80c55081120070540b140555010400c0c1c400d429801480a01104200d0030950002d6011612142c805274145070380302404a40005c903000308002e492a080c0089240200450007500200038034001c60140c1c181010031072803008070b1640a0070032214005030038240854080d00c954103020a221a64074140a075861104032030120541c2119100d10401c00f1000c0c080c481240c150750707034180f9940a0643c0c50100361a11001000c0c600c11041900c0002940c4080030040d00d150341800c0d0420582e604c400300080001d18500344c00380c40d14094804882c00e1840005a00001042c00d010700c119199903000d2402e03444400c840600c0d003028042d10104031882003500010307210358008001a0074050507401040525108004039010246000001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 863135746 1250 863134496 863134543
    0xd080a12091209090c0206040303110f0f0c011b0c02040902150310090b0114250f060207020a14030312040507050a08010e010f0b03030a030f060905010b03180c0109050909 75
    0x24982040088510740b00203000c811003c84c81440611814081d032207143c0060801d50741d0380d03504502502c0c800d40108000f00050240240c4810840090f119030080043c5075520f880300f0522250031540401880c1e003003604044109420345070040c039060400350301a580450031403054008181203000700d41070904540f400108010401481220140645841103810f200c55590b11004440c88000e58040441003031040020b544041900f4240910400420484031044101c1d03440c4e201508000c810f040e01c609800046400451a10306095806030030b400e900c4403c0d00d002030700820ba4074090305560000501d0248086810301c03078200a29001000003c1400104030303103400031071340680594580e480082d800d10751941c500140c14080c401134000301400542c1400080b410490240140b000250f8030b25984480203d201c0c0c0700e0780100c9001c0c0c001019420703501d082080c4000d050b116000c40360304040e0028080b807405603a0105201e011154100c44c0101140c5035a1500c41c18008082c1152404c01040d455 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 863136996 1250 863135746 863135753
    0x20906040b030a050420010203040b03180115090c0903170c0c03010f06050109080c03030703051b100b010e121903030f020c240f160e0a0e01091503020d080a1209 71
    0x20f00d1041d8071501e080c0c0e5641c14a0340310034240c44038440c2900c7c0503030414030052000c120480040e585c003c2d000c2c1004901004503d41c01401c481031070100c100303000e014010a00c000785581c000c80d0301e490214500300062a00d1621b8103403914156524500403a40000340c07856400004200c903480d403000060081050809016030003004026070b1081c0b5001c01c49a0b0000620201c001ca102c00030401c0c0074001d1803401210f540c0840b4076500c140e061248001b0500d10007161042c0800c2070764069400014005408054100090400c840c16181184180c1c0249800c00380604041002000e81841141100c01c020301c43c5410ba015042008112600c20f20109100b65050341c0041d0710744a00504403920340f40c10340094503001c40e00e201141d41c620011400f07070101d00196110320321024601c2051820001e01d55007a800039503d0030071617124914100e82c040060240f9025440707230f1410381c01c0c00300b6178460a44c0342d9408902c103008400b81c042e0841401183d5100020300480d0800d03140b000e03d010800c038000d42d515 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 863138246 1250 863136996 863137001
    0x3010b21070504060803120619090510140d080307020a0f05070f1a030609100302100f0306050406060806040924021908040f24060e160c080a03020906040b030a 70
    0x100c05024038464210002070509251080c0d01c00d40d28050007851401c0703c12603851f445000080d1030325401084001500340e120050080c443c001d04088500810717907007404540d41544040f0303500004131251400c075004110ba42c1e42e1004040d0b841c2e2211050b80c80f643c0352041a81040b159280103851020340c02c444d4804c00001080382d4040d6500004c500c9901502c459600d6802020100b0b41005030804002040c024542103d1041c1d00403004054501d006840780e0104000540c15024103022501e8003a00364401c54040c003841001c1d001c243c0d42005402d00d00b02001b806414007801950160750340f550b41e01c0a1182c60041c2d442c15190300700210f5003284410000074000e6002c0320f0700e02034001e014000c40030124032660344035008540010712080d03008010781b039910340c0300141340c421001c40902030641c01450825000d064024040b1070f5000034a4a0540d2802c80203003843c625810400c4400180100091405000e0301c050702c0300c510b0010380f141c03040c101282c818401d40d00500c0d000d2202104100e070544294 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 863139496 1250 863138246 863138299
    0x601230f0c07180b062b09060209330f09040221070504030807060f3206062d0403061109040f0b060307030b040b0a030302070303170603030a030b03010b 67
    0x3402500f4403001000c140000300c0c0d0220032140d42c4204204a00031a00c02882551045107014400f85400d02c59000380d0b81d0104c4280107400c8920680206110049190201d045203c0c824a00b1508100000c88070400400803486007c440c114207003c2202440140c04c101aa1603050740038004558420041d4070504640c1345100301281841c0154001580382d0307200b44260303803c4a0b4032810039403c00324540c0d0744602a007509070041301c00f2070361130307802c0c8101c130007000304c09080e035400600c1000d6004c10b240c84480c0c0a000007401280900c801b002202c840800c1c500581154161001920024030404210340c40030b03219640c806403940d4100421203a42204143c0101100c40d01200c0c1004115803056001e0140ca03040b03008a40d01c40001e0001400301400f82d00b00035081070000308000780740102c0c0000241181e540742c0054005074020740c8103000709038100c0a600c000754100c407030b460044d141541c0001c4d50703881401d07290410151507014500d41d81d1025003160250140040c00038681150030300680701705001c4c0c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 863140746 1250 863139496 863139509
    0xf0602060907080703050304152615030105150f1c050102090901060e030c15040803030c0c0607080906010b16080a02010b01031104030f1106040302061206030c090601230f0c07 77
    0x482c0000100d002c00020044201c1e0740c08405941410302e02003021103107030031060a0380107200203c061003884c1d81811000881c8190107045242643c00c102e0080c0d40c000e010440b819000381e00d880c09002070001d0281503208203100c2200d040c510aa00c50000c2051241504080c005c808813b6142404110b0b064002e0804008180c03003078266a80c0c2c90900f1181503140004864058022030400041c81c203001550154010455085526066850351410315640c002c03250a100d1002c0403955203001c0f082480702c0764000d04103140042c15410403c00c02d984540c0188501101d50700d00003140009035450021601c1740b03c0d004007255485003400040a4042d0207107040c5140002d2820b1351011000001c1003e540550750002500c9041c1c0116030b4030000c91405201ca06588a0414007000005980d510010808404031801c50700580c102070090618100101d10310074030600c0444104403545e41c0c4220f880710810311448007a07884140a25000f8010301c2056040b5403035010000380010510400590340342110741 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 863141996 1250 863140746 863140753
    0x30f010f0b150a030e07080a0f0b0105010c1e0201170708040c0609150e0303070602030c0a03050603010522230304030c0e0108070515040e01120b060103061413060f06020609 76
    0x20701c070401c200050485892080c00c0340034840b1042e603a100f0750203055100d03441c104503988640c80308115894070054900031100460050007480030000e0900107940100380c2070030020791142060b90341d805440c040b80341c00d00181c0441c00c004003c1d6031203006040a0030301c0b410707883c02150500d14401044a48210345c240d580302c0d83c4240c0000c080d48541c4a072000c81e00b90100003641e84184c03d030100c07007101001d075801d64107220500000000c5075891000314000d0784081d50090b6142c0d510074021741600c1c0020083d5110345d140c0f0007017118000482c03240c80302d00c511006010803002100d00d8840110548070f0464401c80803411402c4011200001c0100142c03406003003000e104560b50700d4183c0c9201424051040d0f40e0708039007000c00a03414000340b4071b00a03040c4441ca41e42441d03182d42400740001000da10454a00002501c5041400541701d04a2303000a000c0c03031706000340790400b21034800c0b030741c0c62820075406483c1088402e050350a2580c8207030040c010755031141280541e9440b000303640e00019031b11700c9075600 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 863143246 1250 863141996 863142011
    0x20f01020606091b0c010c0801050901091404170d0905030307110106080d0e0a031e0c062613060f0b10020732060316030f02280e030f010f 61
    0x10300000e2100d2240c40e004140c00ba50f030340c80d400d43c2c655000c50710504091400040c040849030100c20f001f81241b0000595403c40301d98904010083d91444c180c0c0405102491304225521102c08203403401c0d80903420440048014900c022181c0203485640c10f1a4000c910f0700200d01c1c204813001c0021401003180341d4807900d8514074507605a08076240303803168101d40e034000014800c02e00c0c002c5402d0031105000a05100310542d5a0f11343e00e01c001603840124079180d03083d00c0e03100100701800562401400b41ea00d040a0020050101c0d880d20060101980b40060300500c0010410002026042c103074035031019080c80f002c8044000d40c400b0340381d00d40c1851710820000e01541c403994030004495003103600c0798034100000848603440b581c4000068050300e02d58815400f182c41c440d00d1f0030000750b00860006000b80680b146601d00241180d5844491210003801040040203060011a0180c0340320001c0403000c5100385840020f85200c0c15044040780c05005405036036001d810190f0161048804010046c040003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 863144496 1250 863143246 863143249
    0x30c0c0d08010839032802030601060f02150a1b1713050712110a084b07150801080d03060e04080318120a12090c0b0d06051c020f 57
    0xd0304684083c03c03006080c500704451880721201d074031020b00c10140a80340307040710014803500c6c5980f40000c07450f161600e00e4020811410100101c50040c561841d01e4207010019540082d00d50b003000c50304402c50040c10010a000140a50088083c00c00000310504032280c0d145029240c200c002803a5201030f484200020358607514214401c85565002d0003a00c00300c0e0928549038510742c02d90605a462128448113101d00c0d8484484074405000c880f0300604000e502c0000144030081c00c0c40d4407507640e503080c810046a16450141200000d048a4280e01c200700ca40034400385000d020f588150218006103a02e1002141c221200c603051303500308810340d0f000304164082074007520400c0c0714115002444000040104006402842d0444100f01a04401c0c009290079545828200200404941c00005801d02e02c6c0d60004511b84004803084001d01459086071681c184001c0d0501c200e000810b4002200806800950700a2014180090440c2440180c0743c90b100d8400b03800f40b03801c0f80501c5c1c08140c038185a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 863145746 1250 863144496 863144533
    0x70f091a0403030f050f0d0603110d2303070c12031205070e060d18060b030f0a020a06081b03010329060f0415050d08030702011409060c030c0c0d080108 67
    0x40c01052000389090301d035540c101d0315005145201c100700f14062040382124100300c00104005410802d0106040c1d082d82000880b41643d29441846004200b6104c5c0004502205542442100e145408400250002c00b1815485004001420f2414048000c501414901c0d1100d010341d020b90349481c00454415800f000f211000e403010000300c0e000344011030007490f03c9001031050300303920240031035045454240f800d1004003502e41140c21035169034030800c041c103040016940c0030380d5080007081c1803140c0c0d40116030104800d00640040101e450002105a190107071a0101d80012500d5a80c1d250782d41e04080795207499400c40503440b0a005014401d00c010425140b50103140000c01403241818000100f100404005000c0c1c007510601000c0021590784100d10103000c5e03800740072079581c0ea1506020007400c4500380508003601c80d000070280301a250b40001c1c100d41c0100c1c0301469980d20303240c102d8001c0131340c000d207800700c0401d01c01ca01d10b0802c107503480300025041b41d0300101140d04041418000045 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 863146996 1250 863145746 863145779
    0xa090e0d02120d0203060d05030d050103020f19090507020a0c0803120708010b09040e1204290f0d091a07021b0102060603030d0b150c0706170f060409050f06070f09 72
    0x102c244140807943d85003503654025600300c103005018001080a0395900d9003180c00051540303100300e80d540c004109500304011008503043d4200c400520f802c500c031244154440e11800b0b42200c0c6941da20020717904500800031814015041326810710203d031788a8034145d582d44a040200541861800807031410750144000f02c3c11b039607043c1c40060500d5072031001d000042c80c0c00208c0d5071807489483c044d1919005864001d201034640364001100c08007644a400042030510301240c0480901040302821074002c80c0b05484070481612030200c0c00742c07120705215510111318016090003500900a02c8007482c3c00042e1010001038602c5000310080d085d80041ea00c0740d800301c8406405405c100510110a6142d80c0951643d140041008640c001045c101c0c081a81101c1c51150071030388401001e00020703400c070804542e01c0c0b001c4007a0181500c0c1c1505540d90344c036005030580c0d0082d074440c1e00000801405001072004004402d0445030540f501782c1d4002c00581400c3da040005ca41c0185012402140e980304500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 863148246 1250 863146996 863147023
    0x3042a08010f05042a0e240d0302250b04060f0e030a05120a0215040c1809170922150b030c07240204030b1611060f0a0b0a090e0d02 58
    0x114031041c2418210380c034801c00c142c2c6100c3c111000403d4800011080500034010134807003800b54001000108071287d03842c2d400c24800c0e4204007210b4000380d80000d04d0980e0290000302411107580050038081e01d0380307054000c82c6443e803000c02c01084055106134045c05041c1c00b80e403051080b0502400345910f41e01c0703200d4094456089452103030b510304035520042030f4440e038900c1211803181286408180101d01620121189260400100074840394080d0348a07051451403410000c5074486c2d542e03030516420345d0100604c141004a0041c0040e500c05401203600903e00c1c6007040c0d501c200c10380400c02400d094082c1d041e4440319000c007049160003032083e00e102e20000723980d1929200440c0c4610b44408007046005241d09900310000c4544203090014000942c85480e003511941820851084244070750004041013004240707242c0010399000503142e80182100a0004440d1203154003c000307070942580254000180400008449101d64044d0030007403c000180c0e81180d0380f1041c100d8076480b03626501d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 863149496 1250 863148246 863148263
    0xc09090e100b0d06050c040608010b0307020712081603090323030f09030c0a0303090602060c16030c020102070b12150303070308070305190c0305070306050a0f030803042a08010f0504 80
    0x405007003081e540001030000e0002c155010540e0b45607549825150112413803c01c0a801181c10000745412000e0240940500509181180b804101c000c1d0f99404510405150805508a000c1803190343c1c0c00312501d284081c9500340c0341420380d06010380141d55600c4100e8032a09140d80f03203011101d83c82c2440941c0200200510b251184524031030115410102c4a15414099a81e0f0001c0c29540c81d40e011000b07600c282c640700012444c0520281c00c0460081a1444071401044218820070510b944000150b501d41410003000c403642c00100c0c940403454010010030580041c600001910b035500082c81002902001150541d44405054403405841c1e4000c010402110100340301d07901070f402541c2e20149680488102ca17400302e45003401c2d07544c101902130109036290706001c10982d25010b864050801030303840d0316107249485807034000840c041c403000d400d1900c08000700301042015450036803408040c0c41450507074403c0d034000b0050301209100d2a5465071030001490b08401c041c0c001d07648034940240340da = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 863150746 1250 863149496 863149513
    0x5090102031804060801060e070210140402040903110f071403010606140304110402070c4101051e040f1a0304020103020d02090306101509360c030c09090e 68
    0x18440240b115501c070b6600a4481c1400f080c003510910078400200b0241c0c181c110181495a4040d0800000d0071690201500b4000c40040d210040584160440c1e07042e07130001101006401c00315001e0280075248100703070041184100240d04009000010340340f0100c1003080b00840d86041500721180d51203520003142402c0342c244004000c004c069544a401307006d008220030403070740024040380e000361800c55201781c031608141b191a0701c2c0c1c011442c240a01c0d040c81142c512070800712803081c44501408055000c6046044040c0c0d91184003a100c0b03840409160b0303130640800d90240000e940044c022895141c0c0014800034600e90180b40c601d0f4209180c0066030f06c1c588454004501035449292788490080c1c003041030321141d4a00b000303064804c5501907050711426091903140c0340c0c0791030f5808210741000f95070101801104402d58107402131007039a01c2484030541e8040c00c860503017034100e0007040c00240351a003114a61038058118207602291a0b9440004a0b102c1e81a14210b030480e1b54803085035440a03c9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 863151996 1250 863150746 863150767
    0x1061e0b0702190e0f0105060a02100c0905030a0c06080907030f06151806050a1413200309030c060a090b040f0206040b0d2004060f0f090f08010203090d0509010203 72
    0x3040520300161812503c921859070050003141e181d440301c0d0341038070b0030700401c03003110241c041250140100f01d81c0149404070541d00290340e043c502d804048015a1450221001030044120380700809010702a50914069070408503074000032071140a0102d040100040c0d0503643c0441c4a80c185c072380c03052140342c094156444540040107441e0985911a5580320045030901841d650f0800007848124003148441c1404180000c003d85644420500d0381404000d90032170b0780310b06160b0104c454002000a190700420805658444009080c801300701001090080c407603000301c0100100068401151160b0b214103a141044030402d03d0050705180b621000301c0c0010320a0b060780c110090000384610304180e190410680d55900071001100726659a298001d0403886001803000808814a00b4609003403901102400008810301c82d0300821625401050480d4011102071016190401d110048a901c55040a000b0b52095840100e54456400043c0304988180201d40316100103a01450820342d0004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 863153246 1250 863151996 863152019
    0x21504121209050a020315060a0302040f0609020a172505090a03050304060f08060d0b01050105030a020f12091c02030415020c0d0809011403040201080c07062a0201061e 74
    0x8248204000010082400e545640c0c01202000d90043c8050510000f082c41058500705600700080f4100b00e0320810032485da55030740300510031a030301610040740100145407040000c007001e4000c2c00c440d5102040d004081c0703500401e14401240003c15603c01c40d1141400085a121108600703c03034402c18009031a00c040c8101c000d400c10400140c40f1684460712583d40c1030940c1c106801000005802000407601182d014215907001030341501c9a81c0c00380d040d5101c444108005002d8641032040c00400700c1c04101e00390b4126040e800607000a19103038214682030035111078081d5444240d85c820520400c00040f00d51103103083d10140e40e0001c2d4980303854100d401252040c2c501804003540150301103e0650340b0b0301064400c205100b848a180d459090300005080502c0034084103545200900c20000141d8000c042a50040b82e640e0b40980c4a030400d25140c1f02071320b2400085800c420a4140d9981c0848840701c00100709403242c1c00a000c22612040508200f09810301c1481e00501c5109040200e4a501c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 863154496 1250 863153246 863153273
    0x1a010b0a0516300305040c0509040516090c0311030907030b1e041506080a05071206020c0d020c0909010e060417071a0604060603051302220e010203040c06021504 71
    0x8a89900907281d02e40b10100b42c80501000a8194032020b54400c2c0c908040003c0004201c002d81400c2069051640b16800b14082e94044d8030b01440d946030108062020410071601c031012140440454030744c89004c2e10001e4014070000c02c012074101040134910410700400c0c5d034030440860006046040c42c7d61562a07000e0030140140030030b240e01200c41d131201e58658609a02c140d00a03510b20800d40c1100203064111a000c2e4002611900f000022000060001c40c0000884074901000300c0d0301d1182c0e0030035030000c6c480d0320a105100e200c0d1848020020760041220301d2802801c8400c214155034800a0b5030988070105901516a0800400a400103800c6284041c0b010701c900b00d030710305040701070b82c03034010920a200e0380c040c00c48110002c004140c07031b1174010b140203444185070900c40c1e810840e580c00070000240d82c00070b20a00241e0b10a10000e44d048880701420401c50b1014044004070005090007580142c3c1c00356140140106c0104441d0f00001e90000c0c03c002500454965039944d403100b11103803008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 863155746 1250 863154496 863154517
    0x11104030f021516060b0f0f2805120d02060a02040f0b0f12040b01080c190b0d140c1209030c0c1201060e102607140a1805041a010b0a05 60
    0x180b0a01c2d80610030100e068601c14882d4000140c100c680c1002c0050000030381f60b0003482840f5001110b55103440300d4540e034643c15030235030325040005030315514500c80a40c603800c11070300080101600200c0917000109070301c40c4c150355026a003168880c120a5800d0340301d54000d0000103400b4a8081110b0081140140091a8500343c0941051002450341c003c201d01078506451607006100184115901030002c4c400c400000c999400420b0740700100c42014559600c644c00d0b00480100707489092203881e4000c0c010003100b40c0520076503450120343c2c0044540209080714480204080095070072980001107a8124800c10010000740068004104502c1d0300d400c4508040d541318640020907070041001c842c06a910312828528850030804c820700c0b0741c0e10b2403252418404882e0b045181c403d0000c501c10b81503c49180800101c010aa000b00e940c0c90701c1944103200840c8521110084900540d210902440c803613024084444046114048801030038000c01c000c0420030070001c1e0105014000030869500c8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 863156996 1250 863155746 863155789
    0x2a040510050f0604172404030207060c1a0703020a0201060b0412021c0606030501060612150605031008030c01050601090b0a02030f090d050109030e030c19030f050106050a0b0c011104030f02 83
    0x481714240e030f1700b401458521880907403185602c40c20310382c0071160744800c403480030800016516003a10002c3d524801c1c2d1180c1c0c0d0a20940a44003414010000681d151001c811b003c8818031341480c5100030001e500010100e00154a0450041010742c03544c01190119020070b485101e08803820740030440348946400c4070784002c4031404103110004695008402c01140140000694580780c454042c26000c40040315810142c905589030f81c1036078034601060180c03031340e42c40c00f142c0301e964001d4580b0202e51240c110119910000c200100d600303805402c45441100203a0315509a00d070749120f81c82c3c1a015640444c00560800d0040c00c3c000b001303c4020f030030000c50082002903140344580b02d850841e00c0c01c81c01078001a0084030200b01608080010a0076103d0a9424203074a0402c0f00d281f91000780140801440203440f80014418480c00b5007105000d054001d0104d01001d688448240d540e500c4a0480c0209508000d2074000095907030f029142241c0e0070000d02c2002051940c03c008900301005403140c0c0241 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 863158246 1250 863156996 863156999
    0x1403010219020f1e21090301320c0415020a0c0e0f010b0906300c0408070f0e1306060f0b040915031e060b032a040510050f0604 56
    0x1a41e15051420300c039894001c1c10004210640040c14500312190202413003040c1c3e148080c00800c00540b410b00e00d01c44011580c041004010400c02c00e210381032002d40d044d820b2425600b0034070b1282d18055071031020040700c44a540100e020311041610704484002c8940014001007199911143d007403101c2e50303e21310540ea02089075a8a102e41215513400490720100d41008000e14644400080d5000d400031422460602c2110000a03401307108613134a525401d1440c03e1105560381420400c00c4130402c03000f07841d101da450580c00daa01550018403454240b88250713500004d0140084244030150346029001c1f200c0340c1c3d00d000340805d8134030b00e00303e0403030b40e4540e581c4002031180c0207140b0101c05046400c001a81c2d440c504821381090311611510300c102c002500401b000081c00c4640c40251022070184d841da40c01180d420080000c000780030513540c00d4041d09625503001981010519007401988801c212403040030010300084038400c6a9a02c089088103505010380e00d01405401e91743d12000f07100b43e00d000d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 863159496 1250 863158246 863158267
    0x50c121906090506041d0c040b0f180601021c0905010c141c1106220807050a0501020a030507020a1104020c0304050a0801020c120703090b09010c0516030309060c0c14030102 76
    0x50384241d2002c403440381e950301801868a85030040100c0d9401c1e6018100d02e410350501035a03111130745681114400c1c0c1d55805800d0894980c6511410800001080480e28001c0c440c8107100e010400c81e1101c2c018014450800c5500e141d0682a0300c60030042d55450703054074100401507401c284218003d0321030000c2e05084803004842082202002c1d600601c082034012190700740034002c00b135096503101840e01708100304028200380000d01003030151a40d6454801c04100c2c18281924420403502404902400c0220010700405400400c90110107071303020082c5503034041e012a00d88400070401080780000d4510b807202450030f50080d000b0340d104101502d02d031a139100d0004120390740036440710001d40d4021601029400080c4050303004100e28107102443c0035541e90f0000c10b08031241c01032000080700810101843d901c1041c0b4070301c2003580f001c211400140300d000000b107410380070b2001b20000b03241054003040040c07103625448445a0b02c00208141a030400611282ca42c00d44848590190f50900421003103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 863160746 1250 863159496 863159501
    0xd0207080d2007031e03060312030920090f150301090302060901110405130e1c1e0509060d0504020f2107150e041a04050a0606030f050c1219 62
    0xc1c4180074200040a400000160307556500b2000800c400d0700c81440081c0109420603040054425480702480540007510010f800a100c1c40c3c00c0030700044401a021600c0c160141c3c40703084035600070440c802e42c1208105040f1a1222001329aa0f082091000400c0000c01072141450304800340c4400c0c48894081e40000c41c2c00c5910f03800080d80145c0c400018020641001c0c03161030b8520010012aa1500d420080490724907044948122040b03035a030038414000100c02c0c0804981c080981289082551503400700408060707940412851100412140704102d602544c00c030707401d9180c0076021b142880d49400e032171001441d00034000d903040050440d5040059450040414808000f0000441024456441145803504e603400a003c0c2850081501025076008590045400310845003c035214503e5002251104030401d4410341050410040c0805038000340c200200b070703032002c0e42d040213804260360104056131400e07161500c00c00d10030400450949248100709071310a08100000d000c01206070f185208 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 863161996 1250 863160746 863160757
    0x50d0203070b09010c0c030f02010207170414010c0c06111e0d080a05010b030420040c020d030f0204030b040f0206041a031602210d0603080705100b061c020d020708 72
    0x1a00002601c00820240d10318807900107007420020015040406030185c0540400340c1c0240c103105541e8110f0711000c2c403d404490001e54815080b11501d81c0c8000402d0342900140940b0080c0c000c103a10741c011135480359030158041500806150240761074054156034440c084c04c941005805001034401c110709030240c02c01d40000b9400300507c04120a100000c1c11104040d01c017044560802e0010003071640720006a80d04241c04c000101c0490903901400903841c1c10100c044ca0f0010708140700c46901d9900400c1c407200010700e40c0c90600c4003d00c103a81e2041203200d1804010589a03091340403031b0105450030040c119492002c0c10080c50551207004440341010603c0c4103070742c0d04900100304914980f01c0d00002801203d14001000500c1c061202100c6000507108425011030b00401c03548004986504018001c541000718541d5880450810b20b4075280442141c6810b1402d00d60040030a003004800c40e0901d00303503002c100c40e800743c508e044040650700c00c0050042d29a028040d030008185254010300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 863163246 1250 863161996 863162023
    0x40b160203041d041a16051b012a020d0219050c060708030108010f02041409061c061a03120f0304030905040501081e0d020d08060604030c031a060a061707030905 71
    0x601c6860140b9241004000f041079281d60a10030906000c8941000d00d61800b44409a041280c0c6594041c01d0323402c20b00040d03503c04281d5600380f685036a4072445410b003010200d11140381020001031002c0b010303661040070b00540c5005030301500c51070300c440280402c078202e8948150191052900d5810000340f45401510003610014030001c01000064024814a2601e541020080d81460710f0700c1807004800841d01801c80c01620680d002448540d1032045402ca84130f08884105c1c03102d6054200342e4000c0c052242c0b1042c5e20100b40703001e040d05280001d2988a955002018686801e1040000216540001d801103041c4040c103640810780ba0789070302401d40a0031001d0000c002d441c84021100710004a0740640c40c8060700844100d1000c150b000c03816100141c90360404c040da0b5256000410340c5413040b40d20203480110090b02c04001c101307200607203620440b0184452205a2030320010003094441c035110f50000726843c800d40901c0c5101d0340920551110107400c0015004d50300762030f100e027030200c00010349 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 863164496 1250 863163246 863163299
    0xc05030c150a1406011407020409050f15060f0d02120f0316030f092306041d010f080304050a031103010f060308190905031207052a0f09040b16020304 66
    0xc040c2c1542d1041c0c20204400e03a1018150b42880ca00191903090060107a440d004000a040c0702591600e4100210080d803180407501c0200210410755180c0151512800c400320f217100101e12031303181c81801c01701c2d4120000c140f5081c03414141c0c2003164040b44044542c001e4010b444520407002c400784054403103012250403050201046140041c6090300300381c42403040c800d200c01d0a22820108419004180443d03121003840c4844420029085006e6a4010340b1000d007080084d61041c01000c0000b03040b110014a91500281c4505003251607000382d00510b5041002c503441080401c1700142d03c0900f5071001741c00080c01d004560101d1040d01d91540040c1c0d40500c00003441020881e4a25400300560b007249080c5914904144c0001d458405566080c148000080368880c24400d0030b03c02c104104c1e01704560441d90f880341011080e94103002080c001c1c8a4900c503010b001141c1000c2c0c800743c0c070807544410380407004d64a200310799a04010003800041144401c1c000490769900c0f007242030702c102d4882c20780d8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 863165746 1250 863164496 863164501
    0x30e07030f0c030605011d151201020d06150807050a050a090e0702300405060c0c0909240c0a0f0e060427060501140706020d020403030c030f02030a0905010c05030c15 73
    0x8101755401a800755072264218180b01d03061859404425404c660200c1141e00c0356109180003603a4501c0d102d0a80c00c195200003041c00081c10a5403010040300d4401041c1040f08446010940b4204000c80d240e0020403800c000d07040303250340300e8001021622030358240144241c2d02c5011107940c1400450720329000d45d2000003c91141d0400b4050304103006070140152201700641540b4000b03500452040d580a69004203c5030381d82c800038040c250000a014050407003602e000348007642d41d00b40d60001ca40e081d0101402040601000ea090300727110305e400648003491b0403207803d41110010002042c50040048081c4c80c03050a07911080140010310407000d6050f800e4469583d289440c0c41d085d000311340142d103000010082a40c0291010081c110a01a030390313151744090030240083c0c4144d51031108007030310004d40401016004054020b103d4000e594080d003411204500fa65684160803002c00400c6001030f0400c8158490341e00480300728440e1054904100c2e004400c1490701c03821203200e00428500d03408 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 863166996 1250 863165746 863165753
    0x10090609120305190b0102070608041106071b09091a04060f0516080f06150f070f2a050a05060c030c030a02010b01020d0504060e0f180405072303060601030e07030f0c03 74
    0x10304c90603000c420141000f100030b5450000c2c0d03540070144285424000a000050180840019071000d1480b01806042e5160b08030300c1d04041c0d0f108041d030142070107042408040b80707550081c8150900a507000084400070f201c0d10b080d80780c0c1564020012101c0300d4071081c06d0101084540141d0307000d4484c00c82d10b25510010110017400e100402040404415580340401100c0da599180203025110f0101c0b0903681c4184109104189100707104002e411000720403400c4042140740e1a140c401846000400a60402d140401042024440c4240e42d80400c80100030711007440c120000740a20750240086030702d01045074520f40e045d40c110b04a00740150355652404141035805101c0403483c1000d40c901903203407a0814402403ea0100c070301005000b2041c80311000c01d80d458441d400d400c052a41c00c00846a403905c2e01c0e04940d83c1d038160051003204040046189500c4980751200850001c005003e0710031a0b0302c4a00440092403600340001c0180f0031106d00002058009821610040c059100303000317900d04504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 863168246 1250 863166996 863167021
    0xb041b030506030d2f070e090604060f0504030c0209090c0a0b091503240d210f09030c120f02060307050a030b1219020303040f08010e0d020f10090609120305 69
    0x3113a01803205407030340020041202491001c410f04c05000c103120a407082c00380d581c54a6850713003040d500800309209029009000087c0c103071045208010071300400e4085032015081e00d01c2a60010041005d50301c0c408018685030701c1c00c0340d1180041d002c682c0034801410000d07400d813a29a104c04103200000030301c90543d04007828004a00718042e0502461428808101e0b00ca941c8094080c00d0094049103c1300340e50b9070340260308180da9812801040d2403c8102d592a00311941d1b0960600100d610120309508843c020b10b0301c4411a03421142148080b807801440b6610345600c52800c4403254003420303010005968020142d0300440c010b903240c9484209034000a0704540c500d000003807140301000109408040000349490030480945414031010301107102003032075400769400021082c004032030040341c1050705501847c2c0010310b60341194100c0e411200d0990312140c044840d035100343c10075640301d14100d400350011031071a03100e0480014003094a072038507545021a1044140066154000c3c0b15a01526a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 863169496 1250 863168246 863168263
    0x100518040c05070b040804050904030e01020f0d0f08060a030501020c07031a060a0b0921210a0f080408090a031217061e01030605090106050a0f0206060906040b041b03050603 76
    0xa8500308621001c0400c040d155006552009008050031400102001b000c0001c0d9802001d020381040d565052a113000740c100c0c0d81804841c0e00607c64901100c500a1000940001485045d00d94581800c1850000c4803c450000c140941002d40d0180000000f4000d10082400c03c40b06400361901c98150f287c081c41d890350520a07401d000c3c840e42c00f07211346661105108400c40d4881002e0560b41d001c4100424603c118103041c0e407140341120340c139070400100c0204100c000542d132150030318044843c10407030207200d00451036920009220443c16001490081c00344a4110303000700e820a04000151300000d00b105c1c070b240c00413105c008400415807440340e000142c00358051140c1110245611f0040c0203d05032400e40030502c40455407800c01202d0710f9000350f1001c0042c20010b000d045c2290303101c0c000982250311082d00d200000e0004850341c1e08003031000c514036001c0c3e600140100c82a49848042002510040c0c800135032281d0303a180744040111f0008078040d01e050154802060624121040605142d6038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 863170746 1250 863169496 863169499
    0x1b03070804061808120315130b150708070201180806040c0e09010c020c010315050301050412020c180106080c190c1e03051c060512060a150b0307030504050c100518 72
    0xd1010500007400041a60404426030003620b603129034940010116070130520340440d070000504142d910740230806400030103640c0c00070b450301703101c1a044840400003071042a03c050060700e0184440b00056105540340da801140d2040c02c04a05501d502c00e10b410801d00303442c2107850158044c0100310404040c1c010f076520044420082010780681d04019441d0325071b82800e17504140c2d544c54201800407c40b0220000307081c014008106902c1c00d441c020980902c0300e05042d016200380500440746181030607101381e042c0790102e00300c004c0c3e901c1d0a000b61b9017414064130030503240030241700c02c02444405810324032000c42541d446070301d64106030034030490000c4000760704031034900100303405004039404c54102c80e00706241540305011a0300303070321450000b00300baa04036980c400f84001c03000b82c003031500094040c0200e20b501c4c000c220345a44c0c0a140102074003284214500090280001440640a54030181c0e0150007102552054040b410004007202103003001840842c0b404640083c41e08481e145a1414060 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 863171996 1250 863170746 863170787
    0x819030506060703082a0a031e0204381914031b090307050612011403011503110a05030f0703060516050403021e150301051002060402151b0307080406 66
    0x303d40c1c8008020074801040d5482140409110b545004603200e20100600326940e40340c0d886007042c00340140500a88411102e0640703941003140502d80721882100c0440380e503062008410301186115900c034110510481d2818a044091005045001001050180030f146004588008044409080340900307440c0034000040c1441040078407d0804c0e417030852403094482a07511100c0f207000091915565801082d0461004141006800ca8402040e81611042083e41d0744411107182410708a540d0b42c604070600882071141040071448501c000200c20b200a0403c810540d1075001003468001c0703103800e00700a980700c46800c105001c89441006d40118170081c0b4080c0000240c50020101c6c0075070f004c040d00c0b404104404484040342440b00f00910403000d85840d0804414401e41c01c01a0002d100c1d0b070780074104413400805280c0c4003141c917610a41e8000e14400d0b41160313044500a4907084440700400d00e000c0c21007203802d22041080035245051054104555036401c010000300f54004e1039010454010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 863173246 1250 863171996 863172007
    0x5090a1808030c0d063f06060f05032b0c0807020415083306131407180509040b0705040312080136020d0609020d020d0605090c040302010c0c050d1103120a05040b1303081903050606 79
    0x580071009000940300c4d860405641371403400c210680d4801d006000b94030902c0d2007848034080007420107110031284480d00340c990004070600c50060407001200c035500400340800c540c41d00360b030040c80c40940140c030140c640c20310801803001d00011600300e600317243da141c0640001c000110342e0145104208080b41807003000e1051820b804103c1941d0003500003403900798801c00280b1490f01c80d00a4900458000c05001c600b01007188010f080c480c1c0c00e005580c03541801d81340701c829117108409145ca03211031156040d5000e00745403c5040003500a400e00702003980c0c55443c0052410030900107000c481c0c072002070050b41c1c0c03d03000c0d42c00d104840d0903600c1240070f0340313a11003001041c00e0f035102543d00b00e03502800d044401a44030303d0548444806a008964010300c1c070503c010500c8001d00791071a5010040d4115400c1c43d411190f41d01070740c0030742c21034000080d400300f0040c8070b480102400b0b010b90990701101c9a1200d5103a64a02d0160340041d000010b01441c16224041d0342540350080c140c2141e42610700c2d51410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 863174496 1250 863173246 863173303
    0x3122015042901050f040e0304060e09061005120901021c1e0506100c0f060507170108010b0d0609050c090c070501051005090a1808030c0d063f06060f0503 68
    0x240500c40d05102d000e20030f80c0c1d05a51b0312190400d200f03002d8248107984d070f11629810081d1450b0a80e00710240030703448010000d2094100f1018a824454032600d40364104a0203500041203508002d00a0010b55002d0081c001503859000c440c0400d0315514801160783c01e01100c8002d428511903c004420740e050509000d0203481d10101144024180e11b040183c0003d681132010040580b000002c1030107140504000209600c0400710155407426403046d4001e07640c90b1049426594004044c962190024000c130b400540300740e000c1e440e480d11031001d8031000461540005c0c0b032070a0440b0038400310900042e0000c1044400c2c8034031036101c100707142c08040c40d078201004182001002085d6004c441e5a07081e03d00480200c810100c0081d41d032101d0070550b60f03d464580c62817141c1080e40f641c0751540c20503101050110710110078042806000e00908510b00b803201b2008125006008502c813221858403c0c100451200d0240101801e0502c4020500910384418549002c007104440915040040c2c503032106c030b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 863175746 1250 863174496 863174573
    0x10020f0f0a120c24050403030506010f2f07090c1e0e010c050c0901080c0126130c08100b0a0e060f040c02030918040c050a0312201504 59
    0x1620b145103410055039855242c0a143c1000c2c000c28041581c4810b80c00c812000e2007908070134440d038483c0d5030600440c2c0f503400054555114803002100480d50100e03054210684185041c4003126a481c4940250f08040c00035506003002d41d00066502500c4a103030103407503600021440b01901d24161a841d11703801e0f404c030061501825500350317410400300c107000006201080080301240c50005002a225580d20840e0b6960754581e04441c0d804651206a0400c010a840303520010591901c0d22010181c0c0c3d80004142c00c10222403411030f0192003010002c600c0101c00c100102400b91701010000301400c62004201145007942d118070565001c010800120f6101c1080013a0410819100441c5080320350b5810790031400381010040e0000c080400c11a0040700c6c280140e0b0080e401102155040340d100d40070301c8120900c0e800b025100c00061304222015910840008400c8003807184c0341c40001c402e200e400c0b414140d500420b261080c0c100c10a010901c2180203601c0303040d80312110326140c1110381c1324038000b5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 863176996 1250 863175746 863175773
    0x9090c0803180105030c07061b1b150b0d050d170c0306100c05030f0a080109060506160b060102011803020d0f030b01170615040b03010e01090b0d0b130210020f0f0a 72
    0x4004d40070001c540c1c0e0440207810340c3d1140e64800d00a0101c07050180d421482d100240074601e000605c52041a055544449100550b0303603001200d210011426100301c0c07025048441200c1d4000b80c4188160380411802d1103d001003032207a0760382608408820f81c00e10107801c80070744030142c9a1020030900101c0d580300c1c01a88000b1005040001040070702d41422400c1d40150081f5184148000030060001c40d841a10a03051b43c1d900081080190307255000e2062501410102d138102a04040d03034103010030040c60426a2040c0144004102e00c0000c0380710124000004104801580c00818410034507900311103c065071700c2c880d01e0200485180080000c0c9125160f9408001401845003c6142a126242e20700c0988181c080e600741d40d560317200c1d10303509564002d1103040e503540a11000460440014000d51410420083c401c4821112070b458031050b50703034090880d150000861074058010780b1640e4001d41403441e503401418180f0034200e0010304021a101100c40550480c0c1000c80000b10400000391 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 863178246 1250 863176996 863176999
    0x8070f0903140703081b010e011b0809191208090f060a020703092105102c0102071208011d1e09030f04090c090e040b0106050901020c0a09090c080318 66
    0x1011030080700c01c10b900385441d07508003038410000001c80110907044984030883d100041c200030842141040c035000d08172a4000f854003c1d59805103c8a07051a104084840c1c1000c0b841c001e50700d01945078072440840e2980a1700c1103954088003108210b080c2c0d0441409944100440007400c00c55050f46580c4d51220740041c02000126030200f042e0301414450300350400a0008541d405000d200d1041c1c41900d48c40000d0f0003144d15120b07003445280c3c0000c017405410401e10042c0c45511040c008000c1882c00d00401e41580d231025075092014a0204001e41058841d03281b2940302c034060765041c580218560402075880e0041d49030b040c8180282500d2505004460503d04441000f140c0c494007045419446198074400480b6408100400c084a02e80d100d8820f5081503110500c1d001d607a01c200406211080380d01070603000d40c8400400c503650240e4020a00c040c0140b050b5810180c9031000206480e01c10f400c00408140d544078008200b00595140b000034042c107400039800c000802d4a843c091518809089 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 863179496 1250 863178246 863178263
    0x603030801030b060904050a170d05091e1b010e011403041b1202010c020607060b190914070519090b1605010612122106030b0f071806050711030d050a08070f0903 71
    0x100f070301081c840140d444481c40a40117100764206031030401e94a030700315503e00303100c054101d101140014002070ec1c1c1712681c07003c400011024120000544481401c400c206050101c440b0040c40c031801500c00441c45a840341346500d030f403503a4080900d000048181c1000e010100030005040160b07800c0b060322004036a04442c1640c0c3d030304161400001a1807148001a0045800310132401c4264410b02d079542510803055040280e107182c800c241e02415010784450010400801142da89125529000190910b050078000005540c0c0c0e20b080c1c5540d482050362042c07500c0304c00d02c05000c103c02805448010700103103000f21400c00304c5881c0c0850300b441080144040c80400084212407a031190725007007600800c04003c11009549041c801060401124980d00c1041d02c80001001c140c05190051010344070008403c865a041c00420741e50703a400356406030344001851035042d066580800c11440e80c454140d8405444050441014040500c05000142880351414844030840c0d4448510012680c003c1c625 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 863180746 1250 863179496 863179523
    0x60c1817010902030321060d11010f0320070c0801020a05030105060a0903050d17060d03050a0e0312070c08070b07150c18271a0108060604090603030801030b060904050a 74
    0x3818014045000000e42600001c200000d03c04030444011a02d41072180e9a1010380c1e650760b00700281000e000200501d0507a9a03c00c10403035512402c0001151000d070b00700010f11101c54504400e000c8008840c1070303140c0900180c107108103d4500d80240050038484001d509019a944016040d40014050140205008100300c02941d07c201e100714001c42d00481503a849589981b401042d4124101d08d09070310321b101e41c010a1080c2802da61803241a03030140c2e42c060605043d4030080f6083c8200d001030a61601c22088510f10702c20080000b070800700d20604110314024503201115043c551103502c0312440390020302084e00803551203110450022080c2c10f0000d8034400210341910701d88441c500301c01e081d200d4290003080003030110441c0210b00c00030007001e40700102d111070f03910161341d01e101c51001e8001005040107070360350050944c03e81203080240580d00301b0b600d0300154000c5400550003500010340242c0100709000b2030060321600080305440c000014641500c5aa41d0b404c0c21002c0207040e10082d414 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 863181996 1250 863180746 863180789
    0xb0301052b0803010b0409060b0c0604020118240e03030309070504090201120e0f212d030a0b15070b040201081f0f0e0906090d0e03031312060c18 64
    0x407506601600341da031207503181d0408807030781d070050701402c0303103071850044045403142c942c1c010b98480d000e00310002c201b07a0781c1d55401115482c44402e4a601490520714001c0b4603001c0d505042a21281d500c041e0020110305000300510110309460300341d0081e00304006002d240d01c0b001c82c17407005842c2e068801003440c50107480101d403042d485a00d0b4050706440c200d00301000e0386005c1f55040c0015030000854120800080b500509005c003c1c01d451001601009448070100550110203036602c40e01c2e4014500c1120a501840c840d44101ca0004840d5903c003164a941e14060003002070a540c410310b010300f03002c07550780c900f00d15090150020341031100301400625842c007080c0c0705220540c0c002e10000001a07498007000741c569a103004160f04100c85100080c02d101d0002022803103079131090000c0039407808040040d1140c5401c1d94107650980404c100c2d5075040741d2800000c80080c13009040c203919194042c20035800f11410200d00b14100940403030002141400303112000185c07202c8030742c2d440d41c4904001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 863183246 1250 863181996 863182069
    0xd030c08090d0501020711040b0607020d0602070501050c0d0c05120c090301060306230a1505150705011406030d03060321020102070b0c041d040302030d02090f0a030510060b030105 79
    0x1c0103240e0218080b00a542044019000703400c455200d01c92208015465204010941e6011580c540d0444820301003500035141c040c07600d01400b4041e0800524281403901c8007420b4a800f26150340c0d01540c0009c0c60003140c1c48030300c54a040b10000b07141c03241c10400e2502c405040d060001c0d00c6d0420075100410a004180d0702940f1800095520440422801034000120100e100440c11032520240c00d100004800d040f1600420754011101003009160901703041c100030180003d002c1c0300c0b65001050090300d0008a0034440c10710707004103030144a1890301c1c003a000c0525000c02000007904050801a04100140c1410490400a0703004030240380039501c9020102d009026200b8080c182d00401414840c158074a48000d209130350b00d42c413001c100f44090641d000405801640d00400507802000900c800389000d07400341980f100c00521584240c80303082d0011381c005c00030750000d60b056004101303106000701d0f91740324403801440c00c400348a01303661402d000038080c0f40450b003001c0048080a55031170036002c41e00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 863184496 1250 863183246 863183257
    0x804051c120b120c010f0c0f050601050a12030806040b120304150206070c1a0403050d0c030c02060603010b0f0f0d0803070c031d03030a030e0f010f0218040b0d030c08 73
    0x2022a01188040010040c080e060081d101e0000e0303481d041e6424050308000e803040c3c050f0350011004280740c50381e010045030310345a20348511042091701c02070034001a4010241c8031a8a02030001442c540d4100700400c80070860702d43c440000c1c036128900301070009400043c12603210b10100c0c0c1c0001c141c08a4008580e00c0402405000001c0c040040c0106500f460352801c91140f552076421500d01d03545101040e03d0b54406500090000b621554155540781561680168440e100e860306c60304104a030f07400c1406035499084900b010a80b00c1e490000e48660421009030b1054040b4002d01c15440d0380400301d0340c550f0300350361114003900810b28800829200d007030a1030300091340208140d680c0d01e08404002c3c0384072030140c1c0c1100010410301d0038140c001c155a08000c0c03036280040107946820400513041e8002c1c55040180d0900d0b000e02400003200300381c00e201d07d0700c100000b81c50141e5981c0c1074820586c803c4810f0030b031f41c5214524200000045880b8a40a900c4250341410400d04a03102428500d90f2030050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 863185746 1250 863184496 863184523
    0x204050c0f07080301170c0901090b0102070504020c010c08101805060609061605241801090507062609031c1824110313030c050717070602060c0a080405 67
    0x5491030403c020000214101c1d07200c541044012a092a1503645841103030030300940c80100000144006103442d0701c41201c0d040140121100c3c1030351100410240d0300f01c0300c4d050207107035960450300b20b005801c83c061940c000802640c1d0800035060031108031426100c03150000c44035070348400040701c40e02c4001c129082202c0062845807550303481d0748010a103146010b000c41e0329000d002c0fa5913003a90070400303558030403040c0440300203c142c1c2c500750904c084100641010801b5074807a01e890001c10740600171903001d032502d90303105081c40d1a201c2282c45d6100e04440520700701c0450f10100100d898002c4283c910301d41e6580c2035480c1c41b10700e16042001410312801c5103000c1070f00000b000b004200e580c40044284400802c04200c0c80f110f02500b04045400414613820590310420000d03800700711007000c242045210b4105100000c5064440924103045904006404681600c0d1003d01c0d02e8100300a02c010a22407000380740a1801d1061241240141415081444211004101001428030412004419 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 863186996 1250 863185746 863185777
    0x18120a0318050a02100f02030d0e0a020901090e1204030804060e0a0806090102030f09160b09040621020a08032104060924180302071214070b04050406060806010c0204050c 75
    0x7518141203444141c42c4030f040744284001d0031046040c50181810020010f61a0041c1d4141207540c41c580000d402844600d0105014201407400180c1e254110701d8003a02d490352000410740b4502203903d103400d0318441c4e004402c1c002480200001410300302280c0c01d680807072400c40c0eaa0110600403688003001604044ca06006140c10000d43c807105502861042d510301b0b040b08003070f450703111070140c5450000524042c1b01101d11010b11100102800070003101c1c2d0b0203400050b10651315240780002802108004042503011306400d015031a029071100003038202a0041d518151081c41944d502d002d140580180460544c0005002d03c2a00c6e84042c0784560841c076178003050781c3e44032414030881da842001c041c212450084074120604034581d06a00c0d1035416001071a645040c209005079800c2145001c07229280c2418480d04030380c90a0183c0f100500340c03454030685a070300300000c100903510b40f50001001c00c00c00d4001c0020a0b80e001c1c1c480750f03000c6d8040c0c8000034681c4424584507003030312a00000740e81840 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 863188246 1250 863186996 863187041
    0x3501061206090c062c211510210312090b07090906050f130b0d030810061404030602130302030105180613050307290a0203010602010518120a03 63
    0x2001d4100c400d0103481060b0003101c03243ca418045e6a00807424514a01108610138010703148000c120303440154201c003c02e100040b442000780c030300c07540201c240c50381820b0708807000319901440c000c21895000403100080d604003504018283c19046803000c0c0710381c05c000207060768800307150007080354410072503e01c10180036251130307420b0090b54032400b13840c02400204540000034101ca1548159015070707100034890000820ba80c0c00308403030200c1801c3c0f5100d003160785542121841d0b03902c100c0240a280f090b254100146841070301210040c04582c032400c14064419111030b1481d190004940c15240d10000043c2c44403040110441145031541009406620705824010301e41c102c020360303840401c000c80440e1110f41d1290860303c0442900307040249aa8024040900041c0c81034840da140d0305480c1c50002d0301182c1241c000c0003a040c003600c103460710a500000510000f6428003030315510424200141d00351500a14615540c0d107500d55480d0fa80000201d000c0003107911a4029501016801c100f00d12000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 863189496 1250 863188246 863188253
    0x3110d0504060f0e01080c2101121203050f0c0c0a140102030a201e1603030914011a010513120c080706090e010915051c060635010612 59
    0xc0c0d0260081d003001c10451100b103115079100d807003589441ca2060f9520b068589480e03680b00001d070448c128460194103c0800018103210f622240d9001f010300451340f540110306401c010482403403030010b9000b098200000c2003660508080c46541090405190070703600c8074000b403441d040400c0c07410001e20041c906c080a4503003403815005180640002da000300030041c5c1e100625100e0b50109207109220340428451103d048247c5000207040760b0070ba40c2d8903880c28055000919100600c40300840109655003043e80900c4071a4100381403e203a0107000b04105011301034402181124110503a0421a0004442d54080c0c04614072400402c150400c54040700b03075a107000304403400c2d01d0259511510402900248803442030004c078040718145c0e0440034950b4288034010b4007501c6080a6101e02e03500642c1c0010b1607407208400125004924410030100b5103481c40e112041e00c1c607503842118641848005070701320080344040c0c6480503180c041001644d84481c0c2c20140500791980c030410005006c101d880051 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 863190746 1250 863189496 863189507
    0xc07030236010503070602030a1403090f0a0615150e0405090c0411031603050f0a1802060301031a0903030903090d02040e07150906020d12020a09170a05010b151603110d 74
    0x59400c111309580c0000d0711800100c2c1d407170003807001002c0011102d0300701010b01d200c654015900901900240c840303000c01312007594540141d030107044481d030b0360f5150302e000c24005000c0c01401810b00c01917a10056440444001e10308904d207071400313200d1582c89011035282d50b41000303040d1030b4541c060000d0051030444072103004aa082100c0c280310701090015901c48152080c481c0d82e00c01c044226101e266500e485202c0c0c40106007541d461281103184480075005030707440341c000d50300030740c412080600c440c0900300000c04803180162180f5501d90060062000301200401501c0014000352011981010700e400002c0183c180326402c02c11f64041e004010406083e02044048441e9042c1c0b0b80e920340940e01d8401b207948140641040700060302d5800700180350307500c40d00107040c094005d1074840ca4941e2104c24210154540342107240442c0d00421800301044070a000c1d40b01c880b0011a03801d14500c410805000381440740e420038002c1810b42e880b1240030540505400d030044100c640c1120304003100920003400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 863191996 1250 863190746 863190749
    0x506070c060b0301020a090b030406060324140403020d0309021f05030f070206090601060809150a0f0b030a0c0306020a02120c060a14330d060203011a0c0703023601 72
    0x52003400c1c0b682d4956503040500890741244080e5581118a41c60200390000a4002400441e0b110351105800004644c2007010288000c0034025070b07c01224164410f44100c5209010500043d441001044086900860801d208070010304000c00d00349180e01c00114080c4941c400304441414400711034941c03030380c046e01031442462090200f80064854032000c0e030303841400700e07102d03503181e8001c0b00140260388c840c980c2d40e5048100c010031107142c480800020508510200e6002c10b10503950840b594444000b809900400b00c016009424410003c5c2c031000709542e031900015100c1500001c0b1b0709032580c0f08100139120209102c8a1a4407171006c48042c50700c603041601c00800c85410a50300c2e07648c9420030805a07000c3c001d00203200080440c0c00b062946480c0c3d6404d440d20510314005a0301d40c56881d1000c500324082e11458005a40352b0605010140070b5403092240b003c1c1d000144807800080d500022240183ea40403510702d4103480c0e210240c51200c503440301d04007490303202000e101100044130341000d50 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 863193246 1250 863191996 863192003
    0x3090105012d050616050d020604060f0605030a1e1b0306111603110f030d0e0f060712050402040f020c060603010c020102162004022b060e0f0a090506070c 68
    0x4416041c04000c590b03496559854601481038012020042c2e49009802020600f4103004103032a1541d080d140d041c02d00e07000030f8035070001d0b030041c100300005c01c00341e482040b80254000030b00b000f003c0d05250100c1e0b44c0b00c00c0000001e00040c4024450540162950440305000b580520540c003140600c20380c24520300c0c82e620040b1900d038100f140c00107044510506a0310f1071944041d1080308036046450031102051a89a48070041c0500c540000002c4403c0c0001c110b1070b00e02c9000851000d41105520380740c100c000d00c03884800d8100d401481003503540400018400d00c00d042e000700b0161070714000140149010300519440901c0004c9000b042ca41c00b150542c4204000c41c001c01c0140100700090b4240c3c425681e036000340840190501d800641c0d88120802009941000b01c1c0302c0d0b09020010404030b80c84008490501c2d81030403094004895102c6406501c0f000c0004c09101481c0b030f00c0381c42c2401d21310140c81800708200240000b2000d030103079031000c080b1a07084400c17a401d0342404403001d0006041b50100380d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 863194496 1250 863193246 863193269
    0x4171305010e0d120c15090b06131d01020703020610030c0b0d11040311010e0d110d050a02030307050a0210090b0301180e100506011202090604030210112506030c1d010509060309010501 81
    0x10101061b007071040791441e0360410310108240d0749420801607000c0c4003c400c2c0c1c51569032064682000c4102c0e10480d88804200d000060395242181800381c50000c00809040201110352014030000b640220500100d80800a40d0768544907607041000140c403000c1c82e8810311301004074001050140311011075000c14002c0c0c1742c2c0001a2800b2090001901ea0480003925060340d0b151550782c14101020343c6084503004105603170107880c1690009042d5803113150140d8065010101c108154640001e07021868926030900c3c0404510700514190113000c1441600d848003180588000c0e408611342002c0e5020110b0000d030740865010354a51001094142da24030f000860300800b80303104a03064402c40e440808020001070400b4a036078204412680402e80080411003c07001903002c100303080000d140c2e00c1841c07c84441c075544483e081803840100caa8030010405082c01c00300c0c010642c01030012840c00292030000408100c3c0000181d41c144501c0b4181b80c1c0080b40003081100d032403811350203a41603c5450118 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 863195746 1250 863194496 863194523
    0x5180c1909080d1e0302191d03030301141804050a0b060d02030d0f0e0f1e0301020f07080307081608070c14030d050603070b19030209010e0a0801020304171305010e0d120c 75
    0x1710200d020b040400c1098011800032090010300400c910b46030170032407810369480a0445404241150003c1e0300142c4d0010008410744c10030718006824190444811250500702d280503102d6075519200701314003811400380318010885640310106480005900603080b6554800d4001c40104480d0701d42e405000040c2e50b41d40006040d02e00074081ca00104002031074030703040754000500c406180c0c40c2e55011903132545d801c201c200c68007405100075080d002c0c0aa0301e08c90712450001c4001e07182860080040302e400b0b002024003003840d5000000c0300d0f0403560030302d0461100c2c2c03800e24141c10400825020203280c5d00c03000c6003110711586da58002d14443c0c80240c0580d00d10540d80c00d0914214000e1810580704d0340c0c00d00c02d0711041e20303119a010741140041403610b0419480000d011884c00c122507000380c02d50b65000410481070214000c0030b90300d000d003000405441e08000c02c0b8001150051400354604014641c40c508002d9920340800c400d015801600c00f8a0700d2400a1000d400d07041100400c0b1610071882a5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 863196996 1250 863195746 863195807
    0x31206030718050a0608060103030f020d020a0b19090b180705030c1819110403020415051c02010c05060a051b03010b030a0506120d0905180c1909080d 66
    0x70264100c414040500001850304031800020302002455800b2043d80d602c40007038403540400050f0b000754003c2d06c0d42140810070703081c02400c2480681c0058190350080361280002007000e4a8642e2090320744982c00640d83c33082a4101c050a0018006400400c404c024080303a41c0180301407000c035403101e000b120802e07035540e000c0c95124070343e000045034080356114000501035490704445501c211103150b000c080000500041c0107c600540e10820500c0000c00e003801141414407481e0180849440d1411400d89031000295410340788060114802c00041940c1045902400010006942c00710030740f0b90a1600301488001407000301c40d0000103202c180712010406000c238045038107850b18101c00314615510460402c01510020348403d030401510364071300103408014002481d8440d0142e865030b804900d000100040400d00d6a650034005003d00b05114a10104808a603141d61000e00c401040b05035510003074805e04000c0d800b030002c43c0954200c00d102c503540000c5d108006011081841c00f1214083e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 863198246 1250 863196996 863197003
    0x1515020a050a0f0c17010c080c0310090f110c030924031b400807090b0414090705041d0c0d06020d0f1506030e030a1d0d0503120603 58
    0x94001e052600314010601c0443c2e035105110107101c2c003813007103242c40507560065aa100c4070181c00c00e0015954407801c6414045d4402c100a0b004064030001c2811030501c946032900c14030f46482030f00d5015540305911400340d00160400784010684203119a203039004013608a445c0d5001c04041441b41d103408506001c0782d840d11310015518000d103101e49040d07a8880ca0f486603560710004001c004824144005c0445003194480c00c1c658080f144585008a030140e11035500c40780c2000f030140001d20014000340095400000e101d41100c0d4108404a03080580d003010400034044195010290a203c00802c0000c0c000002c4a204a5405940400c40100039032704000d2003110041132034009810a250740c02c03003441d018458240140c080c0344014500380c42c10880004640a03482c0b03140c1071607141d402129001031091640c030700070040c1c0e0500f4010480e03105549500d900c1002000000e20542d4641b1500c6900e541c0c12499481c2c1380a000c0a40c02038407802c00130f65031380003080701c820706600c0d0034001550341c107020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 863199496 1250 863198246 863198263
    0x70c0b120a0902011b2901180b0a121a070c0c0939080108120f03190203040b0402120f3f0304031101020a050a0f050c01151502 56
    0x20040c88105446000030762001c0c0c660328109904000c1101c003510452a251801a140c0f0381c450b120814003002d20703040d840c400c0318100e40e07514155580d200c01044003032416010b8000d505601003000480200e480e0006100b6003d640040f90a6a4a000880100205c1050010000c0c1032000114480e40d01e20070b08035000d41c280c003001000d0071a84041000b01341665000358400c5c00240c110031064821a4207120341441c401c8441200301c1002800300f0f1000d503000840c07a405400d84402409041400040c1d5a4041c8100c03940780340c200b00c0020008608500c0390000740e00a0620400c250b650703017810704041e40311010507141a0b01c03801c60064520800400020748000c460400300c05072038100d05810303145c0101c450340382910000c180c0c001412840c01080c019504070315903000508603124281410003c1c1907008402070a002684100503150f007032600302c815111001c074645000416952842011603542c05015001c258960814002e0713200081a41a17410a0761121100d281e40c80d61040c401300d82d00c4141 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 863200746 1250 863199496 863199517
    0x120b042a140c1209031504120e010c08040e04021305040302061005061305010f091a04090b090106020c1c0506190e0c06090d050304240e010801062f030f070c0b 70
    0xd02c3c0b030b00414803c0d180030700010f81e0003c00342c650500c1503040f0070070b41d120106c40032500c0d15000074520030345a41110b08006420802c1c40d1180c428100c035070700c00260340f09600030480e0106440d000034007159a14842c2a04544034030009200c2c5040a1034042d544110a80d20b1b504407240300c050102c0e103410709409a44021140c1c1940c0c2010b546060300542c2e41d16031069580741042030204d4041b84003101d0b10064484100c1c1481c18559452800400034221501a00d509220798050401004002e90008a5001c0210b04a4040c58520b800c81012500040707003040040c540d000d00381c208540c414030140c141c1400c400c41d500274404411404030341c644460207c40190360144003404a0716040c18a25081c251461040040364a85a03c400034446c0303080ca6141c0252141110768401481c45900c5003c0d180045401c0c203107503070554142a03015040c040c0490074040307134005c003030304041251070841030390001c10f5044401e980d90780001840311b00c1941e1048a06503924000140009200260740040710307a440c64 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 863201996 1250 863200746 863200753
    0x190c020102061621021b030301030615031721040f0b1b0409150b0c070906051f18030606080321010e010512070f0b04080d0f120b042a140c 61
    0x203c1004803484030458203405440540c01e209201360f00300e141d108440c6e0805140c00554a035850b500d815800d0316240403040081030301c48a02000013950b00d95140081e0041e0080c007507107610303540301003940c2680e42411111040c0b51300b109100a011450001d0b03e0740501901000303802c3e03902c0c10b112000142483e0a440740305c000c100000c00050401781d00481074014040340e4280e54a9448030030800c00e400040c9404596003080e00708000a82c0140308400080c44262000c841a5074038102094103814004031380000c0c041700090468603821001c3e01000a5503000b1000c11500781c81d0003445542c7c0d0403940142c9850113024130390014002203800d03480d04840c00ca5a142c9083ea0800e03003807191903500030301c070580c044c400c1500215003900c00e400300c5405402c0e0701043d240c40380c1c64585980c1c60301d20800071000c00e000100d0303a901d241039403148402c00c0c00c01065602045070303c024002f05006000540e40110303410300320180580700440c5441c404c002c00000d036480c01024480705440c0e0300700f0700c2000d1141c2010750 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 863203246 1250 863201996 863202017
    0x1204032c0111031606050609090a02030a02040911030604030207080115080601030f03090e0a0504060f0c08010e150306011203080928170a030921080103080f190c0201020616 76
    0x103200b00e03290400c0c00c1c50720701520700b400c10b0340c0ea407803c12100010084801c1754a40c0f0802c0841d0a00c103480301d51190800008040e140c0311b9130082900c174080c500d0040c5c00350b40c4480e280824028603400e081882e40b80a012200c1900d450706000b5101c02042c05050019420b224031003a07000b00007080780d001d4607525000340c022a46540e0356544020f04e403030000c03814828070040014200c001020f900e4804e001080b004140381c9480d141c107108642405030300448007441c0000050a06910013401c0c3d0665044413209045603c4280340c040000110b444c403e43e01d44914400070941164218251b0581842601c40c6071040c0c0346c500002da102c41c40302075001d262156103010242c00c00e05001030090040e00644003144003244c600e680d00d10983c024000354000ca0f8480c00c1c1c140800008550b040700443d10400d030b0414031680c92100030458401840301400405000c1100511400200f08456a811035011601821650070303002500d0044030080507800350141d580090103a5080c00400701702e0002039038804036000e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 863204496 1250 863203246 863203249
    0x10504380711130b06041514181207051c061103132a030b071205220501060f0f080129010507260403060b04090206161104021204032c 59
    0x16040005080c883c582c580300c5980c01c68881100038000361859480c0b0725030710f4020340ea01034605400d032009150a90020000072040700115410100c552104a8060182c5442c110036107144c0707006e80e0003841d407020050810051007450190304280c040e224000500442d420090360b00707410b00003140e6010400000c9880240015000702400c880781c1022403002c0c0d4100c3c61017100910f4500c07182c1040300e40a49442c24422543e4000040c0280100303103450030b2002d494103000c0c92204005d040000504902158148402c20000303401c040c0180034550071130040e043e80d0b943c04c1940c410042c4100142d5500c1c00020100b003400d07400000344bc80381200c0000c201c8a8919004456660000340203885805481071480b1601c46c0b11421120342007460030303100b1345030f03401c606050f011600e5118503140704500c0e005415006864070026242d4120101d208075107507460ba8100f07140c0d04811780c40c989a0282c400030307059128500c07410040c0d0141e80243c3c1c5a01c2c50b2284509068400f507181c12191b10100b2820b40019004d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 863205746 1250 863204496 863204509
    0x6090f03030c020d29011e03020a050105090111010c0810080105010303050a08060f0a090f0f0e300703090e0c0901140c01060801230708010f090b010504380711 70
    0x4851144903544061502840d01140c1c000301060820005e09190004110140780c55514601844610018940807451980001e10041840c811113041c4400407400f408960b0065a544840c2c00c0c41c1030003440000b000a1000704010001c40d045940c0303401a01c404103a03d0014480c07141a80d5140d1101440c02101b800f06469078803005020235405050034143d1a21912241d42e50001031107a0a00424400c0c0365007001c00588604280c0141c8035494028a50b441101c00600954148100e444010901031400d0384000c1180d58203060300d6100c04000303201d004050340b14a045086500c0545600c055407140b07580d01030305104000cac0c0700d070004600d142c007004810520346c01011011101e000001d0700c10755500605095514056141c0c00481c3c400114552019407400a6507129240c0c0c6428001907040085c03a4414203894050303044070645e140081e0202ea4041c030304542c003824500c690302900d107480711072640c0c404a05440c0c1c0b40913449001260081203160703c05942802d0791201181014408c007009000340e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 863206996 1250 863205746 863205769
    0x50315060409020a0201050a0534050405030a0c03020406060518012007090f050105010302030c1b0c0622060f020a140111070f050f0a151e021306090f03030c02 70
    0xd02000c10003000070414858802098100d03142d13000130074145403000d4071000b00d501c0244525a4001284041500d504411503010f540d86070813001d03000d92011401080b200c9000d40c1c0c000700c2d094800c48580505004404548104480c800c440030300c10f0a888203811a130718000c2c3c0d1460b0068045c10442e00707200b58054500700c05002c12440044000c15207800075185000c111794401c0416a03962016800310504a0007414054142800c065117103080c600c15034001032083d070054090070388040120640e8800280702c1d1964049000b041f294480594101c050080f100c906529840e42d0200da00000b403060203801e010402c0041a00a0410b10a190325401e00441021940f1040b039541d504a0090407400b040c0a0700c1160b02500e03802000720000c0c9440e41c986841c45414051507070020b00400006000384421185004c46004042008580d221350300c407110900140c2c03100010300116031005403035080c03655203007103c07c0ba503640855560b0300c0000c041d50140c20701014000940c100b04010150900501045 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 863208246 1250 863206996 863206999
    0xa110c040612080318011e060b0306030303010501050304080c030304082503050910031107060b0901081b06160b0a1b05040b030a1d01140604290f180a1401080d050315 73
    0x1424a42d21725503103421a05c0072805600c0e9031505101c2c44441140d184640c034050240380170504e107581880400242c4c3c0f400b051242904120000000904119505054542d48607405045a4a03030406240015090300b00c1c020070340c842c2542014184540d100740292000c259010b8480320320b880c1000d018804605e22018040d400e243d10340c0601c040080780c10000700380b181e000740070008660100e281005140c00c0c1c1a44440ca0390fa024001c840c49064a10718407070464170089032401d540714040c414900300340140c002c01800074540307841007041c2c44219400521500902404038903400c40030070301c140c400d4025400391362182d400030700010b20450420307801131790072210580c984030100300401c001d542580d00c82e80000c49850221000c0c0134603404d240c092900d6641260714044601191885083e050340c0c0b8140d03840b40b1500c0d0700c10f244011611401c126001c0a0b05010401c121441c20116071800351500d5003607003404000e250000101d5030404110f11203841030030354606165496105000c2100031552070042d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 863209496 1250 863208246 863208271
    0x40c0201020c1c200d1d090712050108070e060d0f0c0b19090b2b0f0b090610050a0804320705031f051305030a110c0406120803 56
    0x60300701503403c2001c4428003a00540110b8404904600200030399420880382d100c4010310808000300b41008551313103080ca456441c181c3c0904a06107107614026031040303606500840030780288003170245d00a022801810100340c0500050740c1e69184c1d00d9030f51440d48998408581a000407400926201d8100708401c0e000356a8400c0c40c0b0201d486010420441d5405000c0781c000000744842ca11903161810401c9030103504103452211705d09821044c0d64460708903a6141440d003081c80d02d00a5100ca42d0310301e031200c4808010801801e030813504100801d103180300e05119800f0307603001444600d40b031041851800e42903617450341000400701080e549070703101500448100c4040c850480f030151a21480120030712807002c61240a040c807000030f0307003070240f20f820a0b4020741028045c4200490041c0306060100c00304500040d03140c0e180e040d8641003280300900201103020001c0d042c0000346d440742c0d0001c41c2c480c19006031202032090360104011603000707204902130b20002604c2c02010440c402c0c00b45a1102c032002c0760 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 863210746 1250 863209496 863209507
    0xe030f120a0c0c0b03130c06020703390b0d05090105060f09280207110a0b030121080c0c091f090b0f03061611011a040905031623060411040c020102 65
    0x1c04075542040702c103a081c800c0c09103c1b1100f40102e8842a500904240c0040c000050446d221098003030914044403400c5400c8a9240c005100c480e01c0301e2202a0450411500d00c640f600007a1156070721a4420364001410725000c40c0100106204180c041d13600103015441c4240b02b602404080c0b90010240c20101a1044c9890301d01d24103d250312600e0a04002c00595900c0320b842c00416518607641e43c180514521402400a82c050f482200d0544131304030398400740000c1115920ba5120800741d030040c40b0302d40214440e03058007000139500f544100c00320380030310f030b03641d42c02d10401d90f191100e40c8a8000c400740e8020030046d81900d54086994004c1c05882c103030318410351a0100385010000c0c2c03441c05e050071401100055250b80940551242e0700220001d008221082c41c800c580c6000c4102c1452045a48044820030040100101d03140c406010000100900c240d0400c8490700f081284c500301359400f4102c0c812a0740001058061007a40c0c40b00d85a800c0c82024030078040100075291400e01559800c020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 863211996 1250 863210746 863210759
    0x90f120a0c031a15090408090a030c0305030d050c031018110315040501080c0303040e0907180509061b07150608010e030c0c060c1c0306090c0e030f120a0c0c 69
    0x620700594011412030010701110801d5103503900d802884103803081d6003a1301c42d0405a442000c425040b40d0000700300754840c0141d00018a00040e40c3d0301c01462050402400030030400040041c01070719a40c82d00c10071080e56910031010751031104685480020142007070a000103080714082501d08101810b000588440301070304089282d00a41c0c0d07241b414205c1e50501c0c9a140351501515015021a10203018100c1e001d01c00f00380d40c1d00032406200702ca07800f4100001c0665608112900c028001c460040c400008041c15000081406480b075000600402000507480e00c0d242c61048441415481254500310080d140d410882c2d001c20520700c13407662120b00c0010b00f0705090040c02d50201c8200003640d5501600c0389240c1c9441c1c0c0111415002d000705121600200308003040d00044080e400c50740350000018001d040700141798a400c0750345440d19142702080e82d0350b440001d80e0a108020340072034141102a02c3c106949002c0c207a280c0054500030065108103601c00d51810f1003a0303110f01d0985181544500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 863213246 1250 863211996 863212013
    0x30e15070314010b0d0c050f071520041a070c0303120e031306030b0a0b07080307181d0f2a040536060105030414210301080111090f120a 60
    0x20b00c5400304000c0171988441220b4144241c481803810341c1426844d140004914203041d014555020f00480a501c5d580c0403446901d412040340103120403400d10440c0680110310348241c0142c01000c007840403485035035062038040400c58040c55000024a0400c500c2c0d0b03541210080c1510842e038841d55194107115500d56403c10241c19840021a18220b1007401c2403001400c0b40c01d440e107070602c912200f8078108002c002c40000ca0324402d8001da60595680d403161000c0d10408120b00c48d030f411400b03095500140803003060380e4040a080311590a009203071200f040c0100b184a0566100c0703912901000702c004180c801d481d40041506242220508090b40c60000442d0780303607241c0003c0000c1140d40318011403105130900c2d1442060240040d00c0c5c240c14070500003803490000a10003030210f070580d01842401031081010b0600e0403803e06c0c00f0841e10103100f02c026007170f030802e203d095815030038400440c1c2e0788484d00d015124654005007580ca450491101006000300b421840264a4040e4122030804140d810303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 863214496 1250 863213246 863213249
    0x606050f180a0e09100501050d06020705030708040905070e01030203161d040f060e0c070507060e0103090206071109070c02030606090a020408060703020715181b051011010c030e1507031401 83
    0x1109540c1c0c00c1c4c0342591031181001501005e9030382c1c41e498000180302e240e8500340c401441a070040401622100c0b2850010b185103e80300d03000e0286100403400003401102c581245115220507610602003540c1040154240d000c10380d0240f0b071101070300402c0c41c6010310405c06000c80d41205403040e4000e0000002050490b802c080c0c00c1c910b000d81b110818007010b13a13402000b0f9040294940481d103007548989030203803521031310300034241044920069110a47e20075089486170030380040c00d03159181d04038504911001e66440042d80943c81e800f000424140c0038515a924854028014102d190390300400c102c40070310000d0900105e55824080811400010081c0d144510040e480050f0b94140300c2c104480ca021509440700001c50400d5064915031041d1601a1407103540b102560301c0c000344101109001d070525404c51a000364039090803a0009a000c9029412100d4860007086401003144046003583d0700c850410305030f644440c2840c00c0c035034217034001207038010303564580020a82c0c01c0011241c2040310a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 863215746 1250 863214496 863214509
    0x151201020d0608070602060a020c030f18130605150c1e06040c050910120c15030609140403050703080709050d030e1314060f0a030206041e06030606050f180a 69
    0x4200d01019100d0780c814100030309000c2008140b401d150034002507645000900950340b0f00e4003c5039608540340104140c030799401614507015110f0010180d580002d448866080f8031a51300c000080e25046440d103da1000c0c1c84018024208038840080c0c210341560240404003007030700c03961108080142800d036400d111014020050700c10341c10541040c2d05141519001540300300d0b140f5050113080c080100c6440100c1d4070041e24160800f403682030100e101801039011203080c040c0c4681c1360249540c140e0100c426208480b10401c0b5104c82c2411902050a0481c1d00501040007002000013081c0507640c065401800351a0001c01641c40b4008100d50140d10b02089010921004030100700d80f80c00529010740800c42d98003080500500b580b08508075002034002405002d03090b401c0b1050713450703005440e405542c0151607199550f40d908542c0c0000380c502c80e50030403000c000d0940815854420f00804003100c8043d51a682008810b102d40030311540145a107000703101108608107110344945032031000400d039 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 863216996 1250 863215746 863215751
    0x1218090108060f07030e07030b0c0c070e091603020a05040b19060c03030b010518060904090501060e10051905010302130302041406030601120b0a0504052b020c010e18151201 76
    0x14800083c11400801502c8070302894109550041c0c170000015844044940044148107143c81e114000105445200700d101c1780d40c040d1102c04200c80e22a0000c0e5130040c1400800c0703c90091464902c050001000c7c040298040c820340001c1005181070340140180d20001800b04500e5404036802000c000d1803130b0300410208230140c05410500d501480f03a440307103180030700300540341c140d4050181310f520721030380d070300358803402d008641420f040c2c9940c0c3c44040801d5100b002046119110683c011903c00b0480300300002500c1e240011560b824490300d104500e070b40c1c1d03d5103101d5050402e001580a500443c20100380107030040070000150340d550044003c15418002c0041c19410511306240c10301d80b05802c046480e415000b120000030ba00d1000352035002400d05070020360f50300c03285001418001e010080403403502c0320302e10001128158032500031001c1d155408441c201541c070f000541d8a50306c52200b42c4d610051025071188124103801602d0b5010340e1206014001c844107d0000388221031540700d000c510303076 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 863218246 1250 863216996 863217001
    0x4060c0302120403020f21070303021b030106031a0408091c02041a010203070314041e06030e07270f110d0510210c1809060b0a08121809010806 63
    0x540601c0142040b0300d400c5412071a090030754011584144241100344e0003105a00c0744240c000c0920f400764040c00d580f060584504c81c0d0b5a080096940072203000040e42e94640c08244200d915051040c40c4c01c90364400c401d20450490850070201080e00200280c40e1248100b20f03070212650792071020b44020358180da4503038010701507006200803100c030031104c40d810061065100340107a800100780c481e50303640346c0b80c03101c1205030001e0f2402c0540940d6000348106045001c480d00c03500c42650103902175920a070b41c04c100100340e505c00d007540c4983c503114480705410f00c8280016604040b503c1409038040007180461102d10000016046901100c81b4007131160010a504c1a545250f0044603041028810752004150406110300d541a1420140350544400c400910342005180500308000303101e40c18448400c00d4a544050f0301414920908035030691500b01c1c4a5410303d442c1c8043e82c00c0c7c400c4c4100800c0400b0321520f29080700ea200485907118890700b40520852075507210308241c00f9011040207460b107030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 863219496 1250 863218246 863218253
    0x5070504060f02010c020709020f04030803130510090201080c09060c120316080f060105031305030403030804060c170105091905010305010f18080f16020409060e0610120615080304060c 81
    0x1041c040b00c111045904243c0c001c102d840e07000952209564039004016038507440410102803610507a840288000d50100400140704e40301c000c600300e42030140c001c0d2041210031258050460759180d100901040340e10300400c1c160070091024010010024041a1801e00b008600d030740f50003c05880003190000000400c5500052036500500c5d070f644a040c140c1c040c0c241070203000b03040c01c0010300003410800f000c400254000c0c0d40101e44c0c04000c1d000020350350788644030308004050100c2103c00f40c4809003080c08011100e803181c00020b1522134821403111480e400e001c00c202c0340090203801c511520300d100d4868043c101c20746c440c05000714403801c0000b0b0380d001034500707003020745da000c2d00c000b56030601c4040d0b0000401e0446046414a411201c1403a0740c41c03000d102681c800a00c070347d03000f0303402920784000038040081e507a0291080190100460b156a994094040c0440c2c02500a540b1044940ca0304100010820f411080075480440e0410300c42c0b070388480c40a07146030010340c0a0b0700003855000060090 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 863220746 1250 863219496 863219507
    0x2304061a180a09170a0314060f030c040e0120071a0106050a030b03210903011b020a060207050a051606030501090c090e1b0c15360a05010507050406 65
    0x110006451181c1c14500c20104004a418000d1510380701a48a034a00c00130495000d40000c0d055400d05000740d120300c41d24000400038440c18242400c65800300d0041070f050b282c441c82003400000010300504152a1200602c170140c400300c03948081d150748403075016228600010300ba8030310130300c1411040d031100991308200174815210802040d022002d6401070012980c40002c0fa00d144880c1d08011480c4600d010110703141844e41a504c6490ba00d078071840784a094000d5000700340240b4201c000f803050500c0b2040902c03a07620f480e4451805603000c00e00700c00c006807254015107403882c0164261000040c0c1620740509161344042d008940e000310aa081c841d154241c886d590150000c04000c00c0807091181000d0010001070255007180180c03400001c001041d80000384101041c828500c3d610b80b445514000e96651544840c134429109a800041c49454900301000c0d01120105c0c2c00364600d0050182000360b520701e10150a454000c955224011440074082c0c0e40c0110300d00d83d2416980d86c40d24400802 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 863221996 1250 863220746 863220791
    0x70f02010b0f011e0c080a03091401050c03011a070210020a020a0905010e0415021e041811030c0c1203090303010e010605031608151206060312070f06230406 69
    0x110b04892200e84140d40d034840c012455500084007800da0060540000b0750b900b41c01c1500090070590002003032840c99605802c00c004407445049030f00382c4001800c0819090b542c04441c4c81e807421000744010001501030f200f4000e00144002180742c9011038a0300070a41c01da211460990141c0d20040c841000c500304680700f0001001040c40c104617650406110142e107440250000c2d000c83d010121290703480c20b1550481da110f50b01011141c003410102c07403180742190082d01c40c509004807440050384170503250340910400042c3d80c1c41c8282c0345503129502040541c11001c0000703500d1141510900d0004a12001103000d528080c0041d03440e90301d4104074a54405050304103004108040c01480401c0134490080008240c1d03508003402903503208511501000180c0b00c81c50b5200b207071031030b002181030300c0070400c1806800150103607140f0401416043c0082c1c80b41d8040100307403612909008001c900070750302042100001c656181d1000c880082c1d141e4030140103403005d440407540d4a03260020301c1641344000e40c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 863223246 1250 863221996 863221999
    0x30612010204081b030307030203071113090b01082419060b040902070506011205060402090a151d010f0305030a030c2105090606010813020f15120906010801020f0a1b0605070f02010b 80
    0x61414005e503230001e441c0c4c060483d00812130707c0701101980350350f81c0e0400006090001503004209255607400d01441d809000c0c0326074001c5000d1408030b02101ca02c240ca1401c403003803d024200282351159002c131080b01180c580c10203209669960300ac00d10181203001000103181c0c4100140e2154402e0502c40d080c500180e003ca4203d00c0c1d00e400b194005440071400680c0300781c040b28a100d41c0c0c0e03a03041e0350760f000d004038645d2001400c81c010004210b9110b03c0c0c000b2604000404110340c09685c072602c10b4960b450711070002030401d5005001d051b51982c407030f03001000b0400041c034000c0900311080e4a001d4030320584441c4020156116010084051380c10405140c1c004401d18101c030300c40c01d028002400001e21a400030380070316241c45c80c140154454030703c681241c60002076119580c0052140c100a5041c040ccd5114030307030b402070900000304200c050080d202a8410080b2281ca00610020b0603240c40c0b900c0c407410740d41100504107110100303071240302d11442503919444124034400300c04070090840303400d940c085 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 863224496 1250 863223246 863223253
    0x501060e24120103121d0d0f080309101d19031e0c02090f061509060403080f0316050c15090c030a0b060103061e0e071416031202031605030612010204081b03 69
    0x280444108036040d00c001e65021f0b124070b00c8020040c00c0c00b14510600840c044c04005001060011401c4001060303a003441c2c0c0723440d04002c8259501d080245035240c44100b60b43c2079000c0201103104240e006501508280300e4105807002600070409000703c00136126554000c208083c50b03140c15420201a940d501032096421b840301807600200141e40c40c02c403018503002c1d000c0301040d40803080e00c1d0a03088601654011103180c0c3c807444224201c04080d4406c0756070300360098912114580c078134000c0040e03135003c14101d00900381c010035145100a20003002084842a4814044000e242d6201804900240360203409105194500740c0005400d680d039650084090201c44002a4016420f1181d5001510505050580e09488413502140e00c0f04c1c8070140b038034031100b0025102c101c0701d16a0003c15a02480b03a00c80c2d00c0340300e250208880c105d0000300d40301c002e0100c3c80c040481e41c1600c20030045a10440041c00c1c1039012401d0801c2c142240c016030001e45555010700c0194039a41e8401a0699a02c40c0c00c41c003c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 863225746 1250 863224496 863224517
    0xb18040506011d1b2d0315010207030503181503130c08120d0c02120c03032205191407030b010e0114100e040603021807030f0501060e2412010312 64
    0x4003400000600b04520380c0700e808920500c2c400c040b45c0310880104c5103022110000000c44041d040d0035441a682c4a071000341c41d03c508030040d40049655170499400801440c1011010724120281405040308a5132001c41d05840f4803c06103000081c0d80030303454240001c2002030040c070705402500c030a40c000c01040d0b4408035402895404134070445e6808014201c1c042059a04808240e1034031b441071400c07210384600891840c1e18444004013944c441e505461400c1c0209070580b85020001003c00c4000c1c00d80e1308010304001411800032840324011303104506407921103124000b80c9003010500c0d00304550700d00003000100103084954100602514410ba802468440c02000050400c0710010690061280401c0381140550b25588031744000c5402410fa8000000c4031120b11207140b10884003000070a281140c00041c6030468401d20b816035009481e8034880c080c0d01800c0001c0c0c1c80d0008000300a200d000100c28542200c0f03030000c0d0604801c0c40d40034002550552800e0300a54040840b03040070803104980c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 863226996 1250 863225746 863225761
    0x608010b150d060902070503190c03051801110105101e260106030c1401180f0621060602010b10020609070909060e0106030305090418020d03030b18040506011d 70
    0x29821005000c1125542e55205100702a4082c20041c0d03c804056440440c070001401400b0000707007e0b03480c142c205a840c0856690060300c1034021070001800181c02880300401240800010800170001410800c02d81c0812040490a5aa048818070707000036500c6001c10a44c42c070208411510324031201803c82c03c40c200742c411441610403c00e48064003918161742d4403074807000e600041c003868001d07400140003030f00c0302c154102d0031040d01c01d10350000f580c0c44907640d210007240198000391151880c20300d43c8645800c10485040343d10101c000400d00a001c01003190032030301c0c27203004003c100c650004030360550002e041005100c020f4890a0a5400c13420070091700160201e0100c2c01e42c0e070011030000d040c0350141000d00c0180a10108010558a07010010041c150000003426291000302d400380155803800c64650601000032000039000341c004199130001034043c1d003001001210242c07645450031108011800c420700c0640382070758160082c8005100305003419480368400116400f4400b040e05001d070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 863228246 1250 863226996 863227009
    0xf040303050601091517013c23030106081203041205090d060b0301050a15030f0201051c060905060a08150c130b180a0609090f1407020303040302010608010b 69
    0x50004040555400c0060b005078003c2c2070000245c40941402550f80c1002e0401419080c910900102a5010034000056074072655540024442005130311880c51444551002d00711484100d5240d40d400180001050340394140c01c1c510610601d200168100f1000d10040c0350031a80c16400c071305142d811031148807010110400480750025403007240100c401071908011181c501032035483c00d038003d0200c0c44110a1111940111102240c02c4000300850744607103880c2001c890f03001f010500c00e10000c110030401310b0145405015501d004bc10180d19000c084010280c0307000348041040c00c0b0540c1e40100f80030084042c415550301c2030041c1c81010420f07051803002c5546905400b4140612025400007031600740c0303440255002800ca0700440700181c1c0e01d40700c903030021350055008460816000c00090306149881d5035010211420342e1038040266003019082c3c00505007044400c00c40d40d40300caa00c00030b0701c0b07a4400c8141c81180c1a5000e19141e04107840d000303083d12819800440d143c0e04241171108255030b0f5a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 863229496 1250 863228246 863228251
    0xb0a022503020c0603090f1605032a060a05030906010605071109060d02030d09170604030530011d13030e040905010e151e0c04030f03030f2f030f 64
    0x41030100356059151908a1810000c1c04000c0c0d0040008020300140d05d01c009004510320b05c254050b201c10032404860342d4a1155240300b0507500d54001517034407501c07210300c030100081c104138500b54062800c0340c24081450f43d803044290301c000813000001c0000105041c060b1501502080c0307046c0d4074021241d00d40706440070702185804e01c2410882c0c00305403a81d0707400e001403081d01e90150549403400b81440d00a000c0d040c4d1882810f110100920907001c8070b076000308900d0700c59070340740d11480d040c24a00ca0040c03030400604007504440d030300c903001410044640c8440c45802005281d80e035204100c0c100d24890b0100d00007500003d0100c1c40c0c0484640020742000e04075210b014243c50000c0d082c45c0c0c41c1800303805044172442024441c080c0c400948400224010f00c2881180a41800c15061440010032101c80d54111002e00040400788400e2000800c42c08104450501920f404581113070070f60211412030b1621580140e00c0c12505000014500003a000c202d254017802c14a01d066240000d5581e0318a01c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 863230746 1250 863229496 863229547
    0x3011202090a15030c05040f0227010507050a1209050d0308040b1e04201009120c1e050411160b1806010905061c03020d110118030c0b0a02 61
    0x41c4400904032100036444282c40c4401e891142601c1070356803c2c136040e58071060040e24040c50615005502c40e910754001c641c00740924031382501c040c0e05136840d42d0660001a000d0181000000c00144010075020484807125030701501a581001502d140054411142c9030300c0280101e445e12483c60100750480313001daa0180d00070890743c10b5552102304645100303031000c0440c412018018140400d120341d4030304c0816000540040c401c0e034248480104240741c5d140f031510400049019006014000d0020521032040340700704440641d20b9200c42c0e44c4d9030201d4400c0030002c1c44054004042003185004e001e40d001340d2038900e580616040d4030702210000e458541101401e200c020201013003841050004d1800c9804d0030310305403009075844419503c0540416a9040d124201c03401e00d036010321000c0250075040320ba254000709003803200c52900303541c2e007100b1220000f8295038400c8403035824207007a015201e42d54070958861001b5880707449c0962603a00042e1080038118414056440d1038021a0400c9540c3d00e02c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 863231996 1250 863230746 863230759
    0x302010503150a1523040305190222051009021309020306121906060506030f01060f0903020306100302030609010b0a1206020c03040b030a0506010309080f07060e0a050616020303011202 81
    0x8269000c1280d2480341e501903003038400305002129078142c0c005201111341c00410111a42168807840f170320000d0056000190446e002600f9803102a080700900000d551310140544402041d1801006111138807091048245922402000207264840009101404030307200210308240d0042c1500907141240d010383d100c41680003002c40e200381e030303201c2502e461405043c04aa66031141d04034580706c40c400a940480c0c0c12414604041000d1070b0000a8038400c1c280e2002e000c2442e8a0b0000440703100f48241419820f0010584021015843c00d100291041150188954007145944149490418020b040381400e074903140c0c1240b01790303480410340d008445541031000b84140250030244003d00c91a0200040d5100009000641002c0c100c09036200380a205820042642c1e26001902621201c1c1e0004040c4a020084031309008803040161211074010800000c401d038035004c4013490300b0030042003501c05034010420330a1166816400845500c81131001d9030540d403400d92400c00641121500901c00c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 863233246 1250 863231996 863232031
    0x30a09030e04050405010e061b030c071506090605131802060a02070803161101020c0a0e1f03080d0b01020d02030f0a03020d0510061107060c0b040501060b1c0b09010302010503 77
    0x500c299081c50741c04600038810011800d091510300d0080c0175100d60300030b4500606000411010000d11260824070003400b1091542da40c0d0408540f00313510140c812144d2060f00c0580c2d9860382c40034441c020140c002c818001504508020402c000c20324032990a08400e81817100c02c1044940e21017641d58002d81c1a180030341c54050103141681040c0d501d4008580307078440031a00b155413006440c01d500c44207001c0c040790200c481000c001282c072002030510058001020000800012814840b200e0b4003200002e03403400044500d548450401c0500d520a0f07440010100d8018002d034240d2060000000d000d000030607071a1282c00c0040c0d128000c40f80000e501704008160a40e280d1b02076012a41c00210903c010001441d00c41e0f000d80c0c1081082c06042d0002d080d83c07402d0368081d000001d9400c2950407940740c111344001a60358600c00c0c00d00080c81155255204c500000f021003a5a010341319800307071140d200c90b000018401480884aa40e03040c81d220799049001040942d800004481d00100340c408004121b1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 863234496 1250 863233246 863233253
    0xb090f180405011a09070f08070201020d02040b030105130b0a181d030c010f0c0504140619090e07030203130f05070e01080106030c0f030507050111070b0d0501080d0212030a09 77
    0xa10140002030300311030180204410000c041d8040e41a9502050f192aa45684c150600c40302d400200d4008000c1054404000b120038000c0400703580c05900d51002514042e0020b410b04240d070080da01817001000f0100060299181c00c901044004420200c00c1240c000c66030009210080c2e0340c411110030129a07114103108038129000410402156001d4440c508200100956240e2107419540c03c1c0703520302600c0c0c20114002e80103520602c5095a07036103040c1130404c03165030b00088a0100080d4032050800c9465020301c1943e00143c07180c04a03844100c0c4180c601400004013503002001902014410010050030407054210b90100580004801d540d0245924040f03240580503009035007100c41101c000100c8d218150040c1c0140c0c1e2244803620140e0780d0b224000703a0b6042c0e0034000103049030040c01080c4850b501c1610500c1844007010215441e50780e50300c06c9061958400c540da10701e05525030700103000080042141d03400340a0325100a001240940c1e01d039084030701001d0040700b584d036211006c40b03060 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 863235746 1250 863234496 863234509
    0xf0206030a0209062709010e0c0a120c090812030702030412020609041e06080708060106050f0d0f06061d0d170903031c0e1f0c050d090c06180b090f 65
    0x1030110182100ea9540761401c5ea000305042480300101c01141520965030b41801c00c1030116040f5025460f070109262255a001364082e040b4150040401000d8031809000c2100c6014040740b070f14454079100465420a034602e41480c803144000c551200e8200306002c102580002141c044450a29030030f03225105a100240305031156000341c6038000c1c18200c04000351207402280c1741035003814003000c0200750b40d12004203403141d0440c481d0042c1c0f81c11500041216a005400821681e003460b07506c185002500d118401c02c48284107c3c030001d45980d03000902a1541240658296506414180c094400c400d000182034484092004080c1c01030175848480b14202d103c00e40e800700b04003d06803611958400e0907080034940c039404104005081100c0d07119002004204028040400308000e40400c4c1c410050402901608451108008040000c4109010544546581184180e101c103c3d490b1800c2001459068220303003406813000000d1003080517441400c2101c503c28016140003070b4601031600000c0d013 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 863236996 1250 863235746 863235757
    0x8010501180312031a04090302030405040c020a05060f09120906030a0911030a03031407050a2715081f050f040506150309030406020106090b0604091508010c05120c070f0206030a02 79
    0x945443d11030303c00031a0780540095801e140e03413032003480c03500346030501700815501c590f18041d0150304104028810340c1031503004001c01d111180101e40b80880a562007625110f0101c0300000141c13209001d00013411010301c01080a40700b001c03036090402415a001030341520015004106148d96400003100300511038040c1070704860001d058400100c850704000d0050320444441a00010649000400d214041c8003075404003a000d60310451070303112180c914041001e4020b00903080121180d000503c074200300400c000745450340d43e500003160401c0c19010102890b00d0310442c6c0d04c41001d8809101c6520342540b0301038040421680481c498071040042085000b0b044000100300f0400400c110300c3d25070000040088031200d500800119a41e00000c50407104c10120392a0b004804000c10090789141e90045070744500c0a10ba030303100c17003543c40f41061300310746114800001040b0041401011550210310791644941610078039860020295500c08480d0b0301890024450b0401001060200300349505545 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 863238246 1250 863236996 863237003
    0xf0c0304023706030603050705030f0a0212150c091008040b07031a1002030a090801020403030504181b02010c09050303030c0f13031b03061a180a09021f0806010c03080105011803 78
    0xb9661070b0311004005c2c0c201c0b40804e991512801c030002805050006040c000400038001030300b030354076040d1708004000d404d0181d64141c1d4880c510308002d011802d01d0703100340100c91140f42d40b035448003804148880181d560b843c1009120748c032020800030034600841c140d0301440628000881d50700440b540038418180a00d1070360030030703200d141203680e0680010007030110f4032840d12000c81c00e580d0361078054240d2045005c02000218180f20401081172002e2460110311240c0030041020803420710149800d0440c0300b01080180e459540b80c14145801c10080b102500c420350207980707903103025030b07948089101d8050381da00e4004002035050b8960300300070f10404c007130341d80403503a43e01100481c0d5000d20345402c6804203a0340d1a2900011046001407215400741c1180c0140103c50b100b070a200c80c00203070220045c5401003440c0c59601840050303032100040c00380c4060100c100031400c0700081d401080020018580c0b4140301d182c200c140003180e00107003030300d044881c24078046022034411845541865650392004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 863239496 1250 863238246 863238349
    0x12d060911030108070e0108121606090f150e061f0f0b040906060302032512090c090609110d2414040b0a06120f1508060f0c030402 58
    0x10180c1c85001c0d40110704075031840341201d413680d0311458098a014400e2161800c16030100701074034009071003807004c0c05207180303c24602e0b42c0000094440600340c40314001d00721004440c1d1284131007003200281150721320200c0ea500821850861048181c0c0c0c504018001590b0303c0402059070301c400e0580002040609041740080441c0c55403104013800c10b4101340101040d00b4101240464483d10034820b42e40708040c14500e82080e1480308194001c03103140144400c0070817108034510f004040d100e004103001c43e03210300301d03000d40c040c40c02010f182100c84c0354014012550a04880203111000a410b46100e503040c00000508441c00314030361684840e0201d00150308201d5044009030311200d00302c0e4080b1422064030140500b2818104001c02c4049034004c8101080f9608409544d240b410707840f00450440d04400011150000030020f1082035482d40f222141c0e03400142001044a0404010758008032100052800c0d420309900042440400b119440c2c0a00301c000341c0c00c07001041d60312240450b0903401245 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 863240746 1250 863239496 863239511
    0xe100b0a051818120904050a06080d0c050f0c010c14190305030619060f050a09030503070803090d030203060603060d0204093005130e061f0305070908012d0609 70
    0x40e188400442e0780b1101c0900303041490303e4250001c25a0180070160080885c50020600200801080c000d00f40c08501e655840c408034075410104509100c00e00c945c0c40e00c071300034038044c94224a0030f2070036241d48505410441311000c0c41e9030004080d04a0540c0041501041c0074503c82162420761510b82d04c1c070402522030344540606402000440c01448141d400b002e4820704440b2880c0741c00c25030701c141070000b40106a01210703588140701401c1800d0892400340980c80d9680c4540c1c1c615040302d00e007030b01c0c440c03000018040c0c9900c08006032400051142015070031482d00d640083e501c1d00004040c0c40c090302c1841c90501c00c5507210b03440000301ca075101d03040300810f03241c54181d11405220b0403c0c0810324000c0c0314168203550300071000e035001410300854805802e410010402141c00c000b0f89600c0e0021010301b514505441440d4aa03100212030b568002041d141c011300003018101264010842d50b450b10001000c8a101c2494a181713180d9021542003203011130456000050150f94040207040b480e0150 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 863241996 1250 863240746 863240779
    0x6110313090615050c0c010e030a05121923130b1804050105060c1c051201080105090c10050a081b0c07031a0709030b0c2a010c030e100b0a05 62
    0xc0401910000c015600303c8101a882c103991a21404803080c00da0340c00b4010325200780d031051410503034021001c1c2c196110b04880d0382c4c40914000315010784960028000c515061052040c0c01d040380000314038030b4403058010b59551034070131115031ba5242e1099940002020700d8030302041010200140401205a640c0b400a0301240d24102100800705100f0b9090400003d02d0346440c1081e580003030b1601e409010301d10240035004515002e6440808203204040c0903512280000300040350003485d408002082c1803030501036860502810303410040c46075990780e1552072081da128065900c680c2c00341c00d2612150300c5001088042210040800ba0415800100c000f0b801801181d00f104072032080d12031007029507644d6070081d42c0302000c0360ba6000103680e154080003c940400780242c5c01c03202e40b111151a0446e510600c414034801c45500e51090308001146000c0798009101d46402e10000d440c040140c0700c400d20070b00ba26400780442d80515180c407501c0c10001a542c003d0f4010041c00d0041000d00818100b04c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 863243246 1250 863241996 863242001
    0x6150a050d150b0307050901121109190f0b06040b0c15070207080705011b080d060302041b0305010b07121d0901090c1215060e03010b030604060519060b0703050304034508070611031309 81
    0x14071030301100d00380742c14400400b4dc5c50049100060300240800e003810700745070324420a508002c19950040c4120a00c5405106c0781c0055903004030100d901800c0490f040822451421800d070384110304012040c8a101105170803440c841c1ca00e1544040c0f000d43d16201003480c50007400c2c0c19000654410f10704003005142030964400041c00110640f0b0601c9641e0340e41d0400d0100d40111000503100701d000099000c61684201480381400b0301c126011030426852a011940c0110240c20100784160f030b1300441070001c2c0e040300204100f151030030320511290583d924000c428075240d205003c24044004d080ca00395076004e42005102071000703000c6030014a89803c200c0c1c064202618484441403074030402b880045803e009040684054a01c0980f8002d05a5001c0340c0300e50006009501b04100c02441c4458102820f62040345c8095880c40c445803c841c0200035160100f04819000b4010f0494108002018003c00d20004690840c00c08546640109070a2401c52180e00c801d41ca035142020008a10f20603590b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 863244496 1250 863243246 863243281
    0x70e1207080d0e0303250f0b07301808070501050f070f0c170c0303040b1b0403110d03021c11010c05070506150a050d150b0307050901121109 62
    0x41e001c032040940c003000155902e07403c104141e509500100503251070020140c1050300c99607420481320504070410380713910014a07001c1004a80c144402024400c060750f2100c0d00d440c102c003510441c3c4084460030310381081a801804a4506c017180c40e980406c040c01e0a10160a24403900700012656610252412500814040701d000e44c8155681003c1100a071003046601c1044034203450300d03084a0059216400c1501034401016503071031042103031905001c0184081c500407440344004201c141002501040a42c4100b00352032000034041c0020000b1400b8042c540030068400e4070a082c503c912400c00300c0c00e010b13850405102c08468560480c90305544440780b0701e44d04200d04003c0003003190150049445218503000600103a11101c0401c03145866038011042004d0000d04100341c1a0341c1d07502141030344010004c1622080b0014800403644045401038400608044002d424140d0904000462050041c00740c1031021400303810010800c05285181c010710b28000345008214980394915070f410034186c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 863245746 1250 863244496 863244509
    0x7150507020309090103171b010c030b0108060a0e0603030c01021207020c030d0e090907090c0c020909190f0f02041406031b0a0515040f0e0132010503070e1207 70
    0x910000400c0c03a031011041c0e50200200502072a040e900e10b450760f20154050005051070b2110405c641000c940c213940b419121200b244001192410391060701504030342040417a1070601c0b801008001e4281e6072084000300b920241d40b0035100a4852a0100345580a0017010400a610010f0040101c049201d170091081415608550104a4803001d140d20361007400802c1000c14480410500a890000e0503e5032080710b0004940d1010350707440c50303070007990000104400801e042a090380103508120351a140d02100400c000c0281c031304e10046210103541c052101811226245008408108150a00340703c0c50350002c00a101822045903109070000c4e050b0b403014800d01ca907026000d03424245081403902c540008100c0391410f0700d402d042c001c840c40300c02c400b500481000c00004c10183e00d080e040d0070140010071421203e41d810039020344040f510100341302f2082c0241580d407020013690f91811101190f003e1a1458898035140c200340d13105d2809114007940004910381c072401880c000036140c2d0441e902d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 863246996 1250 863245746 863245751
    0x21e0109020a140109121e0323090f0108071202070b0604050618160504180c0f020613170c060901090309090603030c020d110d030207050102071406030f19020715 71
    0x50f1540c640c140c21841d280141c0c085080143c0800c00c903501c071030b81d08031000d00a00c942c003840b10400e40300c0700900c607001c0d0084000c00c88040110f41d40581a00d1035562041846002504d04445100085c1d403040d50702000c3d41c10403100c5000203000c01c0c4142e5855001000e08201913403034140c10b140c00454148c4c2114254000c41c0781c01c0008005142c64048809a440c02581840407911040348040440d5810b10442050000c20000003921043c85001420400b0f10604001088500000e0013000b9034228600801154003140038032251440000e02c0d950000d41c0810100f100380340840603001c0901030150f84002c28000d100404c0342982e0107400143d046881790b52600801c5072250140800c6418500010780060380020b00c0d4001820715403003c01032a03010b03022002c600e81d0b40c080050343c8040c00ba5001c80050704aa4010856541c04104000c0a8980409403140c8508284041540340c00010080e5110b051070f400803500911151142ca688191500c83c01c4d55a0740882c1051a04510b81400c400300191 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 863248246 1250 863246996 863246999
    0x509010207080c0c180c07020906010e032407031b0302030907031223040b090405060a0f0602071508061e01140409200304050a03110c03060106080f1b0910021e0109020a 74
    0x31140c4c07101714420303170000543c5400e25286409111a002000702080c1c144040080201e15943d03042041d585c040c0040088503100c03d0a01000008020002e4041414113003802c1420701586940160305d000394441d031400685030b5a4060303101d4545180b40d40042c14a031060407442c000654003036401c0008001904481c18034502200081382c20348514410701d01c1c038032010b000c03250851419410282d0030410007044114102c1c2c0701c1c2c054428110341a17000d9009130b0b001c0f134420002c00a04488a03101d111080c1400c500502e0507001044454240c020600c600505521101020341c6c0035030802d06442e202828003540711a11007801030008d000250101c0040b031034402e002e01407403000204a0303100e254050041c0400303811943d003e07150600404034105c1313580503800c2408160344081280c06d000701a1a52444800e04000d4414003460070007034440b40c10b0801c0d0020f404c5c03440c6180421a07480c0d0070207480c240000415041c00b2402e050981402181450100120346544001500035546182c021107400f510f03039 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 863249496 1250 863248246 863248279
    0x1e0603040303020417150a0f06030813180e0a0b070201022206030b0d0c050f06190309060c020a0f02060d2d0b090f0118020d0e0129060403060509010207080c0c 70
    0x4410401c46d040c0c0c8a00b403813000603840801c58000c0388480c0303408000800e0700d030748a60b14811186c0146011400a1f03840107805c04c0070040e0940c11181c003480c148010440c0040f130310015612010000005480e200c03010002c9000d0603c00d6044901c0e0980c070b0802e0341205042c0d62100c2c078111016203d4640001e0420304640028070340000090240360340032101c2813030b1500c0c1c041440840515510180e500010510011070b81c640401703161a00c9444540d000500e00c449031800070200c0d0809030244003194018000c000c00500c0c0ea089224007103404031151500d801800342200c01a100c81800f004507602088058543d180800e0003140b030780511900140007410301c100901c0540f180031035030550880012001040030030910820364900020701075004d441e01850848050555000500600440e9562040c0311000c00081030420a20343d030003201c44144041605c00111a40124040a00410758440229000071401d5044400042e8840186034641c1a1221407503158010381c2c0045003c0c006044d56520070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 863250746 1250 863249496 863249503
    0xe0f0708010e0304050904030e03030d050f15031506130e0a12020c130906020906180907050c0d120605090c1207030522050c060d1a03030f0304021e0603040303020417 73
    0x30155942c0154203080c900801c00510300030260007902400f41e0303002a4400c549091004040d1300440c80c02c041824185003801481000c0000d259001106001001500315540810445030070140caa4414446031215000540c0b11a0340d01c0c0c000c41c40d01d281c05202720a14102142110009000d01e800791002c0440c0b50003a0f89500051214a5020558012403100c000341039100009031030146200604085408012980d075921081d00c1000d16039a00e00702180c54036068050640c450300900d406801c2001014049681d60003400007002800803401450041d00c4899128000404005125061074100750510100d103500c607140c1e0032a0380761b14000144a00e8002e010340303406000741c1804c00d0200031101c008040303171501d9490704942601555050b8003950f0390b05401382508040306000007500c507455a410380081408200340c9030180c0c0051200c0c140e103001000c00d49901980660380c1600d22004440014405040008003590014010040c4814954585d021300140d50111740d140107840d0075070724055030703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 863251996 1250 863250746 863250761
    0x10091a0402090103080708130609031104112a010c030e060702010e07030f060f0903120b0301090c1a040b030705030708060904120509060f0f09090c1602041d010e0f070801 75
    0x400c0701e20b01c0010000150b003c001801c032580520703c09410810544d81a0040c00030b190b025030000340801400748280401c16a6544009000f10b8003000b20704a80e03003d00b100341c002c6008041d440c0d8118000c50403882400c420030308041e03501c83d0082001100f4a20302500030103001481100c180304d00700000748001d00510a200d03581e51086c0040c8071591131940c880d84c03801e11015084401e540c03699400612551240950541d85100c0d841c2e00c00101070113640f950880303818500e4140300340e04100203000825102543d43c420340382403002007084030341c043e628420349104941c04409411000810800003ea200d009540200c1840d666100c01d501c650381004003000d8140e80203460016880c260b451024002c00050000c840080e00d101c2c2401c43d0f40c015640280c00442c42d01d00341c0d400028440100346400301a060303104004540307080c01c0901010100c090941744040c024045c9540303d0f15619202c2d00c030020002c554041e5002440040da0b01144142c5a00c55810a501b542c4540350010603480c006009000c03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 863253246 1250 863251996 863251999
    0x10303050d050a09020d03020705040f061419080a060f0605010e01021f0b030d080124020307030c0602040f1d0612030a0815090f01060e01020c092710091a0402 70
    0x3400d1800d4816079400801000d00100d0402c0d07541d21202005884110034101c0c4507009401802085281000b0b0205403000c0b00802100c0c1858144181301c00c4008900074207a421042e03d22503000034203c0203003030302a810303900000c016205502e441000c216071340c7c0003400c040011030424040a076039400103465072106000e10310b0150300700a070103540b5001c001468003201d415254010a00a1030300c4086410003e0041344200003800c0000103002c10300340c810510620340300c10031008054820480d4002d4503170086410080402c011840741206202d0769405660150410a006c905040c0d80d424000351120805121003c0c0018070000103400c40c600294a510b010411002031407a0040e40139084841410003064021001d0042c0300110740b9840d85107016200307861b41140e0990550400d003010b8403a1004102990440d48043c0590900740c13100914180c105c1130fa00c0090340c1c00044640e4500c01e40d5580c6200c10820710401c0d4005115602e02d41050f215140643d0404510075814541c3e080130240840c3d019 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 863254496 1250 863253246 863253257
    0x4031e0b0f0402040f0509010f05100608070c030e03010c0302180a03021309020607060e0106061403160f030b030109050601060e0108090c2b051e0307050d180e010e07090806010303 79
    0x107119280501a840d0b030061009100150304074101c1003130300490320280c624607c141e45d100303880c500344003183c45155000120b82d041d0804262401c04000d10654006003140c00b0080ea1755180d400309805070200c00f081c501e0040c02030040e011040002030003500901105c6004922500c014590341c20040d070b030403055a030043e0a140381400c0d03a682c00720250081c1d0030205e030080e1082105501080180c46601c40b0340c0c51100c001f141c040d00d0060000c1502d81c180041d45030281e0b04000740100191130f030002c459008801c0c100600d030041024000e40003080e14500c410b070994244070401c02000401701c0c1c20340c142c0d1101c4e22a6070500e01020011501c514088403142042c3d84881c0007e000707803030035410000c90254410b4808182882a24011404083d003000444840c1d00040c2003180d1040004400c0190404080c0190306114007915540e9490013000a000d01b4421800640a0224a1030f0b1490002c0c087e80e50740b81405583d04da2100c90100800c03160600040d442d500086010030f00410190f040700c0c0c02d075996 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 863255746 1250 863254496 863254501
    0x1081e010302041a0402070c080f0d0e040c0e0d21030e1b0d0c170c0607030e1221091003020c150a180302010506010f030507090e0603030c060c04031e0b 67
    0x34880100ba65841601300380780c803004c100c4440d650f035000030320030b0a106120b10086c8031f242020382803500180354484622a0072100d00410b91a80c0041502180c00303044601241d41ca80750341c02610307075010021000703030800c280d2013100050005408a030700c1100443d4081c0b00c20030416140403401c1f18a0031b52103060540140c52004440042100381064a0100038800741078038072559070790a60711450f82c1c4400c1031180038a03200c0403440b40501890000c1001900d00b503281c603c055400618000390030f03d0036445010f80c500e51000300c0c8003c1110a1809010180c01410707410802640004c82c1c0000c0990392251262601240c42d152081c004d8a00d6034240c8801003108bd0110140c203e40c00000900041c03455903a420804c030352244540f02c58080501035000011380e800c1808c00140019071003076000b800d143c00c050504c40c15940c02141442101c01030051a2403036155803001a0440c4205a1082564405d441c203005141c2040c40040046078071889a02c180c580b40000080d610341c0d1001d401030000d6000700300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 863256996 1250 863255746 863255749
    0xd080703082a0f040e0907090509010c090504151725031a0a02090d03120506010e03070603020c030f07061b020d0203030c07050109240b040203091e0f0a050c01081e010302 75
    0x1400050904843c1c00c0d04003500d5075140c280c0740c0c0b01110391010076030202d1010008242580304107504504484000d12000e1680c0d60702410b0701c8414803502d40101e0b81c400c0045282244040040080c269401040c1d00300300d40181170356910041c0003030843e060b850540b01051400b201c0500d54040743e03803100198000d840d22180d640200c10340200a40d1906408011041c60340c0d48654100c03180a1080c0c880e98060200c44000e041124401000c0506100d1000c1d42440c0564000a01008594440c80c0259540b48443c1c0341c5400c41c010313114448004400882e94004011083e040011070807d41f10007010748007007500c0101d0766503514030b045101581040010603d1440c0800c01049030600490021803030200d650780e90003007a4511214185803818151200e03035420400c0c00390b1f50000074219415811801d0942080f601c0e40c059412456801d0f065403008490100d05002d0845045803503020b035804c40d003803810203075102c0f480001c0e120f001400c80c4000810030601c060600044006000160b01d80d83e00707590 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 863258246 1250 863256996 863257081
    0xe22051006170708090a0b07091406031e0a0f020f0d050705030c193507090303090e1509010b0307021204031113110c0a05010e0d02100b0f0d08070308 66
    0x400c002006e014540744800030501d44d14031b0b18007850035552849001441c000000303071000b6a02380c1c204e1040c0010424840d4511707510803030703401e12018007440c0c65032503c03078810b0300000f400c00712040300403140003003004181180d421010300741e400078803901440320755595001100d40344003c9074250142c590511070000718403c4074414048403103450500d07414031100160141079108560300b40d4450040c02100035043c00c10f140c84039030340207411401c000f0803150942e030700a0001c508074001c840464101000048800e054207024501d04200170304444d5155840e51400031840e4000c80d10740001d0312486071030300281c01d4114100e80440c0c4e000031b4546203500c408410414000c003050004d0f40041c0d201c922011404220400500c0300c002c035503004090408440c034009003501c407541a20401500074600e00da401540102d1000b5507032810260004908a140c0d00151300f800d6420390441e0802c1030581c8001c104400d00005002807802910340405a0b625100c40150400f0203c011405103152800040119490035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 863259496 1250 863258246 863258251
    0x912080c0102120f070e0a060903030327080a020c15030411030f1b0315040b06011407060f060501030e010b0105220306051e011e05010e22051006170708 67
    0x114005490201e1800705604443c00c141c4803540c040441405000e413081c0c1003204419180c900390b81500e122440c0110160509505100140900d9182c241e035481a503030b0158461300c1103243c03504004240c0d0603814013450319048604407070098842e09481010515000c1c041108100d81200c1d000e156079115522400d010785400d10060b094814004012000c80d4184444415420045031040c044008401010b292241c10303625044012441402d02001c06d07400758201e6400102030070800201e41c8031210500c182d00c01c5540c06400da40c9850080141544240c0040048640c260390501000d1032200503a400c80b0f000e90007180c00300d40c04022a06481c4074410070181e4541c0321815a4000c40e541e41c84035015038804580000c3e042c60035000d1400d80d500011080360150004841c0e03c2044030342855040c0801445010345410b200c840c18942070659128104c13a0f90000030b403200c0d641da0010b01040c1d00e010707020a03035034415146903040010401c244038031401d4604000740185142aa120403109440a4001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 863260746 1250 863259496 863259517
    0x2a15010918110117010e15090c0414010c05010e01064b0504020c032208060f10091b031a03121e03040f0c05150d051005030a1103010c091208 62
    0x100c1d445084601418201314024000c4540d01c07001071620300315040c40a041403441d40d11501420040c481c41542a401340c41c25100c0751600100303104001c50068a40b070b0940200140039608141c0c08400004043d00300004590721040d0101041701440050014540704e100d03103082140070b42103903140346403844400c1c10f902c01802c40c880c448252500045400d982c0544020340a40c0d0001504500078006481c5103171600d5030000400a4290030a420181c8800b800360010070300283e03c40101c0e010440f1001307494014080e280707040000c41702200080390005150058140400c3c500310030740703030048034416a040300070790024090f0441000031452a002078010744460110b0403107a1807010322042810b0000c1d405a805140501074064403450605034494040c2c0015001d100e0083c0410029007480c002c0d9441d2226803036000c1a2a641c0c40e01c40710100c205644400d0f4588148031900c003e10622600c030b58800201a8020300c51001000000d4038800c269220300065134418944440200d10b00c2005481680c15 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 863261996 1250 863260746 863260757
    0x30906171f0b0708130504290f04180c060f020c21060f1f1401051c0c05071412070813090203070806030c0306040b0c2a150109181101 59
    0x8807060002c120341c000e0300381200c2e1030b0b0000400c108075400028005005000840c2d00b07010b030890900303101c031024440034800d0b415541010300c0b4080503580e03141409485040600208041420301031000a0f1010319542603030405c40c070300e04c0443c565108103031141050b10107800510031174180009214290340d528001041c150403140100c1e04601d002d001c007a0080700e0702c407405002804d000c85000d1502c44412010409503440c010704001c2030801c03085441065100b400e065484200d22000e65000c032030081044020103203040141d260300e541100c068000a4010801d00c0c0e2103041c1c141c0c40550f03440921451030b80080092001c83c0000b080c0344001c3c8010310b800c2030002d0030b00d50b03280101d00c26600300303807000c9000c0759a40c41040b200742800c0002c185e21001c22001000a0f040c983c940b0305082201a01000e0000000030700b40301040340c840010208030b039484200000c96240014150b80741d1044210481c3d660748404000130312010940a404404d900726007550841d00740541d11100c4402c0d000d25445e042c4030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 863263246 1250 863261996 863261999
    0x2060301230a0902030f090d090315021303060507020c0603060a050603041b0b0405150304030c1103031c0903020d0f02060105061b0f1015060e310603030906171f 71
    0x84402d200c032401000941400350312401c050b0044218600b004100b0810b030b6011240c105032840c0d00c900e000d02100c0c0c01001150510900e294014040c0c0304080342c014030241e113481c00008018081e40503611800c8158207039001c1d0215a0200041440196101544220041c2d02840240381040c000c58015204d0010404d81158421041c05510741960114010703c0006c102040302d4141f090181140f00709544072645103240640e4094003002034480007600c011140240da0807075442c204221148040807036124116030110b03d031283d014082100c0110014021058071010450150002d05600802d68020b44000c0c3c2c209402c0c0515500128409520000343c3d070303d07600030b10b102800244601d2000101030900e0114582a840a030368000305054040000000c017080800c1d4051104580c41d6411903c1c00c04408c6c80c07070b221002c281540c4103070035114602928000c1410f00213a004004891084c1c84d01000c0300d0b520030081e1021060845d81681090341000011a482c0c81382200d070408200081c821100c15 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 863264496 1250 863263246 863263249
    0x2090f040f180b16050403030f2003070609140606060a0f03090605180615060403141005070c0b07031109040b0307080d05120606040815101e0e0f040206030123 70
    0x64901d60b415508201c88400740440320071449580d0040303843c141050352510f459660300421104d84030403158100300030603c4d4444184d02c01e60800240b003d442085903216905801c0200041c80c008504607010403421301e4580e04d200011400c1489680c1c01420f031400d22a81080558500ca02c00b1540020103035a1305052000031f030303e44038060240c20030003110014800581e50031450514050038001e90006442c7c48629503660390390032602034035400441418075540c01d1080502e40313030a06450300000d03820002006485a808010910f849000b000340f50030a88881200340e040f9500c04a42d045aa03604021203007180c101500b20304810400a0b046030501a61083c01c2410310180084440002c0c0000440c9006007800343c2d021074003c1000c4400c035145c01d1903d00300c55036641915031218201404100080c00c580480444000140303010805600140c0c00e803042c284510426014506400441d0008103480b42300400d0b00c5481036601600e031520f1039007024080400320001e80420300040f0402005900ca5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 863265746 1250 863264496 863264531
    0xe090408090d030903020f03070f1712040e1608010803070b15030615032b0c051e070f0602160b1b0a060b0909060702100507090b070309080c0402090f040f 68
    0xb50099940c1c6212908510402180c82c40001c1c005100790300051f001e210070544403086000303c901905151040080b908152070518050000080f4140c0021800140c466110a110352180350008045218540f481d101983d00007070138050740b00740c1d03401846400000798240c1d00c00d541003202c1d8050f103488d4500000c00640f40c40c80803980c5400350703101c40c84000254141086066400300c001c03140544c4c2c284882e40000c001c0c40c1c1c8403a04400700802e40690105110050040382d40404845089403c0c4031010030a9a0351408240304170ba00040e894240021000d1010451010007422012200c00c2c107480c0240403041d9810501c000c02c100701010413041c00307440d41000414192231081e200442c1d003000110802600203401000d80f541030b00310703004010807294007007007841c0380e08000c00c40082e0329225071204540340703500f9400140440b00d00081340000c0c95000450142150000e804690050011000b48816800360307004c407640107102c4c5001980280b800d038200403200700000000146440c580c0d00d401d0b05 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 863266996 1250 863265746 863265769
    0x60c0d020c1605010905030a0f0b130b0708060109060f05090d0201020c2107150f030e0c0a030614250804021c0c030317040f0212101e1505010e09040809 67
    0x1494103082c41c0070007203035130171205c0c420080008502030616040b46440c1d00c0351014050b0350045c0700d81c1007000000c2c4150184103032960480c0c1c20000d0303402140b801101c0035203842e10940350140400d00d90703800003c02c0c0d4841c600f00707a00e4400c3e51b9a100c2c1441440c40600240492145017281540141d1701c401201d626048400070350301200650300e81412220001d82e43c00d203800c42e0864424440418010160990003100c050000031141c5800525009940982030400c84289151540314161100010501401341c004031b07107042000d00107100b41d8803041200343d41c1114400e11054003001954030580580e000340341e0950f01c00e0002e407403050fa0510f12a40d510908590800031180c900c0a03400c10b00625501241141da2040f1515080d43c540c18582c80d2000e00e0800110007d01c600c0d561034135001d1200f400d1103081e0f00441440d409010905000781404400396031040f90f01090b515015070380c8030b240c1204004908035103068481c40c0d1001911024044101d00c010019a0710f801c0070005519561680c015042c1c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 863268246 1250 863266996 863267023
    0x7030b270612060a0207020a050a15110a05010c05090906091902130812070c06020304141519120b0105040e16110313030605060103021911100504061406090108060c0d020c 75
    0x59841b01c5910410000c1d054a030030540c010203000c042840b0b0000710040016051007103050050b00709504503503071f43c41c084001c2e20003440c2e9406c00340c85241141d0403101170f01100c641107403019225680c000078086103050403035805170185401c2c40d40041004d010f90007040c01150850580c85100d840305907251402c014645c81084107040014400148110b01c039541d005020b0600c095442c0a1604512459a851800f015446480400030003c0481500c00454854035a49040d4190b01200034801500700030500e03280841c098101108440c032584500b0403501916640c10702d010194440707080c001c601c2007000c0081028818010103040707200404201030403180d404015140780c0c0a0840c6481c00a5982c06081c0c0c905050040c00a0104001c1c13804018014103030901c8c0007080f240582d640180340401203407184900501d040144000d10075503400402c00d41a8448845401391107940600c21044000d103e900380700c0c0c0010010036400300c040d9000b81102a07000d18094144607620303904600342045041c0c0784 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 863269496 1250 863268246 863268251
    0x1030e01021602060c070530030f2b150302030c0406050d06020a171003210c02010f200c040506010e01090e090a080a033e130b04080607030b270612060a 67
    0x15200c045078402030b03414001c0142301035410680800d0307109460340900c1380000343c03101c11414041c28162054204169520384850103000e80c040da5010010240124081079000f400f44480b48842801e2501506049802c042d00e4105c0031f08003a121600250000c403640c00800c4009411145014403911030580252031800c1d0100c0e4213455072502c1881c251a0312180f03001062201d80b41880e042d0040760021441d40c082c200324201d840000811207408119003071803401003c061f0f071b4510101a0008910041000960b0200190344820005541610414150500094203803100b0b00c052598007002a030400d03407500846074000d0041d540d05e036040c0c100008020010307a43c0d80243c10154900440303101101d220301c803480004881010102040e1a80544480d1100000180919100540b0301010003c002040c86191616142c0010b40c0e224101500d0380400a0f08180041c0544d140055032000000040026504a105120303e580000800180007650010400b080480302c0a802e02c480ba11601c12f00c07000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 863270746 1250 863269496 863269549
    0xa030605040c0f0312090906180518030c1b030a0b0c1b01051e0718150e13020307081503070e1339031104270602030601030e01021602060c0705 63
    0xb4071b0aa0258003128032907007844004c0141c2c0c000c2c42010301d08001c6a2002142550360130840c0015500c0310301c07000c25240f000240c403001c560700c0424095043c282c07040004902044c1c0a00305036a524118001a010b8401240415130031411030008105428045a00d600c0f41d2107162041c0d400c55104403044c1a18031302034218802c06140d894a0740d80c1c803004500340882602001c040c0d04665a40600a0000030345038240c03171401a43c0502007a03056108010101d0000d0146500284040e4005841704c2c800304500c0d02c003051507051a110b030843c58503070260007002c071145410a100c030111005040d1b980600a94440b0001241800c80d04141e40059860030307119070305400c0b09940011003120381004119541490038800581078240c0180324000448000ca0b00d810040d4510200071404102a03082c90790001c0904200011500074500c41c1800743c0f4104494160b01c4900c0d030a0740f0450180000c0f1040f5040940c00618103140a012118852411640820780310008030b40000604040000c81e070030441030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 863271996 1250 863270746 863270783
    0xb070f08160b22080a1107120c060c080f0304060b193002041a060d140c0703050307030c050c011404200a0324020a050a030e06060a030605040c0f03 65
    0x165080f0040302d440d40007100e42c24510044100da43c4034002c1c80c4500001d02c0116451003640031200fa480114291600f695480440581c80030940f80704071510f0701003c40020f191070140d560b0007003990300080d42e1407a0000300c0c0c8142e102548010022216980c1c1c81d00e0400c82034840000301a4070182da55004901346d418040008842c0101e800c40740040781c03401c1124100010a4482602038590503100810842e01c0d00000c09680a2031100d200e07041100441d00c44107806203a00142d00d40e16030200381481e00d40b64580b501d80940300b01a00980070981c2080402d80040c400d03440107a01d1000d900e0010f05210490110328251500398200194810346041488180305021045d000085c3c2101561400030035070002041220801c0e104c003409222007840004800c100e00100580111450b000840d0b9030311a408019040e60041c10000000131b24200401130a400c00280b01130054100800612a19203166034802c060580208104d96200140300300160340d0f021014510082c504c01c05258611544086 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 863273246 1250 863271996 863272013
    0xc1e0c0307090507120e03040510020d0e0a03081c0b040e01141f30060501030302060702061b1e210f04020a06030902030c0307080309100314010b070f0816 68
    0x100700b03595042c90b00040c05401e681107210602d0480c071100c000702d124404502950708600456103e079411a11810000034130340c0e40480d60b00d807480616203070840101204410b120890000380001882210108491548030042646020140c0440072001c158442010080740550b0b10320642071509a44035140c11080c08815408903a011100d49050068000041100440c50364548100500e24004d03101d0542c8029001919500041c044c05408036031800500c0c001000300003d04c020b50060040a0100700c68034404140c0500690540d0000042c4942c5085990250b0b4402700d00d2000c0e195030905051550303582c44000c2d04d40721401c0f110040d07902c1402c0b0307095078002c0f5008010074103070030300e5408001c010794074650400c040d60118500042c030440c0a1001c01c0c904802c004800d40c0c54810350f60000b03410341700000201521041610307242040071500070b05070140d4240c0c10720041d038188a14014812003004101400c8038a006202c4201c245016403940010f030b62004000754401c14180016809208419 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 863274496 1250 863273246 863273249
    0x50106090b0903190f0c0b090901050301050610080c070b1e06060705030d1e05040f050d0e0d1205120106050a030b090f34120f05010b0f0c1e0c0307 65
    0xa007418540b48000c0c00203920344c0308003000304004000703020300902402241c091100004e40d1015040306032507150702c568100c5801c901c4203a803089401c4000880e09003410300800f8000c0c0d0340a440081c1600035078506554400008000d042c1900c000d20191011035a0756004e06c2c081c026254070003020341d6035035141103030600004106c00d0140c03c0801024000074030000c100c0300e500151007000900fa202602001201d00a1008240f90413401c010502c41070210142c210304200d881901100d142c3e5101d1542610402c08000c0100c0d80280044a101e0100d1110380340558000802e10b013091402e41d6500d038440101c0801c1e04000000340d004076400480bd43c140c030810010b090102d038120325a1820031140781003600028018107031100040d086801440c1d100e000a0603401e00c2c4006080403e20100b0700600d0341c89044120070710340d424071600b107030244050321030107040e00e145130720040c5400d100c2200c1c071001d40e1180c4c0780758820780b00e00015043c01d0141c0444003580280060b003c0c09032503224504241c90540103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 863275746 1250 863274496 863274509
    0x3040f2f1507081902011d0d0201060519121707030c0c050a3b0106050702090a061a074710061409090106030204030c060e010527030a0605010609 64
    0x2c01c80e05011524540944d054850b2640c40c3c1c1480002064007240500145070605a81e0395103144540c000c001d000c10307a1000344985030b00030000f50369240e0810010303c0c664071071000c4202c440101404640040301d108603a1500074025000341d0610752007640c145500c0184141d00150b0442c1d054001c210303440001100030700f070446054003120b00305010820b40ca101c0c10205000d4210b010725425103080c0004020080c2c88207907605458030342e590300000d0890b41c01070a049214682d0580018040c040521610058840e02c04d003520300300c41525194005940800c0342911240f00f054070307404140c404c030b80380b0240c2928801484441d4a0201101c000070100848222810039246070812030091201c42e02e500c02c40340d1500e0146102609081e45c51898420711b802d9903008205100080b480700c0c0c143c0c004000700d0b48503607184040075036510400c54017103038446c100c030303000440802200c503459480ca040701c0c1300d402c0c1c88401c088010090000107450500c080d40200c03070843d140e400400c100d54010a000e0008c008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 863276996 1250 863275746 863275789
    0xb0604090e07241d150d0c0c081e04030b07020106031e020d11060f040e10051002030405090c2107020c1206040b091f020d05010f0b03040f2f 62
    0x14807400f18529290451940810025040f56964116002c101c00721000c4401034195866108681d40700782150f0700203c20418000e043c140c1074a00c1c9031003103680803075031600810214180f021005000703590f40320350f0700f00041c522014800800440c0300443c040c0e002e0b080e96000016014035600d03140c45041010041060341600c0d5020100c0581c8943e0b41d034050407940b05203170b09900721902d4000340403130150702401032a807400450082040e64082d40454010b21003428541d5140395541d0400c403822541040e414016001400200258240f03032404917000b2949000396410720349600b080c0b1103100015a64100705440403c280300100390103110242005c0010769101110701c886481d565615a00640014941d1035503100080c2d582800703201d403007441d000d48040100080c11210210b1f0194004042556002d031404000090009142c10190102c84500692906541da0303515140a01480d81b581650008031040c0c082c1072003030740d000f00848400009040c100404400130700b800b010140c00182d00d021384a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 863278246 1250 863276996 863277029
    0xa170103020d11121b090c210a0906050c09040b191403031306020a060e0d080c071403031906080a08070b040302070e070306090e071a0d0b0604090e07 66
    0xb2114100c0c2d0500d030740c0210125a02c615080c0228500e00601224109140103401e0784086443c461020105462400c03030300c1424a031203605003480288074502e1002d510a000a00400544c020112516440000942e000070070011a407512010795000700c8804c2c4a06a00181101c1946030921600303c03860011f889281c100c040c001c440c5e0701050f2190040b900d01c8000d450b45d012140c1c3d010000c58130480d10100c01e000f10150b50707900c065a24070314400200c600743d0030300c4913120050b00006444000385601d0380e984c250a4540c00010070607948291780135528040f62500e80a50500204010340c041e02c21a1459884a101c3c01c0b00704045800d140c0040586400c040418004502c560080e2100d0f55007012504945403990300d801d0386400a198000100210703618108081f198143c2e0004e4111140c0490a001a051440f007071342e1907001c1800b81e00c034244001544041202882c2019000e9140c9840700020304113034450014413541c025904c8421200c2d1101b168800d41f00d014001d000c0280320070080c0c1007105 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 863279496 1250 863278246 863278249
    0x1410030209062b0b07080a0c0212030415060b0a03060506161112010e010c090510080c1305220c051204110a1805061e03030f0a03021902030a17010302 66
    0x5201410803842403444030200d1900c1078070060320314119003800f000d44501e0f0b006840d01d01c040c00412203c401c08608003000044081c462801882c44d8036189034054034205080005c5580240c00180003690f664030403103164000103a0610441014146203c000380d100c07000c400f0014252070140d00440d001d01001e1003250001c18600200c0810281c1c4a1420f050074004107022641d8006810b40e030345510b6007002c185003140c42c010352294860000907920b4100c0340362203509004051104646100019178468009500b141e4114050625540d03506458000c0c59502c0c000142c0640d9082d02d1038640d600310b14440c0d07216481503c40c541c001811070402d242010b03403852010010660051014100c0e1481c0b0600900030340d10084071401a01a86c011030100141c0c2111400c001d11046455a0040540e40d0390903107800e2021802c598440c01c010019403900240348540950f07600300c100202d00f0b01d1380034488160040301070613a103030300600d40c0d5000303640303804c6640d20040841c00000f240d902c02e011144010f0025 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 863280746 1250 863279496 863279509
    0x3070f1404050618070306061404120b09010209120f060f0106091703040f060302091e060f1e0703391202101811090601051e07020d0614100302 63
    0x440310884001a455861201080d400002c1c50100100c552507841008001a01503000f401612003e64a010710a000542440510301c9a80a032000412048100100050009007010341c071410034000036050220039800f10700c45051540300d256490b040900919031152082214541c41114881c1c28070b520351500c01c01800384101d03409a000308110030071102c00e03110020000c6a00901202c1060b101c1c20f0368170038000b0001e41059604607c914200002c070444c48001c690f07400e03100a001024545030034140c08519416521030302c1140344070303004c0c46042921040001c01400181e07010780c413180e0102c040b06068484a081142c1e200c00c01120804409605201d06250302001681c00700b80b5100400c46403000340c1c40c0c410701c0740100c4172442c24950b020301610902800158401c1c072a8100715640c510140401014075812a043e600044060240e5245902c03c0040540845103911001e03141c010140c01103507101d800c000c0b0a03540941c0300c403514840f04050101d91540006c15081c0c0410b00c0707042da40010007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 863281996 1250 863280746 863280779
    0xa02010e060c011b050703030b0301111c0b0d030c141b0607080c0d03060f09060b0d050705070803070c20010c1202010b1801080c1207060c11030f0c03070f 68
    0x18038408540d01200d01000d5004410030503001e00103040c00307402d02400904542c001c82d01100004e060904802c0a405c05023343d0803c51984030355207040107400d00d0000054907007500d640302041c1c3c452517070344010307120002c0013403510f80280e45002c070400d8181058240b842c0c1600501006074000e00003414407403201d15031403440660803900e8541c0c92580b418111818001d480c200d12140c00f130038000c0b00440da010350000040320810504100300f1036840290104403101d600c16002d01a6040101440170b501c1c50f441a54410454100b007401c00c032160300c402506802c02c451803401700d40c1e1aa81802400031941c56607620b2003039142c11041018810000821541c0190802021002082e16042d81d480c001c1d00a05000c01015013a40c2d0401440010415050400e1080012501a480d0f41e1161400c103490304001c50500361004242c410f22b0b0030000c442c8404803040c01d60b15600011049080b07076405000e1602500c4c0240f000300030034515003080600740041c035445905d80b008182c3e020490481c1030800d030300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 863283246 1250 863281996 863281999
    0x30a1104091e06150206010b0c0708070303030b0333060103110723061014040207020d060e0715170c040e0c0c010c0521070e0604260a02010e 62
    0x584020051245165000341d4000e94021801e00074801541c40007034001c4440d500d0b8400041c44065030354500008000c1c0c0c0c0c803840c80c2c01a00000014000351900000070400855800100d8000c940c2c1d4074406800c26001c0d802c2180080e4030350003406154942000f40b450614a41000790782600112040e05681e10790001040440034498000a019070707000380c0c0100c07100d0002d01001aa244183c1c580300301c040d14407054a4144ea00c60303081030b414001f00080d0503481030a501c0c101420b41801d210160000580d56981c540d0301a400b0041400140c6682e0ba00c00000d920071100840c060040c04045420300846410041c054a080340485540c070b54003200c07492070a86c031456443d01726101c1c199102840c0c461b640048010807056018003248c0195500100001c0b40008020010000e1001d07007101e0b20300c644508101c04002d860070030403031358000407842500501141090825410030401045a5800c5540107104440c42c00e11458030400400c01d010316007400003c00b030003407810746d940040c241e0301241005a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 863284496 1250 863283246 863283251
    0x2090a0608060f040c022b09052202070305041410052209020a02070312050a090e43030501080a06092307052e11010204230a0f0803030a 60
    0x8420f074890708400c01111801500602c0130201501d4060f54540500c000d020906501c3d140740920042c0c01c2c0b0400c0885100c07a51004512403400c8200315046491100c502c1d0800c40c072250501c40c1c0250b45c070040417410f201c3d407504ea846c2c13803400002081e100e0510002c1405200143c0c0c8001900754070408a41a0340100340300845070702d1507400d86503404016604072100da1480094003400194001a001d02203e11078868400000c020382d008980d85e000700f400001c0410004641030144110641c1415841403a41c047c040c0301c070042d242104000c01e0700030a141c1140701306a0340030815139038600303003191440e4840c24248420751601c914540d64905c03005000e41074903562008101084180031100b03a01103411080ea640e00d414400d032450b00d518151241920540d01403a000142c0281c40741482d82c40140072a003000040300e90300040d1041c146680c3c100206540c00c210120301014011031005010070455134040b84a00204103105a400c0c0da500949111400c115081081c2e503800000c695000d060113402 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 863285746 1250 863284496 863284501
    0x41101120c0e1c0506100e0105030706020c01030c1707030516033e030c030603102306030304090c09050901061704081e0c0a020915010c022701151202090a0608 70
    0xc42040c00140c0b0302c000c013680501e0f014010f0031404d0502c00c40640301d15400b8494a0303640e03002010b075940898400c400143c2c01c00d480705005503019a20a000008403030501c140c6403207031520013403c1500c003100d050011039507482c10f00104000012001c20039000c5800d0400c40c0780800c0000c4c03401a01c100000c500b607888240b0300e44503100c0c0b040c04440d07140303132941d43d10f00e481e030500310142c0401341c0007103910a0080c41807000c50703c91170416004503001554040c440140350a541d00501c150300030001c0a03190035100400c000601c5003486d20602d800b402c0c07180d0310b101c9000c0c01c000c1001010799061f48410100044202206094500e0300c003c0346c1c03c50b80c04904599a6448002088949e1022075922407940030045600000400d020903420140d130f1007281c5404080d5a081819143c2ca0364014080d030000b1041c111110060410601d20084041194402d0040f080c6801c01e14091400c00d0f00500c0c0c03403603005007d000d205600300203c01c40c06000300c0025810211000c0102e01c6294031840348400f00204c1101 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 863286996 1250 863285746 863285779
    0x12060e0f0a230106170c09040803040b040f021c021c0c0e0a110d2705030306060d09050709150905070518040e01051611060402090c03041505041101120c0e 68
    0x142e070400e680d0b01c00003409060364400094100c10b0307041012070044e0003000601880341c50710050151085503c03155060654599849010503031400810031500407100302520000b5a540b085444102d426190742d0760003420883c410300042c4150061412001c000d2020560001900000c1c884180e80d00d90703100510310394504000001030070000c81c4000079101c0000b03103d080d4404540083e548589400716a0952842e0030280405903032513800c0180942d0014000314465141080c001d02101c811103a0100d40071040d40c851900b01401503011000d02c0e80c0d80d1070480307200c07070b4503010f80d20092070712200c20400351804d880301614038440c0080b014815000c072005548156501e0f448002d01180440080000e8506181c66107588404041ca26004c81c43c40034410001c5800000c50754031a6501074140b902c1915201c2e0301000540014004454111070341102d48102c2e02c59218007071040303000c1c4902048000c480c4001400042d00c003021b0444023410098491205c9400c05002e0b03106020944060040081d01803 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 863288246 1250 863286996 863287043
    0x60609070c0813030606231e0616030e06120105040b01170f090c030714041104150f030b060c061609091d0c040c0801030b13060612060e0f0a 62
    0x1d030700901100000c50019404030910031007000340c1348269400c10880f52034680d4803510803081000040c1c00c0345003001c0b200c0c4900309004813040c6018004185559004c1d1800060403940000b0070300910740003100c0000703050590042001101441c25100c203441c00c0740b102e001c01e900749014001c1900072602c42000d4521070b4800c12001010418403c8007002508204d80f88181c07503030301900c03860598460360203400200d140201d80c800c11961818100e0305d04030703c5901484050130042a090b80c3e00101031100080d02e5900c07078140c104013800780e55074a41d14150084041d00329031340030b0b035014010a400d210402140500180300c50300a00e03a01e0724500056500e40085401e80c50f1604008211818000f07000a0340848010358810940090b055034503000c00300c000e00c030031160340e80040b00000711004010008120040759041c0c0001e40710700c0215001c5255241c610599055910407180c194004008006009140c8202d5550341d000d0005800018154030304240c0d1b072018280044d01303110098841c2c0404c1c81440b0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 863289496 1250 863288246 863288267
    0x200301120821070f0e06120a02070c082401150509040b1f02060a1506080c0c01110403060b0405010302100e010903020d03021e03042102040b0901170d020f06060907 72
    0x201c48102114256120042c03400c1400d0310300c000415485100383d2900c078004e1000308060300c000303400b50f400c2c0400f0034990944800050400907a16500300900c0010480c5002204c02800c02000201042c1030b144003640d07031000340e00d0705802c9088041c10040c0000c0c40103600300284480f451405984816845001600518030301c01e21310391040c00c4c4c40c42c4025040c0c9100c0e01084410941d0240c44481d5520714125003030362080b03003c00d1400e0312801420711005014900c150781003c07000007038a0901c05020002421104a4031401e01904000704080081020901072000c100006490500c80303549140d0110f0350b001000304801c4284808064814010b901c03030002c0364025074000345680c00c00c10b40303030030065141e00358922154070b2000c81500c05d2503480400421602290072124206075880c1d000d10141d0480703001c25504907440f030703119802c0307111540ea14030901d4080c20481c80d00400980c034010001d071038040d80741602419504003c035909003144002c5091a4400ea0075280341e00355643d50341e011180c14070301 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 863290746 1250 863289496 863289517
    0x30a0f05010f08011a0a0501030c090f03052a03060f1806010b0c060c130b070602190801170f0601051908100207060609380604060e042003011208 64
    0x1480c00001d500e0010414075000c690304038008001052015800c50074041002c4c3d90190049600003080065511035484150004405e01d8460b00c0143c544d81099003501c942e038001d440650150641c00e860380d40c001d04d620400003c1c0074944074850b040d000400e883d030340c0003480c2e041f040400c1303c002084195030036620480070078200e00341c0d0072542c0c58450b0407201d9003151b810f500e071600c02e0100160071041d0320700c100d1355013010342c01d66914071a182500c003151a0b4805601210455000c2c080e4403c0c4516a0741c018480d1004c81d203440390030b903040c050008070101203001c1070300c2240c1c80302e61101890325000c40d00f941035813401d81e0604159004021061a001400d912103042881051140c01c000000c0c0e40c05410700d03911816051046c0341d40c44c1c00d0300081d1762581c032440402000e24000308842903004044000d84800c1c0388000c007490810107002030840d070000c0e488079011a090042400c12858103118110841c1315002004006103040d0b0b038002c0ca03a000c14000c0302000c03150510f02005000c1d00c003007660981c406 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 863291996 1250 863290746 863290751
    0xe010212093a030c12050715020702011205270105010623130b03071403070807081f17070b030c161e03110c0907080a0902120a2603040503040506030a0f 67
    0x554070f030050103c1c5000d681543c11010301400a000140b0072011110b01c0380c0c00c00c207148400d110034044100217502500049042c4034020704024403400250160b18880c0110011841c3e1101d10346002c0b0424481411103030340c00fa40f400d8010300000b41c10503030a8070501111014000751003900301145240f84100c4021140d41142d40c1000500403100e4402103225500030303170b80c1030381c0180400a04c40d0b15000594080340070400c0700d80007940652140589036800010700ca00140e10856480d40c01d19009155000f0250400000f180000020000c002c82070040c010b10003002e15618003004d50132240d0050204000401c41d40d2070301141031200400f01000c00b00c4496800c420310340f405241c080e0808131100b081c0885402181c03012480c41c03501c1d003442c511030326058903a84100c0e511002c00d2001062502c80890344400e00400b040ca50b180204003012449201d4040100404054204c03246500f002603600d01101008008020000e800401950102c40003915519202e0b158180000050480f500d018044540f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 863293246 1250 863291996 863292109
    0xf01210602031612060302030c09041a010b04091d121303050601350c01031808030a0504060506150409110d0203040c0f08161e05030a030e01021209 65
    0x411070070300f00700485419100d591000003a02070b40c40c11707a9010301c00a1740c503801c0045100c0540c1000c181c03981d07015224550001c40f88103042600098440d082c2c011070070300031011a041c00081d0a602c03480e03a029100040f081e1040c0b00441c8041d5950217859903200304a4804912005c41310710200390340011350340c402d003501c03101d40c0c46643c48542c0c0c1036070601051071740166600119800002c04521a6034450301c0c03003d8810b030b20030100150b0140c00c0c00c1c0760b01c0c0d0204403201c0e04400460303980300245000f0580d0801c082114105400c02e1020388501402c980c2c03207505006003200d4030700c0d003032804c0b2030807101100c1c804614128031020b021218081c24885850050001082208000750702e80d0b2790007600d5013a48990f806c56241c020460b5908214041c0301c8108801540a02c02d40c03003480b1020036400d030401070b02200300f40c132480483d09000002c00101c002c1403100342100081d40c2c0501c020002d0441d08004c260a01010b54001401021103204d10341172102914100c55420914014a030142103084114070243c8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 863294496 1250 863293246 863293261
    0x20309120607080a060b1605190803060906061c0b01180303080402240904021303050111071101080403080f1b1306030f0506010c0b0a14040809010201140f0121060203 73
    0x7040100d0724007001500c5080001c2d8025803a00c42c080645282000c0c0a040c00040800c0140c501e60600e0161801c0c81410840341c1e41c1241d9032035a03c0c50030311510301d25440e030400c0814000f01c0710028101500c5107000340314090f4044030804a02a144014801c0072070500c58040040e11068402c958510014440d154003105058010b141540100d100f81c0e45a140c407070452407265841d10040048805400e0200040506460315401030034510908074008a20590340383c0d91039084414991300d035100c3c1180450000c3c10300c003e22411511961081c01c200c071140c503050303030f004280c0306005156000106103100892102c01d00d20031010303086420307003071000e9a940e01c2c1100c101c800c2150b44a9000020b04020750310300d040b4858050540034100607124160000042d0750b80740c210364402401051901d640301c00c003040c1281c040609a015034004c80456503102a40d00009081d0741d02201046407050041051002081c2c2030b6100c0e130304440c0d11a0150b6413482c550700c2095000000680040e00403070000c028030042 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 863295746 1250 863294496 863294503
    0x30f0f2105120a050108120702030717010b0109060302030f062b140c041517030f04030615051903060c0e061c061208030423010c020f011d1c02030912 66
    0x45895605415981d0b43c41003000d0007070382e009002d80e55031a0401501211030300210006412800c3c0300034261401c040d2241c09031a882c0071003e43c40c5516079110010501d0395600880c40a01a000303e150951940c03602c0d86205244080c05068580208101c905107102c40340c10081640c9080c0708481600703207074841410905802d000c400c62501c2d10f4040c3c80d10403440b40c0f40c184034070a10f43c00b04c05a50483c083c41c00034101c1402d0f2801e02d000c43d09000421242da80515010014000746209200020f0382c401c58805561904000e81c0009001d4218a43d030707100000c8440d4404400c03264482c6010800f015500c108130f504c1d0101d0707401140c101c100418114422020700c94201d03400d00102c0410030256a1381c1d21704250012a500000d00072040400c080703000b10324612a1513500300c601c024031440c0c1c20b80d011000b5084404605002005801c0038101c050668020b001e050304800c40051158040710b0130415440d110215550f103000c1c0400740000e031186590003841503e944003402096849070f6010781a84644 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 863296996 1250 863295746 863295757
    0x40b04030306090e1f060509070206090706033803010204181107020d080c120403060c031a0303040b0c070915091407050304020409171801020106050a030f0f2105 71
    0x820708201000c22000958400c00301c4c00700f03102e0020407012035104d03940f640000f03071070181211180e1211380104854a03058001d900403062940181482e141011030b05040c1b8101d07401102c1050b080c02150200c408031000c4046148010303800a4080000c0c1c1030b14400c0d80c0c05c5c5000c035039806500100d400078004016044450000c007503440180900b100064840290f4400c2150080d440700321200140701144e28900900a4980000112001a0401d948076562904150f00803508191144000c4420f1580f45c02250071038504c041400c4c0c0303c41c0c48040000e8480c011402030405606000c00c84600326242000504010699140108583c1c5011004181860301e24090003d055060155210b400c0103091400742c424952542c0c0d0505503203c5908200c05000da088003554503460340c4181c1202210700340014269010200700c200c049040440000e400d44800d64003140c8a09134182c010408940007080c0260950b900c101e68070060b1174640303400b072a01c1006c0c000c04200300b2042c0502031003540e0000020032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 863298246 1250 863296996 863297003
    0x706050702130507170c0706090b04021306030210120f02040801090b0705040302010e0906061210050a0e0402150c190f06050c130303030c3c0f0e0d1703040b04 70
    0x21030388425001c40742c00d542040da1020000340565035030f044000300e8003540f65003000c5181d10252400313040d900c684054035044107060352642c60b40028001189810b280001c5400019030f420700c0043d20710f4002500e01c1d10346610f02c02c18440305507194251011903900c080c4403169507030300c11516291181c25480c001c108021013254840b00f840085100d280c050300503101140d034146e603031450540b0003009000040030050615034202805000d4045051031f0360311028172807c8400d0185042c01d24082c200b11300c802c155448000b2a5001006000158a4000b00c41c18000005803d07a40e485100d010402e241080146600c05802604000f01d010002c8140030300c4405070040c0003d2060351180a007120301d520035900c5402c880a0b05c1881040000c2c0070780c004181c1605035040503400c001810f1102101904c441341446401c035840202c501c0d008400400b503850290f00d5113000f88104904100242503148007016a51042041c00c074840d0070481c080d1075203030074201c0d032028003500ca0400780b5000c0011072382620101d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 863299496 1250 863298246 863298259
    0x10e011517030c0d030209011101090614160c06090302071d010801060e0705070f030302040b0f07150c02031219090b0a0c0f020d03110702030f1005060301020a0f0e120706050702 78
    0x284091000000f40c48034a1645070242c00810301148080d8020761001402c10305010840c6480b9550050a01c5260902c40c0148800321b1304440601711140f0140f00208544116405482c20302e544d40da02c0f250040c0040e030b01413800240d0707171058141030746050b250b98410460103204900d10501040741c6e5100d14101c4020000900403203884129101c0e96031000c840d000b0002d00c4c00d00085004c104200e980b4207819009044c01032a09440d00c0000d58280e00c085164102100005040402c110300c1411180000001690400c092001444020f4491241030704110003082264046005000114103504403081691400c0001c6405890705403c00700701290101c1e480341c40d080400100c0c6001740c3ca82e006d040215070150150a00305102035008000b101c00202900c0c9040c880000103840410500c201c1000004c010002100c00c5078491050b100c0050406010f0390045c03010800d00c5410400100000b0007a06225120780c8400303000c160740114150600850744600f03800000c42e280c116004000f41402543c10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 863300746 1250 863299496 863299529
    0x9080c060903070b030415063c171e01020906030103080307030b0916031a01080a020c010609020a081b04120b04020d0609120f1e211104060e030a0f060c02010e0115 72
    0x2d94003038541409082a00e625840c110031002c0000c074140c1d10480540d446400300b00783c070b800451350401d452032402c0040764065919109569081c0344910100c2074480000e500c0d100150020940341e01062100601c40c80f4f010000c560310500075000b41d0702c00700000d4210499440e000550360f5101c00340c4a11080400d180604c4860100300a0000d504400d41c1a1200142a02d68140e86ca0096100c1d040480e00d80d5a10399000c01d0300600c41c00180188181692602c1d02801c0000210200c4980f1183c514940e80c400c010070801800b0242a01481e60b030003907070601c1191344c1c9001280710b088140000030704180c68002d42d80104840040054600c0352142d03200501e0a00900050b203142050020f00c806504880d0100140c59100700004030b8182700d0920b00c0c003521410304094100b6103201c02c2038450003000116040c401c49074004000c0030f520404038014591010740380c83c0c1104508030b40c40043c220a481d4001c014a0720300035000000710b4900c920003001070b100d112420201044090203101c4691420300c1c071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 863301996 1250 863300746 863300759
    0xf021b03120601110a080f0a020f07031203050408160f060b010e01020c0d1a040b0f0c19121b020708101b0e0103140c130609080c060903070b03041506 66
    0x9485540d81e03103040c90022500c8480040d160140200d00518261146000e454002074424018005194840d00095122540f0b9036001c6d041403041e0351128007541c0100b00820200340c091050f0350420807030b802d00040540f514103003c00c0c24802d000125640d2800d4a10400811102070541e0040b12f000d80001c0020040103001150203a03608003074140180c0c840c1c0f450500d1860840c001e000a14440c4281a001d0100451403041d441400c41e819900c044c446800c0194048103103800c0380e4091000003e00349800c00c008941c0e06006020520f41080004400006413100d0726580441b0140420120b05501403400301802907660a00b40200c100764019110800a11840d5010300d034152007100c06002c030802c69807031003118807190b02c0c1108c80c1010f440e0300d1100b0f4201d414115041c00345010300d5202c0d540c3ca0340d1030390340314002441368000d00821901d03070820000400080703080c4038001011580940d4a08400000a107041c1081d004030140c100008103110400075802c2e1000d03411404403e06221240c0d44d101c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 863303246 1250 863301996 863302003
    0x620190206010f031e051c030612022805030f070524070f080f040e0105210705010507020d0c0905010501110309030705040e03130e06310209030307060f021b 69
    0x3c907207824441407003010302c00900803042030452001031124801d540079164580910385130058003000c00c28069600300306401507243c00f5020183c00c01500080104486a0210b080d0145070115480e03c1c01c425074016441410000652004000060458110002c01405951154110b20906100b10754441c1c0300f89442140c414030040c4801c4141c1d02da428440b43c0c1d10303a440010000c083c2252611030421083c804400350801501c041d008031150510301751704000c24008004050840d80780d4a403d0f011071950380c00d200041900a640082ca851b1740c403000e840c0702040c04120701d59001003054070001404245299a640154100c034401d0707030b47d2460329400030b8105899104500303203550076400620050045040c10b400c0b000b4528250710842c0d2074440d50020f6080381c1001c5811000c0300310b80550600405d441c101c1245591003000f0786603204510740b007111261b072141c8c8020488616a801003050100d9a13014815034000a070821401d104035240300114a00950103455280305110680065011000000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 863304496 1250 863303246 863303249
    0x10111506030d0c0c0f0306020d1a0d021c05060c0c0c120a020405041a07030e010c05040e0f0703150b03100905040b060d172101120c0909062019020601 66
    0x24001e82010402e500e800c0ba42d0018440c0305441e01c0c80700742030005007007107101d1440700194098540103881d40e55891f21442520320306080d4101000000800d02c405950f000421240280e048440b01d64840c0f04034441c24404800240c090024001c150420622201c0e100050044030032201c10741c0c1c0002d011a042008000310006c0c0c0814590000c48480c0040c18560301075130f00070740601c0000503c8807840400d050300460895090780043e845280c284440e107003d0085220400d11410b000b41854146600e590000100a120408030751241c408600400c0c00782d44072500262001205800107505e66140c540c0d40c1c0d00983e25040d807015004030010f4500d210388265400746a01c40b0004541d40c4400c0200903d010f94030304241c46d1017a01008249400100e28008c01c5401e0340c0d2102e66020f4840100d4120199005912200094011001c41d1001031070b02c0941c1d0003520710042d80003c1c60b26850411000601103c40014019240e08600400d100c1c980c4016019001d090742c606803040d50762001c100c1e00c60100307 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 863305746 1250 863304496 863304499
    0x9031204060207090e0111071a0c03010510081312091a03040c09020702030f160501080901090209040215070f230106080c0609060c03040603020306090106080108150a090210111506 79
    0x424402d200c10744e03e40d0040800d5488401c004159000300e581c0d0715a041d80011003c960308a01100f1203409003143c07070707441c0c0c0d444005100344c182150300d4140410006541d106808040040c00d10008204107840038541110a41184261502102e50000034111096500420017140d5210542c148555a020101d03442282d1014606100618040010000e5044140d040748d05000707085102e00048002c0190302c40d80c01200b0a5102c416113003400240080c0400f41040e826641040340403005a1a46102d81f50000c2d0b0540f04a0480c40341000089054056144021304207841c0d05c55400134801c800d05480c540c0010490b41000c04408102c00c54200e17540c500c0341c0300b06a0084904801d07280760034009820440c6024203418134180c1040d0602d421580b0903005803000c20f1707011007800350303501740740c21411b01406c1281404003082d41040302c41c5079113000082c80c4982e428104000603828607130641004c13003923941c040c1030726402c1c01541c44041c00e0310080300d10380000752149010150f213002070f40100f14080c820 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 863306996 1250 863305746 863305753
    0x30402211b0f180a1d15040309031406061203030405060403140403060509010f061d0109050c0913051602011404080717070c0305070b031909020f030d05090312040602 73
    0x200a00c03800000084a620981c024004582210191140081c28242040c0302c074203542e991030014681001c42e07030101e2445d885c0b510b84041e411100300001072280405201800f621010b5650352408455844094000500c5502c0a000d2103580350f000198213805102c0850b24110b9204072000e00c1c0fa503034001102c0180c01c51f44403e0110f004203016013207145400030029038061a01c0e0700c03501d80b601559810740701d030261a0346d282d0030b1240d0400b02e84204405451007002c425584101501d031907a0185c41801030311017003a0740310b000c20207402c0072204640c210080981300a03a4050b20550400040800b215140ca20f05542802c0001c1c1c00d01c10701c40d100d110b130091158000c9688554880d022645c00c4400d045803c034241c049407001203c407040c0904002d92050f5200515141546041030510000e540032613041241801400f400d03018500094103c0c1010f06400030354401103000140380650192002501801040d207503d04480d4403030024001c4c2c039001d030203d4040d2a130340b1003000802c1c4154031807400140c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 863308246 1250 863306996 863307013
    0xc090b0f031815270c0f120d0c0507060f0207060f0e0904050c0a090b181f0b0a120605060f0703141308070f082808030c04080d080c0d0c050d09060203040221 69
    0x40c01407a481620640a0500342d4840c00c001c87d05072030514450011804200c1c0400408104075003005400b002d01118548800e1360428404082c0d61048180900401d11000b1010030311041d104005005070300300300078006400e900b01410002c0d100c0c25030b40344281c01142c905d51b02140070307132090040240303186024114000170003100d80d541801c07040c00b52900e0040490494000c0107040c921603c5030140c071140081d00e699818080f80a420720305c826614003072290034224200283d079a808166070251400c440c4503941c60307a00e45030488841340700504000c42064049114040f0070181d0041a09440350307602265607464507200301c500709401034850311500707512a0342200407082101c001001d100d00d52515100b0b0801040e9900c800b6604201c0c0c8410b600d0602103000c20500c181000002201e1a942c100502c40d801c100d01e40b040c0901c91300ca41c034040390303032240202c1c1c207114410011076460340c100790000c0249440354036150010398400d44013648913120810108680c45c85000814442100071401050b082c07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 863309352 1106 863308246 863308249
    0x2060906100b0705010e06010e010f08010b090601030b060f0c06040c05100c120912110f030d051c0603240c090b0f031815270c 56
    0x340d100d0030501c44404800e807209026501d8807a101c56031040c80741400c5000d8020884c0341e802900c01c040000441c411040d2103c1d06903121140405521680c039040542a2901c01034a01d601c040c001000c6600c84d80130740c1c810641400003411303a50421255111141301b503003120b0100002901711100704030400918180c90405080c0c1140d550b04030301e206241c010a221271400c4020001c800d02422940500e01550f4840000c1c0b60740c1151144404861906250004020840d507018580b68110241c07d49000310300241c3e000340ca07a440074242400c18402c0f03400b0300382000c03003d10142da4a46021020030b107809641c0e0200300e44003c1d8003030b0450b4803108003021a00b045404100304030000b2424000c2d1400c010484890311004845240c0706e0300c1d6900e07010002440004403000620078003850441d10503c0705909442005014045070b400c0096141a0305000403150241c04181c1040706007100c507 = true := by decide +kernel

theorem cover : BRFrame.Cov 863129496 863309352 := by
  have h0 := BRFrame.cov_init 863129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 863129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 863129496 ≤ n) (h2 : n < 863309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
