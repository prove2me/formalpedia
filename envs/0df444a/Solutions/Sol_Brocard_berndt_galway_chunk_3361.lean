-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3361
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:26:18.753426+00:00
-- url     : https://prove2.me/submissions/17e91625-2047-4c43-a7be-2836df644c78

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 604316546 ≤ n < 604496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 604317796 1250 604316546 604316567
    0x2040605221502010504030e041104030f020301230a06060206040c05010806150a210212071b0f0c08010b01030903270305010219020d05091e03010b180a0606 69
    0x14000c2100c010100c5011203600e022030034541d0301d0601c25030750341012001c4003104807102c03005075142c00c180030a06901007003d001041d003c13941042580820320080191b40308500c402001000c0304800749043d0340d400c0d800001c02c1900104054030340c200c0d506482d841038904072200c058181c544400452550310002d195881540d1040180315910708040040d03a04c04801030080354442d0310100300b500041c02c920082c00005030181c44580380e4000495030746280080101490070b006105001141e0100300360032606800c0006402c0c2901d14100c042c2c0c4038080024080800b801c0c912103001500c0400c40d06d1081d07901140c41e418020800580b00344011420f44400d154090b000610040890820421403101014500102641c041e80c0a0350ba90700c841c2641c100300b044614400b01010400c101a4040c04000c203410f61a142c118904602100090031303601c02e02040c02d503100724034058845c0e180c900358000d0302c131a0801007034182e12100004126103c0340b42251364042036130421400140303640c00b8100911 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 604319046 1250 604317796 604317809
    0x203120f011d040519060f0c0c0b01170f0706020601050a0b18060a030e060405010c0906111c030e0f0604060f0b181e130c0b0301150e040b0604140a090204 68
    0x2d01c02031421000c1d00345148098401c1d41e49003c3d440c0740100100c0c05e180036040f4144030b124003046079204400b55030115898801c5c030a090018080341000001c0b03000d94602e055505d4440d180410044500030285840041c0201c148280326141c008030f0a150001240390484008483d1420003d8864403000d01e14090b01c078407526100c01100203c4110301e031074400b40101400318900003600b902c940380458545001540c040e541c0d40d55540303400440030b90018110300900280d0174800e0090b2007403540c130b50f607600701d50109407040d03820107090b1140396210381c014440c10341d0604201d405010b0403112070b6854100540e021141c003460082501c88601050065124080c070041c00144e07403074000381401415200080c070109440621095601d01d03030074071100321070040707541c030012511111070b6150203190300c100e0390000943c0b07036070600040000c55094404140300d038100b03241000d0b510380104082005000481c4c42280e0180000c00d01107030462441609040c842c1d002c5440541059032a9080b00c101d00c540e0080e01e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 604320296 1250 604319046 604319069
    0xf05040c0f111009060204080c03030c0607030e030f0d0203070206090d05070303020f0c0109050706082505071a15040b0a05030d0c050304090c050307111501060f090e0103030203120f01 81
    0x1800214010342c08030b121082041e00341e41d114640c000c078080032902d11070302c01c4682942c081400d101c04001000401e40c0007809600441c40d2800c5040e0043e070b10080103000004040d16240c80300312075441803003a66005420f0b4011a1b0301d80101c0c810a602070b410440d6408014820100003810b10040022110203004003070f11180c0ca0071a40d910224082c4d17100b00200034880204000c082a401001d1048207812806580500f040d98108507008000d054081e000c40e00301c048800e400010160404201d104401290610b960f80c3c091501c0e01c1e92006040c40700117810b1041d61030810030760310030096058207840c078205c03020010000b102c42040095045800b589425620854101035001d01642407050311038055030446c0c0c10550b49084e5082507480713060540700010310200c1403010198201c800308071041e00030f002030030101e0461038141501500501c5810100301d40c00d416105c0440c0140c0500d00608210303001c0c2e83c0590303124100603540c1d43c41340d00250341501403140080d52803500155014160703480f0040a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 604321546 1250 604320296 604320317
    0x22060e010e09150613030602070b0c0702061c0e0114070f14031f090504060603020f06070f02060d090b0408070b0c04080a06020d0e0d080114030d02060a05090c1503010f05040c 77
    0x8041c40f8610800c001c0d90080001c0243c2c200002e07002d404a001035120f06805a030729170103447e0a0f500d200001c1c10300c80070482c0034010b1030016030300e040a80e45a01d0160400950b00d8074811011405803400c000781c40c5180d4a01902204d1105050b4030b01c44c42401c05444400514601d244110381065144080443d2103a003803011804940e0a0f4409040c80c28155035803541c0b8640758030304101110b0f42500c085030496918002001142043c000d94242400120742141c203028482d201d44855400b800002441100b000800d19280205a4440000a600400030101c42c0c5800d10f81041c0c541d12824080e29486084c400103541180070340116416100140301428a10300340c1e682d400c01a402c84100784c803406440711502c402c0003c08000103070030b04402e03568a04295240c20712240491039503a510343d01075004460038942c0141c0000344160485c0800c50005090b90300c07154950f00f428034041220358031445126250708101154400b95040c0c0b10b044a007403c189070385000b044110744c1400c10070804103441060 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 604322796 1250 604321546 604321561
    0x6030a050309283201020607080403050c120405133e0307020d0f0e0d080313020d08030403020607020106060e2205010602030d060510140f22060e010e09 67
    0x111889400f00c0522181d9030450000e00541115000e070003403440c3c801c500202103c1c0c032030b0507400b80070b1804890001c044a03102090000b500c4034002400341d014420b44401050030584a80c04443c01008410b050f03408440c10038091510300e5000748a8a40300340d12015500f6078040151140d41e2040c0b401005030b180103040100981c2001e25102c0d90104410300001d140400c0e042003000547c440c10141c4e000c1d10f9552400c04003d894810b080c0d2034a0b04004000d1800e1810b5210004500845c542280c485601c0f0b0369548542d121811b600400250803140c01d0240c0d84c02c20a180000d18041c1e0311940950f442030759040422800c9600a108260000c0d01e51100254641403241d490510103400c0c07100101c1101380103040105551080e444900181d00024001500c40418030650300034040440301060f071030001d800300604450502d2030383c2001a0001544824a80501044401c4000700b402207007200088110a04400b00080c0f0803c0080358085080c2c0202d584103131030a0704a201e005119640700c1e02c8148 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 604324046 1250 604322796 604322809
    0xc0c030319020d0c030c02060a0e120d0e1225020a030b090c0307030b01090f020f1801021c120e0a150c0c0203060a0504030e010207061b0c03230606030a050309 70
    0x111401180b9401c004201000700340d40034840c801070903030320086110549460024504940208075040d07491a04240a0701003030007040c1c141400d22080d07401501c03450b940c60b919000340064401500d240c8034003280d200c8800e0035840074040040e00444603038004050f0f0303d203813a40680c4d002002075216030086030520001f220320004641160118048400303003035054000c00d1504409400a03070f540b41c00c0d41d00402880c6032a008502c0240e0b0304c2e441c15802d2501003101c2c0c080030b0003410740c48200c5841c2901156400d074401c0101440a55540341400d0110031402030140c990b040381c51070742e103030b4904040320b03080484400225414461b83c80300c40c41041c0244007440c40001d0404000d405d0810a1a00400002d60303810042035008116204000646040c6072030003038038001e010074945c0c0c10340d000400b081146540280020400035002c90740b0b00128403c5113052080d50240d03800013840c0c00c0f41b411800c403030713002c250304001c2118031104200c42c016114101010307a00c5a104c0b00c010030b90780c010460b072481030903c80d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 604325296 1250 604324046 604324081
    0x2070b0412030e03010c0c050c03030405010e0907210603150e100e03040803040810050108010501050303120a0b0d0305090f240702131805070f0609140a03080d0902090c0c0303 77
    0x74500048450307030100000342550b800580000002d072011487c00b00b031007c14029220502ca04400440c0f500b454040040c100f004603020a92080302e40c0310001781e02c94081c00d4a120342c001965841c80e04088000e64cd200280321030700054800345c9074030340b00090f03102d007502c990341040010100410b40c040d100308904024000d0303980340d40c1c1503000c1403000040d0303000104003600180c40d07c400030300000e5801784410030403a04160701c99559a030529004000740d031804001c03a0b05500d039030000800140d6030007800c000a8140200002e0304520494190418154400050002d5100440d4001c2502181008224002e0324a80580f00c11a03c0a50020000b01c03104009041480c40685502c0303410b1029000d8008444e00c3c9070707036455014007503c000000c00c002807001e000540009a4034000007401d2034002044803407280160805013082c1540d5181c1c0380c2d642e00005d4019075001e81c01f00d5407044255541d0029000412040b400b544041020461301007040c000d40d220307004888011819035481070030410074031150 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 604326546 1250 604325296 604325303
    0x8090909010b0a060c06111207080c0c1b03060906190b0307030803070503040b0f041109070c020a09020c07080c061912020d050403080a0510091104080a050708070602070b0412 77
    0x88011807041920f42500e060010485911607100141241c18442c00b980c800701c41c6122152020029101222035900d82690081c6a500c1c0001d815581e40c45040e00303d20680c9005000c80c40351010800700710b0000418599001800c0e01a650075803a0701c402d40b44d40d41d0080d00d01c80181120450117070304000ca0340e4040340f115040102211b0265540361130b05443d640c010b0300d441c000031740000700700300074030890b029419000046400529a1072900c0c0d02e4000f080e111402d29584070382c01c5840400c500900c0b503200c4d0240c00b40c0041c0000d00301540c0300c0c4460000e50110000350710900500307400040206000c1801d040c4100003a14036480d200440160380c1c414001003044000380407440c1d04880c0780d0387c0c00b44050b100301403040000182c0e40c01e1031b00340903041c20300c001d090b004d00038104000c000381e26214001002c2200c6528002081e41c1c8504c40c0d002c0000d0045400064451180541c41020f1280014a11040744c000e00241ea448d242c03200c0d0102e80310003540c05443e041e1807003000b013000040d0100c0f0102c00722a00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 604327796 1250 604326546 604326551
    0xc09060e012d030e060708010501030207080c1510060c02031207050115031101020114190b041b23090d030e04020403120e04050a0516030b031005010303090612090809090901 76
    0x1001c2d1501c078142506000030003880d058044102c030340701c1d0b0188681c0c011500b220009010914000400812088050203480e04140e0042491010801e0100070f5980880c07680e4140d5082018058082c2c4076800f048680d0710090310b4020000460070701690920044640240180c841d480442c0d004405940c000c0004444540da50307a00091001c03481018000914450005080c8994414000a0030f4031180360501003004800c00900074000080800d80c500000302600109034a030150002500134a402d2501c400e102c00c0440b9001071f0036070703c410380710f04075000348002095100452003001d0030b43c010b40ac21603820001c00802400400e01424007204106001000546400e490381d8480c1444039982070100b0204600e0204283c05280a000d0241d001e01d1200d000c01c294686030031000782150921913484181075030343c5004009a04c00f0301010619030340b0380200f841300d56901e245c0102101c49520035880040c1c89514841605040c600034001500d03080781004c5d040070000c0007003224820300078007005807a66 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 604329046 1250 604327796 604327817
    0x101d01090318150f120e121209060103050a022107032108040507090e15010b040e0906070c1e0b040302011e0204031e0305040f0f14040c09060e01 64
    0x400034024191598800d650340920b41d40800d20a10089180c1d030880c8045911045840c14800c0e84031000c00003001052801c80179054040185100074005178100d000c4c640a03030748403040100000401441030300b1031030154240c039940d030401803500c41c0300c00e00004040e50041079129002d494683c004000c03104026a100d40b10f11600c08055203040181d070300c00c032044181440314001140480803c818090805c0c10b2032282071400c0c0d0b9076140c95822034007448484a41e2013140946000c0cac20406413094500f804580c1c1c4081d40c44d6051b500003034005200e1086002c9500000034001f40012823182e00a10302504c484003198000d076101c0020300905140b50002141102c030030b4011410b80c1c0c0b08140110b009030000901240c54940c090f8004c44d030014940c04203401004104005260098821070012120348204000281d03440c04680301d00c0355620041c26044480c0011903c000441c0044045480c00c54503550f980380800180300c2500c52010311980400d61408040203002e005095841c0c0c400d030140f5040c28000f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 604330296 1250 604329046 604329101
    0x90e0f07031a2d0f130f260c0304050301051308040b030c0f07060614150d020307030605030f011b0801030b0402010c0213020424050c0d0f03060e04030e0103060e060310 74
    0x21000e410f40c00c02005100140441880c6604074150441c40418680700c0040160301c610124400b41b800c010100101a2103d40300c40f0054258100390008080d2600c0e9904d08100308682e4130b40040c000c0502c254070308404601c81c014215005c007075240c1d012080b6824180381c21991891742d04028500c04003030404003d4654450722290003041060f20130b00c1c0c00a00a8101814203842204030440f080c0a400549200c0481403d800242c41d07250140c44805a40c0366900303c8101c001e4034455024170b40500c2151911841c00c101904914120400400700022002c00411308980d0b121080c48050910410789020501551042200b070030b640e400901160322141c0582d020408903405079000419202d603a40003181c10041c0e6074600b01200005160481c141810200390b191a4075001c00d01b04188181000707416021402a0410030050014107541407051403d414003400c542c0c2e5242d145030000349802c0000c04c0d49000c0c004400d02899020b0b0040c414000071061202c010845030808140c0043d0800011512 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 604331546 1250 604330296 604330351
    0x14190c090513021b03041a090d050604140f0c061c090213020414060c030405190816080c1008010504090f050a0c030b09060105010f050f13090e0f07031a 67
    0xc180c0100030060382c4981c82d0b000031100620b60000440a0b07042000b080116148807c0e484920010001e06603950300f005d5070006105640d80ba000030818096071040000f441450761803041c0e0050080c0c26206151011005940c44d00d031460140c0343d1080d000d00103044609404000b01800001941d00002c150700b060700062040c0c12102c10b03080c0e00c5134002406100c07105910b41040d055080a980c11420a41c2d0400102c4c0c0f207008034003a07180906036400107a0018040165400014061107098403081d00c24010045400c01d41400740051a00c00d8080800503410100e141017220009076541c04666402c190820001d40700b0110192941107402c00c03128042075060016885c424852090b440803107203540740c4043c4071040100500200d0700000c00400880e6000702c0d031240107090300e03d072865031031841104030b151500480070b000c0c0e02411042c0380400c52151940c0702c0c4805115600448a40802801d68666104e030140401070240d911422031419400c1245002508072500514031120411080b900f280c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 604332796 1250 604331546 604331569
    0x70e100c15110d06050a031502090105070807080306010e030a050d0f0509150a090608090607080705070506100e0105060403170a02151009051803030712060909080405030114190c0905 80
    0x1040100002e911808094a03c20040104011b0f51310307040d11071440c4c40d00b4002e95480c1251071407040e000a00095180e1049084034480ca03403084c03e0948800c0c0c0c3d41041c400381d400407a070481c0441c0380994040c0311440c0c0003880c07218149d48075000b0309110603c000d08a445030300c0707a80c020040c0300c0140441d0308203aa0780400d0720781310b502d40d2160684500c95030500a0241d20030380c1c000c109100b450700610450000114000f64020928207015140d92500f80c0b00300d03001d200c0c428025100b07000e80000e01005a45041da190121480d45402040ca642c0791000c024440c03046101c01452080b512034220880340c86003002c2d1078081c0d41c0380151807442c0c1300d01c28100c0000d0000c460740300c800d036001d480c1400415150f100780c035003010112450480d00211510000c1e640d1101030410028841198101001605950031070703c050407016800340031048013881c150302c0307907000781c0034251295091031000541034800e019864490b44441090711988486014040002d0608014000401c032620201141c0354684401811 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 604334046 1250 604332796 604332821
    0x30c0201060f09140619060f051605030904050601050a0e0405060f0d05070e07020a0206032206020406051b061006110a080f1c060f090e07090c080f070e100c15 70
    0x5500004c510101c1c1018400500d5a0f11a001a014609001310414030b80c2c42614403900781740b15010810007003940c030760150030b0100d40204881c130350040801c5800b0000e0010500700759401e01058541d0001500c0c40d01a5020f8240020f900300901c0d6400d207041d81100382c1000d4054605c41d418610b910204125a048400a071350585c001441048018651030030207030b104059202800d0448440d43c0004c5281c0300c00303000d1091086080010090000c44500054141903226004561719540d584024116400409a41e200d1074210b000340c3d40c1148020036003602c620103001854285909007501501c5040d98800086001d100300042c607000510313803000078012041a640169102e02c440c0d10124141980d603102d041100c0e0072302d24100401c50001400d4000c0d160540c2c0b01240580088030303500e140101a0b80400442402d0111551314107400c054014002c030303118540908195200c0c04251000c01e49071102d640c20100f002c2c2da14641900c16042a1580e500c140714841c0c0c0f9a04c4802e00c40c040d54489405203 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 604335296 1250 604334046 604334051
    0x2b050303090d02030301230303091002010c09090b0a030b0c07050709090c0b21090307051b010306080a030509300c1e130c020a02130b040f091101030c0201060f09 71
    0x4081d21008000d01d8548011500c01035156604002c00c0701c545c821070504030424107000c903202410a41d000c1c006c0d02c0b401702014000411007401c54400902801113521050049200c0200114180d24540221000b05c14050101e10312180b45540d010550320000b0010b01c0140340500c00113000490031300c0404000d0800742d1011a00350700c0390400c0e0410141540c480d160b0003c040081c0c8160036040e1201c5402040458800b0200e40d0f41e01610509522840f00c00070700ca805030440100305107031a0342c403031149044281d0301000265100e410140c0d5801c5100ca01038007255060103040400c0c5095905c2004541c00c0010840f01405002c21648040e0400454102c05400c66042c1c00d00300c2c10050710041c2112401c19441d00003542c01000300700515284082d02204503151401104401d008202c0901e078a40d01a00750000343c1794407007400c0010100d440c02a032165080000005034088103000c0c40140c0754000702000031144100005400608240309241e096540760340002a90702549490240285041c1c02d01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 604336546 1250 604335296 604335301
    0x61d01021f0b04050c0307020d180807092012010311010c0b01150e06030106140d060e09060115170a0b040b09130218040c03031202130f0801292b050303 67
    0xf0441607800050440c0d6609100f4003c20520035400110304120001038100880a030b00460640c0034804403e404c03803101031250341000901c015044e071042c1103108130104443e2050f40c0c00d28540709140309050340c10708020341800c01800030503481c40300c40e4044c100504145000079450341d140703c00144260f0062461000341c001481e405500310740100002c24044410070716540c10540060310118198895185041010500c0301286c5a243c0c0100007401c1850060015894540591580c0d12002d009802205000c40d8481402c00c0c01000c400320004002000c0154941c1c4100a0300300030141403030041c0d40262208036143c12070316220ba9182c020760055500c01840e000600511030700b102440c881e2000801210108000718442480600030b6a1349842c3c01c0444036a0000040c02a00415081c21070b140c3c2c08030800643c1c82c414034481c1045030422402488030701043c03103100481d44a056070802c00d58090f1000c2076400d01e40800014018544030b0f843c1d000b03500040105001007a00740b1012502ca5200105 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 604337796 1250 604336546 604336549
    0x7060e030105060f060a03020d1104030609021c03020705010e010e0d08030a140118090507090c051309020c0616031e0603020a05241b2b0306061d01021f0b 68
    0x20b041d03440501541c21500511406022030600e00c610041e201c00c040c1e000ca4072860000454102048111604030229100c0da1642420f01c02000c10203801ca100310358222140940c01d040030f2a0003951a0142c01400d5414585001583c0d00c5c20010001030402401c1c5c036030034115a4070012003c18690003074074195160b00e001d02c411800c40c0c03c1c000101201080400040180b640091088080c0080c2d5110208000800d440c0040c945803c030380204049600380540c2d0840c60354840d000c2c01c10044a0345d04101c41c0307035454201d80100d02ca4900321903481c0d0461320006030b40c0822080c400001c40d030a464001012021b5030380788401d034030307001e50312510f07040c0c980c3e03010410351419268950141030111040b2700b030710817280000101050303131001620000d100841c400c101d03000414880b60040341130070155100c80707040110400e41c50720346c0c3d03081c3c2120403840703640048030301e100344291000ea80072503e5801c4000e5241e20704181e42800400180e04500c241071400020109400103020898000d91012808100850 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 604339046 1250 604337796 604337801
    0x61812110705010309020906040b06120a091502190806031c03060312030203010608041b050a080a03022109010809072111010e011407021503090d0323010b031807060e0301 75
    0x14002da04040c100132020001d642e601030b10781c3d00050221b800003002d940900110300b8074020b0440e000c40040d8190708000b02c141050f00644000c42c41401d000e1040d20846020030100e01a07450b117041e005075000442d49020b03026020858102d607005040b0346503150180d6540189021842c002c00000c0c3c0c660b002002048800c481030300141c8110b0a0a60540d810001d0041541d00300401c00b40500460408950501c54254041809030802414800c40c2c1900c3e42c9200f96106c0c08944118014407030000b1a598000b1001c49440600341010415490440b48900445001e180500303040e4480c0a10b403c00142c110500c400c80c0503028241d5407082100d2a18200f005251610780d00f804c1c140442401d22058036030340084410380703440e40d80414070b0710342d1200d00118460654118418000d60000420720010300710000351003411135116a420b114264950950010ba040c182255910303030b64a000050180016480255a104650090782d481844058140c0761070580d2907845036020601004200045003070a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 604340296 1250 604339046 604339049
    0x1206111b06100812030c070b04061d0c0f0d030e0315180d0203040b070f0501090311010e0307020f040c2715050c1209011205041b05010c0b040618121107 67
    0x190b4103500b90b6141c0500c0390740351034100207909400040000000c500f400450141c40d0050f8002c1c04201c0c0074581860010020100c40c0b040d02c855500ae101100490407001a4070100c08a01030955202c040340e45007449400f00c0314003001c40502c46100c80840c01038400b0415540c4160500700e80c8901e42c00d18458520003944000050b803000d80004075a40f468540001c2250111492180c01c90756503025030618050351080044010801d50a045025007032560010054024450042c020044502091001c1d550b03481400002500200c040c0c00400b41032626034046032901d001c9040a04124500500121105480e20b0210411101029042c0080049144510651103d6051540c0340042110100351788900e040c15230240800e00040030010f9911451560201880490040c0414201842c2041c00e120600c60800d4404070500d000191070340c80b9007804048240c01c1a150034280e25207848001c0900310051a995031248601040c0f00041c4213801e00080010041d0f6078035413900315101c1c200e030500803103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 604341546 1250 604340296 604340311
    0x10f0e07030f02061e120a060f050d110402070503190329101e0320041a0304080f120702011508071712040e0709050108010e011206111b06 61
    0x840810300c0050a18411081c640383c045522071344903071100c812410101d119070f500c2ca0101c3c00101305010040c20110100c1d00584d0426030a11100fa110040030403007080a2140703030350010303402e42d0f101c0111b21500c031101c021180c06003025162102e2a00c4091856000b02c000d409004444000c21031269414032554000351f9601458088500240c0b02d040d4030003030a0800b1610418454110505840c0548420945034420302d6042110854441e400b400070320003040f160456401d542c41480c01c00c020001100e096901d5103500f0f52100040e81070002007500001c20403211501d007000a5040800303080098810b10703a40300b46550307040c42c107000000d003940c2c41840042c0d003442e529030b0140007554000c600030094410f500e01080c00d289030309070840e181844e06054940c421a0001c1c0110741e80200d410480e00c01d00c0c058031072001c816524001141c07081c40c24411b0404c080904c400501031513070f1007030341403603039a002c0d00c3c0100321103c0a55600c001075000001030001c10030007800788154010140031441d032241d031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 604342796 1250 604341546 604341553
    0xe0306070507021003140705041e0602030a140708030406020306040f090503220506030106021c0806033c0106080f0109080a0c1e111e152109010f0e 65
    0x1861400540075018030b03140248500f9034043c1061810f0701c281c4c000f404e941d0010079009a14200740c5405006c540c011700920a000d40141040e11403169581203281c01c80d8103580c0118542007445000701e030a03410101c148511071108001d2070012511400144d4092802010f005a890038500200300c101c0b50700817003800c221414030625501282001c0140c2e00c0196050311781880c19440c044a4580c58042508402d41c0081d0100000c6506d550000e544170400141c002c2d0640000780b5104140c0b40410100c070803c0d0705034055801e91090f21303840c1e0880700e16007a405a40364901000a10002c589543c2d64004109903075440b0310800ca4010b0410400c40c1194115000700191a8961600f620610440034404180890450702e2000c0100c007640107900168050b1290318003130541c0c0b61268002074180a00c030b20540541500e000c000e00640f00320892040000c0c91049000d12604410300035402918600c41441085010b2413095248404070a100304864000010b0a11414030403c044032044030148809a1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 604344046 1250 604342796 604342801
    0x105180114010308090f0d051b2e0302090d1b0605040b0306062104050f16180b04061211030124170a021e01020c04020f0d0902030a05070f060e0306 65
    0x610195000d06590b00039941300c2d5581c030b07804042120b845110900c41d400000c1003400ba405e1050202c0c103205c02070000ca030385640440c00392041241010a09410b003810346035010000e680801ca4003801c01d800d000c11309016051024101c0042e07000350b2240b000303981910b0348002d10300310440c103000d00101818030750038018107050400c900f032200c0c0d000041213070340105400900f02c02103c001480c0220449030030603d14010745810b207070a03a1140700c10b0303100e00124450110320395001150360014a041c1c0b08032513501810700d06c6a40241000c0c2849070801904195140c1c408203c80524500e10000a1300511b02a0f46940a00f0285401c441c2a03002c180d400c6654400107442042c4103000c00b000b182c81f980e0140304151180c40605003000045c000c0258406280800380f540c1c0c41864184c0014500240c0070303035041c2c140500600c0280d00c5100012100e000d0100002ea040329044d034400c0459500150840d400d80080d6510b4501d00078003078003c03410408200e8005c000e079070ba110380211091402a0003130101030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 604345296 1250 604344046 604344071
    0x18041b080f07020a110a120c03060c090501080403051b2401090501050a060f0311130501030b03060702101515050c1002040806060f0609130e0c0f210a060e01051801 72
    0x3a207a40000a005031171107203840c101a520207030b10001818a00152601e02280ca180c481c1a403452484215191400c0559a00509004041d108115101038481d140d842e0303034a9501f100c1030390164400c0c101c04031740c40c20003000010042006c207021100c9402d04a4420440c40d44410880c00140c1c00780c0c04460a040041c002500e440320440c3c1129610304018103043c0c0203c1d8264041e20782c0d0041402e45100c045100f900700394580c4058800ca403000e0f201041190710300020305031140c10440fa503102580c00640c49030580c540036030004641c24110300100e212a521180c80301c0891088004030000900702080714000c0110902c02c0e080728100e0000110b113418503081c0c85607140c000050420b0311602941910b06030b1900c40904403226001e0080403a070b413912144c40b0f0003000702801600070589100317940141016090400c5404840e580c001d081c0c5182c0c8119115259080c1e5200c2418650390203440340101c001916130051200900314007001089529044040f0300f01c11601b0702240307506a04248024041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 604346546 1250 604345296 604345303
    0x5030a030f111603110a05010c1403040c051002010b120a03020706020604050d1407080d1401050d0f3306080c040204180b0301020c1b0f03010c020d0518041b080f0702 73
    0x80c040c0000c0c20300026a0f0f1130509450207420316802e40031038021000c03810100001035210500070282c9031a0000c072103440400785416400215001410014407100070b0015191a59291346180344505c0085031404540011a46500082501844641c000da42e50410545c0520504014211900c005c00c1180340c6600c550390ba4420401d102c2007806400c0c00e490b421501c00c2070460303252540013440349980740042e1a004005082c900401186800684004a920300c1d00030190203065400101024018402e501c8071147c4e50640402c08100d6120b83c91150300c800f02402030b4401c150400c200000752280b40000c00c60424084200d814400c2d84104402d100d11225030302c40e0701d04052200400603001c284900030900a104009500c281032044c0820703403400804c1c806c80d5028000c01a28013010b1500300ca41030600761000010001c2c090b82017849280540740c4170b00b000e0501e81589042c443d000702481c0d004a412a4003450500d080503103100b01070510b04e500315083da9000740910315400020314010000070744 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 604347796 1250 604346546 604346557
    0x207030c080307170403022505060f0f071a09012a030528020d06090908040605070314030c0c06060102300c030409020a1e020c1c0c0305030a030f11 65
    0x10790700100110741c05034490200040c200100025540040c141800d0181d40e80701c10502e00b00301c110f01c03100c2204010180070300302c1d000c44038013400050030416018900725150b00a14100020b1040511030000440c40d19554044285c40d0501803044604041d480e0742d09441c3c007d1a04080d481c51200014092840304146020605140c0313000166512070191740300000c0810801341c800c40884100c014000c0301507900800300d003524008108000ca5507001e050041d10b428980242051100b13000820019005000a0482912924005640f2003400310b00384010b401c240e40d11640c0d00b80c04900800e03001000c010040e0044400d00040800005040071420003481c03c0c5881460140d09802d111086d41c1e404003a0b0300c0c1c0b9034400042da40c996032591440c0d4000e401a400079030000742c0c03034500c111100e101003458040001b019406480706811000500c0107030783e4a00340c649904035401e44035502046008101001940c8903001669445150b00d40040a55140f0b00d400041140f4003010440200344110840300b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 604349046 1250 604347796 604347803
    0x10050a06051606181b0f050f0607030e0a0f0303090501030c08040c180908070620072d02040c090501030f0204061d12060403020601030312021204060f230402090603010207030c 77
    0x9034042080713211001800350001c018150344154404001d05c43d22040801d05440d5080b0041407001d554108001b500300840c400c1c542c200404001a80100c0e00c03841d210302c411240075007445145a5502c20850001c40182e0068001031406032084c841587d06016a4403c4901c5240801c01030406803100c20221885128900c40030101400019036811030f500100c0c420750f04108041d03124003082c2004c0d405440c0000050346240c018450000168040e9001d803100c0581081510320150031005030894a82c5402c400980e000d110b00f402d55005030348500500d5421040c55070345284651803c0009021b403060740a0308201c00740181700901c15280d000051200b120100e010001010702c90801144441c05100c5ca01d010a001e500c04100a041d00020003e048903c69680c1e58408150046d1050407070252264640b21024507401140200b0345c9178007c11602c503200240090301038401001a1750210001d02c1c0d603520740c18100d013044258584402c14030f61050041e8000d52800d042035074010590185c924004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 604350296 1250 604349046 604349051
    0x60203090c0406240917030306040509010504050d0f09050619030608010606050f160c06111005161107080303100512060903030118090f060e06090f06010b0a050f0310050a06051606 79
    0xc101003071080041000800d0100391040303006411041d407d450b0782c422a001c40c006d90501d8042804420140b0905100300c1d000005000307500301c0c0c50012125401c844070341c60100103083e200070880da641c080041601948040f104043d000e0310b0400541070703850341e5000071050392414104001e041c3e0000f013183e90780c244102400d507541905118650341c010545e00050f050000f05040801c40c1038000055080120340e100888013040d03080c004110585004545240445200944078a6000d0294020502c031591440c141c1d117265032078181162840d00304a42d4441c11710018101002103050900c1c00500420305c0001820b0f480c500780121a5032803006100b0124202c00b00610b00d29200115405011a184e00c02c111b0811306001c0d050440241501c0050b6170220300404011485001c0c00003080e41103555028040e001c260b01e040106541c51708041560414418204035074803401d001200254440e0004001e1010a45e00f04400e000090149070480c00610808114421031141c0c80c0e0000d94000740c2c402c002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 604351546 1250 604350296 604350359
    0x50705190e1e0303040b04082a03071a19020619050f1b040801090305040e06090f0105060f0d150905011703031315230603030f03040f030306050904060203090c0406 72
    0x11030314520455001b201c8500d4003043c00300300040007043c26146148a01091404414034624400701d4503030800d00a0b50582c080c00040100e040040200448103100112a0341480b04c0c02444508680c0304200680060300000104801000c540640c1d40c1d007102010303001c0040f03107070000b40c0160041c0090000c0641480d61090162030041c200102c40c0a081d40000910403d4890b280c00341c4960001d0081802d000d880000165240c10f04002151103070030141d400c081c42d039103031005025507a070100d84030141d03240d4100b00008a84090b40590111076082c800d250308018a00511582129410b030800e40546022604400c040b540c00000d9980145a10301c514041c84c5d400c1c1303050080c40d8444641010143d00340640040d46c3d40003190f480300e050b00c00741d12001c40b82d0745860405450384180160344849800510200c1c020030901071121102620074100002d2240d201c0c00042c104000c11a4216000d5800204108840e0814007080c1140c1109403024024182840b82c10920054480b04030322071078110904 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 604352796 1250 604351546 604351549
    0xd0605130b0a0e04141e0105010501140702100e0a0303050301092a050c030d1103090d08070f03020705033f04020609010c052a040e06041a041401050705190e1e 70
    0x11001c00041104c080f500c01d080c5801e001441103002186c0380455502c0c00c40001020750160724040d000d520304003c1c15141a03200e5080103110300f82c5105540410404011564154031000692001b450003034a6964580d0300d0501c0130401d42d0400302400c01c101c0006068108a0755003451011409022810010780302d040410340700d4070f1070081c400210241c1d41080d80b410043c050200082d4092041030017903540c0106c044409a800c2c2205580030070000391882d240031842c0e4401e07400341c028184244c00b0b5a00e400c0a0351200ca002e244002050328030f03e001c402c1d40a2a0039254901103401d4004210841403a2906800254140c0105900c040c144414200c095040000c1031005008400c2002d00900034000a5000108004480c98820b4000ea141170b000380c84200000038150f12071366001c1da0554698036a414260085000540202d4442014066a2200160070301502d840303002107645035611401c0d001140110543c40ca01380c541400031010305418191070f0010401e5109031440400c00f0721f145420b0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 604354046 1250 604352796 604352813
    0x306150708040f0501021e030a0f0203070c2c361c14030c0403020f0a0812032401020607080615030c0403050c060c0a260d0605130b0a0e04 61
    0x40050081d1400500801d643c801c075003111041c0d0b8001c0e400c0350440644801000312011248000e01070a90003800030902e51881150501d4111005105803820701c1c07032568400d94490142d0b0000d110001f50110b16080100c0e100494845d0350b03072091a8482075040c0b00c100500312010600d115003540d002000c1c055407101452141c42c00b843d460034200c44099601c0030b2800d44110fa0400f2100010320b90000b8030201250303040980b40030311015003280d40b4103845c680c01c0000c0042454805504200010f5000514001c18090710004d00c08900700156645002d42d0a11114004409030104081d0744094980003030764002003069011490707082c9031041da1140000194001284512600e0301d90001040080d805500c0020300f0449104030103d07484020210104172840c090110791001e2540031801510218500100d04090a11400c04c02000d100c1071054014131680185400a0907a88601c01044079007003288100c0d2550003451420013040c88144005051243c5d02d01c101d031800031286010400388110340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 604355296 1250 604354046 604354057
    0x903040b1e04151e0504050108151924030903021506060d0e240f07030f02090d290618041406100e0c0f03010312020a06020d0e0c0406030503030615 65
    0xc2c01d158003000780c0d200202085982d41610484504c0c00c14826540360040c001e80d410b4070381c1610758440750f0b80c82841aa42400301c945407151321440488954207030b240740e04540c8015040b4103804224503c18200c07204003201d04000c082c0100b500d0400340b040420703070110f07034074403c0325601854400fa602c03140b00040340c0380201584480344a1400080020740e40b030005d00503954640407038552445140600074500214000c880b0700d179102100f400007035803041c400d500904400034501c40041c1450007000209400703c208800c03c54403002c04038901c49035000d0700c2c80ca600c0c3c9440c203c4030504c591715040020620300c102d02241d107054002e040012504002e03020b0101166850684121585841c02481003d0250210f00c0f030080f40740c44980c04100703580c01800c210b44907040e90801062070360b4a565509040d20a01c03000a0b4210b006103858040000d40c44e000404e41c0c0d00c00d0701c1e00841c4000612444600300b80c200102d1a10036890700d00b042000803c0032060701d61000c0112041400040390940852452050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 604356546 1250 604355296 604355309
    0x90402040b100f09051804030804050115141e011b1113140a060605090f0f0d051e2a01120203010801090606150903021207090906140903040b1e04 64
    0x1800c1c2c55014103940a03851002d000d185680d0014807036600c005100281c0d00546c03841104d146e04100150200b03009061154001340b160707000241405400868034001000b68114440f40c01044600030440d00d0301d4258422032002030031900303203003101f14800a8850034007020711041d400c2d0403203a0760081c00030070f00d0b03c2510600081e0034030201074030145d00c4200510203c030307883c5c48140b540f4020501200442c418601901c07403680b2240c1c904840e20b0304002010103154034081d0300c08a00001254192242d500394413040d4840c000130040c0c2c1003611310003600010040110340070380e44000303214107060020302c0c4c0500081804c2411031942c0103602c40100c03200442030749005a03250002000050b21601540400070715402030004114054171231421240b0b00045040e288001070090f4010320241c500080c0c12180b40d800803040300c008503541d50302c0c8401d4031324120017510b1083c0c0d00c1c41d80c5036210f54a10070a039070041280b0b0255140c07500706119001d49009074803080d01c9054034400e4101c2d500d0120812200075162 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 604357796 1250 604356546 604356559
    0x907030c0806100b03090a02210d030e1e0606100207081c08010f0303050706050a020417031b0c06190e130905010c0305131103010f0c020f0d050f09090402040b 70
    0x449000359a900d50040c1c0d141045040140b0300054201c135240d007541d000f80b400d00064122481c054007046200b948090107207440707401d03526a180b5401010010710607030218549021078155252040f2904000c1181d0544140380d603104001c50a601000c205103600038021503840c400f003170780100c0c101d10f48615500301040500c9000b54148403d0313010700e01c0034001089961381e00010382e01c1e000c0c0e191001c019844010007049040c03200b46c00280f510740000703500400107800141026030704c40188044111a000c580e49542002910449c80c03000c00b400c000c51444207400a004581d098800f04d0b10324400d80004004042d806034028000d584148440018994010003520340521821480d2004022209003203410b5071901c01d8005100b4000e0084a10030340c4815070702c40e0001c0d25501c403503100c1410035403410781c19543c078241c000e0041014860501e42c450745a00034051105406441072410011494000920006110f000c03042a032030011101c1040e0141c6010740d440d203903440854058003c4440c800d0780543c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 604359046 1250 604357796 604357799
    0x3090c0a060809060c0a0e041805100b040b090f1911040306020d05071103040b0c031c05010303090602060c04030f02060c0f01150909020d02010e060f07030e01080702010507080f0907030c 82
    0x7644030034264003440f400303000c0d99020f46501114146610a01c80b026003c10400c0e820311a113490583d0240300c10719000c0c0c41d00d074800046a510300e410820300d500c40800041e0303903c0c6025910704141c0705002d490403041c4c4080020742450140002203620081103001c0a002141d0420b18116458000d80019122854600d8035642c0b0b9150510103034200c4003c10480f249818002130105100c0c103914154070b0300d1440035514003814000e05014991195000301064070040003214270584502410040004100200140c0c6506500e40141700b550654021011540410705102c1f82d035112104540032640d01c01a00c161801c0c1c075102107031441c020003148401d46d0203903811103002d421040d00804100441c0316042c403616070329080c108040300c1400c000650002003040302140154051000f060003100000c018504000c403440850702d03d5844050100c000070b084601030302d1107581044006030844031a0009000c545011140244100b40c010b0040c83d60485c20b00c00700304049420b1010034080d40d007200d40c070070303c06 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 604360296 1250 604359046 604359059
    0xe1317190e09040c0308130512151b160303240501030e1516050405150705011a060d0b01120e1501050607031425030807090b091503090c0a 61
    0x140c4441803544049a40d80c0000728903407820340822071180e5400030540c501ca03800c545826503030f42c014001c11624250300a40c003050035510381c1d640f822500d0040009041c1c0c500e4480d01c0c2c080c0800c01a048601c0c2d0154181c0a840901d0703c00140c0d8800b280c1244002d5a100050800302d010303100e580308801c46501600c0010746980e003100358000a41c0c6080c2c8050281d0400035054aa5403405880040c9a00400c0d8001c118100d502a0800000e0f0016181c96400c140e203540025218942c0840b9105415600203824401c00c5028041c1c0903101c820450454000207030500414424407800380510007070341d03403103086039520b80c041c1d90b000d08141c411000803c120303841c142c0d4581d6643e1803003000750051502e840000495162110454500d1949962501190903d80407810a00d4109644c1c4c22041c080f0010303801491900d06400445050003513607400414140031700c000e030448400e0b400064842e0741c00c00601900d03441d407030810b03000341d800c0a03842d907500d6407031ba20381d00c0c00d0070f1014071002d500c80c901c0c1c0c10000701d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 604361546 1250 604360296 604360327
    0x611030d051503060c0f090111010e12030403020105060d03050f0a030f02030c0406031a0303090910150504090506010f1409211f050f01030f0201110d02012003010e1317 74
    0x408190f00311419034840814500c014000d641424a08103010080f0040035449080d1442070300318244e0010406495040b8140d00b8802c12150360f030201d00001c800c00091660900856400c0a400e42e90303408001c000741c90041c41449819290b02d865540062001300381c9120750b0007025a0942d0300011034490501070f0f40c1810951052140c0c2e4002405d0030249004840c500811502400c4010025490a10310b00244400c0d050024032000b02200a40000150510b000107850500c0066a4680b47d0f901e09000840c001c42d100503010504200340c3c180c011380d0454100c012040d0341a10502c40e95141e2940500003906440400060184150402140040340c08009031903203080002c446003010000c0012103c004807201115104403480051004202041b108000300240d103006141c004a0381280b40301d050710740003c231141207006070b5441422149100240781d2140b07410000a490b1031441d45002d4640c180018040d01d032108030150080010200101e810f101f103a48045280304507201e256041c4055078 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 604362796 1250 604361546 604361581
    0x10050702010606020c2d0d15021902150f1f030c0306051e0703020d02091c020901080f100c0c0c0603140f0403020d0f11011805011b02070611030d05 65
    0x26200e00c1c0b400750313401e18002c41071a06c00c102d03c00040d2203240c2000300a015413010700000726002100c1142020200b43d2002d11507905c2601c0204c050f90b58601c105102d0b00840d84030303c1540446d00f0034030750001d401000307101c03243e00005441814512515800f144202081842086040e03440b11030200000b00700b10840d00c1c404a900440e0100019524080200d4840c000c0e00c491322070920500300003d038258007a9003d441515440c000060a007481d07000825040501c6924030546035280c001e00c0bc003149800030085000d000c904001d482c10400485000307558014005441c100b145d12016040c0250344500703400704d20745400110f00b500c000d0781c50380081c00506007001d100151200c201c001039000c0300700303090f414042ca50640c001d104246590130100ca030041d405550030204090059540090442401850b1840c0b101d800b502c00154400c0c03a080303084400380013084442c04c40d0020210342868000ca2800700711200c40c10404802004017032120f0441c400c503103110952a10b080b0a1281d4640c40050000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 604364046 1250 604362796 604362809
    0x40f0905010b0406120903031409010902031015091e02032e150c060e0304080d1d0f06070503070b0a052e0605090a090603030507020907080412030e100507020106 71
    0x10907640c0760300060a440c07180b03000d0200490b4a81d00e5061068070143d000c191101d000385000a401d004010040c0904802030340d031044280e445440c000c040d854103100011a144404804003c074408607224550361040600c180c0b00155510b141080341da840c901841d20701c880607030704115601e240607003045120000c1128003221545000c4c59007802217a01d064030750b0589403010520803007550070b56812182895050700c1210015240c0a0041048008201400140281c0409401145c0200c0002040e015041c1080721943c0c40c16061a2040c1e03c1c0e00e0707807002c001d110659401d82c1c0c820351404c22500d1440f5500d0010300482101b010000940035030740c0214007504c0e509a400860907445041949070588500740307046210800e8004015640c0114014481d504e005030203a0001950340b00248105c860980c010303800706000089090851820101540d8040c0c101d0602031010b0619032507a801c1c0680100300c0f031042c10799980e0f100102c210108070540e41b060201034103004518180c14000e003c1d180911858 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 604365296 1250 604364046 604364051
    0x15020301030519050a1101120f0e0d08010506033601090309090c02072705010b18100e091302210d0914060a0306030b101d04020102031b12040f09 64
    0xc04010040c56101a0f40d401000030f2607414413503250f242c4035004070400325040c0851119401c9040d0b956019000740750107024400126070f00e22544035401c007045140600100003150005204595a00f800d0303c0d008901e00c1782807525081300d4801201c404840c0003002000a6815041045420054201c4901ca910a940f141d0f1a15a03546005080d84c1e40c415503640560056030080c0b005048142c80403000342d40d4000c90480018074152800e08031130080c1c1111428450008121600c0d101090301c80d00c3d13034030003500ea084000210007001401020040e994601c201c1d6030501054100000d594961140b40c7c008010410592902c1c1c286880e078400c0a0320940349010302c2c000d02c1080c60041d1012800c5507840c58107004440c1d0000101300e40343c2d1240740d80d002070554542010001c07885900030b007032192018080480c1103500b85040d1f03050a194001076000781000d14020000141d0340482661304d0b91000107128804c080b0b1441684e4240441400c050304510000301d00000e41c0f000000395101100d0604104 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 604366546 1250 604365296 604365313
    0x1020f0403051b061c09050316030203090411090d030509060405060a0807081006021b0d0605070207140a1d04060b12011a0406030512030c0f0a031d0705090a0209030a150203010305 79
    0x1c4c040e150003504402c0e940011000e408018002140c6c002d91a0341b442401030b0384c6000180000885002c64114040c0d00580c400700b4100d0003410144078110f0207010054110b030402084900144c403640090034028100007001c030341107446031911401d480c050440144625103d100340030b0020012803045841000186a00001c50303101d42c090702d01c070003e4841650142082c502d040c03040808810701001907541000c5005c2c84100403601f20310425010302500da001c0c01c895480c102002d624048000d03400c901c00c14070301c101041454424030b55070307600c90740389074503541c00b550342d070400382d0050440d0032085402030703914840b1950b50740041d4031061050341c1c4030307020750a518070380303400c0c001158118000180594450680301c52811409800345070300c011510141450300c8070380c8180001c00e1300440d101034040780c0c4600d515000300782c8680a6004031035044000b000d02e2843e040003e00e1b030315405810054580e41c0042c0c038981704d480a01602c06034981019103040e1554a4181500c004d5000748001c0d500c50250240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 604367796 1250 604366546 604366549
    0xc0c0409061b18060f0c060e0a0b070906020316081e1c020c070506031807060e040501080102030f0106270f080d050309060f060a030f0606140406120b0901020f0403051b 74
    0x29500c07480301c0400f0ba0142580c148081941c00406040290301071003c204811400100c0c10302a14026611000262500115510b4891803000d00603000c0801d0004140b0203001e000c0e800410343e04a001c1c08139000409004034140031000344250b1080161180c0034005500382082140300501545038a80802e01c1070b102a02400c0d0b0484c040d182544482e0f402c02d4008110500d4000d01454204544400402040040000ca20303d03080c540c0e444000070403e0403003034104614061084500408a44000394914a00441070f080030031414040e840a0003801400d8407085d000080a00c102d91224040700301c086600d424117913a01c04100d00c100c141610800d2100403209203c4d8060302d025142c100c00512280d20b40d0003e03c1c6040b440188110741040300d180340000410314142c283c520060142400040d4907050100001000c4010f5050b5030195040ca40c00700040341c1003c03480c0307021070b03044000e00c50345444100d60315000e44210211420300010201e004018004003080c1004080b0241c651503150200303000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 604369046 1250 604367796 604367807
    0x2070611030706090c05090403170a1b080c1908090d03090803150310140f01091a04021b030f0d1505011205070905100906020115080a080c0c0409061b 66
    0x3203804145810a02034a80062001d803c039410282c82200e4694080d501c03400401d09054007140e0a80c001102208a03026070112212401c0c0c00c410400c00c1488a14409411200b00480c841c1c044002c004c5403100142c0304541078130680e107201c51048084480030b160010014000031003a908003585006254400001034000c1c841d4862040c0d001c901103046599441d07946200300c00310458240c041c0512041d44091116504c02e01c0c00441d00500e18004608196030809943d00c2e058001ea105685010340c0c4004800f80380400303680c0139804980260380c44c0701500200072000c14180c43c0a1403803001251000c0048042c40c040c00313614408003010040e80d40e030383d041405803003480d10407140450480d10100d180c01c00281c1156900c21071500300310707003890380e5100402d100c00c480160040004e200c502e01481116428003c290303900808003440340c00142007131076071502c0d2a0382daa0014103d01c40090f8010120000f403100d9100b807100208200315a80c101c0c20041d01812100c0381e051090403030501c0503565a0b0003813 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 604370296 1250 604369046 604369067
    0x906090108070b030a1103010605270f060702011b230114040f020319060203090c302404060506060703020d031104030c0b0a0201051b07030806180a0606020706 70
    0x107001030112915007490240c2e243e002909a080d61038032040e201085040442c01140209440c0c3d903184d42c0c6800210021b0300b13881001e0f5001c2103640890308540200d96270fa83c007c907600b44c0d04940c0c450750703071001e88016145201c132505150a84403000740d040051107400000c50582e00c50b0343c6100e4a040305000b01040c200c80440505038039524944d404540455400300c0f050a0907407020301200c0720704c00202c1c00071301c213542c413074004a62140d000010440311460030b001220140d0400d443c0c1a200030040700d001008640aa20541800c00034161105913a1004000301c140040a841c1680c051010203169120380c10030885090341d0700c80c1014040344c16414404112860160190301620a980d49a1000c401500806010a081c08002d001c0440490400c10074200108422022a559100000030180c00e49600811800d03501000244000900408104464600754980f505e04040e030740d940000b91141d041c920f103c5e04a049001c0821500c1c1ca02c1e9445030080d118a902180c4c2e52555520046642c000394 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 604371546 1250 604370296 604370309
    0xf0610081207060207080c06041101020106030b0109090c15030f14151504091503050c0406120b0c0409020705010222060c03200f0a0b1b030601050d110a090509060901 73
    0x1a10078086645401014041907807082d41c0262410140c0e854007400798002001821f02a04980e09010800034000c42001820304e0a00090208a1071a2540007009905105d4103480c02d031034a0440040010858070580917050460900248101c403400080c001c0c1104443d100c1c4852400301c450040e9540e91840d144500b0b4900c4106070508070785000d00c2aa085254034a00d4010010311000c0b8040140b80110404100c041c0310215043d807840c1009854940b9064859008d00d1904c401400710b00c5864160348902604101c048000751070b018804805c42c461544410001480401c045c400c220041d001010300ca800c0100384141a41c41d2425050149483d210b0040404d0400300c0341400280180012200700041c40d00a003c0c0e002c1c0103000c6400c2c86803002d543e8480742c2000603c1010000c0300c504a80d000380f43e0000d00204134195140101052101034002418031a001c600712050b130055400000c400714908600580381d0441d0840500018801e0048078802d24480c80000c003103040c40300030305048030300c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 604372796 1250 604371546 604371553
    0x3081903150f090e15010b0c060a1401030212030d1d010b040b0108070c02010c020d03090608070509100c020319060b15161209170d1e021c050403020405090f061008 72
    0x10701508030009080111004a40340908074841002c8411285c0c81402880c1010307000303540e055541126414090300410f1030101d146032000840c00301e054114410b054950646403801082a1207004620b140030303000e903042c1c185084c040160000c60f03d2140e5103c48168000c000c0c001b076a44c3c01c0400080d95002402180040c3e082000105542c1c410009d10102c14010304180c038403501190081003c2c000044003e901085800c0c80400c1400c0d07100e030809030300a0040ca4224104882940010407460200f8400020840c84c0d07130b61728013599024060304109444c880b022006403212841e24002919885003079a20031001d5208101d8003411710001c40340c0384142c1680405030004e00d59210100131103000c4410701081150321020940d411015056114151080010862a206201e004017024000108400c0100704220303030039512034000804c10041d072200d07002210703a0051003100f1180d0380035940c0041e42c02801c0105004100b0008540601c400a40c481030754102e0783ea4218141c980b240e28070800a0551 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 604374046 1250 604372796 604372799
    0x2090402060d0f090b040b0f090304030201050d110a030f0b03030426010207140c0f0609060307030e0c0a0902250512030432250506090a03081903150f 66
    0x5031441c01411411121500001c06185140500302110030110f0100c403102c0e450402d01040c0b00440600650006070742082200900e000725039540c4034015480000c0c18017502003854004111190041c0030702007041603146486032182007004010b05840000c1c0400c0b2490b143d0b02071010308010044600b6030b842c1091140300d200d0501e42c0440005903c154581d0255400e1020b02d000958101c400031000e17065100425540b40c07078100304450740300700900352803046008104908494036010300f13481d408105824004bc440f40c2c6080013604040b0f03141031f500d500220082c130109030801c459010f405030050542c00364a0000307070190700c04414020300f42d003e003d5510807000c41d405550440300071988a40b042442d055000701034a40c03030490030b00c10141c0205000202140d40f41301c010400c10344200344403040641c442d80c003c01da0020b003040708074014107004072000035a08010313031524007440000b075600a0f00c6964688403414480b2280003003c2d402c000190a00c0c482070514603d401118054480d04c1c82c4c0404980d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 604375296 1250 604374046 604374049
    0x209031e07030b01030f0c060f12090201090b210609010602072319061e0801050d030c0b04060b01111204060f030b190914011d10080304080705180402090402 69
    0xc2041561850355100d4500d01100040035400403900075407294456918203c0246403503191055550003241c00c00500c80024a920365000c00b114050201d410f0b400a4641420700040b1400041508402402200000c02410903031070124040a2000399008030103c9407230303403020001c81001c288141e50050340002000e000b0f41d6030030410010451408160102c00e030501728040b4000e011401e603500f4084100910401c80307190000d04030507034191800480e0007150240040502860018000c2d6801065403191103401c140c01800009c507040e800038103590540c80d1500c0c0c1200945441e40d15140010816042815514400075466815104411803207045c81d0510204550380380c0404241e608054aa030b401100070f446030640704412643c0214000303c41814501880d090312148014040071080780d0004020b031018450911202aa240004d0329041d100c6007406c1841c183c0302e801c03003c1c181c0000100003d003a200014100c0498100740e5840c80b90451a602e5014401801c03100650411f442c0c00009006 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 604376546 1250 604375296 604375333
    0x31f05090103060e3903010207200301020d05040c1508010623090d1406010b071e05011506020609120a0f2316021503040f080703050904181203020903 66
    0x8401c00e81c212019140c10712001e0840e480c4880c0c030812185d01c0038810b44088040c410340c1d50700590b410380096182011035175980020554179000c2d032000880c090700b001d04696083d01104d11140c07003a13005101508090a240c0c0c032018551041c18944900d454080b0101070190a071603040b121152a45910f8907070480b280400b00c0c1220441c104843e5041141480c156910001c1400c014007421014070029a0101d403e464440103812590604000380f11900005845d020112a203904003180d02001d40094500355003d00031641005025103035002002c01d0580c0c1c0040c14a2007071011b6002c40c0c0081051081c6140d040c400c020210000803414800040d00f20b0140b80c0944001280c80c190503d1040d9048844840341c0210124181d41c1c042c02880342d003949881d04031001340344264140c003031171800c06981d0808640300b1280000c180c60400f04802c001e060203801940e2400d00040c109000840b12100840f03032565a03e102180d14880e40100710340454880d200750b50039084090300604500c00702e0400c4006 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 604377796 1250 604376546 604376561
    0x9030f0306041d1e1c030b030a08030f0901050f0415090c0b0d0204060e0a0522020c0703060506040e16050d0f12050301050312210c070c0308031f0509010306 69
    0x2000b0b0b03121045182010b1101ea00c114803120400003038451040314051941d015181c030a84940d4603070008801060b403c46808221000b4010b0b820b00142c0c00002d13201003802c10036004006485207201000b0404044610303102c10340306200d8000204000d950f03030215074a80d218160340242010310540d0b9407982c80b50056001c480894040c2d043d02040b29500c0c040041941d0254034a20307605500818100903207600050309122007402203480384011070030b0501144007032208005401300010581450100d600580d0b044803414114a015100340b1a00c1c0d04110015200641d6241d0081d46820078505003000c0100300e0192420480416018131482d101c01c0246001008000b95440d200041c81d010002e540c105a9613500501a210b843d142d41c0b40a04060926041c0b079080c0424440401c0b140c0c0d494084240d07200341b07000c80021200c0064480900b0750b51030333019100005040c10000c000100c18050280060361003507655017102110004105064507100e4030600c12070360000c40c00030040c4000343d4940c11004c07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 604379046 1250 604377796 604377799
    0x60c0c0807120b180109200a03080a03021b07240806090402040b12030d0b100503070f050a0e030f100b0303041d0402040209100e0a060e0d02010c050c04060f0504060e09030f0306 78
    0x80c120003003013440382110b141c00b0044903040c14104918818000c0b4201c540d0342100100c60301d9489034030310348850400340310b1205420708150303000950340704000c3d6407413a0300200048902240c2c503003a00d41c185030b81c1c03403000501c034150360683d01100c400382544148010351080c00c028222101e592103136400d120103400800c01c000e9000d0025549040c1b501404c1020b480800c140b00808102e00002c04148175810000d8840481000800c1040004031790704400c614034100d0440ca4a503540e8030700300000301c0b001c40f000c00c041585409074107484082c4000001e110303003108030002e01c100a003548041c03c059891080f84140f00080303070110030141c682c01c1d4803892070340d21a00140025150190420014080b0b4455010f14808100c00d07546008440c10705011407405491503051200e04143c2d440300003903d0a0180c0002410007030304d8121103080203001d01569600d0f070f2004d00180030300c0f510781920321414401c0e401040e0003a850321000041c0c000d455003219010305e0011015501e0300c14540514051580001c010b207 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 604380296 1250 604379046 604379071
    0xc01031104050415050f01021207030819090305090316150e0a0801020708180420030a06090e010b040f0207030504180b03030414120703170a030f0501060c0c0807120b 73
    0xb0a5100c60046594000c00300d01121481410135041020070040062024110b503c208034104245010307008813000e464050412091f01c0d079903010301910440b0b0800b0740006040c00c044140b010035030030002622955104905807078625248442c0d00750303845500d20803a00b282d199550103400b898052082e08420042c040c080c10350441d120750025080e42d10001c400c40c0c12480c0081d000075020198201101c915200702c1c0c0a101c0310408040c3c03210080c2131001118204140000400c1004809501c804001c200b258802e11001040c00143d078000c1c004180243c2c0101d06000c1101002c4a582c4215400303d0f0341358860f0350074682800003540c0b0b0742d0324004803443c0703c03076403051401d040f039404001800052401c41c030310504119422040c042104130008201a0700e0f40b00240600004102c88403403c28907112030a2942c40b0305484104a000c3d24000544444042c070300800410010b601c00c1c2c5502405003d40c000b000c1007550b4440042d1f03603c007284104000ba00300d0244210028181200b00c42e0000c0011690 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 604381546 1250 604380296 604380299
    0x150c01020d090f0b0705030603071a0c2505030f15040302030403060f02030105040e030c0a060506010318050606030d080115030b2d03100605010e040209040618150e090c01031104 78
    0x55822121111002d60f00c89108101c91410428420042980041e803803608500794245000402d81d1a0f01d507001d8004600003c16179102203008420580d100b00008008503048951558521020707000e2a41410038240f4042d4000710341c0b4140000c030480ba0101e4800240340ca074046505d60f01600d80054802c03130441c0030070040007000c2480c60280b10943c00c42c0d07410069986d450802040103c46105581c111181c000b807290406540000c10340c140b003d900854046810340d200c5004a0052114280301c3c400c801103449000b00303200c8002484c03032069405404540350b00f07400b2002924088004d10445020b004031100b0101c50070310075001152600e0001c0c08030344095000180b40040140c801c400500716040450388621180f4041200d1041d000b010a400c00ca20342c14240001c0580424004803130185400140003083c0781ca50364403040051007032954150140400c1003510010340743c5c05010208018001501240340c0207185e402c24048c440c07200050503000d44810043d4041c1403044046050032206100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 604382796 1250 604381546 604381567
    0x3070c20030f0d0203221a0d0b120a020904020402130b03040212063d170d0e030c0f0607080f0310050f060307030906060b0c010c26010e04080c03130302030d0e150c0102 74
    0x411009030f1f503034800d4081d00c54000ca211501110381c0c48004500c11080009040380750312000c544c7d911000d8042e60b02d07440d1a565400444d002c0d100d042c890514182c80f4040c0001c01c055500040c50003148211400310300c5a03284124207603680825582c544500c40103250420b044141e92582e55141844c400c101280328200080c170380703c0fa41160303000c200d201c0c03024220b40c20209001d00c1f11240945450800a20007030900740860303550f840ca00001402200340003881c1c401c0d56074282c01d84540301d500c041e01d40d64a0000c0c604000e801d8000780c40b40e03800888035400210380c3c2e141c1301001081c00d40b005055682103070344450742100030b04030210050702e0250b581c60003c030303181d00c0e03801c01031070090100c00007c03130310305444a001404e500da00424160140c40421162410110b540003290445250100c107141648850504520b24401d0b0000f0107410700c800501901400307800300b000c038100d82c001c500b9600c002c1c00c51801541c80292600f12203501040c052411889400800007402100c0301130000103080901194 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 604384046 1250 604382796 604382819
    0x1062903040311010c1d1e0d030905310b0607030c06150e10140a1401090e040f0c080a0203060c0d060e180c01090b04060503070c20030f0d020322 64
    0x107480400111a4001465400d9408440028408003600e041c0a500c81115a01c0c10052a072200fa910032300300c404246c01894410b034525001351000510088007811083c2c0740071018041c83e0310b843d40ca24049010013510b0b1156214403c40c0c40c0d4080c00d103a103440c1080d50110746110394603900f2641c2a40d00e49806954076564080301024145607440c150082c01c1542d04400c1580040d444110b808643e5814000c0640712001010225848803041548004107100180c0340340507190002000160604200414441140c2d8040d54890003031700341601580d1101541c035210540c11002940541c040e9011407640650b00d00113001c031500f41940003640d161030301d400c02000c50307042d034400c00c4504040d12241c42c412018498000d003049e090a0034010303145848021203041c016449035406011000c03001551080c0298001c0341d50301e9021306505070030a010510004111a0a074a083c024400c001341c072403c941e030001e0600d44030411a0000c6040a544244800c0c82e1000140c081100c84a20500090b0303441c0c421 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 604385296 1250 604384046 604384061
    0x30403080306090408160b0f060f0a1226040609050a081504050f1e06060108040c0308070303060b07120201060603050709140301020d1b020d0c0309291b0106290304031101 75
    0x201a46105070800d003d800942040c003509d903510910b46041d05071410799030302880504070380301402113602c2000a8208907841c04852424140b10342c101103d001072121000c4000c01c140e0381603486940e00c00740c94a0502c410807038240a11041680007100c4441103040c0000303100da02c288580112440032013038600140c2001001841c0a1032000d80441035400301c1d034140302803075200c2c1080c40e11080740c3c501b60b100c40c070300b181d50ae10014040c814002212021701d84079400031006842c0100d01c0070b503249540e20380392040c080859030781e1005520388100454100e01c03038003625002e80c007135035100d642c0d803401d1032001f0903aa9140005180d042d03600300074070040c022880c028025a10802c0400c12013140020401030b0404101051600030042103904501c0000d40002c1c03001c0a0f2a0036844400c4001d2540c5aa0745200306080b0705d0340c0c04040081015624800490441850a01048002d0001560715224102951590840c5003408003001e401d004080c107100c80035540c0640285414480320200d0952035003100e114 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 604386546 1250 604385296 604385303
    0x161b06020312090307020102070303050703181814060a0b0d060302190f0e0714030901180c170304080d0c030513090b09182a04061508060303040308030609040816 71
    0x45105008910300d81c03605640003c00901452900200d07500003925800b6600004042c000c011441405161103101036100580c5a0510700303e106440c0d140300700c0d000440504610200d1b06004101c91200d290640e2940500700190441d24400e06001d0503401603040b450a10504c10b2f030b1504000003580d64810040c000318507c004e6242500d0502c0c0d0a440c11a10f00c0e0456526180450144929903901200c20850105201205034491301c0b8100c002e4050300d2185003540303150b500c180401c070901c80202c0180003151000c5003107018100c0e03103041050b124012072051110740c0d0040003e2041190040395040d8005200e07152851400d10441c1d03100030300e90b007690410040181e03141200d180e1360070071106017900b10720301070146904d52035207036003059403411859455182d000c0803407151282d807054950200c0d00d50200800c2440502d880b400c0d0188030540e00800400002e6001c008101541404170031034060741c0d00481d0b01417841c0c0d03400040c001c030000d002d801190a802d0400c48881d4003407081240d480154803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 604387796 1250 604386546 604386553
    0x3020c1b04202203080a080f2d0702030c19060c031406120304051002030c0712020108042616030e010801050a06030b0402070501022803050c161b0602 66
    0x9410081c0070403104800d0351a00c1100d010700c02a002ca040c0441a1810100820b03902c00e2000c8264441081080b015800100030710b90100d840c9020a8100041c144924560700c5079628a41d199010380e400101c0e2821240c100780c3d4401c0d6101190024090095031040690048910b0b000040c1d480c0c600e0000701c142d01c0d0102019010ba68003c1001030700900320b07a114180307030501904111120040c9103820245c10140700d1001400040c417028024010f0b1002088000e0800d508120030701d10194480c0d00124a0001c140035081b0007203984400c02900070750494041c3d5038550203036140d990300c681000c0c01601c007091458281800a1105501400410344440c0d01c024020b0041c0c400d24010340085582c9510f103041c46001001444180c954004241c205c5a00d482c001c04d150303600c040402c0081c130071030700c4c041c24a500003d803a080718010140f10410780b030003660800d19080420007044086880075181d07905800400c12145a8590404d0340c03003110b20303010361109451314104500004c0e4858440c1d0043c0f01680 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 604389046 1250 604387796 604387843
    0x90607031104140f030106030203010c050c10090503070b041704030f140105071b02040204121101080108060402010e0108090312011401200a061104120507140d0b0c0a03020c 76
    0x2581400354600101c016207046040505088a4009121074045080e000395113030640780e000c0b0359003504210021500030b0000c00001c07160400017402c41d4025104a070a900c140d01013041c00384480e1154920254108028500303141c016603079945040e40143c400c1d154010f15080f25182c50340080c000f400154814010050740c1a4103150040c03480c0c01c80d030038030701960740351100700103520342c004417a511015a5082e94050010152000074000e01564003d0241c0c0380b02e181030b207000c00025419020510f00240c030307101c0c82c5070785c4d50b11415036861044034000e00140d8034030080061540940d25071500031913244240c0382442c103078514182c142e1409038490550150301d08880d061a50700103406080009a0800d034104038686151034a43d80c02c000c28000700602d9503104003403c1c8111402c00da0b0090106106a07400d1007a80d401d14a50b1044a4001c07000c0b200c004415410340c03850020000400319501480503207440e6503240d92600b1642001004900f41a001c102c0c0c10200d2009009001d6001e82c2c9032140c0708030f403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 604390296 1250 604389046 604389061
    0x1060e0a0905040f082a070e090607210f1b03050c0406050403150b1008091006151d030114090c03121c14190e0303130204090212060906 60
    0x210660000341c03440d1400080c0804030724014901c03c01e00b50860142c0c0d43e5880c0504030811859542c000300382101030340100c120824500402d041c8125141c4240b40502da4460a000d90307202d00056130700d100814250007003489040b0010902c80d0740341e0440c41000500c000c49817001003d8820501511803030fa2001c102058900342c0510505801c20b0032641154141400c04101401a200d03d000c003502701444d15078480101a01900300d0f1040040c0500340c4800c00c2d80030316019000e0f00742500d000029010704916600b540d9800e10840003120080941d107562000d08080a4862045202031444001e011030344440c3d0310b403000d00444007051040001aa40c514100d41400e0070072160424062094104410780400115444255000f443c001021440e8000b1044205801400d0406c50310344030b8a0800104111081618480480b04201c01e106010408020601c241c8030f200c104c1d103014223034030a2108200507003000c3d4800310200b0701c00ba101c41800810741903124a0007008803001c00700c40d40a0810007505 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 604391546 1250 604390296 604390309
    0x1a1005070b16020a0206070623040302010e0a0804140123070204060519060f11010f1a030703030221090603090a15060303090314100501080706200d0507170301060e 72
    0x1e1541040304042c0106500e0083d00da102d00b4601031b211340d001007512001d1203e144c1c000140ba1002d400c07412034a511303200361a19101c00031503054005d5440c3c031a03046034500c8040781031881d95030300c046106d14013070510a00c1400b01c00c1103000c0c01c2c10441511740d00345c2c20407030a9220f0700c0001c070014505500c0e101e4074410401500d00941029000e4080094208001c400c00c11040040c0c9103076040c51101008142c804881c01c02030607444100c69800c05070ba5200d030b00709a034445a400307042c0c00d00c10300324240c0708001d0640e910868032004005074000a0301e004620346000c03c40580e40b0710512114503100086d4006000c1e40c00070b8400c52919001900ca840401550000007140c02003844004e0042c00d00e5a180900b50001d81e02c00580607002c480d409034a4000f0600009500506030041000705503160900075507a10380c94081c00c80804c201d600e0340e030f10b41006a0810310f0b1022107235004124031441c11000319415000804211303940140708040c0041c0c105407801070350103015956150000915500b003000003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 604392796 1250 604391546 604391551
    0xe0609161e09020a02150f15030303060d0b060102010e0312150109080c0405070c120c0c050307230d02060a0c020916020c010c110a0b0c10020c101a1005070b 69
    0x440601d070049004402051801c100308580500c1e82c0180c031248940002c0c1c0c20810a690007000b0445428200200044a10318190040d2640442d6002008051060556a203c1510072541c825102141c840024400307006d5182d02510601c00421180e800266891131500100c80130f072030031901101040403032030358103080706101c03802460b1942009141038602500e8212106200b40140d844100203003045010300070400300c1551000d5601034424007000d0040c81d0900341502250f1244c1200d10008440c0390004002d8142d0308c402e0480981120105440290401105540c030781011240800c0e60159840174041c200032980c0b40c0300c410021609204000100c40000d1810303004001c4d800c070b005001035000402610b101802c0c04c1c04114200c550400ca06041205040c0d985d208000880118071086081d018184200c80c04c4104c4802c0c802c0882400c0c00d0b40546c1c4c4258016038071408454000011907080108008a0400e10480680e40f48010845501080130003501182c80051440104041c1418a0782d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 604394046 1250 604392796 604392809
    0x61716140408033c070516030803040c05060c0c09060a05030304030317100614031305010c170c0304110d061b2606030705010c06021911240402060a030e060916 70
    0x10100c01c0c0c4142d804e41d61014144071500c610010850004008041140811030401041107010055481c50b042d80181d2080b101291220315100000909003042d00c2500d0f241522070700070700301c010a00c0080c802d10b1040101001d40c45441e910000030161018401080514001c1d84c170103400b0076690f0041c90001d1406490800752010f82d0408000051b44800903c1c07560034180b048603030344d854403400129400d0101c2c4003e84039510f0644d840c0020358000e403100709041183c241e01d440640d12603206843e14042105d01a207003040440c1420558a0b00c112803102503441864005482d48101c140d010044200300b5400c2d003c40c0c041c552a1081c0c0361104a1004880303c004100f00d00d51902e04003190b110007040c8a001e0501c0203121010040200c590181c41249003540b154003501400700c0001041c260b0384520070840c1e030080c0c4002c60400c128000e01c5004000727408400000940b00c540c00d01c5243d078803001d2590105a070396071102c3c0f06040144a59809000f10400401402c1988802030900f00c91903804903 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 604395296 1250 604394046 604394107
    0x608150303040e0a021b03090418021305130c0807030201092c1003020316030209060607081602060d1802090903090306011206090803010f0f06171614040803 69
    0x28015550010403034055806440801d211500c41c11003540181c0102e002415440144144a000703814001020709007281e800c4600b444080500e1562002824086101035000052466201c00a01d0141c000c2c9400a40d14160407850300e05d07a450384a5001d840c0e401003640d681140008106644e84084510b015000744000f8100d5550612481003600c0090ba542c60b0381118180002002099403401c005c3c000c60700581071b5030003000031408000720400c031802300328420405a40829883e00b8072a0949600c1a405103010389001d112030396030740d607102c0521003c90340032008129080614085004000003840c4a0042020023826441006100c010052181030036500c11b01c5407103d0369400180860449100789403c3c1c03428a200e042403c05072290290141c250813000000080c1044030a40c050300f218030000f01d041d2204d071110303401c0700e40c0c1490f50700c0328402c480e085002c03503031340e209140400c1304504a500701100d080d03146204031b04c103c1c0c000750b001e49040c1e040400d8603900d42a000344440324400408480 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 604396546 1250 604395296 604395331
    0x190f0218130b040305040504020409021213120516080412110103180b10030b0c0a03110708070318090c0c05240f04030e090a0c031407090909081c02040608 68
    0x4211106540e070704082e1001c1d1650020030141406103040f83c000d44000b810555a80e6110303812071703001c0d6105004a005040007040003d5410400f000598182607000d08010104100110100c0707260b00070740c500c2141e00300c412544a0004d02140014030050840c00b03060803a000850030301501e07610160355000d0606042031244100c50f03250301c01c1d28501c968454060791030b50701c3d80e505180710f006551700010401c8906009001796080e40001030a1407201640d014000c3c2503480f0b43e0000c26004e140310050440700103001c00c0f00041d0048855802203108424850000c80d0380708005c0c805c0e0b504540b05400170542c60b035009014003409111144c803c0c44501104c0c0005180405091701d1280d000f003140703111146071030102d8100741c0b140c4030304480da1400401149580c01c002d40c86000501c1c15000b08404240b9100b51610b4080009036414491505601d80071562403411280d04042c1a02840c102d50322442003201a075181c59610000c1c9452400280041e1642d042802c040c0424501030806200201102c15 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 604397796 1250 604396546 604396561
    0x103150305120d18050a140a0309060f02030702030106270501050303030f06130903090e1510050a12020318010c02060c031f05030a05010c030f0902030c060a02190f0218 74
    0x1511964030405401a543d28161024400000c28070102c010001c2d00000f401d1005000e800a4001e400c6030040041001c2c03107828031515039442400350f0000b8080350880c0e50801405010b50321105240a00d40143da00d4006680d000030b0848020303400100000302d10b507800400300f805c1c1c040b00c02c01c010001b5004002d954148800250b80340002411213403589518000900e2640364040c0e4804011001c1e0000e22050301980303005040700300720380143c5018000c440c0001301d0009005d4010320001c403001e098500e1418014508481c2c9600c010000428800f000d004490341219510007548030344580350f103000d082116000c0c61400c0d513200300020750442d4002c105200480307444408994000701109401d000a0700403450301b071400c1805600081d03250141d960382c003043c010103400518072010b0360350b001c00920140c11040c9017155400603002c2d4043d800311031002d0312800d00f0030043c20f0700b6200303004071000c0200310703115a80040380b40340341140e1480c40039101008500300010313528101c8894102544507442e0002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 604399046 1250 604397796 604397803
    0xe0a0e12120a0507090305060c0c0d0306030f1119091d0304050a0e0a0b0a0b03040c050a061202030a060b04170f1906051302040507030e0c030609120315100804020103150305 76
    0x100b042d03003003540d14008103050600030304a40004640c0032081d52003501e00b011110340540c1120b18440d0390750061030500d509040c0709100301f0040d6984048040803414903030700c0b40815a50304c002842c0e0000040840100000f401c8188503000305002d1078003148205c517078001080039001e01c00004109900034001484103a43e208590002d541c284c510071181585c601080070041c01100c010150402010f040104442c40d14100440c0305a0081c80c04030709440c4d6031000d0010121142c480c1400050790f00041070200c10482e0000c50700403103141d0001c140b1300c1e2100d0740000f8543c46a030040003002c0004181c442c0c0310b0010304c4201e10006420f00030b040c1c2e18a1602e6105000c4084245c0103003140e58401c00901503c0c83c00c1500d505843d0050700070055494808400b900402a21110181d68450b080c656030300c0b45000142c90b4802e1059a000d03000034000ca41d05120550800b800c031760324417000d41c080b1121685418000760903012440c3d03101d0816042c0303800050111804a00304100309400d80301c082c8089400003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 604400296 1250 604399046 604399051
    0x91d030a1e050f0a08060405101a07050307020a0e040b150109030609060f1d0106090e0a110a031a0115050316233f1f0e0a0e1212 57
    0x1c04080180711101d04044420303101d072075001494035030301050f07500500f540080202d00c20181038804110a48a111101c00203012620503065007071206406100e06c680035001414940344500c2c00c49041041c0fa600203842185103811105805810000300300501407a0b46c4125004200c0301c0004400c944000002012100c0902001d0510354490700c181042040a030f004045150b44d9200810002c03413039200e42c03528100c09030040b003e59820b202c40440c47c0340841c8580031f2100d01940003008001d0184d0380360303410400d2070703049568071952070b2200001203103180040d10741110b2000700c81456981041500f60310300b071000041800300030040c01040b0f014011911849185091800c129660708100340c4d40c0346400403200c484101d010750110315501c41c0c901d08850f0000d441d03644021000118080300d14072500701d1900c0d8220105010180104402040000b00400c02034107180c4450f0415488101c80d0006040584001492230758801e1151000d520a0114601d040c603800c24442c50140c0ca0b0101c0040d40101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 604401546 1250 604400296 604400327
    0x30f061512081612120b06340f0f031706010c02090a020c0109150606080c0409020306041404030215010e090d080a0617030a020d14040b0702011107091d030a 69
    0x9041410740844032940d040082e4803001003480e01c1044031000b844800100c00b28526242403440031a51864070704262030b0309503000c038401e401440380b00c441c040e010382340c0c0c10588500c81d00390480c10010480d603070b08448a0a005850441010429280081c14005400026042040c0c204144016680c0c1310080e11070154044490511039154150751a0003071007034038000c1c11150b10700110b0b031041200560038480003d032004410032031250380f580c0941d9044001c492402088a0803c028041810980d010b950810300c0640002200d00560035030111400303007030b1001e41c0547d00c00407038884210058004140075112030502c03244541850151607540b8a48a00d506c803e21401c0b0002840c1a403a540c4038030004c0010503c024030f0082104440b5840340c2c032103031101d4018000d4007940412507000b54032103a021101d451100b880d05141004010864101c40d004a0411980980c1c1213004001007180f00051701d03404800298000421030700c0d10700c101241d1024406a00240400c0714804e40050203181594071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 604402796 1250 604401546 604401563
    0x5070512040606050a120b160203090d051005010b04140d080a2003030c0a1403040f021221091309080a0c1727010507050703020609060405030601030f061512 69
    0x101c0d03103881d501603c42500400d0708110041400100031404d05110384505020394480003203070b1551584101c0b4403d094903c00301590013002200c0d801d04052044e15550b40c018000d940d00ca881201184c4191907080e8060801c4200106042c807862403032541c0c081d03540f001211604c80000300742d5100992401580e2481c5c09100b9400c0c0d440c00c00c02071015401600e40b0031041520713901d18104162490a401041100002803c2a030f40206d803420304004481c0070700d0f0084240710202065600f0881148655020000d2601a0403440c1403030611401400d0640078090030010b4071007491600b400100503108038204091800c03d004100401c000d071040301d01940d50b9143c11030f0842401e05000c000d4003040740d103030211503400240106070841c09080000c0d0341a2000500b4107409003150045a440c0240380000d00709801c102030410042c41c0650040c6561640605a642804c0c0d03210006810402d007640107581c1d2000c500c0000342002040d100e0032820120202013075055a042c2100e604500d40343c0740c00101040d5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 604404046 1250 604402796 604402801
    0x403091a1e03090f06010b0f1e07030f031a010804060b0d02090c03070305070e1e0f060409050108192001020114090c01080a0501150c0f050a0503180405070512 70
    0x111080350380241880080440700340003100480c4540c0c1c0111240f1249024810030031028070400320311a4101c40d00755903100c1c01c2446813005ca000c1c55010048030450491030074803200044500b030010b002e0540c00b94981c0710024005030400350941d0f0403d111061080800e0700f800e041e6a8120008580003500300f507000504618038000302d8104030000300e010f541700683c84100041c00600b00c00451241c4125a0140818ac0391a0021b0f2500c05c60f4407101948400c0306c03001d40750603056000d0ba001500100804141d4584601000704500da4065007222004648640c010300410b9420015034a00c44a006c620395408203098588800854070704003c403c00f0311030702e1311400440e032007500a00b1250807617006032252428580a115034840c4220704140c00b29100400090090b112481342c14100c800d10503d44003481c10300e074000c803842240b44c0f6040300d08507280d441110102d4810440100d015114800840c0d48003e05030101140901d0030710010700c0745041400300300346540d205090302d22a00c0108850051074 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 604405296 1250 604404046 604404089
    0xe011b0e0d0204050c071101021f0b03070e18011514090a060b13030b070804080d09080f0429040810020304031b050705010f0c0c03080318010c030b10030203040309 72
    0x646900000ba510a0408080c403220044140003441118441c10900d00c800400c840103a8940d07000500603081102e40c848514007500403038100146498005050300c10542d01c907e060414040f0030f640c01100081c65016865001809100b95220200300403018484076142031500309490301407100d168000c6a610020415182c07480d00000d0107003c41076a4180c403120900040a9160341600c0141e0f501d12440000c14910790043e100c260140d50890388280c6040010f0225001070601c003071007201e80c44810806603409219050280020b0081da0000e0740781b551404d0720714414600400b50101c0f425404000c1080082800070345c1c0c42540c02405030150326503445090642d40795540381c10860100c2c0d00e0058001c20480c011840700700762102600c441c01d42008040c421507007041480f40080c1500b5003c201800880c9401019582c085510384400302864520300c803003420346101807101ea0210391074a40e5038100e4541003644a41d5050940740840c20740c6801e88005200220030301c2403000e60712014213801400f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 604406546 1250 604405296 604405309
    0x4080d0923010b010e1801290705010506090f09070608130501020a08190b0607151119090e09060721090b0105040e01050103240b0a06020f010e011b0e 66
    0x5104800200507001d18a045029244852009000030050f003000c050900d045c11080c02c00c03c04444000c40140c0c20701d03c1720314081a0310100f281e5088a10300d110100091a8801803103268401da0000c03a0030306103641031005604001d4a450744024060b002c01c00c0c1035800055080484502c1d01d0103031811344404e003407046048015003010b44035500000708400030580040c00b01d03004d00f800c22098080d10728580811811a00c071400c0840d07100300c0c100900004a9502e1131104280705104800003681c4047c40c084194660229112801082d00070201906454005840600524544846005a00e0700000c0280c60b124014800024040c03003500d10a001101d03803948842007a031501080110540c1c0b400d003160020424440d051049086c15a414852581800307024100c9a00c0103a019a500d00300c0c1e90951360707942604090603815500e0585568a40ea4030907618000c19140e0041c01d0130050000500b829600c800024413680c0c0c0c18583e040c0b003a814400c0c90305603070b0f1a10303180c505901c7c0d1082001944 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 604407796 1250 604406546 604406573
    0x807020a05062704020f09060306211f050c0a0c0f0204020310091a180703180602070212060115050c03130b0406090608070215090309090412020d0804080d09 69
    0x200140042100303900207805942c070341c0c2c00e85600310030030b90404103c0c810413040e4481e61419400000c0305012a15090406c40e0256030041001005070b00c0b1494241d421200080d040001c1180c0da82c407030400421103290b5098a000d00b01d40c98041070207607180c410f120104d1885030394032140421010700800010b02102c07103100d8030816070003070096642e420014100080c9030020301400c50ba143c60410800024158440803811303000c4041e22644016812110f070320781c0f40600a041202345619200ea449a9918a0340140c4c0d4092092900684031985801131040c10080000710001c180d21100043c0841c010040d1203408050310340c9081c507130311482507200c2800c3d40903c0b428070a110000300c1c004030f5401c40041c00b40058030410b0380e510417810356440044900540941d1040d02503008403903048146205410800c0d44806000212840c0090352008a11009405c0701c0551b0954000500e4403010303a414010030440d002c45140c0042107041a4035243c0c424420034054210031650360350360208000c0020107040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 604409046 1250 604407796 604407799
    0x403020a060c08060414090a060c1b05010f05060402030405061503120c0703032601091107050f15151507020117070507020907030c020a1202030c0a060b18040201020a0807020a05 78
    0x7100c8980b14201808080b030965100380708074180355103107510780c40700741c50309108a122400400880300140c46000c014001c290020081090000030001e6040c0c1d0148a900300e1446a000028144001520380085139030280c00c952089004100780000300c2c0c40002d4294100070b100c1c2902006012480010b4030b0304000d502003103500800800c5040390340501203020303002c41e8042d8480320700440719205009052072040c0d40c0d00b07010b82c1441005014042841d8040e030740d81100341107164070704412521071600d489101c0003550640e6100721250403440703064003030407508002c8030010184030382c03200070014102601203401082c00d07007804118101507a00c079a4403601121300074400c081483c20404030051540e80004c4082c0c0c000c0c144e4601081d0090300c00e104184918819901400046600361340d100500a415004001144018400d800483c14280821040503200745000680421141c06110911240c198042a40041e034420080541d8000c160b0881d55903002000a90b180c0d164400103149002e0b036000755 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 604410296 1250 604409046 604409051
    0x60e0649050706030203040f11010507020901090b01030b030111070605060d0c0303020a062f090a031b0305012004030b0a020d0906090b0f09100e030904091209080703030e090403020a06 81
    0x1448124040e880080409001e981a6070b581a202e441c150240d120a031801042c500420300c5010110b2207100640f00c1d402d00c1458160324000d10780d000a41e020358281c003e058072654a0040f0307031b029a05449006042d03141a4000c2c4081102100c007a586406500006400c194440d80050400c1d907035414140401603011401ca83c200b0307120304009603980782d130b070b40115485c501d804002d51404001c8820002c2200c00c55400745010454450b03286c100f80c02041003540c2110784981d000c0009241c0301514281d01414110034404145035080c25030a4503028502900c4544030311242c1040d07101a1401c807029a508450040615224206414000c0c03090714801034005141490b00c904010051f008080c00c540654080c441c01d40790080b0846100c002a600e1640c66408912070148401c20b5400061013020b181c41520300703260040c0b000ca02661400001282d0b440080401c500640d500801d208014000200040001c1400e5540c054502007003202003030b22401111000404041c17082124401203640801c09 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 604411546 1250 604410296 604410409
    0xf020619110a090e010b03090606121f0509070b07080306060f12040b241818160f0602030a050a0302090a03020d1a0c0a0203370f03060e06 61
    0x74079010060040c076070a40d9454000041c400004402c1e02d015101d540d0107003000e40c4550701004404503900d10160304074001c80303031038450331920041c1003085050724183c0401d0078504281d10074144400c54000b166030070004d10180009c46c41c0031080ea0341c001c80548081341d4416164030742a015000700400040f0071140282000100080d48003200c0c02080321070402002c0c8d001c50841e4109110003801041c0c0c018200801c41a0700300c110711000e0390400c0c0c002c0d500c405908515821070303080c850319030300c51705100480b0701c000c20480d4801d61071800289807030300c040c60400340c10000083c420302c00c11249000b059000b0403070b45000d41da00c40004c801154011700021242c2410700c1e080c041d80070504103041c40e1010004c009020040740c0e60444a051032258080e5140a440803020f65421960036008601601801000803800040e10341d14411280d0507101d4035180c6006000c0141540c1c0103401034075075284060103000302c41c2c681801170341c0d811109038121010405199072900c1c000c7c40c0034229607070380c0580104 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 604412796 1250 604411546 604411567
    0x60f030a060605190b160201110f03090f04090314071b061d04020301050d150902060304080310090b01080c1b070f030c0807260f01090804090c0f02061911 68
    0x34408445003690400704005080d080b00320141d0403441117103030405003001040b001440350052030b600548141080e00f1200d2880c3d409a140c1003004205004551002a40164510700b100d84c60b015200b084030305004084069030f005003041c4925004a034120000318a00c410072080031a02d1240180c004038205403203a4440e00102a001c580e800715482d600d0b0028a0491810315008aa05070395020302203400b44411690340c401c0130420b07640641f21055a51a090005a031600c2c015405140550304060f101d0801c400091019000c036401301c11403600d0720501100d45d0740c100040d41d44c80b171100f000040d00e50310301810304e00c0300c0c00e1409140f442c1802020800308031011451400c2c400c1e24080c088041c0b0a5403079102403603403189a4021400317020140c1e48081c0c14441018061895003085609842c090b40c01140f010382550318210044851600204003441405da00c0d1150584180c01c91509a40003040d03200083e44485026000e0707091807005803141441e000550300074268041d0f800d408503940d01007030603 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 604414046 1250 604412796 604412801
    0x30a0507380a060b090f0109030b0717010902040e0f07020a06090804151809020a0203070803040b150105070f030813050718051303050d0c14071506050324060f030a06 73
    0x1294070404641050110b40200e02d1032140c0c00030354248001c124a002e40e404100700e0310301d407041d22544c100f0450480200001e03180d1641d29006080b0742d201d840080c1c04100c0054034a2005030411900d10f8030601c4200040c160358988103801151112141c1c0d0540c80c0e501e412070504c0d444500180019090403123803010405a48020320071100040302c040010240c84100701d991064061038409502c3c1e03510028458001c0c0d650003003014108500442e890700c12039550712070880d00b084a0541d01800034504102c80c03500500c048203440102481d00519141d11a0760301810f0781c0035410050108050b440c000b600009039820b06005c403a4110003120310442c2d980303504002c5820740440343c0380c040e42407a012680503020f0b044211901079060b120117041030000354105000b003505400410030044040c60703540e041c2e01c00e00010322980740140c0305c4c0101c3c0b440054804c8261905540a40e00035402200c0580400314401d00d071117600c4c2200c0307a0f0350765291501400a41c02c04103000809505004d0350403c036040080c50b9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 604415296 1250 604414046 604414133
    0x6061707051504062001020c06090c0102010612030807200f0c030c0111031e09090109021801020303011d0c280305070813030f031d0d031a03030a0507 66
    0x725503116101a1018003100d072070003103104d0040443d4900090503801d03221202c45803006039540d000107003801903400e8450b10707004007924040402e41100290380c042e56820302501c00500b51181840e9080202a500100a080001c0c080010072070000c24a03028909101d10982215140c84111600018081401c948503001000414803038070620889851650041c00503224158081001d1401c05070b024501c180800006030009140c4002007000300400e56440d21240d000c0c200800c80142c6075001d4400000440750500130040c107650060004000c4c01c00d120840c46040c8280e40066401e41d211b6011007145400380c01c88040c4400022038000c1e1209804040c2e0000e41c400d582c0d018441c1c2d03101c40310180c501c4503040d24001003508a04040c0070200c1c4c0a9404545402c03002d140009070445110380504200343d500b40c44004681140c200600741c2076142c000d03040200440c601c00000c0118078400a552407003114803201c00e006010032020103012200d448072a503c6011407208881c0035050030f210b070100c140e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 604416546 1250 604415296 604415299
    0x1f0e1b042303060103020906090405160b03012c06040b040902151e040b03070e0d1202030a02010e0303090717030409090c050a0909151e02040b03180a03020a0f0606170705 75
    0x12841081610724000400f07504803034014010042075200e090038008081c00c010800d88803841100c20002c03001c1d2407006884000d00200b00c183d40c50b94140030240007110f118450041d000d064039038050039003501900c182a00701000f1100000c1c4001c90b500410084d042c5041d020350700c40601541a00b41480143c010030745442c61028880c091000c84e020a07506000e540994043d05005000091241e8000c810480b03e0103802404124102190f030780311100114501d041900580010903440d407142c0d0240520414911414055800c502d401c5001540d1140036100e04252004999044003002c08240304a81c040d003000b0105105403d103a00380100b020415100f0203000365002040043e90744094440c607280554010b01007403080c95401406400740012a450a1146101006d16085481240f00a000038000c1c0780e0100c1d141d24041049003002c2036800d4007000c15820014030315000943c007050701e20449502c14002940c00302c7c14180341e001008960072a1030141b00c039454044050400140c00402c9900 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 604417796 1250 604416546 604416599
    0x10509040f0e0a1b030f0323030a1a010c0f151e06060e04050103210912061401060207050102060103060f0231061b031b020402070c0e1f0e1b04 63
    0xc080703001c1c0100131002d2001402602a881200e40041c1c480c08000203503000010344001e903000b4125844240d40d005031065000e00390740d04201c01c052140403140d04d203031110908185182c110745841e18401ca12201c039001b044402c00015907126040b85500203a150300c203645a4a410828220101d0018101805518081031080065110b075213020b00038141070b6a0f109e03440f02412a907500440c1c0000e01d00b030100100340700407020089003800055400c2c1020300d00030321000c211840300e0401a00780d8801a0802c808540002e0340600ca6642c002407990304480e80584001801c0d569148010000c1c0500280000204040d680080180c9070b030040c2c850081880620400c1155503800c1c0a60b0a45541102d40714440c4080c50904d01180c01014400e60101942c0d140701c402102603030008003203078000c000485541ea0030300024010103a1b268032150340222100750340303a101e52070440c981c01103403854032628240b60060000030b2081d00061f911075020311980c2d85003e07141c940b80d17900f00803506507003076a140701c000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 604419046 1250 604417796 604417823
    0x30507030b07120b0a090b0d1502090901050901080d1121121f152003190e09161e020f120702090a0203250504090b030105090c010509040f0e0a 63
    0x1180b00704d40d4020b5000303040345402490018140040d2018400c503da10403042c0d444000402c000c0249002d0602607030100503070722600b49003040b21115044e0091070062001800500c1400c500107000360003c000740c00d20215150100141c50300c1d00b00603207001c83c9108090f080e241503007094000a4080c83c182c0c0322402280c2d43e14032241840a0084014400701011601c80c200526058048a5170f000d240c5890309490003a040090350f07210741c00200c42c90002c0c2d480051071401275030245083c0700f060780c164940f1a6010740441d0000780061070150484841c40494031000e502e075070140c0c80c0303140e44c2840c140003c100c400c0c1041001e502d03040c0c40d48120300240078045d86010040102c07800c40c0c080b694018503895190712034840c2c54000350401020130102c00c1e0032100180c4017031041c80e00e40c0314852071581c0359a0744904295800c81030340c103800c1d0968040d80c1400e0500c041440c0100303990301c000e034080ca000d6072940341200003d405842c400000700b180750320b020300c3c002c407d00d000f00314680034600403c4808481d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 604420296 1250 604419046 604419077
    0x1030b030c030d11010b041e0b010504061706121b01020705030307030c060b030313030501020403020a1a030f2706160207061403100b0c0105190c0504050405060604030507030b07 78
    0x2031040071601c0d40d158029040c1c46245034080e6001d04103400b0301100006d0301c400c0850104d4200d0b0300c0784803500c8010119080340d0300710a1050045003480d50080c80d000b82400c0c980407014021001010400340000303804c000181d6a92154200f04980403c15012500c1c0004180008000980c4046200d801070084190215960a0000072a0085545540c03140d80005094442900030080040b075a503142c00304000e40c42c0c04104c034030103510186001d2000166154031354410001015090b92003091002070004e1030201090f40740d003d880c0c0c0701a030b50705c0300e00c020340da0803031080c0e8141e2085210703007a013180c45002c4000079440001e4191056200c0c5082440c40c3d110110280c0e92081b980c0714440010700c40903002e10704003c0300c0f0051034208060004c440c01c550342720784201c180d40c1c04c041c0085079070360f40d51010010031f11443c070346c181c84040e4814410000103006050040482c4030750f0040b2405540c070380010403441c2d16001c040f18000e40e00442611010341e00c80ca00500b1280f41544da03c000606000001602c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 604421546 1250 604420296 604420303
    0x50d05010503011b03021e03040b070f0c02060a120f021b010b12060106111218010e150307180b0a050c15010e0712091208060321030105040506240901030b03 69
    0x113504005a1010301c1040001200a075002e401282c50301310800f003100b80d0f0414000003450180344108550500e07442d0196004010840480182c001c10411061741400b5031038103800c540c0309241c00d1404042007030080c1042e9000d881612281100544005908408489503031f0828404401c8040248645048182003042030b0310554404a000d400250042084901541001140140320819100004040100d0894070781050b4288508040000d089205542e13000d0700701d408000c0d00f00c900384100194022000000c0c00000c20031424413303280380801070700e030030004020010842c034903e841c0c0c1c0300e240c140f000345650059484d00d81c0c14442c03045c0400600070130661841c1a65610024909296a00c04080b0340c000100b0629650071565108060041981d4111540102207203483e0042c3c542486030030302d4a010029407401c4011119030002c03c82c40c000c00c0307003102d0440c0c40484e80498203454030400100b0448080ca0b03060003540ea68541c3c20300e600035160182c154110300f620204144880d01c0705142c5c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 604422796 1250 604421546 604421561
    0x120705010f05070b0609090f0f07060e180703051803040801060504050609130f0609120201050106110f0c240c0a06050604090503071502041d041506320a06050d0501050301 75
    0x10503414001a60600303006c48040c1d0b0081c0e469044502042c94440d140b0b081808086a03001c903904803810511019070098048109020191030900c42e0001d1004c004010b030001504040805484801141c820b900d41904892410402000da0780c1c0c8a0307032000058000c2c0054410780c1d0095050500180f0a445c00081c228421b8907411141005440d00c3d031f032a403034500c000440c00c40d03899503681400004500c24142031000034403290000220355050120240810305207404100d0ba65205509004510384045081d4007955010380b81401080ca444c800628138410f8048440400500401e000790280e100082629019000312820004d5460b10b2092005403610380d0406002035108006000c00aa4094a0003060b4403989900505090302c5064040c0c0198100485101c2c1003010700c03e0200b84100c0d1116030072408041c5604200d40e5103030001e1002140001d4550400710500303880d50001e01c4043c099030404400d40108203225089e240d4101500d20342190041141407860701d000815181014401c070030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 604424046 1250 604422796 604422803
    0x30b0f07020a1101051303230f030d15080a03051b031215180c070302060c0406090e0403030204090f0e0d03060b03130212010906090b091207080f09120705010f0507 72
    0x1100760692a250540e070b0103d80b2150400030704100b444143c130525400d40000e14030911449140c0164140200d0200d400303503001248030307005034909038004c070300000881d0340803e002000402d2071588040c1c900c0aa41d5075034800207040c042c0c2c01400c010154010001c00308002d094000030f401147c0010361700e6603405040c1d01450452503040c0807030b129040c0c1d0203000c5030210004000d4009100e204484507413004041e55000d15040010603008101034043c820640d0100c0c8419145092901e000c80c0281003031818031900c070092280c003010406152203501214041c00088806004103001300007610020501080544203e025010a41190f14842e008040032140c6484183d4116100d1440300c00041c0000c03207040b44d01c201d030116490f201590a00800c00d06500854001408281c5810901d0820f00001c0540c1c5013500308a5007045060031503015684525003001109407034090707503e840f0529109903940a44d101c10810f10711400c40c50000b40f200c041d204283c2c0c865942d9000c40009440034000d266005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 604425296 1250 604424046 604424053
    0x21009081c050f0c01200415050702031504140f0a1101110606040c0201060e0a140c120114060c06040b0132190302060a1206170d0e0a0510030501030b0f0702 69
    0xb0f1020a8948000d004c10021084c0002082421988a0030942c00144217600010b08042820880520406030000c034940540c1400703490302804c2d900080c0c80300c5041c11032010305030400d00440c080c4251400041c0c0040403000407982c2d01c040c22a183d80d07032800010300484e40107040d100e00c95050f52103000c1e0030a04a10100003408641c89080400000d025120040c808541d86c0c1c400001d014000b21110500582200c503002030400104110070b80f00b0f40313000f00f024400001c100003080300a0010604035045074a1181c4208144e0031210020310607114100e41514240f20b00c2c0244030074402080301030313412515601c884840300207402c01c007c0e00b014041031045403d81001129403d00b42001044411050062052003070207070303142d40c00502aa00100d4400c000958880400c1031039040d180f10722005030115841c4203411b1840010107a9441c0200c80801c402c0100c20040c80410b80c40c0c120800001d804004d0464140901450005000300403d02c82031300ca40e9000408148685601c680050244240d903028 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 604426546 1250 604425296 604425307
    0x90f0f05011a0d050a0b1522050a0903170c070b01090e0d02010b0315100306061e0f03330218011e090519090603030531150903021009081c05 62
    0xf528a58040148a841051501f90720001d8665400d104a0440c50b1070502c0e0b12080b005155981c01100c40041a6030001c516203000000400d400c8008249206003a008044c0182e4460700400828054003200400c58082d0780004074641c0c0507600004400018401150502610700a00300d098031400d44010b505a0040e80d0701100302131540c0c3d08960b10044042684200a135240e640340102d03456a441094841280b070500e202406400c01240300030902008018001425a02e9024100c000100d80c00e0800b40003455000c1c0303484005030303440c42c00749400104644602c0c0030368801c00306000350800c3c1c80c0003d03106504040103c00302c1e41034101c00303025955010b64441c200002d000c0a507000045a60001090000000d2801c4a501511b0080c40c0b007a0385d160b0300c8020903481558251204030b0f19800022020945510b07203110500351008480034104270420000340040d0a54400219810180d0803c802700c00b2080c040c2d03003106580d01180d030f2074400c03150001401900b50b091490030740078a200043c802c001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 604427796 1250 604426546 604426553
    0x908300c0d02131214060403080a0f090c0603060f0e100b070515040503040501031d210705070e0f06090c030705090a0b12010614040f0504090f0f05011a0d050a 70
    0x10704035092210780010302e0280d6040540c001600c040d44103804040d00c0135440e808010309100d480c615a5281703001030117030341001e13034029001d49001082c00c0b08069448130314100e4500070360405480d264003e50100400ea07110381e4010003a0555000350320302002c040000107104000304c15594800d1455004e0101c7d80c504103011103a01d58020707082940d443c070550403410218161009401d024030311400007143c0e11490040050281d070f02c08020311480d980440003400904001080241120803100e141d29500b0020a454010368024418082c10350700c01c1c450f01061f19a005046640640b140c070440c000303540d403020100441c60508640203031000c038042c00407401e101d000d8800780032511002072404400c2a200c1a004900d82c111021141fa100c41d080010841690842c10b0b103c503070100c1002c40d6203003d040901045e640142c1e8030a007402156100c503800e06100c1907459526506500c908010188000c80c102035000c0d03c082034400c501030011110f0303414140b40c01c0e088244081e41c01342c00340c00c000c41144c6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 604429046 1250 604427796 604427821
    0x40605070210030b0a08010501030201171e07141b070b0306010203160c0b03131208011413020424030510060c02100e09130308010e091509030409090830 67
    0x16455040c162190f146020b40d64a070b817940c03009056407000005080d03165000040410a118807a085007042c01c50034440c2400780500b80c900d180350041080c0c1d0446d11041d0089a40c0c10b500440111070b0340d4003094500c2c1d010071801806a41c1c80d00b120440b00125101c086050720b500c03054840c107016900030043d90012070354414800356114091100341901c0c03a0307601c2d040030182c0e10072910114140758a150080400504c3c0c4c4071002245502e1402da2690740c1804003005c82c850344d20030100e10503580c2c0132124a141c100b9404036405880721204a02a4070860001c0741d0300409141484000f090404001484d03511041134410f0885da207941c0c0d40400841c4540910013030703c00b00000383c0f040144400020045460300c019041c00f4900e101a008411166424004c11420041e04800941c12010f4180580c0040000703520000344240c002d0340710141c81d4030b42603601d50304c1242d000000d00783c2440c0d010800d0003045406014101558012003600c0081c0790450040d001c001c80010030012040f00c042007841c10300c003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 604430296 1250 604429046 604429069
    0x9010905090d0c030e030d0c20090a0b03071e06201011220807050a03080a20060c042409140406121401180f1101090e0406150b0406050702 61
    0xf07090180e501c4172130a01003800e083c0582e1882d008604501020002c1104212840c0885004041d0458806e52032400182c1c050030041c08101100b40c44410845040d501807020400a00543c10081c0640040141407201d10f151882107001013101940070044d41c2d030300c0401c06041c03864480054040900003000c2e12004180400404c2c040c04b070148508100001420111200034880d1845201040d10303186c1307003e00d044400d0300880c1c0103994034001000001c007850192524203045042c0b01d40340c03459011050741c002c151044d070042d051040c4c40c24042074503280e0300201300345c0349142c4504904840010b640080189542c0e00d400006000f16000c110307500c00290f400c080010000e0000c170382c1c907603103038800c01c1072500070801500c00c2e90f0070140d9014191000d102d940086600e400040e84100b0003601c81181039100070f48090000809090104a10b81c13081d1890809440d81d0400c00646040c1410401c00070801003c0c081c110410003a004107107801d0160a0f50300315450340c2c0d1010b00d04180d42e401d10249041a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 604431546 1250 604430296 604430303
    0x6090603030c191403160221370b0f060d020102060621011a040e07051507020f04021603090501081306020c0307050109080c01050f1003020f0f03070f0509010905090d0c 74
    0x896100c4c071180c040c4001d2840c2c6a00419031850b1142e14010011031100081406041100c2d420800491000c04140c0300d19002c1b62001000c3d01420030302c00c11204c14200d03c007100b40b0708000f072586401c020041d0920f81c010801005003c40c03c1d942c08081c000b00665012029001d640040f0003d0b000749814104190941c2514011445c091a1500541c1c00d66211722540006400742ea103031078006003840d2241404800a24009001a0340340201044034100c42002200500c0130015016041d9120414010750154001c2c00031076403614007240d13503079030595412000c900103860008000344a40c0300d0300311310b80181c0300f0112001a8a1050360780200a521080030548940418441000071950a00c0307200703849406911031a903180c607800c22035400c4540041c0300b84040d0003002d05011040000410001c00d90341c4c1035a100e0702c1000c1c00070000c1c0140305800c1d076865051246487c0490070340142d1003104115036080d626102140d80354480d080c01e80c1c070f003200c031003489030f2000c01d45402642c070070482c09a00707500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 604432796 1250 604431546 604431563
    0x110304080c0705040519050a050c03160314150f01211d1606020d030513240f0f0b01020c1f050d11040608010b0a02060a11040b1206090603030c19 64
    0x83d150003141c2501c1c0110b442045c800480001d0703010051070307400703010707413110054404101c5480d000f813444034a400054900c140140c00c2c003001069450282c6d0084480820840002d101440c01d40b50039191032402d040f80b280542072856041c51654041d0070880010582c60090282d510000385000004103010000c54000035080701c1000034560042c00b14103003001582c2021010241071000180c0740820884140c01014542010040620300340b03524110382903030080349680c41010b0318041c4d82c2c521541189190800d0310786103246554010300e903c05d07003200c01d2800342406140000001a038403801c04d0447c00c1d8000000002c108020032920b941100c0004003400d040d410820b84014a80450700001e0041c01d200000181c148007442c5c00140140c0100310362000175203866481a40292160000303058041e2aa4030b42103440c800700055000e4901405080c05013580b544c1e20481401c2c0c08041c2030320554016154000400d0550801000706d50850b0a00c200400c0e0450144843c090303000c0701900d040e0b03003954 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 604434046 1250 604432796 604432799
    0xb2805040617211215040c02070501140a05041a19051e0412120306090c260103050714010c0b01030501140105010801150c050307060204030b01090f110304080c07 71
    0x10384a104640150022031020350400b400151060f2508012a940081d940d00b003c2d070b000240314103103044802e60000d20f8002030075503c0d2103074022401102440d180303070301500302500c60070815070005041088400907a11400b4501c407048103503249104d05500c000c0050000c120612842e4403590b980c0d08008048030510345000c2ca442cbc07a161258482c08070b0cd40019400003180b40c246030010620301001c40d4500c100c145010b10303080044502005102c00105050300c40301c404540d01e40250b201000822004000380126020b89400411141d2030200c01da401c0d00890380201c280d140280009416280e0050081203940c0c101900314403049502e1000c2410014070b582c030040003c00104419000b03611130000840c011154030104184514140c11660401284100410040142c07005144810584c0d052800d50464281002c600b0b510a402020740305a00014000040100c0161524100d459044080200c40d43c0641040300780e0b840d41341041c4c0108410303c04140851000c0d1b00408504110030704945089 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 604435296 1250 604434046 604434049
    0x60904022209140a0b01020109020312130905060d150b0d060b010e0306040c05040914030a0504170a3f020d14070210110f07080307020f03010b2805 65
    0x2a480005a1000d90440c095808905610184000301800004030300f88403545484524500d59840101048500d41d25440c4042c0164000e40c400f8401580103410b64020000c4841e24000342d40c010010b940180003000c2002955440902c81c15004410060084250309010303124043c00945040c01c0c3d00001e5561042d1039130745e588607144404d41511030354020690403007480001d044070303400006290003500120100300000d905103801e141613034801c980005000505040c64620042411800c0d003280c0300c00211007116681002c058403c4803c490481e5560b04000c0d0b803100c0e01c0b6645148002c02540040c004847c500044141c1c41d821012410503600e0b80c40c40e444410031000f46421000405a044040ca0360801640700c1080340c403a5500c0e40740035182c40000c2d40405d0760410203001d07401c02c00621490040384c805090004480c90b125640c05c484001d0744171041c19032258030095040380705400039104050389040c18000d184a130b41005054030001c02d11400c3c99414100c8a40c424010a81d030198040f03000d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 604436546 1250 604435296 604435301
    0x2100207080d0f12020901200c03010905010203160912061a0301150305010b010908031905090604030b01050a050a0312030b0604051503060f06160f0804090516142502060904 76
    0x142080e030794480d24000b0f50301c00946069400004000014010850f01c045030360042e0113500c5501c01d0341c6510710484907880780300741404001c8043ca42d1650030494490140301054001c0c50080340180d120222800704440b0965500e01c040c4125842a10082000b00c00b00c0d500e5405400322803280300d910069240400c00090860f680000c0200300642a100c2c10700510000740b10310701d0101c40a00340030505600300f8144581e07074002c04014aa0000030101504e00c401c0c460001da0341515400303031141c0d0700c0d2070f260f11381801d02e000240542c5000f5409154001058a810064041100c1d00060b04440e0706c0843c0604401a0200707140300c0e600a03908100c0000d442e2129541003400004507882940c80c0d081c000f0402109418201c0c055100d05001c0c01510082d14070030748814036a0798450755403144010507103081509406940e2089464914000070400c500281d0108260101c01580c2e480031040c00c1005000854041d0490b04269580101c041ca0700c4072143c400005107540c002051242015403d10000c0c06 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 604437796 1250 604436546 604436563
    0x311070b040302010e010213030f05011d0609010f0507050a0825030c080606090f0d0c050a0b030a0507020d021c0c0b07030b0a08010e101e050403022401120210020708 73
    0x403500e054a08000a155081c410744410b002460025403500c10307518202107a203612404041c10301d00c141c22005003003100940c8201146922904040a103855a022040d15030804403070b07503096942000c40a025650b2148509171242000303884580c01c10191103c01c4403401c10041250520030700b4051501507403040d00b51058441d400c0c81d5404038046517107200c003e22024010b002140213020600c514500b41d9683c44000c140c031401500c031031802c60503034184400c80c2401075200d160072102d280c801003500f17070400d00107510400000100f80a60b80b11020100d07583c00e41c54001c0c0c00107812404403c620516551900f8800480510b00320100c9680d94442d03108440c0c0503141e0102007903984102c0d4685050440c00f003401041c0f6240204078017080d4001017510303002540240c0100c0ea903601c21486070400003c1e0380561012120204002c14503091030040c3d500c098406010014080e84000014298000d4407500d06861800540b9500c455007039082c842180710f10509481580952500450f000b5001c119810 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 604439046 1250 604437796 604437803
    0xf0201110114280e160b0301030c03030f0c080d0c08060612010302040b0f0307080c030616020304060309062d0501090c02070504050c12040804030b0106050f0711030715080103050d0e091501031107 86
    0x1400c5a44c0009a400302c0c0c81da407006c80d000b0307403d00040001c6500300106008407501820214440101610f04480a980300310000781035400100c1c900c2e200c0042c540c001d001c0b196050300d07041090346900c0200122030085800b040094511a8014001800c16800c0070040840180c100c4c141203914070002030404909800c030032002ea0080c042440b591404104542e00700c220800e000b503444200701d400a40324482c0e0b0050109054543c051f030000c03c29113a004440049005001c07841c0d50842e00e4070741000781400c80c8121205800c2400108820215200c1c2e00040d56a81e0014200c2503c0e000071310010303120040980340100024088403034290408844284141d10a9828a40e510b0852401090000c0706030080d4042110903c00c99400d88016400c98034542d800240c9007005260780000a890151650489820800250080c101031500030083d1810799218506584490b82c1c4030804580318505407a03429403004038030010032650381607400468074202043c50041048600c541e0f01c0810f9501150084 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 604440296 1250 604439046 604439053
    0x120408010209031b0a032a061205150d030c15090807031106040b34050c0f0d050901080a020f0a050307021606050901030e0f0601030f0201110114280e 66
    0x8046103020300001c040c00c40c07142c406052884801010030411035207400000d1480c07032416040507240c0a0195800820041098100a001d071202d100402002d080b08074074144031b00b00380128007140800d42140030b2f01140a13005440304806a10101c0b0620045a0160f074a60300c4aa00241000114041c40001da0300484031141e803043c807407800038005503611b0100f14281e0050003c0c40001184101340e9034102034041011081000c00980c0700c00080901701c0300b83c00b072496074216110300c5a000809002c1c130410803403d869154401d00d040e01d899000c8003410f03000040702040205002e42c024004e0750380000342603074010b041c080180c1e0380d04243d070300643c20368011840107c1008141ca03410004c03102d038074002d04d9825004034581200900a400f881041c50306150302d50f020f442d01410308021224821080d0000ca40240d41c1d6403e00909600c503401301a030001c5d040800c1554180c00500400c8440c44448c030b0928a15515030760181403c01c02e00c0100030180d12060007108403900c107400341d1501c1d0303030180f03015 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 604441546 1250 604440296 604440307
    0x3052b06090b100804050d0e010e041a1c1a100b0409050a05130f0803090f01060308030405120a052d03150a060c030c080c071707060207050904021309051204080102 72
    0xf00501d0618041c0070408001401d010400015030114140600340118140702c03c0c051705800041e601c2c44a959580f82e04540703440c00445001525191035900c1c08019601c455801d00700c207102081c03021681c080070308010701d0703a80c7c00510b001d0245900d543c0b0001c150f0081c0002c03900d07000200e0030759015502a13041c9035211024031040440034401e40e900002c0c00e800340300b03950180340c0d1032030040104e40780c1c041e004440100c000341c80c145050000000110745940200f14160700e80c58415004d420640d0155164490b44400151018081007101ea1559458880c01d003800850424680c4851080803540e80721a0348415001c1103641110145001d403442e000f02c00f40024a00060100c400c449074410820440d1003088407020a40041500c501310380c102520f00d83d603085801105140460603440070300e01403514000da0031003240100f02c0b842650002e500b9a0a120313511010401511070907500a075010f41401c0078201103000300c0d400012500c3c03148090300c600354840d02007110340d50016807184100c2d940002d40f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 604442796 1250 604441546 604441549
    0x120405030a08010f03020d0215090411041401090503150403051207020a0614061003110702060c0d0207080705150a0207350105040f0b0c040504020703030204031a0403052b06090b 78
    0x3405004d08584518508400c0c07468002500d1100b076054003a008000e8032201070000702c0c04c03070120b40101c00c01800070300c148000c058031704075140c2c0140f15905100c041804200304039886a1018000c80d01c00800030041d0a500240b807985861000d0022010700104215508000d0b501d042d80030b01c940c3c519000307030400a185007800b1090f5113810007030044c2c05440d43c04012070f99850300c81000d1031141d0342c60002407038400d045070a495446242c1000c2d522030004110707000c41400000d40d0313081e014003560a031125255071750402e0f03599134218014158000509082098228001c0000d80200d4019204450009030745002c0c00031010721000d20405090120a081c00600010044c440191241f10008100c249860f40301c422012150010040407a01e4401c041186815100306890140030018421540c44200b4038018009500c640b208032607640c3c506c1c10040c0b03650344441c02e107481150140c403041d1510074125140c0d44081c42344885010000c59408241242c4d0a15102d0700000e03003125100000c10610030030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 604444046 1250 604442796 604442807
    0x6012106090f021f09090b011206291312080d0c090807062a02120d031407030b030c04050a09080304050120040308041e050414070306120b1b120405030a 67
    0x41004ea01c94440c01c80849980e500c4110319003128035900d00011660001d00040360341c1c107007040c41c06034054108513010450f150b48406810b1528000a0105122030407185000780074055010481045040400c08108002d941c1e03031809e000500c1418490b02e0020348014040c2106c81106541c40003510300d0000740501641000044054a20390071720380b0b080306890748022071b0540900e5204141c2074030800e0b800110340ba101c03106440c441081c42500d03946164104000c00074441c90405002101c001000725061900901c103008a00c0d2001c0c004d40f011550890521001e04409081c0b8060550307a410510b002c108040081d42c001e84c406d1002042040551040c610307000504031540ca6051020001003000a1245084801302c0c7d410040c410038146140c2d2561400c00e40b03e1344440c1d006410139954040410b011568184030fa00151403c008164a400d900b014079561400d00074400551000030816000e602d8200300105006840380d0f5203010390410031407280b54000d65080701c040c1c4c00880c00394099074022 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 604445296 1250 604444046 604444069
    0x60a14120a0c0e15070303060b0d0507020c01080f070809160e0a060e010501120e010b041a090a0c09050f030a0f0b04050c06160b15061305040f02070506012106090f02 73
    0x240340c03c210450016000544013241d90b4801c4501399130000f40b42e02094000d8001c074000303100070524244c66410459403000540011103941c0010300807800964901d41c05103400d41e0040c94090340d068003596030b40c034064a001d407005d0010500b612a00a4030003915a002c03001038040d00355003140ca081c0c0d003403034080d1000342c2c0c490340c104804880406005012a0b40c0c030401d0250340c107205510119807094030580f05401800c81c035270565003050030040302c58403500e040302c0d00040840054802e0a01990384000c240c0846003092408400104020400c015520381a02418071945d4000d00b6180005c0f22580c603000502c04010048800d0700b018010002072110920546010040c19a0140d240c0110400c00c0d078021020b200000b001c5054250105840351102c20b4402c1d81444060030303140d91400d01c071410030345050040c8150783c411402c1283c400e071940c0c254002d0b21581540300000b010940d00304a120500c0300e001c030556001300e40e000d00700580460070358043c0c100760038040ca840300c0035030196006200c080c4015 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 604446546 1250 604445296 604445321
    0x9030d06080a0b0f0c0903071212031505040906020903060a050f150d03031a10030e0106050a0b0d0203131b05150a0206040b0912070516080a050309060a14120a 70
    0x1c0302d81401040e1181c9049910080021919865643e141c00c60381540c011441312541500c2014004100c1e4450b0650860145000e2000000540c84150044064a11a04105946007242802003019003450f4004200c1140b041c0c43c00f6003800e80103000b29127020800c46000701c4081d00c900521141380030700c903a100d400410526101c0780c0001e480c1c0218200940e410802403c255491400110302c1d81c85848220302c142c0014858840500c106034000d018102038518a01107529200002481d440c1c030581201c111001c821081c2d0a000664410b10002d4100070500d01010711040c144d48001200559880c80c011070304070000745294100380900076400e141082e0503162000400c1340e180501c3d000111b10350300c10b0780319200002d255201848a0b00740f03100281605540400801d409040000c04202d1207011051100b4581c4000e580c0d100b540d07511414000041c046070001c005220721070a020004211002403414000d501031f483c41031641696000420307441c00703020381c0418420512594011b100201c4007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 604447796 1250 604446546 604446553
    0x4050a05030a030903080912060a141f0504090606050a08030706050a0506060912010605030a060b1009030b070e0102070f03060213062613020a030f17030106050d180b09030d0608 78
    0x690303000384c848103207400007900380700d4042030160b0203136140d44960794000b204600b130702c40034100500900c000d02405016800100242070000300c0392558031542c4d44541f003648880c01882482d02e0180001442c2a0005407906a2114000324403526560300d200000c2400d1b0006580e150546d06101007210400381592051500303010901c40c556071010250b032160a005c4881c1081c180c600c07580355004004941c440707505400340303030140d40a000035580050301c80d101c01d50300b80c4001909208200c42d004003501006141060600100c1c1031b05d48503250741d0358a07843c18011a0155a00c2c0c100344040e01407980d008660345600010480000e111680e4914010b001d01c0c00c0a4006d11104c0c0c5814079030400c0e465468000941541c001000c124901c140d0042490300900b8821419490f800c0201264009403420355031a00c070124251001c194074003c80e8100c441c0c07981d82900b00740a186140d0060188002040ca050741414a204003040080603018000c4410500648d500c50100281005842e4160311110203900f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 604449046 1250 604447796 604447813
    0x8040c080c0a1412010f09020a080102090d150b03060c031608070f030c0c0606120b0903030709090c022109030d03061202010503060a0e0c0d0509060603210f030c04050a0503 76
    0x484040b402401d4600f01c46000d125810b0307080c0424200444408144103640c00c001c9944581011544043c201a00a68509000d42c0d225007401d42030348601d14205412119000401d80484c5e99004c120042740101c9001141100740400042c0c60a10255401d07800644008144281d09445600d0f44245803c5418828002d14061502420110302070f041070041c903071241e0351074044511481c484111103602030401c00c4500c0d10354040801128030404c0446800c074201b0049003a01f4030010540340b150a0651b00d21200741c2c14605400050304035a415202035126001001d103c0b001c0f4004400d5a480c2083d802548a5941108040ca880b44d44103012050600d001000d002c01d00032002c05411b481d0b02801e10715507907200c0c1e00206240310f4040d80a00f0300f201900c82401850602c040060030000c0f8190340c1841192241103a40c2e481e03500940705140d0651016405207089110540f11116424607841001d04201c0011440c91441e4003c944044c0c400b000000d0030700161914003503d42c0034120550080040f031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 604450296 1250 604449046 604449049
    0x8071b0c050405100b160b09072304021215040b0a0303050f0c03131203030501240c05011b03091e08120c13180e120d09050f070608040c080c 62
    0x814040c035401681c40d040066100e42d0046134a000038802e010380c040d6150324032064100341009040342200d580c0035000c007099190720f002590105885041124405080121040c403800413102c60070382e50050303024041d842000580c056258071604603581c9660400c100d0404100c2103440e04010a48103403030380001030021944c0b1105503802d04a409289541c0e6081d404400c3d8514095000c0380b4102034401c4078082400c5000303030203e07e0624441c0e1024455662241c82840b81030b02b241c84800c02000c20b8203021500f80e0721800b12007000c54011000080c0c6007503040380759160f20b0f040036200c5010984550150080001c4031040c4400f0400c10240164820712540c1c0c0c050103849100b6107403684190940110701480d01010403038503e000f54001d509502c565030184060600100303245100502d14140c0b00d182c5102c808605507603411b0851007401d24141032000070f04003c00144000f40d54901c04e03040089240c0c001080000c0141a51707489185030303403400385405003268445d504002e20f140c20000c1c0e14040c9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 604451546 1250 604450296 604450313
    0xc12290c090f1504180e0a020d03080718090218120d0f1e111006030c05041104080706050c160501020a080306040f05071e020a02030304141203030708071b 68
    0x8410129001901c840c0054000740c02842c0c810304911007158000b900080c42d02d0750303c850300a00310020b03809000606d08950440d484240c070181c0070750445c89100000c00001c0c860211298001800d00b03045840001c0d00c1b604015500f034503000383c080594000349043d04200c0c145002c8219150071078485070000d2604261030384590b044108030702400849841c091965015050310004140c0a906074070b0203504032140205440c0d1030340c080d0121400346408620010020f8018070007601d81050034503a0843c90481400003c0c4040400108003c50a001c007040341e00302030090074000c1145aa0346030300c034103010301824102041d121110304000c4c944e500800c02a43c02081040c00f40c3d4000409a880b40c0e620400300d40a00300701a45051000e2820f001c20851542102d208440da094080400316200000441603a03034103081c040195140c1c0c02403004211594050912200e51480984407c03416202e01020030301d980c00941d074a40200384d52208000d0300e141d00c904071141261384013510080216164950041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 604452796 1250 604451546 604451557
    0x7031d030c0c1c0f02150d050f181b01021002040f0302010813051002090120010606110f120d021e03061306060507060c11071409100b0a05070c12290c 66
    0x994220a04da4190750300d40108031042060021040c0d500c1005000b0040242400c036103038400c07140d4540100701c800340740409000840b02000300130208040400c10341120070b400611000d0451240c080c0c200c1c141080e0380040c0008001d0545141401c03030a620001d000300d9402440c0700c4d0b00748860309464000c22000203d101003040c3c561401a61aa520303c0101c40c40089030000c502c4000c80b6000000c4200c105500001c202c0d00365540311030491500c1500c1d213881d03c05507040c2100c2a40418400c1c5040001e103402000c502c9110100189406506010b00c2c1c4e8040c1d007059501d060260200400556040c201c03800e81140201c15010460706017010005802401001d00141c2034554804030400618020102d0000a101c030301d086902c429900d05003031000c5010400043e0141c1d4205001c9416403030f0f5408d1803025100004440d90401d001e0080c00c80301504440f10036a1a0a050341c0c0000b5410b1061006c44034441c003502240b95540d00111104d0b10400c510101840f45202c100208043e10b21540140c90 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 604454046 1250 604452796 604452803
    0x7080a050709110702040e1606030c0e19050a0305071e0303170402122a190510030f1814060c0d0b03070e0901020c060112020f0103020307031d030c0c1c 67
    0x51980602e0303c00e003114020740c00300a42142c984502d10195034400990001c503403074480d170061480d60311031508a00341c8a071460703024042441052100081d00e02126035252044a03010300c0d1400c20740c1c960018119901381d5100b0f582a41128106100e0380b080400303c08002501100019070381495560300912510703024041c0b0349040c034502c001c1011555143d08071500c409240c8200c41c45512400d0b16261b000030403403801c3c03070203c02010411703a03c1d0400540e0075080382410511055040d181c1001d01c441c02054a10a404040e035a5002200014140c030410281c803011380300f41212110140361000b04402405050200b42e070140b8100300d0303040040001c45014406c01c00d00400c001c0d041d44042483c0c04003540019203034800c10420001c28210550182c50304286460444144e6680d440c200082555514030207504120300d5002e80712554001d40045810000e0340c50b0002d513104149042141c0401c81100302d02440e040091034040741d14040088052010080f0b50000b001100e45070804040d003103840000307 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 604455296 1250 604454046 604454051
    0x209131506080115031a1f2007090e0313060201090201080901021317030d14071b030e091302030105040c1806060905041a0303031f06090503060f04060b03030409090507080a050709 79
    0x1040455070442d5442000d240140208003d00101d0301f0059040807802d0440c4001490104da45488514030045031032080c140c403000d004c2c29420840200080c240f418060007030b500c001c0020b0091480406080002003003203034000226504203100042c2a1000903101c0741c95a8018016028031140d005a484221000181a0714080c0558a8024194001c141d140380340c503440c0c0300c0e81c0302010088444882c491081d03035882c05481080001d0f2201081100c0f040a00014000e2100300038900305541c0e059003111442e09051481d290940c0082e0035604200e508a0720008500e50820a4140c407042015540801c03c1e8140001d90400d2030041c9200300030301c20184116100d81a0101305042a05092203505002c2d007503940e43e2500b042d0701e008011101c0382820380030042c01d400140b0796110f40c4000003610f00c0103025105079221103406401c440303400781065610550760328200c80d15550401c0104001c1c45181c130b002c664a1b0150410600b00001d5070300508240d0007042460700001c038049007910030398200c40d000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 604456546 1250 604455296 604455311
    0x1a0406140f0612160f051207061e140703030b030c010201020a020c091305010c0f0f0305040807240c0309110f0906060705030915041701140a020d020913150608011503 73
    0x10350b032514400d00c18444c0c1c1145184c2000c1074002201c140f0b0b81c00d0318425542921640700505019a0b181b0346413040500290284000d240d41d9080c519880003200b50300e11304006081402d500b902c0d815030100704110082556501c1c0303c2c9060800340140c03104010240000c604003018184041d4403034918001703081c41414004005501905080301c003075941600080200031021075100040c0c16000301140d040b02080100e0018400a8404d000e4580304652281045040c80b609584900702c083c4207101e1030a00c0e41c058000031606100c14442c03480e1403d82590701280580e0345087c6007102c00707148000c490162100d0440921a03443d402500c6800032015124169a4092401d0507404c1d8080c085542d40c0c060a0540040705a000d02c201500c20b445030001041004401c100b0740901700c404042034003141e0010a4005103105085901800800c440d2103405447e120045002407451643e000c0004c0e061a901c132040c6114000c3e2004500241096080c0f0b800994180a03203502c074401010706010030991039800c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 604457796 1250 604456546 604456579
    0x30f0f0f0c0a031812020f0d02070b07020103140f0a0f0203090d08070c14070302040e010b130e030c0105010e04060501050102030304031e110d0c0312020906090910031a0406140f06 79
    0x1180c1e4404e18071420150242150707140c074141c03001e0540b105c80014841c0b20f501c0400100040743c01c150351a1070360007c2010038a029086141e982112038240d060603583c402c0c581e255942004268030903100034104c81450f03e018006c1000b02d8000c010795180b840e1050040110f400000100f540c4210f00d0741c02c0020299450003822070320382d0b49542d80108402c61154403461404800100394041d40e100315014422410709071040c1b030813a6802d2034040d130301c4a414404440901e6640d840b01036444981f1f020303070f0b192022166a01d425510281d1014030350303051b03402c200411321060348038450142c0000d00c0a140f031820140c500030a201c608000308941c0145d0300d03c401341014004d0380000107001940c000d40303251900314100940062082c080c01e60105804840dc83c00c2c0003014401c81301008801411641810030590500441c610028001000d4101650012012418403214406101505580e02c000c4d403429181c05019100d00010001100c59000d041c004040448011039602000a030754183c800a007000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 604459046 1250 604457796 604457801
    0x1a04050a0f0513151d07030302060406050705070f12051b06061203090901031502070f0f120e0a0314010e061f060905090426130302180907060f02070b040b030f0f0f0c0a03 75
    0x3042048030340f1030706c00c1c00420146c001c104548102d004a108100e00c1c0d40340f84064450380b1820340700800d01100754002e0700000e49841c5040000c80010300c1c0040c1403140d02554200d2182c42004100d025600407070812078035107000d0b4508464050301001a504081d05540410507910041c04024804005000030b03400320461941070f2041180c012810300c1c1c00350014204650044c49260043d034008a03a5101001c2103030155861005010000e0804261715103551150f03000c00849064401c055520351b4003502015400300025401030702c011060703144c4808100d80b06404003060740c4c401c1080c01f046480801280e40c0780103589034040c1c0c0210001e2502003440c15241d07510b0b54000641103843c0c5010880000b60b20040400c881134030f100b0364080d0000c050300709107106618030480303030082c403a1f010000504c8514807812a200d00305040e4012214100e48034800030707100d50400c0d00109000c5002008010041014407600c54008000c00c3c00d145040c18840c0c0318803010180249014806031002a170002c4080c46035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 604460296 1250 604459046 604459091
    0x91e05030c01020711010e0301140a0c030204090903200d0801063e01140c16050f1906060509060d02090627040c06050a02060103061a04050a0f051315 66
    0x80001c560310130380e030b1515141450520303840f10b0020301941101c0b09070b0b0a0500ca480213210144001452603601c501c3e042000c0c1800c0300c1c811040540234040040c40400e1402090800c91007600d0b9452468510310351003d03541d0f904584c1d80c1c800d5000e00b811000060300654210b042d90054a00500d42c0b4140d60340b119a1180001040100402030020f0101c480c1c46134200c00310000c08950092200c8000b03180c1013419410240c0ea043d24041d81084407c00851400c8400421140704100365100800c804d03184a041039840c01c1c0400420702c0c117501d903004004552041c41c028140032078400c642d504000000c02d0420004c0c410090240c0010300210b4000c2d42c800c055103070348031102d0317211803002c01103590000b040c5001a41c007110280c1048201140320742c000c0095400440d4160300a000c1c030b81c6113860310b81c003505e0441100038000c044400c038082640c596005951040154034070104042d0040448402140c1c4010070407050313880d0b4000c1d103600087c485641000d510040f20301c04207505414040407079192911 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 604461546 1250 604460296 604460317
    0x302271306060e1801110901020c120712030e03060a111909080a050106090e031c020a1218030e0a08030f0c0106050409051b010c080702240c150a091e0503 68
    0x2003c10048130b4200c80c2d012109102c0320b000240088030302c00081c600c1c0c9002e5041c4842c0543c018400e0b018140c1012440101d05044d21800c96504075510704080030020803030310040d40021446100b040c4141008c1051a03002105104100044107081e44800074a00400354051418089184181d03030280c0300d0050310380035044190503560001d1b03451901c18001c02c640e10680791080e081c600c0001c00000c0c08029281004081054080c043c114403807000c000358410208402442501606541c0b143c0c520302c10f0502100d0065015000c0034a01d05010b8401640e4400c1a44100d00307445051202002c04800d49800d07407041d510464542c449400f0703103405401c0541046030000e00e4103048409118001a95007416402d25900b88a0303202c44c44c004540b00580044080c00d800001c10000c4014181101e1219400001d07041c1d019101c4c0034010881d003158803d070140101507001e00b0b482a40744040e0741c8080d400841c00030342040b442140e41c0da84001c01201e12060000a1403403841002071000610455125180 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 604462796 1250 604461546 604461569
    0x1090b0d090209010b070b0f01060e0d05070b0406030609050a0501061d030f0a05070303081006170c1c0b1e03101107081201140102150402040b01030902130501030227130606 76
    0x843d0300f01c1d01030035000200d05998041016004c41c0450805008d501c0c1641c005135100e8105030342c4242804089044034408039042e05c18030000203200700c400005000945400d990101d0703514034201115007910b002621131940b0900c3d1a0040180360782011a01c0d28a44461075101341c510480c600107420705000070119409030060319140000c00c100894100246c0b440b0b13458024480c0c0300c1d103220312a0a58107025030f2010800d0007000401081d201c2241c2d07a0322130822103110346001c0324110b43c5a00c1c9413414010361000d90b210408401c881c60005001d14944a00550074003a81c0440d200003a5222401c0403480380103a91000e0701881e004040301100c5031a50852803d030303a5010b00164941898100348121903c040280d03001a40c1d41d0701c089128100c54003084100745080d111902080014005455180d041c599140110750058446801c01140d4102c02100010198914010b1054490102d070b0003040c6803110328034201f0324000c40e50100c2c8e0042c2c0914074000d8070001a1400320700808140e00894804c0f070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 604464046 1250 604462796 604462799
    0x182a0418020d1407020604030333030201090803070b0604091e03020d0206070e060a080c1306080910090c0303032414030c010207080c060306030312090303070311040501090b0d09020901 81
    0x180d94000b0625001c00c0307001041001c01c12940001d0020041d500540107800600c041408203120f0740000c41c10103529445028186000304c0c00780c0c554036140202c03c40c0140e80d80010420340da0404900300041c0000c00103145050459601d25000f00c80c01448a480340d9500c00543c01031080c224055a8115401c6041041d00840b50801941c0d8903220948200103100b0701d000038040e1172083c20034020141000c3e0a040c04e2619112040d1040b01c4000c103885920007041c822050440c00c40019600101000d4851030704038104a0582410b160200710803012440c18590504000741c0324031281d17801c90b5054540065402405020300102003420345224214032181440860f01030010000045410390460844a4039401c0d5401607803a82161f121350300c0b031604911149442402c02a00455000c1d90050549103062000000d0703801c244000d6803a9600c9500100c100308100c0c0c0c040c4200361940b9414150607007050b14180c00245109506d0040c40c692042c042400982c050450700b14911440c2d0081c8051001e6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 604465296 1250 604464046 604464089
    0x15030210080103050111090d060504030c1220030301060207121b090f0e0607090909030e0415061413050d0311010501060503070e010302040302091303050c010608060105182a04 77
    0x8207402c3c001a00c0c15442c2c400d40c100c1c800801002c403001c007500038010055984440d21200018680100203400744852940ea0800245500c50070113441d205946841580c141d107418120860404920300240030ba008100601000d07800003070002c111200041c03005500141031030714682d040781c021001418440704e45004070720b101013900440c9004d0000002000100d6895440b07558a410513568180401c0010300b0610202c0e0150f0000c0c540180a8203107942daa16680001c10200c800c242018200030b41d0190003404000d60105810050981c00c9401c0c1c1d0614891080d1090b01501c14400d0300e2044400d000c0000c2014000e03000340b1015800600200015a55094007500d181d1044841200080302910001d0003503000744261400d80c0d07000f4080075140e5840460402712034015400517014042c0921026500283c24001c1801030712283c005040b01d03500d4042807145106035841c4101c2c03c00c0030b101c2003044038499000710002130181c000070400200528a8407540300d20840d0840c41c50115540b0900205 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 604466546 1250 604465296 604465307
    0x131d060a0204090e0606010e0f030111030c1209031c05180307030903020901050103060b040e0c3703060303080a09210201020304170f07030e06310e1302010315030210 73
    0x226809143c081c81442070b00340304580c46007000c440c1103021074407032004074003241030894950043c0400500005045442344d03803032440c2031704102c8030344400c0b03003000414980c107102c00c282131030300821245c004505204041b641c0d60074280300d000c00800354517550340000d405024101410441c50701c1542c1941e40d1081e07281001003007880e407404181c1c003c443d018000255944644135042c01c45a02042513400c0ca0f003800040360119101820b000c1d030445040c080200c1c480c0942220b10740c0c42043e02c151041450981c03110078840c075076806171501414940070042001c070740c11405166014205540c001550300d910f02d007a0382c003007140720400504c502511148901d40d64055004501030b42c018802540200190754242096209018440c5004c40080c0401e000090203840000c01021700104101d0400d500c090540c500c1c6121408076403511200384d00f61015040340f04a01a0261050101c55821440c045091a1861500d181d0090400d651401c07200c900000300c3c02d9842c040c55009155103600807098100030038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 604467796 1250 604466546 604466549
    0x7030c090221010f0b0711060c03030405010509030315100c14010605010201180203031c0f151827020d05060f1b090f12192f131d060a0204 61
    0x41011640505036108840c19002d030403504101900d102c80390800d0440c100c03a0300001c1c0111001d5001071512801681e035040a81006442c540080d9200e2406050480c00d541d40504112020b41042091006180240b051202284000c1c0c551242c5021300310001c442c001c0c40c00c5800342c01c0200000703610741c0070344040d04004100c580c240d0083c8848080c03621a203450b0303055550b00071b61550082000004107400790307640300300344c5505c0c600014090545c000e00d2006e030348510b1140790308004c1e02c06007441003050300c0408072441100590b00700441f120310f01c0070f410350109a012000500485144000442d510406c0b400f01c4280d00c10144c4a0504003400321200d808010f0743d120508148a880360b83c0340c618050255601c0c6a4010100c22800f44a1400e01140c03149108800d42c0c0f501960902015040e40d8808141c5ca0a10880c4881203243c44804600310f004003450000307240300300c0c0c4180b120040c5d407003002e409c010f403075a17140014207c81d084101303003e120310058050005024007400c111030549030354007620 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 604469046 1250 604467796 604467817
    0x607230a050c1c2d030b03100212060a06030203192d050702060708040305030f131a070e1822020307031101030f021c0f0b0316080f0a080703030e07030c0902 69
    0x803034020490640448034110090f004901510305803119002e40305e0f4004603120345026050310841c2c80c00c1503541e0180d9200307c00000c40320111000340010342c1012001a80180080d140440c114241a200b6410303201402070700010ba1900c400141071107549607001c4540240c00c104015000c0d142c0a6900030282100b00d4001d0007600030100003070a0203000d10003140c440d079855924645907a44000903500c4284c4094920b600740410103680b08002145200d40c42211140d65044000c18039298030000c043c541c0300d0b42414041c1c0480f41100c48040906500c840c0c0000407000e1032598030b103414156242028044002035454440c0396000800d110f0140414a0344400a903414403900d80d501103108180e201e18480c02820395288020800100c006502c003c03151503502d10046946032004001a1030143c6c440d030302010500c1c8004040000b244c0c00c00c400211a80701201a15802416440307001860080700c0f030290a142c1ca331855489442014003041d00610b5214040c2e240306034449a000009400280070007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 604470296 1250 604469046 604469057
    0x2090618040501080c0a031403041d0a0507110723090c0406031512030c1b0f1403070803070201050c0c0918010b120d0315091a01020607230a050c1c 65
    0x480d141348003140300844448040c1150029a245035a84480210125007803401d6000612022a1307550b1b03a608c080c03102d8081805800054145142580112040501748030248910180030701080000800c210b02108c42001040301c2c2c4d4030800031ba1040c007544544c00507034480507132004c000c08540844c0260080d16190b40c0c00b0054a010040e07551088080c3c1c0c09118105007102c4044800248a11814079017940b00d6078542021260f0491100341c010076940210f0b004446d8180300b0f10040d12050709a401401c030890051110070f14041a9644034410004041d041000005e000703000132004009000c29014068002d0140346001c0008a240c00c40380e008484040d400e2000c050258982059520703403e14004024004032251854290010034441590400b10322601a001802e074078a442440e1814030000340103800755140d500024103201d0024204402e00a11400100780c448005018000c49003524071030301d0381c03484100c03000e84080c050054440345038802c00f41090190702c08015048100c0d003c42d00c03030317 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 604471546 1250 604470296 604470299
    0x70f0315050405030904020a0c020904122601140109031502180409150509070806160206011e05010f05120a090b01080c031207060603020916021203090c010e0402090618040501 77
    0x424241c0c0c2081e600030700690710922030002e00b85032036401071140e083e403410164402c050700c0e0b0200383d030007508030303403d03101900c9035100f011a89030001c074401c02d4203d002a440c044a03040507448614000103010754150307030020070440d06159000300d100001542c2c1005804400e5200c101481300a507100503504960f95494003040101c6040a001d04c0c00c10507840300c0c011051110b0b21500c200202401010403200b841103510005007858280546401050440c00d004080350301a00041c1c80e000040e409060f2910f88039a155251840a1080c3c07825546c092809828080e1303000720848982c0909114409006c20400500051003e0381e40042c0041e0312460003084a0303a6031305c11003a1110001c00794940c040e0000c1c07000001d903508040c001c100d03884c82460001002c9480c2c7d0081200702504071800110312074840c0224030f1054040000720102c000055a0b14a10314060201940f00c0072510720250500154060b4545655225010f40e0f41045000d42001d4560103e0201030b01c2c12588006014015480c0000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 604472796 1250 604471546 604471583
    0x80a0e0111030304020108190e01230402010219020411030903130605180d0606081221061005031503060a090209100506073503071e09180e070f03 64
    0x59140c40940c0078051400c3d55100d4005540d5200c1c01041c0e00884000c000c032100071580903100b403100e0f00c44032000000b101d02c00780314540881c088480051421140341d00404c030041c6e9000a24490f18640d804841316903c1c0140701207070280c58189500481c1c500007004000020100202900002e03410b81c0540940365681c10094506200e0541004181009110b260030a07050841d1a44161449200f000400740d640308803075420680e2041d58207811117000244071603560190590b11701000503181720680142010000184128001c0c4801d8003401004000140ea11840052041c0b943c2c4001d401d85a81b458810f01000c0282642c0300228446d111a60206402c085440304440030303640d010b40300c6c0c2c1c5019500c0d00d4820341003688000300a101d0324100300842100b4060551203c200801c803241325100e00b86510003914100e50101200c140204407180009002c1c4e00c00a100e003240c498018074008500c900c102c42d0054040c80320100402e21620500152000f004001401100e0180030b800c2c42d04403590390f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 604474046 1250 604472796 604472807
    0x115120510090c090b030304030b0a09020a14030d030e01150e01080717070b0702060d02180a14010c0323070c0839130e0f010506100503150d0c03080a0e01 68
    0x82001d01800c16200f010b020041c9658007020792000c004040740d04096a0b5034648001050444030020f800ba03d48000d07208608020407418090502c042c160080e00420001081e59500c0e40c8000404151b140c00c1078104101c020b600102015011155981003507071550400b982c0c1801c2845a0240ba03c030b025000103008450306080c0a092381104080d0445515006020444d90020030382640c0c1b006e400c11000c26030094510042140540d100c090030342100c80441048112941c50b8032880d0a4440b0428403803450381d000140148159040c203000e40c2102c6c8500740800c032075421000043da03481c00010075005002c2194004c0049540b580c003298803010408500c00c8411f0003044141c864541e51600c0c5406e2040e0b544000042d6000191074070070460504080c0006a9900340c405002a4220540b5616041c00030b0041c0c0d6805803017030b210313040c4222200030f00800f07512000304044d203d04003402c0360280c950340708000740d400c0c281c204454540f184d8490400c071260707500840340280485c0c0100c3c503c540650186 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 604475296 1250 604474046 604474061
    0x1308160f050f070501091703042102130e030318100f0b0f0a060c03030207050c060301090905070902040627080f10050f06130b01020109060f0c0e0f0d080c0115120510 73
    0x41e940c40d03600c2447e040041d90456418180c0d4011408140004200e07915104006291441c10302d580c51000342c0c142c014000d80e840b4102c440c280303003418420105900c000001c200c0350070441c19681001601c5002c00c55604004100d12103500d1f00f8100b0074000c0807020160000058003400f1101c03d07403421070f03480410200040752310540d00482c0c148241900828002da000c3e200c6a40140d05403598054a2000100350340c1c030980002c02c00694a000c8403081c00000c00208016056200c021071400c1d0604030090a003a111080b210040c080094410041c4144000404000e00581d400c4030080050030403896115044400d40580051501d000901c95071100e4031110b000d1080908260f4400200c5208003002c0d12000310b0f90740c103541d01d480101d000107502c2d10452a070000700d132000107692480c5c21002460154080301d8030b4403030304a6100030300e0940e4424800b40c0800d40c2c08200d003036580740d440503004d000d130003100040c0882c280800c0000500303180340004803010b507101c0c20a80b100b90906022103030440b007a5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 604476546 1250 604475296 604475299
    0xf050306030a05102a09051c0b010e01180b031e1624080103020d0206031503060c031b07051504052b081609062106081b01171308160f050f0705 63
    0x24040c0410031400c02c4030b9030800044000100f40e00644541e1a80c3c09c40d1102a40107180ea036100c103004000c0b111803d05005040c07a580d880620040c2003100010340d8a056040303e00007113590070300300d0205400003000b00c4081d58541060b07101401c0d5a0710414a4050101400150340d0303580c90100348a424030071814103041c2c0354000e140250710341040d000c1c4019904010300c91505284032080d8015a96420403406101d110f60811980d84d0745044404040304a01c4ea06021040305800d00000b40040e401140b0301079090041500b6580341d0b41c13182001ca01d00401070f280b450106001100c0040411080e406004c090200c83e26a2425900c0740000c08201d4844403081900150307015a09201c028401e803003120503841000d0070740320a050342190440842d60280d001d00550740c007501c0c0380c0050713102800b000900e40fa02400c244c0c02c4a203130004590b074000f500a0940720710500c001c25803420451034500740c90b180c00000c0c0300c00320419228540510343c80d4611106403410310038412070512150000400300c007030302c60 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 604477796 1250 604476546 604476557
    0x60906110d0806060708120405010b0316030212160314152509090f0504140f0601090b060f041203090b04050a17010207050a050d0f0306060f050306030a05102a 70
    0x14502040b50800b4014020a03440070b401c00181c00072131003a07005081c1030110358013500e2440c14580340c1242150303540700030240241c0001c2c401401c1801900c0e0a40d00b22a0191250040d0103402c0c05000c0c100722480141100160642c0d201200b0b02c640b484c89059600129021a0003801c2804010300504004440401c403903040001100c407100d100c070202c01d50b040403d0a152040039142d030031400545406071100480f403581c0748100300034881028180103001240354050604609412001a2070f01c10502510f808180c503001d8120715034981508403040714140720585a151500c402c000c800081080005400182c088030010410401d001c0846089a6004022a51191500050f41c00d240c06001c4031000d555030a0044001041c0240a64000c82d0700c201c015110181d1801310151030740501d030402400f0103140000a11590307812541c0000c903401c40c0e0a00e55101da0320340300020315000f24000003e100c4c0c040e00c0b17020070b2054059000801026210007140740071006098003882c11843d444c0b0401c00088 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 604479046 1250 604477796 604477813
    0x1e120c0714121e190f140403030c050c0406080309150708041511030702030303061e12010c120225030908061009050a050906060906062206090611 64
    0x810100500003580314091003252941150101420482d11980241148000151480c0380f5a4208180041001c607085140c1c145002900090b401401c0c50740c2c01070611200da04044c050038010707801c080b503040100d0003540d500da40720328000f0302e6101c400303008541a219050001500f460300b070040c0c00503a41101c0042d81800340401c100401c070156805aa070801ca0100403c001040032030b0014030140c60361013526030211100390070007446070603003501e0031415400502000303005a03804000c991b00010200c810400d980c3c698820400800c0e040c1a1035a40700004200107410040d0640040c1683c07041030300c60000450310301c10014140e1060b411001c07081d000c400f160744041c03160070502c0ea01660003840c0c4414515140c5904d5490444162040150108000030400c100f800902a8030b6000440c024240b0280c203000020a958a0020f084284031340c8401000070072030b445d0041510101495004000481c41000c0c6607203940c1440c0e40a0040040d02008012503010302901d20340440c0c0c3d0500c402482c016 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 604480296 1250 604479046 604479061
    0x307121e02010c02150c04090608070501020c0a1a07060209100305040b0105150f160503040905040b0a0b0f150d090606030c060305040c150c02040603030e120706090324111e12 77
    0x5c400c001c10f010307031000042c040402c00c80d400e44240409402204c0050040341c1c20000060f140988001510307100d60840f83c0e00313001a001c0c20350701c1d03481031101e071890780d86030b03a514601400607000e4035401c0c0d500f001c16a0803c5c50030540c140c001d03a000c0c074001e0442c2c0305c4d40e07600c070000e00c24950840506511070030700410060311100307a524010510014510318000e8841c8455560500b150320960244440548030010302051000b403d44680d00a003076540f0400410031040701003013a00120a400300c2c420850440e80080f0380061600715a0042c0c00d07114200b01483e4079103441c40c010401808180c881040a030000310b5141c0c000d118483c060b03034014000c00710b403078a0050385404446022040d00e0404c2216840c0d0001602c83d8050714010714420340f00d070b00c00309800006012541820b030040030081d60018408014440d003010a01d0141c2c2d0700702d0300710704d00322800307008035108041404111400301d8541210800c6107442d07031703014103038a0400904c80303003001004810317441c864060035403607124041e0a040440d45c038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 604481546 1250 604480296 604480333
    0x50105041a1e061309110a0c0308060307270b040c080f1506070804080f1b060f09060d051609051f021c03050901230402120307121e02010c02 62
    0x200c00452110b10410800400b00d10315800030003d604018901000c18400704159001e20794841801c14400743c1001c4a40300300074101135443c03202405100d01100401d0301903c4c144640c0010306103200c45440805000c2c20701254000e41d150350154204d2403e403040c1c1039898140220581030a127039680700d500c1e4582c0401c069040b5805840309035850b082c0e00f81000c5540700c000c0601070240c058402241c6075440d02801c1070410075040d46682c03054010b10303885d0001c4c1c0034091040200c14002d6842070340710555080c0c000018850154100d602600101e000b40204285400852140402041c0e030b1940008440e17081c1c416080c1070041d00d9003d01e0074222120384901c81300c10421881000c0c03040700c00c3c59681079100e40480d2006094500000d80720010440c4440090142c044a5a104040c24080e500e00c5410511941c074090300c0284501c0301b4030700d00781a003201003041d00d0455402480440c07052410101c080e03c0a40c2c0e4034841074068844440701010140103209903902d040c41c03500031300b6075490441d03a1400ea = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 604482796 1250 604481546 604481569
    0x606031003050607180503061b0f0d09050a0501060e0115031e14070f02070b0d02070c050303120420220608012c0c06180d0206030c0d050105041a 64
    0x14086021500003000c00d4081200c2405000d094454914a004030161400054010313001b0301d00075486603050029002d001841d40b0400c40c41c00708020346907550761007130000600c1992500c0b42110305062140b0103111001c51401e51031441803000300f01840c1c4d44e1401c01450f400c24450244140650f400c0b0140c035601903000501c0d0114284c0104203440e04142c03180d4111113059400504120a0740e04000700030703030070004c1d0015001060004103480e07490170658071030031f03c6070040301481d003034010801da0100b1000242ea40c000d03100c02010f0340d845042c0c0c410142140703682203070180c41e0b84004400c130404d2001c00c0a90303040120805089901880c8480c0b41d481c14159601d4100d134807080d40c4410000749441c080c895031110042c4440203109010351300c442c02e6500303904912100541d070040003203940c4071703a05c100032121140105410000d0703a00200000818040c442000603400950010030011b041c03030041c0c01440100008142042580d0300c80c0b0520044410010141d4a91000251990314500c0c0c00d111114 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 604484046 1250 604482796 604482811
    0xa0b0a03110f130801020f0a031509110a02010b0f0a030f170a0e0f030c0307063006081c0f03180602040b070c09110d051e09030a02070815060603 64
    0x90041880c2100e5012640402c1100c0d020328408504140442040350b4410000e0503018025420059166034030300c401e00c14100c0b03000625079034112802c500c40c84280c01e00e005059906080200e00d0328505503410a0384421801c42c015441c1c0f0402410320b01d040300c1030f0f01c1448009071408138024190b03034503404100c5e5803400071703540308200400509448003458000e011908642da00d140070106120180b00146802c1200c1b0b9200340c0247c1c1b0204110348000600400b2510b4603e003140300c0f0100401a0091030320301070b0807003107001200da8541894072110741001d400c40300f20508032501c003070030511101050f2198030800000a200c000ea0500e20920076001118212511000f00396403455550311b402c100c4c1e02640c0030030a018400303d4110240145071461b0402085803400c14043d280c647e0800e00c165128030810504d01c01e59800100745043c0c1440032155403640c4200b01d00b079460070304204080e92500040701c1540184104c06010a100700c0c042180c0d4070002003211607010039261081048200e40000f045203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 604485296 1250 604484046 604484051
    0x12020702040c091509140108040807050a0c0f0506031b0c0c120c040608060705030f0a180317101212020312040b01031208072012040305070905150a0b0a03 68
    0x2200907a071140314050041c2400c0c0c40d24a55103207400701451403445000b110000780305070118100805400c9070208541c0d5002403a120707200755142e140100c014010410060500d10034000d60f042000b072050001070503280b034208407070b8046542e18100040c030b200864051954500c880703281c41560f2040c1020780300942c220415609440201c8010031168412201c0d000e045a104100790001810a4880c00700a0007120f00034040c0d40c03a101c0c0c1e016119100180641e0880e0700403200060407c3c9456009054080820b001c80013100c45d1810010208051011100c00355102d41d004107091009400a07841100c104d0096140c001c1c000352122008006100424003d5000c20010128035030700d90f0780c0c0350b84201e204034015901c950450800700c04505440d0b074002c0900007200f060180300c0d174000102102e10080b4200c1c150050b102803074118240850f035210044407400c0810701100b0004007244640507250348900800a55944012003421040f030000c4441e04000c01600c1840300f070400c5401820424004d0402 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 604486546 1250 604485296 604485307
    0x90519111903020405090a15120f020405010e041a1e040c080d0504230918100507020a1505071403102102041b080c0a030b04020307020f0d020f0d1202 66
    0x1202041d600603004180001d40c001418002c40c644401100d40050303d2030010807800400c401e901a9840540c000c01c0343c40700341c84148000700003000ca03040400d00c3d0301400c144a1569594901401440103840c12151212644404c005944072095a584141c0c00036044404418001416261405000d40309031440c990481c008503412004001700444036606540c0c05568504d080c18000703044201180d24114880d881201071159586c0d800c001e5044400340354402001c00002c540c2e40c1c6403c440354081d4903418180000c2110054011807185034007400750740d007041111805400001260390840302c80c0081142d90390342c03000b4a030014010b164081c61101030200466110f004441d000d030a07090206084404220002045051501035512045030714602c1d00d07449848624007804c0008018400e29041c140070801c0090240300340c20612401070094000c6540c0e0402c040025110205101074a0f428499800482e503502d10009503507201d08240e00c068045106001c0701111f0340902040c0021105400f0700c03a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 604487796 1250 604486546 604486567
    0x1407080301030b04050f070b0a050d0b0409060617030705060a180f0b160f0e120a0204050a020403020406050d030203091903052b0e060d020f120a1509051911 69
    0x40d4040c60256144080f280b6091401a1401341c00318074183c5603800040b0f003005800965410380b200c0b1403490801c00c1c0ca5003054800d040040081700c0020394403e0a201c0079500340034041e400141039840305a404403427080b0050760181d40b44942c1500414503480107001501b6800a075010301c1e1451140404441c101c1d03a1521441c1244002c1074040d95140000400c0c007560707205030000203803a40143d00b045841020704c0c2c08060300b88600c0301403030f6000ea002128180d609803010301054003a09e42c020720070021401c160301031800035081350008a01881c50048042568070f420303e651b008456250b80114030f403100f1141480720070000100c9404207403842480120000e40140a040b0702d000303d11890f1039080c9940b10020150488231020035052002c6a508400d091315040103c405003240b543d000360703907280f06002150061161441800c01006040244104803541d508500c200408034014a0100d5407940ca03500d0071100240c641d050385901000400401c0c81c620303085a42c81c0d1551f031040c00e0909182e1740 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 604489046 1250 604487796 604487813
    0x81201060207060305240d030302190809011109060706020d1b02030a031a0a0e04170307020709050106050a0504050f240c19121404090c121a101407 65
    0x80000c809a08000300c2404003d90520540361b0098203400121101c400b11181381070342010501070a401811416188030074103029804454510440d40880c0c030300d100c01e9400c01800303420305540300c9440754205148101c03144904000d0303441546000b0000f510305001d81e40c17550300a41c040200140c3d043e03101c5003101c044127100c41015411a44d550061503441034000381c020f0443d1b01c04941d2075040448a20f895465444c5c2901003401d841c0c0c00158103003203444d80d08169200700c203050070740064604000b0402c8012035000c01d4840451700495818085030340c0b100002d803402e01514101000194040c803081095140c41d1151070300413003001d8070800c0301c541e4880311486c10a0b00340e0b02c40b00d036031200043c0f41b25074584100078810044140114503030003011113584606041e81040906c0d006c010302ea540d02400c0c1c2e0881400c0398014038007500d003045072144520300588a9130601203505144ca2a003094070a0821041500c05604034000f07081504003c0485800c2d50f800316040c0c4444500482440100d00150825 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 604490296 1250 604489046 604489049
    0x120d02010e1011250206030c04031e0302060106050c0c030a12080702030408192f030c030a0206220f03061d0604030e09070e0909070e011208090f0114030a0605040c0207031509081201 80
    0x1031882e0f5542b41076042000300481c80a03a88040000d186070316801017a03011681e241500d03114030b081552807041e01c041e90300e4001180412a414010b140400e810030841444441c0b034110030742c543c2101030f500c000d420703a241d0141e4030860581d600400b108100c24005454403407815446848151400310720760510402094241d208a09100c103441c440f40454074040040410000045009000c908000d60200d00c00307020f2a0390710039440034204041c091880402200d1400352a21750800e004156a9040071000b0306020b104085c010b5000c0d010809450801040040c4a1070f01034540001d1255a071050000c1d40300010b00e03640c100500da4048071900da99503080c1f240039900b40c07030041c0400313403d211354103001181c1a4402c040c40280c0482c0c0900051084041c0e80960104466581507001c84030010386001c1010340003540340480000c100070410640f6404031007035803015182001007009611050307035203105500000d000d01c01c460151409121068024616071441204c030b20b0300703100e15629002c1d01c40d8020b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 604491546 1250 604490296 604490311
    0x50118031e170f2e0302061e0c371202010204050a03061a030d140c070312080403021c05120c07080c0303070806010c02060301090b120d02010e101125020603 69
    0x2030f01440f04a00c840e4520001485004070b180541681002c8904041d070b9452200900461010403903a840e180c241341e458981c0f80035a00d4680da914a0310704196140c0704030320500c8511010310341d21a8050302c0030030040380030a00c904860341c15560058a8201e8550f802e91110802c640d020440403460791079803040303e00214860705000c6449001400030012074580640880c2c02940040071035035110350300500403031091180c494500e94900c0e0315107200341810201e40000c1c042043c061060486d484e48010034510135400780d0709075008855200c0d51084040c120016201c00600240204001036282100ca03d80004400103000c1c5400748990307403044036410101c2042007503000401000400c2d030b00320b903199a0000c03091801c1800c0035620f5002a10a010600402e401c580d0ba0320f4105034143c9400841c0760b1015004412282805008580203002c0c01043c6403100707050140c0d400040e044800c2e401059070001d00c902400c0e0512003d1003081c200751002c88034801a02003466000c6000da2140c100a6015540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 604492796 1250 604491546 604491571
    0x5010e0d0306090b09041b0b0f040815060f040b030109230601120503070b07031e15080316060908120f010e090d1211070506010e0103050118031e17 65
    0x300d440682180c00c103502601d0081c1c242419204156211074501d580103a101c045842100740345444100d19071541d4001081d000380000e010440710141d0341c05801107890788401c603251084c0d50030000c40c071104207941854114440c2660740c1c05c189066000505a81c4020b400010944040c0e00c8590307200c041d4824507540004140b0500c1c80005050140c1800b602ca0720600b0b40090003107940b2166a4490b501c4c0c05001e2100301408150301500c40c0c4c100304252401d204056035440f040c03800707140080c00c0c00e099038480310801800010f9888400310a0390300c003590450702004102d04988504010b071000e8902151016420171219840c0e50400380a94001c031440303112810305604000e842e041c161030181003074505522200c29240c042e98440000011a5540100803900e200d0112258a80c0c0c091290001c0182c0102070011494000720300055041724005d400034000144161081391240d99100d4010300010801d00c260f2a406c3c80184518180b40d40385d10b0701885d200b0400009400d544410307aa9030b43c6204 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 604494046 1250 604492796 604492813
    0xc0c12030b03070b0d02310503060f060d081b0114060d0803060d030c080309060907060801032f0d0503070209150d06200703081b13090e0a0807030504032603040b06030a05010e 77
    0x80c26030f1f4010060700d0150000c111038100308030480b6610100421291041c09483e0060701004604810b5800c02c0440b5400101031344954001c47e07019144406560041723004440c00903032140703130540648110a80180d041031458a41c1801d0200030400c120303045e0705205180d0b4458000a82c0d00c0c005501c6803200030040c00ca581055030302e690030b02c54a5403001c0304111841c1c0040c000b00340d4141c29491a5081d040f800c102c1350032800740300d4801c0b1780c8592a0300d900030099100c090a11001200520500b4800c4902100540c0c6e40c43c180080304080241e801c0c0c000600c5a00c0f64001003440e4020300c2802d0f100111311010300d10016509034650711810045001850050034012607a10840401d400210304600050401240c0880320708490041e103d9120400e403120303407080340350307406000888403290000c0000c0e031345070680d0070b000d8641d910902c0100c0d407224501040c00a01002641101c1c648003510701c1c0207180d521992651138090802030600e540c18040d01005100044092141d02c00d00448000a4029076 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 604495296 1250 604494046 604494127
    0x63309150a0c0501060602070b0d0b010216290a020706050304030c06060b0a02370c1206050906180607050f0c1605030c010206091e030d0c0c12030b03070b0d02 70
    0x4620690010042d980301c03007000d003d400804c005a076020ac07182035001031040c0144004174501200102e490000c20704114000c2101c3d022145148000c0d00b10001c9100e900c05000b001184610071140380340010781209805003c014801d10045402c14000d29005881c0c2e41948c941e04c00300d42203540980c4501c0c4000035248003030f0b901840b0b0604a059586094960410f90250800c03088540f51004200d941c00720506100300700445260501400c038501059011000e1840c0090040c0f10070b90741e00e1014440d400001d514408282d0614641b0001d110107851035468024044d075058005510f00c05280c4018001001003810401080d09101c8031400743c20f07c61440d040071f1504005007140d070241190007031010010f00100c00588003107820401060680d41c20000c03441d03a410341c000c06140e5064507051940340c01207294881d5030020798078011800c000b001000c0000c240e04541d44c41746403e0300368121041c01c0040400c1074002d40144218410054500483c220001ca020006101e0320651354412070110502c7d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 604496402 1106 604495296 604495301
    0x20909120c030307080c040605180a1805070e0f031b012d020706030203160c02010e10090e0906011206020a090f0e063309150a0c0501 59
    0x22008511080c1d51a5401942d240d0b00098030030011442c0c44500c00112400c881c0320382c8402d8900101d05881d8012545007000391940f2030200e01d0000b800d4200d0030946021041c00f098000780e42c0c13900d18409010444101369190080e181184158610f0300c2c0040e6401c070700c1c10f074200726096519161004036106032081d200c00e00c500301d00c03500310201c200b22003052103824038058081da0403094940314101d040340021241c400e005424500b85d1804d0602503c03481c00307600d00600d000d80500103810007082d01d481c812019500080d69100c13040290107010313100c03903400004041c05071449501d004c401c800708150300d40000e0445a0300003a04410140168920300060001605000350b00e50782d498801d00d00802291514000c6002643d8004422080d0500c1d0f8818005e034015012107400d41d0181c40c20940107100300c1504841e000c1005801c3d02c2240000e400c00405a584007681c084071441c0050a = true := by decide +kernel

theorem cover : BRFrame.Cov 604316546 604496402 := by
  have h0 := BRFrame.cov_init 604316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 604316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 604316546 ≤ n) (h2 : n < 604496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
