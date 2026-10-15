-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4856
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:57:07.786042+00:00
-- url     : https://prove2.me/submissions/dbd1fd80-3375-430f-a8c4-132efafdadf7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 873201438 ≤ n < 873381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 873202688 1250 873201438 873201479
    0x111005041518050108280b040f0c020d020d02030703030225030906031a0618060c1c020c010c05031c020d06082d07170c0a030f020f03030f04090207020f0307 69
    0x1d0140716900e03030042d1741100c0180d800d8042c0e100a4035105e01400040d62407814402c10f4600040380c26074103440818210760741c0c0c52003548402e0310703280b1140189404010b9000e0840c03d5200a0140442642009440c0d0140d40c50007420150002001fa41c00741d02e01c04200350740040441000c035004418a000b401a0300d0178030809000c2030409400002c858207140c0055a802000760980e0b19114680244502c804000113140e0f40c070203401d1106000d40001040000a503e9034010500501c02e034800002e8944405003000504100c0c00c40419000150040151000b01081005509040304a850030302d01030701420f16183d610070f1500707200041e00c080008040650041d0102d42c0d581001000b441c1a4000804202e01450f69020610400000e03480811005200503070005170744440162400066030300a643d401a2040c00c0d000c8840b03010341ca00708012007030300d520840040d4a000c1c841748501d4014013a92140121555000c14150103640b100203030300406100082c266030f40b850300d03200010740c10120640c28 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 873203938 1250 873202688 873202727
    0x90e1005070207060e0f0a09090320010519050433060f031109070201020405180402031b011209030903020301022101090c021209061902030a1b1110050415 68
    0x2080005002042c16800d0f100c0170780d209400282d89205000000d45000c80c22908809181800900384c1000d200d0461894400ea481030001204e0800141c94401011740c004684d0b49040309115440e01d000251280a6415080c04551903842d400c000800305465000c14844003100d00c0c10512088040725100300c02a4480010000345d0307140c0304110f03420100717070000820000903e0300c440e009203080c42074640c2c840400d10002d45480e0f15000820400c00d19031340345e0310455440b41c043c0701c03c51601b44504820005031300c4e10700e203450240c038000a01100304425031022613640c8903446000d040c42809043c000d560091f00941d5610b0341012080441c03003503c0f01d407441c1500c0400003c41c0e4400207004030300d0750380503540c0102071222440c0c2c5000115800b01014980c00341007000795409001c00f5444560307050895801468a40791851030150018003ea041c06410740c4180224000050b522004c489030884103648294000480401c140c0d21440345410401440060100071040d440c0d020351440d00350381100a5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 873205188 1250 873203938 873203941
    0x5070509120a02091305031c060608160c060b010c02030a0804060318080d2c060105040c11070902030601020307050313030c050904031205060102031b010b1507050a031107090e1005 79
    0x11040d225030342c0328802076100c0300040205141c402c4d080854129107020748180c03441c150303c03845007464142035400d900085607102c000400241e500a08a107030300c6880e4558149130000b101c0d43c0203280c0095010010b15207565443c4d40c0b03580b40d00c11074101c648207a0140854055070001c0c00e14412540103840b603140024103100f0044d00c0115500350940e036855000d0000c0c0d00340341120f0742c0d510242c10041107010002c54811008403507014058a00300d1021a11406442194148024081580e414a0707800742401210000c0d8030300c0c050001201c4044640290005840b41c8810004074214031807034070050054480401e501c62403201c1c4541680440303128008a0316041d6079502402040c160489011f000301d0f45400d0b04150031140c40d0844da070702c1001481901c0c42d04402503001d41f0360080c40e004034056030f0b5494003404441d003081d105a203120013411200e581083c096035291135480000c44401010040800c00c0207101400410200002d01000038050103040501c4801585e182c0006801441c034904010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 873206438 1250 873205188 873205219
    0x6120605010c03020a03030506180a020307080c031b0d0605210c030c1c02011e020f0708030f04150c0c030b060f1f05070201120509030316053a05070509 67
    0x2030b4080b41545600a0040b8407007689080d8001e20009200e03542044292004141c461911009544200c088442c01070320303804c0194001b401c2d1f1348014804240c0501c10801d00407484120811a10950403281e907080e50f400c0c5051155002c4d050b941c3c4520b80080c04011090401001240daa8600b515100704881c0c025805908050751929694240b54001741300c4070841c039521448140c03e803403090041c10705010180000042c40307842180301d9003010041c2c200502065100ca4180003540090494000940c200401da0300b1411480c85107102e862144106011502c088270700031055004090303000414464550781d00c0c205480c0e40c08084402e103216980782d884403083d61610800103005401c116002c2c50145c00840801c3c1c806500a485c02d87c140450402034141d8151640a00d40c03046049101940d102d00b024000e400c4003100798002c540902509022114081d07015070a250202285804904544465101604403841603c00b456580790700300002c015070701c1c0d0000020070304981c0070307900092011700b40f2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 873207688 1250 873206438 873206447
    0xc0302180c0702040203130b0403030e010614210708030708030604142809080304120e120c01050d0905010e0c0109090c02061f1e05041515030903050c01060612060501 73
    0x2101c00300c01c50034007808880d000d414942c1c09103070710142c00051000460843d07299198408421a4200c000a448070b411114400007030084c0c0b00208548840d002e4028000341c0010310802003070322041d40030303880f40b40403640300c030010000c0000500408050300c0e941c00b00d07810000c00541c01110014040c505164803290b100810300121441044400b201c016010341080482c1e070b684140c540e0804000d80c41c3c4482c2c0010a0200b401180690b208845070a54040100009090000f460341c0d014820030541000a21445010412800030402480c02503511004031052100500114001030115031810000602c25980089c0b50104810241c0724071484943c0d49011005031240c0b03010b001d00580000d404601d4440c1011a0240c800c80d1051070303810390507100c40710083e1561101c041d500c0300905082d010030541c00c00d071088815009461104035805410300101c28901c40c2c00503945800c00d55140e50040038184904241e0316030081d4007001703002075a1f4400c4005c0c01e140d0010701103c5000cac0740000004056003c0e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 873208938 1250 873207688 873207691
    0x317030604060b070c1a03040f0b0718091406030a0b0a050702030f0c0102030603060a020c0304030b25260403201204151103210c120f1501032f13030c030218 69
    0x740c012741c219940c0d080560f07c05442c182c140205040c1c1420b80d00e142c07001c00030161074481c0c00002c10090321250000d4a07080079280900a030070165a0202007060380707820651004035010b0100751a20f8107403040740b861061451900d101c0601013449450200190001d502950f400c600b00d64050301e801c40488124824046000d101d540300704820030005544107555580040e01901c03c100c2c811403420f0500da00c0542000c0000050808004051403401d1044a00b0300726100c22448417032840c08c0d40d8054200f2000c000c03a82190181840300300c03000b203020084100c541000117125500c8559860510103072001070580000483d900031800411031400005440382045c2c07000318540034202c0540c01800c1c01d1005090040d0800c006c0094000c1da450520446c6d01030103182d10364800910305502c841030030403080240d050405060500c0c2940700a00c030760700192038001641110040e682c1d041c035008440e00c544202e1803032010b40200d0001c00c0c01600c0b200303541241d001b601c4c403201031080f154200e4500c000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 873210188 1250 873208938 873208943
    0x509090d050a0f030230280504020402070212070f080a0b1f090e07061e0207090f090f15142e0e0f1b040317030604060b070c1a0304 58
    0x40501090711600d10030706591540c0e43c0b050030018600402e901c15040780c0402e80d821040010204c89080300340c2084100d809901c41c0e12825400190300302e06d104010090714034604544070710740760404036041d035171075034119041258000c00800c08132440b81c448135160748141c4910b00040b080140b00003001c01d40803541c1542a94010024642070392503009031004c40d400c69111103010190401c0c00300d21080d003072080d02116040c1c3e500520703840346003a00003485001c05491008440e034a114030403000c544c00248010a640401740040f58032000e642d02ca40003003204c45801f5068000445522060240241840310b0340100c010090200402e00b02c4205441c240c242e81c031a070401c0d80e031005080942e02900c086a0a03070445020f80c242c86941d06010a140c9100b900c1c41c00b160903103c41400440c80064864580c3c00c0c103107042060405d4915191200b0a501c040c3c10200307004000400101140e507180e20140c060506a444640c42d280b00d81090a4808698012401081c4107030305024034580175441075900c640e6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 873211438 1250 873210188 873210197
    0x40b07320705100e09010603150f05010e0f270a0f0b0d080a02100525090503030f0f0906120a06060201151e09020f0a1d180c090301150509090d 63
    0x61a01d01407041102c0602c0c2c0403c20011100c4c031030b40d1580d03990302c0d0700341c000c02d0956000b041c180a600c1c84203400c00342c55031200580040ca001e0810269800021030030444e0700465101c071008084002050f01c84c10003032490800645884c0c4a84000801d2481690190032003000c00c00c0111400c0f400013007210401035030720380c1c0700600c951030a0020342404010184c0302850f1066032041410403991170150380090f60031220034150717202070000310310901000c81300302e044600e40203140c01d00d48030101c1d89031710543c81a510a98400103070303120054800c4007250f00341c840107041e00780e41e1440072034070903046c41b4203862500641342000400900984140a04000c0074801c10220311218030f0700c00e940640041910140909031608800082c0006440c0301030901200300e03500b030580d10803900000810b110f0111000c880d10501d80611035001d07460b2041a10000303580310408100d07a84542802c810180903c43c0096415801d1040d140484454245140120b4109855401560301c500c90020780b5010a4081e550005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 873212688 1250 873211438 873211453
    0x90b0c0403020a181401030c1d040c051002010e0616090806040305033d0611010e0316150609020405040f0207051b0a0b13150c11040f02040b0732 64
    0x203800c6180b1300ca44143e41d0354001401000081980340e542c1c4241c3c015980700256100c20088403d00d000780340084000c00c0c4100e002442c280c1d0751a44800240e025090003030a0020700040840d00075030151b00210400800c40e440c1c0d103031400022028405c00c074501e1000959000300001c0c0f0345030000c1c0c080c0c011a4541ca482d415a51621829a420010070308a541d40d25170306000c940c21400c0310a98070542c44140f00d1004141820850302428003030048403402c40701e80c5800c0440c00c0000c40841945c408400c89810301d1008056800d082e0481d1680c0d003d81c60b002458a0030004820003e0341c002c00c11190261070910010310001408812070080c07020181041d00300021446c4c0700520021250850040142042107540c2c0382e2071320910740d820126900c0d00c000202e410600c0304010f10990095462070924085a80014542e500c00e420f85d024903030240030715192414110b1050301d030f406660281220b0b4024030745650f200c0c00c20090300304440c02c01e405d82500d005900c48604031800307140c2508004100041540 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 873213938 1250 873212688 873212699
    0x1602030f0f0304030302040e0a0b040e03041415070804320102030a0e040e0d0e0906150a030f0b090a0212090c061c180c0e010b0a12200409090b0c0403020a 68
    0x142c0c4024011401c050f030070840400c50700554450780e130103804581c0001800a02c1801800121660050b0003445a841400104803104512503a112500350555001503404d5142c5403042c468015020014080c2c180407a0200f2000300300414110022400700d0082108035042007202d10f0f80e444285402d005810400c08405c480d4064407180e1a0000050400100c510410183c5414040049120740004007001d090030361514080f00c1150f04445d0131034a2814800e903100c20303500f071842859a10818103455a60450310280305600c054a0801d01905485a81c80c0002c0b903203000754440212000c54544600104a51610016484a014002030040761410301058501000d44091040000e48035890320551070144018911400304030b40710703200075a440f40c200058404600303416003101107415000d20140403420390005000c2022948504c1c0019010a51100e00300e803e0440380f0384000680000500080b05a07070390380b106411034061007400c22075494a4100700060300c40c910002c1d44c03010b0b296105100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 873215188 1250 873213938 873213967
    0x50a140c070314300a1407050d050c060a060e180a0501060e0906070c030c08030402011803030810080c131e050a0603060617210c0f061602030f 63
    0x28503003030a1046800e1142d4942d0303003e6480d5140110503619804c1142c1c900c00c600001844150300031410140110101081e519184980c01a407551a0030032031810341d114034803494074080300d0001e60040f0541e040300c410a41c019001c3c1d8005400e072001485264002000d2407400d215242c2512010041400a503c500c1c1c205d61082115810900082c0a405110400200240315000040805d000b281d055482e100900d10f040000081c440c0d0b0a01c11f075280c1000000341c0c00305910200b6a84102c1741900c0340c94500048a004245035002e4007d100119804810302d90400f8500d8454500b07014031242c8070341c0300c0310321680340c80a10040c1a0040765007003810000e6811500000e81c114000304a00a20810300c120311802c0d0380003620501d160695a090500502089018000c040c040340a11450804a408000e0f5070b0344900035230740da11401c0c4002e402e0001914a80840303425610301400c03a1042010020042d44681c81581c10500188650305038105950011041d15554080482e01d1400c10b18025140d22 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 873216438 1250 873215188 873215197
    0x70e01080405152e0f0e1b0322060905070f03030c02101403041a06091e060303040b0c07080c01140304140a24110c0a0602070602090405091c050a14 65
    0x900125001416403928001c0c482141c0d1202c09103c40000186000426960003034190046c9114483d00410800e900c008214200e9042804201160b526a240b603482c10a220603101c240644050b4071a803c0309004554210302216070007141a9030341d00390340b40208580008584001008200030f0050400903142881d07800b10b040303043e400c00c4c2030f43d00026524441d0300c0d80102d4007240d15181c014450300302602c3c0101207540c1b010040d1007580250038200c503601004500e040a55401e000b40400003a000c0d2401c1c0140c40003040010303090703902c0c5c2d0b50302c8503840e480d0000d0380036032000b610601c41a404c40350f101d140d010029030500d112661864031503490751401c041207044009810f00c0350304c0b1786500190102102030401060790000215140100d815102038421402c2c404810084c117008170034404001141511140d60701c031000581e204024074042c030180c000c81843c90b41c407510b40300c1000700301d0001048a80721a0f02c101c000e04824121302605840034042d51f014400014480c000c4522a280403030f0042 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 873217688 1250 873216438 873216451
    0x140109092c070905040b0403140a080a0905101a1203030402010f0c0c05100c0b0702010c1d03010f1a0102060f100e0705070f0309150201061206150f0e070e0108040515 73
    0xa4007110f85599a4400f55401602d01b10703840e00074002003009241d07100003140540350348158503514040e070f22100280001006484c1c1701c451380e65010310b030b81080410010580301c0c8036000c030140310300381001d82c1c80c19070f0b441c11481d01805420804010700c500b10021080382d100d0b55050f100c0754103060340c2c501d04079140c000c0301404540c440400c100200d00350755940d1441204521603030780d07000340310b02514000c06081c0f400b5000741c080d03a0400c0508642d8980002c6d1400340c1200025840501040302c00009002d8400e05400d904001d19044036402500d905c0343c3c0c0705107010701c00c2e0202d4180e501c503400050984d881c02c40347c94440087c0c15005014090035035000310382161781860301711704007030141d190b280c1c1c480b40b056022404504054000c2095214a541040010304940001c01420345001c100040507080c102c001010196100795882a10211021702406007281700316040b4100e40b5207004440c0328100b074a0480110b490301e20268100d40c45009414071076648200507102000810900048014018084 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 873218938 1250 873217688 873217693
    0x7050702030a08030108030901091401080c0a18030c0e100e0c03062b05010b010c030203030a0c1e020607120203060f21030c0a1202030309031204020f0a140109092c 72
    0x5210118443c1009036004e021818040c6958103982d4001401480c1c203035000c1300740c014141d030381511180c2e004200c403607001907401c0c485680e03544203040842c0c0030100031000e5801c8450664010003440358503015a400c2d2850040c0030403040d142c04001e1042040c0c00d10807034619413480c1000680811604025507004035015201d4240f6900f100c201c0301c0b94414076840a103c0b00b00061042c81882000d0003a00000d1100b800c002e100758442d900c00135120301c40100745000e401d071920300000286100340c2603180042000300c1842046854500000c2d264102903558900040c844541c0c0d03032a0a00c0b92080342d0090f2130041002050320191350030f114540080b00540c0b101006106811010704c0c20500080218007904809842060351515040c1198100703c0008011580f0034010450035100001c00c882c40a202c0d07510301c180325034551000841051a2442854025418050006d03007485240035820743c0d1030090b200c00890300d480b080c100b41200c45618504040f034040c80c2440620440012114003408100004d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 873220188 1250 873218938 873218953
    0x70503100b01021c081e0705091e030604030c12080c18030c091602190b1311030d2a080414060409090803090d050406020d050a0c05060c0301090b060702090705070203 73
    0x1460070701081e283c499040817921482c10042010b84080d0800000a06410012114103020000814500580b002140036021040a5a5240b50514500400b003540203044849a01e01403038010010101248216003d11640d04a5094503000385040e603c07a04050a00e40d0812001100340c40c200d4241c1421190940180c0002c0a1243c658810302d5204242c02c1036a1b41d003190746408020301d044803000060480801075400d0b1400103100b14801b54128840719408600c4250f181030091520307212140065140c441e0030501c0c10f0094204400c07243d0312040c01010911034a5610300d00d4411440c02c803004083e61000c02003070050391188801c0642180f4040c008a09050702d40c0c5052089500c20b030740568a150000c020081c10150801415561740080d01d415403c0030300d04500a5a05c030074404111040c01000700300c2100031803050051b00e8480b90000100c60244c101112030906680c401c0c0a0440010704084040e042410710a003120103e41e0b01610003900340d0386040b806c807526007000c9001c83c2d15009158 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 873221438 1250 873220188 873220213
    0x70906080628050115090608040c0e0712020c06071115040314070c090f180c0302011d03011811100813031e02060a0501210f11150705010e070503100b0102 68
    0x200f5203010740717003021980c1c41c0800c111501401010b0540d10440800c4080340402c400190004682806c4881140001140ea1180c1d8401c0c0da51120150428407410b1001c1a84140b070580000c0300d40c0204030949508100c00075107210151a5240c90300c0c03516628246c600490006845075465070720010540e04018184401541c901200c002164040a40580c60354101c641d0b526051081103523103a9004400035042d143c41d40c1e40340f0310b04010b110180c140b00c07041c941d5082248141587d00d103203640c014000c2020340341420100300701300d030410b20503508508480804809420081c0c5030b0382456481d40c030f07420a0741e0f079441c014240f031000b189011010031070b41c03000b8055002e5405034403050314085031b0054100b0b4a00100701a00b1554142d00c55043c0004954030b01c01d40028009031440f500b0380000071610036500c1d6041026036184000441d913006028010310008074030041e00a0420a4030940090190448405a81e0340d60910f60207440c1d410340141a4115000700b140d402100c542c101801034564808210 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 873222688 1250 873221438 873221441
    0xf0603070513020301090b040e0d1110050a1506031104260a0822050f0618090a0621020a060c2916080103120e18090f070906080628 58
    0x40d000e8480c3d0040010b00404c2014000c41550305400e903001c100040140c414241c1e40d50107040210140104d070080c02c00c03228814032034801d0a44c0c258006006030705006007000002c140c14044d035500c4a81e42070740424828030a0148400307400740030030081e080504210050800f0920b803400c1c05880c0b000035007000d2a401003480141c0f42d07940100702c645d48031043c0e00300300945031009200c03162090000320b600b07000395920607040300e04a1000b500c07000c1d241c00c445114412220300aa2031180c0c0059980108400c5503d00d070007541c1568510084010140d1511000381201c00040600a41c0005111014401c480c410402c409072075000341904200005c001168414071090100c264910b4603222040000d5032a85044a00c55582d452500030220340c51901c52070700110008020301c00300180f6803c0a101952000101002d80440c8814035074103061101103070795941403500e15000a4003886800207500c03a910304c9404115001d40001c5e00c000e03610350400d01c80c000429402102e03007070300b4080f6100d458280da = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 873223938 1250 873222688 873222709
    0x90c32041802090d03051207020705010504030605150310060821030105010c1712012d05100306080709020a090b0a0c0210032c070b090d1101030e0307151103040b0f06030705 76
    0x191b1591691101075440006403c08010400c5041d03510100e010841da90707109080358220303504080e00050b15200d03180034921324050035101c2641031107112820703111000030345e00c254119034400d0103c07055820050400a400d100c0240305d0368031040309000411286d4000c2006010b2070740b2812098010303039803041c4540c43c076400c81d01d01c18008115440050040345031000b0309100306000c2100280080f0000c11010206040c3c41c000c00e07000f903c01061810085001c2e070402070151174610256a0350a07143c02038640250007111f0303500b00007481c41e00c00207102a0213030300711070f103240b01c40e6500f2018a20039020700c41b40d030840384242001c15590f54030200c41c1505401c0000d0300030400390001818610760301101460084940c001814202081200c20715a6403038030140068690b021980b40031500b501d00040e80240b001c8002c0f2b410600002851904124000d000b00c22407141076001000305161403600d0281c54041110010503c8020402059002c81d0690440794400b200034220b40e00719865901003441c0611 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 873225188 1250 873223938 873223943
    0x1b01090b160206060603040203030d151203021c030b01020601121505070221180d26071727030c042309010b010522090c32041802090d 59
    0xa10304040c403440750b4188103540d0080e80c00c507401030440c2040c1d00020703101d03c40d0075030300100c06988512458001071502061f100500c0d09101810201e01c03507003400780d202d0004980d0940d000481000000505000340b241100c20310040e40108890380c20840c0002c03541c2020002507a07103521400d44200c1c04c1c19240540c92040c000d541c098181403e021003c0b4085480905458003003074401e0007641d0107404c02c040b541d64540d00482d100d007000c40a506243c07002c5203030300c1d001624050b4080e079031a503d0560390005200145c0301e0b001c4926407120000d5019000d0090300c0342030882c200411300c2443e8050000c9209030903644014181c80e62002501c0004084900c1c40c00c0107020200720140b840d0f0401c65210400e81d0000f04400288001c44490340003c0040c800c298441166610807000104a800542c0c464009055140d5041148504810307014200001c48503040303541380c0080020301081a00e945520712203582007070321241000d003007910001e1010b226411100d48642c1c00e002400702640c8565a400c0710a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 873226438 1250 873225188 873225211
    0x7021c0306030b0703141308190c050f010203090d030b0301020d062322150e010f0f06030e0a12140403060204050f01170f0a0603020d060f0c141b01090b 67
    0x515601c0c03ca2914800100854180361a207228080e1610368200300e150310103c0c41241062a000c4c500e4802c1450041000380e40014002901500400d90460300000401303018000b20b80c407903040342511509138403040351900d1054000c1c0a007110500d02a400030030411000078000740c1480b481035104400ca0344a68490711840701c01002003c00c0350600030700c0c01c80700d48081d500550800e10880c3d042603c56002900081c11036500c226002e000311902008402400600f01841d5095035107403050300300b50010340680d41c141ca5080c0e074001a507500038132520040b032040764050b1104000300d85644034144151802441400000c8604080c4000c9007002000514800c0a005895905007003c8c00010101244807034144030041d0303203882c0a20f08801c0d4081c0d00c504000e003001640d641d03c1c60420040c1149034402900310014000a40820046412658a00c807402100300500388070814126109040b081210720300003410442031003c2c8a1605c5682a01c0e01030303000124030070a0310b03a245580540219459070064 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 873227688 1250 873226438 873226451
    0x21201090e1504020d0201050909040f030807081e0403021608010608120306060706050406060321080f01060e04020f190c0308010803091518040c0e01180e0103080307021c03 76
    0x65164072501c445511500000d00b1401540c001c110041c08000c1c0002c0d01c40c2150b44484030440e88184129001c0b82405031a82049090038580300e800b811144404402144030040015174007482912010b11403070100030ba0802421444103c00300350310010300190110b00805504d401e100c1c4150131030900401c4511300000c0ca09186c115070301d0030705410a0031003070352503010800c4c4240750392210161a41c080d0882c00018a90321240341c42001400d050344018002d841c01188100e4515410b0403510242000e03840d0641240d690f011450007600e070074010300c4007041001c2015070b20b5080c158003600030a406844060701e030070350000e4041d0a000c1014840400540701c41d981808040d404172000d0700501c001c0d0015414040382400040c0702c03a03002108500340403004140303031500c0c2d00d036104809005540a041000603501410b401030488100140150104000c14140070703035040804c070b00800310390000040803150790075903803006c0840d81302400e950114800d0392001c10f0340c881401600104d0006a46000540 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 873228938 1250 873227688 873227699
    0xc07020f01120e010518160609051e0306190506090609010b0a03090b271203181c0801090c02061302010c022205040303050a05091e071a03090705030f0d030b01050409021201 76
    0x40c1f480105125104001d854400c01c503e40d0015204000e03101c0498050911001c04044d1041102078108401d031700d0b120b680140f0103c0303076903881a401c252205a1081c4003560310001072080112041d00c145400c5085400100034000e070305406094010392902e00403404124a446181281c001a1520410072000c12030491181f800e44e280311461048550241440c52201c03a070301c4400f8000101042510100c940c15030300240024890031043c05000410300e0f071044280080108a40000d01643c9030081c03030b146144a6180c0002040351107128441c40990b11014a94011122410612000c80e084201c0700c0111342115001c2c120181400007041700041c0500d81414000d00b076900240807071003140c3c541403d00090b030b14042010f8081c504e00015105114942c5400145030066951000c203a80c80c3c66006101203007004001103000c1c122400445a40035103e6040585454840ba40020380c0e80c801000315440901070381141c0303202c1c081410401c0c10180d5401450003682c0c005c507050f41d100c540d00c1005000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 873230188 1250 873228938 873228943
    0xe010c0206033111010c02011e0905030f0a420c080a090f14030f0d0204150207060815030a14060f010f0f060e0301090c06080f0c07020f01120e010518 66
    0x81030b14241c042d225401d201d131100942c00b80303410803450412030341107a00c50659002d18810404000300c220711030004c10944d80000c001c032000c2d01610b4402d0190608070804c0440000d0f900220540080701085242d0380c811a00d09101000d168520550490042580c002c5402c240301d101648200140440d000c0009a40208039280c0108030004032898030081402249802c901411510b50100803010300c0c600c2c02400e1842c50003214a07a001a0500040c2c441c1170b80440e402034003c40b00041c031490340200c0c0c140801c1e80c640966002c1c2e036000405a90018034411800300540d030307030840e02405540c0c14507419111407910000222039090107500a0b001e020204c680c8010345801001c0d4010405041820092054060b00680c4140e07030401418482c0701c0501c1d40c0170341c00040d485920542801c9082d41d24500034201400c06c0307482051120b170140004507055000380458002941c001c1555210702d891000544a4107064140481400c0da40c00102102c0310f400d01c6003e0180441800d044490f2200b84941031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 873231438 1250 873230188 873230251
    0x1050f040b011d01051c0501150602071a091009030602070305180406060212070201110703030207030c0902070203030f03070320030117161412070f05121c0e010c020603 74
    0x504400c1c0021401450310100c81ea0b1306692041380c445c11411011540102945801d24014145510700014a1003400040e100b6000700c8203d9000c0c0c40c180e50396503642c0819201900c10003030a8413020003a078505443c00400b000c00c40d82660030540075468494482800301d8201030f40440200d080000d81841c207001680c2c40301004801100d09108d1581800030003900e5a00c00c0ca442d084000001c1140d408581c020800c0781804040d250072195556940d050080d030305d00741d52005a9842c009001c0200c0e55420078000c0f42c010360707009402140f0b400400c4035140303450380c80203007800100b42d139030800c401407140b4030000c4010301044110600e4480d41444412041d40000b00f507002040c0d0302401c0303a905000555040380d001c907a9030f1380e80c205800383c0600209031514652003002c801405100c1012904950901240341918015244c6110351035448503425a110a00511201925909a095881b9a10070f0000303d4043c0c1d07040c03510300100360780c940c0454695001601c51a10103006c555010700c0c14040b0781600d8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 873232688 1250 873231438 873231449
    0x110702041a03100e15160314100b070c081e070504061d10051507061526191401050a05131e020d11010806060a02030d021b01050f040b01 60
    0x100304140640c000950710310010014010302038540c03403202c0f44c460781070200d4005da00958011000c281360604014480d400c1c60803032140400d2401503ea410b140505040510911050200e10803060808034905559040300d1402c40d4040410000403917050070602c10007032220f010140c1c00450400c44404903043c05101c2c0c006c50302031450201c04000c000401d05182e03100102e0b843c4141003680b18410643c001003801d400264108503000f0f201800c0410700801804079500956040100210014060952080c0e80c4900c1c2502c02141c85440d0810000c4c102c0d40900b01044001c813031402580b500e000708dc8800b40c2006454035201417a00710803c40c4280200b80c1c1c4424804230070440da142102c10300c1c41d045079650f8003401d041a04007030b000c1501004845905501e400900c41070304400c0c10b282903101ca4025600c0b0900203044100803d90364140038090ba50744a200707402860404c0d899100380380094020140c0c2000020440c0841d142c1400c0038400d2034014a00b401c4d03010b91514090618007034000f03060b07001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 873233938 1250 873232688 873232721
    0x50d031107290706111b070f05090406150503101515020312070e090a050411030109020f04180206030f01050306090307031d0409140d020f0c09070f110111070204 71
    0x480142c102e00700300315079a00202e02e05058461100b820000020f000e500c18014010b0b9002462141440d1104840d04032518000300b1280a284c40b46445110014a8031401382c0101c81440800d001403035030b8000c0106015100d400b60b12a81ea5a00005e03c7c0c1100042903010f0140c1c0c8465400000d8403152030354000c0e00d02c4003500c03020b03041407000c020764070b03c40c1d50207050030200340030041340050303100310700204090000030611034071410140411002001d042e2003ca6010701603442c906030030b0406000c0d41c001e03190010004503500010303c0501000d0500425406082d0340d2072404080183d4801000c1c42c024500c040803010320b58180000c1c10b10b41000500155110b0340b05005160002360b105840d0b582d050b41c03001443c000d80d44004046005414183ca0081010302d84102d8100701c10000503812265040726400c4602c00c00703904446c46d4884070b0560410341c001d0080c01c00280c51500403492102d0308896032601030201c01e0701c1c1c1e00150844d80e40c1001518009000221542585070502442c01c680b03038030880 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 873235188 1250 873233938 873233969
    0x608060108060403051b01020a1d010c0b0f0c0c011505010e01022b0509040914070b0423030c0310050105010801050603190902010e0409030801030204061a0a03090507050d031107 78
    0xa4950b55200204001c040020029070200001c610303440000a00045400079519a4030031040509071407120203a1031241e04225446280d250321542c40e130150a500030742070b0a0581c407005441d00381070358020006401010208090000981e092080c1800401980000945541400c0004050000c00c5441c50f04652120040e64001492101c1440300e850900e1012940900310202c2915640a0b2407404ca07485850500d06038140078903a01400c04a00c0c40d20700741c1d200307152600b0720541140550701581140d98107000035500700000640b080c00d60f61600a0454a20584e041c00080c5016048041c8142094070750300104103a5811100d81070151204960407411480c000d03000505001000d8400041c05403224203c5066900603a00c24210382c40192042c032400c001410007401000d02071104078059481c106001443d00240720a2400c010354810760145041c01c00d10048006d0200300405440314000c00500084941da00310a411165200761603906490341c104091a0801e4401e40c40b02c0c0c29008a01c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 873236438 1250 873235188 873235199
    0x9110405010e07050c01090b0108150a0606020c09040c09020f040e0a09200f0901141c03171e04230721050307060c050301170f062d010b0a0306080601 66
    0x100c1d842d030703c030003d0300d481519031014529103400741c800396002a1900c0c1d4000000f003808440400d881e11401d0300f2800c45006c544a00900000301c4500703200f1100103812030070301074541b07142c060603040d002801b520144109589500158041341d212000004c0c0361140040d081200115032030219034800202030041201e0401e50716002140510000011402402e00280e908155070705548904007890107050000c05686035041d456502000f0918988501c0304c4a031210700d500b00940402c0a0680d155540d5103861580d001e495101c9e50025061141d04c0c0e0304426095800b09460321402d01c294060212401c1350b000203030540129842c90001e0190710b41020a00f8800c58040d12050344480320000c41c000005905414298150702500030000d010b03a082141010046600c40040c40c16a060031a1007000d114940303a00319a50094080c1170b4020750001d03800203a038144081c80800940840c6080d2000e1961074110311200c40600340c000710080d54001c81c011120641c51b2082c3c1c400350001300000c04540d410725 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 873237688 1250 873236438 873236459
    0x70b0106050a050412050114190608030c0d1b060903030203040204061d010315020702040204030605010515040e0f060f0418060f0605010507021302070f030f03290112061203030911040501 82
    0x1e02940c446510005c580408101c0254411686a03669400441107820522611140c0a55207200c5010319400c02c58081807180c000b0040381c0003041894020030600c2502c603010b480c11044174102c8070001c42000c603214080f41c001d02403141410301c03030354005030340e4901031040100b03c46581e0400c01c18190b11481410b424540c105006040d00d8100c103038200e11003d00400700c4068454070030002d40203400407034000100840c03500550f0590700f04485c00d0240d50204001c000441c026441124450240360b40801d040c40306451002c1d0300094003810721000342c2c01400c081002d9038081e400c00c001d036408a4280009001051042507040700c68040e05114181c61f100c0020818058000003078402e0307aa17102e189007004010360480b60040c2e84036410100580c4542000b400071000c405202001c00d0038481042e54003100c00880c15000c4490101e0200c03980707a914011104c00483c6407410000c00e680d1035000c1510040c0c00d01756058a07100b41d030085403401d1103151010f050300250f071503907001d40e041900501000c01e01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 873238938 1250 873237688 873237697
    0xf06091c020d0c060f06080a170a1b030504260705041a0411041a121e0705090a080313030501200a12150e090105070806010f03151a070b0106050a05 65
    0x31403a12040285071804d0160003020121840190341d4541000040c043c1c502246610403070303004480c04105c568190307503800d4480c858400544001100b400e00c111020302c0c01c01004810a020340b905a0519840d030200f152498070780041242d4482c1ca0503070340f00350741c0400c0180d00c01503e4261020301c0b02001a00d821100382d2003840006110300d03107481c0070420079500681500c0046c04410944070320f85103119040502544905c200c5d08884505034002490f20461070040c0170b4104180d4820040c0c2c3d6144001101c0c10f81252014070382c480000c0c00b00299003841040500304041340d80c0d0103802854a589030050031248000386050251200c0403607050700d00c2c0810207956241d0354a0800b02080706540c82103400600c800c010030210440340311004207240661002c4680714155001c001c000c1c60711040c209079403900301100d5550018443c0c1100d2002d05100343c00460b088c400505440503890344548180c4102d078001030109200036804583c1034180419106800e0040c0010304000d458001e1011008005124 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 873240188 1250 873238938 873238963
    0x30b10090e07060f300b2805010807031d241506130314061e090a081809010b1e03131707120914042705010e0f06091c02 53
    0x2d4514120514018014252100961803110fa4824603440b172803001c01041c9445816020315000c001c0600f40d0b00035800c02000603081001c01201440c90304004580c9010020110000c25031039080304003070068040c5101c0c01e1646034002412501290004882000e80f8001008901048201c24008c084c26080144003d0038815100707681d40b5000c000c0d6441c130115040d4002440700040d9442500000404a0707074034050040540c000c5082c420380e4400c5401d044040d00c413030480c0d07005150350400060b110303030041c414142c0d44084c1c0512126000c0004d98800002d81c010050948001600860702103609034282d03050314603442d42821800d01d10406040564440f01c010444405078000a003000c00c541e06481c0340641c00700654003200d8420380020496903051044400800c82c0c0400b403405450306003c9e01e130b04056400500440081120340c181d070f80ca200000143d55039580c0c0e90621001c40d0003801055884050b0b04c0c005d08032410143c02c59854180c042c06021025158036200f5062550702140b5485181c8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 873241438 1250 873240188 873240197
    0x6050420090f1e041101031505011d0a0506160210020d0c08090d0b090307050c03010605060a200102070807030e0405130303150f15021501050a05060310030b10090e07060f 75
    0x42d1103c1801682035101841e406200410074204020030000404002d2040302c281d909015000100d12080b1407160a4018240030528103440c444044602c1030566440d240b00820007001a5610400701c1d001c3d5004003d414007a11002107180150300700702c0c900d40c90226403440107000aa0568900a121002c40d000091000600141c01a00caa840d410710b21840e0b90411145030b000d0030b00d481d07c00d43d25800300c041156076014620401a4620b418411502240d0028015619000e401c0d0300803100f00c040150200840f110036110b103258441c0034405807241e03501c580140c0c0c0d0b0b51300c01400d000e4855108010018800d600700403c11031b202103400020840c00341d00d4200410403400c40d20a001b90b003c11134020005005042e80e0006e06840c0300801d0b03c1c0303580303d26001e841b280115010b1030a0340306d4003401015049400d200c001c100a0502e0301c0115131041c00b100c0761000454036035441c0581b80c1c10580341c039500002c210380140720249a5100d88504102060000c00c012031508a02411440d00e005048043c003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 873242688 1250 873241438 873241441
    0x60910020307020402121509160c08040b04090603140a0c060e0d050d09061206450f0c170609100f0b04090509062203031806050420090f 60
    0x94000c10035203800300d600810640d1510389000c940b401e410401c81d03480700e02d4000700881c980c041c00c04810380c80c001c00c0420084c1030030b003c0c212420744404002e01011200030004000004411082501400c0641415080402c0451031030602c0c0d0030340c20248990341e180350450b84503000011840111281105d000781065101e8510440010704082100200903103d8001e02c0003e098181d402050034003501d8494403000403640c0076214100c1165500e00917503000841d03540c0065840c80001000007440c4207080644807009000343c141183d00b8009114404500342c490700029803207081030280200303109413403500e0342c05040c3c00000c00c00c5102e030242145000311815000714954140e4a5803d4014107886c018040889030b84100c90540b9511602c03480c040310b4600004203802e210b001c90094060014441d258003408840a070100c901c40e0120800c41c203269940001c01340640043c0c881206407030050700001200d02e07207400d19618102440003403022040d94121804c0555444204d0560030400c50040035605 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 873243938 1250 873242688 873242719
    0xc011b09060813080703020c12010e0705063004031d0f0d050106080706050706050f04030522051e033d0e0a05030a020c06160b1003060204060504140f0609 68
    0xc4034050381c0013916805002554400b8141c0005550003070b01800e4603030242a51039558454200c404420490000e500711500c10440c61510703001074160b024088000700c0041d8400b040c0c0c4210700c0e01c84014074900d41c0c2c2d00001c01c000c1c59000038003000e00c80716130f0500701c0b0100c030400001400304d01c4098903144105018403401b001c0c044258040009040e60008841e08162108005010360308020002c84145007018001511601c90440e440c2c05a50f1545940d81000ca080310040c05070909401b00c0c040107000c000d00010507a850f000f0082c0711492014441d003082c1d40c3c0340140b5040410250582c0c844041d14199252207008201c1c00002114200314161040c1d10214402005008401a0200688195204101881008001028401e0340c680803200c80f07007841404d0241078040c01c060003c00814107481c480100744910780303040d030040005c00075500540e140d6481608070f802c26044000010030108081c004c030340120349101e40828085585140325601c0100050182c802c0412640c091220031440c03040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 873245188 1250 873243938 873243961
    0x15031a0105060327010617210f0304030804060f151d2502030903010501060314070905030a080c0f07060206150f0a060c020112061508070804030e01080603030d050c0c011b090608 78
    0xb80100c41110f00d01f140c020203200c0d50b124500304503101c1561345051400c070301038002c034215100c01c18031300082800c6658640301a152030308020000c1c3d0794141c45000b08a9807010303030300c0703003c1c81e003070201314031488850070002400074800c001203422059030910340a00511601154140404c2004605840c0211404210490442c001c020f41640c06609100002c03400341d0301a00074003841c1d50581d082c00300c2e981e14980d040340c10340c0d00d900c55150076400c08540300011130021402080607c10b445d003210006107244071032500e0030143d81c0c09500141c01c034500b4007103003ea9882e07001e100036100701d480e20810801003000500d070f650b080c4103200034040c1303452401007103900580341041c6201c0450410088107a8401014040d4440c41d81908001000c03140002c03141070048050394000c90700740d44c0d803030710700c08020005458001010f00010351620080c0308268040005000e00c511803442c0b80e1a20362205240300001d03080d510707103201022988035829080018181d01541400c101e91300b03441d050900380c47e040000c48 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 873246438 1250 873245188 873245201
    0xa1403132a0902070201030e03250c0e151905030319020c0d050c01450801020d0f1107030c030e010504051807090b1801110115031a010506032701 64
    0x216180010009899200b42e030103801424000e880a0080035885101c060302c91180380740d00c1e402400d0100b181c0450b59210040ca102c0e05110b41c119031111761710780505402c5000100c0e0000c01d0b401485614001314200903500211045005031500042400e08000903124001c540b03030140d2141d00c0c0000c04040742c4c4204500015228080e102054403040c0d4101a03850f11414106603000c00c41c0c1d641c40803c006800032003140311a0000541d001c00076403100086480c039400d10403090210329449804120118203100620500d8002d01002407000c0b0105407400c262a94801c0d21120b100c2c0611482c00403d4002006011032a45440c06a00301c01c2d0314401600c19020300c0d00f086400107a400000704020b41d42100321400381d5400d07102c00345660b81c0ea48020380580300e108510101010301a111201d10750081981d4803151aa000010a95280100242021001a90003030f5941e0313003130108210716003000c018140d000d04015078001d4590310700003041c0c0101d606003280365801c1c00d84490000d03100035000e40c40314 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 873247688 1250 873246438 873246503
    0x106140609130c1101150605090112060902040f0305060c0c1230090f0105150607020d06050906040b070327020303070507060509010908030705120a0c05010c0201020a140313 76
    0x802c10f0085108008100b0580560300300455880c00a40c0d0032809900b01000048660641e02c092800c2d00c1c240044460310380702403451005648640000c50220070034000391002e05494040c056026155003002ca00d00840a030640e00500002c00c0319122000000c038000c1c12010041c1541541e5486000c4a980300a0001100104014680b100006480040c3c0606409a40b540c01252405010f0080e62422614160b48001400c0518204803540d030038903802615005000411101d0405400d880725002e841c0105c40041d060307045003040000b0007494074040b80c1c000680740340c200845819441d07101040c48803c2c200e42007950719610302d0740443d5020011124000d074410181c0e08000d80d1181c014009401c80e604940c0480d405900200300d0840000c1030320255174209000b040c460b0420310b1000b80540c0b1102a00080203403580000b00030940901a51070f1a60445d070005940d03940d0005c00034808184210a410900700410500400100c1c00740c400b410b054012032080e9404108400c0300e4828012840c42 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 873248938 1250 873247688 873247691
    0x310030f05031207020f0619140a0f0c0c0f062d0504020405090c030319180e010609141f02190b01050a08030a170702011d0105040c0503010614060913 66
    0x50420030084043c0c04290111100c015035501c1d004800c1c0d031102c00c45044a90280d0007c8001200903149480e0f800700d4800075070700020b015149512400d0000c00450b03600c01c02540300c2e6040c2e12041494030030b900d0340c0301042ca0040b2410a0ba581c075a00c842d0007009002d00410380705c2d121020070f1013840c80f0ba503880396000c00e40c402c0010f5010100070301402084034141d224030b10303120000ea510000424420b840d548010061481d00b09511f85040e80340e60803580c0c902c10071101605000c140035540042c440680440c0400350941c3d850010000c240160341d8005000303d040425400c3c0194984480d810908030032001c460b08401406a0101d1a00240b0003107a260310004031001424816a4950725040e900c040e18201c1d8440e88441d01e556036480784332400400161000300d1050303802c05c1583c50540107417a81c800441c6101005024143c1c20f00c2c851031591150b5561420310080000c482c51040091500381c009206407460200303110003280e485c4d5820350140d0b4000a50714065a15142c4c2072443c1c5406600 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 873250188 1250 873248938 873248963
    0x91c021e101d1c020a1506080307081e0703050913151706090309030312101e090c020a0803010b07020105120a0c0206100302090103171e0306181b031003 67
    0x2074404402282082410740c0307028542003000701d0030514010f681070400301e800402d050f02c0f4507036a00b03141c0940140c0406140d81c0c2d405000c07548010600083c00348a0140c462281c581c0d810300d540003d000100301000580990030003500000940102c19203840080454420a070780726800990b90103000c03c14101c4010000c25500442d0010510b084100105c0c1100d003218415a2510315050340c030302c40c00a40c181c0c194828001402034507036604c416544010044e05407a40c86e80d4414084c0d9210040040309100b40c403080c00140820780d03040c49920005010b030310051007540083c4d250320065210602400c000d1001c005002c0301964040c0c401c03034425104e2840002021314000c0c242c08005c080c80182e44005010300008601c50815803034070359003a0381c0c00408a40082e480c643e150010b4a00b8407846c940910300034010b41c543c03001589001da00582810042d07554a161071001c0000321311403812045410302c00e28040c012101c0c60520030441c008919500c642d83d9444814180071484501d80c0300508841681c02d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 873251438 1250 873250188 873250211
    0x507061805010e39030304033e0a030b090a15090b0c0705030301050603062b03020601170619090c180b060a0f120b030d08091c021e10 59
    0x40c0000b4003440702c0011388021000042001c203603141c2c80702d020360761444003010b440e480ca809002101c00315900101280d02d45903581d5510204100d42400900d141003a50210701e58105c2007021050042074207030a00b07210741c48a04000b916560881c00301400f039030030400004030038043c1082840315075a00000c001e40314003904220035011f017161030412507002c890785001c20100d00941d000e44d204580d004000c0c0d81141e0030314041c403505400040041742d00804200c00d9411040701d002240f180c0c0754406604918010403810040c2c176040c8103a2200d803400c96100d440d807180c404003148454101d2202c030f2291507502a0705c00000090054424043d1041c06101c8000500144607010701c142c910941e01c05001104100c42000801e028210310240171450041c00811b4403071154034181c011880c0703068000b80055594010a00c2c2000d41c1015074041101c0b4420b1001c04d03881000000d4031404d0450f883c00c8800342c030460081d12210218448401181d62034180d600e025024006000f44a001000804c644010b40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 873252688 1250 873251438 873251441
    0x5090a030e041e02031f030c030b15120c03010b0603090a0314070210020d0206090c090613060e0c090f04090c0611010e0d090302041b090506090d08030403021e011b050706180501 78
    0x1502d480c0d40781044206c10b20240a9102c22940840e0381000342e40d64958a181c440d0141d511008242121000d0081d40e428015074408541c11074000d140e03030082030b0181300401450f084a4a01090070b108503002d03c100102840000b440702d00403070b454500552102e02e00c41503003406000301c010095000110042c40303102a68001303181c80070140c40d07508071034040d1124440749031074503600c4030303056001380705c0200103503060805c1902d07000803401881d0300056403546c660781000b110209036042440340c0c10000740401103140108146500090860303003001080c820360340744a9400140d1140c0414014002c4d031070b494110003940071091401812044d03900000d01c1c184020990030690100300d10680c900500c0304009070140b0301040c0703040d04c5901e0300c610780740c104000c01102d90070010021764401c1c0304031031080c0020b407040003442c051440794005204c400e0200740302c4070450841500d9101d00368542480e440c9a001440c1d11040c101d82c0d24244107a1f1020340341840e0016080c143d89400401c42c81070310410800c07005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 873253938 1250 873252688 873252691
    0x1308030307023414011b0302030c010606031505220e0705010f0c12110f071202120a12080c0705160e0702010e07031515090204140405090a030e041e0203 67
    0x41580712207101442d5801d800400f142c1c884400711030b00107408180b00c000405110038214000506041c50468908124804114048402240160800302e22a1040c0409001c0e85015040600301400f5000090780c08a10540d024031079540308120440c944c0922080d08a046d0003401c0715100e081c05111990800250303504810b00c152030000d60444080c0d20400d20840d00e506090340d0002e618003807901d859804a07040c10711034810000502403240c3d0600700c9081007020000401c401d10354105014030a004001511740880ca05c04101d4010185200005c0d0f03540100701c80000440c289240145c41e1030f03c205129002d1362000800030f20421104444800d40d10761008121074603aa000c030065a40d4801c01c85c01e8a01d080502c40141d40021820704c001824215441c0c0c0040c0101f07000207040c0081000c03541080b00551084171f420354001400d101c0b101d0581018610100b00380c8060110741000c04d00240d5681c4032050103070810255200c81c0f20b041c0d9581d00810000302c03145800c40154a80754400340003d610 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 873255188 1250 873253938 873253963
    0x3080304050705060909072d030614040905060a0c1205190b0102210c0a2a1212030e01090c090b011107050105030403050c0309040207150f0b1302130803030702 70
    0x60b0340b00000c103032410034203c3c0d0706644003401d083d0a0752201e11050380c17810102c2000345c0c100302642844000410703051101030942d00c900d42c0c0c0402c58500c0c0014099001502d1364583c1c3c0901d040c64400c0c1d020031400141681c012000c0d24000401010385402124104102c41d2810100c0e400d120602c100c642c0740e55170b0a04005a1140e0804c07100b51050f006982c0c071b840c005141e07420f003524440c3c15222403251002500202504000b95034003581c0954809a07060b6500b0080304003400c400c0b81c003c1240e1801441140035218501d10f01d14400c405445081d00d12401119041c2010744801d21140c0485c000c0d044050f00c03591110741c1e61990303900c2d503c01030301504c0c200016a0010740900c407042d800c1ca0001401d68201c1c2c4040e103c3c0c91175515542c400f2515a803100c214102e103444100700380d10303d82c2ca0ba80700504000380510000e15942d9210061841540c80340051102040d09007101c90b070040d65523211744441081c030b00c44010390341e0071010942d10201d00705070f00c0b100c00c9000100030044140e40114440304480e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 873256438 1250 873255188 873255193
    0xa1403031e07080d051e01050a090c03090b0f0906010f080c0603040501021b1b041512050f07030b011701021315031401120b0603030a0e040c1e031406030c030a060f02070c0308030405 80
    0xa04511a86d820700100740308407584404d00c4c035003c0001d41001d500000c4d400565290104400c04c035900d0701c1d040705001f03550300b501298004040000004003400024007505400b2000c40901380741024940d511040d050116204140000110301000700075411909420407030801075544518070810152111800180c21003e5050110110f6040c540b520071f44c0c48100d6003290305045075080080130b8898002c00d03241160144a0307600010142c5c40108030780001180b085240c8007041d030521203000d240e1006049102860307070040c0036000b102c0d07056440500649025003080410007005e43c0049015003c44070304d60501c917003600004600b517041c1140d40c00c90f03580124078800b03403030b15048289656485000c0c0400001040141d2400d494501600082c601903242d00d0600d175140e42c03003038800c141c0304000ca0003c00840e54403200c09054085810301c0b1a40100700701c001d806c5a000000c040303a20381c05508001000c06030345103440c4561318015416102110b401040d4483c21540300c0c6840515a0300c1614160f070310340b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 873257688 1250 873256438 873256471
    0x40b040b150d06050901111204060c090b033102010f181710150e0112020a0905090a050c0108090d0c050f0304030c0303090504020301050d021311030903090a1403031e07080d05 77
    0x1c0303a94202311180ca03030008803114103654490703e80100402036000d80004005040300001400105080554020368404081c9240041c6e06085a40070030100e500d50b05070712580849a4000d41e820601d0901400b080c0d040800f0071408090801d045194aa00601628000f203840c1e02040607001070301c440300313111154040000c4045015005041d800c02d11854802110090050226001c000192042144058200d202040d1034010007400d0303403400c40c2c18a40356400341c140ca0090040070842441074620a00301031801d4185051f009489800c40d035440d50902070004050400c01c0f1081250340c0f541d007543d105685d1111303142e00d02030711018418442500003526541c0d0200d0703a40381c28401c8a0407544014404180d40c4056420b1000451b00107104c14a0659140318290b4003484480003148208101c0e00039541d59002541040000c02c80e54100102c044294600c0038030a8178004200c60b0f52034a08078400c1000e40314524000300030301c10303c0d03c002c00501022400003000c00359904020300440e0743d941d41900340b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 873258938 1250 873257688 873257711
    0x501030915020c0703052a2e0804022d1e040603110a0807181e06030c0819080a0503060a031401060306060503030a0e04110d090f020f09040b040b150d06050901 70
    0x190001c00c0c10b019200c2403480008819161050a050f4018900300320965200123000b02d1204803008840d5035404506454100011841e000054621540c5a001035002c410f1062030400703400361007029418000d03c3e10010384001a81d24901510003120000c1060190030748a181c01101c0389840031f5031130b000c0c1e07425003804559600302140c0801a01e0880300d921600181142d49500130706604016040c102540c010781c1444103400e4050039014500075490390510078a05076080b45400309000399650625246c03d10301002402d00821100c1110b40c900c0d041d904d0fa201d850002e8540401d580c401404644a110410b143c44c006401810480c0c4c080c0104100055652043c15281c1c8180d2004000049a21544800b24030b020ba10101c03a0204100743c19080100b200d0302a002c96440325029503601c3c948405600071440d14504d61015414142c3e654041424542d845d08200a0094070081101e1202c03400601c0c0020b4422a83e011010010480c02c03003808107040050060400b550690059400c0c10181c0e0030303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 873260188 1250 873258938 873258973
    0x7140106210308130c0e090a05070503010903020c09101503091a011206050a0f020703091e05010512060d080a1206080d09030b06040605210d0e06040501030915020c070305 75
    0x815010f85400a450740e60f03082010303036200101303011983c040d40200e02040740712424160030310401c107100040c8003070151030070014601045075001c0e034480d03030501c0503140c000b84d0b0200300a680d055080c3c4040889486007a200782c0f0300c454035080742c0088800c016910307003983c0c1c0c90782206038941e000700b0194081c01101c0180e00c0d01c0c2d21007401103181403d403406080b800901c0329440580d0003c8400c20025210800c03519440030f0768001c030400d030300142c40a0300c24084036001c0c075880841e00c0400030564003224540800a025801400c4600060980010019032280ca9113070b01000c41a0340800c0e5a940c500e010400908401d240c4980d081c6d10910308100883d50250010321064170000c582c0b58a003150b031440d81c0f174600b8594014002a0415100c20340024107480e02000082c0b90b41a020f480e04a40c800030681c14540040400351a040207011280d4001c0707031315001704890a980d030a19010445506504090003058210710000c0090b62002a25142d80030010400c0300030347e0f20039001d603002c10035000d0100b007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 873261438 1250 873260188 873260249
    0xc1b0106050f09090109140a200a0501050a0c060204170607080c18030114041a0a0b1f1b0b0601030e0307080d1515090e07020a0b0f0c07140106 63
    0xc0c1c000b4810707240203000d4940900e5030b50344000c0c070800108101c10380f542c0f08250742c59040020144d984c4030a0b610003c02040482d01e117144498000340302c00240c2e44000103542d03000e407441407074144140002c00000d100d10132103030704991541000701035517115950510340c031040394420312100f294043c1030301080300644201a56401108506601410149180550760401001110f903c2d40340d940d40504d0320308202010705040c030036402090292030034514445500807064008004017001460902c0c20305141d40e458000c003d403008101c601a000c00c40e1803074196042c41c510250703050382d911180c02d00d00402601503195880b80034207170307820700c14004869580c507034078011142c00402c03d140a000143c091407241c2c1c46400000a0315954501c140ea4072a4500350b0b02110345040c030300080000c80140103111001c0640e9810801c0351004003c02c1c1a140c98140b00280b0190607103517402c20110100344c080045200f42c07188603402014018400140e541000c0c002d003042d109048084034215181150f018103100d000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 873262688 1250 873261438 873261449
    0xa060e030c0909101d160f0621090c060914010507141f02071707051e1c0e1005130b030604110a0804020a090c020c0103020f070b0c1b0106 61
    0x1440c510041c242080340140008150318610701c01e00c00200c03002205400f500c40800105080580300d0200e51440605100020400720004101020204101e500c0c040030f034000c540c001d00d006c0c0304480c800c110304e030100e2203410b40b00b40c0c1403410480141d05115080514408903407050b01c914581c16610200300c200b1101d05c040b89400b08001703110501c0800c100350b2501c00700341550307005d56a590702400e48580d001c507244080c050340c40f40d000c56800104080002c840d43c865070030805290600301107684d100e81d078945035005c04400f40040e0448400b281c20800612002c90350820602c000582070362401000111044406480f40d124665a210413901070000c842011400002801c28581007102c088501d90000c1c10003600f1a5560ba08889412001d0002d4802c0e0401c40da80d603900d0307041600405c00b01c1d60194000310880307480d18203203100d1182c000444184014082c01c0241e00c9414803070f54610680543c00003e826402450204003403041e500300148584d240100c5500303407803214070000c80d0803148240100c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 873263938 1250 873262688 873262693
    0x1140106020a020105181c0c0603060312030c0309140f0105060f010504030209040f060f0203161806030c0e040207050c030d0e03060a1d1005060f040b090609060d0615050a060e03 78
    0x201809544a40000c01075400e8041e01140e505030100003040054165141f803298202c91400040d040040040061009002504d41813005500355160f41d412600e0031070b000d4051590320240010080d001e50444008950840341d41c201403109024655140c90b141c6601500301e503e44800142e030342c40c0c448120203401206941d05401c141c2182e0078081010750250064030000607200c2c83d180000c076a4020480c020030100700168480c2007920404951052162182047c03090004010300c64114018440303084036001d01d800306003012144420b40c0c0c542c40d0740800e41e4010740000b07000014004005128040a207080c2e003103503030b400801707082107800d036034641c02450703254000101084515480790001172030105211301941d02820205580c030b260225800d011400c5a8885d000c100c507031300c0d18400070841000240c2d810310001d5460f03030000d680c260008102601c901c0000020801a44909504c0108154040010090703181c186544400c8241d0780d01c03403d40b0800000c100851928458099000e0a0001900 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 873265188 1250 873263938 873263953
    0xd0f0e010b01031503110603190c020102070b07020a03140313020301050a060812030108070e0613020a030c03060f050604030b0a150311030d050f0316052205040f050c1903020d050114030114010602 86
    0x20030803180c1c40508200038111840c80c00c9e1464100c20303c00c80203000595000182c0e948a103182454042500400801c00c1d9040403880d0700102c3e81000d41e410506105500c019500d54809004690324841000065055860802000030843d8140c0c400415605c0c540c04a8022040640e8501c0423031000340220100c58115120030020351001d030303c00c0b9030031080040480c80350340369003940381003280c100769240300000307458116502c541d5070544900e0000c2c0074003410b01c0000c00c2c00c02021545500c80c81c4402007110410200080b0340700340c50381c4804d0b1100300f8980c800c001140c3c0d80c20901600100c06408034800d0080c1201042490b002d04c0c100d540b070801c0780801303600310383d50611010701300b00a001040e014801c0801c00014440c040000000600b0f00c440b0702105054281b90600c070407103180710488501c191602c003d00040442c0380c015680140101800c40f01d2071782040300102c2c040d0042c0e40100c6882c600f003034008222503015070040c0d910502c0540003045207001e4001b200c007180500384550b8015030481c1e003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 873266438 1250 873265188 873265223
    0xf010f050c192103181b0902040f0905061801060c03120e21120c0a090504020d0209120a030912020d0c0803033304020d0f0e010b01031503 61
    0x40034000d10100407050381c81c85090095074000380e84200c0d82c101c82450304606001e0051280121031038102109150805c8a0700003418a180e451103c5c0001170046a46c607116000701c0c2c0c40744004030014000f032000941d1a1541d80050754003c16860040600b05402c0c94001001420b00c400da040c0c110444085403005a40782c06801d589402d942402601041461041040344501d0350042c90307034040c0800002c00c01448201c0003040200000410751060107810800040c140f01c81800c0d840d041800c11045075901d03503405805450020240d84407e82050001c03419a0483d041e0750b000c1c0660741001e42e00c005186900d0340d1025150101914010081840c00384148090030703d1294141d407851002d84205075030007150f241c0c40d0101a4076031080b48039500000030044d403040c10400804074941a203882e40c0c074590280031102c10700700400000a00881d400300702844028204c2e0054900c4e4401e6007020444440b400310b94a0180c2035030108180400d080800064040a400d000403044a40181003107034040c0402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 873267688 1250 873266438 873266447
    0x30402061c020706051501032d0b01110a1b0b19030b030a0c24090602100c090314060109051305030d0b06041502031216081819061a0f010f 61
    0x210003050015500f4482400020340502c00c00b405102c03040017001c848034184000400396a01d51074140050f01102d000c01040c1925200c5c0da000e280010781001c1000050303140101c8901c1d01f0700740040064441c1c0c4c0e081500b0f000028011214020346d0000b00b00026841e000c0c901c1c0a44103e048441c1206010342148000b10f10941c0400300c501c60080c00c0e540811400c0d2220f40111015401c0106840718280b10b000501d002a1100d000703212103818070b00c803c01e152480181d142c420262100c000141c49811741c041582c4100b821002965100801200150100b0583d5546e00700034065a10528a02000304541c1840d114214103101d0703100006510302488005000d001d4816441a16080351040c000420800749203604441d41a40310b5004680f101d0900e040c00a09000207004007400310380d00d020b075a0190768008445076200d00a4600e9540085107102c100e1f250000400c52500300c4150100c4040c200403140c1c1092050b07402c080d0040914007040360030030583e055540312680c00b01d8203001c05204c405004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 873268938 1250 873267688 873267727
    0x60709080316150f0e0c15071202100906021b0708030f22171b09070c050a0c090204090614010f0804240c121103010b130b0703022103040206 62
    0x41000c501e22002088261060341c2c414115208100d465460765030200170104403081c0f80b09000c070b4181c8055081c46070f818800348200f40740500700190038102007076400d00070404000c4a0302615410400010300e42414030003034100c07074200140718032100141600340f840000d9810556200e40c01452030320340e0300f114517984c9a100502032500d40712200c5846904600740f24130034009000003000c00c0241000310125904140303441010b03c003900b8402454000c03546814925951090b80e900b044480881d250410519200720800004d25405951001003420300054001e0f0048482ca0b1009000c03042d180e5180d18503d02c10284018001010000c0c00001c0340d01c51100190802e01841d03218116850b041501c2d0b4030703a80d049106142164542040c0c042d41039008104540d001901041008810a1000403030210b00c018407070281403890104565018a150b0b283c0c180040442c0741c6440d94600036841c0181d12114282880c0a454110503800300c0c8a14450007102d2003a80d0092540303142c8100d2a0100d4540c0e404d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 873270188 1250 873268938 873268943
    0x20c060a1b0f03020d090b07050a030f031503030e010909020f0d05071106340c02041a040618061d0c070c08190203012d0b0f0d0f0302060709080316 65
    0x1100c00c05000803540c068054405940643d005d80032081401c0809420842c3d80d501103d14050104240d8000c03076008110a0344003507151900c05a100d40c0424204c001e4100340903210311108020000004264000b158101c40c0f44082e29800d018554071a299002c9004100600b443c103113042001a104418a50080f40e00200c5400c181c0040044c3c51002031a240048130a042e2218810b00881c1c0c0d4515681188040907400b002580b01e03904000c100100a0100c0b00c00083c000c40d11000c1443c4c42c45044413068418003009081088415a00d01040d014640c0c440c200882c210300c2c1420204000c00c0c01d11048215055001c910b940382d4968070014001d542c05040c0a83d610b083d184004512150103000c010300d00034003408000d6211030180101030840f00c0180c00c402c48085010402a550098810b0151480f03a81d1200021049081030205800b4001c1d26081307a8403400c10700034007013002a1400854480c900130b03800c4541c0380d91b030504140c4403484680107016a0307a1003801241920150024001441031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 873271438 1250 873270188 873270227
    0x603030f07020d1a090f010612030e0907050d092003010203090a080306180c1e0c0a080912030f03070210050415051b0d020c06090304120b04030c0b04120e01020c060a 73
    0xc03d612020b20b26813a05541d01c00751a0026800b06100b80d00900400c03014002d4609014602200c0e5075010301700a0380000024000c0904c8000580180d000c0c03400d68003005000c2c2403d110752070ba2460300e503102d04c0510f01c81e40c840501806142089080c14070980340314800c80740040181500b00d4580d81c484c1e4000914a96003c800054219100c2103075454050250403904140b64889940000c03146003d00e00044510f0020340500900c202444001511342c44540c0080146503645804000320300124800d5000903200d00c030005903549483c1c3e0541c010341c401c0e500d5a0a644580381d0000c55102a102c040d05d01510a00d50b8001c18401c3d40ba40d680003e4101c04491654002c40ca0a07a03084525034004000c0161071a038007050b8009642001e000c0d4580c04100c5c0c0e4051450a42001c0b03038900115640710000e084480781e01c0001c1c0402d401800206106070304001a0102e915180c58004a0a40110b00203000540e0500341c2034120350000859455515004080d01d0601442da00200d8080d44100900700c00744c0d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 873272688 1250 873271438 873271463
    0x2071d010842041124070813030b0123030d050c032101060f14030c07150f0209040605041a100c1b170a05070506031b0c010902090603030f07020d 64
    0x203800c84041c2410002c0d01e544444051903c0c0c10700300b22544003504000c0c0145c10501500100254540400550081003070b030741500c40c80c25041c00b2049003d10554090b800203491008001c1c441e180d550613040302c0d48040c400701641d041130070760f943c011203a0880940641c000000c0010160088020b4a0722016a00032241803a0f000042c56004420441682c018840d220005211712940102085800c84083c00d004645207406c1c3c0211007a40710007800c4441600300810081d04009019140308504980307424240054854805504025800783d100d8030b100e18584000007410b41401d00401541103204881101c0302c00180c4140a20400c02c25410810002d48000c9000081c6080c000044198548039240c40304038100340c42c6506103481c00c0030981041c0d201a100c1c0c000110300040744415140191106500c0303885040304400000141c2a0640083d2000700c3c10748801c030070540c050418035000300c40f40e55040e1a110305040d140d02c186200c12040d14000c0105401504000e168408010304c601c3c46098103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 873273938 1250 873272688 873272773
    0x120d0e0a080906072a14010201020c0604080706060b0c0c040c0c050c0103050405010209042d060b040b130f0306020c070b0319052505040f081507082502071d0108 71
    0x141701e0483c04660148040003d021220007002c0799120340b00301703000843c5032420031602d050782c3d14402032000740881300000b00c50003005050780081008104a070b40c86610b401c140a04103071640001a43c190040b0b1600c91211300c500d2061000c003282503000006418600d4241c030045016003c002c0090b0350564080103a284c940e11140301d0750508250703401d0840c82c890081071080140a03c200781c0720b803a50f400d103c02401040042c1044030120b800306860a69a03010303007442d090400c0c4041e4480400c505001c00c5c004203001941e0000c203056080e00d0143e810103078580300d01c00c00d1400142c800c0c4581d050341001112100c4010b40c090350704003074950390001c4012400f6042c00724004d002480c0400103100441c0c100900c83c458660310016050a002811041c1a91038030000440b60040c080410000b00401080c100c503140300c0d1050940003154407140f00318a0142000e540c03004940300301094440300f51148881d00c3e5100c04542d040ea44070314058400c0c05200c00241c05403940c48500118002040e1141c001c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 873275188 1250 873273938 873273983
    0x3070801061808033c1603031b1e03060602061602010912052203020609040b19091a0306010f1703040b0d0c09050405090d110c03120d0e0a08090607 65
    0xd0f07011005e90b55511410900441032207102201d90086400f140000e0101030258110300340c0f800e001d001d40c0c0e0707410381d62824142200038144006a002c082940da00c81008613550001e03400254125400c1c1400450b0768602007141110140e208ac40010b070002d00c0410802c01094070b0848140c1c000c2c2c0300200d02e4151350b44440c240d41e1a00c81c41c460101e100011800030501d80c09001480c442c02c0c104490070380c1d0345941c000c40c202d440349540c1644520b0399005600e00c50f550310301c054031003002103006282d07400d078413600f09000501082400d41360344041d81540200c0d510300003a55a040c1c03087c1c0c84403816100d2500504040090030100c11006134001400080382c10b00703031007007d40040141d44e4800700e80c2c050107480290102c2515001035000d01e0500c0104908400c000481c0f91444100785401c0b28140d81c0b010714981010b0008403641d5040c020100c0d1240080d840d800074010a0194040c10025410380800055036030840d40310090042c50305100010040c9450130140190b5405400840b142c032461618088 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 873276438 1250 873275188 873275197
    0x60206072c150715060303141303020910031a04140703021c0812090102090109051c1506090c0e180402130513020a1706060103150302061e070b16050307080106180803 73
    0x104c40d03a03583c80b042090592001d4982820310340b00d0300c42850140107807500d41c0040914040a4021083d1307102091031502009400d200458202203001c3c03071030032520303425101d00d1801c1c0e0301541c0b111b2a491382007526032004901201201d1b03004000e0f55441248084030814500c0c0d03c8010745e400b00040c05049040072010301141e00c0340ba550b2000503a0f038801c880c0050040b203c641c0000380650025851054100c884148410780c03c1c2d000000541002ca0a41002d00135061039000041002e003014860004680c2101030303c0784085003200c0030809501071003425500d10a0807100030350322403e00c100c6e00307440da0b103154000381c0c01450039414048102c4c0c9039000700e10103400c10b52001140c049060003080c01b0390402e211140e003101e000d11742408500401418640c68100740c2c04060300c0f60307030001042007500c40079044108556001d0640c65890f40c1603814101c458000440f80418070b5122170200034038040c46141228410000d98485000c00c4e4200320301192440718425420305007190040c00810351150070005070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 873277688 1250 873276438 873276473
    0xc0a0c020114040302280602060c0f090301060801020d09060f201b0601060c1202060c0f0a020102071704031a06010c29010305030a031116260301060206072c1507 71
    0x40d030681c3c0703035103001244d500c6d6194000000c64108109014a058040d0f00f16600c00e03d11b80c1c11580c48008800000c1c0c0141025444074101d50710008485c100c116a03900442d4040340039001c01c000b041c40c4048001c0540305024204003285540c0c00a03000042c0010380a0320440310f5116148261035640e213045032a02000f0781080e000f0485c40a400002c11500103110050394500d03102030401402c1c40d14610030710340980d43c88941414000b040b4903802030710035415900b00e182c00c041c2600c40300c000443c02c1002d0754402c4c04185c0709641344c558500003c0300e4041d550340c090030041c1c1d113140d00d0a100da2074032400040b901c0c4e13255020300c1c001c070401e0400d001d0a00c5805e001e90300410141d503a0340c007070020107002c4a00072407011a00510501800034100020909201c105400018003070741100b065410340500d5400c00701d081c00c142c90210000c580c040d40010074900c901c10340d803a40c50a2058280000000e5200b0000e05c650b9082c1c5040c0407003550800b07091850300d82625084890411420b507491240040040d5800c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 873278938 1250 873277688 873277729
    0x5090f030d320f07141b0d05030118021317060106090807030c170f0d051206040b0d030c020111100b0906040203070801060309050709180b0c0a0c020114040302 70
    0xc046285211410079071114010303402c455081d1201c1c00c00b22608607401003a01c5941c4000c800000c19980c000d950b00f01c1c54840581d445a903400e4100d400c41c01001c9002d04400040c030074421031110250194045030f041c1c40c1c8010703900c0e80d60007460344e800b0061b40c01220340280c0e88014031000161451821401035060600318050951581070400040c11204261301441d00c5a004120800100d08104044002d032100c10000c840030511005600f03203000c081e45180e621510400d002c0f070300402c3c0d000c0c016114050161401c0c243c651030301020002560a01c030a82540055411f121000003401807148603c0c8601c1818140f851044048025092a10401005881640701d0892030103c3c90000c1303403241d0000c4100c41c11400e509001100525403a414010801410ba8480e600301c02d100040144800620b6007e00902ca82088500c9200300c4601da80c000301c4440030b511004c110280740100659000c003499036200545580d00d0340044032220500b242e42601c55004000204c0541c40d10210880044100c406 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 873280188 1250 873278938 873278951
    0x6020706150b090910180f1104060207090609150b0a021e010618090c03020111101b0e0d0201051e070501090c031a01080d0503072106180203010503030a0305090f030d 73
    0x4c0c03000c0100e004000c0200d41211880500c0002c030038640a040f103409074100021400c40e681c1c091030003000031804181804801040002e0400e038000390034003e4640210f810b00601c0d598003440c1c400e84040506c0b5925014007c1014840c07541ca24024109000261048070000305444980003050840301d101141d050b511a00103001c1ca03919000e011300700004100082110b600203403200f14a10841e8000241004907501047c88002c2c003c00100d80140881e0500700450180c9001c038003400b540888807038012808804c003110040c0760258580d041da50301a1282032505059118848486071741e842c051841030811300c11800840e42c03d200b10002c4910860ba600d080c142142402028841c1003214007090110b5000148030011000c60000319009141c1442d81d10703a01c0e0130b40281c3e0795801da040d02d2074030300c03080c0407851510040d290404c0007142d031520703100310480c0c1c0100051810b03440240100d5030180d001308a10740b00c80b44203500a55005404006a9280146104400d4290741c480d05010051588952 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 873281438 1250 873280188 873280207
    0x2070803041716180b030705130504080403051f050106230f1c14060a0f0b03040f02031c0806010302070c051311030705040504060e0403020c040f061e091104050d06020706150b 77
    0x2140b403103417000c110b005040032480c0c038001403042c140c10380100401d10380312000304042060110948010310350110540e80780201d00d120392441880c403c00058001c0d81840e000145850051484070604d85620395010b0311a8120581c101c643d41c00303111141c40300b080c108080b0781c0c8801042c110b4410700300c140700085400815480f281c6076114024112921800b103200003000b02c241000050710403100c001c8840340c0c580c1d41c0c9040010140403680000780d01801500042d404e5207810f5202448000d1a52312541140e0b04c50800440c120300030540c0c01040440000c109210b18944800c8603040c8020010010030400d0a000040d12960070540300170001c03a201040c10300c403600c2d150143c3c1000e098040d403080610314094a00a68507044251114000d40ea04e00c0c01501009098011001905130a000490400488020204da060301c5e0302c2041025403611194034101c010001c01c5404440004010400311303070150f2200c90096101c9441121200e80d80c000300c402101d070b0707520070700002c1025191840c1c9480c0d022 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 873282688 1250 873281438 873281441
    0x1e0708120c070608190b060d0e010209011403090a020904140a03120c0e06030f060a0506040b040501020114060f2806110c09160311040302030303040f030f0207080304171618 76
    0x2500400705212040f0700b00318140c260800301405d42d90746880c01082d050514001725245102d10b0f480504041d08001e840042c001054004140c1c0c0300c0c084ea01c0440c17841d00503150003410b000a441c1e1342000c1e080041c0140252030300404072600540200c0307810501d890f03c13074022403034a2003440c421000b0402e428696801007089100b403401c904880c0c10a091943c00400c0015203601c40180040b444511a0b40810074546610642c00c000c0e1001611081e41c0325250409012142c0003071140500640c01c2584808040e602039450038081d00007c4c044218442c5c40ca800c00404030940910981e080940031404450b0742c00030000a0000c106580322020000070401005003488c00308440348d80124840000c1c003001c201d03205243c5011440c2c034a0002036201148180400303510465201941c1484044140000d0010b04020640490311a48030081310460b50721050b80c0b200304900c5a40c0c4990428802003108000b5902180100b040407002d0307070f8050b480100500c0c1c2c4400c00e5000441521340a016211316070885 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 873283938 1250 873282688 873282703
    0xe070510020703030f0503091218100201050a0b0619030e0307120c1106130b090613030804090b09090a0f06060909030e03010e01060f26030711090a06081e0708120c 72
    0x5c1e203441841c5150131100d4680e10b008840180032050000500481d0000c40c03080108101c420082002070101c682c800028060300040c0c034203801d1a490a60814902d02d0000304860000c50030103502d1110751002c00b02a00108041c0d21041c0040c001002410000b0f00c00703505005000c2625259901c0d01070b0241072100400290301c280b1401400100581c83c0646101c0b05200111056426019903441d00342d80070496500958071000354554120201104108540c005032060710741020301002000038042c01c1208010040c1d43c901e0303168002011440100c0c490405140f11180501c1001c10703204d55804550301114024003080c1c0005100a6040c1d51501d02801049080c0040d20020301c41c80d410504604d01200c003070f21842202c01d1a0640720a60750840c0860700c0e44031a5150152038640140703040140e460441d03003450a03c14210040041c0d21040c00340b2030034064070414001445c50164096100001c14211034216074544034052001540c0d41003004030b200020074880070140c071561031029403440c0004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 873285188 1250 873283938 873283967
    0x30b090c1e0301021204050d1b1e050f0102040b04080d030603080a03090606180b0306090615130e01020f07060f0c05030106052a010b01090e040206070b0703150b070201020c010f050d0e07051002070303 88
    0x1407420424007103445189039031500302c070a41e1038049449070340c5481c07441c1400030341d0501c9037035002203800a1100080302c003510444080000f0f4409a540303500f4104e003210303180c2c00002c2002e0401d1144c200b510344280c1c0280311980c8124000118140c5540d0401e02c500c01a55440442c00e41300e852109940c18240407903500131202d640209014101890100d641d608204034582c0100068400855550466001403d81d15a000000c40d654011056000d9299111030010b0790b41600780281c0406071b09442c89600e2421459960b02811a402c0600031034a80d07020184c5042401c1600754444080d002156088400966503000010800c080c2c100240c5540601da00c001c5401500c4000c02000da16a8021140e0faa039001014102598641c2c5042c0c005202d5820251400800300202040c0800068003e01400303000341c00303c4085005c014011106400f801c1080c100042c410b0100420032100c640000c09031110000940c0d00090702ca0f00495410100002c8500043c0c0c401d1000300207040d0060450f08080310b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 873286438 1250 873285188 873285227
    0xb0f0913091e020f040f05040c0e01230102030909012601180f21020a03031415040b010311070b060a0b18010503100803030907030b090c1e0301021204050d 68
    0x441d80340d014020000494442c10142031040080c00c66a40e40414150104004c00802901402c00907201c0240021942101d015101e000d0200f03030600714a5440e41240d40e000d54a49482c104c0b2404a9051500c8541d018154802400500e6050351108960741c0a0460107540e044c482549200c01070f1030101085081200d41d1414169050794141127030054245500b110511000c03019a26081000b00303401892400107282d4203115840b02c6501080100c8100c0c083e55040c4007120154190010054064521500a05000a482e665800c2c40d40203c00c18031814100001d04400390160940d8550100d00101d036215964001c2000902d419240c0328040e1940d062010300300340101c54140d00d1040c038080010705110b40840056400c41c419844800a801e5200030740c1d441c0d0030502060f07580c401040c001100c5012400c400622003910028501480180c018640b2000e5a507007803807510103024030340d08190555002c03c040f054540800000902551042000380085108804028100492480703d010720340d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 873287688 1250 873286438 873286451
    0xf03030304060b0a092003070e0303070b15011d101215080f060402130203090319050703170c07060218090403050d05060603010302150c0106150f0e1023040b0f0913 72
    0x405c0d481824a000c51b40503001d5076032038481050555807841254440c59140c0700015880042001054006000389190f0305202444040c4600640b004107122814032014421901c01011b40e1410b042314032445040c608141c1d14040d603070703030b0328500b9100946608a00f443d000d030400c0254000c10490380140f544604081c07c09800d040d80020981c1e01c40c00c019090198000c00801c665140038412076080482c030341440d448444e450200a001078011010580101c2c0035406100381c81000840303114413135940d03a0943c41c9030030795030b6845200030b41000110070f0f03400340304901160550701d800e100701c1d000781c0c006d89855495103162003001c0f00781c800080c01c65015800520040006864602c841d80c0707a10b146010054035114441400f500600c00c9a0200c541c1d0340e0541d80315440503400c030001450031215955051102e0308290309100b01c02c0901400e01001500380c10310084401041c10004403503800401c4c03c00c0c50190780d525040c00c290440d40071400c8140000900410720b2400d82034503259005012800d0000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 873288938 1250 873287688 873287711
    0xf05030c0c0f0604060807050c010204050603040c06081e0a09060b100c21080106120212180705010206010e071824110f0a06020a0509130b040b060c1b0f03030304060b0a09 75
    0x9071440a0301f002c0502a012803c1100c1207003c0d01038501070113020b00042d45900c0c01d41003012031b0044a100d6640401d000b40f0115030380c110340140002e4126881740b208038294945800c220028501c280080d079200740d440110070810b42d601c146040e101c2c0d1495a81c4114030142c0d00f0030b0070043c5000712030b0340000007584003d5041c46800200341c504440700c0303041030702d510814585444d001e44a80b0700300c0700400b141030007004542c5c0300700003070341c0507401190b030446440741e4a0380c1c01aa5604402c1c0104c510901c514000617903100d1103400c2945455920841c0040d0150381c07040c0d00403040d10008900c80c0101e044080c500e0303250340e002c044c0384001001d16008003840c001d01c5100c0364950396000c101071f129940001d00d000c0c0f4217004a04580b05000d010300b450790310083c4402880700800e400014188298204441c81c0001d14103601901d150900c0b19020344800704041e46415106d098140a00360428a48134403030f041541c09002562007227005104c04106008803104200c491015500800b80c142d1401e242010b4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 873290188 1250 873288938 873288947
    0xe06270603390a08060a0501140d02090a0f06050901030f0203060601080c070201120209060406020f070b2502030a02091305071e0b090607050a050a051002180603040f05030c0c0f060406 81
    0x444041e002c1c00600301d500000c00305050a5040d0000d0b9120710030706003440346008081e80f245040380e401c4105403181032409020090301c3d5a07010700180d80b01030314401181804980d940044c0240003030303000c005609039483e0003240c1600426402035640c808002d15030f006504041c001580d01c58402d00e01903042c1e20342498003001c0c40c081d041c4080d0400c0b034010752220042c42c80e0303411151020b000130442a191640d905000b507803041201e6000100f4060300d000010840b512600750b4130407880000c140c001d180e06000c20980340002e80c850aa07418860a10003001584419031103502404032003917084034240c0c0720306010340380c2440c9511041c1c225117084801a0769064044601056650303072172200390340d285124002800c60042c854040c04a0048a0020080140006891121034032650585900310501000d220803401580384030034a5620b400b031000303000d00d001d20055601a100e410204c56101e21501e42528642191031403079115402940c0300038032480c10b07000043e07a04c0801c50381540707071a080060003403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 873291438 1250 873290188 873290263
    0x90e09010209210a0b1006091403030a050706020f03011410020d081317030702011410210813030809040e0613020405070912110f040c08010e06270603 66
    0x40700510540c489080f10824003907190f00315040b200d00c08240c280855003094092061150314003203a502c0b90001400d011070120000304406c0240914200b641d4000240e5060340401c40807558603500f00000440c8100d024081c1d4040c00002c6960301100010340c052000742e00034040030005550010100c40300180e44000000d03840010407520301901c10140c070b01203401240c25054136140b9030700442040381490781540605101c907040a403041150b110303502c5d4201c03042418001c030b110780c1c0d8000d03aa00342d281b0708d8074030b06c0800700344074071740c12860041c40103c1e001420003150011241c031030000500c3c581d5441c00f0700942168840c6080a0042402c14091341c00c0d040443c00c000074000e640b58000108118000c0300040b005094208410040b0326141c540700c28216504800540306d0344140c1e9000c1d00d14100f620a81e10301e081191a14542a401c00c1c40510020344018180e40e13020032003000d18003601c209094240542404070114010a0812100305800c025501c00110406030078040d034a01111100aa0305 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 873292688 1250 873291438 873291469
    0xf08041227031b12030c031d030303090a06060617060d02060c030f0d060608130627050f12032802070b01061d010305090d03020c0703050706090e09010209 68
    0x100014500380c8148040c08003007095075021036151040001441095440701c0e840e4011400e8402c80540c8070202810980c0691101030300056041c1d8104000078040c060380ba005c0007205010300f4850303615000180c80c1d0f5004030340c1060950004d240000400101d8012040a0007181c18044401e0201d41000c0542003801003696100b84001101c40e001d5444200860b45540c4c15503003525510304c0200000081e070b42c0403140c4440743c58540040000d11a100306100c90242d2015181070b08682b803c1d80381c80c0c002d880580102c41400a64a0401182000f41200404d08a00c260083c24170448941421800c0c84076406008600250404c2003107032800100b075046100b0b88407200b8010355034800c06d0241c030003402001801420703000c00b800049001c0c0d0300442d2000c100300000c5c050710007210f4500e004506440f400e5440e40a46c3d030104800b811540e00940140140c00c078080201e07806242e9a844040c40c00005034071540c0442c1d5140c00502149802d0104507500c0303517000000b945401d80803c045807101007682c2c1d02c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 873293938 1250 873292688 873292697
    0x10030209180c1306051903021b07090e07080607050a0c0c0906090204090c0c030207050f13050c03191404080d150b03070f09032a09020a030c0f080412 66
    0x881a180c1d5440c88030184407429a00710301e001e18100c91038400e56030060250200b00d881000c07000500d070b0f215000b19220804070040283c0074011191080c2c010b500000500b1382c01c50b503042e00301144180100607240c0141210400400c003031542a19043c100040c90f004040141c0024040180c4207411400310340b1010124901811140024100f8686542507a0030400c1114145100020030740420b401400c1941d80c40c00d070801801c1d040700d01c103460700a0306c00002405030308262020040703864007104403202084054a103458081d0b40710000c008544041380c0c5081c0e42c40c004014031009a46044042c00240300101e020411118180c600d0701100d4002080103000140000e42c55840d46a103401550704202c8041e00b070201962140f041303c0a0750021503503100001c80b12511075291a00c9441c1280c201c9810103001b03121005100d44c5400c012181800c42066640c48100001c2d60000a200503c0c43c03a6403039130001408004602c0c000e1007503000d100360b0420000040144800f00360a940c1141310b01c19641171 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 873295188 1250 873293938 873293947
    0x50306060a031b0f0312030b03030307080a05130f06020409050609100306020d1d0601090b0105130e0601030b030a060c02070e0421121a0f041b030504081e071b05100302 74
    0x80440f202c59541d0080044c20010f481d001040142900f5150302d18940380d2010300600c00000241643c0780405c81d454030002e0404804100110003543c0095046039607180c02031768075051170302d50040001c0084012180f15a0004040161070744a100f1603410000c101d542d90494140783c1072406c403011381c40c0005030003aa40080d0181c0761a4a07075025012400046420190042801528544803203003442000c035100c2c1010001d21196200300c00301c0b44817440d0a10304220f801e00301b00c211061400c009050724145540c40b21140b00c070341e82c1000340070381e072a03c14907010a038040790ba0380081c1080810303800544040003800c240030018410204040c3e501540d00c1b46590024091601112016a000901e01c0020b14000140488040c0a0342003c40a04107883e41e003140545e0b181808104d03000307031480c00340c100c10300b9501061741c42c841c2d0000d9400c6405441d02070704015068021114801111030110f1100c07a0006000c0200414500007107400781942c1c0c0f8610707140d0704d4039020808619454011b40e0401d80c0c0000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 873296438 1250 873295188 873295223
    0x1210090c08190b1f020d1107060305090c0a15090e04030c02040504021809070905060618060a050405090a0504060f0e1b150a030b13020f07060b0f0405090115050306060a03 75
    0x10300003d0316400080144031a0071480326200520424021a28018000d8880700c803901d40c0188410303107100320b02c0001040400e207040300c1140205400b80044016000d0961401d205a07109078418000e810550f0040d0501c41da850f40240c250302c184d5209042a260036410007002c41d410079400d00c6c4841e0140e501107103582d11480002c1001e84c0030103900c0001d110000c18012084030001e4007400f0345022090800c12030302d40c0f100704115405a155403007070b81d11010841c40c80b58100040a8100d610317081c107001c1e0400da2a940041c0788a4411500f120070307240e90b1820481404020b0084011445888108004200b11072070100e803940800340c07000510405000400b031b81030f2913807400100e520043c5c91090341c035a028804020043c0c410040c584d8891051454001044111442100e00500241170401d240005503643c44004c1c02850302c14550002c20031000c01e0480d2514081e107031051054500018883e5442c07110f000385aa169000302d0300903800002003080d50b860740d40001c1305481d0001c480c202c110b10a075 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 873297688 1250 873296438 873296441
    0x9030b041401053c0c0f070f1a180606010f02160305160509071e030b03030a022a0a09051812040f23130f021210090c0819 54
    0x801c0d0994141d86840108818641084010703041c4620b02c03018a80d1030020311091211050400c64080600070841010540340d801c0c0308001c02030006102401d50a01380261076050090203406400d4034034504d50300a0340080325603500e0316070f403200124505444506514481c0b9a40c1e17040100b0b0b045c180710002500d044034500801000c61008120542480d88688038585540c03114000704141d01180d0700e01101044510741580c0d0305100c1d0300349a41d108500c04c0103610500082603200b40d9103061650310707140c0700c105072001e00c028500780c400f40e001045e04403080804000c43c580080c181101c48158001840410380c1d825050108440300c0da28041260b4960920948140400d03a041020b984585240000c520f00070a010304102e49044a408001c20307500c1105100c14407150310700003500310030280d814091f0b03d840050f0140510f113803d40050030444110510f0700303d0388805203ea07003040c0310104006102500e0340c0c2d2030025014036070701442901c00342417000c0c206800180004001d0b03c2e14aca02c4110241d050b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 873298938 1250 873297688 873297713
    0x309040902130e031801080601020303150118141f02030d0b040204050604180b0301050106090e0702120f04031e02010f050c0a12052206080106051b030c0f190309030b04 74
    0x200b002c0181c00f0600d8082e955a9014200202c0303041800002401e0355070140c248280321700b8040e00554070310354407158401e84110100c00d25905108030403050022051045070b2140c06410590b00e444904d02500e01000003040c0703010f0903c0c20002c140c0424143d4140e0201c01d076450b5841c6a040030601140d9040014081e00032500155000000030a00140c220045400f8207001c405400c030400008110106146c02d03a20240611404600c40c0d074401c0100700c0030b64468660100c0305105444081007000f158501646c400d25107032000500c046011b00070b218207098a110780e25046040850f0207141e60740080c041050070ba076480300b8400c003c50070030807828040c03094150b02680a514441080417a8001801e1038100a250696010303522084002e21400707440078109403409600c44040c1603280c100125441e501c130003074154844440b0003102c40d0b80b800c20001360080981c10009000b0280c581c50840e45040c0079011540e1040c100b000d003a001003034102c071402054a41001040030190b681341482e4284000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 873300188 1250 873298938 873298969
    0x3030f0a0e040c0804030906090518190501060f020d0c260f0a020303040606080318100c0203011401090e06070c080721081501020d200c06030a09110a080309040902 72
    0x10507004583c0c0303070b910401c80362107035219131103900b03c03161124002c440e0345c00d41d8010660010380918071030541c00f019445140e403044100005036402d003481150b20080d00d5080c1c2c80b64010078402407560128540621500d005010b8501e85000c48030201c3d2035040b0340341900400307540c11800900c10341c944c2d107800108481d142040460010b80c0e5a1241200960f40ccc0e004850682d1440d251640218501c2d402100712003418000940404c4010506020484a4819003001c0411b00015000c20401600d083c09802d0760580c03600d040c83d1080d1f141401c42002d4586c2c18190300f01e140c112100b00034403150458900351900b0f411540087c0c8540091401a24102d05203071291103000c03004990214090f0303c5101a48102c180c20b900b46010800e01005903501d0181c007005401144030100300141d0208003182c010006814041180d80301098070011131070661054401c250201d445000300000d11840c10383d505001d51003958020301680c9406100740d00c0c2e000e03007140540b02d5519403158809564502d10319510040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 873301438 1250 873300188 873300191
    0x1303020f03160e060f060f030703110d06031514060123040b03090c1f120b030a0803091c090608040605090c03010f0b0a3302070308030403030c020114010503030f0a0e04 74
    0x5407100303540b100b1503c040300d4840c45942011070060403800d11905403020045140b0f400750035902e8142c810750140007145080348800d071040c041e04101040700d0041900660003901000990428403c41c0c405a030700c520313054003120304501c0500015913400500302c101750010548074203800c1c00c907450701c0c61705105a51210400d680f0210910121020218207076020003000c66141c1540d50f565803c3c030040050500c07500c000b207080c039070f040180108950401920000e008060f2294030140755601603927a00151110402640003c80c07485c0c0c0210312604040c408562803c09901051820740010482d0800820003004103032903002041c42c0c07981c00c1010140140f4010003e2000621078854680144007460074280308071120389000903d0080428040d00c0714071290079108801c0c004544400e1b60300c6000001c07400718440d002001000c10f2803d806180070354444e5a011908401c007200007425074101101000259212400400c05a9400800c480712400c400029648a40c0500001d459202d074040041d074006 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 873302688 1250 873301438 873301483
    0x312200a0308090624100309080a031e0501080604030f0e0306010e07091a071b0b03190b062b060807090e280201030504020f1f02010f021303020f03 65
    0x10340120160f84545003000840e50265a202170441c11098040020401a00302001e203004078208400e0004210800d8100400d0100a41e07480c00d0480d0301900742040003a0b55070700c0c100352200713018038105030200c44428107000c00d504062540b6100c46010f4002014056010001004240a4602d10fa200340c0b000b020307524a0740e918410051116001ca41c424009002e001011511400c410310749084c0c0b68411882e58140462070340c0d41c0e4040080100110b2101c54410000584141c51100842c444c01400c2000448400b40188070000e4072404400184500c0c0c041c446611141c2100c00d003141c0d03400e4400c41d0140000c1c000c401210041c11a50030600c20340c041c000b80410240301980100501001000882d00500003080b13511540303000e8410841c1d42d01000ca00705001642c0710350466904035000501d40008028010700041080700d0b007400f110781c0c00c0310500c40c2042003a02841090f40034140e0754402c0d460482d104081d4105c407085800000d2240c502080814807a4801b08900814090000d0181c43d11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 873303938 1250 873302688 873302693
    0x7060609140702010c091406030603010923010b0a1404050a0e07080109050f0604050607030c090f120501050106020d05090d141501030c0b0405010801150e06130f0b03010312200a 78
    0x20024100c4016000d13600705400c020200344030f202c07140e01311410300300103200892000040000561001d0b000d560701d592039520840120340481c0020702045501a1007099100c50480d42030f00355a05500811f210304034503a420015000710600181e45140b04540024056440308111002050000300c1d41009100f641030214a00005500000081e0b010b80200d5075000c0a6403495039540c001242c00400345c0c3c01100c04150352600a07040340010f54214104884555103490b82c042c1c01c0502079100380061014011b101d030070300c00c0070f1040c035000d03000d94400750003c002e02810107407940c81000200780c043d802070714844003405180350804610508801c1030311808203001501d000c0c1030400703000503550784518600000c0d000742100d08441c104d0701306031a20442c2d0781c6044803c10540800d628444244000b008640001740d9990340100070b041c210011130342c680d44c2812200c494501841d041400b0600040005202140c00b2a0f036103da00d25981c50314030230480d00402e1203d40c0c24000c18140c02c00f0310618040e8001c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 873305188 1250 873303938 873303971
    0x2407201b01030506150a12060302030d05031f0b1818011d0c0c191b0807091529041703090f040524011413050f010906120207060609 58
    0x154800907a000d0080d0b40310344d003c000c520320213480c28070140e10042004005441c000c41240c640b0702d10384c040008225590b600828180742c00640041e0010703000100b08180c01c001c00d03040d100400ca280402c007480c2d42c1854034200c400d00c50040b006500f00c9030b0140008003079030307a0300c00501c3c1180c100300d81c9440b030b580d01d1481d40300502109511403c2480c0403c00500e40c5e00710f050641d507030414800020400d1110282c09410141a085011303200382021080e45100c401e854000400106a17220042000a1628041d0800c403881c04404c10a01c0c9180c010800c5000c00f60041a604400801420b00760410f51402d0b11a5600c00d590106821f03e08000710f4807203403840800901818031080d02c0516544801c8402c00003111011110350407400c241074001211108000b42800e0a10740605094000c0e0f5110380d8580b199400c14000000c201c0d4484509108904107800307202019003082c00c1a404240c20800040e0070300003414009246a58040365840502c00d854100340020b0120102c00c01102406030503020 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 873306438 1250 873305188 873305233
    0x103111e0d022b0c2a060b030604031107080703020d0b091608030a0905060406050d0b04061220010507030c0b06060904060e0402030105100b09041d010213030302240720 74
    0x503640c604a404201c0601401c000ea245100c4280c100b800c018815000001000d20040c003039a94694501c0c410413148c50130000103004500a03142c04142c5814151480d15003c2150440320b0190480c0c1000c0005803241d100582e0141d90010311650b17250b135030400da1881d00220390001810512068000128490044010640074010b5600c00914540303450034050144168070418000410800004c4180c050350b40c001d18081000070400b1820aa039030501c0081c620f41c1c40015243d0310360040f4006034201382001d144400100c20b00b012801c01d8001d44014254040f40c0d080070308040080c80026501c3d5072500225403981d200100304104254603103803e010a0502203d08038025880e042c04100140c00800c901d4045030358145c007041c40c1440c90002e110140c01003100c01c0000c01140d00d41950001801c0c0060191301102c4019511001d145080081ca86400c054030001160b000c5143c03030400c089056445075001801e803d10ba0003681d0040f01e12070048000401300c1d9054010320039a01000080c800000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 873307688 1250 873306438 873306517
    0x60f0717070c14010e040b01022d010f0504110112091a070201051008250b0318100c02030910020c1906031d0a0209062d0103111e0d02 59
    0xa08195860308140d915801d09149070fa4085000400000c6451030550850000c2130818410b8603005009504102004c00d0002e0140001c08648242880020801d1146008110100e01d041c4034a082584804c810840410312050400601c84868080d281840e00141e03242c640c840341c055032202d95606044110401642da40006509040214401c005200110b00075039800c80007a26540b041d81003a1407040c2c00c400801d011082c00300d20002040d40014020b14821416443d800f1a02420103050340d042025100001800502d4400c08148099002040c6ca40307500d01602c5042a09806101c20b030301c0d25170500c01040e840384191804101c1070704040f2b42081241c0d01510b05000d408001950780800b1075580407a295242d22070289e44001d45051105990005c00c064143c016200d1f03285e0140340d55a10340c041e0046c0544c20105021282d50f410f00c60000700102c940d20310ba04008081001c03840c03084051064500d140c6d400f003000c0b8110651941211413506500040001100707a03503503240c40140400400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 873308938 1250 873307688 873307703
    0xc16030503031e060f011211030109020406030510031113020c1006060e06070302060406020310051903020910152114040b18060f070201090b090105060f0a06050405060f071707 77
    0xc500300d88807042d410f180210401848075080009070070044070702030000d8001c2d400c0103071209003150b403480105005502901030010007583d26800d00c5000380c03d840014040c840c806910740c0007000071035117410050030240c408564100000c40d003038044001034000d460040481c1c0c090030a50100303154555004004035015610b400606d46020070404c0b0483c0258500980036030010710000780040c48a07402154842c45c10f640c2c04441c262100007040c0d0351180d025188000400112084c030039482d20403049507001201c60400218607041c48480a5065100c1802205012095001c0c0e880d0a010000841e010075202200708512410b50202450070320f825542910490030314000b08055a0508910500180300000102004d440384401035038250001452030045560b250146000101b01a45613400352050b4030020641c1e042c10301c200300d00d01034013503415031080c0c0c07420340104445a0000305940c11070702c007103941c81d44801001072141414070851500401c2d01c016540c4450b1004c00c075101030b0078803d00075484d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 873310188 1250 873308938 873308971
    0x150f0b0301050712091a07050a1d010507260309070e09010207210903081305031e12130803040e04050d0e18040609150b131503080c1603050303 63
    0xc0c982290001c1d2040c500184c0180c4d0700300c40081c040c0d08810f90807403142c1d140e090f041c00b520070a0142d03100c0540303542c80041c80000b0756500040d440180d98901d1130511014217459003600c000030b23205124109c00140082d40e44000c0700302c3d1411190040e002041c185d03d455960303103000754078251600317000d020b14901c44000a010840036181403080e036000c9603110160540c440c7c07001c1100185090b80c95403000800581003400300000701c02a002c1c19110100e58030b40060203007404100b42c1044810400d42d07580c141200d003126070414000a400200c40d000084080e680c0100840c2120139642e04d03000480540300004000441401d00340d0300a202e14001c1c002e503025405007520840c2c00b413040c401d1966006988401080c101000c5600c001d402a100364030014002c4200d65512070104402001003a8007643c0e00c80302200760400030b10f0f0700080c4950300010000e1580c120704404085605000c081c0400a0119240e042c4000030003048100c0ea150075410b498495980c54100d90300d510854100000c02c40382c45 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 873311438 1250 873310188 873310211
    0x20d1b18050a050f220212060105190302090f031501051017040305160f0f030f1404091113030804180606210605040c050405090106081b16150f 63
    0xd49100940700024690380300589000200a8054007040d0070742d41c0131500300360019014090b1802c03901c402c020004003607140c2e500302c416007014440051104d8188142040020018050318020f1020b142590400680300c000920100350404d00c003441c0f00390144210311000000b040e203c18002c0c129041203490742c14410100c40125440310f815003038201c401e4103140200b0002406031001c2e108041001c0c203003c00c030b403925481c1c00c040c58640890030b80d201142550002c00b8035601a01c045035451142c00d28058447c0243d802c900b151041784a400c441d582d907002c4515a4160f00700c2210039038801c007012540c040d03880e8100050658010301c12422004050102d000060300c0d240036203002c49609890340d07503240e05c00c20303d549150300b807004081c1160703a03448030702180a03036446c801d0100301801c0e560b40503241c1d030038001407008050b410380201e4144110b40d020482030011294030505009040c500d8240c0314008100803a0b203c40d009480202142070540180841e203142d984245085c14194009004185c44207 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 873312688 1250 873311438 873311477
    0x4120b0112050307030f02011413020103110c070e150d08040e0a061518080d05070605060a0e060114070c061d0111060612160303031e0c02100f020d1b 66
    0x420010440d0f00240b00401c003280c00340c1c80f06000c3e14075900000c1150549001c82080e842011140d46441e131281c080c3c04415941c0c035200340c201c508010b80c82e40d850031389403140342561011944100c0c182e080d100000110120a40c0e051018086c0b005401c0d02450641c600d011407407134229000d4402d100c0003410000c0d5030322005024800c11540000b03502070f4081c164900854009400e1980e0005100d07030ba40c0c00203001e210401148103242c000d0b41c1d07042d440701c2d018070f0050203030707200a02084c2c03190340b08403001d01a0042c580d680c01c2d0405c100742807007a03400d00f44c03a0040b5040d000d128005410318580320000904c0c1f076040304c101841500148840710400012200541d114900724260344080c0d444400021081d0501034076501480403070104503a41310314000d400707501555443e00b080340060344031204140c03100d01281c00c042d540e141c0c1c4507040c0007081d207441000b95582076104030b4021503a2a20b010b00383c144050741c1121000f00300010103114149142940da8500c0c1c0303980e010a03000440c464407040302c00c00346 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 873313938 1250 873312688 873312719
    0xf06040210031d0703150606030b0a0902090d060e07031401020c060a0506060904021c0e0327010306030204051f140915030c0306071d011704021e030304120b01 70
    0x10021403100c1c2001070201c0003059422600d485a801c0303034401d42102c0b0002c10014008521500b6030f0828107000400340c030180c1b038950b4000700925040c04603001c402c5d61018080030039688500740050321208094006001c0c101c18040140110340703014240f03021103c0100705101628000c12130034803000034045d4094203c0c4550744601c540c94016802181019196070032580e00000010169810022800005030803a4880388081214a441c0300326601d12410038001e144040c107049000d0360070510203181524500c0034a030b040030040f0301c9a01901c41e5070ba010394098405190041c1042095150541502d04410141d00482c07814103200e11000036441d10f02c454496102501400d40c42c15a1200c01c60136903a00181d440c415414058046545690f072020031031070344684807a6651a404280352100700482a0700f445026040200399403148058500c0b0050042e000f65050321203002d108440c0c1c0862f09010004448998140000940010303141d500010b07c40e451030103010f80708102e0741c0e03030300c81d0071130000b1b1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 873315188 1250 873313938 873313943
    0x3090604030828050711030c0c120715030207170d051509060d0308040507031202030324060711040609020406050a09080c0307030f1b17010c09030305160804080f030c0f0604 76
    0x40352450b0300c02560040e004103800c01506e003005100b10400d4910710381940c001c1c42103810700380d108a960080d20b2402c40300c000402228180607040381c41c1080005280d8200b4200d0034014944c000402104010215000361a11f0034818038164880e100a05a0805000d00b40c0364044090304216901b0203c0c60420560350050b4001071400d9280e2500c0d9038161b8031540010025103050240c180c0000c0821103440f0003410340459980503560700d00d040d0f050500041d8940728110541c1089465419039130300c031042100c46294011710300e5180101650300003030241090350020503100e400030800042d000d4003c0040c10300c04c94540c0700e124140f61500d03019592501041c1c3c02c80e034140d0103814204003142c94036007038039032941c0070342103c5030201c2141140e100070f000c16a21210311104405144481d00728284119502c0e000f07585010302da403a05e1900c00902500903040280a0780001e0030140c0100a03c0900700c4004103c0c81c2c040e2815400b004603016101d40000000f44c05600804e030a40703104c200c0c0882c8662045a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 873316438 1250 873315188 873315241
    0x618011505160c3303090f05030a030c1101051504020c01020d0c09050a0e060d06021c0509030703080a0c081b0409060b070b010501081b09120609060a1a0a030b09010908030906040308 80
    0x40d110340c00320301400030780d00301755071f40700910a01038003041040c0002c100b07500c09520041344030000200000c00441e81c4c1144c40c4aaa4908800e11403d60150303400d16030341e01e800700c40158903030507207652043c0288100030609080b00d00e4000d040d040326030088413107001c0b55400c484070000965601e481c0c000401c0200c80265020b503540c248a40047c1c00d540c09000c4044080d2200582c0d9004211098101d0700c0c01d60351003441390300c041110400c042d4812021540290b0a45040c441e944a0210107404000c015001d042030145a41040c10814800410f480040c0907a081c10300c459035503800075951940c0b1014054850304590000460305500403840c4034001c583c46030301c140c03400c001c400c02024aa0414182c041c4d00c10001d070003604441c0e4041105a001c0c0703408402814003030400364512800c0720034003c16038001d10149003000743e8035038170080340e0b80840c3e0704607801d10074981e12140e043d401480340087c0200400408400d02062410015000c2c1c407680c0700b910f4414564030391038099240d8514400d200070825 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 873317688 1250 873316438 873316529
    0xb1005090a0506300910020909130321060302150702280e090d03060f0b0d0504051c0207060806041104140f03031902060618011505160c 60
    0x9003000001000d0015100704c079682e410142c8007000d022451100c00c41c81407000c00800348070020f00d00b4818010913800005c4110314080b01c0c01c01144c10907100810100548120000d41000d040c0951180000c03030490300c0005d0005541c40c112040200702a00043c5d000300f0303820200c1c2107d1035200003100e806540080140000b0804a150940c49038894a1511151603180900050005a80340d103640140c40180181403107404c44a00141101c495502408002091840070401000385208545c04551706200200c2c0c0c40e61142801e80c0b50540c3c0200355541c2d40b81c00807078009202d40c0840c540050b00c1d010b68498030035454540410007a164102d501c5846080104000c01c210400c204c5144054a0050200010118243c000030300710741286505503107800700c07501c91006d1a54107001c141d41c0600211512403000c0300c0c0458006e1011014041c0b10340121520001e03031280c600074025900180ca04449149102d25581380c41451030355a032190300c05400508440c400c2940f400482055148481007122405 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 873318938 1250 873317688 873317699
    0x10e2508070e0a0908031641161a01080c0306060d050c04060b1809090606040507090305060a0213320f0603040605060109080f0c0d0c050d03030b1005090a 68
    0x2c500241c02050a507541c0e90340000020b08500c09507109440f00b862058048154400190100311180d004202500c418000740304103481031854101e0140e1911484844203010145101c80c40c07141c5404081603010207000941003001e030f00821107045045090f69459a40e8509000780e551103aa088543e15800410016041e070808135140036403140501c0840702500c00d400f000c141160030a40001c0b540410009042c40101e0803110a401c1c141c5c0103840c618042e00c2c2000c03030340d900c07414081c012921a64407000860b604c14403540c501c1020799081029201da604101e1200e40096008180214a00da50103000180c1c904801c01d400d03c0a258028a2000c07030442e900703d9100000c03146401550041000e407290000303490305406580701300e115000c000b0700f60030a03038000750013203c9076071060364150b100140e00e241503103001c500883c03507a000751880b0038000754030710b8881405036403a0405e981125500300444141035054000e40f20812081e50344812030540c100c2c084680d0f12903070089507008030b41e80c0c00c100403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 873320188 1250 873318938 873318959
    0x10b012606010915030c0207080f031b0a020907050703030f09050a0f030504120804170a0c030818091302090c161403090a03050f0d080412030b12010e250807 69
    0x744120145000211640c030b81651140c41030204401c03000095455010400247d010000040030300f0180300100840d6180d081c03070342c1d964454510204a980d801c410601c4101c80d08111400308164020139040c9035250040c0010107030f40110350144c0012f4104216031030020b0080c4200009560020003810f00307a88140c4813410200280c901c1103082020822000820702c800301e1080e035410b0302c81c0205654039454a44050284807011a503490650440c02052000614003002c034400c407a4404402921591a00326030000e0381c61501c6074a800150560412030049820f5144200c114400c80b89030303c10351100c00c039941c460300660b40380c40f140310a008458004141d04408403050701200c0e01c100c900d010386100118100340a90303130044a00e540f008011510180040c0311310b06100d442854502500d24141c4c5802d109030686810603018103549402c07040aa07102c107405248001c0b901e07002800b403440c90500542d6655208840d61510440c01c3c21344502c04032041d026141100d981c1001001414208043d050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 873321438 1250 873320188 873320191
    0xc0d05100503010e0d02070b0430170306100c0803130c0b07230303040302070911130f06030c0e030309310f0c020c0d0b0a0e070f030203010b0126 64
    0x48145a2462002881d03640074040c0320703101111031000d400e01c500c0343c40c3c019113030803266009040c6c0c02400344018420743d21030340c04182c078800c001c20b504105011502c1000802164050002d000303c0401d04c03000b603411109400444c001c0764203440e1040d9010103c4012110302c41f082030000d11807a01000482c8007603840c2100300d1b501d40d005000091036039035078080c140602d521401049401803c00c01a143c4680c1c02984943c00003151100603501c0c520381030307400940382c2029010f440d012543d50241c181507820410252403d00301140344c0046626110f417505440110148901c5000034103108851136410700ca002c8401c241c210103802107081417200005c000f200040d407000d000300701c1c49143c0500c1d0513424040d00716546002ca40c100281d410844040c00095400e01c556540c01d6501001c1d44e00d0464443d103a00d0008150400b58400042d102d056210300a0620118401480c0c4188440800c1014001c0310510860348200c0082026149090065036800311030680861481c0110f50b500042003200e043c4207 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 873322688 1250 873321438 873321451
    0x6031b0c0304080f060a0c0f050702190902210901140f07020330060109030f110112020d02120a050603030703032004030b061201330306090510050a050c0d05 69
    0x1203040c00d440d044040d1911340502d04a62807030b0b209105100e05070441d84506011a01c244c034024098200e100c03000b803c603225503d002401208445081c00121007224111000b4080f010b10a5648060300100c2c4494003a0701d015420680d4195804500c076800140718900350301400090204440e40c44280499180381c000748484150b000400a466584860030003031004110305100e001d101803244204030346806001007400d03040c0502080c060012443c818407252605510100781c818143c49200121003010300140194038850011130600c8501c45250081c201d400e8080564181a0742c540c4a5002900c9003a0760361030305600f041000303101191007034100f600040000351070703106600d594a480c540d40ba0b20030350056a159003000b080c04003d25124400a5885190700700038040c0417682c0e202c15015030900b01480030303088406102009c00008140c0c00c8001141c01c80b1003009000a2400d08a03101e454001e482d4110b103240c0400107806050718421b01e4001d1030650122428017a0b417114400c010b02c4003070050f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 873323938 1250 873322688 873322693
    0x16090506030a080c0c04020a09090c140313240e0c0306100b160b01030b0a14040201020d1d030303071812150216020a0801020d0b09150616121d06031b0c 67
    0x5c2201d580b168002003c0791075283d030315020440c0c0303400d1180b01107a2508c01401c1c1040200320540210030900740a070707500a46240d11180307180c000da2900380341d0f001860703001c409480b00032044023155040c140c0c07000001000c20403d40c2c42d104131150030103444e100c08694074480d84200e0700b4180922440d0070301070401c151b42a40d0400100c4000d4640c20144c5c6400d80c001c40f2894020703020882d0a03a201d00a141c0d00c0e0040c1061800e140c00d00b54000b0b0340310041844200b04100c892941013058510365010307802c032284040c09490340d0341009807009101c02c0d61180d000c0c003071a41080b400500030001c840ca0b544400e41003840d82505498200b10280a03601c5020701c5120303000c07102c42000160b034916072240014441c010005960305c01522808040e14047c0c880580b04440150422243e910b04901c0b5042210048501da82d550040c1e08002c4003001d01100040c102d06c605000c00b00e08590007080951000030151207041e03482407171004108440c0f01c11114414000d109000c0080b00c14001c002070301c00501c0003800e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 873325188 1250 873323938 873323953
    0x70b04060507052113080109030e041a090906040c050604060f05030a1b0e01123e0c0703150509031603090510270b12070e0405070216090506030a080c 66
    0x210240440960075130f02e400f41c64001103524030040c1018081e0020480c5500a200c02552910003411080003a002036000b19119500655048130410b60400503400003000c1280c981000d0009a41d06c07034084030308859049000202095501d821820340701150030130340d01c80c6501e607a00d0302c00326a035404c084d050b501515203600e41070110259400303000c00455090368903401010720300000100101c200350b180b144071614026009080c40740d14607103242c3d03040307040d100e140402c044090300c00c080502c240301c001501135010031650a1040041360f20001ca82c056400590514000503680c400c49506460f0320105610400090032062480408009100d00034104280d209554401050f000c0c2150340412001808101c40c8201c03110300441100c0045191807043c004039030801d016072600f48103911101822080300f0000840441c421204490078000c054018046400d01d50000386d0340d005407020701150303446150404101800303a81304442c0708140040080008107910303141c00c4500e501c05428440c06025014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 873326438 1250 873325188 873325213
    0xa081036061a0c010501050a320406150e011427090109020909011403070b0d150306021b0a02010822050313030c091118040f0e0309010f02070b0406050705 68
    0x41c40e421011100651643c0d1030014411107400c441050300312502c65490b204083c444507102c110901d184481204120714851a00d5810320340628251904c01c3d8440d0900c800070507994201a500111201261075942401d01c0c2c4900648500440c8002c1201c02c58051265500d0036041000c402c108444200005041803c0400880c0084200b600040f01007500050b04145508041d0341c224010645000b50440061310100040c1e01c0300c2d42840340e090460804101e200c458403c80c0c8c401410340341c01101100701150381e460301001940100303000884210301c03441c4205091401058800c05181d051b92130310341c07640c4d81d00e00d5000d4020b0000049800301503101501400500104020400d40c4124284d1191032407851030041062040c9400050502c1d00302946012103001d2402910241c0e0b00720b02020020344051004100204589800340241c281810007400c2c0c001c03400300040c008190280d0343d008080400c000260395038105803240c2c0b81150b00c20001046030354484c3c800303064810b00c07034415112900880e8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 873327688 1250 873326438 873326459
    0x5090f120a062003060d03030c050c2b230c030c030c07030c1a0906030402012a03030605030d0903020925121505030606010f02120a08103606 62
    0x204002c490055940e60328519502c8a03980c019142c0212445141c13540c81e100e030106500e680c03410b40c0102410340700c406000109014605960a038071480c4204d444030261807032401e05a00a05400e0303d04035108c43c40300360041d4420032103125516051070711707422020b05221501c1074541c4400606a4140002e1001c00d24518050000307061007040345004100403421030030030480e07520480c3d0003948441044e03413450400c09ca05500355940d624007200c8054903940d0743d00058420314420008881070a00610a6819070703002103510000e010701075982080101d032118241541d441000c0390240105290900c2000149400c00e06140e0200401b0100c4281900c107819882401640075400008683e043c014020650710a20501b4a22070004100b03e11252501c0003080d180d440160030b0034104503c0e0446003004070b000700441c92400d00001c1045c1c1c0d44440848004100070410784607044c2684582400148043c0fa401c2ca4940c036200d503106011100350501b4401040e420441503101c0341070348860b00040e401811 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 873328938 1250 873327688 873327703
    0x901120f0207140d02030310120f02150a02011a01020304140402090a080a03030e030306090711010617071d0f060d050a02150a03050f01030b070518100306031406010605090f12 77
    0x100030504041c40780030003d60502c1c1046400c401154801d00070051032050510004003281e2a002821a00d00307910b081c40380c04642400e0019400c24100d181c8044010202d500810715149568000c02a0810256a4041140c2c0100b074041c0142d1080c84280059060320044004a05005000601d44106140031a842505650115810390088000d44042c540c0500a004400c002400a54035610b4141c002a4050b0710251098040010324580ca503407003142540040013178020955060b03410307a84120b0442e41c40041d40102d000008071308108011400550312100d00404000f420030006035128014000024400b480036600c40c802e0442c00030158a6800c4009000312900c141d032941d9114044024094900c060851702c02c1b25146001007004c14103c0d48000c0d00f181051070980c0d51204090034000c41c070341000c64406d50010882c0001409142c1581c4088112881000088a00307440102a603443e00024031132840440c40801c0000310310f00d00740d541c0701880303c030040c4410424100e088020b49803074003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 873330188 1250 873328938 873328943
    0x60302030402011b0f0b061306032402070b0c0a090f0806071d03070311040207020901080a0203010516050415140d14011205250e04031701060e01050901120f0207 71
    0x28008180029564481c10424181d0000c8996100e0318485660701100c1d50305c01100034010b102c140c1c020480d40d6a0302e40ca0034400004007501800403584900b800100f060045448000303020707003540f4000b80e840090080d00ca010b50410f030000c080780c0d580c0241044641c0b0a07124102003080700038010601508010041c40500f0280004100c82d142c22a0050965600300580d022030205090b107040150f5400107201d016a68400c07203102076001503c010078042c0c002d40070020341c0300180c038001044a0300c00040c0101074500890080c891600c9007004442c1c150821400240000e00070001840050032490b03040c80100d0703191a200701e030440000350122094102c007407481881500c03100803050000411641c503025107031000c60440345020b50381d0744507550348480a130603c030003031200c45840c020300000c41c040e0000c000c0482c903194a03203414500244440710307120240c04094451360020130840d00c20302014032a80b006840309880c05550100546482c40a031585544060702d584089001103000c3c0041c211151 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 873331438 1250 873330188 873330191
    0x3040905090d11060a0c11030c060a140603071401090b04120302011109010504061214090f071a0403033b01030609090f17160b06010f090302030d11010f060603 70
    0x1800c100302410400811018403c02c4001c40c1500000b80c008206190450700490380040c28070510841030300c10003c84036000040b8000480d1003004480045a1a403103081d04010401004850900302c4a5101054031001d40551000c8424412240d40c41c030355a014031814185040d0b4943d8520400c80503600a4018880358074400c817060b01090b80900a40c031000e240d10031000c0c02c180b080c07030000381180030310b02c68032741000384250300141d060b10180d000380d100d04c2d4041c00981c828030b4078041041c0d461600118042c0c240c403954600003642000c418080d4015417108841d145414510303182100c0d0b8030304040380d40d455a01c0064080c24010b4020f04440309180703180b0b00c00c0d041d10700080c0c00542290126030000a2080c00e1042c0c110004204040ca00b59207a07200f49104002080b40700c0c010b459006a1130310781c0901300c0c801d69800034030121586191203140b09903215403036680c40450865880d0a070784002509640075802700c01845008010509440c0e00110000614a0200b00d03d14103461480d841034002c43e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 873332688 1250 873331438 873331441
    0x120d09020306060a03111315081e070b03130614011404060b030606040306021c0f09140c03100f0b0a0e1f14090402060d090b060a09090c03110a030503040905 69
    0x509061041560183c000c80301075010364915104d03c150341500000e614440d0b101020401420101603000c2c1810164400480c0c00b22500c1d0302300995201390102e07030b821001c01d250415a641d008009512030658401c56502811900d0701b200244101405040464280c1d40303031590132480d0040c90344040d00921240c040302806000b100180400c803171040c0c01484094004200304469a101d400c1107804680d4028401682c4896448031000485901812624144c0c2440d80348403a000c0c0b030b50440d54046001d40601da9400d00341100d00390340c1e25034156181d0740640006402021503206584201031843d04540f0110b8081301050004140102039048224601604000c4c4412100504880c0c10300d034940040a00700e0a007419010b030070346800c00702d50034401d6441e803001800315104c800940e07004520807c0240211100d602d00f05c1e150800031600c26001d0381624500240d03d11480c002e07007401c01d400c032482c240c25504640b210020ba007000d40740e164020040a20002c001401080188010101c0500010b0a03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 873333938 1250 873332688 873332693
    0x50f0c010905061510020a02270c0301050301110712030b04060b21010909031407110901080a0212031e03091903050309010e0c1f030e01060b04030c0905010803030c0c120d09 76
    0x4401d0411260b014030702c21080c5190726600000c1c6041c1f41d6070101c2c2c0601551071924940d404203005002d480c40a100494103002081c11440c0156050300d0b0103c000b84175545142250011714060014003610410000000780d0249000383e025483c04040a440808c10359101c010300402a80600d0f412002d8814040c071848007201507050a5000d0031a8440611040b000f0380c40c0107041208001c0c011a21540000741d0a003008080103c1c3d21060401800551040da502c0350102d42714010303480180d002e03c5840c6001c0888036800f1084651101120511420b02c1210000114441c0c000800300c00300da10079a1058005241200640356909102c4da441070359030b2900250150a4880200366100319030711440000c04c550799000c428000d44941240700c450001300d841c5044000c0d0480182141c2907501c1c01d2030106e200c503091001442a01c1c0107500742c9401075615000c1c0000c8400074800c00e000e641083c400705400d070101a00030002d0391f24620882d41c881c00e0503001c0c650036901c1038000c00a0315685900b09801c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 873335188 1250 873333938 873333961
    0x506090d03050105060c340e01060201200a0e010e040f02040510030b03060a0902031908130605090315040507030c0807091107020d0b06010207030602210603030408030703050f0c01090506 82
    0x1614043e1106424450000c40300c0d80d03100b101040d05400c4000c580a00ca8141d010310307040b11f43c011942e0140f001d40b1a56521080300481080c01410015420a5030007011070700c615900d1942d000c0504100e510300a0301c80f404032003c0003a83d9140c0d04200e2007034907218035030750307940110185001024801070340c4519000403c0680941000401e05146c14100c42e450581e402052080c0e0022880c000820070240d0b502c0040d0404c0b00d40441142c40c1d81c0450640410300c02500f025100d05a89508030040140d12140245c68074026201020383c164010248480c0782c000e400ca505070403610410032142e43c0303a200c0e80c9205041040d60022038450b0301030340f020041d00c0c20f00c0c000c00040701d0500580901d0000c03030740c01142401040706e1000d4071003180100031a0707850b4130805c20f100065401010464440036584000045648003505e0205100b00036004501d140c41e0101c2110200d036000c10046140c200241d8050711036400c552581740c2070140500840d100507000b8041d03008410702c83d00141c00540f800215030034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 873336438 1250 873335188 873335191
    0x70c11092d150d12120207050303091501090b0f0411040b0a030c09120201080f060102190807170a02061b040b0c010f0f0e0705090c071e0b0601030504080a030507020a0506090d0305 79
    0xc0c45800860000d0380800c01058903d0b030004824500143c4170302030b10700800040d100710003000b0411301c0004104004144041030000078440b28065003c01d5981c1c6148031002e807184124280e521180d8401400001e1600e98001c02107241c6064031241401d507683e2030000b264000031000c00102c1d46980e0f20701c0010740c0c0b000c0c04a003d800c8250042a00750000c1d00002d1411100800358030501030348a0101e8000d038002c20520b407186080039407444030080d035403400d1035054015010807074003502d40000902074404904240ca8801c0c0b819401800c1c0740d81c0f01e80546031440e017004c10218492070104000300780ca00700b460007402031204600000c110400070b03540c4071044500700032032b04094501d01582629107200c04502e6508541040b1000200760701d6503030322400f4900c56460010500c2002403805440c0c0076042d95000c4240b40109038100c1d195640c0707401501a01e10449004001d00070800030515254000c0c0c0c00780d17421000038412582a040e46999076460094165100d100b81d51000101d0084254103000d8903 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 873337688 1250 873336438 873336481
    0x928030b090607090b07060e010f0b1207243e07030305160c17010c020607021615020309090702011b0c05060f0c0d0203010906030b070c11092d 63
    0x20030441c0f425001c02400d50708a8024000085800202481404080d8003e25a413884c0c00c402040300011084180b0024102d01c84001d02880352018988404000421048112290700403140700b0180755003e540c4c60440319980c0303035003804151440408407001d104000134200d00050100040820b17154805222120700764603544031544161014800a0b500c8401d40d06e200307910500d02c0c0301c00c0b609490807040e1904a500300c0000c11400c0780b2880d07215501500141c0c0d84007500e800307071003594440200c00c07030b00c1d1840c040500c852104030103c00c0000003042c00d18003030710169500c152420801000c0001e006958150b49041c0107030344600800c1c1008002d88100c8400881a00700b01c90001c1c0a1ba903100d0721000000c006450340300c1ca40001540c0700794918103c0b01c0d11f0042660445d540e46c1c5038088440105054001a596190841d00240300c1d40c0c024000d040c1c0301500b0002d40380d413a010000c00c10034044001454185c00e24407070001c2d0792007055600410b50400484501481451408002d00c80c40c2c1c083d0750840 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 873338938 1250 873337688 873337693
    0x1404060b03010e0c0907021e030901080f1b09010c060c0c05060c04060207031209030203030d0204140406030f06090809060a0c0210030c1d01050702120105060111010515060928030b09 80
    0x41400c3c81c02c0000d501c103000c400640d42166a540d9002e416801d003802106805018404000d0134514280003200a2200320000d80742d46141d601e5550b68a103140c60304031010f00d1800c100d200c20002c0c65030b1302800380424100501d0420303540c1d4840c2e40c84d032081d18050311946010a007070508142c104203003803000c0750380440e04030059403e2629095000b035a9180600c000b80c48800080c1000c180e1b50322903100c0d40061138020b021240e640b040e841e510002503100d4810a910760b0040c0c0f082ca0602d10309401284212500a800308459100340d444100c003c10100ca000c8030604c400300007010084e100c0c400549810741c0345450b02c8148202c180140001450708400f0030b0201403410014244458021000d992852440507252219540004c0140c0d49480303080c2003c4e40c8494502c10130030040c201500007c2c450142a07880e0040440412a2070b4240c9038280c8031550304038000da9400e00e42d8103208015001500008190310021885090100c02020003540b20041c0f071180d050060091006003150f560308002a90f00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 873340188 1250 873338938 873338951
    0xf0603031e09040e0f152805091510031e05060403230f0306030d09061e030609090f030f05130e041406010611010b0909030901140d1404060b0301 64
    0x20000416441c8a4010001c40300403032815926220740c1d22615000c036251007143c04245c011700259668024a5481520003031081c000680d41c40004042411000d010244440703d0425400d00b110241c60018105105803245401104401b4178184940703004045500300e04900e5030860404014090042d18101200e069031841000060300000340a80d10940519140d188011000c405a40e601d2400c4400141d46c0c6002c079031108c90516210085008030801c03012074500000c15030054a504050380304400108801ca10b140c0300b040300c0c603c0d0300c0d105540d5500d400200303603485000c03a804840308030000b40c079584004900c400c201500f2150346041980f41f814014104100710103c1542c00005010713892507200400301007010000168100004000c501013919a00d603100c4500602c0020b00c2a80e00f201c660074503414070007608001f29250700070044035000c0c6140ca041100195001c0d002000035400360381b0100000d41d0280c8052045071207180c2d50985603081414107040120a03180c3e0303161454401d925081 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 873341438 1250 873340188 873340207
    0x606080c0904020a11060f240a17010e01140609070c0b0106050702040f0f0e21040909170c03040504050c1603110f07030c1d07020316050102090d06050f060303 70
    0x81c1c1d000d1040884001da80d0742110f20b02142d416200c500342201c0c500c0366405020882c1c0849121310b10442a280c410b11948176240c0e0505070701c900b608041030b04900c040c0740030f110203861a19001107450f402c5c0c0010803040c5203106418211420709002401d001601000c0c450140340c88100c0c9a00a00d0398074005071000c400f0b07240d80b181c4400600c1a4410b000001a48104544564028034100c180c0d1030820029004060031200142c500440d4484050042c020754003c42c6003000403018450f01403101560400e130400c0c14200040c40e8030101600c41800b0580f80c0715024204000400b42544004081c0d51501d281c4824002659400381003031500030401c1c8a000c0e400c0c7c01d0300c0d58010300f5980504d0a808022000503259040c00080c1c2809811400790b2400401400b00e480d51010881c0c3ca54071003401c0049c1c4408084418460549806005070800c11140c1b50017008003a804100074050b1000604d8030203407034000381685202810449070140c8800401041e0040f0501a40d88803100303074051450004040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 873342688 1250 873341438 873341461
    0x1504090c060c030311031510021902120c0a08070f060f0c290705041a03060d260307090302120606030c04110c07030503070209092e1e060801060608 65
    0xd0084008210b1109003001c2414400e40064086000d140c005680d2801c110700584081b0380d201c80354600500181038800916840000c0d95800d02112201c8240b0702710440e420400841e9044424151034030803284a0701203951414040401460608000e00f00320385420001c041806466200c08140113800501c00313211398102d4414043d140d4000440503000301d410040c44040c0c025403040b074904089400403c2070807504140244240c0b83ca848812795030380e11544140140703120407110142c200002456010000b001c0c8189500780300743e0034800410360106103c030141d03d608100d0f4540009a407a0b84104150f041042005841c1102800600424a40200442d9503245240c001e140200c1e603030410100921880015a0901c414032030a46403c25920b080c56941c0e030f04801002c0c1c0c4502100f0000c00d2004900044024803000c6545981e41c1d100d110207401d6540c008104801c0203141d031240161b003030100400c00c680001c102e15000000c1d10504103a2114216016a000401031040340820f020011640 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 873343938 1250 873342688 873342713
    0x1e0f0c1d061e13080d0207050a300b0f01050901060309050706050d09050102030405060103020f0d170306011215061412010527040303090204200304200d050105150409 73
    0x200b2041c0842002061000c55a5100300802030b401da10078600082100c02000c07401c0e806a01e02d0b03608071190162503000b04140c0749040c0c8110049031034401e6117898030f46c001a03001300b0b20303481446116901400a48540820b402c007182c0f41003c0c3c4841030014005403401c1040f490140065290400076080c00342e80740c503502c0100d07018090902c800854a0440301041d40c102441c0d00c0e601500954681c280b9150031030355020203000403481403803642141855030034032281ca0240c0303982000d00450341c1d00e8210880200c03940003a08442c1001241c80841c80c035000c49000700d000c1068083c00701014507190803c001d050050070309a000c000c000410003c0009070b45032007100d040d50b400316184200c01044100790f90146403500840702281c14250100304c141f6402d680120340c030a0090341c0a0280e030800d201440100780b1890b0a030500c040052020902003030100240c011140b94207900d040003101e480000409011440504031140c0c3e4590041168016804c2c2405005100075101440964419614940072541c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 873345188 1250 873343938 873343957
    0xe1003110405030d021506031c03151d040302060609060a05090916061e020604030804060e0a060e0102070c05030c060a0f0203091c031715041e0f0c1d06 67
    0x4030368050300030002064040790010700005040700d1500840c040c4c007a480c1e42610f00c5600c40100c3c0d08000801905011070510540440141d1a90700308a0440c01a001041c01d12001d21f00009485c0b408a11012100e01900d50904034516030816807600d031034005c1c54100018929030282d1048030074071850340c0321103c08070180c40c4200e6a110841c4e0b00e5030400c0e4501010903605070104001003800148058000c400c2040f01140c0003c401c01c0d0319121030082c0d0303658005a80050002e509000010040f030240c0e800840304420840c15510054007648078001542c480101660599500141300800c10443c401494001d00b4280c0c040c3c0a4030010900044250040c050f091042c00300303548030000264828000c80b4581d0380014002c80740d52801141540840030403240c2240442c111201c44501c1c000b0a0106502c25808054881c84206203c020b100242c425911901900f00244c0044400d0b81034500a5180140d507142001840380e441c030100400c00e155200020750389000c0c0a500c808030351200f9048884408 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 873346438 1250 873345188 873345191
    0x80c060a060302130216020325121121060c0901092c13050f060103060e15060f1311031006051206010c0c030f1a0c16020d0c0b040b070309060e1003 65
    0x2000740307030464118064020020340c14064842c00200316440345880000d000030001e2002001034480b941080d04025207003000d0204bc0c1014000000d030303c1d241100304141002910b01c483c001c4e03043e803d25840d0500c25a00380c1c54004000c2092400c40d40d111810f840100100000c10036034030744001480c00039222501040c4149034980d00060180c03c09110f2504400d5401000c40380425a081c2540d91070300f5081c0011501c0904004500920840010302d80e51064815080c084035521200104100710081340e0b43c090b00090f2005900b440a030240c424000c40c02c4a45ca101c668038940760425510741e18840d040802404010f0042074260461b0400c100d5002c6c0081c00e04c20900b203c40e0400e03107070300e09903540010441e218080301c220800c421000c1c0000013000035002140305481c1c003900c0705658003075013a08126541400e02c4060141c0752002c41d00c03001501825480c00311b0340d00c0d8601c03548142d01c607030000340c1e09000024a4504140d8881c02690040c810741ca04185601000c10000d5411081001b0722030405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 873347688 1250 873346438 873346447
    0x41505040e2803110a030c1e051e16060201093e0402040b04060309051b01020c15090a1e0e19020c1005150918061609030c03080c060a0603021302 64
    0x94040d804544c1040c060004880d00c440b61407800401400c2600d00440e003011141030700408250064240c1803006034000f001c1c0100318031880145200f15090000e019440c458041e0039001403030f900c900c990103418181c0c00070591920504050800341c820358440e1101401d010408010001468003c0003082d0001c240280305d0488400001e001e80541d40110b012040c0010f00001e1443d055400325024a00c10001c0e01c003448001a000045140300c401c0140c05070700b0225460307000789460030200c0748450030a080700d41440b0868000c5544101e44d9000206040e0000044910296101c07805400401100c41d981003d441c09034903100c0450004111280c465401046510b94850240080d81116051005c1040140341400491101034501442c4502070401c00000c200203905032084030302070000010040602c1d4030380200e039620300350a9000c05000c01c040ca07030300440004c0e61701410000031030040320000d0321910782c5401c0780c0c10400042e04411040789460001c10041e21000b100d00319055900c4801a282d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 873348938 1250 873347688 873347693
    0x1d0321090115061d0405070207090e15091e01020a020304150519120e010504051510120602030f060105030402150306181807150804110d02041505040e28 67
    0x5040040b8a6942c2680c1c00b410104015034000c003c0300040100c00951101400070009000c1140c4c0c0c10f403403201c0141c1042c5070511096416030410307038044110604a862007400728101d1000407800b41c070982d0590f0000c440c034014072048100a034404030050002145000f0820f58040d58910852280342c200ca02c1c1240012401805901a0380d004241d02c40120800c2041c2c44009146008100d81500c0003841d100305c6650780d46052084030300c5580e10400400030b824542d011159140ca00034020041e1641100022585080582c1015000b601c120701c0561681001e10700005501ca00030022410400f0520800c0b0150313440703000c00f00c030040340070011b80d50b607855800110f41041600341c094640c10010000b8882aa9050500924495659800c1d2241c985d25015103411701000f40e04401b00080c034880c04034010410b400c01501000400820700c11811041c2d60204058a07160100400c21042e054802c1002e420680106d41405070108060310190182c043c50000f40d8030290001120f06800441d003104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 873350188 1250 873348938 873348941
    0xc2003151e0703140a09031e0813020d12030f180203031b010609111329090406030209090303040c060905060a1103040503010608060403031107080301361d03210901 72
    0x15544c0240e541c1e03200a19214285c40003800d100482140003420095003041d682001d00307a02005145e06581c0ca098030340b10801044224404804103aa003c1c1c0c9030200c0400140c6a4009213044107000d032004a0700a81c01c8150344120380f8026a2040d680103146244e8005a40c044203c0d21170940c0c41d00503880b1135001441e858010b145070f40200040e60f18010311100d200b40030001030207400c9004e8203100741c05500d5041c0203207480320074412a4550b80361001c01c00c1141031040068540600c000d040000c2890381c81d000102d400e80f0944240465800c00400e1000340803004030039001400c1d103420800f505519020100d8100c0c0304481c41c620400c034403802c9101c40324030240304840c010b00c8028000c2c0103240e12034071002e480d110141e40440110b07140010b440349030f4603141c0c1a51400c5070050b00403402c1da03181a5815041e41002c07449110b09110f40c00c103c0c2c1d84510246000c00d102440010002095982440342d02401c49188003010942c2e4803d20604c3d400760180364001d55a4a00100701c011039403a412441ca0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 873351438 1250 873350188 873350201
    0x30103030507031d1009290a050a2604060506010806010e0d0f08040e270a030509031504050708071a0a0c17040602030904060b13050609010c2003151e0703 68
    0x55110001020200319117031b000e040300e81039580c1180e400031303810110500c2100800c8842c0c0e903800321800500428006902035000350101d82d0103800c105c0c540800a4070340c0100307058510414480000301c08240000c0c01f0306445200d0f4803031000c0c20012454140700300041d01c0f804100c1d040f58400e0080c20034600030000e8030440f1151240c0d011500c0d80e240c03a113070350b1758030880740c811510484000321140b1820f10b4080882401542095608050b0003100007940703003143c1d244c1c0302101c400c0e01761080c0110912035404514003144145d0296001e01821424500d0705402d02c1c3c1258014841c0c17441c1c991140185040141c101d40c0c51920605111b007200f4030034901003084545d1754104200708007000c41c00154032500440240103248040b10104003007515801a29541d000b03c0084400085840c03034213102a00345080240300380c81c01414810ba180100b81e482e070080c1020503400e03641041050500d508a400c08009504003034140c4d450000ca03e140014051180302401e522078091200305402280556002c1d50214 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 873352688 1250 873351438 873351497
    0x8030a08010e0613051e06090f061512090d0801050604050a180615090312050304051b010203041509081509030d1a130b090609100e040204020d051906080303010303050703 75
    0x744031780d1500b10444101500c040070100b540c1245680041e4082c60325080c43c0d07205242ea041c4403281903e0340790034000724a01600c0503c0103902d007005103020840200d0591441140c800b001881c4490105600401d0480c0603409640076010601c0140301980e54007200c003090740e030345840050346000b0074030014000d400b45620014410302d020342250304190788004040250390041c86210310f0f645241c08200c55078407045074040c006803c030302404810000c407400c020122400501c1224102038440310120007000d164180100032803e0808100f0006070107200308483c00d4401c00040d070b00c43c40c00c0c141480c0c03648601c0e800e00c0106a91850609607c14030854001e41c40c442c0640100c2c06641201c241c0001401c507204001e2107144200001000c5d07107444e4624600c6074030b90301c1e040d501d6a031905081c0c3c5d809880180049900503002c1c0100b8004030b981d40300300341c444c0b8100c0241124141c0b100e0010001c0340c00c00d4103c106141c10810041c00400e40003803c481d95181c0c14580f80104c50300300300c80070010b40c3c0e00b0b0211 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 873353938 1250 873352688 873352691
    0x608070308180a18110910050c0c130f1406010c1b0f090209130e072306070b0f0106050703080c0a0c150b040b0d170a020f01020a031508030a08010e0613 67
    0x208120b00303515a074078100b180260b0104184880540f00c640640118103495034429005554007070386d60702c510040c05550300b03000e00b240c61a50060f00012151040010284820341c0c1c0c3c2e081040f15000030380210580c161741c00c3e00394022030400304002808001c200350301a00e202201124440540702c44703100e0400415110605101641d22503802c00080d60007807900511071142000305c807000090911070204551000402003041d40e10f400e0310281c4500b04400ea5451072100070f11071045580b5100c004140041c81741000d03500d28584480d08032024041070708001c0402c001842690002908100140e4008040d404070070384940d0b800008540307112280b18014440d42c28110081200055172b000030b0700401f8100c5040c00301c5510f1308140440d4400d89000503100030205d1174401c80c1c40e00400000c2c40486200c0c41070380c0c2d6800000003020300303913440b041d05c442c0040e50310440600725100f4072901349c02404011024614000c05000e000344101010f003d4071008010720f101242665a03400010340c4d074070091031b00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 873355188 1250 873353938 873353959
    0xb03030c01050411010e12060705030c0f0a020327240408160609060f0801031b080a030210050711070506031b0a08010612021804050c160b0612060709090906140c031603060807030818 80
    0xf0001d41760b40025080d1d02030104005011200d07804103540c22890003001030705d802d0021402003c61140d08a80390b000d8005009c0401c0080b942c0d46042c841042544a0380030300308080c928000c40148900b82503032000d01007110404001c1c43c4150703c5019981181c1d0425074203901d290000000c04a00055903000e00524801c40303400b003081540110b80005000101341c1e04101950340c03094280c1e42000c14501c0a4200d401024080c4264641000a0b5420807281e481480e10301c10011900c0c0925407011000f00045000900100505548a2407200300310700c4c030340029400c0002c2d08030107459900c40003a42622464681e0001000302070980d040d101041c480c03256030006400541860a04d41d081500c1003401442541700740a960a4001a42401103220b941c50040e841c0c0352501c2d010090100c008210707850f5840c1c2010100e00724801d0784c040c1c00f40051142c003d94a040030000d00c0f508480b000d00e10001c1c5400d01201b00004000865144220307030304165a940d58070703007000c00c0c0ca081d413092084c500d621240d50b41 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 873356438 1250 873355188 873355207
    0x303070c020f120a03030507030501120209100512030304061107080a030b1212040807090612030503100b0a030605130e06070c020312030c090a0801020705100b03030c01050411010e12060705030c0f 86
    0x91343c503141d90180d101044582c483c008102e054580c00d0041328602d80d1102032040041c00c064285960101c0301c2050100c1c440c0e01c503070000c0c1005608512070365a0b40c0c400305c14041071000d60b224140c1172240c03503420785207048101d0b6110b01c10f9005114003070b07082c5582c4048152864654050710340d4007a40060558103900307510200480702d6001070191503951320680368040f031111258801c2c4019602100d0003900044480d41d02119103a10003092482070b85801e403400030745001c8038005408244100d86000c92803500b01000e1009400e0703101e4841074007904140c030030208044040b91454002d9214030308420000ea490011a142c1030b41100c0c8000442c4000040148050f9103402900c10064102d43d15205c003030356600120300741d005038080078100340c202c02000240702546921100c5e0b40403001c0c1c2960304107034040c5905801c42d8402c071010703103c0850385084030401c0d6034800c0d0141642c05080351044041c1d0040481c00795100c0d03009000d0b90502c90300001080b01203103445d05489113400f03c11001941c922004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 873357688 1250 873356438 873356443
    0x6080606210a0f060e1e0c16060f110304020f1c0206070b040201090b0a0509090703060509041131090f022e030c0c02040b0a080313030b180303070c020f12 68
    0x781603007409494082d0200d080c0317a1041c0e00741d0040945040151b89810361100301203101710007600604a0013020000038110b91811b2220910355401030301c001403855129150101552041048042001420802c020050340e48403150f40300002c0c25240e030b400c035a60701091403620214407600039600410200304501002504621144a00c0c802c1c0d841808056440307001d032240d40118141c02020a20a000340021402c1207101243d028015140100744a90380b02c000c5180c0c001c09132030582c1d0804030b01c06403007400c1c1024809411404035450080202c4a003200d69507105865a111408003a600c0d0301c40002803000082804004603001080b40c40001020801c0c500d400120404210300310340055588180280244a001c0095040d03482d41400c1c840650b0800c4003c01a08910a40c0070b454220080382107081040944500d0040e100010103550440c00d100d0700f0b5507801010700490490032400300d0301c1d030800070050f80d401c0346450a04d010f1804041c400507000884101100d40c0068200d101600c610200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 873358938 1250 873357688 873357701
    0x70b070c030c0e06031e150426040b090103091412030a0c020d080606090d060f0b010201290618040212040605060a03030207270c0207030302150106080606210a 70
    0xd4480307000601d40e41e001030f064446049409a505403c542c9000406e80c180840113443e0501041c103448028001904010402000b03403019600c0c08510008a40f50780200c202d401d010340d61681c40281040c1c94806588001d220340400d2504040d1207952420400050315500c07005200e005050301e4030340e100c0c1550711f0440c1d0422111001c0c240d05000100300030a00104484458842c0c41e036030714103c2e81c0c40c041482881d600c40d6003415003005100f005000400c0c2c10b0700c554044044501804100e42440324002400e4406580c0c200704030f0625181085420301583c072001884003010766000f0b0303e42402141001011686854035074000380000b5501210390440820f0920840c8115030400507030311070328240b080040d0b482c080100564803800c1c041c07101c0f1034540c814007400905410460f01401c12118000b0640d95200e4a805c056801301c14180100340d01480441c4904200481414031580b5040d80203142650140141c0d00545000031058151509203400c401c60101801a0900508141070b12000500d1b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 873360188 1250 873358938 873358943
    0x6030c03080a17010506030c16061b0f110c0d050a0f060209090901090c03080f07051f0507051c020d18230f030d0c0c050a0614130203030d0e070b070c03 67
    0x4510003c10500341106030424103035100500402d0560740d83c000c8002d00ea50003461041034280380e07092a100002e4150080860025511101c49440b01801c0c20107000000010f6080050180742812055007680000300080c05c06070413940d107400301816003840d500300130750f64a02074500314040f80f0040911440360018107141c6800d58194400b0340d00c4054281c200e9038011703802444170058500c02c0000c9244071001d040a01c44c0d80031b48916042050f5651407504220114181034401404c68a1001c8011803045641c0a000e509005c2c0c43d1a6000c20800c148200310070070b06d00c07240ea0105a01824150542c01519121070b9131500110710200d03410300041d00380d00c6044180e08a90103a543da80f60050106010500c4010350001b141007050000380000603000c41c3c0c880004001c880e50310303017000c64010000c8540c11750180300000303418881340b0103860600c103005042130301000580c01408c00580300001128402c40b400c040016042c0b14024409003060469070200092860110320281440001600c4004591 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 873361438 1250 873360188 873360197
    0x40305150709060905010203090d060605060d060810090c0e0705070b091c051809061507140d03090b060d06060825050f091303020a06050709030308060a0302150a0306030c03080a 78
    0x90743c0304412036118085000d00e0340142c000340154005418200e0411a0399482400301156842e190740110306260044151304032a0b507117442c410040700e0428001c1801007103004100b4441504292107810450515104030a00c0e50720388400120138a11880c10307541c140b0307800580309006e410440406503941d941001d200e0384448190a02d43c50603801001121030b2261104040c0b104d21628000700300703c030b4500404042e089a0319541000c49600c07040010b00425201d503020560348030304041d04515094805400038103041c58512441e0102d107008010562280c01150030259840041c40d0480c090720580c0d0008209104200d444c405c1c0c244140c00c2d011010481e0a00340000d10f80e11010041c00c484180841c0c0c0e08140b58030045038486584001e8910380900a0040b1040b40440750788900072104100c845d0320008911442c00e02c02c159220340903541101c4200c0e50100030604613000150030441d401000c513002100081d0b02d800e50381c040c5d0000801141c1100b0f00c2d075072456030390404107816489848000c0004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 873362688 1250 873361438 873361457
    0x5070f0906020c0f0301020c0a030c200f090c090a03030503180312061c0c0f1403030a0f0f1b0501020a18080309152a0c01031e0c050403051507 63
    0x522030302101084949036401020740049080c1400144c010095405070155020020320000360020031100d00300034840e41c0c07404400c1c2080d08203280d41c40d00050701581c6824501d580e40d1415a540302d5440c40ea207408882e003031501e4441c01400640c0344600d465441e000754404000100349604140594490b80d0f96544001c03188101e0020b19441340704000022070382c1d600100116409080040a02041c4041e2190841161501c1e803a0581d600032180d000e10200e0b04800d00034044078880c00c0e1408070b0010243c0045007010a9000301401400541003205d0030445108052800380b0712801c0000071108003181c00c0f81c4960700303c0c10080d000c2d5000d4407440c03000c2407020404200c003602004030001120b0351a0003450030f01018908006a91841010020031820140190021001203a0306400c12041000798001013050020b4054201640085014145032406048214104442180f540c0000503201d00041740303442c1074415039403405a6000034010340705003c0a07420400144140350300032100d030345400700e41 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 873363938 1250 873362688 873362717
    0xe010e101d19091e17030112170c031b010209040f0f06050f03030712090504020c0d140f040902090a1e06033b0c100e13020315240d0507 60
    0x382c8288002c004d0008581c00245254000e50780c108018492280b0600100002e4182c2c0301759030b075042038110300d9040310765900e614100400841800c0c50210690450360070801c2e0184807540b42d0040d0b42e20308046602c07550081d01000000c0d4108d408000c0014002c000c184404041c0800826003500c0304c07030100d45000360200e0185441c0180e941c1d0204014021031030440e039507a42c00b91055020300840144264090003080c0c99945001034041003068000a040c0400714003002410400b220b90f9481507440c04004401d9050010300448094940018000d40d03900c0200f40850361041e519400122200d0802ea1031250000c100c00702a0101e400981e4203008005c030300c4d411031150b00ba01481080c3c00c501c8a10b44075501d1420820035400860010090303843c80c0b00a1808680c0c080a40d903094400181010300c902ca0600e814100040c2c00000d01108500b9482c1c88181e034081c0c42d01c202e5107944200c3c40e00c26200c1c0d40040344000c1c40000440d1200e04d43e00c0b02c4500340d4107405801d040d90003601140700344010b42403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 873365188 1250 873363938 873363941
    0xd0209010e0d02030601060f020f060c09100f0f0f090506120907140603070804061b0f0207080606062517090907030b090604051012200a0e010e101d19 66
    0xc3e0000d0240582ea4a401c03070540308040840910404e60251000d580c4400300c040c0400707031244014131152a030743d5019004011010310b00d00c1c212418440e00b07001c01b14003140e21000c025038046042c28038051140c4a200142d6007a40c0a511403944410009aaa00748400550005028201080c1201c00c8162582100d544c4071140e0214260826014400241507034814090726401500075100080c803001c0b01441c3d1001908405003c0c0c0105000a0800c8805a810407942000704050409070015043c000300091561040c1d00307040f8018450400300004c8611469603610000380e11140e01c040c0f4203298281851070760000d010389807207034850100081050b0301900580788600c0c0001c020030042c2d07943c201048010180500743d4403220080c1c0001190020840d58920101805a5052440d900b0800b01c040e9048452042803030240340b03100307800c2180b40d01246440d41941e041031103a01031552a096819520103941e072228400e4950a44034000303400300900700f00c0c0141204070043e4000d45002c8401c10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 873366438 1250 873365188 873365209
    0x90c1227071517070210200d14010501021b04050c13230a2103050f0c0f0c0f01080a0e0111070f020109050402130608040f0b101d040b010b09040605060d0209010e 71
    0x2000d6009a030005880400030707407050740b00220704012020318615103a02101646c01c0200c500b0305055a81e84100342d09d82c0010780f21401020244010404144504001f20f481464100214003507512000421000480c1c0b00a03202000e41c00b0101503451170b55074240d0b011401060030082200441c1d0b4480714064100f0141510556008400f01404505902e15003100182c00c203c00b502001024411952500c0802c1c00a08003c20000b0051110840c400010740c1082c051042040c0720303020785107500c003141e600a07030400d81c84400c40c000060b1032580482c0c59405440e01c103801d409100e80c005071000810815807a00305129001780d0b075084003140c4890602c401c0744160804469030700a0f600c402c11030f031032107003001c540e0013803084040441043c00741d03542800c1d010065030b0b5039a451001c020103000c14650200c0440c40300d0205840d1449901b81601d41d240054410b0080141d6850006030b145c1550701e5070f80002005000c003074100c5903245000c075003000003504206c1d2558000784407040c9103c954506031702d045 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 873367688 1250 873366438 873366451
    0x80706110f0901050d0e0712110301090f031209020603040c09051302030c0d03020114131205090f010f17070810170709090c17030405090c1227071517 66
    0xd52810ba501401910240c0001d15541135040c4c80f200d464001c44c106000c000c0007018000c44c0106031925900d8820585c0103080034240c042e80c50f0100010105014043c5a010f0b0f40c2c1500f4002a840b180b100070801410f00100042c2d00508008140010030010203419030441d207080608218648070995200b5105901400c007039455400002038902c240b1b01007110202c0c0e03501c80c0c000040d5a075030502c061403140c40b04880d80c080b6402181c0080c414440d885d40e01d05610606485c110385000702ca14002454010f03801c00e124100107402440c550320501814803140b12070b644403030f01c0c1c0340c500e00010300401561044030210451030fa074400c0080d04414003820345282c0b250341c001070710100303041000c1d040050000140564481c0f003c03941c000380c40f243d040c00e003100400150020b141c2e00d504160602400701000350507259000300400c016814480c255980582181080d42d07214292081921134181282e400c415070401805240000501c401d42580d43c0742052090707803034184039840040b06502c0b0f011000c8910 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 873368938 1250 873367688 873367717
    0x1081f0504111e0a120203190b01140d0b090a2003030301090b010507021e040501050906060a120e0d031409070308040b030a0f0e1b031f0b0d06050408070611 69
    0x14800b040c5409182881a5900e802614002c1c402c4100003410851040e4004c04041100a50040650800f840424421211b13141c41c03050000d82c1c4c2da680704a414051107018a0074111f0251420243c7c1c0c1c0094075950180c0007400b80384036050891040341c40e81301024088070a4031300e040c01c0490403041c1e034900808503000180558110307031901150102030261490000c3c104001041200010f0360f4a242c20440020201030301894444000700740411128103070840c070312840c0101704001a0b41c0e100c0342221a4040f0f24501030b07900c080d00c56120340241a159044903a0390180b58035103044180d0651041c02c441c800c01c86010925200c81030078649400d420300016294810800c01031141034500d100a50300409600da00055000f1f80807441e03022102052842c14540e0800c610510410785040c0000c82198000c43c00b50901070300c0d00f0010011079911600765510941c49002e00521640ca04000c0002190050303001c0c010361800349095900e03640621011a01c06162a251405a04643e0300340e9a103071515400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 873370188 1250 873368938 873368963
    0x2100509130e1005060a030804030b010e0a0b0604090207020a0509011202090a020a09051210020304032d210902061204030809031215030f011109030705120303070804140601081f0504 80
    0x100040035044c001c1ca42a00640e521074000006125132000b00015809003003030f1902c81d410904640b4001e80050641c3d1003081c10559072800d51380c4c40d00700300c41c102c4040c00401a0703105494404206065410381c0540d9101e00e07020000504860241c00031804540b08030781d92121603941007501c2003203000301014100058032041042c407450800c0d00d14500e40a11820803152035180c41c40b028800d80c0d000711800c8000072402441400015109001800c00311a04480025813034040c41000300b0405500109641418038401d20316850102540207492441d00a800c0d00d41d9180032946600b44480140c408400041d25a400503a02031400b1050383c00f105140900c0e004540c40e054243d803829442c000310580e15004100388550007100921038a500300d00c3e90b1300c071543c03036007020400c00d0300380011540001e0050f00e45051003007406a000c0100c030351101d26030074030016036151780c01d00607032070200315006908038880c03a4008554410b00050300c40d40c142030840555030300b421180501707003690030648009150012011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 873371438 1250 873370188 873370213
    0xc180f09050c030c0306100e0601110a03020d11030903100f0e0f0a030206070516060c0e04020c070303120204062024010f230427080d14061309050a02100509130e 71
    0x400381c9409c840145840d80003c00711041d8682009490b000490141e07200e245100556500a40105100e5402c90051405d0803802c50100e80c58200d10126280c01075a92080000044030981c09000e0030321b9140304480c0c0700d254070030100d41d9503071443e0003c2d001f5205030400516418814021118090003290166030000700e166203281c0641071b805001d200340800908205040e417203520140c868160740400402c4c07071501c2c5007006404d10801c20168507515004000c14000d080d0051082c1e1a000512030000075245100c869030b505180c24261103259004c0f241e1812228811380303050050603107410b150b61031401590781e403001c5503c9082c009401c042e0000b0580420b41464564080d106190140c1501c00b4a0110282c2483c05050282001c0b5460400807034200c807661428800c0d42000400821410707400c0c00d00b080016a00000e480906285030f0701c6050030420002c0034000910443d44c00b8082c50100d802c100006030582e080b0200e00c50046401c4202100010b2030381c0130b0b181050a440c1c0207441c40301000e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 873372688 1250 873371438 873371459
    0x20c0f011b030216240f15270203071701060201140402090714030112050f010504110904050a080a050715050f060607390e040c180f09050c030c030610 66
    0x400f103025441a51a400002113038128000102070944041a6641c0074505c00d0703580e080b502441020300b80d480c0303091901e2440c03035010705000c420355400100e440d07030703144094500d00c4451f03015210601d41640080140f29105400542c022441e82c1c500301040210ba807100341c103d00305c400180d401e14001e1100c0c070100e0054146091100e401c13000b64900072803c5504842ca18a2070b40c801c1e404010f5a0912024610034841c0501070588038000036802407099080c00d03140c001d1180c110384019071041c40000701290030000104541100203600c00c0c80306032228111500034007181c020a01c2552003561aa1502181040c24031032248103801e032400141030794803004203101803500070080880b07a042c021250a4090303400c0840d11040818003580203204038880401c24000c008030742d030003455000e240c1c3c1c3c144000226200a140705403440340c0100c2c403241c1c8600f61848060400580c00032800c626020844050050100703031071692600582c12a190764003500c3c14507a40300c108070707502510041001401d0000c000711 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 873373938 1250 873372688 873372697
    0x501020d11132c0603101a011202040b0d0b18090c0a0603091a07140d0603020414090c040504030504170f0111040e1605091011190807060f1509020c0f011b0302 70
    0x1404650250b01b4058120048400251101441e2500c4490011556034024681e055100c50180e0a60800b07140070780b89400e60061000140b011a101d080342d00640c4c45010541c5000e80305a00ba2070321900702004016199010703801914010440160081250740c001c0c0190380820380d01146080e01d010000540c0c280740c1c1c10103401c40d810050348071061005105c5160144c030fa88280480000b07002c0e032551040108036040100400c240c0302c6580c0810608000c00300e1008020102a140440c139591186000ca075584500c2d00418102e007010318802101d00000696004c181000e600204404000070380690128040c5101d5090080c41180c002020078000f01d8807034011612720b09145040c0a40e0900154001c1345d03a4000c0d90000d00c5540c0110f501100400c410420742d0a4541d8201ea00030342500c880b03407288180d0901234103060303c40c103101d0f03c101600d81c0180707c4412132042048586031911500700107507102a1119510b0704c02c82a0034180401c0621a000c203411861480740c10040a01c034055010313401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 873375188 1250 873373938 873373951
    0x301051e040b041103010e010f0c1701030b13060c020109030f0305101809080307021b06030c03150d0c080a0308010503301e0d18031b0501020d11132c 66
    0xe04d010a100d5134900740200a200300710407001180070aa02c004000854800428140400000711802400d092801131054196070300214030705c0f10b40da0764044010310340500c1040242828a02103051540076810340c44001e0a62095540d0400f2040508084043c0c4109441848070350620300806c003c10742801060f020919889003000c50b101d440c03038031801c209420464005d00960414400141c2064050100c90900c030803c403206800c508054044102c42c2c0401030040f0149800c04039a88642d83c0d480c0103541c031040d440039200d400e032a1141c4c4490f4454040410032404104c440c0f00200f8903140c0400d11b18121400c030416209074442092040c03404c4118074543c0f4034800f83c20401e4601c104500702c9102003102ea003c0350b040c0d0780c601d41603185040f03e82d01e61244110380802c248050000e80c2c0814003c040100d2040d00745d0b610780c0c06061150091240c40440c228651505c152040c0c01e070701d004040d08400905035034881c5140d07640c0640e40100203858843e10380c095448121800e9080c40814402d81000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 873376438 1250 873375188 873375203
    0xf08090f043c020705301204140709020417031204060b181e0108011404060c02190c0807080604050a02011d10020703050105071d06030a1103150301051e040b04 70
    0x10b00c0712654404070b0740482c500741c030b05802032045881100305030b21159010205002d5507482c0301100c4407540c11079009200c0d00e21a504a004045814003646500c50001c4ca8520400e54000982e00c0741000c000354054800d003610560700c10441d8004941c080190348002940f80000005a95550b840000a25203441100d512001850f01d81c0c12020207104200d11500208440701701c50940324401940d564416404081c03140c0c1054103540c03e003c03102c4010743e0044c0d80540003040ca1103070188103a0034078280345860711500d1558000310050000004070b4800b1a04018140c401e07154030340c080356499101c00c0340d0151003940300040140065109a9950f01c10082c001c4182080c8440240022800c000003852440117a00412040c4207000f000c0c42129042080c0e4213003040030f141e2203d1004040c04965103524803070400880000d0400c0d06940181292040c0c3e0000f6640c0c0e440d2041c600c1d00c2804c404075419020b9843c100001d0010b00c800c03810102404035040740007900d031740d40d9a10b984440400501c04c40c0c00c030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 873377688 1250 873376438 873376541
    0xf020604080f070e0c03162001020d02191e0e030c090a0504060501140a06120e06040f200609040905150a0218030304060f1b0f08090f04 60
    0xd0505000405990074240301030900320340f52074030800d00c400000c5d05240c00c84008205210a04184044407842a90941419000001e444000c1c513482c50310b55015404d00d500000300d9062000250b030090840c00b560b1340c2c8814402d400d0f000704444071224080e06011703d2410b00b038407005417030143c0260350075107000804840c00ca0740f2a001142e00c1c0803094400c00f9a103615001031100300407a500440713024200311054158403041c00c600003400c2c10070b103106000601102c15201d8001c20002e8000442c802c402a0856440b802c003481c0a544004402c441910625442031040e01c040307121050303207040300100031306180c10710381884c0801006001c000c1040303c55120b030908003080014100801440350040c0d001c0140ca5801d9007401403540506400e05501c40c0c0c008200c14018140c0100f4147c41042851502417200d8101c002464141000c1c1c1001800c40308480307001c1c00801c000c0c02e0042581401c00c0c1c0c1c10203400e200c10801d01c01034610030100183e80d5004103018906070100000c4800c031a5111904880b40c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 873378938 1250 873377688 873377699
    0x70e0a0905010204030c0501200601060c03020a06050c070c150806060a1b0c081209130207050703300e030a0201030c020106030b010e06010e0306040b04060c090e070201050f150a030f020604 83
    0xc81c1e01031780c0100c50520010800b00115030304101c503403030489001d6149011444054280342e4844805001d03420501139070060b85000d0520030410740011a502c06800c0200f03007401c0b08072030103640248408035441448904003042c042044016100001c60585030400c0d01c0d180e400030006c013504544080342c02c208c03c0c4502000c1d500348601e010240306004540c0d010386c980c01c3c10032060510305042c0e80100d0601007040901c2c00c6440d60b03000076001c5041c1c07100c016100d0b0001c0c6801c81c140000303a84003812440d401c00030310007800a01e180b06031007820b02e4002100584603011080d10808a0b001903550316810000c10340e40554026009441c0107a4a4400018107035125902c130944a1004c2e0002c4003407130400070800100d96004001c4034130100e0210011b01c0d50740b4041c1d46089607010014001424903071034800c104c41c00d600580643c0d0180c504403003064414640f50700001d009203411114041402e02403004200d90080100c0701001c0d50308064400c95155007540c54003491003094110407a042007041000050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 873380188 1250 873378938 873378941
    0x13050303070e01030f06030b0408181e0a0914070c0309050406140405100e010311060418050901051503210c011d16050a090f09020901171e070e0a090501 67
    0x3180c16191603901a040c10301c00010300b260340520183c2d174890310301001400401d45130b4801d243e2242c0e20240f89d9659040b0003288074101c03040c2040d6250043d030742602403001203120303950307a80b60319005851040c9150b0703903458603c0c150b030b1201610480c808444804200414842c2d15002482d502a00709018019502c0000c00c049501c5907200c445c2d8181034140181092a140c015030350824003410304000420b0074500803084070346062200520b00c0d03804500c80407103920348109580040650520644484035804032000140c0001c60302c040a035440c000014403104060301101d0100303403001c0c0040502403d084800b0501b0103c0140c5403061100a202d80500c042e000d0003038042c4840008040f4411a84e0f900d0090b207006400c80f03000c40405034183c002d00c0907840f2034000104460b414040071480805107400ea03002003415000194002c0c414000120b05000300c11910421044848100d03841004036400d242041010483c0c101d0300794100c2c40c020028003503008801d503086980004001a2610036070740d07490 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 873381294 1106 873380188 873380191
    0x10b250309091a03010b180705130509070c0308070f1b0f02090907080c010e030c0d050f0a0c0e01050f0f1509030a0c050913170313050303 61
    0x3414410a05a4001c2c04022030801480b01c514102d60110018811072a01039824100c1102c207504211b290040408008a414400d9468561044480d50301104840e50040c818803400b02c0c0540d80c0c85181c1c0d0081c01c65840d40c1d041c1100b80c0c0303000307804600300422500c1071150781c50300d40c20141e4001c01c1092115680c0c0c0b2010401d2003091034114000b40160380c02a4010540d0010004030300000100e500640341c000c4203c0c1d6012111000440c2c2c207000c8080442e030180c1065245d9820381c28002c4103080706900c91401d070b400c0f202109021074906038821000395213103444c0540c1003006900039856103001d44410303245c0c1003018601a0204201540b07850380b080c013680815503590701a11000b0213030360340d040008040da1a10545400e100a403013556005480c0f042d003130440862400079141a4006c419580090f00610313088200401c042c2503080108400d20f42e031020300c15031000510900c000c6 = true := by decide +kernel

theorem cover : BRFrame.Cov 873201438 873381294 := by
  have h0 := BRFrame.cov_init 873201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 873201438 ≤ n) (h2 : n < 873381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
