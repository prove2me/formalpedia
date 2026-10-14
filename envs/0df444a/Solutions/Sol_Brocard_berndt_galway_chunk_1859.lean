-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1859
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:55:52.661033+00:00
-- url     : https://prove2.me/submissions/e7f1011d-8b75-4a81-8903-985bce65e476

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 334172661 ≤ n < 334352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 334173911 1250 334172661 334172711
    0xe030307030e0304150f081003050619020d0e070503100612141609231e06010207050a0335070213060909050f1e03180f09010306020c0115050310 64
    0x28081e200b03140f4102d640b000009400c0000c91f181c04100ea12000c00c207400c3c405103400054101c0d840003000c22542c0b035950400c003400261900d001404c00c810b24403548143c82c086240d00750142d00107001409145010b2280f900c0900d90f00800700b10040c138005082888503a034510250200b01000c60b00d000d036580c140320950080c0485981c0c00010b82d02e41ea00d001c01402c1ca844962031344c20302000400545c0d902a1015401210105ca402c29003c0701120680c1984000629150440c061a0400162629801070040185108841c048155060340080039200004144003c034000c601e074020301100e25100c802c4411198054586103d6030038140701070710142202c0d51001c50307818501403041c0c2c203000010518501ca800b40c0c030142c07501003038071140e5030340b08010b01d8018150a80081001c2400d2302001c007840100c82d4800303030009010401401c000b4505200c00d070f02c01c0d14420f40014a8400c4082e080c40b40740b0210391400c002040b000d0070800440d03074845403600040c0c41282d5440c041013001c412041d248140d9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 334175161 1250 334173911 334173929
    0x90c1f0c0f0c0e16020d030207030203120603070b0403140d02010c0f110c10030e06060a1d0405010f02070b090105012405181201020711040608030306061b0a0308060907030e030307030e0304 83
    0xd030510313184200c1a0141a09000d0050080d4602079031010320a00880d40d506415034021414202c00c011500c00c400806000d05505100d202d100141d0a00c0d801c02401c0214007072041060384200d000ca0007810308035001c00c40c208591404140c1002542c02a01c8091200045d02c1d01080074490701d118240350100b032020065020440c1a00742292540c9074110405550211003034030b104c0c0e180d410a21003a0750241c016401c0796100394021445d00c441e41490310ba0310a00840c000b0800759410148071040b6481410f058450203090010008804424000c1d5801403900f01003103110ba404009900c10f01031140e0348000200900041d0710030108c09040e449030502d86005080904403d40d4505040c000d40c482c2034125094203c02a41c2100b0b841d09100b15821254200095869940e880c0c00b0400164400551050758950a51283c035444000300600c42281384251502c584d5420300d01c1c01c102d40b1000c000c205008060405d4191a4203010210999401c0b182c20f042c0400c4190000141c3d03411400365170001002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 334176411 1250 334175161 334175189
    0x3030c0708120f0a1406010519050909010e010f0b0901120203040609050715030b010207050307050f010536030a0c0306230f06010801080a080f070c0806090c1f0c0f0c 73
    0x141c4500d4043c4600030021040100542c640c2c0c0744010800b0381080382c0ca240810014071003c1c03a412444800e04102035800d18103a0f10b0041ea000003c1d0707508c102070304110401c04400006000741d030418182040585840c07141e031414004c81e980024030303809102c00c080d8070864011010071b04210030358000a6400e5808005d40b034042e40c0711104e15021643d100b466200290500c41c0302c400c654004039004040e00d034007402500c10f840c20710301030059800752203411504005040110100c100c507011804c400b00000007580c130f0a0081c0101c0a542100116601c1a129070050701c084000181d074000c010040b04d5101c1000700c2d4880301c100c81410b054001101119103021550100184080c4001045105440980324542542d88580059603075092040b00100121400c00041c1007255002016149c240d00c210a01030240c1d441d6100350342440025110058540e101100608c05031500d100a40518071580c1d04907480c00042480043c0701103004040907042d100001c4004061141e184001c3c40640348140c00c07619 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 334177661 1250 334176411 334176421
    0x14030705030313151407030b2b0812070c1101031e1e1409071409010612060b1206040b01050913110706140106021009240608100b04050a02090303030c070812 69
    0x4030025040b06c44000080c584118100b10740380c4500d5019490081d0b1180032415144a02c20910441d801d82003514524418020341e0f0100381e8200146200b0000769448500c60032580c0381411408044484450606040c102c514045203003029014095010040011075400c000310f0303002000c0705a0700d0150b9805420546076035240d660100c5403900600c6010129904140c0d142d01c803144680c5450a410790004200c80108a058414602c001d59450300c45000541a507803061420702c00d03840560306401403041c440401585103032904c50382c500c140303080c2451407a250000d0700027060020b140462040f450754503d02c00c41c401c0480000d0741c41c482c1d4041000c006032020320070028003405092180c00014072070500440030442030341c01807804940d80b0084068020b002c401100980d08540c1d109440550b50f6803000059440b804c011200c03100098400016415a2402c148400c1d50002800c0003056401000000600e8a002084951042c1810710741078440446117018502e0340b181b035040000480140c0107201d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 334178911 1250 334177661 334177691
    0xb03060c070507150c03050a030612060509010f0504050709020a090b0f0c060106020a031704081e04060233071b03031a0906010c03180f0f031403070503031315 70
    0x22050718001c03800c640d05590350350900c0032130304840d41341d55001070081041080028080e0001d405c01030038030305001c07640c6601c846070000403901440081d640c01d500c803014407043d03c81c28401c28502051064080c0b0507403400d0380b21035944000d603120301e01600380d000450b860a10b116080d8180508a4000b5440e520003401081c01e00e550032000c264445406101d00002e205400042c16400950b81a160000201c02041b6107409001008000b0f55070003c04000b440c805008182c51510707000424242c081d2618101003000785414039001002d89030100d12643e501c1203100071070864203202d8400006206580c3d40100449a402c0d0300c001a2011440e814405410180c140d0005103d45070805071010130190b01c1002c1051428054840d680850904991a80400c1c0b00d5031801c100b241c240c0c561000002d03a41c81808200d005107031300c0102402c414050034001c22448174140d48107240305000860800c022619815282d01c809003c1d485111b1800c00c1b84000c1107408201d54054110a400030400034030510000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 334180161 1250 334178911 334178917
    0xa1211011d030702090906010e0402091503060414010e0f0601090c180303080103021014070609050102160c050a1a0d1505120109060e010509100e0c12070e010602071a0d0b03060c 78
    0x724490f4017003600003280441c0001d0810304aa14095440c1401d8807241c007072000788100540503806804503407103a0341c02600c04004c881c1c000d502c112281b4135000b5504205a00b140c0d0b01081100064000e1030083c1804034001425905443c217000000404a03c803010940300c021031008040160329010a000051540060b4141d040f28000d5036042101013000d44221202c181ca41605441d8940501000c404201583e120420640c0b181000510b4000600c0030522104085e441c12640809070030020b000e070b81000b450300001000d00290700351188620105000550040382c01558405686010340b410700c11140c0b105000500000e8048e1092140c400303a407034003030b05018030309440031400c126140b40f860405100745807003403242c10041e0454080c4a22400064a0f42000b5588113200341805000d46036501c030b0700515150401d0740100801843d200c1d5405650b00c1c160300c40383c00d54010b6a41003110350800c0800140901010031103641d80c504810410000b491101c45080d0540300e45020020300c1c40b029030003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 334181411 1250 334180161 334180163
    0x1050c0c2d10140c0703020a091a0909030a0c170f0322020f040b040f050114030d030603030806010c0f0b190b040b0a050f03100e100e0a1211011d0307 66
    0x5940d9101c402006000c030040b54144920009111041020f2010300c5200241a60f03004460135503240e2070b6207800203a041400350b001085865950702d03642c214100040240d280700c501c180c030707406094a0310300401c6441c1c1c02030003600c03014000584861020000c0c2044a41c5c22980e04002c5107444180b00d03003d251a03604112100144d50000c140441e403120300180380c1107181c960040c0101400c03580c1c10280009401d03014042c540241d1940e502c4445941d1038015203010306481c5007d070355000441020540780043c103040d11800c1c58502982800840e40c400a429400282030a1040458050703151603125401c03c403002401e00c140380024802d0000045005160b07003d1610018010240c20104010031510700c038250a41c001e944001c100410300f032102218503114001815500394200504944042d900700443c1d03410711382c0010604081c0d00082d40300781031001000800821a000c2d030342d07131129543c41c22010408240100403249608040c001d4010801e0441030070303001000103036180491540c0b03401501c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 334182661 1250 334181411 334181479
    0x5040b0a0e1c020901090b060d0207080717030c040603090f08030a060602070501021516021218091b0a030f1b0915020d02100209040b061c151401050c0c 67
    0x507030076000c942da000c03281026800501c01c04469207017102d4413000780b025560003508203000740034007011000e8610140001c10b000d4017210350340e5601850003c110849403040780b254400140140800c140002007a138060b10b185046c001000c10301400c081248880d00c03140102103035400070030400b40740f50a411603022580c258003100c0000340c47e600160f0701c0d00c0480429155000a01d400200061075030750340c00b2103a07515030060710204a00300c10040c01d6a40041804042c6002e108410501c42c180302c1036181d88214600c001d04042d20804d0340d030034030350b10400210008054131058402ca150781194007070350170115040458900303034000d5000075000d8882d91003103171910b141454041070b03d5400030414503086080ea40c09880480800c07041a0002d402c400100c640007a07850346c01c508181c40d07003002062031480d83c0010301e10014481245d4003d840ba42041c000341001a80010406048159004150144242041034844260f02c8005207059030215440c0d5109644d000f099a4524041c24000201e140000d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 334183911 1250 334182661 334182679
    0x1206020d0207140114071d0f040c050a0810031e0c0b0a03060614040812070512040e0405190206090f040f02070b040b0108010509030f0c100e01020409060504090f1205040b0a0e 77
    0x11100180fa40400c07206c45020407041c0e252140441811358800d51801070090115a404104001180c115003001031350401203040020050003041c1c00141e1103500540304040350002c1c0e815592052012800c50540010741c400010f881e908110800035504003030f20079451255200e10b460300009000d46428810000030600a0b0b00d0100e43e44210307070840302600e1714480105210511500c100c40380b5800f00c0c2083e03803140907104144d500298404000d1009103101000c0340b03114246410322a092144c1c1007181c880c0090740304403900050312000d0640d48a040c1c1240d00c03070035408001000ca030281c002056402841803000502c0d80400905c2c0e841c03907010b43e0141d40d5510f00340e0b80300c0010302d00f207513815590860203500522004000c4803000c8014006a11100300f0303198004c1503040d12605440801c00c0d0f0350500d94010600740301740c0e06544910030082404a40500004a40742c480c00e0f010300c0d142001401031030082019a0996001e0b83c02c0310004e105000b00c0c6560386a800034000d0603a0348103c80107100f4252a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 334185161 1250 334183911 334183931
    0x110f0d0509131802010f1202040602010b010915171806040515130503030619090513140d0905040c02010915021201050411091216030602040806011203091206020d02071401 75
    0xe4407a00c100780020741c0c03c900c0c401c2060b800555a15020020013401c0089146d5402108a1140040d1000b03084540000ca0300f036103140009040301046401c018405161000d5260400f41d0006030b01c4601844c042d501e43c1c0503111001d90002c4402a400d0743c42d2548140020300080200c0003510340d08120a0b4440900182c42c0ca8590000c01120148007801aa00c00d1020412900e0182e0114241c0409403010051540d503498800007074600490f49115220366007140a030511906040c0c81d070401d08124082d2440c4900c00360702801000483c01114051652004410700d418003d41c00f841409821191203001003000310b0180f006540811411221111240c3c0005130034209806426030904429412a0500c40720505100220014005216041c0300d0740c82900b043c951010401000303107000300000340c0d4903030400700290300d002c00690180c1d402050070720750800030960110340e00e030594428440165910084e03080c02d4010f40200300c01e4118080c0b0024400d0304110350003501d031607519110b0009000c0d100031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 334186411 1250 334185161 334185199
    0x10f020c032b090806010e10180b01030e0105011d090f0105090319031503060e1c0f02061303050f0a0306260f2b0215070c050f0715110f0d0509 63
    0xc51203401c107139901050040c800c4421192005501c405802a4890003603a82c1c110140142c821014045a841e51807858070980d50340340c00b0f6000c200e66000000c0c4002d5142050041681880788100c41c00040a580130075100001403001b6594540303484000e0259040c10010592289d0226291700c920841c440e010a54980c003d000f210030b03018640561101541c550340b5044060005014030708543e000b01452800d1541c502d0310001111040c55a50001600c9400c00281c1350500c06044d040205040440f44000260300404440c140207501c54440d8a90100b0f920650240c0010342000c82c4030401c40c1030b03101405002e480d110410000140855800d44507014005403903868605101521080e80d044200c00c100003401e1f052144500d0b441103c03a03010105404088544042e1414800250030042c207600f0b03c142000708a459601210186c08110324050140302e00d0b00c8448001001d00112900a02800303006105840044e504ca0041c6d0b85803180b0a1802407060b40106240c41c4907800f0305030f001c107100c94 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 334187661 1250 334186411 334186427
    0x307050601290a0809030c06070909060e04021e0d0507080d030615020c0402090a030204020409020d0e030f03130f02030d0c1b050112050901090c150e0915010f020c032b 74
    0xb0060445191480000048404401c003c0040031203120400043d4050702040001d644034a4070f650710081a5401c010713030403058480e44e81c003e10046d800513003030001507620001401d800b0b0076150381c2072500303010000c0810303030045440a010f041c6018a04000510600220790220015504d580401405403078500c2c100102c8400628400144c1c8030304030608007818070782e004080701c85004010715155903403940090180d82c85508800581600419102d28404050242c1401a0b1403034024504014140d281180c582c0070003094007601c56a041520010b00050b024040c0210380c003d03065900704000f40e24003034044104c1081c2100d0307141d8190341c0b102c00d41c0c030084128001d40d44165144004203800c0300c0000040c010180810005550b03490b43c403000145400242070080018031501030110741200d0008d403c0d40309187e4218029041e50041000405988110500e102d8003428800103078128940200d1808411f485180d41503c40c4483c076289000300d00d40c1d10f842c0307401c52104142c44045407440403541c0700 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 334188911 1250 334187661 334187729
    0x6010503130f1407090f060b3103080712020607030608030f0f16290103030903151d0c030708030f0301030311011b050c0c0f0f0111010e0307050601 65
    0x1621a4805000900760040382c0d0030039401894508510010100654140310896001c40055a540c05400e610790307495001e0a4010150700c0525428407a03401c3c29081c1584a007664031107441c91030b003800740e5500d1420b07041401a640205405840c4c2e14203103440151000d1866002c1c001d80310700c00c0094103a0788640240380a59001802842c180420100a400b20307420070b40d10411280c13028400c2e82d0061140302c06ca059204c0c0a60748041a02941c90707601c20314404600c0d817403810841c0110061001c80d800100d800100e035408484c146003c00394400b500c00170100b0004040903a0306c4081c1c068525440082c201c904600e040f410381d0101e50741c03071210760b81e82e01c6410100d0032501c0d4240010001b09009194242d543d810050000c10345440708032000680b200000505000714402040100d101c05040050b507070400e1098691548201040000a4008121810040c10000c5c1d04000c0c0040c002c0a412200e104098081120f882d801241b81680c3c0b02d08090188410009990010150700d8800ca4050a401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 334190161 1250 334188911 334188931
    0xe0601060e040b1206130308010f0f030f030314040b061e030a1e080c072d0320062703150714040e0f07140403150c1b0302031206010503 60
    0x441400018000541003c08086502c94100013115204003020b02c00307284100311015001801130002d00e4090001c01040c2c000c400c038450315131f40a00184103a03001c01402e80c0d8100800d40e00206481c45c089014002010503888924400000d0000f000340341002e40d4050402140c3c036005480c0c0c04844221544243d4804680c90783c860701d20b10380841c86860707024082d10b03003003180c1c042d0b0302400d40c44000700c90348070916030461a800b400c0b0401140322900e006996412005100099920302c4000010a41001c6c0c040940402003400c0ca1922075810380070590034042000c2c010300e4440030310141400301f03445e049402c80a00400121a4112843c2c0407581e400d500084006001058445600884010b100c81c0c0880314014003c10020400d000c002c4191403254149040071450b038034003c03900502401c98191900c0007014184002d00005008011074005c90000c4000000c0d02c95003000110f4540003505290300200000d002c0c10803c0c0740c0e004c00108840d48411031740104030303181e0800446180c40129640601 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 334191411 1250 334190161 334190177
    0x311160306020d0908040b071a090606130f1505090702072d030209250f090b0d2403050d090f1715180705060408060606030a0609061203030e060106 65
    0x5410766000e490466240d5a0020702c80e036040d55540c1c1643d0058001c0001c4c1c1c1c1021039040e080010f281c3e0784980b200d040501000560030a540113580e1024098400c512031700c41c90b0000340641105500002c50100a280d00340a60111001114010030341c42c01418080d04c40c040014203000e0002078404110781e030b000040c21220504418000084d80b4490b50611180240341002015030350f02c0075900d001e1100861090540c09500d244200100240f1078080184460168404101c0340c101123048103c03060350301a5035440071607a00c81e00c0146160381e0891260090804881000740062450405480c0b1400454804000301081a00c0c2401ca17485981400c0c0410801401210340d001c0031041114125402c4882c03c82d8020301c0c0e001c0440342225440c100c2c03072070448008040242049240e000300703001e95010307203018200f070416070f2107a800400840c00b621f0300101060f6801d8190303000f60002e0921640800140f6103e000216003182e07040c00903400a81032203004032701c007500803414034100e40c02c50b111000d03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 334192661 1250 334191411 334191413
    0x3090f050706120f0e1e0c09010906231e040e060106020d1101020f07030c0501021314030706030515040506030f0111180105090a060e04020f0d020403062901050f040b0c010903111603 80
    0xc0c14a410741900111f80901d0f0b01444058441d4608075018040000001c2807181c100740c44103800030991107074580d40012a030299010368850096442420030100492130380c0651890108018054101c1c2c441840e2140074000031300301d9804030321001030002582c1c640d45440000311440e4203030b005001e11401400c800300301c4400001d0081a510a08910500016040c8400342c3d200802d0000c4540c440d0603903000c44c0046807202d190500080000c9c0800342410881030130702c0704900007103440d1848007030f000b2552140819403942d402c2001d00140c0c80324100034000d40385581c5540c00d81d40c01082e00311030540b100f102c184241e90f0045050f51862000070b4038071000ca41c5420300032541d011100e80303d00e0b0419801c00c44211400b100c03d00034119819071000159886103503280c0242150380710107030309404659500415500000740902e030b400000c1c1c240380c900d80b10920400c2c0c0949910403075005241110740001c0c109014481900300d045202c0c001c0c0c40e9040e005070b00b204080d03155030703112200041c10860440148 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 334193911 1250 334192661 334192693
    0x20607110414191e3e04050d02011e021b060306030d120b030d050403020a0b030402031c02030913150b0a0504060c110303070b01090501050d02010c0303090f050706120f0e 75
    0x1a1070b00c4141d50310380301d04038081007085503080c0040c40b80580e41032501d03181c515200c00a0b0000d4503d10201218150100d03160f02c031046c041c6024251003505200038503419688100d01002d440803807a603843c5510941090081e40e1100c034104a02c041d5104000070039180e14140c01600e00c502c2014002c0e00790110301200450308210b0445030088104c0d640c0c00140f003542c808004150741100b86032280ca641c2d6046004200e46203070f0f9076220656501c42002000b0060b10089825220114482c0d4a0750200520302c806174158041d440001d50401204040001c0c1c41907283c019491501c0c1090301c1e088003d80301c020003e654400c0500900102da4100030400401d4804c03400250b89038000c1e003010700700044080020b41103a00154054502035840c80041c44483d08612540d401441e046440c011440e4540c0d0010304001c0c00c2071806428583d50380850b40a00c000210400b000c01c0d4400252a801500d40c0740185c0000307100c030000c1030310624003502c08403004881d00c42d5600c50340d1240018046e903e0510004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 334195161 1250 334193911 334193921
    0x20c06070b09120d02070c080a11060c19060506040c0f1d010909020a021c050903120901180306051f0515030712060b0a14033102060711041419 63
    0x100c4072449400f03020303605110410094055404c8135a0003582e15400c078249416074a090f90003103502508060501000030b460301d00c0c07102c010741c03040d908242c455103800e50b11b0b8181111140711000001401c0c5048040120325030040e4446c0350111010002c1c0c3d85140c20450301020134a03400d1002c1992440c0208182c1034100d11007084820500d82480080c0e1155888000c0e078110500a40241e0322948242d000d0f01d0300c412041c06800138074034010741410340c0040002e9a81d003103182603085205000880080a9214006001c013101080190400441d900e00c0c200004120488000c3c0d80038183c018008a0900680745030022180010300c84a440000742000b220113500140c002c1c1c05000c80004042c0c5d40e032844d8014400200034414682d03448440360a405800d1410105422464410070410800ca90f03000c001042c0c402070300d50b000d803021108502d2000c1c516240d04440690300040c08240c0f802009041800401042d6050b1003d01c01a504003450800c640e2051b0f428006001d601c901c44800c04006d5400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 334196411 1250 334195161 334195171
    0xb040515180901020d0f091205031b030c0415020f1b030a0b06030307021f2607030b01020111070501050411030a0b01060302030403200c0102010c0203090f12070509010605120601020c06070b 83
    0x6107440c285c400351400702c0c1c10803600500c030691207403210401e0200711401c1d00c69030203090400f28994940301c2d5404800c80b0301d1000c1014900c0e40400030480111442055074040c2c14092507a001d10148514081c3d903c001d0340b510b0280b5071180b80d018001d0400390a4021105000181c0207206403486070b95103600b40c040090413181c1500c0300f803250001684c3c5e00c0b25001408000301481a10501449000070075801580c1c0152001c20500185007010641040b5a558001d025103030001e0502c2e49000100e0140000007034403410f41101042800902c0819030109018500c9130302c0054180114005250f280c1076000d10107000074401c14010085a400b031b400071948148249021103072081400c20508400c241044c0c40b880c1607202206241e0107580911650800703072424001581490000c0f0005040c3c00f403d001020700070302c1040d201c010003400801007103001d130034014000f841642e16140000d000c1d4108803400c111112103c0b010801c19400481c0300301441750b010b424685480c0c80c546861304081e0300a82 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 334197661 1250 334196411 334196413
    0x310510060f0b18040908180103140604090f081c05010909020d030c0c030605070512180c010c0501020d020c062a0304061802032d0f06070309031407060b0405151809 72
    0x118504103030382e14800e80317241c2481080410303128000a000104066819942035060526103a1a00c69601004403c80d0348650103c0b008a00c7da41c003850410010344a05800515218001c14100c005020652059480010040003003119a0342e4401d41410b40e00e01d0403000c0d400a2122032481c011910034482d0f001c1c2c941c042d414103030546543c0d03502c0008480040b14604002440400c1048880d015074503001e403c030520824003001200300e4007125460f44000000030781800b221005000c00c200c403c0d011750760704201000c0115210074a213034000b074680d201251030042c0306103038104400c11a80c550201001e01d00240c0f00090455a65944100080500b141c0d84c2d00701c00b4019842400507030b410000341c407030140251400100e1b4840007a8103031010500104527103a5800400c21002c0a00740060000e502c2103951a010503c41e8030ba04040e00c0901c0180c0314010280000a00c95040c84038640026880c00020382e1300300420340da200b40d01e01c03e84502d40d6180e07070310404400704e8540b51021000300981003601c4e40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 334198911 1250 334197661 334197697
    0x30f010b0903032209060b070507180f050a05070e09040305121909030c0c14010203030c070204061a0c0d030204060c0f060e0109030e03070501030606080f310510060f0b 74
    0x82d00d220030507080030340c13410284245602071088403038030f029070401000340300c040600300703140c1c0d40e1901c2c5c4034070b01405140043c0c1486660640c4017011a00700301e84074522600204180d040682842004e0001200c489021402c4c040d2141001d00f0171901d514882e1341c0554a40d402c0c605064419204a00064445a0060344081c21607201214a1148900c001d1081d00e644c80204020f1501d01d2039030f10150b0002404d418400e00d8658a66008022290720218100071103070b850b035180c80001c009000344d8200f5012003200c9619480c2d000d00f09c0000705540da12000454211445004e07088003648154091203000400c1140708000160a1450a4030070900c41c03c801300707500c2400c0d101c4c242155001d80c015800100d1511054150b41400d2280c10060003003072034240140740c10580080c002410141540300030040d5a000101c00e41040741da01c12005214100e07851440d0b00c1c0004441550a4650050700c0342c0c0180211202e245249129000803038084000e451061031410706407801503005901c58114081c00c01d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 334200161 1250 334198911 334198927
    0x1e0c03020a120f120b060f0304020604210b090d1d03011409010c110a1214070503030103060b01020606040516050d020d0e0a0c080a170c030d0507030507030b0105030f010b090303 78
    0xba100490903200b0a54490360070201c80d00006200e00b8501404c012403524141580303085071110f01c100c0725051614011280e032a2200c2c800306040c1c6c4102d81c0a0000c07503001c3c40001aa02109150302030220340650000350b4991141c0c0141c2e502d65155004410104442103120840340043d201243c907188030044c0001110705201c01c981c68120803c4601c0e044607550f9802c41c0704520b03044400140b4070501500140903100ea5640d50300304810000d40481c06010b0a08c50448400700c6c284d08403000c09502c80280e81c0c03a96941e00d4180d0290410041e80c40c050700030600010001d00b0981b140c2480b80106519500c0750050408064450364420780046004a8003005802c8145c0224001c0518207aa1003005208100c0a4184414070103515003003040c29401180c0444041903030780041001210212200a80c0d030368404605501d18030480001d146224100b20030089890742650110340b0500d099103052103050014001156540300490f0031240f0b0408110052001c1c10500307020b0190f841001d01203d08d00440d0b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 334201411 1250 334200161 334200173
    0xa0e010815070c15050610081b07080c0d0503010303030b030c01122f0306090106210c0903060c08010312020703020607061a09160e0d051c050d1805010501061e0c03020a 74
    0x310a04040003505c60060011909103400d103c0d003201c02c240b601a1a0341041c40b030040380d0072041e481401070814007260540511203445c0440d1308030000882102c16800b000c80b40070348260024403050300400e10308a0301302d803d410045111010000c1c160364061000e491029046c0c002c1c20b0f0f1980824400c0144c2614400c03c200c195100d00c1c0c4110047c0c002034581c40c25008015074082c0c145c1080c0100200304d1407150fa004001e1441d48140c45c214580032a41005085d000c0351541c0480c0d0000d44164100720440003240c0c2c011103114180c034040c10112000003246401a0f81d0380b0007510000350800da0810100001c601594080e00f5080d5960313a458001e0342000d0000303041060240c071071300160b00f81c00a00c001c001750021601c46801341c080d948029000060749a154032213a441088051421440d58402040e6200704101e40610501400400114507031402e00c46644411850803180c1e50729080000c94224012036080070130316881a2940414040d11108841c0310311640750844c00d42c03180d001d440001a907 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 334202661 1250 334201411 334201433
    0x50a1b08070513090b1e01090b07080717030714160206160503190e03060112080a111f0f05010b16031101050403080a200f0a0219050105060a0e010815070c 68
    0x5200d404c041802400f03001004a00c080071070303d0307224035050200e0482090740c00000c450112180003003107a40300c0350705080c159082c2c03041140040c02508103101e005904440c070000f0b1405000d41d9924000c408003048540703000e41c41900d841074400c01f000c1c0b40c0000141b8000d0000c04c2c40240d40e081c00d030004070b0740d503840d14515040622444208892180845a5030344c0c864014461034400300e005010075450a103a00c50b003201c00000c0602082c00000d1520340d8030340155042804000309100310b40440c003c0c0c903165030a801000c40f829007014100702103002082824000d0070705031442c0702d480e1881c001c0e019482c44445d0b401b9a200300e040c1f00d842091500d1701c44080c0304031072085000b82c54004180c03a20421305001c0b544d003504c001440040e9020031484d010401030603101c0c1003400540a50b42c138218410b040e0701e82032000c40180001d004d8188014104201034010701d008081c2941c001d0721441e120701f0f44601d10704d001d000d030700c1956102c68003803070346a20542c0f1416085112800c003c280100c880d118912100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 334203911 1250 334202661 334202669
    0xe010c0c1802090d0521252118090509060105040c1b03030506090a0e0a03030506011107150305091f0c050909090106140402211506040602010f050a1b08070513 70
    0x28002082d085507846d80d40180022540200c400545002c2030741e041410002030510310250f21810541c0c0c214100045289101039030400002001480e070368428000300322207540c0c03440701c64030304240c400010b410f10b090091900a00081c0040d0009030700380000d1000400c000030b1254104001074403e41145003551408180860181d500031846152410038018440400b0b003402c440b15203040360900c3d048030042400ca00f4954145004901c4e9104c2c071004030382a0f0f05400c0c00d1440350007103481c00aa4490002c81038022000f25860601980d520785c00007540314a21800000310399034002500c0c04400907583c1c400408050a8109281084e44010115082800c12545200603a645190070b1200111450100010980c111000d614007a180b8509207008240e07007804602048094010a844040150380380c145442c000d045c1949403507861000030301804c000700d81604101c0c5460003241800d0414000c0e40c201c140b5102080b006c0994080040700c0074440200b15008024051012881208101c07180d08020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 334205161 1250 334203911 334203913
    0x311011404080f12030105220b100513061e03112b0e0d12020c0c06120f090703080307050d0e010e031e180108040f06051003030e010c0c1802090d05 65
    0xf0b02c1102000f50714024100814241e1900140010400d80d43c40100500c000c100b11402c0405060781744114902a044010342c0d00c1d44680952441034006a003c4003402c0c09000c40004040f0440e501d4a0980b50480400983c030100701c140070000407080c2c02500440040e16030700c41d42354078008000800c19080c80c940c55008400b00810600342214a9050041015018500016101d81da458440c050711420075042511032140d008106864202d4061110a4461a014007410340c2c40055100c0a45524001c4800c290400610000b0039290381d80000d14805881c0d20001a6203580c4545805840b281c10810401c02c88039200c0700007140004e000c1c01003443d0514a000119258100c0e2640042c3c01c400c1e07603101551141c4203112005580d80780008941d004002803c11000340d40f554141105200708800000e89014102001d00001c90450829641160f000b56501d80407a82e0b103400446070061600d4025103c90100a0180607401082c00c10040c1c1c80c180403c0141780600703d5022510303500d1650015502 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 334206411 1250 334205161 334205173
    0x11060313050d1e090f140a0509040804030203100506100c05190506011404181713030503071505040308060405090a060e150105010f0807051e030a050105011b0c031101140408 76
    0x15841e01420703c00d8140d1000c0c01c100009608044201e041811036114406054a16000072091751700c8a10b1719030040c0070060300c111842c0c5018100428564010b10049020348180d00c002d80c40003155200d0203014038002800e841c555104008101c6040c0c03089171058441c1e0141c078010009035181c10130321a6002d403141005d007449615140c4415140c0940c40c203800d008905080040050081c0b42d405186616481140d56007941e6000110358914000c0440e0180d006168000220501c0400000340031101d110b801e517034100e440790103042c4003520b50544008000c10342a6011940b649041c2d005613901084e01d02c00c55039081c0003916000e064071507a41c0c40145a400a6042050a41d001030400e40900700030f082500b40c06180303a20003405901d004201e101040000704030009200e04144900d40300005040e03c154a03824041c4000009000a2003498041000c404c440b000086100001c81d01141e001858443d216103143c4681400e01c401a548504110841d50399503034440c3d002000e0005041300c00020a1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 334207661 1250 334206411 334206437
    0x90201030c020a08041701021909090b0f09130336061b0305090319080903070501140a0806040b030f0a0506072c1516020f04050411060313050d 63
    0x8950001203448110f4101d82c100c04045880e40049404031444901c901400809035613085009000d0b540c0e84c0220a002c0020b4503c90960003003095055880780c4108010b01440a001c10400d24402d10200c6d41010320500050703c1d044800d44549080c502a052264000780c2100c03608200300180c400d07a103982841c02260021100da0080140054100b6003031000c031481043d280c10758020010b500090412400042c2c01c0c00f541c5091040700d821645000740d12031a08583d1030b040d6903a40041d0700040c003d01c1621000103040d07121388002d00300b00362500201031070709031015012682404010700c45500a900d9510400312924200608101d1280e900f014010b280034502d8480d042100182040040080c901d040c0e0691500048801d282010f0002841c4200022031001c2248018060f880e001c41d0580810741040d480d05c1202e103040c2d00b034405c1b1500c00c0c540f103da10412048400903600505070f528480c18241c00c03810540025a0848000915031607119002e940b01c0d0314108401000000154124640074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 334208911 1250 334207661 334207667
    0x1090609050903030403080f0a0b131d0d05161e210302090a09090f1205090f0d151107060203010305010212070302030601080415060b0d2301030c030f08091201090201 73
    0x503000902d04028501d181026180207103c2080540b81d141f80015484c003003100100a540114565140a08186012841c40034000c008045102c280d0019621b0900c01c3c4c4010740022840403e1300051341ca4070b0381030101c400010340040036000001c9500a01400d0f00d207080f004074400c844407a6102d4428a0980e0320108030b101d500d0450080d24006040c0140980c5e001a030718070184c03109441000c0c0e000540c1d0401428005c6940c0038084000c0c2904220385004204c0c02d0344140200320340402520190032850a003000c1c04201d11810f440540107210411072084080f404da04850080015403240c80d0400c41217849500c1264004c0e8400c40302130f0360001c1c041002d2981d090320568040502e00b011801c2d840c108001a00d0308a00810042030307590a10300c150507078503043d480321024015211400340c403070159886140040007070215003468105041c00c0310341284008210581a2503000d20268101c80ca15031b110030b001182c611045441c44018441e825036511203414068425901320004141d03416180009 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 334210161 1250 334208911 334208921
    0x6130503070e0705040b07170d1b0906021005060105190f030f020c0303040605040203030d0204030501060e0a0903090e070c0b0c0a0809072d030605070c1b0f030609050c030601090609 80
    0x203800600d20210400a0003600241590101c1306c80d140140d0352a1528a440710030003c0180c210409200041200800c01041e903221041c444400a500104204250b40944100a0611511006030310100c44011581c1c0182c00030398000d02d060503c68148890120312142c00e4585d4608000001c045940500c00740d9454082c44c1c2d000382c80daa40461410300b02c1034145489100051000d04102d8031540807a0446d00c00704102c0d0070103601c0840c02c64079151a481c01901904052055a1804440e02d011649006ca40d00c1201c40aa9054682c1840f6a103400c0b40c41c001c40000500020510120040000100c0d21740c0c081d5500c18100b000103559601c201d46006001c0c00006010f0819561000d5800d0110002e15026508d031040c020b081c25084608a2400404601441d00002d00303007800c210074440c03569000075031040c7c460f104210504444040c2d0101a039a4421446025020002804c0803c08555141e10040f8114094414ad8500c0d944000100307181001c01c1e400f03031404d43d0342e42c40b0400c0400c405100d2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 334211411 1250 334210161 334210169
    0x71206050f04021c11040e0d03054c030c0509070306080718020702030709090b0a020702010e010e031c0905010e0609030a08030c041a07060c0e03100e0c0613050307 72
    0x1c0d145241059004200c050035160704103409a150800460305002d140c0c090140c03070010003001070085460403110701d13440e0906656000042405c003000f05191902c0741c3c000c5442c41551100e00c1d0003200c03401100681107103100d0111528885401d21103001c21082941c8040030714003450039142100d15060910445207002400441014502101400b80940126a400403512010021110500202c12010082c80b56100088d40341c03042460001e580207041d004040c03500d010b4007500c00309580300d04241040e8407561100a0000302c0e1008041455030040d69003a0204901504882c0a14180c99848111202c03080f1020302091403d91304000c0c07580d00400407014031005071909800d010403840400e540342c600740001020300501100080c10220b0741000d403401050324003940f01110100440c095030f290300c03149058902900780a100300c140c60182986504821000d8018003045031615000300c01002001130348802c0d801084000003a6503181d070050040550410b0110038518600380402d8030740420303070780 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 334212661 1250 334211411 334211431
    0x1090e04060b100c2604090204080c0405011a0909130b07020f0c040903050f0918010b03010f090b280f03240b01051602030a020a0b120a0b0f0d0507030507120605 71
    0x44094000781c0c80700d80b440c1100c150b03403210f172241046100780920301e40296088405071610215000902140001c0c0a005258054804125590306c4449545500b01a8242d0f9a01088100101c25282c01c060342403d130b02c90400c1000da50390b0301da1036807502104002500c0450060384088070f80e100b0f4460610448041070022142000080703290b5030081c08500400d100070070003150100300e9043c5615042d50103800080e0729030145c805980c540c020954030390828010741e8440d800440010621640350301c1901100c0740d0050902003406500306c15403c0420160703c1d0602078500300c842c0050b220401610140107544200c0708801c6034034105e02107071a80404002c514001c2d0342021004a40c0b40d03000011214142d1802900120100071400402c3ca0700001040c0290440b00c0403030002480145100a480c20846403851f05e580347d150004500c3c2641c400c41085588800da07441106038500d01a0701ea100c0040c8a00300b560905941c1340c07145400c0006030340c000d98005054032515001c000d421702c290780c4c3c07200c40c0b41 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 334213911 1250 334212661 334212677
    0xa020d1406030c04091703041a1311060306040b0a060f0305130b0103080318072409080d03022203062c03030402060d020c0d02010b122a01090e04060b10 67
    0x1100196840401800c810700840d51094094240400c06c454510748100c1d51403225524141454024941c81c00305006031030038880d5a0226204d1411040707900141038101c3c55051204d080c80b007c115207903001030900e86c1c0c0103569001a02c01600d440c400b01c1c0080c0669103810201003a00400a801da4000802d101c255041c2103404a000540c1c60701d00a040d25000b0b194681c8030760f150f0000038002802000c6401c1c1c5e0740720f00c42c400110116180342d100704aa404150100001250300015101c0000341d000301c80c542e41115904070311440c801d501625100c54800407030211340030284c0801c4003084064005440a07602d8030200b40c0c51505001d81e010702104500005c0110042c01200c050700da020180000780718010011b903d0003811426010b40343c02d05aa41c082c0c600c0300c0350030310010b8000c00c03a840045004000000030380ca02c1080200d01e0380020420f09140351004d0090440380380e80c0ca164001707000d05000c42c1e00030100b20203180020304e40c0309034800d090010f040d612007010000c81caa581e482240c2084080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 334215161 1250 334213911 334213921
    0x12070f0f0e070309030c0c090614010201020a0206010e0603010b04020c1b0d0f1203092301050a02121b040e1f05060a1d120a080d0b060901020d0503041a0a020d14 71
    0x1071580009603180014141c6882e01e011030b1108800354000e0b0411031341c00f2000c505014181e011030f08440102c2ca102101560090042e800e0b030041c2d040480150700032100401003004d20b01e60490348560028000500c5095010000f412078100603208421940031070411a038020312016a2985640120340c00c0e034010302c0a070354466070b49040e070000a00054204a8901c403c0b40240c200c07180c0554843c041484114080110580e038034001c0260780320035828000440c1d500c00b1107108030380440035640d56203007069454801c54031140402a03c0211042000c10001a00d66007090606020300444403100041100c13084000e500c070354054000c03520640040114021454006e00c0c1040341041940d664a11490b1010000d9200c241071507595215005400601007000fa510740109a000c07202c250420065074000240040c41c000d10001501607070040340100c11a6009602842e8894825403c0e580c40d0019030150481d50241901e510b41c0c4550040348826800390340d40652409840b035200341003498588 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 334216411 1250 334215161 334215179
    0x27010c020307090b01030f0c0c02030c0603010f05190b19020d0302090609090a0e0609010905060a09050601030b0c0c0313060f0309031e03200304020108130b0708070c0212070f0f 78
    0xb610801002070b5442c008a074090340030790004c58038206080e1080004a0711907501404030720a07040100c1c402d0041c000c01041500c1c080055078165500b01d030254a035142424140304541da15140c5c40088040440400604405554014078084c21404051041c0030b03001080645000d080c40720082c18180107000042c00c0b030f180d80098034104a400c4590002e281c0b640d800000044c80c10103d10741c0140901010003411030b1054015a0009126504035136030390740e40107020011034003801001000354006200410201c0e0400000d59005404000c180e45070017802c0f4645c91450b0300c40354101046c12310b4800304002c07043c2c01ca40b20110000c140d040c24802c1c0c643d03644d00104203c0301c0c1190b40c160140e0107140c02c10498482d80c0003400b03102125040d600c056502d2a00b051341900b0072a012400941a000002d8a003550644030b01c134403030340c0603410810030340b550681035a0002006103c403080080d003405000250741d400400b0803c03601c0b002e01402a0908000d0b01c82965803150b00130384800012101c0030021109 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 334217661 1250 334216411 334216423
    0x30203100e1f0209040903020c0114070b150310061509090b090c0f0c070e0604110c12180d060f0b030a1a330102011802010e040509100227010c0203 65
    0x819080442d04600d1088440d1000340501400c0c07540151810021901701500000c0b10351188800740c072160740c00380210450000d14800c0d5403004204440792004030304088061a00340c0700c681001403d0b950380d0050709200c002100c1069000d0903007007100000d44500250412164000f502110909111940007a008600200c901170020f1886500000f04451030814100c1600c0100300300300181e0700d1107075462a200380106005c0d50304900c11460411000d0f00300c0103800441e030401302007001515040001d041901da45402411800328000712001d0400000c0e50340c3c284248009120399070008903600c01100f8201200d12404c0503c0c026403080c628280400c1c47d0800021221614100103185c0e80d4440c00e0031040242040842904c1840c021910820103801303a9403525111002c0e402000644040c00340e0380340500300d541d4080d01241c01a40402d85030f00f0b00c0c2d08401e90082e9101e0032107808412208885040340d10020301000d80c040301c0328084000c040c3c10b04802052000c24a804400d90b41580c00107510b070030b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 334218911 1250 334217661 334217683
    0xb010903050a171c06090606090810020d06030804080114090c030304030b09010e0111040611030304110906010c080c0c0f0a0605120711100b090703150524030709030203100e 76
    0x3282d41c0c030000710342d04410440e445400000945000c0c8113a008124000d00320718001d07454030034149180418094841c40d00b010450b06014020030991103e003030300034002d50111029240d85900c801c004004518003600a1006100200c0009082200145035281201010b010101c154025003941019aa03001041e81c007500d4100c1107103e16070300c1d90000780c0e0040a121100642c103500346040c2e00149181480540120390054680c4102c0140c48103029840e840b08a03402448621051401802c5050400d4455400041810a1110145a501c1e4129660445048241d25500045040050b82400c00000d1040d94003a00c0003e010383c103298018006e80151403a0406c12040034000900c150721491001c4900420b45040d1920001c0344985580600020060300740240d512001054441d44680310301406031890701c04892800b407e0108029403081c0b2420b2422000180e0410566031220040080d809582c07a6154455000c0c0b4500c1411304200c07903030100340c1c01d04d8504030000c410010b0109018240b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 334220161 1250 334218911 334218923
    0xa0b0a0f0908060f04021008070c0f0f230d090b070f02011b06021e0c1e01090c08060a0e0a050a1b032301060510170c070807030905040b010903050a 65
    0x1810000c0012506036403940d1200d2030300d100e1035080c06038070410245050b00a42c000c0d50040900c80c2d603000c007070b1050f0000350740c1c0c540001c0c041014030010a400701003c10180c0d2141c2142c10308440c603900c85800e01c442085c02c40392028001e0f05d2805511404000c00c003603191260425001040c1740030080700280c0900c0d280648401e144c0e034000340031a0700c0b40040c0880046001d4101c80100c0850400500a400410a071100b251105540180140b580b40a646034080e0003001040c602245d030414441d4950001c504002540d220862640000e112400d01d2000c0c212810041c041407519481031800c0e0b6042070540c44075600300881010200d0000303e84402081c5d005a01c0e0481c0000e4130420080d441003d920142c0b0701949107200c3c1c0e60300f00d200841c6841024500d0000e10040741c41d10300700605107144117400341c0841d05061041c0003038240c49440366442810908910301780aa141c9483c03450758040d02c02140026402c41082c032031072800d4810740d4001f84003845c000d40003034215913816a8860026101501d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 334221411 1250 334220161 334220177
    0x170d090b0309030f1209101116030203040504020d0f050c03100909020f150c0606102304240906030908030a0209280311031203130c0509041a060a0b0a 66
    0x100841c2042150111010b0f504120b60701d4000c5030b050000c080d021b48600e104c500030071701d0600081015000b10504d00f405800350700d02c0c062009080442190000c01e08405500090000007519070f40c40c80640a00b4850311008203020460000b22012560010003811910800b80288415644100740300703002c4d0b131081c0c070000034000410b00028401c20000c01c0d24540c004030181454140c090154007911405424504450780c80c1c8410040102d21180740c1c42410002d10303811000e4520f0341a01e89490384208983c81030791714160b1105003001200782601280c045211040c10b40300340c4258410201d1008141d1450100b0841c40309a4808142d0312014100f0002035401150b8080103039a56256002401c060401c10b4050801190f041c070146440b41c8401e0b1107561381c0b000c2100c4c4c1401d0108441d03940d17101d030000740f501d5076545820000c1c6810b8620002d50307082821171800f0410b0303212140903174003c90113211040f6401a40c54840388000d580107241600885404404004015910055886050391420000a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 334222661 1250 334221411 334221421
    0x3140f0d1206121505060f03030d0c03110301090203010608010608060109090b130f0507091a12040507090504060b040c0302160201050d0207081c0c050406021506010903050f07170d090b03 82
    0x5001a500083c440c0c0c8107820711901001319041e0002e00c43d01d891802030080b995804204096403a03408038150309a0070402c4408107c01c4198818028444142400140e4446800010320b030764000b40c0115030369507800401413150079044260b0354018507607880c1c050050b240060001b008000f8604c1105100c6490300c10341c6480e581c0b8680c0040400560840402c001c09800003440040e06d07064417004003040301c0020110340e00d407540c0944145140d100404500d003660207804149140d00c010801d413641d000e4544045906055401035502460251001003042c84240c01008100d403401c041c44010316104004d18043e5405c103010801000d40c09003400d40d00c4104800501c2e0203403269003001031103110300140c0300c00804408400300e05014400b074002c0091030794400065846210750700905000d40d102007020344110b031b500001c240c0d00c108180360400090ba903030b039201c80c50306001d10300b00c240a40042d0f00c14410900c0c00302c0840a0b141c00c0740000d2540071018180030304062040d005042d101c141c0080021 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 334223911 1250 334222661 334222697
    0x7080703021e0603072c0906150c10020403020913150c050f13030b071b150219170703050714030406180f141501230907050403140f0d 59
    0x4040c4441c090f101c80e0b0740c1d20313104200904001c0425402e1000c4002164003200403a6200c5074401e240c500034002070b0a945501d000c0141040810b40c0050b80e040e001c014210f84000103100e01014804000d0015845504510401c949003000400501c401c003080500000412440043c410310603046110000c1c901003156822100c0d03210700300d28811a58000503e80076403d110400d02c0b02101d01072101400c160b29142021100124800620710a00300b20558820102e0400b031400c1e40000e0384e4200051138688040d4a0306004509620b107175010a903c8099240455070000905a10260602d42048145881d05000d03000d081c80303110b401c2c840200800010200a990b0380b001121000c400c40f00308030038280380b61004038060881003c56060485080400310b02600003100c1203014141c20510300d940e030030500c40101024100c0c00c200340d0301d41e01450319203090f140c04028601500316561055625401c0d8104101802804500d40710b1540c4804c2402c41c9142001c10700403200506481c14026910042c4004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 334225161 1250 334223911 334223959
    0x9030a0c06020d030b1c14101503110904031b0c1205010204170d0219020d0209092104150c02120118020a05031903050f040e0c03070806030708070302 66
    0x4240380c40040d0302258042c0c0020714507000c000e032541c00380150140d41080c0590780c00e6520302e20b0200b1709141408000182804034481071414103030102c0d501c5941946201041d01d07040058240881c500c00300178014824800b050403180841500d40c000d150620780d9004140140c840e098003840c1407040260000c015442c0d80c0394000b000c18001e50b610820241c28202c0c000e41c407903c5801c124401c86800414864004203c0c2c0c3c1400e0301e02e4010304140401003400d5130303000c0620324041781d1004005268070016601c03545201e019840b82d4006040442c2801c80c400b1444840440e01c003800c0f6800d000c1000300580c00000c1e5441b40c6060b103045600308030a44045a1180750800f4020465401c0400c000003a50703482d0740c40504030740216030500740b055507101415291a00d0801c0741140d042d208070700c040400c0c003e00081c145070004c02c0200d8906659402c4000c0c4240080d602d00c420080c0c00800e02c100316600020894201800301c0103820000d2810554603a40d40480c030009019140a5a405107480880000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 334226411 1250 334225161 334225163
    0x130204090c061704030203040e07030207050109050d0306050402180f0f0303030a09020f010f0818031b0303010905090106180507050403060e0d09140307030206251401061409070509030a 81
    0x20511028119241051261425004510020b590694400d24900b6085450f1380620f030150051803405040030745150404800034040c0060580030440c240c0000d00c00d2140794a4a402240078103244101541c00509881807a40528860340c0140041c0080020f454803ca9640c5030894515036903074240f0b00840d42d92400d5107540d981c980004000c000250445411038500c2610840700c0c1c0390340c4d1841c24015500c00740c0f807900c00310002d00c031040081c4000400d040051409080c3d68201da042909a0f5201200b04034404000f070500e810200c0100401c1000e03001d05900f029201c030092005904055808880a0101070364a2103207458101084000740140b040f1000313960412000d010035500c0f5445070356188e04d00c802c24800a00740c044001100e202c10f0f0040103580e42e0081c058410f040c42d580030041301d600f0040c0360144102014002d9204c000c03210b1014004580b00c0d00314600b80502c0014002d007102c000e544015015541e120b4103107651b41d0303a03141803984444581042a240c40c0000080ba24200d0104c0c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 334227661 1250 334226411 334226419
    0x4050a02120706030b06031006030504050a021003060819050a021c06020307030204170109170c10020a0207050a0e04030f1b0203060103150f0905121b010501150e060306090109051302 80
    0x1526040301200400d20b00c0546203291424002d4038812418007140d1b00c0201d40081240c5c21150082c00900d01c039400076a000f038025000c440750b41c59a9000141c128550381090004a562a5820868104144030039103c003080307070701008018007a030344540c2c1d11852504000ad10922003411040d2000ec010402250015003041c1d04644902d4002c00140003580f150184105071a143d041c1d04100d03c030140220701030341e075018016416154140f04e0740f500c10b8002000700c1a039030087d01081d07184004544041c3c128061168002d12800d40307800c00788001410a60000040210040100000300c0d4118150b0b581c0c1d14064580f40f580310200c400c0b818490804410001c0d0316001c0c2900010500402c014030b009a403c501408200c1c03016414601c00c2250350340700004196410080c2c03007107000141036020340103048290540c1c000001441d41c1031400c4503001d130041380c01d42110710400548642d0080703030344140c22029200716145d400c1c130000203581c0c901c0512440681c00d8403480091078445900c1c0b041002c86038064 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 334228911 1250 334227661 334227679
    0x1060807080304090e1015030303061403460b1303021f02070503120105010e0a0515070c210303051513090201180f0509090307030f081512011b021b040504050a02 71
    0x151007d2031143c0234030007540000c3c1005008522824010102581c0c80701c014010001aa0007080b408032604000010810064a540c08034041d48580400a08554072811801d00008110300c2d0003901600d0242001c40880309280c1c0290009800241ea12030794200c1c041c2e0440f1201c00d5084c80e101a00c140f100081142c0404207500c6540c0c842414014107941098885804104244081c400d03001441e2181f980d10450364101e030035200c02100c0c002c2100034002c402c2c1d0b40c41c1c59200d4107041c071190241c040300c000c0400c0d4a0b001505051b0315118403900955401542d440c026040c41c00919101a40103010000982d03410001c011a8020415121260200201121401e0b500c2c1d00c5501c104d1558842c01b400385110900080c4142c0c03006c000c4980e03c3e507064881a00c5060720440459512000409070011168542c9841069565004c2c88c02081071000c4008581864204628004070052680c20350940d400341c00600c01a0343d50301408100c0d100140d0b0700003982e98480c18a18038004001c6400303500aa036030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 334230161 1250 334228911 334228931
    0x6110d11070b040608330613030501290603060a0e13050105090a11030102090102030313050a080721080114102a0b0c0f0301030b191d01060807080304090e10 69
    0x10004910032544041440111719005440c04160040841c840d01d030380c0c0c9600011355462802e00003919408c802c42c210800d005499507205800c4400e524518000680507a10503060249084c090700c1c07640030180c031024207500701980495082c90f000d000301441109400c00207051005103024100c44150000000e00090911070070a90300c42090075010354414991010290090a050088030310341241a0300079031860b0307501c065000540d400c80d90115800c4c0510345040d4040313221003014004880c042d180c4c0c88160702020041c000703444900341c200130520012000400c600701d06007140c846114800c4e10f80300715080d5915800c60b00d014001d60810800101400007100e85c03c115001402c0c15441002003210b81c0c1c84902c1c0943d060f000d0b00141d00b1030340b03401300010300000b104202d5003030b040f504030030f000203400d22034134061000c1d2100f003510031010382c00c001c441141242d400d006a60003031016001425115042042141d140d01c03550007001e03122a11414004220b02c0104101d03509018900c0c4100566078070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 334231411 1250 334230161 334230167
    0xf020307061d1906030203100f08010c0806030a02090705130509040b07020d020f06060f130c081015020309041d06100810020c0a020910050a170706110d11070b0406 72
    0x50004919003444040d9201442d424101005041201d000031001d03001441d09000724041d40c0b00420090b18031104000001f90700d042450050082d00b0140c0c004540369841c144020100070000b03140905c690b201d50341c0c00000d80c45d0010b5803500001d1324542244c2c0c40b0061a151900000c866000d1500208040200020b2002078205640a00c1c869030036070f6141d84100340101d94072040e18141040940058000c038109160031a213030f100314400580b41904c0c0030090341580b021180307c5840100801e040e8805c215940c0010200315015002c8a2018211510034050080d47c9018858295006a42d952000649154070b40e02202041e400a401c4130301901e0022420501c2c0075180c46000054443c407403082130442c5007070080c0c80180c4031900c01429180d6054003003101007200503240d081003509071200441c0603102e98034080040c0c0000b60254843d10003840d1168940021307940003900304000c00100c0d00040c44080b41c902403c40d031501d030100000550354607050400d2030651261361000710000303001a130341d90 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 334232661 1250 334231411 334231427
    0xb0a11160b060310290d060e0c0f03010e0d03050402060909091e120304020108100503010501060306080714010c0b090106050607150e0604151a040207050a0c0b12070305040f02030706 80
    0x2c801d505503040412620354200c2a00c02021101c07542164031300d41e0650b80030790110360a490080060886840f01e8041d10361004403041040b1400c501c0d00110940c0303140b170414201c0c00284c0c8100760020800d41c040c0d030917070503269850314004104060301c98000c107042d59111b8051f900e52850041130307071846060030780c00f49590302506500c844200c035040014042e984030201e200c00c040610750540d90310310359480e801100e80040050280d040c91a8084c40842e003500c0c04d1203039a0280c02a43ca0004045091003452890515158044000344d804241080c0681c0d900028988111394084900030351601d80050160140c859a0092030f00840040350348014041004a503480341c001002c42040f0711840059019114001103401401d19482c8003489082c3e0511035200c1c01d04040e11803250100c0c51ba141d80000d0699111603826180d40d400a0140d109001802d000c0400034030204d2001d500d4054656045a90600024032010a00d90b60340005018007002034003400d4001d60090984144580b904400b4100d40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 334233911 1250 334232661 334232671
    0x703031e06180501030506070c02041503231207060902060c0a03080a0c0804050c060a030e0303240307080a030509011b12201b01050405030d08011802070b0a11160b 72
    0x702d07100c44440303090145480795605a0350070070003800e07860380c8402040e5191040100304a030416036442034661145d98851810002d907100c0d65020590340c00100c100900480c80565032007164025284c4c00e48081a40000c8500c282e42c4003401140f52011400012282e00603170360003c0150044041250070158404c605e41c0c0308520401042051011044003140c0e1000c04881c0249070740d0000003001c07c289411001380c1042d08103454045001c4115202603801c0da00240d80780850f8004000c5584155551740181d1585603070144d00425255180c400300591342c024003600601800000104207060381d105415220316641c8403054810307010f0582c9010010001102ea0340e1000841c5080c50304080d0228bc0c00b0308504400950080401d0501c0380c02121071003580c0c20216044c44810840001d4a4600380f100c25007a990a4a0300180347d8504032940d004800038021241500b48100052800110300131402504a60003150005810081c0d001480107403080d143d01c44103104200c0100010071900c184401d00c10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 334235161 1250 334233911 334233929
    0x908040b0322030e0910050a030602030f0603011b080c09040c0c02031002040518060a150f0f020a020904080d0905032224050d0212040606050f12070504020703031e06 73
    0x501020469450340102c4801400100350082c02061458050303034584e00038001e0010903940b0b03a56180002c000ca001c540c000c0301d1803a000300070044030720510207840e68404002c0c0d0080c84181c407a0000700303160f441c24000900130b02c4151004610740c1705203c01551902c010141c0b00704a68898400d01500c4400d00180c101d11910402039800040d18103402a141114005410040620061000c0203028440109000d400c210400d10004150780d004903442002512a169075900110030000109030b90800541c100c1075511203a0ba40340180c51307000803281e10540001d169500d400401d0340d14005030030b501e80301a00b1484003003061800510714150b0496001800b1228060007079581e0040204244042d00c0ba80082e05030300300380800c0358010700050005000200005180c44400001e424a42d142a902516050707a0fa11050080342081c0d2550b80000c0001ca41d6a490051041e245664440c010b02503d030042d500850001704041c0280c004050707084009030a89048001100642d0080c003044c410700441c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 334236411 1250 334235161 334235191
    0xc010507110601060c050c090703021306021903050702180403021c02011e09020d0f051005010501021606210f0209041104140103020a0e1809010507091d0702010908040b03 75
    0x2595000303010341c100352001c000c040c0c0b0703035a0b2821909443c180d0300c410042d00d0b50300444040701d01c20f030780350400355100d8001c907240140c8801c08884600070035040c9400000c2594082800346a18001281b00c0b000042c1d814984655110380920100d82c096244030840100000c03854203120816801040501d540440028040540c025202e012826960400b200c071326078518641204c42002050340004846034000780010610030b400d6551029982a101e0003a0f03610341200c01a4003048400b030045600401003440140010240403008111140c0c50384105c2003031041d000074140100c2d0a40305550907150100d0400c010a100c0007070b40001a50094480e280304a06c0d1902112120b14440191800d5032056840640140c0c5c6580066009502c504815414011030206916055903100324015910031071180c00300e002d0804030340c40c600b9114090550700500031400f5090141c91420201c0c2c03c407560400da50601c4d40c2e2a059810380c01008110340c050a4002c0000e400300301609144010b6010b54440321140070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 334237661 1250 334236411 334236421
    0xd0908301b030f0709170d08010f05091f080102070f0b01050d03080411060d09120e040e100f0f020301060215070503150609040e0609010f050a020a02071206020d110c0105 75
    0x8034541a010240440d6403052001c903204210682d00c0c144e0003000390818004c126221001c0100703211041a102d00c0680c460403011481c140d0080714540142a80074051600700d081c200000d6000100400750514030b050740004420341005840d00324002c000c450001c65a891150906005119a142064175134010140001825003007100b2104c0c62960503a49046080d212070b902d102c0307200c14064056500072000d00c22402c800d9103521507420b4003482410f03425184054984060002191782c07942603c600d150090140c81c2d00804a80003580c68a9108001b5950b20b220001c1801800081710410079144040004903640784c0004a6208544010350712a03c160380380141200c241c4011901e616907001c8035180c0344040e007043c1000c2c100c3c0e45801080410f814400c0074203030340390403002ca420a806079122020390000d005140f280c0751708007811070402e602d00340d40d50304040c4d030b2034089114058510b00b4264101050000560549800a115250620982d031300d034007008165820850050030385500c1c289c0403036 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 334238911 1250 334237661 334237681
    0x201180609090608030408060c0307032d14100605091908060121031706012105011514090105030613020301030f02010e0301020c0a080c0111030a0501030309050a03080d090830 77
    0x800300c03601f140042c0b9a9959842c12580320360005856401815100c0141c0040c0c4030202d880903051411340089202c840c0c0da00c1490b10203555401d01800c8a400e0310005004015103214510340a030b03402c82c10150307514103050010400507800490800c11648550601144220002c14910704031148412102c89400380400190449a0a01801400302c1d80030400d1144103003499040581c0090141050500e864201c00e0047c00b1104d2526075041c603641e10320043c41240c8090b00c404810915618107482c19003080300c9030707010030321428103814180a00400014803e42e612050f580310300352411015516540c1d03c0c6407100f031681c40c440c0200d02054850002203c03070b01701403090366419000790008145480803511040244d5100300040800d55417200540440e44504038000c1d801020700c01c800294961540c01c0040001115402c41845501408003c0010540c0801941c41c4480d0b460b00010384400f003407801c144103204450103900488427406400c042031411205080301526403841c140740ca980c1d484214 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 334240161 1250 334238911 334238917
    0x503030a05030a0b150a0c05060c04030b0a050a110d0e1b10080417041e0e0708010e100302100804020103141905061305011716060e010c020118060909060803 69
    0x31000040060002811403540d641101c050900040c00c8290055110707100c2013484d41c404864900030966006104080103801c209443e804070039042c1c0b40382010708591f184154090041c050301162a2139401007040e030750995002c0300344460f41140507952040c200041030054082151aa038880c0244010110800c01020a9910007407008001840180452000780e940c100094000c1e54548142c113040c01da0b540300c00d4000d10250072032080060050080124500340001d540d00308200c084440c8041c880080c0d00013044606460380d1403003884280d5984c80c0207101082d000d40c000780d40f22117401c06480c2c07000d40042d0980c0c01a8001e0f41c0038490382038280d8580b11158420382d0300d022420001d820496900b03001e03900c295004800101042c05a050b100c4055069600a800c81c00c2105000903030107480200400030030304217112403a444200c640c501000540049800042c96040c4960b00881c0002c40e84160304081c980195044591403268076514001c0c4070752402e0141c01c019902c0d0110101d0500000015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 334241411 1250 334240161 334240177
    0x1030903090e090a06020417061807210c090b010813020f2106010303081608070816110f0c01020f01060308040504110c0304120210030c0e010815040e0a020109050303 73
    0x19150880c0d10b001c100004403000200f40010700e001e8440c0000004503240010001480304580780b15400e80320400160500001a002007840a0140541c40e011034001c80c00b1011035070200483d80030071003010842040300e12500c10090107040340070804100d182041d48055403426082e41e4a0140342d03103e01c2014001484134501a500c0804e420140c1281d00d0090007651400300c0c000b0007401d00000c4da82c062440c21100b030700708074045801d8100b0800200307910f280800441081d032030802600c0c1000000074012100190180c000015038280064000d80101c00200c6010303280000c0f9600c0300c036140da8168031007058008050040c002e404110800d00b0050050300300741c0fa0819001440c0a150000b080000c0905000003c000311003403010240030841440544000c3c4280b80e103031724080ba40b071310400800d0ac0f80700c0e5415007810f1500c107401d88850340c0840c0600c070303111003820904107035128030740844035502c60000116400350500409940c2608045580b501d054400c1c4c031030300903441d214801c0603264050848 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 334242661 1250 334241411 334241417
    0x150306090c0f021507200c19030b01150e1c0b060a03081206030717010902040f110904091103010c052a0a030e04020d021204021e1e03012307090501030903 68
    0x2d405090b50070361004c1d4010020382409000e908107504024142c10f54000c0f0440203800c40d440c24680c506141d0b01c00801c070841d40a0391142903003542c3e210014004103000d121106080b8403100c140300780c0181d01c16802c040c40205201d10380d4881c0480a0034030403001400300d0702e1a4080700441e0050038051400e5059943c0300c5803a030300b09094010320030400900101076a0340b501c9580000504500b0481500c100100f03090008030b003611140c0140015102000d0340d50011600e00302e4900c071581c0616058440058084a02046c80060760038000e62803081e14411343d0f071552a0078224541960030200078442d03003020f030755002d0606100c0c248880d2078100d004071407800d5800c00708640340004d2280c8207083d0807000041005041481c01c182c56822a00b00006420b940300c0400e05000651400c0031440f103420380e69521000c0b000c0704100100303a001c80c26070b03c0c1542c1c0c01045802c420701caa80c207400c200e0340c0c0100102d4240c0401d5402e00317a070034003500564285010904000c2c0204940d4402c0c0034848200390161 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 334243911 1250 334242661 334242673
    0x603170a02070602280510090c06030b06090d060b040b0306010b0a03050c0c06011701020f030f010315050402030304140a0302030d050a0906020c06030f0405032208070b030f04020910150306090c0f02 87
    0x5c180c481a40b120641e040b0341500500c200025040b00510a46100900030b92851001a040140142c12159950b024078424001031020001e0303903a582038080c04560f072101d00418038510600205003c0c0000884240c0e140c0610b00001c180400c038640603090070b62269030103124544a40d0740c5080b4602c40d4820304100d40c0c2010005000e5a0340c44001000c50200f0040018a084900c003484021500f058801042408106004005000140421401601c02e00800300100d04199000030358074462845a040c898241c89001541d6507a40c502c0900291340141c1a19003403003094800800c103600040340310300400c04c40f820110b074003880080d168030003100c040e10148c1345072500d1855150040c0010011940307403004214102d0402c05076030800c8400b10300d010070410703840d080c50003050401d4856000b08040400a0007084030703211010148a80060301030303c01500316240c1c030401c4007d02d01541c11181e104200d407244886540d41c598403070800c070707030242200f00207600302004201c8010b0510064100164803072 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 334245161 1250 334243911 334243963
    0xb07020603011403030c01050a0902090a0c090501120605030307050304050a1a0304031b020d03110601090e0c1306050d0b090115140910170105150a061b060603170a02070602 76
    0x20882e6001c0e0300c2d4001c0440342400c008001b05800c0d107a003110075035211303a15002018218107140b04000e07000341403c4402d000e00004844c1c01840742c8400d00c111030401c010140b0b5000c00101d180d2100014040150650750b0f603410b2402d0039690b80c1d010344980c1e4010204608001010300d00580c000940d03407455140e4616640702c0e0341f401c0700c0c0303401c00d0b0040c0000c00007861411030045e80d0b41004108060702c691562125083e603501c0240c144041684800409070814840e007a5000010801c2d2081042c115480140d640880340840000c00180e0445600300c06a07815280522407840021481542003200074001c903042146021683c503114410170480100d07012400105143c425002c07135010801100a0003015500c0156014898224800c007980c1e135583c0040c00001d010b41d1001410307c0c48150380c411080391400c94010500c0e4508181c80001095001084080201d160003410055401160816000300d22208100f11980b0802203680544580310700007540d10f0001c140204c0c0c980c4805410b40d450600c3c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 334246411 1250 334245161 334245179
    0x30a050304170706050403020d0219170c03120a0605061303060f09121107050d0f02060a090b07030512060a0e010b0f0705120a0807080f0a020903210c01060b0702060301 74
    0x740040310951103502820741c2956040029000c554054240072900742007a040c044d003041c28003a0800215080070b00900c9039121003501412030305912280f40d40010b040303c44031007001e00a2100004050000080e07034020001c00c10441801f52840c0d660401c201640d420170421580300c2c2c955440c0100744dc0c0003040010503501d0340011810141c0400c04980c10b40700340d0351443c0c0d41303c88400440200d043c41c0c08a14030031600304403680c0a4001510079103650200f40e00c80d1000440c200380b00a02c91a0009044501d00b03110301c2d0080c0050564001d51901c0f01c2c2c8902d0050030641026000a11300782180300000c605103003181a407021030782e03800a40e001e1a42841c03d032141c20750103c140081203c07800c100640010f1000c0082d20114207030043e08076150002454010403400f0060040020008124184840300801890301034100f5094080181e0f6400000013180c02c081004060035080d14161020488004402d0020b2040289120007002266140c1035440000c0c0a076680203034000c1d10502c010701803015 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 334247661 1250 334246411 334246417
    0x1605010804060207140721080f030709030c030503030703230613021e120610350f010305010b04061428030c0e06270c0405030717060a0207020102030a05 67
    0x4010340003d07141194a403100d0102e04c2c3c0304180c04910b6030010008100204503100207000103041e543c2e032140d00b00817549955101e805020040305540c40008081888c5038000d4000d4401544d001d00b01c7c0080d640c3e2820150b03220341007180c0d040e0100b814403041a10034504081d4028070b11001c022640042e4480c0d0060040010b01003904000c0b550342041300030207100d1010540007603942e107400c039642d55008451081034407d1001d452940580b01281c0490f00c156005003a000b03490400d248040344800c2444412140441da841d100c0d010f050b2601b06202000b010582c041c0d040c3c038004e000074494407483d1410b0004961051243c0100c4600154001ca02e0386040300c8000100c0d0f2080b0131102a10070074482c841082801544110b96a41304e86a0400c0800304500c102540103008030b6240410000920300700c0080e640c01d400641a0f40502400a08401c820300c043d42c000c0d0001400721250f042e2540c0321032002840b100d03220641480784400050014130940200c40b402641a8003460420718101c0c3d0a56984d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 334248911 1250 334247661 334247663
    0xc06020d020c0601091b09060e0402120405010902030f070f051e0604080319051e28050a080f011d07140a1706040e03040b0702130c0903050d021605010804 68
    0x94081040021044160010744078100e0110007a21082d40340c2400e10003201c1203000c180c900d02c40c0080c481e000075900000e00c4400c684141c00c1c6040300041c800000790003803003000031080600e04603c044c0003c0c01015817188031030034420b80458000c3c4685840306a030b1800301c0c6c030400034403d44131041803105042404580ca5603c180000000400300d44400182c0c007074125400c0b80c117065002044034400003408800e11500c039a2031f030074194503003107a15560940d5440740302c1103130310003403000104c045451006a00b101e1000c09030700e21201003411244c02c003e1155000c800010300007100c0381d001c07400d480701180c2c10074103d03010b125008001520005039512a100c008058005110212220525403c500c00003020341c808195110000300f840c100300f26910349009405c95019500c0c8c000d512210401c000100c1c0c0668910101c132603213400703440c40040c2050080f440b041c100300c0d082590483d00580c00c0f210b01030590303202d003081d15401d62016030100c1c2c0c0d4007031960503d094091410030422413940035501c520307001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 334250161 1250 334248911 334248923
    0x60112030203040f0321170c0715050712060603020c0309101806021c020a0201140c01020d0e0c011e08061c050307120207080102040b18120609030405041a010f0c 71
    0x400d0740ca103040e281503007040e402034440b20134106444951242041b88500034000c181000c0401c24124001c002d60080000d001640000c4000361000a110f6036154100c4c11980705642403005240c0081c0040c01c00c00589a605000ca04110010032070900a000b0765229841071001182008001e5082000d48051807156909200e140c0003c5a6101b103800c21900144c181c2c1c1d0010b160002989a005840c0c1c01264010421904030350000e100507a44001d60f1030030110b98400064950340c00320b14890091081e540c04501003890480f92840c0d21101003039a01b00c08100b45c1f20610300c3e0a400040b0151100407000341400901e142c800140c0914040e0740011000310101ca800c0c001038500e03a030321403559001d00720540b90226046291920194100420740103010180006e50400e494800c0c015820300941e020806407044c0364070b540c11143c403410381505503281ca010444010b0b013400795035188c81c5d500c980100350203141046207030f429100450740c0b08685030323106035200c51060001c1e5204644140c0783c100c0481d20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 334251411 1250 334250161 334250167
    0xc0108041515140a060e03060601030f1d070302040b04060b07060207061103040501050a0e0f030f0d0f330b04060e010e06030a0c26060d03050403061b031a03060112030203 75
    0x844002d207010103000d40108407000145000718401c101d840809030b40318008100d103402401219440c040782164101c0020b0030f01080000341c40c43c3c4078001c0c10307440110400040408084d18048200010304008880c000c2d5400c1004502800c04c3c40165401c90081048100040111400154166004182c001d0045500240c401e010003198016076006540980341a1344680500c5481642c9100b1070760b54005400040001c95058441113440b40600700b00c58100080104000340b8100603504178180780031500004008681c0d1030b00810790b0812482030886e0041c4407400d0752500d000500d15554040e110b002d91030a0a0501d0408221400c4c2c400c10700c241c0c108445041101a982c40c1c5201030341c0921240a004200703c0b4a19400400d0000d81c0039010311030811300503992200d070711140e040513000704094554002c001075078141914503116540c0300401d802d25207050000445041442041e0f284140c1d54140b000051040148109440904046905801503001000f8661447d400c01510f40d110f4015281 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 334252661 1250 334251411 334251431
    0x4032906210105040803090d020703030f03151703070507080a05071a13090c260627010605030105090105061c0209040605030708010b10170103021c0506130c05030c01080415 76
    0x420b480d4252070031117940001100f030028107407041c8002e0440900b01d10040c0141c07461500c6c010300c42240d071034001007403554034143d980300400ca441500014100e50880d02d140600090441076991f4031120054a0710b004007132002c1004540441c50000590700700004050315820420310080b034030040c1c8400c0c0d03071a00040100788580068802008010711056100107a0807020480c007401660681070000c40420b040d03e4460071103404000b2240c0c02500650312810300007209a5491020340700a20303400b0004022800000d4001d51010003107040e1001036405610f244d90310010b000c814098692141c1e9400c069040310b43e06601d591b40a007145140082012484907078910209082c1100b90300404900d9440343d210b81c1c45070405803c4400c000c0329a143c8401d07180812068621280301c10b020080c8141603982c0310403d00c480c3c50195060280d0868160342c007500b80899030169410031304408036000280000c00042034640491840703182032043c2c4902496907075998410000d070142410703100302c895032484040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 334253911 1250 334252661 334252663
    0xc170115110a03030b15090d080d14160f050304021e04020f040e0a1406030703080f09040f051006210b06070512040603060b070309180e0d050403290621 67
    0x8801e0b6406900c001079403404583c02e00c00321002e001011103a0f4081085a005540c50303000c11043d140740c10403002a20740c00e44107050000f40801c420502144d02488007030000d074090021030001103101d152903108001d108000d0540b03060008440195010304523070001c00c41c001440a140440b5440180010318041c80400b0210180d08143c04c09003012131130004102041d10188100041c2c8480240001c02034580700c00000d0b6110041c1c00000c180c2c400100710041591304078000d441906600a0081c0004142d014143c40107120840b03201011080103c0001501070040100c140d5030350400403540c14440d00c6040444c060b0600c0068aa0071020402210010810911590300100303400402d41c1e40e920f1801e6002019182d89402003035000904200070400039400c100b82200729000705054001c00c84c0c0382c080d001c0050000c058030034500e000742c0c000c034142c044e070010041003580e02c20201d81c4600c2140c58446100c0c00c5500050090305040600030403424502190039400b500305c03500b204120400c61106007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 334255161 1250 334253911 334253923
    0x1d1803041206050109271a190b092a070203030301080609070609051e01210b011b050d0c0503041701060609050303030f011e08120c010c17011511 64
    0x4991000c058048003400c106143c000c160050460302c1091100c45c505050b510440d460810349250042203c2c0e1803101001f03906040800d80b44007131015007102d494903a0001251400c00c44024040510b0b20060000900e003003e1001d02400d820130095030590b001d00c000c0700a01280c2c0b43d0700c00860405100a400607501000207501074002000a00500d080c20400503207000c0f40c40d00f12404ac400007210900880d1075203038006569009079030a10000c82d40c49401070314020460322400c03901009408030700d5104a1b40e500709442c1328800381d032482d6140c0d80700012030066076020800208a604911403841c0b010384104085420789010b1410340f803400d0b5685801402c1c0c04044030400312641d44400c020080d484d000803100d80104002d402861441c981103503144800441401070403035a80005c00f00914400d80d030b40d400c0c00a001010f08644c61200c60307081c0540c0340e4201c80b007400d0b803a40c00d103000b4007038540c45600004101003524050034443d900b426a142d0364607601086000822030b1001000120550070024 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 334256411 1250 334255161 334255169
    0x90603120c01060503190305030c030709150201050f0c04050f04021e04090c0905010c030e0111100603061a040b0a17010216080d0501090209030a0620120f09071d180304 74
    0xf092490142814180803a421800751100d0500640402282e000001c695005603408109aa60f52302c401083d2a510300075040b0f25054441400384425864056000034004c5d143c2100c00f0500d5514001162564030990048640191100b4425025420a500a0107030b540f10084810180b40c1c0c0010202c0c82034005d540800c00c5140c480700300035161038000588601601013841c100381001d0407070310044c2015400200d8141004106c8000d100703040320070300c410101501074060600800d940d80c2840000750410030884241c407070024211600d185094415010300380005403065401a140201ca0b540b024020054880c040d5020000311004105024100d0011480307071003016128074032181c01004540c07058121040329841000301041c1b030b46c0e000404510b21380d40030402044c03076111148000c00706e410031780c0301c3c1c0807078100841c281c1220b0746c5090216100b2486480b2002d05d0b95500d4a13803540d602c1c070314032811001d00c02c661400c1d55003c120030005a40021041064031980422081080c13447e441544 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 334257661 1250 334256411 334256413
    0xf010603050114060306100e060c030d06050301020a0912060902131a040504021e0a1508011701020306130b180403050c07060c020a05090423070f1211090603120c 71
    0x50086035014450180548020700540391440030780c40200e559803101900c801d00c1404100109201c079403043c660f00026030400b420a640b204094021103940b13402c4082e02d00c1381107080600c0441d41d4107051094071003130411030740c44084d45840c0c100d055490000b03119054440c81e0f10b50043c40e003d6100d820911414000c905000180c040c06010419841e01142041c0c902c500d080a040c000982d43d00c7d030a114001c10402d055030350310701000002804561311980022a80c0030300941000c0d10b1034105007900e04a80034400c80580c04101024514200d200171510380340e202101e00814440c40682c1d078040300b00c82502800043d02e001480d081d0603800d0030111411400100002020b01c4000b0003484000d00501060401200070840c6034002745108541e80a110300403103040d0006030501008160400306460580b101030304640781d1103046034480b9100e00441300700200c0c084001840c03041080181a050760400170300403150100b1410040c0d0020040c001c0343d454490070020003050042c450050440c01e039120 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 334258911 1250 334257661 334257691
    0x903060905070f0b070b0705210103053004090b060c0318120d05040b070303021b07031a0c070210020f1009110a08250b030a09170c0a0b1905 62
    0x782e0305a181007600b105440d2081403007480c00290006c1d0101c0d40000f590700f003558503488011580c80c3c801d01c038100c2c1c08272582150703030000081c00790100f81d04220740038855801c4640040c1c10a00668507918040c2040340c0e500421082042c4403440d802034004810042619103880b0840c2c04080c0b468100d00001420030312210074841903031918540c07840928000354007604049010303c802602500903803064003064180080e0800401d4403907412150152020113514081d40440d182407613560301240400c9a166450b000d101e144013080d43c4a10707102e1044442001d1078800d19a0a201a00d20b40c1120041944601c203c0c0511102e010b1100c3c4410280d0320000082060403800c0803038440d0000520180601d0034404184034481010a0f1444c60820107180e011942a40fa200c0420b008142d0b07205955204010080c00070f5a55550000312045010300d240c2e040410300d02c490314041d8803030b04c144440182c0c841c610a80018540902d440c1d03000c6440025119840c2c80381400c04140c42007100c503804502c0c3c2d98 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 334260161 1250 334258911 334258919
    0xd09060f05091906020904020c07061d0109140d1b12110609060304031115010303171b04060f02030f07141501050d14100f020d0c080f16090306090507 66
    0x40d00c16140d0240d642d200508802000c20f010499a4800c542c1c042e0100703400280504050b21660126905c04194008588000fa41c1e560010724600101134034821881d0600441c8081c0d61107190501c090b00e004101d01043d180d030741800c102c082d4800a80403662110064466210901420702c0c030310040034405940d980d009018034028156456002909108007001c2c02620115220003041c0c0e54001d5042c141076031980b12500d40c8078544420240c5810b9900e0f41a8004000c00d0707072200880d0a0314200e0f0031485c080b51982403010b11640003440124460000501c0100100ca1096208205480325801070f00d00c0c01a50303800444a5600c409026a0454400a0581007400c420081200d023002c4500040440394103050000351a1410090040e000549c681815104e000090000044108802c58101700207054410990040d40058410005245c0740940e0280218001c54285201d00342c0c00405690b1944c681000d0000169000840004c00003822000f01c00143c3c00d21a51280e180260300400015280c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 334261411 1250 334260161 334260191
    0x913150f0503010e0601140a0902030a0204090e010209090c0306010c050615180c18041107030c020405060102010c020c091305120d0c0905031509100f0203090c0d0203060109050c0d0906 81
    0x1441d40554043da1420b81035840700b29000c03500c54190768003248910007201079940040d41c0c0710000d402109400d0f1001040c014a064140d0007007040702c02c40e8000b4480380104490242c201d0003200c00d0706800081c907030001450020240d00459015505041c42000718a8903111149400f80845121480101000c0c1d210418a011400d08608403c01c10840440c1d1510490400b041d01a02ea10400c04500490344000305c0d1362650000904504651f20345621a4510b0400402038242040305902592800c000308082d544180100315100003660014000d1511101c1800101c40c0000d002000750482d04d005e0384000b6030140180c5240d909000c039003c0c0c8072281114100c084581094a00c418001c40e0481000551408241d03a4203101440030900480d558282c222401c05003904080804149412803881c400300841d40a58001c21b1348008460340710020b0024403501c418080d6003e54581d11202c010003030450980c00581d0701c8a84070400783d04244096144405440f9180c1007115005c1e2102411152a15 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 334262661 1250 334261411 334261439
    0x409090302010b13060503120a02030f18120606030703020d0f06060e0f06030a0c030b07030e0708070906050a061403130816110f011d190b041505030615091315 70
    0x14002001410306d404c001a135908801070703002800b00c0003c0317542001c807170080c801e82c0d07ca1414591a142d44130300c8540d4441e03030001007040e4548100346250748607000190000e44030f032042c1c4000c1c0c001c20009046800704040b441c11088100c88813034048c040200003401c2c90007004000c1a0000d200c910340d0408200c000c0c3c2c485001404075000f83d02c041945004500700040c10030480303400c00428101c0751a0100b040300a0480311680300d42d94030910500050304040010082c0880391000c4040142c6a111030400c90001514401d00002450300311111005c0c101000c021034010b030031807034510b1402050f07645d40c803200d401c003034900150320b01c11031048818041c6a0700a034800000481d00b0f41a013240403000680381c2c1c90315401c0b501a00b100c541002e0071a40329444c003418072000362a400e035103450303554041c510143d116000700b0150903a002008803e190156056a000700c03802421703042a20b80d01c050700a1680c211030354096005511003242c034030062080c810001c0241030004504610382c20402c04078060345d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 334263911 1250 334262661 334262689
    0xf050a0b0324060706050702031b060c0a0f0c0501090303140a0203090d2006040b0403030c08090c040902060f0c0c0a051210050c0f040803090306130b06010c080409090302010b 77
    0x10100200414402d2010400c9101c0302c0850034206907225000200d501409000c1004089525010074414401d8000001c2c1c040c107148001c0d80042210005c191a8071060143d8035003501c1c110520141440602802c00d08101c880b440c5058a82031025885e86825034461075403d0300400e40c3c900751102c842c80c3c035400e0f4990201003060103500d181001104035030f503602480d41c000204500c7ca58074003d44280162907500c5103050204880480c03d00d41040300640d0015582200402c0ca04000700b51818003500c06503104e292010302500c41030020106000280c09100e40c102c0e4484020030584e034035401510064103200c91900c1c000d009050700c100520400300955042a445805280b40000b0900000624041800b00a001c007040a4907000c0410020703000301e00560500d2080880c010820010000250061080407000c031003441e262440d2582d503c04030414003801070800e42d800229254001c51404c607286100301413051400d540c035003101d000c5420011003200141d458250320320180c60458150940f003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 334265161 1250 334263911 334263929
    0x140a020f07270c1b050c03010c020102130806010e24150c100b06090d020f030607050c150c0708090d0804090b0f180601110c03010c03230106120902030c0402040f050a 73
    0x1da0303020940a0f00c112007441807131128840e060800c2c2c04002c03042c00f80406410003d00244849161050068042d400c07548161103400702c0345500050310040003d000f4103e0b8070a00c20040281c88100140280001c3e80c0e00b880098001140081c401d80c40e00000c08410500400d0030640714224079002e103003442c00c00c1110500303071802d080002405a60304421660784c1c0508035086030320622148041030300d000e0320703010f002c0e0b148c0508020401c1b019000401001d03c008132800f5142e290200c114064403501080d80c0000350314409000620024894100902d40f000f00105420701459040d0355404059100e9044200210345401c40b100050802c04a00e032982c1100705c07441c00b00d5444481021004403801009141041403110202204150501410444a00c044c00070b00020b440041c0240150016000340c0481d003032428602c0280071010a4002e060790f9180d590555440f83c2c038401000980500c1c40c083e03034036000340464000076039150710091004000d4040c2001740185001c081003618201c40d0301840c1030b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 334266411 1250 334265161 334265171
    0xf010606021f090204020a080108060c070503070618020a060504080f0102041422022106041a040506060d1d0717120a0309050f0709050702030a140a020f0727 69
    0x600c0e50040b611040b1941e020150941c82201d0740301c20006018200000394010717100140a40e40c481d4445000760503548031b2001c4944503100c103244400c1c6403040e48005401c607002803029030b00156403030304907502c14070700068240c00c2403046400041140e1080e52000300440d0300060100403503002400400200740c1041e008505051510031703890850318840d0501803040b140258000181141c028a264084907107400854503042218100480d60101034040c1c0c004050b2800000c400c0d2070540220800c0020f00b20b005001c801d012005d000c00740c98054a00d551100040c03101880b041c1541c414074042c0584556410700103e005144141450516000b44814840c0541412aa0302000603c80445808008501e99802e22003000b18000d2404100080c00b42c000c50b5550a03100f080007a9040c2501d2103a40104115182c0d50400d81ea40c0c428000b000c0c010691414044c43c1a012003005046803043c41d005840035501080c0c0c2103824446550024280384d41442903d00d0000240c40c04100d075800c001c0c4007000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 334267661 1250 334266411 334266419
    0x131506020d0e0405090f030f0901090e0106122c06060a1e0303050a02030f0a0201020a0206061c0f15050421090b091c0b101e0302060405060c0f06040309080f0106 71
    0x2c010546141c003140202d488002040c060354081018101e03d030130143c1980c1d1118040c0c8991481e681c451210607000a415071804030b480c0c0d03148011541221041e0320b40754540030003101942c0c054840a0040d2220019018850904110246090000c941d40c007000d400c81e071800b90100042e210f82034011400e030652071400200b037100114810010380742c042c20010f80b80c158a90301240b0350f10580b003280e401c2075004508004450340540280000da5055000c0e1ba441c0d980751428030185001d004400b86510110210507000702c1e01c1c1000586500c1c0c05844844290111801444192082910300b200c048501001d0364134001c801d510640d280030b4803403030164101841c02914006038000c0d0341c51144289528010305039940c07000505c80a22640c4500892002c2c41e00740da0160032031046105582c0080c249000d040250301801c3e14010959500420b20340c02d05040c0400e100c0310b40c11a4081949070310541007203080c810002c115203441070740b00303980301e011290038040402d08000c4411100c41303585c0e0401c0700c280 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 334268911 1250 334267661 334267667
    0x170a0605071206090b100c05010e0a060504060e0c061801050708040e012c0402010813020409050d0207050a05090109091506120210022d031c0e0705060a120203060f131506020d 77
    0x20304121b100b403414582400380b90800313034010300b1006411a1148240e59001c410070409401c03840c0702d28040d0504100030a81848901d8a0341600d1560540c0058100200144507000300d0440c3c042d5501031500d10700344120b0b903840d02015400346d002035006d030001e031004101041242c000c14141900e9440314640d0b42040b841c42d280e040c0805440281840096030000345045d610080c13554403160014020311480009003059a19000c0d101e0312000140958000401c0e141420340c84d01c001c44401401800060b0700c2e102e4004000d0407101012180c0d5561558410940790f050b000341d401078074008407003252468940c8104a044100740d111481503420a11510005400c601c21507400182a044040150b0040244442c01d621a0301054044480e80000c5820345c100340360f10040e00e40c40b404089400554030303001000400e0280b10b4040c000030360b8160000014500c2c640203903421040c00f0304805d602c50440c20000d4002d01c041d0400f0703045260b54294505450302c00d00b0a106c02031034240042c110a400c2c420f401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 334270161 1250 334268911 334268929
    0x3030507060c030f0f090c15080c0904060314010e011802030a0303092111060705120c220e150603070c08031e1602070e0105060301170a0605071206090b 67
    0x64103860b61405000c40141c001c0e0005295421070003420000c0c06080040c020040c07110041c20303508a440003901042840c00d40790414003180f6580c4031420241d540c11341c004850360040310000d80041c0c81e000d0010020780b405c0d128403208410300002081d0007071501115400c40e1703013503208106522080d000e0040507840119881d0021601440c01050051040c18000c66140012901c10070311100c03c0181c4001a9009148103c1c01c8000340030749109072130300013086030b090052070303042e110442051001c00c9500d90000003d1000c00700c400c2c2500d82c00700e401803a0607038003050341c1d0000200802120030055020080f643d84210140d045554506508180500400c1c0e1250100000c04120300003000c285022442003506001103008803e10302503262034880142c15405074035800e8050b00c5540e10100e002c450a03903145068a101520b124216864070008000501941c1e002180f203010313100f40700d400724100340075a5100d5081a1554494400e8000d03a12084503c00d912181d0240c1c64048008844d5840c1e40c04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 334271411 1250 334270161 334270163
    0x1a012a0c15031a01140a03090b010f030201030f020304212c01020c0a06081504020702060d0c181508040201051905040f0e150f0a08010e10050f090607230403140606010903030507 78
    0x182d21441d17a80304c00c7c0e0003400e22040c050301e980002c03400040c0c0340036840704a4065a2003030343c0920440f04404007410580c001500e000b031040b0281101c40c0b6015034811400c04000080d1300d001189400640710140845450300545840d4080b060500180742d44c0411080c44050780c103441d41400c4514140000b4102c1300701400c400d20030000001a40e110f6502c1d80c042d0342c40030b90000d00c0e4603651501c040001d0001c0018200c00c030042110800b1007503501600322990702c00c440e03102042a000d101c07140d504480182004000f2818440207100e04208842d40151000c000c0c101529429580d9080481c40c1f02108800ea005030a80b200703102c20400c80c00c91030b0407911150b0070117032503c820001e01d140014a000d03000c1c2d00031181c0f0b5032038240726484c500000107800c52001130a007400c10881d140c8400184000c04122168402e5500110100e4017041c0b058010752101044000003d8103081c40310b0311021561b000d54000c0c0c0780c284400307400d400d40318402c0c40000e422803030900700411110f255503009002c41c0a5454 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 334272661 1250 334271411 334271447
    0x50606040e1c030f110f03040201020d080903090904080c0a050622050309040c0203040302180f0f0402010e2134050d0305071b03080c011a012a0c15031a01 68
    0x50f4008030a44c940c000000d84101c00d00290703154222440102000d40044409a00600c40c205400d07401c14055200a80180d00910155181c030f070040d418041c00c04070103081211504bc08011030b040c482024844404d12038800c07030150039141403c43c08032044c0c846a08007c100c0d4840c4508010008000104481d501c0c107080d20086146611901d00340e0450003a0f52010350805461180800c80d8003500398581e101d403220071040300d02d980302d180c055215502c04450090124144950700e07600c602d8600c00624204c14400e40c240c003411400c058440c2088170403d03040c251003100c80880e050b000f103c00340038040c540c214040b854101d480c040c00242484210480a0184000000c0100a1002c212503410503034028080440b9441d6481c0380003000c030350100b032501005500c0c10100c0001c0c2c09a0307850405116a0594030615401402c85070b9148880481800d07a4071111044a00c00c000358190402c20300524110700009503848071494040d09444031800582c180000042100b006030ba00541041c05600d9152 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 334273911 1250 334272661 334272671
    0x30405120703060e0706030f06050109140d060c21140f09070f060509100e0901050114090409060506011205070c0818090108100e0601050906190b0304050606040e1c03 73
    0x1003001800d0200c40c0d04050003003400c0c2990300080410001700c030001c0f00c14550f010820000001600e0003100c8050003010b00154101c0d0080000d8030824804043d04000240003070840d92907a503c070400c0700c9000703e0300c4000c41d41c2c810000240300e614820030090240309a40034010706100c0b010b0f0082100b0003d02200607080140e0104540c20300411080e005000d040100c0c0c280385071110400b910f0380e0451068184a0003440d0310070b8840510451a01c120b008019154456076428000151006c07880001c1da1040408107000c0300c0e98075540c0f406050701150040b03a0004882c2843c00c0014226409052200300a81c2800c4c2400101a40074a50f0020550010307440c41d1543c0071611041a409400000c1540c0910404004640c0074001b08500320003400164081241c01c03041e004540d10743d14244a51640400b810700042c0c4107040030114a100181b0b4413104801e00c9072180281d20080d00103803403d0320658840400c101140c00c1034420351090700d01e401c1c01030442c000c02015800c919a080a10801050b8480d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 334275161 1250 334273911 334273939
    0x603030301062709060512011a040b0d060203040b040c05090c07030c03090503010e060603010c1d12161701050c07080319060f06080a050106050309070308090f0a030605071d0102030405 81
    0x81c2c822070040181c0c400304120013652501e205001e0078190080501c6049600c81c03064100d03a0512905c6000e071441c41113081641441c00800009000d2198019040000e0f150390a00140f202d1005600ca103104081c0004d96040c142071030017584001d600703d41d0207a8110b1041c881c100120030195030f41d0a40c10315000e540710701140340448400041c0c2e480f0a0709507082445c003213246800800d030700d48954800c1d8020421340c0c1c51144112400b109035007210142c0345200711201c405040111007071a441400c0404c481e96201c0c1c0c990051001d100c140e2014039072044c21a8400d92000081c000c1d160040c11080d6818213003440c54541d403100b44800b030100d07648110000050144145950003100080081155605c40302d90f59a10160000000301c407805812031502c0f0020400034014000d480c00f41070038000070040c203400c40d07a5488903580004141c1d60701841a1a00e90a1070b0744600400d00510701c2000007081d41d0901200c05000c03034000b07900302c41d00341030507180354500c83e40c0c00400d0320216001112214001e0b811 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 334276411 1250 334275161 334275197
    0x18050703150b0913051302011404210501021b031c050420030106090609090221030a0c05030c240a09030503190207050f01020403020907020307240e0d09060e040203060303030106 78
    0x46078070a4413030074189802c110042c0380510420000e103000307807150300900040c01141d01d15031181b8000d024603c4900e1440380601c0c0c0068500c00d0449100d600014500004000b00306103010401040c01c00990001513140001483d85642c81058200390300b0500041c20700d640c8048000e11150300702c2e042000118a003240c0c03a0360075044900280180d40742001829244c03100c1c3c1003d88040501a80111801a0440302807900103010110fa0703640320002e542018100b0f40100d6000d8042042544e15102c1071111130303860b0710240402c2848120070a03415072652502081d055041c1002400d60290b00d142000e44408a60408126907100100e010010200050051014001d001d290400f5203e840303040101b1510200560050040d03900031036030004180d80342c01040381d0740d220b501c80050018403102c40c0c184000d800650f420b032014030b442c000410200d03103070400340d440d0140440f000000540303c0038041082580144103000740c0e030019a030941c80d526008011a5072480188a9041080048482c1d0070032455 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 334277661 1250 334276411 334276429
    0x506030a060507020d0e031203041e06060e06040e0f0607030c1b08030f0603210a09051201270203190503040f030507080706050909150a05060418050703150b09 70
    0x140c031101c100b20500306800b0080d51030310301710305900c0414802c5d0344c80516441c0010b001c0880c618050b00c40e500c1c540d1196078681600102c4ca80c550f101c003c034001020300158080c020f05015082d50810001c103454030030200420b5482d029040f401300d801604040d014180040fa0b45988040b16050114a14451410441d26030445503400807500301c5603824003040145000042d809103000088107402e0b52620010142c0f038000303401494030108400403403041690b100d20054010010340c0d04202c042584c7d0b400c0070414070360240d201d01c525655a4201a600c00d0b02c07540c8171062010000d684803e40c4c001d07560219684400548855843c3c24808010404100c420021079014086030001d200d4501d43e64900b840e03440031a03028a514501a001000c01d40703a124006441c0d001c0c0c0c00901a01080d2105590361210360392103070810340c212038090000300341510390b04000c00003440200490b403916082d00040c241140d40c0504401c00305804d1a2919520902485a1400b540d8a408900f9540c0c150f0302c0c00141446 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 334278911 1250 334277661 334277663
    0x6030115051e0a0b0c011505041104030f020609060a03090c1a0d0203191515050310090902010306080f0a0516060207030308090a0c060806030c0405010b0a030b010309080d0603050d08010311040506030a 88
    0x403000510500c990344190056403681100761207064100c1d403140104001d541c0cac42031a0001d180418441000460514020100384500141006140200e440c0200b0260340c0504540d6011903114841032080090448083c5d000b00b0105000c00742d110700f0001560568402c101c88060740c150084003040701001c0c484a9259801c2000d2420030800d403004076801003180407440790408400c0032110303400b00f05003d0401c82e8429441c04c00c06500e82410200c402340100303000c1800303a04040c0d4840c03001c20009070030444100c0c03485c103035001007075050072a150403880e081c1d400d02080ca60b416031000c104081500010703802c082d2581802e01c1440e90303460380441c84c03406811132000382000d0351810001850743d401c0b207103003400b0341c0c0280d00340d1303440c40c0302a41030106a0f0401e12070000c442e2400c0040c0709c1100c0c4a58400c0c0c00c281c60500d4041244407450712d0700400d0b60010614104982c0e500c070f0080003000003c210901c0d0079011800c2c40e002d80e43c1345440355822030071440b102c18065526080000c10542c1c0c02e1081c510ba031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 334280161 1250 334278911 334278929
    0x512010b0d03020c01110102041212030b04090c05030f01090809280b040303080a020c0a0b06210706090e0f01210212010c140421020103060b0c010506030115051e0a 72
    0x5001d2400e0096681125010340ca0100350100441841c101e418002ca8066459421001c114106540d548440c0e2490301c06044c001c0603a100001d03140c66945014484c0b09600480040d1040c5050500701400c2a80b40c0d600701c0702c16850204180001200081511003600c1c040300c4c03906ca01c42c3d090041800c50b806295605150252000c0085410f59603803000d00240e80c020303619102c6950321120340340f0803803092998010840c0e1112016400103000b05c4c00c01c0f64000c2019280c500c0002401103510080d404014540400b81c00c560000d0060a078000039035002002181070840320f0381000700e055411004103026080c40010340410500800280340340f40100e05602070f08182d004001c105213140208190501c0c1800602e00e001101600515082075400343d9a00b5451850740c0784000c074041800504202c5c08030b051603143d45001400d1038041c006841c0040c0444004500351a11404150840f003d04481010f6008078000600c201e0303e400c03484c0c12080442002c09511145504000f541640d080e900241003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 334281411 1250 334280161 334280179
    0x207080a050a031508060f19060902040806070503040f060b18090105070e060406020304170708010c020609070905040c0308033102361b121801060303090512010b 71
    0x1034254490014000840196010040003612a0b450150b6105070310810341c565100d400481e0009150103ca280c01600541c1c18403440f40c100f420250039200c0a42c040020580e022804001d004c200f4001a648204680780080c698a001d41d61502d080003e001d010340300d15690243c0542d41d07100c01081c0c0108818030f114100251401000c0103020b8801242e0400c005901c281d0340010310305009090302c06852071034001e5420f0a06080305421030070301440e50900c2511819100240c9840f00380704101c034041003640607001c1480c4c400d511602d001c1441d1700c8002c40c58640070800003c600c2d80091b4400f0b49074003018503592600c0350f0f80512000304c50034440e00480a070002d5a80c40f10a0301c4d4941503c09803080d110b81c0c10001c403220102155154607001c031511048552400d40078654000c1e81c4030750010600340c0c6002c07180e801c00d042070701940050142d0031155001c01c041c00081800f0340c818140c0d40d12030b88000c0c4034507070442c5e5000703216a1007032080b28060030311038911541071031003034001900000016010100c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 334282661 1250 334281411 334281427
    0xc04020f03010302030c0909101503020a03050a1a0c0708211918120e011404060e01110309181512031905030106080402010f03020d1418150a0906020708 67
    0x76802807008130301c00e02c00d54178030900d54184a1543c500c12506c84014003108604420020003034150151100c941e002840310202c0107a8640081001030740c014002840c410002c0e147c52400c0700400f00303030701420b0b28944041101342e540500450b01800e1b48544055201c66550030300303038011032125420510360215a0304022511460190308000e080a00300144032212058800c01c001004665002c3c080190b40e4424015840c00b03079111190560042c54088a50400e04214040d140c0082d0020000120002d072881c00944c0d0000000c040050f01f80044d6207092058400507003105c458420500c0e2000e411400604480c1018114001c03540000d0101e41440c652010415140d6100e5400c0855000e142048519501c6c800c00c01daa0507200300e501c42481d16280c503001901d01d040500320034003c242d020481850003050314058060f010000310001202409e0010b6059229030b000b409015440d4403d407446040c00b0010308003543c2000804800060000300303070034010086d101701c0b013014141e45000100e0b42 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 334283911 1250 334282661 334282687
    0x4171803060435091e030604060b0f1503040b150307081f060e07030504061b0206060312032202030c03070f06090e01180e01061e0314030f030403110c0402 68
    0x16402003441880028084203000c14042d2a074480f0b0f90000551500b0b0041c1e403c1403d0068455035052098200303c486128110006071800300211411901246c54508034a107d00703052030b0b82c924244003110300d61100c01801d92104d503e804010805084070070544081000d00c20421f200c0c2e0340c4404003a0990751210b0b11b0704211507451290b28642c02ea4895411880f2404015130b1140c8426151340754800c550f59180c1c0c80c001c60107820050302c1500c4599a40c4a04a410183d61802500101c40b640140082e131601d1002c140c1070080c040e1a440c1c100350f04008101403800c0d0b010340c80da1a14089585925035502c107002080c5400712002044d0f070588101480400c00c900d0120410b07048031800c7e40d44488584c0c0320390078403025020038440d907035502c28024005800c007000c5800c040710000100700001819903880803800f81240031858100d5550101510501c140f00700c14406c3e10788801c1c0b03540114079000a42c1800074261200520250400010000c1c80c44e8800d02031054009840008205641303414040e2401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 334285161 1250 334283911 334283933
    0xc081b0c030706050a0807020327011e05040515040e01030812090a020603010b0328020c10090c0611071e05010f0c11041505040e0a0203010b09041718030604 69
    0x80161140c045045580d240025400007500c0860f52641d0824004450654600d1000740c040700c2540014040c203405805220320b940c4034180c50070985030503a0700030000076100b21001d0380480c482103074901c110502d09800c842150202c40064036031003040314001042c08054000c83e001b00d106108032000010500402074050000c00d804041c18800e1a200c03401d0310743d034039030000000a4001800340010020318603c1300145502c852500f00b890001c0c40c000c29414040010040789950565011414030380e000c034100280780340d02a400e8401c01111415488110fa952100e129201c20004101f40a10920070188401c9004144403100c000a86240050312110441c480c052940000c2c0c40401c440f0742144520761400c54540c10150b000d5500040c131080c00068402120100040d414480c2c2c005510f480340d00c1b601003940743c8000038044825007881014256103070085428400da041000b400085503d04090303003c5502c840f44915551440c405002c202e0384114071207981e0500404080000707204008501c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 334286411 1250 334285161 334285207
    0x10201090c1a0c062d09061f032102070605090901030627030c05100c1b0309051806041a030717010f06031a0a050705090411360919020a0c08 62
    0x50a9000c1021040c0c005440011159104c1c03503130283d80820148c2c5140004030507a040c40003880300344d054594a80d11201d81220107031034030a00d4a44000c041c402d9040c00140098019172501314030740554200001c0c2c0c0d292040c08094140c2e07a40300c10700d41e00803d407100e600c1840140c40303400c03500b0760b81e090038003030001406010162854002d00031040e0043c51544207031506c000d495225104444a00704280d0000000140c0c201c00740240740c440450996200f03014503648901040b40741041c3d00d030841c1032200b690b0145510200b6020000f0206145a4001c0b032900c0903640c1c910b010006071016030600e1809008007071561040309103012400f00c14081021008200c10080d00700200c10740d12094109021101c0464a000004600744000f01b803526141e008080c401c00e40500c520b0600243d40900c070180030400e038940c00b002280c00c42158001c0010428403812801c00c58140b00c65103418030210901c2280e44082480d0750b603000908140f842d024090f00303001540c00003082c40d11080c2400c504e044032074082c07503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 334287661 1250 334286411 334286461
    0x60303071407030501051f060f0c0203100c110f15100302060307030c11060f19022106010f030917030a021201180608061b0f04120c05040506010201090c1a0c06 70
    0x40000d148441f04c001e9100141918504c4686061504c281210450b1a010b01c032000c120b0002013800141c0d504120204011041c000001051848070b400a4150380c0c82c130f00701d20820341140c0302d02006400701141c1c421102d441e00c004100c066440d004240900030f1607400080d4805008806d00010641c1944000802411900c0e031900c651101c00d803040c0e850348111128038048400744009114000f507404400104c000d2144090b09240500192540b110418041c1040d0700441c1000c10507150380c005035054002c5024141042000b000342c80307220018120302115a0034081c00400b05210003810b0b81103c41500710303034400102c1c0e0b58407107809002480c03504401074481c908100002c901080d020510398007503861100001040c40300041c145046411141503804400001d00001680d03c0718850040c14082c480d581804202c0e04240801c401c4860241c5490b04586c9400406400181110200c40c2a40c003035141554410840e0210b011075031044500c80d0016001c1c150500221880c0c080c6601c15002c4985 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 334288911 1250 334287661 334287671
    0x5040308010506090a0302010f030f0e06040b06100f0f14070303140108030c06040b060f09091516050306130204150e04060b070335070215091207020405060303071407030501 76
    0x1808000703c9001d803460941d844051444108015030081241101041a5050204012100307420707580488131001410421034001c8010001000804940c4552100084550b4107070a4004003004141280743c00c1c080d818020030765074030303244c43e4004c03401c4080300409050560740c2d0b00381c43d1030000c02815210704501c14400c03035040007040c500408001e651910803044014000b5039113940716070b2000c5e44080d00c20343d0403d0304401d084085031600060507100d10000705c0140b041840350341001141a00013010707000c03000050407084104640c0007003182d03005101114103081440f0f101150200920459004d40010b40c40c0031141c4441641020200503100d0301180c0822000369643d01d210241d224000c2c00800056034494070a003102c0301d0340910b02050842c05840d0122240901c0c202c51901c2007035482c98050b03400441c0c1c411a000860131340e29400746641c0058a603030111012400040c0c003422200078416a00c03100000c50b96201003040d1039045030000341541c0b81b03a18100078291104040d00060b5080c0d4204 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 334290161 1250 334288911 334288919
    0x10504032a02090c0d1a10031104050909030a111501030b0910020a030b0112050603030318120a11100e06160e0d06270c05120309130539030612100504030801 69
    0x2010080c6d1602c00c1c0a80fa0750606a08000304800030070040701e035100c0741c0400303100125168450003900d9200d000c83c50011a030b12500b0120140440d036240c1c1409a40d5801721100110014080c5041030441c8c0c0c0c1300780c1c4500f49031140034140c0c0c20300340c0c2c500900408920118501c0c03c62603160b08410307007524003070321100e02d0280c80d408110161072003210046c0e0164020404100307250400c0c0c5000e0801c01300034059031143c44420526000c1a805400340e00002842d1019018078084140203294004000000030081511010025611170400400403000301c042c20b0000026140282402c40603c40000c2802c0801c0a030fa00c1c0c41001440c4049003801145550305180001014107600700003ca40c020210711016031401c4200441484e116207801403900007842800b1b0a516038000c4c1050025840d60042801d00d801c4000c000201030340400e0700d08a10f43c3c403030f84403042c2c1071a580c92a40b00e62005038482c1e40c1e644950124a200440440c0b00106100b1184514540034450744254011446940c0300303d0aa640c0d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 334291411 1250 334290161 334290191
    0xa03080106200d080405190302030d0501090509071403010b121507091a13050402180f06040308090603040c080601030f05100902060a030e0c2d03010504032a02090c0d 73
    0x20685282ca502014641d52040d003e5000310f58001e209408441c0d020582c1420f1031030000304103504801691000c035180807001540c1c00358901414810408020310311385071035038590f40c2c840c1d4480c0d03141214500381c3c442c1c090348080d00803100006029084003009229405003503502d11484590b2041e000000002c201c0c024032468a0b40210360040c04102c8000100490501c07107540403c0100112440c0300e0000903998869001402c0210201102c42401c078080b03009002c0802144040c1d02e10610b8100401e1000803181015500c503024240c400f1a00ea50300d9252072a2003400640001c152880380e07400020401c200d41c05207050b030500c20020384024068500710f42050712075003d0001d600090030300c904840710f0721a5004203041c01c82042241ea40524001c04100b00d115408080f604a902c078444c40300c0707080c075101c915030320000003a00200180d1800303840081144202c03051142280d881c8400d9076411043c03001801e01140e400a08505060403e940804003c0c0c0c01300d81e600071040d081805880403010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 334292661 1250 334291411 334291457
    0x6011202060306010c080d09321f140106030c091e03060b150712020c030a0201050d09030905040c0201020a080c13170a1209080c031501180f060303030606090f08030d05060409050a03080106 83
    0x1149da170040001003034110310030700050744081d484584903580300708203124594031a13070580c0208125140062520002400202117050700d400615005142200c6002070040c02e032469802c032900100000b501b02c04810014410030b82484a282c41000041441c2c0103010000801801414242d006c4501c5044840207054554058407c080d010030424032040c00e0300b54158020107425840784c0f4040502c0e541340c80005d4115a1a0051140142e5010500840d1103401c031a5454000480750030003401c1c100f00018440112201e8040c03403c00b01450b8051704280e4100308182c5100c564801d4106010000108004180350114850800180309118800450b4140440c04004ea90f00000a8003034503824200c080540810800c61030340280c0d5120035054a01d0341c2449600302440c0302e503502260b900e103801700080c80c0b20403e4004200400702e4070010800d000e4000101c1d21a15925000807070a507a52100040090440203006400360044203e4002003560101503039042c0c58054942c14800404002c102c18151 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 334293911 1250 334292661 334292753
    0x6090302073015090204051501030f111801050c01110d14040302100b030a050a060509010606050c0d0e0109051903120e06040e09120c06070206011202060306010c080d09 74
    0x11008000c1000314400072001d008818440f2004544442c140e40403400300c0b00e04131745d40108600c400e100a00a90303414011584800981001400a084e5180b040c0201d84542000e07800c807280103401e107442c00c3e40110142c400307281c0380d81c008210320b003607142c4148040c6d8000070028881910b09620344035406142e00a550195406500804d0601c0e207460940b4000d03e4100c45266141c41818031690018000b04018000b141c415000132402d0700340010b0282c2900d071533405c50307028445c082c4001c0441c1d2900003203101d482c803028a008441052048010303510790728240c01c0250001640b03c0b580c003d04805c1c920302401c807807007400610b403400c02114084826200c01411140d00010402c8200254441c8080247c0c005000d0015110001e000d41c410302700355440852040800d0300000e0421420680501200303004104030844074804003101d0340048c205102c010b12150512803002c09150601210300296980700380616020042d040643c20010b11104440300b03082c0180803150368040c80021403402d244420 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 334295161 1250 334293911 334293989
    0x180503090108180106080f0c0103050601142206031b0f0e060903070806180f06040f03050a030b040218031e0303160c020303030f041406010b0a0f020a0609030207 71
    0x95003030001181c0314070700544040d40c5518040210400343c4001e10600000b407251000400c0200702d00c03001c483c00c0040080c58681414580300030840343d660009203040c608a04100f64640c5d40103c00407000d640c4001c0c202d08000ca400c1c42d000850f84941591001175440d5030b0380040c50004880580448006004141a60000f940e500d001251400c25401801340188020305491826032159000d0340ba250044528101e0b81c50303501461182c0c50300920050381500c1051010b4606427400c0d4a8102c00c0584000c4010704010300082d20080c206d100794400134030100b005105541c7c031010501c0d82e540402905e4046803007030146018001300c901a1030103030340030f0b070320300002a505668a550481505141c1c1000000a00444012801c0140d5040c4019841070020154a68a50410341403c50004120a40749440c5a10900c018080300741d01704152007250328549050031110301c848038120f04010322900014101070404201404240e00803d06400740c8600d25100c202107900c0c0304641e600a2042c013161504 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 334296411 1250 334295161 334295167
    0x30b040b090d14090d0602071b141804020f0d1b05060702101b0b160e03030306010804022404090c02061003080d18050604050c01080a060302010806120114010b040306180503 76
    0xc20f103100380151103400e02c01860765100071a01c0d1070350001c0c0c1c0c0c040304003140c03010980034200340c482c1603070f11040c009041440d1003000b144126102055141c3c403800d1707174000c22405440000c0d0865492a803010911400a480080c51900c0e6240c08031240c0c10004110300c13070f46030035031001c202c904012080d41c0d441d07500180300fa404a07500d07510540310390102e0f0402c40504002030f84458040364044a905000d403042440380580351302c0031800203100c0c0002c2488036100343c00810074480242ea0010981e50065011240c0c11900800c41602e0b103100c251004000a40800201d800100b000c0c040d80b00200e10a600c0d000c1c0d54941d940e00c4046001e00c20240002032101d201030003502d0402d0507560192071541c1504400164150481c0c0f24640381c00001c03107003140c5070741c08006216141d503401500c403901700d40081d4060015a09590000c2e250120080c016400b0340d05003401001400d40c250403260030000280081c1c0b1079035071102403404182c0e003d4001039811900348241c0d080d03010300d140440205a0307007240145003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 334297661 1250 334296411 334296437
    0x216111e040c030e07080c010215010302010c15240f06020604030c060e0a0c0909110111070306200c0f16140f0102070902030901090308010509070804080d090c030b040b090d 76
    0x1401c0c024528401c05551301e101103030070602001003901a041642c000d0041c92502400240b1344420821004907255407c801040140d0f000510303e014240e0021038020240c2d0110201d00080091108001c0e00c508102c5008007000450741c008002d032255180c0c600c3c40c032500c1d020141d9890b9410f503001400200d071400603401048030b80d44490400c13402501030300c1420503d82c407002c800105907008004840c0d0340da88000300300200780080005840081c00d00070f0020720a40241d50307c40082d844040d00207620b03501e418400d102c0e288081049501c07250700d190b803a041d4181c0c43c03aa5564032520214090310600200d04042e6452a1524003220134410110481d80000300501001140c0074142505621030828081560401400610f1040da4007100010b181c0620781030003000e000060b440b4501407411007040c0144c440d03125042e25405071700800240d9a032411501200003c00345214040c2c1006c60564011003048200c20003140a20b0088826043c1e5440740004c9503160051326029502066042007006 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 334298911 1250 334297661 334297669
    0x1b0315060e18010603080a0809060702011506140f070506040c061d0f013b0406030f06090309030503070303050f0c090a172b02070614071b090216111e 66
    0xc0c84902c40001003801a6250f40e59410b54012078100001300300c0401c02c01c8400b1004200859100083c0e00c001c0c4155003a00c050140e00709481d00410701042104103501502c079070071f803080781c0f03006d1300d1205030503520082400c10980f1400c00303031022282d024504100044440c4074810b003520401042c1501002c1d0042c000c100045419441c00d082d051240042c1d4440c0c02c1c2c1da1012212059101080e00c48031240d0007640c2010a034103082d940c06200707a14203881800410160400b01d452242c1c000400a514041400c0c140c40996103070348002d060b8440011800c0070903071f05030041405003566201e4039119441e1500f46030550b00440340d01c150080ca113a88200300750306503101c40c4443c0000307840c10b458070482d008000310002c813000408030305801e10490707081040e143e0410103180100709601c1c0529804811a0144116101e03100024054880101920b4181d00021142200900f0a00340440d42d643c0a61840040022400c1c000e87c1c90140800209906013814514001c0800368004084060725030700c0100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 334300161 1250 334298911 334298941
    0x501080709180216020909010903030b060f070602031005030d090503190515190207030309051504120804061503050c0108061009091512050703050d031505120a1b0315060e 75
    0x301034004050840c80c0540c503100400347c060201031001180b0490302e401d010b400d4551162440b070049004002400640c0c86c10030540e01c500394800800b40e0340340c61300e414a0240350010707044650b0500541d00040c2c040c603045218102150025001d40701c002507500c684850503103030b10402400540012005a2460603071602c540e510080c0428807440d414900b07100d59080303030880d68080340800d0b542c0044805200d4100050300c0038148203400400c2c64601540c4000b424030004840105000c4010b01180411602d42c01680022034010401002b05650341805542e50490142080c04500c1c900081410750400001c104400c0081e034644207981d40c5080400070003004c0006403240030001024000c10691400003800000900500c010139203141103082040c00c040040325500181413074106811020001110f0200440300100d400f03e100255200e207180c10032080c100001c19001030b00c502c1002c0000032424140580740190000c1510b0918245000110b9000c0c0c000ea4400100410020b29034020a517a1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 334301411 1250 334300161 334300177
    0x30a0c0b04020a17010605040e010203041115040e10090c39020a03050304061412130203010e06090708152a0706020a0806090717060103020c031c0605010807091802 72
    0x585641d84046150502c10558501303030490351180c404100f40d1515005002e038510390200214654240342d60b03030010070f07014412254018030030030000003008000f032000da40003000d02008485080c64160040b410452850080711070a030300e0321081c0074282c0c5c804d003585ca2441c2d4a0982c0307050b0803120101405005140384507800c038140654000000182c0b511444000190301c50401981c482c0d003822406000386491101d410070042c000d11000b0072015540340c242e6000103445041d0300800300035001007800740c00108011201845484188443c41c1d6000481000300c690080aa07510002c5100d24209101d0381605e420780c00200894402d6020700c40710b40351515082846035007503d00040c990f00c40301641c000b400114082482c1c01c082207041c0c24080030103540003500749071117003d400d08010400001315001d040c042c10554080b480308100b0404000f100c901c88140009102030010a080104c0502400d029143c00901d61b4000300362654010030100d4240ca2014003155441d417550180207000f9042851 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 334302661 1250 334301411 334301419
    0x3190f08310f020414041709040902100207030b06040e0303010b0a090f03030305011d010b180406080f0304030204060e0702031603030908030c09030610121506171e030a0c0b0402 78
    0xd245a441d0065940411000d485a10b03030300341e0341c080c40c0100402c0703c010480124a203180399040200241c1c10642100100074001901c1d40ca0780d8851012400901024030029080300400c490321001c2d940000350034048902c40c1d09125495941c0e85c0c240030954203146c03050b2460b94414001800b1240000707000c2c0054002a1803d14502656001000c9000d0580d070b1083d404030b50350700014080401142903242003100c44002c9902194940307020039450344522050440c01b561107d05640301d60380c40c8d07001000240302840880b041101e44000c060b4880e44140b00480c4034924020780001c0000220207030078407941d25034014600f003003122685045008000c4c0c10803010140e80358440000952210051800341c4403010145840d100d044d418185001c8002c3d0a000d40c80c040712004105115086a40024042d40058030308119280c1c8001680600717456000700181807600311030040b80c10380009041105240e01403590b240f0840860701c5645030701c26402c83e01d00080e04a481000407904451000d900188054 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 334303911 1250 334302661 334302721
    0xb010315121b0b040f05010207052d06040603060503191a04030309060203010e221211011503080306420d0c0207050111150a05220503190f08 62
    0x81070864041403030741c110fa14002800705040c840d00c2541101c0c14080d04007800289595400c0800040602c0301c504180c1c4081c4003000481004401c500c00781c0d80301c0c80c00151400d900e5544615000d0081c140c1401407501034481c040d1301100d1542d40c01012012160080c51510403085103030b0401d10a65801041a0140342e00c44510f01c00103120780c802180203003c0d900c80c0140742d0800c2072050700580c542c4540c40c0b07222000725030180041004800140c0c215000d60914900d40702070050780c3d40c0500081d41d46603542042c0310000209115aa0004601c11041107a03142c0318a01484001c000c582032442c44440303148000441c1081d00c001440d0b40703c510310510384010303040003000c481c0101640d0400d28124016080034100700040c0d60486040da60410180020340300c05c0c500c0405001d0382c0c0c00b00503e000c2825841e039000c03400d070b203529416400042e50000100c000c3e403449400e01c66901d602c44194091803869110081c60072600c59040e9089460499070381c40c26584603c0486500c00d0700b02111404103032406 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 334305161 1250 334303911 334303943
    0x1060804030c1203050403110a05070b030709090e0a0326060d0624050a15020a08070f0b010e0615090306180115090e010506030309060a08040507030b0c0d0b01031512 73
    0x9811003100b460240e0340c0031807986080d00c4c000340081a41d444007101ca900c00c0742800005180892040180d415020b0700c23784960b20306c48210385003e00d681c03080c1e41e80d0386025295000c1c0c1e0000719a101000b8006d40355041440c2207805011000c5c03203501007000340036100e2404241c0a01d0300a403403034142030144801180040500300c9044030030342c013940801c0d80d041c02400e04121904200b040c420043c100c0e0590814924420340010f52a1003030440c1c010700c800000654102001800d0900ba10b41c01d80180741d050b12582c42d4103024414450507a8041c0c07186e041355810302005004042200e1580c00b0180160080781c4440c40403181c0318088542d81441035407900e44280e12882c0500c0c82600030f02d4981c4010600300c000c008058211400901074600940081000800303075181c1e0300803955121000c0c98822071641e030b6406c02030b003031002d1a0001450041d00300144200c95040034007134000420390b400104803450f44a401501101c3c4c03c0308000c0e129a41c0c441c410818942e8403401d0941450044011610210103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 334306411 1250 334305161 334305173
    0x2202090402090406090b0424171c02280314030a0605042c010c020a081308060c040509060d0b011701060b070c0e010b040e0c0c0a02130203070f0e0901060804030c 71
    0x845d040139500b159100500e003101d1401c0d01810046110b0305010141d2981f40d01c00c4594500c2d01e502912017040074191b4080c00b5400100721064140c0c10f660480301000100032130081d15807180140c00031300f03440d4040303803010f030f1171280c81c3c40b100b103240d041c4c40f40b4061550220013880103401c010f14a0384059940e4100041e41c3d2500d010740030b0080c94010116140300051b54852031142a205c0404c0f9040e8500b880c0007203120780002d840000d40c0c2e004080b01d03440e85010380e6081030366030441d04501e203280030711800d01c544c40d04440d0140050b02c0341262240e410760703582418051400d01d40900540040b02c0c0b240100b202294031254011a02450800810003d0b1282c14024050b80140300840c2e400342401c00800070b41f0015003016024000c410941481c0c01d00d03007101c101c68440040d042211001d80041e407450880420081d0390711503075000c0c00d001046624207450300002d40048481001007140103000c1c05000b8802e802800c1c10800080051015900b0003c0440300b00b08011300850600c102543c40b9408915 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 334307661 1250 334306411 334306421
    0x50405100c051e040f09050414010e030406110309011e02070b070c090501060809030702010e040902100801030b070309021e0414010b07030201180b040f051903090f0522020904020904 80
    0x900303602d440c2e9849900140e03c2c140c94014405030700c402c0b10240014060034500c04003070401c9400b00d401c00700e503945070f41c20007003901e15100c1c41c1c2c0c5c2c0056103001c8014414010100c0070744100c4407661900186801c10071012038032403046480660002d4900041000c20510381140e4841c0c2101d50710440307031103075116200310ba02c1f80e0001c40140c401d81581c13002002809810702441d4050005898a1111030401e007044660b24040c00000034144007400c1c449900c80c0c3c45d1076200e0601c0c0c60f0010040b03001480040300182043c0d40038041038804030465400140c0c018081d002e80048664040c0c0307403030a01c440b80900040310408610724154807507200c1045103031000b00c1200081c0a02141c2d47c80d5a558170322450701a08640f0b00e0541259285901e01b41400442c20441e200e86c0d210340c000f8a049914262031800e43d0422061801e902d10400c1c0c110700c5d08041c107a12507400c4054900314850700e0311140e1680c0812000c0500075080102c0d00e401d019581c152081640c002d030040c100054409410032140a0018041d0b42e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 334308911 1250 334307661 334307681
    0x4110904031b0c1701060920160515010303030e0105060108130f060b09071e09060e06340c080c031f0905100f050f04020603130f0203030c07080708010204060207050405040510 77
    0x5e9102c190a00c442649031254440d8621240300c1031003c003a0003203600d500350007018242010b40c60402c080d03070144071040c0f240f0f4001c00090320700080c280d82c607031078003500804191950250713541c0381034001940e41d4080c0c1d151a00500049038027084411682d5241e40c040d94400303a00310b4106413985101c4110f901c502120034080e10300c07500c4201f01103840a4550001c0c01c0242d0350601001482141080815007002152800d801c1c260758031503852a00f87c000d0b0000440c608000910041e1030340c1440f00024083c0070504042c2cbc031980c2c045d05407d44c0c03091019503d03101202e6050341500060300c00c418000c1c4a1440d12044c0b010810301040c00401612018201034807941c041c04550b403590030f644100201c1c2e101c2c07954440c5149c2c0105079a41407c1e00460298003004110384200352003c49540284541441703424000c541c018110f990b691a801c2210303440e0002841540000d109104021032034903c1802981e0550301180d00925036146010100009480043e005942d01e00030765010b500c00940c0b9000e0a4404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 334310161 1250 334308911 334308913
    0xa0f12020117040f0b150a1a1e090301230a050403020a17071a190e01020409020f0702030c220507050415030507080907030f060504021503070804110904031b0c17 71
    0x5030301c00d800d15a180003002065100044a0201e0740036003070740c59115a5050307523010301c60840b412070b08a11210040c401e001c1401c1100c0d000c0c580c0000045c80c44001000c0541d401e800034000e03020744281e46010440103090f4240c000b600308002038801c403040e070b2006500c40d000303204072819040c1d1034550041d0003032000c0d01b4107542c2c1c43c000382d0319082c0140210081c410b040200e40d42003c0c0d10341180d0303202c12690440034644980351228100c00d0004c0094050b10040e2410a4003151741e2044084400c026a1051104034001d00802004220510380b009c0501c000562002e400f01d50007145038200c0000b400c0042103901400028003000c01d01e00405030b2540541d1b1030680b8000b81da8209030360040e05030500100f03210f14641c8048402e10000720178806100d1000d40c449008910350b11a8400101140002081b095141401208100c00270707500100f010701a900581d52151041d000c8018841c0c40101290042d0101313002c1c41c91441d45000014401c099280980245103410351100c0c505032020310643c81e90085 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 334311411 1250 334310161 334310183
    0x12050304031704081c020913061a040b070b0a06090c030b03010b092e0b16030f05120c07020d05250f0303140c01021c1a0a0f1202011704 60
    0x405400010307410b1091034802d0505107614140d601e0f8079042c0f00340191900c84610040c1810401c04158068541444000303114000128103d400c8400819141c42461541d030000d01003899100d07240022501a22440340701c0c0b9180c4003064940c0025450098480d50006503103010000e10580c1c144110311032107007141d44c0030840046100405d42503902040e4060320600300001030081c0a054400050590308040780c0529209101442d071078610421a80b02c0851030a00260707050418040d2805000d91700c1c400d458581d038086850f0390486440c0141141d210154050703601190110b5000806414407a1000b000300105000584d515410a904043d03401c15803122500c2d10310758103481700c010b08045c0049000c2d40e11498030b0760310018800d00d00640c41c403417a04000143c810140340f0a404990340c200002181203051710101004038001e10b1111440801946401d40080b000d2811a15420480b070400320400240c601b018910307021585072610032410f06c00c940f440c0c8854003000001d003a03c030764085e04030300c50 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 334312661 1250 334311411 334311413
    0x60503010806160503061c0206220b09010f051602040603080a0f03090c05090c070507080606040b01030212010b0307090801051e0c0712050d02070503130501180305100905030712050304 81
    0x460030502a0403480d000710000c251500f6141e003c800d803940300200312440c0b00e007440c007610040460031440f02c01030f4204500140d0040c03d80240400030b40344d80d060645c032044066460b40045054040c143c0440c0c002160741c7d10f049100f0344500080d00044900c1b0030244803142c01540003030110380d00ca6008803120030010603075030780c00e0fa006500300c115121507040a1103c5071440d50786814106240c0038151041440c00301244000f810182503c11140d0300c4011a185640c46081095883c5401c450141c4903604180140106512900a031040150b10a0b1080c0c221390801d10000c100342c0005105004201c01d9180029042600340184d6015000c4120328420241c4020303003048410a00500c0c00d405500208076030030008507054078000c100c0d1803500d0040d494400c5519010060f2160a40103005171002060501017603210280c02e0040702c41c241c036545136500d0011507044e1080214840076000f9001161602c101607480e41284a40520843c02d980c503205299450840c0712280c1d14900c0009080401048 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 334313911 1250 334312661 334312663
    0xa060509090a03030e032107020c060c010603200d03030b01030e011103061003050c030c28031b020f100e011b050307030b1807030b0102070806390403020d15060605030108 75
    0x81001030300c0300050742c603029405d8035207541c0d4041e4111004044802c0400941280d10a1103036a001c0f0ad80180810381c0c49001010903406840c1500050359100c40054010102040b60302d041104d1490190289001e20b0190300c042c1c0043c5001e0300807505054075aa8500c00720b440a1040322012003c1520712038407402e01c0380501410b840d120351074038240341c90701052040359481c60094030360121351034524580e40d0b01e58403e0242501c884444003074410320050911250307250107411040c0e000c0c641094065915628000490761000031070085c491079002161100101480c0e6003060394445900320001ca135000f8203202d442e00b440c02c0d0a100c1d0000403004014032a0041d030501600c3c81126044a040502651490f6042c20b5070401405070f400f80350b44c074480045240d00170f10540004012000503100c09260505641e40704000c400002c215906081d44413110026111000e4641c00c003440c0700b11401e0a05541c203104112900280c2658035101c00c0c2000e01c0044942d0140b60b000d0009603aa0340d8803545804121 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 334315161 1250 334313911 334313921
    0x304140708151b0f130b030a09031b110d02030c090f0711070f210f05030414040e120a020f030c0106150201021801051e030a0912020d0f05030a060509090a0303 70
    0x69200c00d55040f42203086010043c00303860f24004004280b90380c410200c94041c80303640440d8419040c0c2c6102000f00003040d0010b5001288080c0281c682507080028440a901800c08802c001020107240e041c13005501c2c1840c00c020543e05101604941d0105104000104c8040f022104801181e01400030001402e034401440460f8070500320044c504a818041c1019600680380926007007030103112005140300070090541c130030142c7c000301a0b04141744d66007003090301d80d8002e0180c0003000c0100c81c40c450450810707100c0c00421031f89060160a20f00f51800161105510552094045101e2002140c00303200d82800200040803054000089051412100f04188070710311560030156407050125072079880e01211101304040302481c1840e82d600f07001402103003078840d019003000607140c04002c1080b81c1c20142d101c41c13081801242c0d5076200e1150120204daa502a0400304000075060a4130702c40800e014001a6401c240302c40c4010800c651070700042140448100c03040b10542c2d11103800001859014450 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 334316411 1250 334315161 334315171
    0xb040b01031e08030c030c04030602070c290d0e011b0807080c0a170601020115080a17041a07020d0b1603060e06220e0d09140a0e0705030414070815 65
    0x2d50400120706031100f4420303000c01010444005800000581c80d01043c0f4110f80155030301a03421900d50f0322500b0681e055400901800c840416031441211b07102400c1114425150382074120306242c4170170ba5030903401511084066511647d240c218120585803c050207085180443c2c0e40d1035464a4100c2c1d0007025203401070300a00d0040b104200001d1010703404a0211807040031160f030309842d45c0b42c0c000100e00415510385080180302c2018000314102d0800f10750040c040e40501b070945c00401561603031203218460b80c0700e0f01d0450000450310030341045524000e064590300003004184003140c1a140c2140030300c0c044038840030402d0703000c0440819941500c1341c1e1020303012808543c6030300d207001408610381c200c03107070190401c1c5d02c1211100100310768550411010692141709031450039280340d80c090044e003400d0240c0880e200e201940d1500d40d052002210089036400740d5a0710107a2584c7d0000d844580c8083d00c00d660402c1c4d9011810b50b00e07c0d04101c410300506400b401886080c0021070700415012000c1c3c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 334317661 1250 334316411 334316453
    0x105010605070f0303050405100e03090f0a0e0f040f05011b03180209060d06150b090307080f120304050c030a0506150405012916060c080106030b09040605130b040b0103 74
    0x85507201244140201c0843c01e5814100016a07813a1380c2441482c2c40031419061071102d00704040f8540c0303480007101030302c06940c1c1954800341d0101030b44208110b1059030f0007040327883d54a210004003550f80d0340c00b006802a00511503010151010349505007503c0d82c003610240c042e100d03d0070528602da41880794a40003003010382d10b80c11078541603000810003040078000510800545a48100740130b240d5004000340b10b0b46548103000315270794000303000c050740003100c0d124401d004400b4005052000854442032254403480640000a583d50718607665800c0548180c03100e100d20b016401d520f071001c11203004550b008500400080c80c0042c402e42900d01c40c8110706000d0390400004125840c0590380e5030707582c06016808054076255100c0c5074400c0b80030b4546e00c074a060710a412032000b0b201c03056202c01000b46503640c80440680e00c46600740d05651015001c2a0000308060000300413901940c020358010031115100301641d4200d40b0340d03003604507050b01c0a40d0382e601c00e01c0042080007440c412403542042e02031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 334318911 1250 334317661 334317667
    0x20a121b09140d03120b09040f020918030901050d02040510020105180a020f040e0f061306051005130f02221409010833010806040c050609030a0609060b04020304140105010605 77
    0x2c808200c01a0700018000d091040c01d90508050840d42d42156005140241c241c900da4a402c1c1405031020040b101b05a00900c44000410503092254072510711940078074000b5854582100b004487c1ca6100e205500c2e0060380c24040810f895842590003808105140d0004c2000d00b031080c000c02010400309503a805560200401e82d00589a6045180038a142242d0020304d400d40e425074507041081c440060780c0540500304c101b002d0007005203144d0110a00608080140d61f580c03c0519205031380c1360007031990000900c5030b480300400340c540040d20a40b480c01da000d0b00f00280b801d00e0343c1d980c400e0b4458078041e000b6801c1c014400c24050017000c0410700c034110b81818855150207502521459a24040b00c0f41070a100501e01445d251140d5008140381c0d616801c804642e0341c0c0710075a4840e903080c1c501300c4410321004000180781ca8440d043e65801352009001d4810f0520b2a560031004003131032442194815180c00e89420a03941c1c51001d18070850090090902c1030448010660840d00c1c160400401d0107824 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 334320161 1250 334318911 334318949
    0x61608030f01080d14030a1407050711030c1e010201090804060905031c08041b03080301150807110c0d030215042a14060711030f0c030c0307030203030d020a121b09 72
    0x44246580841400907043c6d80c0c1c0c481080300005480f00051440070600b00c0004e01c840742d5030110003030002d0742c041d044240003110244201912400e10403445540444602200d101199182030001095041400005003400403039681040c00c4d0090342c0000046450201d08024a047c180008100c0300264200b2103000c400064001e400400041c0015001c0410391075400e0b0041a4a1100e101854104030f802d42c0760340c0d486a000005882003000c100000f417840c00400c4505000322124002c00407404082c11402c1d4000050100c49094008190114450030509840c082129003907640114080d19a00590314501820750802142103a90b00c41c001101200400c50016602042210440100c540c540d9800c0542040a80605503d201540c54040c800e1005150000003801e00c012030010340c21341d442c0c0d5904004142e114803a521000e50550002c0142e10000021b0342e000340440716550502c07550070103004c480b98040740d03011b20114500c080803614501c3e466800c98442e500a19810071025034400c45 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 334321411 1250 334320161 334320167
    0x16050304051b030f01023007020c06030709090504140708060f0a09020f03030d0b1f0804060b01090b0c0708060105100e0d030e1519050307050a0e061608030f01080d 72
    0x5840d00030b5101c0522440030303560360381031001049101426000399100d405202000d005203c8070b019845030103001100b000d50000714400c58511441c0550017503c0440d01d181d042c05003c0c0c2c0b009240c00e00f04054400045800f000d213200c0e19008900400c8020604490b007040240361000750340120565501020402c0060b1180e4240d01da4442141180818590014404221002c074041c40081d403500000c25800a00700590744041c81c50b442c1250300440c081a5107411040c401c0c19546000d0004018070002400300d592038000801d0250189050000141e54034103c020039007200900c00340c2d68102c40002c004c405420007070140036180450f01c0040d00d400380c11001d80b916403140c1c0410301030340d142e0907c4028903004a00050894501501690f400326612420815a80c404408486841c61246034010042d03c40d0301130301d10505241c0c0f546460900d202200b030720403041c1d50641c9a4050340c10400748031803074280079000030002e115400080d100c1c08c1115540b15503d0301600901501e1f403050f41a0f401881d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 334322661 1250 334321411 334321423
    0x311030c040e1903020a0b01060507150b030c1207030605040b150108130222020d020403030216060818010e0102070303020327030d020d18050a03090f080a0b18151605030405 76
    0x801c14005440d101410316059007800105503021f00102580070000456a40000003020f040d40305001d003a4060243c402910200e540040780302c0e030594000d1015003c24181408040205e11000382290a060799a0f50381c3c80590314119412030707a100c284400d00c5900342049e41640481340703003403c2c1203680789000c80284004894640d0068421405180c1460ba1141c044103100c1008804450555443c107503403000601a40c0300e071004900500c5210301c8803414080c0c0031401402c3d180c941e503a0b403806423680c40045522601c044400001035684030b1201c00085404d00c001c11105110382c0740562645056881e20321841c46071500400b084004100081c0310010103c2100c10101d002100140c58444483c107100007040d00e07500029480d5a0b0709040c07401d1140020f502c0c1000c1b4840c4d50b906811a0b281d000110008005207d40ca42c2c903070046403c1800182d03224000e03a0b02103c03541c04003105030381e42d000d44c07480c140021806036400c86000040c426100c10ba6030030100341200d28202145036040a942e16680e4035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 334323911 1250 334322661 334322683
    0x130206030a020304151b09080c06070204230709050a09050618070201090218100b040f12110d060e07090921140c060703290d02010e0a0311030c040e 65
    0x741d40040054100162403450208049101c0000c200d92901110303402c02180711a00503034003141c20300328001040701c00021050005000078004d1410001a0750034003000e0440d1640070012912002c0c4842c100910340c008940c42421f02d9603d00c41c1403880c00040c4a107007422a0001140141810100701d00c0713071258200001c3c1c0495a4107000203a64445204900404803040001e41c04043d4400d110900c14002890314068251040f0a040096a40c24070605d40d00c1036104210001c580d50784200407610007404841b0009002d051031410320f4032010000307260f40d42c0460084451356590318403d17103444d0301000420f019200c5503008001d10f1031b180d1162441d03c8403045603031001d80c1c196044000d81c50f105d90328006220201c0d001740c42d201c11000d40b1458550344115918000286040900054059003c07200c101d43c130018107000007010344400901100b001c0a0700164140055184607802d291642e0070030000550280803d454521103070000c042c18588480007881c0300d14100700f003c032040d40c0d000c50344840603 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 334325161 1250 334323911 334323931
    0x501080f180111120604050114030a1205191709030a0516080c030c06010305010b1f030b010c1410060b040b0a0507030e0a030b0403020c0d0302061f0909050c010813020603 75
    0x1020105034241c090100c1c010320000d0320001080614840c4182c2ea44c2034010001100c06000c541e0722010315503483c92404030500e034194020a880004141006170403031081c1500d14166140810b0240c400352410b10441e50321000400c000040d00803036000c110560341000307250019520380117800c8001041802401307144884640b66000c000100030f031403021512103d0309242a65298900255040c0d1581401d210940c0c140d420500e1003842031402446100b120200b0084081d60300704607040850050558840b40340c1800314480701d6401240700d00022454141048005152003030450400206640b140d0307001c1409200107000610200070080e05641c5071110318601243c0740c00090404031200102c0300c0b64960042c41e04d07240403003403011503049039100318003a03001c503030700302c1104014049501d80c0d9000140044e00b010001c19007c00070100035880804d46c914900c62425204c1065108542000724103d03201c1c0d00c0140420003a50300500d03ca80d110a544c600c141072503000c0e401150040c40020495002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 334326411 1250 334325161 334325191
    0xe060c0f0904090204060303090815041a180a080a0e011b060e03070b241903141e0601060807050724061211010305060316120507031403090a0501080f 66
    0x101e03440c0c540c400e051440d0003c00a1243c242d40c0d04018091100c140070f02e9407036000e0034801428500384041004c0c010b40d84190010b07201505581d100c05050300c040c00c10f0010740480d0403902c80151080000c00b200c0c0b0f000e89092540c607286280007500d00d1101031411418031a0009101c030142009110001d000c40e04400e0220b640b20403041030340c1c2144102c500082c54a82000103124102d030710421903500940042d0320b413481c41440241040440c20b204d001404003c8001d0105000040c0c0302c03208000d01d02e0000044400d4040f2a80008001710480400000140e0080d0010843c0a50040215802401c2070416038a042059144c2c075403403094400c0340001c040805482c0802e172516a0344804000c04104040c03002da950645818441c0c0558912114002402c2c036010411070300c1c1c04101c40e203003040741c0f00c26858074914250041d0908500f07000140c03414003580c44c00001140002040c0107aa40c0e00380003540c0d451414000300880d0784e00581000e8108840d103403c01040c19040c49042d80c01220010b44212 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 334327661 1250 334326411 334326427
    0x8030411030d020c01390213020c0606041805030a0522120b18280c0609033e040f3b030f0a020a02090103080d0e060c0f 53
    0x8215a030300e455150148a074800146040d940072607000200c04003640c03155a501d02c00031000400f100c0d000f02000100041e00100340303031404124800c02c1280d2010740202d140c281c454080e01d0898001056859454021070104100392800d03114400c400810949640284407140e22030954030300451505906012000073720003222070f0b05220b00340400d142001e02140c81c588405542d5001c0401c082c003154942208000f01c0c03020350b4007120a44010301c04030010481403a4510205c1080b4500341458160454400d00180116a0164440001d440140c8580c20030518514011f07088011803504500c1260000c200d6284240040381000e1901e4100c20480800701514030024004160280319130404a15180412100d0301e038610141c40c010801d2080c0100801c0022150076100912040b1803409410811a21000010040190885090394412225507000d03581c08510042c07420b0b002950b90b02d0740482c4c0b1568034480360240a40c1c0d041e00801801640c00c100452400c1030142c00707040b030402580425805 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 334328911 1250 334327661 334327673
    0x503041a0408070b25230d0b0a060f230d0c0806011404050303040302060a1209061d030a0206070e03030d06090506040b0604060e090402060405030a06051501020d020a080304 76
    0x9a1191004608003020300702031038032544592259100321580708a02c0001400c1c074860444d5880c0c105449448000442032200d0300b1103402401000003401c8a00c4c02c0401c1c854408228041c1107980007d0790001040d008210411680340640d5201104105003001c1d8481160350002d00c281e04c00300d8030280008980803e00c01e42d103c0340075044891400b240b50007001c6000395403201203a8050202030302e443c07100284810342d070503a41c803c2d8000c042d015402004100010308000303004080e000f12a1074080141d0b440040038000340d03400c40c5426076405858249880901050714103808420503060021850805920710107500d498000b0510002d01c8496880340c1c01e140c50030702c01c940604140020030000340c1e4a900800f001400107039102802a460070359400018101a41100c040e15001d89508018030010320400103400070082049801c540103000c00196904d08001c5608040e01c94072010032540340542400e07200000702d004590455000301d42d10708a013500030814800d1681c001d91500c0d583e03903aa080c20 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 334330161 1250 334328911 334328933
    0x703081602040f0c0309060e0a03090e180706030c030c091503270f110d1e02060f12040201110102090d080f0712050c1204050a051207080105130204060902070b0403050304 75
    0x224911074284a802d0140c16417540c0100c1600d44290420014008000075042d950702035030341c0c010042040040180030b1544034000e00e55000344401e440968035450480000d0401040303503c6240440e40b40c0c000807114039010f0180301d00190461810070386540c42c1c00b1707821100516800404050547e114a403100f0782c1b04803405038030720840b00184055507020b145020700104001c04015501c6081c034404400d03041c9403180d10400c1454110440c182003003401c1c03c0d000800024031208130b9000d00c003001040640381861000d40404030051540007200d14050001410340c101401550b41c1e0703644100400c2c03140e6614480301012031508505401d40320345d801180300e5203034440c007000030340b90304ca4a40d128152590b10074010528181c0200545500e44d510240041c440d000e18015141c2c0f0914280003404035082c02c12440c500c150104040b05e80142d51852480c0c2107e5040d1400d011a400035442c103425030915014107002852607000451400307500707880700490b010300944001d0400070000302180030300c0118400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 334331411 1250 334330161 334330181
    0x501030507022503020f060705030901200607030c02061503120f09060c010203191a0112020d110426150402120105010801021812070501051308010e010b030f070308160204 75
    0x1c1410f0002503000210343d02c082900c0100d1003176a00c000150f140381881c400303032203034070768840e0042d8200f00440b401913620b001d880e2201486032202c4440d40d03140e0002013043c0d501601e003913100042c0940708480000e052403001482d1002e0706500301c505800945001540c01c0352036070805002a140c100070481c07801c0070702c10001450341c420400705103031800c56819801580a0306996602420108101c40c0140a4540351965055800040000706174507500a100000391509011001444d00e01420391200c11191900d5404151110110b8184104a180344040c0c404551100f00e002c2d100d0b105200c0c2542d9026003132162410036066001003030071500d80608841c1e06001210013070025603100c0fa0011700135040302e00d0041011001c03c25441460515003145a071145000340601b64841c01c101c01501c06502481c101c0b60036100030040024908070a1003580e22a00d0380000109490000c41d007010319003c940e102e410348a070420081040050007400c1201c7c1100402403442003041c0460002400901c1010f032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 334332661 1250 334331411 334331443
    0x110a0909060c0806010c2f040f0615030225050708030403050a060b04020705030a0305060303190e10020c1c030201060b0d090c230d0203010b030d36050103050702 71
    0x201500400503903070030200c0201401c0e643c564050381c514004481c00c445840014000c500d00d01d010148441200d005490a000841e5600452614a002041c01c880c0c4000d81c0d1035246558000c20700880b42e034a81074072000e00240c502903061081c4016240320394100d08c03001c00004c154580a032400c01900f8040c0c24014000c2d441aa52250380e40d081c043d884110124044681e02c1c645442e50f14145400d10965501c5038002d001182808034522050b8020b00e00a0103455241c4018415254543c60f20080d0402288440d03983d50022540f200500841d444504d016030150340000d4074503c1d1540314404041550540102070641041850070103900402240d044071401260010b000100403403540c00552149110720f030b02d209a1681c503c810449480d4161070034050014800c81c0120901d0404500341c0d146000900002d40c10b82e14070f00180c90500413407084000304540c604c40000710440720f11a625002c1e0b00090382900c280c5010b225124074030070744c055541416075400114003041e1080000940c00f5030803003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 334333911 1250 334332661 334332671
    0xe0f06070210290d02150c1f020c0a0209131707050d142a0106080607170613091b09020d0f0204050a0b0a0c12050d110306010c110a09 59
    0x900003512050340341c4548032003508005034200d0143e4a0104820281066007a44240c3d1081004102000c0075180003030741e10103040504c0c200358040b01002042e840d500c0700000d021080c41060540d5048151080c0e640305144148000300c08507201003042d034080350b03045401c00b6183d501e440c000304204d201c070100a001204000f5800e061019298000c10b280e0b40600200c40001c07001c0001222002001445100d42c88418016405030501605c3d210742c030300080d150741c140c1100a502d130050031143d6941c02130303999602c0352041c8030700c03c0d0300180aa401c5240501c07503a4207501c0c200001c01c5211164003c026100c0d659100c8030014003100e0300c02c41683d1525280b0340300c2c0c040da0f02c00f10031004c2d40114264058240c90b001c041340010f031140c42140d00f2120b02601c40700f81680b8041030360070b1941100801c0c0701030200340c03243d2400080302c0d64030504070020a5100d498580342400781d4402141e5040102e040f2900c001c0080c0031840ea0460061000181d00440040031400c400b0701240c21400b580d880320b2403842c102 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 334335161 1250 334333911 334333921
    0x403020105100801051006050f04091b03060f08030f0304150c0c05120a090308090303040e070903231e070f03050a1a16030515060c011b05090a06030e0f06 68
    0x1900441e000310300b0304030318050003a268440a400c131601034540004440d200701d01000b219000340d0181074107130b1210540c1c5007032070f035928548001d03a80d0110b000da0303810072203080c2c0151982d090704c03170314000c1c102110307060710350074203105105680b48201040070000c90004070000d410400340309a4009a03081e4044140845140c580e00904428001c58044959004801b2201c1b02590650280c4d9600062a07650384070141c955180c4100f03a600480100e80c26000802010840351500b9001d2401603005a80740f082c2039240d420051312442035410005040c00300095500c02200b8005000c0032845521110480c2c002d030403400e00e0389000010381c055400c810450b071000040c080e0210340c0242546c0115090080e0604402d00902d03007034421645032828008500200c1207070351082d809103920090b69182c0e1b074030040700c090019016820a11051100f0303174407260035207203201e2403000192403100303d414001d0401d01c0220000300704222602078001019079803411206404030810040080c0d0b5000d03019600d4078100707 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 334336411 1250 334335161 334335163
    0xa05040618050c03060d0b060a03060e0a0c080a08180307051003021b01060509040b0a1e3e070510051006090e0603071403010b2805060c071715040302 66
    0x20844045002e00d000c0c0051055000001141c0c0b203400000c2000400081941d0f0708948a08044c3c40c0d42c0e004950140080000b83d540c0c0720b51101583e0b00720003410403200602d03050884042030741007080d40c0e8011180100001c0d1506040c1e80c100c0e450401da0146140703800c40441c0c81c0a425600056000d4144101000156007580c02400c4647c009503402c1502401c0340142805e9800c28840e007a0003501200010b030100742816070054110f21855000725090418680b280b02c03c0403102d1010f001b0316504c581e982081025541601c80040418602502d502c41000c040020518503400b0090200720000707404d010044240b008800a6034048020402410a4990710391040300a0041001140206070f0124501e1404000d03103210700310080081c0b42c55424808005091029508002e806d992650707644640f55890b0200038050b4151003640414000d00c0c929046d141200682c0001c0c0920020000c00042c04004643d0742d0a856008c5803800c110001340c4641490130400c2c0000303205041c640401e1001b0940c2c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 334337661 1250 334336411 334336439
    0x30e0a0b15060705061302060415050a0f0e150d0e10020306090702070e0606090d0b040605040c17100c0207031406040201020c040c0f0309240204050a060e03060a09020a050406 77
    0x6400802080c029a0030350030702c0141e116091018215502c100002001181c120512104076880600183e0074290b0300c1c0c0d10b903038000c42c2e24201d480200300c0118480b03080e65031281503000d0186251821448021072007000c40c1166121450003a403006000505803195030194000f09204050a012507000030080c0c00010020340040e0f64030380c403501c1101c022913802c510000b804419600c2c840549503054543d5000c0040c160b105049075900141703505035050119001c400350314403ca0194001041514151615484580c1582c000d43c5a20030220002c003501040003038503800c6000480c0c00045c040f000000280d2030305a8643c0b0040100c880c401e05004410004515180030b0380c1f00f0317001c842640d4484410403080e9201507a899001884102e00c000525102e0b070450300150f4020910b42d1034034094103407400c28240d0040711184241e0313000507040140b8100001a980146030724030b0304002d00d00408001a882d0324000d006c840409841d40090015907860094100c01804000c1003008083c4ea02c07415036134006 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 334338911 1250 334337661 334337671
    0xd0b060301060807062f060a0509010f180302161a130801020c030c07090504321b09060607230309061611010e0a0603110705010e06060316080c09040201030e0a0b 71
    0x100302100b203100c521401e1b4070710848000380c65001d8040c550322180400c00600c80100808420741d200c1e40c8a418041080c4a1020040103c2240b5002c03031000307003000fa1074441c05900c0304900824820040103224a021031036043c5201d46c024550303603203101c8801415880615000342e101035200050280c00054000001e12320b900c09a010740752a566034554001c11500c003141c000d8100c04448203160341030b058201c44140c000e208044d00700d40150703000b04414078058100114148138040c0c1441740320b107483d00c5244030368480001c0b55041d28088090b5961082c0d501006a140c80d050b4504c80c5168503000d090054a00007040502800c2e03c80b084258a10380c01c000240040c0c585010301c05159040c0c2d441088001c042003809441c0c040007520707103003045006160b041c40ea00c000000a0190100160080c040c59500981580050842d403c0c200101820030700d1900b46602012500791003009841e0300862040c45003030040b10101c40b1555680011707406080d6440c41040d0394080c6252880800c10300250b814011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 334340161 1250 334338911 334338947
    0xc1406010e0c0405030309040f02130b181f0813050610060906030506030703031d09010b0405010f0206090601091d03030709180e060604020f0c0601060e010e0108060d0b06030106080706 81
    0xe40b6190b444481c10f01c100c0c003506130075800400c4a40d80c0d83c20310b50415000c0355a5088014a0301c9d0702e040c03020040c0001900600040000050b1000c0014180c003c0420360440880360807243e8091089200141c00b04090340c0e03014401d14200250322203003c4c00d0007864040d0081e007a112035182800d0540c00d0b6070003034041d40300810160000481c00622030301c2050710071180680100a02400d43d02d0903101d450046600121518000740113106603195105d030071f130003080d0003030070a61903500300800500301c6140145102c003154440820420301010002d003d50450b60280400260041c0d5030000b9200181c01120303004481c8400000d000440754000a850100c0d24507075482c0041b030001a400005460120340c0060301e80c0d00100c046147d0f407416500401c1801d150400700340c90480c00c0e481e00e500b400c009034003a9000c280c14444140c019600004d0b00c00125400f440c0c51101481e09000042812148500c06440d0080900c0001d1594800f544507802070031a28044817030b100d40c0c42d00000c1417016900380704209 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 334341411 1250 334340161 334340189
    0xf150a020610090b031e0309030706030209030d0507030804060515060a0f140a0c0b060a05030d020a0b010504050103080423060414150703020c190f12020909070e07030207030c140601 80
    0x4103440c01d10135010000c0340100513120380d18614420803c103900c59444141c150000f0406007000c0da4041019000500c02e549000d611803803c20201810203004481c2d03102441b404200da00b001981c4140c103940e10640c80040000c9944854190007010a4103401d2560840000507851403100c2d003121103400e5030903c43e51364080b0030b02000e000c0b115900901180c0ea01246040319074400060310703c464140c0c4180c0c040c000c100303070980e6100080e142c042820400c10140e000524082c0a0002146203a4054030313068400744915491607441c14410703c075500c900800200e56143c14030980700c22101640780d50100519031602c480d29032121505618081c41e56510603a00304400c1c3c2c40d03010900702070340c2441c0c0d01030f0043c00b240c0440340c0c280404c0030b280c1d03449041c4c2864030722804078103074000d401201d002d014801520a582c040903c140588802d01130880d54030b40c0d0140c142041501034a04c01ea0741d1054103441c0c050703100d0070541703000c0d074105480f404028212540c00e840706101d840002402412034400c0f803040a4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 334342661 1250 334341411 334341419
    0x1110020f090f04060305031b0c19080f21030c13090e010f050c0a141903062c0105100c0b0a2a0c0b0628030c0506090a03020f150a020610 60
    0x7044501605c0000d142c1d80045c88a2500a1000c2411a0000084c40705070790440198100040c100a820201d821100400d60810700660b40104050340790350104100421201401403290b018054204420504100c2c0000014a0103002c003401c1c0c0f600300001300500c0d0880d5840c0c4407104003500104aa096241d0b1800c001c40041101500805016005c00d05480b441c020207054200c0314164928000ca04800b0100b140f449449040031082d284072107181d0b030004080d4144007205200e070321000d0300e0500001101c0c40c821150080640b41c07504607001262000c0008070007240c02c0d00c0665907804054003048000d030802155002540055141e2a0842e10091b12801c4594040801c2c0c24183c0a0400099a600702000000c2c00401c106400600c002d10f00c4160f040108803c0c00e03c800071240d4000c03803140d19103042040041044190b009003200722040c1d8105141f02c2c001c0340c1009158440030744604c031001c1000c0f000d910390000074144444043c894541c1e0780303034106d000b035a00d03502954401c15030030480c68006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 334343911 1250 334342661 334342669
    0x9230904140d0302041802030408041d06150301270e161a040e040f03030b130b010e0a080d12020f04120c08031201030b0601090509070207060201140f071110020f090f 73
    0x101660071b01c100203401034650710312040094100074811108900b08000c0400c0c4107210300a031038054440001007581a00d005828480e040460001140c81c0e424240014800050800141c0c14641c0048a88010b90402e032240440500103450198010b4065a00094242d54840030b00001340d45828111000d10042e0344800100d503c294446e0340e07010710f001008140040c03101c403802c0c02c029001e03141c049040303103001001901765501d5803820341907140c2c0e4445072540781d40c03c01d60455107060708440b43c0322545c1c0f4050445850380d1441c15950708101480d141c02d034904852364151402606000041500c032612001800c901d400c0082e000d640c200b0128000140c00000081200d03040f209007028103846910716078030750b01854005030541c0c0c148131000d00d001c20310380c6a10001b03601c05c010550007008054a0a0340290844402105001a10100e00b08000d81c000d0880042d50308000380b80b400341d03a81a014040d03a07040072500c402e81c00c04a0b0000401c5c1a9001002c000741c4640c01d412600c12030740c1c441c02c000300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 334345161 1250 334343911 334343917
    0x8010608250303050a02070308040b030702061302030601170307050123010f0308070602090f090a050a0c020a050c01200304080102070c080309010804111804060507090f0609230904140d0302 83
    0x40144428081d20920019116401921030b1980310b00440707a0310b540f01d6417001c5041d04281c1004104d41004000c000d01e696040144c00d030418001c40481e480d070035058001c29190b900c1401403403191811141034104014040040307a20f00c68001c4d000300901c50b9006101840100c0e20128002520b07600c0e030001c10352804003640039080720f501029803441c040081c1e07102006900244d00440e80100001584240b54940401c054072881022200166900d08800d40c00700b150b08007100401150300030200320380019030004080f0000107090130110044a950203124090000314891511310703010100c2c000813540415009010810301c40d1400c041e1644e12102c09076900d02440c83d00b103001903500b9001c6404035024852541100c04007030046224541c1c01d00807040c00f080305032411100d0380d59030000c00008950042c421009480c2003d1107000807441c1410041448015015014101c00c0400520400801d030102244119101410300d00140c03a00341030030071680030f401c1160410350003003802d500b004030310074421 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 334346411 1250 334345161 334345213
    0x8010b010f0210110f130504051506040506070203010b100305250e040c0e03120417070b0d0b0307030215030a0c03050702030f160501090f051209090c2208010608 71
    0xa0004a43d48044000a40012130345a09a803078100320100c00014907000078280880d00e0801190b680713241c60244802c4800052000038260303640c034508449551507008460072214110f071085e4aa400500019004141409060780e0101c0c400074208156a05600704a1160390650300c44203070807600d5000300c4111104462500000740c950281903915240960001444030b000c0d03c0d005c05d000540b82c001c42e1a00f20940e40b00d402c45000401c0400100d0032100d121407104600750050410240780645444d020702982240a550640700c1d2003941c0180c800b00000c900550300200013040f0305140b282000101c0d44103441c0709501c18205860031401c3c601074041e0074012405980114980f0104201e245419049000341e40600000c01880b8800305209000d00c480301d50290720011400c482c54070b00203140280b0052002ca070400c0601c40c042070b9a45134840340750702c46030303000d07015035940000079200c500c0b0806001840020720300210080f411034015841907080e03500c1003088986050700c2240b000c40c40c2900844d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 334347661 1250 334346411 334346413
    0x70e1504061d1203090901170d0c08090604090b0f09060108130804030b07030e070603110307030b0409051c030606080c0708071a0c131d010b031b1308010b010f02 71
    0x110401c00d0a00c1246030300340d5101c40ca01440205030114001030440d640e80120740440764070114546501e490043e00c6107004000700203444082d55040e039a441d8507000e460303034050140098401603c3c05d20500030101c550401c801081d03030303a692303403500d4a090080c140f00d507500c1d005840d021040e40c640c0c1003412040740101e0050710744181a0b540c2c1441141c41580d4154122504135003400000000394041c40701a018907420744003c1030b010700c20b0381350b98902000caa00c91401c05040040501401c42c10300c1c21a42c21101500c0e020035503241880104000c2c180d00040204188a403096a0f21124280b040c110a00c1000740d6013444455030301d0f14210391651040e5502c60304c100c01040034200040080d00100030083c8030b4070a8544e490900840400c6042c01100c11a58076440090918440c20b21071500c280600b9440c908640d5520458070103200c000d405025007203032000d001000c101d41115072022111007100900801c2d985443c042c0c0d0345100c03040680700341c9429600700109564158080c1c041d803d860b6103181c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 334348911 1250 334347661 334347667
    0xc020310020f09060301030c0501020f150a0b010924080912030105091e070207031a0c16060609020d0f0608010c1416140307050d02070b040506031b03010e070e15 71
    0x1154001c1d8051a55408046020809500a43c80704d8015500960107100300601e01451b0034000fa00703004050641d8001904420181c49285e0050384c160f42c3c0101d010300c40010f91040744001030392480a6500980140401d90200c840749800070b20700c212400b101c80d81e070760415449141046903114aa1900c5030700c02d045c03d20051205050040d1407031b40c0200b030301c0070040140b50348a40ea010030f86003c1c1e54079030058002c034105005102c880b1860400410f00c0c4200b69003d40350003030340800140584c940040c001c0c0c4401c86100d00340225500044040c24204400310b64a0b91200c0c1210000c050b98001d40c9440d81c02c241b80040c04180600c1911804501502c032402d4200c15070290071500c3d07100c80040b4034101da40500540110300700b060458401c40f01200110303940d03035144c00c1c0545440c4000c00c0610466100705030600005030103a00342e80455106991742502c0e515101d08808264a1003082840f4464000c0000542e540304114024052513894031555003407001441441807048881c0103110021600f0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 334350161 1250 334348911 334348933
    0x3041802130e1e07020c0114090102070e010b090103060905070e0613080d11190c06200a11190b0f030603030705011e0b122d0d1e0c0203 60
    0x40e030010681100508940c031074030307901c9194141d100c003001d54080440107404600041000250780e0899000312007800101354071140b110000709159400b4110b5100c11001184010f156402084440d010703103280350144a10b585c403400140d442c1c0d013007408400d0000f0704104001980543c5482510f00500065031009041a4030b001801351031340c400044d0a070010f41400002441c52018000b1258418107561042c0c182d014840100c0e260040e54101000200368148070300c00050040081c0700c04a5117181400e20740403004020f002032130210300420504c180109e1a003441048000c0d6052421a01d00702c480070321001112046600901c524081d0404801c000c101d891803540004c406960300076001411607241a2050341c2c3d990940c2d080c40600202d4007000d203110541c17030000b40902c00700444c094030740c0354080000940e170590342c1c828845001804220040c4404079480203810f03040c1780f041694100c40c10022110801030000215040703100d5282e00480103104010701c2080c07000c40854009000f8503400702d00c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 334351411 1250 334350161 334350209
    0x11b110319050d060807180c0e12010b120c1801080604030311041d0a1b020c040f1407090311040501030305090f0406050414011505030603030a0e0109050627030304 72
    0x1c210700e920030310005006402c84140103002c0d150107485c15002429096142003803094408005203022403000d81010314503686c4550080700440f1062044402c101c40303212050410b801484c1005245400c1562501e09400030304001408040340703401501d041c14107088808241c205000300380104031031380d040040840d01092180e0031110403107110a0071149410359034803492083c0070320b80541e42034200c9001c003080446407081c071501c00140c402d00f0005611099940c0d00079154600d00b40b0700c4d0704c00c69075001c460ba84c90009601c1901d4004015003400c0113400d28450281000003140701c00c46030719603481900d010b00d08043c0107080c100c175410b03103e4608040d420410400c00c0b220b42100f044d007281da12240051303256145e02036209400442e0850503c6075060003403824103143c03400e800c003040c040200103002c05524000211a241c8103280340c02c0c4031074011140100e4582074140c0c04694404c90118488c250000310310071008014030b2258100610801d640c0902d500d0b40194820502c440342c18680202803449 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 334352517 1106 334351411 334351447
    0x1e0a0215091f0b031023010305061603060506040308031918030e0a03030816020a0b04030e190303050a0302090301060b0706020a0f0305040206040b09040b04060602011b1103 76
    0x30803c000710341d4078190f00c1042810782c0e079560b000c6109007104072030762002040c0081c0880c0c0256075a08000e44c0c3c50740240c5c0c881e078544040340f4928040c0c0d0300078440c0740d0440b04083d214a040c1480d503140c40310583c000a001300744010440b407400203000f400740700c0c4c111705c8441d0014400c1c984000b4207000340301044515082e130183c843e0a03014008680c002e5903680c0c0c82270001c1c010b02500904030504a0030b110360668010a181c400307030188400c02d03400120651a6030f500f5581800b400c06c01102c440390041ca980300240100d003040080e0744405210380c004010120700540081045540c0c0c503417840051b4096081503401c2a0b01180545803c1c1d802401d5440500e0903107010711550606030001032051081c1d200c4c406a8010001d2807403603940362604402241c500040041100d65503071b4001a0281c4445c40441d5100c460902e1303c40c00b4513004540751034094812070015410104005c00e0940400c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 334172661 334352517 := by
  have h0 := BRFrame.cov_init 334172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 334172661 ≤ n) (h2 : n < 334352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
