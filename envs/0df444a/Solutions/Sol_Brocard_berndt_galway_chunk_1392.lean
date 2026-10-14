-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1392
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:45:03.635166+00:00
-- url     : https://prove2.me/submissions/a8608043-766d-4a32-8ba3-bb83f1c4343f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 250179856 ≤ n < 250359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 250181106 1250 250179856 250179869
    0x30c0516110f12010207060506090108030307121d10151d04020a050603180d0c02060d0518190308010504020f160302010b180603060708070806010c0501020f04141201060f 75
    0x188029000c5645a20340d074403820510007450203d100024059640c040d5010314411142541010080b030880e05248603403d059401c000055401c6903200c400450f5008003810307014040513121208205507841c0e400c1d4410589409001074140c11240140ca4400c1c0c6240307400701d940e501c80890080040c07210000c1003603010381507403500012a450301c0c00082d40301c010300d070019039208000109121480800c481c0c2c0c0708500300e030202504c0b11040c02031015544500281d5001e50040000c000c9594103403d65441030354002107e0300380b5502c00c0721030a1072525143c5040d00701d801540c0d0a41d2003405050704440c009004040454055240050906d0054414003c1b0410005404c40201d018402c01d8001e420541e5000d078042e1840603120354002403182a01401d40740c0600a0103454046a0564482d601e02c601c902944d488100041c1c8681c001107940483c49041900d03155800e200407000d031000200140b0080804501e80c81a20900008000c0441d452564070384c043d078075240c420410510410006422602d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 250182356 1250 250181106 250181123
    0x304053c010e15070b0c07022106040609060e060103030315090b03070303050715051905070215160909060e06040623100c1202010e0c0a27020408030301080706030c0516 74
    0x190070740f1518240128140144001152030411012000401c0a40b03a40c034000c07207405c00b4030042c050010b00b040c0302d1040141b100e500080c001030b000c9205d940007640c1e150302c205000601486034100150410b1000c0c0c0086002a4980c180340c080360103000000000b528021108010f142302020002e42c0d912814807008003400070201d041024455404015410785011120500c49403800c11540740508880703803000d001d26860a40803c29040c0f00140c0203c43c2c2c1e40c260b801c4030799034680c0390741d00d1415003003821510200603a060001c07503014407a000b00d9000349442508603038a030601c1010031068580a410140c080315503075890a00c8007a024940300414201996803407000b4903450001c4031260030010300603010700074990412032000e074158008031090407507174140c0c0c1440e10741c58100240034602e4410305107050b02030000d145000203030f07510700081c440c120b0400502d016510001030b415600242d00c034003100d80001c00704201c0c950709401f039640c802c0010304c0d140d80740c821901241c102185c2156005030007080b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 250183606 1250 250182356 250182379
    0x501050312160305090a03080c0105070804030e0409020f060715180f0303180807050309012d110a0f120e01020105010b031303020a050105010909300c050304053c010e 73
    0x50190b012604002005011b8030070403500d030300b460000c43d44242e80c0e00c0078540c41e20001844651042082e01e01403507065458101042da000104805892000800da0348446c151400000c1c81d40c410b0002c109151181a00c042000054402181144e18440c130101c80b11444502c4035000a13034040b83e500c07506a15040001d0107030704500c500351030003180100c0103010020000382c00d020301c035000018000802090741c0320b840e0740fa4051328015004410010b8520f910160b031000902c0140038010b09000d454004044070034248440d109c610716048058800c3d18044101c4407941c1c4240e61111b80840e2102c0217000034070a030f52528140319964070000704200c02d0000e180c4012404c0520920101c12200d42081c000e012035615162000d0083c101040115003940c40403224407100f200001d6118203c00080030480300f00c96100009480880c0210030854140c0010440404c041e5a0240040300c26448405020302d02d4200000804a00c0c3d018960004180c0c0b440c4d80c5801141c0e4840e080c00e03c4840103841030000315 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 250184856 1250 250183606 250183613
    0x609080114040305160f1a09010b03010b0f01050a0e1807120203091914010501060203030a0e070e0115121e0e010504021e0102030705030412030e09010f0b07020a05091504050105031216 81
    0x1b00240c0c6004064013038000450a082e4030003502a0300540740030300200003003031036542014220741c181c181003500b00700441078000056018001500d81040c0c0d5060031050034040c000001c0181158403c0801911844800c1c402c026034000204200380d03001000442c9142410b02c40c40e50b494802c0c4034000e1010400015034000c102c1074849083d048400b0314024001941c503a40c0180d12500121103803010a4a00a1005092540080c15030202e82e80a42c480641d03900b000d02e0034105801555024040c8212002e0300c020046403885418400c42a4880d46030341c50050782507507820340d00340070316000300d40e81414140005039a41e031500340c500380c0f44c43c2c1e000108640500300603400e500030340401030100c0c0800710380001c045c01440c4002280303d01c250744044c24541290300700008d8990a000b186400c09440781c0511001451000504820b80000d00011703140b80e41c1c00016004110803100f4094003040b03a40028001d007424003405002d054218043c0222030300107107204180d4094801501c3c1c090030208441c8050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 250186106 1250 250184856 250184873
    0x26031b0405090708061212070b0903070519020f0103051e04050c04020c010b0f10081b0f0408010b04050907082805010c1e020601050d020f01031401060908011404030516 74
    0x1020007409401d540d1411903c043c100c0c0c02c040780c40600408514005407284c4401080b1a00030031070b603c040c24200710041d1a02d40d40450000c2c4100107504c803c01800380070402c104a1145010403c0d06100c0103051284144081c449079182e1050605040c00f00b8803001c0b624450304541d08460810600c1c81c070380c1d5241441c81ca049004050b130343e041440080e10980803001904038088550b02a288240210400418841c02038501d2244200095401e80441c2206100c8503800c0c110101c0300c44100c0c240503030000c0203c125402944020300b9030b95654192079460500e4043d461b132041031200581405860036100680322180e441c5420f0000c1c40c000400229a500d168900c0c00180d013000007000f04400406015000e00c080258140785560500103c085092000403450b0503181d010700300c070900d802d0540c24040340c0200d4460440c140743c3c42d641c8400c201a4524207943c000c7c13030030341c2e120152540303020305240c21107035801d0358804d8055141e020400031a4124080356a40c1003066014203002d011810001e50 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 250187356 1250 250186106 250186109
    0x22060503061309030e09090c1e06070b04080d0204090203070f03090804091e06030609033e0a060e1b040204030803060111030d0c05090a0503011505040515090a0926031b04 75
    0x107200040c01c0034400c0201001842c4200051b060314152780c003091a40301400740b0801c00040f941e101904210940000303440d07071503080d041489010301500307101c0c4044091007a600213402c241c2070184d003c0200110190712941405400d0706508040180f0303c130a807a000614411070156080350758480656105070020714085e2102203105450400010382c0b00d140150140903164401d40c00100d4880c03845c241000c4d00c0c22081b0b0114030202c001954000c0d414a8606d4103003902a02d01010300412022401003560350103007060080b008000b8100d04280b2111984496000e0b0140300c0c0564410b00003403002518203030480390440f10900700384da40c0e070304400700c81c03072a611504500c00009800e0200480a0b80c2e000006001c0c403803021204410250380320024142252220482803101c0422a00d040005041c5540701310f801c82c000b40e4420007400010404160512000d4400804c140c1d501c2c500542401038800d40c0b180c404140001303020443e28861960300981c000541260041d002480c2c41484c210700e2541100e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 250188606 1250 250187356 250187359
    0x806040c0f02250314010e010b011d010c060e06090d020601080708060f06030102070503040b0306010921030e0a15080406050f060105032d040b04050c0303091c0c05030322060503061309030e 83
    0x1c558030783e0285840c00b8000741f68040c80c1a40c2415600401176006904403904075441c0c40302a0600000c100c0111075002c81c0d540c082d04c00030341c3e401c0604c8220f5010302c44640700740140720081110745c0c1088002894458164403844d40c507006030310180501000850081e0304421850b40c2c0c0c44842c1c480600284c024490b01900401600c40007600084031103601000d94440c00f402d88403c1c0100e561a06009000036a001d403002019543c034144000083c000e80186066010241010f012192901078040d00e40702c25007c07000105200f04100807c010741400f6042e0700c951078080a0800b81000d60000c1c00d103010240c64148502c02c1042c013820940d907005043d03c0c80510452010a850800341480107850000382ca084d40c003809100b2484460782400000c9403c43c0c8000f40406520385140c07200c05115100d21300007160218071507038000500d583e00b007004e0900d0382040006007011985102214407512007503400719090043c05d000f0000340303540f0000c1e151091032940801040720300862804468401c4ac001d1410f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 250189856 1250 250188606 250188623
    0x703020f0a240230070609080309011a030f07051c050106060c02120706200102070b0103032718050403020c03060a0e0d0507020603150d050a030806040c0f022503 71
    0x1850500c2c05940c10035200c201c90302030313580c82200052030284480c000c8461429a144d60010f07050319080001c02080410300414001070b444521341d0b107103480c42c2c0c810b652684040c0e4540403c0e80c50581301031644800650200c00408034082d43c591829100d41e010710800f0700c0b604040b9154400f803a654001c000960340d004000300b000680300c0d007016040303049045050b80592600b83c82041e070100001030060a88045403a07860b012081d002c25400c107402c0c42d0315080c039255000d012040004216414645c00f840c400e845a005080b0396210422504c519402d141c100c11410b10000c00a00d00000100d00c60000c4460012a070307a41c403820160324201e8540740181d050b120700400c04c2120002e552280316401d8406054403103041041d02e040311940100c50007c1e60003242040402c400707ca11942c103c1100c0c002400130752040d502600c07018100f6040c03450940210358030f801000142d2a00d40b00e007007070030300e0103080119008064500080d41c62420303984514540911401ca0a55080002260f900456202042 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 250191106 1250 250189856 250189889
    0x10210020d0603150e070b0a0203070506042603070f05030403030221011e0503030414030c0a0603020405030c010813030e040b0607200301050402010c1502040f1203080601110703020f0a 81
    0x900780102181e00c0296403000912400b0355444c442402410183e10085004114060a002845040e5400725103d001980301c20400c0400180b000d0016600c1140680c06c0c01540c91003c00a10340c0105a0540101c0c440c181042041481342c1c22140030300200c3e4240c0341c541d0301c036541e82c60264002e00c43c2c2e0007920302400d41905200440003107e50424141c5242c20900340e283c0500c0301d1543e040c08010300615905030001d0005001e40d8000e41281469044024202c401040c00e8a001c285074190b84e800c000000307078001030b060010303040411234619242c8003841e011a5600c0c0030700034041c0d0000f44540c018100851441100c1e890b035501c2c1c100800b00d40300100001c0ea0746000d40740540c02e0000310700384000d000c003503040350401d83d1074103124a901c1035406855501114000355540742e1000301c0d241c800d51059600380000300d09001502d8800007e0141d544c0821200291400c1c050204100200442d04202c1d566160030a030500202d061800c0302e80c180d503501d1150b50007100040210400b40c00501daa4000c0f90354 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 250192356 1250 250191106 250191127
    0x804061b170901030e0c0a0e0c04090c050d06050a0317031003060c110105010e0412080415021602010824040e07053003032520010c02010c05070f0303020901021002 72
    0xb0041c40200b600d0400c84d15100c070781801d480d0401d00c25001d40c000d120490400802d01012201d81d4003150000c145498951180c4850084070a507400039000240d0118611480580922a0002510080f80c200082e103185551380310a6401e120420b516224001c008102c00d40c0d00170490602940d40250b0a0200c030311000c0000301421002e000d84141c542c01d00000091114980c0c502074000c580001e1581d14030f0ba00040c06035035003000034008403105540c4401c401c100280c1c03072000d409208288684130440240d136000051486402919401140501d8202e41107030710a21440320750214015900071801441d00c484c0300c0d0a04450b94400c58104280380c405d02c03200101600d8000351054512001080d5420000d4515071700e0200b01c5103850a020034058000310041161101d00300b00e01035203841204191250340b50714807016100c2c03015095a44a589a0490940a000f5000d9420091400906100c50794842444501400744090b040c194001002c0f070741d9034030a00c442a049580d585007599501003410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 250193606 1250 250192356 250192403
    0x7021509010e09090c220504030503010518090705150403020616060510080a062013060f020d05180a0509010b040503010605100509220905010e0d0c0804061b 69
    0x34540090881000c8802c18030f8015401d600035288280104880314914040c0b00c4065101310240303040d050f0005640d01c0201050140d80d1003140701c1c1e52001e4882d45082c051180020354080813822424046041000280000034824110703101141c40c40c0c1c24007907150b42c2102d1403181c0d41020750003a81c000b5080b100400c802c4140c6841e9031103000c0400c100d82e1151150f04c0300741024012115250081c000b0880420741c641c0001d041c50903200365840c8825040700009a155210080b580290184030f4410000780d5001803540c1107100e214000340c1614184070200a2407031040d142240d0000d0070081c0180c2140d00c0303944102000d880c014142d03010340d5071a001000b180c0d03003151181d50300c41e44c2402004511801c11050040a1410070b07140c1da424281e060040007207821418040c40700342c1d9903d05958110f5a00c1d40a00041d560084000141100d44800d1003400d001c0b03000c9802051160140215000901e044105c41c111403a074a451107580312144060b031030040341820301502d045000161b5040c2d000005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 250194856 1250 250193606 250193617
    0x190c05070503070e0c1e16050d0e0607080c0f0f0a0606090c08040f02150a0c03030e030705120c070b04030b0106030c0905030705060a02010906020307020f101a01050a0302070215 78
    0x1141151185581d400805549440a0281c5004201c4a1011401c800010000f030406014042c0240c881c0030b0b80170300d41c0e02060b0040303040c40715010039a81d4a070b81885410701c894035211100d860036003241e2002384041650381c80341c4c010007002c04030005802101c0302c6d800e01c0400070100105054076040020ba60146944003549442941c2d1a4904400040e46036007510481620074004c0d15000600d681c1c50701e90714484051034009070f07000502000c20307940d01c414010040a0903100f5440b18600030480c2c3c100101158150090b05809031300803c2072001003600001c008401c0c209113104142d440c8000e042103400c3c0006070344500300a403804600482000000c0743e02078140d038100e41d41080849020b900854201c0320300d00c20281c041e0400d80c020300403030400b48000d03c00101d0f54000400c55040355a01c0c1d904a0f44203c1e42100140c00c2100d200125403814041d810181420300c170180004c1580c11070b000c2e401089502842d05010780080d920032224000c1d01a904566002861458520310b421000e1903641d005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 250196106 1250 250194856 250194863
    0x10c0f081008060403050d1404080d0b0603060310020a09080f0a14010515061e0f030a06080d0203090103050709080105100504050709060206060f12100c020105060406030201170705190c 81
    0xc20000704007021880825003201e00250042203540c6641d00d007912154040001148001d407528411314440080d4280d00c1d0095202d85905c90f40d40380040c020000301c0b400c3d80205482a4030800501101da900020744481d02c00352903000507610125010b00741d840401c5a0b0200d4140d000b5154070540c0080c02207000e44199001da445001c5c03180c0d0f901c405500321101161590394003410721180d07041b1070404402030301703010048405503e0014650b59420000740c0010303d03005e5101e0000000c0004480b41d41c0030b401d0060021030010700824440d852301035100d0058109141c1015550300001d010f00b44266a4800149000d100801903800c0c0305c40710410f0703558140101801036042c0300c0441c2a052003940408100c6000da400303401e00f81c907044c04028081c0645c910943e8000c003140c42400d00090f003803140d240d100c1d03040040050100841000617095910041c0028415031500314108050703600b084000220205540503c65a59568102a6494055015040f0071825040480b040c2c4030707001509416203d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 250197356 1250 250196106 250196117
    0x804020915011e030e010f0e0c040204060c110d060c022a0307030308100302060408060109200301030308180319090e040c060807020307080708030103061803020601140f03010c0f 78
    0x114105a00d4201c900740d10300500003501034407003450814980c0014294035689280c08204290030b10310883c00d43e504144076403440307603448404210009003004047c840c91400ea80960905152160180c251a1024809485070840c0c01d092440d60b9502c420083c8900c1e44001c1c200700340031908100958401c041070000e04170030081011903908100002c01c16001500040c000d142071030450344c2c215001c1030081c1c046181000000f001000503603034032015002030a0984000d00d115031404a541e800d450203c81848410808402c071a03401021042c2103030705494150a00e541c1581701c146085d181c401011624540c103000118201b6a801c007a40f0000403210010740d50721041d40d460f8405401c50110a403001000303440c0403d0100203440c021164103600028a0040e60b05040a684445545500803030040342d1a50b00000140b04001c0b05d4824004003028200c40035030030780c0303c2d0f540296650310180142030715100014070745c00441d0f99804e02d035404400c01074003e014440e605000904012031001c015000b180 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 250198606 1250 250197356 250197361
    0xc080c060a060810060e06011808121e09060a0305070509090103050c0a0b0313120203070c14121906050a0b0301020d090506070c17030601050d150f0b2703010b03060708040209 77
    0x104c0030300464041d590f00030006403441e280c0c0001941c00d0983c0900d20000160707803020000310000706229045002082c0340d64256a40941f2400d00c03101807c0713002c20b010340b0900b841012a151a01002c4d10b41040d01820300250a40320f0315019115806030100403135100207444004400c000b404107249042c1c0350706580001d04151995114841404100c0d40030f601d5440d9040000c011a54403528040d1002c05801a20b14001247c0c8070140882000e070040c021403001440c80c82c0e81400d011030841c40191100000c0c0c0321142100700440d0356000042c2d006000340e5291400701c4d04100c150341c440203034028024000c640c0d44440d0401100502140c190995041c0915000100c05e50b026601c1a0316907940601001c52546a0700c00303204803504054082c50400c1400c0c00a4021000d29210f01071980070082c48400c699868804030049000f43c2d03030400c205101c414401c00d00c40200c4840b486070399114501d00301c18903040c081d010038014030050400329450712030a000e2100f444e0b0401d4115008074002c4e6a00e03800c40c5d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 250199856 1250 250198606 250198633
    0x110906011b060908091002010507021204030b071133060105032809020d0b090706300207060908030f010815070305060103090501050903130e0601050a0c080c060a0608 73
    0xc0c0080410407014442000303841c000561541c4038a00c0e2070700c030307480c0242012142c801007141d5210106440c1c003d0b030364803c144407003942c042001c0b190f40d4612004582ca05411a5a580705211000c0e0019040c810b40b951500e00c07190b02800f010740e040c0304000a044511000e2096070742140d2854108100b92102c001c080350a40d40701e90101ca01c10b141070420200781090560380300c2d48402c4049107441a041d500c0340c5170001a03440d0400c00060301c1c013804504d034103400c041350007508000050f0310240078407001d034280140f1444c10a0b143e002c150000784519082407503024a00d0068866820028551890729090034100030207034002e580200f00947c1069180d03078844005650300c50254082142c9040c0840c00510028401c0e04030310b61108061602003140c0b0983d550b40b90075903600380d4003481c09409c04203031304d03038076803003074a50480189025280b15400b0b00700b03000081d015102c0c1e5041401000f11050042c0180700180088500300801c0c0012242c15140141198004000601a8119900611500e007800e03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 250201106 1250 250199856 250199867
    0x25060e0f0a1203050d050a090501391107030302071e0b0f031306090809030c09130803040c1a090a0504021c02160f060b0901050316051905040911090601 67
    0x1019040450090414400b01d80895200500f1030400038204003a08000700c0c40c3c0206401760458030000b144010240c07800c0c42c00e4941ca250542803040104030071030403062124200703007416000380c00003010840e03069104503006921b54042c0c00140c46241800000c05500040c444120750b9842e031100800c03140c1085c101036441d402d2061009022080c002551401c9140340103640000c0b030802402c645024642c0e844003070300c05240b401d0b00c2c5503c000c200c021040c102841107105101044542c440d082c40c044a9258102025507005400810017100003400c01c149106002c01408440d4440301c040d0041c00c100c00307455400060700902810120f10001100c0c2854000e845201c0c0120500c031401d01040440b01e00290442c0c94070000041c80c03442042e003c41d02d5000d20070301880c003415020a041e18200c092001d8040107a125600070b5001506050541c00600e1003102036a0080314011520004404005541c0c10203402c801d42c018034180700442000800c09400314801c1c0c1c26191040c1e10380e60f280055a1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 250202356 1250 250201106 250201129
    0x190e0907091a0c0f0d030b0604081c03090b0406411005040612111215070309140a120318020d0804030605010605030a0609020906070303020c25060e 65
    0x49180c001d01801841c84002d0403030201c40c00b41c038040341000c0303900800501d00083c0c031400300f60981204400d0700050780d00d801400501441514100d2403e4601170707000e03541e00b01c8100c6a002148100e0f5074000c9151003500705020307140e00444400068141410310900a1840341c41052115040900210007901a48001210b03035580e110a89501c60906610715014180200301480c8005102070101c0c207580d0358030a880180949066441e015141e603d000078100303202c4498103114100700610440d400e14002991080b440540301c15648540301c10034268060100100c4c02407100c035000c0e141d1440240c000848003e00d80c021108080c41d20202c18059003156030070205040001ca8035a106800340c20b14580015140c1d2241441034a030907500d854107000c075002a00444001a400010f100005c0e0140c000d0002415610404525094848000070618450100c004040c11b40128280c424180184010614034090562000b020082c003a003c58481c1002e000d0b080114002142c003003d51300341110b00c0030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 250203606 1250 250202356 250202371
    0xa081209070504090c170705030d0201020909060f030304050d0303020708190215040c050d050a140109021002070609140d0c03050d02070806041a0925060807020d0c06020c070902190e09 81
    0x214079410606e90400c0300219804c4801c640c8146140001c40e501c00b084a11246e101a030300040c2c8503c111401c00580e4680903155500c07481c408445461b80e6903000c411141226012101545006820703d0250064050400050811407007c00c20031000072549010407229400c590a1700d8011070b42e05604035032540151005081240f42007001e010a0400c121160303011390107401201e80042e81c039603800013010010044503540fa511a03508004500f010304100c0320b6070206001030412039052400c000c2c4982c41e94403c016002d4482410119541c403a5142d880503c0d4100c20394003c0c5039104d0602c01e41c1e89030542c505500600c12600001054000460b0b240c0c003540c2c0c030940c2284404948040e41c031500e10043c00810546c020400e001140011915410003808003e860450080349450806004444018440b40664101148681d5a168840024003c07164820801a110211100c0d142c2c034260301c47d04807080311171000441e540b103c2500000881c0d00c4010b5591f101240401800b4840903481c15200c80 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 250204856 1250 250203606 250203623
    0xb07051602130b0d0507050102070e162102030a14010b040b09040902061603080708010f0b0d110c01110415030b010c060218090c190504120605090a08120907050409 72
    0x680c0103140c20506410881c0c00c0c0340000c12140070395000104140d141160858081e40000360401655806001443c02401c080d545524140780c03000880e80c0c035020030024842000346003408400029942508020442d603010011500c0b0b01e048004440185407003441c00803d003110313100015180010350102e505a501d001050f6082800324000c0c8009007814440480e0b1010052200103500b000c4c005480c46403901aa43d10403003410039880c050305407081038001368040e00c1000c000b0b00000010a00302e0b162004404000201e24400d4000d00c051405410f105002550802c41c1c6212003850f814080c01c15039102071818034502414075020340444030140111400310310b51140c4d040100c1c403540d02410300401c0400c2c890500042d02c80001d00400021039400ca0034140115861605404010402c6004034150510318038003810721040d58104210507400070010341d292400145140c2c41072144882c4540e0120246031194100c80c2801d0320580304a130f07168682d201d81da4001a05240c28012030481c0b54000444 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 250206106 1250 250204856 250204897
    0x40b01020c01030218030307150e0303041e0212071206060e0f04020111010204121a0609390a050c0d0302030709030803180609060105040b06031e0910090308040b0705 73
    0x41d80650400d05e001c00e407000c402414000e40c1d850600c000d0203031710710030854248c100c243d124481c3e0440d0449102d20b601070b4814420800080c0e091000d9011399105403160041c6803026200080201000e0a114001c81c007507440b00042c5041002241c2d0800c40c410002401401d0310351507035071401c4004a80c1000030000e01c10106000d940100040610b071201e000015142c103440c1c0f80c00540c1e007401000b003151030007080d420000300d400d94200340070b4204c081104ca41d849420030b40c1100003000050490010380354040c0c491044141001c0074010780741e100d040b42542d11140e009801608a400070810351540b07005600900c80607501c42e01c2224429003294949082c11819a1504103450700010064041340c00d40c0e0300e000040d020b080010f503110718816001042c2e150b0500382807009030f030980911280111000d00078040084001585804074800c000c00e0301d0120707038880f142d0070302e01022500d41c5901c803032410040742c0c181a400300400c0d03c0745008042490f0a83c98101048400d4030428510b11440c445a011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 250207356 1250 250206106 250206109
    0x206010f080a0b06190306180317060306040206090301060f0f0510171501090302040504060509101a06030703090c1d01121109040228030606060206040b0106030e1c050d050105040b01020c 82
    0x2c9220740e005940152460860301e0387e81c1c610441d49a00005280700003101d6000007050b510442550304000c40200240003070600c440440d50340c03080580b00a20411021640d42526142580550300400c41210003110407036841d40100003041d040c0c01024010740301b0710000003183d40502c61124403200030700340c07054142c1d48500b40e4400004d035a04030b15041210420000000d80d4035030103118041c40c0140c50000d920300b044214a0f24117040400300380b180070300b000d851291407422032a00707551b01ca00548403c0d07030b00d543d4410300310000d121108000741601a040c901061544643c1c1002c2c04922a06075030303420750303621000144451055141c0042c01203202c003640200300d0034070040d02c0d900544064080074100c0c0020020035a0748401da11040344414101c4401c10510035280225001007074617002400d9035081c40c1c1c0320800d001105001d4201417603100d011180d071186081100c0e4411030030b0311410035014110800010400d9101e0352121444504000001c10030b45443e20600e800801c3c144c0082401840d41c13030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 250208606 1250 250207356 250207369
    0xa11090d030809010f1406040c0f140d0e060103030206150a052110020408030a1701051c050c1305010512060903180111010c020a0302120405101d0a03030206010f080a0b06 75
    0x3000f5582d15501c907041d81c81c103003106015000c103106107504c0303800603840e0520611040742d0300300410b842000614240001070b01d800c01c6850403501072882c0e11a0b0366624154502c0040c181c20452301e0b1481c8070b0400000185a03000c0361090055441c0c01c0000c09540b25001044082c0e0328600640e644540c00d00c4809403801c410101031a80d40c400071040da201e00d042d0707082c07510413070700154405099500001850740007142e10044003a8050020040d2070615418640032801141107a501005225044400300d000e1040030800000310802c020581b001c1a0110f081c6c290140500b0700c07585019410003841103001000c007040b450310965050000b503060545610128100c08a2000000d0601c090b00c840810400700a024007443e840003900101030030002ca1900a1a00200040039030790f0510600043c00a0b135030f5528141641400740c40c00300c10b10908102140814040385464070b601c4256020008101500818440e040710010304403800201c1e600e802d003580b102c1007004010000c510b0035000555524203207 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 250209856 1250 250208606 250208611
    0x1b03040b0406110a0204110904060e0112060905100f0f050903120402061b03130e01060503240406091a010f140702091e010603023a0b0402090a06080a11090d0308 71
    0x100f003100c0030000300d5004181168040e25010b4400b00f000200d40300c29003058090b00d8000c0c0000c02e14441150f1624140050050380048010619602c844806c001d000c03080008800c642d079244020801045461000d400608500110309400c5080030300007140d00e440402640e001c8428210007112036a01c47d42004ad051340180e102082100780c480300342000c81c400300b008d05500321034203e8001003217050a10610124505a0001c2c0410070104200714802c0305144030b001c490600314007118041a00400060050682a00030070b80052520100340c010950010364043c0302031007078884010071004510220761460080c40d203200554005c100c554014100b01d1030544d8401189181c9520312828100c900700c607090203034004030021381c001c11840550318003008170980c0c140480c45074003000900400030f0510581d929058410709990340400c0c074210784a940485085440042a0074541500c58201402d4200c080d101000c555141c2003211544500c048200d0300c007103500500400c441e100f02c0d0350480c2d066a00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 250211106 1250 250209856 250209887
    0xc030601032d0f15030302031c0f050702010b010806010306050105040302120c090f1b03010303201c0f17091e010f0c031b0207030305190c0210051b03040b0406 70
    0xb8008528651804000d0403075110070440000b081c0d0004044400302034030034030080380310700004124041000a8001007180c032200e4081c4854109408c002e00304000a00f40402038031483d600b00401c001c1c50720390642c491548288243ca07401400d4403500e0046084031010b00459020400c1080207001610b46100503030000b141311012a01d025004502283c038484080d90100866800c0303006101104003060f030010110061401c6642c25585135490003003d151a40f82803240306142030f040990300c4581441141c0b1141d40c02c0d0a1441e20b030301d41590041242d00c444080d01c00044958160203c200390000319030f80640c44100c005c0502410070704500c807030704c14002e41a142e20f661701c1307244081c0d1511038010000d0070581610000340401c164a00ea41050a890300e10b64110340140506000083d00401920400c0048182500d12100c1d2458290352007009103901039030000c11504021040307a400b2005020701045662110100d512840b07029550f4065801003040801003440240038040c4200345031040c0c1400e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 250212356 1250 250211106 250211141
    0x30f0e0601121b1202030607170c0304050a050a15060b1801050a05040f12020a05030303130308071103070c050301180f0f0623090c01110a0b07050c1c0f03050c03060103 74
    0x503d03401da04100964089003290101016940c1545820b00c05203a100e49582000700769005c840c9000b4111003801001940094004030101e01840343c20402088007135400011a840c2e41c6941c10400f0388248000a80b94249081c507402080c0340100005460300005054040c9000195220064a1540186119604001c070500c40013503405800750000004102e803c4103c4a03117102801840400000e61300020700039403082040c8001c40c07000c903a501141c03640501d02101035842e0300300201c0f446542525041c0040c400400d02e442030000348584d58084444c110020001c070700c0c51966030502911024030140004c52120034100c00700d13907a41107040c06107205040000f915040ba1190b8500b4105025081800009040400c81500b1041241704200300013401d20181c060000d007a80c9030348846d41071008045d00791901c00320b81e003180184240c8143c1412101510402c2e800d0003000e0f01d1a4019036100800180c2d5001d61845641c020300c280ca001c1c0c0ca09450551940e0389000065010300307001090300540d0305 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 250213606 1250 250212356 250212383
    0x121d280213051506040b0703030b0405150d03050d0c050d0515030a08030601050f0c01050708060f030c041802040203010e0f0c030705160c08250503070b09090a0b090412030f0e060112 80
    0x30b89080050029080314a5500d071200e600703050040850351074002b1680210725200901c100445041c11015603c801101d0303685085034240b50440e01406042c04816071107007000d266581080d00300c0c002d070408540c1510200700f1a0303114107900b1604c00e4105080ca80580007500450003185181c401154043c0c07060401c0ca160114200e0341c00c0c107562081301c0903101a5511400c2c4000d15078000703d40c540190040b42c001d0404602c0a00217912491a400c2d040d00c1981d0b101515171000708880d52103500d458004004540b65070b91911700c9138244c00102c0c0c40041111002c40042c00e1401030106036400750046903900b0f420715821185c0e00343d43e1a03100d1801d036440a403a190000359040200109241030305000510403a24000c030044004451580e0061807203034000c14030a00c9030700e0405050315142242151f80a042e500c403669131500074008070b40c03c2c03904070b45410104810700c0b040030b6030316041000d203940c1000b00700e2100d0b401c03408035011140081d85580043c0010400f94110351030012043e03008000c0ca01c1d159 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 250214856 1250 250213606 250213609
    0xf070e0a03030809060a0507050d15050402070b06031908030f06062a0706030b09071b0807060501050f0402190807021e010c0201060602150106121d2802130515 70
    0x40d089035008074000b50000c03003046a604000e100c4c041e00a5219141849207061007000076005004400b9082c1600e5a14400da460000601c0316a40050034090710440daa0403450034815030707034202101c10602a22480c440142d80c00c41c078040b40d03001c036a000300c555401d50300e80029900c02ca03c0007400d0f03240d21a805211001c1c12010701508068806220710784043d02d1407001d201c0d1418082c83d607000806043c98908a0180307504c600380c2c001d6115246140000c0310310790f00005244000115140600940004a200820004998000c038180e030f004503010049541c442e01008143d01c980c44141407403100a5580728019402803802e25001000c900540d103111a00320b0300c2400348800e0032110001691078a83c15101a41c085c03041c0c1c4040c00580c40980420000c4100d0034803c41411312034074081000700c1082e64008112a4401e0701c0242c810f14401c0da810052011180d074500b40d4050f040300f0800c0000c4560080341c200c0c0c0f20038100b16806000d43c0181c0b044c1025800041000501d9042c014a02c030781032850320f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 250216106 1250 250214856 250214869
    0x1120809190504021306020106060f140901091206050103051005040f0b0c0f18120109050d0509030c0a080c0109140307091e140103030306090203010f180902190305010b0a030b0f070e 80
    0xc2c450b40140b04145d0703500d017120003070a44402c1e503c40014480001c4041d20440e03848100001003600b4000d65035a580700e0340c40101c42101c03666208003041c00d19841000d0800550785c0005049034000c004550342e014040d10b019049413000d841c024196001d410016002400d4440126400305040c110b45003004111001000d0541c44821340c40d040d10940d401c54001480d00303401c500c81820303c0d48020003001e40580e59030f039a2000366921180a0102c0401c07141281d5604002c00100c0400151071100025580d03411f59036540004c18803c1d002c01c48400000c20080b822130038151034800014000e100c82c510346105200140500503141000d07113049407507065510b0807400f60285400c0050448401d541c5141070082c1200c20700e400c034400c0540104010400109601c0c503205c240d80c02202e401c10010043d04014006000c0b0010094000c083c050343c00d41c101c45600780c242c1c1100d0140000340500e440460420401100a000c005e0005441d44086541c0117011640280e02600a00b0502a40411600020349 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 250217356 1250 250216106 250216117
    0x110a021314011703120c0c101d39030118030f0509091503010f0509061e093d020304030f110718020d1a0103050112080919050402 57
    0x50507194008201040440e95645004104a00c030f0f0384040201008025100d20629112601c00801500418024075042c000c03a00d4813455501200d5060b40f213011000041d06000541401c030040c0c00c0095000694040307050400c0b001d03280e1000c0d8400403407010171420070755944034061249001002984040e2024400d00742d0b2a154036040d160312660a00c7c0c010100c80600c3c0c20442089002e000403a03040d20340c8954590010605950f0761000c0c0c1d032000200b4010107142c001407040a04000900c0b05440010034024018001d20f0000d4450340311484201c0150602551440160b03032080400e4902c0d06440468020518010701e02051800c4d00e8048408100d803415031500300080d800000c0c4410982c00a03600c0140c00b40d0f0b802d002400141e6841c2142c0c460000c3d20929101c1811544100c010900c241d04640b0042d01480042110208030100c007281503000401007400303e0b141600200341120041c5032280c00c9503001d03c000389003400c000c060001081021241031410072540c540441c2a0751180007400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 250218606 1250 250217356 250217389
    0x615080106110f07090510050d0c061b05010c09140103020c0601050f040b060307050301050f120c011206170303010302030f0715030207080915070203011a0612100509010303050c010e071203110a02 86
    0x1103c3c1400303071f0070070040286584030b64440c0214108030000215160f859078101c504a00704000c605c201036105010a28081c1ca000300a5460311b810700c2e03203e9800505c1841031b500303011803040c0070003000ca005400704d1062849414a550001004020320720b010201312074452400703080800c1003074514002c1021500203560b1031011035000310050000b03007014208003245000841d051400d02c20030649154550106d025000d040010030511005603400d183c12402c014040e2940100349565059141a01c83d00280800c0703100e40928400340038403071000140c0b90191070543d03200130301501d03040300150003d501155085940300c01c103101505030b1b0340d18012000c0311403840d200607503a0350072248101030031600241d001100c0407494844a202e50744810003039650826404c400c2074040e840b88c2c1000c03c10401550b1110b40d0001d1400008010103034084090700780998840700900180c008207240076211912402003400b003010840c15000401c0c0b05040552580940c6416940c0800704d54002c108e00192144a49 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 250219856 1250 250218606 250218611
    0x1011040905040b0a0e0102040b030403030b010c02060a030207050c0f0102060106110f0303010e070318150902060717090307080f1005040303020c1e19110d08120a0f0615080106110f0709 81
    0x1081300f605010300aa8407510400131840d060801300c5c408070768000034101504040ea110200c1e86180d0064441c41945600140740072344074480c1c540010081d40c80401e040780c141c011400741420301e0070410190700301e02c40c05070003a01240c3e0130324004441d00580660041c800e4070480c0054100c4040c21310040d4040e0008400d010380034901402e0113000c1c0c81c614075154001486801e820400309241100c03001c503003004507001282102035400002c2c094010302074040c0c0a440a040f0442e04454410024a00c528080d0203030740400f50744601258440024443c421181e801c4410080100c0d05036034403ca41c01842410300508081070030041c0c1e4a466403a05081e444081d149001414100040200d800f424682c1d1020035982c000c141d890312105454948000d000300c1040068208002c6200c060301c0000c0e1116589503450725190580401a00c00000c1c440c04240c508440461190034020b140001140c02d0f072500645640303082c0d02160248040c0b090121103015050030138840b80d0060003580004c246100d4003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 250221106 1250 250219856 250219861
    0xe0a030602090607142103040b070f0201150914010b03010e01090902010512040308040507080304060e06070c050d0309180504080901080417040e0115090302032e1119020f1011040905040b 82
    0x714101c4090b1030100d500d14003011f0003040006001e1401144e030100035807030404500c0e80e8202042e40508501d102d800110f0f6031881010a45190540c44100075040c0038031400c0c3d840c0d1780e540f5108018403082c000e80aa480c2d6180050001d607655801a00c0c05501c10b1400c3c40c50000c2e03007005410000e00030b41b4101c0002e0203900038041030000c1000030070080c0124501443c6003e1501c20060100140400042c0c0907660100e4040203000d88500e42e007001f410003400d8503000409500d0010000c1615010700720520550501124000a03648101c91045510295051501250710019101488014000c83e40d10349807280c034806414603000684014044290380c10038650411070355843c0d2090428961042101082c401c00245c0d038001740900c00481d182d80041c106528070041400303078080c0da6102c00e441c94103040705184a00010001007070340d01900c1c0300705203800b480f12800f00e1b00c030ba001483d846940d5001c0188400e141b07149a00c103400344001c50a8151034955100707406029124100e0301626560315074400c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 250222356 1250 250221106 250221133
    0x607140a021f1706040905070b031f060503010509041b060203070b0604050906070815090c120603070e180a0b0a02040f060801030c0e09100f020d0c0e0a03060209060714 74
    0x4490005122495801e1206541981c003e20843e01c04028850440710b210210300c0e5500d960340b0003904950000f013a184260780b0784500304003a1b801a11411404020700394a04241007100010200351003c940e1060701e5a4030700420032020040191060b6803500420742d458184040345200c0e4401402c4580141d9190002802d00ba0303000107006003c07501407400d000c1044014140810b126074071015505020601c2c0e02c425110091308407034040c845800107074180038440c0f051700b0440548001d8080c100140fa6030b80d505800c1c551200c4251096108044076030300820141c110980000c41c10030020400c49c0c5074403000f030300c0d19006500d040d24995030782c070703070014080c0200420b400d58580a07040721304203840341d5455503440b0030111040340f08001601100c9804034103121070601c400303100d14a0484040c001e0284000d1060002d61014400894a41c40c1c804265007080c02507004041c1c02d1070041001c0d8040e40341d62100e001940c883d9080a920210070001ca40000e90f81054420703c900101c030060096814040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 250223606 1250 250222356 250222369
    0xa050109060905060a05150c0f1c03020c0c060a030e160503210a0f03060503032107030c2304030b0a05060108011223070b040b0c1903020a08090607140a02 68
    0xc11100c02c042c10202000303e103484d550030440072501c054440c0f0b40c0780c200682030184a406050341e41940e50107500c181441e480b00000b00c001a00d10100c0c1100115244807009400300c5c81200c40200a9070030800d080700d91450218064036030711a072070801069894942c6055801c02c2000840c164002c2c101810a0010341003c1080030b40c88000354068095403000001101030700d001d001041401c0041c0e005001c8401e1b0300c40d403c80001041d001e022130781c032510607a1442100d079480c0030329112042c0c1044000b8405c50321900950780c2404080e1500644048440e05004d0311a209401d0151004000c001c000005201c040550744607650044000510f8140000010700641040e800782260003008640d00d40440c40c10f80c076007140d5950034104101581c4041555a04003260740d80705440850300407070b0020b054600c1e44001c202a010010a46107c162081c0d03d028680303d200b00301034016400700030b407900015100c1004081c20600180350b1070070603d10380e0f1000418820f21190a2450708904088400c40c00c114 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 250224856 1250 250223606 250223609
    0xf11190e0603010905060a0b03090d0f030b1011070e07020a06060f1a0310030516081c051c0603050a14060a0b100e0105090307030b16030207050d11150a05010906 71
    0x92030520201012400001c8042c08103000e0310b124256a03170007268080d13950b4007041c4003d240c1e1540c1951a0300e40f201d5696144c00c034510540c00820300b003010486205100748034070784181c10014034550091000810413908a403403481a204643b02e40b95022507400c1c01001810310aa105500400b110f01151800800340c0f003685e071082104501243d424000b060490045a100860003418030b80c5030350b00e281e020f808011076580050700d140240d0382d524113140081c00c20716041c0c8040c201214030103600750740310201c00440c0552050010b00107001581000368024400000c03401060300c042116602c0e0f84a050802c0e4000c041211501c960014150307030a00c05010303580c0e201400390703010082550088081514002080a248100610402148050303070042c000e4a0400d24054211030f10592280741c9480d41040950300c031081003185e10980300e4914401e000f21221581d201003d4206e4480c0303400281d0f003080c81c1c410001031600488203960344010700304040c40d2041582200c0403e032549091801021076406 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 250226106 1250 250224856 250224907
    0x20111060610113a050405090601050c0c0d060509120403080306060a0c080a020a0311010905100506012c120f03041406070803101509140609040617010b0906040c1d01030f11 76
    0x740010847e0390303514884282d202c5e400b030078501d540f1000246004d05107100d8130145a40074070914403076418000b80c0c0d0f100510907615141256015480002e0821580c000c1e0320005010800401c0050700c6410464042d007403d6080d401c0480c0c03842450b540e03035903042c1c000b1007450300140e00c007003294014154060303800b840409511008010105207a220503860380442d0010b5551141c9610106030541d1040c00c814440002542c1c244200001115000000107140c2008034801c203010400c40044810203d800460400d910000303528091500c03900c4224440c1021010f580400c043c000200481c00304801103119a05004200c0055820031054028200c0c511800800b003088100d0140486140d6948404829504461413511090301800080140101d80c1014003103441a0040e0703d502c0005402a8102c0740c81140c900c0748aa8903807060008442c0b0b08010a000a030300c0c10604136503100e07500e003d804421018500824002c08241080d001d48110300441a034003540010383d00d6022440c1da0880c80418030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 250227356 1250 250226106 250226117
    0x7080a0504050d0f0e0303040f0305121204060c230307020708210c07210302010b011403130f02120a0203060a11040b0310050406060c020111060610113a 67
    0xc294558959405024550030300f0320080003904c07806140115603100c0740741002021a0b0760780e078488403443c15040b518030040740c1512a40400d24031710803209082c6c92031460300801c4003610b9500d541300c24000d0305a06c8507460500100140102c0c0001c90b02052820b50286090201e6983c1007881000349042440d89c0501000d4000980c0f02003481690200c1c00480810101915240e4801d05042401c003142680800106032000d80000381010000b51602d040328066002002031184050056400310240c01d80111750f00c10800000c0c82e00f1100031b078503c2c0e00034040d04084004401075030202c0c00f0088041c0c00245d081e407164442c0802c6160402c956a4410605141400088100b0390140194011b500800f0381616000c4005819244a402d4040003820010810300502d5941da0000d03100601281c004e0b80016800000d07400002c6001aa4500480b40642a210000c04540b0100c40780c038411147c464040c042c404002d00842d8040e0100b8902c4200805090a090b06050045c1d1340d15627081018424800c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 250228606 1250 250227356 250227361
    0x1170705090601030b030c030a1a0703020a0207060c05010f0e031b121603021f15230411090301060905060102011506090614271306080309040e010e060f07080a05 71
    0xc54401074241c0105080c01c000c074050341c0c42c400190078000710701e03d0540c1612a8090003414024400040302c03250028000001e001e03101c2000840c182d100c1c00206c00050b0344618010090340780b14021007000c55004d1000094800131000c04c40342500e40700302e900f0788144d00100325211928075100542d030941c00c1d440001d068031000f00c1c00c82100c5025901c501c0162802c040c1c400c10906009200100004075440c00300c3d800307166100321410050031004c18001d43d00c51407038008a1b5215030001060100070700d1115268100150130304000140000daa000c039130703052081c0100d454903102405483c0c040c0042d01004506c9103002c000080c21900900c0c1c0d48441c07141042e40810038103400c007402900340d96203480d001484503035003003100c14144a00940a003041501c0008500000200f0b072540f2000e09044910324160f480c40c0000b41e050364040c0c0200d407030a8001b0071a001c910f14042d44110202c551070000802c409943c2c4952900b4900c2c101ea5000c1d40340340c04400c014a10f54084011503200c50300c0c1c0c1e82040b8a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 250229856 1250 250228606 250228609
    0x31106130c05061602040b0a0b0310030b07090302030a0b0c160506190501031e03020c1806190b09040e0703050105010e071116030212071a0a09080705150f0d020301090501170705 78
    0x41c80288400b81c0126540c7d081d0103940d4131104544000b82200004065890800142550480c051480b0544024000001081045204144410440c0c1d0010010902914191140c1002510290100420f08010400c0b0049560041054040c43e4004d81c043c2403245007042c950100b04910840d01000d1303501c1d140050001680b60b1540d1014184900301c0060902d03900d1409910f020101e480ea40da009100c810802000c14481c5016403103504295032040a100035400b007100c00c20098019070400000502101d001800c1c00c0d0f1200c001440c0c0d4008a900c900d070780351500c07404c548081c0c00c40f610303000301c81080001194001d490f510740300c18520001e0844c00200d4200801c0c000440c0402440340b06249004500038004004650140c02d4610090100c2d03282c640b1401e4407680046040e602180010b40000766608010070680100c8902038101d62013159038503802512036005800e1050b94000a1000344041307042032010318042c2400240014855046c9880080d840d01c01d02c1d031800b40395010b5002403000c3d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 250231106 1250 250229856 250229887
    0xc060a0b010507170d09060605040f140115051201060215070203070b01060c151a0f0105031611030c070f0609080105132904110108160804020d031106130c0506 70
    0x103da00403c0e00081c2582c0040715a035a403080c4010200c1e95800d101c0744005201c1c00343c1c04001144c0e41142e040241c0516441810180c421390480a03005511f10001003008007001c40100920086914100d031400502c1d00c01c13218411001e0300048016031001c00700d0780511000541803908040f05000450401e2226a600e1111102c14015542001026a00b8400700544401094100300f8801760a202d50302605010121103945690300911401329205038000c0395008000b268040c0a044061801c603c18102040d200d8408100c1c10038854842040090282c0d1f8040c40380170040c08101c020140c0452411130b000b48a0101600f03d0081e50345040c05101c00f80c04810340744060b481e44a071544403c8907075a40c0340201038448823010027600800c081080704118041c01d005503013040c02d8032201e20503100d2040030710301501c54001c800c0c0452032901c003080c0545400c1d0945800180b203132402d026001e4000d242141800030a54070000c84070b9a01071014200b0501030480c002502c010745801d8140881d1524200c034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 250232356 1250 250231106 250231117
    0xb04120312020705030a08070e01030e03070602070203030c0d080907090e06130212070b04091b05040608131a1008010506010e040b0a08010c0c0c06020102030f06090a0b090106050c060a0b0105 84
    0x14000070310441d9100c2100c036019103560a40210559494600502d0701074001c2134102d0300e41000401030f0300581515800707072080060402e405002503080c04510b81d203540003903000900591f4544002e01a0103505c140c100009030b80044140c0c0d402259040407507105140c038861360415a481820400c1980c9280b07000181241d115040c4200300002c405c440c00403030350010300452182500d015409012800152020041c0200c1d1402c1004111031407110551661503003ca414800c000f9000f00710402010f032044283c2a000644c98503440c0b0b0780c1800d90b0300d2541e03102c100154882500c0b040313403c11904030000c1d800c05008004902c0244954941240001c141c884c1d88e1170543d22640da20403001d125134403890000005410b400c1c001b00700303030416580083d200c1000b003d070840344001e05610205a02d841070003564050781850701c0449490325003c0070082c0c4031030014807070f0074025520810030240c2d03a504084503000348010f850380d0b640c55601020b034070b0606070020b1600341e14074201241d05009980c403004580 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 250233606 1250 250232356 250232363
    0x20105030406180c0f0e0a0c090b0f040906170c0d2103021201060e1e0904020108060f21010b12070504093f02010c080f270a06060b0412 60
    0x141c81031441e5006042c502081401411004c0c0d2402c02150008555042c1070030740349072031115031a0b6079501c244007050b5000700c014200028400c450805c0709042090241000c0203014265900b040d4039880c1006c1142c195038000d00c20004012114048500140302012400d40306540c030b43c80400650300c0300641c00141141c4c0b25860000c98807481e110341c1c8260f040c0e4064440f040106840c9513903401c0300510449036180e03804e00c40e400111780091042c01c01c849160261201400c18091135903284c00544000600805a83d000030031204410081ea90300c400c00100e49040c07000d0f4102005035003c030709086605540b40c0e0340c0078190080c0d40d241c601c0000111142211811a008030318514070303240c42100c10f1140b01441b1142044c680081c540c4650b5400715564003403076007140c0c101c401d11444049081e600c04100c9440420005000b0503542481940c210368401102c0791f0341030000f01c0c0040d80c02114560f4041002540c0c02c030303913000000c01926000c0c0d400105543e588c400d0806041c200c10b41e5040e00c5214008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 250234856 1250 250233606 250233611
    0x60c0c010209030715080c030103110105030a061d010608060307030b0a090204090c08070614090f0409060e1005041101051c0e0a21080601020102040f030609051213170109020105030406 81
    0x5004050094044400440c4083c0c240d8481e44e5070b520301c801200c0740c8642010b0105202c50006501444484143c074102d0b5000844c1480301d42044005554651009c0c28001c8501c0d2521004a800301441c00f01000240f944200100c0640c5003581c0200100006000640729800443d02000403840307035813440b600868968000101a241c500c000b174010880305100030070300da048450005204070040b4804040750000d88501001920201c4032402c2481541000782d072100c0110002c0b0468101a800714440c94031074000065910000001c0d18039102c00003d00a0145444404000c10414400d4480c40f030700500b0b0034018140381d00000c8a2000d100c03102c005041c00c2d0b44d1107001d65035010081129190360380d04141700340f117a00b8403d00e200a503500da803030f6100d01240222003c0742080d44144204c2c0d00321081100302025050660b51900050500385905882c207102d000811b65015101702c00400c450764410303450040003841c000f1040c8a0381103541d5000003e9140c61801000350340c0100031a503000d640000d00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 250236106 1250 250234856 250234867
    0xb04030e090c3a090b090c06091503090a0b2d010f0e090a0f080d1b081306020f0a0201020a020601060f0903020919050a02090325090b1210020703030c050c060c 70
    0x21550071041d0f50078403202e2a41415000401d008600c0111406040d4007815079003e035544400340000340c4140340c3e0303181d0040c2c85840c2c650f000302d41d080003558200300560281c03200c411031600d510010503420345659001002d110807506909403d2101803000f01c480f4400901170358500391442c0d26819861186d025107006010000311450418803403010119030203e90001c1a0b0703114101100143c0040d980f500e0440e14040c2240041c0141040148504201c0d41c3c03601a61f81c0c400544000592208000311102034080c0504150b242c1804041d0401b85950f5000507210050128000c1c503208042e445003052010000811401e1640103400724240c075010758040301d280e150081450075540c5041d588281d0f80b0303c4c0c107040c0840d14100e600200303203030b039000c60440c0c0384000c0800d055003024540052150406034400402c000d80c00d129008a480d00c540240000c0900151070a05406e00c903161140391401980020000c0030540c01d4403550702d0300603031860881c1c00c020911180e0f66440401612080c0704482c0440d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 250237356 1250 250236106 250236187
    0x5040e03030121050615040506060712030b0415140907182c0708010e060f1806030a050307050d090902180922050114061005030a090f0b04030e090c 65
    0xd10f40d4040e540101200d415142c4920b500d4401854a602c1902c42c60078035001c1342c004d10b4031200740c411540d0410012142074000100640052450100c1241c1141c1c580c110200e03036400140c5444000c2044511940c105213820701000075104008008200b440100d1001c03007004180261b00805030f5481581100c42c1c9030307028080000031816401002604001e03074003080540c0b41d120403064101c4407010035040d0b9a1b1210010004203183d072030503094100710010804a00d422040d03a190b90018805002c0d502a00c000da15000d055a224860980362903010a88140700d569001003500018800300500710b0420345100006a42c051038050079078429a201000300308a4a40100d0340d03848004491100c110341b6515282103030180c94000f0b8070300941d455003c0010a1420a260017481401c0b0943d1001c2c50740e503030901c412000f011705540542c2c40f6421945140c00007903081040c24041d82c000d40380c800c085a44401008035032074004254021024082c0801043c81d802c64028001a076900808032121030071081 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 250238606 1250 250237356 250237409
    0xf12050d110a090e0c0904050411100203190903120c03030e01180b090a0209130606051309140f030d0b061c02090901090b030c0f0616030e0a05040e030301 68
    0x40e030103081a26200c01085140c4854004020801698072494141e541d6584801c030703520000c9801e0400c4000c10483c028040c0390a50000d40c0c014410081440c100c240c40380070a100d141250441000350b031000400c65042e22080102c41c5e1804124a00004080e00b90b82e00d41c02031400c8501181c0910002144182c2054081d820881011007500c1c001c1200448010013120310350014135041d118820f611002ca01c01010108201c00c14175000b426011003a1110a42410103038a42007041e22078942d00e06012819986110418074840d0001002144801c840d041031702c044c0c442107040c40e40c1c96002e5205a0101c88011040e122580a58003000a42803c5440032407100e210b0014200781d141307420951038000d241d00d51b029124406065a12220700d0ba00c680c4114201d480110620754981d0214117604000d280c4140070008003200946041c0c2000000d410301ca00d5202031050440100e0480500303040c0c0f40c00e0511580e001000111810702c80d178410500d0491312072006011b0400c1c0034021985a014950080 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 250239856 1250 250238606 250238617
    0x1020a02031b040f06081908071a01090614091501110a0c0303171905060604120b06150f03010302121e0c0a090621061803030509060c070f1205 63
    0x5401d841d49540001140b071039000d4a1030318148624546260800d500b01d01340708610a0f521550001c013564607c400002030140c0e41d200382256a01806c00000700000d10240c820030400410110030101541085640001d6440c00c1c0c000d103620f4405520350030f045507100104103400119403c0c0441d55110141700403540340d0040c0f40c1068013441401c20b42c0003005118104601103e01035598410004a0300030021843d58098070341003d5400d08080e0000c254010b0b900c59900060300901d11841c099030ba4480201da03010f44103043e035100300003030204016401c1c061070907224a44007044151414a8000c54841c490106001c041c1c0560701d0082c1400201108010b100c0c944a004c0d9081c4214105207001c90750f407940b0070100d8a0207542d0320080000c1072103041c020705003610408405140307140c100040311114111041015600301e515003084400c1e42c14400d02015201d400307660041005d14118080c0d9107400c1e400340100c10b4a0104114a1010811211490b40e4a6500c41407607403404070101400c43e20750058 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 250241106 1250 250239856 250239859
    0x318030305151c0521030a02250f03021203060105071103030706140907081603060c021e01020a08100806070c080c010c0801050909152e0b130801150e0601020a02 71
    0x164a82d0061600c20b03443d908040910481c02c071001110400c0b80c00e0b501007480e000d02d041217641440421100300840d0040e03c0e4420380d10451419841c158942c4e00e0814224040580700410141000000d040d410710686038050700c0500d0040c51804c103540000d00b14843e0440c0944804185a0056455901030084810b555046003040c09800000c20038881d60740802c3e1000d50f040d204000300000d50041c0440c1402c04400b0007041981518515100c01d401780c44032841800460061070b0560b030b08956203000e480610440400011b8590803409005000510050245405e03240b008000f0001d90700001004c582c00034180c40c02c0400341000d494000258003d0341c0480b0220350900752344040e0780b07078800402e83c100c8000720745920b40c0743c1340c400c280c80c0c0b20201102003084183e012400a484400c2d120f520861140b42c00c018401c400017000000721025440d6040b021520314001290044036210500c00c00240403042d00811070301c800b001b0036a40e04109441981958803a01c03000a500e40e00921030311601980 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 250242356 1250 250241106 250241119
    0xe0406080a06021306030507360e15090c0a03180f08031006051602190513020a20061b0403080a031b0309050712020a1502031801031803030515 63
    0x2451801c0c00194120344c40240c90080032070030004d0070354800c1c05150301030b200944500d4444000c01c507662401032184d07034401ca11562442862454247c014804d580106003120001075241452140c0350012154071150f240f01b1100d803418081c044501c08102c40c200e210314140050100001e039402200200d500740e000e46003504004000d030034000304d00000d52090382180d034094041500c9540540381402051219450603152411940050804140c060058448170b809400302c21b42d1200040c0c1d990341e0384655480340c00d4010410345821508644151b180c240c03e9000316298144d1021403650780d410080c03606160300c40f00c002d41d41c3c0148458088902564101480c0d036560641040041c0c0600000381c00600e5500c0c50b1541e52841a1080c40340d10340f5142e010010b04401c0d480d203a594101e01c1102502640d2010700340c84000340e4000d00000e028001d003d590040d40d201e017400f8001c02d00c051b10b501c1e140bd041c50b0901c0c01080c003004100058450300355040c1400181034541503080031852030402034903a003021 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 250243606 1250 250242356 250242373
    0x4121403040902070203121612021009030903110f180c13030b04050d110705040b04021303050607080901090309051207080714130207030509010c111509130515010e040608 75
    0x112600103081c130718003e400300e03038801c00c90040802640c0b0908403405040344407041500700080590b0318030b0303058a01e188103d0304580e50482c1000c00f140d154a00031800304600850400c10881010306049592800b12a1010032000540c00b1038600b000c906202454452448002428a60600306132043c000c000001412410b0700e034a440310b01c1080965098800340b04280d08201e4003803107126800e43c106032000160420518010501015000c0100c140742d00940074001c54980701410390310b802c02540103a00402040c2005840580302c4400a003420000d80d05212100000c82d0f00605210112030041d0341d050035904000c0c480c070303081c80e12503000416240030b81400015083c00a100c4028400e0040710003840c00080780c4d43ca2000c92040308001000320f181408520590741c0109035001d4034134010b60700d008000704030100240c15410004603207609424082046000d81c00d04014001506125460402850a2401200e442085814291410401d03c80c628141e9519142c00c110000c1c0080000c032011070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 250244856 1250 250243606 250243619
    0x60b030f1519050d0c0905040602040312170103030807020c030d030c1b0c09020702240703030b0f01140d0f060b0d15030c0608040f051e0705040902060412140304 71
    0x25800d44034003200e9080407500e502145401d8a01d00c002c2c0c00300350b10021249207820f050007a43d00003440240c0350b200e40d0400c0090100d501d8060709211703500c203e0005940f82d0551a00070000300f0940009001c010040c1c600e5040300902c074148a05480e01410030002565071130004074a0702200300c013041d4041c01212040304810350107400143d5241d00513224540b01000d08015500800400040503041a44072202080311913695801003088070300160100c8000d40c1e500305000550401100c86400502c0d00050300424150305201e030048101084420941403043c1d030000814541f5081845842040c000900b14101d461660010070081c00703048090101d070303a0b02d100d02e0f10503803c80c03010900740d40d0601408000c0c1d080b141c1c060400b81ca901182041440b41000e03000c4074074200013403044405040010395200411001c0001b00d01120120107032040090b0901e203204d061400035400b09001c3c90034090700c480103903505c40686003524683c1035544403003229402c00b546030900c1a02c80010f107010004010492 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 250246106 1250 250244856 250244881
    0x9040f0204020c0d1d0102120a0c02061c0b0603060d112b1203090b0f0a0b06030408071109010803180406091418070605040512012d0e010627060b03 65
    0x24089640c0358031020b92114020301060303a07217111480380140c014501c103c04801510f0702904007400ca51038800e007031044035400700d1a00d41c0010001e800c00c1a1038403040e018403d40e4004c0c1110b60009070b444c02d055040c100c0220701032140d00c41c0014030701c0b4216071350b01c0d0582d210b0340301c1c40c000c8603980c5204484031401d20701410010741420340d050341c1001d003441c14006003a000c4e0180480c1103601c1003a85115646103101030301c0140000d40b40e0700c1390903207070b5000343c2c41941d0700d0018500640c02030124a6035040d0a02c1d085102403400300c1014040c02043c0010842c1d1540030051702d49289480c40d80d098050402000103000300f00300d1f00400e40c0e181c548008560344008003444a4450025492610441c030403408000f90b690b2030304c0c45040300141081009010790300708401d0502080c10004004660243c80c0340d54101008106014043c1f0b81c5486401c1c42d031030b0f00c0507000d82d0403207060345402049464142004003880d5204d0300403028540404a244c81180702441c0d1103034005040c0036044540300e06144500e03488 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 250247356 1250 250246106 250246123
    0xa03060b0f150705060f04020901050114090a031a091609020f04090501092007020a0b070807060c030203090d030216140f0303010b030f06011803060e100501032a1409040f0204020c 79
    0x415204903c00280030f00c3c1071b105e941e401642c00a00303400780c0368071f000b00441c0e08a001c00001806407805005140c415203403450400003862003650040c038a80403200c903500f200c0000900544940d84811900c12605201c22800020303150010809a40c0c1ca103140c10340c082a128544c010804680360000000c2c4221060340081d82d0412910160051a20440d0000802e80603102000c4d40c01580800e01304030360902c0070001c0181c248900c5415040c0f4000e5100e80742124401c0e85240c0100740c00004010004200784249240541c090030218180f5203081d17442c1084280741c0200070076071050a114200c030080701304110100d0291032421240e4a6840d103070320305d10b40d030020b5444804804894000c0340c070381d6000b180010004109000d03860042440c50301c6102c090801e01003e942c1c4c500850030440103035003140c020342d4044c500501c0706034203141c01a10340202005003c4003403c1c0424080c5024445006001000d01c14000c00315602541d42e1200e0400c0742090300c81205c02035001d07100240304e01040038081041070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 250248606 1250 250247356 250247363
    0x1807180c030b090f060d020d020306040308060a0605131e1505040509010b2d0c07081f0203090618070b0412051203010b121806040b0f090703020a03060b0f1507 70
    0x1114120b10030a000b4404019a52460784400a43c00120603041032000c290040d40020501581c1d0312064010904241c2c1c20b403415000903181a0070000c0b00c2c10800428030040406203000c41c40c003031040c00f9082142103140510720300440e08070061003c402c400c0f12070a01425400d64082d5030b01c44c07800c902034015807151140a000301c103020000a410b5a000c410317507490001604100348880f200c0e5074644114415404901016081480424280c1c4008c100c800060001840100882e801049004d18580e000345030105c4818010020040c0c80c40d404100700d604006440c45120141c01181c1700e050404889400c2200310f240080340004001303003a2507504081a000b031099510b4503a106521000358802405608089401005088410420801d0f419031220000c5030b0b4003c2c8041c3d00d41602d05141003507900390382c1850088103100c92000e40c2640e20740c002640b0402001914616404201c2d92421440080d14103952041c940a45445005842c0350000d0001c0c42041040142e1300d0301c02c1070341c11220068 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 250249856 1250 250248606 250248611
    0x307080318010b04090c03080d2c010f180b0403090b03070302030a0b04061a070f06090302010e0706020105060114180a0305250302090a0216150501170606091807180c03 74
    0x800c906007480f40c005d4050308101000c80d19030860b00c841005a021040d0408050358800c801c145500795041503644241841d40f6941c004014821f446007541c458810003e8443e140030341d80d8400400e18026010260740c4148110169512800d003901d0003019503008083c0304a000042003420750f41a40207603c2003003400010007800c003c410501003110f0242c0a80149480c004082d08070001400c0c002e8030626104207203034000001169500400e071080a0350880141c0c0d150005001090018003905000e800d2500c0204514a00320703000038504080c4c04002c02b05000001060982c1e0007010926002d021405030042500b40e69a1906943e15802088581c00c00c0c07100080381c40845500741030700710450350020808401c0791201592140250301c0072491000c1c0c6182c0c4119040002c00888109810b40c072050400200c541c50f0042e10150102041285805500804204000c6176680c03852140c208401800039084616042c6400e4900103ca41012008486110113050311000b190040700d20640302d41e506 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 250251106 1250 250249856 250249871
    0x11060c01050a0506121b09130602130f24080606091c020102010f02120c0a05160305030603060f0c160c17030d0b01090f06030c0203120411010914060714030708031801 73
    0x45d00c2d142c0b990b21030401c100209901e00b48aa0340340801000d50840728003980124a1091341d0748003000c030303404401d0721135901c03c01c81c10400410404a92200040c00030121001c43c00c0302c10f03400d4008480c03280c0c84000912904030007041c0581c6800055030003a0700090103c0d607210007000a024683d50b40320204900544c2003100f008030900c0c0302d00070783e08258100303000f12400d6201c58a641c2d040d5045142d840c1c040010070b1000050700001c040e10038205130b009440e09640ea0414400741800c07d40002c010400d050608020b00c5001c96401c0200e490046810305c00310204011813621203203c03041a40050143c104510784002070820120042000451194041003c076030118019070346140188190781300ca0b00c121504000d000e0194020406888540c815645400086400421406425141a5980e560911141c529940c00601c414094071141445011040e15000010200d1280f580001c01c02c80c0c0341b0780d41d8110b0390010000d039004207500c006415120720704107c2901080d9040e007001445582030402 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 250252356 1250 250251106 250251139
    0xd06030b0c181905010509060706020f0c0c010203030402060d05090f030a02031b0105060a03150f09030306030b070306050a0b0a0905060a020c090c27031006090b0109170a11060c01050a0506 83
    0x1c07205826a41c080d508075443d441d10006448682069000d00d802010411086e0300040d050300c002e140c40c100c803401503501c7e0040010024030702420885114190f620400912015039106c81c00c1e5100b4103002c1c00e02050594072003807a50300344203502120405520012906101e1743c0d070080042c08180030311241c0345c1d410306240d4204c58240c42c820340ea40740d00000060028004203c40d08800c0041c44a208000701e49210421800c0007100e0601d913081d000284e40d05402d008100c074000c40c03190000050318090000030b0820000450b81c00492152a400410014001c901c55000b420050b0003420010030690320f8804000c40070b034031030084555042c170518180c030004190648900c01e45d030300340f0246106d421020b1010f400c421100c0303080181265040c86003080c40500c0d84031900403a0081c1100ea580450b008001100151101c0d502c0d4005030140150011141c2200c1400504071000340c1c1c06c100ca044801e0b06000200c2c41030700c14203d040d91554242010003141200b50f80041c0d0007080b0507981c1c180402c001c00c0c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 250253606 1250 250252356 250252369
    0x72705010e04030305060604030c0b03060a0b03101517180106060c11010f2a031d010e0409030507020d06060807050904030509010305090c030d020705040b030c01140d06030b0c18 78
    0xd4407035100c00c00000c2800700b0710a174400c680c8018040d1000d403400b1340383d403030b80001c0480315403002034002d80020030002c0c80e0804d207140c980100000c8130751a0450a002d1146540e005080c020720844c80d12801245542c80d1081c469000c25038100c0510950368184914514140c556140780e1550a42c2040d0000440c107110b20181d00360f050b003108ac0e41c010902000011250002030403c01001c104100580d07910485100c0c003442c1c2c02e20010340344031403003503064038014040880921040351010468000b00b404c50341c0165814403550021140003078070300c08d02e145c10341e418010311a02035042449000060f04110181d4070440c140d4228804850440790340320700b0450300c04d40480300107001650130f02040d082940240c2010750021040800d40d42e00f101c111000c42e1400c49901040001607100c204200700508251003203108100090b0042c100c14041000064409101c4005c1c00f0000e4200180c04400d2501c0e542c40900516800703420b80f101401c1c20940000140c1044041034452000350705040b0301440d121 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 250254856 1250 250253606 250253609
    0xf15130f08070f031a06030c100507140d09050120011b0905030303073c05220e01170c0d060203070e09090717030714071502010204140f04090507270501 67
    0x5e10141c100c4221009034504001024051580510a01e0301c0f03401190b41e09891001d00c8207a60750b07a0307902c40c0580e042c041c841842900700346003e9008101d139002e00325071140414055681c2800c100049503601d40c0300c0402c036451281800c000b5480c03e144540c41074078034001c101e45d81c59a5943c180d52142c4400802d40c503440142c8103d030105040c1051a03802501a111a0305400b9080301d200030482504480301d0a00b80c040d5602400151001500d11100304001c00c4540c070268292550701c42ea03906060840c600003106001d513084407406510601340c501d82c20442102c20f00d0028116017241940307072030a00c000e5082903c0c42d0020451048031f2543c01d00308404000c0c455042207004014807464484815024656111410000e010400c116800b24030290404214403d5010041100c1840c1900b04982007815075002021640100b000300242e03600503003a1031a103d022901c1e07940c5080301e500010010b2001800090042c05001c2001515a411103031160640210341c24a44002e00a85100c1c41200c0d405d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 250256106 1250 250254856 250254863
    0x140108010e0f1b09041a0406170604080c0a24110a0c1202120f0307021203150f060c010e0c130b010c080a0c0f0f02010f030b0f15130f08070f03 63
    0x80c07400622901c1840500fa0928107014444601e02440c80700030900703650005154640205004032001103604081c401e0360018081c00c082c2401083c0b421040c951101c10241020381110000b180d2440740040a01041418950002d01002c0014887c0c1101c50910804600303484a1480e00c03002c80c0504040394200c43c04401c566551014030904c90795801900b42c1c40b50a800110711035111200d030b8040c00b0700e0081005401c0031040781d440c0d1030180d40091915100b209101c4034003070180706105a1000b4044000c48555046440080741c1e02c1c4200031036030364000c0340c0042005600b4401c200c01d0f0706001041e88010b5034000c1c4d4814a16010b60305800040d25172031180107000078442840000402d02800c00390090b1640341c43d01d901002e140d51600b900c5a04d808000762202064640007400319a000040e0035600e0310142010b1011ba010180047ca00d01c1030700b0780382401100090341142d40b407489482228480c88141056890b0741e51524001658034046009590041c0720b0503e0100e1010311056150302240d50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 250257356 1250 250256106 250256131
    0x3010501091815110a0203040f0503010c050d050601030207120305090d050301062a0c06081609260a0204020414150c0c1309020301090b0a0f1401090c0513140108010e 73
    0xb100e40e12014010b2800c0002940366607142071510854420000a0007980c116900860b122402e000044500c2c5171140c5c4014880c0e0b00d00441c403500d00da0000c0c140d50454800c0c1d0b03000a4180c2d940001a40a44030701c96000b02680500545004a01c0c1c066020500403070385007044410404181c0010303103881c8400c0c080c58000c1001800981107040100d00c58050a0301042416000c010305503448642c940e42d03607002603010800040400c50301c1c00200300c002c81c407600d541c03600f08480c0d444c0406400454600c00d41000c20054441c1c52000241000c118070741207070b58042c10865071969205800480003240c628401d2003040343d4114160003109030000d0350090619807000e80100604a03082204400c0a422080002c9442d401c407503026030350a1003030618541c0203581110b407910b0071f20049003c9681c0212240205458280408503c1403014603060540d19003c0000914144405040d18a8058050382000d102c0d00340802080381583e8000c0c00c8000c41080e241c80a0030398840c071b0300d01d00381002142d0b210940300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 250258606 1250 250257356 250257401
    0x1b0f140c09071b06090b101a071101030209061e13080f06070c02120d05040501260a2c030c0114040b04030c03110f0109030e030703080d0515130b0301050109 69
    0x80c0d000383d00540300c1c0c1c40340d080015100d0f80795035006002d030000c44034200682c0604038108483d03003940d810003e43c0710000000320f103000c01a5603129210440000d0aa04140c2c1c0403c4414442e1240d2003241d039200c5115a00b101a86c030101400b0f03400d6802201800e00351107035200002946040007031008041c020900180c80380380d50701c0608403400308100790305a9111075080d245411042c014030160510302030b50f0b174030150384904080014020010703c000f43c5188580030098410040c000710565608001c0610006c42e5062035200d440c00c1c101d000e03541c1c0d486082001420409034400c00030082654084801c000c0c040c070381003d00c8001c21090101ca0241c00c3c54120000500046c0c4141404d80c0c00d98401c1c203255501710813034214079262204105941070160340d00c0198000385908402d6490812204a00905001d421551901641d006001200350311940390408a41c8810001011301220300e0094842c0e1510060b982080010b0440e01d00c00a01a520784000811590044d004d00143c00712040b40d003684e0300c07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 250259856 1250 250258606 250258637
    0x40c052802030909040f0605010e0f0403080601090512011a0d080415120f09151a01080402040f090c180203010e060f03010b0a120201020f030c06071b0f140c0907 71
    0x1100a121400318001082000f06a507210005a40541e009a60704e116a80c031a00e8503008460042c0c00049480300e46804010a800102c620550300030f82c540f81198482e00e0310001030720000c4682e0803e0b0350280c02c1c0ba01e02d6000d079505510843c40c501124006c0d80343e0312070384800c1c0076138925080360107802c2281c200710501848002a03220500090b45180c01d489108084401d00116007003400031841980c1c940e00c0b40002d1048000c1d1505240f80701000030400091180204007119440351300b0a414440754100150642d510340e0b0004e031a180b00c1c100140300941240c60100303c1c2031500c1c010040310180106140003808818402c1e03a0507645862201612921400b081002e01e540c203400700c170b6140d900c40c80300500545510032420028420132202c003501441610029086c040d44010200d20b03a4814040602100c0c0b00141d0b00e900152142801c05441a40e940640c1d200c000e03078003020303048440e00c0b000b800070441200b42c4084400400310590b5900031a1401700705040209039444000500220f0b20200702 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 250261106 1250 250259856 250259917
    0x10212060f102109060e0609012f190306082401050d0602130608011a0909151810050103110a0f08100923010e0405060c030c1c0605040c05 61
    0x1c0349043c211001020881007040c400340e4002e0081250b10030f450b0400c0a103082402c02c24160440f0321070f4024800c0484002503400b0740b07410b00d4114100d000e26240c29401c142403071001c58481101580042c04044501c502c06000350080d0310a49000344112910140c01403114101050100303050407003010644d2802c82004201c1c00030a005407003066080040b8009180d560072b004004000fa511440b0032076251200d070002c103411001907180105410402401e403076441400b13155024000085d80c8a240d000325000c0b510440c4060f10002c90a07491600784a0b00480841e020700440d2402d9030b00b8800140d1001688a0170301031054051f0204190100b40c2461500a00c0640e600140040301817409960340e000b41000d54a9000c1c00c48012610075444241914400031580e014207214000e000c0305007040e542d6103a407124010000321b1000750120104080c90120070888189031401c0c40e81c1e0303821855240c041c4004200f580314136886507244c0003104070b070680a0002e954290802202e40006100b00700c5890b0b44 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 250262356 1250 250261106 250261127
    0x40f06050315060703120617030403020d0807020d0606031101050c190303020c070b030a050606130603091b140103051506180f0616050607020109320708010212060f10 73
    0x40c440165000c0b01c0e580d21880080c0c80d05500950701d17183d036140381130040c00031588281c0044883c801c1003141030800d804008101c4007207070380c1030790b026030079a1040c28a0b103035030f0003420802035104000003040028020707240c0003030098a01842c070031011041070340010b40d0a44100c0700d4072000380d000880020710b0a001c02c4030800c00345001e81005440c1080341c140e02800c00c1700702e4000f200c0029012040c418007240ca0f03c1941c0e4412420707100585800c030003080e00408055988128030401d51100520720800100316890303c0a0b01800c4010140241c90b0140740018100c6444960b00080c9004005610540d1400801440100103800307075246c480040c4020140c1d011116072540c01940c03048484c1060340320400105080040c4841079420845035103005412300b200903059504682c109526070780404c000d1440c41010440900401003031140e11010f00e02c0340b44c030340540384401d4080c10b44001444d21040d00240348000e480c00c6020301c5603591400700400e1400c02c66031290801083c4416001c450b0050f0241c0b103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 250263606 1250 250262356 250262371
    0x40f020109080f1e0304050303191101020a09180c082e08010501031a07050a0e04090c2318180709050405031b060f1f0317090a0605040f060503 63
    0x35442a281d80c1c0151402c3e00840c82c2026650141042c028040a4400024a9444000081c628051526001942d2400b40100403880c1207107401343c01c01c00900414144401500d21802507444541c808005070071482603124414a8200c283c0d05610b039408680b16814607004103131240304050726180e500c01d0426405a501900f000c2d0080d01820b501401c003113808005090f002c001107815811850609248480c000a9000c059002018820305c2c540200076510403050602d841c080310303c2900c1c0000c0107801030000141c02c4004003603010601e000424591000840081c01078400b4030292000e0014040c140030040e03002e99100004a400000b401c482d51102c2021101110b041c55103800e0120219002501c003101c0316031002031844100c028034140740c044100854050081850f00c81124014401c1c01004800e20a1034035070380544224908030b09201454029850340800c0e6810080a40b05902501101e40700360081500040c0c014441d8044400b51200207000d644421700d0324000f46c9142c1c10192688 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 250264856 1250 250263606 250263617
    0x6032d020a0e120a050d090b04120206210402040e122217070f0e0c03070e01021c11060a020309031204050109020d051507030b031906151205010605040c08040f0201 72
    0x400c4242e96440f50104400030203806003504020b1440d01e9031034145821011402d004800800b000310100000a64045940224810000202510014a240c03281d02607403004c049509540d030159125983e99184198403c0d9020000180003481c410380d6900c0940401598140070402e03484112000425003080300c040092100d481500d4034200c0f0110f105003242444282c0c048101049031062403010080144143c24881915040080c010350144c03000609201c14480070303c0340220640d2080014500300300c004c1c1200d1544a0013010020544010300b113517441c46100d2140803a140915034401c9900411801c0300031031801c0301001c0b9102070403000030001c1c2c4055680341650000358690041d0403148601c100d01906044400d040101450040a06420101032501d6840010350b140012a140058442000507002a0541c0f03095009050701c0e190800e040100b0300d02c00503040c15860101d0741d446106000a1007440d4a5070140030442d800360700d62100141260700420f02041700c04c02021030705401032501 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 250266106 1250 250264856 250264877
    0x303180103110d0603120815210a08030106020106031104051e18061e0a060612020c070902070c0e010b070b04140c09070206150f0604090b19060201050106032d020a 72
    0x30758048422035401500d10306c920000161840ea440510399a103c4c0062190702c01130891680031507040708288242c003084246250005118103004c000500306c0552280300103507650784450000f4060003052200319010240002c03030340520302d01801001d204051302d00c0c40140c20028480140b80003030003e003005a40c100b0030500d5001020050001d80c0c8244021501104000d140040300d60303000170020084210549415401e01049620242c00c008080c0300c0c00c00561038804000383c0f1810011154809a4038500c006210010400c0d40040c00c02110700100d10103010b40c1c1c3e036801a8445101c1c4038001040240c03404000b030000781c960324604000c5010902111504c0c141400440c81c0e800045d208030740940e012500304440403401400d04104428103950b14849020b100f408504076000301d0107000d2800b500c60340b4030680c0c0e4458403080c01421040c02c07000300500740d58902c0070b80206070030b006d18800030b81080d0b0f140c2294504041c20581c90b640d04450313071445840520640c4000d41110303400d4005c0101d40c540 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 250267356 1250 250266106 250266127
    0x5091503070c0c17064201020d02060106090b070f06150e13030206060409020409170703030501050a030f1b05041518050907030b040f060207030201020c0606030318010311 75
    0xd584500600d4550155800e407030b0a16102c0c0c40d10590264800c00d409994180c0000004200d09070040c0c195550010040e0080142e4400e005240707107050744643d14550340c5400e00b0120340180084c2042a02551305c1c04108440c01c0341c854809025600102e14001402c0081d40c106000034480540654030b80c540b0b07102144e8982081d1400000b42c03011400e20240306100200040c185950011440e60358032046006035500a034440b03070002c00c103070300c2250b485800c4820340d165038100051690340031801080c00b411506990055801c600703001c0c0d00107441c000010034141440250030050f00e0f0041d40800d0b1f00d00442e52400d00901c0580d514400481076040b00103901e0700d030341c05000701c01811008406a07843c10000e151500020039200713040c2050405052250040020417203600380d90300000e0011991342c640c100000e442c642d681c0000c2649100142c80307410701d82d040d400741c02c00f642001d050398010340b07d107003c060b070780d01a0000c80c03072070f8103030004000c0200e6019502c19902e020704100760a040117803804 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 250268606 1250 250267356 250267399
    0x40c26070903110102070f1203020d02010c0f1107030209041202060a1802040207051203010b04050319080304080a03090807030e1e0901091a0402040b1213120f0c050715021509030a0509 81
    0x24001429000c8c0c182c0001304050b0144242c0c034080a917480204018501c41400800b0700b0300300800c030b130305103c071001078607804c51004d10010028680150482013541003d207001541280c0044207072006020300700210349141103070b006002c074000c000014550003030f030a40c0800c0300950001408031020320500f044107440c054032001650007440394001d49a201e0f442d00050600f400001685503045241004909001032480b000f5070750010741002c40700ea00c4991440c2d040d0f0040044400284c0f00070300202d941c7e810140e10401c1c0000c000002c0e100f01d04a0007070072210480181e282c1e42d81c640d20504440c010b0140182550224800c8014008101251424840800c040381d10a030031042e0000c03000900c000d50f810101540d6070f0080d10500100303840c4e051680301c43c0300d5071240107500030401484001d82e00840b0701c0b86080400980c0c00009480d8080da441c1000309002c2c0110800c0400740c0241c441c884403401c148100a84215603880145150000c0b0503070071070b025804200540d80c01000b10948074402100039 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 250269856 1250 250268606 250268609
    0x1031407060c0314071b0503010f110703140c0105010b090406090e0d030507020a0b1305070501050f040303050f040e1807510e0405150d060f0209040c26070903110102070f 75
    0x1031200946ca58242010315094079400c11031040d140341401c0e12000003a010034101c0d0b040d60f1301031800003204030f4460340460722841254200e02c641d40c2010004501001848010404603104903010001e01e07039a001e1103130a6804604030020f19811940403a900d00f80a40c101d207611140600c160356081e1302c00c0d51191856801510104100244c612003142044020092031026000034201903040c500c0c5454000954490390000a0400c0400315003003080c01c2d29142503401504846070710780424501014031280341ca0515415086510035608002900d085440d0240d110405651a90207070b91411081881c0b0000b450f00119a01000070403021400303e0b4040c4070180300d2050781d0f1242100402d100801050340c6003d84518048070b2061403580540d0341c7c450080ca20030707a000304042021006491001c00a009200303440e0f401c142081408144503510034840007603c5a0003034001c20900f041640b016007101e0840e200e0000ca20242c809001203001c841c0c48000d5600305104a602c03040d02d40074045416201d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 250271106 1250 250269856 250269893
    0xc09120303060a06230c070b030406020d060b130506070f060903020a11010212030106110f011503020a0e330303040311010806010311040603090312060b0301031407060c031407 77
    0x403003801220b2400d240740368003e050a01c5d0800035402c181d044c3d0700c0003c0d00850050388102e000688940040c80030700c81c0d5002010040340c010f0301c81c41c080c18542c02a51041000f46441450701d00c000c20402440070a540b030a40d1002030080d4120304001c10701031070340d1203d003007a00d54055040b180300026105001d001c2d0442c4c03284d4050000c900f081e1415422800490004a056400c80540c42001d1001d21050341d045a0035882c004410303505107490182000c1e10303e802c2c26419401d04030554100ea02d1020400d00b02c070b200b0baa02024550340c030824004028015904076081c00050034090030204840211042522080105486018101000646554081e0784111034154220018009540e00f18087d00d92041c1d081c2003d105c001d02020200100e0701c650700602041c141e8918052080c1071090442003004100c610b0104031045e2541085d0301d06420911040718808106050728902400c041025000c444840d01c0701071040341990b030203070b490300021001080e0824082c0804004107041c0c000c0c0c002c04007403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 250272356 1250 250271106 250271113
    0x60b040c030204180501030f0201052203050d090504050903070209341403060d0b100306060905010f05031212070c0b16110a050703110a170c0406050103090209040204050c0912 77
    0x548908016140d071513002c1c0b0301100b4605401000071400c1603000400559092801e141c0c1c4480e000d40c06482515441c00c0082d84042801b00842005000955a9940165503e03103143c100d59603400c100c142c520840c0e856031103802c14400040181400c10016400240c0e1011603030402002c01c04103d0904000ca04040164400b1540da6003016080070044883c0c0e121081410b00d54500070011400c031010090005208400e10b00010b00f110840c00d2062000e554045003d11481d81c0da04403a07009464203018220030b030040041e00140c07134039002401c48810414030740030500f01000c586103140201c90042000301032000d1008030398000303051101c803d885034586000c409117001807594000d1000d076400c00404110b42c014590a40442c00000308601101e40c425030b140f40141c401d00c00b040140c00c05a105500c00a00c2850002c0d01e54008110344d64840c03000d80c1c08003c010741c1c41c2d00441c1516400034001e5000382410000c580503080541190b544100c0111016180c00d100801194003c0060034400d40744c0d40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 250273606 1250 250272356 250272359
    0x503190c060906050711041803030605190f140f1c0b01050105040513020c0f070608250f05091203040f0911041a03100510050327060112060b040c030204 67
    0x403840c0c10900c050040361a040300500d08118010b4580d20921401402c40e000c5805400c0196999402c00f132000c041e003200e0301546580516002e40906110301038070344070348101810784110a400111100454103200021202645402081c60300e60707600108075604035040009503030301900c8941ca149208800500c00b0f22159980341001c0b030782d061042c1c00c41810002d0411007005130340d40d130520f100305034040f400c401a46c4404a0300c04514085880250720501d000b090b20000c1c4440d00000020f02ca440c098800e4000801041c026000c10320309580901c01041d481c000030350201d4444d03001303002d00b0b9102500c0c50070703401d20385000180b82d03400c540d00c10ba030900c021103424802c016a41c001c0d0700424662080b1203042c00c1c10020580c0909904000e5100354a4010000500e1406480000002054003070300c0f142500300100402410344e4011205201d140e110b14812154940381599400015041e1070058030f0706034202030700742e402c0402100050310102e4807a582c1400566580c0b140c034458900c01c3c0c4006a840c0e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 250274856 1250 250273606 250273613
    0x803040b090d0f020d0f030902150910030902010912110a0b0c0c010302070b01030605130803070903020103240e07022e0c17060402071403070501051909020607020409030306050319 79
    0x4058258840200304540c814083e0050b00041d601224aa2a0400c00422441c98000b02c0007001000d1000e580100014010205401c0703407401007142d203609540044408903c544283d0688441d00002030000c1c9101c3da04019a003000007031404110f209000700a03201146400150304004690018441c401c000500118415020404020106020b080650901c140d5458030040100140700c06401d0399120400078410a00080c0c03107801081d4000c03072803902d0303081c041002480c2c04514003040340402e00e00400d80040e1442024190400e015a40c121850310b400c100110211103009800c040651080b0785958122400c01314056401d09107562640007051615241e03c2c0641c0c40c40c05689041c0000d02c110454056115000740340e001c60207440c05a50749a03245888181c020503403012010783d000106020302040810741005000d01242d00310100340d15601003002c3c040351034034413000398480342c20000d40700142007580248403480d0183c01c0c00121541c0d92004a410329000c02c600b114000c0484040c00c040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 250276106 1250 250274856 250274863
    0x2304090221060106180f030809060705030a0e1e130f0b030102042903040512030603030405040c0c060b12070314101b030f1419090c0b04050909010e0606090a06030803040b09 76
    0xb407400040313103517041c98a131805603201c21095010207440d0300c20010394101561071304822102700a03400000c6a9442c1c0710040020301c0000c145541c41d102e02e00d5449164114103020341c0144001d02c000b0209000c1841a001620060402608419209490300381d880c030340e0381c3c0a201600080074000415840340812008000d440c00264401c442360314003e00610002c0391000842c16002d10146010741d680f0307100c500020307155000b40d5002aa1050810300140c03a41940506003c40e02c6204070001c2c0f009a45101c1000214400b680120015911046040022900241c2d4062426220005646401a0b5641400140c4402142142c400c040c00107905c402c465140c403850040704c07152502080313401c0940450403082c0001900c100e000c050038540c0d00075120156402250f407079902c65400034545648482c220f8054103c0e01c1614400e840000000382101010701a02c0e000702d00300750290906950f08000c005000c40080c2251008a0365858088005403119000310301407409000207020a203010110a0329 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 250277356 1250 250276106 250276127
    0x210f07061d07030c05061305011d0a23010201060501050901032304111806090f0a14070224090d050f0708030a0b040b0102190204020d1404120206012304090221060106 73
    0x1d400104061544141f1814a6605032030092070054825904e6a481c42480f02c00d4211f01540407103d174000159079520b40e40000004024008545111b18604005a00321070a41c420940807030700400c100131442d8032075070054241d96040c1c0c601015090003070244204c001310454046403203580d070491031100303803505880d111200105500051070303919005010a0140b075014003100d00201800022403001c00064000800452214031102003520b4840c000950f1000c1c0c1101281041d4800c0c2100610460b007d00c4482c1304900c607000400001000c5003049074203034041d4803c100c1101c010300200c00002c1da00c10049d030003440e0030300700811910240010031048400460485040d5405002e00442c2e110461440070001d5404072001078441180d00840341c06000c1c00701d030503091807803034000300700400040501550558204d5421030742e0582e258089500f0800c1c00c406041c9040d60344c010a2071030b07880c060b00701152880c800303030079503540402d10307081da10590754031413610342040c0c00850040c048194003c00706070b03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 250278606 1250 250277356 250277359
    0x10212092704030206010e010b120a0207060c030911040c090e0a150308120a0623010e03010c020a0c06050901231c1a04110f0c0111030108060702210f07061d07030c05 73
    0x1c0f40c0c1d524080385109e0368481d0201900c58440300500050f00601554169070040f5001181030001c4022441c0013001044280000c5602c4a807410074207120341403a103c0e114032002030380c58000d5003e08204d14494117140080011b00038948400c801c00b03a60520070030742001036101321015903c0303815543c01d6460400000b0040078290b490f21f00d040080d040d01340340c0d164525008040e10800380e070500340101c5d000c542807100e150301903080100405203903a0008110618a000b1520f414101c0c0d1034800840d240d10400d0b080600242042202800c0c0f2004000240c41c0c20210048052410642d00f4085051425010000e41142c0d551030090604104041003002c41c1002100d003040403001c0d402c0340304070740c0c042c4002c202d80180c40411624100142540308401c1d4681911070b05449603514000f00b42e45041c00c40740e01005026141652007100401e8189404030301c120b00320380703041c069040303110b15581e0440720302941c03c5902c508407004203503613080410004401c1c0c400640019819030038403a050210660016 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 250279856 1250 250278606 250278629
    0x210c04090201120207060e011a030c1c120c0c0906060e09161d062802160909082b0e06040b04060b1519030b0d0201021209270403020601 60
    0x20060707078440b0040d101c0340c3c654540141c483c0884e05080000b401b25101504941d840d1482c2704581a407030110b174242845e0700b101100c0d90706100c80188a0b08103c0118441c43d82c0c02841860740c001410455680c440c090240b52200c0c6494481c3c0301c558850260740d06c541010b80d039501062000503403080001400c01e030246c941003064101904283e241d4084a0920f408100701c0390702101d0078241100b416101c944008100746d849000100a01c40b07000004840440304c0740710840c0e8120781a0020030103000050040007503800d0f0514104d005009004d140a00702d4601c0350803c0581102009440c24894000996800c0c0d206d0521440504084440c1d40700b02c06060350101003001700143c851084107030b0003507201d00c000c15400400b5020455078456103240e1900c00f6804642500d804560f07002c4900585059603051000390b180300d061001070300345c3d0300c80640180c10100c4071000160013800206016003001e46040c6000e0080c00381303080714548005600d200a41c0c8801400189541000300a002d0300824804 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 250281106 1250 250279856 250279871
    0x70f020a061110020c0c030a050105061216031b050306070c0b070504051c020d020603070e0a0e01140108092811040204050a120303061d060108070807020a0f020609210c04 75
    0x80300d5446080d00e040c243e01c1500020b4100f40000e06009034802c00c034000d41210311050042c41d1030340c00792504440c8a4050002e0107031076648614000f0303141511b881410b41c0140c005055403903401d8040b428840400c9803000340303180000d254508121a0f4030603445aa01c000b60100c0320b1408014004009d840072040010500082c40195900280c81e401100180100c2a80d10294800328a04160244001e903000708007008002d40641c001004621a4030102c4846040380e484503810031042c5800e004114500004110070800d65005040064000440d50300300c4002c81300020094640000404200346404220010300d0200800a00c40d503a01c01c004660540c00c290a110100746d0032182403040d6100c0700010100300c01418001d41c00381000e001d0988280b0b141554807410100c450a05030703221030008590500180280b80301da000c50340a805141d000e032203002c81c583c4a803480e510b075a450690340000c04100942d81992941e44201c0c0e0401c000494000c80d100008805090182030998a80254185441c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 250282356 1250 250281106 250281137
    0x1a070e01020c27010f03030908070605040905040f060606120615081f0807031202060a05060f060901020f010e0d0f0f020a08220305061f0b0301061b08070f020a06 71
    0x80780d410320380041e00c110b908410216400c894403002656400203c4603000c0000c50700703514001c114415030380640c5070078000035aa80d0406613200b845204074030000c0d509010038840c0c1d000d140c00c91178116014540c1028240c0380e0f81c684600f100c036aa40001d0204400d2681030202d4031847c01100d00800310109488251030b2003410107014860000d041007112441c4200c4200d80c075890300305170350203441840b0403500c0e401d80f24608400d09100b0f10703441e0070151040740001503e07032142e40a0780b0301c01d4401a205201ca81132200a21000760001e07880c1c14103501603200c203002611400d1241c086810041401885102e0754250041c0104500e818490108003202d00b51201c016000511041101d500514542e52090a407400300c402d10601944154680c441341070000c14001e002400d01d0003407540c4240381c034062808900c05007400c1464803400c5080c84007803004102d407030b001d01446544d18003c0d200b100d01c20440c550300c041d4154444e00701201c4c0100e1408204003542807801e9a040a81400d040031003801d0340a55 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 250283606 1250 250282356 250282363
    0x2030a03080402012a060509061005130b03010f060302120604110f150307020105041704030f021c14030403060f0e031207050c0d050d050702160608221a070e0102 71
    0x4040d050064050118045910400d4140700f41c0d0a000b0811202c4400346401064607800717404240d03070150404003c90b88010010507100e00031080503203405d22582c6801c061122500c3c83c5881d00400c03a40d0740c00303a02d4031900d00307015446180300b50400c00500c0c142107204014041214a0484259600001c1080002246240e02ca511400304a403000032000182c000100e0a4446554801c1010400f0050113a980e0301500018001d6108802c400f00f0006860303900700705801103100c041d00d05100c18140ea00903051408110019112212034521031046a88a038208290a1480340045a00002d010000d0003c64441c143d0314101c01b420500c0a52400c240d566503a0090200400b0030000c14000311b8a054015000c07038000c0c4003200c06079100d8007984403001d0140c0d00100c040805140c1003600040c0020b10204a207124065070481c64109a41810000c44210b01d000340f02d101250080e4040340c0c80040300480e009070181c8076501d80d00ea07030210b801248548000c090891010300c0740c0031000007501d1380c011 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 250284856 1250 250283606 250283623
    0x60a0e07150311070c080a0b0f090a020402030a06050303030c0a09050303030105060910030b12030d0b0a0e04030f02030c12030405160e0604090501090c090608070b030106080c0703020f16050a0803070203 89
    0x42c640410250300ca410820f80a2150758001003101c0148000020080c80128003100c032580030343c10341030340c59491101410145904803030314001e68001c07072624001031601d0340c0070b182c0280d41c41c1000606540c0340c6010074034662041da01d88400e03100c0801d640c0303c1c1c1648180400c01a24007a07000e5415540742c00301040c02c0780a4040040d00c5110712402801086120b54407481640c032005000051810400c0c000c6510f03980034901c489039240c10400d000007e41800c0024404480d107070704128403540d0302c81d202101c003120b03954020300860000b005001a003090410030b5000da202144030b502d9070ba003028a8014a81107151708041d030030303c1c49842c0401c02c40e2125913140d0b611040c02e41d4041807414052400300e0060105075002441e0752188400410312a9181d031141e0140e078880c00440d90f0741031702d4100001e2130780024860080043d03a82e90016150140c000c0292908c0e510a00448a202e200881691300b44800c0d84040116084c20700c1c0304010038900000594018075840000e1440c00e107060700440d0311286d44 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 250286106 1250 250284856 250284899
    0x6050604050f0d02130b040c020106030807080309120304080315240f09060409020403120804050316080f0c0d0906030c02060f040201091701140c0307023408060a0e07 73
    0xc1405000b9490f04158510099401040c8044901203080c842c0001c01c02c0e501100d010700e11f007041010b055401403080c80152908460303490304018603540d641c5210b900c001d1000c0354a006008140c01d543c440203028501480c81240d00d907440b480c2200c03990800c052160580b911500740d10300400e0b41e0b0204090410000080085402e54500c0d01c00110740080c80b9051880e5040354001400082012027507000d081501d22803c04007601c031042500032a01d0090a80d0041c0c45074004220404c03000000d000000b106a11440780c40e41000c3d130441ca021003031342019205884542004500d045d0071a84004040f003d006203081c00c20081081c100c00964032000201010011070400c800720302568003c1d0701d010014042030091904016140440601078482c0442414651281601182060b804c0e03400b5248640c038154018802c565805901c55400303296003041c07103000800c6a2003010f9110901030b888001d07000d002d0042505007081e540324003c85910100302030507038004d140103001483d01d0703200f40d54090b40d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 250287356 1250 250286106 250286119
    0x16060c030f0302130306060906060311040b0a090306020a08091c0212030a0b0d05160518220203100903021c080c0a180f1e080c04091b03080c0f010605060405 69
    0xc01c0200750001c0c41002c0d030340400507000850010401015030014815181060340600c90386035500c1043d42901c1006502c09440c60092205001602c01704010b4600f50606140002c2100e54a403960400ca0340010304000c00620003108004803044100141020004881000151907900c040000c1d228805106100121500000800c110840300d8114441c0054006c4c07210301601903d01d030140d941d1502154031100c80913105000078940c43c040074004512040d030303d8012450703520150380c0c1711105240f9150700d01300707005401d001d405a101005001c519086030400091071075800e0030064648100c85070380c02015003240f6010785e4180c0d400a18079400c6a20b84010540f141d685840940c0c0c030940380300100401c02d490301c00c00991641d1500500f01103613507200c039505200b0b03140c144d5040040c00c24090703021668000311800f0780a08207580103410302801201a003600c1d80b004d0f2411080441e065201341d4000e440400c40d040d401906001107040d04180703600030801c00d8031342030201361a40200d2242394802c02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 250288606 1250 250287356 250287377
    0xd05090f0c060a030b03030d0204030c0e060a06050a03090b04111302030c0702010f0c08070b0712020909220c15020c010c0506040f0305040810051b07020303041e0302030303160216060c03 82
    0x740203030001e199000c001800e0760388036075236496444000d40183c0b1050b61061445e002c0040c407940c2181c03001d4018200900064003860400d01c00ba1079030b80c091340d07020040640d284407070b00111701450311f140d00031031040500072080f8070284200038109001100480a00d48100203000c45220305908581d00640c3c2800c0a560b0b50041c9075040d02d078035242c1c000240c1084400070341030003080b100c1e0349005e1191546450f80d045588165065400b20300800b0441078202c810340d00490010204400360480e9959044180d464241840d41c2e1291000302d9588455a484030b500c2441d02c0305030701405241c2c429607081c6001403271800c554031010350300d40e8094006003884090b1980e650a252044040760050072000b4201e8000c48070400c0c0000052200721a1110300480f110551201100f607202107900213900100114140717410061500c103c130701a158420510019071a0010042c1c4052000e075205100750101d1400f4101d41100c00703400c054085210703220001c0ca9400601035242c2060501002540500d442c8101e013 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 250289856 1250 250288606 250288627
    0x30e0607110f041e05130f050109030810030b0a05060415080105010306050105040b090a0222031b060305091e07080d091406090d0326270105070e01320d05090f0c06 72
    0x102e1b040d40d0044d000d81d880344841d03410320105410050a181c070070b0303440f21400d035250001c1d84d09492090000806030040d010103d08d0358804c0f60802901710000030030014030000190084811004030b0344c842031040e5141c20040060151a1007064010030040c0d4003442034800c650f0020b07180c0b8100802d00c520707055001c10b4100b8450524141e160b0060a0544411840740d01d80c140a4400d01075510708003100302c120030010410a00c00c0c001c0c24001c0010714020642040083c00200d594141140d400d0748a100b130b041c001aa01c0c40810140040d110151240f031400c03404c20841d25140700d49400981e0080c0700403c02441030303855803550041c10542624119a40c04d26050040c03079281da500c00c090409500300c10920500103da0b100d80007080842d18241503041c4058085103098510490310300000c62140c01c02d1300025400b50301142c56060050109440d400d5021121844170b10ba03449244a0328040814050440c2140d0322a03207801c02c0d645402807030404041d5004542d15030008030b1141c0500c00c00300c0c814590 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 250291106 1250 250289856 250289881
    0x3041106130302040504150c18061d06120f0106140901030209011101050a02031501020105042a090c0801050a051f0509120307050d03061e05010309030e0607110f041e05 74
    0x510fa00800a0140381000c1c200061603521a80604845526207000c4a40481c02540c0024101904510a4091624120080c0d17191030040300520103000d4860602c0c841070741c0d004010000400950362103051030402c408090b00c500c0b8141c0110040c44058030000b09a04061390664003410401d00e00560b0703c080e1680102e901c4a030b0b040441c81035600700000c0c03042408880d000387d40700b2080d24592003000000d0400481c241c0e102614098140304803440390300f030403115910441c0c164074000c0d45035140d2143c1d159030384012641d5159098002841c08001030002d803424030380d0030005007411200300d09401c01c00010008038000000344507052180008035000c03542c56407440700b40e44215600030360351107251500300340da1100340d020807920001c1e15100021a076000c0340c003112100e90f00e80c50000c03001103060074010350041030391000070b4041c440b940f1500100703582c0d80c40050034114411460b94100240032028000384c80c410704d04c014440c1e400d007012400460614400a1101e29001c0c502182d035031202d904e001034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 250292356 1250 250291106 250291109
    0x6030c090f031e050f100506061608070311060403090311090c091221031914040b062b0b0f01050112111201120c080c090601030e280312020304110613 66
    0x4602a4204140c0150401b01e640c044440c0c40c1c05050000b41c0c0d40204006203072061203241b026100c642d20b008404a913880015103030052280c18150440486407100900d8000c049500310005000d0280c2130007089000500680d0000042d14504003606050100d113601c1d00411b04440e0291807034050074041c6040400600d0303c5002080c040c0203070303503040202030740507944201c1d80d0684520300703104204c000010b07900c940c04840d005654200956211a9030700c82c8a40000780880b603100748410592881180c1110b081030100c483c844118050782c1151404a1120718010100503803000754100402a0b41d810070103125103c0445040010110700d002e41c001d0f824005c030001e80d208180c1c80360000c41e0700d200d46c0ba52176a00c68090b01c102c00b805030365051065940c0800f44000c5400100c8a40402d0b050350207034014182a03a0031030191060a002d00b179a0152150303d40d034261041000781d00004050540023120b01d08005060801035142d464151101143e10460a404a0141e000010084501e582d0040c040c0b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 250293606 1250 250292356 250292363
    0x90510030605010320030606031e0a050103030e0102010603111504030c060504050a0b0c120c150702010b1017061203040e011d0705031009050c040503150106030c090f031e 75
    0x8114404590080003803046004842c0400d1600b00041d46048a0043c000c000340f02d14070f0405d142d0b80c0e9000511205400103410f100030605980f0718140c04942c0340300414812441000c0000340d030f40c51401d009008000d010b0307015055902d0020f040c00031400007511100e012800340c03114440c2e61401404100d2511aa500c040c0c00c00e44103032008103040380d00000510489204584504200d03869580e400d01d11711511149031412742c4900944600c0da45841d003e401c02c001500c06540c20380e50a0021241c03100000c0f24a400180d650700c0080c000d9160041f641c50300040e061a116561b2416400c00011b480300240503184142075201071007024280800459000e494008588615565a21945881000c0e24044002e180440400089000b4810f5007624442d444101c000b001542c5044039440050002810b03052202d0000c11012403661002c04c0200c13103808142984001c030307615201c4010201c1340e040400104004401108014505410b0448019690041ca09c8401b907040b012103103024201604c2d000b07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 250294856 1250 250293606 250293619
    0x50c0717030d1506090803040f05011409030f0129061602030304232103070609141b04050c0f0d050601020c0901080114060307270b0d0c03060b150a0c030905 69
    0xc000c5a030035941c104a500701d468110401c1e484d1000552a03015a000d070136080d01e12701c00100003561162010030b4515245005030f0345414545800b081c2405200754142c01c0b07603034542d0010350b1800c6020004489448001d182c0803106130314a80052131922407070440041601c06400b4103429903400f8800c07580108a18001480d20314040004001501c0709100594401c0c03106110908800038446d0081f5904200c004c041c42c45d08407160754140040070042d90550700c2d0907000101041d000c4042003c0018100f1040300c1d65160505030b8200001d8410007030400b12410000e100003031104c0c486a040c0c0f6aa0222000041000d80e20000100d14001d006100c456100f042c0d80000a154007040d884001036842a6400340e00550701c14080c59a82d05a138424000c1e2041d40030b00c2008039245080d0400b9900702400b5010480c03401207c0014004048600141c03800041420b08104020503803260000c060400d44e03100c01074808008505805005440040742441003060040040600c41c9112002070721004104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 250296106 1250 250294856 250294871
    0x20d0c0801020406090e0702010207020913030c06020c0f19020d0b04080d020d020c01150305120f090303040303051201080a03080c0a0e040e10110906030c0f0c030a02100606050c0717030d 82
    0x41500e00703d4446c0281d00c48440c00402d000c18810300032158400e1b00a4441d027a04e0b102e001030300203900c4682c2c03000d0301080001c3c240744c0001400c0b40010300d080c244c030070000c00e1909461001e0a040912142202d221040c40c0e0005c0c00c010785031503042c0f02d4000c0d08451485042c0c1c1d118180740986105022030b2a1400b840000c0702081540a50b000d0003451117440b008100714090310900002044e0680006003455003c40130b9140c3c680592002403425803d07181440e400c0444250100c0d2854000d038000f01c01181011805c01c3e1000700c0c3d0b0300a24018801480201210543c50b200039003041030240801707050703400000c2c1040703046001e0b807000342030008050b10406c5450311140c0c5045d1600e001c0320701c41c83c1290400101704020240c000503211010301c0240b1072407030350711018150b8009900840f40c0c0da80440c800d00c02802417030f00a0000e000114900e402901c0c005480415031030459045801c490280513052218604010000610030262104181d1030703400f42c0c4204480a14501440840300c8459040a20 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 250297356 1250 250296106 250296119
    0x7061103040b0c07030905130b040e0a05160f060e0609031501080c040603030e0f1507050601030308100b070201030c14070804081005061320030403170109020408030403020d0c08010204 81
    0x2144640e001d0b215488464840b41e0700c0e9001841981c2020303000a540400c14811880c0520b843c0c004411401c0001641e22030050104040d0b4108421089103a00000a1002403040511185901041000303a4500031340c1400860041c0a8060040600300001951f00c001161582c1c030440386120802021a039540c00003220040d20003109016801c110301502c403011600782000e010780000e90381d254417a03c000004881c24004614000c08d021940a044912410300440856008044690140703014100070341c11400c0107040c0c4c440c003138404c08070902c030070b141040f00040080039168003642c24640804c42d103021301d04c12500d50110305545510a4000243c220411080600a000321280807050311000c000301008070086034000c0303682a422091000c2d1800746d0100f0740e030100308400d151581c0d0150b004a1000008581e0f00200c400b140480c0420384840c10f800d040b802d131240100003448040d468582042800394070307030159100080c040e0b4880601d00c4100036005000d44040e100fa1002151035075613035817 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 250298606 1250 250297356 250297391
    0x903100609020310051c0f0602040b0c030318071a0310080106060302090111121603050c0303040b070305061f05180607030f0906090312050723010608160e0c0705030706 74
    0x88a14401e0310040d00d0020340e41c2801c0d040c21030b071b45522440c4801000107903203072042d00700c1d880c54049482c103900304000f1034041481000350120040c02070055403280750000014900410011880016a10429040120140040e12140075110000c961a1641c5880709000c10320a00758000c07802a5090800121b282d5915502a15844101f40d030740200002901507031382c1e114101700c1d0078184026020408074501c0e11454500038030f01c5100b480c000e864045c0900031503085070819102110611051024030442c0340d42742c040d490300044122248030741c01881c6600c1d0720451620702e45040611001044400080d1140d900040c540c034405032403203948031240c0c80c006008040615a01000c1401c0c6100403500c07a21652404d4284d9034081c1003814042003110054400b6000844121102c0c4000c4800004400c501500001244002c42c00418100e091020003400c02200d03140c030036071080d110b001c204503c107070010000780c00c02c85445625030f0740c03960707414010300354031801a000e070006040403000706c003600300d01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 250299856 1250 250298606 250298611
    0x6030c040e0a06091401060e06150a02030d05040b0f15031e070509090102130b130522020705010507200304120c0312050309011d25090906061a070b070509031006090203 74
    0x54000308003440e05c031000c85000349230944680b500040c512820b0001d506c401d200400c211030310341c0112803e041c10840c40c2001d41e08215802c4074005132800503c486402c0b031200031504034880e0322410507002130200119603110660304240344419680d51113050521000c0c0001c0c0d0203000060400b801da07240c0003400c3c6000c1d40c4909030580c1e00f649030440005001c4008415602a42c918020b60070f0345504e04010402000c1310744500003035524111003002086005031000b80240b51069002044620f80200060500040b0702201c052462143c41c0c25500d044010046034141d401a00c40035031110b00500341030300c03010010703003009140c1902c00b0b0b216a54907410002035407003094004c00900200000001c610340ca00d00c020044407955019903106c6800d109550302000c10901e8902241c00280d1381e03900d201c8280d5031400003c0d240d040c0c3c0d5540621132100c8450141c0d00301c24a00c8200d0b4034042c40399880d112680d90040502c1b04014022445003031598091000c4d60041850000901c0710340d40340e016510003541305 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 250301106 1250 250299856 250299893
    0x5030315010c0c06210f0c1e0c0f140f030712050f0d0b01020a151a04021e0304110402070c060e0d05060c0a030204030b070509130506030c040e0a0609 66
    0x4620005803588905095500c00f80d001c8141002c2c030b0f00d880c000756940355044081c290450715450703400981c03651520a1585400f41400c0210b0b603000800006016038800d08000ca008400c80c5600400e2143c000045480d100e5003e2111040c007d01c1c2c2c01d00450001200b10b032503003203002d1003240c082184400000381541c980103088100c0648549081600d25200c0c28486e50813081302800b4680c2c03400300b80c0c2d029606a11043c01550076254480c5e80b40503800080c40254104940c0d05d26640b4003188110080d4080b1920541e002c501c0c0c0481e41d04100040030076054404000500000000c0822040d500d0744c03120840c2c0a40155181d84180c0f900b4101d040303a81c0110340000d83c0700c0c1101411071604000c070301d015a80000252030a5100d402000940b5480700440c9002d240e000c02001000034640540d451141c2043d6403803d481314841c00030400ea180110555003c040e0034841808015900420318074070007a002c4500095040c5112889410702c3c039141c0c0090031503443d0007400414094000e01e4007903043c1c030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 250302356 1250 250301106 250301131
    0x70e12030f070209090d020a02011209020a06030608070e24031f0902040c0201020304020a0603051b0408100e1f020306011e0305010302010e120a29010f060f050a0507150e0109050303 80
    0x20380c00380091341c0d414646c00480043c1c1c4400300301c00155014101041c461141d0384030219484075140c0218a00311495072007440041d50340c141c108116002407200130054a41c8031015003050420072908005540c0054903000c01104004800e04156410450031591405208501500041003180c1200811041500380d0007030b41409980c0d0109031062003124410ba50007003c074125642014070840040400030303d00c003129008031040040303c2101501a10003840050010855560a060f10700150f481301c8003200d003958030603e80c101d00404c20648440707440c1e00c0d901c0010b0b00d9070703182c00048480e02100c80841a40e4054401c0c00b80d5007643c5a0401e0b81038070300030707294104140c1c51041800a11100e02e004030f203258004000c1e410000d1840c03146030310300d00800005408440702040780c404c40368400707038002d203d01400b680040007007640004000710900803a00f4002d00b0a101620081e22603c0741c110014031000e80c10b480001c0340d142e03aa1004100b8001800200800d400d01e20340190f40350300035904001840c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 250303606 1250 250302356 250302361
    0x91903030c0e090103150b030709150306271101140706050603010501141507060f0c02240c030105092e090e030408030406080a090b25080609070e12030f070209 70
    0xc0c4210f4050489900c111014002600000f240000f00040c04c2d5103a4140100e8100003004400ca01410842c1125044580340c21442c624149085810650700f211041a092828000e00e1501e40314000c1c1194200090b1450103652800403208003005000d407074040740b00880d2030020703c01280d02244c0b04034400c0e0000c010303598841e503013134500e032580c00000c81e400032005201268501e9651701510303e8178420f0002260b1600c1c200c80442c05d4480f2074403078a0059201044039440d43e80c0301e0040340c480c0c01008046401034289141d89540d0f41c80140181130003040b082001c1442103601a07031210440f460740c00020007403c00b4000e000a10200c520408042a0602100d8080341c0340220449003150704003401945010301d0603a0039942e108000b0320007201e40307a64405080100701c0c1181c0f00c91091142c800b10043d192034043e1420590031802c0c00c18030400c5244d40400c0350548440b0400d50304810345003004c03045100010002041c400c0078118104c420300001c1010316034005014003401001d4402c803034441147d03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 250304856 1250 250303606 250303609
    0x9030f02010e0316080f0706050403090b1204020d0201170403020706270909022206030210050a020a0318031703090c090702030301031e140606091e0a05091903030c0e 73
    0xb01e9415a2050940c2c200b0004600c0c21013100340882c1c00c4501c43c411480c140684004120313650f400c00e0b00c041e2002c07500d88040004255014602001506045c40340030f00301f26024031400f0114100a03c024010180e00321000305580c05002c84140c4180c1d4486055564540352030001d44501e00d40c4030b00c8022500d0220b038081c8061088a0110b00d082098115002c071030702d00109100500007000040c0c1e00710103600c442806803017020006116045001d2070104160789580705000280c0e18039019803081107c280728a51a085c0d001c100c4641141c2c151800e00840380b00051950024030300c07903000900b4040c032154a12607107611078000d140308100c0e20050b250129011000d001170420100e50010042e0400c0006000241c180a00003c103035041c9400b500c901c200503a00d06a140781da1440311113680d4007500421105240a104c4603502054104166460034010381d040002d03001d01611107100b83c2d031070f10006840c01c4005c025542ea00c450420740c2644002a03401c001c0d000303200ea08410000216080c0f21030689 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 250306106 1250 250304856 250304861
    0x11104050105181c0c03020f0f03030a12020c1510091103160203041d0a050a110f070602120c0403052401064d010c020c100207080a0609030f0201 64
    0x8031031041c2c45180c682034041e841000048150140c46500c41c07072900301c1c1102556880054200c0c01d00c20114903100d1411801000300181c140340100d44a803014007109203442e100031080d80c801419500f4241c04c441620002e00003e0302070285020400e1051903040300420320111070440c000d03c441c4044401c0c8948400704030054904807814051001d0003000403a00c0700c0e22240c50300309050042d2040d60309003520b0702030411003503203000d5a40000d1440c1e01e00340110040c1d1881666003007140d1306810004400c048030f4145503405a1700c180c4507504004942c0324180a21501100c82242d002203c5075a00e15140c092104640c0180c0800d4500b84113146614503d10700860264046070403404080680703a03c1c114007100c80c3c2116020540c03140c0040d00d00c03040704a484085910b00d441c0c1f52104181207010343e40805d94507802d110320320150341c1c1c1000080e0712881e4003c00c448d00703040c2013959040207007808154203a1038101241c0c043c0240b0302c0345411000034004540d021030308482c400d5540c0c1f248a050400103c4c203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 250307356 1250 250306106 250306109
    0x507320d050d182309070f020c01120b060c0609150405120c030c120a0225050d0c03050f010b01090e06090a02031b0c010c0e090c16080c0604110102011104 68
    0x1c1503100b14200d01509000354050541c1d2a40440c811030256150b41c000111003032035249030b0380360144e0034104901a00c1c044040ca44d02101078988107508038810a8000d40d20791040007a20705001035040e550381050070903000f03030064040c00f03000305503124848505142d07140811104000300307015080c000403007880c2c800510760159410200810b40e0515101200c0c81341d0303000030300201070743c8810890030700701d03040600190310300d55080d01c0210b450b03a040050103400c24440005089030a00650765041c010030480003146d051340c10030750b00000d0442e40f600c3c0120200695400140c5940308280c10304640101c150491141004c0030b076620518581e48400500d05200107a8105510816041c0080c0045491b9070146903c03102008101d640f280c102d50b0100b020b035101500c0305905075160500a401581c0040d0f50001d003000544607005a4074110280a0090064225149602607148600b2080c058030710142c400990b410810745a0600745072800301200d245040310140903508000c241035480c001d0206a80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 250308606 1250 250307356 250307363
    0xd030c05160b0a09020301140103050c0301021309050604141003330c050d06080703021203031012060204090c0e03100501060c0206070203070f0b0301080105060603070f08040507320d 80
    0x20800603942e940c2c80b5807000200010314803039a40150b4400f5035401d0141c0f50038100300030880e6a886d41036050a5080c15440516103000360700400c1034011100340350402000304c40c282d070000111902c0d40d000140240500c0e004082d24942400d05005601250f1310003401107038801c0403194482000d050300d03822410303001c000c180f507244600c1086040705030407a00200790020103440d0041c98204124104001c03120b685c0c00a4450341e02c0458140110300781241003401509075203005504502d4803a0000a00f004140216140b194880030000208403d40d015140030300110b080c1446010103140c8000c8c56134400b070365400d11902c18040001d84640d0103100da581a520030342c0c1c0f1588025115024810351f680b040310202c1e09807141101c00103c1802e903c055074080e000d4450303000d0ba603500d00800b0070709440300542541d11642c0c0400602c200560000d0011219054609004240c2e41d92800c00030b042002a51081030503c0c2e40114511420448012840c03a01403c5a05042c10610340e031b007441516105030301c005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 250309856 1250 250308606 250308637
    0x5070605180624010c111c120504061706030607110102070506010b18090727090608010c020706090e06010c05030c0a110406060302040b0711060706020c1b062b0204030f050d030c05 79
    0x411540c184680d031004c0076003184103000e02a07107d41d9100460038010f42e40d42e00c000780000c10240318550f0b101c90515480c80700301c40e41e03551604200c00060b480740b002805140511034041104c40a0a0081d015501501d41090681d0344540e980c00c210b090b02d5005802801d4090700c0005031a070549042541a4021096640c56969070010310305904500c0a01c1c55030400720b904900300010745010580640c2c005081c1100c00854007588e0740b800a80b03000c509030484001c2c8001401c2c00d1096035100451281c3c090343c00d2070314410800042c101282544100c4a001149018110703107030701807143c0710780c901940d18030030794080001581d11310041f42240640c0c001d403400080d04104c050040b0303414001852100400400c100c1c034122090340d404089a2250920181c02d4000c1082400200c4942e1280e50000c03070107a903407901d402c54025010658140e00c2400359035401c000d010790004800b0382c0d07054030044d562000f804c1040c00073b1410120b07914000405111f0009003010800100e4070b10800c155081d50a651046 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 250311106 1250 250309856 250309883
    0x102010e0d030209040207170702190602030a0807090e0423010606080a02070204062303070f06120c02010b060d200903070e040203010f0615080601030c05070605180624010c 76
    0x100d029501c83e550299002d50207000080124000c1084074951488c141070b001c0c1c0c0c0c0c14451041c450b04007010b410794081c07200101c20410016070007208a885c0d00c501840e103071203155503038407040c2d40d61030b1280c02201d585c4034080f080204000b864010003200001c019446070513180c0d041c080c6030a0314100d001e031400042c02c1c04041400c01742d0b2500030300041d620080004c03e805803030740300611072407002840701142c0c40c0362a0a1011642003e1010b10050400402001c140d070b41000c1e8084d00010440e4454800c4642d0f07080e0340f021083c400c1d401504122001800300755200030300b00c0e840014000d0400c0904200f01d010080800c00b030a12001c0341c072a0030300500503014003031903c200d8582000c002031081e40c055488400c03882c2c00e01c0a034800c0d00060705a90f0214040644030480044c000c2e08006d0a00d810b05251002d0106a02e4020068840700303070740301c0c8011a8503640c590024441c005803001d00748827481404140100c17541e60708015801400104141202c48071010011201c800c041d034405082c031850b6601d03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 250312356 1250 250311106 250311133
    0xb04032c0d080c120c1c050a1d1815040f0b03120315031c03150614071109040305040512070302210a050a0507050109090203010308160203100f0504110102010e 70
    0x504201c0c00750b43c064440200c2070660801e059484040c5452494004411440e032a03284118058000b1135546402c600304a07000e42e002c1c0455041d07031503664801c445908444074517034405031580c29501c6400f07d00565400c0c02510754141d94982d1038003d01c2142010800100209940321741782170030300d006004041c40d44098200f1172407584040c0c80082c44000300004004552010020f4403160311030f0001e80d150070021014001d04462002100007070802500fa0104401f41d401a21110840c00304a07049540703004601d000700d04000d8100301ba64000c519402000300b45900030014004489042c0c5546041e606081806900d40d4401d00009510411201d400308180000c40148803444c504e050481d0000c42050302d44074980424150211025402204103108950381b04000d44020b0050b21000e50965045643c1c608003406201c102c1c1510010210000c015903408105840c0d1950100d84200105002408240c0240904403000c0c0d480b0800505c550502c2d52051007900714018818001e080e0500c61703a107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 250313606 1250 250312356 250312373
    0x603040c0e0403091d070906111c12090b0901110703020d050702040b120604060c0201060b1e07020604090c020c0d02030c0f03100f020301080c01050403022206030b04032c0d 76
    0x4006a00708040804041a06074410380f030313043c518000c0f440300540d40c07030038503402810302022390080c00c01c01035035101e11490400c0014408040c0300500150100c030000030401152100d4180a264110078103110380903080c0000394900308e00423981c61000740400c0d60700c44184581c03031150b03003c0140140d012a04080c0d1303603485074000d462100c1c402880032903540002c40000d0740360084034110a00f035030002070600c0100070a901c1a100000306500007030040c28500b8054500c04e01614001c40c484414290a81e0400e4414104a41d031460740109070781c0c2c4580d11821440b000f842d104000c10054843c043c88040507113440c80603044215401802420801481000d0040070184161810f402d44180794002e10140035601512a54129a20300140c6a40c944503000d407500803a10311090600204100500150f1a8248400048400c0c452016000256010400e0090806610113000f06503444103200415a1007100d8071a0444204e41c40303020040c807c240712582703901c80d4001a038030800103000000010101d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 250314856 1250 250313606 250313611
    0x40b0310051509041a03100218280503032704060306180b06180705130b0d02041805010819021206010801060f08030a0503060909010e0f030d06050603040c0e 69
    0x10303001104030a6558022440c1240307a81140645150042080c1c0d0440c00c0070702c1102211305403c1900c4088152510109481e03400703800c0400c580d1a00000c415140354030300203c7c1d0720a070314080c100d245d800c1c00300b01020000c1d128011050b0101914410002594500002590380d1a41c0c80c03004800010400301c82e4249400e1400da010303401c0340c1c851900001041c900d1089107000c11002880c441c55000302c2c0340c100807001c00186454031032240311a91b0280101c002000d030740c1c440a142460390b5a0707503c0030032050391085a944254014500020135106000103900600201c804160103021000d40f00030054042d42c00074000c041c1c45904c00071006100070b000700481c400c0750340080c00034078a802d107401d0070714203118090b048002580e45480b0100044a60125160700806600024500708941000b00074020311014000d148609003800c041030744110294030181035604407408690a42c40792006058503074202c29480b91480c3d24000e4002400d05000048070300c66517000210641007410102e4100715450003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 250316106 1250 250314856 250314871
    0x50604060f020a0507180b01050c060f04021504060f030f09110112140109050f09030a021c091205061008031303121b08030105090604090f0f02060c01060f1802070503040b03 76
    0x40c00030316000f2130000c1c401000600504001315600d071a540c0e924800362008242402c3c1000000c2019480e440d1001c41c21940280c94519401e02c030362103074000940e0101ca4600010003240002030001589a0403506d4200c0485564406205007082c200c0e0384411a40552805400321041d81300603c7e2541c4500f0405803d00100c07480000c501e03100e40c1b20300b0031101c4240c00c40300c29559a442400f0301c135241010020741c800c0c00762004503d4000c01c803000035151080280c0c5044590581c0c088408054005c6032400054105100c0911500d609400c0c203a41e04e98040e90070302a2403c3c000300c0401c00100210440305010070a403801b07060306284d95210000002d1550300301d400c101003911030082c00412055400c1c94540a850785030b4680d41044200f00394044080c0030715214a10b0800da660010b51010803108205402909502c40c14400340045040e500c04c810000707030b582d440c0440100d070324444031600341c0a49141d000c096048040b1511100100c0c070a1003030182051740144001c02c0040340b00001140e00161 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 250317356 1250 250316106 250316113
    0x140117070201110703020f1624030f0908030a0605010e210c1914220905010e10061e06091701060b12070e090c04171c09030201020d09050604060f02 65
    0x9a0080f03c85640c0c004680c1100160001241c64803400340070070000b0120034040a0402e040f45c5400606540340645849400090a200d001880c105000350302c046c400e1510000144500c000a240c440c980e548111441405149481d002162a500c00d00184201302c1c0302400c0d000a108400040000a000c3d2000344051032260200708405a120a050003088170240303040342e0f44045c02c00007640c0d00e200d0500703c0b060140030323031040d5001030b280700b80c070a030303104103503980001841da00e41d410640c1c0980751140d013502442c4907140c803107884240c1990000e02110130740c0c0c00440306100001d03413078000d01155100c3e6100248141806001020310800792800685142000162596a5010352415078000030f440107032103240340702081300280e0440c030201c00c02d080468041003545000c150000700d50041c0d00401402c440e010f480000c0d005d00c00c0194103030301c0302480030150070280101e20040c0a00e19a000803401802400750280c451401404803034141d43d001000241402c0c1414406c441a40407001135004510 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 250318606 1250 250317356 250317371
    0x9010605011b020a15020a151b030e16081b0910030212070905280b010f0305060d05030d0504140703030f0f09180e0d110a08030a0905060114030601140117070201 71
    0x144011704607400c01d225009442d4508131418218040c0c455081502006410300b82c411300c0f104a00900510040b0041c00c0000794503a000200b1841c140151902c1c8002c0010658041180c010009002c00c642003051619a4412201c1003400303240881543d00c0d54039903940780014001460070340c2115040890081c22240c49036a20708829040d5001940c6003850b07051100c40000c42c0c2201941510b9450644100c1441103041c0000020301d140402c510100815079140c3c08103c407a40c03080c40d084021030b0460222601d400c0041090002032a0941d022100c4805900000c07501c40c50104000d01125010340303601115200010068402c4d0b0440800f00c0b0030050036403000304d88203003642ca4a950305a0804c10019102980528803441e21103904e0000e000d10a240401a4640000080d00818a41c0c000a081c1e20b0380c40d60b0364280084c29100070000c10a029000000c206107007120701c0040745000840880c0d0340d50341c0c0d0b5412004e040c0701c00140c0e50b00140e090b11a5001e4480d5640110303800c14071900c00000e520 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 250319856 1250 250318606 250318619
    0x3030b030a0b0105030c010c0b1906090903090e010608010b04090513020928051504020702040609230c13030b060120030403050111130323010603140609010605011b020a 74
    0x11900c0440b03105000030014131032030030f00f04035040100134203003001503186940b034442803c11940202840c09001e80c8220990200070b6540141004014820050002d050715180c040c0c116451801010501d000f00000010791510902116040750500140b8503c1c1030305160550001d800c000b000c9803e48151544d041c5c0040e125614110320070403840d0904140c410303840f0001c42544400718541d0341c3c0c3c20f0504c420700c00c1c0d03c903444503542c0150108840050f039810300c5101040c064a40303940700e100c540b03103014180b4001c030351420f201c42c2e111710038030703510716003550390001c0090742d40c01003502d40d41280c01d2546c4284001110792400b582c20242c1414203180204049410400c982c4500d0b010100325000030804004000c0f0902030590000c1e007081d80b00e424404442c0455200349018800902055007141080d00419400c0a2208146442000920039103450341803000c08003400b100301c50098443e2600041030298103210310810303204141c1d0f40010b0315015100e40800c9100810b016640031010741e4001651 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 250321106 1250 250319856 250319863
    0x5151018021309020d0507140901110703050304081509011404060c05090a06030219050c0c090408120708060f030d080c1308030721170403050f041e0306060501020705091303030b03 79
    0x70300c01c110003d40c1d60186040300c84182c030805000300040c012505080301d030700c646100a2702c811000030300c0e181d600300701c110801a1030b100c81544094080d010029011480322070100b80801058007075040042d0700d440b4280058225090701003d2422050303100c01050000c1c829030800b651035620351421504007040c0100141301003546500c14400f085d4000340384030141c3da140f8139821b40c803151410154200480720b031810351170704000000345102d0740394000024208503201042c0d07038441030064a00c4215260400015101302c20650700c040c403a22105401d408030b032400051143c1041655a607200160300c0b103043c0002603401c205181d1701c4020f410080450382c8981080a01440350158801042ca40030202e20201d0300c0c80c40d411004201b14030646801424140d55402541155141c0b80c06955210040d040642902554001d50940001c220710440d0803500c1402071029280160001c110056480d801681c3d101400e1007480d0b04258400b001480711000000b00f000c9090080c1404540d46040c072000a00303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 250322356 1250 250321106 250321109
    0x1b0d0f021204150b06040306020c0f0f070315020c0c09450303090d14070c0e070206010b1911010908040f030c090b09040b130209090a051510180213 65
    0x20403407031032010407082c092103040e0542c08a5000e80100f2006185001081e0b0394400c5000c058855600002d90380c0072488208200c4040c1101c42c42900e046100c21100180c450005200c1940c01c4200c0220001601e070080c4200c17520b0886d40e000070700c0c0e815000c400b03000c1030307a01c020200035018281c4400510b05101b007200c1c4209607034800482c1d0075002d207250b40c500b50018240c0103041d02c41c0e00038000c2050350400050580401d00303d60400c00310410280d00da600c41481010340040240c0494440029100103200106003d98842c0d000c0e00c019a8881d082c926050181c400b6041d039042a950407185054000c140303900f517001e03491002054811071910382007400e500580c881d9400e01a032020400034031103c0000303032019221100c03044c044080b080780010a840350285c0040c00c41060240803882000d5010341a41440d540a495040f031450030600c0c95071500c50001c01615140500c5200c0b100304c140014076030b4414144400b1444842e030400303030b020001d02d040c138903a43c9005600b049a007030340081240b00c020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 250323606 1250 250322356 250322377
    0xe25090e0117120403030516110d0609030206090c09010b090103140709030c09110414060c0615040c0c0c030f080c011b0e01021605060a02030d0f09060e061b0d0f02 72
    0x1840b0701ca000c8280c1e01d001e4000a14a02c80d0b08140001d00c000780c0e00000322020801c02449900303180c141410041050f0703840501442e84402a02c00490400c211904210446030098095a505a03100c480c000e8a998407154601d600c00700300001400320003582d6005e406540d40c1032400052004a03424926103086007990034002290003c03900300200115407044001402c0c0c03130700c41800305605038018445140500c0c01b4188401c4104c82c2d2101e400e0315900c040d100341100ca20300303e0702e890400c040c4076417110344c00403512400303039040581501b4054010a80395544075441b00c00300c01203d25644403488900700c1c0840480c0c12020801208520341c1c424042c07008240d1155603144800c0100c04030151a00c446442110b0643d0071808030b40402c604c1140004e000c940054640c0d60740d503054004100e04510860003907400345494004401c0d00c032901d030340c40409042d10a0340204004901c01004580d80c0700c084407402050600c0b50180a12a02c1850250400f20300b110408034005603034402610036a0003241c41c41 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 250324856 1250 250323606 250323629
    0x3150702030c070e1f0312030b0112150e090c0d1514090625051801030b0312031605030118091a04031205010f060221040914100e25090e01 61
    0x104210340180d00300c3c85d0f801e903076284201c0720034a513039601d410303203182c55180d44149035803200b4816007640180034817004004c1142d002c00c1032a5114208002d041c00600443c00f500803030a0018454420004201354510401004008140c055036203404a0440c2e51003645012510303601c0580050a40c480e4050150380c10001400b62880c2c40c41e0703000200c0828208909408112284100340107030424200d440c0130b1003200281d403e0404002c0180c000d401c500414682600c1344101d605c40d2106504065400f40540b01c2c0e00c090303220016903044605000030b000e48030850722a03603804003090505903c03d4291910a4014940001c828801300384450360850301a0041508081040301064403807040b1070141660303040115200341020002590b41a081d8150018003010307020515040c80c0020948000f000114401d0203181070000c500025003800f03071004514058407003008141c3c0c82e10350101c00d1203139136140c014122210054030740d1401001d08408500038008500c0c0003080c04543c1000e4a8042c00c0079201c83c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 250326106 1250 250324856 250324861
    0x504050d030b09010f050d03110f030406030f050c09090a090203032106010c0b1f0503060901020910020a030503040204050604020d05251106010e0702100204080a0b070305040203150702030c070e 85
    0x140aa42000710342c144074410020050040e00300742c012060654006580c0f401d0b03050102e14003034804010190f90035020303200306e007801815904000f004000b0313120166000e003c0c1603040c40080d4203558003612900304d1000300b031000e000380341000c2541683c05803045c1004149190103070007290442d8051100c01e080311242000c09040b8000604109420144c20700c0e0203046c54503a0740b1504941180500710076a01c05105840c0b801203090411000d0192000070300342c96542c100f0448440c000c0d40303c02c0b401c0380203401d419400700c841e070300100c0c040c050650507440c0c0781e103180e903a07074204002420000c094651199080c40151400440345c400e1b24400d020350064654030103201014100440128001802006010004004001c80c040b030060304460000000e96003940300e01009074103009e0744100440b8282d10124000510040018140940c40d01131580c170311182d02c4060080341034034000c0b200a90140d100381c0500c2c0f480f0408040c4540d1201981c03054074101508400c40905040003a4400000c1c6841d4074107 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 250327356 1250 250326106 250326133
    0x706021606061d040201030e070503120301080d050a020a030e15180306091207060e070302060c071505091804020316090902030c0f0108070c02032103090708010e0a060b060c01050405 80
    0x1500c406030500180c100c00303042000f1250340042c038000f40001e0415072681e0071500f034110104040b6016000090517503c01143e10f4240c030400350000d00c2100340d144106415410380501a0045a40c00c0f000d640c040c1c0b400c90b91585041d5030103010210700da9042200c00341103412240c004d00c0508a0034100c042480b20880483d02014640038020300740340d40c10b03000501c0070100168104115280310344d0083e0701181c8403000c00c4129040131410351000e9040000014141c1da04140400c0f40c105603100c0c511a92911840000112071074060032644d2508200d026249041601200e41650f0b8007034401001c0740c4088908a10a04c9403140a520884900d91925415000c44c54240281050088203a942a2410f11038400003011800040c2483c4180510349080c5030540d1014050307415024415074545144100c0200801150381c002c8403c107065025a0740c010543c1c102c180192050742c5011401003c1c4460340ea104c09008010440c0c100d81e10020810444990680030300a2a20542c0580090040003400c01c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 250328606 1250 250327356 250327361
    0xc0604050108010b03061908010504121b020f0a03020301020a05071a0708010e0a06080d02070614090a0302090406110a050903010c02070513110c0f070501141201171005040c060e09090d030509030706021606 90
    0xc4211051054260100786c440c0c01c1c00100c1122150101c48513031180c000400432640301c0c5204d800282d0194000034800707090369004401015590700c60260504140901d01d8204201c0c1420340d00c81c400501d0309001000b07082040d980f01904815080c500144032541c60102c00d1601c2c9001500e880981c1081408100140d046501500d02c1d40280c2440752400031500000741c030700c803642e000c02803059110b100810b0500903a036000d0641c1c80c810010302e030741d5034600c2078018056401c2404042d10942c200040c41e0fa03660300c0402d070502115405060300240400045000c00500741134440c41c3c03800002032040a030202c40c20401c03402c401d01794070050003001c1d041000040c011000d10308480c42d41c039020029980c0701410f01c0291411101e004821400c1c109a8141160030920500200d040b050b042c502440140402000700e074040b606540c90742a0b604c640d02c000d008054500300c403502d41640082503c0b8584a02941203075034881c0400d01900e10304403c80c0d84c2d98040f6000304100003a41092101700706c00300240c61 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 250329856 1250 250328606 250328633
    0xd02010f023c010e0a0204091a04030309060b061602010813051005070e0a03170a0c080d0b040f150509060303040302090411040b06090607260a020105090c0604050108010b03061908010504 82
    0x3000b844240c4a410482d5514041c0c4540240500e96800f000014010b02c00040949e144603118950650f00700b07414020080d022180307059850525104400d0f80c00e2521004031340c5000701c604050403841005400640d04404002c20341200350600f0656000010300038484170074002031240d0001807500700181c001f412001d401c0c40359402207011007001d0000c210340c5404050b440f00e01d80329003544c40c151444115110050700c50000d00304240412010354003502900300314941441038404000c1000344000c140c05950900c0c0c02c08100f02c0171a0414810b60070400e041c0c1d9030000015041768509582c2e9404544064012101590402c80b102c44508041c07800c0d0003081a4200c1c112280b90034028804001802c510640c60700410320390050154440351214081c10151001c034000f0515100c0c40b9010001e0301070038080725156400d02650426018501d1314000b07a80a561041c3e540c00b0607030b8204002c03030707403141d00240106501440e91030040a4011490501c000a402840700100e242e041c1072800844c03900c10b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 250331106 1250 250329856 250329973
    0x1d010603150b0319061e0915110405060702040f02070803090604030801050a26101b0e0901030b01050105030c0d0207060912080f0c0706060506030a091509020d02010f02 74
    0x2c4040f520341421201c0740076a0313a50400d10000b4007131101000d026003e024070200485083c182420728040c000030382c00da82a42050084203000d124150082d401240c0b01d10300883d680840c00348100d001600b0315a202040180410000624140b926142c14102e508115480c1180e58004001c000c02c0641c0591090b00610040c0c450420b12800d040121240c241031404508040118100ea84091442000005c1d00740c6901c01c001c1200f841444140c12204402500c0c110102d001700401c0c080350b00f0f003000454102c0b604401ca1803410703424200111050303030000d400d2030109801130005101c8440113100030500144510783c00280494646026110b0009001ca80000e008224040286c0304c1d01c0715403001c1d40007a0166020350f4880d40c2d49010070082905410640d001a004000c01c44000d016901410405000d01d1407420203040311401d20050b07500003000250412800ea90200065000e007002030607035501401542c080d22214180d1100801171091111001d01c84005003408400210300c903c243c0100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 250332356 1250 250331106 250331113
    0x20c03040e04080415020111030402060d140c04081501051005070f1b09050610090e100b0f09150a020a03080414063606040b06180708010501170115031d010603150b03 73
    0x70301c0368850144e001c00ae001278003644d000540b10000b120039500c00b2411039140c10302c1100c079040c60520320595070014015203919100f11000e2a0902d001450800e040311b40003441411044113000044075241c019002c200c0c5e4090b08007000c00005880341d80304d0403000e4080b42020850b0b500c1c0c40703401030a0b40c10182055000f4404928a200d445078032038a01c0040d90032000b40c4041c2074881661441a60020f80e021210340e410100d62002610f00c51700082102e42802c030307090500e05140d440f01c4c090a21034140c039900960300c140d03210340000f8003407886036074000c0c040c0800c00d070b068009245850410b80200c81c1d002c00c0300c040f061a5180c512010020244240e0100b00d003040c1c03903418003002a41d0716000740024008081040028096a451185000340030031811807681003070030000c10240401d20203001d40c0c0d01080800c1c072800049000343c03034407a040b10350000807140034025070242a001000c1d01d403102c46609060400305203a030a024087c4900551146010000c245c00710716000c400c03a0488c102c9a0300c01d41 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 250333606 1250 250332356 250332371
    0x10e0706020a03170f13020a1d06091501120507090b0c0a050d09081e03090a030c08060a05071218080c0d11011503021504030218090d0806060d020c03040e040804150201 74
    0x644955001d5000c0070321613110006e41000d00000b03019041e154407150081090312860750012001083ca14060388040d40c03082c10548409501803c001c4030f903086140001c030402c141015200c042d400680e04880c590602810f055298141c0c1742c01c44d407141c441c14880380e0003500356008001c4200b20b0694000e8640c581000701a081c40c407056240c521388100c007d00c0000d00da5504d81e14200074403c468000d1001418080107666034138020702c003241c1d1445800c8040c014100011501111405154840d140c9a0f442c2041c1d6100b074404000280683c940010444107004060000905402c0c02030040003510001044c4071154070b2801402007180d03810100d10742c0d0510000b41d09015a54070000150385c0e04440c0700c80b20707841342001170059008aa002130f51081c96040851016035a400420f8015603011094810040c1a0b09083e03850ba00c080d10542d400a000b0042404480c0c140d6010b09001c030b1076003041d28501661503a64060105007511306035401100081c081110300022a0580d0407041c00e400240004c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 250334856 1250 250333606 250333621
    0x2b05010506160809040204080c092401030504030c0b0a0506100e0f0609010c0c09060e090604030c17070b0a0204090e0721020f06070302010b01030b010e06040b0705010e0706020a0317 80
    0x18000c529065038442c215410a504001440054840006000e0411500c40e5a28174100703a0324601041c10398000c0b07035000d020840c15100c0554400c0418047c000140c01c600c0c0810045000381002403003541000018564040001c1c400e203207460003051004c0021504c0c1c10900e042211358080d0300d2a010a101200000c1c07401a00c0320095120303c58400c446040d241d080101c0141c6000c041910b00402d1230314510f902180742003403640b014064600c159a2101740c1c1d5200700280356142800c0c2c5019010403000560100028003000c012612194040f00752410540555281e880c02c0c44151924400d003034000c90f06018990369441003a101c2c103040801400120b240c5500c187d080c034244043d440002445604960640d220009550800400509581d0345e030b40483c180240280500c481c50380c0000e0401c0e400f0030b41c42d03203e803043c89011035009100519080c40c00715126125440703600c04a603255201e1580d945284400e010319001000c0030b8008d0040200c06140084c5a00f44800c0900c00080c024800d00260 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 250336106 1250 250334856 250334869
    0x60b040c0c0b010315021b100b060c2d0d080108060f040308010b0a0c0209071815020d0302070c030219080601151b03020f0102030112020a050306060312130b2b050105 73
    0x110fa0f0070130981000da6101d070740d071703030001c0d1080d651124500302d400c03a0b203036034a004001040b0301d8036240040104410300c121001c01c8113502c5007400d1402c07681d012004c00f0700081c1850910b20040e41c4e0700140341491762440d04806044c08540206600880c50600c0100080341007030000c0d9038024000c0d0600b0017545020781d00541120b2040c055102c2d0301001060580c099402030220354000c82d0001c0c980009460b28040080605010010002c281030304013400041d100980b5040b03001d0380c0c1c0160040e042c00307418120118000e410402d4103448002c0145000800b50f101c41d8076a925240508540c0b0000c0f07410728620503d00001a4085803800d00311003801c440c0d956201d07021001483c090050b044640c8500d0074102d141c04240780842e100d95100000029140803034540a03001e481c405da40442039151340d0420580c450700c04980c45601a00007100981d40021200c0040c03c400405121010a0503220a4401155000204083c4003442d1020460070042400340c4403141321400711038144519811705001c04c12 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 250337356 1250 250336106 250336109
    0x20f24070c090b0315072d02010c1e050a030b04060e06180105031b0105190e010e0607020a03063c0506030a26090d060902040c0f1710080604060b040c0c0b01 69
    0x251003881c002c20780e803a205000000034200144403021025028210341d4905030381842e44100598a0002c89560a5005681c0c662994000001e2280c00f8103a501041c0c82c164080402cdc041055074500d0398581585d07a82c42800d000d058503800292442c0781050038400d0303180c10b4105051441c070160740100041e580000e610041c040c5450040710f080b541d010f0040e17801d07002e036080d5207049038040d03002040d10940c0115021911071090340e0b103c604a210006006042c812520084d4000c507030384900b072021070000c0c1c01c480180340050300107810404038101000080040c00d0203d40a006951610b41c0303c00240e03000c1e45402c41c000310050805203483e42e0f1201c0224451050b894400b114208050301d1441d411002e448409601408282041c0b4107460300d000100f82203c0c0480c800d614101c60240d02034420580002c0703070007a5454405481d41e01556250785500f0040c41c0a0540c1420304021890406c14050207010b5840740402003681c100610811040d1001c40700c242c020091030200c4e042c04148101038050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 250338606 1250 250337356 250337383
    0xf09100c0b0c09041814070b0f030105040908040f03050a030905090906040204050c0405190504060608060603010306091b1e2408090703080c0a12020118020f24070c090b03 75
    0x42e41d56882c00f001c90050b050952a54000340c070200030342c405015650440321404c14410041e1540103840e101c003143c150103002c0c5e102000110900040c070823420140e2114100902601c08181002e556030103c460110a0340c204a8046d0005000318040580122110010707040484000c02c80b864840e14039a51014001c1c4080c1c4101d84031804109400c44640849025140c05441501d403040788842401604020703105103401341e8548040021243c0c0f20354002402040010728680c65646191200000b0745501041911480041d1590f8040d00721081e48e18070003803003101d80404116030b164074600b100102580c03100030f4085400640d001441040801c5d602100c50741d060944075502c40180244c944169500020300000000411201402001901002036407050301400c0750440b40c14012800c2c0d840f81001048051001c03d0000018900586140d9941101420100c880c004048240c8180c110b68042d40325003000010b11b01c400c1c031013240600700191032824018000c0c501c3c0000440d41d500550817503030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 250339856 1250 250338606 250338631
    0x207030210050a1109040222090b1905010f050705011518150f06030e0f0105070206220203030409020a05090907050c0c01080c160206070b040b0f0106080906040b0712020f09100c0b 79
    0x71444240550208040c81901c0300341108e40c0c503207442c411402414003250141c422103684840060348100c902640d03050720810f030f4071000301640d081000e88181c3c118805c101c8195403514000140d00c0303480345203200282054900f800c0c00500c0701c401607040329524541100c000e00c00183c1804011503804940d82150341a103400654200b0130800c2a081c032450051203140755003000184040300d44c6c0054070a02841040c1c02d2000c04c84c01601000d2025603004c00700030f405800030b200400c00d804165025002c120110f040881ca0071000c0800140f01c5201210280c000c1080801d6422400d0b10801a110303120341d0030300b800e607410b00700403150080303501545506280181811285d1011900d400054411640c0d00411203010340c102032030b103804100300850b1120f030707900802030001484a203d1001240a40f91920107000356846540300c5a2502d207000b8064818003003641401020440c0310b10051451000c40580d55031541c0c1d6a000b000f01003860301900000308031550704290085500040a2900071400c0240e4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 250341106 1250 250339856 250339867
    0x40209010e0417090105070b0a0207021203031014060c0607020a1202011104030f050a08040b0304110d11010e01020c030a060f0e070503071215020f0d24120203030d0207030210050a11090402 83
    0x407502ca101e0b0447c002c6c030025054040c4088292285c0180003020b20880d5079012154840012607a20f02044076a60032a428046081080e2101002d034040c41c860040e1580f417a150700c0c644028a40702c01521f4101c010380c4264642d00034040c601100080340380b041c0c4003d0082c1d0004103405207090085000c090800f0340502615010401c040042800f0541d10034500350b00c5950b0ba0710440e4090304201e8007525280050241440c15250440e8046c010951044840c04101c0f00c8400454260030442c0140f03040d8401d143d004003c5980410601c60a075102d25030126060008800c4803040c0c43d4108882402548003170000e10480e50082150010340b0702054a00c10809242d05001031041104407074202218070014160100030162001030841210798982030100d082010111b000e40320340c4154045524101040c24007200e0300210740e01030050f0005040b0703420314982c2000b020072a4000c00045000d40e1103151107032090385190003150380c804101e42c7c04002c901002903000038544101107100c0e00ca146c0c0040c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 250342356 1250 250341106 250341109
    0xb061318020108100e01121203111c1d010c170402030618120f0406083603040b162a031e0c0602030a0e1f030504020d08030f040209010e041709 63
    0x44c03d0001c0c03d110754081540d50f0349081041c40090380b00070555501264400300341615001c0e005007245188002142e03481c100030741d01601c601d0000070b160649000c0d05c88142c00d0419122044900700341502c040000f039a0040403002030611203452140f44070304075480d401c002c05a5000300e502070b4400403516000ca180080e410980d800c0019003110503180207008102111100c408002401c181c807003944410105032100944403003c051080701280820070070610243c148c1581440c10300200400700708582c01c041d103600240101d0307005656103c40b48550154980c2c04c2c450700b880400b000d000c2c0d2500d4070b0058042880c500300b6641300c5000c0a0550660085149034a02e120007607540c00d1900b0590072100142c44280007512070b0b0100240700006050480501100d02d4241551080f180b1280450883ca10302c1d03017026405480010030a1f0390101c03072180c24401003490200110712807000e800008180d850720b441001580181a009800c50030451810400000c080c151503000017402054450b413281c26800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 250343606 1250 250342356 250342381
    0x3070908070e0a0f051902090f0d061413030e012604050115080d210908030a0501062607110c0402040b04140d12031a04090b061318020108 61
    0x344900c03018070a03140001210040844214080c260009042c0001c01044001c5000d17030314240c542070055821040d0407002d0a21b154004d1083c0350028001320700c46161100083c1c1e01480d998810344800e0346848160340b0420250340b1076607001000421a01d101d03046501c00404401d415030586041c028000c1c8420608500c6090f8840c0e6500c192000ba5138038a00391804c1406031000030302c03010705040000400f0a41c0040403640303804548180d170b5241c9545004000c19110401020a007203240c0f6550a480004904000c00951080c0761354100131900b5407400c20300519641d9525052005038180100c64443c0c1c01e60316031200c0d04540302d450141c1c00c080d181c40c070039800c000740449210b501a10006000881450420141084481e46207a078091200d5101c18091a80c034000d4009121282c0500c2c10101940660700162400507081c1110082c030a01202040407101e601005a60703420b0140d0820040e0701d0f008250042101324240c090026001c0c0207002d070103205204500074144900130001a0a040110 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 250344856 1250 250343606 250343609
    0x203071211040509070c0b0f011202011d1c0c06050306090a0506010306080d090f0503030a08010b031009020a050d0f0608030a0c0201140703081602060f13020111010c0302090f190506030709 83
    0x920031442405c00c20741c06450b00320454002c81e4070000717440c001500385101003d424100e40480c10788100c07096281e4011540c1140342220b09030840010b601d01d1130181c4070300c0d03d909803003c035600010400031f0440c01c0c440b0140e192035106c8010080c00f0010840a52200c43c0ca503a00300c02039070707000f0400d5151030005801030411a0019080c80c41500e030300e00d901c80e0b84011083c08591546d181c1100091701c40050644a1248408410104000c0c800401000d6182001180e11400890301d00c1c1800d42c407440803a007640d01806c0f81600081021580300740c030b58001e20802900ca04842000c000880ca4100e0842c4c80e401503280c00000d001c070081d840410341e402020200e54520b0b414082c3c940d18116450050414003080d62241d2001c012407400318055800000c2a034002c600007450201155200425003a0b10030000c07204904019140180e0301d0b03001c5090185e07682c0c000782510013684800c00e06050060b482c148610140c442d0004021020b109070040804c18251030080e82c105a6a80e91454150b9094445 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 250346106 1250 250344856 250344859
    0x30f0705010b0d030e13091e0302160806040b060105210a1113060f050c100504080d051608100506030c090103060b0301030602030412052a0708070b0301090b030102030712110405 78
    0x40b401d810401d0b60240d01c07a03101d010300306c0700c41c04074149002203102104d040103c001c15820016440d03c0007214444011620a48642304941450458401502d10440540d101c0f00b441c0c0c2c0f02006000c1007280071802250300c48002c0c0380150404a809040c0d441c01e602c4584032070700100418022441145140e0001201c1c4000c450226940d00c0d0440180100d12400340701d6031000405035003000a055100ea0100d44c850051540201184071800d40807800030301d40603004851000d010010b1000340c4125008052140940e0540510005079810012380a000000d045041c2c240303803000d06008560740d08065070b8000022180480d1a10030b0200180c0082282d80c120b040b881e04084000000c111054004500c00e91140444404a0b84400000d03100350007401c2054140c1c1e20031203000001c2034150b11003a0925151a000c440c11b150b6154161418142182c00001c42c14200100602445031140140c1c410034506a000714518a00204014172380c11810000048444e1036076040b42d5029221425200a07140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 250347356 1250 250346106 250346119
    0x203060708071e12051005012003041a090906060a020a03081801060f06031505060906030a0f0614030f0d0e10020106032f04050c0417010207050f070e0c04050102030f0705010b 77
    0x100094031025011050500140c1404002081c11b940e60254004441040c0c43d42108071030405114008a24005e00001162000b480002401d1b0220207030743d0041c0003a040e91b030342c1d280800024007211120061885003c0c403400c000c0540190350010b00c45140940516042e22039841d52204043c0c0c210a5000d5200c8035800c2510200f061488961140c00311109a1000c01c81204c00721100069030f400751090a074440b009101c8001c01e820080000e40c3d000503035840002d10300c40e81c140030300105d40881d00115804840c424184407241400c01031022011030b40c2008040650b40030000910324640191501d020f00312662a110b5524000d41040b409550b210b0700703203d01500d00880c103070852590084140c1c0342d060300540f00c01c114209031040e02c0c02140c035460134071b1500d070520341c101c8500c0100c50081c031003a640c00c2213090049101030041039491401c1501a05a880c940700100304980030217007650407051400c00041100e80c0e0000201c0d035904242800c4251605054107215004007100641c8030381200c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 250348606 1250 250347356 250347407
    0x90409060902130c02070611070302150702040906060801060509240307090f021305190312051626030f0f06062107030608070f030204020c011e14070c020306070807 72
    0x480e0f03a00003220501c0e41d40d00701e4054680d141780880b0141c802c03e401140c03603000050107101600b08641c0d441c4c0b00c1c00030700b542e940c506500c56001c142110b40c0d200c030540d03c036680c0301400d000400080c01000c3c010442104e1642190805c80d03c01500840403071503900c030141b0304480d44225070300c09018000c018050080d040214000401d100d002070761191114000c03a082034100418186003035140500a03c5e2070952100049044d80c0d01c1044081604106c0f40903c1418002c1180b0b18000300440e000c00c43c0b082c40b4580a0b1158890f80c0d025003800c5150180c403602061041110b00c015003d91542d01c0b490f0102c1307100c01e50f00c609c00800c1d2540324513003207010080f02014407002460040700c0664043c0d2050343d01085250364950b007054540714a4050f61101003402c3c1c1c0204054a000d402400c01300103450000034440c07a2031700e000c61000308061590f9201c03a4032180c3c850003400e0321001440c1d00049034104014030800c207500003600c401c0c0040550041c44030510114102510840301811000413070342c01004a82d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 250349856 1250 250348606 250348639
    0x6010c080c0601050a050a12030f090b040b0c10090503070809040f0e1c02210708090a030c06030e010207170d060509092d030a110a050109060f0f060b090409060902 72
    0x4102c240640b40c040d04c290900001d550a02c0812901201c1400021082c81c80080d030742160b841000942180800ca10707400c010480d007040c04010002050b10500351651001103049031070501400d0702e850400a4540240c41c40811004421a0851a8030a604a580f00700810018004041e108000c500ba01d1030708215003030400c4002203404800410001c0e9850700d82c00908201c0e6904c00382c1c0b8080c403c4a101130b03003040300e00d6007070009490064410070505003020380000c00704110003401d80c001e590340c0e0b2400d41c04001c06501403080c03120440450b0004c1d403400790651220a11000d003000d81440d00300c0c0000303e494918001d80d00100140400030721010060800c20340c0e440e9a098011040d0587c00e42c401c0b0642c002e0180e80b441c0c10b02009050004d1414699600010b8520030514a11642e103030049150b50000150203104112140b07100310360024240c1211200f0000b210b05144421f94560b25200051001b001c90030141c40d16400c0c01c50300800c581c0c404d840c02401070011100025001850104152400d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 250351106 1250 250349856 250349863
    0x210204091401050108090f10111c0203190207080720040e010203010602010c0216060818010606080712020306010c0204020f0d090b04210c022403090f2a0906010c080c 73
    0x103c0f14241d03681082603c4000d42e141d00d1700b040c0f0740b0000c2554031184c04c90142e100290402c054000085c1e04a034148084002a5524000440400c2c5411540041006218500ea00450000410001d401c50a008a42c0d661210354810481f02504040040d106d6030310210000c188040c0d0080f0151051280c01011007a55010390820f0040384007650a1180344d241c124400240305140b20a0511511079a900e0300398140c03485500944107541c03000031802d404043e14000d02800d0014492503a44162031302d0f01c000002c16910b0110703800c2e08601d00420600c00140c0e130200c21403443c160101c4005a8454441401109a10980f00386124003401c03c105030090091f080100c80c8914002c450f400f410480201d41400c54451000c01c080c0406d01c1008280007509020310b03402400c2c0e00807980725a80310a0b00003196103036001140d09000c254080c48100d03a035403d0a0107041403080c1580c0140d982008580d801c04988120758600500450401e00000d50310b078810380070003510039008101d0565441101c1c0d070003505c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 250352356 1250 250351106 250351109
    0x13050409110406050f0f120a0515100510051b010e0a0c140a03150209040b21070f080d05130e1905010605090d06050612060a020703020c10210204091401 67
    0x4a10310f4454006801d0600800800b5052001401060701c07810301020403c003175204da03110004620a0041e4140000d03c200046910451402d1030401185802c00b00c0b130340c080310701e60481c0d4000e00560818118041d0001d003560410070740310410a03070703403d503481d5084d00510290044001c60720428500c4001e115043c08800c044d250b5440035055811b016400b030240f24115448000c1c1020990203d140d010300c410343c05000020002000410490000000200d070340200030b0b4503084055035021041c42d0043c0801621004080c902194201e65152800d125107030507071044080140200019143d082030056a02603000c0d02e841002c90000f4140a2007400c1a2541d003042512490324080001c242203001d00140c0d440e50000a1500020700056a110005003901034102c40c1c20681c803070706500e00444103200c0785128080346240181c6810250070020314180211380010b0085001200ba00d14480d4400501405242d45800040d150081d0051b03510091155900410889240150114200c1602403104e030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 250353606 1250 250352356 250352359
    0x108040b181002090a08070506120c040b0a090e06040c1d010903060e0d11031602060711040509061504061d0c040801060f0302010e04140105040e0a05120d0c0c030807051305040911 79
    0x20082030f00c41140c147d80b03840c1401903a5110b0b0050010860020200c01e102e0382c010503071903c050419549136050100c0341c01c00c108a03030115003410000e100110320782254651040e4200c8060290102c0c502c0060030040e00406a800140c00c0782c1345000380780e4003480d4550011648100e0401c6004204802c540c2c4803049007002c0c10000300300103a001c40301c41c80001690f201d011010304115400000354208041544004d101300c446040003d500c24041e03986d40b1460f0301c2860494013501880c5041c05000102d80e08c541c26551089180080500078001c404101c10306a600e0310540c1e03c11742e160542076103aa030007541d000304299030030b0072000b00e031900320342032200c040700c0c402c0e20b40800354402182000b0945001c0565150390b042c00500421007803600d80c00130b1b68100594810b8030f01b26080c0c0d0301c90900f0f06880c4003000134200400a0000f42d500c19500c20314500e80c00610302000016a0340e071b801401d241019102d00d00704280800c00c141c01042201e50300d0010b040081003000a155540b502d440030a500e107d005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 250354856 1250 250353606 250353619
    0x120907060804031704030908010504050a060605030d0215071701080a1b05060702010c02010909021303020a0b03130b091609090303110c0706120902090405060f01060c020108040b18100209 82
    0x505240220708990241d985612032014084010000141900d0005e0003035081190340364000404031000c0c81647e000d0740c000c0001e0041d808280c101032094809503800a80254071140340300390000e80c041f81c3c0c00030350030394030056060031744542c8001c941c0c2098804030345034802c0c0356800004079507174001703422456148142900300d401d42603942d02220010080c8203094001c48100316580040d0300c81d540042015205060402420b902c40a419089811a07100110714507050303039007072081d4500320100d0b40092030450b00081c130310300d4406803240c52101c6c8888014100c1d80030300b02183d030414040c80601c7c2920090701d005038403260b17600d14170030103440030410550210307260243c00745074640c00a0440b40c200900f04001e00c499494480212080e55014000c500442d5030b580c0c0c07480050381c91110079800b50f070090700101940d080480c14840da500c01030344400d05200448280d000140d812002d503070350068200344004103582d581c801d29240b040c0c000c90341600034010b1841200d02500c1c954042c1c008082c01340e515 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 250356106 1250 250354856 250354859
    0xf090518030a0207141e12071a0d0f0e0304050607170a17060108070f110c03010906020a0f08040c150c1502180906090109020f0f1305090a14010905070c0206120907 72
    0x5200c0341141841c910b4511094224500d20241412205149100b04c80422952070725a503d81c9c8041c0309680c01a1324410300c0001403070703600a904034043c054060f80080d404010304024203100380d0b6644071320321440380105808980b4509002c441145c1c0825a1016800e07150742d40520040140403501e800d2003444a0b44100c07011681c154420440c4074402c4845407240030000e440640b05545070014090b40780007a2007100c201d40301a46080c0a002d907800c4c4280310158032040c1c5000050414201030210b14204800c2c0d40c100004140842d4180c0c040b0303007024982c104001c29003074088460100a010141070000c01014a94040c0e05c96030040100420740c2d0316802d440e0001d130040014030032003550340d10b5100c1407140043c4460505a4002c050340c028a400c80307840c01000c5100284150002c0040709405072512804001c10b0501010031035119018840c01c105050803031143c200b02460600802140ea80e030b88000a801c1800b400c00000782c250020021501e038502450b0300092520200c9951a46000d440f40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 250357356 1250 250356106 250356109
    0xc03050103030912020d14160f06020f061302130209030307030903021507020d02060c0a1b1a0423031002040e100b07020a120c0b0d0b0a0605040f090518030a020714 72
    0x21060303683e950050400500044548800e02c7d41d02c064214040d6900030080c003003a070305810618040003000740080300b4804900e403210103800e01c803410300001c01c40d400403c02c02c0000c00c0c40100c400c64503681210322a20098480550340c0003402380d43d00c21a01840001078800a168100c1801401c4030b00c21918002031900c10041c8141b00d005201d0000d401200d40344a0800502d800c4021385102486441102c1c02c081140c0c43d881807405103912241401070f1804401d01808100403044c135941c074100c0c2ca042e481d05141400b5100c6d001225941c100f0041c4500c24050895582031100360280525107030150348036601ca000c14800c8280c291055001d071155500300003101e14000e0191748070780d03400606201c50b06282c400f00700655100c1a03000c80d64164038140c00b190351911074025000440803031000290640d8404148140313140182c102c1001e00000340700c1005521980010242607c8001c40e0100700c5440d4502c2440d0100c2450b600200c01d80804111501c480d5400074110003120300140418440104020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 250358606 1250 250357356 250357379
    0x15050a0f0c021e0c040501060f090503061015171e010e060a0302060d0209040f090b0916060e01050d020c060601140301030b0402010804110307151808030a0809100c030501030309 78
    0x706810096045254040402c500361240703070f20f550f400c030000d0f10b01001e0f40100050803194260000b2010a107180c1c1b440344420f42c4000c403c4041e01e07091b070052865040c54041d82a0030030441c407610400ca007070030070303803140740c82c031489030540c51059440030350400c2e0074103418110301060052100c5000308d42000c0000f4920400c039403c64000c01c80078195049240c01d5800b0b12003664000958403210940800c0040595100e5100e820808618058005081d84842c94003040e4214007030084951503014001001a94000440c0d25040b21141d043c080c640300f41d0440145c40c41c0c0a02c1d0520400b280c8013050000c8851000b1415a1146000344da8044034580102c214605602080c0405411222030900007001035016110245c0c0241c081c41c100349140d1817100c0020b14060342c6811880c40b0b85180c0340c0d00490142c01441f0f500c003628030214030040f0203041035455645da0103045900300c1000465004070b08444400d102c864001c1410800604c591000c4200241c0546800c1c0700480028400c008006002503000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 250359712 1106 250358606 250358621
    0x1c050d08011701020c15060102070e01030b010e07080103031b08121003060f020f03040f020a0503030f0301060e0409210e030d020106090c0905100f0302040315050a0f 73
    0xd2503020000754000300102d00d83e00500882c190120003107400b1001c00c5800200c4401581d030000100c3ca004455448020a0b1480700004001d104402803101e050f00c0403031240e1105038403503030303011902e40d0700034480070780000d0070044440017021850311004c24080c014514a82011010311324079000d400c00b07039009a2010f030040c0c003c01c00c00006024149540e110900110b04224a0113444180ea10000700f0007010070302200d16000442d44c030320420002070709003c0d084a45540c1e820800a10641c828052280810a81104401545030034028161160b5009055212040d0f140b491800e4401c1c2c05009003045c00510030300b074619918100100c0880710101c0c1e001256203407810a0800c201d2311100d0b141400c01c00c0f403001c2440580c0312001180717004005843d20841041880e00210000e0040d500000c2082d110800002040034094120a010701a5800c0030071015000700300100885d507a1 = true := by decide +kernel

theorem cover : BRFrame.Cov 250179856 250359712 := by
  have h0 := BRFrame.cov_init 250179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 250179856 ≤ n) (h2 : n < 250359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
