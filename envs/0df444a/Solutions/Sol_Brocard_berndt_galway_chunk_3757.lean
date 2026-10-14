-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3757
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:35:30.125989+00:00
-- url     : https://prove2.me/submissions/7783cc12-efd8-44ce-a265-c3cb9c65feda

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 675539568 ≤ n < 675719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 675540818 1250 675539568 675539581
    0xf0506040b0609060d180803090d080a05040302070308030907050d0510051e0604090215070b07090902070507050603040c030803252607140d0905010e01050c1213080a08 74
    0xa07100a1080644195801c010042c410707941c6204550b12001000008151100c6807850050401502c03100500003a02c004100101c449010820030a050300075159074000351201072080303007220001c8900030301583c48100e091020400705005154400c0d800307030803202000d40310004106407200091084559502c6084282c1300c01c08540113555208081129041c504031200841d08142034001d404140119039039801071040d502d5050440c1c04000001203559130300c1039149441c1580b800d0403203822002440300d580c00310f20103100f40204ca01c0326811a0003420000c1c202020406958009402200d4010158000000065200016511400288400c0040c0c140700e495000540c01d801c01212040200100540b101c034020031a01d022064103056030701005c0e41d030b0300000f07540745c000c0000c2403018005c011030384034034030980e64000300381c0c1c42e100c0c100920120201d0f44002d806d81c0c40640741d000000070140a442900ca1410701959840541e41495031220903807500d640c2d01a622403214140080c1d80002002070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 675542068 1250 675540818 675540821
    0x80412051b01030c0c0b04050118140c1f052d0a0201060e19330f0914220c1404140c09013902011206050901060e0d060f050604 56
    0xc1c0d2428281407252003104400200507180c1084018031480491011606000c001d6005414014089030700c503412103401c0c103215480c1c8500c40440310305071080400445641c141140d00321aa02e000c80034025414034030700025205600400304100c240810440300c000001e0491801c0b056141c103000c44176680b0103a0310300c0242900c1144c0c02c21400050600240140201408010031441c801ca0b0230001c0c100100e400e01c00c80301c090b880201a50f001e02980c0d40800d41d0444005c45044580035031001e00708607a14000c481c10344180e14015a640c600d4040042d80000101d900601d101d89480c9418071103845a6803445682031440d08102d42c0b0440344002c44886080910442e003514000055020141c0f510728040019031051180840c10400768184001030b00d10300c0c04800d0101c800f50410b6158101240d07001054040611005030f000482a0b814074210007d0b510482c402d540c005810624240e08020043d80d000c0c00c5c10038441e030000d0080100728049031303142c480c2c90341400c242031010540303042140c00c100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 675543318 1250 675542068 675542113
    0x60f1c031806030905101a0a180c0804050c090c1308010204062c19030803010b0d0b012a170d060f06031401031401060b04030807020a0905190908041205 67
    0x1010f26103005262808140c0010341030b14400c400c864080f40c0d000948921850042c92000042e420110300400840c1d009185c60000f00c5030f09004800700280024010700302d42c0060156006401904618100000b03814184902540714201c200c07600d03c0c0140040409280c00305580c45202e6503540858103002240d4407249140615880c0d258411041c001520380c00c104440b00000a882440d04003044c080340150000c4000c01540c2186080703232030350b0350380103072180e11b50185410000c03ca280c40e0202e1175541c0140e00c1c00741003080c0e02e00c5940300f032007032600005502d0480700d4003071382c405181015012016941c000141481c00c1202c20210381c0d84e1400722890300040994000d18180b5082c000c0d641e6030f0301448116141103036001403410507a0185001014010810398115100b5800000340100520442c00d0041c04541d1003580d6910925541d0800c03c5c0803a03100303072040c1030440300741a00381c00500510703000000280c0c042c00026103025030310050054004503041c0100d070035800200000d0680480d200446 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 675544568 1250 675543318 675543329
    0x80c06090102030d05101502010f062111150307020115090c12050c0708030c030f06180106030504021915020106081203070c11041a091608060f1c0318 66
    0x990030320014200107502c9001e560b00803666203a81d040001d600362100c194171401000754a40011454100c4107000340a032030050184100f280c01c0050000380c014104003e1a4505244000902040c0c0307180d803805c0c9081c02d0803c01030f52064008101e506030843c131030001d6001e080d0580001480c4070928901541c940c4481e80714a0749545032480f10031980f60043c46844080c2c102e600300041e150f6501d541d003e0180598180580014000b000b00480e80501d50020343c010008100040b001d9a0384804101105000300401c4060004903070040050500070341207543c1052005008071301c03c00445210015850280c0e1203100c400c0e0296264247c01902031203807a014203c400007410f40d95600c0369800b136661101030324035800c000700f48074030b0341c140aa00c0c02d041012607002441813081d90308410b1000b041c02c1500c410136214294060218802c1c10f20244404001d03c541e0300c0b00301c80c9503516000c100400c18049211a004001e4004001d0024000001d46080c14400d440e00e0700d0880c884602400c800300740340c021 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 675545818 1250 675544568 675544579
    0x90c021f1d0d1106090a0f03120b130209010e04090f030521090c04110a08040602090f090c030f01052b080d0e0d08060109060e0f06070b04030504080c 66
    0x1100c016800009020354000da112804507501100d01800024448222486101d5001d1407200190450344a00c401c41c00701101422a110754441411140d02c4010100c40103040c0c1c800d403030807600042e0140003d900101044540000d184412030003060302c80141c0104980007560001d100c40841d130700807882c11f1050900b075904005861843c0e880880309412044060140030b0007040c13010819900d01a1000d000d240c81024550318103210f00c1850399040340302680340c480d41c18a0f4038600703ca0004800d41c0d112480c142e50310b02468540d42c8815000b0341c015a21550030010680116030507484004481d8044c5040d80d80e500c1c0c1e01d1030200c11109401c0d0341a0130041c030580c014018101a02d100115251035070720304010410740480d0518214030644500e91404a0390303410009008001c80700441c0300410955203403030300b9049030b4640f80115001d04840c01442c4c0451031842e0603290506140103102c070321890141c5054500070b0341d030315040803041c01217800f200081c01c0000d05001c220300c14840e040010106652 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 675547068 1250 675545818 675545833
    0xf0c14010c081e060405040f0c090603051507020309010c140a0302210301060206040b0901061a09010f0f090b0c0703050625020304032307180c08100807290310090c02 73
    0x140c0c502001c0f00074000d10722440e100d4000c2810b2029031140f0220312a402140000950b40c1c0788007020140000b484262001c0c000c4a60029107880d800b5481886000554050b42c5031100d014015529809000c80544030030324442040c00d203450703003000348008190180c0c0080031000d00c41da50700d085074100012510351401c0103200400c403035074000411581090f032006100740981c1d141000640141025030200b0400a018180000340d41103003002080c01460a0341c810744102801c0400351090341009100303100080d41d0050070090200150082c00c05180740350203864410344e882d140c4034035000301070f030f581c078003441441c1d02382d42080b8070032100701117159160f002650a29243d601c1d01106541c0955045040302040108503031918810b20040740502040031214006000c018448e100401c4405019808240200f0205401c02035410303020013180c9048c4000c10446092582c1654591302e00d0b089800c100300c240e5202c180d4811100003444c40380c2803000000d030321540760604c02c4040c1c0d80080c901200f0b5400100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 675548318 1250 675547068 675547111
    0x608070b040f052e081e010510050d091202011b0905060d0e1014070e01080415020703020715020109020906180609180f010e010e030406050a0f0c14010c08 68
    0x22000c004442040341c0148880600c213405007400345a01d40400d00800b090402c0786840303604500d181c1d024110504100400940301b507030b10406103070203001e00c0354440400081d8402c3c09105170014078103070380180400300d903001069682507280c07808200108050b035101d155054020701c1c1240c201150350118a0200031a910382008105244210302c040c800c0e05440d4010f40089030020041804429140201000071340502c1401d02c07001e13a810780c1d0070710005a91161504c000e61040b8001805181c103c03100340c4051480c885010000d50210400301c0942c0a00c07100009c41c004140748102d60700400c1d4001042c400c100e803040151948000304441c0c4640d800400c0141da00078460702e5194000b10a03244c1028549904544070610b01c00e25880d40c00303511071007208207042007041d08036443c083c04240003400701510b844583e036103d0041d4043c20700001d00074820100d0b500d124070a5100140841d0612107001304803030b143c1c0011440d00800383c603a10ba4548580300e001d03540c008e25941d880707041691480c6d910290039 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 675549568 1250 675548318 675548339
    0x9040e0c0108101a0a050c03071101080c21040c1205072c07030b030708030409090507050f130b1c0803150f010c030c020f0a1203020601050306040803010504050423010608070b04 78
    0x9032810148003008524051700d40c0c041c404881084149404a03074440c202031030030204607540c03442c40300d0000b10b000313001c07802006410064400c0c8401414006007000301050b1140040d420091003a03500c032201001c0080e2045103c0424030b11320b40520b018044040c20020301c0340c401d40140c608414105501724404110107149040326800c10154a00031606003010ba000a28103074090304101028000028000342c007d02a501000d5424480c8060750842c903624402c018902d0703459410310350811549045080e001c1a40e0b4420310302103500400302c224000241c403a0700c81c40368450b8001c4801250000500c4001c0c01e03031485e084145181281d00032100701030800000e00e820504000141444112190f600455aaa20700e03008540380107230107141c8095031405008100c0c0890a01a009409107400200342401c000c604170f032241f13401012481c07540c1d203084d0038031009040c024019986466009a2a45140000c000022041c40504008100d40b402c1c44020390030003181c2c0e0300c4245103000c100000c00c41c59904 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 675550818 1250 675549568 675549599
    0x3040e010308071a01081b0603070c0b10030f0809031605011e030e03070305040501080109050708063d0311030910020f131520060103061109040e0c010810 68
    0xb4407030746841e9107250100400c07008009054140c0803c00c0003180e60a4001100081c0b4502460340c410048080710034400c080c40181c0b0b030b420008440708032617008964921103c9800000b50fa82030f0204a549840c1c6112001914400701c0d510f2400066044040c68104500600b0700b81035029444880c3c541400600040610081e44002d03040d000501e8001a001e1fa00c40e0001e900c42400703807640d035170039841e005016600a0050070301080442002060243c02c2c1c0c440c00b4802d031455280c42d0701c1620340c2c03030820281010640c80c6401142e1002450b51b12060480ba03021210030f1202c480590a00300c012029098130310854081900c100140200036030100c000076610300394410f50340e00681d20014080341852030701ca080c03111850502c1169000982c4445100b11100b1100140d46510308042d803403401c0920940f00703a40030b00c0e0030345c0a14018808544181d00007103d000c440d0103180d20301280540490300f80c1e001244400c512b80c02031800040303103580210240b0762005c5503046102449050080c1e0400b20690b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 675552068 1250 675550818 675550823
    0x3140a0c0210030204050d0503220f09092d020f01020a0b041b05150c1204030f0311070f0b04050f030c0d060b0d020402030114040b010e0303070b19020403080406030c0203040e0103 79
    0x200302e00c41c041024043c2d0704450240c107001d031241c1035168490800070796a40c0034000c0b01d003040c800507050781c1d1401071191100003907594030310106075150700d400213442c003615140700140d40391030055001481ca61003162201282c020409651500d00f444d0f4010444000040c154a50654201d002c01100046c8601e020300e0b40150b000c10845402c40c4103c445045d400d100d0341281e600603580840b150100c18090018040d04c03c0f03401c2c00c9402c1c00f2082d07480400c660150f4400240301004c0c0c0041c4100184c042c0d4400700b8913140f588111840903980d00442d10903112168044c69151000240501c01421b2404028120303000580c0103282080404002c103004620020019110558814040c1c3e043c0d40d0741000c559000ea0014070942d101e503183c2e00400102490003200504c210314000150100394081c0780d0500d000b5100034003035130900c3e5544c0c032541e030245402001f03070031644102c10300302086009510250000e14082c100c601e4441d802e1400180440303100500040641d48248000c0140b0308400c0a0f290549a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 675553318 1250 675552068 675552079
    0x518010209180c0c0d11060109090c050402030411090a150902040e0c0307090e07030509010506030d050a030e07030c090501060f140405220516020c0111070504090213061203140a0c02 80
    0x40c0d039034103d4180d50064816240c6a4050302d0100311405074400e041a0002d6448410380b0500e0344e80d075070150121103102000170410808180204050310701a405150f000d4060451102035110a8000412483c4c04440c0c42c3c80156550240c481003030f0443c130170030000c1d00b041c1800f10b2400c1d091012501240c680141810320054000001803000d9200f140090000c1803441000523250600e1072018002d000102c070708803078a41c64103000541500e4002100e0710b03030f1100d07516113901d0204880422000b502c01070031103031040d1061b103c0000010b4803030610800241445000003e281d410181c004080d4881e00c42c0e088200503150b07400320403045400d021141141c00865600c25080c124009490401c410000d01d180303035928140401040f40e01c541e54441c4080000e0f4245c0310041c2d03800d401134414a42d00c24894245078003c0e00c0078040740c107155100d004e00c5030009220000c407111050100e1306640791900000060780120170681e0406422104d0100c015500800007800c5c610300b508010b010307003030f00c4802034842d6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 675554568 1250 675553318 675553321
    0x5010305211821012d05060f091e040b07090e04081921061a070519050703240b010c0305031513090602040e090105130305070c18051801020918 63
    0xd0f4011941c0910800300c040091103405502c880303040010034400071940c0007041c42d1981c550b040316988919481554010b100710103421905040c00008400180f0305c0543c4400d2000c9415554100c001240c419407045010b800c0710714001800901c1e003070807940705c80c29079802001484002010842519010307450304410501c804102401151019100003108913044d03030700314600710b290720790750840025500c040c19640d1a1005d40d100150301842204400b03085500f040f00c1c40400386620015510405006008446240d070b266140d00d14441100f0b00c0c1c44031002c1c0c1c40d8480e6461000c2074040ca801845007420884141c503170b40d80700a49a440b004048103401d0703020000c008480d90b00c00009000070308601504120910384d0b0328004000754402c1c090440e0008014002419400b014000c3c40d03c11400c10070b1030381e10034140355016500c64116403021214280145004105007802c000c00b041c200c1c031640b1b40814036052001da4014020090030701d00301b04e41d00402c448034003600d64403c40c0350403464000221206 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 675555818 1250 675554568 675554599
    0x603090510230609072001061703040608070f08181c0504081501030f020105160614070810080619021207080f090c0a0e090a0501050103052118 63
    0x3010034101203501c8051034018042480000b00072041032040d0b00310610300180e00e8000c100f100c0c0c040c0c1203c3c110005083c141c0c0300b284040400916200c149481030000c9200342c0c860340800851740150404002d281e00c086400c200c810340c02010b0a070040ca050501c03404603520000c0042c1502d4000f42003d081040d03454401184000801c07291441006c56101c00c1c11001c90210000d00d1a44644a00883c5100b400c1d001100881c1c401c2903241243e42c001ca081c9036000882d8015a030f140c01c802c1c0c80064034010114040b020582c5401650380d1440942e070390103c10f250940024000020213054003402c00c100100c180002c0000144a80d042100342001c004c544083d1401c5401034071599186540130000d010a0020030b54015018500803a10050800255620002072640d2803074888081980b00509140811121038190000d6802074140016242d04401c0b070745031a801d480d403e038002c554036404a0148100c030740000c0340445010703158070b40e01c52030300c00d0f0b0300d140d008440340c8c1c40c101e80d10800364442040700 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 675557068 1250 675555818 675555823
    0x30215070201200304140307050f0108060a0e0a1407050711040e2b020f0f06040f020402090603190c170f130b0a0c120902030d1107050a0e0a0b09060a06030905 70
    0x3003811584000c00e495030b0f5203900f101d403a500030344910a189800690010b815180101301c000903550054008e00200c0c0e4008011604c007400500715a812465444003c1920243c10398880d105041c407038008904401115840e0740076070b5004000c00b0070010300b805541c0c0000c01e4058540d4098074101c40120780c0590b41008241451006480e48146144440786010070000c1c2c14415503001c0165000c0d03446121080c07400f2921490b10111510064000b440014002a2451002c40d65280050801410501014080b46140d4000d41780e1481500c600040720707001040314040e00500a50750b26110481c2c1d4a444104040e070b400241526005502d07040c00188007044603070341c005007a0b42100c4000168142558078400800e01403800c5c0000450107203060b10b40c90b286008401034154050020300114801c2c4c4411100110b9180d00c4000d01c0c0a190000109075868203542c1d00542039040c21030b8a00e040c4590160120343e2840000ec0c000c900038820000a696002e4840b41290118140456800a585802e90 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 675558318 1250 675557068 675557087
    0x1009030e090612010c0903021c020105030c0a032c100b0d0222050103031d010f300c03020a0905030a020906010c0507080a0b04020102060a113c1e04030215070201 71
    0xf52550b107403189a0181c10350160406086a0095035a2000000e04034030314036042c080c11401a000c2a401c1020422104d0741000804000c1c030280b0300003c051041c4040301c4042d800d40c041c03400b2040c0f220711080d4000c0c0c0c0c040c00b810070070403465502042007160060108260301c5d07602c00040e00c560031071036506a982c800841e505440e2103680d4010000c0390784030310303010380b43e42d046200000c800321868522052550180d0902c00d0028115103030f400070b1181d9001c12040e003115416100c00c0501c20480c5800c0ca4610600600701050416280541c4400716803400501040c1d255001c40d00c244d01c085100700140c0c46111407960084020b20300040107a540e81441480c0062503400350f4210b1140b01c04000c00d2014200c403c07030055200364261070a54030f5815445044c0e075005240f04108100802000540c49001d04c0d40a80031302040d00526071080c460100c004e120b100000b0132101b0254001000c84441c00c50503000305191060280150500713045401207a880911082d45650800303001541c0d00a40e8010680c94 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 675559568 1250 675558318 675558349
    0x6010206010602190302031b0325030c0b071101090606082104141f021b12060106080601090317040303020114040b04150912030b040e010e1f0e1e1009030e0906 70
    0x110440d45100a00da56281c3c44908201c10072345d852b00751000d0b41c030386102c0c40e00d81c180c6e0503640e0000c00310416103586002460140128051164001c00b0041403103080c040d002c1c55a015103400241c01e49011031142c201550381d4490708240400b1603980210307041040076102135505c0c08000490303183c284008501036035000001114540e0f4840741c0c0e0041c060340041c0a007140f4100084104d810454401400001800000b0300c5d035403600802d005005091080014075408a01450710000503566500c4000f0803000824620580318030010703050061603024010f00a01525502c560344544c038107615038920310040604020301c42c01c035441c071078011403545400052889820940c6202618515400a001451440759440c040c0742091030210103440184105605030780c00b00064002c6250311100340c0460b154140420106a80c0c80d15000504881000968000d078202a0940d410004074101c0d40d1500b02c014012000d503e00b0500e12000180c0c0c08090038070703101d1040d5407202e12a11480c00040030100c882c401c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 675560818 1250 675559568 675559597
    0x100b010e130506010e01030b090a1a0402040815090a20040f0c02030a080c0f04030605090a060e0d080901182913020a050f060f1e0a12050601020601060219030203 71
    0x54a1900007141d21107030143c202600c900f407600e20058015010740340c140c00c0541c2d1001c1241d00051b074540741504030401505035000f0448405000070000b038207e802c00d421118095000500d001a8a040c12f4091a00000c5c014001e010610180c0c2d01c0713410b01c2c000040a0750005944088214654446802031340001007810400d000880800c100295642c0040b90f450f0001010040810a0b82c2400701c100c6840311011680c452808e07042d501c821000c2d103006003e0300340310701c1200d06080c0802c0e5184540c941d006080b002034171042c811036000801c1c08401814000c0305034900b4451001500700e41800600c1c1e80da02c0500d5100d00d5003043d40345040d00e5810340310002200b41d203c0400075036903409209401c1c1140300700c442100c40c90311401441802c90140f039a41340c02c41410009681c04d1051070010f02041e0741049940480141c155012180e10b8100b4120200032038100e69400400c580140a5107500020a10007482e4079031610400a5841e8851506015011008810142814420301c00c5400d6241d0b200fa0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 675562068 1250 675560818 675560839
    0x803070809013207021203120402090a020331060c08060a09060506030711120a0804030801060825140f0406020d0504181a040e0616050903100b010e 65
    0x34480c85503480900140d00040c40301d5902000348400c841841c0c22408001d204010003400c032011903546038800c15040e40d1181020002008580c01000280b034000c24440742c00205007824030501c14110009080521994010b00422241c640c030403d0711544034010700b20004401051303401100c1a203811500240000e4200b8102d00c40b910f070032820140c010401628403089880d99041001c046031298041c4d40c0c0d128608101041007144903811941048040c1020f550007122100214803050740100c1131140030407803620400c418180c0181216004003030908007941d0a1500713020103209810410b0700444038080c03022518110b10721941030082c4080e0062010b075076440540c00444c1c000d8000e0b01c10040184074029855034420302c21000c0e201140c001c4c4604a0544e400b8281030405000780c0c94150701c12618444905205036200e018074101000c07980013410240c2070206150165410903002c0005000d82001302c00c1c0c2903100013a20402c41e8040540020380c0c02400001200e01c2109185166400b0348041e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 675563318 1250 675562068 675562073
    0x2d03051c020a09080c01030227010201060b130302010314090a12030e010c0c050f0706050a0e2205040615140904020f0d03020d0e0907050f0309070e15130905061807080307 75
    0x1c2c3c0348030960712010b040320082a800c2c001181a0b1207074030911190102e01000f1703e20911040880490200014000414000e40b90595018035400041d0a8291f22040e080104255601445400f81e416030104500c80300e4034117030404070381d1041c03808401010031096204642e0354507c0390b80f002d201022408000c0c481c00500c03c40050a89a000505a48070301849110340e0441000003040800c80305161502c0d41401e19802052340e102068040082d0810081c000300d46000d80090143e03401064aa41c0005c3c3c2070400c0d08020044841461f81004002c940000c180b01901d00720f80146078021080324030755596541c40c80414110ba00310100c158000710b07010444000c141c0c01248171141540c0940d0307010101000d500402014200658040c0003003001000040c2e803242c0654020f41c0d11003041ca00301c1e6807050703549102d2060b9000803109000d150418094a11043c0352000c401e887c03c4a05134424000d04072145c8501e902c582c0083c1c40d011031111b1401714500018000c0c00442e00405c80e2200341d07a1694040d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 675564568 1250 675563318 675563327
    0xa0804030c120e3f070918030f03090201210b04020f071202060c031b0912070807060306050a170a05060a0f06150f05160c080a2d03051c020a 62
    0x501e8460302c42c10034180104490b020b50540d100a000748640444030b40000c00b84e544242d002251040c8401d8003658501144007052402443d81c00300d0307010901000c0c1c010741d0400030840200348522800709801d00c540400540c2e88150750303100c00c41d8807000012032210b80a040d0340041480103603c540003070012a00070b003a840188007500000780107030000003103003104500c101d86a02e400c0f500d401d01104144085140d40c034503402c000c510031012008007440c11a10b00c0c009130741c200e0300140d4800b080c0d001d82024041c00d40d092003000b000303040504007884180e04110008540009600400000000400060115440821031f040b0501c0e000750544040d82802010380d0007030204210489840e030f0908900065a160b080c80c0035409011a580b48172004a240008803960380c881071700d03004400a030b00d0403c6c01042040c40030300014242c580c000c02c0c07020700f06e1505041c254403424048a0300c19a050700f000c9254103180c20945000e1f4527107001b0755a40e000354440d1001c1006030780e1210800c0c1c804600b550f003e42d00f0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 675565818 1250 675564568 675564587
    0x6051303020a030807140a0c06051614060702071d18011e020d05150306060f04060807090e01150605040e07090902030903030906161b1514071101020901050a0804030c12 74
    0xc0c404442d01d2001c400d8030300d0750780c040c7e400000b0100b11900030100441c0d4460000b40070416216190600d61000d55241c0208400311001c07040925042202880482c80d01004810b0040c1000e0f040405900200360700001034200042070350901f010f1aa4800707045010039030200d40c841b0b41d88084d209200d048031518800a400c40030f0024422843c100108100c1c0d10f1000480698840050080c0703d182d6525050182d83c1d003d083ea11034200b03480340e40104074800c0501440000e012004800209050b003010498251590741080c848801c0c04180c042c0800f590100417a02a0344999102c0015504e41190465203903546a00c2450000d10100500010190101c0114010b07050760313084642d1505c8441e4164601020100c030140458a1404071042100c13400c0d10400c034a9003e980c0c0b000d501c40c11200d00f81d042d241045644215078036204104078030148c02140c90010181c82e20004c509020354040043d00b00e100315201541406240d0340001c2c1010303c40e40c40030f03104075070100030499150f5000d003016040090 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 675567068 1250 675565818 675565823
    0x6080d08011d0f07030b030708010c03091a0103230c0402040b0a030e06060f1003180c0503070b030f0106030e011503050607021002071a1f0602060f0612060106051303020a030807 78
    0x10240d070315001d108100442e19014410f14042c0f8241a01c804400380c3c0180004c80d0016014000c1c100000f41050b002e11802c03444c00c0d455100800c00f2070062401011220b1884400440036112100500c0480d0a2504402d2809602005c800520205011461401d10780d40d201943c800e00010740071490000c2040a015031000ca910240003110b00042c04036103c100c115200da420560143d24403101e882e1100131440c1b4003800c1d0500203a544000c0034400080102150242da108011241c00c103c9410304211781e00041c0074a405640c11800c2c600400b03111800f040c0304000806403180365000762072030300b0b510000306402517038250003407a540c13803a12030b0300c0d41411590103026000e045070341100f0b200c580c0202da82c0ea40c0c2c0600c100200b100c60034140708400002074080d214041546050309018981c00045801601c11074004000c03600d44042c40c43e0143e000240580e000308480015441a000c00060080c196001d40c104551229907071280d14401070426800030b03505c035103114030001c240168080100b66050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 675568318 1250 675567068 675567089
    0x40306050112020a140f01030f0b030105100f06050c0d030914030705060420030c06070611040b1206040b0105120601051614120705120d18031e2303090106080d0801 72
    0xe9a4210034101c5c1828030b1a019007040174640c44036010740c0b0951101542000c0c1100c0002c1007415100840e00f121001ca90031504040034003401c0c8458880c0188500003004507107442403034012600b8840d6140c460031070840c0141b6485440704010059940c01410701e408070b40382181c5c0c076060703a800c0042c0d40d1807081da0280c552050480c040c0b0f540405180418000c0f680c05402041c0040c0c0100a0058943c01041c09032480c2d03540d2104d0300c072510740300c5004100a0004140003a2070f00758482c054034000d0030142086205515250b5140005d9800c08192444032144052000080e603a450041e00d181c07051a151150203d412a0824100026420640c41080042d021110802a540780344076851049101c060100d91110240704061001c03800201004010b024000c2003c100300300f00c1c1c18000c0c1c3c81d10030071408510314854140e070038091790b10301030040031082c90040c0b401d40031700c2c2403160650503022281c0e0140d13900000050141d0002d4010354001c2c0412800c80d800c5506031034000b02107203020302840c903046 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 675569568 1250 675568318 675568339
    0x50c040f0c0207380c0f1605040b0d05010f0207200a030b130c09020c06100b09060705030c0706030c090e070e0d02040b100810050303070804030f0804030605011202 72
    0x29421445054441d42464008100b1213052091a84d001000c0701c4074051071308030303d400d204070f035100302040b80c040408084c0c402511101420345d85814104103203103460b0580e004000240d41c01015460203070803900296000110541c5510128040007110a400313000b03503003400820702440b113070340c0d008000340341c0034100c0b450070100001320505500d0102c1c13021030b51001000c030f024001f00305213813406a040799000700380d108901600d540e4002c0b612181d600515000c0d5001c91501240d81090140b50b512038003000e1802123103400d000c6650360501a2951543c0101001301e049801c010b0100101c4400003e094101c52000fa9540c0c0004c01420f22840d4200000c0d40e41417000030910660300c078090050400d40c56400500c0107020a2003200f406941060b40d2154503422100e1460f201e1601400c0300f1017144c3d86000d664a010400608100f0050784268000e900401144004c900b0f0b41d000d8800b502d901c03450b0b02c42408a84c7c03e00300545d000b2504040c1c01c09180500000346841c400811024041c13082d2406ca80d071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 675570818 1250 675569568 675569591
    0x170c10050d1d1e0f06070306060f05031303031509020d1505091302010804210e01030b030a020d060507032913020a360b2d0f0f0d09050c04 61
    0x2c2c2c807a0220b01805944030380c3c0c1e44508601800c100d030307020401c208221820444806401443c0510a4038a100400da8655081c000d4a90040500149075018209546541080f42042c5004200711074094205583e4600740c540720800c00c807084c8000c001031700c1306545500440138961b00804000c81c51907201c0702c0780000055641801c001d124030901c0d0b00e500c4841036822607001540c00d010018401c45c0d03e000740001c0e4240000702c0e135110400354081039450020f00c4060200140454180305150307407081d841401c034400182d4840d034071080c0207540803a0218541e2241003042d40980800b08035503070302c001e06003040cac0c5102000d001c0a1032640e504540f072620030309075000707140100c4c810b06800c0c00001b04814001001e003680e1007041032081d11210500030320380d81407468951403540203801c27401809200042208640c01d1410b101003080c1d4681c0f5102e80040014000d0325040d100d080c201461034403001c9a04502c1004a078150f41414011031720601c00101da41c076151fa100c0021000e21481180340c004142007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 675572068 1250 675570818 675570851
    0xf0513020901181103190b090c0a11070510020f010f11160302120d1d0106150f03090510140a060302030304061803140705120313170c10050d 62
    0x846940140100d1075690900268100483d124210b4207038007034880148a00c03400c0d03280300a5106161b500d804804480e8098680c5094a40c10340c40342e48a042e0880601c440b0b034244404444086844d400e200c03108490b1200b88a0400166a000507400a04145262641d64002c0388100d0400c210b40c00801980341091611011110107021490a01006012420b0035403640044c6404660003401150f4410701100300311030413a0b1200362100041a00c90040c0300c415420f408802a207026170000074090b803814414800f04410303219401004001550f008013600074040e07070001c0d8040340c0020590f94021401030541e4007500d00400103540b840c00140000300c40c5112445190192070b0f00170040d500c0e0500c2d01c80200d4000c030007200384003a0305244050000014100ca000400c0900c02d0340d010303003a010f20300410450881804000c01a05410800c40d0f00041003600c1c0741d10040da076048107004005030780613500600d800401c105903500900600d0801d116290000042c00c89a45003040510954105004054 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 675573318 1250 675572068 675572101
    0x4030215090a020d110904050705030f1902010804080d0203010b04140618040b04060e1312020a0c26060a09050c060a02060408030604090f080901031d030a080a0b12010f05 75
    0x365103800c0b00000100503d02041c2052016018151088001003000001502c072074040d0340032074542d4000388080000741400e00a205e0008040b002810807a440101000051803003c80c00174100305c6082c0006040200c0d50040d00e414170980f0a0442d100e68586199151960250007405050a42e43c00c8000300c500e8154100c4644580401da4038029041c2081400060710364200034662141e1a9000440c00e01c42074090b943c41109040e0400302c8006050a0000c1e00000d40110102150401c404041c081001d00c00700404441000700d018600c90146103c1c8501100b90404140c858044c038410b02c402c2e0545034004901d224010740944e1a200c0c1e0607010060588076281c40c12016800c95000a0045950100915800031001d1b0000c6089500c96a900c22000c81880080301e1400011414030990b5038036102d9060b11045d082105c400090780074505079500d0080103494030030030100d10006849108079402c05640390074007404001c508107984192a01801c0d48120a20407549490009056180d5640040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 675574568 1250 675573318 675573331
    0x70323091e030106050411090a050103020f0406050702031912020d0518040213030501140711010621020a050a06260f1311060d0e010e120f090f12010504030215 70
    0x80407480008451440e07400721074404540d055588410000e000e807a64040c005404d41c03444095a82d806883c0d04000c00326550781c01a904152040c072008582820303a000300d400361105402c002c0d0301d03480680f000078981840080b030268404103209401003000b90541d14004a2800d50302602c43c620101d1104880a0013018a000c04005460460000c1810668010440c155007000380164042d100e440c0d0a003900c646042d46165121003d0801c41e4041e880802045010340c09402481150700d0840c059030040c00d0603c00c10b00204105841d84210341d01d4480501c0141405007108200c0c86d80c800f009400810302c4400d40312500c0c0030402070010644460b4041d446400840c000c400340e61287d1040c50361021003010122001160100b10306502d544038000b81250050f42030380481c0d0f5040b1041260300303494250140742000c2e0f000c1402000580c0005c0e00341e402c030002120315240c072070410b13400141010840c04d20080d0010303041030401014207419000340c0c1c85140207808a0740086600801d64548020032a0340c07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 675575818 1250 675574568 675574579
    0x40b0a030f0e0c12070e0108030a0909060605090603130b0103390b030408040b04120212010e1506030a1a0406051b07030c0309090507020106081c080a091707032309 72
    0x350f5507103240500c1840c201115581c205c2da011034543d0b00410b082042a003080015600104082d0142a40320900c94040c04020005000103450504054054040c1e03280c01881024044000750400750110200b00c11603030041600000c650303403410b0909068034101c240324007105032080c141da848400190030b481c04e12600a100d8410925112a04c41c151b08054801c0750614801c01000618000e20400b900180440b0203070510000401c4c410080f412002a843c08603590622601a10030030001c07461041c2109060414911644e810001900340741d03c4280c0184413581758000181c00041c40e0301e166104034032440c01042940c13601e036401c240b9034030413101c1d20154070010050440020b20501c4641502d901c02c2c10301c0c09610b5200c100103401c5d16802c88005005039907640c1d080145081c09c005c66140000201c0b20858261b50001c00108017a200400d41c038a01902d8441010800c000401002402040d01c0016901c0da0350501c1c00030045034154540620501c81c0f0448a500010050200c48403801c00911 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 675577068 1250 675575818 675575833
    0xf0606030302010f2a1b0605060108010906080c042c011d0102070f110d021804051c0509011809020a11070e0c16032a06060b03010f060c0c0506040b0a030f0e 69
    0x11805e04030510000c80d1020000000d0220300c1241709100c2c024012031041c2d5001c2200d2800e28001081082c0503401074582d00d0510f1000c0041305030104c0c42150f515410b031000b0801420170102d00c00f028a04550480d8048061507a8641401042d8004041608c111040035a1030184888660a0f401060805001200341d50151000a12084e00400c0441c1c80501506542107480c4c0000780309900310f001c003031428803600042104101d024002e1581200c91000b903082d500152060051480c041c03559a5070511147e915102011040356240c030b801017903d18425980d4401a10f40100200c1c500301005200303120b00a40031681c1c0180d000c0c040d100d041001d46440c203020164649040c50115401c00360300b8440b54075410068009001c4414103030060070039020b0300c2000c032450058201c41d081e5020250005c81803005020000030f119410301104e0b0381e480c2c64071a00e807190030721811411555018a40c4202c00040001e10390108801a01c1341a400351804c106040d00c1d1040d80c01580d40c1000c602156810188 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 675578318 1250 675577068 675577121
    0x11060606040e0f1324050708010f120204090507060203091207230409151505011103030406050403020f010c0e0a1509030602131d06040c21020a0c0f0606030302010f 72
    0x168820784c4582c600c2043d0070742010b9511075080e030818400404090700c030005032081424002e0b01941e50054024500f43c0c1300f56242540c0341340307242e40c42d001e10800348081c2445403040d962103420170403209401c00c0c00c0d14001560740348042d42c0da0740f00d00007190065134081c0c042200e141e000b0907014100c480c0f00d1a200c0304042c81d0200f000812084000182d44582ea400018000c03c8000102656805000200054001c403a8035444900c860f1548094100000b0f200680c0c8125804415650419403200d40441e035900e5038901a8109003012441441961a114a040c0415441f0504100210701070b90411860b9840340e8150341d424144070f6500b03001c00c403a0300d41040010001d50051003007100c0401d1546125848103180c501e904c2800b02ca9000608074501801098902441001d1a036811818101c505150003101203c0b051401c1a00c11403655020403650a61402182040070403513001390303096819010b502d4003500400c0c25010035001580303001244903a0648510400e180014260400144a40900c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 675579568 1250 675578318 675578341
    0x60909060f070c06020d140a060b090607030201200d0606050901230408100b0319150203040309050a0314010c0807140d0213030b0118050606070201030c1e11060606040e 74
    0x1800b0842000400788807000420344501c041c02c1c00d0f00f5518808124401c0c038580076004620003030105107080d8a00f903010007140300541d007101e62035401a40e074107171602c0d29420141d0040210040300e21200d0303c2400220704410805000b015484444402088510703264281100e490140d000360602052070034030b403912030075032078070800c050440c1010700503281c00d4440c0150382c01c1c2006080c1e444d00064032401c11040707500c0c05000c007000c41500c00202c0c0542407440d0721660070104480c5c03504030000341d0000114040c10311803043c0f003014110207062004159074a04d01507c00246e11500e0250b0b039468001e61001c0c030f80c804d400b9103001d5000c0c6e50300c4901c40704500041c01d545074000e00c2607803422070b13081000011542c038801c02007005500510b11b400d030640c0340c104280180151036407650707940c40c81d0008005482d40c400c41520240c0d6028a070005506822000a4442c400007440205984c0c1c076600c0d104c003080d903105000d0000580d10b02c054030782d640c03500400e0110034000c80c06804030724031115001a003601e424 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 675580818 1250 675579568 675579571
    0x506240a0e31020a05031617120711010206070903170c160b071a04080720090a050105040c090f1502030717040e0f061f030f05010e010e060909060f 65
    0x200071440702c0380d04004071141c01c0ca1050070342e030b101081112425203056140c149403010003484250080c280c80b1161a10240c611000341c000c40004000b500340030f0001200070403207201d103919001540c540c0c9040320b0400300404201091490f005210f4180041c4203d40f0450400c02181c1d03020320707501804031007811045116006524140c800b442609015484408548800d030b000348215015550f0f41c41c074604000c44800301e004c20100b010f58010090200280c110b4040352205508071103040700d0b09101c44d1080c1400d065012000754428072090a010349008950300c414100c90b400ca804002034100b651041d01c1c40750291003190b14030044c400d001c21458012944d4401c00070890704c182e83c40d0420700c0d500c0010701c0c201801400d8440c0e401140034000380602c03075481900210392400311a1030785005400104c1da00c80540314030ba8200308480308024124080c0d002070a008224403c00e10142d03841d4511600b0252092040307000599000c00404c3e070380d040c0b130f003859070150001c0c1c0043d044640d1038480b010041c400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 675582068 1250 675580818 675580831
    0x4020724021317010e030414100314040c0e01090b13021e03010f030c0e06211f05040501060902120723030115081803040302220501030506240a0e 64
    0x2000c21040e040d69060b40c48034409010420106010f80460512a03800c568010440303c050364001c1006010b030010f0703807192003140502240c0100311400f410b4000c41c041c003104251560510780f41400e110810000031803050a40d034030307540c0e12040b5070380c0c69003044181c88850315099042041a6104880c200444e0014407840c0c0c2900310041004a02c1000a0000d6109921002040c1c000070800d204100c1243da504009000b14a20300d003040c1065800908100100c090750511900c0150401401031000d00c607640304241074244601403402d0150040c2d018140c2220103c4087d460628007040c03001003803007034880492080585003810b42d601841030310904002040404158150300c1d001080c544000011806042c000613900840c024402018150702c0c0d0140855003420084403410880d40c0c0000242c03001c490b0112075110069a504915003112004440c0310001c260600700084140240020b51070f00408604a54604041c5000403090f002ca46107a001c80d0300c4138082038104640079280f68410340001c2c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 675583318 1250 675582068 675582071
    0x10e190e04020a030c1206181205220603141003080306060304170a20060601081506040914060a0e011a0a170906100605071e151103060f04020724 64
    0x113442e0344035000c3c2c0d24513941c0700c2d00351106202e51500c204030341400307106840c600700c1030720f43c1d070740462940c42030b08109841c40003004100c000301e001004514252800040c90b40541c0104031080d448200c0100a010000841d4050640c3c0001160841440d900740740b0880390440011815030722058100021130b031002c0c00a55070f1070703c501030340d000301c0040380010000b800075500c54614110300c20390024040c0c1103040300d44419421480811100e41d802610700c83d8400048914021491004000588507010782d400035048945030585c02d002e01c401c1050400d025a800300d0303040e024142e0740c030603e0507440303424003400d40400544015420015000c0011b4200c0c049242014021080c4805801d85080c000329050202580540b050100860b0101c220a01508a62070800d1600c401d40d1985030040c01c10400122000c0c82c040c2001003400703821404003082410f4210140403802080000b091542c2094402a10441c41100c541d40c1502c0c3c60310894140341e600403030964542420a480700744200110110b140800d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 675584568 1250 675583318 675583339
    0x501060f030e1b04020a140d0911010509100e240c010e1603060b01030207060905010911030a0309170705030607050307080a0912080406150807140406030b0c09041409030306010e190e0402 82
    0x102c881031f01400192110480004100c982c03802c09440f003034102c0c1c240380e04ac000304000f03407002507c032000300c120104c40a00b070125010070030801007015180c1544031280e6204c217454074031030035030030180c01010f605841000911030b1102050300141c45640d134006203d8a0341480e0010000154180c0000710081c81c14100103051808548450302501e0b0400b02c111926555003480e402000300101060501090a40003043c2c0c04910369406041080c0383c2c0a0f01244040820464955030010880c1001030306001d01500c0c058201090058401d03042075940720003280c1010005210f428492081625041c3c01079155509884414004c6d00c0c10341e0050014ac1c2c1d2192164034501c59000140700940040140c000140b190701d25210811481c6072208200ea1303c21070038000100007044149404640141e0b4020503295581c0000740080d000301503480905070b00e03016070f508000303c2c0c038008409035216000c2a26122803403200c14041141c1d800030400b80c1030b8540380a00080c80026120440681c2c000d2001c1d1110100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 675585818 1250 675584568 675584597
    0x6050a2d060f052b05030c0a03111239070303200601051c020306010f080f06010f06030c05040e040b0106110a0302120c010b040501060f030e1b04020a 66
    0x30060009440009654045081101085144200c10040048a08400200d0b04140004e0b6003c001e01d1a03081100408040740b21003041c5072030450600b41c1d071000403aa41c40402c0b01f911a103442d5000019004a80015640341c481d42c07012071514941100000d009103446c42c8110140406500e03007580010405000d820381449030840080340b0002c1118030b00070842c04c0c0c50b501d0300a108481145107a0308420850489200403580020158155141140c41c4410800644d804060000c001b50000e90f041c441d800001a21010202c00d01c005c0e0740e002019528140315141e001c43d680c107420310801c030041c00e0f442c03410480b5510981c03190001c085a071070702c6482c3c1580d4180c480c2000038180c03015215007a903040100300c5503070010005000c51a4042c0038142c0340c20251006900e030300c0078401c25071b9058800101c1005c0c80c3c40a41c0034211502004004000658641c040142605403418109002c64684040020442800661008484682c5020010361003403141884007941004d440d83c010f200001840c1c204 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 675587068 1250 675585818 675585851
    0xa0c0203071e050d1e0c0c090b03160b131403070603240e0711070605030f0612031c050c121b0712020c01020c010905090a050c0d09050f010c110a06050a 67
    0x920104541d05c4900070340484c0c40880c2070f103c9601c060380600402c00c4c1d6000001e01d8080040045a0344002e00080c1101090042810500c41d803a00d0309801c4030700400443c0c21911440a8032601030740c0c48a0051300b9880d41039881402c030382c8440031a4035920003402001654131903001000076281d19617023030600809100e201e9440ca4159040f41400c005c0b09000c10800e154070180d903000745130000d00101551450110080d0440c132004e441c07884d81e0482080000d86a45414500904001011040325900c1c0e0301b800e582c0c8a4100c0d100421070070a418000483ca005203e130007920f032086401c0708612441d440c4c0310105550f4158400340317821504030601c040400308255100c1c4001c554801d401509004d199040020709261402c8a040e05009000c04140980d0705ca0a40059010b050590001025281c00c0c5060b0740c1d40c00b8000401c8103090074441c0305d02c01c02c40003040b1105600e500381e009215203540391340c00395a002e000e4003980c4a5648603c0e50440442c880d600003c0d0082804100007900c0d080070303c440c88 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 675588318 1250 675587068 675587083
    0x909031202070b18031620010219110102010219030209010801061d0402031f1e0e042d061a010e030d020a0f030c0c030804030b07021c11150106080402090a0c0203071e05 74
    0x36001d8425020801444002401000c51f10744248003400d040d0526000b001282040d60001400200c0300c0c3c100150264000d60480d0406070018800300710203401e060000300654400c1c4200c600080182c000026150f018040002d0a00004803c1428041d80d82061100a402c01080520403991220400c0e00c0c042903032030014050041d0011451202182049030155010151310034000c0031009001c0001194100fa96900140290008661000e06544c6094070b417518050b00680103526151600349140c0c4141c441c040307003038000c0e00c0e0b030005a1507550400d44c0f82c5200f4504100540c114205a01c0003d011440303130f4082d24801d090962072031007161207803004032500d5002100c0c1060001811320500031541d240356030103034840c4010205903451040c0d900c0d88002214810b0f050000a410601c8040814400c0344103c5100349400e8880307623901c0000404455080d503042e40030380c884c1404035209813010b0082d00c0c0c200401340c0003903180545036500c0c0102d0010680700d01d112902e1040c0c0480011342c0134088036 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 675589568 1250 675588318 675588323
    0x30709091e0b0f0f0402010e1e1e0f041401060509010c1203020307080f10060e130f0c0f0c1119030b04030f02070501090f030b040602040f0909031202070b180316 71
    0x1820074070741074483c001e00030070140c0440b44110100c42004010b0b07074060008082502d09450541c3d07180c110550f1078010440340040c10354440400510f07910301081d80e8003048590241141c64214803040c80051000700e5070070389110212440c0100040c8913040c09000100113001e018900041110966110a8070014000703e10800180d0008140989244c0c0140b115130000d0070301c4540318441c1807106d40e60410742a02c2c0710303030024001480b5440b50545c1d070301c8401c0b041d403040c0100107200020003100048020711b8034201c200c1c04955210180701e0464402d50745010354a90040c0c40c40c102d18010710402002c504850250103851840c0b0902000042c1c003c1c3e66240594460340362010a0020800040e0030103101f038004504201c00c01c0b0080140340e21b050300140c00c0341c0e040b82080c51103417103500b0510013a1246400c000b0341480f210200042d0201160301641c8903900030307034403680140d006c010110141c1c440d00300040d1109000c940864102403180b001268428800c400f1249440c0704141c002c0e4080341c064000707 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 675590818 1250 675589568 675589583
    0x6031e06010305010b06092116081c020607050a0804020d060f0b04050f0709090b1201050106080a0c05041a09030718020909060303160f031403010b27030709091e 71
    0x400800c0424004c03c1e0301701c5400c9420f14144850741c1d002c03407100f242c0346003003490002e6902115030b10340005000c14040c501c3d998000344002610707044400d66450040c80d60b8a200005560300500162000c11510302910041c2d071011714080440d14100c80e48030300a013040e0b90004084ae012400106117208491045001a101054031801c0d2420842150002031112004140314420032400b1030b4005200e10580d040f840d030002e00a83c44801180380c5907280c00040d000c9610742030004c40d14603004078010740b007201e803c2c800740a9082010b80c2103074a03000381c2c4a00303010681159030310040c14503c0c1029080f148405000c0300c16459950810103102c0e0b42c401d9065404950015180001c0d0408011140d40040b040d001149000c0c0381c4884540c41c13018491001d4400090030791000200341c0301e82d6895429100d40100161a561503410b103c0c0c41d42d0000780d044544c0d5191980d8000030442c0c0c40d1501c02681001409040380c41e181c40306840c05411054030031200b0414078100d0789036810000340201101c074007400c003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 675592068 1250 675590818 675590821
    0x303040e01180b0f01050a05070c0e180102070c2c0a051012020f01030b0d150b0109081915060819021002031309020a110613060510030308040b06031e06 67
    0x180c03810405007509003441003d080c000280300c0d035181c0e01e10075644031000b071a1180c1d4800c0c41e0030044a00b0700801c04010100d003d4881c0010b240314400400d9402141150a0000300400c00c99886e801c070310070700000403c540c103a404200014040c0c00b8030401400840180803101b9184590f1400c14a01c04950b140f030660303500c10500c5480c0c1c0e00302183d90040c0c2201185074150b100c883c1c0000b00340c3d03500004c0c07281c105901c415030f40205454501041e9861540410450707004021024010090711120314000e0009081c0b8500048a8400146000c0f8103046090300070b41c4204203440344500d03c08011300120289031250b2001480c900104142090b4400003441000d03000f02510402c4819080e812036842150f1041c0724618245030000d00c40001c841d451000140c0c2c820283c202030b41c0c0102c0c8403501c5551400703504100721500c0f54900440b107140d840303540208034a6441c4104034940e0192800064005206000003400082030300a8003904010f00500701c5044203003034a00c0b044070080c00011018aa0801030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 675593318 1250 675592068 675592079
    0xe01050906041101050708120a020403140a1a040206030604090309080a0807060507050909011806030c0605130503120d051e100311090c0a1803080426150112050c0303040e01 76
    0x91850f0040d01007441c0c0070385880c640303441e50300e031500540000568004c0c1d07101c0411040d5802ea4103e0b0001c561082e403c00c4800d41d96070710181c44003500c04007502e940c08c05042c801420f100d010000b92290340e0051480b4155120322040c00003d103c201401c4050001201001c20380c10b100b0020b0300000381c0301d8079000c0c1e0346042500d4220151000985550203201041c020340455580c1c544415064440f0441d82810b1100b032030360b6050141c100c95001800306542e0312404903410b41d104000300701c002008103866041690714400e01d43c2d2041044180c0c1000b00c01404117003a40030054005540114281d42a5a85628007411981482c1003e56184100c02d02880c410010030404840c40c064072801100c14881ca4504000808414820088448104034110110781c5018482030384c260301440c1c0041105403615200e02074800310008183c1c861070b074840b95108608000700002221100c0c0758008800004691900d00e000c00c0000190b842190b2a0150043d90001c0f500c00304054070003451a000d44019951511 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 675594568 1250 675593318 675593333
    0x40836010e09060904020d0f06110c161401030b04060b0c0f100b090f180d050d06091a21010203040615080312011502070306020c06060102240c0a030e0105090604 71
    0x1a0180303000d0b0341c405080103816603d189040350300076016240f401c0400740e0b80c50312121700d1030500e0006284500d0845583c0400701500040c20440219108487c0f04140c1401c4801c540c214074401c1488031104244030703005551181d01b002c5584d020203000410302c507490b1400910160480c0c0d43d6140d5540c406040200b100904002d91400c80481c0e0340c00704072001d02100412214040102800d51720038019011900404800854203c501c07820025512103090340134001705946d00584140304240c0c200700c00840c240d0581c0c820021500500c0d20300108448010040c403401112824405000054400e0003201c003407802e0008610681c416000000e03848240000740c0c1c52004140c0000c40340d40c2c03040c001c541c00b441c40d072820281517410844e80e1154403401c00504034a440913940008002c0c1d0b00214007082d83c0ac00001ea0540100e40136000e651030544401d031542500702014519051551020011400000b4204010404064640340209008040071f0f1032034251749081d1805006036106078100310030f12054 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 675595818 1250 675594568 675594587
    0x17120c0f0321060a0b070f0201090321021b09040f06021c200403030f11010e030409060801060b09010f05161e05010b1509040506030c030a03020721030804083601 71
    0x12140584c0d41410180c400707440e4098054000c1807103003420200003e580c000d4090030001c591140c6079400b440502042030b0848001101d51070050b00c14240d82c5900840c9a8010220a08019180d03c1e526510340d100c5100107106c440058a04940c00c01110f4400070500c0710550320050010008600f69110f180703003141d0019004000368541c60140070500c006903102802000d5003000745054000401405040b50041120003042c25003803200240014001c40b4640040c4110384021000b0001a9964040001d8030301c10254014001210400050001c0e070040018001110741e0b03104143d0600801e40d180783c0885203001c8007011115510056608011b000d0141404000081c1c500030100b540c4211a20f08c18018160380e584565101c0307000410a031800c001b210240c0c1401401c960043d5050700b0065220300103400740001840d185c82c0221904020f0011146802e80d00d136031000e05036550364881e80f0407a00980b00805e000d075040c4080031b100c09415002c0098101c000d15105402551040c00548006207 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 675597068 1250 675595818 675595831
    0x20301030218150a0801092001050f071509150f06060518010e060d06051014040311060c0f1609050f13150e01060f17120c0f0321 57
    0x4000500c01a240c070302d00b441001280c0303822580d007070300e400202c43d4450f001d0480f402c2d00074220803800142d10301c054204221480c0203a04048074034125851500d009007007141d009000c502c041000d115642c904100501c2c4240c01501c200183d90201c816010546000800030354204642c03404141c41c11045100d500c01408036104104905890100098000e005000c4040d03291440d140d000c00603a4003c00e244085040020951550356205012b0480103020034040c081c0030340d00702d4100140040c0645201c980c03085071902100d041c01d01c0c0d5994402180080203c694000d6014041640d54442c2040f840b80c5548040014144408410200c0f031403034081584141011030414040c001c03603101a5807080c1c3c016075038500e00c0042d09001d082590041d0a42e51340c0e1003055140c6031070310091410640c401e40c1521341c1d034446461101d03900c82101005903032068a11032942c00403035091b1000c3c10745d030b00108541c440c0903080d1000c04080000c07042c110b401403252040c030340d01c4000285d110004c85980860b803115 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 675598318 1250 675597068 675597071
    0x30a0617100b0a0806040c08060606041a0d1b08250e090c070f0c03020a092a140406050d0b0a030807060b06040905011d0f0717040c1d100603 62
    0x1204002040d80c880c10040300981036640d40e034030b440440e1180494003001c0d00302c800c211a400e04052500340203640c040d11a8a0407402104003181880c41c21400300c0e8211140e04101c41400c08412000030120703031280c1c224840e400d90303030f030701c810700e0314a800100404425094840032282d00d00703007500c80e038155000c05d240301c1010b007131050002a045c0c0060000c0c00a150a8402590740e039200d50540c4160310542201403c035000081000c4200041c288002c02500e1003502c175480000e0340d925064098501d4071000d034180e1140741c1078134405020305038030316440a04186084a80c4001d1101c61401581c010b4110000203600020801e402200b24040c45075113210030344010402d1803031511600e000380614800101303241c2d11001c009107035588000940c2d0107402d00000802007540e540c1078500f100481c117068811001001d00c000b0b0381038414210502d11400494442030101c00d805000e020340014010701c2100c2040320341c0d1020521141003448030109054039032600ea9181014030100c41741d5851a4031000c01c25 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 675599568 1250 675598318 675598349
    0x6040c1a041701050f0a0605100c0813030c080d05040b18010e19080c03060903041509030206120708060109080c010327030206070801080f100e0102070b0901051008030f07020d03110a0305030a06 85
    0x54aa00d418049e06044038a81103200f0300040c80d069255200d82116852003000d18600441070058403c4540200c408441c100e8210300643d0005a80c540140d00c0340c120740100902102008007031982c004200f010701450940048200c02000031003c0c10002400c403001c0e03502400c280a00b00c010452182c0428049000b800180740484030280c0d80e104d5405200030351b0f031000c6072100034640520381e04009150700400c0f0a0321848a482c03030001d0394508480302c400140ca250080b0309075500a44a2209486547e401341c03008254100064007e4001030301c3c00065880031801d0031520400080114407500c1c82540a044103042c1040001c1000c00103030040c00580e0402201c24040381000150382c03076448903d600124000c1c900540290081c0240360700904400d808908000750720742c041d440300f80b24540d0b1507215805a03441d46041a564000c03030410720a40b540401109000d45042c400c0c00c44150720a281c203580700c6040184490030802c11000c105c0108001100f4040341c0d00c3d284c025280644952003c0b01d0b1711 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 675600818 1250 675599568 675599579
    0x1d0610090f0204030519021807020307122d0c02040e0601171f1802030124080d1d0f060403050309130209010c0f1716110306040c1a041701050f0a06 65
    0xa48604506405401101d808213074115218842018001c0360301c00381c44001c43ca40724102940300d5001410407982402980033700358030a40034030144001c540744a482240724200351240c0111100f950000310b030078045161403881c0103030780b03601a0111002098020308500c0d407600c25a65040e00403c003414426070401c50006203621251034038807044110b030003000300e0a00b0240c0614134612224000194243d428448611180302d00c000080c803400000c42c0020815a84e1010403540f036901010007030001840c0f144000d40e21040d501025081d1420090902c0c40d01c81d2080c000602c180c0c010791085139590000306480000d850502c08454000d80340030420351815071904002086c040c40c1c140300a0080804800510900511420b0707451500c0e40e4610f210350328200d00f81140c2c45d682030258110f070003920303e0f11a40d0540c03c1c045421405203030300c0001c3c3c0360240c0c2000d2404001d140c00180008041c02d007808002441800703080010203e410031000000c0600302071000e0090008002d050415050415008000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 675602068 1250 675600818 675600823
    0x906030601050d0602030a0b060a021e03040602101a1903050d051204030c1112010e100c050406050a02010e01050c09120a020102031c0906151d06010509041d0610090f02040305 77
    0xf070703e81c0041c0040e41d035694607102c100104044804a90000700100e610600c490700041c030200f08400d0007403103409003400c9010b110365034403c0c2e018500040e0409207450414440c070b034108403449048800c01e08550b10015020a040759074a10140c4103c443c940001c00c2408814000c040c0310b0500c0b403504610304902d0124032001090f000d000101003054442021050000b1164008020500180440060001070b504580606140d1650013514050382600b600c05071840d100e4212006031545815003040d14010302030b00d050300042c140d10259501e410694800e00801c0c0304003403047d01c0c1a129035441e80c07420000e02c8282e0350700c420040301a85c010b00e44203025070380010554010703000c01103e8010541c0c0c0c6100c1c25000d0700411400a01003810701c0190031a00c61051040400c0e5600e031070f0041c5401324070718100000b9100079150140805c200f08805001c60402d508800003940c403008c1000c200010103010300d8a09030044804031650301070b1100c14440f0000500032401540d001260540c182411b6440790b58 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 675603318 1250 675602068 675602089
    0x9010617070609170a0218060a06020c031c051c0f1112040605070306080a060903080619030b0601090b0a0915050a0203040b03060f1e030d0801060c02221505090603060105 75
    0x7441642c9102441340c550300c0c01c1240c00c00d05940030386200c1c09920004098203140b00c0c03d88600d440358074040c0c4081a0140f0000c4d021408220040041000418580f107034421030301c1840c0c0c2001044010000c803001e4800c840a2070230003004140b000228424104102800c48040e1380401c100c400e0100500340a021034415603503041604844001800d40345c0703000540044c0707102e50140c0e440d40580c059043c280b0000380d2104142c0c074041e841d03a2400d50303070b10300803c04068407240400000303102d00b54052012880c0c03d1000342e071046060401c80705c06d035180d540c100c00d40c1c2c00c240c2007d0005240c16005000741c43c0118501c7c4051801030a18078244050344d003000e501ea00541c042c80b90000c00100c0001c5d0381c0e0352154070000b5448009040700c4d045800c140109121184605013090080c4506041c43c4504c1744034600c418101c070700c01d54a0f0341e100d88c016801c111903c08400c0000800e00c1440003d00070100c040e10070041c1d941443ca11071490140b07080c042c441c450200400141c07003a000003004100d01d1300d41e08500b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 675604568 1250 675603318 675603329
    0xc010e10110313030606050a0b030907030f050c0409110102160602030904110f19090506040b03010509130b010f0602101404030c0302010e060c040e0906061c05070e09010617070609 79
    0xd110201c012074291660080c0100c043c2c11070f0200c2000070600001d81c6c0600c0950b081039850704903070758488090404c0b922064030a207205030f101240c10004540345e4085c1566041c07003041603034003002001d0000350640710048402d03268082d42022880711580c0400440404e08550481a508103103040000781d2680542c41d505da0150b80c95111803003000b030303001c81110b0100c000004401e40700c1350810f0b1203501c101c807140d2118010603403620000c03e803490002c082c0e0741150025941c0c5442d5a00706401c1c001c041d8006030184240007584078601c400140c4000d441ca01810209901406607460140000d29009811400324a40c03883e040607a48007021048500d68003a0301070414001002081c80d00b207005000c03c1b80075100c0c40c0a50002d0200d40b0110400400443d15444018041c50b101c503c4580d84500c010703500c0030350043c1c41003458903040014141d485a41070140c4255400255241d486440d030001c215500402139564103030a200a2003003480402e80550400010400542007000140c207042042c00f07903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 675605818 1250 675604568 675604577
    0x109050f2208120a0e061f060c0f0203070e0a0b0904050705062a011a01020606091b1308010203161e050318190201080a0b06090909030702090c0c0c010e10 68
    0x2404140140c920403224401d400f08158002c0e8601140400300408201407551020301444011a51180290903001030001c1d200c2400b0f4251440d00f06c00b03031038a4110503400c4403010080709028001da6014000b100c014000b0b504032041038a004d40e06181103801c08181184140030b034405000200d100001d0200c280c80003610401c1d941d01e030209032040b0700720b15071078510b039007204102c800340c10802c0c19040302c507504a800011507504883c1000680c2c4500080b01c43c160020848000140484c03191151440d004141310b0200b8035000b00d01070400408030a0ba044002140e400009009002c000c0e00e42c0e01140303e00928014001c0328000c45c1e01040340c40b01d501400200000440880c44d8102e204a070080c003030001004582844076043c2070f00c40c44440e03e00007a804102010300007504250300f8010016174040c020450703841d00001d10304001c0541009040c06400b031100f03010b482e0051302c441e1a070a0040e59181c421a46401d1510301840c03038411902000350403c5496000344465843e00552040c5a5006080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 675607068 1250 675605818 675605881
    0x90c14040603082d0c0109150603031b03030b12031e03010806010e0a0b100e01020d03061a070507030b070c0c05040c0516050a0c18050c09030a0f05031606050109050f 73
    0xa403190640e103000103044413400024041d001e01c00540c0090090380c4151a0400e0710034502002c00c0454a00380f00140201300300d00c0000034803400b41c3d9080340665100f410009001c0c0f0300704000c12041500c601001c01150b000090342c9464040b071060f00040404a40c1140c3c0c91507041400c660340301e110612a81c010a41c0310f10100d0342d680394a402c000d00402000d403e0034800400a00020050b000301c03002c40d40540181d4242158a81c841e0080d0ba040d00c119441c48881101c590002c400c02d98400342c006e96460080d01c01c080005421201a81e01030703611503941d0040301e0304900f010784007075043e5400203105600c2c01e051001c4080d00a0203844401e0540030341c010b0a9001c40c00c0960502c14885c1c0f00514602c0d5899001c0382001c4051020b0480c03252080c01040903684008483c0d0161103404c0915034194480c190000c0056481000c41c0015485241507070308000041281484003c2044021580c032610380005004100d081e01c60345030701000c4100340c00c05504110059500c08014242c056034002c2e01e440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 675608318 1250 675607068 675607117
    0x904170a0302071208040209270607050405120303010317070f0c06020d0e030118020904080c010501060c02041a01140f160c0807060c0525050301090c1404060308 71
    0x88558064520260540d031440038030001002984000000c8078225984258520514417404c022072007039601400300459621401c06c40400142030b00e805103550380e5407000140c6074841c103200c079a014000c40e03260141c540d42801d0801001c0013100c800492141c0c01800100089401400030b130400700088031500359503000c2c81c1403403007070551301410107030030302d4850307100082c120f607000800003509002c0e42d84940112000c03c1c101802d07680d01040310400d0f40d103400141000345c0f611003103042e0020f201e002003601e4004400b00180c20340d013099100d40d001c15105104181503080c10300548581c42103031294160b19480850000e0030300040c1c01c10b00c11665002040d8401c49003c0603013100d144c603004000c2c50000c5202ca1070451105881402503160900802000140d911b01a202e600841540600680990030a03c1c42c159801c029542607406801d00710000003a07079480031305c250541c01c0d010744c10001c07405040c00d01095061001a9100340518940101000494000e10656245170319403101d08020f5420709 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 675609568 1250 675608318 675608333
    0x6091d031c0506180906010e09030a12020a0215040c051e100e0112090606180c05030708060d140102070308060f031213051804030306060224091203070203090307120f020904 76
    0xa08108084480741c140300c5d101c100050303200c5c100c031016038510505a83d03044081c1d0f12806290213010210740005640440c842540d00035041c0c16001c0e04c119030008080205403030483c81c0942d41900c111110300400e1206007000c01c404e01c0400c102c160212140407a040119501103036a5242004001c0608084a280c2e80701d0f1300d403d5000090004203020692582c2441c0e00244441d2117149103806000401a210003514000d1441c024000d0301e40b641107590b01c59041e5602140148601d901103904080b06000451208240544403100800140c4a0307038240f5000e40148400340a0910400303504c10215010394002075585424040c11a195807210340100d0313021100c900c1508815480580032940e070700100ca401154070304c12402030b40e051280d155100c0c0c040ea00d0f440c0304184010100000c4040765007400e1101041070304000b45604441d4a40030492030410b080d002503a1880040c2c10020340600c9500e0104a60b001400415484048180c0f403966410300e00c05000d00000e00410440e0001400c0c0000d5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 675610818 1250 675609568 675609589
    0x11100210050108030a0e0d080f0d02070803070c1a06090105010c03030b120d080705280210151505041805060a0f090f0f09020d060513050106091d031c0506 68
    0x218424400c1d540c50769038854482d0000f03000c3c1ca000444d601c07490341140c50700d0000d0700a419007014100e454414030220014440c0d0002c0c580c81d044940811580001580300300c011841005143d482104602d01ca01d0706641c4110719009c0295210141c1d0103000d69a603c3c0d4a03132504681007404d1030200c40d2980c1c40e060b0007074503068000341c0d071042a4211000ca00880030400c00d141007001e0b07031002c503165222042034650740540c1c0904920034040500d1a50192041000c0ca41d9181c00741c01181c0312210014422015100d5242180b2007056440c602000018642c02c0102500789050400d1070415083ca00021000045139004e154102d4031880400c0c1c658440b040007401401011003504d420395186d040c100c003e00020785400c8250f0340703840440403c402c11440365031385450f401400c0d03102c2440c003903c400000e0540076140300c07004400c410b00300380061001d10905004105c411004158000b8945444c101c0c00e910041100c81078004015024141000400c040b9144800300c1d03001620780c0301c44000c078544200307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 675612068 1250 675610818 675610843
    0xc12100908030402120718090c0312030b090604021215041b0801081018020907030b04020d09050f0105040308013006330e1b0304140606030a111002 65
    0x600600e05060110540003503120354001d840890a04c0c40c007210083c3d469426110340085840034011010300036a4a8001c1e401e458014034848a0040d12501c2c0c41050b41c000c91880000320f070b0707100862801401d003a0007180c1d0202080b034046040c0b1400c82d4100c0c000c00380041c102420b00915000c454a15620307030f8416120924201d6440d4884010401d025118400a00600e000c9104000404000000d0b500034615000e8441019400c4c0b90381d80c0c0e00340304103020064603142c10700d0707112000500325440307520107010300d41200c05001c00c3e4031000d410100d04055100c103805035142d0400c400c000100703802030302280c1198200d20071401c0d80158100048580301618544809100c2c1c000040018844a80c010364400080e4050000040c82c1007003450600103142c0c0c441d0641000c14800400110b22040ca5256105000145044001c030300040002c1c100d52084800f00e40038990781e9001c80d408130040104940c0008150000d0031000841d0700c503c103403820350001451090b28a24502d0200303038401e2002122569 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 675613318 1250 675612068 675612071
    0x328090b190c062d0f0507090603021b030c0c1801050928050f04060e0730050a060c021002130509180106060f0f051e07020303070804090204090605040c020c1210 71
    0x46030001d00004c0000c41007001680d031400d01000d19200d002e644901ea0043c000c1d603d40b45a4140b03044001d40107900301c6851007400c90000c0700d018200000900040204015070405842034084000400c050001c440b003001d9000c64200005208640302e04071000d4100c21900601c00c4c2440081083d003c0c41000d05084031241e5040c402808441b4106d4104c4078091031003000180006620000710b99528085446140b051010103504207036889001200d01c0c400010007010754a800c1d8076034807414130303003e02840300300c803010740e00d464205445505000074a0004601d403419443c0c10705070b800324540e02c0c119020740341c892803105003c81c1c1582c0345001c1483c0a940c80500901015590301c270007070b2412000006803008580d005038a00c0e001d510840880b0030340e0900501c0b40310442a41002c2d04d030b164001c240200c3c0c051108202100205040002030801841d0340c030005aa44d5041450610989000390700407405039080c030611003441500402c550340c0e00003041d58460f50580a000c96940303041f034501d44030302005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 675614568 1250 675613318 675613361
    0x1050f04120b0402130203130305030601140f0a081b090609011215031104020c03040e0622020306040606031404020405040201090f030309090b0306270328090b190c06 73
    0x1c190041440d120303500880b0705c80d6901c0c000074503040591100700c442380014a032211402c000207004001954202c43c041c500390200002030707000c0c54099071003070484101c01203022442070012a40704410b154041441c0f10f60320070308200255015141d0003130070040c0b8401c645c04500c1d601389900ca100f003464207000312031b4188035040f88010b08c1d4032074806034081580c0003549030702d000002e42098000c541d421004280103615261500007296081e403c040c0c501d50b0311810b01014214040200314241440902107180140d803410030703c00300310071904d5a0703101030b05240c10040400152041c0fa0101036005405a401045c40e50341c505c01200d03900342c42c0d00107212594150b40c0c04400d055001d08a1000d80c4d0404504100118090040681d41c032001c641c109103a1103903803d0642c42412031103080140c900b46c0007c50342003080340200c400740c00e0f561140541e81c0e14646c4440100c2c00754400d28102c01004002d581c4d074603020b504040b807010450306003000c1c401e010a01e030900081090583c85946015100b5100b0b1211 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 675615818 1250 675614568 675614573
    0x3120c1612080a060f030b06030a1b080601050904080703030b040b060d020408070906210302010b090a05091c1d010207050d0f210503130f14030307020106060e0603010501050f0412 79
    0x858070407407161070004075000700185400a10784100400e542500700111585850b60740e4840b001c050040040790907002d81412240011038a1403003000d40a452420322021a0804c803e1030301c3c18805910252140301d01c0014800491000c4003200e41881d01403401107010708070303c00443c0182c000703c405243c0100b00010401404c07842c80e809001a200e0400907aa0308503a90000d91066807454018a11001e0200c1031011039446854000100c051003800049100c443c3c030b20004900b000c0403191000415200d0b020489840e106002c40030400304a00c2800f41d0220202000400c00360b485118034802e40050701d0b0307910083e80200310180042c000140910750580e80c61500742d10402c80903100f2100343c201506181505400c45800c038400c0140303907940074111b40d0780408003000062000340680351203d6401e210400328503844400b40035406828000d45d5242040d017002421101586c2c030100400c8103144402c2d038140c0d911001c50341142c00c24030b002e640729184007411082c00d10581d840010f41c41000140c1104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 675617068 1250 675615818 675615833
    0x39020307090e0d050903030a1803081606050115020d110c040f0c0801050d030e0904020114030709082a09060a152d0c140f190b100803120c16 62
    0x440300b0401d02a140b000001c00b00030380e858010000b106034141c000744040d10b0f41500c582d02d0a00580358070030500240c4c55590303d81c030903903620980b003012001d00203008410606c046030040d07a004244c02c5543c00300c0710099000003500c0f924004100801c000c543d001840b01c40301d08100c88840c210b80140100034007404481400000c005041d200c5000c210107030f00000301854110844080c840e0540caa143c520b114a900b0403481d203500038022414030021440900003440f00700060340c45810b040d29450959400c0a411501d06401d00300f010300320440450813140103e1418800043c80c81d4142ca0285507510350300006032611420303400ca02080e084000d00540340715805100c1c0400c1c41d44540750240c001240d0710240d00d010304590411804211451246000583d410880e9494441160b065030340c00c070382c0c000e44030341000e00940c982d00c1411668020724003400050a101d0360010620142140982d1500d41d50036140d0044521030102441a20005650301c804030040b5003400075448881081003a00786047e01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 675618318 1250 675617068 675617081
    0x3010302040c09150f180e1902180f042307080108032b0f050a20030907060f09030501110406180f150e15193902030709 53
    0x244200d041c02a001c01281c003502c3e111007920019120f50061826000054900c01e081e803a4110800410710741d058680c080080c04c0380302515503001d190305582010030803031100311a420500c002c0944104180c00c4250660300b4101c5010005655880c0c82d800708600041c001c01d64000004822000e485020f60368622242e1640e20880d070a031211941641c858072545d6990003658140074040500e00380c0964940c0131780f507007003000030551803000c104000c640c04000b0940b4415030321814401d4841d502400b4040711080d0f104c2c01c1454021504d0708502d05480071076602c41c1944501010700c01000040f032807491044040502441d0454001d102c10103010015149aa106100f0030000410b040c45ea424440c907181994000c40d0070b01020403a82c2c1b418207548603803004030003404c41305018070034507010595166500c03861130548949044640340c0035888100318417041c0540c14070381002070b06050380040c3d01010f82c0680004c400d010391140500040810390307040d0b80c0301c0f01e40698903206013071000601d004181c1004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 675619568 1250 675618318 675618323
    0x50405010f052b0f0206070609060c0909150317041508040b0a050601020a02010e2b0203010b01090819080405032d12030105191802070201020d09050d0209101802030103 74
    0x4922210080f4030044445a42a90342d0140c0c40e00c00c11010b01180d5040c1c0c2c040001030000704081d20344116070f610003080303d5404100300c60464484007005071584c0c10a90000080c10103050600900014140750104454640001400d41402d080c072070841e00000c4065070042c00900810a022894200000e800d10700112011500841d03a840041c9010078240100390107118180c0080c24002101e90040d81e44070f08001141ea007088001c110214034031022014000004580044c00d20206060b0040c14250750f0310303d1109041c000101810881e48000060780c091048401d12040305164061505900354801d6074041640340c8190030a100d1035000007098243c1c000110780c0c0803880418858415622504c024001e800710300b80070300040200d810001000c00390302d108420401003050300c8100038580540300280e813081c1d5550100302c034021540c04110148108150b820900740d16840c00000030032800788001c3c020301070324040011900141500e004ca802426900d058840450072201070340e4000d40091006 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 675620818 1250 675619568 675619579
    0x80d0e12091f021c1d060f0a0302070303020d06061d04060f1a0d05070207030b072c0d020301061d0109091121030a0801060315081b0307050405010f05 66
    0x3803031185012401100c00100002d0a1280040ca1080901c40240450740d1040b05500560b003405400391113103d8180c07081c218640700c550807044141000c004280c030100c8228000c907020405d17000c485820b401544c407400071520740585d6030816031504501900860505003001d0f0708000010030400c5c1c0041c4043c200c002051160142c14549004200985019210b510040d82d03170321206108005c9540324042000d025500712900d07054407511038408840701101c3c2d410068000d07100501c200b0481358001ca402c000245048641000c030051000303516484070307400701000d0404601c82d908584910080c0016960018001c02c45a5510307500e090490202c1070011022285040010410804512610210580000d00310119a1800013400070403824400c0c02e210750302003406100f080e04800c1004000390001540d61034a607501d00040581641c00c00c0d01440500300d1204800e000041340080c0303858250341500004201c200000000c01c0c201402d0fa044a60024101000030441e0114016082d040f0f03801900c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 675622068 1250 675620818 675620833
    0x7120c170919140415030503040305012a0206010510020f010c0e15030f130510050406090b130f061d010509010c02070608150f010e04020d050702070b070b180109080d0e 74
    0x20030b82c07507a2601c0c0203109540504011082c0389041590200d030386600c0480a070403466490751690782c81e6401c154401c54140e0b45400390000c08078090a2010b8100700d1415490b41c450b100081c010b9240c04050180300d0013003640d200b44180c0316208000500e80854000000c220f2131504030070003420080c6804241c0c1c06940541004c1d2206103228046a104400204005206464454a0301611029444107803002d20a6904803400602036104050103244900b000107044665850041d086040c002d2041e03080381d8068a0460104401b0f0841a180300da2042c000a0004c5a00070300d401b60412030a0900641c0d0f10785003c11410f00070551204840c111150201d6002c0d590300d4004441c848800c80d02e8158941040b0445c0801d401c2c4045000703081441410305000c44501c02d0041400c9800c207441400c9919115414032a003241c042c05030310003404a050b4850316104440c0c4034074011040180c03074800503401108000744565400e6101c083d4440d40004070940d1501c00e82a800094040e5840d119864001e454 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 675623318 1250 675622068 675622099
    0x30507080c13171510030b16051806220302031e031b120a08180c03190c030803090703051027020a0b0f0406020111070201020307120c1709 61
    0x306896105031041040c081007030070800241c3e00f528403816a40043d124a900a000811003085030390b200b1150701080081c3c0074950300f0f0407a04010040c04e1150b10b441600c4420f00c03007940c002c0450b00c0390070340c1c2404030b1341204903070001c20218464200840710b044030b00d01c20711418070903148011013103c1c0201c0444440e1500c4821180720001c0c011900c40c4030b948104004181c00040710f00709800c0243d8507003614086418140c082496a2060280400056014040200c2200145580c410034042c050081c4007100028000c00c0c0c4c2d600c0d00f0036502a41e100000c0e0010104102588150b01540d40110001d44038200700300741c10364a02c0c481c0405c503100d020781c0e65014414007561060105100c801440c03008406200880c1001d0b04400740c10982e082081d0500106c0c8540c0c0340c034028140181c42045155840c0d141c008002e086580600d0988801001040b403240035030703400403c0e103805640211014000c41c040c40740a40b4158400a002002c401040511040d5045008060f050001c000da4904a0000184 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 675624568 1250 675623318 675623341
    0x10f1b1e0b1e0103020d05030c030a090612050f0c07020a0f150207060e09040627110a0605030105060708031e040b0703050916030602031305070e100f180c051903050708 74
    0x2e001c62400c000d2410042001d071900314400d8034598001e1064900d061480243d190940c0d0016084c24042703070f55580104185a4044540b050808016408000a0416140d411800c0700040c26044032804041001d03401d560307603900030000400800c0e416400c071603980c41880441070984991403001d401002c0300003034103d00501090310030950081c60180d0a5a0301d545080051074408080c000e080000c0b02d1390040014081e0010700164016542108801c03a440201703c004001764100404225003403004002c0c3d80c940405860703600750b1004481c0c0e2259620000d55096541400040800700e01e80414802070151408811380a809030b540c0c1441146e0390042020380c0d1341074a4400840d004903102003000414101e80c09550045a0b1100480c2c9665154a0f100c2c90b00c4880c1c4c1011003e0408001801449880c1102e0213000344121003045980307501d010000540d0082c600181c0c014247c0350078075040c48034420011544000080c1d0341102035001074a000070000e1008691090100304040081120003500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 675625818 1250 675624568 675624601
    0x42301120317101d061201020c0a0809010507021305040519050606010f4404120c0303060b120402090c18010309080f041707090b010f1b1e0b 62
    0x1503111406003042d400d0034030b40036a8005045030300c410940400071500d065107004000103800b030308144003001e05248007040940da1030181d0350a20390b031042043c8079218201082c43c41c2d02c0c3e40c100d86050344442c5290010b0f280d602c2a8080254840ca85071441a50981c446d40030070b010f58082c3c2c08860000180b12080c2982c051020f41c007811a80c08100001c156621a088010b003041c85881c260340c614241c02c582c513000300795101d01b0707013194000039424640780b90400352038184210183d40e10300380d1410a62519182d00d06403c00746810080e0000c1c0c80c0341854080e402c941c0003401ca01c2c0710244c4e40c16106428246d07080c400c0d501207203e46209000300714040003d6081d0f030b2a800d031482d00350900329800700041d4000d1001000803504030a081c44200304600403000980010034211880c403140c03400070008a420a000758000c00d41081c5401c100ca0700c81e90740041c054101c00954141056164482d009000981039650700091543c00c1d20030200121180d805040b6942c6032180c510200c17240c42d00350f651480ca1a1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 675627068 1250 675625818 675625823
    0x7080714040915150b04080a02040e15010b2d121b04050d020d14010203040311030a0926100204050a06030e0d0f180e0103290f100504230112 62
    0x24003c0c0c2d075040d5180c180e03010315149002c180003c2d01e40ca60350034100300745401030342c0041c402e80c04c10310000080d070a0034054000c80e10b07114009481c000d0a1450200d10401060040050a040109000350b14075540c1c042c5505d140c1c40e40d800041d003422401501c0101e0344c01081d200c40b10b0600e00c03010458000301c1c0030000c0d181215502000d07042906104c140020340d0910a802e90303004108200d0040400d10141d00c400d0301084800015980f46400c1c240640a070700300b100d40504c80d038003c00403d88140d5120030000f0036540c40401c4455402c04038003d003100311074504880c2c134050040e8060610a07203071542c001d0048503025030304104102e51324034060302122501c050034000398000f1500054064400c2044407900200740c00c0c803c1000c10071a44c0074408807506c0e000291450300181c014401c1c07000e8144941000b6800740542c084400001d803109480c0800a0a0040c11500c014080760302952003034070320b0000d40005041001500b845100c074203000070824042060a04008001007a140703900c02c040344403241c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 675628318 1250 675627068 675627083
    0x10b0a090f02160c030b06010503010b090108040218070309140d090e13140c090c0721050904020d02030f160c0f0213060303031b02030c120f0c070807140409 69
    0x38503000889010301145071610948aa0030424100c40d00d000301d8968010720300a0507000c064600351310b0316035049240941540e040c0b0000b840108400c8e030311803003111a020b0007031801101e10744a0788041840c800e080ca0800e030212611804006d4200d601d50700071a0441e00400032408032008c0e6007046516025201d419000140a004052260a00000c09250001c91016060b040100c20340c403940300c0c01c040c881d6890b1903030300803808524403071918001058104d898004035514190443d40d419100b10103d18110000070b40e40084000d81c079000320243d5480b03410207401959258244400030300254400c03940701100c040c000010409034400c0c01003030502c83c00943c4a8841c0110251074015242c07402d000101d0703200002c00034840b00c10391a4022000214444e440101d24101850b000410520850391280115442444112100100018820410003046113800c1ea0f8101840c954206480f41c442821450f204117140002c0041c0e0000303089049030340901842560b105254104025149039141c042c2c281c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 675629568 1250 675628318 675628339
    0x4060c09120b041e1505160c020d050106080d0c020a080c0102031c110a03050108300703021212061c051506210d0e06030103080304030e030f012408010b 67
    0x1c0c0894185038002d8004c0355401541c007641003130b15080198800c0211030b00703e035020801d410010303e4050240c100c90000f12a080c0003036940d070000d2001007000c002030311400300006402c003440000e41c4400040c0c003d03102a50718895486034050941c01c0c5052080b8082c508aa20004880001107084440140705034042d62600700d8220441a140081c810712800c3c0307640d9803c030921400240d070002d10121aa5440c04519503140c02c40041c01d029119066000b90541502000003000350a00d1408501101200c141d84131289401e040f46000d020605511140700001541c6020460b050002303886480215003448000d04064040c26140440c1c00000341550f124144000e6900a05064a50b1085014011315111009100d0f03008050801401c5030333000fa00110768030364000742e10181d41560b00e10260791403851945940e644000ca4840104060100844000340b045d40e90f0f405e10540200103003400007880b4000c11001003601b081e2208000c4010040c07800b03800039261406008501c04032000811003030343d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 675630818 1250 675629568 675629573
    0x30915020a053a020610051f0f0207050613080c15070f15050f0f0c0c100207020406030b01030803060f010e01170711070602030c0d02160605070f08030106050304060c0912 75
    0x80c11141200200403002c0da441c40f00d110902d003441c0c9034a00c25940107100a04001840c6d03605510035070400350041206c0035119914000d5004801c0c7d10305000e14000c00200c2e00e03030340e00301d0070216941c006070f03446000054580700240c030303242d40041914850021345943d1841c2808101e40400401c06000001209118042c045580c00d8145410107004010760210350026034071075012241c04441c0c960445000d4000d0003904100010704690003406c84140390700d01104180c1003a41c440076504015901e94000640d44115292600322000443c1c0c016401141941c5034540907540b40c0049519038003845115080c004150b1040d0ba03050000001a150b05c0001900000c0c0305011070001800d400c103010f032841c221110f5540410440e40240540ea02542d00d40b07100040c098207281c51081c0d80421035104104555035039038001c8040040b0b980a0410b1580d035042841d00c3c09007074031182005441c01102100009440d50410f0003540710b0b41c0b08070810002560418001e403900603e500030301d4000032071301100c0c600 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 675632068 1250 675630818 675630853
    0x30804110607060212150910090509030403080a05190e060403080d0e061512070b0a080a1104030f060b0405090d0f09120c0e1015050d1404030915020a05 67
    0x604140a48030303524020b020340720003050368800d4000b041c454910800f000b41c801e501c1c1040c081c4001c8202c400722940c0c202410381012181c9030340681d003041c9543c1c1010510b09241002242c0c001c40d44503171140e032100700140001d080c68120024043e0710f01c0141c0c100300c0e182442070052100400c0c000b07022034201802c41c0c41741026500b0540030006026a181e400c02030b2070b9030411216100d910700b0388444580340c3c903400602c4118603182d0314440745540010410b10405503c1000e94803410601c2c03a240b03802b642d811100002602c40140a41074840d000640401806442600e50b4800350003007500f0b12001400300c0c00d01089034000c4942c880c0035000041d1030200780703108941c5440c11500344e14281c3c0500351110351942040e0b042c50402c4511030320241040000341d500b008680e0f8040e580d8080c0e05003083c42c0c40082c810818481e56000204200002c000e10112455848003894115070206030445180519001e0076100d668082e02d4018921003400d03141780c81c8006a01c05070756074410007418079802402007054 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 675633318 1250 675632068 675632093
    0x100e1b0d020d0905030418020310050d022d01110c030d1d1203030901050907030c1a0d0c030b0127120f050f0c090601110a0b220c050909010207030804 66
    0x440c1902004001c10819042c0200308480d0b00402c00346941e2072802d215050a1a401ca286203003103401032040041d460503e4a000e000c8070710070707104801040c02603c0001d203500d01d030729403480641d900200e100d82462410140007003042c8080e2903449040c1c0719502603030b50740c400c2d91134121707810707444040803141d07075441072090a03240b140d1b0907071810203002c03a50002001d8012216401d0190340c004420070007840400d001c0d09401c6103203840606141402d40e00c0b20901c9003c14040c083d41310980c044034140c40c141e94002c846407100c0b03040041046140c40c0400801800307400c00d51900003440c40441120740c0560019609203028210880d481d650f190403589205003051501c00e540c45a841704005d0045234051046000d400441070203019140c40c203108214280d00701030200e904004c14440400d601300070000711070100030341148440d41f071a0b40750010b1030240082d400b0004c4d11408403401b00d00810914981d136100f80c0e10b0450300c42040d59500303e00c083c00c0b8000c42801070002000880440c01040d003203050b02 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 675634568 1250 675633318 675633337
    0x3080a11070f06051306080f0103030e1c052521050a080f0310080604030509040504050f010c0906020f0114010b1303060203040b16020106030203100c090e04030305100e1b 75
    0x32007000380e40320541070102e4956403050300418400940c501502c0107000204024001c00d040c00c26450401e04995031855805020080c02e0104070790342c150b00c41d0356401c2c403405901580040040c50031541d184c81ca88429111910010790302c20034082c0300045903031940c1402922403900e004c2200e04078288a002610b03020303080c26503e5026060521000c101441d0040c10a50301070090700d5624107083c11190866074242d4050f01e0b190300680300f0300c80003d0b07010003128559082200c01140d030381c4517401c1c03ca003807021101c0300d8040d540c82e02c6901058a50454518011038005400748c9a07104509004142616112a0101c3c0c00c0ea0030304005104281c69030f40a0010030100558020455860b6541e000803a4000e41d010384d078068070307001001703001d8140321014540c3c0c3d956403000b40807051440c1d01190780c071040e0304002c844290300c4484d40c5901078441c9541c0c000408151140d086681072600f4090001c02003a500101c0004051201280382c0381c99029481c050a405242c80c0c0c1215141222041c0780d030002c8401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 675635818 1250 675634568 675634573
    0xf040c090b0705030a1b0b04030e0103020c0d0801141c020d15020a0903110402071226010909020901060807020d030c0306051e09150f040b240310060903080a11 70
    0x1050607458400a00102c1e8032a40c0150307914580c128015103064801980180700c07041060303100f40021242c89036183c203d42c0c1400d00c200304010010043e0068010424113542c5481407000c010580381d40106000c4c103e8800691100340c62141c8000d00281841c180d65040c011072498840e40b00505008800580702070085214a4003148401c000d2401d81e480340b2a00400076994038420b2041c0b0070318002803443c2c1380b4120b070114580901c9070348601c0510609481c17081448101580d400010390341140074108000300b10500d102c59a1207000501c0201118071082c0d0042c460b680001c5902802149041c2c016111a0010100c0f180b15840450103002d52821407001c00d903c2e4140000c0c5034a0380065000020b4408824958a0700c1c0c410501c01350610003820302d150009201108140c1d51114441825158402e46000c00d0207001c4001184d401d018403043d40c0c441008194800030031121400255000e03101c41c201881001c0d5907030004540d074165034040034025500030003110840c00d010724149040703031488105 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 675637068 1250 675635818 675635837
    0x2150c060f010303090608150f060d0906051b0a021005060303070b010308030910020313140a051207140c06031306140702010e0f0318010c03020a170405010813020f040c 74
    0x618505152003a5400c040314080900107208064000c030510001d0142860607184924100c1d180c80c08403080d600d119030107541e051a00c1c220075140c0e00111000b080340d218051003603414926094004103003c03205101c0d44074078040507055400841c0200ca4281c0c030035034010728401200350f00010081c075000c1c108541c1440304010200018000650003802103000d0350306c07a903c0c6c0c503000e0f40715400c1ca042549500345070b41c07041042080d450203e44820802c0b40e0410741d4451300803070b81080703203190410261000c0e00d18415429500142070201c80204001d078400e0407032101106944014903a1010820381003988401e083c00001c40c607503040c1c0c0d04070341c0b02030041c4000b1407440e059909a03a0a004190b40150050751903003411800e800c000c1007202e030a01ca03841d004625000030f407580141d580300020b182c1810004c000070a4001c1c54070801141ca0826084904d003001c01c4400c80004116600507c2014086101900010324086020003444a61500900b500010f0070079031040200030b042042c5802d091118024 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 675638318 1250 675637068 675637087
    0xe0d0f0503130b0a0509010c0905031c120203130519052a0a0b1b0a0f03030213090218120109030903110d140606040b030f0d1404090903080a0b011b0215 67
    0x40050040c06401d00011710341c01d090025500703648604402d40e0511000c0c85c8100503984001491906000a444801219400e5004100c034144005008103582d2800401404030000720f41d98546da031a4841e10807210b1b50b11f1100e21500d0103074003400d4054102e4101c0c904141c3c24002c44001c1c03544030904020700b460341d64030000c005088690542c1101c5114003001c16940030041d0b1174038607000d824101d440203002103901c580da6141c00f05d080c0d50006081540101c1d4030440301f0304900002010b0000d400d8155140c2402c1004100b4020411010502c02c21041113800d404003010f128040010784c1607544e01c0300e41d40c15912201c400410404c002604072500040c4074000c07846114400200b1300c1e910014010609010701000155030714541d40c944290090041c0700a098800a103070481c503d110308101c100320803580c0d0407042d2070080358055a0030609103581001003641c811003051051144240030804d225807140112900550030302c120a01504c8068903c01600d00842440b2100315030310041440d019446 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 675639568 1250 675638318 675638333
    0x405041a030105090d091211280305060f010f06020309010e0a150804060e03030606220b1c050f010b04030303020c12040f030b0f0610080601141c0e0d0f050313 70
    0x12544e4907100d410006901c030006521104000040c02c104482d1004940a600c5801020003201c80c0607120b01c00800d4400e0300c00303100f000c003100c3d80c2c0c411001343e02d002c0d07981e4188142c85400c102c61300300d8002c640200104421611a20b40000c1d5404c99000b0b5040050020041d00d480e203d02900350340c020001c1c0c0c4001010b04402440f038441360000da075041c06a05103450041c054920300000c7d883c03660001d00800800b510b61038140c8100c135275141e0b8480c0c4000f00300d90000003003a60039000f12000070000107080f0100280f0114002441c01c102000b0001c80c0d07521103100134119408c1c0224010880304104c1080441c1c480d0700a05054280c0c5010f8484a0608000c0c88100368010351018003041c405500c1002400200304510b503120707865001441240c549800003842d10310f10060840c0030300010002068203070b4810000e10344000c9801001641d142c4041d800888903a200006411750141080303111518048082400c84420b05107844003003541240d10401e6902d60001408400001e020240d0540401c189 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 675640818 1250 675639568 675639571
    0xe0904020a0b0f04050102160302151b0d0c05060702061006030c03060503010504050109200904081b0604050309150702090414100c0305040b1e0c0a030209031509150103080405041a030105 82
    0x7955443c3d0380c031381c541030002e41401e49000c3c81701c211611040341040035842d81d2481240c40c480c404c04090381c490320024424804090a0020203d130b200d52a100f07a0525000f40030510310f1030040c4101c80c65943c8034a0201e035214011542c201403c0d0700541c0c20400c19000e900105443e42c080e041c04100151288040f07800c580d01141c094420b60f44520340300c020300c2480d02e1001e0160f90040d00d1075034140c900c400455000203010304000c0090b4030018100031092101410344210986403410748041c0d08041c01e1250343c94001c0303030700103200d6141c0c0c0182e140340c2d000100c2168841039014001300101d40d119100c0007403006101000203154050305040380170701101032154402e1040c56403800501d504017800c02e241c048200400754586582080748009500304090944c43d8080300d00054640e59034000c1c0002c9000c0c0c007440721000c1d054401c1881d010b40400702010490f104803070142c115a03d50580c0743c0f03c40602e035030071703c070203811620104800d000505243c2c2189556816807810220f94071b1501e030200b03084072070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 675642068 1250 675640818 675640837
    0xa14030c0f0d1403100308130302370303020c091f1d060a061b150e15060607020603011208040506070506060a09020f0d0b0f0d0f05010c050a0e0904020a0b 68
    0x1001245060301030700605500c843c29240c20b101825441e1000040e0842c2601e0700000d0440c490206484440c4010317004e40f417028580c0540301240001800c4402c481c0031800002107002c42081c55140301007694009512030440303805034000d2411100c00310134468141d00203410010210003103c4007010380300040007000001e1121021500114095466880c00c800c0040c080300d2066400c14020003100b980484c58060076011a88120803640c11441c0c00039010b0b030780103001c0c264242454242c01450501040034083d03191820180d42c060f60f0390b10200183c0d4820610000d602c0702c0144014040342d851050800f4030a88102d109600d00707034036100000c10a800c030300750807105170f48004100005403c0c889401c3c4002d000c8001c0c1582048010000c010440c000c03120851941039071074007010307032550b030313030b0305070300e88202010b00120203c540c581480c070100302500005030350310343c00d00f03014400d001c2c8202c0480b00c02d511256120301d203d00700c0340c1c1001034005002d04140d900080c4d04c4808079241d86480300610180e00c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 675643318 1250 675642068 675642073
    0xe0d240e03030703180b0c0a020708010c020f0601050436020303122e090b010507170316170105040b010519030605190e06040506011103070f1a090a14030c0f 69
    0x20b00340d83c0040a48000107107094001c0d46021680340010035480e40c1a0708041c450707206a844100340c1004a19000144c0d0000e1101c0d070030010780300031082e000f181d403a80070041c070401d03519660f1300c400078042900c84d4400d541d001c0703514102c418050100d02401000c010100c0f01e1401e0040000e07500043d02e90b030051622100c03000b103060f003031200000c6041d280554400000d20320b00b125404c82e440c04400c2d86414807401c99000c0d00c40c6072269040e07100c0d10858030b0096120307a00c40107030710301082440c8031600111072650b01021583d03200070003203018141005902c0c00103595001c907070b03003820240000703080502d40050501c9014000d00b40090308102c00400e102c0459500010250700d003100300310100701542c640041c0495001401d10080e02c06502c465800502520080341c00d80318440101c56460005003910200c3c0400b0510741c0401030070f07040d205110740c0603612100014441400c401114035060360101d0071903015050900c0003c1d01d80071044401c200b07680580c0d0400104098840c1040e00c21012440e0301d8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 675644568 1250 675643318 675643321
    0x80316050312150f1008191404060219020a0c0506130902180306130203070909080712080a060906060e090403050c031b010e060402030d0c050109060f0506010306060e0d240e0303 78
    0x24200129030702c00d120760480d02d42101d009245e001408150024110320010b81000c814031003041ca4a0b0040fa11160492021940e2486c280c1000002900b00301201c440d01c801080807100d03a00e01c0020b10701d045941254414001e5031501080000f02d41c0074600c011f214002e4114006074107455840640740c0d14110702840e014884c424010182070503402415001c00c42c0c80c0b2186480940c40000b00041961048980040c0b40303155410500540c2c007035035000038000542c402c0e0280d00160700400c030305e00070780c200c05082c0001c075110b12a4000380d07034081c001d500000b803040110400d64034002c00342c03903006406070800d107140c00d100c00541821580003409002c00b4000890120f50303004424403a070b01c031900d0154003400c0325060a50000f503c07010220001003c0200010082081c04404c4d480342e00d100e42e1100c010404031000d14072a6000e04412a0741e6400f01e81303030103000120180541414248030900070f101881c4503071151340c0c83d8401041c007084800800b50501d500b0954541611880148031200030040d61079 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 675645818 1250 675644568 675644611
    0xf020c010e060106050a230906070c06020714010c08090111190308010905010503030910030b030d030902090f070f0f0c060234080f0d0b0415060f09080316050312 71
    0x400d001a1300a01c20000f04100002040360710600541c64565214015850840000e010040314000c1080f4a07612020001e4101c2c2004545c0c1111811960180c00780c0d00010358507504240d411815103106404074444461100000b92118010203814005061000f8041c01002c40d09152000e040041800491b118001005141d00020218010f0002c0c0000303101c20741c14040401e442e800380d801c0585c0250100040c0d00f507103034001c1d000f10042c5c180c05000c440705e8001040c001400380480ca08264010036069000c500c9000000320024131410840d04c480c0047d0076404422284c83c017980d10b2040c1004400c0713140c2e1001402c103000405050a20351381034804120780700c4e020401a8140c56a0681c41005400301c040012a004192042c11241000081e16403506442c0e0101502108a0f019031180c501080d01d40c4101012200c00140e41c1682e03600400e00b40402c0c0180d90204407801020826402400038a501032085040c1080d114460701c2543d04149603410804011802921484466980407408003a0b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 675647068 1250 675645818 675645823
    0xe010605030109051002030606070803090a1110080711030403081201090501051012050c0d023615070609080a020a060b010e0d2d051501060305190905010f020c010e 72
    0xa040e085000308244040c035078400e603035035034652480702c01e4507008000168640d81d0307242a290ba0a4202c40019501d161030800c85440b41003403202120481828101d07031019050241c040324030810079845201954486200c00d48480c1c8280111035180d1004100110020b9041c070090101600801c140e48460b50400850300c007904c00517041680111445004024296441082152003021035400013980c4c0c0c50b40d14810700640b043d00001e000a600000c5d6490a070030411000c03942c0300450701600700c00042580080700c40c2c02e00d801061a0b100752403031404a103000211000b4440903200e40c10014400143c0c0d80d441009401c18008213016802802074030090040034011003108480910b03090140d032980000140c51070b440408060545000e9640d610001108800f40000d4048a040416032514080c68065503030894040e58040036481080001034032802409914024032062056001c0101d0400200740280020001580c1c00d42d280c405c501d11f4411284028a14031104600200300c6c540ca4a03401407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 675648318 1250 675647068 675647081
    0xc0804060b0a08120912190809032d1e0705010e030c0d0b07081003213605120a02060d15350316050102120a0203060307060503040f0809010c0b0a0e01 66
    0x1000d40c1c010805545d074030048409200d00307c42d80080003548603580580403901c1c140c00c3c07c22102650b00c007804042072030821142d0b070048402d2000c08a500742d034800c60480015040050211215510056042c82558000c4415400c2c519010701100c8086a100000036120402c2c41000e8511052100c01c1c040d055600c148099030101200c004000303e0f40c507645e1483d40d2400c0d170034402c00d510545c1d8a40119098403a81099140103101516901d2401071007003000000400c0070204651410b000c900007400d030800d00c038815100c501c820054858441d4640a20195900000100102903600c03415260f100c5c040044900c0640070441900300b01d00030903282916060034211070f900081001601c0c040400034000222041c42c042ca0084000c00800d52030000d019016234440159034011030030030007021250369800740d84100c001710700301c603404c560b02c400607685c80c0300a0b02c01401e040c2404500f1000b050011004000ca030a0614000410110070f807186107407101c00f0760714540312a0329400d054411070b00034042c62 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 675649568 1250 675648318 675648349
    0x20a0f0b18030702031509150c132103032d20130303050906040801061e06110309010c0c0e09060a15140907021c0c0b01090c0804060b0a081209 63
    0x214a0f0035841d8001aa595510450201c03000740c0b14400039401190902c02c581d60614a988908a141454401c0c0425500550b445ea040c00c907140c1c1e0009040c090035121604c0d04040c1004034100b12100b6142100a0000b00112041c0004084a02d01503032000500b0003104e1442c0042c0003600c9501221250f400c107284503405442408203001c000c450280001d01042102d51500b400d6a640041c000403540324002c5030321000403540382c40000200314400c5070303006140111402d02e1000198aa000036a03946036011401c900030b0b0b10500c4900e90319409a01e00107030303a5000d900c10a40003952180a4002d20600300d518421035040081440314101c5940604404200711904603d007150416410b070b109040010742c4941305903030711008225501e0082c4010f100d07084151601d11240140d910000d00103d103824012959503000780000036182c0003d20810000441a954855007a191500c0f0000540511089564400e100203000508100200403c0760540444585203032030304940000c00c040c02d82c040511 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 675650818 1250 675649568 675649573
    0x90605010212120708060301180f050c030708031602220902130203011d1e10030b150d081e031009060e220606081501090c0309020102071401020a0f0b18 67
    0x21020383e03a80142d10540c00a101e141000e038554440c0c00280c050410f56444402600c000c900f09000e100040000c5001d071801081140d035804158800d01d81d03104054411520150000d20140a4042600c1c041082c40d900090030039410182c41401040d4000645d219025055940c08410b001c5003407070a81c01542003183c2030708608542c5418807041040800418482e0b041d00817200250000000100d542040391501c6407009030b51400034208070203980d87c0d000940e980c401180024001400521110100500c043c0c04104402041d0f036030107400341c20200401552550310f8166800d1007942030b000d10311500b090004124a07900d403544210845076a50410758214102c00100700c0340c1c000c1002c03a0000c010440013041d14a04240c03c10304010521500054040e0081340c181d08442246004850305980103454200b10070246c0c0c82c0306a0490340e0708a0000d0240e0041d401c01c0000480740105181609810f00503107945034515603030119101c20407a4110342240900303003481041ca11624584091501c000300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 675652068 1250 675650818 675650827
    0x12180613020f040b150706021b06040c15050c0d030c031103100515041d160c03120e12030408040617010f031704080f060a0c09270b0307090605010212 66
    0x3040381c0e151041403041c0190b8480d029940c103501c5059a5105c884500403445484507814a4102d010394000d0400051071000d41d010061448000b0408502032a440783e615401ca9140c164030300700f44601140c1c807000348a0300b0302206d00c945034148148002c40e0700c1940e0000f1104980000a811a09070b04814440d0604c00d10800178884410220340c0241c8008076506015000c082c1100b600785d104940048029510f402c084041c0796694811403801026840c00e500303040080103004503071140450340007074002001950309032500f2141da441200b03070025050590b000c01c8000814802650300503102100d00a6000804100b403603400101c10858181d035a020815070351405015080c500c60500002c0c3c50000a00102c81c14a4400c0c07046070300520140c415203031452800c1000d0350b1641b9088401004072400c041c02c41c03108510410f20002034a020340000c00300803108255410814412001c24000c880e600d01c60100c3c107540401043e4001c11000b400400c100d420203000a0030611401038501043c5420322 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 675653318 1250 675652068 675652073
    0x1090308060409140a0503070c050d05150a060f06210606021f061d0405010606033602090c1902011a0f030c0a14031203090a1712180613 60
    0x2080075088a4129408201d6691505120a00340c9883c814400b080c820b5015000420401001500e501401000031411050b50740060016107001d101c03005203030f82c003d013605024060340c10900a4108005400015025448540c03404400b80280c00c001c0101e80145204400307251502d80e2051041c880010500656241c002c0c041d40d04e4044590b040000030402036080706aa025070f000c01c0040c900462009189001401d44800000c420b0700e060b5515401c0c83c0c000b1503018080e001e0040105140070514600c03200303d4a405685015084407000c94074406e26452026990b410340c12801000082c5445580751204410200c51070078214195081da41000e45484080904070589000c001e0140c07860702a020740d020009082c001c3c22819958404081480841d00c1011540c800740410025012100d139500c04941c01001400304070362050295010081e074800107808115240280003031007018604105c8545000030481e0002c44982094032070b8200c850001001c1080850341140241500e40c5841040d82c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 675654568 1250 675653318 675653327
    0xe1501020715021002030106030501060f0201051b071e03080919020102070b03071709030d2d020c120a0e0a1d1807180501050f0109180c050d0c020706020f010903 71
    0x912400324424050b0202d01c804034002d008440203c8502e0004555941c0c49490240040600380503241c0084c0400051940d66401417240d28001e045050304042d00700301641d05c119841c0d100400468481241c400f200344802101c102c1524440d10a0302c5480c41450803031205881d00c4401700000d0450a600013403800541d8002c01d80101b46c031002800700ea03903581c40d1003064551200942034001d90720038101c1001184080400506920982c01c003003804403140c101300c2c94440c01080080300751a41c60b01a1a01301141140c1c1c01042401000c1056407400c103003070071041b80243c00900c3d818000c6080da24000c8514548208031401070080c1c000001d1030701820140003011940020100c1018841c208e1001b024040201301403001040c0000c812601656084200b0014007400e220341806032103085908041580101c10680a4407079909580f1400c400543c0c0340c4c0054064900c544090180c04c000121a00402d40101704541c1100d0b0003c5c181c06e40b9044009240c0141c0005a10890b49441d40080001303a00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 675655818 1250 675654568 675654583
    0x902040e0715031109090f181b0d02030a0c0902090a090608100504240218010203040605450312092413030b010602060a0c140a0c060c0302040e150102 66
    0x3e2400041d8840000e542074143d210b440c1c41164448021000c020142c40c1c12104540b00c0c0d225141c02180001c4106521655171144030351002c000d904185541410742000143c0540c260b000600700c0b10440615201c450300d050040e049078441236000601e909940c00c0034614040140601030f8100041440c015240752604641401580b07441c3d00d03240450180010046941151505844000c1506d10803007034007002944409000001c0300300c54104841658000300541d421921307640c9465140c1030141c1d40211914000d000642ea81800034141c005c011799034005803400303001c880c3c02c0ea800ca810107582010320307000080c607840e007040400300107020080c0c5490030290314500c0e01541016000c02c2c4e100d4400603501540664a607042000320002040c4040c0c640041d0403100307160269034994071150b003048240d80044221a0118680741d20070205a000c07400100500002d03403500140701e40f1640e40d0b41c016101500c0300200000c1c1c000c20140000304501c926203410601c03411140301e0740c044a00c0045d494485 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 675657068 1250 675655818 675655859
    0x50c0d0b030307030f0c0609050f01020c010f0504030807080901020f030c1b010b0a14010203090405040f1403040b071502091e030c0613060c02120703030f0e01020303070e040b01050904020d0902040e07 88
    0x2c416140306c2c05c10031350303401c007040030350740300d41074a411501130100c0d94000d400140d050781d150740c01c010000d203440380175104032405250142d4030648241d480600c10388903a0405070610011b99420025116140300140c080c60262094604003035650507480000b500c0300100001401003a4980f4000c0c01702581d0342ca41c02c00c201c4a5003580c19070340e024080e00503819030107005000398205081c101044100108040c0140986114000100301c600c80c4254088e52809a4082c0c242101c1080100700003103003103840104001280540d0161030403441002281c03803d5046044404011032074101c010b107a150600190080c1501a0307145401c20002c900bc50010756440d105540902184008000640d250360507803001403074140c0100d41540b030760780c54020f107900b045c40c03c1e5400195600e01202c0042d840071044a01510041e900d81301001c0c122410800107203060b0101e0350500c541048440c485845030300107891105042c80c4000746418650040c802a10062140007a16401c008414072143d035a05001d03841c1c1c907c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 675658318 1250 675657068 675657077
    0x906121506110a38070e0103020702040e031c050c0f0414150c0c0a120b4510060501020607182616120f0c09050c0d0b030307030f 57
    0x4404030460805070011806001109102c645180051100c08256040c90072082c55000d10280800404e04a00c1c080d2a828001035202c48950900d600c6500a007140b140020b100080c030760040021a491a804200c00341705015503002e070f8011405c064450300358080009180c0c18175100010840c20201e100da4021040c2e10081c10b000850681c4410084107d0251000551541c0d5803801c2b4001e03a80c0da01444109101c0c0d1090a00407440c80e00030501290a107511100071007040d04c8a242640b02c0d004400790310303500004c40700e0f20000b0350410549544040c0000c41c01c400440300054080608008202014221842c108181040141d90001c0c0c1a540301016281c50407000d0f90039440a60b8000990380520040d10030600200e0490000700001480d01c00c1c04811540801000e54144840d02c42c00e02c90001580048100c003004602500303804414540300c0c41c04103c2e03054545201d402110415500880c024601280117103019800e441a242041001c600840c140381e00c9a4000b01308100c2c18145c0001c01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 675659568 1250 675658318 675658337
    0x604230a0e060c0403060c021915240302090606032502030f040e09210922050709080d11030301060e130f052403060402060c0703120906121506 63
    0x81034540c4410041080c99066403140c0c1804480c034500d540042c08240d0f010351401c5800343d2043d000040c0e01d022180f2200c400c01c0041f2240e140c0004034018079050046058903000e40444100e40150020443c2c42035004000e44582940140038010340c000340018040c050400c04d1049802c1d2420703041d8400f03800304200080b03400803003404900318028030000e0302d0301a02c08034000c50301940408805100750001c60032245803410310400d1910518150601c60011041000b4005890038031b00510444001d44002e80801400c04000f8607003200c10449014002514407241803154036414458507001c0a014a00311841d2031102c502e25859100c107100307080c14407049400f0200b4607207400c0000301c40300148013402c1150032000c2040602504089440c80b00404094995029101d0444545084180041c0080c80d56903500e600b1b2201725405400a46000d11a02c0c600200280c03c600c0ca0742d0350428581d4a00060360f10703203103024040320620700354140b02c982808503292040a0035030800c000c131441e03440d004600 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 675660818 1250 675659568 675659581
    0xf06080a112205160507113303070f020312061e18010e130c03110d02030f0102040305010c0f020613063b01090302060705030901020421020306060423 66
    0x1020318001e04414050310200c00049030038525444140300740b0034036103141c401c4880c440341201c40c1e100d11600244400f4801c00341c50b00d01d00740b05d03030100c009848c0050090301045080c41d4120b844110302e0f080c008058000010044403e074002d10f01c140e541c030240000c41c109802d080300072144400c01007940e80102d10038880d19106181000c40000c0c0e01101400d4401c20020407900321a016a00340940c00806044401103400c002c000003444424641154040302018110742d82c121599410206580d03001000f1114400581d03010710004243d50303000307800165035500c0c51502d2800d40d407460080c281402060101d940d05190041840c680c44402c0d00c40050b428203151612200030031682400075186480c4642c1d074541441040c64008014540703030f0145800001d100e0401d800c0e280e480c1801801a001071022a400c070b4018005560002d15103400541069221032a001c2e8582d0140352a41000306014001c10a50505002c202c0d0030210585050145800004609a1420320b4111082c0c13049414030000d050f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 675662068 1250 675660818 675660829
    0x80a0507060c050304050f0613170d06180b010c020904030f140a03140f090312100e0c0304020f0f0105030c090406050901080309030708150109091a0106120f06080a11 73
    0x20999101e2001c100000c1c035160002c055400448046950b407040c60b110b42d02e0703210001000c1d44924920078009509200581d0340c1000d101111103d030004200902c010808110a8000c05001c0d2684402c3d0312000c0c40c16282c03440c00d42e412100102c1c148800c00d603840015072180f40240741c2c0a9054141243c1c40b5070041d03011558081c0d41c03248987e0842c40811340440d4598190416032640c000e105503400240c503805600e4078217030002e80d030840d450b0340100940000f940e240e11240307038003100c0e100403c2540c60742d400da0801c06450132980d0b0840c04800008000840c0b0b0011501c440300c040c2580c248130802c0d0301c0c00006e005844060400d12a1400c08140e126403a40c0d01e401400241c007001d08400c0031540e4a40d40070780c1c0c0b0382141101d54468041e141d00402c0c61200000c00780c228001000802e10541d02e00f104040050900380300640d0070b00a04002d015100c441311440b2030082406a03115043d2249124450301155011640700103201d08004c801c002010300000c104149d1030300300083c0c5000c1c4061000003030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 675663318 1250 675662068 675662077
    0x5120f070213050114010203160b060105040b18121b040203180f01061a031e0703020d1b020705011125080f03070201120e032b02070503040801060b0a0c080a05 70
    0x942c002e0699414030001803150300058101c900c55051011804003034401645c0300c0c05a0500150b0007a41824a0f4000c61a0040095048038040c1420761400d600c03200c4410f83d99000c0c3c004400e18a804101681c4503040940140341d4900182c809418404000004958100c190b1254544980d40110101d400302035180c6030444507090000444452400050035680030344041e2040445004071408142e400c200e41c8000c480c840d451448200c404416144031a18041e4006400c0000b00740c0d00348032412000c001845010030070f003030018a000800540102c02440d05d0810741216042046900314083c00400001d201070702d0040040c10031031400003c211648460440e54480d000c0f5201e040c2c0c1d00140d17100c000c07004140f510300030f994075068600340520510a80b072502e010340395503070700410903200c404101c3c48520901c0c0814406202c0e0301340c40c21503440180d8102410640741904001010410407109105003802800d800303141c1030030070b0104203018016000401001d400c41400041010300e0030b00c50b20888 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 675664568 1250 675663318 675663323
    0xa11090307030f1b0509190207060906050609100f180b1909050108010b06070209070e03060907260a120e0a060c020306101809141c170405120f07 64
    0x2991601e0303590030601c880c1e0f0546030040d42c8107200d914056081400d11001c18040e80c601030084c1c50750f074645010b4504610001e100b00015a5400c0c0907040015041d0b014440d500c0d80a040c0100381410811b0401c41c0e43c0d84081c1211702a030100308400c0107840c202040040444000201110500d0180001e90001d842e80c5040e82e41d01c0040040c199800703d008881c04001e8601c06541000681e88640c01c5500300e6400394200d5030700800a02102c001498654001c5922107401d01e444c4403040306540200e890400182c1e442072042e00411824000036026042404d015180c01b00034000080c016020a40c4459100a010b4020f0301100124006203000e1aa1090340c00f8000c0c02c40d104d8140d032010b0041058600340e9040f4400d02802003c20044c03142c0c105030f0000c0d200c41c010034490301d10f50f4903001c40041c0f040060444151075600c1105200950503c01ea040000d99051041c121006183c002801500b00c4115032810b001002c01b44030114000040c8461014801c1020340d81da9443c0c0c3c0c40008450080e82c0c0300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 675665818 1250 675664568 675664573
    0x180b04032109530304050f1512070e030c09060a140d12081b03090d0518030102071a010e0403050316090503030703021501060306061202030a11220f050102060a110903 73
    0x2008038110f43d2030154950003080100c10001d840c85928642e20391082c0d100d0194440002d0f0302c110f8091400c1d0030004400249200c20346d240c400d441d62040c0b41c4a8080360f2180101d40c11010549450a05200d241c140a20881d181600c92074404001401140140905000c1c808440b5000400740c580d454aa0b03141a000403880440302642c4800900400302190740741d202c4074100d501414100140020b07207005107082005031100c84184141164250404031221000640d500350792000364034288014054280503904480070703c100d00402c44507012042c0e2041e22024544810000865802000d5030341102e000d000c64280203403102c204841c02e002d1508a01c0c0d06000003c0e1740c1d02010303000580700d04d8040240d22803a20680e03030b41a06408468a0f0722802022036101c1003a00d40d02c00e450340c003c5510410085000500d44059600c01da215048840c0745140701a07401c119016114045030140001d00c1a04100fa9489061100007521041c01601d440038082c0c0703179001c900c508070bd01c00603075a002d54003408 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 675667068 1250 675665818 675665909
    0xe0d0f03022b020f18030d03110d05420a06021507120c05130f06020a0f05100216050c040b060706020706060503030a0309150c050708030403180b04032109 68
    0x80103030543c03401d240c1501c03c1c41072547d1191a90b0103406400c40003491441c070a030a0442e000078400c0501030081c5904500744960215900c41d440f50080600001d02807a01c41045000d0a40241e07048817403912030510508004400304100c0380c1c009903a1524424003071070221980c450380402d69071842d9000c40611824182141c5025065100e40901034010040188030b07400342d83c40c022001d411185009000040c1c100240fa00302281d046c161041c2102d100e00c04a50507041414010800c0341c000e6214402007000102030302060010030000300c0d00007801164100142105200003d1080c8038260f0000d06082e008941c6c00140320740b503071080000b02005000e580e41d42040e00002002031030f86100031a0680b0100005211080844c8100841540e068139401e2a0846036200c02203240c00060044003040800069092000082506030000304410031401c0e071524154030b88610035280c00c5410a10704824401348454055010104904139402c49a40d03003880d4002607100003c00090703d4000d05100c400c0c14 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 675668318 1250 675667068 675667087
    0x110703081c0c200f010c05071401020309030d0b0d0f2306060f1216120b0a051e100305010203090c0406050109030b07050a050d0e0d0f03022b020f 64
    0x40c01004400e80311008442407294a4280d482292002584240011002c1200c400c0c0c40320110540f1008030f031003900b00c0c0c1802600a1a0f282034508501c007907000124049600d00030480c1c545019440c86d50400025425441d041c03404580e203010380615101c2050f1a10000f5101f5126000341081c6140c005615011024241c10082608201c40c210200c0400c0d0080381449034290100c0c085018500050103008100124000c100820680500b0000c0501800a454084038100d1041500922240c200d207103c0408c103041c489101080100601e20b098105810044100d81c0341000050030b07108104c0d448400e03290512402141c40a64000030519072000042c0107802c08005500d1070480801c072420711030310380c58000444082030184001050002c0c014081580c59000e00d0240000503202e00d08682000b6280340c0d0941a181180085145600f02ca50602c511079400f800727080f114946401d040d481c0c41c200c080c0c840e101316017a00034031030034084a200f0789d014086203070100d800c2c0080e01c89007a0345805034903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 675669568 1250 675668318 675668333
    0xc0503150402010e060f0301090e1e16170a0212070807140f01030b0102060705071b061715010c0f08130b0a020609010b06040e10030c0810150321110703 67
    0x2a9030582c080340b0f84d419403102502e0302d101210500e5244011150450f403800382c120010f0500d03038212030ba03240580008481400c83c01011a840c0b080124010610b0303444910320704040d45515007202084607907158802d2902d10380000d094811541c10381e003910112030800c0c0d100d410400c01d0780040c41c550081174400107400168400303400e8000000c903900004000102d00640c2220180050940541c105900294000740220050700c10140a400f904510b41000c0501c00000302d89600135a000c00d0000d40d900065420305c0b2030007544040f000c0854070305205e096001900103d00084002c101d0303e040c018071000c2207484802e54200029007038603160800d844400c05c0340c841e0401c07141040107105030000110724040500a02400c40405030415240c6800d0586030110000002c0c1001c002682c41e0b0300020004082c41c40040041c030302e50020706202484002c82505850fa8805011044a103180c014000310b419a444001000451106181419503031541503441c888400d007441d1803070092a00000520020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 675670818 1250 675669568 675669571
    0x306080d030606110102030601021f02070803011205060f0f0619080a030f0f02010605010c0821150a060c052e0204060206010e010e100b0f0d150f0501111002070c050315 74
    0x4544580d0308240c0349001c90b17800c0b408121101e900580c84000d642d489180c4c151003540840400c0c40015281000c20348444281e0b500a070722441c111820a030b11041440018015203400c8500004052b10500b030425060038204005800c40d44561008141e400600000d0040100100b00c1c51003650f009452604000c0d02403001200b0350004034911040f081c0c0b400e03106104d92419203005031500d032113400703890310740c40141e4001e84508076407117941d41c1ca0502c0c00c00f441280244a030000f03001000708006542c083c8183e002580d0300207014030040a41a000051b00410482c419450480a00380010780b4012419408806447c00c0010a80b00150104143c2d80c0070850905881e69070f00c3d0540c0301d03680d510900603102400c0759150328505640d0f1041c05108045801000781c0b0100d9200c03541420604d2490200b00c07070500c101c03413004601c5d0010400c1055001584440202000d0170300c000c070303400000140ca80710320340c51768030a103a264002a01c5041001c0380803400042c1201504452070b40c1c001d0074941b80034500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 675672068 1250 675670818 675670829
    0x305030a17190b06070f0f0c090209030319090f0303020a050118080d0c030204180516020f10090807061b0306151b0c05150717030402100503070306080d0306 69
    0x1946610500091048030503540540c2e407221a440c0d1a0940449060040100b58a0294801e13820809035020070800a8109036450242c1d940d46414441441c2c0401140c40d5a442508030a0042c0101c1d1031b41d40d40407058440f0825a45200040c440001000700e6101d06e442d00b100c20080440100807051583c00034040e100300d031080d80200400d4a260030004100841c0e0140141110001c021102103407504d50042000f19115040160501e41c59800710304007105080b110100303081e030380c80070032400d0a00300c0300f074030b80c100058000b41c0a810382092005440d0310846020f005440e07200d10034001042058000c0341c03074864200d00104809680f000b1401c603801104103006000078140440840c01480740202c1c04c40154158445d492843d0314035810703080c0c1000021003610107064480d4001100c0d143d400b842101443ca0205140e0340e600ca918024180078030403481521010400d01c02c01c00141c40343da0054840311001e06295440e60756001045014000c80c2c2c01a82003805201e00f4250a940c041c0c0140040e206d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 675673318 1250 675672068 675672077
    0x3080304030810030803040807140d11060c0909060d0f15020c0d0f02030322050316050d0306080c0904020409060e010e0c190504110f1305120a020306010e09160305030a 74
    0xc0b0342042c2d1181843c03603400081c0a819040010500181c1060010038034148074030307040c1c00024030450445040800112202000c580030502060baa10003e00c070840e485414140c2041c2803c80c0c1c40045204850000d204070b01078249640c14030705001c644403280f1040d0723078403c4501d140d2004110180700a90090180104181b10f90a94130006501410409550303c0d80d81c1d0045055981d4400c0e4a40b0060080c40303078070100c111025070704020400c180300030410158190790f59030f415103c903d0943d00d0b0500b5250036408052502c0c20130310140301c6c04615100e100c1e004503451340fa9070315140000340040c0b01c0008010700440c5003801644c681c000642241035010110300640c4d184010101c1440240880098104440f01301c0c19424000d600d0603501c03101c0c182000c990394609000f10000c1d00c0749654408001231201c00c1d0410701c20402c500c2c205806000b18486200900030800155020a0b501c0c04107014030580b0355803480008000482c2013014107010318201e2034244a280ea60300705a52641d100010090008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 675674568 1250 675673318 675673321
    0x140f28091b0819080a090302151809010f180b0d0b04030f170a050414030301061710030f120e27060901080706050c12030f060123070f0f0c030803040308 67
    0x8110214043c0040342c2d04038082600d8030302070360700c1644603440690210f0501c15030100c04405030722403160321081540c654404070b07a117000c201401501d8854098450344280b944400600508081ca00c014044804003682e243c0344498524086015101451b811504001948269014000025400d600542c0251035240d070100f030443c0100c812982c4143c060a040076500e02044003020035a203e80e0348240145500e4204107900e09403141540d01c03c2c0d004034000340245403081704085071300e508aa0407201c2c4001066801d45142d070303140c0000c05000c00141c05003030802c0d41d2203c140d006000c024285074004010204500e030004078034120300f45002030410a10080000a042d5003010b21006050301d9a2000400b80b040c0352a408171100d0f44600000c2e100390013241400540a140c010140d40140c1100b9507098041c54140001003c00119001c90030241d1132500c13080d8401d03404141150381c510303081004200d003030340c0c14104989401c0c0c90742c00040c007444041c10b0010601c03441e0000740d8055446a600d11059 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 675675818 1250 675674568 675674579
    0x1020a0f05030601170a0b09070c1205160b06190902070c090527010b040612110301050c0a050703020f0a081312150e0c2101140f28091b 60
    0x81c0000c40d01c83c0d000c01d60040301c5141c400c0d02e03c2050b50b803045c11a83e0104081440c07202080700c15070706556850200c0c4210b81c04208100e03003141c1541c40c081c80751401505001e06e18004005101140a003e0140c4400001158042c0c91300c3d03040003902000d4001c4580810b543ea05144002e5008800550348004103020101d81190b05004060003402190314021038000c100c6c440f034401082e14994a41d4a40d40e0701030f0221241c0b0b460140754001d109018903000840518100303895482400410030307100c0c0c0d00d4038080003007000100741594135180d410b25080303446002d18a4143e182c0161a010000240700d1030031b22a00300003501005041000e942c6640c420802c3d0f40303200201d070040d000c1c0e00061401c0d07007400510400d96500d90041711a10151800c5500070208900030070240c0c0343c46c00307018028071200c10502800704003d004007a2001c1e43c540d081200e0b45031180c10003c03424400780c910382c8811101c12242060398554981000041c43c54a400c1020640c0c600e090503032031030400380100c244540b003000003c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 675677068 1250 675675818 675675827
    0x8040602071208040317040317040f0b030412030b010c06050903090f01020f030913090b09010c020f0d1d0307182301030203100b0402040f120506130201051b1c0201020a0f 75
    0x8240350f025101c03500303003411a80c0300c40b41c1100010345288865010b01c0000045081c6d040354000e07481c440040295104d0a180501d4501c44a036080341c0030325042001480001f030035003c2041c003514440c0c60002200001280102c405054942e006800e0500f04014003054542c007000802008000704e440343c0418004200681c5c41e08241000f140e940d80040c0010420380c00d191406102c100842d03c40003034202010751728110703519400d1340c40c080c15a555004144c641c540411442c113203444039000400240d480d0351401860420100c000d01030407503101c8000c90194504220080280c4219410044a0014090074100070080d068441d00c082d40c4113800a18400c40358000c0b075050740d4010b000303007e0f10b00243c6d231103030042d0908031400c1e0381080c1d0030400020300c82c044411a4014180180c41800c401c00c00342042d0b4500300015002c0841c1404c1d0306809030042c2e0b00101121205240c800603c0c1d6100c10701510313a42031451106241c40200f0781d4200c030407003299040d8014500401c86032184828050010000c58 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 675678318 1250 675677068 675677099
    0xc030e031c0e0f0d08101701020702010306060336050607021c0f12020714030c070e01080606090105010c060f14070815032a030d050903070e04030c080c0c0d0804060207 74
    0x3c9440c1c2045002d002c01520503004a580b180c1c0703040d100050035070f9500d00c0c2e044440440c007842540e654041065011580d1500500c00142540d290600c1050703e2103c03800380300a0380004103d150940400448a1075010782e0004070600c0c2c0140940d0200d143c240e4001c1c0d1a042001c14104144844800380501c1ea0700444021601103241c1d691411000d0404620320025481040c083d00e209198510006c011102000141040030020019012041c075103521522400d0341a005051103800004c01c0059580313454107041d045920174a0260083c0c0c200c0d08140c8000c1004e45030600ba0103040000000c15020343e102414003d10f140e940b680c01e03940c1c2c1c01d00e02100101910040d542c4c190031001c85101021101103c18041100003060803000e080080c0000c2d01d40b00d900030318030000c202e010842034200d140510864000b0061690b52007040e240558004207581e4600100a080e1903001c2010100100c0801c4440071805010740303081050940740c20004001e40040c424032006200d0024041400340100c4003e9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 675679568 1250 675678318 675678343
    0x12020315040b0a0c0509030106080f19080f090117010905040209070807080609060604091505040b010804030e060d02040905190b01020c0d0b090c19090b090114040c030e031c0e 77
    0x8400e43e869030860740010742000242841042010702000400e60740a10400004151b08002480c055400e0060a4100402c880c0b04110344824042c02e14007041d00501140c800301000d0380c542daa60403801d00140c500311200841c800e6440324003400400c2910f03940c2d02041c0964002c079880e4140b542e0382c02c1c2c01c607100c18049919100141a17a408201e80e400c1c0b03458082d801c000010705a0741025103441100e422508003030803416103980c42c03407410402410140314070390a025003131070f00000c90f04c1e15850140ca50542542401d009960000701e12076600e60550640b00505980b120a011074144034140400303201000b0713070491142e864050707010215800015800c410080c05000448070290a0300c412400c0340000f80200b20500030010a801e4981c0c60740360041100c1c42001c2d00b2200c40742000c41a404503007900d100715019040c80700042c0f203c081e58203c5501050004c03180440c3d080500781046020b012941c40003170144c8404551408010080800c00c480f029071034000f0495071010200c09590b80c02100c001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 675680818 1250 675679568 675679583
    0x60106021e0a2414060a080106030803010b070c1710060b0a09030204270308011505030705030604020d06050a06031a1f1101150b070308070c02030309010c06151202031504 75
    0x4001890200000079803c80601d1103110000c0c5107002c92040d6032400251062a40751201086100d103000200d480c0501481c900030007800c0c4c2150ba9a00b1603200600a103403102c84081a031000b00000030b50030802800b2803510501e16072803071443c0d6580c0d907002c002180781107609101e40070641c2c600040c2920900320781c55032440d402c01e24503001d0000400324061414070728880c0803403421b8054500260004494400c1d540c0c41c61640c03401e00031031000d441c44101d6070104042003090000480e44941030302d41102c000c84005035243c6c0c050310804002d010a41c0400d4021410100020f1419019400102e905080311030404104078481d003040101c800c00303408007011019560f0103070841c9206002510912004000004440708000c504800c502d049a000303c0240030005601004c250380907480a40140702424024143d50155000a0700c2c3d010b0640d101d4100070006c0d45035030502c151500000d03203040c5d456034414044c3d512044440c40720320001c48168020712913080d40401d001800c0130340340d01c187d400c40c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 675682068 1250 675680818 675680833
    0x270b0f031002091504060206090609070806040b13170a0311190507080c01050c0d0e010507080a02130b0408011a0d031e0314070e1509061207030e0f060106021e 70
    0x5800c0000e403c56482c8a8005082d8400c1c0c05114242000410140201d6002419140b80c2603c01514180000f0040c2d403032900101810010303603070700142d03040c0c006500c2410108a07039209003c9400c2c9d050140c0018240e81184458180e90070078540080c281c03e103040ea001c3c400381d242c1c01d000903080e1049800305407044050744907210b01284684081c001461090400c14600111030040368251141590064407240b0005512522400e00c1d10440540500f000001c1c0024603005034041e18407840100a0000243c000500400030041d4080b00c00c060b00201800c1500c41d522401204c0c028410481940d20001e20300c0003048003440d1a2900700c07910b50385036848002a2080c01842d0b140340072400e500f00c041c50b0711032810244100c88051120302c00c210f29903e412600d9203050810405415030907800003142c000b041070207580d4a584085a0050640c42d0b880c1f002915224011030050031a04000781c5030b4043c1d01c4549019040102e00035048590b2039007100d054001002103850b40281c0802c0c50b05443d8015031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 675683318 1250 675682068 675682093
    0x20c0a0e0f0601140d050a050105100503060108220305040509101505091302121e1e18060408130b0a050910030624030f020a0c02010810270b0f03 64
    0x80402d500103010b00d13100e00441c1d08031008141c5604444982c050b401d0b100c40030000804040d219450040c9012a4080440c11a0100184c00c600c4090207550401c1640d1000603440a449106001202071910841103d01e442c2d040c003e0240d000380c028588281c0e84000400c8190711b0072021401519005c8034105218000d01c4015aa00c0d0b0260440c01d802007440f1500d00c89030a020f101520848028000c9c03400300c1d01c2c102a040f008031a21484c80b44520b6282810311426800d610b502c14902400c03841c0c1821a070701d4190882ca005220300724401d00c10310800041000f002001c401524150207030300c0500c802c881e264403181c03549009841e49500094014403207610546040161040c10440030f00f0005003164407003012000005900020242c42403444016407200b43e41072282c04020104d640085080050707640004201005000000e4100310103200032405120500c002500286460301200360000303c0846800407515140d00746110503842d02c40711171940d00340fa032800c03094160000c002d01030284126 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 675684568 1250 675683318 675683341
    0x1b091003210207090c051b15070c1406040302010b13050408030f280b030c0306010e010509041a04031d0108100915050a031a060109140603061f0e01020c0a0e 69
    0x181c914011841100c10000e0852039911401c2e01c0b0100e0fa9807210b80d0340306440115806401103420440165000d41c05c0c0403c0d02c00010032254000d409440e00070480c0f802800d00354034400c020b0190390494000c880c140010142c05500808695000f41e8010380000c0f0b49602600c1124001c8401408501040001903000c0e1044400250321a0502c000030b161503081c49903c0080440c100921f0750025500d4485141c02e01d0100921954950120010143d940c10b04002c0410024184035040c01b506100c000b01e0108101c809841c450030b80e414056811501c0d05040003000300402c0c040000980701c591110401e5944a80c01c2240b14250307101d10a088286003065200082011499050400800f034501044903521107059400541c02034807402032030707424400e03c2280c002019020034140f0103c803004000080781d00c0380c0803100c040b0844001e620ba030b84880204004180000c075403140c91000c003540954154100c030410b403050350281d00300c1d10b01c6440d0031f0510099400901481c510302841d580010805c0044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 675685818 1250 675684568 675684623
    0x80c1212030402150c15010501180f090207050f03031e0c0a1704140a080705060c03010821090607060207120f12180803040b0117011e050a0e1b091003 66
    0x40c60382280c80c00d02500452418500c500300010b10b0340c031b0100c1c010495036034400048800000b4a2028000e194035011440c042200240b20700d00071183c01081c0d00080c460284403901c4214003038810380781e480c82c100510481540401d041000c80b241450041100c55444105030340c011300c55611081c0e507580d040845003103103120081046820720101d0200741c00d10581842074810b41d0340f146030b03040d0b12401c0d03600d0982e0500302c0040580c0f02281d0f00f800100300c40c1c4c00000704110080c444078002001d5001180348004103208205400c0e0700301d0f00010300107042000030f070f005103980c90080600000554030f0000417100402210000000140303d43c1d1900000c6416610a030514032418012502e000d802e961021481c0c1c000722019140011508010400e038040180d1504655888000810000908100c1c070741144d01140b03501440c4954640028803c103c0a60260541010880c00c440b00350016101d1451911040c4003500d01400217100030903034a241416034201541d0384444840c801c042c8424805084940 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 675687068 1250 675685818 675685849
    0x140c010e1c30020304030f0b0907030606080c090105100903080a031b11060a050417090102100c030c0f11031803011811040c080c03010e071b0302061b070507061404030c080c1212030402 81
    0xad9903400000042c1c2911603000101684005888065004000c00003070010503482039002d4a846520269003a5110010206496200070003985075002440c0480003071040002051000c0354021180d80c020307400050300304c0301d00000421220700d556044030200940e8010307200240b01d903810780d280711030702d44400e0f014025444d0188100c4622900034621141a01c00050a481c00f1a42c0e40180800940d0311030b030010900e4541c0d0409842c41100d500c0b810b0341d41d21400100c19001980c900030210103035400c0d006204202c10075072016100c100642004101e0f258042c05192196250103420012940030b951000e00c18441110010f08581c0380421450001c10020104d0b02042a03070005001c0402c094031290201e01e0199000b84041c1c5040656440310400758041c4d901e1991003440454002100064001d0544440d840d10400c00b407030741e1802c80b602d8000e40d08010b00c6444a52804141500e0000ba00703681c0380c02c200d0310018030012001c06070351501d00e110916650000200009030160600d100042c18416 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 675688318 1250 675687068 675687073
    0x331503080d0e100605090c0a0c0b10080d1701051909090f020904060c0e061c09030e15030f0703021303030e0607060e0307140c010e1c30020304030f0b09 67
    0x42e0500c1041d080c14403071421070110707503038809042c0205c0c1850058a903008050001c4146440303645000503010740e0000384d00510381d5503002c0000700d5070241113582c88000c100c0701c021110380c00d005a50192664001c1c012401090703008000002d501d18101d800c2c5c5c2491814820080189400d000d10039015000c0c1c100c09448141c00a10000c0c0141c0318a6a02c6215500413440000c125003103076001003241802c0761003e80301d01802e0000c1070085050300713050308080c0c0324860005254005803070262007000c5840c4078140d1250b1056201c019a01030030000b988280c0b420b40d558640d55441110560403401009010100048164001c2c40001c0c0580700317000341d20b40010006c84c2050015550001580c038100910f083c540c2010644c4800c120301d14070024410003401024101170190100000c04215009500703070712891810040204800c400c0c2c0100701e041d80c010303101e003410901c0305800c110014442c0d058a50070918020105050341d10100503942903aa00c031005002103919511400210640500000c07681d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 675689568 1250 675688318 675688331
    0x604081c090f121a040323070314070c030b090d080c03090717100204091a0d05031e0715090201140301032418061508011509090807331503080d 63
    0xc0300404c03107403096209a070b0795402d00c042c2180191314030344020341425071000e044c00307c030b0000303900403032180b10200401900a403550741504001c03241c0d07401c580c8041c00140400080c080301d402c01041040146030181c07a10b20b02d036180c040309003025100844401ca525045201c09119400c444100c5150500e4003904480c000d04044007100201c2c0e000b179004074030043c1e680c1c074041c5030460000c080454001c0c00700c4514140300c0094840355244e00c079411409400489041c5504902d801010542d41040d400c598440c03201030000d06c03c0001000c0c0030200340c0c0440d88035a10012255a01c000b200d0503203030f20160f030006c0441d1802070340f00d000300307010250b524942d1180714200b4000102808090420300900004c5424048981000441d04860304201d0181c1d04005401c5101114602600100c9035203d500003030008460038050b54034002c00c04001e19500301e1011001040c040c207046c010000250301d480311304611480d905c1d981200c42130030100088030705030070003080170070641d001600c01c441d6208004643d9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 675690818 1250 675689568 675689603
    0x7060b150a020d03050c090a030308060103060b070b040b0622091a04110f0105250f021305060102011107050613061d1606050a0c080906090604081c090f12 68
    0xd035000541d590005034403140c414280141d15004042e00925030f140309625001811000c2101d210321030202074140146080404d801c0c2c0d00c81c0d03111000030410b10325041c4d105c40c000e18118101c03003c2643e041d02d001c05034001103020f07482c00340c01003020214249102c015010384502558040c2c14044003d4a14008249030b5141244400d07007034610461003141e109900700c0a4100300112075407501c50300c9040040900207a035001d4900c3d030003e501208440441c650500051030300742e2200194440c025080300d81502588103070300080c1c001600525098001388003405195607030303440750300a258010b0f00540c49103002c50082c0b5203030603900358054003c10002ca201c0c030440030204540032030750141840380d500c07076500d41400c03c840300d4070035019041a181217032a1400050005192031100c1e01d010300360000000340f08169540b09402c4901078139000e08840d88559860341503948a03900000502e0ba0a0880c5545000462180c0c03030b06010b85e103102d004500740d5420007200201310825004120341c08804c14900581 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 675692068 1250 675690818 675690859
    0x625120c020405070509180c0702032401050f060409050403030e030c0a020f030f07060f03020c100209040b040615030b0303040504060e0915150d050a061517060c07060b 74
    0x125140151034404004a69206000072154020951010000240040c006641d183c01581c1041d4401c0030300040c0030b45800428508911500d88000d40c10302c611006100c203404448031307503102c100c0035a04141c3c0b01d03a600e1052145049000400c1c66003c50304010502c0104103c1d88034a400a01030301e0006420903101c0149441c60340441104890360b482a81c0704021450100751100c0030800c1035000e4035082c503c0c0c85581e5511680c5009074414005200c1208148911075416954114440f6048070181c041091a24000354007501140740214240014441039007840e0142004803416010b01c2d5120100b0860120000c010060406505000c100310006003036a03030b8040c1c04060902e1860307401070b905000d940c0a261044002c99290043c01d04010086080040800d5a44010f8151083c01d0340910340c0c54982d003400c081c624014000c0c2c0c03615095a07040041c21060f04107649143c0781350620a0900040c0c141d68543c1158641c0b075860b010000400025542d400c200507010020b000800310f40c4025a6602 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 675693318 1250 675692068 675692093
    0x312020a020a0825050f070803090a15020f0601030c0e0601020d0f05030a02070b09031222120507150510080f06061504230102070509040b041b050621010f050625 71
    0x2101ca038006c04080c44144800d2043d0402046140c00840c0380070004008a00e62081500c14014a40c0200700b8140c100350082c000c2d4980302e0018020340d801580c4030b00d00400c4861f818012100702d640c0c4000003500c1940001100300c28002981ca82d0000e511084c1c004a495034002040d1103121602800303443c00203816110114082c110803005161189502c41034450a8a03008100803402080905d40342d0300303294050424440700750410f40f4040030200e2008150b071a803240070300c020f000d051800e004011b400c0055202c00d01070403c4481845019988030709942d0b540c400f42d00c6840d400d8005402150452a1902000d02d90401c03005c074403400e0640c0e87c0da4602859220b26212400d440058004c1c414541c1d060268401070710086500c4025801c1540b505403070008000c0000703095000c8040b4072052100c4920f42c110007030400900fa0f564503090380c0c1e421f40030803420f050b52800d880c80520010030300700780711003c0b042583e0000c2e142d141424001c0f0080f802d503e000301c00c10445101c01000ba03401003040f102002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 675694568 1250 675693318 675693323
    0x302150f0a0b031e0a050120040e09030909070e1f02030901030b03100c02160906211401150317030c07021e130e100c081f0e0703090312020a020a0825 66
    0x17061504850704180b8250b0b881604000c01521640d031020040110b24001d481c1603500d030060700070465444171030007860341c402c8440c40c84c5d01842e584100003a01d50700025454200000707450b911440540b243c0c011208400c45513010002d600140002c01044d4866402480741c11001411100d4109040d40f1000031901040607607001070700600c0380c100740508003902c000d000701508403040064502c0c1402c0184102c0c0045001c2054840301140003040c402450346054a20000c0402006170746d02e0105c03151251100c612089131189895031451101d08602029203121f80c040300340d15460402958200301040403000d0f80382d030601c441541010102d89400402d01e0f00301d001c02500161079504010428904444000000200d509242c0b08034021a4449440da4201480700180c004100c2e009410540301502074120038603802d010020046815416005513807810b010792100c04c022561541190164891994a50096408a2a00c00010301c07107400034040c4040d0328800c03019621000350788000c2003030200c0c4107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 675695818 1250 675694568 675694573
    0x30150f12011b051207120207050d091517040f020613062105040210052d0a0e091608071205090c040b06090120120a0305040302150f0a0b031e 62
    0x100014030942001c0c080b0050240d0030010305002c01c1e00c2c0710400c581c02c010101c0381080609103242002e0b15854065030951a400310030350749400b0b400032004121b03507014440c0300721010341d0014250300940110449446404141914942551030b6290880c00396007854040b60050001c1040341942d4882424140c0a4440b955a401d0650007603503d9081c521403640b610601c003450035042c08010394550010313a00442850900503212012a2501c5c0b00360103a00d20108050900441480c5240354a04000c051101e150344900c4001030001c2c06010848408032000d0304a44160b100c0600014080c0c0603007607001003185040b2130b100b02110484411b96800b1b41e03030020154040c0d40080c08500c0d06015101704410180c804c40e003001c2c980c0c00020310368010f5984c1c207121214a03010f1030705240c070140040b005682d41d030b2151550341c021490000300140822a02038006000e101d142006450341340520324001c40034115131010b59100c640b0a4070003031114000395541403013810503014002c4c0041aa0451800c0c15902 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 675697068 1250 675695818 675695831
    0xf070905091c17040c0504020a03021b0a021810050d12030c020111160c0e042006040e0403110f060c070318030201210b130230150f1201 60
    0x1150314007290100c40c82d541490744095180b2180e4003200e500c03009040001400c506483e203040030354a210140d000b1b00e0304940006013080300070b03400d81c001b00480c10000007098009041e1001c891749400d242d80c4020741c00390000c0c1c900d4000b007400080c3c680e00710f0304100402582581e200c00040b14042529001c440c1d41714524660704455406111700740440e15540000e01055841210f0403540e80301d440c0c116514141c84c500c4041c00d01600190640c054041e00014015900f45410500a051003002c0e800b81242c541c5950395000f070800c0c4003641c08544400d02c2e02191921307556070079501507003201110095441001004559610704010301d03030007200b001075103503501c110740e0500030000c50100d40d1100d50580030003003c00050742d00103184d5a141c02824101a40741d040c180c2c10a000e04480145103500c203220840c0c0e46202d41d225401803400114011900c0ca9001840403120854220b200b01041c440342d5146c00a08a00301500555200e000010b2030140c0c0b500315040050f000400035a071b035141c180c0d514103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 675698318 1250 675697068 675697081
    0x3050c040e07051207031709190302031e1501030b060118051819060b120a0c08010506030711030d0906051305060a0b0609040f0510090207170a020f070905 68
    0x2044204890040e20305200c4002801c0c4140d580b155188a014010a1003410940c4410001d1000d80080c6500030a60b0381c0484494a030300b99190007008031903105a218034413280240751586001710803280d02a0103002642c1455140052004861380c0700c00301c5000c0c1d40c0b850100e116000d10f0003401f9511074a030402c042d00703200000500c0341e0300024180c120120030a20903c10755036491004c1c1020160408012010b5a50420821030240e40d107814540c400c0c100311012070181c41d18001b80603011404c0a050b0720071b558064080055a00ba80c042030085a0000c005002c241030484c002c551059090501e1036000390415a4280780d80e0146004003c1141d80341d00d1740082000500882d90422000c80f2010500425500c03041d0700c0300c5014002d51001a030f18200d4509075202c0e602640d00c103400c002d00411a010881000c407019040071103041c4807110040030007007040b110714800d84038003a4009401d0080f206c03404200182560008102e0000c3d40b04542c080e030b40c0000204458030203004440790100d02d605181 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 675699568 1250 675698318 675698323
    0x303030f011701090c030807021f1205070305070f0c0204180308090601060c030206070806010905090112140d090e0a020909042001021f0b1807030204210c05011805190305 75
    0xc000b041c409905000c0c0002c00b10300e81c06040e00907a41c0000791b8965130702142c4000394985540740d51503620240109a0314940b82d17009048070144185052060145584448046045540494070040401c0c01c80191180c15446024003203000c0b88060030000c1c036002e40501aa02190820f6401c5000500920802400d50000c1c0422401041d0714184401d20102d42c1d60040e40720314004041c4070400c015a000901a607214034408002080c0140402c041075866152411000460520945403036054205480180500040706101e1404940c3c41040e458203104640c000c0f10300250115121075000c2c050380300b03180d40b410b0603603005611424982611581818224a0a542244805041d900a100390034425450040e10b500e0300d4088003800036401208900040d1702c59100402c4508045140080200880c0c059000f0010798800400201c8501403040803000c61408522004046007403c04003000154064540394501d00e91901441000381e845801040440c412681941d400718600a420810300006 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 675700818 1250 675699568 675699599
    0xc070501110601151809060314010c02070807180219110f060709120303380a1815030609050a030f0e031c030f02030a150e070e0411090303030f01 64
    0x308000360009615140034046840e40d40001d000c1405008404100490048170010b030113040c80f243c04000c041e40ba400c3c4000100380303201c0e52070b426628180c0003154190000036940101c5074050300810009042030a0241c0031080b80d03e4a1007429003c1c4041e04a44020a2440c028808280e03180101c8401c0810020b2401d0442901114941c125400f40001241d020030154180e46902004400340642490103c004005040c4040b034440b50031b44030515000c01c24200c001070000c110f220650845001020800144e4940c89031509100c9002c149166074007417500440c584003141c1d540b1180c041c0d920b0301e80f481926900c2904440580000141c80b04040d0010324804042c001403034a00f001001c0000401ea0b81d170329846050351115a402d80c0748056603c42d8000001c024078101e0150744a0401c1280c44c00070700a02e80030002c0040c7c41c9280800c0d00003005400b64803419090752400f03d070b2514041800010038800b0404040d840c4200715003145500c040000398054519102064150740c544503202080c0d014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 675702068 1250 675700818 675700847
    0x60c240601260406020a0507051e010b0105120406090c05030a08030717010501020d0e0402220f1a0a03050907030804060f4a042901030c320c070501 65
    0x80000d20030b041c10414804035409544a000140e0340c01d09030704c00750740703501030080010101e210300510090340f4006400b080001640c641c00038440303552250010b46050003a21005070350403000000280c04900b25812410195000740d0146518540340c02c00301e418095203100540c0c07041c01c000184040154803c3d03100391a010459080c2803194180300000f903d410880b655181004070303c404500a951751541160000703140001c0304012091840106d42c0c6d00220380c41115036440c0c400301d00240300f281c109003008a1240401441d0318044903400180c00500300a019034000e40706079100440000c86520040010385407a40300c641449406040080c019000d11107054040c5081400c071440890309280f51254182c01e60961600a020f292010300340043d0105c48207601500b04070000152070a07000c1425804142c00300c640491461510054050300c003010190800504289100b800800c004d5096801074030007030030060f1480111a000c59056000754640c0c5442d038001c2c890401c0b0382e40e01b014500f0f8480c0c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 675703318 1250 675702068 675702107
    0x20d080402130915021602030f030f030c0d0e0d090504150501210b0a1502100908070201030209010c02032a09090c041d060106031508030306090105060c240601 70
    0x26103039020400300042c110b8038803800d50b112500c030801c101058611401c02e084400045407030700d00010106c18050041d09050303000b8065103100d81c0c2d40c1103000c012241ca90000d00005481d544505203032000a5015107a540c40b0686d03900501e0300b10200501c0804440030890f6030703031038010741010100000c0f1100c02c18004004001990b0030041070341c1100d81c1112110b02d0000440801c0c260300740000c00382041c051389640c005014080400e01851380990315880d12a2a400c07540980c041401d40c200300d82441d400980043c02c188007210041d031103070700108030390764061416181c03c150316804a4505510003c103c1e1078003210182c82040881c515481080110045540c040c1c2800c004004da038079448440c03d03440c0666203914004c0d59030450214040244041c80c0200d460f15a07650500400500f84041049042480500005400710000007928005c082c0185210701c2a4641802c002d41d036400031380c2c800c60031300403420305c6504054130320705010410041c0d82d0301c0310851400d1400102045044640503007950b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 675704568 1250 675703318 675703321
    0x605100210020a0c0b1f0f0303051207030b060c0a03080a091511041e140f0303161b230111060415150b09040c0908030904091719020d08 60
    0x80d40c0040e000340340c40241000140c1d00c004030081102d0300d11826001508030310a1005204c0c4510480740340d044010401d4285090307194403410f0040c0c2c0802c81d4403024001034024410803800d02c04081ca42c6030000301a040002d0350024103004250300790003c064007081070300010180c00a068010700a1940081203c50401c041030950b40c3d0550761381c1c1c6114502d06030b00c0d5980980b1107880c0c55203044a014149403030700c282040010111400042650340603541240610902031001d5040411380740780342c00c2000b0051800c02040300b2909412500c102019a0b8406160703e40c009101d00a00c401c2003d0646c04039a441405943c00040c0300e0300314000200c5040101d0120494190311000c5040c81d00107030f00507160054185080d001c00040d0030b0b01d5201e000304009100c00016003401d03072002040340080c242c81c24405a0703520802541c041526208417007098208216944882c0341070307030003a0007061042d1020164007903900b01c0411690441410058944c00140164400f03640410603800802414580311585 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 675705818 1250 675704568 675704599
    0xc0c09010f0e06030307050f03030a11040303090605181507111c140f07060c0201110a0c050409080d06091416050d0b13091b0609050906150f03040809040605 69
    0x700300592041c82002840400451950782d824421526110707000800c43c1d0307003c0d51000030355480c0c0d0b10641e01120034601e0100140c0880e02d00d03d0503241181c0e05a10741100d014030703003041501c40d0f90020320307003c500d85440650071019035100c0c2c00c5401c644802d0580e4035180d03026881c10701d146254080c0135500c242c400c03c03403604010a42000d20722186500000d400e81000380321003094500054112040c1550003003050116030305030302180010321b6600036a2040125480f04003000c2c3c8801540780050300788403000da0284600c0c2402e400c074000c2ca51141400e00c3c50118400307884011a002600403445403501c64030102044002c58031056003200c28042d401c141c028803850041c1180c42047c0142c1e07101c3d6283c000105c000c0ea2510f9a220314032a4210303050101600d1803404003203a02c240c01d4002d80030300b1603143c0850742502c0f03800c600c01584d9010b0506000d50b180c1c40200000d1841010125610881c00c02034500c000c490800a1400365129500e401d807102d0910301040f06031407264003c180205030704c9268645 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 675707068 1250 675705818 675705839
    0x8030a09081932210a170705120f070225030609030e03060a060306111204110303220306060b1603080a0b061c050f010f03080c0709060303050c0c0901 66
    0x760a51119030203110740660030200003410303c0c01d009801078940400d240c841140b4081910b02140140441c0c1c500c01e4001499154118090300b0425000201c070b10207011001c40e039045140d0f4020f0010709005048c0b40301605070003030040d81110804500500b24060043c134036010001808111004a8120240a03015503004004002448042c001986503112003040c5806244090603014029040e502c061510503039042c040c102902c000c5500d280340481e2145400d5505041c1c070190480f00f042c4400030b88039a01d0712204940ca50010903894002040b000708502c0b03181032041d401240e001e0704083c0e458614113041013251181d1344102011a400c000080300320032240d10381064158141008001511034041100041001c0ca96123900114009015107046c4100c10036020408410103040c040303aa628034840c1110340082c0b18140c031101880100780000307403800c0054a04408001c0c1200e40c20b555a400342001e9508507407064011407400284000300700014811b5003145a8203807440066545030803807000703 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 675708318 1250 675707068 675707113
    0x501020706170709050d0506091209060a030e030c0601061e0801211704140405061c0b07050c06040305030403030f0b030d050a0c0204020a0801050a06030b0d020105030a140108030a0908 81
    0xb1120038400949000c2c010255540588000f500e08a0703008070500d0712640c0c1d5081030382d01e40750b41e1180c0088c020481a4850413248206006021103083c980d1100056015005801c1e800405000501085401b66000c0003518001c1c0910f42d50749148401e801c042024a04440710910200f0141da401402401000402e1442c00b03915011421030135036003810b0101c190400e00302c0b0384000c0303040014005501d540c10700c07003c0c902005c00c580404c4103880c2d010410140c81000502c0814034aa040c21b4840418086039245a10614900341186400c01314401e0500300700c0c0444045000c22000320078482810b40c10f111350006440005810000f1b0900000001e03603a002d010045010043d0000b2141040e901c1101c400d40d540381e0180042d519500ca50b54081c0181c0c5c0700b40105401048400c0c40014124801d0294143c440d101501001036401c0340d1b001100c0a5100034020114107880304c8aa0a810110401d107078020b140f1a00910f44070519484003d100c41c055038000038055001c030781070242d25107080a506 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 675709568 1250 675708318 675708347
    0xf0608060109050f0f09010e0a11090a090b0607051603030e0301140105060901210506030d080c0a1d0d050105191505040e12031f0f0303050d050c0c01090614010501020706 75
    0x104120b40e21a00050781c0000b0700c45c415820403244400010559480c201c01030040200c4c24041c00402100c103003114041c003031400455404200f40ca01003089900e2988050b60b2032401030718080c946280c0c0c0d2038091030f00c02180201903109800c50402c000b4183c1c08006040b4900f411002403204c5c1d40e844288101c01101030041a10134880041c0b04602e0b6800b44c448441a42c51100d20341b03603005442072a41008103130859030300d03000303011f0114480c1d00d1910a824070f6208903042c407c0306007441401041210f082860210070151400e00301c030f02c0313810f560b1038002e840c40c064030078400401c080c0b4105400c04014418030445a04107802c160038800020403003540d0a080d01c20a450010342c0c50b130412042c40c9030603c03044c02c40e10710310340c000184001f00c410702081d00c6450b1000302e04080c1e41603551130141e2181d681840082c0003d0410700c05040c0714100b540003107401c803554284050a11030039070959805c452000a08807a036030342d140301c09000b1041c51201540189001d001502202c0c2c5808030161252140310801c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 675710818 1250 675709568 675709579
    0xc08090318030f151b070512220905100e0105030307020d0c030f0c0906060816030e0a080f0d15060512070201090812070e03010b030c060d0204030f0c0f060806010905 73
    0x101c1e1a910b080000c2d2085403000700488002c0500303640c01000d00542034900c8051030105200440c00c0050002c00c6030318030341d8008002e1a0300c0304501482c80311500200501e41c200c000fa0f64400c00003d0703018081201816445d400024a4108030b04900b0745240c2ca90f0100700a0f208001c01040035076408020740b00600c1d019030300d54103c82c12034900102680002d420082c005003440003010103004800c50b50106581d14400100811a26641c0c00e440601e8200c400540020f114910030541d02d100740c220313185445a00040310010900c680e40d8124541080810100713031030303012070342e400350900790300841001040e02c0d0750130350a444c200f02009140c1d2040c1480300701d01800000228030094401d42c0f044040b103820142c030710b0b114800c40240b5003c449082d01c20b040011120900603046142c1031144610000000b001000018048014801035401894007011100e42c00d00c00000810030b10352007001c01c14401d5600c190b019090100c600c1a00707141e500220100600300d4200841d60341c004038503038181c8400726030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 675712068 1250 675710818 675710857
    0x40e06030f030414060409020a020a02030d080906150409060f0b0a060c020a06050322080d060801150620010501080c0102010606090b25020613030215070c0e07051b0606040c080903 79
    0x105e165885194804116079100007500c80c80c0513804601108002d100b02c0648401410000086942950544a02000340c00500111302658140b142c43c00d03091102500224105082e80c03124002c80351003540c18404940c8481e0216502e2828908080203080d480c1031519400030181c010402040050269500b07100e00003010400e1545013840001d0341800b0140482d240700c2061610742900d8106500705840c09081200105409406020b91042d2407a680602c80c042440c040b012500c02074200ba40c1300078401848921910b0000c00e0103101d010746003200040112a030718100081c21500356901c540b00f00401c0040610259219000305c0c0c05003082884100524a1030500c800455013000400070750003500056140f87c07041d101c02048040301d000b16143d02d80c81040400b0076038944a040d500825070340c6541c4092000ca60f008021540100350781c60320504001480100030503100034841c0062282c2c0c0b200c3d080260503d4140954803001402d45454030300c0342440c08060b90799001d402500c4a05140e50390 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 675713318 1250 675712068 675712109
    0x10801090512030c071209030b0a02070203030a0309030306050301060803070210171315020313050f0d14070c120f0c0504060303140c1006090207110d0c0611070e0705040e06030f0304 80
    0x1402d17922229000590b25241c0c11590724042c1c4216118402100c2c5c0c0e80c0c3c47d4000401c0340f0024403d45031010f0300076000d980342c074441c460103c0040030b886e40214107041e40c6030401b00d5030351400d1041c1c90240c84c6400045070307281094010021602e414141800030024009000304a00741c03203681c52504040c160944660220103494114110000c030620001c103e840801040b15801010300500030380c5001700c0030384040d000440d60380c17a2200c3d0349160700c3c0d0214070504100c50307460b1075000040240398042c1440018668480d5420000030800100503110942c088015000340401003000038000c000c101d07810001c144c40c65038007810300c904c400344490610030007060030b125a1100b0700083c110075104480400005450741c0c032840003900035040a030f030540d0508071310021500b0807403190760196811411100d2128134286040b1103500a600d1103244501813050300092007021b41c0d621034090764040c1c8840352503a084c40d14507030856a009040768401d600c030640450640c1c5010040750300b51160301e0312180c45410000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 675714568 1250 675713318 675713341
    0x11a01080912030f1e040b15060408191a07080402061b010507110d1704060b060705030c0d1b02090a0f1d0304060906170a0203070c02210601080109051203 68
    0x595825402c07400820840d5843c80100414801d145000700c01481c103032240c092400c40501281c00502d05c1c20b180303001ca41c5036050300049074903818008018500d0720f40c5036468a03081c0f4045090b4540b000540f41501020007003495040d40007030750310f40311f600600d1030222002015208050400380c0203d42c0040c9080d854462a07070000b540701e84e950024800c84c18181c400620392183c41600300e865000388203088541c54442c0c00400b80e81410034420540300d44841d190384000300400702c6000e0303111004002c0007000a8050001c0e001d0b280c080005480407517079446016101d00d141110f86041092603140d61b10050362031110040c0c1268a484000480c2c0344400c0a8500030010449105115140040804040c24000000303200b514078a035142c2c603007950707103d40580300409400344c01050100002c001074402ca081d43d000e56804039035464a1a1030804540126075000300508454040704c500ca84035204102c0e080012030b005282c280e008000000c0140c039801d07282c00007402c2e0582901e80c000017003210900d86 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 675715818 1250 675714568 675714583
    0x3070b040b1312021e0f0309060c070f1d151c0309080f100b09090d0c061104030602090405090313060806132915040519080709090212011a010809 64
    0x200c80540104104040d581d000b0001d8944102d001070018100e4004021030310070902c41b1403030020750074607094034200481a00f207080d200000b440351007400591031001c100414000d1242411401406082c441881c151190080481c0c4404601c00045040740d203580c1d40e510044503183c615082c49805500d400c8404041542c003e042501c0bda26402c00300741d0000c00c44c0d110256112004214442041c014410640811200740145070814030743c5031f4080740100d01080071144602c4001600b501c01507a500340940082d0015543c6903404102c40c000e506161045d590410b841000031400d1032114035080c2c61f445024000c290811080d0310100d00da58849483c800c003844241031080c05101d06000202100102e1b00100d03000d96040c1503980b0a060800d8850802c40c0c155405030320740380a05100500140349100614403202d414111000600705605220340800307040015008136224080340100300320174984651141050345801101107044110702a00c80140e0b4003800c1c880e600f03076a102c0440e41401f10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 675717068 1250 675715818 675715823
    0x170f04150b13151203020703020112060b0703030c110a080f0c030c0114090d1716021606030b01031a0d02010c0f1b0303080c0703080109110c07230303070b040b13 71
    0x180b15070500740030000703030450030700c01050b501a07010b15503844100c00c2d10b04850200140240c0c01c140000c1c0055403103171900f01140c000d0f030100841c41e82d0395290003a1f51644100010b0380029502e04220710704580c08140715207520303412002009100000d4035a8209440703510600044034400194804040c54240290b0703082c031490340c0080100c004150003082091700111144100ea000c0e1562100d10b9070b014500980342c8103065028107807140c4e80c14485000103252062554194030618642e0217000442400a0000d09190754020650b01441400981030f40d000084164030009105104079090312100c0f9101e40d21602403912140d4a02e81e8203080b00c94140c0d03294090214508018401409108200500110b0303201c0c0e40c83d0a0720340d480c0f01030701007180030f800e000a0016aa1034010004160260844c1420000c80c0081515024249c40018078040141e800302003003d480b80821000b0b526222040c40c900d00341540918a001d402e03684640e25a200240001c012018a4020454031032a4ed130841911a5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 675718318 1250 675717068 675717079
    0xd05190611092b050703060b0a080319030c090b07050f0706031806051b0f030f07030b030307170c010c03060e0c0a170a0b04090605060f121b060708031006170f04150b 73
    0x41d207d0400c08040c103151110309002d14030f070032000990749034004120348200100140842130220302c603e00724003511803446e00380c0401c034130140c001c101d03107500b04018600184580001c2003002c10010205082000503403000051515041500090000d10300030302c1c1c07001c0e6012600041c26a6444804105c1c210400f005048103540030400c4c6d4010345000d001540910402040c0d214680c2d036041c0c0441c15581800503854164000f07200030700008410742c8141a41c2c618152002d4100501070340403c0c02c503100d591040f40002e0300e902040003095003624050b074103c07a6000c0384e249084094030700544400c0108032501d400040c01c6002031191b148d01d5000c860a208010010f200118160428101400c025590b0310320401d031030300d00e810301444d00303000700c610800c01d001c050800c0344c140c05c0b5180b811592900540d900900c4c20003081000030350b010001c0d031180c0c40d1400307508041420860020a4201c11611200b290f007085000e01140c103403c40c40b4958040d80c4407070340140c04914400890060306003140607c0d00a03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 675719424 1106 675718318 675718333
    0x330e1b0715060911070309150203030f0a11040f05030c0103060e01050d050c0301090f0b07030e15060f04060e071412060108060d05190611092b05 64
    0x1e003500200064015500c1c080e440903034516649498490320002111400c040c0c0010072400508144a100200241d404401a50380d100107080308504031038000c0081c2c4031004913080301c1001c0d4101e52015031a00d0341ca8500c041c840400d40106c0d031113401800540c940035407081c4a443d007110030760250075040c1d9107070500344503030b100810500f56011701420220300215102400748403a098890b40700402499081d051200c4100d40c082e04c2c031010141000c4840c68034580002d68007195000b5082d0050103626408009903c00c2c2c0c88800b09a04941854000142d840010390480c1c411502c175280c0404410010300c030350b04103204909046110420241c041201548942ca9a90380800007411108408400341c80703403441c0c02850710088840c8083c6003040070410100e4080c000c540216104682c3c285a00d06001500c105254101c0c000d02c62401e41103401350542e100c014110745a0083c1c2030751a01c = true := by decide +kernel

theorem cover : BRFrame.Cov 675539568 675719424 := by
  have h0 := BRFrame.cov_init 675539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 675539568 ≤ n) (h2 : n < 675719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
