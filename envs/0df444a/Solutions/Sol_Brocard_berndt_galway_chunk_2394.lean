-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2394
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:35:30.568264+00:00
-- url     : https://prove2.me/submissions/ac5e4e69-65e4-4419-8384-1c1c883c26e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 430395683 ≤ n < 430575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 430396933 1250 430395683 430395689
    0xb0703140d14070c020a0b0702010c05070b0301050a050a030b06041104170c0405060108070f0f020c0307090c0206222607030f0212090918070807120507050418030804060213 76
    0x1001180b40b004402003412040c4000e805a014450441c0000300143c81d00c0c0d1308032003206c803243c1a16031500518001600c0018846000800070701400e4070220b4a620107102840c1660429948091410303200d10a00044064602010303042c60421800200103250681080100444072901507041a0351070813035100005800340900441c0d0071241d40b40702141007038400d0070780c024824600381c0c1050070080e02c00780c51140b06e440c240741000b80b208403440550b0f0003080342007500d180c0034080399659a40e4440f580014020a4814001400f581000c140549800c00306e0600600c5160380c00c81c071040c02a5075801100c150180c40003242e41c10002c0c5030329104200f40c05021302a02035100d000444806407002424903014501c2d01c1000001400002e22039191a40c1303c540c0007001a03440c003900300521074410310305055684a05139134031035960007180e808018a07515015502c20301c11141c074907460303074200001c2d2001d80700e503030500403905802c410109100c2c0714859003240c0a034100500c1c2414145001010801d01d070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 430398183 1250 430396933 430396957
    0x911100203090613140a210524010f0812220e041a0601020601230d0b090f150601050a030906140901090b0115050405120c0405011401030b03070503070b070314 70
    0x10020665032a00e1103136103080441e590202641007d810341080a0700b17804401456000c00710710f40400208004c4580440341240c41000030b840307243c07a0116450300c2401010120051104001081c5900240c5007030030042100c071260030100b550a642424520110031f03c405d0400203000002e20100c00c0481c580a0340c01950342440350a41c03401c18808040020b0b00700c41c11544040300420415a821041c010401403030340048032440e00c00e00014071074a01341d002c003421045e02f2500b4030140440004003940001c1814060398500994910f007040440000c455450108030200308001003140310f41c0c00360003000c0c0300c0d40f03000410150121203818907580840d000348a40e1340da030058100703000b06000c1043c0105140102c0c2e076800c01c0c01c83c10040040c0514828280107a11900d080c005010080c45404195000640104003960b9644c8460b4402291390003954042441c054601da01c0341004103224003954405002041c0440c41d1203898800c0780d200810a6003000f18048482c11301000500080038032038008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 430399433 1250 430398183 430398217
    0x2040b0d020316020f0c04020904020d0e011b17010e07021603120210020301050612040c0308031504060b0309060103110f04060305010506010e0d12030906020909040b04051009111002030906 83
    0x84800580710407041c03c00055501050031407043c0340c000511442c0108041d1000744c4c6603a083c00200f4068000c480c0050211400d00000f2100c0c0041580400c03101841a803110400d21000d100c244d40321407400b0070401c2e024603200010720a80a44100590b005a01d910443d0046014900603911110561300100c0e84103000600c8060305990400508100c1c80120f10118519450080010403500c00c030440c9106c20a070450002c0c00348215070b4200c000843e000384c07065a0300e01e012001251103800580c4940d02c11403504101140300700d10354041c0c03440b07042080001c10446e401d54480c0e400c0b000800d16082d0340b10120210400c01900e42c2d01070344005620074000407a090034900c0c000340410001100060003800b40210b0000815420f800d030901c000341d2400c000900300c0c4141081d001030f1094054064024200c80e060008100f8000c104030b1140e80100f0607505052210000c0209540d03901d0b1020344045080b0202105a00d0069640c1015803000d0049a01e0541c1910124005800c070030a03145d0b0088103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 430400683 1250 430399433 430399441
    0x30507080304030c1b170313051908070f0801110307020d03092a08012703030e0703020a0b0a1707051e12040b0a0506030a0206040605090406030b0a06170c0f010f0302040b0d0203 78
    0x41c02e00d41617291401c03010b1408c00c2c070140c1f203114144c1217500c00e0300d00c24240000c2c2c03902821030100808001e46400001d482e9040c1d21440414491009845090070541c130b0507280600201c0e044050724006c0010340c0c003601c02c0d203040910440242040600a0300d81030260071001e100110f5114204058800c0c0308414104c85240c02c07a56070840e507601c107080c8264140390584503409200c229043c4d2100780e144c203000070102e50b40b051103450281c0c1030300000c0d000621003c000c684e107840035014000c00c020642d2140300380045000e00380c0c4035034025103001d0041a000d20120f600d0180008502c49540c0081c42000e01380340d20b901800300c1d0800d0940b0300b070380d200007240c040c094501414025164030079820350050200c13502590100c6d5051007584504c3d000c0090200300700c0c0b002c0e943c6800903801180c000d1200c42031410312000c040000c2105206103c19040074071854038100b20003144005081c0002004480c4e070014010041d148003424210700c0c1e08256007000049100d80d1420041c240d00303c01c0d80b00060b1a494 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 430401933 1250 430400683 430400699
    0x1020138060c0d08091b0d050115141923040e1501030b0f0103020d031110142205030a050a020a0602070f032601060f0c080309010c03060b07030507080304030c1b 71
    0x40085c00584168000d400043d00e80304440c50340708441c0c94166540c0080943da81481070050414144050714201c08800c0041e02c0d40804c680341c4c1450340219019100c4265130b1041c40c4040542c2e10443d0340082d106000650700034441140e50704a10b070003404c04100c400401441c1424580040000d0039400c00c00310062041c02400320750f465104510380c1c200b0101d541940c0002d40c00800800004040091000203a50f101000b40106080503070701c600b00b400754000b050161600e11384216869070440c09103014a0340011081301128251642000c040d40c41c00840400440d031f80c0d0300854542056124a00c081c800081c00c0d0b100400740907000b2000880002120f141c02401451a0729044007605810003a02c40c0000c883e000280c11140242000c1409864824040c3e4002e2018075016003081340200401c510001c041d0840d0260201c19541045070648a0404c000d5601480c17134041d0020f4414000c0c2c07800944801d0083d6042802400c190086000c01e50b2440200f07240c50403510805107000908100c42a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 430403183 1250 430401933 430401947
    0x40609020304060b06040308030c130b030403021f09020609060717130312031b210e030301050424180b0d060911010207080a0b060a03060e03130501020138060c0d 71
    0x440403101140350071f01e15120144140009080702c020700c0000607201c00c0c46403091541200400700e8102c1c103600d07482d1a0a02a40300d01500f42c032108240e56030714421005e46454440e44006647c010166428001d240d818031a603a004107804440c084d040307203084000d141198018140078001c603010442050700f14039204258086105400c4281070808a03400b08130180320f01d0340f40008403e49840080801a000203180c0440c0c40b414056040d494440e060000030b40100055040c2d0b00150313414000c0b050603068000d116031180d1503415080d016140103210140300b0388400711556819a00100e020484a40082d1418003904811510607903101030340d004100080094101d010f600340041c008540c0b520f807000b5214010b0b08001080c070507840f0002a4150780340b00c1d01501071500301c1c00c1000f140801c045010360b40d03400052400590315618500080c1503105024003450706510400e104000700794019040c1001c00c011407004054148110780000e241c90341e60240c0700156240b402000381010312030000d003d00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 430404433 1250 430403183 430403201
    0x72001030b0a050616020603070c05010536071a270f04021b0a0c0806090102032503020c010e07061107080a0210090f0803040302010f0e0f040f0b04060902030406 71
    0x30505100050300c00b0342c0c1c1c441014003120020b0b40c0e0300c2d5690710780e10f440650000072000002d504c8140407051003802c640c0201c6040606220300e008203d2520364240e02d43c1a85135000751f20304c1441400740555120f83c04450f54070b840030440011501740e03580300e032109100303d002d0302208014240c2c0400c1c001d540500080501c0c9030150f07240a1084002c4146020400e82d8004e1100c040c05190005203054860100e101c041010070943e0051720740700712645c54811900080c0c2d1048070346910964000c24031000c4184212401800711119008101141c48040c00201102000080034558240b00781ca83c10a400e0081c9400c00c803609018024650604602801d42400c016800741ca036840b025060118420006900024a0b01195580580f1039601001c8411f09880e40001040090b85180040c1c0a20004043e100382c030300c02d0b2990844000e0000b030450328106030070420782d448080d40d82c4540c0c2900b06a400019564010345004c91801110030100e41503540581c0aa0116a40003003000241b15080c4568119 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 430405683 1250 430404433 430404437
    0x1217012306070203100e0a0212071706090a02100c050a0c062304030816140102180402032203020f0d0206040204060608062809050c0a0809010b060d0509030f072001 72
    0x1882e800b03030003007641d480c80d000305405a00e60720341c51000400740c20007650690650042600d024020491511034460940384a2000c0b000b0f400b91428001003000f096483c42010a200100f03400c80c0141c0802c01150041c2d41105d0a200d80da001140100e00c00f4081d031a02d90340100b0382e003054940307008402442181000c80c2c080980001c08800724a11861100312011a900400c1c015110801c1e100840750341465a040107100740c9105030302e210b034080190041d00d010903030750700380c0707104981084240016444100c0703a68210700320b0005aa902d2004000403251501d000f48102c1c2c40c144080451240341c40240c0c030303400c005640000304001c11440c040c0a200c01402c95403800002504101002c01c5013086124041300024440d03e48100414090300c0c248401000c2007807050040382002c0b401500b85034041e820150019010100041940105009a202001c80500402d20b1b20b01500040c0d002050041d00710300c001d001c10451548681181409001c2c2d8074011913aa04100c55030f103130284040f164940031241 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 430406933 1250 430405683 430405687
    0x20f1008090f061905061516060b0103060b030121050304270c02071205010b03160905060a0e190605120c09070306060219030e04051f08070e041217012306 68
    0x1c20010311811300003045000c0300c0c02090f00d80301e080004004002d070804041c10410041882c0001c060f0300c0d500c400f8601d01406081018043c100011230035151640202900880c04000410090020302001880f00c03081400d0400300b400399903034150540d84264003580c100c1d10443d8941181c0900e40f00452210020030381c8c20004200d0044029448070151b1280e041c000809441210501400b074010010360103005003954002c15945810f40310484403801742c00c050030b10700800180a030400036203800550700340d01c0c0b105003e40d4500d000744da070080a1180002e4800d4507a50700044030345600090030055508040130303000320305814007807010005000b800f0400b05401c042c001c10406d0340105040210b1240e8401c0351441c5007542c14291100d80401c02c4882e0413038a48410040710001181c40c0c0b9034030054008114010b19510b40006542d1012401131421103109000410006585404010042c3c0c0440c2400f204581e4503285e45071581d24264000343c5d080d2502130618070281050b04100d01444130890b9618 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 430408183 1250 430406933 430406941
    0x4090e010b1003050402280905090307021e0a05061206030f031306050703110625020c1e041103181908431a010e04080304020f1008090f06 61
    0x1066004042c0b0707044181544c0e20089030a64032804826050b8800c0290310100c1c15620180031304404e1458418102c1661500011486440d008011240c40540083c2034841c11038520090030350416101c140ca5a114a81c064005600d07128000075003c2c0c0761305e1441c40081c1d071034038038289030030614a032000c0385044d0000c10002c11204840808a01034400d980740840e01d44110b842c0070b0740c40384140008400c00d4480d42c0104801405000c1400100300c400401540482d4041c800aa0b5584440610243e0103000702030b005000dc01440340c0103024880040c80403a00a800e021038440b03e40c41510810040464402e110030160010003505140501c0000c043e1030154480d299205640500d10300505508500c1a54560603107440815114402c0100644060b0b1718440403245c414410121080710303c800d4001510010004c0e880c0490704850b1000941c64840d030340c942d10050140e00041003240e000c01022200006501c4403421503c0034002500c80c00c009080147c0101d24016400e01c40c0303480c1d903210380100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 430409433 1250 430408183 430408189
    0x50a0905031c14040f14030408030a110a08040e0a2703110a06050c12010b04050d0f14072709030509100c0203031210090b1008070c0605010b04090e010b 67
    0x1d03003030300c0485440d8007070480840c10500043d11011949044200007441404207109540b402503050704c0c412101034061109003c0c189450307004901c6002110307001444400005805081d6503440c0002040980e42c2c9a800c1daa91034120f43c216804c02c8644030072140400500d0f9110382300341c0c12a14428150469401c0428240f03411404610100504000b1044420004040d00300b000b00c04156124005000758584540c03904216080701c00740c644680c00d90400002d076601400100c0301500c03c050401d00400c56640c071510310203c18000100c130010321035060300d03d6031b100900c0700c50042c0c4100c007400402c1104002c2c1284080031a60001180d5034070b819120000607420000300c0f5030001d003d0300e03902111006030805999180034400d020f90103000019101842540c2c4204180c495480d8100c0031441d62340350049501202c440b000110381020104051075869405100483ea20103000d107400d1f040c1d100e1a59814060350780aa001407d50140403c040c880b030b4000d400342c00a000e14450082122000794000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 430410683 1250 430409433 430409437
    0x30e0307121e030e1f140909040201050c070b0f190e22060806010b030f090f10021305060a030614060a05040e091914010614100e0406051e04050a090503 67
    0x411074030705402600c0030076001340307000c580c1220300505099070103100301d0f5a03213103c918901034800002d241d0039441000d85888800c0d11034680c0050225009551594015109540900c221625600c01c62000040c1c10703000400900e100004020310a4851078a0403000c2c088021031070408051002c51102c2c09429111028410304d04203250b214003075149086d02d81d10000b0251038000d540c06009910020440511039001035004086951042505503184110030741c941c0c03004004054640c10800784c07000440c43d10780281103002104c48418440690b02c1c0c0024269074000c00795100400d07211001000304592603044032080c09030035107207245040c0607148002c2062155018000d603070b80c954004101462400c10003100b0b003140c000c0d88a0504889420011040c0c1c0800420061540c00e00102013400340d8034414007036101e1409008c400350f103460103c0030b440c0040100140303a041070f034800c4001042c0c0da0f51031000402d070706000000c00c14511070800b0301055480007050383d00b000307007002020390001d000041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 430411933 1250 430410683 430410713
    0xc0405091b041b1701080609190305120403020f1e070603020714010204180b0102070605090907170a0905070e060a03030804050a0f110906030d0806011803020409030e030712 76
    0x100c169000380d80c550000b0002d01610000240c891a9200a2080b15800c108140c3c4422482c03002d5419a80e6600d01700e96403200115020500d03278000d005503200d50815058618241c51081c2841401d00c1100c506080720100c00f250190010b074070020000282030014015426041c20154810b6050344020043c16a641202e208403010503a00088010a0202010f03043c00d240c01c0440007595502d0f510111518184031005140c400c440c41c02d000078681390700006015007110003644402e0304180c0300d2020482403a100a00d0300d0144202010510000b4140d075009078031030801d03420001003401e420300b4810300c2c25070b10303400061420000c54140021036641001c1c2c2400c50341d25142000584c3c1d1180382c01c0e41040d10301000100342d640c2101c100401c220410341c1e1001210000c1e00c070308509a54207010544d4401c0240c07810804169070b800807618070751080d52203c5803106145031845c016682c940c041000c440010302d0036400541001d58410300791078140302c84401440c82c00e40e851100c003026252004041c512074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 430413183 1250 430411933 430411963
    0x80103050c0d0501110a0203031e0105030712140a15140903030a110c160e0703020711040c030b030307050c09060a03170904060503010c08040302100e1b010c02090a0e0c040509 77
    0x101070003c00409410a08098418401841e100d02c0c40100180d540c0e0401d80d540244104c0400041d9600941c1070682130480c1d000030001c02c031240c80c200902c6500f1a204000360340510100000d02c00c0100200030005c1d103a03218000740c0c60202103400480c8100d44120040706080d50800e410310054030000025a038000c880d0010018001c40722100f42c01d0188160024000180510000d4581c18130140c80030500b2181c62021680f902d0350b03070303450440807407256010040111207a46010660b40c00c103580115054000e504000641490280020b851a002098100d4190f070001104910341d08004000c1c0d03410a0090303c44880a904560390700121050140801d1542d203004991240540c1d15a0801c0004140240c02003081d800d220300d00400c0740908a03000c0c1d016102c0c80c1c2c030b03c00d0300c85418803802071515030600c0170b800380d07280d0780c11350080e2048982c910904210f40d600c2c64501603506c060f581802100ca229000900000da5000103041c03400112a4034130451905040000070000861a900100085 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 430414433 1250 430413183 430413199
    0x70308160306080a03090302030105010905160c03020f010f020d0b0a0302010c0b0a11070f0c06180b030c040b2b052401090b0409061802071a0421050d0c080103050c 72
    0x341104400400c041c1d80454030a2142e44207030b0050541268880042d0390007980203003c140e899070f528a05540050f02ea100c501d40f4628800c4100c2403081a81030480d40c07092051319114056500781c0d40c2034400c0607000c0010175600050003100e031403c1344150000040c0584010515903d142c0010f0718030112600043c065480b80400030303503011219400008030601030040540c40e5801800c0c05444100288401c82d0344404030003010920500030720752403500c0309a40101d000210301340035180019420140984480e04403d003c00700d0042c0a440141640d0317128195958070300c141940f02c600304803c800d880760701d0341403920087c0440e000310621542200c44d483c080002c00c094407100101c4404019510141c506040841c0c04185c00806400c0364003280c149407020030805a540111004a100d03400000b80b440d0781200c00c0e01008e080d24403502d83d0042c002c0c1c0e2003000c507400e5104a12900d1480ca044d142c0021400262440070360390f184686140d2000b1482c10685560660352503a903102d10440e0164491020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 430415683 1250 430414433 430414471
    0x3010302010c140d050306180f0c07081201120c060f050d050402030c030f0c0f06191103041212080a1b050f131202090609090d082502070905010506070308 68
    0x200314506007042d0240203da141342d602c3c4000400c1a042075800300e02c074010703400c094400310110381304003801428924040c0640e52100342e211050703030744212411246a131080c0038401c2c01440c80f80101d07000300300c1c0a5491928046a00e440b084095950b00908207200d010440d0444240d4080281e4480410319580028691070b6800020316000702020200c1c0d1510881e1b441c4101c00310007090700009a8030540f186c0202d811840d007001100d0007620305902020b090324519502041c440c5030080864108101620314142e2542e004210060f0807420546096a402139101d05455000480d5030b8011040b14003044040e8140b00d0000c0140000051081003040100f00c41021320301c01011100c456041c80c14000100d5510b400800900380c403404181c1c40b0364508000030301c0c5410501c0b0694403a5900c6009880d1142e014041030745e05090141411600480150610013003c5513840c446500341466001882d05501d800403041c01c0c1c1d00e0580009010b0281840601c0000303410100032a04640079946140b000c0d0701c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 430416933 1250 430415683 430415693
    0x1060e070203160f331a0906040e07030302031e0703020c0d031202042c0601080f04030c2f040209030a03030902061e041a090f0609010215100f080109030503010302010c 74
    0x4074480020340302c911000700701a41c5c4a80c2020458080000c00210321003181c80702085011030b204204100c036015401d43d02e00020b0b140c007010039940040004c10000f03000340d26a481034036140040d041200981e10002d400d0074459040d02102550752002d86005203050700ca541c0003515a01194502c1d4018600300044504050042194500f060958a8115101e130b80d6441c04c100314500e00610101810480300d24000c0c4c484616024a104003810b854001305519115428494a84002c009030f0802c40328a07010030000750040480c04005c1c2844000c002c14010400c0040040b60100010034480d40c410440b4880740d07107002c00d07510402e0390903040002e02140340e030000c504c143c803071005811201c401d000d42141803200300a018105071814602c103034809807064080c6420900c11201100c1e4003006600b500c01c802e1600c20002d018184061040da41d41401c10201e00501032810f4400300d01c80a0408003c0c00a041d11207440001404054000d02c111141510054107910041c0406410080d03410540d1003404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 430418183 1250 430416933 430416953
    0x30c050d1112030904060e01052110020d0e011803020d05090111010c0206090d0e0a0308030619030506220c0e06010512070f09081609020a0201090f0c03020301060e07020316 76
    0x79a02810b841405000003403110b849501c000b00441c4140e00d4a0404181c0c24050114181603d001501c0700710785988842d145500140c8200710002c0900c120070603880b911800b030010b02861020140003203810b03a4074045031800d49031015000e481c0b031a403212507080403d6000440122000d190b00f071243c0e8415441c00100c80240c103c3c0b440d00b60b43d40c20505d150951b41d0380051842d00c500341d0340054442209000600f1a003220310340003410360044c8001e40a1002c00c031120700960700a003008040540c041101110007038081420350054505403c03100410408a803c0700200c04981c00240005000e079100d9680c0d040800200e0050183e10070340040000c600c0e03400f50b0116105940c03132404841c480d1030101c000a1414031a818240700060605200203485e0400140007e04160342c04000c0c030f60103040018060003034000040c0c000c115900c40500c440800c07001e9921b0951b0700c2c0200769102c02d4a0640c0181030175607025070300064000103034004109080e80c0c08020b41d0b1000b00400e039079500d245001d040c01501d01c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 430419433 1250 430418183 430418213
    0xa02060c12040816170709150e04060f062106051005090a02090f06041d040219080a060b060712080c0706060b0a030b030303090c0405040c1d0f10030c050d 68
    0x90400000c01055203000018480050951500504001605ca0003010f80c941d0390021003c440d0703400a078045c024015150020b4480642c900c40d16462544d60318020f01c00ca41082d00d003610b15640e5050000c42028090107540041c240e68414202c40c0542c180e0780315100c8840d24009803095036110080303402800e69840840007403000400e80300d075500304161800e00a44c0130304c100030721400b1007505d000c0550a00c0e6099504803044858225003118190b49243ca070b5690060049a004855a43c1c4006c41e4040d039005002910550000309070100b014a40b1200321485641954072070142408010002420b0302400002c203002032038906070070384520300e041e9418001c15100402da9410000701081c41da214002a012191155506020032a101003e05440f80700503590000c3c5030b0041d03440c060150030070f9000f590b0010311500000010a41e640300c00d01d0f01d43e2081031031840307004440060101c40901c100441d90000030340401000700500c1c43c3d8a60075882480d02c50140a51050041d203414044101c90808007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 430420683 1250 430419433 430419463
    0x6060d090f0512040801200301031506031b0609120209060616050a061b08070504150e03010216150b101215150f1d060f0c1506150c0a02060c 62
    0x100f440c0e01c01418416049409040d07519868410381e00d40300c44005110740f00d10064110744170728503425516a5001c244508200c05089504c0d80c1c0000001013071300054801c2d4100d404000c4402c18180030004180403495403009034601704600b148030259540000454020208846650780e40ca60900940441003100d44052305030700598a2050030300016401411503600640140390801e1180101601c14030001e44505002510520051080c14000c188480562001341400c051450031b01c4002800ea80c096681385001e940310001d00801c00202201c0c2594804929506210640c003050200381c60100c0d0001c00e104009100c0010340001029030b0081c07404040c5002141101600c50404800c812640000d01e000601e8104411104510501301c80d411301c800030003c429405418003c000a940260070a0503e0723041c00c0081c04070704001001000110a18911650b040d4903100f010412140d00b10303282c82040510820060003d4140410640c40d95035040380c2c0c5035141c141000e440d42c500390608150380d00e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 430421933 1250 430420683 430420693
    0x309010503071413060f020d0206070809030c16090b150703051e0a0806150a0206010506030405070e2a0f0304020409060216051c020114010303081e041a0f06060d090f05 74
    0x4e411010307a1100080d035403070b40c580f082c10002c0c050003240e5a040c1d200e000c400603001070001c10f0315213200e2811950003080c0d031011241411280741e1028244403003a603507400c80c0214117038200702ea4104e60250420300201141c0e60008551100700e0521248501000142000b200080c080350b250f4450528856444007001a1502c500882e00c5c05003801c035068a040d4450780004403c2281880008103c0c1c4003800c6580c06031045919000902855403c0640200c03140d0040c044041040b1001c8403440e84038480074440d14601020ba044a80300440c0c0718001a425a032003004841d46642d803400450390459415180003a1803060340c20b00350024000c103044502041417500958080c07104c00945403070800c1d01c44000200850182d9000da00702c41c601c4580c1e50f00d8040b41c50040001c40e02903003031142d2016401c1581150a10080700c0f070707520140211400c44141150042005800e01d41d1000303154410003080702440c1d141003400005049001c3d821692400e02d0312036111038204040c941c0710204242e40300c0c003255 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 430423183 1250 430421933 430421947
    0x15050f071a0703060506130302060d0207060e1b0a0f050d11030d0306060801080106051c050309030607120f050705030c07030203190e090a021602010e0d0c0b0d0f090503090105030714 80
    0x6801d8109035400c900190500b84007080c03900d03042c01140c0e1400702580d502c0c00300f40c0c6103138240200760308a409811546a800c1c40200c021038258041c8d007040400e00c00103071041074940120415600f01c6807048500aa0500b1414000080d03404256011345030101d41c50b0040e15924500b92a14983c1480b900d505070040e00705a05896806400007400c0d00c0813a00c40491036a25080c618cc01c03604244500c2c0e5224650110440214080021000a6a0045084d00e190161040200340b41810540300400018000e0050312500070580c40340c072a200554010034005d07420b114800401901019101050400c3d0000354030040600030411a071600780055540221454000c0c2c1c05840c40303030042102c602841640000400e80d0101c0d2088411400c101c15400d011a10b5075001114001007008605800442c0034814402040c5032541503001451314005959a8000c80c04041c0203442ea0107880322242810030030001c001a5010007a00c0790901c00386016501d07983e07020b00c120781041c0c5400031224800400604c1d5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 430424433 1250 430423183 430423223
    0x512090313060e030705010c0f020d080c030301060c060f0b0a0e100315050105150313082a0606010f0c020108010905100e010f03030215010e0609070905120703060b01050415050f07 79
    0xe040c4480c04074182c600b42950381e001950017207448c2000805000c030440001005251425150110500034031170b19040030301c044101e03441c6604c00e0300b003c130100d80741311040020400b060046200c2004101818040d40340c294020a5070400c0f10301410114801c4000011440c2065805d01d400458101a44d5140e0642041a42004000a01680c1e000b0003507001c0141044600c001180d016a40c0940f110020041e40c0c0c0319a07101d43c1000707084140f0680744044140900d540c02d00443c10b581134801c00307403125050420000d0b1801c250081e13040f0521280032100c40c00351fa000b00d051811a19501c50100356540c1e5244501d488201d5030300640c0701d14018100106000c00090b06141c1900e1081c2c0031070700b40c0701d802d40c0c48003180502440f9081e84051800d002402a05211608940250607820180e032100e1b22040014556040c000e0201515400b500b0300300203110480c080c00031400000e09101c0c0c642070a10189518882c60b01d84d1305010b205c80001d80e60542d2003034108030780005800900030300c1194010400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 430425683 1250 430424433 430424447
    0x919081903021312050706090303020706030b030c0604080606120c01120e010f090c030605011e05010e030109150e120c0a03050c0f060c0c0d0906020c010e13061403120901051209031306 81
    0x816105d074070808001140380b03801410980203498260b0020a807091511004030060500604860b4150084503c940e00b40d4441c0c2c4041c0000c1d14062000d00014509141449801c0500918580480c1d0000801242c8c9036000f407103040da94030580c00046280070b05141c0141c054007172046c14034600d500c1c2c80400070600406540070001d41348070b45014800e0740d90700d03008001b0b400640380c020750302e05041500406c055070089000000498000d000840c00c0510b98030740310f0f4030150311100d260009840b00d0b21130f401014188000748155510b618800e007086948420356903030f5102c2c0c41005060007000500d00201c01810000c000311114018111940c5140416024001c0c0e004015078880c00c2c89034810030310aa034043c0110320159540381d130007800d9035100030004443c048880086950031042c2280500318481e40c902079800078201e407541d003030032001084080c03600e0100842d20842443d482442102460380e03105044030200c4400d8000c1c1d0305952108214181944100c19084c0402c0c0c038607440c005211908401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 430426933 1250 430425683 430425719
    0x2160507061205070e0d02030a2a06030e07031112010e010f050105030607080402090705160f1403030f040b1b0a020d1e050304080307032309190819030213 68
    0x3980b9200e04905420800c1954025039424010640c030740d00241d114207202c55480b0030740780024111842c80030075483c0d150400c141c20130020903450700b111441c0480303e041200302d002020585801c00001100e4240d450b151000c03404018071005907c06c1c0304d01107941c2c02004940c07296444000b0880f80300002c042500070514018410401802c01c0300000741c07803a001c50000d01c546001e88952a0503940c5030308000e8160401800380f010b000c0c080c00202005c002e040c00044c0e803903100d43d40e4098412101e0400720300303000200c20119a19030003003007003149070704540300d01e04e410a40c4803102d440c843d1150802407850102da60700040e04901d0100d001d000310b541c0010050305200054640d4070520200c083c000980c2400880381601240003000400c00158100000311f501089500e00010a280c074140022003031103400745045d14089a003014008c41c0f403402c0c0710021444023403000101c40f620030b40d500c070603841c001c082d0034404d138580e200701e0010900e010340c04841c451076900ba4035040e6282c41e03c40c216403c0e90100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 430428183 1250 430426933 430426937
    0x70807020a120312020703120c090909081b0f030409090305040e04060b0a0902090d08032208030702010c030c17060301060302040608010e010b03010b010923030a1101030c02010c0801180216050706 86
    0x3049184081045c400c03140025019603d001103150200c0190b4094000c08103032808101c9007010000392000310b4400c0700c0800d4455440f0f103944104564a010000410149030075081d042398440c0081210000102c50840302c0d0507070080745001007424141c410f40100d41c00902041c0c0711200700000c0080319402213070a40d0044074a10308041d01c82d1242d5003280a0f6640062300010345103201b1010502d490f01440d4803412a0280c41d9081c02440740c1e0700781c800c0c00e00c00c003101da24602000b07002c0b04540a0080d004c0314419864100808940b0101c0100b12007840003404a03031700442400b0074070940b42900711102954010308240b10017035890031a5802041e90203a408001c0d441c2c40c410020628040c0500b01060234141e4a940c02103081c07230184000915607800c1c0d02c094101040c800121910b00f44001e02a03280110540444126804000b6094401c0b44842a045900d080303648000c494210f034805041d03c1c1010607002c59540e07440c80380e100a00c142240030b8014200c0300100d10400000207a0403098070455 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 430429433 1250 430428183 430428197
    0xe01060c022106060d060b0312030403080106021609020a020309030604080903012d0b030f2401051804060b06042601060608040c030f030c060e15070908070902070807020a1203 77
    0x801c141540c040030300c0000101a0820fa002c036501e0724010560510645c0164400141078111300006032600c082075141500240c1e0100802c8103054014900c2c0e8010003190000e801c22200a401c10f08803401c031030044418143d07020600c240018820019220090406011a801c80c113050074800388a410150310b06109e9801c11000d143e0b01428079500003001055243c485031981504600980585004030b103a40d01031181c10002468581b003040098150941c1404005688421020b0030020010503000140110103503512552030b200008050b41d03000303403c050001008035414002400d603100e079500c00309008902011042c400ea90007145d601c0341ca94510020400340c3c0c1d55440c01d03900071604503070282c07410303e428004001241d40c1ba020701c1c0150b4424078060032a40c4803586c03240102e842034a9040c200340d0082034440c02400000000d0b03a0400c0d80c038200b00c1c50f29071822102d641d40340300e41e0040c000e0954000c2111810405a0804d0742c0429600510b880c0a03d80c90b642901b143c004056000e80020b508 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 430430683 1250 430429433 430429459
    0x130e1f06061404121406070c06050606040e071d0604090213080106030203030a030f02070b0c0a030b01021c110a02150a022503110a03021c020906041815060e01060c02 73
    0x240c0050b0151090144026041c185410707101e080ca0444a0000d84002c0d0710020503c54038402800742510030101c41e220b0001c8401141021030443e9001040036001d6401000140a188407226486501444506c4c2031105600e07000015900c4002101c0c4040e00240003043c042010301158028002450310422450503895403407100074241d42c2544400fa416800c10083c4001003482500481c09825402c2c031301601d4030841e075403650040c2c5000c460102805001040c82d20b907141d458054800d2980d0b09200500981200502d65400740300c40000c100248421805e600c06006030a06c03040c401c40b5002820711050a0642d00f550b4000e6001c01280790040c050039200c41803c0461035001c94039032041301270300c14100c0d0642d601c2c403000b4000340d803400d45d110341142d07000001a59200300c1002c0700a03000000d1000a2542d03c14000f81d640c002c1d100910450405044200303030143c031100074101e1038010401200c400c0e03203501c114009113000c1c0c0000510f04003d50000c211503404c20880d002e000e20a940311036141032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 430431933 1250 430430683 430430687
    0x3081303050306011103040e070905040e010c050f090409050d0c0c080a080a050315130204090b0d11010804030c140610150905010807180e0f010b0a050702130e1f0606 73
    0x1400180180403850510104506502c203d9008060000b004103e82c03400340c44036102c8501c070380201c0c0e01c2000101d952074244000d00700342c02400c000002800003405011402403003c0d016000c3d400e020001000040f0700d030440795407990040030980b5049426508001d441c0c0400a2440701c8802050b07500356603803540000c401e540041c10440303054009413880d01708031102d01d08444903840644000c8001141ba84159a0740d034612811304102408020016520391074141010305841c48030944901c1205408040d03408525488034a80c400d24003480e190000750b540f45800d8418050020001d0300c000706440031600220000a27116006600d01032600110540d110b1502c6100c1450300069800106034007001c120650144a81903008551400d1517903180c90200b0b901c9591040d194880c4000508801c10700140144c000ca441d8003500445515a24001011001801c203110700e032802406650342c1003501002228a6102d044030712100307810382e2101150380e0b008142c81c2408114180000d07280403400242d00d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 430433183 1250 430431933 430431961
    0x706110a0c03120902030303070816050c0a0204150b0d0204241706060f072006160f030c080d0203060306090303010f120c0308040e19060608040609110406120308 71
    0xc1a96611140204000e54040314064001c010101400e80c0b2804080300503030341400550310035407031070703440c03407060300c0e01503c0c400c042c01517050300000340038041050740d0800b0000b1074185925501039401140700044560090b10454072580070755845440420304102c407080540050084944e180260803002c200c003401420300b504c16050706000b05050b15209507450424159040d48010020541818900000c00102c406c1d880440205c0351800401c101b103c40c6020118000021041a9401400c00011a54078002d40d00803c502400895101d1400300030984a40c41c181c030913541c084107160b1140d03e00d02180c0013a4005480a40c4a40103190001da01242e001050380d0407203021500c401c03481071415200b1091640155026100030303c6680011004c00c0b0804002e10051880d400c0700347c01d40c6042e2141c288808032041d941c00c10141410002c210581c0d01c0120341d0b8005407c92e8001500300418134094000b600c0010000350886c0c00d03c078000a182d180d200b0007070603150003610b0315111660b07009a14501d030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 430434433 1250 430433183 430433197
    0xc0503060a18110c0102071707020631140102010c14090d06020f0724060b0406111c02060109062705100e190e0c030709180611070611 59
    0x40e000300740c00c002003580300202540c0a0704448001403002960701c8042000e030b020a0300c41415039000a03000041081d40b0a04290f030b0f007074200c00e06007848c0d80c5500141440c8645c0105c20f60701140c1c02214503522039045030341084500c040101d503880c4c07580c0b034038090f00019070740c110075015520380317808100a90b00a0034569452414031986525114500007081a161100304090319603a9007840002c041c1c00f00700004101503801881c0b22025502a018103d00083d00d040c1d00a07400717420150200007100c04107055606540c030908002c0500a002d51110b03142407022580c20034004501000441c20f141c010403854160398080070244456a260301c5104102c074250307080d0702c403030069241e40f607050407036551b02443d00f101074000b464500700d1360390048509000040c0c99000325048486c0c40100864800d06c602644c0343d2104010b040c6808006e800a500c030140e40c0704881080e42c0305c8051400c0300079180c01079400e1642c0214104a062071a210b81801c507000b0000440d01c0344e2030b00707460307148000c510003d46940c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 430435683 1250 430434433 430434439
    0x180606140c0c190315091e0c121e060506040b030d021213120b060306060d02180702030c0d080402100801031203150e0412090e0919170301030807060c050306 69
    0x601c5680c40500c408000000f800c0c000404607002e02000250b43e119694095209039000881d441120f0f00300301814507514440205c549140042c801300040710015100215090428a1100d560346c3e410407034444e049200301c0c0c0d61241103124060003088130580c8100c0c002c0c88242d40400c000310940042c150307180a40d40301180540e100044003a0109080001002c0d40440700ca000c4041c20b0b42c3d4100c514411544400c111380e918070810070406541420400d6035400001160704a02d1240075402203801024003c00d001503841014000031074250081085586031040300080300c900e4000000d000700f4108054030100e04c0360b0120140d4a41851252403c24166600b010340240b841d038032020264001c203102c514412022280304000035181000041161181d80503411066540d42c4141700103001c040c1d41e03006102540d00d000c060001d0301000282c1861000c661310f40a84610700302d070801c0c103100c05240f200c442e0350500000010080140b100c2c003500e0300500c9031a05008008000e042a40c260004960144e0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 430436933 1250 430435683 430435693
    0x120f07090e010f030b22080c060703050f01030b041406011202030c03010c02030919050303130512071802091c0804050102150603060714071a01051302160f0c180606140c 74
    0x10110710344030102070b04006c50710809100c0c0c0407282044074002034180382c142c03664003001c01d0b0880c00c10010700c60f00d076214441d444d0030855890940750301000240d0601001d84944c5928000500300b203002020216810000740446000d50b035900c1480f1003130304c10100120300a0140c40e103903000c00e09050180c040000d80c01e0f009941022801d40900407008958052000703002122480003426480520090148880c4104169401c0d4201403e001e101d03550485010303602d901c0b00302d080041c00040e0060000c00a240c16016070349015200c005443c0001b0f030741c104040c3c0d4000c90010410041104004d0040b1802a026905001401e5500481101c400c481c1950107030410710019001a10030b140b0351700d414a045c0c0300603080c6821520746d84c65002104101c051103803c1e0350018801841e2601d42c054400501c424203600d000305000b500300c1c803072102c1c000c01407425140f24008401c00040c1d1090303401078005518110454400304c040b9401410fa02d00c101008501c5808450070010600800c9507481c0f1503400c000c2c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 430438183 1250 430436933 430436939
    0xa1412010608040302100203011d34050d02030a0b03010c2a0c2d050a03080711150c060703150e07110304081204170712060c0302120f07090e010f 64
    0x259402c44010300860460064180c0f07501c1c513071460b102540c00b0b00692461103544003526a0290010a40513015400004010b00f481c2018059820466410300e21a64201c150000e0f9490540711401144000c4a0041c004420820420f03420b038401460230808400030b0060b0b60200c00c09449110b8501140a2041c43c6c00740d600e808101074002090034548a4010801141d9541d031030131607811030b21911844016100c01c9640306100600b031900002c0c0c0402c0300d4040c0d007981341d030f6240c5949105c2c2120081280321500456015039940040e10050a011344511541d00c070f0301d01c0fa0301c40c0c8640040700c410011078984143c400040502880d990140d0742c407828280b080c3d44a002043d20044565800041244000c1001046d40c51040c13180fa22566800702680d81c07100e042c0922607007095400f03110700c540f40d40410b108200c0b44000c600d0341020550080e000150001c01c496086010f07103c1e003038803002854138010510002d509810407e40c0300300ca0507682d044110f501e550020030181400c1c8180f038111102c1380c1042c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 430439433 1250 430438183 430438187
    0x606020f0709050c0322060e0c030f0f1005090c03120d050a050103020105040501081504061707081902011103040e010609080d0e0f1018060216060912120c0b09030a14120106 76
    0x440c06d00c0255101e13070341d00c0404554600080d18264508030031103410203e105909801c080280c1101c0b41284005020302c03800c407c141c607944c0c0031380340543c00205454402048010300d042c0709030541c3c980080c040d552109002c07507500006034842560608500d140c0b0340000c020b1042445400e050fa03078141d44162030b0030725100c011100004040d002409040312050f1803911940c0700e1050320000c2c0030714003d070500c0c0e40c2407903034031403e2103c680c1c442d03909500300440e00d403401c0c092444865800c51742400c040300d072030b00c000c0002461402540c03c004c0d0102d1a050010603070542001c0c4903030898804000301c2c2c0031440d400e01c2c01c8441102ca421001d811060148031407205140c403045451242c07109142c00080100711074101508511035601120260300241c54032104c132001c92600501038102814610303031062401141303081c050800f11000d0030381c0149030b000c483e480c2d11445042071010b4000c0d042c0c05040c10709400180e1660301c02951000458002d94600c184184040107494081802c3c04880b0a60b82c40c4c4074003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 430440683 1250 430439433 430439461
    0x70b0601032405041413120c170d0c0203090d11030a1e03030b12060a020310121a150a03080f0408030703120b120d030b0f040606020f0709050c03 64
    0x902810701d910740e507400c0380d81100445104800003410780303070400705481c007030600c02114520401e038a05501d4060400c00481c42c01007030400e0701d50740820300d406030320800e880440e045080f0040003040440c0e51004400d05241010140c02581c540c203000f0009100d8110050760307030303103e8041103981000260b1640c401151a8040f08246400c01809452911000c1c1c2d80f00c454541003030189041c6201075041c400185a854031078418181c5040d210940c00300c1c5a030180590300c0348000c000740000740e000070004000c0c2c500c960300c040003840500b03081c80408080345083e010003941070b87c0c03603890b8426180025240003e0021120383c2640d0182c03400302110305540301c0c041540d006002425614900300301c0020304c064100001d02e01d4a019503122429581310b1105c0c0025500c500500a1140d20704030070720348494602007074002070711a8504001510a8400e800b00b040a20074032076155009141540008070300c3d0300482c0038500c40e0681800d4640440e03c130340016088420903201503440c2101400007030712030422250 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 430441933 1250 430440683 430440691
    0x18040c0906210206090607050601181103010e06030a120c060c0302031315060522140106051215060318010506120a0803070c080f0702100807051801110115180c05070b 73
    0x30701413900c807903a00486c80b0f550109508651503030103070300100304103204000001d400850100081c40511104641581d480c0410f019845d17809103020040303003a65500308406601d0b19444a4100e40007070358008090030110320084c05503000350130440c0f080740341c910903c2202d10a8007100c40d44100c80141d500c1d909210300e0400d4030b4024140c0e9507000482e04d5138850b5513000000c1d4080d10f1941440c0600c1030000240d8038101c00516030340040c0c00c01404415000340a81e400c80d00c225543d02100d035120f880e03255081c501140c110ba0070242c00418019000ba0506001d407580319004004e00c1191124424040500c01840b6900d01c1a0442c11402e00014420b400443d0000039a2400011a0100f6150120140d002d824032090a5100080e0f580442c20304485030a040201424a15114540003c4c0580310b442007000d0001340701d001c0502c446070b0342e0003070032041c141c007010000070070410b040c20a1009c5100031900a02c00010103144152072881c44074010b00300300d2102c0d60703915030601900b03a03200a41d910b0040c1c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 430443183 1250 430441933 430441939
    0x4060e1e120d3b0703020603060607050102090a061d1e04050408040f08010204061103070b2a0c0c0f030316030f090b0a0206070801140d1403070218040c09062102 71
    0x358601d0101103e105681c5294540c080c0d81c05116401c1064280d0b81c08030b040f06554080c0c0001408001503a101010b0b26404101603c0617551540780745401d500920580902c039600c10340d15040171801907400b12108612010003620854450103810401c1016040d000280f8003082c080d0000000c14145034014540091151078114100390701d516000f2403041158203c101b8a030343c003203030070840142d00000441200c09603402071032400b6002d03191a020018001d04da03080d001840002070ba203aa00908a09102403120960b540d1118480368034103454101108129100b0f0309641c9256040386008821100d03602c03500c20301428428416581525230302e034034000440a002c1102c500259211152004120708040c2d6805012249454400600300800c10381203402c0007115520580c465840702c1103c0c40c0d005800c01e03001582039503424680d80c074521078078100940040c5c06000d00700d150741d0660921401144541003c1c901d050300e40041d80120740003481a8000001e844850500206651380304074081c500103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 430444433 1250 430443183 430443191
    0x20409030306080d0f08010e07080a15081006080d09050306070f02120c01360314041e060206090105040803010311010e0a0f0f0803041410120504060e1e120d 69
    0x42e01c1042c4c1041d094480641c0469482c02c0701c102d44503803144916002d01000b130030b801e5990410103001400c00100802410385a0341c0c400d001c1c44105100c00281d00140488012924000da10426050107804640b00b4049640b00c0c0104a414450189c0c81c08802da8002500400c0341c2da03900c01040721000010701c0b001c0258040c45a818000820000c01880e01113600400412114400f640301030016089450080d00340c5140d49032140070710140d00c0d00301c0b40160146413814204c00201d4003007045100700e41c051803a02084900203420280f80500c00e0301118132a4003601c08a5448010103800d0301e0040303070b000b400400200018000101c400071818011003062601c0750000382c961001c45c4070324015410000f48024250300400c41d03035400740d04040180c500a4051410145000c411007594000c6950f40c0e0f2066070340501d190029032050203946140e40e80c80606000718241424503000401311421842114002c00400c503240300c402d0a00d0f10801c000c080b004240c0344100b98120b41c0c583d00111103100f641911 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 430445683 1250 430444433 430444439
    0x60d0b04020301031415070e1002030904020d290f09090c030d02100612050622080f0a032a030f0b04090b060108070903030e091e040516080a050604020409030306 71
    0x380e0720295020750300c1440600c03200410380320002e19000700300085124030b000322000c10655550201d405100201d00750340091050141600a070700314080c0041d80d540180c404203069400d1070261b0031101d46000c022043c01001242c2d91005c090800303148070407a4000d11200d1040031907081811206510017101000d440180710b418000070b0410381c0c0c80c110b200048e4004d450305020b400242c410030000b80302542309001300d8542e5170f40d142c0d112600207000c0c118038012100030711114444000306030590355014044560712440465011615084850744900081c41d0250b0410403144450505e059052004070341e40002d01810001c4025000c80e401d02d54405407107034203d42c0315481d03501a00302d030103201c0c00c0004000c2c906040010b020900c0148a0000c110b4441020008070390003041071100e14100741c816040640e035051490f050080320800c00341440050b1020001407181c0810f40b81440803041200c040880c0c1d98451455403800500c601038460303000034000c90018982a48480d4a00d0f22908020580d559 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 430446933 1250 430445683 430445689
    0x3140709060e1c030c02030d05040302010e3106080115053a081207080c04090c020703020904150b01030614040209041b0816020109030c110d06060909050c03070b09060d0b 75
    0x21803c07403c901040d81d84103130800310f01e0300703100c0006001382030300d40030382400e00e0364000800302c0764245121405441140880d0446010310346008030061504840300e003602400000010040480384503070007641d403030003461245520803d070507074040300c0c00105621074207004005140c40040380106000304900d6403501e10303040c1c85145a8010011030082000c552510228141001002e80082c8440200b15200c41000703d1030240105680545144c8500003c045c201c8000a0745010a9600040d50250f010700c10042006207507a9a080c29500b8580180000014030005400f5074956009080c2c800c0030103140b03918581015800303002c880327400400c041840b40003034802061101d45010000d0001e100242007000101c1e40d0509030320200d840348001c000760303039031764038024244410000000c02e1200d14207900e14642d650100300e05085d5400c50410001d2030b940d10516802010301c207500b00d413240a400c201311090310f008101e000844441c0c10b2075070b141444007010403100c5d41c4070101c10703904035035108021041a2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 430448183 1250 430446933 430446979
    0x1802130915050f0f280e0f090c090f150f0d050309011d03060f190e010b010f02060c0f0906120108010b040f0911011206030f0b0703140709060e 63
    0x7445800041c2040d05080c103200108420a0b1181c1c020340c044e850003842034544455028030080c0da0100e090070305013410405140072143c0c0d4040210074030900c081c001460300c503c2c201400360340c10038200c0c0d80955103882402a001d030201c80702800500d4076000201c148040a20f04605410001c0c0561481c92071000050410a1694419149580089449641c2e9600000c811410310002c0d0030b2a1034200c014400250303683d03c000c1440c05419590000300d00d14814101ca00a4100800c4c40c092000401c003250484c001d080254a280c0010900000703007203018000700345103003d009415202494400000042d080507484000c906e07400100411200580844030b401d52806407458000100340040d100080200b42c44800e0011600b40e80b80c03002e1500041d02d0109001e046400038284210055a201640e80080a5950014207054102090030041003403881c8040c0c4641d1403510108075280c9403030991505914100d5500001c9170714580e0a000d140d0145050442018008001052102d0100c03c040200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 430449433 1250 430448183 430448201
    0x21906051f030b090f06090705011b0b0f040c050d08030417070b0403030623010203191101110702040c0503040c030f02130c1206150909020f040f0e07021618021309 72
    0x3e2040c260501a10f100117208228101c1141d1008040500704801e5075030701d5100c144502410f0040b215078800c82c0100c003d54066145070400012059490100091404100300722170444448084880200340e501d8280e50a407140f03500250814151b5895946040041c02da902d030200711a2000c1c082e60000400812010780320358440d03139020445920705401e51040e00c0d22030008000303002c6010b940b844e032070b40e0020568a00b224080780a14459104e074100741d03143c1281c00854203041d402d21869001c001d400e000140850ba00c01d4500b0015580d00920440b043e020075540100150013120041011403151841c52401c2c1740002d049245161842516004650b03032001c0301001303d10250304201c0f580c40b0912510008009400107000581100d450007040c982d5603009020100da801b054003080410881c003984c0c0600840e4408526141d1540c00002500b0310490380c900045c401d0080d00f9641041140d404411203800e040000e1402ea00d0f10801c030081c0d044200e41420b56182610300040b100c2c101e008030011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 430450683 1250 430449433 430449443
    0xf0525050102090d080d0501080705130b040b06181c0c0b0d0b0901090506010809120409021b070e04021201180803090a1b06030e19111503010608060a0501021906051f03 74
    0x581c0400440e41800d41f00143d04c000080d80091004000e541c8031002c075952a0f0300c003c0c1c0c0008844100b030002a0042440c0c540e01900b0640200b00c80150301d440305044081c07043c040b07031058461000c0b6030082080c243e903004010050101d480c030030409111403001070000c000c0c00090104042c0d00c1c1c0c0011580c0038509900000320180c8510034403c495801450b0744d5000702c5010082c0000e5000c51000c11024850b51003a8080b440d40001c480307901c0e1050448404000210f1000c3e40c00c104ea690395003400f240002d0760141c1c131446041500d1006c280c01481000c5803070400d110740003010502034507600390b9500014000c9069003d810380085c002141004182c10f80c900200e0307020704403818108010100c0c2d442c1032800540d5401000c01a102002c4d5003203a2404a921480c0d00388005062008503030010741c850410b402d03134100480041140c42e00058401e1040000b51040080d541c2d8440c0120381c1c501079815403207210000654201c0126a45821065000c8030280424120320140c00605614105651050310 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 430451933 1250 430450683 430450687
    0x712080403030908010b0321041208090103110703020a0321020c0a0b150a0e04062a02010f0603080d05090c101808070e0f090c100f0f0525050102090d08 67
    0x8040c0c03c425080c001d81311000080041d141c1e03200200390381e0310b0325003440070304c034602c103904580d0401442d0101c0d0003034407450500a5030300255244c810303a16000008031601007810800c00c0107002d08054255012207815178010006050240c03070a0310440b08000719001500113403100b4507107641c2280020480c506034100100702e90070f00380c2460100f101d0040d02d421100b2004417554002642d5407410310301038034000030703400c11651600e14011000b400403210507080f0111100d844981a0300f0320070804414244c0d6002407204805a0304404202c59a41c0001401c12000307000c811410303090780c0c1c031040c0d00c0355050044034186203264000480b842c03078003c0320704006036445401c50194888103d901005000803802171004a00b85080d000d0b200d50000c000301d1103940940005920844100070340c0810610251026810b000e5008000300311404030760411000c00d20100750580742c688510200e4005080100403614070750220001c00e280e0900c10041a5420740d024400d05d1035a41d01c2c400482d124a00c141c0c0c8142d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 430453183 1250 430451933 430451939
    0x406030b0907141014210414070609120614090703111f1107091506080906010f050d020307090204140306090a0b040b1e0a021c05010503030a030e07120804 68
    0x914002c2940c00941001d160b07038410f1080b40c2c555480400c00e2029604000c403c44294503e84000d60249296102c0c003004040c0d925203900042000580c001d03405154004201c0d007031500802c2d598490362007020009805040100400e0a910219800040c030814021500c3c03805203583c100300c40f0341500c1020958000d00e00400c20044100000c503c4141c0c01c0c3e0b100c1c0c40c4204960840034407080860001c60500c201a04c43c0d1018150500881c400b41a21000800668004040342e0506000038003646011400c40b50120346c000d000008c44604030f9601448044025040000b03204031008070340f1049030144201c1c280410503901c40c1c0047c0001d4124205003418441481701014074044e00603080c2001604000d40580c04074500324071140d440750b08080c25008540702e0f0094410215960b0f80c4160345540d2200c00e005802c401034000f04807001c0c5111074511042d40180c00c440c100c580a1190300d602d07070b00070840341107064020f07005903000e0701043c0309441d4020b6807410189080c65850b0030440c0e440000060074 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 430454433 1250 430453183 430453201
    0xd0309090c020c09060d0f050a03030902011d0a1e09020309010c1b1e02061b10050a1103011203030e1605040507050414090903041206050a0b0f0d080f090406030b 71
    0x561140782588000c20f0680c41c035202003003a88102a00c0c043c0a588040c80b42010b00c0f5913803100b01406a4030800700d4407603061606008000340348010080380022a01c1c01d807028200440c0140741941e080050010440c1840c185030740c50444ac181c1d079502d0107291810300011301c4028a20103144504802d100102c0d86c040c0b101002089403e04084c0035100d52000c003804004100034104409100104290a401d604098000035555020304103c11003416500311900d0740d25000824040c0d408400140300340180c1e00c1e0002080d003920b80380a250301034604140010003490380f05101425407640281000504000351385d43c81750a040b1760305208011a085c0304d40170481c1d03017094030841d54004440d140547c2032900300320507450200d558540305031203213080c480030400500c0d0520440f80103149403d2880707001c102e01c0c50703d400a010112070a8011034603110704035440c4c1c10a91151005524014488585812269100d000b030303400c10300540440300c0003400207903410b485504c00c1078007440c0260400070b82c52510350b200d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 430455683 1250 430454433 430454441
    0x903030b181b03040b0a0f020d0203010621021801050306040b090f0412020d0e1002101d010605030c011e03180803040b06010c0512090409021507021f08010303110c0d030909 76
    0x42d009a200704208100210360881c0090b90080040180403e440034620300d154041d004481c05001138610000000031040d811903629814280454407034008000a400050220f01a010300061100341081f1001059882030780215446034004000007090031060010030144041103510602c0c072204582030105000500c0202c1c0f804031000e00c01440c240d4030050300100121101c0302071501504260184510050080c030506e44074138420241048107003030340130781c2600007004400070f40159440d1000110300c41c2000300300c0e0100420706856a0380036024821005000121580000c000c2540e0341001d68040141c1602a002c0175000b80704051310380c181818018011500501010b05100c21004da950006401264452185003154003071501c0d80c4200c80842c015214410000b94803007c603c07862510000060b0141004a0080d00d014210450001f001c501801c101c0c000c100c04a000480100002885103c0480d0b0801c01c0c2c0040c0c0b0420304015001c1540707089410821000f040080c1000c0c40030307000c0c2e442 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 430456933 1250 430455683 430455721
    0x90504080307024c0507090f2c06060d0903021f090201090312120204080709140103030e0607020609031617070e041b1502010b190503100903030b18 65
    0xb00280e000c40c81d00400e00c0c1101e83c200307500001c04444d01e40c010416842c0348121109507513500c00c03c2c407582c500590b0007007929401d4014098440c2908101160b92400702c01681d0740550301085c0202400c81003001303003044800051429a002c08100003995034000103020781460140b10360001c10700d020000c520500c4400c06040c1070710b0401d1401c0b4440d0003503030740900e8020403242c010b0204602e03d00f03904411140c151004d22050078690001500180702c800008024084034680c1e40200844548682011070302c2400f841702800051081c80540102c0c80d04a0092017030300d1009054030324003078025011a041000110360501e003200b00607020004dca0741000840c5281710600d01803d0400d0030036100c000a0440500090310500801c90f043c0d4a424910003507001a19100b03504145200100c80d0090180110485860007070b54409422910108a00717194800d880c4010040d0000004049000000b03100b0803505408141d150318241400751680700f00c206060704203507100680f1b840c014240c4000c03200c0d585 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 430458183 1250 430456933 430456963
    0x1e18091b1d0f19050619081c0e010f180f09020706050604051b0d060503060408040911030103020f010e0409060513111e1203070510020d0e1c0f0909050408030702 71
    0x70070025083c000392900d80819030442ca00040f030b91100d0001c111180440c1701c6016554144107404188541c001600343c6004000021840102010181c00c81d0051012081e503400305080c800c0030b202150044400345070f01c0c0000d0941e03002c015034a030385408501982c0d601041031b281e1300040d6a0b06024490051729402107069030103200a040c1580c1d620307000301e01d003202190036040100381058400c0d41030b0844801000028100e941e20b051030b003005200c81e4014410803450510300205200c269001c202034138122a001004081c41480010066030301c1050a0350869126540b0012000020003034441c3c0d50060765000c2c40c3c80b95041561030078011400350343e036010b880381d022900010814681070702c1a507100541505d02c3c9001090b00103645285001740d40c1d0040440c010310000900c40666030340500000000044240a0005040700540e100c1e031400346034829444a00c000d820016000d4960100c070034000e0700d410700c49a41e481d16544200c907015181162802e200100b8403c541e6810007114202e18007903 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 430459433 1250 430458183 430458211
    0x4080d090503182737051012020102031207021c0f03060911090f0a1211100e03120f1309060602010c0801080a020913050102070c1e18091b1d 62
    0x221310724408020004e0a03039400804010f1481c110381003e03000c01c440d940c68500c02d0300584c07541d9007240002c4e000868842c85502280100045d500f095504006182c6030107030003441ca0700d21202c0417200c00034030051494041d0f1040340740303a04070780f03c400500d4105c1c6078903035030b620403141c45958004050390102d600420080b402d01603a038160108000444032080300841300a0740300384015000c94550100c1c1d5104c4210f010f164010346050040b50203454181000c00c480003800c1841c805c809481c0c0111105909416620641520840c04040750090001762100c482650500c01d4407001c5040e07032a49600901d0b0307010340314038040000c16024058403134140c00a00f0a00c0c070960410b41c126a0340d40d030020010384621030100c042004139105006000303505070040004e40d5030b0b8259003003002c1d0003c000d11501c1d00c94601403815038221071580b505501595a600059500103103110300c0e15000d0038003405c058540c0c9003c2540c0c100601c3c80402444020403103505421701c00c1000e406c508030a01c07001448440340300c0403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 430460683 1250 430459433 430459489
    0xa05072903180a050601060503010e0a0903021905070b071b050607020d030e0105160b040212340e010e39180301022b0903020604080d09050318 63
    0x1503802540d52004200020500301c2d926601c2c8180340460044016209005400010031070319848402107040c4c07018030304052010b480b012410070131550b5000340640160000040801e2000d03c010f41d01d12820b010304210361400c1d4170340d1007100695100140490720f0054a480040030038141a00302c1005201c02c8074001c2c01d00c01240c0119513401c8803802d0080402c4000000300744682c5c021004d5030390030540300d0381d654080b00715843c180041c1c54040c0c400ba4482c0607080b01b01e84084030b001410a1030050914a0084c42c0300241b201703c00b10203064500c400141106042c04500d216888128600a10f650320309003e00d402d0494a000808031440010301c1c1150b8200c0c101030b424060603102c40c500c080400303c40c941e607144000035410100400301440da0306500000304400c07a11340b440c4541158011a50106080100d0b100d440d2040703440d0341034010050b821a40008002c03d55003405024208020341c40450805000d41e115811a4044503d448156125800c0d0800704c0c00c2446c08092901c0d503181e003881090303203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 430461933 1250 430460683 430460759
    0xf04090503030403110114070c030201051b18040e030c011b1b03050901030b040c0f0e04060810111b011a0d17030919050a0614010e01060507140a0507 66
    0x40000c1004e000c0c402c852200100e840425405010030100b408007181103410484002400560000300541c0190b09207800708808007419126640311090f50b03036220346049010020b8028250076003000640c800d54440f482c150781402400205116441c94000091828814401e01c4004a03414842030410036004441d41110300e1490200801d16050b050060b19a035412004902404042c2070b0150024141080c0c4140c3d41c0d0002e01200e4180d001d03449480c016804401440101c0f1058454452550b1011448450900566220300c111080c0c028003c3c1c035191142c0421410605c01e0980022640c0d965605000d0381240a860b40420000403540e0303880d000d4080d1030310082d058000f140e07010003510020105d02d000e141008175091003090b9011244181d02a820000c4c0c4515684070165022401c2c201c0c11207032041c000081038180c1e0001c290310610399003800800c40c1c03580c0120804681300c03803540a54104262040000c0301010388150001c00d452400d05000303104802c3c40a81d018011854485000c040380 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 430463183 1250 430461933 430461937
    0x40503150f100b220510201f150e0117100905030306210d021b0a121203090c12031e0207180212070c032307030c020a0b0d0207020f04090503 62
    0x400c5000c0300d10044000403a01100c4c0090650040c0e038400742010b980030816401107044000d91134000300b4143c90041103121140c444602c1010080c4010308400c8038402440da0b80d01940d0410280384200141136180c0d041119241803e070071100040301040304042048004000d20401801400014030060b00c1542d0750f40c2c2d881c04003034a0544030340c0004211881d00030800c04c4041e12000200120748210700340ca07102a41b1000403220060040158070316020b5242455030f00380d01120f4641d49502207015240c2c5460415001c00000d1004058032403156002160281e00b003c0d001d40110f21140001145601e00036020702e010081c0441c810081c25900782640f900426040308450b2407444499440c1d08054508000f03200745240c090340c504c60344007401030060b4010401c2c1c0b081403180e12440e002c8a003060014205880d80303001005280000c002410009114000120005101602440e0810344903005c80e0301a800c518403517030803d640400c0030030035850000da03000d0760304006490402c541541503c419840b8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 430464433 1250 430463183 430463197
    0x1b0c06050a0c05040e07020a17133503090d1203050a0510060c02060d0213030525060323010b0307120e0601060305040201120507020604120e1e010203040503150f100b 73
    0x140700f91000621b43d038024070030061810343c4110503030305141d607108501c4180e400c80d0880c0e000c024002000420030f000a00314010b88490f00e4a04003120b000d10741c20f0a022540308400b184800d00040c80344907100d44561000c2040355100d0302009101e209103d90080c12280c0c01811120018204414060050001c100c81d5069540324030702455981d03001c2c00428954403507804940d40e00d603c0000c041e90100c03000c01c402002e40b8800e0060701d100040504062001507040c400c642c800e00d01c0c407a4100540c41c080d0f4050307603840800c01c80c2400c525095040011584001342d2182a541e0800020805d101e540007807090b9032026044010445003078007130303140e07941c0e0319050040301d06040e40c4501040079a801404004030030766440c035080c40340303152002c0000e4540720292003c48010750400300011220780119013184015001030f02800352880f450507030010b07a4181030358990550004000104041e18140301c03030640d07062000005421401c03e0383c0c8285e500d0a00828141c400414004107111400f1a01c00321944 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 430465683 1250 430464433 430464449
    0x103150501110a08070b06040e030f0901030b0a05030d120c03061802070201050412030320030f040f030315090209180105060d050448080d050309011b0c06050a0c0504 73
    0x30154150078207243c2069100301900540000c14540c0c104400308684901c42c80d02501d0620034241007920080c0d40c0c0c003501c560100018024020910079504c40c4d4407400031040020314040944d5603a50109082208000303020b00040c14800007001c1011050140c40e01c0b592440c034040100520303000030305510003a84040d00803071940028848095a00c80c209503809030441000c44c030707005c0b081032134081c0062015001c0b00800031403c011621826445d40103036485443c2c00c0f4800c0416940c0c90ba51000701020022044080c03581d200c149402d052528590f1801400080d900140d4a110000801080070030740181280d103040d5490040c461034403140c0542340c010f9202c8601040c00c0d1551303d0a403984808240100c0080308c50020aa00b00c1d0f03403a0060088035a0320f0b500070b05400030f0f1001e206100e0104501480309954032485007009050305c164001c5034010303c00ca0000a80d04808894482140310707100400340065220300c012801e1060620505404c5105100100b24411010b01c0107800c5000e6440b031204 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 430466933 1250 430465683 430465697
    0x7050d02030615210f043f0e0f090108031c0902090c0304031805030309060a111606080c19050a0c15020415020613060e1e0703060b0103150501 63
    0x3940d0f49440880500d11001e110105071928454152500f60035041e829a2005240c280080790000c0c281401c5240510f03084148000010804820b82e001a401e182e08001710400000000044208035282c241c6801c14607550300a58507251401c200c01c443d10204039902c120903100040100c248000125218414664884088004078113403000041c00d0540020f0341103096101000340341000c0f400110301c114820780ba00b001c80310301028412086a81805116055030007006008030519241000e0181000903260146500c0d11700c013030043c203268003000040080c092201c1c007402115001036041d40d1000c44100d110f0300781050600034000310812050660140400000d9072640c10780704440b001f075020b401221016842c0c4207031005c40000c0d03129100720281c1c89060941808514800700712103005100403980c100844110f0348a00008003600060b420301441207000180e000050012107400b4a00110060706040d0700e141031000580e945402098101031404000c00c905003640d09001068510030b2030440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 430468183 1250 430466933 430466941
    0x130201030e0a051006061b0c06052208070303140c0604020d1a15040b010516080d290901060e03030a030c050d0e0a050d0e010819061205010207050106060807050d0203 73
    0xa0a100c2c4024010b041130082000c0d40d4501c2c182a00711030100e601c82c3e518088280c040c5107942c1944201802e00503e843d02404007000051b20910280080c3c90950000b00012100e014481f1706400c070380d5204012541240400300709158020740d0700020a204030124038030341070712010010340342c200081000340f03d00e01d6103e804080c4094801c600400b0b50382030ba9408440d00702000300c03000600c01e03000c119206904040c80140c0a503c01c41c10b441c6410500f9003090b803034020345e540e102c0043d00030b03808418007981c1d1b43c00503d400c000000040d480401c0f80c869041c52900c0704900384605680142c000f0000d229011070f84135000d440000441d00121014640003d0009824004035954442c2c2c020715082d06003091081800c940340410380501040c171a400321159400501e500340e4250000b004e0b800e012170010340000d414400c547d500705a51345c4a909002407190745400c003c2114401510741518280e601017a0241000002d2003004003400340c41c1044185440c1c1008001e0103031152070703150b84055030084049 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 430469433 1250 430468183 430468211
    0x160f090609150b0c0a020405010e270709110c0102030f0117150a020c0f060c090414160c051207030801210b160201140c0304120302040302010504270e030405031513020103 75
    0x9640c85e00ea00500034481943c3d01e8143c0075107154103940b18021602031544164420021290702c1007200e0316140641071441c07400a5103030003442480e04800403c01d04110180c49040700717100442c030556440b90b044240e5418400c11140c40103d64a00380080da01c550104506004502d0060358031034800c01001d6070b24100900d1440c14048124a1080544141c03c14010b2405402c006082c3d08201a5800c0111a550718121900d41600385da286508a0b2235100d00d850310762080311801c158500440445000b01d1281d580f4115a81c0301d040281d00041c07401c8018030400c000d66000342020580c121559559000b03a4942105a0740082e103100342c0b986c101314020201034000e4010310f03104658482204054a0248045031699000715402c4a0082182d00c1c3d082d0402c0c0648250703401d40c2d0301a5112410a030400c51840c005030034030006e01080c0102c9080c40c241480b0b06000d4003c800c49480c001d5510359280c10305040c41c2100342c6460403002070184080085c0c188a10110024240d02481c1c04200340a5620360 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 430470683 1250 430469433 430469443
    0xf1f09090204090c06051801030603120e03240a140402030601051201090203060c090a08061e0a0b030303090c0a060f05090607030c2a06050c0a1103160f090609150b0c 73
    0x4004c0c12103449100005545070041e002e402d01e03441640504500740c208400440440e900b46c00700800300c88504000c11300d054170400140c01500350140440f480d208480c00718408500700b582590380611414410000084a60b005611400c9800b105034502e5041c10707800a80c0762181401050301444000c6e42d80760360f014003500520b90142d0040c0c10794040d805d06551640311a84a81c51190084a00c40c400003451500013072080d2240706102401c2900d070301505000409008054100c03030071a40c0722010082269420700096020340700c4000140300e20780c0c8820a110001080c0c0c0e01510500410a840c14a200d4010040b42e1440304200c1d140c955401d158074040d0361041601c4400f41144c821518554010034070940b1121091202284072660969201c1044405100d06401407201d17410001c5000006485c54052034103141000b0241c0324106850442000c17545c9890b03026500d980d10030350007044035515512440001e0280c1600c00d10526403402150760148090b8810a1503545c000103003c0710404052007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 430471933 1250 430470683 430470701
    0x5031905041e11040b0303090a060c0213111c0209220e0102040e010e0a110d050403020f10020d050603010c02070b070501090b0f0601030c022a01170f0f1f09090204 72
    0x1a481482c81035a00f0318010a0b0f60201d40c8074001c500d000103250441c540042580d81d8104020580c41d001030420100716186940150126040314608840003e200000c5c000d0300d40c0c9001060209480302d0410540c070711142d095180f2412207503c10013558000b51140c400ca81c1520784200c07035003c0d6591007400e0030401420803241c0e10702c00c4c0d4404500800c084c403040d0820f60480310b00c00340a41180d203468004804813070008641110820040107600c40c01001034200780d5200e4024015207105401d2070203441d040000802e0751702d842c180e0008000c0c10001291161075040300c4190002c201d281035220010b035072800300e0b02034120381800200b19902000401d4000e64400ba9000846d01280d05010a180405202c142d5549021074242080003006c10300c001144038244190f00000c0505050980c00d2503005001554a64100702c107000c0443c80102c100c031041e034080c44141a14180310b24010480f4661141d02a2410940c032070140b41105101048a0024050b03401c41c02c00003500c204144001030013007020798 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 430473183 1250 430471933 430471973
    0x714070506101502030a02030715090b0f180f031204140a03050406141204021201090501050411101701031509020d060501051e15090d150603020a060503190504 70
    0x1c0c08000404040000040403201d10803201110408200750580c0c5034043c0001400059005116060201c0c51002d20359400380d01c200e0000134aa030071915025079281f030844030910300009107401c0c444150408160700603818030013806008030f14120000c140d141d2007442c40e11300c91440881c01103410b00482d00010311700202214111034120703515140240c0140c1040c8101c0340070551607000c80c9907a200c247d080f2100002c5040f07881d01e1070741ea01c2d8200a240c0503244404c100700d65a070800100029403d10501e1b0050380142800c5903140b0004080098028104041d04100300e6006106144500c0031240e0300d064a901c280d0301305003050802d141d00010320407010042c1d405068000307840c042c000705a001d40d05840043c0c4e54206170300c1e1100e422627080003001c403a05400100700d04006502185850180c45040710040c070070708480c115a03c60541000002c140401103540d5203000304218900081907400034103030360178031504501e81982040040254880280c2d840c649a82c00941003000650b082510b1219071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 430474433 1250 430473183 430473193
    0x3010e070f0f0e07050d090c050612010311060c06070507211716020d08040609060915140705030103020d020109050a06031e15292b1407140705 63
    0x9510300714034080311449007582d0b48400e203402003100e00203101814031584041e1035040c5041718001e0202d000b4a0076410030f888014003e0804121581e941d00101604298102601519415810b10071b01d092404c1801c2c5101d0001008100c0c4981000328405600000904101d5219034050070807040c100398410040703aa800101030020b40483c1c014115208540541113408240d03901c40b42480c1c20510b000c42030f8000b50344401c1e180300b003803885076080e15805882440301050480203a62298243c038849402201e112003130010050424402c4c0c801d40d0074030b501c2c65062509600345404044d2084c07006000c041d018400065450342035900a8080000500c800361085031034075070712103000303005101c0c7c40120001c20440040014149440d805030030144404180d2075082d1a14012003140001074404500c148844000d02d02c00039040018040d0070420900d004518006040d15400d1129a2410995079111407074810705983c0e483c01e581500f40d0085c20342c205142e4522411074058002d00420314001c04038440c1c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 430475683 1250 430474433 430474439
    0xa06050c100908070303200d020f0412030306080607020c1e01030b030a0b22080307051c0e030a121b031a0904060606020d0f0806130906020d0b01120207050c0f03010e07 74
    0x100f40c004215980c005d66081190140318002c081c802e0040d44400c03000d407002402390706540002540200011130328a0103881c0f4260740d030600e0402901e543c00065010941d01c100c10000d012060128560007070a620144c02c200825500003030702140558130104090b0a1003002d9401c5900039400540d680d00d008044401c2044913140c08801300100300c800320a0500c09031400c4458120344058050310030b0b4082000d0342503503076282040380c0079001200203000b501d00042542d0340c2501c5070311405a200c0e0248000d15030351011440050054000c115140c08841d05c0d10b1200141c1016042885503444081d140210b94004076250345100540d448c40002e60054940c5c0501c01006943d500090841e02d95030241c4014200420041d925400001224008544110300042191030100c00c40c01c0142403003c0c0000d406030858403900c0882c1c00001744150413540d03441245082d5a0003c5c1082030402880300c09501c0c24002d0b649280e1203002116446010740d05e00d5502544071750703080d000b8030010843c0701e04840d80250303 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 430476933 1250 430475683 430475693
    0xf040308070b01050f030304050325030b0c030703050f0105010c033218040b0303070b04020a03060e0d090f1a09040207050a030903060f05240a080709060504060509060a06050c1009 79
    0x14280301d0380f8494010303107040c2c170094100801aa411a01c00501070140030865078a442d070008080d284403105000380d40b40220015800031150b50003451540407503510703450120409030032204017600c100d9a000806004210b5603034030071511500254103140c0000000e521054001101c143c000c582d145200321a12050703842c0d04014041c10114051420040803803149109100448419068043e0103400400250300440c481e01006a08684083c03c0070107803964a4a42400b1502c0d58a4450b00582100d1351035180c0300c1c2d003d10b0b880d0203003055603958440c0c01d1501d45820310b40c0c0c402c5940d106550502060300200781e90345a064440c4075801c1400d48113852034914004060090901084032010b103803001000c40140f031446018481e46200c1d0701040c1003517401401080c03004200c0045036210400d11004120705405021490090803101d0000c1002410310b81008203480c5a5001903004019420400c91141e0b5807a503001e044031001c0c1000b035079446407a42450b042c00202c07444a060035050040000400c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 430478183 1250 430476933 430476953
    0x2205070c080f0c1c05090103150506040b1b010f0203070f0e10030c140f03040203070609030c1205010219030e12070c0b1e03010311010e18060f0105130b030103030201111e0f04030807 80
    0x3c4004d23a8100038a80d845000410000311900a854010b00240400d00030000c100c4000c0407026803c82c0e1440c01068100798060a60b014040342d5000c868002c814029629040300d4940b450003079070305080d5603040c1c00d070b00411882d40a00c0480300405807144801d22901e800b80e543d01c4000e08640c0d14450340c920350345043c0d140c0c591081d2002c178001c2c80f43d4000000c0701c2e407040c65000d060b80c1e03215051842051400380c1800721584061401d0758155800c102c0041c000e041d03000c8500d204240b980300810324501c8241c6c45814145659440b2154003010029400040d400195600580b44480304580e20f070304c545a980c0751007541100c0c485202040010000c4248006084901c05400090360b50300e204040c40014003000d0aa60030700074482d40304560100c2c6080c81c003100e00318503402041c5042800e05100182e080c80e54861390f0301040b241200013005100385a428090103c03950342c4812010b06e4000300c82c1009000a0f4003402c0c2c406e406c0030100309000d54041080c201e500650f00036900e1a01d40f41141041041c3d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 430479433 1250 430478183 430478197
    0x103110c1e030c0a030305040326010303020613032c09090606043614010903051e04050a030f020a090c021608070602030403030c020d022205070c080f0c1c05 69
    0x52584848207004500e0000200c0d405040700002400781c007180350303400340c01403c0d01030012401e100e40c041044c00f440840d514040e201a811007800011540f5505010f400c01001070030ad280c0c03048001081ba00840c0c0c203d004242502000012006070180d43c100001c007086510b11030950150301030061203420240001c07241d000310801c8500300211490030301c007000d16203542d1006484005521a500d0f9014045401e0742003170a0042031404030450781d1038440f50071108240811000301e000469400c4030180300d45940c1e500712501c0c142d0f4516003400c25001800c864a0391000600c0000200110303021500e1740c650080c0103080354103080c0b0620700c5181003c1d4882c02c454480c148081003880d00003a1000b00042c034101100c00a401035445c150440e10300b00c641a40b1000143e802c034413100d107a00d00503124000d0541d84000720030383c08004550300a0280341a14030242c005010404a0017800b000b0421601c01c48100c00101400941c0e5019505c0e20310f400e10340d8580c80d82c410701c214540202e84c0c40780c000005040d5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 430480683 1250 430479433 430479463
    0x2030610030c06080421020f070803071e020d2301060f0e0f0417130b0d020a18030b0a0c1205180106080102120103030f11030313020a0e06010c030e0103110c 69
    0x60f21001e044502040c01c0301d001d401c10001c10001c884a8036840204aa031056034415201c03019082161103103480d299070700c00ac0c0181d00c000f40350b00a2290082c80184080c00c3d41b04004c1c2103060540020b0113000043c20085c1c082d0680101d40c2100e89102c000b41c20180308100001d0010540d54444007002110b240303d0321b401c2490800c00600f844600d05c14440c407070760b13108070403d8241020411003822030300b00081d4102401d0700c5200220b4000c2d030f5074000d00804004080c02594403100d00c68000c050802480040c6260100a601070000825820070aa4040c4013180e0001d0340060440044802c4035610034100001440e22080c01509001c00c0001340c1020b2032140203104456944804508034401c220041e018403480d0401440020700c64094500011a41e04e4000c0080040c0041103045510554a10040d118208404011810051740400082c4803900400d402440e202c40060010307940810010200002c0210190303090313020758030160100b004020b4040e00d800c44413444a90320a00c442c0c507528 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 430481933 1250 430480683 430480703
    0xa0210022703070f0f090c0e0d061a0d050f120a051905120406091407030515060109080706030e210318010e01090311010513020a060807022a0109050303030705070f0f0203061003 78
    0x8101e40c00765081e10700346238010700007408100b46511030300018004016140424070445000220036500d1880c07041150307005501a05444006900c04d6250031074580070407044070010300030720f05440c2c0c010095501070310000742c9522010301d01c05801c454034410381c0712a212250070a014001400200d62017045d40c00d10a02f0404811214240c4603641c480640c800100350398400c40881c4000c100c9600701d590802d4040c10b0803082d03503884029442c2000c581e83c0005c0d00183c0d5a8040b500b154030708001c1e4200d5803007840504004042440300340c034140d110080c802410700c025800c0154101400354404503541c0c1084000300710040051070010300d40910500b05102c0c41d8241004900200440800e100c40181d0082c82044d00d00c0c0307010b82c02d07252100028691020760140040700030007850084c10307203092524440b42c00e201100428001402c41324541c2c00c024000d902c00e00c2000015030700700089600c00c40d0022240079801d1034901d8011a00d48180d14020b40600480c010b01040e0f05c1c043c50344c1805c1d41c4c402c1c5a152 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 430483183 1250 430481933 430481951
    0x80a020c06041512090506072d0e100c0204050c07030e030f070608041406040f12020d0905010309021f05090909010903120207030201180302030a0210022703070f0f09 73
    0x407405000d680a080b201c0541d80030480501e03030080800820071040e80d200810381c1246511103074141001295010041030481a4035078050582007807050511000061401c102d0000340c00040c00c58101c50492401024032480500304540a0a001058540e00503c240505c2c60242c0c11520301e0b40048508030003059600c20b40308850f1401084022f0741c0e00c2c0c00381c0100203291030904100c0c1c2c2424003800a07106040030140704040340c80c0c140f008910072801144c4204110300d40785050005428551403d4007150450440e1946a03580000500102d0700d007444d01152860a070b000081026000c802c1c2001c1443e200c269108040b5000b0001c2c100e890700403a1020041e541356040300d402c0c1e413a4a1002400160707503a1501c10111002c1c1d000e8a1500e00038030001401070390340c01c0c8050050f242200c0960150f4404a41e4940c0c603035041010303603821a24208207506202c0940c1c00c01c1c55911420310380c140ca00c01c0700d0005800a88041202500a003000121510b01503500c80000511140c2401886e25036800d0040503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 430484433 1250 430483183 430483189
    0x3270106032301062420010221160503181603050705101b0f06020d0f050105030106061e0509060d1a06070f020906121203180a080f03061903080a020c 66
    0x14008555880540c1004585280107402190844085d0b040501240503054194070030740150031034001e92503100040c3d6034071928420302c16030600c60a442c03160a00c40420807400182d07048511103d002d0b203040990701c946441c5074105031440c0d070340704404103486141174803c10340c110403010740100c0e130085040c0c45a06484005204d107800380b480c044408102600301401802d0544601c8003107050240d808801076219a07130350041640d01005401400548a231086001c1c1070b020b11483d0f006100860081000d5464040041e001410000d41e031070344e46030450105080e0301c0c05081180c00c1407100134038032035560300104590001005010740c0075183d0051b8038403242e090305168027181d0716280c011444a01c0c0141c0c590030440c146e000200803a4000c12183c17007d8450510801c11103a1887d4041002508c91900080442c0180a2030000c07491703c3d0302207400e8030f0200b0383e9041140c4884015050441d41c4c1c1d5103074804103851491103000440c070320f124000c0020601042c0c501070110912a5801e41e00034101c102c0130 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 430485683 1250 430484433 430484441
    0xf03011d0c101814010e0d05030d050f09071403010603020a030c09051b09060a211409120a0f090b13081b0307050d020d0b0a1b030507020303270106032301 68
    0x1105110303c0124180204658858400aa00c10514208030051522408240d42c480c11a02c12100c1d0350020503240c0325140c450041991002520f81040c209103407803450540c1c0d61209204408888803120b41c519803949003034002c00007070b54014201030070003640c902c2c003540c00305450301c1050225858840441c001310400300b285c840a800600381c55040002080030000258014403520050000c01180706020410300b00031090502c40f5a000014500c2d003d419040b2640c0000f0092846074000c00d075800002d4808038143c0303501c1c0380c46250840084625070402d9600c480b154102d01803801e000b1500005801e40340c00c400c0c05603440d0340181c410091400700100e4a06201c410420b505801283d8207224905201b140049070130300003031065120300d0003611081450b1205460b6103a2468540c071082d0044540c05050310010310607481d00304403a14000000a4032804082c1451591850300c4c005001804009900904002d100b0300003080b5640c3d480c54440300c41861249003007400c0c140303290038826002041c4a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 430486933 1250 430485683 430485707
    0x71a0f2401080c120c090312090a06030e030c030c1c030b010c0b1b0d1a090c04090504110315040b0c040f03060b041512060f050c090f03011d0c10 64
    0x120040d00120500041d40c02020040a80038003c0701030007420340600c5203441007800350039144102c65880460900381400c1100c113001c50401103904204054854650307010503412955640f8000441844000240e4290310030165a25000d1002040710800748501141d010780d101d016822440540d080b414027601a5080d912500d80030400ca52800e20115200c0d100403940107887c04103100083c17504180400150300f0200c61400741698034400700c2440c000c10b40602d50b1031681280d4820300385c501101880d01d0ba200c5c43c000c6443d00f13074803a0f010500b0840383c09600010000001c4c19100800d5022207200b5400008803020b5604501000c0801c0030207409100703c1307041e1040c0940007403040342507494032000f81180036620f5403c15a40d1001001041039801800c018059003918003c40000701e0410a054800b482a00045c0500e4031050140e5421007404a0741114802d40f50f101880c0c0081001038014112800d03542ca000521120003001e220000c500800501c00c1150004d425600410040710243c003002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 430488183 1250 430486933 430486981
    0x60909090f1202190803091005061302090d0f03180e270f0d02030c0606010e060a030b040b04020408010b131b140408030d020a020c0117070f0302071a0f 67
    0xe030301c000120b00c65411201c2181128011980c03026203210104000c941918000c0e1094000401440a0348a0903ca01003600e215610240114180000091042d1040c0809804801d90008002116440700031210b18895006034602c20301403034909000d0030704103049000e850302d804166000b15000e400c4070a1705010307500e0050311011042401c20b21b1401c0d0410307035811611130710911f2004994850b0400904110962590203180c980107041e000380d00d0000007a01c55070500812200495041d1204000d030b64001c00c4130710340494400701c800301040081c205681d0f4981c000d40002408130703181e5415000860f443c2c02c1501c0510725003021410707040445441d40081005c000080c541d040c26a4841c00d17500d0103030310001c1da405240aaa807c9403038515403048102d003075101d40109034000c0701901440f4045d003039117003801d01171651032510020b524102d60013008a800e02c481041802c3c040d901c1399044e94603840e8000040a00c0309030b100740040c182c080071a08000040c0c1c0000025070380100c0c4001d1081109424 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 430489433 1250 430488183 430488203
    0xa061a1f0909020c0102040f12030816020a170c010c091706100b03040c09020c012c0a06020d0e12070c0614070201030203060409060203070e0f1801090b0a0f0e0106090909 75
    0x402e65010358044250540150f40138840443c00c0d42c1141691001049420611000c41c01d81b89406400700e907000707142e941a60550207030f116425801107504452998803c2c072450410030149540c00650040111904840d840c040605960301e8110b0b10b00c0040c2c510584150000417003000b2002e0343d03503204890b100a02c10141404115251207900a503420912a8420401da10f4131581c00d10700b01c0c1c1010107154004ea442d03121402ca40040c00300005042507141005080070381c415841c01e5990a403202d0000c00440c0d0000b05c51080d840340354800d0040764070a205542103807a40700c80d800415008a03006a408600940b80006e100d030240100c1e07018030150806280c10000f20307400650081d00300070030058101d41c84840c18800101188000c51003503015846415180846c0f40902941c6248001e409010b01c1c04c1000f040003c2c900c0c4017000781180c42c40440815050140e202043c19007000b948001e195070340942022682c031412610b100e040c1c828a648642d503080da110a20401d4651400300038006040c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 430490683 1250 430489433 430489439
    0x60702100608100b15180a0b041202090a1b0207030c08060105030d12090c080607020124050f03030d23100302100309020109050a0b04090b030714120a061a1f09 70
    0x10f60b42094245010080c10fa030050031003055000c1c00b03a403104903800307090038100f40c0c54141c1c0d15010f20f015010f4020400c80b0350906003020b0442c8480b40c0050306c06841455500c000a54000c020340015508690409920002003031010b00039540e04010300040360000901e01012825010010b0894101c43e001801041641c2000e0170580c0c0700f0251b424442c044a86505031400480c0c0d680c4404802803072050300810391458100c8000f0300b11105c3c140040c0f10040e52040c034080103890741000c07106a44046030f44a4100301c0942c0040d1562242c002c0c5501da09003043e010b0140c0d60a000403418880140d030b12074800d030342d98a44100601c9800c0d400000e520158125070803000714030903401103108a10605003065500e4136070740000d812801e654003002c41d42400140512a516890080000c00030054004000b00c0f400c20f013940c813030720114074149405007420380424081100b0400c9211569600814104480c10158020544403c07140d41c00c01e0180d0b44040a101c1c200f44028000351040129640e040c0801e41 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 430491933 1250 430490683 430490713
    0x8070f27090b1804171b010501181a152107030905060c120f1503070b040501021009051527070e0115080a0f090203070b0d05130b0105060d0e0d02060702100608 70
    0x2c90a20301e02020014011b0060543c0f091103554007074912a80006c41ca81c0c40c0d500d8810a64114503041c1c8102020450150015299640e0301045403541c0e840c0b02e070300d401c6002210540148140e80e0140d20007104014003d40c56019807080800c03038022415904150b40702081d16803144620021515040300c128001280d0058905040b508001c10188298054034214002031502141c1e07000390403003c40001d002c10266070100441d0081207640f01c030600050303000d611001d4440c0048071080c03806540c0d400010754425055902c92014030304212146030619040001d07541d9402c940c1c0a2a00002000000481c84600d60301d000510390781640c0d140c103102c0d6207080004020b05000c0300b0741c11401391540b40c254016901440350b04003800d030150345d040e114040d1008000036164044c0100c030301b640e03512403008041068903c8032819540d040d04c019aa1300140c100160040040c480541d01c00c0c0590003e038a00140c0c089070030781c000e00040e0700f181d1108602c92001800c4660038030071509a07501a10141a03940 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 430493183 1250 430491933 430491937
    0x30b130b13031103030a1a0d0c0302090705040b1b07090e03070f320c0d0f03031503061404020103050601020d36060f090608070f27090b180417 63
    0x76200c0d18100b220181480c0101d0b00d541c00a0768034100e0203803200014860107030300c140740b40301c503501c00c80b000c6a20300c1264880c5500c40c14140006401466100c4c0020560750040003113400410b4800c0b0006e5a4558041c081c01c070016075003200700228061080d0010305501c2c00e0041004190b0355101031454101c0c10340d6011121004650111240045064540b4040c2c01c418000d214491045804550105144081a08250070240c000380f203905d0841115011691514148040941c142400101c0d0070104600f036142a02d140c0c0014020380c1844070302d203020402070034028041c51003030303c05021640701e040040e43ca40f5062111100041d008850603a182400b00c0d0510403000100c40c1d840d14020016691060070024a8000e0381c0030680c580302480d000e0794020f2042c801420079240c00d0030a814280c5000f02400150703583e42081150865a81115041c4424042c8101e10210203520141ea550030112001c2c1480d0343d0303801e201d031706140c44241d001d0842100051180b50302c43c04150608075032003802c08190b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 430494433 1250 430493183 430493221
    0x80703140612011103090a06050117060106120e0a1103010f05011401030f020c03040609030b010f0e07141c1a0405100b030c0d060617010b09010c151113030b130b 71
    0x159280c42e10294070741d04e42e80003940203d04400251000300c90b14104103007031b5076041e80208848200c2d0603007681c0070280070030034505507200c0d807074000f030703040b40417803116024266080c2c03001c0b1f045c081d0b40d06401c100200b44595580c030003016030080c07040c143c2d140581c1048a0f024450428000f10310011191298800d03840502c1458800b600103082c50480050145560400e80189011030004c540038400e000b030340c10a490040011040c50102c1500b0300301194071f5a980607200700140070003482c49101081e609010ba40d4201d440c1c0c096001d0a0f8035420188020340609251034170724200103800422181811b0040781c3c0310b00d608400504025140021729601035100800450551000340882c0300e50000c1c60040200a12040d901e0046100005140400010041c0d1128442443c10800083d1590b00002d03c042e034a500104004a480300c100498000ba0441e0309284108240014881208504421358042902c0c0502c083d00e441da5290f071441030441900b417001420045580c3e0000b0403941c1080410045 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 430495683 1250 430494433 430494469
    0x72d02100c05040b0310090b10090e0c040305010903020d091a0301030f020123030a0c05040501021b0a1703071505190203040f0206030f18010507050702010c05030f13060807031406 79
    0x941a914111300ca8250070581d40c100600081304420081529940926503012804483c400d94410b01014040d0407071800740b00d0350011020210000d400111580240e40046030000000c0c040d2400b54a4020b4842c04450400f0300815490360010550030804046c041104c2c0c3ca121a0500c1d40c6d085440e503560914080400f2810000180740365029009e07450044c0700c2e605a03184d0116240d09044040e44c00740c5a030301401c5010084140010056607030300007a6981d500e040300a4140d0403200140114018031380e41d410081c800135800c62100603030f44002006090460003400d50014080c203405040d804d03500147c0e40c00395090714000640003481407542c011900301d1301ca182e1236000b10b00c4560110365a81c104850700e49104d1404410031110204035022160743c2440c8400821007450444030141060080c0d0704040d04002201d4044010410304100701c8880b020007004054542c82e624102011000e600e005007400540c450700440d130424000c1c081c11040c0c42480c4d15002c119620081401605004075510141c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 430496933 1250 430495683 430495687
    0x2030439030b06130c02100b09060901090e0a050102031305070b0708040b0c1c0e010e0a08030f0f04030204060e01080d080105030a080c0c100e120a0b04060c0c0b072d02100c05 77
    0x2404a40c415414281170039006000d04981e101020300407200c2411006d401a05a00104100c6541e5841074606441e03600c07900080c006c6002071141c0ca40500004002d2441d0b10003c284520b0441d11850030301c2d4584180b00725a205034446c0c1040b0380d036000b01d50000f003006005210500000d080310003c2c3c00c100405404551032420321141007400c01e1412910311020401070548210596802001e103240e801c820f590a088162401110030303541d10418101440c2000c0215410744100c698808440007107070001e0050200503120080da0754070160070300c5208003074802c10080680040c001c00c0035038101c41c40200900302040e000c1d1a400429480781c991203000d400b61501e100c41c1942c60003a81004154542d0750070301e55180c98400c0c48515141c602e4119071070381c41800710f0800501980d1999a00541c0520082403051042c03400741c030458107514004120031942c00800c0300840c1d004441010045030341c80c598a10510400c00400e503c0320004281e80140c11900c00789441d95030f81d070061200e228003894854 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 430498183 1250 430496933 430496959
    0xb06070b13050a0f150b0613050112060504020c030c010b03151911030a0617070806130f150e060610050a030536010506040b010c11010302090402030439030b06 70
    0x44413034003e07036800c0b01c40308050390f484011142d8620030b4441500045d04e219140c03407807000701c0d800d041440e4403c4904022002080750350340302c2d142c0c003c04014030028000359140c03150000c0164590b086040c1d07190603580f03000300d500c510f4075000800c052b0074205161882400d0315030a145081004104241d49402c03900c0d1030071700c404403c28100541c030800003800c00107116401c09070300104c82c0300c141500a440780c1c01050f040c04800b0001c251070382c00c41c0382620742d02da00c0d0045150000b2840382a400103400a18000405900721240340c1088014161032016070300260748207000c00030119000c04c1c5074400148140f0441c0380e50790007503110316005928070726080f02e00c48041c1110843d201c00b5806910000f00c1c0c3c9040c60038103220900955410080444050066000420000708401841140600281c41100c1e850120344d0007075049407a00b8001030020356591501d801c106108540b1614141c603038694100c581803503402c000745103c0542c0064a034204c50545151075881041c00090015544540084110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 430499433 1250 430498183 430498193
    0x509100305130c03060b1002010c0f1b051203010311190909060b0901080c041103160c060b092511030906090f4204051201090606030b01090b06070b13050a 68
    0x26002584145d1000c07910f000d418042c408600041d02d003600540e030500d0300c10320720039410022181e500302440c075181d8800c159000040000d100729110140c9136000360b06003007c1602a80b401181640e02541c000c0030703000449814441f240740800c40c070301b43c80c202d242c105001d20711141c0c01240c0024025440032441da4240c00000350711010a90002d48035078840304c00d1a0342410140a0341c1401c28004255078110729104807410301c0c2c402140c80540810503a103075540104070a50f4040510082c000e41b0400355031600c0309ca020407034141f0344103003c80022001d160510091013440c1c01c2c58428200780295041050311400d1200350380160291740c2e4402c0f007000c00340c0e440da11900020006aa166400f81041c0343c0142e19050851944c0d4440044021065407040ca800e25035100701c408440707069402c40140303074550104c103004041141000340346505000b4000103200302c00500b01d05171003003403038100180c01c0c8440401007039104000300100381e070890f0000100050310703801e01408218001c90980309400c04642d90 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 430500683 1250 430499433 430499453
    0xc0306150d050d050418060305070509090717030d061203020c1e150d050f0103120c0606080115030303060504020a1403060307030506041203051b030a0e0c0d051c050910030513 77
    0x8281c0011350082410000380da404841403400005240040021034250f40300c1c00c0e16541c5074000c450045a145000c640640c404014617001400308811200e401c682c6d00d4400c60301c0c2d502c4001e6502c859818000c02194615280c4080c00d40d582d4160000c180c101070403c00c0c003090310881100b41d0421a10085003500b50b1b00c070b41101421103410803006070744d500c2400d2100c3c4100c40010341000807620303804005000048185101e900301d039040381000a0305269900d1b0210251041d608100d8065080414910030018a0900700301540c5c4a9141440410307221001e1000328064800c84800048000c200004240200001103030410409025140d45685035120b951030110180c070100c1d02103602c00140300b00341c1c1d418459190400b0700720203400c2451655414070692404007500d42c2c048140c0d1103180440e002e10801c01480707100d0020f04441c0041c5224209541c450800441c24658a5800d0303580e6400c7c1403050b011101149401417041500941e100300c210000c00000b880c1c00d121910000c0743c4000709449441c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 430501933 1250 430500683 430500703
    0xf09080114041a010501020d0804080918040210082806210606050609010c03030510030b131a040203030403080f07020d0f03170601121a1e0a080c0306150d05 69
    0x4150380700382014a842c008010140c0f0281c3e10300400341d001408030780c3e404105c05410059514020009844904008505110310780d12141c0c8900201616208042c0081000e403040b402280e00c8060001d111009440d202012100400d8142011120400c006140d035180c20915216040000b08144c452100e40440000c200e11141c650801c0341030503040114500544010700002d4541c01d0070076071400f001034518800c09200405054503400021001c0c4101ca03ca080219080001c01810f820115440781280403680001c1c2c50300d00c001c174007014a004660b444240101d501a0013540b609145444122203500614501d82400300c007008400f0140e40c8100340c0c2c244c40c41c000e1040580d001d605140c05041c141b41e0950100710195a00108507041e038001381c411009072540700000c80c5c1d09441d0561052040d40840c4101d40c41241c18080191007415a0040030028000780e8980d100ca40d2505001903440520f059030300d515502c14000541c00c010300e04280f4101d0000508640010b80c035542d112420051608 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 430503183 1250 430501933 430501961
    0x60c0f1b010203160201140c0d1e020a0e031c030e070e04061a0103090f080906040306050a0b030111070b0126010e0c090106090e0a09030c0b040506041712070f090801 73
    0x2100780030684c0c0c804002c0345200d054a000800803803914400140c107042004100e803001d0080840c0b08039400e800c0b50080d90440740300d041441050000e0182410081d00008081030014419400103800303400c0c0000c4088011101111000c000c4507000021009004050408481c40c000e40200140c101c5000c101c09000714400c08001c15116000440780030400c00840b0716504060a000010b4041021042003a00031600050465070380c10000001c15501d10543d407000784210b2400b0200580500c086c0d1001032038a4040340207000208002040301c406000c3c03000301a116500c3c4100401819280040c50140c0c41c902e0600903041142d41075401d821510320b040840e13000d03000007210585500c1e1455080303024081c1400c0c050320703007810030181001095009140616883d650304011081c14001c2010203c0d040d4824400001c40c6031500e80715880e42401d0f02d040f161043c03640e0990b00a07100705020740300320030a4440d51a00f2a80d03506411540c00d9552441d90307050202c0071901040c2036000380201d402c940161 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 430504433 1250 430503183 430503187
    0xc0c1a0106020d0e0f0d0309120602030a0b010201091211070b04090c17013b04050304030303050c272e020601080109050c01181d04020301140405060c0f1b0102 70
    0x7221001e410000c007150440108400003404402641e40d40d9455a095070096845264009441c901680c02c110f20360802e0441001c00241201044940d400851040038460787c14800c403000100107a01340c5542d03101c018a0010208071428005200e44034141000048000300c464450341c86109424a034000d8106d49107003910ad11032111140d401c400700c81b0103400034131000b101d50742c0b618000107140d241828103c003880065000041845400903084940004103000c5500a42860719002d40d5a502c1480100c000c01d04110000c0c4411603118262406847c650440c814480007202d000100c40821340400c40e480502582c4032004c000015607035028000d8200402c03c1100030410020b031800030160b00c518156030411034150f0004001280c546050042820000d05581c4030b00018101da28076504080c4000707003448d2112995440c140901d034023540c020380c000c1141003541e0b009180c9000080302d02800d950302940110340d0342c03010b980051520401022400d810101004800390a071500841e9008a030381d00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 430505683 1250 430504433 430504439
    0x19110901020c0307030302060615132718140a1a150303040b07030e2205040605130507030209060102030f0c0a1209080c010305060a081009150606050d0c0c1a01 70
    0x100448041804228020b080e0710745186c0d0300030b5660400900c2e49004102c1640c14200a071108415a0442085207403100e460b0758903040441c810b841642400a045c2c85001a02151002d1521401d0b5180207044440036019459440340000401c42e03c802001922500c103c010204010010f50100e100c41a1211070040c02c10701d2452988170443c0c52114841c1d04104020003118005d074086408440e07140c03c10660030303050080002d46801c0c4181d008850002e00004c09039440d040da91000e84280d1098074100400e4a030384005d0344000c40c00c424000c00c254048a4144003515003403250980c032000500c1241c0c60599103890901c840e80000e0300103481940110204420040007524801542445143c001416840c0000c0303140d442204812803414146e4400c0030401c0e0741c4400c0c00c00c401500c0200100c4405050302141000203001900b81903800d640010607041810002e030040c17030100c5820344e4640c0e0902080103196401031403d6060442408511030481d0002002031000010034003040181d40410340c9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 430506933 1250 430505683 430505687
    0x16030c0b0a06180905010b10020d0801140117060303040b07140c03060408040306090213020309100507030b1311040e01080f0d0801050a030305160506010b0d060509070804080319110901 81
    0x10282200070000d0500e00140b0041031540014208032103612000714a44640b4103007540100b81411042d5040205990704154898002852080140c000c0c0d85480f01e5030399903005106031521010700301e4006500c02004034943d50703600c125150046402001d5078546036aa05a46000e5401280201d0b10003808004138100c6000038400000c0c201c0b4241c02415444c50107650b0300405100b00e01000b406d481d62803200c40155150030400e4002103000c0d01c411075581c140740c045156500d203c0800c0d008078a080100250b1280e11900982c245840c01038640c99002c500903042801401048007800d6a42d101030000190380d020000f607040c020b08007103019100d1841c0320036002c0e041008021a1406220340d180041046440308284c000c1107a8040c6003054903000c880d40612001027203580d0240403841000000f00711660084014460a804013404110b080c5e525014401e0301001203404a010174a2400041d01060441c4000d40d80001d1001d030484032009050b8844085800008181848801c0811104000e513 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 430508183 1250 430506933 430506953
    0xa0e010f0c1e140313120905030f1c1407020a0306090c0e0c160204141014090f0601030c1103030403030902120a0c0302011812050606030d1403011a16030c 68
    0x224052505145404040b0000d04110042c1c41445000200000011820180782c0b0290800d9a40800700000500e01e00700000c11111131070181922a01900701c0030410780307100180130400d448040848a1050800010590300c419061101607103c2c0020000d2a00690b9400a8107000e54400d1703600069081c3e60b4106941c8010343d13504184000710800c4c007440320081c078000950f500d003ca41345202100d59414804140034042c11544060600240028003081c0c09101b4a10b10642c0c070040c010f40061040d00041180d03200080c0c9081208018490101e0440e510030340107041c140601d420600a40d0411403100c07461980215410f03400a80d841d0b00200031845e029401a03c80f860303aa00400b0742140540302c81081208603c002130510403a420981c0ca8031028100d04030081c1040d45c88003400a03407d0416540381c02c01102c050b071180c01031030f200603802405049000c42c292075a62900e403c5a003800300000340c400001c80500414134051001b04600390050300c48a200c2481b030383d9020b601c00494a0700240384 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 430509433 1250 430508183 430508207
    0x51e06060a03060b0706050f181b0406171c0302130915030f1b0b0a08070807120213170d020706050702010c0b1602150c07020d0c03141f0501030b010302090a0e010f0c 73
    0x445034000d19a0700c1278030019103090600603400d0701c0c030403149041000400a29066025516500002c09100c0c422007012550480300986850b4500410164000c00c800320b00c1a40c03100d1188208855082c00f1074401c5a10440a800340c0d0b003682c07285140c50391180b0340721013040c9108558240d0304ea102d1160507100c86215000030014698078606107010100c010748440c0004000104020445001070f089500c2080b0007080d0f54881c24045541e941588100254801c06000309510f8441c040070110803414006440b0008055580c041c14595050036000c0310b855210400903030400111800d6a40820310b1020800c1c007a04482602c050f4a00b100702010b030030318094110480c446407030f80080100c208900d07000c41b119181d04641c0d14007098500d00c1c0c81c001040c9990405080500315958044154000250056070380d5046220207080b0000034944000b0740307209010041c103144641004000604204207803540050386644c02150981561140ca401c55284110324100d0701d481e07182d204801a04229810fa0b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 430510683 1250 430509433 430509451
    0x9060d02130f0b21090a1e02011b08030f04060b060a0305150d03020601150201061a1209070f0302100e03010507020c1905030d1b0b04060f051e06060a03060b0706050f 73
    0x2400c051580fa0744d80304d4400f0b0000310341c00311000b001401c44802445034004441e409242a0000799a00e001001106216003089000c6151780a01d500340c50050760302110865448500a8a1070792501e1b9102c00310702d00540308a0325940c51311440025969408054441c2c0352190740d00040f1440c2c529603451090700c1d5009000e0007000c090001c203020039408150a419039500540a05d54142480001c070300400055000b4141c0800e540251340a0072607080050100c1a0041d00c0c0b000b05445d00344280c4d4640105104410348035403039881c10401402c0142c031501d021030312418050f44010701180400d0a6800403511000140c00131228023410b86064002803c40b234220b400026819401d04010030750383d0711a20324440920450382201070842c001600140c800944c00b60f2801c03481d061524110010b0001c05c1b6414400c9810040011911800d007c2017800300302291103a803016480740e505000c2d0301d60005c2411400c16484030300100ea030880c1c0f64014100ca502c1280001000d00c1c00800314180b544003e805100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 430511933 1250 430510683 430510687
    0x1212090e0a0c080c090d030f050c03071b0b040602030319110a020c0913050601120c2d09050403050a080901060f080a05191502031510030903080a0209060f09060d02130f0b 75
    0x101725158407450310590703645800c04501200555000303841034000c00d252402d0320300c00005e1503000c2041c3c0c4420041352821300030072030300c1564444003d101c25003d0307405503c005a0061000824400d81c0505d81d078440c02c1d40b010000b0b250303214110300c2415036100c4071007580549d00800d2b412446003402c41030180e02c01a401c23841404241680c0da420f032036001c10b104180040d20009960301c28010b0482c41d04000b4401618046490000f0840c10612034003000304d01c0903190b221680000e40d4481c2409890f11440e81a0788407807070210400c0090301c04100240c40054959a01e8402040403a101090f00016143c640010007421005182c41480e158820700c40e200c035010340c0350008000624071804611000d00c00400542c5940d500082200d6864a1004042d0307c1040031b40f07001130854250740710408850003547c2d04e00c40d65603114000c5040c1d1061220881d040a810854080d00ca0ba402001e0103140301c004103110315001e6981c1ca00c00c2640c01407081a400a0b8850b0030410080b410b06d101c050050511800e218 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 430513183 1250 430511933 430511947
    0x8071205060303041202150a0f0e010c0317040f080a09091d121b0114010302043e0d0204140a06030605030a080919060206010801151212090e0a0c080c 66
    0xb03a124091303486682c84080201200404551ba0348052030412400a207410b030300d44854813002004101043c1e1441c0108003032000c00c0d0301c2544501c44800ba00b035010785030360354080030041900d40d03481401041035a4000c0454003030b82c00590514024001141b40341d0f1001d5616040c02d51500403241c2c84214500c8414038050700428013140854403070b0007041078014007034454032025050444040c8280c0861800d5203820390740c801c3c040300e49070a141600c4c000e0f5001c0096409000b40e00030030002070f0b4140c41c0c42103003200c0300342c080610031f500341e821090584401c20709100f00309e1a84e60503600940c0084822041e88005002c09090a00b48800140f0b032901d07003400b00710314080c0400c0c1c4031021040080e05031203000905040540b1407500542000e08118a2400b80b95580e0070003e44541e800c0c0680360b01542000454950001024038580540301440704a150301400c0350346030041021425000818024190b0300010801449a145489034082560100d1008200c0c24000c0031482c00900d0024102d03002d108039 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 430514433 1250 430513183 430513189
    0xd05090f1015030b0705071707060b061e0c03040e0c09030f0303010f05040b2205091603020906241308070e070c120e04020f04050f0d050d03050a0b0a03030807120506 73
    0x34a04480d000760f13001e40251602c560481d001e209402018081926410a88810030241002040d0041c06040d0421514008008000451055034448910450021a004104a080e2004011100304401101d103026600c240b1002c2000c0200c0c0c0030000100302288a0089080503c030b9030b0b0034071443d04051840c6604000420081c44c01c24014507006568412100790203840c3d0803584c0c441c2a400001611055a10003850310107400100c81840840c028851112041c40111110b4401d03241e0082c2064040e58a810078055800d2241011103c04030402801d24004d55844d00206003490804844590160814500d0352801c9116801110781c509440204800c1e00d90050078800a1540001c10b50b103211001781d0110b41040d89091342c6039200d4030004912501d84452401001210415035000000e041884108089240740c00d0014000d5048040e51a1889200c0c0d801103520034100c1400068002c1d01901241102c1619041140858401d0382485000358014502d001124202e07201801180381c41004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 430515683 1250 430514433 430514471
    0x1103030a050412080d0203040503030403030e0606030307030c080417030d1103060105070f0507080313030213090206030c03041b03060c020115030305040b0f09040e03040609080c1c080d05090f10 85
    0x1820381c0f0000015548010403880d03c044902c182e000300e005540340d04081c24000c1d141d80c01650114042032030100c410b942602c1c0030030340a20515000f00550706059080e02c0a171961020120200c07180001000302141d0110f003a5190004200254001c0d51120110781c241001c492030300c410548600014020403103182ea000040710503c07503002c8883d040080440c5800b07031900c0046d03003010206003c0411298000105c0514140489000b16032030100c0c0809880c0400c02c484a0100103500a0342c1080094402d04040000b1a000351240918107110101c6011103003590f0420781080354a942c0300e18980d01e00c95824050020100170f24840c0d84206d0b0716554020b801c6110b544182c942c08200801c46500130b0b541001611040301001c1c105218504003081900e80301e80c418001d001c0810f8a40340082180d550002d2100b080e80740180c4070300071500380070304440503c3c00c1d10312089075015004c00508441030090b00515020326140d200628550600c4c15800d0305000031004204011450002290039840803001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 430516933 1250 430515683 430515689
    0xb0c0c0d051b07060509031506100e03070306020a050304110f01020c100908120d06360b030f0d030b12060a11090a12060501060c02030303070e030309100c1103030a0504 74
    0x4110750b07900d11401404240c0c540c042c5484001e0702031050000b60440e04400200241c0000300d00781c684012145040b461440025102642c110035803403c40341441d8050504180503802c01002c07514000d0f81e0b59101d0040c1c2e480240010001140402400708111004070700080240e42164080035000b140e6000075910054030418a200e020340d013500b004120b0041d007401d0040d01182c0180c40780030540d40c10492003648040340f600c030302e43e2801100060f0701103014442d032171886c8040607003014003400c826200ea240300282e161440e02030340d66458850741e5804111b0030582c2c01c9070303c0181900030043d02c0040c048428804034240140904100e640c01032101041060b1b000034078802c0010072082d0985109910300911904541040c000b48010400389150012903020754425041131105030389800f4202d41817103880304000c1d0160700038030100b44214051492007104e608c02070308582c280010400012180c0703800c0c43c07410300410141540002448000028001d9205056000b1440c040c0c02c5200104688500e01c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 430518183 1250 430516933 430516937
    0x310050a0b1504231f02010f181407120303020c0a0b010f0e0a02040f0e061306121412070210050c0304030c0510030606051c02130306090b0c0c0d 64
    0x100010410496603221240da0000a41640000410300000144540c05030141301e00d50340030212942c1161143c0b4054100d414409012601d000e02e0701d07001ca44070311503070341642d000307654135280f002c8000300c0c640c030422002c1d4444070601440a80703207091400f0b030841c0754403400146410040042c08060700010490340c044c0ea06140c0183e85540070402c680c140ba8418400400c180c00a100004801d0140002c1c2c0040d00c16031a2540119196102d050703080344254455038404505120081001c004540c03004d6500c840042d10100308058900003180c219904e90b004030340c1440c001c1c510901484484400340888000d024000e01030948207103214070444c0101d0704002c0c4586c0c1d0768814464030605c520143c55142003400c048a441307503100e1074404034200c03ca018090248010f1480d41148500c00e004a804039031031516146d00d00140891184d189041c140040004030b03400300311641c1c0d00720b005014980150f005a40009043c280c2c0d1a100c00e071513101801070000b440b02402014403155010401038845c0401d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 430519433 1250 430518183 430518191
    0x615090d020402030106050a0207081b0103091a041b05010c0206030109020306030304180906140709090c09080304120b071d0f0f0301090c06020c10120b01050c0303040c0518060310 79
    0x1000008041010351800250080d002100024490f5001006402c0300702d00c60b0241c4450946801202e595140c945003961302141000c11060304550082c1d00c40111a4000c401d04100c012414010820000301582c01321202621103005210042c01081ea100141600b483e12007110380058000034003c3c0418080c00ca040799001001c0f80c02c40d034040040320000c104400c41100c0c91507821020300024400800140c80755810842c00307241e050220010b00d4480d510544600c03a8050400c0b80210061072440a22001c0c8040d03641c0200f80394000304041d00045c803001001c00d100c1c0d15a803a01d4200d1207000b428050910070341409417841c3e1000c0c41c0201c10a480306807018403c1607405d000254071150244010750b0907500c1c040001040c01103260900f07044d075405800315186185007030709024030b506103140341c94002600c0595249000c8481e0300480f4601d40c0c14504a41800c070424001c504540c800ea9044884428090f420011420440494220094082210701503458400c0100340c40300e071400c8580c0c0d81290380e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 430520683 1250 430519433 430519447
    0x2070f05060106180e04060e21071505010518041415090709090c0b0a021e06100b18240307081b120f100906080c01030b0906010c080708040b0d0501031401050615 71
    0x1042140701e1142d0240440e4207045a1262511500795022b0007081d00c0e5212080c01c000d40e61281405040d0403604041d140885004400c2c2140394401006001120b481e5000d01c42d8000c40300702080307401c0c0c0c41800b62481d5074082c140003d1039031030240580e01683d542c906001245001c108500c620034100c03090740b030229507981d4040c0022810402609250300c60f10008a8541c800480000742451141c0d00d14626114000d07250550600340d4060030f0154080b0881b043c400d51080e00b0300c50b070003d000c041200001c14040e04843c070b100085801c11610380002603204002c00c0000d051740b130300c2480440c0d03070100c1d000d280c0714000e100200f1414004120503003214000c4007044a460001c102c050080c04800e508010450300c0d1981d50380c6591030900000d0003c2c2c00c104440205160000d010341c0280030584031034030a41c0d05640c070100c45030020704080d603030700f04c082c000040d841c0302d204010890845540b00014031581103190203410b03c0031010019a503603152204000b81601c07008409442c0c0940903a8160320303049 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 430521933 1250 430520683 430520711
    0x30a050c19091509050601020a021c030e040e0307031e1e021603050615120a061d1c1106071202090402040f09151e030209060402070f05060106180e0406 67
    0x55501c00c1054500c3c10001da84030000c01c0c43e4040984030020020721068440e800126a50420102d000e5407003507250880070303417504010b448038444078881d040c808030300106180001e08480aa0001c403400d504002589810964050495100b403d44940001c101019084000b081111511281289031b580d602c18010290b00801100003400e0140b6241c841a41c0c50746060354980100755022114028030507c40710251500038008141000355400504441a45480d03e00c0948294a4401100c482c5000f445000030010712400550f424100f001c204048100a002080134030741807c9440f10360800818440780c039a00c20713940714291041e0708015864944090005000748110380c040d80b0354100954001810081c03a410a40c003085255a000b04803d45c0c50800400102c40398030100422000c4981c1840145000b60712150003882c090001070034003d9036500c601055881c41000d54842d131109004000e120703841007200054007503040c0b202c0c114520f0001d1940c0d50400240c80145a942c8980000c400c0c4a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 430523183 1250 430521933 430521979
    0x1e060f04030912060c030501060c03020309040b010513150806040b090f04020f030d0801080c010c05061906150e03010c181a0c07060f1b0305070206031f0b120105030a050c 75
    0x108000d015501440f191400400501c00440800080303030a02c3c0000442c140242d030224610741d00f5030055464100300c0c204100007040752841e41418001d081c441c43ca03580304082d07106400f81900c0c00c0d8600e080324800070003501d0280001e0909104a00340106140c7c2e50310307000940c1360456905501c0e110f0546403031000580c0420106d01e46600f500c2040b4040704001d90094901e13040f101d0b60300685186109031380045030a42804080500301e98444404076808001103a8484105094004000362043c2c0f80ca008200c441c0c1311240702c20000b658580d41041c64a002e00c20034441607640d00703000504141260b00540501e80078400c0c80300041000c04001c14a107058000c441c0c0042c800c0c81610f02440e19164060300801d02e0480f010f0025141008411040c071020110b1202c00b5059101e031800c18000c0d9003008416803000700788160020001c2200c252803490201d4135806030010352040e50f00c407041d07860503c04202050b804288a0741c086070001d40030a0000c103600006142c1075400e50400140c5142600c011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 430524433 1250 430523183 430523189
    0x3120c030f0c09031109010b12090a02030d12050601030b0916020316060e151b0901020a051c0e060301050a090c050c06010807060f02010506010f05160b0c03091e060f040309 76
    0x182d003482c10b009211a40700340c4040c1500d12a942034840031020400348800040d0034024400c21400c200310041540090300180340c1e001421504559982c040c940c00b080c20104d0511005004c41c0011700030510511040c050654411020719080210a0320742e4001100500080d11030200300b202d000307008801d184244201c400d0854081c0e0b0074551426a86001d00040142103c1b00c076942c061241040381d86884100302ca401400c55007000e41d5000030720030300400c0c25445907000d00e05504c00d400c1101c0c0010f0060180020551000c4240d8034200c040c10800781c03850765800d00d40d41c420701003080103000d40d65070340784260141e8059400004041c1c09280c0180c55030700c141400c0d1801c17072040340000102000d001503210b003540d0255555070583d005d0818164265101507880e14085031781604250192480b44c0060201103103c0ca400021a214503210300c8d484007001d5886500d4210700004111216004020540e130b0038030a03c001411210003103c041e6141d41c0c0251844425900d01030100e814075200740b12581c06 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 430525683 1250 430524433 430524461
    0x40506040b2e05030403052b05090f01060602460b0411040207120e0a09021204060b03030408030a030b0d060e030304030e0f010207092c0d080a0903120c03 68
    0x2408000c0070824031180c102c290710220b201422014448050b00c0350003524040c5a06884180c01c0c00b400b100c114541007075803407070783c8104d8003514030200d6040c0b0f9501071503020301d400c44040d210101005000e07500755440ca8102c0c806560008507034403028000800b035609a60b4140740c0e402d00502c0c0345504410f10300d441500ca2520401a1031100f424828990845405148100c02003030340c0120410601059008001c0094080c04c1e10140d902107132805281ea41030803103c010941081b082e16040c0700c0c81203030040e41c0850354286910703080108004142c46510320700301c2c0c110015410140390102865a070f100d603034180e004241c0c441003c40d09580b5607603c680703801540318000740f011240c3c01d089156039401c102c0d4240c00145011200c5d002031700300038003a00c00106041c1d026000b250f04024040002d070503080030b401382c1c100d081c45602d45180724040c071840c80c059802c0003601e03811010040007040400e002d0b0240307246614002c001e83c0042c0c0c0100c0607000004610002141d9010507a000340c2c000d0941080ca0300d2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 430526933 1250 430525683 430525699
    0x4061107030f05060a0506090402100f141813020c120715180312060303050a0e0f1002070303091707150c02090a02040807061704060b0d050f160801051302040506040b 73
    0x20000d004c00e0151081d0a0048104019a00c1d6420480b43d208241da01a400c00036510121f15400d201d10b1000010100e14100300c1a41e5003074000c1040541d101c001070380700542050711a0206031620340d080707405104100a003035040c54803046000340c0307032030580c0244903401c0c1d000204a4100310010b105032840311500031040100030107603e500c1411007050740003100019000b060040640440d480f480f410340e6090b980b0b03c0e0030801626016248034100e2203034a544161121041034260381c0d07021468000c0c108c02d81c00307030005528500c0c02425180d4150001066400410726801c1822400911081120844014210064158801591800007100f4013030b404c41d0846e8108003900c0e00640042c01203035020011036004590301e100850344201c06108120420646201003030104201d5001007004a60041070700310010129a2150702e00050701004031304a0300141c1003114014443ca203440003c14500c0002d100d00d181c04900417400e0444070400920036542d460100c3d2543c3c072242e1202106280c0509400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 430528183 1250 430526933 430526963
    0x522080c0613301a0901091a130f201f0c03050403060213140a03021c060b0303030901050a1a0102060f07110102070f06060f0b030a0b01050f161202120406110703 71
    0xf22903807140b01140c0450340b03004c011901d110414030503043c1e0b5039048000d26031307120081d41600d650f0305400f03840304008050f07020340000800c072801e04148441d88900808460800815400140b0105143c1000e22404050002560040400c5c003c040c5011003842c003290380ca020303481d0584250140380c10240130144040b40c211102c5602542d0b8105031a0851320460054245004000b030000e641e000c02900302c1c20741903004040710a224408030400384680c0c3d02260341802800480d1454004440c8810181e4648090194000c141e00c2010b80f90b4010750759a0021000c13240010795213000242070302518007030400005410030300c60611505903c164a00a658612480c1880e805036011210196001440c14030b00152510400742c0d10400c80e00810a210b040d941e8010302d160080c0f200c3d20545050040400041c8180c0d910ba0f0b0080c4201068000c400000486600b41805e10b201c04002d00c06c19544040c2d010203900e41d408058604840e00fa1500f8603d400003c10f045007003101d2036100032708002e10b000f140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 430529433 1250 430528183 430528193
    0x3050906070818031213061107090912120209210f1e011b0804080c0a020a12050c030d140c0c060703111002180d02010522080c061330 59
    0x1d41040001102101d203207400c0d52081c01751a11500d540120240c80340c6108000141c0601c1d06002d154060710240c4442540d13800441e0180ca02c1040111454061360302c100b405281c001084e1034945080a80443c2088106800329001c000e4540d44007d62940582e00c8030400b0408020824084003400c0c141c171800f042c0300c0306d003610144903200049295400c0ca000408220b0000e0340c00940c0304265035407014603484589030b400050b4004203600383c0314040c1d0040800961503444ca00300003880e0b40e410180c080ca03000d0920f9420702140d503003254420703000ba5101c0660103910070404c58030f040381a00f103503503203042c03c14240c0e1608110884450300702e000070620500349a0412900d1600d075040f0300903100d0b00314841801c0001c911030038401114582285090095070b080496031000d041c1c0c81070400070300d05440c88502c40700c4c0302c002102d0711180c606891400d010184c0f05016181980800741c440508007181c0c201000d0010070140210000400d070000440407100f4440c030f012000c00305009030070800303486c00d00345 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 430530683 1250 430529433 430529467
    0x203011401050f061306080c0f1315030e10050603010e0f1c09030c0603020a17180c1c060b040605120102030105040605120a0b0c04090c0302090a091404030509060708 73
    0x200ba102e011601283d811608001c011195418104075501e21941d00f400c000307640d40700c0007811541611000b40003e0841c484128000c101c900742c5000141d142c1e6142c03204024841c040e008442040609107021185040c10000b00d000d02c6440c0440007043e00e6507500046801800307078440c03001992180018450301c81c41e000c0b0345000d44078003803085143e9000c022142550f200b195403000400140620b0003c0040500c25809010700540c24603000d046e075101420014078004041d2100386a0108540c0a400c8e00d1200700910b103c1008180c0340e80c0c3c54405882c5003524000c0003c0760103443c2d5925400c0743e09a03a91230b640309002070301c80149125108000e000c3c065000750000d01602c0e0090746040710202e02481e15000c01004080c08600805494041e0356450004240162001c0403810003032102149644080c080c1c40c8002119540050300c6140113020403054122a90124102e0786c07410300d00a42c030720301440001d071b801500f50074520b603500d03180c201080051044010103403000c440820260030541603441 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 430531933 1250 430530683 430530689
    0x4210203160605030415021c050c12070509031015030312020c03120f060904020f0d0f2a090603080a050c070e0406020307030e1b19030506010602032d160602070203011401 75
    0x102c440c2d107581c02200300004a101c1c060031090501c03230308150596144c031590006584052101e100c141007103056031072215171030429110540412070200304940f0500342002601c40716040703880240000350b40c658403a1441d1219000240c1000100140741980c10901c0c0c04803440100c20b001125500e100c0003030200300882068607400714240143e408100e5a141030036450b8050b640013400d6142d01e81c000350420a20303040b0f00200302c90001c030b00c1c49840d000c40c0d58141190138400d000c0c000b8600d1602c1d01010b020454801350403825500745450410700c04903c00f8002e69400c0002810000c1d0740b585481401c601d844200e60002c10200e180d2000c210820401d40c010b0350050205890a0025042000c101900c3d03100302d00d82402500f86050104009280c58070103000c503920b08003c0d0360355041d1a038854a09006098104a001d0f80c800281034101d60900d01e0310324040c03c5548640210300c102c040030b06110307214100315540750780410780300312040c4482941102c0015030300170001c000300190881d032042c2d90f0100344 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 430533183 1250 430531933 430531943
    0x3020f120f0616201203041b0e070906140d050405070b04061e0305150f222c0a083a05010506091309030e030709051b042102031606050304 61
    0xc00c4a143c07849031824040303000328610029040300310240017500020b07000144140c80d506104130540924054010101d809003e0701c1c2c0581c1d003146040c1034007801c0c44006030305c01020840c11000d515081400300040d11003c042c5080041400d0700c860a229280c07025a4001017032a210000340010620341182c00d40103030003040907540030302c00b814800607803c440c4100c4d48591069a0318189260600c0d1990803141803481c0203054044000e9030f070007800340c0161a42c585c0d82946641c0c441543e00e0300d044030104007880982100d41022001070343c0785207496414a1000404090001c528091982003a90303c031216101c21500c00c0a08082c044020032a90400d2100d05d6840c1d03107850008034850074002c040328407840e4040d041c0048d01c40224018401084d44190a8080001007802c0c020182d40c144144001004c482d0030209050410111030522050070184030412600200410000201b0310081311031048400900c010440795079001280c1040b8002c200042051b540f40c88c00305010703402401541c0528015 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 430534433 1250 430533183 430533197
    0x602030d0f05070c020d031b0303021b071d070e1002031b030f07150f180c050d1203090510020c030a0905040204060207052101050703090203150103020f120f0616 71
    0x107440348034111002a111000003401e002090000f505044601c01c0e8540e00c203140101d81c00f10709600c90400040c1d000ca080340002c3d0005038203d40c2c1c0c0c80107000b141c0d41d00030400c040d100c25450301301c0c00c0c080010310703801c042880302d0404d00051009020b00d940d401c070714001a000d05c00348111601c00940701c0c2d0129040520900c1d09018240c00c000000003511105442851220b02d0b008481d100c5603820065031500d81c58194039040c2000092226000b070310000c015802c025990b1455900c0e03c42c4c000e20a54024501808045819402083c0c1b1903d16450b4801d103400d0000341c80410741051070502c01550600c090300b80c00013940001088000000700200c219603504c056810380c541d402c020036403203180308440041e44124418050b6103442c0038038040c11080c007003541102c0c0d82c0b10a40542928411200c11000c030799980081c9082d81024480d480080302a00b110403601e44c1107500083ea1040780002e840e000341c10342e031001d1201072000c20259010320b00b09011101d11b403400071f034003450f80700059010302d00007010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 430535683 1250 430534433 430534451
    0x60207060518070b0406050c0f0712021002030a0503010504050a18030f11071d13150b131e050a0e060a0902032104060503070311071b1508040b060f0a0602030d 70
    0x2c089145802e0b01e456030400c5152a2410804403803c3d041045010524052180100d0306000200318400040c0b00307000e07801c40012010300400200980c101349007025504200204202d456000f81240d064070003c40d0000b8680e00c0303110b40d8a0003407090340b150b82820203403106c61005051f000701d102005130095680e03081c1e421001040700382e21903c0d18032803450400400c55401c0c680c0d12003035110705c0d40800749030410207a8100316140d001030488025107034100140d9a00c001462810058250407002c64544000e0040705440b41c82c01840e0700041e9071110519964074081500448141c04c4600e1010801e41201c0b2603040070138084005098101c000c910a10a5000e20a0014241110310782d8400081a18038100391a1010985417940010034002c10199100300603940d0841c110060722089025070b1400c0b11388032041e01004405099504226003994020075a041c1b0b031a44800d00e164455440108030810340c4806000c40d000101410300c00345d019001100105409a00002a10600d0b00403031042c400511 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 430536933 1250 430535683 430535731
    0x30f091509032a030a082505030d0e010605010503090d080702120c0c0901050f0a030303051003080406081512071e050a08060901150302090411180a0b030c030309090f130602070605 79
    0x2000c013000400d08803050102e0260150f07c115000680840420106002113090340e8107030442c0d00100c80740098603a00d04040c2590b400912075000900f00a00700b9500d181410f403038265543e0300310851141001003000000e40364034400e100321812420709500c1c1c2501e40c1c2040803115100d0700a00e0180d4010550000002000c3c81e1083e454114000b000d00f6a02140313040d0303142100038020061200180042d44100040001c02c002c00070301c002e0203e66600e10303041c1007400582000b6084006200d11440a4180300840307401c022842c101103410814010003c000654030a0000c0b03106940306070350120f245940040e01c1d100c0480d03410700c18501e20008101100390441d07010592840c0f800040e402440340000100054900046194441001000c540e000c0003000001c000c0018100c4000340032507118100000307681410020404265002c4002e035090070310041c049038408800603c100308164040022410010fa8190701d050200d030800301c00e540d1703680d45d0701344540500415500d407655500030500d1000c00c0c131 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 430538183 1250 430536933 430536943
    0x1d09010c0507020913200f0f1e0f0406090b18090c010f05071b061701141005040305120909150a060302210f04060c02030f091509032a03 60
    0x25035495140c24115250280066030600a0500350010249420070000c12401600e54400c204c24662500124140d030b028045411400c5003280e0040c11428020355043e0340d0b403d0b11188050b50007d0f10044149500c00040a101c40c0d0740c0c030a508a4546100413802407011b402030b0703080c0c0384166072813400103050344244410280100d480920303036080391548010030344c03041c040c800300c1120600c2d103c4d0802c107407511202104411381000c60f83c4a10806410841c16800a8168580103180f40e00d0300100e40c03602d03c0030b03920b40b40e0304018284070300110500e113504c0f18010f406071009140c02c2405c44010a400c030301d0201540d4000d130181807248003070100151501d46000d8101d485000040d2402001919080e800e9020b50402d40d10f010b24003206a220200b09010064028800c2400d80d07031480c0c040c24541440e0049800f0000c84404540003040b142c5006401c50049401d501320648031a22010940c000240b8140102081e8a506000c1d50084504080582c101c6016a42c050003418491006275810582d8503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 430539433 1250 430538183 430538201
    0x20c2d06071106070606090212070f030212060f0307030f05030904052514090d0302011a0103090b040b0606040b0f1c060807050415090e0a0c140a030b04110303041d0901 74
    0x84420b600045402e0501c04090103010744078038404211143c4404e501000c1e604400f0310011510090b40802500e07030b50158910301c00801500f411454104001c000b00b1a4580081099005945803450100503490403c424002150081c1400702412034615185440c1e40c800e002c098400e60414010800b450b00418090902c40002c3d680c00d180a090400151555180b0800c02032a50b01d00b80f000c0501d9807100c2c4101c0092a20981c0001103081d119440f0001103511a1101d034105481d00c40c81c03a0006100f802d0180d0031541240301c02e0000d42c1c8000c00500c5600c0349070030182204001017070305c101c03808000000d040e0380409401001e4000200082000880d034140c41503600c550700c40d01c0c0820050520354031102e00703c03440d46d5402054a4032200c01d001a203045c0c180c0c603680307680406410014841c00d0443d41001e00214456000300001440c002002d20305d00e40030152a08240c8400315003048003001054845c41d40147c1900c1e201c90381c0b40040c0300c0c10303616130b0614803862080c100040c08103c01031040201c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 430540683 1250 430539433 430539443
    0xf03180303130b100503010e0f10020408060106122703120509030d0b01030603140618010c021218030106140316080a03050901020f01110306041103040b041101020c2d0607 75
    0x702c0c0704652904032055601910294a0345400d6001003200c0d10203000c0e514140d0404c0b0002d02103c4005a91301e4502500300081c0805c0d24030600061058060100703015044403a140b90111003246102d0303c2a000b0015503c030818048030f080f071440e60349410010003c0e0882c2c0203888040c1d00d8483c40c0400000d0394030447e000441c5410801c95070390540c01301e42c0600056101890700040e5581ca0742d0710318a54009172040764071550310100030070001c80f04003a062040880d0031402801100f0710501c0195841b01c1010820740030000100745900401c481100700040390800800a2000f80d0342c0d194060240701000202c1c130b0090160100d00c1e800d4101101c909411510044010141c2e00d101d5241104c1c540c200319103160440c09150f0950b00cad10a001d0084000141c41000b646540c0d0074407008000c22201c6141c00c1c010b804505104010200300d18080207a8045d400043d00c1200243c1000102d0500c1071084900d81c0c40360020b100c55103800e01c40b15025500d4101305280c4e01c6510b41d640d042003c103005103900205 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 430541933 1250 430540683 430540711
    0x109110702100f0203120a06170a0f03080a0f02072109060804081b100501080c040e250b0414130513060c2313210204090c0b0f03180303 60
    0x901d0a201e400e45540504080c8180c0b17061003041b54a0611003031007959010890b984804c4280401c803403007158880a040a00c0003008030f41407aa5408403041460b00c00581408098000600101e40a812606445429040456881005262400d1151003110084518048004010801a008101c3c0600b42d80c4140c540c004075540e1581e806440c0c0e4040c002c03c0c0440c0c0d52000e03070b02041c01000c110301804000c1d5040080396960405205500c1d01c1000d02000384a6400e0403840b2040003008151150003901003000007545c0e08880e01d050b003194806078412100b2120014001400c10380342d02110400e1507048072600f1108511030701c3c071416118140c80302c07160400145000b40c001821a8000d000805603818951041b688601050301300d12521224000c40c1480060120054045292010050940300c1e01e003090a606035801d0006e84810b6540090041d6650317078602c0c0600a4985854000708040c4c0e846075541e403200300d0325601e250401e6419065060920402943d801c0d00801641e12030328101c030401c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 430543183 1250 430541933 430541959
    0x4120b0703052802071505010f170a03050d02070323090114042d030f03080105130c080106050c0c0904080403154206020601061713060e03041206050109110702 70
    0xf40003540166000c942c5400d55410003400c1c40e15602800d4020446030314425030451074607041883c2c01d02c0b01070090017030350082200780f400203400900707442c1d404540302401030706c1e228a4501034810185081200020720709031401841d40c1c0700c1034001420320030001ea0728042000200d83c46101030f07020f540610a01d250201d0a00200c032416030400300f0991550149800d4010342e240c0325038013400c240e40410380c0018a040018805805d1012803941401200e48080040501079100117200b148180910b40c10000c00050610440300100b013055584000184078201c0c0342858500010940e00034481107030450030044549024442c01d00c42c1001d862180c580400c5c04000007038806030618034040910a00c4000805850700c80706200ca0351f40d015220036001004e103941000c902070402008002c6001418074403030100850903544111b03058110303a020102059001848035018114000c64010345c103880005500c1c1d006201c0f844e001141245c0300316404122002c48180c019a441c0715440c806504103040004103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 430544433 1250 430543183 430543261
    0x5012c071a0f03100e0c07020a18020d020d050621190c090f1409012c030c0607020a020a050906060711010504051003140708070c08030c04120b070305 66
    0x404403841060740c19440c10b2502140c04040c0e402c103844a88080421810a0281030032500b030342ca800200c481d610500702202c80e070004920a52601030292001c0300000500c103d0304054068070b90030606900155107030100c0d403501d6070041908039502442400389107540d0800724104030303070212102841d20141010800300714819511728141d507012034010340107800016500300944a084a0720619440104080304483e0742010856000760908042e0f92400c42040e1045035804402040c000c15099006031104140551500703502440c004501c190164a0030482200e80c0072a415943d14400c0702c5000c11251184240071088a040341c0d00c9030412402c10900c00852000c40c4060300d1101d0514040746000d8130f600c0801c0102c014031381c40320082615100202140d81c2c000c0c10840d032081e0705280c00c1000e4607203440300420b0b80000000161212a001020a0320404500c00302c038090315480104107014801403402e8000c5450403114100001d02e4103000ca80d000988030340d1000c102e4130000300c140f113240400740301c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 430545683 1250 430544433 430544459
    0x80c0307021c0201021e13120c0302030d09090606020d050a050d0902060d1a0402030f131406010e09010b0a030213020a090f080c031c02030703030b1c05012c07 70
    0xc880940c4562001412507444005030301606001c036900160300e0b041c80e0140c090320405210401c0210307184c10301002d1002040c031707110242151040c6404801c640090308150038806030a4001a4240c01110f92004406420030007160441d40441340800c00142e880d88102d860b02e0410b241c240c0001c80c2009070091043c41000500640742701080c002641402d168000703421540012581098552518800d4414100c0030340a007071540d406132020361940c5881c410014418400502e420020360b5045001d00a2140c41c48000c009056460203d0303689584561400d0308003101103e6014141d800c01105041c54100342e032610084030790241c0100b2000c401d0342054006500301200c81c0c002c0001c186800501c454480c004d02c3c008148a50180c04804000d030141410000901090a141002d588101d01402d42c000704507a03526400d0310340001c094040000042c83c8840e0b81000343d155032040004481400019402500f42081009910501c0c83e408002c44041048881da0741a0540209008128071a25081 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 430546933 1250 430545683 430545691
    0x60702030f0d02010f060b120a1143030801030b1807030f0303050601170105040b13050403020607180305030f030a15090204050103060f0b1b011d010e0c01030903080c03 74
    0x40c1d07490000010300c05890000703542801c0006070f4442000b00120246846010050007140020b1450b0003400e0301e996402145c060200007031959500e0170030901040e44800e84d890b0307600b8800c0c0c0c840201c10161812120340444880c004042180e030344401d00203007a800318400c03020b078980c440807a268030f180c44011075810014000701c620100310341c0a031000041800303032801852041003101010041c60400400701c940040003030307040c40440412083c03441043c0c4807880c1140e50454000c524542041c0c04510710515403070b220003c42d400c05041c0f004140d004075840d0710903c0c00765158000010300704111505440c40341300140040c0c004001c2c4030740b603c080000071603001c514a400400c282200e4500b09001034569408591010b60105080c003081d85e041c0181001005c3c0645115039560904121007003d100e0100f541e00a02401200c00c01c0c09002900034412144440d5404100e01001c0c4040c10b018115417407216107280510340b840030b801d6000344130301c0b007056415a030358800a90304c0000407005a1b0002d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 430548183 1250 430546933 430546939
    0x405061324080319020f0a110402091804050c0411070b040f080f070308010b03010308040605071113020408070503010c020d180503030403140d03110d090303090c09050123010e060702 80
    0x108000d070124a0541040008024540c0110364030704102d05501c4110f0101c2c04114119048001480d526032800666090746a4004500f4035840d8130480014009204e000112904820b000003503100c040501d460491103980034400340c410074135000080201312290740c0f4184010070402d01c20000800c1d00242c10340d0b401446500082039904294070388001a400c000c44d0354840309030002e000d60806600a40d0a070062034941c0420b4210350441e5100c200d40d004501840c82000b0000c40d402041c41100d1a50400b48207028011040e0100d114691501942c800d0003581c045200d03000d070018460605218004414616a01810030032900c44001c17aaa296103142c0c000d4420300320340d000b2406a5040c0000c1c030045200d04071192609000c114103a041a00c18a903503002e161904110032160303650300301121805080e4100004074442c2a150036401080c5140e0081d000d005085404640340c40d280c0e002a040e600c04154041440010b08030f00c01d06003070180e90701d0303000030f520301c18031100b03418000042d0180e40d20003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 430549433 1250 430548183 430548221
    0x302120c011503051f0603020112021804050a1a0105070b04021203070503130e011401021b0301230a060509090703020432040c15050f0f0c0604030c020f04050613 71
    0x14503441c541c060b42600142c506030440706403065880c061401c02585003c407800c0c01e00099280d0b0b00007820f01892013525815081c0c0006560030301c20155040704d140400000c104010350304244208000402c0c072841d02c00c1181011564800266000b402903c039042ea0007071641c1c3c401d0341e0319400d0001c11046807128424034441440b018000500134009064034085040392004c8140c5492010781115406901c83c40a04512100c1c480c1e499038003080400201c4a0016072003c0703440d808c00403030f00503d4101c601040b52104182c18000c4181c02540560140001810130f02503262100200305031a1015551003202d5840414108014145500208508000000c009142c00c4488103141d13140b4901000101c00c110403042000100441c1014004c06020095000045c1240961000d171651080506082d17160102084018010260b070088981400503041036400504051074054891500c500c0200e104019003481c0d60060304062203042d07c40c00b0300030400703019182c0c030071014401401c814102c1d006c0d414031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 430550683 1250 430549433 430549451
    0x309030a0602360405041425140d0609030315030f0303050f1302091003020303040e011406070c030303090f020a06120b0901141309150203071b0302120c01 68
    0x10038450348822034041c41d405a9280c0d030408044a41c02000c400b403444100078450707036000d1030b0b03101c1d10b0102c0c0300e4005460006050320345007031840495556030882000ca02c10000020700c200f5200d10800700910301000c50804e5140c0710001c0b00288459441c441c0c0d002084042e0203000b00b1080d07001000958028200020f5510000c039a10010012941040d221284004102c400f09a4541310b199030142d120911582a0b08046850150800c51170401030320507084007000c6041e140c03061050344002d55000303044036070361640d030305164015110911400c0c3c91a554114001030382d042c00c400301e8840315031080321090824110764069004251034902a00c80d18030040d01c440040e215800000b01a0265451f03030105000c420105400f03860f280c16000c2e004490120041060201c007010018042c50110780310423101d00d4400d60359004002d255000b41518100f8516511900c1e241d0f8000c50042c4482e507036000030806044605402c11280701e00050040c0d02151991140c24031a0024210880462001044079aa = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 430551933 1250 430550683 430550689
    0xe060c1c060b120f07080a0c0203220501140a09260f01061404020702090f040305070f0b010e01080105090606010807090302060403050106062003040b0703030b1c020a061418030309 79
    0x4602d40021200c001c0c0003d0440411a6181079264410b20310340c890b550610307150b0401000d220010f030034030544c1038480e0411543c841c002c1c4141c84411490720070540d140350100c002d0080d10840f40c4240e5006c42c81c022541e0306041c0c4014226400c1c0031a0b0344030094040c1c03512102c00c000c000d80000246c1069141c0181080c250028800c00703400d1404280003045003410814411a40c91180e00d841c2d20070b9204220003801a2600d0f448964408001c03508207041d07540c0e0342030503519413240e07281c0109201c0c090403407601000a40c1e903450f4181c80074814211500c2e81c03103402c80d0703080b80c00986640c1050307070040300051381c25842141c165a000c000c070302d425040d055030703035011030500d030003030740080741c0b1a51140018840d01c0c0d4440d413010407417100140d881d00b00c8000c3c4000c0a03107a2003a80510343d0340c80740000340e003001d060090700b240f12800b03c05850030f0003100e50351854030013000c10003004034424445588000b0740b1501c14086450381314014404180b5100c1001c12241804813640012501408180b083e0a401d076 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 430553183 1250 430551933 430551941
    0x50c1e09041406090703050a08130e090318090403020615031f0b040f0c0804062a050a0206101406070c270c1b1b0503071403100e060c1c 60
    0x18801d02c040046504401510790602e54002c001070343d190b100d0041000401d00003e0001c504641141c1320036039904584400b513030602140d8000a10507491101070015501001000340122141c1c82600d0b00b025108204202c2e05881c140c0340500140c2c80b2101250f007180003410300c40c1030404003c08440c061a03d486105607644101c00c00e8042041e81c80c60100154100b0b4094010395100c4003808025040b0040c501411485000d0f00140a043e0385a10380d421961a000310400415483e01c209244561400c2009040f03600c074014080041c004c010101381c884600c40350070b10a0303c00b400141d81098603040148440d5070000c07a429590f0b001026000220403c000020151080c205408102003192010ba4901070b0380c0000700720300030010201e02d28810100006110140203034803411100203000d40743c0c455400b00610790010355160041610014020704840c80d50211414141c0c140d6010356001c2d4a03440498120014400c801c0d0050070004e49101c0c0d4a00060a44100e522005103040b8a2000418100d07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 430554433 1250 430553183 430553191
    0x3180703140f01060b070302031e0c070b071b14010c030509060c0c010f0216061101150905010611011404060b01200a060501091812051606050604110403050c1e09 71
    0x2500a0b103284500110207003d6400641041242d80b45400495640290340784215090410030302083d4040e1294001c2240844542503a0703c000c030350216482c0c80407a0b01583c081001210780c503068189043c60700703020016120450310041c10050a4068510040d906112010b40480400c54100411810303a9030310b00c090903600004400500e9070303030700340700000d071804017041c1c002c500750b60116031070038014480c520341201a03d110f40b404001c0c0156a284e81d81c0984660351680015668540300843c407605180d112034125443d55484045144015040500302c1e181d00080d4588811200001070100b4040c0e00a80020941890309180d440e00c810781c0600d8103007515813052150341094100f6800d024560241e5800352080d01c404102c80e002201d44541c0c82c003600c480c001d060300701302c0e26000403460052003a030b0b0030841c110b00984020451403404c03400510b411901107203d40d02d0079504507948110f110031340c1e040d03d600000626201541004010a004406081c2500a85112030200c40f0b916602c25060117 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 430555683 1250 430554433 430554473
    0x31e051c0f06080a151112040b1005010c030806040209010504030506040605040308070509030a0f0204020d110d111312060b10320409020c0102040b04080a0c0503030f03180703 77
    0x30740140c1d000e000581d002e07540802e649a104986550226940c008112101c118040001400e1000c2d90201d00050048448540c0020989401c01c0103115034400a00c4c8212112481c4048950726100150b504040e41d010140000b18003000158003405c095004100040301410203a081503a290b07901440c0c03031011141192072035120b80600003010341100900b5001142c600300b450134040030001181d540c110218001d001070255074030110a40d241c40d411900150440e6100348071070343c03060344008101e501c00a80003203114a4862000100307039900040d00c070701c590000c800b45411840e180124006003843e20094071442d584802e454960343c0d9131a650300c4002150b884036145072016480d180352170b0f02400e400d40c10a03c1c40b507040c3e17a005540001254150360035100f00684400c0440c000c2402070040d0740002503c4000041c0104441c1c0700042c111140c203114030010f5403010b441d442415101d005603c07c40f050b00d071007440401c0c03140c0312080c3c100902e241c0c1c1c6c2c022242040d541e074039041f80881c4041c0101c82e03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 430556933 1250 430555683 430555691
    0xf03050307030e011e1d04020406020706140c030301050910082a0a0501020c06070f050105040302061f0f0b07030e150d0e0c031b0109080601090516020109031e051c 72
    0xc058012203582220f400c2400c2ca0044400440c902260031005120a4810090550759883c004009603907695076034003021b0411074855803a003034065543d00c402e01508001c12984c1c03042100e40340c0c090040b201510600d00107181145d04e060203104110034007610900c0e54010820010811403810007418099448800700d0b000001d0950110b18144580d4601e00e6006500150043c00140d80010701c4c1c0c0301c1040203171074070b540c2c8485504003004d20310180100200715501701001d120a02d54001140e03030240d408110030049109454240001d60700b43d903c20101c8141040c14200a9083c889001d401400d010b4100a08000c11130000101003410b1003503405c03c240c20104034201c00500c00d00c80c0510b858614030007804254030200000e643c81c8407100c400108a514600b860240f41d206014920003003000700100c400c503584071082e4202512045601d0a021080b00e807107880aa441405802c902ea9050340310041c0c10341c8404000382c0c07203820b245003400610104000c64513610a11042c2101d11042410f0006 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 430558183 1250 430556933 430556947
    0xc070e0426120108010c1403180303010e09010e060f060f010c05060708010303020d020a110d021503010303020d080f041a1f06030902040e010b0a09020a020109060c11010e0601081e070f030503 84
    0xc0c0140c041a007244d8400c2c2e240500740000e50790011210403c107141c540561b0b4a90303540015032603008000355a0110580808000052a000c0d01100c140c0984401d00085c890712121030001e940c0c40004540a00c0c5501d0008082aa58108044c0300d20f070303000041c0340134502c44110b174850074903000e001d9852400013107011004000b41507040c040884d05480a1000d019804080d49a074a100146200b5a500c6070125400c10b1003155035407091207031045000b801185d101d6035070f410007948460510172030001041c003100000c2c804403144840b691165601036070350000e6000c1018002c006000040c0402070324400f415103107044810307010041e001000b0765178000c03c1d4440f0b03501c180000d554011f0504010781e37040c0000002c840d55184080d000b91500050f006840d2400c2280c1240901000384001d03011a280030010300d00141d00c410368190428070600240801003031858031540e6420f00b4030844120b5040001039011400b42070020b0f142e5641144112051307551684a400480303175060b4011a4198400030360b817 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 430559433 1250 430558183 430558207
    0x3190b1804050606030f0304180603050105270d081617090c0307080d0e01120204030b0c0304020f0f01080c0705160902040611010c020a030813060e031e0c070e0426 72
    0xda58400301c194003030100780d075181401b607940e405280220704588001c0491066400300c941c0c028030003150010000c1c0028100070a05d024042d4140380c1841d91400503140e070403080c80300040da03a20360411b141d64003e103c0c2d07a80c1c011104e0301511003403410104501030319840052032400d8001d030f0161920703e0242911a0a100401d0300d8200564020340880d0462010041000d80003010700a01d500700703081288002c0c000c2403440c8001d21541d0002400803540070188260000745a000d0b510a0b8801d407003942641d1680c40c200419600c840400038006042600001c004a00c5003001e01002441361040700d10311003240c00141d00d5845d040d00400340050b4045004c21a0701c1d4018032459101c01010002c00807600003074402034442608030710203401c1c81070100c00b103a00c5000e405203c02426030441001c009414203507100c41d403603078003010f0607050160070001c40f4482080b49004a0f5112070610000b4140d513860300080114a50000b0030643e80d0200603a43d50540000740c01c0c92a4404040c2c8102640c2d0398802400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 430560683 1250 430559433 430559443
    0xd0f060218030106300b09010504151a0114040f0b03040606060c0b062b0c080f16090903020102040503060a051e040302031b070b040306060e0f04020603190b180405 72
    0x30188682c0c10301d40c0c100140c2c00305070205c41d00003241c0c1e400201d03818680440c0781c0083c007502c00e00820300055034081048000c810b600950256229150f4003004011100107081a40c0b548070300708080181d00b1624000d10b41c01030100190492106850a003040c0d5161450900362909500c030285180e4000104000c10a03584100c00150080b810480c10007802e03501c50840017070000300303c907001d20304140f2505580341b5180e81910000c1414858141c6503801403804152040b09840b0303901c1284980388185083c0440464a031103034842b520009583d140c507121100000c1c25021500b034065550030000401c40392002d10195208500000c0d004c602404c0c500c590740c3d0b10b604081440078003c0243e03010300c00002d901004035030000100340724540b0031f011000e240500308901c580c0b01c507294010000700002080f50a4228004541114108072840c0e038404168400a00040314002d51000e0104001024140a080030401411400300001000300800c1d0114551018001c03102a2400315141008108003003080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 430561933 1250 430560683 430560727
    0xd05100f050408030c0a03090b1f08011e020702060f03040b090d0c12050714060703060311120d0f030f06030b09010e0a021c290906011401050304060b0d0f0602 70
    0x820481ca01902d0f0840a400702070694400b480000420b4040248260411407000d5040f26a100c20750624200194035030200381000000d4000840c00016100c4042c480d0003030550300410307800620503203112008000c0d4030030b52080764490014800000f60300c0446002d503100328400c2060280909100c01000d00d002000c40c503010401000c0b4aa02c0700041050bc0448400b806500f81240c581d0a540781488800c3e00c000c01a0600c4c0c440d000410003440d07070581007070080303034080c401c03002004062205201149a007107502420681c0301e0741410025600c5100000701c9441140780026164a104181c242921240e030300c01d42c3e01d03204032028861009428030940941c90030305001090343d41b440ba400b0074141149007100d0402080407005410620401840c016683c202c414001039183c6207902140c11183c5081e1201c8000e03124060011030707020303454095001100c2e016150b040c1181d9031591840c0250100301441c40d044060b88c0280400200c18600c09038695100e4400581c4840300c01004a4507410941 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 430563183 1250 430561933 430561961
    0x207080d0b011b020102030901110a02030a08180d05030f0a050c01091203061d0109110403020409080a08070f080a0213030f05011a011805040b0d0506090a030f03060803160c050d0510 80
    0x43da1600603a00002191780d60002824400016064076a00f281000c0c95040302035054020600c0500400c07040500130905051585424001c00c0003207414405085420303a07008140d0b5008024182074103400d01c1c085e1840082a00d4424030b40450b40600d82c2c00e541c4001005c0714908240001b03100c210f5010300546000d082100450510340d41c010b5000b581d000810312805000036543c0d004003400020306000c8030051074002e0414440c2910038a4000c40550058444200043e0b1003030201d0f082901c10b403440803818007990755194083c0c9611201c04025440020300903030300170608030008005a520030982c80705c24003641c0000303004410880144070780390a013a200c0f030402c129404061544e640700308000c0709441c0d0944002541822440c00f040d80e498a07a400038090780f00f079070100040d41c40d0004000d4551442030b1344403601d03000c000700c06030300781c400d18028200550800d20000084080c19000030380024011b419020481e035560b0b010481c907040c01101a149034103d00c8000414244d540500704007050a4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 430564433 1250 430563183 430563227
    0x1050301050a0c0c06090204020d110d1103040b0a0b010915080f0f010503070614070b0c03150303090a06180e010f0519030203120a03021c02040e06090610050703030207080d0b01 78
    0x3010f00103040030000d1400074071096441c031608040d901c1d80e5040e19040900010100700c2a4030760369607032200c0c0d0480041c0c0d141190070806240c84031602c8806407402640d00c00c0b400302e15034444180000180c020904c1c002d0401041c044002103113203040100250001d07841d2206546800c10281035140310100030010360110070110010000750700d001481504996041ca080c0010602110009440348900040035107445490380520613810707107090007140900c18804070261000840c0381071603140e004022010f9403101004408200c450700a030340e07070a03030380549039013aa130480d45035410a4901c034000e030401c81001e4076029040c41603091001d20042024140020741c4c40035031840d400203aa80407502c0044400000100b41e40001501036016107600050b130b0f07982010020b180da18070070000e4000b4410707032201c1c042c80d03030100f1154117050301001c0c09110081c01c03402c820400a0016074003980021000c400b050b901300280380200b1009000350124906100d00410214011000100750740e150301200300c115505 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 430565683 1250 430564433 430564451
    0x3060c0d0b010e09061002010f0f020a02060f04081b1920010504150516050d0e130e0d030e033c0c0304090b040e01090309030c15080112050f0d0801050301050a 70
    0x550131583e40c0c4070408072020103c580310050101d000d00481c00e01012824100444003680034038640150106807c140d0843d6403e0b9502078411254200c141c4000d801c58100708401602d02d2071494000c0985041c1070116104200000300001041031009410354050305407050180300300c032401403c0c209a031001d180050406007031409007164450001d07016028800700040031402801151001c2000d50b0f0048180c0714030182151025040301d10000c1c20500c6a0300c0341c024042007813010310503140111aa2401000091111002030b0018007481d50b80c104184418406502d82011281d0f030f031000540c0b01d0040340141c02200d0220070146045221080c5d0201c4140824405000000309480c102c55100300c0c003040344003401e40810002e10000c1a000f4080d401c0c000028107064011007588100e9128203521012507a603520f030703c64440c0c400450440050709003030041004d0780049003007168460254060394295464054994540001c1c8100c441c0441c0c410001000146428440e842e0b0081940e40140a0317608 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 430566933 1250 430565683 430565689
    0x40b0103120323040204090f061b050f0702120712050a0b01050102010b011704170a021605040e0c01031a040c0c110a0e061201140a0f0f0219050705030903060c0d0b010e 74
    0x1e070b910b040d60f5041240070005000c0d50360355000510301a4004440008220550609002030000b00d2030403480c4001c00e003034400307105100760212410074030740304a85030510405508126045642c030038001c06034031509402166540b0448201d014640c4144001c02c101d40d51480c110800c0c000580c031650640e4903081d00301c03c0c141d81043c1081440300c25104000b14560b40c61501c410b41c0310760348060b400341c050b010451810b05900003600354030183c1c0915003140869540d004100a0301c90450f00001da9401ca400440e90650082d04a402070002050142e1504c204650104007152178103840c3e4000540d4105a2200313111402d00d40c0b5502d1305040d0355030b10905080c0004482a82000b5040c00d0294000c2c50311050503800a41c44809c1107110b418503100305042010540e0041e124501c054010503240ca502d01c440c010680c42110032070300304400c040040303022064040d00c0701d4104030b100742c480740020071000c408c6a40a2042d1449a40c4070200036480d0030300441c1c440c01320380d12007200d9410700c1500c228000c1c0c596 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 430568183 1250 430566933 430566971
    0x170a020f06070302101a01030506030601050109090b0f030a240905070e04110d030f1115070c050709020c0601180b091b0c0a1a0919060911030303040b01031203 70
    0x240d801e8502039690005890204e03c2d240b030040c030f16021070703140c000221958003070454507840851090384c2c1401503450350700030551078210a104003400310390011410000d41500c0c0c2c002c00d800c4100100300342e210741c1c1c5001c0420f040800500303040b24080503011082c3c0c42415605000c120002c5c0f440020011145942d9445646101c103000743c0091103144000982046104480c0c224110703405403611400c01c0c00d52138090401200c01080c1004504100e850100c0000c000400784042604d04454280e65103a1100076030702060403900565940c060510003180000079070009210700881c40c0b000740381030761501e0092030340a4691444444228207103010724a40f036850300b003519009050005060b039810030400600c078152081c20007a1540740942c068103420320074402041001015842081001940d80d6a0315540f0f84060340c100e8282d03071088449441c0400c0c415400303400c201d4420800d00d415145e81400280c41d50300102c030300320347e0442c0300d10052080010034090100180b0160406100482c0041c03000b00b01c81c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 430569433 1250 430568183 430568209
    0x6120c2105121602061309050108011107021903020603040506060108100e0403031508191a0112030503041b090c14160b101215050114152a07170a02 65
    0xd0310100f0340c01030011202c1c0d000c0500ba5070040209942e0020400500e160100601c140a000e501c0d050001805071010b0041c800b00d03800c0e045070075143c032006600b0042004071400d540f10304d080c0079000c04001038a071803004600690041d00180340c82d00c1c08000040040c080288002c410100c00301c030410a4807401a13030307582c015070b240c100800c0c400c0c0030303402084042c0700541c003c5c41103100b80c07130358104e20004010500898a00880f50508048901040b40150ba0804c2c49540c40f444242291400800d20880c050358121307110310742d150500c40d420401c603c0701200c59000751003941e035074031070441c0e0f03076130b0001422300d4580b95609180b410903001c84802e155806c58014054283d141c020005600700659000d000c02a10a61552800100e81418204486034a007291409010700c1c1200100c0e41c9074105144440e603050003018050a02c02060b07800740c0580004004a80403031442c100c07051030003030300061030301c9007180d60005100440c034003466103410750750b003619502503500941906009600c80d4400f010b02 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 430570683 1250 430569433 430569463
    0x7110606032b022a030709020f04030b0a090503031006080a0c05031918050102090a0e0108061909050604080d0f02121f031e0c050907021c0306120c2105 67
    0x310614000d0b403c1c40700c0d02e503001d0321380302189124044007982d40400726070050042d01150710240d00da429a0040348252110484103540c14081000054001c050f259446190f03440d000c03c0f09541c9956083c80c0d500f00380c070800701d0302d140701d0001c1c00065403012900340d200c02000e40500c8616086600600140320160040700010000f100070510440640c01c805684545141c081440031b4060511500035004501e1080c0b0902d8031000010700c038400711a85506a44a00713000e8401a02e80e80700d61103405082000303e924050b2131318090390100d281481420700c0385010707100050b907801000100504803541c074000403080610502440100210000005a00c000240d152a09280294910170f00e03528055000910351807400803078540404e408601da41a851040d40000c0449881d07600f0003514210480d003401c0141c1c00210401c3d1420551003440400304194100000c0c034540f41e401c0c86403280b00103801a650908455000c2103030960014070390300048104c0c0d048086020140e91140c1c1c6582da2141f50b02c0ca = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 430571933 1250 430570683 430570753
    0x3040c09050612100506030c0a0602150615340b06060a0212040801020403020f010c0807020114160f15050702030406080a1103090c0405090c0a0b030a140711060603 72
    0x601d856010030344108824007800c803000800502c00400191904950785400b23401050710703001941c1003082610061f01c841e40c000d010001a500d003007400500005154035406002100000842083c500061880703c0004e42032541003542c160b940d8810490b01403c0d4064084031000450105404011040d001141101d4290b81c500f44000308a24051002550308110100020005200a015802041100c2c42550002488220340005481802c2c0c10304000c0c0c40050204116001076202c1c1a10401c4906c0ca40c43d02814007151903641b10155a00c2d03070040340c4060126a01070b0a12681145540b405012100140f15a1500c000007d4583c019071091034180041e6002144101503103800590980768034520541e143d2900100117941da2500e08880e5008a1030301c404200509008118420342240140c011030040b03103865420761141d807004094030f00c0c80343e80c0c0c1c040620540d2134808003405045117540307038500e0743d1442c0400c0c1e0802902602c898841c0d17101074517800300c1c80000544e0600504580c55020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 430573183 1250 430571933 430571941
    0xc09052b0203010e0714221d03041206050c040821040302040507202a01020106030b070908060f060913290115020a0c0e091002040f170303040c0905 65
    0x54603044880d402907055003010480c4901e80700c00102001151040901c50b0050f005200600000c00304502c481641e0343d0103009101e15801c00c0740c0090703061030380c2a02c04040060004655a055070003a81041c60030b1003098a90000388160360240d1a040701d022400145818984034103565502e0702e84554000900f2150101200200000306460003140c010303000340011f1920318401001e40100000000c0d0071898001071141c0201c0005209243e64034040c0d0442100400c11481c015040001e540d42d41159228240400044c12004109000341d9030b03034030384032102c41c1001b030a1401c0c80d60003007084c81ca41815100f0092180d5a01c00301e1600300c0040c2540c03050305880e138180889022101010600031705030001c0080d004d40584601141220400c0500b000d40c040d0303180003280c0300c0e0341c0d002010303180d40a03140c3c09100203050300164682200988040380c103403007040c1e40424144e0701305510002c40d80b010708038104038070b01c920250352810945002c055455843d007640c509402c070f50b4034054080101e03507590000b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 430574433 1250 430573183 430573249
    0xf080a060b1c0f0201120911010e04110d2c03090105030a021902060a060602070b03010308031f0801140709030308151309060f0606110d120209040c0e03010c0905 71
    0x96502000301d00340c8082d400c040742400e5480064100d4205d00040200700301d440040840c1c45034454445d0320a08100a480f806001100c16204210b2180c0d401641c40c2c40070b041c2090748100601c0707084140c1c000801c140c9004002c061070040d000d00c5119500c09590401c0c0e203420303000300c04c0300c0100700e090074800d4882c4c48842250000b40200d1540120740103030004258107464000403403a200d18000102800131544464040361100414031984114080a000510003d00120040d41e400341d120b103605c00c1d00100b01030960a40401690001840d84d44d07450000740046480c001e1240d0100d8503007080030310146160390003032907070307600402080d01d0303545003418180c040d624140420141540c081c0148410340403820079400504004c0c1440304124900840040c1550040d045811110700540c00707441c030303615031040640d03c4203686044a40150341c01c001c0d20b1510b90329440390341513802c15075882d0901a140a002d050864903507c1503181480825403007003001e99180c0d0744100202114030841c1302e40d03501101c18 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 430575539 1106 430574433 430574449
    0xb0f1005031f0b0423060f1b0f07061106070503060d150908030106120e0d0c0b040507050d060504050118050705040b191508071b060e1518070f080a060b 67
    0x1819202303582c94055000c000760400988101194420382030741840e0742a000480400c2180c07100b4100380c6401c2190340d40c0802103040140c50b6050010003e18007155210000b03000a050002d60b85d62040542c021024203540300111b503449584507107000c0c100182e0f58405a28a1b0b1a169682d01704010004208890320f1203500c4070480b41540d61116405800020f006807101c1c880c15a00260383d841d01c106960b2028050304002595041c00d01e00340c4e0944070381a000314000050001888045034002c00c201d0225a0212800606040008045006640c030b0001170798502c0310081d00080e6100c415125554208415528181203a480610a485091017858aa41c00340d00910284000884580c400250a0003880403102815a50102c1c01507400702141e900b0f403032041110300a006141c3c100000c00240001c6050700c0c1c00d690800745141c4c0e1b070b02c103810401b070801d07625030003180b13040d46800d01 = true := by decide +kernel

theorem cover : BRFrame.Cov 430395683 430575539 := by
  have h0 := BRFrame.cov_init 430395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 430395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 430395683 ≤ n) (h2 : n < 430575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
