-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2503
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:54:07.48766+00:00
-- url     : https://prove2.me/submissions/1bd22c08-8439-4363-a691-1d0f74bc02f9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 450000000 ≤ n < 450179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 450001250 1250 450000000 450000007
    0x10906080c071a0708060d0f0609061413202b1a1509070e010c021c03080906090a020a060315050a06030e120313170415020d0206130b0103080d150605 66
    0x4517a020001c2078100780120384c0d00030051010346402886056103d40140881e40d9a5107481c10480c103900074600500b9807200414440c030700003086d602401c4040c84202c4141c0d282d010b50810301c000c1100c1c003160b03552026200d21043d03a0380b06003140e010304d00c110141c01c100303242040b5000000c00b0002c03042d408404007480030855040c0031251010f0202c030422001e11901c142002c0214050707001040d440003e109117414501151540003044010725005203440b074a03cbc1501d0950280361300710107414042d24525040310b002c0c1d624010b906440301441040250301400680e010000284260011020396446d10280300703100c2d948000040d01c0840c50b500410110703480301c01d1040c05c0c100511050752079141c861901451071405000d01c80d22005201402071859200e180c18114400134681030303a014010310380f004441c12028842c007a55031458115200010700c1494000341d5103800705414a10080d074403c400006507401e540d01c03851160400351016145030303038a0000c03080c902250420140200321a4885c3e41e50f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 450002500 1250 450001250 450001261
    0x3091c06020c0703031206060518010c0b010803120a0e0c01081807121203060e070f02030d020403030302091c0308060603061c140c03070b070f08070c0f06110606010906080c071a 78
    0x20a4120310036140541fa040040084035008000c90341082d62010301d41c030004040c400141ca0310300400c2005013038400e00380c0021814940000050028400754803030701ca6075585510070b4100340c0d01c0482004909030451074400c003a650040c19a150441d20b054a480301003d0340d081d0751440c4c1181e55016141c440f44110f561014080680c0e50142860717842c0c40d050040a091920442040c200640758100300042506802d00046c42402601c1c451120341704190f41e030302c5c0d682c200100030b0f4002d1a0128410b1034810050108107440e00758410840b5815141d01e82a0b03901c1001300320854100410b620f4214503c0c6603442140b52480041d00c826522031154907107a10600700c640741c500004e02c8420f90003607003c1c040a00522042c18141c0f00c29031307032000101c40410600d00e4800318600511400900410361050041041c507040102c03081030303c405075201003540103005150790343e0b90b1040d141d0b54041207410005000c031070b21031040c141d40300b0706035402c0900d880003c1ea202400161b180c82940c1e60180e00701c00340b02 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 450003750 1250 450002500 450002507
    0x10c0b090a021804050a150908040f03050705120709050a0f09060e1915091103060c040303120c08180304051c050f0d050417100f020d1d03091c06020c070303 69
    0x84080301c120f030107425249416681c15940300f000140280c05814039840c92821080302d42c010100080e84145015101c541e034a01f02076150800b80400c8509000741c20000c510707410110401000d00c2c003001d004000d85890700052100070000a00100c1200d51201c0c0c1303841d50030381e490096004141c0320f00310001d4614031080943e0b040800507541c0c903076110710990707082011038200401d03030980f524400c20000d620111340c90144403c5080c240380ea90107006074410007008001400291040328001d84503107503440d00903040701d021107840e01100c801064202011840880c10416800031032281389040700d140c01e8480c80050203200406007072605c2c1442e102c0d40b01003040b10a20003c40211001c01c0105000d00030604094100d0190b4081ca016071038001c480d000079100300704803038100e03504880801c00101003800c0043d030183d4020384803100c0080c04c204800c032034000700c1d66100d00220345100c051420070041e038040201c4000f49100311000f00542c0d50303ca02c04224a4402860001840300c010052103140d1316024 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 450005000 1250 450003750 450003769
    0xa150c0e100815030f03091e12060403030501240c020a08121e0f07080a0201110310031406010b0d09080d0212160c0507031218090209040f150605030402010c0b090a02 73
    0x40c002d4005c2c82c007210301c0308000010340b82c02e103404652056400645060103500c0c249070103043c030780c088420840c2c88140c82001c14103070b015034003e5900b80410385c0c9424802c4075014449114100c0030500650403a41a4410b840721843c0c0ca10051800c11040d5481035818602280ca20005c0321410000800c83c1c01e41650703900171260100c3c1d141005042002001c1400124028408041c141110019000c0ca1701e9200394004481f0914050b081074407410031968805112500e4001100c2c03401c0140f801e010080c200084c0c884c1250709030038400380317020854004500030300321080c800c80303d0031018001c1001e00c0115002070801b1100645258080d40742144185003800030076500d4400b404602c214500200380302040e8107041d01d8204420345030290584200b110406802e0525406140103d400410000c1c440c0d0010701c600482102d0900030341403c40f4048040340c1c06640d8054481d44c00c54005c210075400341015560190050400820000c441d8071448108141100d01d10419044401748d42d08503d80001403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 450006250 1250 450005000 450005041
    0x5010f03110a0516060c050d0522061d0a050c0307061b020d150c0e1504080a06050601030b030f06070f0e061c0e030c0a02120a150c0e1008 61
    0x1481070340481c408240c501e210b518580c108000b0f0000e10700002980100c2d00c1d07290640d100c1400c00c600007110000402030342002a03500c03409414040807a42c1c03e141480070815007510641c48c180710807560b80d070b824014140c142c01040400c40e02c100c42420820b0520241080354000d801500083c1820b100701402d103e401d0b0050024040641400c405006614400e180481c0c0c0c10384080c0c40190a40c10719600480540010f00c541034100021030184551103901c400d80000c003600c103103000344440242138245000700d00980c4650343c0118004004103001e44c008a8115106050006c3c940c810807000c281000c030011034483c82c40e44400c1c04c6c4440c040e4002c01d403040c002080d1400f20f800c24041030000740c1900c900b01c2c4802d00b41d2034410544841d8040c1d540924030140102c800c1b40c1e90f681406007980d40700c0302c010005034450b860130b0040044080c3c01003489540c595204e080b24804450013020400101540c2d0302c0901000358031001d130001c0c2e8a40b59015095107070b19482d888800e24000d03000400364643e8010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 450007500 1250 450006250 450006257
    0x2a081006061407050a120e0307141003090c05030604030c0308010603110d020c0c041514030a052a03010f06080c0f0603190e1b030d08040308070521090705010f 70
    0x1020081030340e1000b4000b04485070ba010060b07407100282003207454200d0042024000511150300b07001b0690f0481c0700c0901d4108141c06441d4050341d03440c03840d420b0440894980390880c0031000b545403418800d41c4070403000e44c132403030102d650700b43c99001080c6452400c907812404110f0f0312400c0003d1507044801030b4018071040c0307010300035243d000e8051b41d03081c01807013079001e84a500031583d142504e000303101070740340c080014108211560056000d501c00001610503002ca880010091411314100030450b10285a003000051103212010815803610b49152400902e00002c4005c000380d4a0342c080c0101d0640064410021464034200a040381c2041c5242e090207208070441c2c0c40d003030480e450701001c1e66844500d417610300340c6a18803c1c0510000c0c28a0300d110074400c1c05800380018224200e0750003c4a415401d13000c172009440d401030195010303841520050007045071440010162071142000748100148110b160a003100c01c00d05541c1000c5090310640c07240d8000e48028452960703c482840900c00a034030707 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 450008750 1250 450007500 450007511
    0x11030f0f1b0f031e151009030804170a050109051b06090306160201060306060b0a1416080703050d022a011401050906120a0501060e010b0414010c2a0810 67
    0x20742100c42d2007000c29220b108180400012680c41d80c2e14088040241d020030403860502d0041c981c2007400c41e090038010310980c24481e402c440d4511a4003040103480d44800030700d24244c100201c0713161004603152090000d01c50b481c2c01c803000a0007806000c0f00301d4810030083c010300d0708429043c2000044000030750302482003489100503541c2c1c00102035412005400202c402910400c004a0240c40d040d040500501d0078882c0004504240c0b500a10f80b18280369100518503c1c0542000c41621464075910500914800b608020804040007400280c0c883c3c18414908403000d200c43c01640c100c0c0d0784c080d0b00382105140c02c00704108460352000c2000c00c0c44000700401c00c0680481000300406000d51401b4100001c001901500c0b01e40140c84501c0990341118111015881d01e07602900080c05400076070514080000740e0101d07000203544c240e49410260f0140080d540c001150300560440f01651b481485541075450815a00d1a0424521420074610041403c00c6005482c00b545002c0da004518a400b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 450010000 1250 450008750 450008791
    0x702030c0a09020904180822171b090c04030305090a050405130507050301021908061c08031501140d2018040b09040c06050c01091226062211030f0f 65
    0x10b00c101c500400115403c2d0b10a002e840c448c1811001c11a04072031243e151449081d04040f00014100d144520742c004051303d1010b03030405000c2211001e0300d20400000e01030005100203400340020741171411020b008103540540d00d0000800750b030070541c0c0c4404080e034081192810302c44207002c12005004160000d510300b02c58500c40d00700d4134200403107036403c21134a6008100790742c1e00c01a0b0401c0011603501240e00c0752155041040b4258402d032000e075144040346140041e40d501602000441d6440c2002442c00c1c10301405400001d4804030251350080c40e01e400c1707508081c20074070001d0700f0510b061440740d440b00306408041c0001ca072045034180b440f81a03c0c8040100080d02e0003100c100b51002c0385806c0703440703248040000d07025080303410004240c8144c088424464a5011081008012804103c3c074084c40d40024804c455803019519a80c000c40c103c3c04400c3c0d00c000d0070781c882e850b032402c03030f0800190100304549813002c1e03030008c0c0c0b1142a064403143c184012050500365680d0440e628a15841941140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 450011250 1250 450010000 450010013
    0x60919330c08090a20010e0301110a11120a030c050c0f0106080c0411030403200604030f0e01180b18030304090b2e0c1a1503100c050904020702030c0a0902090418 71
    0x4105e04030050b4210080301059204088070400c2c0301c4003070000d20402080096161040c2c0201e80c0d03110008401c404101c51411000174000100d12701003070564a400b40060084018255424492043c004100b1030480c24180421a40e100307080790200000d0603500700140306003060b00814815204600380f40c2c2148403496401c1c1200e4126a15043c90034904114050000500020711442d0540e130240c02c0421082c1038014448401070401130b540d08032860980801506e041c0402415040710203c4403e05122544940300100b600c0e05080c1d4044250310301a00029255a110390400c041c06602c03005d51084a0030020305141c115202d03621b041d0212800c4281e10302c6043c0e50303a03e90004014940c10280c0900621280d101c03038541400002940300d01d07200c8501b00b42490580c1020307002e071240a00c0003000c0000d0b40f144003180100765595a141560180820020350001041640d00d0b015584018000d603592150480050144c18030158581c0c80316010031040f14070900301091800d010b5a004400a450b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 450012500 1250 450011250 450011273
    0x31f0e0106030c1e0e090d030b180a0b190f2c19020d050f19020a02150402040e01051303031b080112060603060203070c05060919330c08090a 62
    0x2d5100708004820607541100030b504c0304691020121884950034019a0b41000c20b50300884006a1001c0c40a8a0a1000e1118001042c80e02d8640089480007080704649250007903030000000803c02000600d002801c000e6180440d0b00c00d0402241e40d1301c0802050210500d20070a80f89a030081d030410400b5100e403d810701100500301400c003c0410940000070780c0980c15100f080704244020003ca00d40381c070482e040c000d81944d250b00c0c0109030f03020001e0702a4140c001c5440403151540900700c28040b081650848410280c8101d912640703171100035410590921610f07100d0203c1062000c1000c40382e0501034111956050381c00c40c035090804104c40e0842e0410f40090466a0010458440f40d0290920300300821240d0070052500b4000000d0040d12a8810501c1741081e000390150b90941c0c513144145a61515181803021100c64200e03924008604090711000c180101d102c1003204036070f81c4680b001c52250f00580e0048056a4032007146402951044c0307403580c8440d40340000c041245807902d0303181c0c0429 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 450013750 1250 450012500 450012509
    0x3020f161a0c0304060c060510031214070b2e0305070b0c0c0907021011040e1b0706050106210506010e100e06030a020d0506060703050a1d031f0e0106030c 68
    0x400c9424035408568039002c0b00d800c10700c220240d81d00c59072034400061101200c241b082e1420341c03d100114a0001818420004076544091030701509000700b801955103886542040c11070742001d11501300420000602c41d41314000414024060b254940007200401c1020070808a4031400c40ca0244001040052840c056030910f00015480340d1160080d00c0c0780600c000f25581e000301499060011003038001400d00e403107a64403501444513100203c40303128140942d11411344000c6118020401d140309100200d50381044801303180b858032005840b8081a10800c2c1d00c000b0018074003290000100d0b03060b00d2012100010301505100d98181880000c1500300301e4801c1d94401c00041e0040c40c1c4030390080156400700e01c070142c0525103c1c900800f40e00000d4012240041116041c40300107521407911004840c052581130b00c1e69820608018400c640c0d46054031580128090300211060140d6000c1124142410034028045491104240c002059031014519940241c0c1000014800201440c8512040c1c8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 450015000 1250 450013750 450013769
    0xa05040c080f0a031b020414071209020f1009170724020a170c150a060602031c0213030206030114190501020c0603150d03050c190b06060c0f06090a03020f16 69
    0x4845202c80c5c2e005021a100d0025405498019041e00f5a407580100910403400c1da1542103518000b00c8201d4161000440020f60141d01180c00c0400c9245c00b40364140710002034038008545503203402d400c60080c046440405504e9021030002c01c0918000c9400e60445c10510080d590b010a9956002c0d59541c010b0400a0281601c20300d83d4402d8626a820b840d00a400c1d201152541c43c0a0780d025043c0c070800ba10200e614a0401c1000f180d550b00001c22600c16040110400850a0145521000075008006a00c1002000f49000000360361444003850180c240707000254401d02914007040744100c001448201091510f1100b0041a038000c41d03042c0000340e0641d0025600da444045107170079811b025010b682d21502030140c4a00380f50b0b000d40a001d0313000a040840390707200c0c1414076500003440050700050003050308100040c080d040120107800304101d80c1d81110043ca40c90031119003060000c039a507070603640c0400c15540c20301d54100400c00b20001484040d207400c000c1d241ca01e0300800014000c00110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 450016250 1250 450015000 450015017
    0x905060402072004091b06080f01031a0703152607050a2c0c070521032e060e0a090e0604060c0c080d050709060318030f0201020906030a05040c080f0a03 67
    0x103030b103a45e0000121036034000c001a0b00c030350385800e052040300750034040d00c00040c280b1000a079501094080080c16030f42c01281140d0001e10603040703603c030301000803d2a4109510f803d080303040701344552019805441c428000504401031603125031901e15051848024a82c49410100010f49500030300e001a136071041241100c007140000c0703028628441c4103407150245c004500b000124903100c005061000c1c8100152480e41c1c401c100145608901c801c80580134a2040001c9544803003681104a0b20340c115441c4610780d121003c801c40c0390001107a0064006c910350050641080c50104807600c01341800e00010050701490204003070351a000200700404031580c0b00107600c040f60042104011041d8403212a5a64004004001d000b4000c1035505074003107081d9110108506020303000f201d6006010802c02c0d00b1b0984130340c80132034031461510100b0080d95420454100c094650a0055100300c2e044c0d580498a410b1914001031070403403640c0004980c0d0042c002826100c07070b001c140e58102c203030940342a544 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 450017500 1250 450016250 450016313
    0xb0402040c11030d0506041103010e13140d0806030c0103060807032a09230c12100b0a0234440705010f0f050f041509090506040207 58
    0x80c144140302c1c41c201284000314140c00d1485030b03904480d02c1075009540c00d00c2201c40703030480c81c80c0a000070301911080c811204000344a0060003408c0b040030602030344602048114201000f410f00c021440c00000103090402000414202000300b072800c00c00c20711381004024907240d6141d44640090200074101c2085030900d1903882c40001c0368102e1807030340352400c401645c2c3d0761407101300608010081040131510103041544c0300c006030610502c915202800707185056010003410401030310080045c42e04100f10000841c0750440f00d4040c11984c0b0310340e0001c0103154648000c034419001410320b03034003401c00682c403902001c4010590340d03811030346800b00500100d1403490030004005040b44070403143d01c001008400b6506c5810842049240f04102a100e043e501c440044807110304505000303000c180e41190a80b0418400c10040c00c11241841846042544800c180c03031b07080c0b030320102c10400242001c1c001c3c004501c40e480703201d80001045404502d05441e95a90800c5254480c0c8485101c4604948001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 450018750 1250 450017500 450017507
    0x3020702040209090f180a020d12091703120c03090309060c0a050313090f0c0816020109020d141c2c1503011703090307050f030f0d091703070b0402040c 67
    0x20f5004070002c000d41030b40d182c0b003142d000c8440000c0702d50540540030200e955110b6203001c1403031031134580c010781014415511602d92110410b21064054100641080c001520300002e0b000380c03060070358242c055030391080a42401d9006103405801d480c8801820018044d07115400811581042400c1c0c1c2e90f1034668100d826210300b01791410b003000d010707070100140e0103034004018800d96003905d0710210200000c1c07040000d02d404a603080181980070502c200081071107100c01f0b51594145c0c840074030000c5400c46c403d6000c038500d14007542c0c0440382c40d2400130754003002c880207105035202242003524a40315089084401080001c83c0342852030b001c140c040e248107541c414248a403c40c0400a001a070000355118107d00860f4424490301d48140c4c2c0030117840320040750200841d42861310060051200074145010042e8100e81c1240301030381481075000307041c0d0000d41805002d5403031409407203050780c461510310031804c51800752040c3c030b22540042140301c0008200642054000f601901d0004070724405800c240c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 450020000 1250 450018750 450018757
    0x110d02060108190228230906010813060f1b0813080703121a01090f0b07020402090a180c03060509061305090705030304030f060b0d20030c041b08090f0706030207020402 74
    0x1c00010400110200c0f10510100180c0210340705950010148100d94046c0c1414114000781d1039441017884002c030b5042e620071031109811070b85070a0004102e00032556803800301c80340c1211915802d600d8010062010f811590600008101750801d1100d1786469001c60303880f242e0000b0020510500460300c4001d06105000075200711500f07910401c45d10000900100480360f200042a000811034200071403601c1c1c5e114070b043c0441c1c4c2e0224800d0b040415035802c01029421042c0f0054004851f001d00003440c820054000801c00c890303030720005904030f203500c0050070b1710f183e608030301c1c09072548906102c03664594400e0030745801000c0e040061076031a00600507090010355032040e03a00d803001290100500c005c0d65840045144240300401240c403000082c0205a07403d528040c02001d80050300c010904065817560003800d6005064070400440c850010b0b0488200d4500c10640703ca401d510540000e0f0841031060300222040c004080c018204119680c1e210424024901090340100b81c00d802c6440342d8058 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 450021250 1250 450020000 450020029
    0x90b0304051603030816050c0717030d021201030b0604050112030305040c050a080d020c03010c02191a130210030e071403030f120601120e060708190c110d020601081902 74
    0x50303035085030f407414004e04402e41500c0c9000c00400c3e000f01c01080c540100100e50000340007001910040386040090080085d26541d0911140002c00c0184082c156a20003080c0004250690a02d95415806c03c0c00c00c1d800010001c501503417070640180201358085551480f116031500e8045155615450400301841070b81c3e11094011409500200d928400810b907807607642000c1e0b08440d1150a50000c142c03e8409443c005005078101a607191110060668070410f60390280705941d8050505144001200004480c1d41030b00b11401c0000104510b020f44869101c0542407034240107942c0c1c2c00c0c400c103841e08600e2140d00d6018005c1041030340181c501b4419a20b000721709103503040d02c6d1800103030280c0c0740b007000b126154005541d07074100c141d1031070391803180750b8a0850820081400c0d641d841c0050366941c10141c01c1c1003080302c00f4010702c14002e0b075074010704103204a02c0d524040320300c643c0a941882c0c1440720034041e0075504000700500112800264070013900d40310900c20508400c20380003007144445900b04 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 450022500 1250 450021250 450021283
    0x204050a0f14061905150a2109030306060f0e10020a050f0105040308280c1101020a090f14030604081b1006050a050103020a050a03052e090e0607090b030405 69
    0x208031194080d04000c1500c652001da80c61307008680b402695050119071030282d65072040300c02d8800c082d0901e50001400750f04031242031511641c401c1d0501d81a426260aa455411755150640d4104145d45402850000c10b820704003804c40020040340642001c0803001c4641c000d84402480c004103a10030004164a1904001503445540d09645500e018090483d0300341c4c0450080c40c00320304c00000381c036400050800c405020301d0340e40100e65548405841412000030820074140490240500203100400150303000da1900c10301c0c3c519154102608448a610143d0074020180c0c507001d10743c4011640c1540150320500e06592200000150202c41e600d848500b104c038480c52010040d411100d500c0782095078400c9801c42d04044d5640300450030381c8258001070001a03024440401424000d421603500080314400d02031040c2c038043e24402e101c003240081048404080c98003040388101511490880e03000710380190400345010280039021200314400c00d481a8400000201070283c203000341800f43d10600c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 450023750 1250 450022500 450022511
    0xa111f030e0d0912031b080f1c05010b040504151214071e050d0f150c091e0312180906031406010602120d020d020408031e160204050a0f 60
    0x6800a00511040940c10a00c1c4150150702c44401e0240b4030b44030480f011050628064611540d040303d00c0c01c0207035481c1240d091085036801c001600c110151800c0e820b02681c140d103070020064607107024411200c06c1c011143c0740038010301a50449030111001c1e580240c034041040c040d0081c4103195410260300100003900e080707000b1010004c081c6100141c0c8d0440400b25841c00d51694111035104c000207846850310b1030540c0040109040c982c00c5550100e0103101d02c99007500f003588440300095509001d108c209603a03100004526a00862318101034040d103402c0081007203040001280410290002070400600d600f00d01c0805445007235040100ca51b008100c0300030b655129040d101804640c08202c1d88400c02c0300d09070100d16800030f20107040350b4890b4001d00c0414019200c024413948a00c0c100204540c08000f0726854000c80c2c0001c20080c020a00196561100b803072400852009141d200342540742c040200c607910611f0071000e441910b40494001070591501c0140348003d001c00444000040d00b0007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 450025000 1250 450023750 450023809
    0xe0d110709061e0819023003310b090607140604110607020d03050903121306021603030905060a05040e090601030b06030f030d0b0a05210d030c020a11 66
    0x301008034048400d002000412500c812030962520384103110502100b0b00501113001618099484100406070f2403508541f482208a42c4030440c0303000c03a84200c496100091a840711701c0b525003000303464804068203281c0b1540c0307e407802d841c011140c0700c2c841d04420041800e034102d6a4034411078001c0c0e9840320f2140017103181810095203036981103400f40c41d8002c404024210300e0400a08441440c2e81c010450310183c20155000e43e4240c004901140d01845200920310f40300c1030220040400040e155411143c540c60b01d94000c0ca014540905c9014103200c00e00e040000070b41020184040d588111a46074441c4ea00745401c4990f03006e01e43c041c41e0070001c00360912241c00c202242260589025078003400d800e40d41e00d8181660b0f8210120f04840c0d90b401086103000203185a406010851300040010882036034607000a100110a48101010300308003405160030317043c08014030b0062101a09081c8440303c00d204019456400e00c10f07001e400d1101940403000b161f501d50224241100c9041603c44450f00f21 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 450026250 1250 450025000 450025019
    0xe010e040b10050310052208190f2a02040507030e0c01030b0109060806040204030204020a170601170105090402030a08271903080f0405060d0b10030e0d11070906 71
    0x680e019956801d030390002c90142c0940500d4401a2000900140f466050a80c440001028001e01c00c0c52070011441c56000740c0c6000481c022450350050711025225200801c11400444c0415100c0090201e42880215260740021955102841c0e855000b450083c8080c540c070043c92215070f0017580309260004104000340c05034001c0341c0c3d604041c4111111b20086200540071220400700c8140420a185000c104803481340d15080d5000502400260030907603a60701050036a000a007480c000302d0b20003803204c40d281c1001e03000d03580d220109203403441f0b03842d214514848442206004840c001d240700c400240030f544003085504581980030f11415601c04c40100256040c03001700c1890002c1c0650040011031074500701550a400342c4a04500c10310791891655001c8041c1d0000f02e00030394910041c040003c480d0341c0d003006051143c0c50241c0c00f1647d032020104012400000d905c0342c200b818038100c15041910301c00a100e651540e51303420040c01101c21400002c0c544252a1300680d9128144007012030030114 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 450027500 1250 450026250 450026279
    0x30b0c0403120f050415051c06050102060a0b09150f2d0d17030907080102040b030703060b121503010b030a21021b0402070f05010504030801080706020a0201020319090e01 75
    0x1910094012203424542103581040c600c1c3c0b40e4001900500c010704c8040d01a800201c2d50b40380a08240e454909640319220352900003034490520301d695680c040145580600c1400e40c88000d50300200030701d88040002664030369018110419080520107210281c5c2c69401008140c0103008081d98509000003821400c01034090342c08000660130740030045958100b081041d01c40d50b86c4001d4000600025090f07114142e00300602001e0309126001000600090071710050020300a003241d00d59980c03800e544064140d60080d440380b1000c02c3c0404c10040d4850226002d507800084182d0941d60b00b0710110002030142041d41d04a03641070241e14008820040d448840b44003491819a011081c1005403605036181c03160b500300041d20041550f40301c0460315281d4010301441d842044c0300c02c603004540d01d55a085036000c98088000c06d855800500001030200f0400005000500c020708039040c080d40002d440b4061810000900005100e44491180c011a699006080c02e02e12000045da95007007042007076203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 450028750 1250 450027500 450027503
    0xf0305060d0b0f1605130e07020c06130e0106110a06110c010c020714010f0215132414060d02060904020d0c0518031207030f091701060e0c070209011806030b0c0403 72
    0x4220342c080c0704c0401e01500541e0f0305c5640c4054806905450144410f040c0380c3d00802080841c02680010306284d43c9600c040c00c0c41701c04141455102074244589840700c60810780001052002c4400028016000064540c0000c2e90144001c9902803044141e032013540280300782c80070a5402e1030152520f00307074001420781c00c0b1410780e0361071402444507200650380300301c10b581d041006802c0410401c0b00880d0340340034117070001565566041c08000e2a03c0c2c0c0c123440c104500088580c10a0000c500700c040380580103c00362411414100c06003403c060380003410004036024001e0085074080391415460340c0303681c1501c90250b8a84400d2004081000004169512000c48002c0210440302a034426050001d046101407103020103851400c02191000c0d128080b9950034001008602480412403000c50400e50813061008000468a07e00301079000c0c03074102c0c008022203000d901c2030244501580c1c4450380c150441d0886180c100303001100004c458090711081c0c0010700581041414003440d0a001c7c170003041200d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 450030000 1250 450028750 450028771
    0xb030d030b0a12110919060f030b0f2403010f09050703020901170c041e1509060e090a0f08041e05040e010203061e01110609010e0106080d0f0305060d0b0f 68
    0xb19207032522a8410034902801503e18004041c4086113801c0005003a81c00c00350b403802081490070019482c0e01900c5498020390100d8500b89000c004103c0c80d40510354001030407a5032036100d4a003107150034042c50012541e20a000c03480008088a40d00c083d40b08030030a01c008402400300d481c0c01d0402c10342d900f856100803402940369000005040c2c0c4064a038001c4403004201405031002d410003008003501050726070b000c031840d4115000e05050a0391203140a05417810001c443c0445c41d1194a8040356410390100000d0076440c810003041c9e84d000706408404c00d070721178154019045c85023003107606070046401c805218010000d1021160007101103440c00c582080ba418001110b031f090580c1e00340d0005890f0542c02284101141d0034110166580c000741403010314000c10012500d801a500d4103c0642c2d181d41035954074201c00c1085002030180d07201a0810400400401980460007803c0315030b50740d5028200341d614000301c3c40542d1055071031416a07410080121150400ba40000308083c0182c8841b02c90 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 450031250 1250 450030000 450030019
    0x5030a08180d050d020f070c03020108090a0201140a1112042102010e0103200a0809060f100315060b0406020d0801080d09030209060a09140a0c0512190b030d030b 71
    0xc08168026140900948202074030180142c050140c955410101c601c0640d1074082c0003000040000b0307409000c4141c0540d0400c00302c2031440c000540511f9000d09260040e0300001014400f60340c200012103030002d15400c81d00e0b81c070b01010500f00c440f4001d20f0704d0140c140c01401c0300c007a05205004041c0040d00c4035440014031300d00300642d02000640042200a001c5440004400303190f41c080d6001e241801007001034145c1240711518820410f40c409514a030201701210180f260041c4100705159000650700c0109007681441c100c083c4040c56944802440c8a803041d1038150f2041540e0030050084c54000111500c640e00c0e064040d4560b07003412030072000207200c00d00014408800040c000075210860b00da016107541190280540400001e000b40c0d0020000d000000ba8003509100300300e912808c01c171940c14942803001180307041d100c0c42d59181003084000d0100100c0c1c00c4200b580703a03410840c180740c600e22820102c070302d007400380560340e1801d6130600804440803461601504441c202a508441d130f110b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 450032500 1250 450031250 450031261
    0x3162303031e0603070510030f0513080403080c010e01090f1202070605040603020a09050306040c151e05090414191512020f031204082d0c09150a0305030a08 69
    0x303403400101c9645220311004140145046200340c807030741d04000b0180680d040145c640010820005600c103207038000036514202c11503000094440c0640015428804841004058480b44894000e44c007000c0c110ba88000703060780c01083c0075880710500f01c94038002404500a641440e0440807002401507550346e90103100300070074603c081071180a075425921954241703820200101c0c02501b0000740c1e0418800e2800f404562079a0030015948200e114003004442103007042e48038541840d001d020340052200078800c41c4d1aa002e400c801001240841c50503a49a4000d4000107002c0d150b8071004030301001551007848100c80d505220301c0030021000c4010302024034200000c0100f2010351040340044204541020700500c2e000c0b00318420118014121034200340045a82c0c011f82c1e000b54050f280c00c0d44000800079140311840440d40301c0380080c15804003030006e001c142a403114602d1075070034451070007040054824122088803168252026003951049510b9203080c583d00c0d403105d00307844081040c0100060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 450033750 1250 450032500 450032503
    0x9120c01140f040e0a06090c11071208070605090c0406050a0308091201200d0b010c1509240203040516060c030f120e0109032c0d05031623 61
    0x81564180d40e01e001d20350740c0c59a51545030300000e16089580d80d0400c0000b82c0302c02501e1020b030050108900000781309251072041001c039201032000505020116090200c01d041c0030a61070200d84200700050b0750b10140e850911071328480d1030300050100e45041c0c207000c000f4000180100c0e030104165810080c3c9a00d0f03034100f20b02c0116500c03004064160403c00b40d0b070241000304101402220440000c10800800b81540682c0c0740054403031400c640c004583c41040c215107004070740e011716003800c06503001d040700e45038070300c02284c00c00c5a42d510f59101c08450301000344056080070070001017101c031a840c1b100a000f140284d40b0607501036403244941d1400c40b80e100008507070381d021980582c89400405046940c15140e00c440c24a405042c40407401070152844554010a4544030281c000000d0600ca80c0c50045c0c8007814008802040e02d214440e04c82c90711488000391001007104680c50806682c662900030b20303501c140c12641c407042080440380e6007045030000001d044010140c2e9003101e180000003150f03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 450035000 1250 450033750 450033763
    0xd060803040b070f02030304050a0315140c0403060e07050a09090501110a0c03081f120b13020a090e010221090618030901030c1b05061008030708030f220501020912 72
    0x30011800104003d00004030300c907141d0740c1e00900c0503085d00c4c1070503a2200007520200280e80701799000d1800302e0114000c04000e00c5210401d0022001c40140c42c1040304403a24035000b280002040039603121442d94005104106a900411005141101c0b0a403038113120000740c22a060100d07641d40c242189400702240d000182c9083c4036140d99803001203121903d04548a00010f02100f01140a404c01950703c510700c90350450281200e04048002080e152a1240360368000511000c11090a0f07202d8800503600c0914903411600904800709688016410980c0203116104a038080381040d00c24900343d02603400032640c030466135103040c0c0700030344c0c0c490000c44030303205001141a40075001042060351030342c000d600c10305c9962400e2030702d46a2046142d115061068003800f0540b00f6a110504002000c00310b4844a4003400e42403001d0f43c03d02605aa5401b00350002134005180e07088041d0009030045125403041d03800f0781024061102d20042e5042c0306000f9440790124900032402c0150811b10f038080005c40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 450036250 1250 450035000 450035009
    0x3040210080606040801022718010303080a0608060907171902040203040606091a03330601110a030e04060e04051507030f0c170109051e0604061503020d06080304 71
    0x2046006103203030044400c05801014268483c0060101040011003440035004200702800b1b5003460b01d03610701521007900240010544580000c014100311074220008181c112503040c1020540e03619070071840c01c0034014903007004901c0e02c2004204520108009000411900340d00c1c0c184003a2400041081c0d2111442101e216000349001d4290005081c95401142c0c0180110ba0004055171a840100300f03441005004510000c22000346400c03c0c03809004d00e200e851111050301c450301869200d080018110351909801d031000000004061380d0160101c0044500c90805807401145107181c0070f070400c56041c140e140214944100490520100c1200ea802960048010324120341112400c0c9403c000003070500c41010348441030803040030750a02980e42514050340740c0c0342c0300c003071072500c070720000c44050b400801e9070303400c20040c02100100d11420184c20300140659003040d50702c450110b0040c05581e8402d11191006000041200364558090195280408002e0103000c0d40d40030500da0b80d0107640078 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 450037500 1250 450036250 450036259
    0x19020402042c09121c09060c0507020a0807062c09040b010312020c1315090204120201030b03060708040201080c090a030c050118060207050f010311040f0312020a1211010207121d0402030402 83
    0x51701000403400c217101180c0000a1800304244056a44610a98001590f040c7c00f1031004102c002c00c5241580c1c804001d801c24500600e8a60303e0114014011a240e0080700c80180e4500c0249803071420805031903580307002c05090058542880d00c0c0c100d0700d1400920050f00d004500080c80a10184045211100e078003009006c1081a051460120024580701c1c070762010611b0085800912065180080c1008080135600d00c1705019041c0005003e56414a04661103030700850704002190303800207a070303640003602031800c500c01f039503114800946813285100c04d591129035084004100480026240240c4000b80d0f03c0c1400541a0300c48145081824084e000140c1c226102c02e10240c113000c80040040041407402123540d0750500000c10311644290041c105000514505000b480b408000d000042030483c40106034410080e16108002d640f600410703002c0110115488160070001d40580e18980d4200380b2a80c04814802e0300030b400c090441ca647c40700c4101c641e00042452030503200b5030744516009007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 450038750 1250 450037500 450037507
    0x13060803090a142101020d06060504050a120f0f1505190e1906051009060b071101090803030a02031312030c2318030316110a051219020402042c0912 65
    0x380c51a40c0c4403d2584e140e10540d800c1c807003030450441500904005021541302c0a541d627040030180411400e00703801a4000020300d1145100180d403912745030100b15084a0018400501458421234101c19407074000c190506002c10b1001c180003460268015822910007084034032040e02d4150789031100c1001400c0540d0341d15100d4804207a10740c1149a01c00340c0070300c440f0419511003200c82c045501c2c0f40c200883d0b807a0301107078902c01c000c0c68a011302d088040900f006a0b1443c86c100b0440d6a81c807000b031101001c80e0700880807518824102c4c0c10390f8035960b4804054100043c07400c00040043c840c00324010009400c00e50201696182095103c007100712054003546403a01c000310082c1e400b948044a1790f00743c4070400c149a0341100f0f00c16208a078074440d0041c0c2d880e64690788108508810340e0b4001900c11400b20310b125214500000f8101c041208091000c10300d03121070300005000f40078681c4401c000039001c9103c10715107010042c0c1481010035a01402146440e0b807100180c5d184108141c220300d075070040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 450040000 1250 450038750 450038779
    0xf12090c120d0f030b030a060f0605090108070603090f080324010503060d030e03160e15061312020d020a0611160f030327090e190312020913060803090a14 68
    0x5058524008400d41804034484000345c000c02e1a010390340c0390582d8542d5843c4210503910400c0d02075400104800c50b4004019414801d00c02c0d11105144541c8080c1a40c849000041004010744d40880540060086480b85010101c0d0400740c02003101c08070200e5080901c41e1900c0d03004000352400b411014001214043e12039600381c454801090302a0384c18480c0800f1001c100c02e00b0880140500740d00880003c9506003c0c00100c1c03c0284485240c2c070890090080600c603c1200065a003120b81702a401e554010040c004146581289240690031075a072550109072035820030712000c1c104070744404503103155050304200718501901c0d005022002c901103034200302182c4183c80140340e10000b92a840c2c1d9291440128200f04085a40301c009855100c005500d1104400d100b00c168074004240c050071496043e035801400929070309104a01c0903404500d00d030503503c42000c0b80c04140341015082201c9601c82c18441c2c0d5a4220608292140d4005540414142070f1015a0348031907001602c2c140904e800c6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 450041250 1250 450040000 450040007
    0x910140306060a0c0209070908160509070806130608032119020906130f05010f050c120a050d05040f020a08070b0702010f0c05061005010f031806020a050f12090c120d 73
    0x48100f0010000710b480c140026070f540008440c0181d1250b180e100840d0b16080c513030303800c0803403111350001d541d8100001000903032034448072141d00a115140440c00d0383e85410005a0341d50b2024490384645152a001080c0000004010040441f00d0199201070004016815007400001c40c0d045208070812200000c403100c454003d40081607001302800d0034a003441003a081c1c400d450340d0107188200000c480030082942c02c880c10200b0040302c0d242162030695000311240d90b0307444100800c040c882c0c000608958242c801d0041d1585021000810f004a0505061140c405c002c1c840041e0301c1089030040c00500301c000014007104403441345403441d0600d4400c0e00103481105a10743c3d60002d200001c0c2d15a800200b0034850a0b00c9241c072440d41d085d010381040c0005040340c06102c4030380e062600c1c14404003c1e1507015030040202030351103800503a841d003140008030f07082d01510200c2116140f0115001800c40720b1440601c5c82800c0c1e4400301c485000036103080050742203014105c9042c5400c4121324546c0d0621 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 450042500 1250 450041250 450041257
    0x70503032706160b0f0c0703081302010509042904021c090305040312080702060a05061e060d060b030726011403070e0c0a090f05031c02010b0411091014030606 70
    0x340603074106402002c40f0885108079072012902035000808200202944050b056089607078900f440f400d0840ca43c3c0c0142001e0400751404004803504840781d0f04581c400c1c41101d181e42c00180003848400d41c007034118840b64030302d800c140c0701e0701e04d14034408640c9040605c203660120b0203005040340611040b292010080c4001141030302044410400400425002c40e1003200907611a078505000d4541540024100f80c001751091441c2810b00b0309218056641028900030324103100d00c00d01c500b070889030006030f003445280126664641032400010305c0502e400c0c00355203e4041620342c4041840e0110142c403500e00034010007410755860f40014001520501b920f0102c4035800341c100c82c14551201c0d4078003003122088480c1d0140100010b40810095407003240b003c001c0c04418103011065003003100003521442201755071081144800b12a0003414400d4010203840400074004000406007000401c1c2c0c1136001c1d082017801180300140045c1c0c0d4034811481021090760041d102b504648504040011a91 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 450043750 1250 450042500 450042577
    0x203031f05060f0a08060a0b03060f06121515040305030d09020310150504060b031b070f0b040308010e0f0708011509030204060b0d1413022b03020d0207050303 70
    0x203445200100e0710381c036a41d000345841e0100710681911090141c074001c242003c0200f040d0b014104101c2c080220301c90f520281ca401000407a01c03080d544405001003800c60089040c521010002a402c0c007103c100c045c0280f0090760000da49200c40c0308a0410050f0880c456480028440e5200300000501007020758090589207100909842c51409080990020350741220310300764103100d42401c2080135251511526008140d1034001c1e60941c54000e0f0041c81d01e880c43d6482500030340c40007030351b8800c01000031045c440389079024444c1c1078141428100144855006d001d404200710313401011a10103180018103a100b1495903403140866030800e04402440c1c070340d2013041d40034040c40e80004070041e42c07280184405881c0c8015200c3c2c480811004010984154081e282d0304504c40c6802e00c8022203102000360041c0c0c0d01600e00303410f61980c01c40130140045400d02c01e0208080104042c0d010907130701284000e64901203a003241c150a8480c1c003015141c3c07143d1170301203140309641c2c240c08440c4e140700300d42c020010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 450045000 1250 450043750 450043801
    0x9040c0501030507090302040e060a0f11090405040201140f090103141302012003041211040c30020301060f170601050d0e120a020304031b060509040902030a14010b011e020303 77
    0x300d1b82c03a030210301035880201c051038132504503a00b000309540c034034070640042051120b4140314049121101d200b962003280c58440c001c1c1c1d2904009420b690140189a0841102014059a420b12903080c3c41494001e1448140080d0a0092180e040d5008100d454041c0d010078840d48410030444d401900c2c54440d02503030400c00480498800b01c81c4c103040c4040c00081c070b1000301380c02021213a4034088408503890040c0034400c520b4900c00c0134003103600c45407400300f100e541000e50a6034183d030145500c0715500502001c034550f000000110780d051340401c596000c19407603210200354451640c511240454222017190005006004403d86191580c1044e41288800f1041d554001030060001846500c1441c0200c0540e00010f001c104200000880030741d10312624581b030a803d81820f20080075440f44400361403146448210312402e660301407045595199201c40f5207100340301014442806012841603036404a40c000403030086001f4503414444891546502940c40e543c0c42900c00d46034680c0e02584650003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 450046250 1250 450045000 450045017
    0x60509060a030207060b19031b0f0b07050307020405011508090601051e0604051503040c080f1b060c060103060e010b010201020403053a080a0501090216260f04080c09040c0501030507 80
    0x2981c41d403076001f03070800c0603503034880503e10708500300010f80b032007001c204c002e140001d40d03802c0200035403c40508050b00d6922320a190758403654242203182d409400c40180d40315160900004842560800d501c0702c80400d5110401d580c2e49126106441e41c0b400d10031681c00c0002401320307102c3c0090850302c1d0071040000400d01401d10352101c000c07600082c2d0000c0070310801e04000080c4801d2100d5038101c0b40080110400401e2000300781d008182d1100081d0018203402d0345181e5404000d95981000d49040560700d8013150025070752070501c1c1d400350111200e0300e400d0354130300064801254418003c58080d81d0300900107014040b032000d040042c822600c00004080884019000d8203400c0c1c680c0c401c002040c05646c1c10b841d9003031050110003114411380c003070a0302600c100040c5070000705545041c0d0515400c0030384004d4a90580740740b4071310180c6c150040c418440b0001211395081030902c000d00161505a400c4034440380340c0500340300e8207441c1074401400d9480315840411846d0f10a4125a500038280c0c0380c0714a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 450047500 1250 450046250 450046271
    0x60e09042d0b0402120304030c050d0f0602190e01050901020a1e02030a0803041a0f0a050408091009080c0a1a07020609060a1d1f030f0605030a03090906060509060a03020706 76
    0x940303a440000c40b40d4000c0342040c4415840c00c480b4150b09601c0c128041c5140605e0344d6100002c04000b80301e1a40900350480d40607040c80840000000000d400403415591044003449605000746005c004c0408a664000156200d51056050b04e882da1b0b0181c00401c286481c0da1903400504680000440c039000b0540000c0c00141c40c1806010390180c8580d10458513030405203032444110b83d0064039a11440c44a03010441c0b50032a031900f05070000365079000007585440d14102881140f040103501500414801007942c0c002d540907121800301c0d0009407d5076007100d4880c08212411a045c4107505a002080701c440c4d100c0c4403c17a0081c82c006200a01c003618081031240426000d40080105a010640442d0003084201c400310040880f641d0450785498030160350840c01105400390510b0700209a40e45070240c40170650f0340d01600150100504551098100d40390042c00103441d0300070140c08600707040b00054114081c2003030b54828000204024103041c01d2130802c9000350810740040d00c2e0315445190129 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 450048750 1250 450047500 450047573
    0x15020d0522030309030b06030a030801050f0f090108030904060b03060f0111010f0614100806061b12071b08060c0d050604020d090b060a0803090f1002070915090501060e0904 76
    0xa000310f02c039450b006541461030410710740c6030304014203940c003a0b0840c502d94000a1381c00040c4506443e000c61344049000305034004078030030141a25101c0e803c031840394004102d00e40700001602100c442101c0501403192560001075840c00217a80c403a80100c2c0d8420028801d41c011420320402941c0c0d04000984940300a00003401e446882d03025482c040614102950242407a401681d0202520300304043d050501c00c01140c3d05114558102805400c48408500d80d01e406000b1580d00844280c040c64840702142411946203040803d440740b044288140012000400729081d845510454446810007410425002c09020001d04c0c2a0b807041d030800400761590031910039690594021180d402c03440ca002c40610941e000f564005498652083c49442c9882c0e88040406d0049541615020203200c1d8001d4241e01d007602a0700725142c071500340070348a81030061440111007220010142403181d640d8548007a62025041807480b90011120340c001000702ea10914402c40d11481e0302c444420320082031080c135 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 450050000 1250 450048750 450048817
    0xe0c01110d0f050d1e2405090c040503060a0c0e01090e01030206030c0903010e010c0201180b0a0e030f07060b04180506041704170604110103050603191514060a15020d05 74
    0x4000803002014174481c0045910444010a80c4000340c1000043c1ca141d151501c1950751081c10310860003040010441c07203c40b02a00c00800014088420030b0070b246050310f000d00f00a21001c000a02480301e110103075840b50313000344121002080465100d034216001c0c00f04640c0700601c01c21050104010b441000d840c03d2050501d880ca6060000420244180000303003900c43d840f48074004185045100000b03d1410158190043c03d8030b940001c01e4442009100c0c03e40c041d44000118410010074040c00b8484a90000c03aa80442150104010f1820b184132003003007040e50101038560341c4072100117000038242c6002540c251070300307a000c282460768941c026150369907451094a80758008800f0f0204108440ca81854080c00c03d00b428402032070318038040b81e076501600003400810036000d100300d81409200001d010140507090070611a20f25040e4080300b05440036601c03a0f00400e582c0c000000c0700f1341004a0304d5001c403044c1e40a0004144514011a659040500c4008042214010040184130605400e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 450051250 1250 450050000 450050021
    0xa0207020a15091502101802061c05100608070c0f12030903030b030c01051909051c050613051b13020406020d0206100e040303020f0c100e0c01110d0f050d 68
    0x40b1101100c0721401801440c96900120b810f5070702081c201a200c0d000f00300001b41e90004180040c085500002c0c03401e100c0d22282e0702035088507000806450013900035012100c808213401041c000d607102c425440122400d24030640001501d20303400314100500c21218406981c0c000d40f58000460003a8441e140081030400e44000400d41c4c1d106401d00301034250003401c11005089002c0d0250250410010704a8801e440041d030000220303840c4401c109010b800180050080506603500d0300c0307484405140c01c41c200507400e40b0907104110000703004084030241d00d28000c0c1e0003000b07041d00d01c03812050ba450008103196100c0c1e000d81c074044e02d0701d52104039101800c010708041d0b0040c64048000b00029040c902d015283d01704e02d24100030184502c2c1101d08642d508180d15240050b48c4407000801c5c00c4a41c01a450316560754040c502d1140408145a00306d0302441a540d41900c0480d0a402d0042d56001110740c540b4855811260b915401280108203004001285052403454200814840411190034044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 450052500 1250 450051250 450051269
    0x180607150606050d06080703020604050603190e0d0e04092003010e060a021207182102030d030c030c0e180a0b090708041101031116170f03041407051302030a0207020a 73
    0x550300c1e00c00d90f1030301405c4020581c010142200505540100340c8603c07442c05124007501000001c594404580c83d81d03104d00384070b151001c00c9840508c04081d0f07103a0203c00003000014205804e0400c2a2030540700d820055580013074030000300c007485141144846040070340f1a606569840100846034000d0260304e12a0768645030051792207402c80c1b8180e0009a000d01420200301440740d1040c10b40441055030010703145034102440c0704042c036094030061140c001c08000d401d070081034202e003105034054201d800901102e89040c030030900198821612001c928507480d0380b0003808004800e884862880c8907803c0960410085100c0345958040342c03d04034103071031080c0014030520402007400700c903d007038400040091a01f030226030760b1b0001c0f103500d60192060186403890300c030100004001c02c03030b080c1c0028170780c20040261325000000ca55171529042280c0654140354445020ad5018001203a0407056400c011f054901f0380c0c1d0780709058402034100520b0944c64540c03c220080250703071010f131400010040c115 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 450053750 1250 450052500 450052507
    0x20f0a091d0402090a180c1d0901021911010b091006032d0e0f0d09050319240204030203010f0209041d1c0c060608031e18060715060605 60
    0x6100341041241e04000c18207400160081c0001640d030b6401964101401c10004110f41400c140c01c00c40844112100134924205403000003000d40f070036503032401010450b50203166195a024899800c1c1c2c814417a000340301d28110400001154000c03a0103404201402000141ea21003c0c00840c100306420b4801d04180380059800708985580740c0101003807241000000c0c0d07403944c0b0282c1980042e8850201d02c02542d511103c1a080c200000c124440b81d14280108491512107030b04800b030f000341c0d07141c00b841d8041d00800640c0b000301066900300140c8594001e881c3c1207400b4012140d0b00b07808222108418000b9008c000000250342c09000340404030882e00070050341c4030780d10f2040004480d00482d03402d003050b48002c0703042d484100100710b4151103088140503250780700d140c40041340c02e14071a680060080d860090003060820000015003010561042c800922100301030a50403103000d0079101e181003c2441c1c0050030282809406420314074410352482d03520b42108200042aa00c0640014001a4011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 450055000 1250 450053750 450053759
    0x90504090305190e06040b0c0c0405040b0907080319050901090f0e190b0904080a12020c06100e090d0c02010c051506010e040228200c0103150b0d0f020f0a09 69
    0xc803450f48114843c0d0800100d02040c440100300300d0300662058500c03c49000c030b510001ca400620900342c015000610412072490070b4a020444100240d8445c40c07544203019010856900000446001d45085480c801140122010460b07003980612600c0d03040020850001a032031201c0c0000c071001e1302d900b008183c03440c0b40001d0105602003c00130b424040c1410001c001e1364a464040c12150000d8220092030340d51850382000ba40c090710644a841c032036510000f030141c83d07030f040403c07041d010302c550590000c0c2490f9038a0081ca420364042d981d03005190010a0720104040c01031000b22040fa2041c101041003503c10f46600742044285001c403d031982e2030700c00b0001d1540e0301980d080c4a8003808c481c00c6045c4030340c1544803d074100034023061070000e101009201040e540030310004544080758440d2224410108654552296090383d00240840c1c03d004002c1d00c1d84059803400003d442c002031416090200450b07101001e0700c1d1500c2c100d403d4503801c2003032030890503a5034000c00d10a006525000b00140c40e1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 450056250 1250 450055000 450055027
    0x60206070201050c1603120b0d0501020c0106050d02010f0e01140301140f100f0804060902060307020304031203050610050904090c0b0c190b04020d11030304060807080601090503070510090504090305 87
    0x2400c1d580324640802c181c0401c040170540803c840354140c982544010005080c510083ca00241501c0d800000000c1d00e0080100540041c0071020040000b4410155901c0c180101306d001c924000f4007081d130003198486143d1141c111001c02d0700d41490700d005404002658195541d00a070060100144005406c03892410b250040307450090741139401501d480c0303800030000e00840058160504019881000c40c080c850a60440b40e04a070300208015a02d00341150003942d44d41c807620048a40910a95855042501900c0b41c42d200d260040c100c035000070b00040301140d0a034002d012882c4e1080d81c2d100d00c030001c610000d00c014080c2c4120321300180c0e607450424600d454000d00c40d200700c000b04204102480047c0c22460029005039043e42d0980f41030b00645814a62035030074412458051102180001d04280d02404030780c040c0c5441d4170b4101c036940b61000115205c46043c018140c150b40300080410441c1010f0702285038004007850801c4015445400042c20b4409100040d8005400814448800c504 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 450057500 1250 450056250 450056261
    0xf0a05040e061906030c031d010b1806030601050108130c090507110102181011030a020a1a0402090403210513020a1d0402060702150d050a0b10020a020415080601060206070201 77
    0x1202e840022081502100c540c614081c00345404158484100d10880c6e4000e81150005074581480c4000c544040c41402e4000e002d07140244e4447c1107003040c0d8808920500511a01070700e000b43c040c0c0700680c205801074a4640e000741c00c465000c0a49410728002c204580444409008031070808942403c0101004011032035441944e4040c1e441042107803616280400c100541c80c13029a008002c101c028401a60601c04113034607200e9502000601c2c003022640032503022210791080040401c40403442030381c5040c814045a000750002e900c0e80c08540841d01481c0a94810382000c405115070034428040701003602c0d0b0580d4003079580714a01d81848114900350b42401f02411003120480c110101c0e4a1142c070403c1310240c0064007506000500da82903454440030030442c1c034100039960b9650600d50314864002c01c0100d0341240c92034601041e00c00030745000e0800b12242c98042c1c3c010162011142c0802c40284082c1040c9220f410044900103003408040c05054001d06141c3c010b00400c0c0703000000682900d9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 450058750 1250 450057500 450057511
    0x18010f0b0303070615120605100902090306060405040606080f030d0e0f0d050a050708040e0a0c050405011d1201050712060602010b060d1a040e0a020f04110306090c0f0a05040e 77
    0xd05000210290340c400105545075190030440116003018482c0d05d00000510a800a1401c0d0395041034140a10205401544c001c800b442918060959901d032118101c0c090348d4209a45504108003240080c07415400903070700b290180d4000202c0c55911400185454144240710407107400104a4459605041c4602581000484041c24600d4404036045031500050301c41801400804035132442c003d4812400d890f0300e6035000d401655215100c5072030f0300c008802200c2a041d050309111101040310f105900340d504541c0181c64201460040c007102c1c000010441c2e40c4550001d140c0003181050404c04d00800380070b43c213191100c0c00301c0700300ca101c0e40040c2d5602c0d03000344065a04141480c666030315200100c6404100305180004d40c0161201d000c00300c0101c03090403d6005080c120821240d040114500807014821690f01c00c480c41000244025038440c230401c060a21028800140c0b5401c28010065000d17441c0741c0e0300d07880c10304c01d02400740c0c081d044034040d240018408502070141c0c440300307901c0c00d4000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 450060000 1250 450058750 450058781
    0x60f080702121605210403030f020f0a060911030d121a0d0303050718060f030b0d0b010806010f06090e0a0e0712150b010c05120d06030c0b0c070b0406020a03081e1801 73
    0x130105c0c80c10004a40c8142d02c402020400320074a047c00452080c803003851041100007d4039106070303880c1030040184c400c03c0c50a0b1081001d541c07244051b843d00184143c0d05500175120000c0140e90488001c005102c45821641c1c8882c0702c000102d440d0b40c918040e0141307580b10303031000216800c021000802035100c00002552024560005008241e000840149a0500c80c600031030784010010204d110618150002054513005800120302d1240104410b0f05840c0701089048020f80c0e1040d08941c0308180e031192400071494100403d00240c01030300929402680002154034156a400c1448005d81c0e10180946074000c4c2102506020701d0540508440f8480900e4880b21040040d2260b88c0c58000c0d02c1a07000c60000006040050185290403a41c000c0d0f401c2162a00086d9403401c003840c00303074013012129540d03008103140820b00d01503030010754044d990b840d4028541605a40d400340c800034009001c0c0b150060036500814000303605440003030300c2200042c0344407040f48410003c2d2401c2d61101e100c201c1d600c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 450061250 1250 450060000 450060043
    0x415050702150a0f1b0c02011d090c070203011116230318040b1003050a0c020607020a12050d020c0a02041b0c0b13050f210301060f080702121605 64
    0x40d2100b094003030f4000741c0980340080c086800100141c0105030310000c0124603a111011600941d4000c02201c40107070003070b00c3d030310703112020032800d0303901a11000441e50b07000d040703031010030000041e0708041c2c20708903c064000240315100900c052203d411100e200b8010f9980c0160304000c005d152007101c1c1c003034000d2080d660303940103a14a44548038020005001c0b00078039898000c11490307507690420081e5040c00780c0488003090031410001d0241208848184501d8102180d40d000b452000404d24450a6103030b014202d450b089956a0f40a54610f80072801000818004065895924401010465003a20090491100c0341c418042500c1c01074506942c500000490045400d410509400359681d00044503c100d6840c0703003000d04041b0345a40b001d45144540c402c400c0c03014400081c00f00e030310044c00f000d1b64141c64404c501c21105100034050000081c080078002242c050040703e4883e084420307030055480390f8170f07000b401d002c164014500c110351641d030038541c2c041030000a1240030b4048000c21040300c2d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 450062500 1250 450061250 450061273
    0x10e090d030212153111090a0509040305070c142404120f0c0618080d050d0f1d072607050f06040e0108011a0d05070312170415050702 59
    0x19188002422940151050b050032006542c0301c4904021790741303002280101c002510070421921760b241c0c03001800b0740352a06c2d54903a500c5a80c202610440320700141a0002e1504160074425045c001901c103c00f401814099140054989a4088003411000a0080c2b1001d100410403d5013083c600b03490200c640a80031708854110800103c4098a0160051882c02102d40c60f11074480da4180301c0140400c001013078042013007036024900008400d10020302d00400c5032155000c544810740a2078031408241c1c104008030b0b941516412043c0c01c600b40342ea000903215081010328100103901c0707040a02580000100348260441480314154140c840c2959240d0100c3c03000000b6503401072806807611409002c0c071040d000c0c0d925403080340e004d001c000000307652030b503502e0103918082c2803071149000c02001240d10100c418104071030039a401e43d07002001031040c603155484100b0310300401e403c62010130085090420000a5000d44140940d10440ea41c03100d030b07038501c4a504d0131582c0145c80c0d0000c5412211800b903 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 450063750 1250 450062500 450062527
    0xc010e1008070f02121801021212012c0411130e0304051311070503090a060c230708030f041707030308040803150d0605100b0405060f0c1005010e090d0302 68
    0x42e8044034034180f9070b40148a4400580c5800480070102d40c101000090101c0015410603035402d060000b030f000c07604c0c0030703e410f5005441409039401510b42711400c2d4004202c01030940281d0030b011134200c042c5103d090140c0380d6410008030308943c03d5078011942001101a0f05200c01c0004070002d000008000c500c40700703580b40d5180d2240d4415a0b200f501c408541c2d161684482d07004003803072001c103140c0030350700d04181c0f4000da1030703410680701c0c0c61042c140c41d1400101304c0d0203242e0001ca00d0f94411030010850790f6621410030360070096004a009440340100c040382c030910400041aa00c00e20022081d1a94544030b14586000200500c00b1308036048401c0820020341c000b10b5140d00543c1c0020410b440350b5444824580d507000c8800d2035644110264200814880b40d40d00c024010307580500304410054684d191801c041c4214401c1603041042044482d61962200010741502104041501c56941040c1007010079601c00780c1100034071041c0c20041c4141c01c102004030120181090509509141050303440e0f4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 450065000 1250 450063750 450063767
    0x7030c080a0e07270c09030c0801060b031f05100c0b0a270f021003050109180314130509010e060117090309011115040303060f08190f021201020c0c010e10 68
    0x110701048106980e181d40d0701141074100004d0501402c204881c4011900c010206d1865100a503104040035101090b1000180905801d49481c0e2106134a1910750824808000550300400f1102d250f0403440407a090350381c201c40e141c129000ba65400103940c0c190901c044144409004120100e00d45000004e4242580180510b81046120215401101030410b010326101c04030307000f0340c0f05000700801109160540d0125040c1c03520303504108581040e1480d14400c0000580300a00032402d000b114510400001e801088000418414401e52682c4c601c040340112400b0380001407101c0401c1c0c10004a07580c02184080081d100315180c613200d00b00119035584030300c1008121750420070804801c1c0080281040580c1d01c0d1030000c03031048040d00e03140c280100240042e0040121150042400042c0e0080c0020400e0b21640300920020015100383d4402c0c440060b4403008a801421848445022031000e202800c4c07110a0500907040744a11840014186040c0300101c40c8074480c008402c00d01554004201c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 450066250 1250 450065000 450065009
    0xa2102010c08040305010504120306080f070510020118050a030e03070b090f0411070c0602070803130e13080708040f1a0703030b0f0429120d0f1707030c080a0e07 71
    0x507210021401c04001c903202d20f81029059608000500c0100002d4181c00a1540401e40d400c00c1020784a8503256192034003031a0f0031405a1051505000341c0c82e1a43d0210016981c9000004408440241294005030314100954190304280004000d141d0003e04642110300214090175405041c0003600300c1da4000d00c880240514000d00300070000d921613620919102403203010040c0c4840e404d2034040200303074480c0a158018010540700182c00e4000201f40c034842501e00c2007003200141802c4100c140000003c0c807071650a010540400c000c1a1207000404081c0e000b0040641d841e400c10306011904603990f8800e44c0782000304004284030040400c25940e05c3d907031628011524074020400500f6150035420020361052414212001c0d90004a40780401480c4144400f10752500710340421003480d044034100422904050071400b40544500204011040d060602c09800c015407000320108074000c445500100740d442e80d654410710f41050203664440280103003440440c000041d02c64485400e4441c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 450067500 1250 450066250 450066257
    0x60c09030a061e02070f170301060e040b040b06040e1f031502030702160b1b0a050304031b030605070815030c010e133903050601020a020d082101050a210201 69
    0xf10600000300040340504003941400c0700f551501214100035900c1c07024528100d41643e10980b1010a641d2014296070480745142c50b502143d061070018072003d044216100765200e5981e03404d20006980b0840940090441e643c5c0580052030007000c01300d170b010090032100503055000c41040000402154500483e0010490056200e443d04d24040c0c0c03070002c98603d61110403154a4003ca000c00200025041d110705402e94400103403a4500969200c552406003c1e007a504100018401700d03031074400c00c0601c240a0383d001c040607603690b03c80e07404407030007a5116000982500305200100440032407004081c1d604401a22842d1041c10000e4485038240110500a824004040c0c0001e65681e0110b081020b0b1b02c01300001840100e25003403080c01041051504100b02c030810803070201d1091140c0ea11503601a001804002229000c00030038001c0e8080c115588070042080e070381602c17050028164040030505c1034410b107504003420404c0a90041c0c101038030420802e480300c2c0d43c0e070490100c64800b4580a08 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 450068750 1250 450067500 450067511
    0x80f060d0302030d0c020d12051e06010903060207080702040c11150a0b21150f070815121b060a09090f02070c0f0315020a0f08180d0809060c09030a06 66
    0x81c0983c1035010304104005450700d40b105d0391852540110740714001c0343c00e41e44c41ca03555007030000c3c2100880380b099403502200076601d40c070051030612000501e41c01040505108944541d243c0d10070b01664403100049403c0040441c0b03260440c140341c007440784450300c1400d00402100e9a0001070399142000ca0300d900394841c0e03410210b561500140e0080004a00c050003040b49003008102c1591041c0c40407000034020f1051488101c44121180341d05401014104080c800f641c64880b011510f4500141801c225842c40c21300f680c00503074401c24590603078000c40010b44844d00b42111442d03a01509002c40c240a07060400c00c0302c164540c003001a005480280c10000f503294040800071000f80280400241904a59030000c0303810f18044003440d08680c0300381da4007046024000318101c00d07030241c02c81480200b2060000c041140d07000707100f40d6500c40301700494a041941c03140129840c20030b04203c08008211b084e4188221000c0c02e100d0682d214a07100d818914140e15036007c280c2c0c6044280d0041e011541e501c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 450070000 1250 450068750 450068753
    0xe01050a0f032309060f01261f15060203091c050f071806050301020406080109050414030a0e15040f05130207080a05090f010c020907030207150614010f080f060d 71
    0x2a4031030184842503d02541c040441000120080c3e4015200307207549114080004000825003104a4141d58440000d18070801c140d120080d4483c2d116407502c4468090761402240c4c01241c0256400c180b5005103020039001920f611900103454250400c01c119042044030721a02c1d100c4c1c1c0d552031407420b0500001c80c04d0145908001d4146800e801c4240d90b107001c0c0200015040f44030141021640d000e0315003c106090f80e80042500700d104178410350000c030b50140c00410443ca6143e22032540b140c050613400c070054810000403070459200e101c04c400418031003e40a83c440c1440340c0c040c0203920400d40e085207400e0510050ac0044103407885040d20a4508480154001903580c042d941c5655000c0591601c0b845100d102400c035810006955004010704003003002990720a1100240c1e00e5009404c400c8503031502e900440195101c154150348400f626041140301b4a59841000000d0800c03610052500340b204000512004501e9400d804000c0e02100340500940440c081740d4008030103d68680007032100c1e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 450071250 1250 450070000 450070007
    0x1b0702040204091104170c090a1a0301111c0b0a0b07050316030e181902180d11090603061b0306040f050708060a09020f04050f010215040f02030c010e01050a0f 70
    0xc81e003040079400d00f0310410400f022104000350050b1842008080c0200c40c4a4813551747e46c0000ca00550303031040d07400340401c00441c881d80c041e100b40640c10016007801455a404a820341d940c44507889003c400c00104802c0800001102210320542160180310759024500000c0890109004000740480c0004200b400c00604000325005480c1e00e111001800340e03141005031079075102c1c00c0700038001e000b03500720f51403000008038000d0701c6046452809079a1518410003034009400a0b5081c1054109400485e00039956030b107071115985220700b007421000c0d072101c801d000b020f40c0041d00380341c0030b41d0003a0240124103000104e1502a60108101c040d00c2e9558003001401515014400040c2c0b030745001700f4404074130340c0840501c0c411441070341c00400055544104104030710038843c008031488010301003840309180205009048940501c119a1501407080f20180640c0050700e0482d42e0745c0815082c002181014001c030817695109003001c1c1c03080101c90002808612540d0744004c01c01c52480c200b061903032301 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 450072500 1250 450071250 450071257
    0x3021507090e0a05060a060c230f07080f1209100c06140a09030311031506070507030507060908070f061d042c210909100806070504031a1b07020402 65
    0x10084107011400c280500c4402480240c4a0721b00400e100180801d8003805420300c000d000b82e00c402caa40082c02411400091111003a0404100c0d018480401ca4500e00c2000400c000d400000081d00e200342c0c8402181e8644400303441070290151050000d62055130300c0b64205407170504207041c440f9420760540750031002850b16030590203d202c0e180061000d106100d9001e425241c1c840c3d28100110310351030080301c0c858007044500e509400c2d11a040c4920500304000600104d80c0300e00111031401e5204c2d5102400c0130400d40100d00000d0480c0b804024824080204d0801800a0304a15202c0c40c2003c600074a00c42150310a007080d0b00c14400c08038103a1b03c0d9913020022018200120b9441214031005101080100c9a0b0364481da00c40d1445c0d84105015210f0710b048003080100803103141c1050354082c403442c5076008102240208020a001034840320605c0500d110b4101d5607078046e1398600b9071802e075070007085450401e020540e01a0401400401001110048401041d142e075164121413002802911 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 450073750 1250 450072500 450072509
    0x7121a0a15020109120c02010206070c0b01060302070516120b0a020a090909020105121f170304030b07020f060903120711060103080d021e070519030e0409030c1b0306060b070302150709 81
    0x241700416034440a03480398042c0c10140c0300340c4c26580d058440940c22a15100c00340000740407940d035034004210050080d40200aa907101c1c200f5590408a44c09a070070314000f195000d500c1090207000d106041001d01e02840fa44604002d200b1400d02c004104000c080d10014040c0c80e04440c1d892036034009580c000c2054031601646059140000c0c03400074114010700e4601003a420820745042c3d40481e0f444030b4a001000b41c1c0d00908002c6040c5480c41d2540c02c22407801a04003000c1d4000e180c01101e4840050144e5407081d55480c005580d2130f40004a80c0c000d01000600f0300d0f04100c040c41000c400c0b50750201d00c950440783c00410642d00c4040503903041e002441040ca0010b10040d401711420707540c0540340082c008103400b8030b09540316150101c00e0700c04401c2c00c024005000034206841d81e1030500d400c1c1d120319501030080c6400f2840c20501c0d43c41300c2041c828441400c065a807021000c10400c0704e2030142001800840603020f003898100e0390040d60302d000c2411840034580040c800504460301c01d46c003440040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 450075000 1250 450073750 450073763
    0x120a0b130c030b0307060e0d060b1507030f0806100f141308010911061c05040f080c06040203010e01060b0a050c03130308070b0709050f0603041a07121a0a15020109 72
    0x7481c2490140c0200500d40b00d0b03c0c000e0040620010720f42d4010b6041c08000c40018141d0740700f0303007075907580e080082c1050044940d0041c03d0f4030610301c2d800b1101000d060003c0c4652030350042066500c002034481000200007a125112038510808035682c8034810075000005400c140c0400082030b911861280144248250040c3c17200c2c0001400350300540002042501070742601035452100c905021041c4a40c4590720304202c2a100b002d1202a040e52286d0343c401d000c2c502c2c40e00449250340d10607070f80e03600c05800015075500c9503003444107500d4281300e5529030440e660002c101d541c0c5000424605402251381c0f074010b01c040402c8401b0b03005000d004076200c62403215404007201e501d034030b070000003900b1801c420740f005488800010015801104a8810f85400070880c1320420300c0c1004020b02030713000a200301d82505031640c1410140100b0303d10315006000c3c6803036010009000a8081044440d040152207284040c1318440041e600e810500800b624289100114410744410007640900340104004042 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 450076250 1250 450075000 450075011
    0x30e0f0118021c030e10050904020d0c080f0405060121020a0b030103120302090609120109050a03091a160807050a050703120306050102013303020a09061703120a0b13 73
    0x3407400705031000c0c001d61085904600e0083c10b05840c20700c0d599842d03c020080345d083d0702c103485c41b40342c0340c00412803604103407420030701c4c1c0101c0c600030805a0300410403881d109903c039081d0340d51240d0020701c000e5006410441c003c5003860991507080e0340c2d64043c400c0031441c0010550030700200b000c980543e03145035006491442070a65a00c81d42c2c1d40d0354424030007030f299145403070515100f1512070b00071110010001000b03d402c005004041155050499511071071540d60313003034004000346041c0002114140a41c841c40c3d0410700d043e01450894000c5a001c0f10f10310310410040032044030401c940a000f07074006890030b8030b464140c5016071070800d90380e0015003d4403130044000100a40c004902000f0342032036609014250b5510700590a9075005102c0002d800d0320a00c004d0400c0351040806402407151022080a8582d01e401149a509907a040440c3e26511482c2c10b00240034110b4500c9100030a24008516014100c42c1c00314001c071000c0c100b42a03143d202c0c030110780140d0300c00d00506400503400b4000c124 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 450077500 1250 450076250 450076271
    0xa0f0803040314160e06121009020f0102010b1518090903090a060305151203090a060203041d070503041b03150c091712030604060906060503011e1401030e0f01 70
    0x1680d070071a210454903848801040c12500c200411100f50b103070020380c0494981400d00180c2d2010a100401c8640c100f81a45101d980898040117400e81a920f16500020219002d00501c4100000d01d800716040da810f203103030881c040c2c940403a0305880d01c1302d04c510542c8540861068810004401c28450b9005841005002007000044001c0035170134402c8556084940d43c0308022703810360744226080c03820a42c00840c50f2a05052886202c04800100d000340c07403502e00301000050340740c01c3c42c0e00300304010392001c03e05100c00c220306803142041191400b0400010711b00680d004205110041000b0400e441d08552406410540c0c22080c5c09150700c911008000b4625403500300082884d074080300c001450307210002071404050300303200451000d0389014084a000d00707a10200c203540060002a04160384040000d4155424814480070342020b50b20190703654949900c0e40c1c540503000c0303100350081071500710800003d0191001009515403c3c01c01244116544100b2400c01035007010802140d401c1c0500c008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 450078750 1250 450077500 450077503
    0x18020702120a20090c09041a030601140909060c0a0f18090f18020f011d090103060c02060a1512030509180714030408071b090f0212090309010806010e0a0f08 69
    0x803c00c001d20700e1101e220034101c100300240c0e82000e50b000c04190344100140902401c2540114409800e14002c0400088403040428684802640171070140340c4c03103e00d03650062030100509030304500e040d00200540c0c1001c42c800802445aa9200d1061040c00e801010070680a58584000090070804031b218940d0f4030301c06400a05609000107031103a152400400460303403910b104010286e00031780751540c070b0101c3c0780c0156018450b164844001201a4481d02020303074448080078082c0d40300f001c0108081001409c040d29120000d450142d0003400d000c1200040070340e8a0807030003151610f922012103d509814192018814401c41540141303240e00c01d02070901e84400194000e0400c1ea842c041703480350300b080f04103403408280c0d402090010104a2007010414030200d0f085035403480889141805d5842070f140302110480c01d4100c2d29a074002c40c070381051102e5076811130341c0003001c6000382d490004202c2c00209410b00041185044c48032101c9000382c55110741164a001e0540078601007800c58482c070809 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 450080000 1250 450078750 450078773
    0x60a0306021303060e1b090a0f05091c110d031e02030a140105180a02070804080d0804030311160b0901060510090f09020403050703030305060609100c020306060301020418020702120a 80
    0xa84410f07003440740d031741458080007610168480382c800b40250f02c04100c8082100b10540544403245058945540d2400b0100c5441007078001e01c59880203084e00289031240760150751030400c00600f800386d6454074060603000840c2e04070226045181c000b4001d211801c00c01c0c1c0f00c0f80d40d084c0c01d10009202200b0410442030941c03003013403e901034030b440c006580c2c1d81d841080000e03034139001c1c40080c0d05207040c0131035124402c036000341040500c688442410302e610389258516140c441c0c005400015001001d10060507010310500035020b112840c180e2400c0300203001c1d8940c800825400609403902000046c002d10400c1d40a0344c0901802800e96104060018000306900d4050094844440140b43c001400f80040e1013114126540080605503c61035a00d0a50060200400407604820100300424050399010b80c10ba41402b00340d10307100340040460042c175152810042019009a10421081c404032910107031070940700c42048009a51502d040c03020071512035621600800c40d00c0740c041110304100c20740c501d6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 450081250 1250 450080000 450080003
    0x120c0807030e030c07170a122003070f0b071106070f0e120d080910090602040312030c0923060c0312092a121c030c0309020a0b03060a0306021303 64
    0x5100c0c02c1004141aa100d11481050b4486680014030401803100b0000c5214581d80e020010b45038541c02a8595608c043c160a0b5240000384020a950f83d64034070341400d200800c1d84420056080c900c1c2540d4920781c58100800150240740d100000505040c45458401800300bc0e040584031241058840500004240313403600c0c01096003031030241c0d101d041051b0048030100100008080b6992208000d0b01c04010240550760036004030100c00030b0b007103814000c61025500c9140c0c01640c680c81c50400454031a03a28400310105402c0035800072100741c2c0180041d0950b039101070f1043c60b400e00e4041c1c1c0c1030300441c260303e00d40e000240481e04541e040070200c060003925000e1070201205a40d50316210b130700c07148080003100040004488420b110405c0805090218901a00324828007050880240c5420002c00780d81075072185610b400b8400681c940a51034660000d1b041c244220f905075400500d02c042c4500920101010100005c1d25a42d00c13420351500850b0484421075a4100c498a40d150200c09c9010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 450082500 1250 450081250 450081257
    0x90a15030b12070927030c0213090f110604180501050a05030304080d0e01050d1a10050711090a090f0c1e060e040504060f0e10050105030a080d0c120c0807 68
    0x7030309035075410892410180050280301070068142000344050041040c042e008105840c2540c400f010301d0004001100b04601070344501003100d500344100943c0e84103030400c0d030a040c1c1c00e0a00f207200140000d9400320120f640419800318450780c2c41c000c50365900846c0d10030b00c080712a0350041c15400800c0d0b400103050380d4066802c000110344403c103042e40c0307108600c02c2c91400ea00030031403c501a8400c840100c0051014074002d847c120601e21208182c40c3c00c401e1810000003242408099483e10034000703c4500041e040039030600200382c803494840b0b98404011800790340d0000002c1c610720407a03030140a0030b40d0f20003800480138210b1b042c1520300340700c503015094500c603c4450000044600040c00403c442583d5501011502e8030028803004c0c03c0041d00485029841c1c810021a8080c0d42c010000c000d05004000c002c0081480f8900060f6041a840140070340c025545020210341c51008880303140d80b0140002c80c1e01d8014070302c100e0f5086850204010411310b0844500d04c0c1d0355000c011f0602501c0c6969 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 450083750 1250 450082500 450082511
    0x140f0102060105010203070807020a0e070210141005120a0b010b0a0314060f0f010c080d0c080a0b0328170c0f070e150604090509030a020f2d0102090a1503 68
    0x50059989890a018240c0503a006022071030000c1c034120010b01c0c1c92480a00701410307943d03965480510f051810799a046c0940c00814002030204100e1050314a00c403403204100a450800c840d21944402c4540680c5025501d0122900d1210070100404000704e6440f6184203015a0350b0142124113401031452040081c1c14450f0a0100c60951049640182d9008020b00d1941d02c05001b045005011001c8483c140710f83c03030384210080341204019050481c40d009000c10594a04080140602e0f07005100030120392a080c0d04141e10740b00040c24000c00c131041c0c052000310032128501d40c200210304e040d0060043c11100c00c40c0300c8007031550b0041c00c10440c60004440106200381c00042d2141c1d42402054110480540000d40011900104076012940074024501d440d40340c0410001303441c01152030150341d50000030307005001541040003141da4200003000c1c0c12425480c8001c0d0103024412291020712043c0314000e5144a5401e604548028a004000380e106541e2481101121924001940c01003071402 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 450085000 1250 450083750 450083779
    0xe07080c090402161211190b040b090304091107020901050d0b06060d0e01050f16020f03040e100803030f010315090309031b081203090601140303090f150414 69
    0x1598198000d9030003106440c20065164280310007034100d41d07a0300e491003401400303400104002560fa02c034030341e441da0366103103c041d00c18000514001019130540090400c50a0b5500414024060242c0196104d0a4001d0030344456040c6480e42c080da4100c0b40e400d9182601a4002c0b40100d0f0042c218a03100f51028050344c1c2e6a4801c0040c14454074401425800c003400000300180307040f100404100101440c005115085040594211001201c100710260300c602c0900124030300340d885030204030a140c8000d11120391803000480c4c49004500c00c004411864001140d600a00c2c1c441c150041c0450714200e030348a10300b07110f10740c01141003031006441c0c14000d15003c1da1400310a000d8000381681540716500d80340d1450356107400c050301c0d11040103800800c658010802030018081c50104035101c8104640b2401c0119689050070f0043c3d104119600d218211901035440100c10340300803000071a0154032521200010601004003100016107031100014041520040c00101c6285031001751f56103900c1c140e61 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 450086250 1250 450085000 450085007
    0x307030510050d060e010609060803090405061002150c160302060609070e0109060509040b040212010e0a2003041403040807030c0b0703090e0c0c06010e0a0506031c1112130e07 77
    0x54010550004070030f841d1000415020f4002c100341d10f403030400005040f9541c11501d8116074803a00032440c0b50b080066181e525141a0082a820042c215000222443c0031880650760f50407648140407541200000074100c208a40c0540750320b030f80c0089080300c09400e02c0c900291078002c2103440910a02c41400464003d44c803c800e541007440d0103859400d0b000c0d00b0588107079031350780042d03031440d6200b6100e81000d0b91580f207038006800c4520090903000c00550501e02c2040016100410b03030b0344100d180002d41e400c0718200061200c054040201581d660307440d01c0c20404600700c0c0c03030f04040c1381502c030001d0005000d030030003d02d6404072809459101080e0382c5500801c4e420744160b82d0007034002400030700d060004100304950340e500305003150f031400d241240c01310020f803e0202c242c0c01124004072440400030201e0203406600e6010000b00c000d0818402d007001801114060201c0000400913551480205a0b0040003550b1a64065080d020746607050500c0c1c10610342641d0080e0300580700f41d82c0201b40310a02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 450087500 1250 450086250 450086281
    0x507030e011b0f0e120a050d020d0c05060a0c120c2001090510020a091d0103020a080f06152b1b0f05010e0f1903120c020f0d0320010203070305 63
    0x106980e2084081903c0d6070803150200d05070480f552014681d0541044020100242d10180d0300c030318064181c00504100190400c0700140c001c0341406054075521001600202e00035a01007a45d150006882460040403161070ba2140300c216600c0340740c44160030f0142c1d0000c214680210580d81e2500001c0c0810014a080e2030010070018a640c0c0400c90302500e0a942e90040c081040c0d0b540760034600541e844481500d02213102a001c0b4080031402c00501c00c0d8101815154090a0808010000c0c0358066005c6607440704c0043c01d209409070644000320b0903503280c50404480203154180600e43c0596041000e0b507920702c2d1442220060b003c0c41e102c2c0500307500840e604045a41600c11501c1c0c1908d0039005480209003000c905902c1054180005000c2e07840005c0c26824000d0307900681501411413400c143c0c20b281d44101401403015400c00d03840140d880e85c5420018260a03903510032280c040303140598241c0700c401a10480720511107111000c038201503028512540b40740c0c0d0103002544442c62180310090 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 450088750 1250 450087500 450087551
    0x3020306011d2a040609060e0402160b040327080d020604030f080a1104151d1e061908150f0906061e03010602030408010b0a0e190603060507030e01 65
    0x120040004031001c814207100141c80f00e4545006040d41c0c50000304090940c81a0492408281039010a12250358000c0902e000c0d0402901d08514000381d0300781410950b035250724010038245c030305c400240805100307090900704e0400700803601444042d00400880300341120b00a400c0c8a1003030003805119584001100380c006d0f501519130482462800f5422038050b1001419000e055450b85946880500c89600400c02480e201a90712487c0302da1035401000a860700c50213440807101c0504244213655001c90400c07110250000704c07180140b4600200d050380c00b030000250f01100200c40e4403540c668000ca00b00e4861407204081c080c2c14000da9082004c22455400015009003001c0005151414184001c20f4402d10081c0290711010b04181400290350090300f0010041e04082420003111400f40510481c190b000c441000038241404000c28045034000c01781440d8a402e412625800c0c0540e920100195801800034030a9140c12034002c6d01030b10f06000103c0043d840c0c030075103a90381c1468106840a40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 450090000 1250 450088750 450088799
    0x909110a0b12070215070c02030c1801050402070501110703180b03010b0a0c020315070906020d030e0a03031e0504110f030d0f080702070e040606030507051c03080a1103100302030601 80
    0x11181d200d019026400c01401c090940c031604081e00b00d245c4564004030f10480c515038555281002520500d420300800c0d162040c00b4a0400c466020820b4141a0207415038109440060300d4941c00d05000703014007010b041c0107588042c009110010305501c1044480b000c51004a10180150713240a01c480b503200904c5003540d50901071000510131403151602840142c00113040700d103113a502480c05c80c0001419030303040e804954240410445280c041c052810a0403503400c080019404492803540c9800e111031002302019501d00041310340c00308950b41e45130071203407140d01000030345001d250030801a4501c84c9041e215810a4203080c00c51300d0700245c1c204940301169200f0000840c54032040d9140d810181c8001c05502a1410201d02c00840004491090380135810104243d403860901174140031040e04414003c41155080d015541e80720105000b03010750501d4900d60390359500c14000d0041c5102d03603400d0f5801c90000140704540c8054900c10050f0382c0210300b500c81c641d903640d41310700c01c800071401c0c01c4019 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 450091250 1250 450090000 450090007
    0xc23070f1a18060a20030412110d05030a05030406140103031b020f120610120305041211090c090909010c2c0301090506071b0f061d0102040909110a0b 66
    0x1640e0001000c0c10b5004848451840c11440c0e0300d0000d5100c2d04a80008000079404203100c2034062003000d11403a0100b035420165241031b0500d090b1865a44030520080c01d5640c4644850842d41c40c0d0340d4560680f00d0700f04080e40d855a001140c001c2240c1c0c401d403010b640303642c1011a90b00c3c0c07001000c003886041b0ba6040e11200781000000e481e00342c4440919070140d0348520001c5a031403554a40406201900e041000985914074283c1741400c43c00d00c007a0010070301411f1030714442d40001e0f0440c2c00c44003607440303c192072440d898040c5440760074840210707038080e0415071000500900003501400f40400b00411506800182d490040e81800ca492504400300020304000e510035030200039015410050072085840502a901d98000c207003521a208000c980725070080b41000301c01ca902149105181400c031101c155401090b48840101883e81c1201500444d644c04002c2c902000b003050043d501582c00009646840d5104111f0700144211601039079101c5085503011481e144c4044590295691119018103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 450092500 1250 450091250 450091289
    0x5031506010e0103090203030c100e03030103030c02060d062402010e1209062101030b011a07021005090d140d02010609060f0306050601090b0f0301050135070c23070f 73
    0x1c1c0301c061415414113040d41d50301c42d440561010710041c5144040ea500a04903240401c00a1382100c80300140b03610075810910041c0002640700e814480880d80482e69103480e0380451070001c0041c1003903417028181516a0090310f02c01c102056503000c0f082c2650b002045000c3c1c0c0c0d101e00ca40c40c2c00c048051380314016010082c50020385068400f0b047c1000c0c0c8800805400c00c80701d120005010001c3e0030135a0b003803454900411072000c43c08001b0342e400f01c0a1601c40d0070f00030603901041244070b041c8074041c244040403448155546030b48082070021900020b071980190341c81c216441d201c104032101c41c9c0c015401c004000c40c50001500075941103440b00d00c9165040d91454840200400025140c01e0410030807960025045400c0d401030180c2256803441c0030f07580c0d49020005000c2500300d03840c49820b540c4020a03103115003030582e401070b000c46103150740215503552400111144480d60000504011004104580e02c40380c441524504581c50030440708019122103028000050902c240000310540d50880c50 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 450093750 1250 450092500 450092507
    0x108011b030b0d1403040914100b070309090b04090602071109071d370513060b0d0f020c0a030903060b01050306060f0d0f1a0f01080603030a0804171306090503150601 73
    0x6900c02c444d811340703040580b6000f10000742d0359050100452400d51009020001c0b400c094080002e0465150192070700340b0541c1c02800700c005601c519600555200f8205001b80c075190817030310005034451404c5503524902e1801518005500403440c0c041c0e11080000b85615000c0d40303946d043ca5140c2151010010303603400401080b10408000210300014103152121204c9411007501800c40060300405072407801e110902020740c510b944038001540c14101d040001404420844d030480f04540d40210766102100807007000303442910100182031203414040f5007410783c00303d0010240c0344504820b205950b03000004481d140029500c140e4041001c005243c035040032940141a003000100021800200343d24542c421205042803c45d242640c50612010343c1ca00000000400380003400d007224141080f6022a03668000c0c3ca4030102400f034103002040501c103004903090702a40b00f0801c2070382c1d140f0904205122800b1075200743c074081143c1e09008a02c2e8a80840d03030805180c6000a8046e040e030f03a0030f0045 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 450095000 1250 450093750 450093773
    0x50d0f02040216030c0b0a150320030d0e120f191a040605091005090c131103270c0105090d031b08031504090203100c1101050108011b030b0d 62
    0x40740d010b41d0030025600203a0002000700c2006000c1e4a440b030410107241408100e0003001410a0100c62500321101081e80c180f40740441034035085152a4013084032004000c500192003d2440c0d41446003c3c800d17075110750b00c011141c020400640d000c8142c0c1990307081c500d80d02c028018507014036030000303580b54001d40e0921001c1140180074030b090311500c880088a520744000251415103010b610790301046100d82003009141c2c25400b15500800903442d00c210f4076034451203040105ca04c83d82c0d54500c01c000801058124100d555038038400701e90f4a080c01c00d46911844a4645254580e040e2403000365030345140403136460018078042e12128500020700c410810b5401900f54100d00b848034202c1885ca41c0e60482207160443c5201d401507a950341801c00c40c2007041e11600010b188105d0804006200585000c0350303400f6070442943c40803824201541c400c0c0d9003151496120034540d1328090000031034134015040b5060052068070102d8510800c0300085041e070320050701564020318060030000002d04242540c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 450096250 1250 450095000 450095003
    0xc15091002040e06010f0c0506010b0307020f07081506060a0509060d060b070f17040605040b09030705031501050108061503060112020f180a0504020a090e060103091403031906050d0f 80
    0x1610a04003608191a04a0700035810000081d04a5000c109a5503040ba004000b083e0103814171405c9403a05544480e900c65050240810103a404004145140d008100c41610300381f201c400d980123030b0b4460f24810b0b52040003140c103540c3d0100a2010034002d050000031a40c01440d5a5074492801030110705000b00340c0e20601c408003101e03694860006d0704123020b00240c412144202c914124050584c1008502e001d100060810400410007003001043c1c0c00c001290111900c200101d6160019080041d080c040243d012030303017500513820381c0c0c0890b58400c01d5060580d0002d07203801102c0d495207420b00210127001900718200b044108041003ca6014a00040c2001c0c060b0300c02624200c0c000d80f01d64642c2d00301107001d5078803600c0b84118010620780340b20b08902500d803d4504608188200d14020314000305881108100400700000c21f0140e4865040b81d00300079084845142c04103811203405549500484001c01c0d880b00840d204681c1104c0c9024044c11540018007500250485442e43c40850450100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 450097500 1250 450096250 450096253
    0xc070305031c05090a06150b0d09150b010f2601060906080f04150e0c12070302030609060603070621020a0906021c0f12060e01032402032206021e030901110c1509 71
    0xa045c5123402c0c0140100b0034020000b00d00d005561034244148031515621f080118100304100364680d91220703a040200380c0514151281e034404031800f03528080301c0c0031000c0e824002000049481500101c00d001101c00d40d90307400503d69031300303d805e01400c94113440c000c0200000b0340d0507500b00701d201d421020409140d038007030303d0030803030301000081441c039a180000415421403d410800e500e0180000d039486040d82016000d6482c00400007912400a40140000d1044000001d29a5039112519580803142c0081c01c42d51103208140c050000d05043c4903c00051140c81d8125082690450b0700d1000c82c03d103600c0700020b80d2910031003a101c581042c021200c02c60703500d007400a161500d14181034000d45c01542c414005101000321040e2091450201048260041052100c0415030303a0200c0707201c0340c0d1070070300e60002c0045192940c00f9106170969143e04102d060141181c1c0c80c00d0000850040740b4202c002c0101071000012a0b01a00a25071910043c0d005114030800521811040641c451140720 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 450098750 1250 450097500 450097541
    0x5071107080d2601060207170a08030a09081e030402100f080f0a020f0409050109060e01081b040f091211210f07020904050303040204060b0301030221030c070305031c05090a06 77
    0x41ca19812000309030305c03804c01644581010400c04030501e42e21104034040d000070b061003490a450741601c0703220140c002250b1a070789240900c01d000860043d200342d2106141c401c17050420517940c9450580094030140e03c50200501081030080c015061000c0b10802505c8802441d6601b80010100280c010302d803804a0b40c08024400305a4410703402040900b250300380009080d4103040a00d005c5822031b0300a24550b01c101c0005024907000004e940c140d00c480c181d02c0c181e06182600c0490042d2000307080f450001400d081d8200c0130024420354a0740c4038096036990481128040c0034407580c1c1c0c0f0352403400c900c12061a03110310400080c280010100c074102414018580300007a4081618254111800e980c40c0e04003005010071880c2a0044030000d24100019a0440d41981c00040300c2c0310313490381d40802e03031041c911007114542d4003031007921410072100040c1c4070040d13501e0030403688070341c0402003030880000201200c4280840302d12409000d105d00c4001003001017440e0f0340c1ca400401884058240854020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 450100000 1250 450098750 450098807
    0x507050604140115031b050910120201030b0901030b160513090504141606080a140115120606110105100815040c030507091a030d0e060d0b0904030305071107080d 71
    0xf84000011071052031b0043c0c0c440018a80d581c02c040303098226620404c062000c1c4035080a07506800720076034914503040c8540c80c65510059008004010035283c20603e00302c0000240422049200d124005030b40402915031000f44048495105040201c42c680c851003009102d04040b0742d01482d0700c2445880b02d101552400d00c2c202c1c0c41c1a003208540e00c002c000054042c04056808000980c02c04181c950922180c80b0302c89070b6944c80001400b80e1a0704241c0d02006c240c440c3c2c40303200c15613200300a019017000f030692182c00080a400b40822115103560912001c10020241d6901e00300031074040078058158036025020301042c0340006031040e10f000c50402c00120204106214550040c80340c0071000500f40e20148415108004041d90a4841e070081810303400700c0740d04400c4020004100710780c85580c6484107801c900042240960071604101010108000c141d09036000501950454440d0f01044a0bc505101d42d40d0035540681451500300d8060718107428001c000a500d0b154014402d03000c00c4807036 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 450101250 1250 450100000 450100031
    0x10503180309090907051009080604060513172502030a120c0b07081e04050d0806031504060b0a080303150f0f030a030c02130b0d080d06030b040609021005070506041401 74
    0x4d4964100a0301305c1c582c00c000798a00120748840c0103455080c1401aa40b615480d143c0790300c0c1c01400030384025110000661a0700d07106151159055100503a00ea03862007124446855030010241014001da9210003110049441101800c1080c0d00400520140305c440d660252504042c0000a0038041c1c0d50a028000600d0b50079401d20840055a03028101d1819140c01d000c10b4141c00250051031000c40107100200d6004a10289072440a0400d007116494034804240350200641400240d84e00c20402e1208103d41c0340c1012810400440b903660446441d0b0010315142d02c401e480c80b0034500c1c500c850340901403d1895121001030303c0241040f18015000c3e01080c204080c0040403400a05030300c2e861011880d1900c8a2441507008171010031071440c641d80820703902a0003400103170211001180d4550454055046403000d10f600108404090405142582c00703007514002c12803207001b8052541010794450300c15510000d0b040001441c042c0c48031380300c49500c1074841e201c0d04071554840604080e08000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 450102500 1250 450101250 450101269
    0x30227090a1104021632060603070618060e01030b041817040609050d05010e01061806060f08130f02060c030901080a060b040b0f090d0f030e0d02010503180309 70
    0x6490000c1d01840719603150581e40e4403440410070b4403991051041902c840407440d1414a0160701100c604214110071185101e0107070700e82c0d401400300d50000484c152185001c0f54480c011070054040ba52010b45421060f00c000102d1000410004104641008010320071a480328107408181800110b030320740200441d06645041d0107070389084ac0301035880c4080200b11184600b0741170122441d48c1c103140c10984014005201e0307200e041d1040c3c00d900d40444c24082c0a610518981c1030301402040750981d50140034800c10104003416106a01e030641c0080c0b940d000da01c40784d50780b103a80d40d10550b0703694600e9030001c401c1203400020b850800305103003000c0060f158a4024110106000010754503614980c00043c01da031401400326031071904005003000803030003880c10f031010b4071640c1700c0841d03c4281d2654440621f004c1d00643e16805900e904a0405000703220b100803403003500a070740b803111820b001d0081c00032288000000034002071003000040c604a000d12010b01e2002440026207182002c0ca1000406600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 450103750 1250 450102500 450102511
    0x11030d230705030a0c022403070e18070804030807030504080904020307120c0207140a0524070c0621020a0c1104020915040f12170315120106030b13050304030227 71
    0x702c845c0540310640c80e000682200d035801840107110409003c4014403800e000280c01e0106001e44130b00713448250b0351003d07a136128090350418000d001e86070100000b4505601564140c01147e0a20702040016203e0300810f03200b1604402c01a103410000c406020080d80001c05c1c0e0b00c100a80340b0b420036072151483c040d4040100c2954003d00341c050500c03d100740b141004402d41d500c1202d600c1000c0009444a0b0840c4d01140c5c1401c00c3d0a030074030710b0321801c84070728800c814000380b02030041880881d002e508100001143d101b07035007852202d040311180c0d000c12803150310b0301500441e030611503040c00034a00100e0190a041c000e0005420701403400c2c08030315103440603542c8000c410008541032158450b08001e460050120602c4011181a60745540600c58400150f21840e5940000000c118200c8003400340211a0050080c00e900311201003804c0c000c1120f404100c607d0034207180401c00202c6802a820030840c1c01401641c030b000d2640d0301300024243e02141e10088140b49039118815080c207001143d1282 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 450105000 1250 450103750 450103757
    0xd0305041511161409040f0c06020304090b0a050f090c040b0d0f0c052a010912050c01060e0907060305090118150f020f04120501110f0711030d230705030a 68
    0x140c6000c0030203803c2050711401d980c07510800400c2080b4142400d42c1c1950619020390342c8103242d03284e40c20700c043e410030201c0b0054080a480724001500c80d50000c007c00407502d1607a010894102c0040030040c0040e00340c8241640103130b4581d090503542c03800752007840e001200d030002e040ca030958500540405811400048100650310003002c40100c815000b0410501a580b60840c03500084041d4030310a040d01002d44004000b5003494060151000d41c498a0b0312034000f203010b545503560b00380007445603000c070551010315420700c0300004070b040c40381030301034021000c00c0c028001f69410b200b0210000c0c0802015400107640303820880740074000085c00d8000d43c2c3d0161f80a4402402400781d0b0000355942129503001c0c0901c1000031449208035031003540c05a9254009003148401141060380c00340040812480c00d103580003420340e98250744c0000030484188038098401c0200c518800705078444070f11190000101d00078420441345080e80301b0030162503010268005007081082c0d20307200c1c61904851103000c0403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 450106250 1250 450105000 450105017
    0xc0504140f130c0602010905100608031c020d020f0702041506020705010302090d0f08220e07030f0e061f05010504050904031107080304060923010e0f131a091e060d03050415 76
    0x28000284600d54500c856249e083c03100d14544500190340740700ba040410403100b00b0200300c83c0109000d40440306030f8a00c420701551070b0706014114a105074804202248107a1500034401e100d5070a29201c07400f11a05500035052040c0340100560283d400141700e01c1e4012a040304480000b01403105003c180c5000f0001c0d96140c081150f82101d0910030085543c1d070100d5040d1041000e00e4050300c446d50712002915001c14010552038541d405040340504105075030080d2020003108034a141420f440d541856900b0030b140c15135130001540d991140d4061541c102c0c406400240100740115540111100c0320012240c403d07585d2440c1c2c81c2540c01981200703000910886040020301a41154602c042000031207503a1041c02d031600180c1015440d514160249032401641c1c0400d44d5100030342c1142007280e000510032200e80c05440040f0507c0c4010452181d02945d020918918459118082c0408095020845501d4200c108803a417082c8590480c05c21400300404102d039003040e800202c07110710300c0c2c450703440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 450107500 1250 450106250 450106253
    0x3110d05060c07022e0c0303060e0f060406060314040b0c091e03010f0501051011030d060618120201080a0509030d020706050403021b13020c0111160c0504140f130c06020109 76
    0x71390340c3c1001e0b4221900c594032140081c003004050b000841c0e01740c1403244d100c2009107001c0d005000c20740d20141d510200c04040120000c485903003288a1602140c0422105413070303100035411200d01d109210b40b0511000000380000d0004009645c00082c0554002e041c9000b41c40010395050071155061a4480c156841c44502d00f424002c0c403619503801c4c0c0c0203201c150b06090100c0c0050b2211503202e0b04100a01c005604181c8082c030403100c100c80315040c24000180c403108050003200b02004009800310790b4a00001d503414900f2281118030303505941d00640c85c0ca40b0850f400142c00041c0180c0c1c01c078041000700c0c0700d04062510090001d28813815001c00d962404d410080c0c00c00c010806468032100a0042035242c81c0c0c0c8056810300362aa0b0a40016214030210100750f00410061001440c6008002a84070310884a21030b00d90a40d0700c42c21052038072503120014402a10401d054021450701e41d40c010405452003140d41d19802002c0c50803081c50312660b80c4030140b502d0040e42c0102c000d40d546480c07000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 450108750 1250 450107500 450107509
    0x20a05120d03180809040906060e0c0a18060516050f0106061e0306080c12120721090302031f02130b180616062d020910030b030703110d05060c0702 65
    0x1418100f448500c00c003072000316210700400d4801e02c4d2025124503a40e04034181002860381c4502c0140c180c40d1540c051074500312120710354584c0303c2c40040b0b02040700c0740039540b28840c0544c90b840070389007942e403080e0601d010000300070f1010307403519400c80d214061140002c0000d4024442c4078024119036640d204039081c0d40c40c088000490400583c0b0030541001028800d0711130002d00141180400e40c1c1c0440444820990f00d800e094034450354a56194001402d20103000d40045880b90000d884070740c40074070040034035041d281c0801a110083d01600920310000100b841092072090941b19418054174100b203542c01d11124a40e203802040070b4031408110211349004003600b500c1014000d5030100e251003041b002e45241081007641c01440e8945401000080c00141e442c3c2c0c050700e900c0a01c0b0780c00803c2c02c036401c85020390448120f4600481e03440003120300c001c0c4603001d003689203000580a8040241152502da07200c507085d00c2c1040c0c12100424135200003c0701005110310071a0640c000a4a0300c81c0c510411 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 450110000 1250 450108750 450108761
    0xf0705161814011e030b011715011202010305040c0b0307091502030a050409020c15040606080c09060918160b0301050a050904230c060d0c080c25020a05120d03 70
    0x49403a80c41e140c40c20b40764000303104a09041d1420901c0002ca941c4c441c0f245484564026000281109101000050b000034040400710700c01c1419820340e13a0f004052500249814024400d001aa80315542503001550080e44a240c115000e9848152500e448404425541e0300550708440007841003a010004d4000c500d01c10124088240b010b54644880004014224007403030095071111540012175000c3e0001c01c100000008981030390801d06880c09042410080110b846051406d004807680c241d250b2034102d00d078a00c1103100405000c11074651481020864040e4403045040d031040d044405102050706662000519000c4011658ad42c10041441a1040d441d403003523006030100b00600c00050f0500003010710743e00d2010200e1880d0f101c0121440c0c604516000007503080100001c1d401103101040c1c005180307800e181d03140c1c074070640c42d800b041b110b007880b41d08444c404086070310007100500c1c01a84403810b46540000e14014080303484e1030004609001c54695000203501803072003d46160303014001e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 450111250 1250 450110000 450110039
    0x7020d0306080c122509050601020309150d0e0618100c02030f0a090e010e421302030906010509010605090102060c0702010c0506040c0512010513080f070516 69
    0x3071215520b000c2c50965500c0412000d14810603103d510200d02c4081000b0303881d10504101900e40804006840c40d201c1c900b958010181d00c1400d180000f60305500010403100320740c10240000e51030109186d4411a66044003240c52032690300d8100301d4107202d03000c000ca5030007140c194a80d4451075008044c0d41e454038100341a4104c0c2c560418900151443d008001d8510380014011029502c3c1c000000841c0c81004d903422569000000000100b0f0341c3c490111914880d9941469021403100443c494170f0307080000840c1c400320302c20b00d00c55100115140300740304411104060440c10f10f040b06031200c0e6050346c1003101c241c4026844240104054036294078110b00400160a18900d00412540000d480c2c40b401407000e0040c410001c0e07100d045910806195400a0300101590018102344c501442c070740789140300701d903c07843e50b465458150340e0061080314000d189982c8101d5440005558400c1ca50b0440860031003145414030aa40103e4002e001c01d0209565441c00c180105090419181d400b00d0900312 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 450112500 1250 450111250 450111257
    0x4020607110d141516051e0a030f0e061003061d0f0a0201170103080d02031305030a02100b010e130506010c0203030c0105060a15080718050303130905161e030f0c0807020d 75
    0xa104407111900d8402d6460281131030540d035a43ea03a10700518540100140b07c0c86050300020b540d0300c0300c81d450b40c002c5044008210741846040740c004a683da407800c041d07400416100c0a01d500300300140e41c0e580034a11a07582003141403006d1842c41101070a25030401b0700801140c1200048a00b10b69000100d140c1d000060204c103482541145c45007555805403403c0101841e40c004081225190010b503130f1070a41e0780c80012070b5520625168001d40300c2e030401103d840d43c64181031341c094031507000d24180024100054502d203888200039134404050f00014207a6070500481e650f842025880601c0102140c041030070000c503c9081c0081488190b4101d42e11212400c00d013565141d20555129140c160010f1103031410300c0c121070312240c00301a0f904195000c03c1d0715100c002151100501d03030fa145001150540b480410a0780d54040001c0b6140c05c1c0c5100e448001490a400e41100310310383c82030701266810038070300003404690320080c1904840000f80c485002c109090300304420341e0341c1042803181c841100e14 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 450113750 1250 450112500 450112543
    0x5060606031e071b081206031b010503040f230c010302030f01050103200d060504050c0a08191107060501050906030c030606060a03020d150f12020904020607110d14 72
    0x1052846001d0701c0415040c038541d120089000c05119440020303103a482d0041a061380d0525140c0303440355921582180318520303001320001d031440c40d0100d40c088200034404e24080c500780c1c05400444003980001c1089a0081c000010f0317001040045142c0340100c03800d030103414110300785c03101c00924010100d24a01d0415004204000d00b04200d500081e0444a00b030034003150414820f207400d03984002c141c01a200001b004114201405200d411000c2118000e96042203281c071851440d840500c2000b00300e002140c516800700340c0314005c64506070b520b91300c03041d4005408a10704061303c0003a0b016050503900c66856800510203850140c20070340d00094120014900000b403e00030a4661100500c1a4810003000c28500306103402a012036040a0288030200070401c0310179850000c4140d075016407410810502c1c1e010130b80012208003c2016030f002050070480d591035500700110355100540443d985a0300900a0703810392512044181414801e1041c80794040000742031924117000d00803220b14034035004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 450115000 1250 450113750 450113761
    0x130b131e03020f04140c040f0608040804031b0b0c01020405040b0609090a0b1c050a030809060702030910030e0a03031409070b22081207020a170c2101060e040506060603 74
    0x8420103007200d90544140d104064010006002445200c500460005c14101088000c0c225040104256103e51400b600f44903164681100e41d0300302154010813214080000388040384030781809031801c0c1081d40c803441090741c8603048142c00760002c1064551680d00850280b12a25060041204240007a90260704007141800054031036000542007003406595020300c4019501d807141c10404100c00e075008268000f0403407900c65903404802c03809900089141000c9042d41202013115402070f078440c1c1c0114206a00c240820414403800c0382e141d000d05554a81091f079072181441410300c0a4000d4400240034003000ca416410017100a2200a850300004030a21510078484c05841c458a6054014204070307042c104902601d0b017a40c3c10440440c8510b081c80b1808000d00002001050300c00d42d0b1a207a040e54421112411118110015101d40c0041c10950750a08085540c4441c0b80b16041c0e2200d8a500746411003800c5502580142041d21925010041070110421080b600008203460b46480d41c07911 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 450116250 1250 450115000 450115049
    0x9040f0201030c02070906030c080f0c100f0903141005180312100306050408220501081612020a110106120206070f14121903050106020601120602130b13 67
    0x4144000703061540d59003c10fa880c43c8200f004101410152500f0451951641004548154288102400e82c0b0454201c201030400206103002d0184014110421b800c00031a405d41c0c444801c801e0410401940647c00070105140341c00d8148261000c2000d0030031024081d9103c03081d80d60080501280358042548600d18850010440c0c0c501b100b49190403c042d100c8400107003180e0364990003d000c0d5030400c424082404207800c020000028103c003007140045445114481e5510507100b0103000ca081440002c04101c136907081210381c05100d01e0084002c0c0044007200040b600600b5801000407810000c103012150244a0200a441000c011507206032040d40041c0c882e2080210003044280bc0d194200200202d0300c1e58910051403001c1520041c0644050005042d0800084402c01445446018868034000e11441c3e0683d6903550140200303a003001d200e1510790411715000c43c0c41d80da003045840500084078418402800f040b14645a0341caa0300d4100c1080c250207034000e000500030b586001080f9542 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 450117500 1250 450116250 450116273
    0x12050f090c0906031e1e0708070e01050a03060c200c0f01090305100c050c100212060f101103090a0b030a0c0f05090118091406120d080c250605150904 66
    0xa9050345d01541d21018a0305c5410300d0703000303a1b00000a070105500040110000700780d90085d1a407900c110341e1516514828015640c2080c483c0350380001c0403100038408516581c00c01060700c250fa040296a1241d0744440880440400003010f0441d0040b2011080a1400c58400c40e0aa582480c0c00800c0c14115120300780c17101450804205016500c0d03415450403405070041e02c40600400054900021990341024040d5101f0380504241644803c00681d15150444544410030009001505110107003502076480d0040d802d24441103100c00d01115840340d5911000c02e001d0310001c5006612414510300c504155200c61940f401800100d80080c4120755009003582d40d03080e001d181c90403100ac04a0514000b45000303400c414062810080f00c440200400700100c0d018910035141441007480070040305442d11f4581907d43c00113039464000c107248004c80340c05060840025000091007040c03100e80c082ca030102080c8215104d5488100304600c0b840344030f080c85070103003090310554040d10305030b50f07101c0031280c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 450118750 1250 450117500 450117523
    0x80928050607052d03030f07020709060e1317070c03050609010b1503040309091803090f0602190503040e04050f0705030109030f0c0311100f06080a111012050f090c090603 75
    0x110b4030584c1d030700c1480740c1901340811250000141c0c0d40d80d082010091040010441e9002d015100380c0c00b0020342e903412440b441c81214807001e2440c05c151160802c1a081e00e01d01c240c161441224030060b045102405001000d8185c416406032400620750300d480380c11f00c0c031300034241c41c0c4507450a1030301411500c1d14409035100c3c0d01c880015966035911071809076004906a00702c4404503250240445c1c608424aa0f144d02c0107000c0d8031000103959441108441d000340034015a00181c100303000d581031042c9110000400584110283c90506480e40045450420212001d440582c49400c14a01c924070901013040030f04001c0d0000e0010008544014040c0080b0143c03810810502c041c100301410b11400102031000505419211102c0303101203003c01416001c50001d840c10314001c00002e4603034002980d00891603229401e146400003581c03c0200303000c6129200414402070810400080c01c40384074441c4900000c0005c4111800c2007885103140840005202d07028070b030b01000303002c1281c0d0700144980c2501c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 450120000 1250 450118750 450118783
    0x801021b0c0d1e0f05010c03230103050c011b06090303061a03060f09040609120807180e0a09140303040f140a032c1906030507091203050708092805060705 68
    0x14501d240c450040e81200310080c041b540392107000202650705030411080c41c2c0c0740121000391a101c000c9441240034081c400144070b076018085129565001e00e021088506030b44454140f13204158803040c0a44d580c483c0d04900190b5200740910180c80900b400b50000946001343c6400c0d881c14030b000c58113001440503007500c1001c059001804214107500245046070303200c52892401c44052801400c1e8880c182c0f02d4402042c0d025000d20240000d0100e80c008403019a54002c08645440b0900b40040c2040c101c207440d080440d407901080b40404000940c0074502c151800542d228481c1081080c858001040c0844d981042022201082c2c0c4640d1080907980f16560b0007110546090100402840403070307440350045003400c1c0d112441100104200c08445540e1420b0000c0d80c0c81e070300116496500d900515480881083c60350000c40d00c60300143c022184152703c114540b0f0f00600c0021034011624000d9010f1800c000303d030000c11009800640010407003901e4050600c100f5950301034481c50010f00e0001e40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 450121250 1250 450120000 450120053
    0x316030309180216060b010e0f150a050c1603020a091103071815050706060608040807060e072105010e0105130213230a0501060f090e0603070801021b0c0d 68
    0xc11640d044583e40d5920104c2c203c1c0c081050714241c000b50140348036403400308900e481c25a0050074400b058044841e0020006203800040b01000507140e00507410002c100a414003060307003c00c80030031141407000141a4035014092035841001404043c80c0c200d007110300d0500b94500790003000a4284ca030400030790b060207080310f4140e2a00c0c100940ca1580b00c914420b04e40c1424003010b5402100600c2010b01407103080c02500c0d201c200980d041041550010700c0240c04114440100354954003035408001610242c4120b5640d83da450701c14101c9099540c50900b0f01d1071401c004200702440380d14614a1684002d108601e000345a0400445110070003074000d6040390018030085845500c041800f41c1041d441c00340003501c01002d152100c0d400c0b00d603240f20300d14040010403400e020381400901c0340840d54a007881d0034284030340022401c0300036150340d405100b88071020400d504280003400700c0000090f1a034028050300341120f8500407598100c907004290010808010a00402000b4042056440304828 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 450122500 1250 450121250 450121289
    0xe15030f06010b0706110306060301030314130b12370b060f0301080d0c020303030a09030e1f03060b0f0d050702070b0301082407020c0910050303040b090316030309 72
    0x425203803203003440c218010500007048210300c19001d40780a0b40508010010098100086e020501c0195441581b05074280010000a442090a09006280d6207003480c20540b0000c0030650b1218a50440303030150201180c100c090541d18040c031680402901200c3c20950518185a00310242c410b8284c0d8442d01c1180c3c4d4440100ca003500311045000000e02803d079990503028000340710380c100f0b004451941c00ba4202e00e00001d8402e4007280d981d15001000395180d5124144800000c080c000c01c2203041c00344032890369645640f10f442102074a00e0389003143c085040c4600005040300d00d95040354080382c0e420301030844056201070559402110199001070b054459100070391400402d41e0015051050000c00460f2880d00403682203090030780454000b04d0400b202c10035100010044039468016408140400d90610381041015001a422000304616035102c030046400c552060708645c80c0350fa800075109001d82002c00a443c68894200c1030505294150f0f81d00800c031080b544034074410110640f8003150b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 450123750 1250 450122500 450122503
    0x3060a03080301090c0e090c160f150506090709080618010e0307120201110a0512040201210b030d080403021f15030b0a060e010837031809060e1503 65
    0x4003a5400000c0c0a45941c0c1d10181500503000003102c240010380940050501420100d010a000c1c0654001e440e040c550424032046220032444810f54420006442c2c0c2008114101c0e1643e40c1c41840f5640070a551030300406008441c44042e10580800c03418030000c2011000100c0d0147c0c002003007501400d03100c801480214090301c550f64251307006010000d06442044041c5110b02d43e6407103107070000c2c0004071001301e07959001e00619400c140401c008201e00b020791a4001c0140d03030f0141c414100541216488a04090041d132030001c240e05140e42c42c00c0241036072034108074220b40c041c400d01d000301480c0f5003994003c7d101c150b1144244000c46540d51101140360468015814035000c1c6ca00c0000b149a6900700820a90f030291000d0b10081d15140010030011b102d011218141e4604d000200600e61070060510509046003c41c1c8611350000101c50300c8881003503501d500254040ea548914203495400344080080c41540600c0e01c03070303290550030030403483d1700c070900c2d58407405413516104101085408030307 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 450125000 1250 450123750 450123769
    0x3020706140709150504050a05040b180a0603200f0108040302150420090115121503080c0f0f100507020a0c030311211e1207030f1a0108010b0306 64
    0x900c261909003042250700c50b485070000b0100d461040c014062180c0614064400344607a001f110b8009408170018032642c00d154108206550000e40781c4003404c0850b1169020640041d10204c1c07115854030001c005001803604100384450031000301c5032008202070700007001c0d0010180d000781484a040c0001b42818024480800c4a092503202a1891b241c2450300f03000c250442d1598807841028800384120038100021464140c03034031684c2c0240500036150081c2ca0034801c00c00d54018060304c4e00c1410700b04030364500d040c1000f50b201d100036a488000300100181426064408920694014840c00d4005400055410010039040c200000d2941703136817400700e04040d6105006084000440030000c1090b80c401c1341d004010b14060240d035001c1c9800d0049602c040d0098811340c1c3d6028062002800034600f2052134030b45940300d80e0b11146400740314499030320500411103140003ca607031190b0889240394140104003d070081c00c4005441000d1a80c0080e20ba00818026000880380100004da000c0e03e584110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 450126250 1250 450125000 450125021
    0x14162109050303042d06051009060b131a030c09120d0c050d051201090513050a1109130209040f0611040801060f080607020d030e0a0206180a0503031903020706 70
    0xd2040c403005081c0169a40d000ba6000c5955841d810942031400051592495103c00c4080d044200e0b41055180c00010341000b803c8001a008400700010b9040714500c0360310003c01301c100907180c45442c04a01409805800d070312100c01034060000000c40403050808480c1d2202c28014130644401000c00800c4071403100103a12101846200c4080c0340541e000b14594a000f0b2181c8100c4032103444440f0110390701d010341400501174500d050010f004102094108a6002080e24100ca801688589801d8501401890150366a801c80807070314085041c504402680403008038500d8103000082d0b4085101807600500c00b5020b1034035884c07460208041c175009001c0546400c1401600d036070301c410040e07000307048522a5800c401c078140c000045034130002c070ba0703980700d078000b078004c0e100075540040258003810140c50038001c180904159840140d84407405040303850308003907803200940d40060510580c8801c98020358442d03401070060388034101c183d6104040342c025500e000341c0c6503a403d1816101500d0790814 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 450127500 1250 450126250 450126317
    0xe04061802040c030f0b040b060a080a0905121b0c011407020312040b040e0a090c03030f05040506211b0a0c0f05010903020105270c3001020307031416 66
    0x14010f65603985500400c4903003103101e80801801d0860801c0004407034508258680000e024000c4482c03c0d40038041c0207500039000381020450a070039640d290b080940341d8169802c0030701d002c03c00c80200c881c0e80a60344240b440ca04018580800b200300040c3c0646042191210105000100300c02151024842441010503181e01141c580d41c071940008000d030028010007420720342540015000804c0c5001e821622500400e250314050700b19242181d82000c030001120501404000014180c3c440d00003c0146c520398440024917110000c48a075520f001c0075018800c1200d220a00000f004800c00840d003041c0300c503080290080c07000b894000a8420f0115002e0219484d021a480a054041d00041e00c542c020b5040704085000707883c03901a00403089804208540c1c800005c02d1101e0501241a00c0d02c000800c012908882d00c030040140c8250b41c2854003a40c4c0d9401101380a501c541500a01c205000c42c41c41081d018942000511113806250030420200400038000c0f8131801e035a5161024440f85110 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 450128750 1250 450127500 450127511
    0x506160809094803041e0b070f05030912090109170102040f0e04051b0609040e0a1b0e15040902060a05030714031e0603031b0a0203160e0406180204 65
    0xa40f0705890418030b1440d54051040240315062460500c014406511003184182d080300451144880894000510440d0611101e03200c8034000c0030380d824900c0c040b6120b43c05407416403a01507001040e000484d01c234101840300600921418602c046000c1c19400e40200d155511200d054004071070028841c0d214150000c03905140388030340d007010b40080c41070b12100d00006170119501d4040600a11081741c015105401c0810040c2c140c22402c001000c1c2524000c3c20b030341c10b0400b94000102103540030560062603500984a410030044c411000080704044040120101c5250900002a10100a01001d000c058091030318800d036450341c0c0f0240c50b042c0c000c0d09440d02c54a8024010700325500986100300030405400c10b02000d182c0180c1164440e00d5003440c81408181c0c00030b0440b206140241845605020920100d48001c07507180718200d0b03100203c40246000c49080c014181000c452000e00d42c1c3c000300894081c400040c1600754241c01590207440041c8401e420034840d241480c0748600254403c1c00c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 450130000 1250 450128750 450128761
    0x3060f1909090c0506040605220509150901050301020a0c0f1b0b0a080a1503021c02030102031003060f0203070c030818060c0702040c08330303070f0c080601050616080909 75
    0x990040889600c188060460b0f070b511002000380d14061482200d00003801041440161001403c04035141c42c0300c00c20208a0f55241c600051040e503044070114042000c0001d11001c1b45040b5011030b0060500364001c51a08401010042018a9004002d4110030030b501840080045415040c2201d81990001005241e286c0d0221600c5038460420340300003c3b440c07008a090b03c4160301c510310426001c401d40c681c001d4615030074000400c00900700401041c10a11044d000350301c0070f00046104408100f05249101c0c00c610f051011140e000c40780000c03e48c41401003101203604146621399070f9402d41005481ca5907402401012020381403603a15240c020700090000382d00c084005440b000d0710803201840855103166003211a100c046031602508015103a01c0a04040c0158602c2ca90095803241040b184001d000420300d180d000c440103e03080c5841051403410310409103110ba000e4010507001c0d08549d450040009c040e0b014161088900c00e0001101004200364107045458a0dc00a4550035007407510 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 450131250 1250 450130000 450130019
    0x9030703050a05250b0d0e010216030504080d050705060a11130321030509060c030c04031e06050f090c010f030e06070908010c020313121103120d0c031103060f19 71
    0x8107500022015405420402c4264030345108205075103034011098240b0a0392040180940100558031f861554200040b2403400641034510410701d000340c40eaa0303039440c40c105050346808004c0d00140c04110090011781c0014401182554122845000c0880d140b40c1c0e0107403138032161252007100c16030740ea1404000420400d032004e4185c8881034019610184002c40e0500341e05903441181d4001041d0007c40002c1d5035200742c031002d143c000002070f84443c1030940705d5031984c410404c0241900340494030303034522804200c030902138160702c08501860055142003c0d9510340d40c5003500c04081d818040d21000018005200340e1105440c03220680c00c940d11414081d5003c2c0207148107000f580303495402c01c10f548031034a0002086a14030007040b051010031621b07100303c482c241a280b0070700b1038003038600d03400b1190559010400c0701040c0d9404800f0559071300c40003070100c0c1218843c0d4500302c189810301d40d60314004030b9400c054a91041040d201c4044881a840c0001c0000c040718400c0400c00350510360200c0c0f50720f83d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 450132500 1250 450131250 450131263
    0x50a0317071e050f0c0c0405061009090c120f0c020c060c070e0405030c01060803040602070f060e060304150e010903020714060304080d0612081c06180209030703050a05 74
    0x29112481044404021504a460115541c20100d5030b4807100e0860100804014030b1082c0c007a14069041c881e2000d0540015840a90f40c081d059024504020407880d207485060f03040f803421030f42c819425400300006803444d4840d1041c8040c1654440c0c2031031131a8044d0701e0040306070102e00010040d0210b054107040042061f810010300602c1034400c000003a0811070300310340c503e940510042443d245448a07030a019880100100c40d40c3c002800410003140b0b00b401458050700e1404090740c1c030780c0e0070000024905334091b031040c8002c0002640401c01142c01503001400e0160035182c0700d5a0b96550b0a0080300e8404202e207214509e840c08040461404042d80b04e01480e41c401e0b4213139102145d40c1d05c00d040d8000112403c0d83d80c0200200041000148100e004291003100d45c0400f1501a985d130100380e840005610b0281c8405600045002c00880382c3c100611740c4600384001084640d0600718504040c0f244200c40082003940098158055502008488002e65125084401c1040e691030407980b01c01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 450133750 1250 450132500 450132503
    0x90708071502060703110f0d0e0604030c140a0308060904060e0d022107120c030c05060f0612030a0e0105210c0712020307050a12210c020727090606050607050a 70
    0x200f501103101035101e80210394094000030041d03410007082e44c414040f81d0740140180d403c015954000c01c1d41025045c48a288500c1c002d844541d04200c00d4201500000543c01540c2c046070401c080c403100282d000355a5682005007900c458020313580b5807900100400071140100780130300c201e0b0100700080303500084142c1c140801c040c0c403a2000140d541c0217061070181e034000500c000700c40044d06607410703c214958280c180c041d01e042c074401d000c1a211941001400e643e20380410340c5280420183d400c010170000e11610000c0015494205010780040c45c4001302c0110b14100040014030241caa848250010344d030007008601203440f42404001c0c0341d0035501188048404071aa0306a103c02c1600200580c1c03407498208010308404110340d5244c807030100b060754a800a2141910001a51203031491801c06603220324180020161604a0080c0c0741c0a0a580002d1411072456100c1410140405182d8094410048042812299882c024018204580255400440104544040c0700f8005000b50b07065 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 450135000 1250 450133750 450133753
    0x2f0d0b06010f050703090b07020616060605010212094905010b15030109020f0d020408060405060a0b010f1d030303041a01060527030111030a06060914010801060503090708071502 78
    0xc82e900c0c02c142e490303024550340500454003008040100c464584010410284014189444c0110b0558100c2d10f21511410a0f1002941c84a042c080d55804005036a55612b0200340c40e410003114078002524010a80a03003400903445103808814203007624580003035000b101c1c8218100c4e201e010403d01020314043c400b40d0b140e41c00e0201e4a03543d82882c0000d06103010316030354400e02c4e50b03003825200c001941c40340e2a02e45940c01d00f0031000140701800d1002d40050044000030301003509041c24224500385000d040480c58914045c0d22004d039a81245110540500714245103c03510350180f031000070091b0001c1c0c40ca0300342c0400000c1101300034901102e9074007161070201d00840c0340d0b02c0d410112024010159040a5280040c2c55203681c4c407460b4404070810340000300003043c0040d00c00480c21068009984003160300da142c0b241801184d401c00d1107000601038000c01190b00004200009000c82c50600c00e0905000000005c01d02c0c02d04144496000741281d44110f41c040f070b590b8110513440c4000401004d006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 450136250 1250 450135000 450135017
    0x30b180f030c0a05101a01110c030703060606080619060f090e010609060f02030a0507020d08071b180e03070609020a1a0d1103040c15020a1403030717042f0d0b0601 72
    0x44403281c806c0180111500c100340545400480c0152002161080f0000ca14401c096018a450380d003000403401440c440c1401080f030f14901000a002c03403001500b414495902d100d80d06010054509a1404488140c0307070850300c160a812040c0c0d40209282c2181c1c4038407064400100d4203d401c000c5850465140d561250250b1011450480c0c9a014030135400d000940200010030143c900f40c003900c21544d008a010f6450f00002d5651820f800c800a554030400c41140c03c000c0126846015501010441d0240140b210b0508004515113a00c41c403000181040e55a048600135901ea61446030042d100d030b0019201e40083c1d40b200400a50403d40c11a0340c058206541202c0c1450004150303805541d11030101a20182849000103400d2800701c0e08604522581c85044081100342c038403280300c4e064410103140c3e2801c24810042c00039000d45050407003041c40000f40000503d44441540d1004e4900440b45039404120300241110104451501e9021400315100e00600904000301070050078240caa904d0f0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 450137500 1250 450136250 450136273
    0x50c0912070618080d050d0e060a0e07080a02060301030f17220f060503161107060918060317030c040302061918121506031a04110604030b180f030c0a05 67
    0x41d01101e0013880343c2078008501404070f0600070700c05031411818140000c5070061007031040038075042d07049444811017500c51881b020044000d00c8440c016280110240c040b0426580100b40d4610040c40001e2290700354005010030301c16400c51340306450582c40785495070b81c82d0504500411005244009480c0150070200003120801d541c4c0071030455042e81c0364103003180c0d919094802005200d52051040c0801d112101c00780c40c8042c080040600b4081c0c0b03441604c02c0c1040c24030981d03051462410410b15141203c24408140118240b07000805403220480c0d403035484d400142d00c0c03405580d10094010b00c000c6060782940c1011544080d40310309940e40c0002d0141c0c80c44514012440341d109803c102905201414041034600340000c090000300480400d0046e940d550740300c80b19a11400044001090304144410011601d800900c40d20b821a90036003030a0440d2120014000040d0441e0403450214510910f4041c05000201920180b801900d403501503d451554455425020890745400740e281d800380c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 450138750 1250 450137500 450137537
    0xb01090612021503041103010c020d02120a0206130c0801110309010f112706040906030507061d01030c180305011506210902010203130602010f05150112050c09120706 73
    0x501064006004001d04030f20b00b80c26089941c8090800e40e14100c83c13205a244548003400340360101402079004004803034640d1002802c2c801590381c5410036420130000440030f15400541207800405d1700030721002010080c0703880200303112554800c0869500f4102c0002c1d407040d14030003561103401458024000a120074002c081250210254030b10748210500c54041d04555004075070088800e805454840c604007540050103035081036201910b01600c41000b8001c101e000d00009009044074107095114401c0001085402900d02c44501d0425941e100c00140a40c4240e8001082e07241e203802c010005601c078103046001e81803450b6051041e02c1d00030310004650740300705d8561034015510030044183c460340d12600d5021340304098059045201c240203500310f050f04092070900800f80c603000002e04490302e442580a440009004281c0c90b183c1000100083e604401084400c1e404610000390326542c1c0054901d160143d042c15982200500c0001c00214400084034026100b40c1e48841044a03130109596 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 450140000 1250 450138750 450138779
    0x909140a0506010603110705011803020106050a080a060f0b0618041b120e0133050108070c110102070812030a060f05130b130c020c1503241207030b010906 68
    0x401c26030000c401040320038425440b2003108030783d45050305c0c40d020140d141c403401d690f4408051803070048004155410560240705101c01000140c841051041c5801595500c0d5409410042c002503203c56146240d283c869010400b0010024219a16a010301341c0b0301822100380012076001e01c0c5010304640000d012000104e10b045069510794000001658402005c0c0c8410340c0b04101c599220141c500101151a010a2240f00940620800031094502141090740c460b44400e042c040c442040c80704240e8480044c1500f503030004840713860500c80000403031901c495035018810501604100365401d824210041d401606d030040d0070301130142c40e42c280e00144034042c4109a0700044109402c09410000d0308046860b0400420300c9403456a41c00300380084c0c440700c14018006801860101c14607181905800c0c01039040c01403528154030700190380c1452054100b2001c0100f455495151180707030b0f611080d0700500c1c6100e2081c0d45000390389182c107085105080c021210940d0034040c0101c2c40403c06100c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 450141250 1250 450140000 450140003
    0x2060a142a06010f1215140c19050301031101052d0d0b0906060909150402030f0601021903052d1909120308040305181206150406150e0310060909140a 66
    0x409084400c5c0d588401524048000e420401600e9244a410868480002610651080e8401380e03540021851403590344500e14407031001d114052006001190422001034400442030900640d1140c0307003513050311120080840400c000281d030001565030003034080074040c01182e030072050024094420400004100884691790040c9086c041d44401c0d00d03001c0185038001200c81d12540083c1141c00102e4181c0e4021039203003d03241041803c0c4045541c0c100801080c440400a030180d40d406169001001c511506c0400303602000d5854030700d0400d010180303030511081840c03140e0a540301300403000d50000008a040801c0800c084180008611000c940d003040c4c1d056050f62028140d0307480da50162542d40005104040c0c40001408150064861000962000440e000100f0943c5001c0e50110001711100d059640504c1c1130560400104e2030b038000c2d002071608142400d40d98480c2e010003080c501307803861030b81e00380ea50300b4601c000990812580c4804940d500510700031403603001c0e03905610740c2e0b00c170030160 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 450142500 1250 450141250 450141269
    0xc0f03090418020d030c150c031a0607031227051005010819061a04140108160308040b03131509031404141201230f0603060402060a142a06010f 63
    0x90044c0020302c108854070800d0704c60424140d210000340c19a100300d4280b091402c0100780d9400b0912914400b000c50803403000000c841040ca04146c40c0e030010100035202a00e00003440d00c030241c000c5075140d000c0d280819a52421390356100b50415003015030b40d0b09042542e800d01149050004180301030042600c01e500b01100c4001e052043c020f640c0d4800030804801e25032103c044501500c4101da41e203018810084000e80300c60a455414150040c1c1842941c0710200300d1045030708810400035025030150b600319a41c804c0d41d95126a2100b444220701502d074100200380c4080184103160a01c01540280640c9001c0e64070b0122802d66000130700740700c4c8140e0088a200d284000d403400c81910b84114426543d111100003c0344040800520945000b00030140c0c5011b05208010410f96040310001700368869070407001003101d81895004a02036104a03007444040100d102e441c10b201314113840403240200b18400c3c8010002420f40e410518588284040c20a18000c0d000006910070344110f001041d10620403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 450143750 1250 450142500 450142519
    0x108040210121424030c28091d060a02210432010f02040e0f1b120108300c010f050a0902010f020715030905030c0f0309041802 56
    0x140685421020021102d40c46849003890a24200d0400d0781c9030040e483c0c1599032060703860722a030851442402c080010702075031084000002654424011081e54150380c03c12841c0c00c12003040c4084641507035006200c0311814841522a00300c9181c11408010303c3c5a01a140c041d111141c035502a80315460540700c5245212429040c9461034400e0503400c940710ba000da45203030380c1c1c000f260079020004a01501621003810441140d8040a0242058140c88020214905070070f007040941d01d04406881000041200c40002e55440341810349a000c000394400c0d4141c541c0070040030301d00d00c100c0034065640640a84c480904038001c900111420f0138001000002d05402926044003694004452000721592504590000840341c1e210341809044071107c00700e170003411400050804502c00483c04210740c0101c0c400c00000d2410085449145100c2c41d010480c0f00482c05c009d869401500d400307602c01c1c040e22a9a60b5803050000050078404001d440c1480000002108080e205210701006034201d001c20 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 450145000 1250 450143750 450143779
    0xf02060708041202010b131b080c030c0a021e0606011704020d12180806091e070e0a0209030607030b0f040903090b0d0e0a0f15050c09150d110409060501080402 70
    0x3d001c1021070700c1c00c0b440005034891117800002c99900140030407030801c550300e81010304000e2091085800081440c01c1c14901410104c6460801e4440204090700103007002c658455450f20920450f01446542c1215200c0c00b2035a8002d20b85a10060719220b000ca0380c2d03c40d0413100c4c81c024900b242e11582d00100076800805498880c2c0c0d1400101c8074621040180041502d0703100f10b00000d1440281003500000c0580d882d0441080f807810500440401040281d000c4114200500050220950b108001202e03003986444d03000700041d004854896a040c01844c04003c0300d0b44e85580481d05060048807502400100c19092100301c1e400d007180a03000440100007417200460100040010702280c440c001440640a00661300f02141c42000725002c0d2080740d403c00620810540e141034028462400b00801d00f81880c0e07000d201d03c18407900c1070041d01c030344105661603660001139502003611200180211440104903508030791150007400612443d099010445511500815100782d034042c04100c0c4440d0030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 450146250 1250 450145000 450145013
    0x609080114040206071b0504110c01050930070c0b03060306010f0605090f1309120f08010e040b04030c0605011514130509150a141c080307030c11010606050a0f0206070804 75
    0xd61b1040c10b013100210000044a4540d0721075007100300040100c407501c80d64a810143c0c290303840a0900481a440340d00c80708248004841500b0000c45140c110f0011100c40c80d60001090003081c6028100e4100c0110000f1849101d00086200b03040c2141075031340584c0c8480c151008510180600310004d8003c1c04542c0c52801c2c5000003c105600052100b9420390000b403825050b6800134100701c6040d2041042c414155030420226542c180003030800200d1036042258545024500510140000b11444041021701d4081d0702c03032214907900940103025a40e15111049401515010f031513000071121781d440120941c105041c0c410320300d1002c81e01d80c00c0514140c10000360f850040c210b452541c44050406040769a01e01a50000345880010300c10716a403110200700d100f00e00c01c41000c0c12107840582e00c0300003800440c11698040746908000450f040301e410222141d0f154629281c04a610746400810754541083c05031070762011594902e0881c0324052422a241c0900791540330116001d0004100091079 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 450147500 1250 450146250 450146273
    0x9010b15030105013b0a09020705010209100914060904020c0d0914030105010f050409021201020705011508030c1e21090a08121e120a0501030203070b0702010e210304060908011404020607 82
    0x30010801b289150300c89845038100d0f0303c45102102d07169400110b4a0841c244005591b01d241c515040c850303c11864842d030143c6400450256034800c9400064124065503550f05503002140c83c02c046070601441081c025048245038040c030380b2000da403016549141c0c83c0500585059941910b2041c600d07516010922007d004039240032a4011001900c000c0500e1091001d4690365004400100c0d540602149410341340c075203600300215541040002c82090103000861000744040c040011144c50000100d51f41020840e000e104c0d200710b000c0200e100503a0000c00a0520100219150300486644d46442580d410903034a0782a0001028003e0b000201030f810111001c039809003a0580c40d0044015480200a00c201c881503c3e0903900c600504c1503080401101c0090700752403010b180b60503543d4001900e1501c54960b518858011340311880c00801c186e030f100aa00050170401c598440d921060003405200340c41c000c8110759840c041211401d40c0e840b100860080b500909201d10702050303034a48030440362 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 450148750 1250 450147500 450147617
    0xf061d011a12031e0306090a0e2104150302180d03210609060e1b0f070209060a0312080f16050301030204020d0624030b03030306150309010b1503010501 67
    0xc14462401078095030012056030883e074461480c1d40703180c90780402c40150f03000381a205008c3d01d8803900a9511030300180100b0400103031a1a4501451142003a22883c4643c0d04200c1d00704180b2980244050f402da000b43c40411554040415003110319002c0c8034641100c1d4101400044012490b0f5103420406000d128001d00b078000c010400c507465151210176100c45034401074450288604200100d1018090850140b0544500d54a040944007020104d40190900648102041c0700031030000e5450500701c80003164002c0c0200c4280f007510070301404602c804c03104c0302c0703c1c041484005641075820758480c0308403040070744a00b4150703400c5d80c081c40001e40050b00365040044e640c1c40c012500001c00070f0341d4824080140c803a90249082850010191060b2018081c06070340184140400b0f9034800c101d2402c04540302010580340e554500c24035014005081e038664002158a4000303105010f01002035040c2c80003078895000c8090445919020781000c1503009464070001060b8407901d404000c1a5017000307 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 450150000 1250 450148750 450148753
    0xc060c070809031501031202010e030a0e040605100e1f0815180f070909021201060302070c1e030c050102060712230a14070801061b0602070f061d011a12 67
    0x8030042c01084c0f42c190407811044040c981940100104810030480303202086941c0300a1144e00d2135102e03410781d80d014116030340c414402c0b007540e0441a41c480358000b0004040007003001402111030840075110289604441c0c0c0602c207154204000748200c05502102d003145941ca4500503a107004411150390146903041d40e00036071f56a4075031a200040b90065011341d500c03c160040c60b00301494040e141e00ca140c0c0c070400344240103103d14a0100d60340242da81c112031050801503074541c80303880c12302001580e81d04505000d40020f0044940100c500c0707140030980307205001c6a41c1d42e945038001a40d484800300c0d02d2100180141d800e082c0c0602d5a81c001c20301c030f0200d10308080311006d0524103030710018208503007010305582e98000b030180c1200c2e00c1c0800c50300a0b0407410400f182e03506055000300061030030443c021701c0c4001003c0720740801c4030540c11035036011f40084a0903800340c074600e4400007620101c13100d94601a9803004c01b008040c0b0610038245200c00c02050440c070111400700344a0b40c5191a03810342d005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 450151250 1250 450150000 450150007
    0x601090605070803062b140c010e0d02100c200a0506090d030e030c210c1c1202070b030a0b030105010b030c09130b10020f06070206060a0b090f0a06180b0c060c0708 72
    0x840c605401b101342052156001e80d041c1c9001562072071a141500300c041e41080744c1d480d4a03030500d44848004103189034054800310010b15844d1400e40345101481c1d0000d00980e40c001000c8014616009580e42e1420100e42520764180d50b0020800a4081e80c115140d001c3c03c0c918603080040d00030001009040c80140940b44190304880014800d00692140d4410b00c402c00d04803010b40c56010f2003468180b1b81c080b5044804010740110840b817011348403000800c1d980c6090020340d44c0724000c2124000601074180c50641c0c0c0e1403c03110b0503005c2e000e2012082e020f5820300340041400100c4001b81c0707102d21801c4003200d00703040d40e10040206003129101c00314aa41c0e0341c2c41031141161280d10404c9141d40c0315400600b10040507144c05441e061000f007480d411900700780e050000c00d5484285800c01c698292521948840302d00f00068a000c0e2200002035001d050840c0014086030084000545c1d00a5a010020415900d40c2508818030407840507428075080304000802c0795405002601c0301c1070080e0341070ba08 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 450152500 1250 450151250 450151309
    0x714040203090a0605240414220f1a0702010c0203091507020d24020301030503090103020903011e0606030c02120a080429160e1f0e030102030a05060109060507080306 73
    0x84500c00c1e1480c05000c1008092191038040f600c00e001c41b081401d4408210b07c0701701c00351151415401600c06010801c0c50800049645030052003004442c1c1c204a001d00b400d01c03146840003d8040454031504100c89400000752400d0043c4035034505488180c018510700118602000121781001c1c142080781d0205100000150300c48400a1646d45c0c490004100441c8401c1e6103a20070305c203130101c03007000c080c01000103200041c8084252540c092081c240546c8880305000007901401c04210042d04908a0303040010085110f9007180c811034886032400c2040c0c0d90384000490b01d032100f002c120403d0110820050640744d00c205100ca07800b9020742c5401e258044034500d03181c050781c04072231809001c40b00d15050209848411b521440d08174181d05040c1041d80564002c90f01c0302d40c3e41140403003a00c0340304a0f078009260107001a01242c19005008556a16000043d4030080c08161123003400241024800b04009004d0750465038000d40000c030031402d550f036207410040000442c84070080b01010f001c503901c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 450153750 1250 450152500 450152513
    0x30a030b2e03020c07150314070e010507020d050d031a0d0f02120c06040807030b01060509130f111201170d09150507080408060402010311190e0303071a1501020714040203090a 77
    0x4006d401d500040190701100007800134181c2d10441c61031010540b510303050064441d0007140d038510b604001e083c129100c00f01e40c00061007203902d10b480985603010b503118509049905034042d80d0315104d041c0340d810070514000d084c0040c41504803002042c0201030100c05002d4039045010042060004e012100380c0c04090300850001d0300130768050501c07036100388018400c2002441005000d80500e16015051454510000310010b240310485080981c1e541d4200403007000503003100c0300840006030500d0390381100c550300500d058424070884070a0b0340c80c01103200704401c010810010313544060340c861810360f05002110202140c480c4001c01032280412000c0000b41120b00500000c1a0880141c409440c0c140000f400307681180340040129442003103002148041d80c3d844900780b05140c0740c10b140321440c4a003c01c0c0b5520401710054048145560340b542d0501091860500c00c201036289007140c949840010790780e0749164040e101c0b9001d0307211122440c0d41042c2d400341d80d010000000311510030203241c4806 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 450155000 1250 450153750 450153763
    0xb040c0302121011090a09090606050915030c060903030307080709050306041505060301060521031213140c0d02101704030504080d020f1009080705030408030a030b2e03020c 76
    0x546881e00716050102c00c0f160148138540d400f004907030700b00e45442e4505000030700c210100d0088460a50340d41040e00240070466001d04050320002c2d140c0e14150034005558503103000640c01d03a500c02d100d415448495070619005407601c1031405401581142c440400035180080c0091040013004480d4134005017980d0200521070090340541441c9071480705040d0343d1000c0d03880081050303010342e06000d003c00540d180c0c076041c203c54440c0c85d4842c0d12000c40c062410743c154418440d01d610700414903403d0001c40316002c03da1842962207443e1050980d181e46903241d4880340c0c80d4101c164400012040d000c054200340750240e9410003e80b409019540d40c014420315005400c1d6030030717400201c01040c01c2c41451002c02805003000150300040940c4501442c8582d611200c4a609000f2070b9210380c4070b801006000400e4400140d030120513242c03907070780381c1003015900e1300100007400009040844002c00c60030000c0d20100e0301d00300485540f02c030a41a42d00000c182d06ca0080040c20141d08000151009600780802c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 450156250 1250 450155000 450155029
    0x3040e07110f010c1e1b03111006080c03010c0c2d1b0e130f1b1502010e01141e0601020f10050619060518030703140d030f020a0c0b040c0302 62
    0x403015113418011456083c85c01415500302800300c81c402c0302005603501c0c0c11028001364580f41c0704e4100c40c598140942008078405d001100d00e801d094020950a0012900001c05501a002001185c0c0c1c800c0048610704805d1801800780009000072500540d0070006042d072442e0b03044400702c5520680d5840318440850041d0380c2d500500044002d20003291240c11064005801000c40c01420009480c1d41181c4c811030700c0d0042150600305800ba883c1451000150004c0c5514510501e018561490107806441c6d4090f05460b194a400b1000c80c240000b500214007034005017180202940b80101030652100d8040c0c4141c1c154455500c069401d44010003441010440743c99000c106810040c0611070207100c0180041a0f0380345641040c000c0382e80c01810340d000c0e07030005041a01c0e203d4803040801c1c03e03d00301e60000303428517000f440c00441001000806000c10500d41c0d4007004446040071b03441d0101c3c041c181010000405002c8801d0205142d4418190060300508662286d036030740342d0001c1d9105c41028407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 450157500 1250 450156250 450156257
    0x2130e0109021e0a120e01060806041401111801030b0f130b04060902092d06031014030f0c0607060f1a18012907060e010608010b0303040e07110f010c 66
    0x120300d0f1480c6080c40082281c0c5070b00b1842c4a09280700160040d01e00700003421410071705680e034000c00444c0e0100350012401000a0815240c090529007402e220814426542c9080f640c28000c20745120325000c404c980c907040521220000e41c2814000450140040308401c0d54440700070f00d4101e0701580e410700d000c1500c1c80e54480010325040b82c4000c0c08140c070fa030781d4810901241f050100e400c0d1a01c85610058069800403005841500c075425007401284800c605141c0104000c0708100749104c2c2000001c09407044000c018080b00038030001c050f0340e00301d42d40c9070341200d400016144000c6e007030080140c40c82c00e20810300840c0b00465001400c1c12901c400c001c0e480d400b2050001c205190625114810901ca03030300410002c20740c1401f00c9020540c0041d0340540a00301c0554441c2030904444040d07038001580031900380f05110750f402c11540641004d00901d0080d520f443c0c046a85071800008a40c00c50b080c00701c0d50142c60307440b4201500d030540d50200a914074003907011522100e42e802c0c46a00c2c400c4404da107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 450158750 1250 450157500 450157507
    0x1e05100e060a180f060b0c0f150c16060213030c050d150c02190f121103031603111612032a021501081f090302060f090c031506030f120d02130e010902 66
    0x4000d441c00701c140c000c44103e50007003202c80407241074141c80254030607881c214169440bc0080410304d20050001406041241b02150380c0b07540090030a144401c40c2c0c020781280380d480b904d0300708201422980440003020f1b030b54804a03408400259401c0342d2001c00c42c500540b40c407546040341040c014840301600f181d40f810035010390300403c1076419107988050940e1600040111030403000650702e100c00b13050711229402c090664501a44030341c1001240300a5007000382d40300e410b01003019101c00046101211a808449041c00c201da00c030341b14603280c0ca403c1109090800c0071010803008800000c0c15410214010490302c2d850340d03000132110070300801e10b030001480c096640c0700c1c040440007001090015000d060100f0940030aa000032455013004404282d03054989420782e00703601c0c1010000342c264150040821500354040d0400025114020030780a95503400c0011000c03a442c0c002c000390500305035006000004058a140d0f000d082c8410601021a082c82c1e1a42e80d03402c00010241d224074452034000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 450160000 1250 450158750 450158767
    0x30406110f030a0c03141b060a0e0303060109050f030a0c082a06030103020925052101080706080a06030501051009150308040512011e05100e060a180f060b 68
    0x1002540d10307407002007019500308000542d00a1138403184034009002c0040c944c10b00140c03100d80c1e02c12107010010000001c8150700300e02c0c0c0c40075100c4804882c2805494a0114a60400710001c03003113a201d800140d6503040100d040004200c4035550f07c009083e018400d5500d050001000c2118220150038000c00070f0208455140400d140700302111215a00342d5000c0101b6245a2568419a419030b641100c90503074075541c0c14040044034004190041560011110744070100f900f150080c03400c540188031300100c142001c542c04000340000e02c105032079035101c04010840300b032113903200b20340156034418003003034590342ca480d00d90035100103480022004447c0b05081044042901c45d141807803154840d2451060b00c0c0d0b80b02c2c101b50b80905c4c444e83d80581c071081007030ba650307510039889080001f04500d185105051101d100b40020201100c43c0690300407030381408515601e0b42d034441840b580e001006119410b0070110300038018801d500d40c0307141d00d64480c100703808410b55501882c00a0014002c138251142441c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 450161250 1250 450160000 450160003
    0x50a0b100504030f110d02150405100e060d18080d1a010c12030f020f0f03060103180807021905120a0512040e0103120c0b010e1b03070c1b0803040611 66
    0x1820202050101c108000c00c0003900b01010200010340080d80e42d28440700040c00f00b400c4548883c00290700034903030303140d03080700c406c18038080c100b624015202e800304c81d00d24541c03d41c2e0f00380f2426030302e552102d03051101c007050f00300c90340100b80b0a0001c0061162801504e60382c51160b50003500820000325112800c131201d414070700842d112090801d04e80003280076615281c20219900b00c4c6200c4040503280d001801c031a03415078045407000c200001180c1d40e140e03044902c8203e0707900301f0b94502e4002810b00700419060005c120151659070342040c00035240036200d50070418802c607501e56819803c442840001056034542d005200c2e11041d11024291032a4207107403450400061131060719107a4011b000a0ac81203a040014134152580300140c0313041c1005da44001e80703072413140b61002840e0345d0340b44002081900c0390380000303030080030070b10303625000c81107a4003002e000e0b4001243e107000018218800ca401140c0c40c55680442590310f5841520265203d880003030a40d4499081708000c90040021030500c00760 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 450162500 1250 450161250 450161269
    0x3003041d0105031009021c17180f030c150a0c0f05010c02010c081012150513050111071505040c09110a09090c0509130204090c0c03110a0308011205070504050a0b 71
    0x41c0340c44c08010241c401c1d8002070519148850004143c021000c0c428200800c41c1029100c100d8044891174580c4212900c16000400e0881581e00a4130343c660100204c0c200041d262070320720700041042d290300002000d100303820780000e01503600708403944680002041d07000c800f010f01030307009000118041d003007a04003a0030755940044890130060040100480904940100d00c00d030360155420006103842428010115888145c1c1040340f140b510341400401003804480f800c010748034a00a0000f150407084101050158884c040e00d82421242070966607100c1c0d034066a03109208501403200f00d41c50350380c580100d0341c5280c0d07078008524001680725001d580042540d8020301a07800280140c1c0310080c402055030080f055618018006101c02960680721a01070740c0203001c0c80300c42000200440100149121a009800d4000c2030f044844004030040c04906a0341064040d2980000d40c0d1a140180303400c0270740f00320243d82c0b500400c040421940d071940605e500548861401203000240c4004000e034054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 450163750 1250 450162500 450162523
    0x30f0c0c0905240a12060f0204141203042610110307030b12030d0504080d090b10140f13150e09070609030308040b070e0d150b3003041d010503 63
    0x450843c0c030154603548403810303103080c0d407440c07184031024507950b140c01e5000e442d0700c1e00c51901450000c1000701c3ca031030200f2480464803004031418507400c802060510348a201c1e0b0f00a11003003188501c58405107800c000415800411000103d403031000700200010215070010381c035886409000030034040e080341d2600a2504030f010480b8840014001700d00c12650b80e2040c40c40305007030079403541c0c00141440a040e05035084000c1112040c003640ca110318280555070001c4035450094100800d0215205003d803000011518000e0810404105404208a10304403025020f080003030b102d881603150820016060401041400584c0005080a00d0f25600300040f44c2c00c01000c114884500b040804c0c0c0c090384d00ca4000f0b820500c81c06003512850f50460304161620401e68100c81d0b541609010060b09454034008400211010480c40c000841000781102603002d03c080c00c0280010740f01114081441c41d1039a001c8102c0450385440d40d1001104000103c809401c0c20b05c0031403070b004005900b400e008550300313007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 450165000 1250 450163750 450163801
    0xc0801050402130504112502011403040f030e151611041e050606040302180f061e0613050a030c0e010e0712020c1e0a0501140105010903030f0c0c0905 66
    0x40c000385444114040548030b964441c40e1107110803001d961102c001c071602002c0d0a51f1030138090300300b4241d040000107000002c0b400284d90540c800100000a0156405181c0c8204502c14206041c0c508890f6501810711865012440340d000540c2014080005d240031202c121050070510458144034080304206490300740101c0c141749609200000500e40a0002c00b03048400152540b42c16001c20414012a04000c1d088443d190401013036007800380e1102e100d4421448001219030310341e801d00c182c0c180b5201005622080ca400801e4040c079101015080511008044022380781c1d50b80009109070300307180d2080c1c1d046141108180b044003200540c060140051114010311418040c00040424030b2034290000d8060740407030464505001404600c0c4001c00c41d0101c9900b11203526841c64560b60740714421981d40d07107050104507104801c549164100d0390140c554140061960300d05840c0da801084008007044608450301002542210305080508500c1c50000b8480c41c3c0a02002101040e00da0340e2850f4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 450166250 1250 450165000 450165007
    0x30b0a0e12030c04031502030a05090106080c010f1b08030601020f0f0715030f091b06030b060909070c0b07080115033809090d0305010b030705090f0d06020c010c0801050402 76
    0x100d200000ea003007900c462860407250340380d031002c5a200e0302c2d0003103400050400f080c0480c61105401c1c9500a1401030780c0b010010013150325a01400d500721034032440391000e01d420002034400c1541c0584822600040c1c00e09001c0382d8440981003003030310038444ca0401c403078502d008800d200d05035030304102e03010700366000c14010111140040362103560780c501d902c140030b10443c03003684001c8560301c81d0700309003c0704158020610552001e07160407070b10601e401e5000803003820a140000f403003600c2402003500341c80c0050310036803401400a05024002c8070003001e050501c069121310f480060b1003589100c0c4901180d56900c4e00c03d50411030005500d07012035490504060400030b24080d00c2e404d10121403134442219040d2801c07a2010040ca4074028490200607510500300d4041001250001c10048640c0e030403941e0400a580e00c80b041c0a0b1a80015114400000c4041c800f154041c01c001c07501c42d40d0030710010b0001d60300c07013034650310303a81643e1095034904270f50f075100c0505600742504480403a000d0701007207606504 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 450167500 1250 450166250 450166271
    0x150e0613080f030c0f0d090b0904090605090f010f060b030c07060617060405010c080f0f180f0705040c0503010608040f0812130606140102100b0d0503040f03050709110d2003070306030b0a 82
    0x107107e0709000c2d200c0800030005001000b03960b580d00c00c1400960000c4107100510b80542055251050303048811525400c28110502c0d40645201d5542929200a8039a0668990014440007500720300740441d80c0316561000400c0214407110310ac1c1d406446c46004080620709458581d09540c2c8028001c01402581000e101c1000070900005500888491180c0e00d10303a9401c0c0c0002c00014041009840f90040300035584a80b00003081c0241510b4050300d05004c50b0000300411541440b09200e68000540c000f408135000a800111140d5044e000700400c90030000c03009a008190031003603420004040701d0b01c51003410811a40107010003410702803e010440c0c400341d40080c0d111102c160308540d149070b842101c05080d41d220080b004036150003c0440f501c59440e000305c1801c4c460240004e4445100b0090006000d1499010b0303400700c41c00e00d040c580c1c1802d001d6403204000d411a1000c000d01401921200004000e0000245106030003a039000b15140d40b940c10945400b40c805008041740e41d0038a280c040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 450168750 1250 450167500 450167507
    0x71821170301030b0114060f0403080924120f06031915050c0c1509030313030c0c09020c1e07060e01030212040b01090b03010207050601060c0213061509150e0613080f030c0f0d 77
    0x20122a00301c078bc0e2541d14002c07100083e1a2031000d012040014900070381007000a07012102400c22800b01940c10071040e1107810300565400700031151036526500843c002440c480180d402a0a55841401088080c5d6600070504003515001c0f80c1c041e0402e1000325040701c5000b001c0080c01000100b080a0b8400750404005543e200e10004101400e5419074650100c201813040701c03200b00c0307035800c89411440d007a211174900010758000140e00700c2e94842c20b040700c0d003503410719040100b0019a800091110314038050055404040102680d81030581c00e204100b698820000e011f407155100e00e59038074080d81480111021600c0e60101c1c07070b001e68030500c000b10000d00c0010700141521001e040c0b042d1010502d10000d4501d80d00d00100100312418428001409402c0310741d0040300d0742c02034a88012480c0c55503000301035011458580300000340249400b400c64241500200b00c42c03031a29020400383c40d1540d0a040c50032000f0b20440c20550300c0050024200117080c41806007046201011701130754410034200a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 450170000 1250 450168750 450168757
    0xc0e090607080907030206220519090504140109110a080a0209011205010b0d11010206060d0f060f0e070305030d060b03010503060708090a060e06071821170301030b0114060f 76
    0x3001d21200b580462064034003049110000d56000300099556101132000e0141d204400058035035444d00700e100030505250410310844144440149405114a030040d210080c00b40a070044d100e12000c0c1c200312144450a0150814150240100e0f0703000f240c51a040c0701c00300240b503006080075085480780710016a10700d03020504440000d0f0301103001c2640c0e41062401014110500b035806000350b0719060810601c0c803031580500300d00b6001da5111b59208000d04c480c1e50960700009080f07415070816040003625a41c8003401440c88810001011140032082034030b041c00c6500240c0d855403022400108501182c00f54074080c0c05d081000d075045516140120341c0e240006401402403041e14400282090000c010b1032142c15005002400b41c0f50020003031a03200c0300d042e034003032000920000c0e00b40a0308410061400840313620b28001a800d81c1c00c4444041a40103110003250300314420900070742000700f000c0c09940a540602c1c2111a154034044042c0320a1410103901409520b0074040c2d42c0e0b03000c42441c00d8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 450171250 1250 450170000 450170011
    0x301e011403100b0a0b1605010b01051614010e030c100b040c0e1c061401060f08071b03020a0c0617181f0b13060501030b030a05120f0f0409090c0e0906 66
    0x101d4016400000981c41103515004410080f00208000d540c6c0809215580c0710300340540000c104080d40030313004581c036102d0f02810000c0a13100040d2200010300d041040c828240d00301000042c144602540141941d1002c03201c60159801500440d60000e00c40c819403e901104850400c601d144208000d03000c43c2e40c400200c1d1080100503c07034140301e66000c2c62001b22a50225003040082000740000700654028082c9000107502c0c41e1f821000d01e405501d40d03600072441078450a120800442803e190401110340440c1180221460034001901c15030084c005080b0940f113014020a442c3ea9110012034010042044212492081e064000c804244202c0b42810182429843d04140303407124041d1044c003400c0d0b41c001000b03a8480781c0b8605154402c4007a20400d81c0c092041594000405940c0c20400e00e010b4883d82064102c541c040039100b0040a46561000b0340d68246400688407000c6500258070052034161628880b800b0407001c07102c40000740a00300c2ea003a00c103080c41c1030303103c0e601c3c10300525 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 450172500 1250 450171250 450171283
    0x10f0501120303111e0d0b03010c0801051003020c010216060510180b0d020d060b040b12030405100314010312090e07080a090303061701060906150203301e011403 71
    0x6240c001c840c0d0490300500307940120201d2045161003030030001d80c406c00c1c00e0030400e45040e400100601c1c060040310b102c40590743e25500642d0038a070800515021002012050540c20021200c01083c01e0000d040300d124032400100d8509a40c0c20610107a5400a0200c180320003c07450903c034020b26403100c103006a280c0704001600d44400310104010032080107001c0c0d844650f450010040002035001000b51a500f95010b200b025646000c2c0028040c80c03040c509040e40003404240301c5410450429081c0c00460310b408510490000d2100c03d94074400c1c1c0043c1d4107046080400164250054500350040000c00107004080c1740108008056900c0a02a0b5801d581c560954100b414400d81010015022051701090900080d03000d0318003e10451040021007810134500150390588250600c0030a070894000d182750240340328111142d42c1d0000c942a00030303030103d02c0c6050050320404445200d0342040381e0150061666611213200d012050780681014810800d4440080c2c4000c680d592240031110f4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 450173750 1250 450172500 450172511
    0x5030603070e040506040c0608010b090d0501060b04031b150e010e1302130512030903030a08040f060f0b0414071407080f0d02270307050904060e150603010f0501120303 74
    0x180000c1c2860300700e81c009000d0181c1c01c2c060109101c4081407503030003103200d400e024202c6a034450f001e403000032003441041c11050060100c00424100041405442480b603400000d400d610358072508032582082d00192a00b0051094100382a108641c101c800f0749103607440701d8403043d501300000309580b0a0021190410183d004c003c886074482138402d08450300c1c1c5810a43d00c0305003034040000c209000b0300c11a4030602d0420209080120301108840000b03070064051840c102c200351068841c050042d00032204201c20202ca00d000c20720510452001500007080071071040188802c0205642009211aa00030922014440825003001e8200503250340944600d4840300b0300d013032410b2140241c105100d2501000a1071149845041d801480e950384058146181d0079460300710114800354107c0515003590000320148458601201d10a52040c8a07000108003580008000d90030805001d202007542c8070380409220b498a000e00130406d4403d903c3c0c8003004070b90715206d0450720706c020002020f0107269072503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 450175000 1250 450173750 450173761
    0xa0b04120e03150a0b01110d050306150a030b0108010b0c1b0d0f0f0201020f060c040b0f090d03020705010908030c0616110703120818030d15050d0b06030f010e030a0503 74
    0x81e04041100c990080680d081c0452403401c100c0f10702001c03240300d02c1c1240381c104c140f69558010009451001307001c01c020482401080c100343c85036030010b044282c0c4036429001200c043c074568001071219424564010a48081000c0007425404040e0000c884c0c0c0c40c4140000c20010740c000801d000000f2001d90b19201404100c00417030910550410082e0107040d8030100c0c1c00034080150f28a49100d4402c0e070860b084a06030303002c0c160300c03901c0a443c07036000040d041100700500c40b641005004501a01c04606181c41c0d030010000e01d001040d048228007603001510100103641e0006594402000024040c42c0b4092034031440a4440d94014400e0f131101c18181c6038100b0507482075002d9a4041581c0c4200c501141c0c403400d00c000e40c1600c00e031403000068045070003d2540d03000700c0e0b0351000000ca420000c4d82000c0340d403035070351002d0035034200091940440f240300001c960b603400070100b4030903004110120a50030314006160030300e004400f81017956814544c01c03619030500002140c209a841d4a405500c907110f1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 450176250 1250 450175000 450175007
    0x70816030905060f0405030f0303060d140304091a0108071b0f08090303030906310b06040e0105070509130204150c050703050a2405010b0d091a010f050a080a0b0412 72
    0x80ba0401a00454080b0b0046602103000c8010300079207000310b0442d01401d4101040c25542d110494440d074100b11400070910020b8070382903070403c0150306001502d0900d910780e52000c5c1111032860610040c002d84424001c00d03941c00c1046540c100100f442d0a6154815010007102d140311040002003e80301030940050920070340034140c4850040080c1900d543e0709100542650700c0c01d0a543c40310420b00014507a221a42030f007400000407455407409000300740400d480d0000d075068000d000039000703074807a0004036500c4004e11815114140c40c0c0c6030f6680f91a05881031112a03948180c1c8800040e10400c018080400500411080a0300600d0410716049035450181e042104e80d500c002d100c2c0c0703c1c4031111001c001c3c1144122801c1c01d045c56040340050b02e100f007a802580c00a00c0348a2040c2c2c010820a800111720350003c460340d5004503c51000d00d99030040c0c907505a10b007640155180e002c0300005100034500704000d04018001c01d001000300200e651500c0308941c802500c020b010450703084409807001d00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 450177500 1250 450176250 450176267
    0xa03051b0717030c0712050607080c120103062c031918060801030b0a1a04020f120903030604061d060f010c061805010f110909100308040816050607081603 68
    0x2888021100710002c0010680c1c0d44d030410007803210f280c0292480410021000c40700c040311550041c00a0140c1d454a01d001c5d5591100906140758512042000810001d240d05500f4000c600c940800200c00a505201d0070004040100b0405041c9205603a0060610000141c4a03035503020800c2081d0515800d00580d00100c00034160b10745109103a100080c0c1c4ca4100344028101c9015014079040f5545030030200782180e154207084032074180005c181401600b4560f0213090341c00310000200313140030030312010011001d20449071070050394000010000f550505000d09030050900d1440c045075400c50032583c0015034802441503004c0c4224002003d0070f030b0b2181d8914059660405003c000f111a02d10410260120041d03080d502507080008200111000b44101d207540c54421401e1405c1c00b5102041104a4001405039003c1150f440710204c080340c56900180010111040200203604103034810400200b201c2c0c0c8158459001801003d02041e14401101e1070305000c940c100b568001240740c16141541b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 450178750 1250 450177500 450177509
    0x3030408100501050301050615070321090602090f0a081209011e080604321504020c03030a0f0b0109050103020a02012403020f0301061d07020a020d080a0e030a03051b07 74
    0x418a10340701c6141025500090598506400078403442e60fa640501c074005074060030704036020000700311100100384a014110f0309075445048140f00801e01d060104182c0d48802c07000da038801d6001441140038a400b5181303100303450003914001841171904950a4a82408401001d4090b000081400060784038400302006280c513022036944080c00940c00404070102201c0360340c01545010718a1506031241c004140c0080181503803100c103d0300f0409000d01c0d00d2000b0301620031440318209100601e1f580d60020740f00740d07000003000f5500c03813800c1540384058681e0800c80149040c508200e242e810303603000740401c0c143c3e2401c1c01c001d40e4800b201c0d08200e004000c444075684c0c900b4100c109002d0708980c3d0110040803680211500501e550012040500700c80251241c14401c8803d0307100310f102030b07484a00d0550700c00103900640c4d40d030750000d030003250020701134010031036a0400c00a150460607402c08403c3c0b50082085d0700400448256030380191240c0b2171040b01105a003a030940140d044082000301d00081e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 450179856 1106 450178750 450178753
    0x30e100905032209090f0314070f03050c0a140d030606020102090a1202150a181409061309050307210503090703060207151e0506042903030408 63
    0xf500307100105801d400000003e0201d0301446241040d40c042c800c001c2d000c007200d21300103042405042800b0b0340b00c00c00b40181804600d00303880300341e12aa41402c000c1d175190108016a494000590002461400c2c0701070441d810721004510104101d000c2c0c1c030b0a10103d03807996010390903400b8400f04aa00450300282c10094201c2542d20307044068009001e484001c00000002281c035030004551301c001c100c1c40f00350b0050354413000d50703000010160101103001c0100f07c140094a50680a400301d4400d8160b000c002c8a1009140d0240c055103074020212650b03112140f415071398a5908804421340c600050301c00395900f501610460740300d20007800103080c41600b5561240000d40007407000303032170000c2c0b40c10416411440038410501e031040001011428450700d8441d030400d5400040016008901b09900ca000342d41d88103042e00c0f486c0501e01151106205910b0111380346015541c80380300c96 = true := by decide +kernel

theorem cover : BRFrame.Cov 450000000 450179856 := by
  have h0 := BRFrame.cov_init 450000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 450000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 450000000 ≤ n) (h2 : n < 450179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
