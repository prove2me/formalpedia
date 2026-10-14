-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1372
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:38:13.382001+00:00
-- url     : https://prove2.me/submissions/3b7802d4-fda4-4953-9f11-bf89de686103

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 246582733 ≤ n < 246762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 246583983 1250 246582733 246582767
    0x80607050c0703020d060f05240904111c030206060103020405060f132d080109110d170d06090f060b16080c0a11130902010f05071a01091b0c0b010b091906050a1d010807 74
    0xd42900503a9440070580dc942c1650054089018212828000c1c54001d0141c41c20781450310401040c0035075242d810444a00340031701400740d0b5580b4811030102e00c600d6010f82c404c099441c0ea107180320300189103040c1d42941ca500d40402805003240c07213814460803620f14000c010101040c090f0340000c1410240b5108100381d000707000c0000ca42d6410444010b943d4803030007001c0c1060742c2c1e03418248000780b918441d59186080b081030402001d030400c1102c020900c1066019045175131f003c10300804001c400000c0300c41c0c82c580802034400a040620b07111003041c0780319004070b2040400395400050b1031000e20902030440d4050f5107080c03c164134080203446039031000c2c1e010707a203c45c001c528001c24441780400303081c000c00c2c44d100d00240a2442801032090302c0b41e5015018100905c401c0b008002c24400000315043d641e5143d00c03e90744110f040009a44200361441d070480807166070500007584d03500070014058035240c0d6141c0c01481200003800d8101040c0c02e02c03c44d404207100c000442c0f002e0b8882c5c031a6072030740c54101e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 246585233 1250 246583983 246584003
    0x30d15051f11030a090e09030306030709051308070c0501030c08090d0e0f03011508120408070b0d1401120b0a02071a1009181209080607050c0703020d060f05240904 72
    0x340b036aa9065a2021282c0800324252400c2041101003038004558080391610285048d41000c074000307521440244503d00c1c40f075840c1d20100d60074400d00000d1070803460744000503039942c40c03881c03030504800505031141d0b030b0200303152011503180180181603c03440342c5060005000031503800c2c502035540104d80010541c00c4100200780c121681c03024403605003039920040010000c24541544c0e50319013480c5406001c00d010f42440308008000000440d90306075800802c175607495001302945000204800c074078543d81259a400001000108208030300300d1240506510410f41d9241c44c130143c143d200c0c40d800105010380410980c0c08648141d00d5958104090350703105c41c15a81d84400000a23503025200248440800d080140200310b40c0d1144c152604129003442401d0a10b85000d654480000400aa090040004071050182000e100c40c00155500030003865a510050400a00402800d54a4088949040049a80e01e4810701c0078071902c04280340390390781d040000d0041c0b105150025104480103c50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 246586483 1250 246585233 246585257
    0x70b040e040611030a020325021509100903090806100e0402011206030c0803210403020c01111c03020408011a0a050103090c181e090203030301030201080c0c01050702030d15051f 78
    0x101e8010360190401440160302d03403c141230484480d4109900801c040c0a05942082d0110707004070301c00c0d410b040c3c1070704840c0302540c66801d5507082098419030042103501e442000000c141d0024004c200ba10101d80403180c0940d603802884410042034028001d0945103240060015841501030048414031203101081e000d40e640d9419203481040d404c00b420a402c00300700307510710b00303201465207140d0160500054000e04158070702a44078030b51121701d030b410880b500c0d11000c003804040116107103003601551030040003001040003c000303402900a16095500b0007186481d8100c2c1c0d900f0081d001c1c0c20003000d004150b0300c0d02c401580100207030700084914042144000502d42d0243c4041030400e5160799021452591010040c202100004240801c003071400e69800096100002681c0c1560390a0920601c1500d88035256071450042990600750303503090508001c807156011016040c000315910060049800041200c0c206034854011203400c040c0c41c203030f40c4d0a0315950190014201905060003100182 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 246587733 1250 246586483 246586511
    0x6010507020301060602030a0e040b10081b0d1b021b09091203010b0406090e04030519030b09090a020901090e0330070806090106080105100f090512010e010608070b040e0406 76
    0x4e65480100941c00110311303021155041030b01000790f44000c0380d00300a09140100003600d0085040346100030801c5040c0081c01212701c0d0131002041840c0858816164103100002c800500348403140022041c601c910081d4100780001061000c0c4003005000c205000b803894103100714403c0051200ca0b080c46203161030071000700c1074030045002c0e0064207109a5214180340000c2d1204402d41d1140c414102c000017000301081d44507081d42d044001858001444100003001100036041030441c2542c000d04d044140455003100140800c00340d0310076201e00e410b50380da504d4210212944800c04980c142c0041111f0103040421604418103d80c0c04940150b0f5443e420724a429103460841d400d80105842d00248071036803815000a50052059140880300340d8140070200740d508203006240401d02c20540740c001080e0b0b00401c440400703000040d05d09510100b901505a020f4010304a000001d0b501c2c0540202c1c4a50700454140299000c86112a151919249400c00c245000400c1030320000d03921042038149374 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 246588983 1250 246587733 246587741
    0x120215040b04140c060406031506090608011211120c040b06091e04020f0a1101060806060607111f02030d0615170403030e01110a0e180606091212070b0906011d06010507020301 77
    0x10013280d0300010180f20f4103030b2412740c10302e40e6001201840030f40c80041200c10343c000c80013415100a1503000c128000c80e031920018010002c1ca07050740c4007900d18011803d070000001c0c01c0c984860121410700a02c61044d007805200e2003a4520f03030fa080380c1c50a840401101d001d00c1110340c4144084c00044c984035100b005415160409904240021200c0c01211100b113400d01442c8060040358000e00b94900f8030000081c05442100740081c0b2092400c01040004d40e50008000f10b07a02280f903484124445c1500000e40b0b90384020f414007101894403802044400320b59100613240c000a07242c0004858442126074a182c0005000f00c04041d1139100c0700340c0b040401c1c081c00d0188d90490120a03112040d1f1707240a880b0700c000a60050040b0b0406241180030b2060000705130708504261585695859090080b596400705a9004042c600c112021040242c0320f4800500000f4054044001d484d2640c4465a88802081c800c0c7d1480c041160b01588403031300704174905030b008101410602e1400495902003403c2d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 246590233 1250 246588983 246588989
    0x114120c03031801020f0d020c0904060e010603050618060603070509100f06050a30020c01090f110a1505090f0a030b1e060402090604090b01020a0f120215040b04140c0604 75
    0xc3c8100c0140900d5804200c1458404441c00160200301105c02000b540d81c2c000d01e00052003044040c5c0400e0078000568428000700307407501c009005280c0c03203061459440009441c2c2140303001c0c3c21940001c60300000b00351382d8010040100076265207883c10040002d2030002900482d03030301401c00d00004888038008020701c01410240c039055100c07030a02c24040c21920314208036404032102e82062804071a80390520868500241d03a005844c3c0e28000400350040c510441c00421000b504003140c0c00f13200b4414040c41410100321484600390751155440c5000411114010000c1481403240c0001403403c1340c0e2a011007040a00100c407911b41c0ca880d81c40000c07206803a03214840001c00c3c0e951342c400707040c082480c2d4007401c1036030154034251f0660701241e581c0c400c034821140000d0391107080e0382c003e0b0300c280078141c2da958001018911410850070066100e058441641d000740c403504284074410f4103900a014861900f01507014001e0790b49494902c4190701c0781d00385d40241d008084078560f90f641c1d80006031003d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 246591483 1250 246590233 246590257
    0x50606040503160303120207030f0c140d120b0a030b0f1513050a0606030e0a14010f150f060206040209060607020301060e09150f04050d0f05070501020a050910080114120c0303 77
    0x343ea1131400d0150100c208000034140c0c0500403c0002e012079000300249103158070382d01c0c284650104500303110101001c080100e051a000d0010a105081d5014003107144042c0c01a4080014003400070411222100f1880300034a4a440c0400251018048022091b40a580314040012400202e800100e4096040c0824040b050ba41c0f81440240c1300d042c424003001d0400d44c10204050004ca80166170343c0d00310a200144440340389840e44409080c2034006458041c1088414403002101c0b1029031803401c0607016000c10412120800220b00b4030001c0c140d80940d4010306030350259190542404150342c46403a00342c0c3c240d925590b00041ea012100c1e85544240b01c076238090448407002103012002000041c0075040b005034504c0034000481c01c0840c1402400005040801109441c440c00f91194002c005028110f940f021800c60078a5400ca40100000403040b80c1c1d51030016200001a25015000e009401854407050340d002d103941850f00350100000c3c090b03011580881e035280002840d5074410007400b41 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 246592733 1250 246591483 246591523
    0x3030801261212061509060c0106050406060e09090309090a11070507030303060807061727060f010603060503010c120b03101a0f0d1e1505090c0307090603030c06050606040503 77
    0xc480c080103e042504400304440c01030904080c186600781d98001c00e900075203d454001079074292203d003503000100500c1c000d00140303c2503940790400f0700075091024525001d1850708001404402012044400f80c80004002414944038040380400614040002103840101000440041b03141004480015482517078041419401c00c000346051802c01da01c05418400000200701321400b4030b011582d80704020310fa440b0842030094101080070500580703840320901580f0180444250f45211041c1a62403a45042c0607840e40c031070500d0300300e6040044000c000741200d00b90002e0300c085500700c1e10b9407110040403030300790f004941c030540b08481c96016601500039101340d00038814103207a2a1810540c800722240d00f0b0071000340c1c5031540c080c0301d1110007003050003840104804209100e00c840991050f891401c200c140b6001c0c2d8020356034903541070701070321901c030f00c81c4002185070f5240902030030349a242c2d031805950b044540e0381e500903240140800d5404003050001180b19107040069032210015503a92030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 246593983 1250 246592733 246592747
    0x10e071a040f0b0310031a061e0616111c020310051e07030906020a0c020f0307061d0409050a0c09050a29030f010c03090506060a030308012612 63
    0x44040e50450444203105106000c01c0080c5012441c41000311401100104d640b642c420300221030b0141c2c1c58200405100504079141e40c481c0c52103040a20491080e01e02410001616002c14614001c2580e0345500c0b940410000264150340c105c2e04022a100d15014a241d10085000401100354000c1d564030f00e51643d50094254981003081d0407245005041c02c02c202e080c840b144400384600e110390705189214040c08213541da42300c2c4d0b22948003103420210864445803108002044000107a1080e80700d02130500d0303041c8130382c13901191030421600c294440b0f180300d0801340c0d054100302e626036848950040d507170422036000c41c0060001036025442880e107801c56504001a0f03208540d409003400d0525440e15445075a1101c222800900701544074140050b03002040b80008d20b02600720000d1103c40d4200420407031025003680000742d405114005880c803541c0d81c64180117903007030b20f80f001400081780c0c08d0040261942c1f0f40340c20300e0b005481d803601c2d480307003445928454500040342e82d14180f61040003c0403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 246595233 1250 246593983 246593999
    0x23105280c05090d0804050d231f09050c03120406080703050601020d140702041d010608121e070c0305030301210507090f020904060e01030203161a0706020c010e07 72
    0x6140c086a0840c01c0080e0780442000030218069000501c0c004c61641da20700041c04505170a450003000c0043c03a21122214500c6c18000c0307200703407890300b041000c03091002015500303010070504030500701c4024040d07034111030900b1000a0076a5140c00e45040c00340020010132070700c0502510402011111405079103900d041801132180c88003c010b48205881c02c0309202c03003a030b0301151100d18038045240a40310703015503000340c415074441e160009601c0352604003403000c503940004546103c944e40c0e500801c51280c0d0340500d19200d03040c140433000780010411000036030303010010f8948411748500119604103c03032941c41c4513141a007608255080c0d80084010007000900381d010081d0020b00d1445034641c0062a0b8a00350340d03550f50f000301800c07503880d09000702554241b58155203886031f00510500040d6580c0365909490b40c400e01090380030b40034201e428207060181d801480200c0b55200309861000c085080503141030340291004640c0300d40c0030401401d00c003c2c2405800001101c14003e0580c2620309100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 246596483 1250 246595233 246595291
    0x40506010e07050301030b0705040503030c0a030306141503040305160f1b0e070f020313030b09010b01050f04090902060f1b060f0123030106080706050403060506030a023105 76
    0x95007141d40200421030150b9100c003d481c1186c0d88418000c0071501c5d628001c0d121405290000c41d0144800b0941c030514800018000e07520500030f44081041c2611001d640c3c0c03981409805482d000450b00903842c03030790300400000f194043c0c001e28007179050029030140c0541c0c6200e011b505480d80060980c0c00b0091065102e00d00c0c0d0500c04000d02d0400031850420035011a00000304401c05006001e144258058000c4c012900202020b4004000540d220b04d804545480c00782c40c00c9560750b103000c5203c0c030554002d000f142c42c100c03581e5154600381403034121002d0203800c0d0f28108a800c45d1091040285820702c20019010b0854000780c044200104608181d1804c80000d0890b041207070f0420040215109010141035000d1916001c1c400344800d1070701003400b500c50360703006503158412841c001440d50360190152042c2e0b84113400074040313034481170101552040b20301070195215107844984c000e41410f80c0c0b1220040d8102141c0146504186075a59085681c01c4916041c00080c04060741011200c8540d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 246597733 1250 246596483 246596489
    0x607090801060f050907050d110d0606080112170a02100908030f1b0d2705010e0d0302040602060c0d1803080603160e040b07050d050123060304050a081e03010e04050601 74
    0x801c209070903103400005400300c2c402801440074004000303250000140c581c9c04c90070003511450f03605030b580d418001124004104920400c800940808000702d07020401c2641e0703031a029000342680e15620341c0403401503450b910400ca42400e601c14002c40b07000700070080c0120800d0301d0103002415107900d0101c090101d109001450a4000c45000303544000c0740d8001c500b50382c0d1507980c070000081d03000c12400d42a00c0340310104000101a1498035092000c028054211150860b804401c3e6000890b42403429010303405940180d1000d42c02c100700060b0f0070a0f4140141000303008081001c0340c03a03092221031802c0521103840c10340024800758100040d03420f040200d071030305185c21070502020503d807040e014401540a04010004500c040c04500c0c00d9100703005845020460320420005542d4030250340303001168400351310108070508080214586804415030340b049821501800102129a84909541c3d02480318810644500714488201d2603190b80954080d081c808005811400d0508109150010580c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 246598983 1250 246597733 246597749
    0x10203031003060b0102031c0603030306151403150d0302010c03060614070b060d1407050310020f091306152706091404091e0317060307030312020903060709080106 72
    0x10911001110201c61407003242d8215900041c40d4002c000100d046110f41010020403007940144c4400000040e48582c1c112446600d0030030101d0742c1d619550301c19420700101c000c00300f404020112900001d480007141c1c041c2e201c48000000400100000e0100f80d80c03000103800503907480032628080c54051141101034545402d0143d842414201088118441c843d00144000902004651340d920f0b136503040b40e1459802441c4c1000c4000103a070480d40d59010740301c1c0ca0303c00c0c4115141c070204200341e031003154000565800c0061902038650107100d000c0660810030004259500d60004105010201e810111651607441d01c01b040c1000442d450840124410030b0404260700740100f02c220b420200150858a0042d88051050718540000c0c00420490902030249100031440341c01c1c1c01c21400725813018a03c2038840b184940e003003921a158000c0116001c607010350080324140040b90242c821644213854407400076183c5010140860b050040075190b0901045004100f40030146082c05084c0281c2441 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 246600233 1250 246598983 246598987
    0x70b01090e0706030906020912030a020d0509010512070c050d021605030c09130804120c0510020609250b0c0d021c080402010804050c0a03080a03060f0b0a080c040f030c090506010203 80
    0x4210703903120621403190505040d5164855010402c0f96016202401401804e03145805007403190740c0d449602c0040804c0050149054549485000b40141c803000031043e910743e03007449003a020341444d54601802c413600340f01e210100e590009108020180a080381540609540aa50501b4008203845038105d14842d403c17201c407480e103503250300428a038442c041e1544820001e1950400f0142485560048950b030801a0084414080b4001340082115400e85404010307070a10344040341c4135101528000c02c2c91f0403605c0d41c2c00407414040e0440d07012800700540448a103030380c0c000c24040755000580010058000061401c00203030184001030700075821500041c008202080b001b0b100c5907005000038140a1800f002c20b051100421071002c0c0803201804006149403607003040900c41e0041c500000000c0d0804001190800c1821190400c448031038800c5410100c11200a9450040090080c0d40321507042c00001244060308265200441c005d0140340f0300181021002015210000d161303d040d0343c42 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 246601483 1250 246600233 246600251
    0x32309030717040305070608010e0a051902030919050c120a110108040c03050a0b040b0108010908030c09120d0503040c0e0c0d0905071d0114090f04260f070b0109 71
    0x30048035550350748621502c01d080c042007182e40860207150405042803080560100c0c00d5504801018143e0321650038141c16541c0710000c8800b80c640841d02800000b0341036030071550740034554004d0345c0c000c805801a10f14818051409008002444030b05aa080c0d01c007085d828a107040c00b842e8002403138030400c0a04035802d42c0740c0b214204041420501030400c11880300103424030141000300400340d41c1c4041030f80d01509080c01c00c20f0040b00d040c1ca0541b42c10000900014094030148a5010615032114000d81555a000400100b0340c0000c00c4054010025116150303a0f0076040c4062a1107000c00d4071074a3702c0b4101400c00c82080c040a4100490a80554007400300b000c40145c192658280480c1d00410212003a01d003003401d24256501020342500305111031961014003030029816101003141c40072481c5907003820410a001c066505122542d92000801c001c074805c00382422002d624524034a0000703114400070b501075803040c6400c030101140030a000040240140344a0700620f0314883c103001c1854 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 246602733 1250 246601483 246601501
    0x100509130b19020301030819110703030c0f0204020307080a1b140a110106060233040201080411090a0203040302010b030d09120c0f030302030702031213050402280323 73
    0x600050003a11000042001550841d0200b8410210b255028019501e07569a860807100a810802011552081d0758500701d0b5000d00c50140840a8003000005000076403840c1c9080d00d0690b10b000060302e071101d00c11000409038645000a501604582d43e61108034907244a404040307544c10079000c1c10010064444644459010304042d4510186241d000c0d070b1a040c0f90760658242081c048028000c0d42807400c0041c4040d0045401070040340841d11385903c803882c28076030000421420005060341c05404000c80d0155119041c2681d100d03110b82d4014144c594400d00107140072004580b101c2d500fa03000010172040590a000d41c8d03091410582c010649440c9220015001d4a160b00031041c00d05a903000c01014030403200e102e44020400a0403048071907807241402902caa1203504c4c2a0f000340304d00142034001034101e0044444107120625812005801d040c1008065440784803101c003545075117074070204002c980300c156050203003ea89000824103400c0a80004c0681c456424407a416610410000808 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 246603983 1250 246602733 246602761
    0x6021212190b0315070e0303270105040e24090601091802070f0c0603232212030b0f0307050d06020a03060e0a0608070b07050a0201080408040b12100509 67
    0x612603280100740d1445100c40e64010414698103640c184581c0c2146148164112022030103565190740f880a0343c0031a41c00e25582e44502e04c080d01d43c80c1816402494403511400c07802d180881c051504601c0c00780c0c0d4000c41c00714408242d603030306010203405c166100c50803481d0085a4821005441c50441441c01c040080e00d020181c1c81000c1c7c131115a1413034155048007079811601c2c0d1a9008006402810b5141070a12980081c0c0c000e44010920344030250468611402c0c03801c0c0c24000c0310211301e005907100e205c0b9148030301c40e1501040b0000381c81948800015040313402d07580c840310680d40004208040e10100b0042c034048428540c042e401840091020342c60319994000720720380201c4090703940c1d52035403021001802c1940c010948580100c0070305c01301e4146a00070804890300e031000c561001d42c499032032203824455890000d065500184035800194001c07440c540e8440d01504c83c81d41007903074545030441107510801c0780b04d080780c4514080061403000310596402511045d41e42103654078010041c0c4081c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 246605233 1250 246603983 246603991
    0x807110604060506010908030403060e0609060405060c0a12060b03091203100e1b0703080a05010f0e16090e190f0908160807061a01170f0a0c0c061506021212 69
    0xc59210303000900070317074022285400141200b034100d0f80e03035076500d0600d84002d2900205c1020940196004a80c10800004880e402242c01601038040c036101d05410070307010350040104c00c043c0b01720388014980120591042e44010503c201c01d403990f900d4003a5250707040c90040e0300c102101010030305c10b11103924070080c01c04065030001c405110040e1aa42130402c6040c0859072800d000e07100c0001c50100701603000740c001d03009190b07414082c01300307980703600552264180900412120600100000786987c0031980784c0c07916006a418000703130040d04c1308130312522944111009003003d14403084070302c2c0b91b0119105418102d01490340c02c201d443d10f40d5480004500c40c5042100142552203240010302840e0301c00c940a4680c003850070054400c0c200c0403140c82c913040980884c00701e5240401d02186440760140a0300c500048071314000b4603074a90310350500400d0f00b042204208104404504002010b6214a07542d038160b800e80f95a0840c50600c0c020300d401ca0713981e03003d21410408d0140c828803481d001c1c126500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 246606483 1250 246605233 246605243
    0xa0b0610021213051c020d02040209010e091618050907030c02030c01020703080406050609070f110703020d05011506050a0e0919050f010303081b0412230c010807110604 74
    0x108101100100e02d85071082a840101d0400011104020700b100b1000c0d8085034415507004400044030320100401c0d00c815500070390050070f440d2140b00140350560040160380350504100070700368444000302d10881e4089401d481e0f0f0f02c1140801003581900004102c0300d02503022980401d81b820f020110300302c81001f0b45040d0070f068551000b104445d00a03c00c0d00c454401a9000b15102c031101e060060041c00e00341d9064405a1424003c24403c6c1403400105105145644409000b43c2046804444041746149040c40b070380070392880400140c0d2520010054a4000c10011400411701c20a9224215260740040b0034030400704007440009401c003010203020482100c2e0b03500155502e03000381c020102c002c001001d809180c00c0801011654400320b55042c0c0f8000e5907441c00b20b42d40c0c00e41118044220040c81e280c0f1900034041044a0210101d0400209201d4810710400c90742c0302104142c442c090045030b0b07030580c0050644542030350b400219260720480a180206248014005807a25140c0241c00500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 246607733 1250 246606483 246606499
    0x1602160f0b0c0f030307050913050103031b050304050a0b090405060301090c18270c06030c0e0d050114090a030f021507030f060305070f050a090e0316110d06050103140a0b06 76
    0xd40d0b4a030a100440c4000c10041c01c1c1c17941c03071078207581c014075640c004000540b01c4d040d51355050704907031241c2c03040c941a2581502ca6610170002c0301c0e110700e10500700c1e00e01124544030405c0082680c0d00d6075105000140303440f80e030558484402c482000b041c0c40c002130007540203a00d0030315814003180d55035110300700b00d03510728164540d51a0510b009001519030790030070328941440005a240c42c101c040041403501400f980d0903003c425191481181900c101d841c0d03c03400036502c803031558807600d40190f0170001c4030701c5603000241744003074a04459034205044031208295040503017628189900041449c1825103c2c0c0302405007a000c040041620034009480f49013015034130702461003808015480f4201441d00b160480e006240e46409610040380940129400340ea0110000030306828140a022a0038014201450a005400304008030b0038680c004159a207110402811595803a12102060310600549003c5140d604604089000340c0e400e03100c01c0a954000c05455011501d540340058000e9001c0340c0c030107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 246608983 1250 246607733 246607747
    0x7171603140a1a1602010e0d03110705120309070801050405030706092405100501050708070b040c030c0e0f07020309010215070e130212070504030803010504110705061602160f0b 78
    0x40c41c00002e004001c003005280ca03440300e80f140d440215140700d400100c1c05511040401d0208034203903020950a84c034203600840c0100c0000303019070003604150001e40500360070800b003034940c1031410505240c142407061000050141c103400500c6840301400f00d00c4024049801c25984403a5203200740c20000e099250741d031301281c041104044100d1a90b404121000802c210300490b5503000f000203686c4107051400c003050000302075010b24292020144c0005a4a00385001c94840c3c07041c28074014800c84042c2100e140100000d01074841e040080c24003030300d2200341c5141a0b440354090403000390958003998014000000160b074001160b10103454a00e511202984810708280c42080107683e490342d20095103501542c1c42051940541490413003e407110069484029069640d40306900010340703140030401c0140014100f0fa00100e2030b4407192008940b510849440302030034110700340d4000d00e11b0b204034100043c8081e0704000d54000c0c64614000b1518052600c0b2400c000352500d48617104814101084039 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 246610233 1250 246608983 246609023
    0x3070b0a12020c061509150310090309051903030807050405060711012f07170601170c04090b0601090f0506040303030534110115090e0a060e07171603 66
    0xe2a0b040055000b100d800d41130420607800c038505c1c00951076010780c0c191030000e103001480c010b170596580c07405000f4207030040c164140c0b000034000e400c105030180140108002516101d040410000503c6561448007850440c5801800010050191001c00209000034890b80c2d07113131400c641d2425400480d1149400780c20005840d10040810b44825030114041010811042ea9000a494000c00c00c140c565079070b2a0003040141315441d650017021507120700c0c0148611f00d605000080c2a035240422191003070410030000d42642e03030034442296841404414070003513580000080c0060700704100e80c0c0104500b40790100d02c07140141e10002d01056142c03008110928901c0c1083d01d15082400c50043c9402c910700414000c403054400c0c9000010311401082e030741c500042c070420038811f06c0070f50b40c0740782c1a103080703115405808a0b202e5015103000d40005100050718900c9020001480607010b0040c03a8a00085c2044445440c0309400054116200d0500f040743d419401800740c81d403200000504070561020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 246611483 1250 246610233 246610237
    0x130f0b011412012307030e060412080a090809010c0606050d0f02010f18061d090a0501080f19060c050409050a02031801090f02211006050f03070b0a1202 67
    0x14001004210010400280c01402504910001e942c5040e021101505140c00c881201c0742028a401d044100c0f106000300e00a07245800074414500480c4120092800600b4141c0640381201c0790205040741c02c1c0a140c100c0d40c10340e800040c10030100040803031500c44003010712511443c01e04014251580104109003a40084042d000140c070080380502246095090b950441c0c0d03040e40030034946845840158420103000e00700c80200c80c14465400d181000580e800318402c00302000309104040c4400079610741d20b140300d06c11942d544012445514051900d0308240c0f180408402e1a000603000d8030400644070248952654881c0c000100203014107001c03103140c0225044482c2141c103050601000c00b5480e0081e50051400c0e0050701002e122041c0c0c15030803500c440d81c00030268095000d41d100507113011500031000b075a200da0704ca0b2015142000340c40c01e0040d902d0f489a540ca680314000d110718209850705030050300064005044490070700d01d042d4003d01641c2c8402c1e04201e05207002018146180d01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 246612733 1250 246611483 246611513
    0x14120613080f120a0b090f100302060f09040213030c0b21100807030807030801090506220e03070605041203060602060f0402040f09151109010c1b050a0e040b010905060913 75
    0x30340450f841c240105490090b21503c00440d22030400c0e400810031014420300a14000c0341280c0182800a203035500f403001c1a0040800c815104100f448640b0031902e070350000744a0306842c407800c0c0e040c1900310318086550901c207411000750044240058215a551030955404580042e200300c0f02c156150b40b5490310141c115041445075000d042e5000040110000241440318031036210f80c2c0e40350f80c07604c0240c0e0803110b040700d00b9640803c1401c0c118411040440c005800d03440520004035000e44400e201a00d158003c050803940151340300e0400092000d4001010707544003203841c06200b000d103005e600a40d03409000e0016981e110440c1d010908556465208410750404810140100d02131403c01d0b41c00e0340c40591003403c1050030a03e28441d414035060480b05400016111032012181030f86804009040c0584003d07011120b0a101041607075031103000900824461340300014528252602002004069110102490800042c800300742d540703020a5520000380d00480d6041021030074441d0b01104070031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 246613983 1250 246612733 246612757
    0x203120301181812020a031e1d03120c0d02011a1f020a0213020405030c010f09060f090f030b04170304020307050d06150806090c1806010309050a0c14120613080f 71
    0x9032410144c02e03000b150304c400c458001d4030b602101807002d4041c100220313001c421850004000c02100d20442c2d0700516031029404016040354290401d141e85020a80d0044c0d403441140d0340030030070358090a0b80c24000d10b02a40d90340c031700daa0b044100c440301041031070003404000115846000d8540c402d1038420043c0081494004010204036410103040800075842405440e0103801299820582075004103040b00d00702e00300340d450800680c54a141104c02e01c40035040202081558400054501861001140a1401200007510b070381002d00c0c00a820355052004030100e400180f0400002d41e40204044045036270a0341c1e407411000301031410f81d00404251034241007606e010780300400d640742e0001e5450311905d40103085034076103c5d040040007a441100c4101981d56030807c000100d0a5220b508102c8501d44100d00321390383e0b0b00f240c0c1c0c0d4007202285950030040c001c6100c0303c260021890300e02d2210f88000034800141640703050520030070b608034120302e4025211170f42c00103099039501052022514070707030040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 246615233 1250 246613983 246614003
    0xa080307080403090608130b0a09081b01150e0f180f06040c0f03080306060c0a0c09050f221205190206010e01060203090a06110309040903080402031203011818 70
    0x40c05025020403020750301940020510030700400c065000d80c902c079000e07600b4551084210707403840d03403544407810000b0072891205481e0182440010700480c058520007010f4900506140c544030074443c2110310084020842a0702000c04000c004900da58403a04010340e01e803442281e5861050702d0f64456080a81e1986d02c1c4540300c22002010b002050349406684104401c6500c103642e0f0002113440a0540409000c1703203010408070f206454a40d009080c1c192007038040c0c0754100c1d1326480e820800200c6502000c0c4403520342c8100705006101c00e04096004001e1000208000c1180e0442480c17050300c000b000b0885103208841211050140301540c0d100304130500b4025104c000084000c2d103540c001e00c60a14100507103400072506134000b000340e07060030401400491010303203000c07021140d0741c1c3c103034081c20900e01081000c114a034880c0d00070307010700318066241e40c405410b003441458074051980314a02d946e170005100600c01c030140c014500c031032504404030104007040803080d110f404c00e0b00041300400d00500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 246616483 1250 246615233 246615241
    0x105011809060617060402040c020d12240821040303050909040c03061109270f070302070507090e0c0904020a1404060909030305101212080c0d0e0102190306030206120402030a0803 79
    0x10310b03522547c400c2d90144059120364005980d110300d00744034800401c94201040c001d481c00d80c0c0c8038001d04461800381c6071120032a482d00b04050340d01a0403030a1540c1148641c40c3c0c1c00008001c0508003d1f848000c034600c0c162850f00c005086d4041c0030001440380c10b840300401d007480f41f103e03400d80207507070803070410001c29601c171443c041030364803000d03501d800b40c0700030001041e20341200c404009120b540255400b505175101c00780007000604c014203100074546d09000c01b501003030041150b8030141084413000141c1610604826161008132040c541c482c0c01207900b0000141c40b035404100c125100c031051001c038001a0b00019018103c0d54000c1d0b800c5500c1e1500300c806041d8150041c50140340001c0615007420b484041c2c5035881d0503078500140c0450448800e14000358401d4040e15400b00e400c00c034107800c1080b5503600c4001d60307401d030522040c01e81d00424928030030141c0300c1c0161100800b40c1400c205103403130756011808a000d122403070f0824009080009003552001e0000c0032a656104c81034950303d20f0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 246617733 1250 246616483 246616529
    0x18051204440304060e0405011203032013050a090c021209030f0307050607080f04050a080306040204051807030606050c0c10111005010f060903020102102c07140301050118090606 78
    0x141c441c480c0065400410b1700c0f0241080c2c4900350684000d604e03485050303081034400364081c01c460041c00c5050280b80394080c01c1310780803401a01c204083c0c400d8842c240e5140c071040102400e4680c120403006c1e481d111070405966000035039806403030f201e10459900c0f40d0490002a0400c50340701440c1282c3d010000707085007000030128900380300320030700c0e10340c00a107850702510f000c0011011640141039900c00c141d8200441d000d80c01555014030010301c098036164035040441d85021000004100f0044081e050084c410b4145c00f03840301811861618038108407140c0030142c1d862500a02d2180540045104a2a001d1280c6c0b05500c02c0b000c60f10440314030041048104000341024402d0b00e201c0f030760824001c10600d128a10080c21079805078018420030380721481c0c1c40700905040380b5090311300620280b50000342c0e02032b412030082112400c02400078145800750700703100d205507020800e1103a49058014040300003082c4404c0d2003c0240c620004140d0220b181c03a400929440d040602078504505215a5003c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 246618983 1250 246617733 246617737
    0x30302010e10020f031f0306020c060403020c0108131509080f040312030213051e0a0b1209190b0c0d02040306090201030c080403050906070c09180512044403 69
    0x1054900846614021441c116403c074010609940004841000401c102d0701a40243c0242d000c5040721990a095484d84c2d000c00302d0740904034005542d0840000c1000b4540c052101d0301c8000c00a00b80aa118540310350070240040b0b03020002840c00009032660781841003654444c09003103600c600100c0d69000400ca02c0c5201e904984003c0759000203101c001540d2074170900035601c1d503030080000c084074241844204600d030343c0c0c12207401450b80410240000503986014151004101504500d40d503861120301d0390b020b2500040c94900541e100307107040c00300f03900c04404140045800082c40515900d5082c1c00021a10920f404035040c24004580441400207d0340445000d030301c00d072000c000308603440f802614000d404031400340c04942d0601c03814400d41000b01c014911070f44100c50045801e51203580d0f07402101c40b005681c3c10508800d071200400c000f8100449100c00d203030b03841d0450a081c034208800d140e50500048030b90b17000d01300408080750001c0784184043c15a200020360300e10030104010b02070307580d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 246620233 1250 246618983 246619001
    0x40905010f0803040b12060103020d06030605060a05060f0405220603050d030f1a01031806050c04171203060123070f0b0a060503030904090f080309030304150b060306121603030201 79
    0x10304a25000064900000044804441140301802c0c1006e100e541c0f00018524000e16860505408010410810a891040c0b40145214400c00260350401e2400e0250740c0400e038000b980a80d00421004065550b0b0406403801c8900480300600806054900710403003120303030040b07800558103203440401000b4000c0b40011500326103a0717041015000030b03280941076401c8000070020705400e40310045a20351082d00400845040000380494a04180c1d581c0304c00c6400c125624007480c0da001c103091202005187e01c4191084c50b0740300400b41f0f02216841840580300c040c0030181405100c8201a04032000440a008211041d411842d258152400d10340c6520700d2022088039544101e8001922000c183d20410040d03401c042c00550400b00c0f5182030000900031100c065885462484201e00011010801180304090300806142c9a081501d0807801c840b42d4841078002440c240301403000a0748514003560740c0040216403043c40c241440c4070745414100d1200440d469904844804014550150020400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 246621483 1250 246620233 246620249
    0x90d021804060c300e1e010e03130b0c01090609050d030b03070807120c080d120605010206130605040c05060d020c0613030507031103090a030606050102010513020a0501050f090604090501 82
    0x804100c001040302c1e50100800b1881c0ba132030b00002c2c0a0702d42d0301000c1480e400c0c5410010000350f000d6074405550320307003258100760130a100c40c0301c21400704500c030a02443ca0400f48010055040c64068183c00c00702c031002c3e0040c3c003c0c9010214818203107030070941100c0350302034102c0b504100700195800c1040d210300581e803003c40401d003418540030150070700180b0082160100c0d0040c100c81402c0c1901d44420803c241815100d5075007504011440d104140010507401e42d450700c8140c030880c07010341340006032403407540494155040401040b1903900c2603d2003000c02507000000140700c2c0c0c1d6034070b80003420f402a0740021342c0244001c614010301c109542e00910003042c40303004441265032540d24138100310171045401800200c003409180c000030700078082683d5040221065a052070b602c000031801d401c2c0785034800d0718525180d90080109503020f210f0030740c005603100c0301c40e44080b0964001c11020303015441140c4c10003a0008a0507446071410b402d4034280c035002842340307a0b030b15500c40390a00905000e0184400c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 246622733 1250 246621483 246621491
    0x1207091d040803060409050c1e0901060f0207060e1c06021e070f021009030f0b071d030c220504050604050c060a020d0e060c031c06050102071802090d02180406 70
    0x900003240000c2184200d9018501901e1641c0d603400f07004c050500d001d4129581e10a070f01780c2060590740e450f105000320315080d1011240c54200000c0204030641a40303d07400703011481c0031051805601207011002c4e254a0306000c280400341c500410104010901e004140304034031381d20102040800e80040a40f2100352004c900016440c40030782c8460f1252007801441c4401e20f014880044c1072034840d00402441c5414035540703003a901e484015011007840e03811602d050000e0104140d10ba0041903422545484808085418a141d03000c640c0d40c0c00d510400030b104400f01170002c8082c002c507442e400d03021041100700b40b0441c109440d0095480c501500c0440c0c6a01401a003181c040c03c020091f5103884016500074003502c0b019a0083e1141c284264449401c5501040060f18480f4100020001211031421140415078074100c10000c031241a084241150031020042003e88091401c0e4100e40c0c0001c2c400695891034100010950f0b03110281c0207401017030840801c0000b4002c4501b05219030f01a54080c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 246623983 1250 246622733 246622769
    0x100b1204020f03030a09180b030703060207020109090903050304200a0801060e010801020f04030b090316030507030809030405011d040902100206190b090135010c320708120709 77
    0x9070300c1e80145c082d40e40000300343c40070400a80038603200317010500100e060002000c02d5000082414074040750426500141c00081d41402c40d603120706440020181c05c41c2c20018084641da0082051101400180c00c0c086407051030f0801c00c1d08001484111a8000c0c981a401c0b55102d540c507019181314410f829084d03072a1800000c48600600071a408240d00c40d03002860703e421070382c41d07810081d8050202c25580c030080c0070064100c0c800c3c2c4030b8885924020b4990300e807214020729004001500c02480615290814001004566000301e65031100036588100b00d504c0c0d4072888046001040da540c40a0343c8215003500340003c0603004906180a85004ca100c00702c0c110401010606541031003141c03c5d0000040f07801080340c8045e1801450f0410a80408a004803041c100d2011203102c5071096061540d55401c0403d10302038000142d1140440c08a046484101502900c2d50200d10140b886540d5070f540001d0507010800701108507540344480c55001c01c82410300e1000103080c51914015446040700c2810740b8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 246625233 1250 246623983 246623989
    0x19020a090501050306011208041511010b01020f0607031a090403110613050d0302030c0702040509031305040e03041a1c05010f05180105010302090a030c0b03041704031a100b1204020f 80
    0x501e060350805001481c0702d03440c07d00c3d00512119403031403e40ba004400d01012401e021118900c002c0300081f40c1d60321100c2d44191007101c0c01c4030001d100d141d05542c01140c42104035400800c9681c0d20030200c0c240024000f600c0300d1420403c2445404040c1d001c01e201040108140d007103a81811030001c40001c950143c1d0b40c0440341c81403484d12200c00303806584070482615482c0d1180d00116401420303001140e00704034181e0b02090984a043e28020300f181c1010a0071062608410440402001c08075010320540a80d500c01c40c0e01c80c452070182465508050095040444210086495080c00d40c10b1048041d200d405d80900202020f010b10102c60101c1d15001030185001d002003e240500f054110b40345918020054000390301501415420200a80d00003010441055002c8010aa90602e0640d2450203190012000806207403c10282d0300a0005001080ea40004911803050b56200c10800d9159545481100d00d07036940300321040040042e14699500342d40d10814001c1d8420b44109a84c08154410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 246626483 1250 246625233 246625241
    0x403080a17010807150504080a140606060708070605070504030f0b1f051f1101060801020c06060121020703170a09030e01030608030d0f0605030a030c0c0e0c121819020a09 75
    0x8410301c13a030154500780115414440804591025400c10601d400c2c1e890032140c1c14140466000da0b60154941039002c8001784c24088030742d1040e4110780351807400059603618151805000800740a0341d139a203000903610b80c0180d0440d4050f5030800c10f0b02c1401d100514041d002248c0841d2060300064000703803110f08910441c440d0400f541d40041c954481c41056000e50b500402c1d10104000c100710485a103d10b0440c400e100c0c010280c078000d4005079480720140c441d40e1400c14050030240c10001428510110114184481c82a5080010300541d445000c1d080c12202078a50060781d20a40c0d000b0750501c08004595441540c2c041c0c840e45405044983c01e400544c2124654882d01c0d45680080150098140c034541c003507040030701031210008004ea200e40220349402c04200f02200840d2503c070018091000301200c0400038251142240d42a14021241c0981e901030100081e105501d584046108518250469441a4400c00840d46410125150307050380c0c0440c03c40507802621920310204500b04a409 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 246627733 1250 246626483 246626489
    0x1090206070605040501111b1507090b070f080409060314120406210e0619110702010309260414090609010b0306150c100e01090201020d080c0f0403080a1701 69
    0x1040d0708102050b2901c001070500104100c0e81075680303031882454070822402034590308030445a0f100c2d26031034000300da500d80804a001800c005100400f0000f103107500c80a44002d590700c07106540d80701c2849244c0280780059070791006146a00110300450f6183c2103900003003c580c050088102c42481516210707407500246445805940e90030803040c40500c6c0160b894049a2031400d0b4035134640c0900c151880c0c1140d400901c0038136541c100101b400014850201c051610b00401c020400002841c254103c49610412400034140340d201c1b4041400d2220b00500c550942c2650484150045110703000600d86074000c0c0650000741d05405244032090404200340e42c440e01c1301911110b0b080e4285030f80c90320075070030040082c0e510000340881c091982141d1800782400c0c1800d14000d10b501017054040038191641040c03640c007168501940080582c0e40041c60201808040c00c04c51a00e0319001c0c1003441600c1404e614029200c1e0010b000010003600304000c21080625603030b030700a05911140380001c10f142c284 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 246628983 1250 246627733 246627739
    0x100e150609070e040e03040308030a021305030303191503060f050f010f03020904020f060f1615020309030306010804020f042c0c03100c0e0a12031d0112020c0102070204051f0602010902 81
    0x38500700c5051961010b85c08480440c210b0f030400ba901e60fa0082c8603031003107522102254000c5440b5402c9030800b2154005400c084000d14218602107c21081684010740495050f41e01d4921030a80c4007507140b000005160055418013030080511740c0039004e003000b906c1e80030309804500000910240900740d10403c0d25401050001d442d01c50381c007044180115585107640c0000104003844c3d11119400080c000720340c030700502002c5100307a4104254500303c400349180e50f5900400422662000110071a80d000800b402c0c0005d650303c036400070980038410b1008164202d8a08240f1301900342010b1441c02e98039160301200f00c5180c000d500d4150300c5a200560b0140c05601c50042148240b00c0c1f42c20600300c0d41480d14180042c2c480e070720f00003560000c246d4042d40e005415207031000245a8441e0100a510b4150f00742030a81d5192100001c0c488281e903608a00c2503a800325203241240000e404030f80d40203400030818800d071b042c40740280c0858840b4a54080c8008030f5562b0002e052401802049603280d001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 246630233 1250 246628983 246628997
    0x610050a060c0602090301021204050d0f18120f0c06180b0424170a0507020d02010506010207260f030a0f0804260d140a15030c090e100e15060907 64
    0x540c0c0c3d40c1d4040e411010f061070f4155000c0c481c04084a048441d1140f0950044004140c604021000074008100c4400344030100120080c0000800800c0c29030b2504136540f03002d60041000c2c59003070941c0301403095440140804100310300061080c3d80444445150300f100082d61141035a42d003000e10091040340705000b04603030b203034500314a81040b085041c00024030f036003084a000068030240d5506080e0072964141880ea89205000c9003550402a031000108d580c00200075074145000080d50392007082c401e000c5100080621040320b0300701c60b0100d50103000c00300c080303c0d107040300c4020003a1642c0100d0103001c006140c04412071107981c071034103030b8500444e0858030118901c194621020702c1002c00344031102c3c00007010440b00c144d40380300384034007550517144002d0710000b41850b00381c4d02c041d1003a0100c0003145015040342403000c41d0541988908030340000000103030f0380c50440055800c1a0400c0e082d4200300d4607006280900b0000410001c58020000c2401e01031503413954100314000f10180c800b88009800c07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 246631483 1250 246630233 246630257
    0x100e13021b0102190e0415050405091f090b0606072d050313170312130f0507080a02040510080c15090a03150c0309030f0e0f090403020610050a06 64
    0x903900a004900e40000640700d0045114025801d99001540740344100760181a501c0b43d541d0700100041c0d03101c00c101c0703042c424160660103844181d80c41c2d0040c140b003141c0c0c810128061850401840426420700b0725410150030380c2c01c0013480140401c0c8815220780100f40c0014143e0700d881000c689440358084161900b20b66040401000c4400721041210121000d00c04c2e000485c0080014141c1c502048002e01800380c1040d82c44d41540d850760650141c10750060042000e5500b42060181d03000b10441820495038506d414035001d4440300c1c6002404601909034042403060001c22a8a80360f0b00a8800707000c95203400c100c81d8050f4005114400c2c6940010100c05510714100380c0c0e10007c030b1845007186040940185c002902e00341d1951048544102000051003081424016004c40c110705003000c00054000391009070910140c15141c104208105085a58603034600fa840d0b00c5040000c0c00101c0d540c6020728000c1e5690009071814200100314140028652070005007602c19251159281c1d408600 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 246632733 1250 246631483 246631519
    0x90c090918020a03080a020f0304180207020a0e0c03011d0f01050f0a0803030c0d0608030901020a020121050c07020306361c0201020a2312070203091806100e 69
    0x1094503150840e01d400e8075a01d0050b0f90f07000461405140100343c066541e4441d64406490004001200203031a04148003c00807030100c4900c3c070a8881c01e02201595408641c40000d140c00e845410401d01c1c03000741d0b0103100d0412218400b85058498175441110002c01da0389140580c0d2404680f48030b000b014900044c0401c0c2040c1e50058000395014111a0381161100801d90441e00304a600b071f0841d08003c40d440242e15814025240186440c1000e140f0b00b44130200000c0d11000d19020180c1401400f01484401c100020414070380070710055400c02c41410a00940d1304240d01501090744a4800d03000421449110182e0b25009495041200c448000000b8010580301080c09070040140c0504c00ca50b149002c1403200080241209500042e40e426101d040501046140780d02980c04000006c0b050b40d0784100301045a000b14582ca040060035a03e090040740365208102c081178000c800d04040302d52000c16418034074010a0210384e40a28504018070442d42500e44410042d0304c41d081050316146c0300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 246633983 1250 246632733 246632741
    0x151b03020906090a06110c18270609030301030c0905100509070c4806051606140105030d0203070f021905030d12050c09130c1b140106090c0909 63
    0x200c000e44050304003c0a88005603118159034803000124090003000b80c480541400001509002140c0c00521741008103030340000c1180003052010700841c03a0000200c20000340125080000080041b1111440c0505000d40c0b03a030002c2c070044460321103508020605910314083e132445100340c1c2407080c2015142000304443c02c00068082401e0214441004011410240719089145000075203011502a804024816441061a00b44036140f421680000145a21101744211042d5280c4691500000e1446103001c81920f40020201803034942c0507020103031020315007412584120191003c6001070402030361a07220381c000c02009500011855001031600c1000752040c4403435408210702c80758617070010a10f04148402240d01007041180c24200045590082c00d902c081d45002444c1031060b4980802e5041400d003120011041e1955020201c0520560301c0c0b11142810700d00c0c401d40c41070310f4103164801400070001500300f5420100701041e484000d010b84020a501a511200b00ca4a420001d000038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 246635233 1250 246633983 246633997
    0x7141e041803030902120f120d110313120206090d0302070510021b0d020c220b090c070506090303010b04030b0a061806050405060102060106140f160f151b0302 70
    0x300307a88121003001180512500145035110b500e00003010040c60041000c1801221496402c0394420014800d00542c0407540103003885260320000d4a0740926044071000e0070070b540510960220120800c41a8621034442c0c00c030316401140002c40c01c48540344102c1c3c44007001c41e014040307940043c0804503158401e900810703550b40500140d5461800d042c0404050f07034050300c5000c840144001c07a82c0d2082805010805004041c1d00003003103004442404510b0944000c0400c2e03581c103c100c40c001000b201c2d15000054261f000030503007549891f240d82544029008400e00382c81c0d40c82104000340001c41c0001c01c59042c2ca0054003c10b050a1850340c8154400100400b04501141c840600180a2140c0e591120300200c1281000c1a41e608003001c0c00104e60000705582e04541c403030001000039a4000586089408030b1044455452900b070024503128410200c05c140703070340050102c6006001c0780c24842036826119025481c862070024030311000384c07002d007103940001c803201540e100c015030f001b54024102d07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 246636483 1250 246635233 246635239
    0x504030809070305030931270224120403110f010203090307060e0304030c090219020c10050d090c090203090105010b03010b0909150607060e0f030c0309040b030705060d06060207141e 80
    0x1034804190031f540f840c1c0e5010072445881d030761182030f40c94080ca0744030401000f001251446140c0300c810f40d00003d4417040075024a607030180455040c42c0140c035844044604240880706c4150b02820b092500070100c032094401d400d010b000354908000e0b00081802186d0064043c000203505140407601d5450080440041e10700c1948000c110010003d03658940110040071030a00050b200ca00420340e81c20215030300d4030312100315000101d42c0a03060707441c0040c0f08a480c4503403401a0322507007801108401807a40f6580a1702006207000001444841900111700c5040b041c4000e11141c0d036103241030203842c0401c5c05400d46505041c85581a14100300ca460b0343c1c000c404407a002c526540c40804103007650b01014003500c6440d160b400c0106841810441520381d00c801754011843c089000103569200d0052502440c130603522105803201503501048850007a110040030103550319841c5040000504c0a841504094024403800080c007805a1540310054600502005161030301c4c41c00000d4210034004180394 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 246637733 1250 246636483 246636529
    0xa2019120512070206150906010c0b04020418060b030115050105030a020a051620100c1e17040e070806012f011b14040b0f03090c030a0605040308090703050309 70
    0x80d40c03074004424090000c3e03402405150501c0c0103110405690081414014210070042c4401641d0059090507910b030843c043d03500c07548030380c400140038000300300b8410140558540c1c84000e0000c554000f08586d0411070081000e107021040c42e102480c00d6100c1c40b07000c51800c2c000615150030580040084210a1a1162030300605100000350301090a90944d24000091a0f0341e5900c00140201142c0e94002c84074555031040401f0010007050311050001c1c140000c00c05680c201c0b840351400e41e8501c0c1e9014a81c0781d0740ba22034000c59007080e0803610410120750064004184c03050300845e1114010003041c0d541710100c2001030044000039481040c40d484400450005a011540038480c0131096860401c54090420040200030007451981e04070201801c0108810006c400301a800c607450308000000c403a803240d071102d40702814098240c00705609802009450f8003000a6540007a21451280e142d0200070740b121500030ba0f40b10694040149190f00800181c0424075044218a101e0030060b90030b07a03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 246638983 1250 246637733 246637747
    0x13080a1106010b070b070908061603060e07080906070809060a020a0e1909060806090712020a09020d090614090a140f010204030b0a1803090b07170a20191205 69
    0x10715140c0c09902100c6115004a004400c001407040340782d400c04058681020b040b0f082124071030300d80e14041c0211241101d81600c0070519802a0081310041200c100c00016500c5c0c100805070400408039844511405458001044a80520300c0240034410070001090507030303185100d0f003000750320050180041c0141400c643c0e0032035407010385104c500808085200049490800c00006a8035960049c401c15000542041200c51001500c3e800319401000020008000d038004190520a00d801c280c41d104d00000c0d1202c0d460405402810030248585404c221840640d40021503584003524508407580202021038041003c2c100c4140040015005950000b45446069422039106900444203070a000082041c900014800d440c54000900301101d84d68005036002000c0c00d070b00d070080401c0c0c0d080104111082c000311800540d1050440b500d082d0786c803401260040e0108070b210515500c803d17200030035150364440200b1002e00c0f0403840c4800e100071654560b0707603003c8100310341c01840c10000c081c0542 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 246640233 1250 246638983 246639017
    0x180b01110a08030106180320090109060b0d1d120a0e040603020f13180f0203010b060301060507060203130c0e0f071b080d02070605011e0e1006110c04240e13080a 71
    0x1c2041c400703c00d03580c050008d503241d061058080050f404462403919200d010451004581d04a403c00310310304100088584a26031140d644c4001d1358580365861085000c804400801c0300c000300b001c90a10f03152900654000d808000554500d4040207400003c290080003a0341461241c0b0000c01d070341144041000d030b4007244920400b140710042a80c900c0e5120400d0015414203110700d904041c0d0549419186606200f0058440e210b284402001e15a0020020740000450800941141c0d031061050501c00d58401c0349888100c020740e1200c110b04495800318003003600848100d1480d900d401100b400300c590b152030f2011542c0248031012852a0200042c2000600707a02c982e9020b42031000c05d600e090705a071034540a1810b0183c02c40204030a01d0001e200b600101200c11038101c42c11882c2c0f415044d840a0032503400d21520102ca1a04141440c1001a20140c441c2c02c649403107a000105420050b80ca4001112404060f2800d64104200f0750b01440450110340c000e081074030043c10544482000000c1c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 246641483 1250 246640233 246640253
    0xd09020301020d02091903120c030903230c01020705030712020402071b080d050a0c060c02031306030501150306030c0b22080a15020703091509180b01110a080301061803 74
    0x208100d142d00280c0f071072181c41d01860381c1203852920101002c01a007140d4900340e22a180c005072300140400440c0460400d8850700c00348024561128442ca044558081188010111100c1025150040300e8411505520009030003080b04c4008005004651400e00e000414440f201c000381d800039020050040802c14076138940c680000d1401040d00d51514040d01e490902c85101000e1040000412039000656440b80b01058019040000054880ca5207801070f89184500c090310040110b91a81c000380080c1c01d68016412100f411184504031045948124100c0d00d007804014441c503010761040c010703405924041c1c41c000074218080c0b82e9a5072688184480f0a00541c0911a298085441c8104000c940e100107412401c0a040a6003080c01c50740d4041c022440ca80540c0009080b0600b00c2d0801d00d2003101d08a006200f4100e14002c00030fa450f1000e005070078502d02c9140400c4850075210350b007480005a0b8124250020042030450342014405c44803101005485c0c10a0340b00c0c4000440401d1602007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 246642733 1250 246641483 246641497
    0x31104050910031209030b0f1302100e01020f0f060408090301060302120c031005150909030f040e090607081603020d060e09010f111e0903100905160801020910050d0902030102 77
    0x4009411440c524101130880c203d1a01da000700204d510081000425500046410810610500032603540b105c44100710100b60100195125201880710504950400100d2914480c00c1c2d09035007504804400055a9104901d422841984a64009408156001e010b0401e2400c01000402c40b180c0e41c0d00010740010a1a45541e2030350003c1406c20103e180c01c11501c46016190241846145005011150454001220700380660414400503100010030f0040789d00c03a0541103d51500c0c0c41c1c881d4812201c2c1c407812a0043c1051003a40081202c250084a40c40d10074080d00e03082c00c1b1031003400072080307010b0b40141000701c0405442d9440859a9120130030000d1041401c0710001410040c0f441003141903621403403a44520902c1004400410501e501e0081c41011403070311840c1c1d640d844180824030306a40702504a072a02d19041d62007042250100b62501c00d41103480207000841e8540030309508270b11402e0034080c0c1c41305005c03d4118443d4050806001000550480050a403c090300031a007668480c0c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 246643983 1250 246642733 246642751
    0x101b060b030712300f050d2a12050f041b091d0c040e1207080d06030c0303080702010c08070f0c050609100c03020c0c04150f080a0b01240311040509 65
    0x1061095000c1a9044c090041a461626840010618440142a00d020340c011141000f0300000c1c3c103452440300341c01038800c10300174142d01c22032102c0c1c4840305074008000e50900350010f00c1c001040940c052040c05000d0080704207000b01140750b1a26034580000b588460b07038405402c850140001207030200d52051010388030321412030b26100c9080c22007641c1004481c8040e0f922071441c0110740d40c4002400106901c212240008441c0d0320415402c020090340990880c4440c03080c10164007108000d4000e050b541140d100340c841d01c80e41d03207450703000f6426107150f00c1249001601c01000550500c4c490502d01c1010456800c02c000d80c045651299810100b04641c028038076441903007071406480151052140300e00062078110b060040669106844101003041c042c0b04a4031141d41c1c1300c2e00000d85400200514290340d03441030307503991451501c1d143d6840841c25076501401d1030000810036074158070005d894500030581c0020009441c419402050350306134003803500d4420b20001c969902c1d2010000d004002d22 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 246645233 1250 246643983 246644003
    0x503040501090b03070815010e0a080c0103180b0a11090d0605190e06010b0f12010e01050108100b07060e160803090306070e0105071e120806101b060b030712 69
    0x440005880c10030035520041050f0001c00411400d15485407810ba04084101c88000005600200403252000324140e0740d58810300740c03800012903410007da00c0049010a890500c4580c101e00354480036107020407030140100130380320002410b1411590158904c000c42000b0340d428048100c0103d410314081180c104d600b583d90324203110191901800301d01010303101110a00c0907106400c1c0032034440301d0620468840e65070205801c0d00011494082d50f42041100e40b1000b11580d44102e4550b09400030310440b03012585c0d40d000720301304019130388151003a6070203840d007140740654590f266401010300d070200d207420340260a200364040040801c040014265400110f4441003d207003014285440038108100780003072140041c0d8181d03003050a03a00c0083e044180050340951408000c4003000540000038003580d034044041c800d01da0420442401071400b5100b0091000c40204151400b240c00c01d0f202c1d039142d90740e001074400140b03244c00011005001a0a85030740c1d640d13510709070751030403c9104110754441c10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 246646483 1250 246645233 246645239
    0x8070602211305071a120c0904050403020615151206010903050708101d06040f0c0819060b0f03030301051311030a0b1008010b070b0a0b0907030c030c0503010e131a04050304 76
    0x420800703074002e0903c030095500710319443e504a400b17500ca1042c1e4a14800301d40000100c0ba11158000d9807864603000d402440a86800d190080d16814112203080d03c002002c0501100c500380320210b01c0019001c00b010501d4405000b60040c0c460300001c0051341008050300780800001c80510402c4000c00d84640108082c81080c9052000d8541300447c00c207041c4641007110300140000661f094200303401031115000015942070840c881021034101d04a10b00ca100d14660b104c862462003a400140503031000c0003881e18007010004121000361070268150300c02e200601c054903000040425160031410009041c0b0fa0055600b071164208480b84414281c2d2901c564003103040070120502c2550440c601850a90b04001e9107449074090040064000b21032500081e03190781c4550f21031704200b0b00040c001082c902c0c10b508000c0240c60150038803000a410220021101406070703055a0589c0c0e903500200025907038240c0e61521541c4141000e845c41402100c90000500025030500d025501950255954600b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 246647733 1250 246646483 246646493
    0xd050d06140d06020703050706060303090614031b0c0a02150a14040305030301090b01030216110a0614040515040b031005040501050f0603040b091f0f0f050103080706022113 76
    0xa00c1c0e44040440021901c03844000e80d80c41503142c0b28143d1000005848000c6420200c0751400740720802031501e454190040f060503004074582c2d023243c200b603480c01021900080c07a1401404240c5000041240030a003403812040840094803440401008a60403401a80c0010709581c0301d0903030b101d12504001070405a095400702c400c440828a4144d498a050b14590300c10b5a68801482180360f038550b03400201c00306a1280d011a441514408144941c5a0303050074104488010303010b8051085243c81c8000481500516040c0006451191214101880c09060000c40442240302d010104020040401c3c0303c14280041d40c014001003c020b0411400c0c082030000701d62068004a10a810a0040d420b0683c0d801d01142e504c1070307000443d909a03071100850030303107049400288141034075405d5041250294142c1d1020f210880c0620091100401c1042241c0c11135100f0b00014082140c00c21812000c502039070000c02c40000d44044601d507030b00c031090310094000b80a40f92140007140591600302404 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 246648983 1250 246647733 246647741
    0x204060809011b0801090b0d150e060604062d080708060106020106090203010e0c091906050d0f05090a020904081306051c06051e01050c06040804081e030301090209120d050d 76
    0x1083e981c40300b410071071020041d000c034605101c2c030742069480d2560701e9520740352085180c13103142e44400c007458078043c4499000c015120416826100340724020018110389050b01840080b52008d20482050700d01400b09030701010f0103075080340b41c1903485040000d61000300708048001003940401070400c65050410003400e41d10a40c0c8030100c55801403006001c12a0600a807030703041a5001001503031100f0201c0416150056000c000c03180d00950341001440b180c1000003085000c254000030000011a519200c01302c134030554104496903c40e085040041c140f00c0500340c0c0203401101d5042c01c00048591404d0b042d2000e0300001d00090004c585d001d0081c02482c04100a451001001d0055500303040c04034801100b019808000880c50640c9040c2907400746084896001c417000a4a00c546818103000b00e0f50342c018881c2c1c5065109050340e8100c0c02c48000c01042011441802541c910303440c010603100a5084210060382c84400c58001c401c519204110051048200e601d85a44130598416038208035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 246650233 1250 246648983 246649001
    0x506041401050c0415020a0c09050a140103150b240403061d0c060d0603060501090902240d0b010e06070f0309060318020409030212220909021804020112020406080901 73
    0x181e03050009204039a90100f00381c1d019161030401c1341c840c0d0404018124609803c1c070001a02000b42c40c0000705034220b06400c801c2c49034000300000d0004216404200d45501c0307003480040d00c1c2c0c0c0255180202d010350260028016134800501c04002c3d1007148100d40c40402d90522854030380b12001504000b0040a4052880030f00843d0381c551103100d0090305810b490390415070880703129080015011440e5046540310201968100c00d04002960b100c00c040c0d001012002c03001d0780315040204c0c44904410202d51507917080c0401906072410598106140800b03400d941c091103040c05000d20100e401621110040c18000740542420603d00203141009468102d461b08480101401c00350b40c454a000034080e0790000036410394001803520b5170350600301d0400050b400c03201d8400400141021603842080300038641c5101d054a2420020b42c2c0da2140030032258143c1000750070071818201294100c42c0000d0a035403003070040c10011070341c045618000040b64402e41082020502d440b003805005a004d205080b64 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 246651483 1250 246650233 246650273
    0x120c0703020607260a061701091704050d031d0d05031c180807050708061807050f0d08160602030c0406030b0a0b0f0309070306090b15010314070e15030103050604 71
    0x5a5201c9480626180c079211001403400b4010382c005c2032440c410350f800a40140500c1c0101520840d080c9030040c041d0150503403e85000d041c6003543c504154802040320100c4030000e09100080d40700755410380d04404011600340c5001c1d1101007280d80e0ba101c01a1386048140310350040d66a9859040c400002901b031072030540301c0185404405030212103506040640c1c41d030000c41190700c0e4030641c50114601840d50700102d4250042c030003403000c01e019110350417640c001c804080e10211601d03003003800312540520301a00c0d480900303a0020f10109100b00001c1030303803480340b0701d07030b205121259203a6200b641e02c255407010304440c0000d030400603107525100300c0800680231107003058014601a0301c41030f00c0c020156010a541130000201c1c0e0b80c440204608001140d01460a004103c02070501e01c0c400203049900340f085940f200c101e121298172038031581e1101c00d06201c01c601c080e00c58120448590985180c102c1d08031b6100d0600e403100a03c4500514000c500c16001414036203042d20740072081102c6480e6140b8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 246652733 1250 246651483 246651497
    0x70c17010b0102030a0c08090409030c020108010806070903241109030f060c0304080a0c0c260a0507030b062205071b030801210b040605060901050109050a0b090402120c0703020607 79
    0x1c0e83e03003c000c84445106030b01d48060131940a092010b000d102d03510b4207a80c4980380444134010190002c01014125000f600d40c50381507030740c0e0f640841d2500c0702120100006081000148005154070800301451821003805031925054010200c04407114118040741840c3c011038062060314040041c02c1c2380301c881c1d0020389044d0a2a004c001514040504000c1c4010307000715503030451900c91179020b00611340110300c19540c19603441003060004680315840100b40000b907a40c1840120000b1030000325a400002014503a1450711002070081e80542640d07031011003604030b55a0a1030114400d0040e4094002c00645d904150302c000d0300b0040d5401c404114080071103280710220b0b810030b0b5030a0444801400c030381c844410740742c0c241004025000c8020140e40c0210f0600082c01178580c46540314010a07108084280d89a800558101030349210b003e5004001c0c000c1404285104000f400000e40040c10140c01c000480c9240300000c079080712480110400842d00000b41035040020070f400c0101424101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 246653983 1250 246652733 246652751
    0x100c1a0103060e070311090c09030a060c08060f01020a0201030c02010609020f27180a1b0e09010e160e0a030503070f0b010e0f0c1b030d0b0126010e070c08070c1701 72
    0x601b28840c2a02c1e40340c0700300d03600000110100c289400300c4110440080c141c40c0341544a1900c0700040c540d103450080000d210300700003645400d1180044107401d1050f001002e41102d01ea00442c058000c0ea42c240085540310603000880b40203038009098030140030000d84d501e40c441c08940d001d102c101e00c4a4040c17580300c024042015900c80c5900301000400710224207009948150f00074024008070b440c4002c28140684504a101e17900013841c1000b04801c9410702d500da40c0e0340d100300c44a101c2c00c2d80c0c0c030070000e94042c104070966030244240c12804540a405d424805a82e07446181c210342040c101643c40e20603a900e1001004078480d816070140100385801c0f02c007818070309045082c40350300400821801e840000d1440d440c102201d0010300045411044070b42d00c1c842040003001800101c4001404600704045241c0011014a00c0196038805c40030480c03d01d03840d01103800182c1f1406800300c4203011842c0d0b24200401c1c400002454418061a00d0652042c40c1c52040742c01e51002c108408866450004a4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 246655233 1250 246653983 246653993
    0x1509011814010f05120f0103020906010c1e050c0a0b0c100513020f010302070b2809020325030c0e18032701200105161805100c1a0103060e0703 63
    0xc582008082c6407100701c0d0780281c40b065465104001702003100a4440d02000201c5007a8405a816a0310940c0e0503065901c030140191049010180020940071071200105107900c8c03084008031a541c011403c45480072548008500d812803a0b4100d24000800012048403c980c2000140020f02c00c084007080305190a1007a446a484840d600038410341a944076080203138407070340650390051f0300404200b07243d05000c4000ba101d000e2441002d041e000804104c2c4100c14a50f1285045140d0050701818207100012070401040c01880c41040341c0303c89608000c0082800d4000c81005410f510390b80700070303038146407807444200c242c50260002903500070401c001c03901c04d007500d402281c5000c00900000d41014140140c0d026007145040800e80d0102a0001c0101c1c201500018065001010a0000b4000c0010215040300181d5010b0a580f0442c40e010812803d114542c021019414605220f62056940d100c4010704205050031109100c4400180280045445080c4900d00c10718010f200301d41c40c0d0703514 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 246656483 1250 246655233 246655259
    0xf0b01051f0f0302091e12190b0703020408030a0f021b012c030a08030f01050d20040207020a031b0b04060f111006030506070e0603071202090f15090118 67
    0x680c0c0030000e650b604056014001e405940600c1d500501100b514103c06030860400a11510514440d0800c030074480100c21000c00d140111002803c0c480c8214000707038490030503220019240c03508066007084009803940061016081414640c0d0b01e614960f11002c070000c0c80d02121144c1d1002c0541c005600c02c4260380c1003540002c40d1400240144c0107900600f800c1641d140010140c140c140c0100804813040001d86130003540b0600c04505150400c1c0d03210418800d841e22066401042c0040c0075404214000100042401d485001440507261000c1c03580401d11011075648100c84600001d00d800f01412401207810020b002c29409403030500d40b0b495402840785500441601c144a0040c40146490b181403041c1d1030f41107820305040c001540d8a2906603601c0404a4201c0c0003e070a02102d04241c0ca40201201c0c01045103513105810050380280c014002d6010102e00d07540302035600c0518500b5110340c101602d1307240d9202102030300c07201004c00161030181003202c0040c081900301024818445d00001d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 246657733 1250 246656483 246656539
    0x518010f0b0301060f080411090106050403050114090307020909210405090f15040b060f0406020609071409010e07110d050903010b030106030203071202130510030c060f020a0b061504030f0b0105 85
    0x6c0c0a03c103a40b0349040c403c1d81075810400b8217800005a00000c51b4007a004001081101c3c4100000c200306080d8000f141c00e440300560705003d440d0000c100703400240c9040b50009820500303c2d400d941100040904c208003039500d90403034035101c86011408011303d00d030104000d44c0c0300007660007a40b404d24001616040e80c07402d488445100c1ca42d6020a60047c0d00d0350001e0302c2400e41c142012036179654070b911000e50f6408040304c42911a1055480105413031000065180362200080d0421040740d00303107250601e200c60000c1204082002d026550b0102c140200300c0304401703110703d4460b6551503044905142c00d49030f20b01082030190b81000410401a2800035410046030780e04441e50706035a0b842d1001074141407610f10000106400d03c01030001e40701031400008103d904c140303401c180d0780356140010b890347e050601442000d07030080c5146030041840384c0c2c861741d4040c03401881c0c440c0c0c0300210303400340c8620780241d0801e80d841108170400d2020060342640700c9016160440c3c480005240c604143c116801000c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 246658983 1250 246657733 246657737
    0x3150103060509120c010f06120c06030b2b0309050103110306040203040f02060c011a040509031803100f02040e0a0204081b1c030c02040f15120c0518010f0b0301060f 73
    0xc0024404a03c2480300a02c4030b00d070541e42c80d5542c04a00d0381d040c06020040c8007480c80d40e00d0601c0c000341840d8103189440401da88181c81d180340d0b42c5450002e400030082c1d400c0e0b0301d410803042d50012404804503001802542e40c0c80c40c50014814090178010400f100ba504184d0625107000d4458054000540660340d00c400c0c102ca000d692036030f880c98202030030b01c0d454078003e410071700c0421881b203a904190030480400340b841180550406801d01000203444054038000e6440d08100064403c1d6200709480c1c0e601c04201a040310000e0003510304543c112100c80152401c3d2590205061242c0b165450b0207035009240b10005600740307030400200580f94900403038699506c201802090f071450721810140080aa00ca5480c40741c26a00740c00c01078482d440254040303100394501a221400d24041c1c0c856064940c500c3c20412000c6414004082d03030a40d160303030054842c00d11079400054030f5a520040101855030840180101e54945100c01242005907000498520390500041c00150b600401c2049241484c1c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 246660233 1250 246658983 246658991
    0xa0308010603200d110309060a0c050f0702120c0a0906050102010609020c030a0815040606170f010317070f060510030c0e040305070204020306061603021c17041220010f0b0315010306 80
    0x3041020080c002445c44044005020080002c0c460307000c12000d102c0c200d200d40512040c40320341408c595034801d02c520000150424489240076080200304282800400070844020455660004a00100f6640315046458a0760014005035034207015002c001d1050040a6041080b5060600d0700c80c040c4442c190b04026a0300b0018014004c41111405100b0b8043d2040100c03640b1854010711080f00710b051044000300310000314161f50400d1a0041c1240c1d04840322540614440d0080300c80d0381d005030425903840032010800b501180561180d9401101302c0d0000762001c1d0f1440c41e201c0700f9901207600807120541184c0070800400d41110880b11f20341ea0440d0f0040c0e8951700c14000408500030000c201000c4000b1981000c2015000245d0320182000c51003410042c0d0096034003140d140100f46c00e4648001c408001060000d1441040e0358044180307403c0c521042005006481d00d41500351803030071180e0791030300481201080d95104e0300510002c00c1d03024002850144007101400003061000404280c0e031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 246661483 1250 246660233 246660247
    0x30606190915020703060c0c12050c010e0f0f240f040204060b07151118060d06051f03050106030204080a1b05030a1b0b1204121e020a030801060320 65
    0x10500d001e402901c00c41400c8510b103042403000940c0c4002500048a5040c0740c80140c402646c011040d606400394402001e880c061000c0e00e08030f485401c030483d001c62564886032034400d00c00c020301c0440005160310780102880c101c40380a41d031a01511486820f15072a04e01d01032220000d51600095000a003046901c0d0700d62954408134000f00700310f6002c144d06000202d4410204800b2107403507885440d5804080c0103200303000603101403a10605020444500c0c960340da0b10480e0600401812a060400e0030000d1203030790361000f081c1d040181108180003d8002c2801c110701e15054801c180c013500302d07498110b0619007400c82103603440c1841400981402d449903a0386022003841e408050183c2070150603221503c5461800006032540c5842a00f84c148400101241c51003c050a442c07141c607101c000d00030103444644a403c00e0400c4044e04000304460f0480426091001c10085880c0301040d5005083d00c42050500410648068100c0e90030103041c250032503c209031900d25260b2010302c1003422550746403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 246662733 1250 246661483 246661487
    0xf060c0207030b1e09010b0d2a03050703030305091902121e1612081b01020702060a170601031a041a0a0b040f08060606031303030b1e01090b03060619 66
    0x440e544001c0183c10f81c20708010904c120404d1aa0ba00058040d0846464462103201c5003a5210510210b40154000c0400c10214203c01c1240b106040040d001199030400b21840e81442a81c5420607511541f003100c0030020140d15114290784240008060080c2c2940740f1100e820b001100758000e44200d07584a00050308603003d00c5010603504200c805610b0030000c0c80c103a980c645102c0d40c58014002d01c440130010f03003440900040306140d40e21a4400e031800080c00300c2c80c100810440d40c05c0342a50350034403030800144c031130400030490b050040c0c0740c140066041e010300183c09600104054109810601c1061102d09101140c10b203150302202c0c0840c0b001003015806100702d4085000c241d01c40000c45000925600340d00007003040d00e0705034101c0e26403d6141c040d107039600d8000f6610260008000c2002441128000c0c20080e803491180c6404110301d0950f500140c0b1040d01385036040700e1441c6200b00441c1e40d607040f903900001001c10340c0b0a18103500c1d00d400011190300402241c10700400504c8207600e045c1c0c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 246663983 1250 246662733 246662743
    0x709020d0e2505060f0307050a050403120e120a0b010303050c0f06011d0f0c0901050714010504030e030115080618010e10051509060f01031116060b090f040f060c02 72
    0xc0d2410085891409585548808203071040b201000126005030b000f2030142002011645400d218250307291664461070b400311050740c0301d0540c00040040900c00480003459601c0d102d81c82080c1707030341c800395802160710400a1240310005001d4072544040004800201c8440401c0d04580c0c0609000e0f48801c0110303000c5080c44103100300d11401e07020b18030001c9000c01144042e40e258040f1031203040b034035a03a09080034035404000d455056242d402884107005540c4030300c005240081c884c0401480d09a080c5050b2825528140ca00f2004a407107041c0c0318170329050910800b00641e00200180d003803940f520a1440d00c5030409000b54003a04186200c5000c002002d42000000b142c0990484010000304280b07040108815214090302c0d03008103244400510304038103c0780c001c68000301001d4401020f440150001c2401e041d40c40d603240b20034454070f220a0650101102d050b07000f0309002c900301d080081000f5410070001c105044007038a40083c0804602d4000700c0c044880d5105a0014140b070016206a01d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 246665233 1250 246663983 246664001
    0x6060f150412110603070207120f170a0f02060114060f07020d030503090714100f0e120312010f210602090301020a030606021c0f0f050405100f0906110709020d 70
    0x344000790001d0342d801e006444840c050b020301c40404924814604001c1035100c20b503440320044e03209500c1032041c554001b0401126521401d540c2070001c0c0542c2d9140c0f900307260f40c2038207440d061005c01e0264070650000200c400e445454805418039604201188400505c41001240941e00203c0d100700d10043c01400c9603e102c1e00207200b82c2c8011f840d03140041c0140d000300c0b40d451180c09052800501d0b8030750350600d0301d1a060010607a0441e500820000c45074507150f00902c0d800c000e000385006120380c5540c0000c040050125000d0355036806c640300f07000340c810b4060380f26a030750540c2290308004160310042c030010003814904400d0180503581c246580a0b020300e010b055415480054000c801c0741c1c050380281d01311215a000d0760342103980031102847c102840e5801202140d20580c2005159200d0460306a0881d8030303040560034240c4440119400020700070041010a003551200b01141d0b402c0301c000310045c401440c080c1c0c0781009007051980c4800161040c56030540d004188444243c150381c0204801c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 246666483 1250 246665233 246665269
    0x1503010b06120103021302031303080c1303050601090e0c0d110a210b15030a14010608070f03031b050a0609020103140406050105040c0e060301051e0303070303020c100e06060f 77
    0x40302d0440c68800d01049007807000301d00c10340e40302030442c1420f0024000e1380d20807800c0360b030356080010180d02c00b943c3c2e0071350003071803c04000420402182a103013044044006980107030300030030b04c640c1490009000c45903d6880300d4000c0e8480882a9a2650340c007460360f1700d5560241d01079910301c80010201e44035031502e800200c080c214212000d80c8120202d82000760301c0340107114912007611010101441c2d0624131510a400d40c01148100c03012482e0b10810f000c41e030046c10000034485583e11075031420000710307821500d92170b4080c0c007040050551003907204070b90801b105450800c662281c5d0302c4560310b569441d002020b490303d9030201c209582c044d50000d5804200d00c03a02e04040d2500d45402002840c007401018840c0340780040c0c100ca074510070314042c0c128440c0605130903d907900b480100300203030403111544004981664440c03681920188003034030740c1c1d51103602c0168075032103401b030b030b66041c44501c004254066142c0b420101a1880c0081c81070f030861400c1c1c0390741451030400004565008141082005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 246667733 1250 246666483 246666487
    0x40e06190e07030b040c0c02060307113a0806010f03050405190f0b0a02031e0402150a05040905150105070311010b120a0b0c09150c030c071214060403081503010b06 72
    0x110568154204c00f401c01030890301009241d10941007614111089074019402081c1070000501040c051041c098140000400b12001030900c0001085110f501140740440c0c080032409954040184a00d904005102800d000225160100008207404403d02e8140100b540328008241880014020124264101c04040c2103010903800c0076a91076102600481d2081c0901d000034600383d005e0320031303079006400d07411403c107102d041100d01c0084228007400a982c010420030844118100c0d1000805107803005444143e125490111450700302d48000340b0078400200303403004103c111307a404000c80e1b01c81540b5080520481c800d0320742c114010801c044440b81c11408400c0049840c48000440d000302c0d0303118280740d5200380d44496411150303008901c0519086040c40144440204c03625002d420090400412282445c10603e5410f10300801c0c3d41c440103249080f146040c090090362401b602100c104440100351134200b559004200b030700018100c503000c05483c645030302507940c01c0d00031045520300141000d0b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 246668983 1250 246667733 246667741
    0xf0b030c160c0308041502010e061315020706050612010c120203153109080904021e03010b09011b0b0f07090515030601032304020118170703050c0105040e06190e 71
    0x3c5107942c001c0c000d11381d503c1002006806c0582c41401502803031592640600a203442c0d8003a20707444001540002c603403241042003400d0440030b540c805000221301409000c01e0310f00304602449490500132003448256410110b128030042e402409611241050801c01a0b40303541d1444c2d19000d8201e0000525445100105410050149c0070500d25100c0c01b500e42c40410702400f5aa5082240c400100082c00d1000a02c04a042c619255015000d0402014142e0011580030f407100c082c1d40d8401d0304a20443e98011800b0319031944c0c008840c1c09415421040c060340d035586e548500c00d8019005041c0842c242621000030794551090880e10002d00001d0065001c982051003503c01941003240c44a0002c5c0c03801070090092817004010104c0300b1400190161652140d400458440c071309080e4800a08110100000d80f0081c4460150090b1507444003a282030382c15890007034140300305e924445040000500041c000400d80c8480aa000780c81216a80301c28041400302c0380e078841d440e90010450021500c204 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 246670233 1250 246668983 246668993
    0xa020a0204060909020d0204050903131d0a090f02092508010e0705030f0118110706020703090501140909061302120709090c05190309050607180f0b030c160c03 70
    0x112211842100c007402240c3c0c0391030040e0221445600040c0d40041c481c2407040250509601c40d40d00810407c080d40c2c54542c0b04803042c103150803190f2018280c141d54080050350028203040507034002035444001d00102003151550b03590582c610002074402e1001c0d101050442001072500c84010405502c002c002200014020b08a418244142c0d23829645940020304410b1150742100d100e40c18980c0151140d908008459203517285085025044980c1d560030111032180c04406040d000380700300405640d80819150050031242543d0010f814040d001c6106503941c41c2680503101800c4040c3c07107641a5030b403406c0008004099007110b00d01290f10004021200401500c0d52512801c49504c07581a4203541e001d40e04115a0060161800110140208014085100400c01051600e441c0101d4032220507200c1c2410320320241c0340d903000301c0c120038260461000314040c030500401000e102c9400c05450200c041843e444010035869034100001990084090040782c8032554940000a42c40d116413a4601 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 246671483 1250 246670233 246670243
    0xb01031e02070c0e040b071101060509190c08010b180118080102040e0c030f0106080903091305091002071109040201050c030a05123402030409050c13150f0c06020702060a02 76
    0x401d5900f0746441d070012500c0080200360900903644140c00d03140907074404200b22130300400900b02ca0420354907900d00140590310500080e0203000c1281c020030010b600a04014100d40b50058403405000b94000100500070241003685e0140034804403d12203522a840101d9540c1c240504081a1800e06040400c8021055007c0c0c0282e44034201c040010341c0303404100c2130140c081240da60b075808941070300602043c1c0c03240c240c40740c0214101c000c2301d00b800901d500050002a0144011134079079596000c0200d02c9408100001c4080440201149080c1075500c0711741018848401d91406000b014002c0f50469118000f103131b14400542c030a0b641c90301c00201c4014040e9000740f400140c0001072101141c02c24811111f141021450070380c0254030035000280c064448004030b20a0001d50106001c0003e02c46258000c003480f686102c06030076503a10400c0c0c0b04628000d001d030400c042c403501c1071001010a83c1c0110700071443c41e80c0f60900c032100c3c14452400e0400f034815484c000350414400301d6022012900092 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 246672733 1250 246671483 246671497
    0x20d08070504080111040f0e0103320102120f1506190e0303160302150603150a020903030a0e120f1005040809060c03070309080d1407110a0b13080601050a03060b01031e02 75
    0x510300ca20648d90380030040d0b40c0e690130f01004c2e20315112030103910103034280c19941024902900000c0c3c0d59805600008a089800511100c46480c2e1032108004142c42c0e0780c481e641c1e0000031050f0003035041c15404082400b501401107942410640061041c06407801030f00d20b1400d043c4000c040701e030754400c900c481c001e0051040780201c015101c1d0401003c20600001d030458814a409400ac00307880304604020f00e83e801d0050040c10000d82d00300b25a0030b580d14140014104140c02e601e807020151003030780c144107041c00320b00051006a0031011044400c01d6010071034110a8059004c041519111414524218401e521441e035020b04001202c1b9640c410103c040c0050502988031042d8081e60744a2040e101c8101702890300c0080d00701d22105034071015010140c2240c44c0100118070002e030307021380850351502294008694810002c074150000000301da60301400340c500d8802401483d450306002c1010440c0b1400020b06003900c4940548480c0d1103903010450700c071011044000310031a010034803402944446 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 246673983 1250 246672733 246672749
    0x3030c170403020f04020a0c021c0c140904031103090348041d0109080702030d09050306280c050a0e0103090f080309070305010c08070f0f020d0807050408011104 71
    0x1015001000400041d10102d0390094034400310526580c0400c8001e6018141c4801442009540140542c59800c40c080c01028520000008001503040c00d03c1680b2031540400040c0c84e1040d240c007041c6d118449025080780d810306200b560025000c03040d81c298041e000070300350075214070740e14441228642e5500b00b410890704220864034622171180100c00428900b04440c8001c003410800300d0500700713503004002180040c030640c2800042d01b0340305403d46ea030003a0300fa542954089003000c2580b40500c034128200300c00f0300b400c890305443e007c00719884540042503621285002d580c03a981c90040100207208072041918208040d41e07402c03401620b1a0448801030300001c1551411042d694043c0c480c02c403102e0b4100c035400111491955881c841e0344d10061402c2c181d030291100002c0002d1003401100000540c039103a582c80d40c034003c08004c041c428049100d10400006261096603260045100da01d50100d034503001c545603851038000c2d985032083d513001044562801c5058080e41c0c50790409401501c03020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 246675233 1250 246673983 246674003
    0x30f060a060504110304051c120f0501030b0709031509170304030306060e180a050405030405061303110907051e090a080f06070305251e0c12020106080a060b030c090103030c 76
    0xe1404c50940022a0000c00a0340a01840c4420316803442503125494002e14200e452010580c52a1090b62140c0b2191084162548018400c202c84200c14580c8003d152138000301052035502c07840c0000015051880c040780d40e44178620b0038082c4d410100780502d4002d02c0351540d80d0605240c020010a52842140001107441100101600e0310020160285011400c5103113071313072075036a40031f00100b001400450b2584030030400042d03281c070340380041e2555045e00d0346c100001925600b00700300c654005900e943e218410250405c04450740050644826445c1189566101d117234548402200b403003070f0380308243d001403989000940b140c800501c07400315011b0001a034627075440d280001d600b90788041d40c5410000e40d60301b0750583e0040c41e8961011025550346091008038484c01c0344824070081030180788002445440000f401d0011034908201580b0741741c8000c0020902c2e001059449105c114002050f2540300c030140c800f00d44d401c003c4d0508440c0c00600a0b103065a40c0e1801a02c0200e07079100031104c00701d0b5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 246676483 1250 246675233 246675251
    0xd05040515160c02010e06090411030a1b080115110304080c12010207050d12090602030a05060f0a0e06210f010c0f0305010501050904230103050d0e0607080702090402030f060a060504 80
    0x4904800b200940d6070311001c80702091039005403180101c4124054000c13401780071905490303039240a0101504040400741d17980307083c0141c180044d030320141b80c0c4982591310002c1c03041d52942e204040340c1c1111480780f4064200d01100a04841c0d110400e491560144000301d40403c408801040ea86e48604003141c3d08014200245200350a0380a00e582c003400c1d5401403407180b07802601400c4859a084100e070400110700c003507560b9000485e00306a0710320700520b07521010421036050000d88454866811100300035501d1429102d07003000100180b92b28015085150701d2131007091410750f40c07103000c013111080e0380d20040d400d222035008080855a010002d0b4021030080c030b041e0300901c105d82c16074106a407054a0500d011051001400700044101117046190441c4400010252001ca003c0e40c030817800390040301c0740f51600410120200c601a0710a0714100855000204030030229002d00781d040d14884007a9680d03000083c203003543c90801c1d50b11401030340c0c07c2141008185e841041650011102000f441c10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 246677733 1250 246676483 246676501
    0x30c020c0a0315110c01050a05060a080303090706052a03120f04080702010804020d120c02032811030a0c030c0911090102060f040204181a0c190806060d05040515 71
    0x1103a100c05001d81d43d88400646100030150001c04209035508480740c50039442c001d420f402c42e0001c6408200b0240e450b03061100714604409400001c0030607000450440c1071541e4415241c1c4c4c8103114500902400007254104001071329031502d00c01e51031031001c540d21a40d1401954403503000c900c012220040d480006400200e1205000340201d400401c8682402d2171940190750203503000d030007a83c0c052002c0e002d2000241055007100d480002d550f45003034454115205140c40c103440310202c1241c11003030094042c24400054031000c903103500800100712907408040800c0c20150910000742c042c1d20200000300034062a0301c062011198210400c1054240c04102d840d151b01401a01c075005030001004210700d18031000c03640e070304240011700002e071801100c00c50780000220800200c501aa126009501404182c105a50701c000002c514a2902c0c0041c46080a5080e4400429052240107004150103841d060107503274203100e12001c10002c40c10141411a6519811402e40c141c06101d0000504444 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 246678983 1250 246677733 246677749
    0x31e1d010915060f080a1e080d09140624060d0e061f0506180a0b0d0b1908030301050105030705040906090b1e0a09020903010b1306051809060403030b03010e010c030c020c 75
    0x1c3c5c0d0100160000c00c2c90380da0b441c1001c0d042c50361800303000080c0d8120240130440200090103a014020000960001d4a1034a0841601c01ca410b07120150010401c10401d01d20100010031503418500d4101d0080100100050180c054001380f01905807034221444241c4000003070040c00f4030200401c41951280074010314901030000e0140310740184061110040040383e40580114102c0010140440c081d204d004004280c0c1040c01428620b40c0c42d0701c0d210002d400e0a003001c00c501003401c90700612150420b280076a813880103103c0c2d103042240001c00684101d2040040d00c01802c0c0d443c400b480907580e202e8003207001d00a142100e0788107040d40801e00c3c400581420300840e02440207004030748040d2401d8050700007500b21121190700340d5201c20183e04641e5400800c3d44500150203400a181e5043c5402e000302028500013010300c0541420500402050004616500940c50f14012840c1c2205102103030150000c8144c1460399801c11040051003605500705440340700d06982111202807900b42006268 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 246680233 1250 246678983 246678989
    0xf06081b0f030c19090f080a05070e040203030c01060e040c090c081611120d110304030c0206090a0b031e0601031509020723010e010b01031e1d010915060f 68
    0x921401c000c0000050041005075500c6143ea0858500700b0003524200446002030407460000920102000e018010410422030041c10340c4000401050051741e4030165100c1c0980155168007035610b001404550b130070000ca401200e8120020301140350b483c0c00100c2c3d462010f0b02d0807292524101408a58880e143c40340c030030b000e4070680d074040d01510781440d480304d00c1d2070307100f0284104803111034020350110f010025105400081040c25580b6072640200c0c0c0d0895000380d19421002100f0400e0101080e441500c40701c4a64044410701e65420940000a030303000d41c41e40c00740852810100c00c0000d10601d031039202512000a00e4850f84568603600110101da208403102021012508018402031210b43d0140c03034134900c11581c60105420300d45c60a0313100164103440b50a145c5d1202e105940303000c801c0c000d058a000c02800d0038001c1440139030f9a11124624030b05001c1a0741d81d100040442c0f8803096060080801526000b0000b04801e801d1140c3c980b07203245940c00986003400303c00103440c11001501811 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 246681483 1250 246680233 246680281
    0xc0a03122313060e12030105040f060602031b0321040204060e0601020a060e030f0712021605090f07210c18082e0f0c080f01032003160f0608 62
    0x400c0d40c0c0e880d0903800e00d1190b240305540c2e66035a07504a0480c2c9404106504545c601001955200d40c9442c08000990320701d00b0112442e241000020802d480d000001d5400c0c0150784903806280200c1030121a1540c01554082500d801c558245c5240d600701b980441781c001c0740292001c0c0812074883e009484103d4040e10a0b60040e072101c1042c1000c1261075124012244280c1c00380da15150400303101110390b4100b00341c2a1140d003020f428030703005990104602005001c203000e6a00b6800d142c80001a40328000502c1110030314010700020352640c1c45036104000d0026030059942d0f0440d888245003008100c002c1c40d681c0450800c3e1511360500c51216602012030310b851000307201c12038009826503002c201900711a02c81202075111a0b0880c0b62501420154050307000b0300051040700c3c0c40008103144000ba00100c001d6160800600208ac903030400c02c9282078070664081035001e070b2480841c0c41d02e0202c1d260701002d030002440116513104140c860404a94140e914071406480d4092240d0210f0040389683c03007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 246682733 1250 246681483 246681551
    0x2060301060f09050405070906081b070201050a1211090a0e04050d051b030d0f05071b110112020d0b040b030312060d080405040222060908060a020702060c0a0312 71
    0xc410b2181854210007a403901e07180580aa481c8045000d07690b00f500c000c4042100a0014400f090b80269525404124940d51040d141e41c1003103142100d10801c00081d0402c5000505440c0d8540902e00040394510400c000304081010a0107194035034210b401d50701d1207110300c1c000004c2c81400102d07003140039034ac2100150600d0164008180c1fa19800046840a40604a20044180103060010f0b1400c14080390380421b2141481880c2c808032200102580f05014550085150403800301222100d4207500050182030a05280016100482c10409100400d4000914418400742940080301d1201d401d0340d0034081000341e2003c0680720f00680d143c034003001001700005006442c1a24183c904c50f4021811310b440d0030303151004101607038003901c561a00000c00d56900c010700310411070564001e0146141100d01c0da41040e403280c1c2c03140b401810500742190086029002d564800c0300700c5078042c01600489140c03030901c0c80e025003980c0d58841e4458449142071172000d40900741e08400c01c075440701c05000712 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 246683983 1250 246682733 246682739
    0x111030606030402041104080c040c0f02031210260d02122b020f09030607211a03010912030609050c19030912200a0305090d1a010e071101050402060301 67
    0xc0a150801001684e10030f40322034001c9446c80d0308000070800b600c42403002d0070555020b0012720040e1030f1403070711650810418030b80c9207249550100540d51034181c801a41030540c1c9880c20001c0702c894854118148130080c0003010300c0c0d407100c5401141d54419221041c4c1e031701649103060991b01c800e1a40480700c219501005592550a14510309000c4803c22065800e81c0715200900c03031089820800f80d16208a0300001c220a062400304078840d070051032854182d81c5184841c0000720349070b026140305c0e00140e88554424400d401d00d040000d0014001800030404450241082148035004106080110349081c9011450841c680201c9200d0132613400c10f02d2030486000c400d0400401100504000c00d40d6030340d24800000c14501c800c490005a680c4c0d1610117420300540300ca80000c03e0b103640461984003109550010350010107565803140110740c0c901d5000510304107041000d840c01348403802140d408002141100e84501c50f00d000d8656543e4030000005510703207650032114160740c040e42c480401c0c0010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 246685233 1250 246683983 246683989
    0x15050702060c0d06031b05040b1203160201030e0d0305010e010b040501020d0f21050912090a060e1512010906090c0e0f0402041a0403050d02060f040809061b0a02040e01110306 77
    0x300215045614001a103543c0c0780c6400c41b9011034402d200382c400c90440800c00c0180741c02d01407030610314421a000141419090803455480c0314018030f0980740254801100c1c156030007076100c00804102d00c0c0994600920905005000f01001d0103014101c4450304000b1641c2c021150a03034056450680041c00c1308801e00c241503078001ca084a842d01004440700095011705a020201d000b040300e0068081100d0610040359410302200390200d4040b40014420418180d03030704017a400c201c902504080581d0340c15074000c580e01486a5480c00030309140010b4181912452001c241c0c100d42c141030341004442c2e20380c0d0b0305a050720801c01101002420030901c400e01460610990400407a00030801481d05aa8140c60711325000f90f44061411803002050400078400244030040603581280b0141c0703054030b0b01070003072110100c01030303c007500c2210701246508541d20344404480f82000400030203c4034041c03d40790907a0fa89c280d808220b0160382130150750001080305000c0c0c1400d0070b40540b049419540c0f90014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 246686483 1250 246685233 246685237
    0x10f03050316060b1e01140f16050705030d08040c05010c1a0703020913061d19090203030706180302072309090304090207030210140f160e030105100315050702060c 72
    0x30070f0f00c110365100d02c0d00c6429038554004001c03080c00f01042d08a4034510030005442d54954103102003142d10104603203000b040d581e03021201880f404002d060340d9131105003000c91810429400c006d0709403003100143c8440b06d0b0840700f401d109500c24000e09404540321801120404e28060004150b003080c007564080b5031010b61005540700149160050826501a00140a004040111400d07881d0344110500c0354040079010403c0c1d1510a4410403000d04010010a6420210b4001c0514642d5100aa10f04550b010300460304000d030400410302915105504881002c03941810071005441a01c40c0021060000e00b20300c90804810350514400c1d50101082c4000c0250040ca800035030b01040201240e400d415101038030449000f54000d0600c0c00074504540c0031030700c607003a54a081e44000300401c001014050005607002c0b65024441c0d481c00e101d90310035650741c2034405105901d54244010001140070141082c02128000c44013902800104e039089800c48400396483c40042c1c10500010350040c8107440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 246687733 1250 246686483 246686527
    0xa0309050a150c03200912010b0603010b0405030c040e210f030c0a0f0207050a050d21020c1003020408060112081b03191b140a0804120209010f030503 66
    0x141c0d000c0038016030352440284203825895025035510007280b00c0c615494400d81d06100c1054040a0b0b002078022030903045400b9806000d40b2800001c200d0000e881000e4101310030800c4090003007600e0396164415503003940c11900840d4001d114a80c0051403070f1a183c0191a444071a80010700307a100316500000a070385a0180c20b0180400c420048840003180a000540c4540c040d1280341c5d86400703034044014441c80356900f08504540c00706505100e29510580040119101154202d16410003840c00c840c2e030b60202001d900319807602001c140b54150b004500c084403500116510a041140303004241d08074000e9020740c803c141c1c050300c014060f40e0442c0010585050151242506120740b40f00c0c1c0210310707052038401ca0300c42e4001141e0481e1902c00200c15000040301801d05569a4446804e0030100c0210301d0b2000d002c102c40e0803200311400c0018002c01140603000410310703030b44a4940340d00100d41c2c542214200d000e24141d000000301d450102ca2040e05580e40000a03524000d0580e0128a8100c1115 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 246688983 1250 246687733 246687743
    0x60a030605070e1f08090304060207060f030608030a090f1703040b03180a0f030e0d03050a0e061b0115050d030f0507081b0a0201030f060b090d050a020409080c0c03120a0309 76
    0x31420340055440350542c94500c2c40c0ca0813455845849010014140c034006802c0d807a650b03200388001d004c841d40103d48030082c3d81c07a40ca411119000030745401c40141c12a6444007245020000d4005082a44011520251010031030840350f015522f05104034104582240c2e03d091b500180014030100007050011604540e03045c005030415a25044070307a0a11007880400c89a60380b11050311410150001d032582206801290f42c980034141d02c0e1005041482450004030401103021a200010381d180d41c250307651001c6e40ca0950200c1e0080498090003800d010782100c403003410715000012149040f080c0d0369205a89984ca4111400c1c47d602c040d9030031342000701d040f00e94540a21140e08803400c1c42d40d1003214003190100130140045640005030489460f0542c900102c0d0501c0001d10000790a2400c8070202c40c1e040e20444002d5100341065400e207130034400020350090034441402c0520918001410801403031505807400c80c0484010560380c0c400c1414145480e420600c00306131114040d502080400b8090 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 246690233 1250 246688983 246688997
    0x908070b091318050f0303040c031e0b10090b12070e040309030501050f010929060901020102040816050a08010c02070902090d02030607120609050103020303090d1505090a03030f05060a03060507 85
    0x10034804001d4440d403c00411030b0302c2c0e8003c400000c3c040100860414001c044014514508050300c0d000083c118900015248050700c03030312040403841e00c1085890182e00a9002c003c02d05000341004c00d1400c2c54403410f05070320300b0a2510201403900340707001840e100000c4005c044251810f84004104240200280d091109114000002c0b5400b0f004c1c00303100d030f400c078401c0080d90b42c10402c10604907000c441e0056209001840300e8004c42100000300d48020310308851181e1039a030b2210040380a0311a41d00400c04a02501e0082ea40c043c0c603000c0080151502241c4480d0728580f41d0101030300300c441c0d51702020016402108100b05440240d4018000301c0d202500085600045401180c42c01c10295086030006440011a0002040c1c1e4400c40700500302c4448280a15451500000eaa90103a41d00b52417050f2891000c0c0000c04c10f2a5040c4540c02481a03230910451501885a40d00c3d404080801d4010a082003c01c0c01048103a200e04d82c07144000900e2042900c0c1035454040081c40000c041c00244110703 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 246691483 1250 246690233 246690259
    0xb2d0307090c08010e011205060601050c0c0415060809060903160f020907020601140609030601030210030e06040b090d030501050d150e010f06050a09050903070f021801090203090d0908070b09 84
    0x2481c010485541c25a03120103103d0f524003150446680340590150f5044024000e0150020b0400f00b18260020002d2801d540c0f0313140300246082c104020400d04650080c5001903146031710546c3e01e04a81210340c0c030b48a6074880c3c0e5400d050b41d5281c1400b1540340005800030032651045803113510100343c480380240030303e88041c225540803500c1044160741c030340c0140e0310010040120459410007101902c1040e17410500704030050b00820750b41c203010b0000a02c101c10a90503451103621a0b03111640e4202e9090888603242024245840c250b002500c400100d4022031078824503e0740280141812980003400f40c3d0080b5540d80c45041180f4024010b0200040c0c40740421400306e5070034000c1d0a03980d03070115000142c07185068200042ca400d650b000f10741860901c0f08214100a02100340d41e441600410f25100105240c80022034000c0c031083d03184400407107040007040f541c00f5640514403a100311802c0724030400c0c15200541d0f410f600b40c821804a90310032070080c441c08902c00080d0420401c050213111001007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 246692733 1250 246691483 246691499
    0x3110a12080a0501091b0c020d0503030709032108070e0a080715030609200715050414190507050d061d0c0114180f0315070e01030b2d0307 61
    0x12221a032040012201030034803a03041d046100e00d07801810541c0b0100401610480300944040b1035500c420309100c1d0030300180c4255107842040544099221003a81d135a868821405405c0b1001d5000685144020329481c8019003070048620b201504161542160ba0b9980c000845040318030a000c1c0340c0014a0450001d8110803c12039140038180c69015541034480405000381101c0268ec030403070561f800c00e40c19a10180740a0140b0701003032444526195507000f00d08110a8030004200040401b9252000b04414041d0351031450f0700d0a1000740c01c0c1c51400f00c00c05008400401e4010300075000f60000381e01000545006494120114450500800e0010700700008100c00a00904640c1c501c1c0c1042000120540c1d0008000b0502c860040d03425043c240d083d0022074989100b100307610700465590380314a0855034200715480360401c010011007610319208100506103880c3c0e00e1480c1c0801e048c0a01041c0c0b0f850168031951740c80c0c010001008202038511500780860900401e80c0390540901000803030158 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 246693983 1250 246692733 246692753
    0x513090209160f050301030b0105060a02160b12090d0801140f0316031211032d0318010605120604110d0c0f1a091309030909060e1803070f03110a 64
    0x1c0c501c0b46410321121040b200190503940100a8082042020001400081c2020082da41910340a650490b142d6403000c500b83e1030f14000f45502d07035507011901c0b00000d8440d040001010309003911490205280c030f40c050f04596400c90b44080c540171a0200c8018410f0800c00c800351004210010503021510441da0b0129003008941445944c200e0070810090080c4020040d9168010041e845c103066018251071100c0e484c0e0040b40f403002c0d0240f104010304401d0295030750003040c483c400004500c0d42ca0900255a0780d4520100c180e614955017480030002d43d03480c0c031814900704034000e2800b42801e039540d65505050124000185584200c2200361a408284980c80f507401800110140000c200e04280d003804a5101400c040400d26004001c040d145480c0d602814000c00f4440301c001c0388940d9246010b464842c081d40201d00d81900d82180003c182500c03850f100c1c0101107064140420580b49640503807280700391540a480021074410700d0002912481c030351251040c24105503005400700d60380d201049 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 246695233 1250 246693983 246693991
    0x2040b04021b0a0203060c0a080411060d020f0307120204060f050708040f06120b04110a050d110a0c110312030f0901060306050a0b03060603060403020616020a0f141504020303040513090209 83
    0x943d0083c0c3c1e9020850804004440d0488840584207040c450316890007041004001d100401c011120107a6041d5910f640040c5c0c2d441c20380780340302992201d0501c4a1000d05810454001002815038411420301400300d03c01c40342901ca0540c2c0e4030b4102026074606032195408490201c5848030200000a010200c150040c03020388856980c00301080400300110302a10741e0000340b03510861500d0f004900b1612248111800b40d86a030410a8540c090ba1200c0001424415020248410001400b104140e40012502c0c40e051240c0144400000c00c2c0045c10b0342e40d852400c1d9034903040b408001040d40310300c1e5820016841000c8034004104261240c1d01c6800f40d6400342e41d03401096842d075a00b107a0500e010701a0541c001c8064004100a00d06500d00a50343c80001d4502e1900c10700e00c5581d000614401d01c6441802034109801d10395440c060b207001d0181110800e0008501c2c00fa44044c03040d9407104a0b202400303250010001c604141c00c1c03174100200100c943c0a207074001507031502d14000584800407102e1003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 246696483 1250 246695233 246695287
    0x727080102070b0a0507090501030e0c120705010914030709091506030c03020a0803031303050a180806040b13030504060e01050403061b0e0609240f07110a0501050a020a02040b0402 79
    0x40c2d01c1e05251000500c03002408007541306090070108018030b5403155450040b00c00c02d10b070100307801e90202e918505046154103103641150002c42c500e8041c400005081c01100c0003030b40c442000f5076440460706804003581c036510758550003119081011000b5a00a85000390003049c034041160104241e020440340306034000c0b00c88031146030b0200300b5844d1011804008040c41c0f00914514640020341c148120165403005060080205e902140644140b92801078180321220f902019900c3e442d0f01a034414044808076031800f0002d001030040207400f200303c0d11280e0715440300360415007403041c00c0c0c402070300400505041010621001021407c41c0c040d2183da902007000145010500401c002c2c03845881c0c00d00c00e800b504042000c3e040340e440350308404e01001d100700c400320468039500704c54141905c22030f400b110a0a1021421100748107052207050700700c0c00100c40a0380100e40d20300066640e030060b82c8802001da00316460300c00c007508080e0001c90f00041d00078001131810f041c82d0310b2090b80ca550403d513100c1d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 246697733 1250 246696483 246696487
    0xb040e09070f030f03030f0e01021b07140303040611010f0903050d05010605090d06050c040e0f16170a1a0a080d12020301050f0607060e01020d0b10170727080102 71
    0x31441000d01c44500a44081041c003001c039421501c501042e189140d20080030544c0c0c580c0042003074142c0340d00004001907000001d41d5a10b0140c00488070740c07070318840440c529000c0c548002403a0f120700000c03440689400340140d400c10381340000564001421a40c11503440d5250200980d400800303104900d001d620030b0710b95503160040504c0d802c00706c0744143c1015082c010100110f0885a840300e802400d0298058004603440d55001c0021040f40070380d622401d1400005010310950005040049104005000d41810300090031481114403698030014a50b001c02101c0100300b140340c4582283c2010440100c0f00d52495006d0000b107110812942d01c1900d5a030007070350a810502da84a09203031601e071a041029401c40d4100780003e08282c0810142c2485178000284050422089070004055103038404000c41d1900010007140d005003190319121445540d604080b03006040c000c20403071b4101c041001400d1426612240f090301c0c0c840c0c64440420400500b203007100c80071a0300107402e0000c5c00000c80056 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 246698983 1250 246697733 246697741
    0x60112030305070207081c03020f040f0518160f0c170d0b010804170304050a0f050309010e0907080609060a0504050c0c010524040b010c05240a0911090405070b040e 72
    0xa0860b41d0203042e00d0110b41010108200300b0b20000b50303414144054203006030034131602c15010b42c000d00c2035550700d5903c1c002c08900050168510b8001c00211030301594204900b205c01060b07940e94220448038012001c42c1e50300351400a074420194008498400e0a10005801164a560383c0a040404c203004a0490008500c8a162014011260381c0c01d0b00382002896410710769a201c4c0801e01041110320350503004000a0b05002081140ca08032940106a2029540035818000d4496011840c124040b80040c101740c17406041002c078079442126240c0c4c83d0300d03e640700c0c0c0c1e040142503500500115803000e104800480c1c0c0c0e90381e0384078482c0605442c00703080c0d03521120908101e09542000b468400344886000c03640c1c1102a81c0c0d210400303d41411140041c103200b1820041c0e441000800014005208040c803410340c604042040c0441011020140406039441c0705540056811100d402055807540202200c684c3c14480451604244954180e0320381d5610364044c454135030026480038282c060044280 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 246700233 1250 246698983 246698987
    0xf04050f0403030614032a060307030c020105010609030b16090803160506070c0c0b03070915030e060f060a03030e120604030c0c0501030c09140a03060f021b010b1011010e06011203 79
    0xb0008000c200c5603e11700f00c41120000c0d03240c0c3c0019554100103c602c59204002001250a0320407800000344425124100054024010451024a04091b42c644030001c1016030088401400312175100c0c90300541d40e0f449115030990025880110400d0025800c80420341040500180104200741000d4020781441801c20300e00e000800303094007050148080845000c0b4102c22451416684a000320300d940c3c3d103030341404803010300c0c4641c45821614503190450241e141d164104500a40c076030022903440761180058100c01d520192031043e407043c448002000000d0107990803954501380180041e014882c8103810a003084000c0782e017100040c01c0c4414000400940008a801410003840c040111000d0326078050a101210b01540c240d8100c02c1e05070a03019030395030001d46d000c5c560144052091403025a4010041d4200045021070703482c01c6002c5222500c414440c00300c040350300078025030b2810180f80702900d006070318001da003000d0f540300e81110721204010001c2c1030003401000b1559101050038100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 246701483 1250 246700233 246700241
    0x15090321210f0402010804111306090c1806180b0c030a020f06070206042d0b0901180b0a02070f05030f0d0b0f100f02070e160e09090d0e0f04050f040303 67
    0x4150621070140601c10002c070003003442e40e4843c0d07083c20500315980300d0341002003100c250040380c25402244401254a01c41380b9800100440d00f544d0814008140c504100340d070b04a20520142c15900540c00c1b08000751846000c050401c1e044420303400d19903a4440b000c0f02c0c07280d8012207205925500c0000c0419840f90304003d1120306100140160081d4141403400948920000e88003801c02ca1140080c4084418001c075021401d80070003481440c1d00810340303400000c079070049803600c9095203840c0b01e00403549440c0709400360040c1c0c00503192083d9959039070460000e4000400544400036005081d40002d04100014039004c4417560b00e141e03c0e0900c0d0803048041d50b128000e2a8040c110002c90f03030b0501c1d2258504510000e5050910b400e80c8201550201d02d0640c00383e1203031656816010a0165503100300c8070041d40d008169580320207508c1080300780b050a090a450145495002c84810113480f032003020710b50490f1000500c407014a140342d800103803c0d19015034003559000300000c148800c158140c82 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 246702733 1250 246701483 246701527
    0x4080f0610140103020d1a31050a0207020d030203040f05060f0a0c06150905040c05060c0706031806050405061e0702030720090108070303030507090515090321 70
    0x5203054541a0240d180c040a548502c4405032a60120b225881e80260141c0c0e00310748001004011303626620342039625207081c03c4a0280900c0c01a40170076041d5505600c9015026450303070020181f010101c024a004140c01040c00c03200350380c02d21140d801030b903074a120660140d0280d0f0003107072900d040401c00303d03403802103a010512840041001c000001c040002307444000d001400c1140c003001300303801c0070400b50100b020050a02590b0210210700d07007100d40c0c04107000701d0041c034a02d032815440b0428080c0500c9034403408107050b40b0401080003014825001804041c200d542032248905e15540c811003a10b80594045820750001c000300910a400c0041c040300d00c03404001010450300b4405800380d2a8800c055001c1d04004d00800074007811045540e4004036100c01038115603c5613541c13003410740c60380e0050000b18000381c100004074038201d100b4030307900b0700741d505c01402130300c10101c2c0905c0462141e100210058140c05001802d80d404982c0d90a0b1301c28065441c00c045503107080a8860108001e8021 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 246703983 1250 246702733 246702763
    0x11150901180e1003060c09060e01030b01020c04020c030d0b04020a1e020f061e0703090804140607050a0606030b0a02030f0f060d050106080d020f010204080a03080408070b01060f0e01020a03080c030709080a080408 93
    0x8070411415500031001949c400e42800c0c002504d410030030040303003061018894030f03412a00000d920005100000000c0c104c54904010070005d504040040000780e1103061441000560300d40400304101d03913400c4605541041a0040325900c44011000034200201151051441d00c450018201001a02c1120a90280b4a45420400c4480310b46e03e101c51070040c0d002e20301004909590003540350710360400716030400d90400110f4000100c2890308a0181607a070000711540130404010524402c2c00b4004d683c06820501d400c0d945030381d12041d02d0268404028440c0390b21440c80e420030400704e1030a10075640640765550240880c1280c2c4000a441d040255103240542da104100030050114040744204446034185448045601d45040001c0c0720f0003400360160103051030000026005400200041809201da11681401c6d600c02005903250604030390041e0120303950100041402c0303020002503a00644c9030418030382094950705800d14112651004603a4440300180622281d81d04002c80d404083c070603 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 246705233 1250 246703983 246703997
    0xb1e0a0f0c170c0306030a0609080c1905100c0e0d06053c130c06081b090603040f1506030b1b042103030f1811150901180e1003060c 58
    0x8035266402c149002450500a058040007054099506020700c6201d00d0300084140021102401e0080c110780c040103134800b1030311811110349401010388403242e8045e5041000740520180300702c5104040d00c04d03c40c0200070400b0001d03076584140d0b9090000042c40b0302070b03000040c0a00d03001c100a1110b5000c0340320750380700f0102d003c50600d180000d03020000d414401040c80302480c0d110106094015403a00b240282460b40040c000300f0001d40c04003241d031060124101e020700f03111084041c2c88403407003900c2040d40c01034802c1000902284002c0c0b046194a481110072048000c0d040624134100c4100c3e420850740e402d455030500030701c0c0040b001c0d042d000b138003041c02e00ca28091408041d03204074118482c11010007a00308644c032040c1402a8009040c41111000522100003105403624400c030040208552610b10300d0301038100c6051020407100c100c01c80c030a00034a4280401e0041d0340c2001c003140e944109641000d0003058124541240314020700004000d0070350a811440d0010644140c03030745600c204419 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 246706483 1250 246705233 246705257
    0x1507031412061806100c020a030b0414010f0204030804030b041505181b032e0c080a15150309050102040504020a08043305070e0a0605090f03060f040b1e0a0f0c 70
    0x155041007000207105051001591b14144046500001a0b501c040c004152500407c81400044004804002c0c41d80000700007404070003c00380101c0c09980005013501e40d083c4021b00000d000201d031250041c1c026120080b007a011002c2c100103550003110000c0f0140f07031805400c01c04200400c022543c0010f21400d10000c41c0200000c02c0c1d4410690304152045071000054051030800800d02540c1403070f41c2c00040c44450409807018001c49030617078201201c0e5103400c0d070300512450301c420254107030b42144508003100940d6050031809859003200540c2c07695800c110000c0e042d80e45200402ea854940d03111541c09180600780514200141911004282620000020b820b604140364411020f5690800282d0b82c4904c2030458803e0000d200b06a00079041110201e611a0440c0140400c0132084601410b4024140e05154681e00c00761900c2c1000c900318800b040001c3d680741d100c2c9074010621809100c0011600c100c1c0100e02c07000b03842003600301e60b903040701d03600745083c80c010f469003c20341d030500c0c00c42140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 246707733 1250 246706483 246706489
    0xb01050708030703020703050d0c2109150b040b0307030c050117010602031e0702030f070f0f0605030103060b040b061201050405010b0306100c11032a0a051507031412061806 76
    0x302c02080d44081581c0044d00b04109070148082c2c4051201c006010416103a00c100c01410400519880564003401030600d411440100e01a141c04a41c2c808251b00d101c0107084114005040800c0c0d60550103922161492055101000310b90003e50280c51034020742441e040c000340c400e00d41e842c860b09000c0310001c0140440e0382c00204662050034100e1480c00380c1c5004c503529000900880c04000d6040c0550100c203401ca6500041010a40b00c2c0010000e903420360354600c01c11111020310586010901c00d100400210360315920003d0005000742c004901d4159176400104980d1000c100c6a52410303401e40140100d0030203100b0203026046a2150310f1070360800c0c0000a56020010300354804018100c508501000b4080040d600203440103030441d41c41c02c189001403165122005401240c4041440c000c034604c0c43d0401c21201101c4000d0400c90480059100c0040c00341d01068060301400b03a41e5200c2c1c40c0404078071000f0643c56141080d441c0c01c4c1c1c01d20f103040100c0916041c6038140003882c11014064666 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 246708983 1250 246707733 246707737
    0xe1c0905150906070b130204020f0c0105090d0c02090604150b0301080d0216091e0e2802010906050a110a030e01032f0d090f030c0c0602150c0d090507080f010b01050708 74
    0x1d401038181c42c8166601501b8000110072920000e4100b0b002003980303c0806c071980702900b04204031310000d00c21a5140d4440c655140c1c014540b050000703043c600074001604004600a41120020340f01082880c41681011040b4003550b00602d90008000b00421811a040c089420f0800052002c4c21040c8000040020100e0041c01f64110b1280d0344d007a41c440d10040d0054000540814400902c0600804066140c503415404070411060b0003003e4141280f8800384000d9001c10760584071200c499051540c00c03100c41d0000701b80c140900900c6c8182c0710311080100841180d462081d981c15122103a039500041c01d0743d41c5c800c0000e4041d1b41e10788540b801d41c10076690300f86100e5440b0ba05151240407400451019000344107000c2d2220070b61400c10414540d04c24092495a03000b180021109992808100d0782c0d52a240c904601000c0c070400818901c0d985c403801000819048000440e044086444250801d1016030106026921110105004007820300a21540e00c50900b090790401c80c4a85440c0d00318 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 246710233 1250 246708983 246708997
    0xd050c0717031606060504060902130b0c07091518020309070b0c0c1801080d0f0c02060a0c08130305010605100c020d0203070b0715050a020309100e1c0905150906 71
    0xc034001240203a4601c0104266a011103440c4500d1943c2c910f60b0520100901c0c072409040c1c0503e040101c007090084450003220705003010060701074442450121601a140c22040702000e8600411a0015080d80c0b20702401005090705102e21340d0b024902007028600101041109640c1c0e4014410005440c1d00400d40e401182c81e1a6160743e5034480700341034142402c14044220f54000b010110441c4080001601d80d410b0304c440c407045614401c2c9a0100b03840c1d42d006110341d040010050005d00005092241c003420000b80300f0f05000006c00340d550344030449900312410b415945256060300b081808424000e103801405d0989090410401c070300c0b0002c101d103810f010302034000c6480040200464030104481c200600700e44180e162a0342203860010301c1d5800c01c1c0c610303071034007414075010038072240d218401c5a002c1c07904400100140707020f8002401c0035200601000480d4000c1c1131000401840c58200e07412012030b543d07102c860b60b509050030800507603c601040b03a60b8480a000740300440d241c4104542c88 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 246711483 1250 246710233 246710249
    0x3060c0e1c02091b0a02010209030709050108030a050f0d020403030c060b0a0b1b1005100611060c0409150b0f120906010b03041b080111030613090b191404140d050c07 73
    0x319541300e003e8000d43c07008900b404400e502000486170495541907000c2c04800004500355803800356564205c2050f10402c0c06042d203d60003c2082700e500a000d40010b00c2591840d100c2e070307410b142a60800d1001ca0300103034415800704800b105e10604100e090710404249a400f107507080442400c0c01601c42d09401285203c181e412494101a100400308105060780300071184002d004500e031071100b003031405603507100e4a80480c0e840d4807451140003012070400e00c26004907191600301854022050b000e849180c2c0520380802e1185000320302001d40c00028024841c00030340803503071044844400042c545008101c103190790006c7d801440010310107030840c0d800c140c00000c1000390120703020150150b4620303980942241d62811507a8901e200c2500c001d1032050304100c2c1c5130441c040e445a001000d990210400610380d070310440c0020f0b084521003100003020a001c02d000942194404801e4440c0001901e088d24607044400c001e40d01e944040024410580c4503140044c1040c50450051740c1c0d6040b40d0140c4c0507 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 246712733 1250 246711483 246711499
    0x70e041b0f0e04050106090302180603120906070b0a150801060302030a081e0d090b150a0e070e04020301330f031d0307060c0207080312150d0c03060c0e1c02 69
    0x50854460a80e040702920003c0040066582d1420040c2c50000301d440101c2c010403c01c4422013040c0002007100d4840c240250260082180e01c050b840c0e407035842982d0040c0c1c402c00c24003098000c185d1240f000d511601c0400382c00180341c0c014082d040801e000360742c03060815030705207481840140c5021600c0030b000c951045401c0e0312540c20002400310102e54111803221501e001c07c82c00014813150304182038907400754110481d40d89a44c0c000071101e1040d01015502b0055140c2c00b040080005051640d000d0004d142041e42460f9984c0000c099074000c0e0b000c1504900ea14001034940c8021401c0324544410451103d1030288050030090701c078250200c1c0070b0007070664a01001407180300e4416881e40c0390720404192030b0744860038076240004050f03107160b6100600c205080030954000000441d00d1f14008070001003506c1e078401c8071000800c0c001011107600008458940d6000461a5507641d014600c903070408102e6030300c50040205100c21a00c3d80900c19035000c0a542c0600b4a010042440c00ba0141c074191 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 246713983 1250 246712733 246712757
    0x1502090301060503030307031e0b0d030804050c0a030c0e0601020607120e010204150c030201060b0a0210050a060801360b070c02280e061504050904030306090c08070e041b 75
    0x303401082c140d402560107010000400100303551550001c00092901e030020400350388020001400c80d620501a075421100d01e50900c400b19019441042d4030500c500121403110b031004e03012a05070780c25940103d4040b1000c81c1d0074882c000f801e5004540c000d0b801c0c070003171903140f60421009154800300541c2d0103011781d49640c440d403940420b404850280c100405101140800003000400b0304107140e2055006520f001030204030f9140300001c03210301e202d40398001d101c00304941ca40310000340340c003070104100301d80d45000001d48240c00b0b001b00c80d003101e81c410f009185800c0c00d100844041c1600c1d003043d072010090700104000203c2c0503a1040d00b10200c1c0c0340c6001041d20910210f40e80c0c40018490424a56401d88581d25186e0780c2c01180703064401034800758205889040134084070310f441070140b00b03180a041c40301388074908084401945c001d009140100d51240d68002c20340c01c5410700040c03440010000c200700310000da00685182a80401500d0400c900c000006480e421b2600d052000b404001a8040031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 246715233 1250 246713983 246713989
    0x1107150801031b0806310201050d0b0d0506040c1d100614090d050607120e0a060903230306091302010807030216020627030d020c0f040f0f06091107150209 68
    0x4003004e0280321049940da410083d083d03030b50741d00700001e0803180d00f0640d03e0b0000404000800c484140313903068581c5800c00d81850303001c2003d800d84243c5d15800c140c1001003403012650800250780501c0c01000746000480c02c0030b02e40c03078604010a00400034030f0154014481e1601c0740060030412142c10785820381041c2e8041000322075503c626144a03034000c08130710100041c000041001c41c01070009444034810103072945842e2054580300da010821641082d24098003090440d040115854880e2621080c0d0340d41c0c000c044600300d074901101441924001c41000b0f01800d2001ca0160412810490310310056410350008082240c001c2c031001c03c041c2c0124243c000b9011321400c1e008000e500606003900c1d803616140c0b03038602040111a40d600c2040540745281c0380e081c081803400d280000c5a000c6d0000100c60002d0100c1242d0340a0540c2d003060362810b00c01480d240ca03214915642090213000300d00680782117122010741c0c0c900c5401c00d019050402c415000900303410807403c0b50500c4001c0142c2c4400340c1e0400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 246716483 1250 246715233 246715283
    0xc09021803030c010c03061203080c0a020f060a021206060702030a20040e10110721020a0f0506040507091b1115070203121015120912110715080103 65
    0x300e5018480896164032034001900250503800080d13030100010341d81c82082651001441c4406000704062401080310052618004d10114800e03004985804000c282190b1410600300c0f50781c40029800300d4941d84507a40080302d00d4100c4011101c190a04c00103400107a15896040e600511118071904580e0780402801d03148100c01900501c10003000c0890401c0700d443d02901c5108a10241c6080c1240001309030550544a105400095503a0b10101040051811003589101e0b641035104480301c0e08001500010850b201d94403401c00340403a03007410320b0107034a8044550080041c55003080003042604030042001c03030300b00f01a450310380c801e185030305d6882e0b050001d895008007c15a8050401c0215600003006103058910342d050200b641c1d60758000c0415040d564040c0a00900d1506d62100b10240b04072110344040f000f0f198000b0700d032415a076840705003000440d0b0306e6000c1240c04605039141601070099000034840c04140580c8050003e400401040c0c1c140001402a0302d921080e10180c000041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 246717733 1250 246716483 246716527
    0xc030c080a18081908070303060905010b0702040e011e09021c03030e0d0f1b141501060f23070503041509090b01050c070902030a020d091209050d0c0902 67
    0x141503510015030300000c02d1140412034101c6688040b041c00500c0c04400036803001d0b024484090702200400c199100d1240c2e0348412825820036072141c40101c0c0c54911031103100e0007000c001d60b4503030b40e55034070b841400203942c0207030344408143e490205010803400c1c0c411740c0d488105012150029040340544001840c1040508560f6540c4080b90303040e004154055001d03840003001c180484012841d002d030700f2143c500300420305200040482095440c140304031100c07680418801c541d100c41d0849090101440d0104800c0320507035035050440100445500508000c250b20054503003103401c210941c0944030203809000001d440003000103643c40601c1418026903014042c8111000d21028101400170204142c0380914400c680c41c14594850f1503014804541030b91a0800290007000d29005051009400042c5101c44c0a5000c000300311895030203108082c003072845803c07040300c0080300a0006009100710b0300494010002e10b09132304003041210807a4812160038074800350b40d6080001e0440980c0d49624 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 246718983 1250 246717733 246717743
    0x18140121091703060414040302120d060302060d0c030b010c0f0f06021209060610030e0d080405030f040b0d0e060408220504050906160306050a06110a0c1211030a0809010c030c 77
    0x1555010b01da00300d1000841c056582100e040c48904291803500034603100030348000303000d42d1000c84215210b190010140c0810401e42d0800102e2035a00c1d00410055403040301c3c5000c041307075110031030000d1907003602c280d1a8044080c6410008100b440c2c0c0c81807240110a407001e0a541240f0f442e80040101a804a42442000c2c0b2550519410b1200c3d045544000c00d9a84520034410701c0001142d140c4a031041400801748200104661031007690b0503941190081c000f030b074460008100d04c41510007000010001060b0988034196102c8010f809602222204041c2507516000942800f0225a0385003e44400e50781040500304d41040540c445414251240d0011303802504100410160004c0030031964411106c0d2000c3d0190311504407011002ca1b5040d010301607015400340400d01c11584191021240710100b03c0c21a910740c180c80c0c4803070008030100c2e8091b5002001319180c220421618520b24030001a0030b074014807502e1995030351340d05070380a250015810000140089411306200d10b00e10300599403c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 246720233 1250 246718983 246719003
    0xc0306130906023901180b13051f0612030801030209070e13020403050d09050907052a03091c0309051512090d090503150c0f0c0d1814012109 62
    0xb0080c01c00d14200103800074131020101d98501003c9070600aa041c2c0c009000d4040d17410713a40550314014482030141454595003c01c0d18446d000071820072258543c40c4102d2103072111514611180b0702610b6080e00040420540c46052400090f00a500c080c1901c0e0304564000c4242d0303810780110744050560400c5030307105000c1050580c1e0f2034081d500501c180c9015100ba10355001c01080c0a4890003128858113030410410800200018810005420551100c40f46d10042a40d10f502005503081800c1c00d001c1d1603040040c02c200d0a04c2c09207064002d441c2500c030204002030040c0c4014186a07810f100d4a40a100c1305030501350150101000c88029014202c0224490b08141c0012940c940b444030003500400c111640c0800d991030009100c1100442c010340c41c0d040381d40d46480d15100c50f08451a44403500c442801802c2054030144500075010940c0d5640301c80c0c10314098403020038071034141c1c809510300098005400050364401c240d81503020105810704034200d50400c034500240607880300640300f031840c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 246721483 1250 246720233 246720277
    0xb01141303060b09060f040509010f020c072c010b07020a0b0316091403060109020a09050a0e07090e06030a110a0803040303030204050f010306050612040201090515030f0c030613090602 81
    0x80444000c0c0c0c2e01a500c1009001240400d202d134000b82034540560003030b0f100d80350b6400791400ba0021507001d9030800012440141c052441c000341d030001030110300c4c19000020107001c900c40c078034404061410b02c08681c0501e0019081140e0403000103003d030391129100020079405648460034580700a1010040c090764903d0071810400c80f0215880c5404001200713503500164081ca10300c0d4140d2011801005003085034684012880294001c2c8024400c1c032216250004260344c07040007250061640000d9414a49800c441c0108283c9032504001040342d560004c0c8039054400140b070581140d03000385546100b0120f500020500d000baa8004042d51000040101c1015850740203441142ca090320100b0501c50070000540903544240100ca800c42014041391004c1c40c407004110382c00c14010f05104441036200c5d408650a1030000c0020820b0280000c2480b000c0e1046032280c95125202c01d12090450800300001818200780d000404030701500da002c0c030303810b0ac2440d90460b4160b6910081c1400c5400e1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 246722733 1250 246721483 246721507
    0xe0405031c0e0d0e03030904050a0b0907050c010c030c08220c14040b0a030302060f180604031d010801030201020c010f1101020307020d080a060b09040f0b0409050102130b0412060b0114 81
    0x5034603180c010b0382d0040d080c40b9102c0310b00130b51601c1e404160003000b650500c0c0c000c80c01d00000b028002c04160540d500c139528101662280c000d098000d00c81540c0c0c40e1754031040d5092207829100d64a200400b05480e004a9500307aa502c1145190000e104010203860082607c41c4008010012180503080c025000f000240341214504d62221801d8107071800d00013a0144820441354480078400030700941c001c1c0000903640300c000c11010b980038821102d0350300e1802611188034039003841250304901241c40d0309008807190440c0341e080d0040400900c3c10a0380d0f50304583c0002d442e07160442d0914144001c41444452842c001c204002d440c0300040000c5460340780c403200081d640c801108050020491240100780b00c907246000d9002a244500401807800000ca01400018806910b031440e4081d92800d00c01403d0f07445000b01c208240c054400982c80e9502100300301408105640000c030505002c20040141c04204001c0c00545600060000303458501c0100680704d845810540759000d507000540800e21039 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 246723983 1250 246722733 246722741
    0x609091806091e071d0702150c09010e1e060306040f1814030a08010323010903030e060703061802070611031008013209160902040527010e0405031c 65
    0x2126000911051001810050ba01c0d40d2590280c01c0901101d0407019001080c1c0e170000681050b8a1b1040b07d11128070b402c8003074080ea80a0ba0380582c0fa010000d0348681c603690010b26030000040031a42c4007100409a154016900a90710744a40507000100000d4990b80e144d5000780803d0448210a11402410251070340812505081c1245d64022124a103041d0304400030a841c8910b03200d85407000a039081d40c4442114100624500b1095014007102e6104140c0a010f0300c02c4840c03090303d010850400d1583c505042c2000141030404040c5085400c2001c3c00c1007860483e03d080c0c0c16080166501241e04201014011680070050034100c000140321156200741b410f803048580b18002003014015031340c0b104840d0a8110090b4414a100081141408035022000e80d0040503100407154000116200b59014200603400024800e501050130440e50501e0a000020448004442c001100c00a02c80400f402d50601038109914039040000d010098100100c4240910060200070740403600d1a15601034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 246725233 1250 246723983 246724003
    0x20a08010f02250c061202071205030709080c061602030f030a0f02010501080a020a0512070f0605090405010509060604260a0c06110c0102031b010b0a121709060909180609 75
    0x6101d1243d00620081d4440c10b426500301c0d031055034890001d140800c100c42e01ca03503031a482001c56a00300b00000000f22810341c4010f651302580ca500b42c80713191040300030340f40b50040d5003d15903c6d080013100a0301561000111051001e00d400034011002060021902e0400701d802402c025220006501d52410380004043ca6440c07030950080c80107030703228141940c0355007a41c0402504843d54100600c110f2400e1580901e031225003004413101d1070340c0c506440048442503440400400e50003d4a810903040900586024003001d4500c11107604001c80450350700d20440c03044080c210480a03001074412000c0f90902c015808040480d5458a0780d4104001c1d00481c0d8829480403560721011000042d501298202c00c01034160007650a102030281740b2020417040000c10010340d50384000c8820030f80c1e0740d1101c041c080c0c0300e0342400d11010700d03d034030b021a0b000120844c03180b80b031030040c030408900c0d58992080391140ca0042d42d540200b030700c0754a0112000d150701600d42680b4051001048181c0300002091050303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 246726483 1250 246725233 246725257
    0x30c11060a0b090907030201020a02090a02120c0d11040f1a07080a09090f050702120a0c021f0201050702030408070504020f07150f0c0f0801090c110a12090b0903060f04020a08010f02 80
    0xf1030321075180d901e681d0480c51000a015800940f8010701510341001a21360081052101500d084001550101d51920840c1e100040c03a901040740e400b618094407d0b070545d000190b0495260505040082c09825541d2107854020b0005020f1204a0a1507000b07480f4030700d070301515450b1580104500a020710a01d40509442685884c034204690051405003074003071a8035802400c02103913005040c0d4410303442a428802841641100c0c180161a5580751070403d48615424109410100c40d000382928009402e4104643c0b00340001d00a4000100d12102200d000700ca0069840600e803581c51014000c0c60b401400c0340c42e03000445660560203401c060b10348108840108180e801c07402050355040c16481407100021121001804010303072950107500d112469081c40d9110007e00030402d841d000580804947c4200b0b8805000c0c5a1a000550803024001802c8000e08040380e0b0300c0030170b50b11400200b5241c04030340d5a00c013103415034403007540ca038000d0400c500090140c4c8506083d580080c0d4130044510003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 246727733 1250 246726483 246726499
    0x71205010c0e0616020307050a080a020f03070f0608070e0406091a04051009090503070203010213150512040b1512070e0a020304020a0303080a0b06040e010501020607030603080a030c11060a0b 84
    0x1a01e00c50340c451164902c0082c50542020b00384440c1c0250880e2040c81260544079110011443e07035104104600101074807401026000007500c10701911450180569000382d0020405108015180ca964000d8075410304d0150000c1d40d502c40120f03504034205501c15000703490544041602003250304841d801c00c80b200c41d008002c2e420f000901c411620704550031b10700c017000d10f001400342c0e4400b40c1120f84158054800c803030030312034190006405caa101800d400e000c1103c2038801c1240307210340c1810006030052030411a043c100150203004060400070b100600c1c00380ba8034005194000001ca42e0310b4138141c05810203500e405144c95a503500e004500400d040341c07400600180c1a480d141c02140c0c4100e0f80507000c0c0c4541407642d58281c400680140c0705c840721986840c0d00d00306039140c2034090300003030602818a6069501d41340c006414040040c0141040506007202480071070f40c0b01c0101d6a0141580c580002d0300810504102c814151032040b418042c0a1941840b5604120b0340203000700c0c1000700c40d000d07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 246728983 1250 246727733 246727751
    0x30703062102180903162609100e0108060105090103090b1f0e10060f14180111011a0f030708031306030516020a060207020d0816140d08041103010e07120501 69
    0x30704850000c8074200301030f0f8810008408846c41132215003078039510640d185007c0c1d0328100e40340c40c40c04140006045045c070001c510200340c1d16210f54050348240035401c151003070300c50300c00c0005d0500c0c2000744114148040020707401c1e240c3e403195100f943c585400115014450500c0a22007114082600c0030610300b61080501107030030759020a90700e010301540030000f85000c0c9019011759812421151103402d0203900300720008030350b0081f402400c40007141607090140609074000504041c22180803c04140c4c509080c403c14504c50002901c14085e080b2400c0703042490040001c0e03d000c1c4681c0144145000101e80b40040c0c0980d240d2020588280707803011b1146640d812145101004881c030f42ca401648485c40784408142c403580200003503400078110b60508000c94540c80c0c05944a0044100c080500d051444103100740d50751690540141c5601508444868440051030b1440207480904140d005420b4114030380d030250301541140301d000017520700c6143d070364010104441807044207603695400c01a4003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 246730233 1250 246728983 246729019
    0x9110301060b03191104080106050a0608270c0402131a0a02150a56010e030a0c150243090e030918060105040506030703062102 56
    0x6042d00c40720405141560384800c189210941003020404020f9650003000003208207140080010740300f8030001054543c6020148141e03801c050340b001003042810800e016948810403404003c002140e0b91110114916000d96801c0c0701400c43d00ee613000c4d100240241d8646065010081105c103c01d001d1054940181c010180f20f10840c001500141c201800001241301c49000d89600055095070000b40c0d0305440016016043c0c2c046c401040103000c0145d62408104181c4920b021000744915510032213000c10600118103004d1f103112410b11900c91000c13001c80d10100003030a00d164121060000d0f260b40c0756000400718010340c821800501458200c00c4011810074001540c80800d50428100c00d01510f44400402c6451000004422020500011124082e02600304165003510196a54245800c100f0242208003e41040010032110402036240e070803500f980c04440d4180d84081e03490b66500000c50080010340c000e03aa010307041c1224410707032400002d0911900e5109035070040d10035800a0107 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 246731483 1250 246730233 246730241
    0xf0a0621020a050a0c051501090e0f0d0509040e0c04051303090618060806030a02030a06061e030b04030822050601031403031605131701090201030b15030402060f0708030a09110301 79
    0xa04400300358200a400d594034440c030401c21041b4012801e560504030015540009044c081c0d20820780b458440000b544413110034400d4028901507030f0b0045c810181c854001801e240550b0488900c299640c452210364510705010f1003000c0c0c0c00080081103145020000311412001c075072010741c0002c401c104046000b81c024461400032010b808215100140782a0342112000001491541c041c004e640c2941c0040e24104882d211a520036200440c103d0f007020301d101540d4003003140751410000004801c0001c036103584611034105070140350001042d81c609408900e40080408030500712601c42c592002441408503059042c4d0f03109444131098640d500d00140d03540e01058661044081303542e07405488440c080d500904e14001d9070080c2007078055031201805400040c008441c0c49507516031010904540c1d1500c01d1445190342115000c5115000010303010040c04001d000a02402d8000f8012200031480e40541d104107a0000e1134035641d1400d800e0030800750041100c21900600c000310100200e19040c01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 246732733 1250 246731483 246731497
    0x2180105130b0a030e0a0c05010206060d02090a0c0e03070b040906050402180111160f0f0503030a05160f020405040302030a1d13020306060c06040f0302061f140f0a062102 75
    0x706080510705080d001d451561003003c1c44401d0503a200e617150500e44007801104c01441c090880d00000c90b01e800000ba081c03260003010a0300ca0003210003004010703961984038581000c001c00303000540040002040c0d403803008411038141e1502c41e020340020072100c2d140091085d101c00600130302503240c0d9402440164080d0900e8059042202d010700400c652003000d0f00740046824504940c1d0804214442d07817802a440d4100c1901c484c0780c400184414101c030b26007840200025401185400d180f0200108103001d14001c04a0385a5a12150000d000000c90440311168000344204801d04251030044c2d0b5944c407500d82c0b14049000c0c2421801811004065094008000b070564500d05881c80341070002944024200c0381c0c0800c00b40718a0f0000c0100b0400300340303d07038801e02d02d02c8040699400c0117458840004c1c2658170740300198906001d50800c0f200c103403049500c02d243c6107605c40c0d106400111000c42000b080da0b00710808400010300a50700459560364452020b862842c81070050101c00242e1103000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 246733983 1250 246732733 246732757
    0x1006320a270c0509041a060c101a01020616050f0f0a021908030604150306060b04081221040f0605090601050a170601140315010312080601030903140a110109050102180105 75
    0x1000340e84c09410300d9004042d82d01d26180703802c440150b4404c002299500300c1c540d5118260310581885070403150501c0f03011a03603440c0c001c0250520b03414200013987d666004129841e02e40c12031100707000c6d442c00b1742e080d9200d000030703600142e8a54105000d00c40040d0030408841d4010b1050806111503441e151840c10102c5401c00c08152071541e619003804044d20001d2440da003211920600000424440d114140140a0701c10400759110b1911070120320344890810840c2c1c04520400101c0483c500d070031101d21144408080712072065940d410401280031141c00050a19410601004495840032400605807082240c004180036207401d00031079000c0c1100b0060000f40d11110040c0b0003c08a2620024074400043c111080c41d2500780ca0002801d10030781c411160f008400d884101020f82010005a0240080c84d0401c00d0130001d45004150390039011100350650400030700c5140307151140501007441d003c0b400c000e108540f03071480c00d01c3c000e5000c1441200800381000f0b00c041c040d0700c55001c642d80c00c5610 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 246735233 1250 246733983 246733987
    0x507050a26040816080c010911090f0105011d03010203070906080901020f0909090102190f14070f02120c0312280c060b010c1707051006320a270c05 65
    0x2c0d50300c0030910b03880000c032803030a400d205a00e000020340c005c008000403260322001280081442c6071015a015190311810310905581d401c00c14034041003a0091304582003441d004488501c65003420070188901c1c004190554000410480d209400070f2890044070340d941d84074141c3c0d0b61201c1c003841c02c0b8040c0701d000381304822082211f51103903d042c2e41c0c6c0350f41060030750000620304070983d5141d50300c0d0900001c800c00412010000e40d140700d0741003050044c400e210407034590700e444038030340d903140c0954034044000b807280c44071440308118042c2c2040046030395070016003100c40001c000043d01074682c00004400b401e8200400f124464480c269902c540c41004030745071858220f640c1e81e02e070405040c51905990401034540040004940c106000000c09424042c1503650382103142401c03030800402c030400b10f030410f013407080820461004405140030203055403650001c80d80044076201025254011595103e0300003040403a0303059140f0100d0100c1841c03200b001b4420441c068581017035411240020012030f0302 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 246736483 1250 246735233 246735241
    0x8010e060a090b0f0d12020106090209060d0c030b0406060e0310020c0c01080c0705010f24050f0d0c0b030c0a02070609080705130b100f030c03050c0412020307090507050a26 76
    0x41c90f0002d0002c910b008003080ca20a0082011880b4070318510025640400c1000800040c1c54080c0307c0c01000c1c042040c03003035241406050100300140305004654520f280e42e41e404e030050328400e500903100c41c00018014010a503903500000c0600803031007502c5100c1c0c000d030280c80300c0214240c82212400400f2902a1041c02110001076500801c01050300840560801c0381c0400101d0a11900b0f14400070410002900d8800203880f074451030050040c00005e1820030070922081e502c0340c0c0b80e43c013030f40021160070048a829242c40701704590b655200405207000401030041403028071002c0c00725541c150303003200c022641d190000ca8015026100c1c1e98580d030410344060006050540600e41c0c03580c030484c40440c90707006601c045404205000560000034940c040e0318a0302c4c0d90705015540f03040b0303d14030b000e00c03060900080d1404148114400d60074008595500441103440501640005000e40352040000380341108014005901c0031203540002000032005a100c00400a03880c0303081e4000c90103103003c2d0746d6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 246737733 1250 246736483 246736499
    0x302040e04022b120818060a0b0a0504110a14040e070f1e0c05070f050a090213030f0308040512030403020303040b1b0a05040e010e011508190203010306050708010e060a 74
    0xc40000c244005100303141042080d9852040180000f0340f180020809500b403400c0014219103000e8411580784c84c110000003058075002072003a411500328080040c00020140004100b401c0301d501c885c2c0c0082c127224180c0101650a030240000c1c140075298030303200a100c40103164a51145000c1c810710031442c9004200c0852042c2c085100c03154450070800e00003044c079009510071121954469002405050300041008000e10641c0f0041c0710041512001030300b490700003111301c1c9003405000d41203640030a050b054100410b10010046801009461501000e414010b01160782190192124843c218000600c55550000c580c85a50154059415510740340daa5034020b820160803034100714074104032030550300001d000502082445480d0a81c0e500e184c891440c00700801688241c5400003070b40b00410115610185e403c0d403022072490080c401c2d507111880d502100c90341c0c10041424501c0440044100a0194082d074040d00c4a0f41f5006c3e5180e980d1030309014260b100b2104a07800c081e020a007004505 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 246738983 1250 246737733 246737749
    0x120708060d020a08010c0f020610170724030c0203090d02010804020a050a06030f0f0c0203070f0c0b0409140906100b090310050901090b1501050a0e060c100c0e010302040e0402 77
    0x408000c2880070010801d4000581150442d0440040f603503440c031060407260f0b004040c00c103007029603001601041c42c000303140060501e6148034817600d0180382d400385103101307405100c0200a00f01502c07038500c0410f80c21102208140000c005c5201003850480c9100300c0a0000040e03c001180040441b0505100c0c4d43c01100d0113000034100b05c0c0c009507840c0000c1000eaa0b9424048040c0a0f584e50000d031710408920400705840d0300301500c080107072906c0b080b0440b8aa02004441309682c000104480c480700e00e240a0740c440b211580500c200c0300c030202e004100140241c00c1503d050001d80c1d0712070003a486128a26485000540d4074080350011040e041040141c40c2c3d002c0d000120009086c0c7d902103d190100f441079442c01c42e110a103503551640940c040141c03817074005401c1004c000080c1c82400020001920f40c0c41000001003e03c03a46640400144d07903075034101c940f92841d132000e50703811000002d404000341000e405c0500109010b107030940070a512900c00c2c0c60446101003091819601c0f03503001c2c03054070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 246740233 1250 246738983 246738991
    0x172a01050a1823060702060d0c051303080d1a090604240b040503071a03060405060406080f0105040b0903090a050d05030909010e01031e0308040b09030c0a050c030c010203120708 78
    0x405640314040000c03141905100b4020300c0c1018185200508005043c000001003508881c0b151400340517900150300c0d0b03c0709480c030300224840b0003d50300e105d090096500d40034114808403000c80c0e007480030007001048e0300030305055042520144440c035407c0301c02241010340e4002042e04000b04074009a90703031411b5008240742c1d1905045284d0950029040507456580d29009080d00600c000b80820841c01c0c1004040020007000c007950020703c0d50603104070100c1c400070384800d111702d071145e02242444e80d40e5030154008000c510304440b216036081c44045e0103400d04030303400e65060000e400001c0c120380021049030f04941005010b0036149003020100081d40c5080701c0262030038402800240415118003441d05c0c040c01038000c03c000c0381d40c994600b07081e141602281d080b1000e07000c8205400042d0b000144103402036070107000c03818684d40360011103284d070007450340a14080c4183d45040060110104100b1b03d103410076015603c220811400690b502c4c402c44800061380e9280b00c0000745410321480c401f80d00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 246741483 1250 246740233 246740237
    0x20f01080613020a0503060a0501080c04090504020a1206091b06020a02010c150507050d0b0607030e0909102414030a1e080a05180910060c0201021006172a01050a 71
    0x10b08810b01242284c00800c940c4001c2400041404103928100c0d0f4998014102481d280302645001d140e01405070180340300b03088206440f0804641156100f50044004e0504642401d14100b138030304082c1c02400c81010240d502101e00e0312850340d4903803030003080e0301a580300341c0040681c06115401100c0903104140141d44c945590300d0080800b8807a03000d00742c000c59081e80e6072a1503940078610b103400c0700d00c90340340b052145004104100020344c1220b5065290301c000c40d6282c085035244120345051030328541042440500c0c000410744014030316002d00f1605010511240a09500c03400040030042031503507183ea05d640001da2400006604903020010342c802800392903503210a980c0c1c0e122041d00072600290100700081000011041440c1c1880510801207c05422038106a049400061003074091402086000c644240c1564000c000380000ca0582e0b040030420a41c2d2508000b2000d610440f940e40c440c00b03030883c140c03c000c0c0002c44860259807074108112000c12604010340b15075100c4011901 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 246742733 1250 246741483 246741499
    0x6130c080a050606101701050d0f0501050703020c010f0b1503130b0405010501090c03020a0c03052515050f0c12070915020105010509090304080601030b13050303070c05060c07020f010806 82
    0x400030014440d010030907108100410060400300c04000c0e400c9030014040d410016408a030783c80d010075070800703d81124406e1f2800c421001b420b003001d0908200c1e00002400d190308020a00a5490741603005211515144008104009403900e6540599000710300c0365500408080c20514200b410800964010b1030309044051045116aa0100134840889040d0b440d80d55403030042010301c856000d0014889407514007145041b211190250503941e407101c4c003408100010031982150300b04801c005c4500d00300c004100144d2903d80c41c00800c0400041060100d185c242008a030302c0d5048012101d0041154a03034142c05d28540804825200400904103801c100000341e00040003200801021183d00300359002040660400003030205660010b0315031999a401003000b00803c210200f0180d0550b9402850180303d62901c910003c003101d01c03000050315a002c004288042c068100d0030080ea5a4450016281c25513075502604603240a01080039400c8582103140b0905503101d002c449600880c01085a5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 246743983 1250 246742733 246742739
    0x11030301210203070801020901032019030608030f1b01020909190204030209040503090a08210d020d15080d0509130207060f020c1b04050705190c02101d040b0306130c 73
    0x80c6000e80c154000c41d800e960015600c4a03652b4140a0540401c1000c00e1580c6e90b41e444484c400b40c0391250590b801e07a8114080c4ac0d91200760b11a4100c00300a0080c40110b80e110090710300803002c0ea6105d903400c04921100201d0f0040da0b002c0600030f62340940001800303034490790f4402c40703154426040c191aaa908076806c000100050303544d510024019401500219181c0c0c0b440c07024001810501d07046407109a02a11305802c107188540c0001c815202c0d104903280e12a000218404064080d000034003061608201000c1003407660a0a40011940004100c40c0001d01d000c0c3c0640303c0d48100340a03c0d4116407400606180708910360005c140281c403d420001c0c0ca43c00d01d01001c0107d8004541d01129a0005c04107003101c0300140c02e00102c1d00b00700711820003850a000300f01030003d10910403400202c60000020303003c840d000b180443c1e083d0341c010344406206021510010900354190b00130140030050b4254614050034241301d91403c905000d4014061070312038030089104407200250444030714030050404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 246745233 1250 246743983 246743989
    0x1501060c060b13022512030e1606020a0b0106050a021b0d1502090102011109030606191802040509250e120f060108060f040b01050f01050c06150a06110303012102 71
    0x403100503031220040c0c03603400389401c4c014017805200307407041200d10828820001c20390342d5140c0012131105090020744410348a0100b410b10900d10380b204d801c000f0a100c001025600813a0070501035118040ca441a42e8803040c090b151409036030598001039021803809990a038080d51f016503200c0340104000d10013a41541d5908000c40c85854102415030041200315255070240903054120030740c07075403250a000f00b503804281e48460003001e491060307101088080c02c07580898440c0c8040e21171134604022429806904c8070195100d1710540380250741003800100d28401c000c1070f00304112030701124500c00d0701004c5e404403503a8410303661035a4800460a100320402c042041f000e41d6507107440016100c00d600d001045414076000508030b825102d2540200000112500f400c6815550b08036050344481c0900030040b00d0500610111070310521030072041c07145203140c101c901c003034600381250940354445d184d5104413031286080502a11581c004c0c001030080040710428984011422800f821010f0095000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 246746483 1250 246745233 246745249
    0xf09020708040510020708010506040b0d1709120706020606090103200f0d0302010603050105060418080a020a080304140c04022502030c0307030f03180303090e07111c030e1501060c060b 81
    0x1044c05031b4820301003000070580070b02850354403140440e4108001d551b10008121110801000180a08a540001000030702240d09a552101c0040c0c40a07403100100d1481565500f07860207810b016101c1c80001031100e00d05103035064160703944030b10b1026490062100302c0b01210340725100541d0203c44949510f4440e2140ca03c60f0304564083c0d030000c03d03090b14500304542140c1014004500442c1005243e0440507022a0361400c156842146140d0340e10980c4001c0f0f00700045e100340107000d02000802c1c4414817002c039aa0103011503903a010b032040c01821780c040000301c1c071804840c030300ca2811a15950700e2451400c0c04010041d400a0300340d90400701d4100000741402c401d40c0080701d0240003254110705040c3c0c49982d00c580303507451100303054405085860181c030011071480b84610710101000001e241c10320070326007a492040020219115280c16480344207203142c0c401e9a110009143c013800c0a881900000c4260304807402c1504c50401d44d0034a0780456a280341c0b070005440050721002d4120840c1c4071080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 246747733 1250 246746483 246746509
    0x30506090a0b1008190602120c0a080f04120f0905060406030510080106050607020f190602030a39080c03030f010504060b09010e12010b03070905061008010f090207080405 75
    0x292540001c039107840400c002000d40303400c6440e00c06074401d0000803800601005411520100e02d50503017500c0c60224042d200c0c0003022248142c0d8034040c00140000c01c0c010700b05440300c0e600c0d00190307036403a90b0140ca0b0740ea000f00c9001c1c0414001440403030721103004000104010b030440c6404245075841d1008540c1c0e03a0f01c88c4c0d0040d40003903560000c02c8030203600309480c54080c0c04030400a00215180a0001e038580c000c04001a1065510300b101144599408900c0c1001040400b070190109650b91806500c07900310fa4400b40c00b00d0300d440d8a01341004008600440264120104030500060740807400c0c0c0d410074150022911808100900980c1c0340b01000550710502c0350144010103907051906000640c0d8550b0f0080e0f07442c0300140080c8456a8001c0d44075854450305907169120313100820031031400352100d400381c50b8141c026083d0100b03118195812040c071912095031720442d1032540c2c103422207010000b44500382d692095220b041c4031011040d001013090a00881c03102e070074035895000040044070440 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 246748983 1250 246747733 246747751
    0x10051909050c03060906012d1e0806030c0a05130b0303161209092f040906090203061c02030d031e2f0f0405130e0703030522050d020415030506 63
    0x1004000841c940551140d1b8002020b18050040c0c50036840703402c004042203824180c00034080740300441101e1203601426a08501c9000180d003544410340b01500c80e41c0c040c0e45070343c004d025000703060066040541580c01210b00c041c10694002c034480f0034040044c9440c0000c00c0e41400204081200d0b118461303003000710300d805116610300490b102e074005046030400b6070080d110241010301c082003125800b05c0848400717007169140000340f4001e6806109921441e00481206450b00c8000705000035580e024611403281a180c00c169081000f0007420140b0009100942c9580500403001c0090711036000380180e41d0b00c01500e0480010b13600011010360349100c0d032000581c41d03000c2c007c00420b004440b44001c40100c00d480c40e07240507070341280d80c0024032550195600071003c280e001c208002c4560300000c0302c9003000701079803221501e902d03001300349500c40300710021820700480d542242e80010340c14002c2128001044000741d64003503803e0001425582c011003034410b4210200001048051000b1840383c4986 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 246750233 1250 246748983 246748987
    0x210111507140705161e06024b010218030a020a18021614060f090712030207030b01170d11030a030b180405061e090a1b08011b090e10051909050c 64
    0x41d5a89030a40c0a80d8051401c542c0b1004c141800c00350f01c183d030002c1e04480c540ca940420044090400d282e49040a4404270045d200104407807106410360282c0355a210080702d42d01c440c94420300f0140c1d200a005406544510301610401640310002c81044220001400c09820503840d41c140100c0840001c0060f944e685442c021110412810720065138801c8524039411003600303001d0708160303513045270740600070390310070000e45000c00e0500800240c401594400300364485580c450349900c0792400200b0050314980316519655240382d0040c03410b40f1a9001203801035041052014049018190100e00c180d00540b680b80450f440c0d07414020304510440c0140001c05c454103129043d82071102040030400449428031043c452150000314412244030b42100c0d0001c18441e00c2201e044142045600c038801a40c070b170010240d42e04180486156580c4a55116011126a540300301044c0c03010848801d021000e5440c0c0902884c0740c24078003488800700000910300181c0c3c80d031003c4401c5400580340f480c400c00300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 246751483 1250 246750233 246750269
    0x6040e060111010608390105030c09031e0705010503070206060f0a030203012c0106030b13061b080402010305010614190905030316050c0307030b130f021011150714070516 75
    0xf5845807651012250803102c21500c00c1114100103605812a11b6041190000c0070400c00d8440100791303110814004c0a507907400d03110112400d014403030706044034101c0c0a004070004041d801682a0b07445080c0c95000752400c0c2e51290204090701c500c82140035071000034501c001c0050b840920840e040501d00600308240d110268004420400c1c3c1c4412814050303043c01018800140941c045640080300c0d1518441600f01c1483d20038050010b111a419014500340f8901d00c030f80c1e50200103240201d0007030b2400c000c1d40c2d0700c40d03d045401c9080c0708155101381d00100007038850f5007030007040320200856524217820141c1d240c00000741141d110105602041c41c20030754003400e10070103015481c8000d5044005080e442e00d0355403010382c80301c002410342c040c801d07020711500203024014034206c0483c1e600401c45840c0d00c00d030000c0603100301c1e01611140114400d042094440c02c2c1101d0f20540070364a99207d400c51614904958941ca61104034111000d00400000c800940c1e508040750010b01038085003401c407440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 246752733 1250 246751483 246751513
    0x90103060c020a20030f010612030305040602090907050a1805090103330603060b03030403020a0315020903030a030c0f030c0e150412030c1401060b0304020d0203011e06061103070206040e060111010608 88
    0x158a03206c501159150007410801d601c0380c29005042141c1c581404030701580c65081040090269402d40c40c1c000341c41c9010050015800b00044c403030380c9080d4a0b805a00ca010b00150300c10302c02c071400b40e1a00304005c60f006101040030000e0a40080d82e00058103421000201c0c81501e2062056000c0140c0507107444040c020400c42c1d0294010200050340214105071031600000c000600c3d51001410350f0301204001d29080320b1580484000342005012241d032854001c1c00100104907945c7c04100080310499880c200c0c0b071107030050040007440d51742c5007401b13855800e0420030039080e0301416580120f420040010840003045020407400e000c0e44403d0403404640c1881c0d42c4001c00300c0034900342a450904103011662000d003d1700e4000d81c06032042000d0824600c003281c0100420800111a038091102400088041d500210305552240d41c41022110000d850943d59002d0900025400401444140280040c03481c000d03510140514043c032200d03498895103801c466003078020000680102000c420884 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 246753983 1250 246752733 246752743
    0xf0b01021203011a030c19080117011e0b03070b03010e0402041d071512150905011508010306180807060605040b0102341502010c0806150d0504170c0615030309090103060c020a2003 79
    0x1001d000001d010301d842800b030030751701c020f51338020207211503030303a54114156103081000c0701c003500c1030000440c0d0702c0d40c6a00c82c8010202046030124400d604101c0220708072803a4081c80c216200481d030051209a06020503da0300b0f02c201c2c1c159400304820703085410410f2036a805402c1c02c4d0340980c0c6000e040c00c0c0c2080540d50540303905030070944418610100e2003c1b00d0b41c0c0407003010b0442e40c00a0300000d60120301e50440015802014014010610204004003804003690088007107550840781000400d0b15000166184c1c0c206041350300400300304290b2136204265030380030843d0018801e4a4814602c0e1107503410490848901030040c01070703544100903180150004a40c035000038040f25400040d514070b0190841c1403048001202095448001050030040d0860205000880f0400102e0700e5a4420880c41d945a104448a50000c0d1440d082030006003008402c49100c000003400384c0489030700f9034031303000050203003060107000b1031150070303070740701c085420f40c1d0410304441780010130580a801c41c00200342c034203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 246755233 1250 246753983 246754019
    0x9100c0b06010309030206010b09041d0c0307081606080c0708040b071b050907030e070806010602030c160b09091008011109040c111c050403060f0b01021203011a030c190801 76
    0x410f04d000c0d070180120341c0002e0780f1811295407001c00c0c0d81c0c69440c0300204002e031100030b400c60040e6446600310601d00c400840d070042d004600750b084907a105d5958110a9403a03071407124210100020310400c0c05103130701c20300c1070744d0f40801f803d804d0901d05035403a50390038a01d0f407040d4032a94850002051503810848075500c00070b00350a0308204081120b060074002540302d6030207444101815610b0480000f1840c040c04061300804403481a100300707694a8074080e4076940701c03c40d81e14041c00340b04d025160840c00d10024a045d030ba02030b07403040d007040800003c0c00701d1004003620151104440d0400058403090034021080c6000c00032006541390452102031001b901e0981030440c061141d0160145001000011000307a0032450a0108003410300350300b001d076911b101d0760b00041e14903424124450144803c03500b26034030040c400c1c1d0803036180f0035000d28030405500007801401c18010140a6400c40b2240ca00040c40e00030400c804002d1802c49009100c40910f0800c0420202041542c0010801181507642140c88 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 246756483 1250 246755233 246755237
    0x40b0a0f110f0601062a03050405120102040b04060309021c08040905010503030909041104090209040605090601121a04030e060c0f121206120f0a08030a0c140304021509100c0b0601 79
    0x145004001e50103450b100140201804c2000100c61b601152419a000c4a88020f561050f00307984070540c10000d104e50301c1400340700c1c0525131146400b0507440051085030112400900214103003420180c00301c000e42810801a6408500a12200c034518800d040035508c1c0d0303100300c0c805a80c4d03900c1d20301400142e41050340428400c0c0c2007880011086d03120b40822035441540b20310110fa0842c0088009402400340c84406900000a44104410010b540d40064000c641e42c0044810581c0d0b10400c942c1c0c045140c201c000c2010f5401c2c0d0311032207403004e00b5180d245c01500c6807c041c0940b00d4454081141c1d40c11424802290340d00c107103250380303000c0d40501264110605244d90303e440c060814203000d001e69009400d1901540c1408008050b500091000c040b1002c8440241e0701c2c0b071401420001e0098105407240d101c92071504000005260003034114503c22611144858111703515a005c00601c44400b02c603920000c00100164030488e41d901a10400802c50750300c0301d14034030f00142004c6002103401041641 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 246757733 1250 246756483 246756493
    0xf060703080a050408040911031e0402011b0c051f0f02010507090302120c060a0206010603050f06090708270a0302161d090a020303130503100c12020c03040b0a0f11 72
    0x408a075105040c0d582c0025002c0002c1a0364846240140c0e0a201303c0d480901d4591078a40e01006188070341c0001c41c090001034000d40d9441e2046038030351001c1035050300c009020404040c11098004d0301c002c01d040d90203008010010a4580d02d10103d001c21000c1e00309510038000d2040d4800005810070000c052101ca50b01c003c00041c58005005001c900550201a1040052080304000080100452004154060280c64603400c0c1681c02075541d00f000e0040d80080b034140400111400001d07504a84100700c0100320800c2a101d0340010354207820b014102c60000c501402e000f98072580303440d24a080701d140070002402d03949400d050080c14009400b608a0f080e010181e800c0002d6906a0b411684c50740c65442d1400075600c81d64603444c900701c0c0d0310400070f400d40408106c40106040c65880c42c01182d0303082c2c095515849201d0700050440714086d4001b00403c0301c405500744d01039000d0380600182d074141402c40e4079040c2c0f20340160440c1d4000c50345120001e401544030800650f80441c10034803000c1c1d0000102 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 246758983 1250 246757733 246757747
    0x50703021f030f05220609020a030c1a0c1c020114040503180a0308091c060e030304060525030c0905040207080d180305270405040501090b0903090a0e06150a020c0f06 73
    0xc09124892800960f80b05c0c44e020b094040c01782c1c42c0d00100c04107500800c4085415030700c2c03a00740390501c20340c40740071080c24220b00c0c1d40141410070800c41d50705010700806000d0740310514400007003209081c0c920404540d61b44240c00408450403464a000301d0140d0011900d5030749907284806400500303260117008004a07202040050315441c15110503150441d0241002d0031a440c000851030010340f005050305040000b40c00f8507a00100055000b280a602d05204039520750194605400880e03654000d00c00c44a04140da10512035423000818000c0f0380780002929070f5500005003660082c11040c0c68070100011204104144d92161a55400c1c0442078043d01b031046440c00380050180001503003416440f00142e107406224004450801f9078002c00802c44c6007401d05155008101d40b6104880f003070f51003004110710900000c1035030707a119030013001d5500300ba00380034040c401c3d000080c213181e4119841d0b400c40c01100d41650007034140340035503600a10000030100100180d401001d180c09000b01303c00c004c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 246760233 1250 246758983 246759001
    0x30c210a091b1a0705030f040303030606140a1b021c06051e040309060302090a170a03020610140d0f0c0815010905070503270f01020a0e030106140d050703021f030f05 73
    0x107660404410302813504d0705003508026003140305100650700d1000000070040201601a0300c10342c1594542c0e500d0101909100009402c24440c08030450701007503e0718002c00d026807502c140707618281d101070000c405100c0e006614004d2109000070803030f100ca80302c0c02001a86401102c110305400801305880302c103810552800f078440912030168008064000841120f075484514900b00101501030307028030405880e845040d00c6140c0c0b004102e00500681020682400480e210941516415000400b80c90300080402c80d004402c0c0c270040329240000103e50740403a0f101287c2800078001d4401900c80c3c80340c40245001444416044034074503511384800d21861641c030005072070380980d044032003130700c0c0910740718592801c83c140302c25a51040c4500c04141230840010340142a08107029194400b108244100305420f0b5142c03409540b07044039084032a10034600c1e041d5002c03040b09014030161401c1036280d8000c1400d402003120708503024000c121002c926070340e061007030f04e440c0945070a0802c000c0c10140b003c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 246761483 1250 246760233 246760259
    0x607200a02150a090510090602010f0e120d141e0a021804091506180c02031c090f05070603140702010c0c0b060312030a0b100c08030c210a091b 63
    0x14a404030001c200000310500607611039014140c001d000c500780090700c500c0244032096a000352340041d401c4c0700720503000b003182d4040c01041e0720803c1c1c06840d040307958505094081d005180034402e82c40e140d000011030705190401c1140190098911034501e01c0410b10f6141c0d001c034014010310702103441009400840307015400c080003816421200490301890900307040c0d5402142c0000b0820712031800100140140350003c1c0d0803a101801c403814410300c210010160303103a0150b0011480d40b1040000c400400c4400c039804040b419104007100034025800c0d171038107494000386402101c0425998004000e8070f0842c0c2c403e9a40c0040d0720b10007806050005080203003884402000142808515404a991a0380510a4a404e030000311403940d160300d406030306000901101a4440d018072490f1404001c2e080c49180b647e041d40e900700051600c1d640340d00b03801c03078203075804208984c02c400c9200240203601070b1040c0105000300315200f00820070075402e080100300c1041c1c045420b203c4540ca0a010810541c81c920 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 246762589 1106 246761483 246761509
    0x70c034103071529130b030d0305281d060f07081306021c1a210102090301090311010f0c0801050607060605030607200a02 54
    0x90384200c140d10040d504405400400c800b40c0420303150f0140160844416100040c00e0304d4000b0368608060b1603410f540c010000007114008030780b801c450000c800305040c0304108040c90b55440047c1d41d510711090b603881859107400015a203c1b111800c00c1c0c80c101000c0d013011282c000713075070084401405180c007007030031601d2283c210103502400000e649214412150500c0c4441e100c0d00425910200002d142d20861112200b405001440b40e00241005010581445030f05801c800e0a0409840c2203d410360859502511302e00599521001d204110300a00c1c1404030490700b8413441035019204054115406600300812001015071251220030b1680444000300460442944604156003c10f0f5095002440b4800180264501a80181200e03880b079003001810ba5a1840405e0034200201d4000000c00d040654000d5500e10305400c240c000602c00b00600900c030f58580c00101c0c490440c0c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 246582733 246762589 := by
  have h0 := BRFrame.cov_init 246582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 246582733 ≤ n) (h2 : n < 246762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
