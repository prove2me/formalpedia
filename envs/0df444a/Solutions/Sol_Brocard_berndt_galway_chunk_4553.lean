-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4553
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:59:44.983624+00:00
-- url     : https://prove2.me/submissions/fe16af39-4451-4731-b71c-3b22c8a242a2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 818705035 ≤ n < 818884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 818706285 1250 818705035 818705039
    0x10060e0d0c030b09070915170c0a17010f090305120a060b03100302030607020f0706030b030c040908091804080d0c0e130c0e0105072a08060109140903130501050c07 72
    0x1000401c8000551054407810000e1030b01c000803505110454000c0c2903101d09144410a003204d0300c2c45010f00340c4404580001840c6296511185411509045a078000d0071840c400034002c2c01c2c4802031105950414024085412105480001c031600c41c00c00401050302031024410202d0803072407003903000c1030701880000c000d525840b01c0c1909400c00c6816004003003a5500600460030180915034110f0000d00041900407600301020b80c45200300c1c041c0c08101503448091403910b41d4104a007403691000a00208150095810800c080354820b420581c091300302e000044081c00c62003010340b440b41d90881c60702c900f05004851158084c4c0852020b460401203003502e24042907940c0e46020080340302d0b901d000120369030041c0c800b4001a9025441c2414000140440340100d40000c0140e02d0300309143e4488950701c078201c0c0e0b10840588140d080262140704240c00481c06072880d0380034584868110103980728691316414525600d110340302c08070600100c1500100a00c0d40114058034071070343d004050301c85681e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 818707535 1250 818706285 818706293
    0xb09060403081611010206042301061a0a020f06070c060b2815110318030f0f030309010605042d0608030d0212060d0b0c0a092106060603020310060e0d 66
    0x38100c0311203c500c1c03c41600a410802091000300c80301c4440a00182045e481d080c2c84100020a4032400fa040c010a07c1d00988901c210039440280540075031800460444420301c1111016081040300502622410700508c40c2000000341c11032080c807942d030380c070000100999280c6e005010030104164100c00c44074035405805007460b400740010007904540c8001e07545012007014110380c202e40c4040c28405107280205000728007104407050610240704035081d0758404bd000c07130702c3c21588413005407060148105103541c47e40d02100941c06a080e40000780070454a0301c0170001210307001c00d000c1d030b903858005000a0b03101301d072035980070605c1041d038000080c4240d80b10181405c40e40510f07142800d542c0d001070000100c40798018019000201900c50003034580c100d80d5007103030602004c0c1c01041e41e0302002c10803020141c407440700e0700050f00d2207840c0d40554880c0f03091540e13404401c5000403110075007071080c0403480700d1291003540d00c141040721042c00140d00e0404182c41203880c3e007200c80d400030410300c20742c0041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 818708785 1250 818707535 818707537
    0x30a05130f03080703030b01050414060306150a020715020d0f1206090e071809020f120109020a06111519020a0e090c09150906070201050c0a020405090c010909050903040b0906040308 80
    0x96010f20100b50740c0e00c0075840d0080841c0e0036001d415050100901043c41a00c01c8280701040d500c4056582d140e0302d8441e03200140d03c051a40b01d05d9080b4400018000b180150301042d46c4044038084242c1c401002900142030b6101d58400f00d87d41d000401b943c0c80d00303105502c0b4110295684801d032500049154a440c04001510b0340c410640f142d540c05034204008402ea00300300310380a0b2288103020415861568009403c02d071184540602c181510b40340c910107036900b0b5010200a5600030107150081d44e980e10050700c550f00290712120070303020f0700f1618030b1000000c0c08458420310144046c0d0f40750032070400d0440000c8d0408074600040011100003c9920b403254144076000e0404814034548505c00c4104000320f1403000742d00320405c120140a55419a1148010b84003403641c2400d10607150498001024500074081001940c01410b10b024401c1c501c1020444d5280040c003030b6200088d02e511000c007103080d030b203041d10a282568400c220400407507101d48040d10400c0002410700740b90541c1c81c1c0b035510032 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 818710035 1250 818708785 818708789
    0x3021602120d021b0619090b070605040308090313270510050406080708070302040f0e0607090312020318131104090c0e1807030506130f140a0509030a05130f 69
    0x10940c03105044010309030b01003001d9480312080b07190504e1300a0f00c80001c01d50317600810a4011014444019180866002d020440003804110ba150b644523040ca0401201a207000d50b002c3d40425200804204103804c0441142c5c2c0540181c10380381c03211840d202409030000301418409a580c02d142440d400426468002c1d0303801203101210700a50345040600708401c452041e480110580e1010204102c0e110002c28508202d1b601160002150aa141c80d8030340905500f8900d64120b014140400207066000581c00c0240c80c0942c0f00c0c03032200345160b0400c0c1d80d40c0c480d000100031956418460f944d114644141208043c11039000b0208910043d00001c0131650019009007114944070a680d4003481c0e030024071210003080440d00343d00002030344c19142240110251121081540390340c0040c84030303101c102c01c48480341d8480e1010060205001a660001c08043c6681d000c041a42000308070303410641e00925008180e210003452502c11158015580c2e41c1c40420700840c0221180e10005180d01c40e0001400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 818711285 1250 818710035 818710069
    0x2090a061203020c03010c020a0b040803060a0b1603090501111e0a06060f03051203190e0c03071203030f0c0807050711040606080a1b08070309050307050303180f070b0a03021602 78
    0x90000e00d04c8201401e40343e840320124215440510f019010070b178810441508950402800c0c3da0703d4075020041050519181c22154070001c0c00a2807641c4003400c2918078a1a500076501d4046698030352004580304065040350307106a91150750005c00140000c12001b80510030b0310200c929560b034aa82c0da03415500c1c164008020451407540800c18000305100202c1e440850030019443c5182c0502008150003880c184801c04641c3c0d4900c2c080829010030803080742c050020101e400c20343e95010304504c040500d41701200080e05102d601e480802032406400b41390441a1541e10705039988c000102c42c180c0100c24142c4103546581407542d101e440d540b14110240840781d89003141d919003550201c0030345600d101108050402e400300b032800144e2100d00a5000380c01854081000805410007a03d103005886010701140000001c2c8412860070300c0e9100d121052000a442001140d2901140c84902510a81c0c070301798401c000c405030042c801c0d4001d00c90581c1100000d4109401038001c510000d003000090700c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 818712535 1250 818711285 818711293
    0x2109060918010f122d0b040b1b040e0a0504021809030301030b090a0c0618090e010c02150702070b340c0909020a0302060c2104050108010f1202090a06120302 69
    0x809015041d021410183c04401810300d0700e079000d945e9560840c0c00ba02000c034403030903195607411450900c0240041e000e035081400c400c400d0600e0309002ca40800c082d030b03c28081191040f41781c845180080c1c2540c040380c20800e201d9000390f441c104203c0140000a0040341d000071010120280c038000c0f201140e00074403201c0300950b280c0d81146440e0021010207007915005a00455124001030003011001069940034908002c1d80302410f4110807040a880c3c00960009081960558440005501506409666a08030303800c00202d8980d4a100c8101946c0d41c43c0103800c4070303a003408691701500041c04000c03510180403c0340c5061003d801200440014039400030010369074100c00340241965504040d04410f5030402000d55941d0008900d020244002406140d0208005002103014403510018461504100c0c0c01c030102503401c10000e44c061700400307021880c0031002282980002c80c680051711000c40c2452403503035440e000c02840c41c00003000c400106417a4100490981c0000098040640c805d030010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 818713785 1250 818712535 818712539
    0x2206020309060c03040803070c0813030f0203060721090201021219030b0306070906120209031606030f06051e0f030106090906051e06120a020a030c0611210906091801 73
    0x29800c10201a002c2111540f090091102207501e40b000c032900990705040174030131003041d490001210b0081315000741e42820100300020078404001e00c40e040032403085003500c5841c0d5440c602528040b46842d41c585108006070341d900d4400b030041d808001480c2c01401280c21202c6407112186255110390704160f034070140b1070f09829940d5054010310060350401c901426041c81c1c04178000700080307061303c10001001030303049611480386566812101006405405e42d0003c40c01c041e85422000310510516000a1800004001440181c414442540d43c024906071200c00302e2103000c4031204100401c0c80e8080241480700d0050356003446050014000707101c0108145000d820300204a80008085c2e40c8450b540b03150003a0f1840d4085102644043d0444000706902e40000c4150325000070310400075009a400c840110034041010100d0b412130704240e44102c0d03120100e105564841d203070000d211105268103030302c9288005508024080001014181c24140f403c0300d0700042d480e403007002114404903000401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 818715035 1250 818713785 818713801
    0x3030509040509010e1c111902031005071407210f020c0f10080c070b09030d0c030b181e0a090b06030d081302010c12080a050601020a0b01090522060203 67
    0x909a80f022100008010441020251586561001e40c48110300c0c0345480e80582c0003405021342c0d40001b500201101c8540a0381304079182e40c904a1541030b4401c0c40b51032074400c102c400d14010148030341040d666285a2046550b540410380e0001c0030700b21f075168620f58610f082071076840046804c0848556404881c034130f90310006801e140000250900501010075600c5d1191501000983d60060510b03012409607035250030005140076191004003411100020302815440000140c844100701000030490303130b441810282c0032076181010454210080c0d40f050300e00410600010765000201030501c40340b0340741d01c2e600c286aa13030044401c601d02a07074030b0b100300051246031001d55921200642c01048800c8540b0f101525000009100802da2103066001c8411a40300703c7c0c907511340d0341c5e000da0010150043c0072405005844116040300e80545054000780c4c00d50310024600f1007040e041500b040d0540d090600701c40c0540001801c1000180580540540f96401c00300c070350003054080d8800503101c0c00d00710302c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 818716285 1250 818715035 818715041
    0xf0f0e0712024b070f05030a05210f06010e0f0a060c0510020f16020f0402032505093003040305060106080601030b1e1306180b1801170307050303010303050904 70
    0x6803056003c0c8003800020140d00b108415000b0345800105401e4460102d890175241204605400134058000400c0e501c0c2100e810034080d003c1d802084d844030200300101104040100b40444480180301c68480c0070130803950141a40c3c0b00200400340070501da01e503842c400f06a240c0300c16404040083c50400a441c2072120a0180c01d0b071000141c242940390101c8240c20104c3d5004070350b4070200000c0300079000821965144100318510a01038400d6449140074001103060100c0d564082181000c01d10807032000b548590100c0f40f1180c8028004100c40d8589802c004400203000035400d60829039102812039084c081000d0801142300f503004000541c100351004000681c043c045034103060030310080d07551640e0b0306e10320112060f511021481d0110034101c001103900002e400d80c2d0342480d2a040002c01c621002400c9181316241d441c44c2845056038010902240346101c60f08607110b000350341c0041c041180c13044c1029420b1710701d00d800c0f01d00700f503ca07860707040c00d617482a401200400c000007200410340c10140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 818717535 1250 818716285 818716357
    0x20d090c15021b210127110a080706050d0902060d0b0120120d2405040b030a02060708090d0611040302040b0102030a020a0312020408030c03040801060f0f0e071202 72
    0xd0f040703420520000011a11440e480340c4c26042224140c40a180d400343c00750b1184000c440f074510013800310352a0300342c03a1a030070301e0071001501c40c0010b0098145950804610b00c03000ca4a100c030052044600c0e00b0320403280d40d001130500f20031407910707070044d07202503500c04000e01b903022900040010280305030f0001400070403041444401d190f0400c08803a6192401140c2140301d0780780041d03441c1d0340d5000c0e080400001c203181403680100c103485512030f047c01c04411000c0d10907900107075010010307080143e08050340c03800c1015000b948044200304003400100d410300030b8104003030090280c0e1184802036403880f064410315400c80020340c101240030800d500d01406581d5011000f07001440ca0b00e00c00d80c40094460618020240034070007a0382141c44445800d504590003008060240c980f01c400140750030780c0fa540f0500c6460300540c200103010a81c0000310488808880c00300a0b5811224034001500d10014002400c640c140010508510220340513800180808803e1a00b0754403071002e01411045081416 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 818718785 1250 818717535 818717563
    0x60212010f0602120d0f05040c05090117030403020d0314030109150608041109060f0d051615050a211b110105061c020f0d120e060f030406020d090c1502 67
    0x724000c100c02078000c958001e8403c3c4890381c50f40d07960b038480c0f9060040c0184c91412602285014100024025066150750984000325800259640e0314030301c1030030221a41103409c54940041108100610b0803402d001071462007030500c420840d4840c44c0841c00d5810076031110b00c0036038031410039840300c40340c01403040c0180c280b030f00780303035100703003003a0b216100d007800505c81c5540210a03140228078036503181010040c1c00380780200540340c1c0c02081d02c0c0c16629140d11035400c8100500030540841d03542c80307840c1d440c06202c81d02e5461608044e500003044842d4203001e01000f450444240d0321809518080c09003032022840d0802140b4010751100c8014a4011012541d040691401c03080c000c540e0f850024034450000198208041090346000098851456510007030780070031b42c0942d030410001d5440002000c1e007665192144002448403d0205a01c64805032165026003000090001040c5601038403261130300d900c1c001902030b442c0d622003000b0103a6402180040030341902c00310001794100010841500d04c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 818720035 1250 818718785 818718809
    0x3280303060509040f0b04060e0304081608010c050f0d0b04020a0e0306072c03030d0504030801080d05070c03080c032b060f03020a050402030601020f0607030501030c0510021002091c06021201 84
    0x13a840d0000354070300c0b1081c014030a01d000300c0840c09120068100401120a034016070340d640b07a0760564207586030740607c64180351010881c0c0000301c1150600c0b81e15900e164a85605160800e0840385880d150712000125403103941d02e259501d0152940d2002c2c1000b461161100300241c0d041c2e50415280040040445c0100b240311346000d16680030108681c4c209001c401c1c11600080003220000e421401810b8032190420300d0b00081005059012069504962400050300c4043c5142201125944280348018014511010042001aa50707034028009540c00b282034a05101240312804000a01e059120f001c50041402d0888650003e01c1b5120080c980e46905850f02480c640c0480c00080c401e100b001d2256a0200029100e03034002e00c4420131000a03101603a21501c0d108501400901080c0020b65030114400c40c00702c1e05003880140203075000c0d0560001c000d0140e18001d9600a0760003064443d4018200300000d800e076141410321246403e00c210009a283d91407180c3d03050140c00143c1c0084d03450a1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 818721285 1250 818720035 818720041
    0xc2c090115021c05040305060f0a0b0105250c0b031003060509010e1009080f07050102040f0e090316080412051b041b030216150f1a030c01050903280303060509 70
    0x30300000c400361000c04403c8142044080440c00359401d02a5500190503030113003108101c248010303000710911031f07442c1c200100504003800300116540c1c0203082d030b010528089016502c100804e120065000e40b4403131504040036030b8403140c1e00e0361540c209030b0300c1e1491071075a03103c00c5c010002c81d8000c2d641d100d80a88001c00245c2000c810250f0360301a0492510380459070360050380d0600103414100c1e01801403401846550b98038524065000b581700d48240807603210321040100b04d48081d10f000e280a205120000e40c104141c2c0f0306011a1580340f550100d0f1510030400c0300003210150042c9612840380110040c1c00d44e12200c5c0c111040d03140d0380050342c5119601e855072120380b41c0700e0348000e46002c02c40c9103001610358000d68980c8e24405510b400290007404030700b040549d409007641000740039444940e824040c9103800d0960361300e11940030143c01d070300d90000c1e4020441d9510070710180c86103000080444014190728100240c40c1e050340f520150701c0690b1082c1c0b00301890f80500402c1c00030300c02070b81c5005040ca = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 818722535 1250 818721285 818721287
    0x110301051303031119111002090a0504180b1504110a021e070504090f020310060e06150706021917010b0409020f09090c040618030b040201030c2c090115 67
    0x1506001c0003014140d4441400d65800c0042095a040c0c050105044442888492005d44184c851035600c00c014881c20541c1d02c80304015000791000000d018040a52050030b150400c80903085441004101000209801c80404c407c1c180441c001e81035225040b0440000205100039120b0f000790004030302004005103040c00f0350028a40c940b8410500f071981103440f120101c24109800d44e8003042e4000e04001d884824881e40d184030701c55581c030072011510080c1032a000b03101035900030702c65840c40c04554000a0042d0820785e20fa181f1109100300c0c3c440c07411115580310001c07a0048402d0b051492001342100342280e402c40c407101c415841c10300c0a41100d42c074040c1901c5191245c0d00030100380b2034012030f90314540300c00c0a06071030b00c204000300100703100c1c034010001040d56003292282c00009040c10b480741c00d1540c0c0030044641901c0d040040080555140c2d0015030280016a14940400845108403070540b40628000c0d00e0341d41c00c0c036202e5544c0202d06002c02c2812038042c0c2000c81d10120b40d11088400c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 818723785 1250 818722535 818722561
    0xb090106230613080f010c0305070c020d170d02030c03040605013f0501020d0b040f0204140f06070b04080a02010c050309061f1518080708210d110711030105 69
    0x203203000b00c2d0060740e500c1d0381150a8410f8a10343d44644a94072507816403240e6040306400030025001513030340420803030b69400d504561303038036007800c010350070001e1a501e68021501d80c02c840c03200303000c441442520780721003c6005001c0340d00032143e9265400000c803c2c0010040300e4080d142c0105201c01891201c4844040d04d0509407035600111440c4181403005489010310320710800384203981180085450701402c0c0d002d0009411071208003031007240703401f6440648500c544240c905440d92500001c16002010007489801700b032040405900c84001c3c000f8800148200040703e1149204600d290344640840c407010342501d48094030710040c02024020080d004a0000305158030002d079446541885076a4040348820b480750703030402c032000d221040540320340b80d40040903003410002c100f4440d0b1070260744407804da07207c5289008043d407a410558401c200c2d4894080b4071502408800f012034941070a03c1441c200b03c0355440d8823000d501c2c00200c0c0700c00a001d0381c46401080060180c0090100e0300e4609a52044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 818725035 1250 818723785 818723849
    0xd060b03041a0a0f05130c1a0d020c07170708010605060301120210120203070c020909010203151219060617070f0b130f060206090d050f07080903010b0a030b090106 72
    0x1010101c50000f00c1e40c09582c2c1104a0800440b401004542046120903032405041d403400e490903c02e0500c00515103c6104040b03a100c84c561116030f0800c0842080c030300c040c0d8020b01c504a064441c00402161040c1030000c40e0502400150091000c03034035101e002030079a140f961001e44110020b0004002c082258132540390041d40c1180c810001080039402581c601d0054058002c0f190710110400441e150045a00c1e0b10040c000c84a01c019640c418170401d090740301c200d4040754401c21000444541d4284040c858008603201003e54080340c003074981d1503001c200d1182081da4190b843e0041000b101203a195401035608045014007409401c0014a4910880c64410b43c0c88002e07002a07280d441e12242c88014002d00b101e0701c40070807010340d00d40b8020340c0e50301c0c1540c2d8400c8034003c03038018040303ca02032030480766120840001c40b403c0c401c03103440d0350f500c6410110341d01c1c0c1c240d503e80208048036030314091030f040510710800c400d101e1403c010807400d08407000381d00101c0c10248900b100740344104000a100b41 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 818726285 1250 818725035 818725073
    0x6070207180f021e04170a1203050907080109110913020a0618030203010e03030f13030c11040603230d0e0d02040f090203030a0e1e0906010c0305040503030f0d060b0304 74
    0x182d100414400c0c40300a03c0358071048003e000100c141550b010542d0f000910480306410910312101c0506105562030f007080d104028501c9040b03501d0111030350300136082a030b40025800d081d03800082d034402131182980c81400f400c44404c400c10380003905514261081c2a0002015401c00440c5903c07540840c90f00c121600071482402800110808140007010b1a100959400b07802841120303004c05d8425500d400c2031b42c50310740c0c414171000082c040080303400341d504240740c165480c20030810b1940c48603002e68040b4005150015212440440483d0840a9038880d1540c0e42500304101c3d41140c001d81e060500700d141a0301000000103a5143c40e540d40c410541c0165011030b030000f2400d8004072940024a10120003c0d0980004965284801c1d001451001040800c0c0c46800d500b0000c41c00810b0a5031881e000c05500c40d43c4030000c14100e5200c0c03d400741100e8440e0900c180780540f100002440c40e0080c0740b100c42011400611040503468a0140100400034803011034254103043d41c3c0c070402c00c031b502c10b4404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 818727535 1250 818726285 818726291
    0x9030607230403030c0620120705090a082508100e0c04050f0f010e010513090c241e0206010501050a02190b0603010b0d080a180314010c020607020718 66
    0x8501c402424690340c0c2490908200d4a0760b8596a00d000b9003c12103401042d110726143c8501c0100c01c26201d00500c00c400b038403656141c41c0070f89640c069051031070098004420030200340450a8152250301c200c40c05072011f2402000020880744c1da81c6441e0708403039520b400407000e040d8100412403000078102040c81030b01d40040ba01000ca10705072442c0402c109509030340b0a0030034080c840740800504481d802241d07622040380030750b0380f100d0100c00b03450b60a01c01c40b5045906000e00c1418200b2580c4283e50640c421064400745607540c001c059002044011901c00300b264a4141402c0d05402034100480c002d44a5a08400401c010001a40358201482900e05104c000141403034114401d1102c00440b0f03816881e030101c80011400e100a1011040302d10074001d62a000e03a8032441d2410442c41c0c01c0c500e41c00100140303000c4500703000702d030040c0803512070408080e14410044002044d201d10055200620000020030207211900241352850140c92802950001c440a004c101d00e010002c4507850010340b03002c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 818728785 1250 818727535 818727557
    0x1c150c0203090d080f0406090f09020408060f190f0614010309050c100207030602120103110d02101b0b0906070f11030a0804170d0c0e0f18040f0b0702060105041109030607 75
    0x454172a0852031040d142000401240c03a42d0050a036400b40c804002d90303007240d103455800030b400324801c90160800943c041000160f2080d49031404550105141030303000c50701c602008490f0282c6442c107020340e607600e8a40d002800307030000000740e502030002c003440c0500c0024440c3d129261100d0090000502842c0341c03a038180003c500801c409801140e01c20320031507540110000401c8045400e0104075480079030381c120742c2c1c00d034030700340c00300b0000e81d5002800c000000c82058815118400c03d501203c901c2e2040441180c0410801044648541c412070058803ca10703000200900d000c821320b062200b4000740d0304418444c00c00c00401c1d01c05400c240d0030040e9691302c0e103080000e40b00c0742a80503c080440300156404c03000c00e0a4000c181d40e07880544950052a0010301081380e070307407840041c56400c4000a51040b4102e13007814032107078000d0700501212414919a8440000850f07007110384001680c0204010800c03410b2510030604642e05c0500601c1c144040000003e465a0000d0722110802030b280c102 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 818730035 1250 818728785 818728793
    0x30209063703090210030227011e0203180a0803030103061e09051c030c0f0e060904141f1a0c0111030a14090303010302030a0210030b1c150c0203090d 66
    0x800840d61240385002025046410009000c1e1103900307000c03400380010030703405c00707502e0f0080c000e03503001001aa503016003130b81d50000c080701e4101c80c008072281040007500c907506003074000c0340d2202d05546181e0301a42c3d8074051403a0840d040910310030190b00590f4501c904104055001c019241903d6100e0302c04100c0a0700e101c40c4003451110400505a070500d024044003c0141c0091300e4240c0c04000410801c0310359215100f0703011203000b2500712001ca1410303001c003054070740b040c480c1c0001d51400a298a06003004440410115000c007001d4a00d40c1100740140142003888111414680403800700c072603202401c1440030a880340311359000010300800441d485010b0202900106201d00310000100e44a24164007444c0c040c021002d1404940340e200c001103410100302000700c9060781d8000d4010b0100d0181a400d001000028401c60b10401d80e8503000d0f0351203584c0d200051030a0807030014070388582c03e1040c102034052035440e41c8000a224a03081210311002d80200a6401004048400511556050070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 818731285 1250 818730035 818730097
    0xe03120a090b0325080906060907090512030c010c03061703070203100b120f102313050f0f1b0607020f0f060904180b0c0301060801090c09051903050d03020906 70
    0x1030142c083e600d84002a100300743d101d041750344507224040403501c01e03403950410b100c040a4144d03201400140301c140c0600040c101102d080440000d00011a89031a030010601821079064004450010707440d11810000707400003112400f410380c0303640041c51a100c910b9000a81d910304c3d20009600d03041d00c07007108000558030000f002c11400c200f241503e44000c3c5060105440e604140030f0082d20700d01d81381c255a14070b0600d1689410210550701d03140480c3d04c8880c0c400c03450842c0e2000480d8180714200316468040424030013426855851001060045c0141d42c0302c00c41e82420200f8140200d00500c10b5901503642c3d4599a6a000030503241c518011a80130301054140c0b041a2555400c142081360043e210007403408202c4005020700340401c5a615880f82d42c0c2005d00c028804c2c0c00c000b661307040050100b410654080342e2510094100306480300e079110702040740c0701c003070442c03000d10030308000c50800901c80144081c211800715071908500e0454000d0005045014034541d01c000c0c000307441415030010711146 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 818732535 1250 818731285 818731321
    0x80a11030303100e18010c0206041412040b180a0e0106030c030b0904030e0a0b0f030a060f0b1b01090c060201020a020d03020a05070f02040603020d080409230a0c1e0e03120a090b03 79
    0x1780c000e10040700c803100040d641d4642a00c044564140328640101001c1c0013240c007000494211091514281c40d00d6540c40e041e811000203000e55035468800031140d60b54003507400008084d594100c19a561500c00b000d403c81c0e03801c3c3c50340c00901d8141a40070b00b207543c841440c194050382c5030801403c814405400324401031800e8000a020f10310010b488148040d07008065442031140c041c06009868580006010081c240d1064028440d400c2c0b043c09441100d0b88200340500d00b062000040e40c8003151941440c0000c640e01c100e0144c2d41c000b4540c6615035051001c06006241d03418194540300d00ca0000602c84c0c030840a001d003480d009142004115906d940000d03004580060108071118000c0c04d064805600510800181503d0300c5e1140e6040c1f84d5641c2d149156112400741c082c026902c07840800c002d4101a00c0900800020040740d0a560b120517015496240055071a464053349410600d40b400c8039050183c02114130500103401c031a540319490304251080300601036125100c11030f201720801d04603 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 818733785 1250 818732535 818732581
    0x2070801061403100605010f0c080d020316110a0507090f1404111206042d0f03111b031b010c0501020f120a141519080a11030303100e 59
    0xc500000340e40d0700c400c1440311002d1030480c00d980d00d440c24901c414003200c0c550f228035400300340312101c41c002103401190292100390085145911304201c0c9074a07401203074401c0b2080d412100891900c1d0a080368006a030000d140e40f848018a40150385455542e034070002031203003031582c540724840303002000b845400c40740b410142e20190000900b01850404e1342540000c18441c0aa0100e07078a802c101c850015402d4022030300722a01f04101003d400418001c0d400000e040400071844001e0f80380064142888142745502030b5990107015441d07260118241a14225100c80754800f00f036141e00565004100411603c000f182d510312824030b20001a10300401440001d070a44d407022a40c421141181401008001601a070080c0d0590fa2042000103c40022500b001c0e041550343c0007a040090400b03142c04040002001c03071040916030a090020180305070050707038080d040042c4490030007074440008540030004402071411842d103901160201d0307000f4400e142c0303d24005800700d02d01c0c41078000000900300344 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 818735035 1250 818733785 818733791
    0xe1f0203190b010216031208070503100b070c0503100515030c13020a03140a021305010305250e0409050307020307060206132a03050c0f10091a2512020312010302060a02070801 77
    0x921f0500d0170211200a200e070010480c0c03100080e420038440c10440744503c014018015090b414035031071070501d80001c2c45c01c942846100c0e6011810781d40030821800c080c28902c2001c034051400c54140000031002c05201c03402079211a0040c1340c039544009141c40c60030f20320040103841d403201c0381085001e88450341160031240c0740d0209002e20303010290001e050084240461111259865004400315042180c40d5004c149813020894001044034003105002c10380ba28013180d601d2500c00010b0211241d105080311305a00000350101181801e100e0b074001043c1d2800a04841e240141500c0b6900407448002000c0c401141c5001e0311070340c10380b00404111a6850303c2841c110b40c59144c4a90b440504249040c8901c1c01d0a0041c407641c82c0076244000500b100d40c1e02ea01a4620304058122400c80b285107201f442c410901000001c0391121082d01084005c0700c400300e14190f12070800e400c000803489200c1045401c1004101c1c1c9103042c0c1000c49044aa060715903aa44200c0b80104a04081c3e1f50382003410b00c0c0d42 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 818736285 1250 818735035 818735039
    0xc0111040305150601020a03120231230f0d140a0c081c051b01091502030f0703060b0414060712090f081b0d080c010e1f0203190b010216 60
    0x10001043c1c0156020001400140d0310340b00010790392811a041300074001049441210680e032a00e0700a00000d500c1c0c0b40908407680a0b6280800c0e86811080380c102e0141480e01007041500a24a14040d5401f282c188580141400c100410440d8005c561480c0c0540f200e914401e080180c0c641e0408500070307680080c0d030a0781c0c40a03d0403260000b540c1c415000b40707102e00b0110414a8810341e03410490890191180c4c0e25101c0008100c00030181c2031a2000010f560b030300e0411000c81c25008030150240101c00c2d0069991411503203454116a001c0c00e408205031800006102d002e80420444040d540110340203260040e1100c0014014071840d0402401d80311001c03040301e80c0f240c00c441e1240a83d030503203982d0b01d0181e032940c00945c2c1d20103010841030f00503044620240082d0819810040203035000b1407005240c0855100900d003514260201c00744140c1c0070840e451508000e001c090911030010201c150310b9418407168100700342c0080c82006001d2030ba1980f200b044c603030003001202c90081e90640415981c0e6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 818737535 1250 818736285 818736293
    0x90510140d1709040615020615030f0a05010c03200a14041d0f010603090803181c110d0c1a07030f060927031409030304030606090e100e030406050c01110403 69
    0x280020140310301445c141040440c1c8412680c0c44060172840d203038001e054035560f030300703c04541100300695660580030340028a05182400d0001107100b40c0260700100d406001004010100c5010460052198800300301a54600c01c038003017100d189025034a00462950500c1c03203100c0162080c1e42c0070009a800c030412080782d001500c010309100e00c20b43e50380500583e03a550f8051341581c10f940401040c0700c804000181e8001e40c00035564410711201811120080701080c84101030300f004c1c0c010030f4081900304442e0300754405c007004196841c2049290440580035241c1c2c03003e02046007102040025103045002032000c0c1e01c2039102e40c909251703142d82400042d940301c403144001c0040c4160300041c2459980340c1001c901403e5602101c0319030550342c460700300c0341446440086810085045600d07000402000010800301c0c01450040c001c40713900000c0d616210341d811403a103512020410319182c00d004142c1c0d80d22601000744c800711101401d0182d52440c030030101030700520078a541004103600100d0040140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 818738785 1250 818737535 818737537
    0x5040f0201030e07050616060f0510080d0e012a050d09180b03030702011d060d1a040c050f0c280308150904030302070219030b060307090510140d17 65
    0x1460007070300c04000c0651003643d89a01d0b104103004854210300304100440300c05640ca440c50006500503c0e002451000800700041039840c1966144081010710009101202052202d1042a035050403c01490040240041c18061494580aa11070b102140540d4051103000442140b10ba00c541035465820b40e41c1406480b222003401107604500385941080c20040c810300c00d40520040007401035007400d007140d004550b074030326165164600d0000c40c6034030400e40d282c2401a201d1681c120700082104102060000f254840c040c405610907410481030001d0b480d0060101c405180b98031401a549805c0b00d092285403107a002e08500300909604524500c003180c54260840c0782c1e100e542d4075603140d100c0b4140510102c00c0101c0c0b00c0d6200c08000e022400207030203507006000a6102414549922000414503000c221090b4000c1d0340b200981c00402070fa902c0e00307200c1103016000121040005042034207a00501c0d0425020703000345482c005c0c0c505402a41c8081210103030725485070204025694400c5e0752005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 818740035 1250 818738785 818738813
    0x3190602040f0b071106070c0b040308031e07080a1d150907060f080a1d0607020604030e0a06170c31050108071b0206040b0a05030f0f010b07240504 65
    0xb80710070480415511a28812143c56a8000c000b11050a0810040007110360150740204d521100c0b10768000b642c0e640300f1001d4401580031307125407138036440c1102012881c03222101100d4800303044007080044140e084508960441c400c07801c00070f4041070f070703480d104031818060411144900c0f4080c00030700250f80001c1114403403140042a01d070500e40c2d07040c042e20b145400d030441c8404104800e00144010769181e200c8240c0c546101c0c442c0c2440d4a2425a103420814151a00001030300407104010505070090b000e1040f101d03054400916042c41c0c004000c107020010303041e0200000d15031010900c201100c4090b64a120707009002c8291302e0055a00d07240384251551011100220101000034445d0b0184509500caa0800d0700e038412288842d00648103078131614641280c2c0160180000308003140140301602d40740403e070b2100c80d40c038103040c1d4901002d034900030020140742aa4030014000c842c020000c0c1c030259907024074020384606000c0000103840c41005d06080509140c80c0801092010003185010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 818741285 1250 818740035 818740049
    0x2061b0106032d060213030218090c0a0803040302091f0806010e090a08160218070e13091112010207050604240c020309011b30050405030c010e0319060204 68
    0x401807180800750800f4545015090f00a0403425000b02150710341c1c0040c21700e200b0003c0c0301200c10703841c1e42c0062075034007a22000d0758040515004109001c503040220000310750046039414401031802074404e581c1d100302e01001f802901e05202041c0452030319040500c49007400d074000035241d030311a48803655a1009201d007500d03242018000c1041c011011075039004c406e4016520610305400361400344000078142104a8002c40c0011001c03c004040000d000d00481142d904c40282110308801c02c1035124441403002d4802c0c0c43c001c403007000184040e11403100d02400340c03003107007410504480c110300901a507807000d8614059001000708215150b11710000c14000d40c02c901aa280d021100d43e01100d46140281016900c00c0000504e02d43c009c010240d2000050f41401c50b101c0c00c20303915400702080301e0450058881c01d81e88100d1540a000724280c0b001d460300c0c90b0490800740780c0030000340d4a11451040606203c1c51441c074544584081c8030740f90f400800c4010611100e1024035084e40254020b2007415 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 818742535 1250 818741285 818741303
    0x206070c0308070c11090f01050a0f050a03030e060c0115030201030507030e1b0a1d060418032c0301140402100309030c0b0a320c07031b02061b010603 66
    0x421050003403010606103605580e0760750043e0344600007a40c030740085000c20388840048800c090003a0740c410040c20301c180001c803881e4103594500700a10103141c550350014203150050345400d1203d0345901c5120b200b2a501031801c0d041d030809480110b6028072650700705200da03500304505d480034207810b1282401283d100b81d13010041a82c50410071070440f201c960390301e9842d030080f000562044003400780088252a00400540390f072a43c0b004c80c4a207000d030004440000c1c0c5029410840c152801e4441c0c0442250f054821800042c1c8a54000746200014105000103807c01204113401554100e583e0f200300078040d008000d0030501403d044104a01218220b02c541b4540800001c218420300a50480aa054998940c40b40144c1d840c00078a080041c80c00c15030680e2601055200b000c8224500280b10b071080c0a0b800320550042d815480e0140200035800340601000f00c40d0000c0d40c0018140104100d000304400038074481d00c0010164130600a00a41c401c01d40018444000c006512020840e40315582c0c007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 818743785 1250 818742535 818742541
    0xf041e1503050f0a0504020f1e13020705030f0c01060308030702060f0c09130b0418030f09060314130c03050601060509190803071202070e0a060e0604052a041a0a0206 73
    0x1103041c1c1d1400c03215200d202c01104007003000000c1d0743e000031b13410034402800e2003001c003c0440070459441034246041e40002c2d0343d602515040c140b408003500b01005d144004d510305040c58035090360302d11410407070f030001c03900000c1c41035923014083d0700c60b0b0041c5038085072040d81ca05000c080256a003d050303801505803000040800e01c4103124804641d0b45450240030128095940190300c2e00030302003010f40d0303a001a00d40030f0b40c4080d003841801d0340a041f4400d4540c11f03040702c60000300a104500c2d503041003040c0b610303260910504805004c0b50030750080d1512200d000c406110f18240010038800d0b0b00040862140c50000300e031407a0858040c0039070035000d980303a0a840c0c0c4d19901ca05400c043c3c6129000e22504200303c0080450340181005604006a00480e04456521170303032404411412540d40c540140e6503c2c0501c254006a01550f0300041d044a081c0038a00b080030041e25400780d06015100314401030302015254140da28203843c02080c04000c0300310004011006485c0680c0550b100500502500c000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 818745035 1250 818743785 818743787
    0xc03041401022b030b010c1a090f0105011d250f180308040317070f11090702060405070902030a06270e1b0609061606090c05030d020a080f041e15 64
    0x2d001011000b01000d91103440032070400d5004100340182141000340e050ba5100214005002500050400d10060016454200b10b0f0600342070402c12100f62b207904140c01040101e0710300342a442007040503070301d214050303d8606a403e81001805004107059152500d412030b0303e9001010b904881e8480c2d280d013242440c040b500300d001c408850000901107041400140080b030500302006d0000305c2015405032410805441c0c986240442d080110707030b861102860a0918141407504036000400c5000505150405c0c1e5034868645036035003e502e0302150b0100004001038025000031009040c0f1546810640c00884500c0100b030040d001807005003414503801c4050884006645900010340342d40c0182240341c141c0401c186d41e440040155404041803200d4003040e154049213010301441050005100b1215180010110702d55921107072082d04100d108150043d0081001c054540d440541c940d544c6120b500b45040900031a00070001114484000c120341e100755003010401c1e0352071010b140c295910a904 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 818746285 1250 818745035 818745073
    0xd0f031e2427060e010b0d1a0f010809102a05042108121e01051507032601060f1205070e0915041514032404080c0304140102 55
    0x308181c1000c03a0405958941d0060b0b003800c5500902c20b07800030036000d60325038105051303000a0b0800d1003268000240700b0242c1400340b00b280c0e40c600400308044d070a85814000985490005058141070040c0c0a000488460090080f03001e40500710342c00b0850f15040800c01502c0b00060048000c4104034002001075030f42c0910705903411500c455010707030070b101d007200b4802c41d024036031501c1112005024004c081924070710704070507440381c0000d48020b004160204a2030340c3c0c0c0e88041e4031160213810394060b20178990712a001152020b90b09400c1000c640c040b004040841d500d81060f0480110400381c0010511650100010114180d9a038030300d054482007100340402c540b070a82d03c50703000c01c510284034801800e0100641d64003e0488107115440c3c280d5030003080a0300c000702d01c4200d04040c40c440900504d140001040440302c010340040070a2255001401e0064a5461603c2c800100500000e000c21a0500441382c4418503c401e8170744850380c07090110031021600c2c140601500686c004d40310001e801d04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 818747535 1250 818746285 818746289
    0x5010c020c010e04200f0c06181905030306040b1c080909010f0501210e06010915090216170408030a030506040b0f10050a031d030c0118050d0f031e24 66
    0xc602c450b09038005c500c180f01c0c0c2c0104005589001c007030000d15007a84080c4092841104245565403001c1d50f004c0351142000150951031548564220159000c9140003090b00c0d4000c10580d00007503e905100c1c00205080c107240240c3d40d0500e01a0010409c004104010740036078002500e511201d40d0301c0712403010f2014254051140098000310b100203102c8c2e01c030103400c11401c03211500011801182c0001034200402600606107554489070106807180081c180c02008255540045007000350000c00c2c2840b60042110184c814545500c003034845081c034034211002841d03820300f01c0366114200c0b01e01401600d030445807244601d140641000084c1400d503610403100c40002c00401960780c110006455903001050002c003010340e140b09030b41395000010400f030403021450004546a040b540b000c2d07403c2d940126410742448220700c014000207440003802c9000001a820311030b04404250204800501d04039401c02108115400d444101d800980e01c003141c50840d45201d480e400305500484940000d0764 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 818748785 1250 818747535 818747561
    0x1308032410050d09110423010b040e0c0f130608040203070906050d060507020c10120507110312130c090c0806091504050603030d0c021015270905010c020c010e04 71
    0x10007103c4104a281e43c401c00850f445800c02c2d0b03c0b1214507038013140c1200d189400140c440d00359a150b000300c0d4440080114010300703020b620b9602d0076050401ea0a650a400342811404031004184911051855410b46100342d50b64020f15110b1079503041c00408205042d070f02030380680180300c0d010800341c80d13901a002c25606c0140c1400342642040e520031004000091116045005080f51685503503a06600003800d01d8888c3d13250200100c529030407204840c80030308030f507051052005461b8454680401a80c50103201c18030b0316a6183e440f00807041030005900d50040040102135001302d0f00c91201e03880411405020394403081180d41e00010721400440c00d031407003140000224a000c0e100d02e016048140d109030040c09036810f00c03900c0d5000b04143c903003102d2a000940c02940558110b0741e4244211692200c03010040c4083d140352030720740004460b0350300c11000428020840100c0d288800d4025544060f13110000300014120300720025200c00101827042c3c00140c0551490325a0b14242c01852000307440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 818750035 1250 818748785 818748787
    0x3306050d02060306060702030709180201080901060e0720190b06100905120a05120c0607090e04060e0a0c06030605150405090720071d090a1505130803241005 69
    0xd58010408160403d580488e4184a83d0a0118110700113008140f0040100781e0300108020311480013400940004241c202c0c20f0b80741803410004110380d030215a0700301c5050309190524a4400305038513074084500e10401207610503012000020407001100f0710096016580316501c5884100030401c0d80c1e5041d900200005944143c14015440c0081000e16080b42c1c0500f21900d040d80b0369200c6d410615002e0030400c2d004400315484010000c18098258050080d15160314500e0400030303048500280a00701030400c40d512050020040d60420650760000d0300102d030300786115035804005000e40564020f40c1e008183c007495840c440440e4034151000d4400c010100002d0307696a85040b0784406801c1166846d103249241c500380c0701d013018400a00900481d0005281e0209692001c01d803090700a0041091980402d5480300851070417030920940720440c0340049003d4694010301a441469654007070801070703000081c051102141d16144c50784040d030703408c459940099102040480b6103246290004140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 818751285 1250 818750035 818750041
    0x90901170a080f0d0603080903070e16081b030a09110d0201020a0f0c03080301080724020d0f11030a0206150102010903141e03010b0705151509043306050d020603 71
    0x1082c00c0a08280d00708502160300745109419040d09944090388103441c40000050001c6940c2020b01001c4041c05c20010848141d0429910b20301384811385180384010071444001180d03205521261942c80290445010343d01c904000300070100410b2100802c81e0320040781104d04110341850042403070350b82d4058007d044041490b8583d10030441124804540c00080c0210100009081601440c06071000314014103444d4104514440c1c00c0c000d001c40c08204280d04076580f04420350004180040c1003851800e082c0000d42107406a9841900c000201c25600001c58044c0641d41e0000d44a44503c2664001c0040403c0d0030005a00300e6040641c0540002c0100c0a0030b2030201c4400002d201d4a41015141065030104403083c000c0c58001780c01401c0b01e503400041003000c2c080c04101180c199204200c202c01c0b1400e00b10a036411181c034021815014021500000f42481811000c41c0c24901e910550440449042c06940012040d9440303802052881c0ca0000700d502e00740041801440f50740076103007a145031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 818752535 1250 818751285 818751293
    0x6030e030a051b01020703180b09150a020c040f0b010806060310170a050307120e090c03070e01021e0616090b04060302090d02100203040504110304051e0a0611090901170a 75
    0x540014603c0c0845200d0741040c3c12424000d00c01808040d01994452010401c00c81148080e00440e42c802c11901d4428800103003541d032201e80d00c41114207040800c91303455094410690926005804d19640f02c2d150130a04021a125600311021307207030b02681d408003181c1e600c004020640c0000d03074040f1100d4034811820b01540e11408080080035200c0f2080fa03200c508290354580c50359201035000c645401e00c4071003c034400e942010610240c0c120032940c0c04201e01d403c0a040c242808001c10482c10002c214511040d02d9009001c03036124a03035091030b4075101702070521800b6500ca206440807841600104402440c41b4840d03401081680d441d501040d2901c0d1402d071044001c0c1d0030075120b031640b060341000700c040181c1d82c1c40780d00ca6452189402a503103c510f00300810003150216900c040c0341040410802001500103d0610307030201c10f100300307607110401c1a1211882e0100c1c400300240351529160018000f1704001003d4501c0007401c03102c0b9200d580c0c0311a889404d0b000700100ca03410381d070701c03c450000000e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 818753785 1250 818752535 818752537
    0x403120305040c08030301080a032a030e0d020901030f111905010c0212060a050a0e0307020315070302070b1008120403051902240c010605011e050d0b10081006030e030a05 75
    0x1c0c011640104560348030b013110b03402c503403080c1d001020603400f5030700b800100f40d00403d81c0341519030650420340c804585100a4120f010006100408001d45c180800c481c03a600c005401c2285034010380202c2d4a0361710380c90302c00c003611807000050701c41d00c1b07802603030507241d01d4610030000f1064510303030324a4000c1e450000191540703401240c089030700000389034244c80502010082103100e89034000340440e6500b040c20b2810211130341002d604000d500b04205400c05030300c0c0054106500040c01c911644030b952036800c00c900034003c08800500410390603040c00341c0c00e0b00d80c00d210790a541441c0113941401080d000c4000c1c40b40b00d2803000070155045407000400791078517600c11011450001c0c05403481c1540c82c0340c401d0079824458000b44510721f004901012052424410b50000e040203003007505086040c141444116100360f2110000c00030b00150900742d085158001030f4501002610002d60200c6240e0040e1214200711051014a150b01e100066014400d0056003400403c01c0b015504d031520b0328204441d5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 818755035 1250 818753785 818753791
    0x5061305090a2a15090314030c0109051612020a0b1806040603090c09020703050306090c0d02040308040e09010b0a060e0409020a141f08010b070f05011d120403120305 73
    0x302e0144810b20008166518410b01c032940c03000c0d041c803811040320314803022540500e4102c044072554907842c0d1954241c119074580c2c16a80c1180a865010520403556031031031203a0351400e0660350030900914200701000803247c043c00401d090b001c0350951500702d404d00c0c0a010030006544004402c0c1c08120b40c0135a40000c20307800b10f400c80304000c07001200000c0342ca0744d40298003500001e90748561801c103010f9007e2624000c3c1207043c100350315041031074800800a0001400c04c5104140e503001113400000d08000301d0360b00f4442000155104c81e036078100742d0780507001442000220501200050f441c000306108012a5060051800c601182850402c0b50070601c4e440e501c541042c0c0c1e400186015a0700c9800300b030010070400946040c0e05104a007407003c0c8451150300078050258550f00003403603540014986040d04c1003005040e0f169020b42c101404003603020200a402d03540b802d103c20b42e017242d5054503003000719820f100720351401425a0346100184074a03c009010b43d100b00111481c1c0d14400e4001c160 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 818756285 1250 818755035 818755051
    0x10209150901020a0212100b010c0203060105040b0a030506041a0106260a140906090c060c06070806040908031f12022b080f07030f08010b0909041509111305061305 72
    0x88401110717408a011840090017410b8141c0c010044c03680c001680e07000b0180e00344002c0c64803103240c48143d40403135030710300041c0030b0350b40f01c1c94880e45c0701029911102255001181c00c0011281c0905040c00c0100d1300018040c1516885d441201c004101603000b103031801a08440302c1d044800d050a41c0101140303101c00645112800c5884911180e01c0c84a90700c843d03401103000074003410703141c02c010f9030403440c0044024000e80115028400ca40d500200440c400b544500c843c1409421541c0d0303100003d0083c02204001841c010020050040f07034501003038208100c2440484c161a600d4480e01d1410541d15034110003036010f955159214251440d40010707401c0140042c2149007400382e540da4200c01c0b90402e980801c001200800c2c4c982c02d150317101c00d002c0c4000640782007180683d4101103500c0220b02c1182c1040740103a132507001140420204228a80d660701d0b00d510100171161441c07504101c002e02c1c941d500c511440100d04107101101480c0b040d18002d0310000c10a09a0a454502000c040c20000344406 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 818757535 1250 818756285 818756293
    0x200301030f061a130e071a030f0a110c060f0106110c06070609050a12080f1003020f030c03010e03120a05010b030612030906030a02070b070c0b0c0d0603050304062001020915090102 79
    0x183c951106401c01c4035080c05070b000811180144800e061400030342c0d41c06828000c1c10007400300354030798000381101e07000b5407407100d20004d5540b2036800c10058180c119039005010800101c00c40f1b03541002c1586070182031908500070b003e0341c0c1d800b4104ca141d40b4011702080290003440c07142682e443c000005020b801e04c04d17071000c2030702e0700c807921264288a80d43c0700a55082c0210740c0d407010780b5548011034a070f21083c940c0d441d0902b420700001018142c1e255000081c066901c014821166540401032960003900040c0244a280032802505459800010005450243c00004034005030303079a00845040c0c5002070702c0e480c11542c400080007860240c007038108810740010482c0042c141c56800055104400b40c032700259403141c0f030307240802c401c402c01070a400400c44840312000006d00000541b83e005810b981c03a003610307004201810f6004000030790004106200000e00016205c2d0000311803150001c060010606621314441000e082c5d00c101401c00d9444182078a103500c40d080410080c0071421810700c110307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 818758785 1250 818757535 818757581
    0x9040503181201050a02030106120603050607030b0418140f0a0b1f090608030406120b030a150e0708010b04060f06050910050909091c030c170601020a15200301030f06 73
    0x7960841390240c039002c0b9582d030008018820380d50005440a40007078040c0040029501c0c54940c10f032901c1024283c3c004058803400c40001d503a0301d5030031580c0001c0c2103903505d00b042c0c00c030341c9441d1000303929114101c2150f000c0e240c085561803101041840d2403d40084032155195100b210342a4520301d0402042454202044081103004051080070007070007160004650f0741e4205100039001440021050030440e040c40c3c1e1200d0a510040341039410142d000e0390280561a50031040c170003034043d05000e40440d1044142c0010600030540040480801c1910104000b540350144018000d90a006003c007060013042402390f01d0038664900340d1000700510b4458207004901c00081c08000702035405900f2944603c5400c0c0740401c208032809201c1e00a03003400c018032682c02c80c0c040c006403011012800c50b0580b001c0091001c2e4002d01c10501e0055000d03a1040c000f02c013000e107150040a040c10304110640c0c060440c0d81c0b0300b0480720100da060301d401400c44640c00c4401c0d40d038400a0500404e150131f00303221000503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 818760035 1250 818758785 818758819
    0x110909130302031c064403091009050f030606090c03060310110a0314010807091d06101d01031e030e03070914060307050a060503100f0b030601020c0904050318 70
    0x10750492007103800408038070380d0302d04510b002503200c80024515940030045900360382d0074403544e04241d42e0fa113001c0101e501846c158122504600406110715000480020100c0107203a00403c3d500c149d41084480400340e04044040c19983c59040360a01d4100303020345d0100b120b101d0040c020b5580040000c00312150b40c0381c9c02000905131128495104140361010450700030f4141c05028620440c880881302a455600d85034000b9903c00c41e81c0b05401070b41d65144400b1394566250403100c0942080042200c006d030404401c49041d8042910070840325480341040001c1d0112a000034a040b40d03003044680d41d81b041100c804038502d001541c0c04a05000942c201e0307003a1038505001d154010b11002c04002800d0f0000003214021110040c0143d100790064001800256140c10105098404919040307881e0f0307440d004140b00d0410240c0152503208004400000d16003205002184140c1e82a400e0740c240840d80170074800810380c161030041a540080c040f420100d510341d001601d20940c0141401c054490150b4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 818761285 1250 818760035 818760067
    0x3032208041818030801181b1107060903080d020c010e01110910020f1015090908040611030a080412050d0f050a180302030703030f060302130b0411090913030203 71
    0x480b02c1107001a10b11055400720311442000000e48503181030140740401640c00400420050040150f1410641c00c0c101068102d43e202d005c00040c106200481ca07000c0c860060821070707407004000f00034450945d0109001d481030740000708481e4415140c50400ea16052090043d4002005440c0559650301c0b11640710301003401780010620100080564a040e04410700c40480000d6004c1c0040d90310111170000c80c00701c0086c1c0c8400507280300d0000141000740d201651422000d50340045011030420303525a080c00282c8000703100320f444039107611030422845039540381c41e03001e083e0020001c20098000503000c10f42e05070034100c800c1c2d0031382780651a0500d00b030401d0342110403417529110003955480070800744206034411400d040301030307500c61825400e030360307400a41d070344240ca20040425448079200010600280c000401640e8008c05015409905c1c007080001042042500d603c030311b0400b000c0381101c0041d00e00315400f030b5202606804e090303582c00c40f14068611030102c04400310301c020041854031100280b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 818762535 1250 818761285 818761289
    0x1c15020d180c0e0610050301120305070b010609091a0d022b0b040b06040e100e012309070510090603091505010b0304050c04020f040302040b0a09060b040806090307050303220804 78
    0x4295030707050148001d4280343c004c02c0c140c003541d007004041800b10740080c252070444503410108000501e1a29003140d2501400304000c0031500703c10000300b4a01d40086605081c1c40c5100c3d001c200d050040418050400851000190001c13501c940c208007500744460504070507081000c0110804050701500c5c0040c0c85010070540b842d4a81c5001d020800002100b41a04444103c5042c80900010703203003140c5a44061a900400b107560302c0c801d0740000c50030f4004100b2071503808100c10700380541781303040d15202d03100301d468040310f010325600401c0e07a02e0804c0c04e402c800380d220790300d2461382400c0480540083c2403000c026180d0720b13100188034658407014016103010300040c04010341c80c0d042515056140c208005031840c0f0403401032100d40303440c85001c001c3c0e804980d01158042030041c0c0c24004120031540581180e1482c90400c0c402040040d480c00c010070888030a01e088526542c1da0300e012a840380214400100f1740c2d0070800c041410340b1040d40e059261800ea001841c0d10001c030540d01c3c400664815 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 818763785 1250 818762535 818762543
    0x24020f0d09080c0a0b0406050715090311060609010609090e030c071d0a02160807060207060f0203011505130311012106030b010e060901090c020309031603021c15020d18 74
    0x70090500000da418000100240400e03190408000d0405070004410700a40c020041001001f249403001d101c0f400906007000708126604200702d503001d013001032803c1d880000042d040c0c458180400c9441c00c1c01c1346400c0c100ca4056071603541d154201012540540124109000c50344018408039241400c24045031008102041400200c01c540d1210001e41c15130042002101500c18041e01c1e170b50786944080080801e80c0023034000c3e600e031094948500240100c050140c000c515003802542c2c0c804540d401903042c5c0d9101d4280e0410941c501e48100c6181c80385034000c400034200a03104100140409459a0b0f844405052a10000c261840ca8403010006125513000b01c0b61280310420501000004d030780e000d0065103034250201d01c0c1040200d80c04a606109581c00540e07980303c180e1380b240c0f00f80183e0b804800002c082e074103100c070900407000300f242041c00244e00c01e46040d00c002e00300e4580881001e1a4a500041c0c0140d1444030500c100000e40000c1d0008445544400f45400541d410f58a1044003a1003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 818765035 1250 818763785 818763797
    0xe100e090d080906010e0610140a03050907080d1202090a05060703091806140108100504021c0509012c0c0406031a0c13090f0b062109030424020f0d 65
    0x4240103207025070141018180c4c1c0c001e9801440601c250b900302c60340c0301e50259003240c00020011012a002c819003810b80c060300314082038224a959154012a0251184604507000c5540f21103c2c2c68032030802072103400c0412440c48407201480d0254029002e0310900404100c1c3d01a0b9400128000c0d41c00002c1c12800901070f00700a210030541080280900c1c5605281003103841d041414542224144524450601000c034001600710200c002c0d041d400307810080c00c1952a51a038901092406c20318445003000a402d2000048031854144111400c019002454031100071500d1030060b40e603401c0c0d00914165005812290110351102e0064800551050b94075401410242c0151390058101806220034510708121112005211594a1096070620180080d600860f2340c4044000c18081c00c0082d04860007288040540d500f4141c400d000400b02c1c41210002e43e607100c0e61036101d110b140900300c00740000d1441100030b4155500c2c07c441c040d00d18012900280403e50500345031a08618440000440c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 818766285 1250 818765035 818765053
    0x32502120111030a240e04061d0a2a0e0702030d110c010b101202160c080a020910080307140a060f1b0306080303222901140306010e100e09 61
    0x20148142c22000648031808042144000809000170000d0320915140003d5980468140211980600d03555460302c0c2c1301e2840d052590030820f445413001d034000e440040c0c98001802c05200c0f24401203c51460800d01042482c1c10254020b02c50328000c0d2402c0c0443c070081c0280304241c007262081254140d4070111880d04d0b0152140000c0c01d441c1000c07169405850a203403101c001d540c01c80c452510440c2800030240e154180f00e086130100c06660702014202c80744005e03000640590204200790514002d540c401000e0f0380f8012141c002e20458032071072880703600400103540415072403201124400c20340001d6a00012490301c41c60180c501c91f020a5682540d038000d81200804264040c005840d59400e082c0035082c41c01c40c42c1354403804000c00700d840c00b03602c2c80000c814503c603440f60a00c140b6400003000310240d20190040c2020070071000e1200c05000f54000100f911403111010790f98002c00100103180390703030030715801120400b07002d400d003041e20303821690124400494000e02c610070f8000c88000c102e001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 818767535 1250 818766285 818766301
    0x90c1e180603020712231b0105061207150905120d0906180915030219182901050408030f090312030709030327090207030306050303250212011103 64
    0x20000e507000e2014180304004c80d4000801c2000c8922240c1c02078100705c280b15400d000784030652440b4400d07248100000049002510b102d04d00f40d040841c1c1010003c100c0ba545000c1400b000d402e240100411551203404100580768214451041296651070301d401c26555400201c0e1008105480c00242a000900360035540c0d41d07c44440300050409182c06c0003600815082e002550701140124104e070341d100d18401d14080380c400340c290001c41c0d000d0001441005422800c0c00030241e14003808038250311506404000460600a10f4005c00b103c403d00d145585541602c0d034a00400e5460700da044c04014030000800641c144043c4c61408090000d1595400ca038408060520341c5811003090b01c0201482071107000303980304a804043d281e0500b009000f5a54021103808000c49031142da0a040c0d104c044042401192900a041a28800e031014041944c840007056182d000741f4201415415082c903020402030f002480c0c1c4d50485001800c0c0f405201c41040c10103003994111501600b19150000c103114140e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 818768785 1250 818767535 818767577
    0x20708040f08150a064a10060926070305030a050c07170a120c0501090f020f0108190c090503010e0d08100b07020609010314040c061d0a090c1e 63
    0x107113440c0400445d4140010790759425a691a10540d400c802d648a201d143c0c5101c0d19801185413100c032034482004201003000b5800000c51308010100303108100040c0290086030000140c89489505000b1548907a1000c04405a2a61802c034103225200001002c110184018008421240e84682ea610b2859803054903100340d40c0c1c0f101e00d80c1c14142c00d48030380e20700010428110303036580803034030171091410800101e50304070b50424058174551901c0d011000704424443c84240462090fa0400c80d00000b03100191a00c210445e1140400e440411041407404601e03448400103c020707082034000640c6800c042821a44507111410055128458075501c058000d000d43e90310042411040c001d080c207024808040f4007401350006e000e0080400c900c1c1a0780e002c1e8100c0d840d40d000c0d40001c41e00515140c2040383e4030588034494140804e0556052442c0403449a001c0d100c400c101810001034213250580d02d40003010a40100f4003040340001c602d042c488032018080c006802c1641e640c0318481c42c940088140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 818770035 1250 818768785 818768791
    0x1602011811010c05100501090507140a0c1b081506031221130b0a09060506040209010905091b03240409020310050a020c0d0206090c04050910020708040f0815 69
    0xc81100e900e14400015400401800d558000380390410480e249403404a2610074411808852075050000104000b9101e07071119100c0e00040e076a001d031308040300154a01c01d2144008481c000b8118040420104e2030918441e405c45004041c0b01102660300e0840500300b00691000816203950417007408064581003050055286003d242d142c0751044456007941c26180c49000300112000a10002d84001d4100c2039021030181c000540c030380d052801d540342d42c0091400480449045284c5004280e13503084c244266000e0b4141a103501e41c07100c0c10042002800500148052180001961400d002070408006140219865000d001c03141d20303038400c2e89400c3c20424003158010b038a000c14580150345e0028205c0c540f4030542d50006901e13140c40c0300c241c029102d41c1c0380b40c6480b4400c030402ca80141da40011201d103d5031301602520603400e01c41041000390754081d2000031903548920011741c44c21a1582c010309540d4401c8410602d89587ea003800d9040034855806030302c06401c4401822a451217882d801c40d4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 818771285 1250 818770035 818770061
    0x5091909180b1005030303010311010507120f090f1202010c17280212190909020412150209100f020114330303030a18020901090b030d030203151215160201 68
    0x43c031418103011956038041480b020b8440240740c180c40906074041c4d411283d070036070414400f1082c1000c8000c0504402e645201c4240010b81d51400003030342400c0d108100c01540d0b42a15035001042c101c1d0011108072040395001c0c2da86103900080d0f4080300390904004c0241c6181c0704d004850042e07500f00b003039016941c02c2081009541003805021140c0041c803040300c18400d40383d1034201020100c81021200d08481c1d0700190940c602c0041c011403801e000c0804030755164814241d44040300c00e14a011001c0e8020359036582e401040c10301012400340d0240034030440296032031000103840c1004030200b030b40000064806d400340841420107440e001c481c80403865804164007400c0c810b08140c0c100400e94034840140351284203039560080c0c00380c0c1d4108000c580c40d50b9030010800c2d1080c2d6101c03881c40c03004184c5403907600d02c240b140000c60f0020600038002d5a01c0344403d40002d207400f2120006224888030000c1580c2100e020312584000004100050701d40a123416001e04a002c20003448084c0c2192031a5000030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 818772535 1250 818771285 818771311
    0x90a1205011d010908120702102406090f06050918040c15050c0c060307030906240807080307081b0616030c0905031903031b0c050709050705091909180b 67
    0x421200000c8410800200048120703590f12501c4c100c0c14980c61081261100e81030400603840cac41410480e07007007500004e0200602c481c1e40c8141c1079520b124180701d84a14162001002c00c9014041d101400c208000500030400c941c01c150380f00140c0120480e01180c0310320040b601030118044842c1c62905260042c148039107002d03084190207648664215405118082c004009854644a5040b100070300764000c02c2480a001507842160b00010350a001050344040501c0000e00860002450720449081902071460174040d03858940040d800825426260b080e1400680ca04a000300030b218851902d03650010781920450f10000c054030841c141d250304010900390140322969011842c01034400382000c2c4424201c0f201c1c5015805421148000c1d040011100300100d4505d402008061380d00e48500145c620741c9403104c49140403550300791600e00c0061000e10203013100e420050b422044080455500103000b66403040c00b0010f40d203030083c4811007004c5d42d070905010131040030036107038100541444030307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 818773785 1250 818772535 818772551
    0x70c0b1321060c050913050601030e030705011b0c121b020d051b041e09050a02031203040b010b250c03051e2a1e18070f090303050a05090a1205011d01 66
    0xb4040c1c00030800412141f5555004210307968003d03445a02604114001e581c3c0b602c046041080c000c007245000b46550b103c8009450380032038815424042c03407070f41c050702c030200c2d002e030900c0c049507a14252030317940d481002e1669080f40540d0340c4401603201c4500c1207000744000361880700310750040c134111011240a00d0410154521040400e5907001070500f00ba900028038845605100c0c1c40e00b0f00e1154042e40502518060350040c0c01d03054000d511541c010222003501c5c0e60b13038403006040380c850103184050503031710300c480c441c0c0d0440103140c070303640250003240074203c040c1e101d8a4035030034014040440e40100d5082662071a0410040c4054500d4020040a1101002e2a4150203482082c80038001c0e01c1b4180020520f044501d1519059100b000060500c03600c081c1c5103a00150383c5001a81c0e070b6008501184080020944510811400d89900d90b0303c4604002d420070090b0707290b801548480e58450030141c40410069501001284418054400410749010a01c201e01c0c40702169900343c00d80341d06220136 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 818775035 1250 818773785 818773789
    0x7020d030b011209020f09040c031707021c0807050609010519020306030303070e0307150c0c0909020d170d0f02070303050919112107030507050105070c0b1321060c0509 74
    0x518108043c000c2020424074094800690310b8980d01c030b0301c030f03034001c802c00240b00901c00d40168101c01d0b02d206035002c0b0407001011602c2c0709540074506d80290710040c1181101040001c009a1000d0507104800140c01c010042d500c0e941007040c00c43c0e104110382c0d5a44200006200d072402440c0741c0d6030710160110319604140021075202c1c03100a0081c0300740100c0c070b020603465450400045000701400200d042d0250303480080203200d10300101041e1100d411418011440c00002c0c855441d8203035001301240310000c0c1d5541da00091491032448a403d00b14144005400e0030319900403841c640c401341c0b000680d00c03801c618029088640103041044c1aa200e8903041c00c0e481945000c1049150b00101103547c250110000902e0350141c01d40d183d190448411030505103100000342d20b0f825644a041510000e944640045440d4081e00700081c20f00010b02d44100007400450380100540a54500805441038507001d20410b50151940c0070300d14a540c0000c004244005407040c000b8924052030700c14640150000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 818776285 1250 818775035 818775047
    0x31611040f0b100903080919030c0617180d0f02071205060a0614090c0f07020d08130b03070c0b090a0b04030507030210051509130b1503011a06040e0c070c0e07020d030b01 75
    0xb00380740603244081142c22001180038001c0c8c011907000c0c1014220301e480d03440040101303802250304100f444203400403c5403034034103140200c4000a444003d1021100c461000c680c0706800c0303038020f02903000b481c8010407100c0000c560300009900490040900d4144282c044045a825500401622035101c40d41005a0390382c1844503000a18109540e4641d06440c1340d401441c411020700950040c40d2131903820070418400054041b103a241e2171207510840c5e40d64844211840304852480010b820301004100107001c4048403034001d0141d8048454481700c5a0752030075003800958080d400b003080400c0c284201581006100258496100140501c0c02c220b0322060840d00c4089010303114465460000340c80d0b8055990841205800c1101020542460006a190b007262500128040e500700b84034070800d43c0c4006084103441c04060460341c64a8645010701101c0c0b800600800300180b4100a140c011911702d01e506006021041a01c1c0124245030030040c0c03501554a40b014141810803070350720566030f0020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 818777535 1250 818776285 818776297
    0x80a0b130b0f03190206070c08010518011505060a0c080c01060605030f0907081c05091306080f0105060603060f0111010c0e0a05030607020604034a09010305031611040f0b10090308 79
    0x15801b02c0d211181803520005a49540d00100c8681d0310b080100004010103210140c0001507140080106c2d0301155482040340c0f8031802a141c08c0782e001c12005c20a40d02c600c80c0c04502c507008404c3c00b41001c884441c2d003421745800d81e1180e000110007009001d41d201403145180d4208040c0c0c401000c1c202c1c41c000403613880d440280202c00001182039884400c0e14002d80803203406000051000000305c00081d0f95030014000313030088040d51b11860304485601007051056501132000200060b05564900041000304450000018100325500e50030500c801000d000b02d42a000d185c1d2210b49600700b440c0e0a002c420540c640c880d42c884d42c400c0d801d00c219103401288282e00583c240c03820646070a8005000310034262200b050704070588680c2d003c0e04480c4451401d20141c4280031000c0d10512004104100081c4c1e02800701502c5a00308000007002c0214a024004c411441107400c00308107080c179030001d02151481118201901d0321014030b64101d191030650a0310301c0f006400d181d8491420740c0c582c20f100c0c0c050b02d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 818778785 1250 818777535 818777539
    0xb030303090d0c111c170f090409050c0901121a040213090318080307050717030d0f06030b130506011a0405010804050c0a082505060a080a0b130b0f031902 68
    0x2e41c420360512400c281c43d1020042e0103480074403901403a41360203410002021044d80c2101540c061b10160b52000300841d100d04200c0c002c4141003145510810005141484040f20706100d000300c05204d070707102c0c01803090081c00c0b9900480c031151040e0030540a0001400e0040b40c88051a004101c01070b543d80480390800202d281002030605414a0155101c0c407600740801c501d500d0005000032240c40020003060301c2e501c11019070ba001a43c8010301400b40e022032051038019001442800444000d03984859a049030f5442d012400726500c0c1c4030324185080c140d072080e48080002c030b4600244102040040d005200c002c040c143d980d100c0c98400342080c060b90107181d0422000030041811322004009c20003d040700105451406a0ba41180d25610401440007100c03880782e080240601c1202d03001c0503030032070750080c1c401c52810800001c00c490100005111103480382c3c2d1140b003184a0340316000ba070724000c03447d040002a854000c1c4100300d41c07a0f11000950f031080c0d000c4600c1200390080412002c0e400360341 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 818780035 1250 818778785 818778797
    0x1e010f0b030a15091a0a06024b0c090106120b0a09020307050403020a061404090b1c0311071a0909071b0b07081f0b0d020f1204060b030303090d 63
    0x6120414001e0114952003e1145003880710104103140c0d240e000300c003180c1d111281d200c0300c02803910a001c00520030703118120158004400300d210300e40071540d00782103204114a2604da41d02002030011101380b11002011040c4848007403031104004100302d504441c00089860054940c50514010044581c0c503030b000d40c5c281d4840c0c2480c951501d52520340d00180c03010030010b64403894400c1c0010030640143c402a80304401c1c6c20400203400f4012002c0d00c101c442203480c0145440d040801c2c240c064012505003a070020141850402400d5128510800381072181e41c542030303140c84401c62030b46800500d400c80d004401ca2096080ca4105c03115044961180b816a8a0764035517840d80416036800c1100c1501c01c001b02d00d1000310300c4c100141614450310402c11510359609648580400700542000c0d075645040103000e010f0b00344000c2e001600a0a40c00e0b604040c007501c2e1141d245040e420301c2c0c1160310340d101e20700c015000f40010802640590325480790154010340c01c52400200440d0358217103640d074810074415 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 818781285 1250 818780035 818780041
    0xb0d1203020f03040f020a05010804050a02010531060305011e140f060310091a181b07050601080c03030a050a0c1b08030c010f0c140c03071202061e010f0b03 69
    0x80039070140e035800b50681501944925040c240b01c0840c6040220481c440c00c0b6849011900d580602100c60007150400000d181585265005603550340c040702d0808165010440128045131103088040c6541d251109200783c0300e4038000000d81902c40680210001000185150007881c00c0720b12250100c60f07030500c40b8080317030342030a0120749550080801e158116100000b00034a440103200010103d801c10341040100c122070a000007048000301811a5010002034002140043d51050098001210036280355410304100c80b101383c40d5000b0345044a2a0b040003004200610090250001406084c0c0c00396103440d080050041451160300e04040c01e04c143c030440b800500c281000f101c5075000c0b100159044890711242d08941d2a0048080340c040c0f5801e0000301e0b600c09101c0d0181d0901c09500b80c42d03207a00750710009541030894101c1c601c03004480c4010302c058404030389189010501c040c9650060b0419046c40e8400c52040c0101c04032a610302c140b00c030010040301501c0f01c0e11000f182da0301860162070f0f403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 818782535 1250 818781285 818781287
    0x151606020f030106021c0c020105161a160206010b070b072001020d050406180803010b070212061e010b03040803062b050d1215050d02180c040306050a0b0d12 69
    0x1029402200c0402080032002150641e000a0f03950700807402451b80c02099504018203e0310744050300720082c0000c00c01e004d03a07004c4803c580c04a0440318031600110090320b01011115400541c11621501e0300c0e051190100011078060150901500d41c0d01d2441d440c051442c2ca907440d0480010704a4000c001044a01c0010244041011600b0b00000c0b170080d0b5460030b0441c0c0000180078180c0c0c0545049180c0f030401c0c1c0e01d0381128051044841e80c0001c126040d81e103041e075020b4068001080c2607030459042001041042c0341841890310a50031600c0101c1c1500a140702010429016041703902441c83c20800d0102007a00041078030f604c000200d41010302259160302c14804110201075262801c0481c0c812401007000100d4076140b046c00d2560743c0c043c0604030742003030b0302602c00c658011021444c112101340300c1400c2c1000b038240e095001412034081814900b130720518000b03003150b0000c6486000300e8140200400c81c004e56401003d04002030284844c203800140000c01180da004221b24020440b07c0141 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 818783785 1250 818782535 818782537
    0x31c021b0601120b040f0b190b040203060a03060b1804080304030e0d03021b01090b0a09050f0102011404020d0303060b07140c010305040b0f0405070b0409051608130803040c030b0103050d02010b15160602 89
    0x980c4007c050801d4203200a00380c000103050000c03002d1045c10b20a01c40c0031418548207580c450540106401e00742851038642c1d5004054030008140c0100c259000000c001030011092401103101c0c00059540b03203040c0c28000c0120502c2c0004912984889810002085d4001408841c07441c0d420f03500b10071400000c0050b60703218915403240c8d031411f40104921218681209000040b6201541c00c03542d00301210004a01725200281c00503540665000860301605005004050440c880d0500084060f2200c05112582e000408102c4001c2200245562112424841c210344130101782400e20541c20140d644c0c1031040d00041112911600d02800241032203400c00010000b0490703a0314090ba560303281d1300000b005c0c1c80200e4110b4030300160904410b03800c5111310a0756200d4580303554500c402c03030340d01d95441aa40e80040c2c01079910f555104d4021012a004003002d0303000310b00c04e0740100304003003091a0180c03c1d540007c82082c0f1820843d60905c07010403e40341200c034000005d002044031054203140041c02 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 818785035 1250 818783785 818783813
    0x10b0c07051203070b070207050d110303040f1530020a0c0204180b0105033f0a120b1905010e040e0609070314060c0901030e031c021b0601120b04 64
    0x80010080c800044070340000c40104060740c0900101c1704503a031211070503603681025105007504619540000c101203201c4078001c130703040e840050030380c0e103001d68414a800181030b40d80c021014425030446901c1e40c240c0c001c0410503511386451070500c1d010707034100c0e000380480c031a50290300700c20340d00000c3e000c2009114903c1210710740d50007041042152035548403180c5402007020115182000800081010f2400050b41d500380001c00040720580c1d105c1d12000d007180950760f81901041c2c1c155801741ca01400ca4000980403141107a03540000704c03029036002c8000c3d035070007484d2140252000640a05480c0341d200c04070003500c90a0a041ca0380302490030105004240e0481440c49901841c3c05100042e500480c40300210f0b4090b049680440c0890440300381c07116025510920351343c10400000845500a030008801c0c0002c0d20150307801c1c8441c4684024964079014a03501c2ca8030b90000702c1d80402c0d954250500d52988107200208011341c1810b104400200302400043c001207111000141005561841d0b608 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 818786285 1250 818785035 818785039
    0x20d02090f07020d0806092802040902190e0907051309090f0501050f010e06150705160312020a0c090f091217060108060d030c140a1b0803070b010b0c0705 68
    0x203062601050909100d4016180e1100501079074100e12469881140a10b016200041c010411601e510160002d0740c00c2c21502c60180002c4002c1e4480d03d0109403016000070b0030700e0b0700c0242c0e507107402d035904080c0c0c500025000070511000c0080f99000e82ca032004410380c030840301c0c2001c0da520640740c0c1e40000c25804a9004680c0319080155540810050600840490703104200921064a0741d1598107800c600034020f48a040c1c0904001600c00e02e050544007610803800c141292400d402500c840e407d04003048403500c1040460901001045044428a030010000d0710207018400030b55174400d0000009403040d601842d483e13a1000303003103003000e610103802540e2041c0c40281e83d4001034000750a1208407075014600b001745400082035075000e03200043c030412004000c000c041b407041d5003e4484480302e90041d120300841c80d4400c060800100000e46000d40240c400026080c00741e8146140d0411f07642212586030800d00070300000500c0f504010f4191040c503201152180f88481d2601c0c0303040b80c6648255 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 818787535 1250 818786285 818786299
    0x3011d0702010b10170c16120c0b090a02010806040e21042d05030115050120121c06050a060507030c080310050f040506010219030207051503010609060c030912020d02 73
    0x5483c0c40d000000b940c90032030300c480307422850307901c00e03006c03801d24000c548003480400034a084c4240001d60b040041411204581080c007004000c64646207601c01c0c0480c0d0f40001580711440300010740d030b00410150b50151044038180080f580c940081500c420313a42c86e9100c42078203285121031400c40c3c40c506a0f80640342c1c40024441104d0080c000700b8000400300c042070814880c1a0000c5598107044c02040031100a44e00d50800740d6183c40011201d111804a4104079003d1555032081954824002110380da280e1640523511b03144405101e2025074120341551400a2800200b080140c807070035010f004560880c00c0142d100c00490405507283c490728100101401c40000400050103807070b480600071745505803510804205a4000e200031a001502c0340360250707202140d03c0c0c3d03001c1c4510b00603c4140e48a441511841c42d900ca010a92140013003800903580074000c40144110b5521260581c003e22091410710007051050300c01401d0760085014901e103103000141d0306003d54540611500005c3d60141c80d02c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 818788785 1250 818787535 818787559
    0x309150d02210a0b0303030610030906060b0901170f0417120f24031203060a030b240d120309030519200d09050d2307081203011d0702010b 61
    0x620440000002200b58207549200841d00c2c003541449940da184030044d0003145103484510400081c010845480c038201500c40101800280031030280e00000c2001615407034840c25808009080705000350040c1004900c21020443c0550120350442e40181c0c116a001403a440480b0081e003103489200140b40d14170b101901070010040700320054a10442034000c0b12640303207511751007404126a90a4010760300d54000d0b19900d01c4181301500464021074020000d5400c2540c1e82c1d6140d1041004641180065418842055080c62418080e40c1040030031908481c0b03072140380c0c1d50b000c00c442070388175504100355503130200ca0201030044013201c2c80b064100c0903070000a440e81c00c0042104120101c1e03124800705041d2078040300070001a404009400315100c1d0b107015030603c03090103e0b4003100d41d82520142170891004003294280303d8003011003030310b100150811138200000c443c03170080e42500a202c0b105040004011504103d14840d000250b2202c80600c980c8619404070301520b58400d040790b1000c008006 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 818790035 1250 818788785 818788807
    0x182f0d050c030706090e0708090c030a0f0204050c040b070611091c020316260709150905090304510306050a05030703020d0f0b0a0c0219050309150d02 66
    0x280c558035104800f11070781c4684404003103030b00f459903101c1d051140c081000442c02150007401159800350010f42265440e0090f40c0000c0d01d040d208113002c0d1003075130b4552540010750915004882e40601c5001d121443c00d4501264500c407449015401762980d9901c80300800044100000c03942240300083c4911080040c031000070340f0228074070004a1207031041c1403000400c048410348584c12106586a83e0503090f20a0075aa5060140d02d01e40c01602d000340790010070058090701c98203400d00c510001051005082110440c00c50340007170a060340990080c07208004460000000c500c50103010301c100682105003001c8601100f801d0310b071132018014180a100c50507c0c007100340c070144c0c001554081c4607465403402880803080d914000d00340c06401000c824405400c1c0300445810702d9110f800d0000841c013698072144c0501d4011356103003e0b044e483d680c0070190981d04110710b0b011458101c600107018800f41c0ea5060b5644150350903180a400c000c00c2801c1d10481582c00e43c3c584555512056540f40e00c0044 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 818791285 1250 818790035 818790043
    0x1806030429010e09061b0a09080d03020307021002030f071407060603080d0b0a030b010306051b0f070303060b28030f090c0806011a030f06060d0c08060301182f0d05 72
    0x1d81c016180e80301c3c00041e1200d0380007030351501504589100b6a40700300806c11030625580038502c02c0c4103020000c54000b0304070b0404c029024048603a030358016100c3c100f10348020706150954103030418650040c4240100710300d41d040c07020713041001410030320750f609459080c0465600403444007802092800c02e002040c80a0200104401421041c0800030b80c1c028a0800c034105100d23003c06442c0c1c514040040c0000b540c0d41e48210f1708586007505003107000a814114445940c495103102c00c0c482c50108844040503054056840174003150790b8101e04050140070345010f00c00001030144210044446041010b5010364040c0ca10720b840820140074440c040e044c05550684a071080380e01c03500c40c500001134440903070800c1c42e0801940d14141342c51501d9409a080e440c00000d0038442c0e00000c2000b00fa4140c6c0c48610600380c0140554541e1001460814201401c40c1c9517890040c40505003a21050300040001550940c00c120f200d031342003403842d0303010442042e425442e042d243e049200310340c880e028800e00023 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 818792535 1250 818791285 818791289
    0x61f05120601091104081507031b0203040812030105131505032a0616060c030b0a031406060105030601020a03051309060b0304050709110702040c0215070f0212180603042901 76
    0xc00c044c007031070000800d0002c26101d2071007900c0c0180c219800d002182c030f0030168030076044480c51030082000031900c05410003048101c4000405030340000343c02c11010409101d49422a040080580d045d985041c000c21442050900c90500c2259211a0f544012a015487e07a0240202070101c902103500010114207008801d803540d00c40c17042001181c2c90f58a0921300700c2d84008008080c1d049c000030391340c0d06d4801a02e040b24106d41819201e05007a21161a02c1080b60010750090101105845c2100c04150a1a002400c1d00d81081303010000c201890340c00081000400d40e1501d80380e580c038501c1c60200400d02d2b03126003009185601b4050000b0306c586c194400f950003140202c1c1503c190720303560380952040300c4115660300c01e080c00c180004005840c0990146900a03214019221039180d6101c141c0340900c0c2c00c80b01d80f80880c18080c401e41200e903042000075180c0400d40c01c064500000c3c801d1642c024042d800b4018442c00740000080c00704410380040b402144103040d942c510204c0c803140304d010003607024 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 818793785 1250 818792535 818792549
    0xe04031e021f050c04030b090a020301020a030525051b0f0106060c021309021318050a03020303160203040302061e040b040b0904050705120a0e030906040905040b0f09061f05120601 79
    0x2c03103040c142c602c0c1c0030b218103400380030700000a6141c14070b0f50ba1860f6030701100500e0049180541884c91015880a00041050311180d41c0c000440c1e00d010030900b1901101e80138500117501500d0644130201da0001c04460681340c4000b4003843d0450b150003107520b4280e403000500d10950a244001401c2c1e80c00c20340940046108030f91601407030130001a110700725408214084e6009109031508200071401d40c1c054111004031142102c030720a10741d00d4141c60406107050482c016071000081100b90019060505036114491000e5440d051542d0001007031030098056002485000c08030200c01c5007441000c4400400080da41e01d41c42d2a0740741a4605542c001d030f14506d010b5800c0100041c44244103400b00c03040700c081a00e28422907115924010010000c580300803141c2d03c01001145002d65403480900001d000c08100421603240520300503001c018050b05070040c504000040c010318920200b01c076030340514100c03210501d4003010120040c9042440c0d01860300802c8101605026a601007250780c16030340c076 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 818795035 1250 818793785 818793823
    0xb060907050c0d0e0411070309090e070e04081602030a050d0206010e01030f0f03020c1201020913181e08040602010209040e03090d0605060d0b1e070c0308010e04031e02 74
    0xe040e001d407258480c540182c0c405420049060000c0741c00b40c6424804900b01600c000340080001e41c00751b040354080c410035004079040503801c00151200d80500009510003d000c1c2103103d16080300500c840f240074200820b85200801c200020000301105100766580003006c5404000c0a800d0060b20303580032030101d50040c02500300108044030010300850489501c07a6400440c0301c516150b464820703c0d05a0110110f000782e6104c010a40d45103240c03100d038240c80200040e5105044d400b00300c3e0251400c0040018641414020049158001c80c20703184181c003d08024009038a6951304010840064070051a40c400407078089800c2d54154060311280009a904201071a101c520703040d6a4003500341600c0d809618003241c000051103540001e500114058800c005e080c481c1d9460440040080b580d400390460b4820180020300d00800905401c250a0304084280002c50b440042543e1014061800c400d40254045000c0500c10310003019200c05540000065044040000b03407120590203030399040c000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 818796285 1250 818795035 818795041
    0xf0f090703080a030c030b0306090f150f01030b0721020a0305060108090706140403020a091e02090603040f0524060114030c040501080c0c01111c05060307090519090b0609 75
    0x40005500d40603650825841d504203501c90300214050100007980350f0070192566004c10b8a5101044286e00911501015090703c084400a01e07141402038400049068614814000c25196000c0e08506403900f000c051220381c5d880c500c1c03e41d441280440b542c101404854110080e03081550302030840501165000c0c422500c440004650f140c03c00e80d00251140c1004e2010411240500340c56403070040e17091611402e0035903a800083ca403003025031100700c807991255550340ca15065a0380d0700c2100880c0180c02c40c14081c454002c0b403040d02000b4802400c600500034007909100c4104444000500e581c0b880b10309000769491030388442c801c140c55040c00b0500c000303410003481540744c0c16a4458000c02e074400d400d0600e0300004481d95480944402000c8904000f0180707003840070b008400b0341000c0755180941d40c1019240003c035084540700600e056a2500302400002c2c0e0b0301140380001c8a0450744041419140d109540c00802c0d00143c0403202c952910342c05400b004142612544142d000311002c001e556 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 818797535 1250 818796285 818796301
    0x804031a01080c010f0e0307080a051c0f1e12091209080d02060f1f0605121b03060d02040e030c0f0c030f06070f03020d112a0c060702030111030f0f 65
    0x1000c0c892802c0c003042ca940d49084010780708800305c00d0070b0203004044400d01c1d56a200327a64205198102d0035500e98100d010071010824141c0582d104410b054500441d8440345103030300603d0002c0703c4455a40510b01e4108620b24136105101c1c13103803d0300b45080104201850752a08039515040d200000010510b030080002d0300c15030116007080074942d582c02030300580d640c102c980d08c10100d00502d0b03144848d4010800c41001c402c0782c103145014000540b140741e41c0c0d4059884040a410004042c1000b40010182980c084050b401c1a80d401071800c0d22360300c2c4420030503c00039000d0030541450000a1002081b28001081c00043c1c0031000703c624000d0b21003500454041c162076040750440503a80364001c10101d60100d1148103030403070744e112a00d80141815001e50000003561a5202404038403100802c403d00e01c0d001840041710303511400d022200031803620b5484140c480d20b000090038403550700030882d8029500c00390002c6d015034500c00728550341d0340382114130014645000d07a900050000780e100010881 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 818798785 1250 818797535 818797543
    0x31b0e042f070503040801180b060307031502090102010b0613091832011416030614010f11060405031b0a050312040218090606031b0607030f0c0804031a0108 69
    0x4800080320041d14070812a04503038541c8005012242440100400100c0e00028824407890f429441a40488030b640d0341448118002c0240c503107840780e040000b0400c006a1007010356540354240b03c07005078031901240010b07801000ca0114143c1c01540002c0c0c50b11342c19018031190419203101c207000f0403a042d51001403003164100c1100050a4588049600400c90a11740b500c201d10401390310401c040c0900e40a01900351201c07001034900c81e042074004d2120258117641c04e110804001d1508001e120724143c2440508100c80e9040c50510901c0c01c0803a0915110b08030400030030520600319020b5051500c0d1031950f0380e0182d01d01c0400e00b94050302c00b406100c80810400d0801350032200860a00d446020b2030100f00074003510890340f11142c0c0301c1461404c0c034040005032042e90520041c014a140120505081c0400045058400001994587c0d00f595031031091720240c5806207072000747c012280c9402d0700c0d0f2982c0501c000e071030f0080c040380000c00c002524100c0c0024240d100e034026a181daa40341070513a0703 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 818800035 1250 818798785 818798831
    0xb2d03062d090c221107060c0206090607030b030705090f01150f09051009271503020306041b08060115030605060a27120515091c03020307031b0e04 65
    0x240d0b40080900d07800625080c0c440002484d150000a004000e2035a480d4040f2a14120b03100e54030640070031450288015441509410801c0b400900040d2134186107054494000030604028541d45060307044198a0420502015180240110710141403100100754460002d1151034101180705202c000090700c0352822411502e0151200b5400c4c908081c1040600c400701d2111704100074440e00e00084c886680c000e15004106892003081040d500c8000003025501c0b42000d12a03000091202000144c0380000d00f542e00c10703007017400d2511391400500960001001540071a41e5403087c80004600000b10032100d03014220b543d14200240b66544090201e1800f601e403e000c0441c0340d003180035a412a200c1e81c5108295030452102c0c10035601c49480f1220084102c1094601d80e000c05c1825400c00d08501205801c00070250003001d01ca6039015011500e40c08214a490400d074022001c201002d0290b044400001240741c1c03007070809a441d15004003007280d101e50180c4500d0a10080021028412010400d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 818801285 1250 818800035 818800051
    0x9110a0b07110d0c0e1e060607031b020907020718060f0603020a0e1020010501051f020c0d03082a090f0111060106031b030b2d03062d 59
    0x410072007151581c40482d490008940d800481d04001480000c00c081040b0020302842c50454803503003032090341c00807094016114285084000c1082c000340d65034071004c0e52001c9505280c240e01c4500c40300304c3c0300303600710002070000c1d00720713012070305100503150085442c0054512404c00c10000030814040c40303084e00d9035441480c0c08001d0000d000c0c007509220350001c05a04017036040c070340041c0103008003040c11000002c202c440020399038981c00c5404001130801210110040d0003d110a5040c080001c07400320300108205003030b0f05030648108010780240074040300d4100080c034045400da41d6041c050401c090884040800351500c0c1c07902e10384411011a40c51001441c80080c1d03003054200018010010540340d81181404071035441c07100c440008000990290406a80124034041076981d1054245009000441490704080b1946041d48419141030342107202c0401e0790502e5030040e8044441c5014000182d0b806005d90780030444800b00b2030144c55000b211500e01041d084010901102a030081603036205 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 818802535 1250 818801285 818801287
    0x507202707030b0303090a060905210c2205161b050a03050a030f06081605030a03050f1c0e01090201091e090203041b090e0c0103050c03191b020109110a0b 68
    0xd5040e486035204070030024002e07044078906040c42c0b0000e8541f0291340c2c42400082c1d1560014000c504200740013800036242c1403a035101045028a400341c4a0074502d031000d010ba40c240c0025604200e040802c1d0081c0f03083c061080105051034500b024422955121041c00b28001072015418031400d001d42a58264010015264000e80c2d5981119280d01241d243d03000c1546034605410215040c1c41500001d01c009401020400d0020000600800d41030780711a11a4118803000d0000c0381e00300c2c080710006001560402d0b5a0301214900c0c00c10f51f10000b1003500c0042c5000c2454500300c005600100c3d2031340c000d0701c5800c843d650714045141c410310386600142e03255880c0ca5040001d0103954000c0c542081c8920505020a18031078549040101c459024111030b6440d0b180c4c040c417104052229909460b000c1c641403180f864541210303131341480060101c0d500d040c501d642d0700100c0c100a0744800c1c120745040d007040305e80e405030050080c0a800c2ca0181070b18600c240541100e01803400da4450000c40d0130101c801 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 818803785 1250 818802535 818802541
    0xf0804020306060108270601051203040b0d0207050111071a0a0501050102030a0e04061d04032c0f0307051e1507020306190b0d060903020d11030409020a05072027 71
    0x443e900c02c40034200000b0820806c040e40341c441c10312804030b0440728844001303108941c909820004401c043c02d200d603045400401c024400311041070100d81c10003203d10750141c0d440c0220326041340105007a1000c0c1044440200e1900e0800440c0000070180003036904e04412645c941044520480f20280310f007a0169004120025802c0c3c00703040908064034000b44001905551980e41d81c07800c214404030842070003100000c1000300760304400845001000420b41c8400309221800000c08460100c10741c0e84510201f41d40003c0b035943c2004070101801014154010145908204070880101504014418022120354512100c19142900d4081d07400400800341500d44600304c0500c2c000714800c101c1d089448a0080c07001d5202e8006111445200d96400180302c10941002414842905250008c00c80003024150710a0b4000050b41c050310780e200b0005036105c80700345058415104000700107041c40180610714010906070344020000b0001a0758901d0001c00310340d07405d001c2c10202280c43c92031031514404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 818805035 1250 818803785 818803787
    0xc1502011a011404030c090605011d0a06140d0c09080f0f15040206160f110108041a10180f0e060421030e030c0606040c0212070803150a030b01060f08040203060601 72
    0x64020016050710303883d04c1c0c60780300c0c0c81d220210303841a000001c441f03803180030400403564054a501205180a68400030b507003541070004000c1c252505c14003003000380170112919038200510842c2c4400b10711060401c40ba40d200440500414860702c07a41c03c3c03500454000628401000c81d0503209501000c02801c20580d00c1d03c400b1641e0340c009441641c000701c06001f0001003030030100c40c940e203040c001d1840303418540c82c030300d42a28040030700260681000550f205000004401145091154002900c0380505540b0b42d5800102c50943da03002401c0c10403114194001c000d00c580c400e91500346841c10500909a080d07026696403502900c00801d1007110114143d650011007040e503002e02e50f2482c000c1002000d4040c918035582001c0003a85007038100c032044c010285030a10624107900e00d00e001820502d0391b02c141c0c3c000d0798096014007a0030100000000b5104091152102100e0140281180b03180e64072400c02c3da0481e40240100004101086600390344d590041c508180709950040040c0200c1e6502c00c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 818806285 1250 818805035 818805047
    0xc120307050f0301300305070f0305160f060507020d020304120201021504150c020601050d03050c0114100305101104030204090501060f080109030801121e0f0209040c1502011a01 78
    0x4104001c1000600012092031207140042d8000d100031041d0140c0707012103026a44a940002d61242e46070114071402c100001d8018054545464014410542d00fa10f1400c082d140f85c0310701030010242d00103850812040210410510346154003443c802c10a03035031800011f990321100101200050f9100b8013003040710b004e016901003451403043c41601c655420300d00071404c003c601600d044408010a0f0400c41d80c80c083da11034510041110300c0108080d51410002c03624101d40600040c04100002500c1c09107980c0035005811014815480e00b00b1501d01f00c00c2c49000058a800115114002c000f0701d01c000e4180d9015500341c5200380c52055290901d16400c10008260100701185c80d55241e8200040344420f402d0312303030010303c1c410b40007181c0c80c111071400424051050b000070070003131007240b00b050118242c0040700003c0b40401d8032100b0080c403e810940040c40c0460802503010941d0b0003044100182080700ca02150b880c50705c41880002e20480a900341c0b1303d032101120381d156212440d51181c6d8400d007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 818807535 1250 818806285 818806291
    0xf05090604020d140d03020405130501030222020c0a050c0901080a030e220e01021b01050f01120c09290f032107080706050603070b1e18030a0f15020c1203 68
    0x141c4d428410900c488000d0708001021034240003003580401c041045092114840051240c0312004009035030541e80002e00980d10300d00800003c0c40030790410515019240d040392000040501101d0001e40d2618107190b44040b44000c1d540600e07c1900001010400000c42d00030042d03054407090354601024041c001c0d41408150f82400010380d0764006066165a0310071001100510400542c0c2d41c4d0044d5500081c0f601c2c1d07501b90341810382c03400c8100b203c0310a01c000c105040d11039203403001030801003d0401e402481c2494000700106e6140034058168420101811451080f5400c445078a886040c3d003044501d08160f162030b42c00d03401140d848072000941140c030207441540808101e091503c20b484903401a08216401c5032815628018405603150802c03483c801418241d0706649480400e00914103003480081082d0085040400d040c1c41324076594010108488024044411481031070400080c002c09051050310040b401d41092800140c40c2d000301c45c0c00214401c000d1540f02481080006154801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 818808785 1250 818807535 818807543
    0x30408040b090d02102f031e090604090e12070302430f0504050601090315090b13060f0b030a0f080408030c031b0d0804030f0917100f05090604020d 65
    0x440d4800c0060782e41c000301c03070043d02865945444001c40754200c4006003410745000c802d50341c3c0c0394211001030400001102c0c08c8030702c50800b42c0104032022a51400e0f40c01007181407580702c00c0125010030140c4140d8040944040020101d40880b820040c02d4042d078801ca01d4003800503000928070100b000d000741d6008110348408036011040000301000041c0743c3d208100c90152080500401b040401400321215001d00402c8808100c1418510f0000e4440201484000c019510340d0001061314509903000683d281e80180c502440c80c9003070701c4203460202c41e0040403640c0e00e107850240e11068969218845e103250001c0e008103000c070890f0b1240010f8480040c0708507a984020800800e8040c0c00f40003030000008841d00460322280d211041d070a6101d85007000140c55801510300c00c4c039041e032000d0035070340194250074032905540004004643c0600c2507000700441a0b0882e034100c0007023000081490381c00c94801010480c0c10302101c44442a00d00540e220302260f0f10000202e4050300e0400300c400240c40c45 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 818810035 1250 818808785 818808799
    0x60c11040e0c12010213050a0e07080a0e0d0c020111060601050409090c0b0d020a090e060a03200a080f1506030a02010e03031603020c12011416020c0a0909110303030408040b09 77
    0x100001603400380c01d443c65882c181d4000c1030502440000d03410b8132010342000c50340b641c102400c0882c40241144e00070441070030022200d01080b02c1c030000361320102400e100182074402c7c2542460010b0303c10038203044200d0000b101018407a8682c54040b82903401040169100d80c6042d10700003500313001e08440711060704c41d00c00204000030302001c02001041218128030003d6194130312908003038100c40c40c5900050100a42d0420400e4540e1034000a0082c3c81e8448000707040044440c00001042e80c0343c00441d40c21203642000400c0035000020081c001c48407100131604580c00640d184106803c4c01d85041b0303090703441078052900540c0030f101200d4130004050212703402c10001c3d201401c0b0a0300b441d41d068025270401501d44a1a0030428550128500c0d440024801c6c07403034415401120071001842d00e0f1170a007510740c0d00f400962003400a220b68810003415120141d8580d111400200902c6208480254611000c41128240802617a100f1a00050094206485c214000b1080c0d4000c400007036211344 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 818811285 1250 818810035 818810053
    0x2060d0e0106140f01020714060a0309141f2a140412020102010b040219030504020a17060f06040b060d0902010e1816020105090726030a18060c11040e 66
    0x300034807a000c010141c8402142034000381505014821240038001811500840d409200720082c4140b030b0000208150b525941c0ca811070340b02100181541d03000140380350342c6204ca180010400180c1c407600080466000211605003c24603070480e00102170840207001d51880d0640515046101030b40030805604040000c1d1949101e00380046c4d100d034015110040085822800750750342441031144c054001c0c0c070210315141c4051548025410314280000800d030301d410000b811925107a00410040520700c01da0103210f5030f07600d0900d440d850202e40c40c0c0661652640000c05500e03150041c0e05c0780c140060074103071414055452074005049141d10590610846c202503ca41e52280f0210405504001d5401d54450a10758581d44000200031a4407046a0409081c01144003021400c902107a40ca9814404403c01041d840c0e0303410042000d0403203440c000420b4014440707401c14004012440112048460a42c0780c840941d5410400c0802508907603421340314414600f403990004803016a19011103688203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 818812535 1250 818811285 818811311
    0x15040b010e090a2409110f070807020109051306080c0603010302150c0a120903060b01030b0604051012020d05010e070903030215071106190b040b0f01030b2404060807050a0206010302060d 82
    0x3203081e0030012004c1c0d940540800900316540320345400454401c140600d4a150b04040284500440302c01900d06107000451a04585c01080004024180070700907000100f51007580000a007414030588102e805010303000442403801400310b078144c0354000e00032810600348010308009038110002c03000082c41441950b4007c9454030b100003100c08207070b0752103125080c01c500d404000e41c2c60095200f4103041c1000c0e20511141c2c0c8180664094038411750b01000c1c1002c218904941ca042c2484c500324105200044c0d00f046002650002410b81d40d003164102407585907442c044075000e9151001400582103040c0041560042003403840c0c2110041c503210311410542042c5508011040d125404050345120041071030b68114040d0b802031040446040103403490000224a000307502c003066a04054ae82d200c214202c1d550300e0f950340491611303c40300c1150710790004801c115a82c002e010380b01c00b0459100001d5900340c4600219904a20b05a02409040e4a150b0a1000a4100074440d81c0d03d41d44a4041030104 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 818813785 1250 818812535 818812571
    0x50a1a030123040f052a01020604020a090b010311070f050708030a0207030f1103100b090c0c2808040608010e0a091e051f0501030212071a090301110c0615040b010e090a 74
    0x981880000014546c00c44c11403520702d0341150344460641d0030500070003015a80f18903031301040703407240340f40812407600c4000101d008003d02c00b20b4500d2a4808169482406010302c07135641905d00c41d030111138005486043d0180e4a0141c58440c80040e408080180001404407803c8012039210380740400008850000080c04c003241c480035a004296100701c0000d141c580704038820b8008207604400d614040792030002c00d03241c001402d21000c052090714152600b041c100d08079805140d402240c00340c0c60355143d280c0105564000e100d100100020b410210703800801c07500c03503200e03040e81c41003243c041c0355030f203011400c64540b40c45001d850794052000480c0310394501c02c070140060805000300141960442c41044035001000c403e0901603441004240007a094041282501071845001c40d51110041c030006409802d00602980c00f48001107079001492000003401c60003100024801103070000540103110803a0f2228211a000078184941d034885400d020503110707013044042c040459948070082180c80f007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 818815035 1250 818813785 818813803
    0x12307061811041505030703110a08011e050109020f0304061806051614070b2a04030f140a030206060105070305071b06110610091806050a1a030123040f05 68
    0x741842c00010780085181a104800f8090f9080201240e1a030510000c2a5110002d02000300f4440300780da8103414503651301200701c0043c24030f40c009100500784001d07030028012402a444000307900307040020031811030900a035854901c0c0c4d81c0c000c034210780d1607885210250000701c219000f5044d208200c1b80110f90300c2e004d8a441003030110742c40c01c40f403804410010009056180381180241007071182400144824800c507411202c100c0704005000403003e1a00f8407410000c4a2301201c50000600108006034070400000442c040c2c0103170241e022400030301030b844486000d40240143c01400004070030f580203001030075040380a0701d06035040171042c1e510600141c140001410300c00794050410850b640c4d01002e14940900180302910007414204080801c5044600400031196200c0c140d1065480b48007041c94411034000e141070000b4200100c41100134242e001c008104000c20320a04c83d0641414003c0d12644840d81170011800c40906030088041c00300540100c0350f00c441c1d02d0644011800c20083c0e02c2c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 818816285 1250 818815035 818815043
    0xc060501032607020d11010203040906090518030a091e03050106080601030b0907030c0303120f152603030a02090a0e0f06010e0d1a04080f0c030c0105060123070618 72
    0x2001c0c81e0480115503060b100d89503080c415100704000e10041c0c641d0070f41180a103034818000c4040c8090200140c1c10350060341c0100c00914500304002846140a41085005800300130100380310010010206489101c1c4000802c04110490300070401c80d2142041d4000d2030510710b00511400703849540c1e503401c0d5681c0394040082a4400b00040c07082c0500b01d00161b420060000084c151685150b807060000400303031001500b4440200f00401d0300441a41000402d0042c24000708420b00400b1a01102c1c00102d00800c032007802800c8801541581c406a41100943c58030001d6055584485100c0040c1d400702d8802c54101c01c081034001074840c511003589008603180101000c0324509500018014405840140e00c2404200000808582c4043c0305941054081c2e46485065840d414000b5140c8141d00700c207000801d0004400c41c4843c0302002412030740b04690700070301950700d0303a0740116150354015410314101c140c030f000042031428400c00140f41962040c0c50200c0c00001c64180705d9441c904402040e030b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 818817535 1250 818816285 818816303
    0xb0409150501050c0604150f020d0c180803042c01121401110d0c5a0c030905040c0e031c0f0f03110d060f080304240c06050103 56
    0x504a51006600c40d03010380000c2c40d01d64180007449160554132180a80050f249418040c4050043c5519402aa0102402043c1956a40c6013401c0040c0140b510f80d06d1000056915103110750345150100901c0c0444180000440c1400d060080c11411080440082441540b80488001001c00c2e40c000240c000c000200000045004078200000c1c0c070700303c034561441141d00d40002c00201c1010a400e42e440d030401c0410020b81c503441440241c3d82050720f080070039190449105402c1c0000030480740e107109680350b402245c050012045080210030300c7c0614138a02050340000311054584141d030300c030707050354000d25000700c3d0306903902c002c20120f0311450300800004284204511307250070104154a410103280307102c910610603900c4000c3c220076000001c00c042028458003034800d43d120f9000a41c4a550640c0580c1d076604819040304020005441801c4c42e1848050000900c0310002c426141299100107004155180c650380842c0354200da40b154100340b04000d00c164001c6041c0740710b11400395100f10506 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 818818785 1250 818817535 818817551
    0x12031c05190b01080c03150312300403230f07020103141b0d0e0304080123010b090402070c1e0306050c040b0d0c090834150e0a0b0409 59
    0x8104468100864003907800c1842c50602c60742e1015025074451006070030b43d61280c0383c08046484195800c41800d1f0305100e8400c00c00c2405070f040000300600000d105140d640341c220002c482a481e4551001c10b01c00c104074034006004680194004500000c1560f0400d01e0040c06100c4035009401018481c44002c00100e20380c030865030140314004500c06001446a01807038440a8500404200c0d0b88140c1c0b08503001c51850700c2d40c02544c011940780070081003901d8a0b00d8803042298000d06010001a10000030500490161200c00e00010305a41c4410034061a0029503801d11001e9400032100b1290554403c0c4006002151501844a513207801c804441c00185141401c50682d5000b03455299001020081004550a54021501303880327507901c000b14400d000300e10181c96916040e800740c0300a0098603441d523400d03201003550107016410103c140c007011040c4602044008014010602d418074a80100c01510303025a03481500041c00074031441402d502c0c1c2802241c240c005902100f106e43d00e421a07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 818820035 1250 818818785 818818801
    0x307120314030420061603030f1505060d0e0a021c020102011d03070f140a0309090507030203060f061e0a02211602100216030809131a12031c05 63
    0x20191070900d0101c0c446040d4185502c0b10b44030102e449885100c2c2d2441c01510404030703220307041901c00d00b400042008400012600b005809886d98641c82442c052619600ca207030300aa80581ea0706a64010304664105801da1420500610b200e487c0c40d043e034414100c0c40401130750396400f200d40050719035081055424140c80017900b52403040f0b81001d240e101412107144083d0001003030307803802030300300b4001807a1f1010760400300a508403042e104191809005204001d154011040c0030845041010412841c1d6803400c049049003c1030b42c4840d4850f004204000040c5008000303000c0c01d80c0c54031345130050102e00d0b0f000c03011242c0c880c030103440142e0070401001d039964072071100150305100101e800c60f2625a10b0b2000021040318160003d12440c425002020124402c020704044102043c5240b914103460f410602c102e0341050f50f40b03e104d145c0380d8a0b1201c010201c0e010340100d000e2000d038171114062a03442001640e403a2204038210300e10086c0140c0c1890741090444c0010702d03103150000505810701e450 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 818821285 1250 818820035 818820047
    0x62e0f0302040b0d023003160c0f06020712081b060610020f060c0717030106122d050a022a1207050a03080c0c0a030e0901290306040b03071203 63
    0x100e449940840c00a50150311401240e10301c0b121b400821002814250320929145410100c0782c001c170f0320010400d01d00c15101a2450350285000b80200165140d560f1020740c1440f03268040d02d001a0840241086201c4126032003001c110300c55800c207810b10385a5028801c264100010101d255480101030041700e05142c00400c1044066201500201107182103c07030313403000090310344210002c2c0010540140080c061190700c2e07e410f140b0806a80303595070721005007516440e04084009625007400b1540600c44a400c984042203482d003a03240d44041c4181d00da00506008150a1005070200b2501c8190420b25090074607044420629200b200c2107201d010386003030220800d480c510a010058180840e200192000c265903141c60580002d9445010400790740c043c40313100700c4952082c802c02c0b10801d500080d00d42203280c0181c0d030016480c4c0e40c0384007481009030415031101d00605d120032414442d11030f807002168092405040822061030036004a440c191880d0f01c16014661103418990400d94452 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 818822535 1250 818821285 818821301
    0x1a0d0b1324151d01090e010b070b0c03150d080412140706050c060f09070b0409020703020d090f0e04020d0c03050f0111092d03010501171c02062e0f030204 68
    0x410101c039022019000341600041081000d81083c21400c0660642e00c00c0300c00c4e902a0442442c07001441d41e507810301c4560f42e000500101c0f00c4c0002840000d05246400342680c1c8a0145440000789400f800c13420302140d4815079105890183c03082101089501c4524000c0980d00c0c41041e480343c034901c00e0860039040404540050081100800c03900101040000e241c81e04640c040c1045000c1ea124101c00601e44802940b02d25064140802c4c002122000c0d40c0c003070801540241c0998005a5900c0f10461350441d840c099011003010414080c40341d14441d407601030340607201a010040b03d1680e912940d101e00f03060740c0102d4035940035007034040d0b107110280610314600d84120383c07a41c1004600341c0000c2d800f00d02849811000200f00e9100e284004100c55143c1c07090380050000c10607035031030b00d000111149000148444c0c500c10030003113501d02c00030503100505042103a40900a10340340c1980e02ea4030f190304402e80c0306031444056001601d540800c0d40c07040c0149641c5400e8002c107480c61061206a4900d5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 818823785 1250 818822535 818822549
    0x6050406020f07032619120b03070509072115030519020f0405060d0f0302030c0c12100b030a0507060305060f0f0a060e1305130308011a0d0b1324 64
    0x5110130400a00017003003041e002012502c45651540001030024018002c08240800c0c0d540c4010840030b4940d0003502d2a0081440208184400d5a18030141130740c2d0b41c180e01c2406c3c1c212440c41e00140403244500c1d8802002691741c1201d0b07161401c00142034041d580301c90106454025452000c104220080142c0b08030f081000c400504000e045400040108a4000c0a28003454803180040c4456442a11280000790b008010442120341350800075501c1e045a604043d00d80310300140040c803442c1101c042ca51012a01008001e54210100c01001400304401c0d8140c00d8404c09040d00d00140c0248614400760801707a40004591800c0740802c55840c0740c441015020701c03601311071a0b9480c4c49142410050302c400d13050040c0036190000c003242c252038681041c105c0710340c0b51205001900388020300122880c1d0203580c03114100c2e41c982003a48503031103481d0700202c1c1e401c0c2c0800104001c18101d801141c030550008241e058082c20f40c05002d030541c0c03135108055008058035000e4803520811a80c41901800304 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 818825035 1250 818823785 818823793
    0x10050c120702070b09010315120605060406080705031b150307020a0302011a101d041d0105010b130e0601020a060e03220609090b040b03030c0d03050a090c170f0706050406020f 77
    0x90001d60718031324071414041c14105600c1e4109240341a0029000310010301e12850340c01c01a040c0c90070054024802590303514803031030902c1d5002510500014402040d102c005002d85814180200d104010780320030301c4a15042109141b506840030041c90186100304440e1300940580d958601c0c00030308442c0d4000360821900400002d0b03450035180d203220190a9a9581441a141c28040101c00d40c1d940310b241d6400c0c0d01c242043d2003040808541c1103603108110f00080240056601d40301d40c842d582c0501044012503480c0c200c4100142ea10822441d90010818016560114036980380c60007a03403030303041c260812039100141e01100d0449500e0a80911070400510810182c14840000c5c28074000b885814402c80c0c440100c1711165070f80e030b8003420070058010122a504c54151814a4640c2a42c04026001c00e01c2d2000043d000d08040c000d10303107131540c42101d0304001810400300f004540c0d42003d440800307119416203803401400c1081138101401154031039640306c514203440203107030003446580001c0c1504 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 818826285 1250 818825035 818825039
    0x30905190504021b010e0a140105040b041704030203102a02100b0a180c02070f030b0c03090c040e010510091406090c0f0703051e07020a090e10050c12070207 69
    0x14021000c0341aa642207901603a1052030452000c581c0000d500b01d40c0b0154a404a60024100c00142c91000d00703114034240151036511511072400c8540455002d01080d60401c001000110411491500d404880002504290f1241c011914280d801e041c034008a5070361312958922081c84000e1084850016548090f000c08060402500d804100d1505902191105400e5483d13689502031000641484051a814450301c6207102c4098510481360070050700404a01282c003800907010314080d0b9030402c10000300f9807544074140b02c043e84010510000b50103403608030b036a20358880c081c0c124242c41da10000309060a28802402969a41f54810704607145480d00c480a401801040d05903c140304a520038000d69403a82025914851100c1010110030001170060801d9000b10180c100020074410009034558451482940d80c400c148003c1c1d44400e0500341000502a250002a11104488161001328040f11444015114143c85489000740301181b8101d52101c12017106900500310320040420324 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 818827535 1250 818826285 818826319
    0x312070b0a0b041b050c01180b16050c0d05031009090506070201061d010e04020d0f0605010911160605190c0305150414013f02031204050a05130f09030c030905 70
    0x14082c4c210013080c420042254a40709100303510214031114040300d441d000403043d181003da8400304483c0c202914140002100700580301310162450303210403030014100010301036800d803400e400040c90340f0200c00ba0700c000800c208885024820131948120000c0c842c60528040107429100183c21010f000d114a80b603411405075090388213030444012703006040054886002240c10381d402084c0192101031400120020011190300960403070306440401c00c82829096800c81c02446085013101d081c038541c0907500e0109070207a0041c2c2c0c000e000f0745849a0b182e03e150290a0580313402c444c00d000401c4c0c1d241308001d01d01079406602d00384020111420040501c0b600310a107809603040c0525540c01c11081c2c90312054102c24103608a04a990000e03000498a40041c0c00c19203c11000c0124007a020340700c281c443c0000104156400d40e0801409480203e003884103004454980d03c2590b0403003503d512441b030251080d407241480701c60090755901468020f90a020302024956409503000d0300401d982d1090304 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 818828785 1250 818827535 818827571
    0x201020c0402030c0405120a02030d09060207050d02011403090c150403030305060a0b0a050d0b0402131d0403020d110c0d030305310803060303070c0f08070b0909070302090312070b0a0b04 82
    0xa40e0040b02d00702c050b072140050741848c1240400000f50584100704080c80c07640d8000c002e000071100d1543c201d45020392184244000c041945000038041002540b2903d0080d100901a640c00b801d03201c1200c0d059070884001404d000c0e241505d441103d000040c0500c2419818060142d00c000151040c2242e0741c54001a0303510340c400c0c40824410008003080406403104e141c1c010440c20040100195101c000e0f844000c03c02990a00c200200d02225502d0b10705201c2c0a514918420740c0c06401424481560700400c0d03500102c5841c1e0340300c0c140640d85c1c2c034950643e103403221810014029a4002001d160909107000c0d0300e0074903007501d0440d040c0300c0e10f1800c60308490501100b0156001c200389403039803101008285180142d20000302881c0f00c8210100714008142c2c035200440300d18100300c6101e1a52044000703031a2080030407054005103200000340c551802a0000d040c1201302500311640d1902e1242c0a100c15004440d00304c1d0f211440340240161030820380a1520b050400312010800c1c034180080b42200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 818830035 1250 818828785 818828789
    0x8040306110f03040c0f06030c09090e0f07091506090e06010e061624060608011703130803040609090b060328021620221808070201020c0402030c04 65
    0x20355240c284081c52200a0380c02ea41c1c6410354080026144c0c140fa2a1040c00040300d0f02074500301c0c0c0b04421001a02911a020742c0e90364078a16110b10b001c5506207100500500030441d4600d41c0b912801d078204040360810807040004000846001402c80e080041005114803960300100c02c01040100074000130858200c00c0fa044542402c19100e82c1e441c08000c1600c07405409440712520300a0b907000c0742404a0b840301c940b02c16001800300340f6044120381000c0300f00e07030700c0340620030001c0e80d90001804150713200079003001a1905102141c1c00c1c1910400f90f00d10341d8404d034001400c1ca41020400304582600301c29018003071b00c1da900040c000c4003400303000b0641501000300141c60a882d801924910341880350401e161200081c50b065544032044542c010300c1e4140200308440e115050003201c884805080c20442c0000780040165107403800315915080c10046030043e81c08000d9a032585601e15200b00c0c2d00c00c1c2e14081c426808507803120100e000182c1031000c020300141c002c43c0100100a080030a40c2c0484d42 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 818831285 1250 818830035 818830043
    0xf060f0e1602010615080406050705160f080705011d0f1b191a07021c020927061e0f010b03011502010204090f14160f030c0e0a0603061d04080403 64
    0x55074007010303081207001d00307800c4c2d12445855080940a00c40d203548012610321560040700184a19113420b04121254400d40c02d050090314507041403100001c4982c032052a10358090b04005090050b1522041c0c21a000c0d0100701000150f11000030456040a0103884039078a0950301520300302c413000b030011a01d41c114001d194800e2030b20b0403980d030b0400b010900900203404111440c0c0c0c56820b082c207845806911204081c4e200d007107072508911500d041c5200c0540c0181c0d0141c4200d0441e00c03180748140381d000030202107906002181c004030384800e0701000114800c199405030382c007120f940c0d00c038480d106100c050804000101500c00601002001c14200c904540503500c016013179175135000080740280603075046103200e1401c1882100300e58040303400c1050390b0302040c01030603215200c0c00c280201341d41250b15482c010507042400001558000da102400d121814100482c601660400181c134801107030b0003c001282e5150400e00c6080003032544580c0400309904405010b00b855101c5a29901540c40018 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 818832535 1250 818831285 818831311
    0x60603060f130603032307080a050a09080102030906152403070c0b01080d0f02031c0f1b0201090302010b0d0201021c0905060a030b030115051807021f0f060f0e 70
    0x110250b180c09111411040b4050420003e2a440b450000c1c00d01141520440c1c80b40d4801007940c0d42c3c2c03414401100c1d07409030300036010361030030351401c10544098009281d04000d0040c0c0c1100021501e0081c0000c42c864a0071501411440c80c1c0f560342500c494080345e0303405001d05601816900f0640003103001500c0003030746001e036545030b43d1000c1c01120031101143c0000c00302c80c013801c0000741c400000541860800c015448030000c080702c80008903504d01840e244402c58040f00d81139800030034540e510802c680380c0110000315030f59620b40c05403081c2c0c5400c02034101c0141e556804030820303d5820700c12184074240482c0c500d07800e500d1030b400013036540c401100320040940c41c2c00e401d0500c079402040c1d17241c000d01d40604100c0c2c451408402c003900801c9600340320b41c040d50074031801c2c00c40140c0d5140c0340b105450004204e48070007900d604000810807002010384003548121400740040f250014130000f025140e180d00821207030100100d800079158107500070b15130031280c82014841951644d400759413080d540d003502 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 818833785 1250 818832535 818832559
    0xf1e060a0b0f040c02060f0906160c17041203080108010e0a230a030207030308011a1b0c04020f04052103090d05150126120f16150902130506060306 65
    0xc0b40701d620110201d5002e0b15003808100038940103c0c4440c03050b20b948401211030ba0342e01c85050344400003112200c204000b00c000c8410400d014800500146010b403005d85d0b4802ea002c03484d1890380d48260800001c10020303040000c1019030101019014010b03460013849007820600c00f081d030380d450303600c0700610028090710034201030540010760308140c0c2d09413400c4501003c2d1904004c4d40f140d071b9038002a00069a13082c000715220071a03120b02801540840422444c1040c1a02c100307010b511070744c4030b900d8203004000442c11181e0311380c00034018068210000c00e03030300c52800c0304020410240030286410115510603e003803443c0e01009032602450300751900b2280925a1820a0502200401080440c003500c07001040d40860368070185803c181294016030b140f441c10100e0341d0380c0d020704244165000410040e41c42c0114180b0081c003040038540390804944c036200e0b603409500c40c104280c140041070751050309509514142c1d210000c00d0840600400190400401081081c4402041c00e07008081c038400c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 818835035 1250 818833785 818833789
    0xa0b16050d06030c06020d080708040b09010e10050115030b060f03060607080f210628170a05010507051c050402060702060a0207080601140901030b0a0e030c0f1e060a0b 74
    0x101e03614003000c1401049229101d14280c4d00c0c0d4542d82c010300700181300d00e400d10030310140581941030040b156600c810220f95901c1c0d545640b02ca0008020801c155214900c41000c00c404020207110355101c8903000c1400d60500ca441345c181c17070300c41d12200209400c1c28608503e03501c07040100e55241000d201d180d40c0d17968650020590a204411000b80a004001a1406000040c102914290381512a13101c210720306c03041241d504000646100b64000784000a00d00410840006030b61604d0380031075000c0310507079078004030101c0a41424030451160020000401000800c1c0710f03440e0b2003022402c085041c903022210300454042d8034090038529a40e2240402e00390b60724038050b030761010b90080103a82d0358525040000d466140512542c405c7d4030401c400850320301c600d0700c410f01e003551000e4480040c6078696162242c40038070240c26400b030142d4503200032521400a000610a208559000f0000041400052850240e00c410541c0001c105440c043c8042030010174600e8000b03802c0d04e030210356a404440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 818836285 1250 818835035 818835037
    0x806091b091903140c04140408090910050a081e070e071d1c1a090c040213120503071b140631080105130b06010c05030c0a0b0a0b01020a0b1605 63
    0x400703444024841d06a07203207640000742084c0f0004066070240089501400d00701e0350801c0c00e4070012724a420a1141c0015424121481e0740d10481f04066521225942d00c04101d0324109a00040c6550300072696803080e000880c41c1c81d4410100b81001002c0c081d10700103519242c508060066000c004101c20200f1301d0b441207140b00304c86608003d141403d001c2e94003180000e903110001d4200d440214941517060140c600001c03d610a451510181c822003102204005c001d502446e200b4550070210000441d024681800609102d48100000d42d0382d40c403182811038044080162140c0c4041c019841400348051010600c4140c00c03080d2000c40e00c0d401c3d030341d00d03605004c04c0c0400401b0a50100000e82002c0100208000084940c0c000c02000740ba00d40e105840d0314044d040c00003600c580d01c4103000c10059441100049071240c0604166800c0804000c010340c10070034004010f48400018106000f103043c0316114040c86000240002c3c401e0078140d07500c080300070000610b0200c03c180a0140302e03040c1c1c0e000308 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 818837535 1250 818836285 818836289
    0x9090102041503020403030f091401200706210e0304090509010209150a0306050303041a030705120702340b0a020c06130e1b070f0f0f030806091b0919 66
    0x2501e1a820b400030004010020f4200e031205800046605a0380481140646442c03801e854420b00360014034004c0320015a001e1a2103030b250b429845401889030503010003880090080c00c1c4036039a0070308031461002042e07850224a0b10740d0b01180d203001024501d5050000403182141c41802003c510356549008842c024006c11480680020104034400b64102c4d02100402c600c400940b000c1007025216800d0542c1c0b03010b1801905003038410b01e07030070020840c40301001e0f6034018014902240361600c0680880ea1412050351488003680c040c90307841b0721a900282c941c0140480070341d10b0b0110100591100d40550810348174244080e040090320440042c0f0070720800558038000707000940e840c02d4010310180c08000c0c038801c010040010f000420000018484581c03000501c1c0040c072070500d40543c50302100060090b42c100c854010011b54600043c074a200d40002c55406034951003040d181c0300e001c0c0316480400900c1000004068500100f11400b4407063314045513090b07034101010f0f601c101e600c02d0000303015 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 818838785 1250 818837535 818837549
    0x1b071206090303140712060602010b060301121b0b0702032803200a050601030b0f07020a060b0d020a090c02060c0c070314030d02070c08070501090e13020414070c0605060904110909010204 82
    0x14040216083e0040d11000613006c01d10030400150340d03174810803405ca41c0d60203000c0790302040402c010442915511400807419006010b80300c140401c9119040d0340701425408081300c03507404504c2030154034060213102c000c880401020b1200158480e10311441e4840144000e0a200044c5410181a0713a0034a026800303155884c00c6030041602d0741400c43c4c1d80c0318244011992561136400140d1400c4d00c1d20b10a40c0a50040d03001042d859001e55122400340100160154011007465100405179841407030040050500701b43c00980d040480000078204074000b081da0704841c0c001c0114281907440010740c50308a94000e00141100041c2120f0181144a60254510b084e80082551400d00c4001c0d0310405c200c4061004954600e40d40740019a400007145c030498901601103c0016003440c00c0c0d420b0001181e2004000203008481c10440500540d810380c0c240c00000c28840b001c0e400c200682c8030716604040100c035660b00b2458190f40320801c1b04904000203000b0b118000c0860000002501074901030045 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 818840035 1250 818838785 818838821
    0x10311072306090114090c0a03031d130207032715110114061212190c0f0506060a060c080307030903140408060609070302120114030a0204020f1b071206090303 70
    0x403c240060191030740000e00c004d1003100401281110800041c80080d81901501c007000c100e246031400c2d01c111240d999050101c051080420b406036851813070340041a2a042c40041e00d500080c14000c0c882c4600801501c0c2d100c1003265508040e890b00c1d169501120002141c84003100d03031004040706c02e1600701030740200b5982018020340c901c0c5504c11540307119a030103550498504014660030359840f0206031081251110421407454541041c07864441e65648508040f01c8405482e40c8a5020159000c401d54080c0c011360140039403032410500380c078014440380ca02540990096102c07000340303110103010301c02416941c8515504041c010441131201c40c2043c100e81ea01d55568124464030780c1e01c1250b101e4070070034a0400051381070340a8401d954465100380b00c0903038960b080203481c0246a6804a219a052107005003410051340d5500082c4203c0145115558079821641d5540240c20100341c0c00800b1908484810b1002c201c103410b90500654001e036020074003020740c5c2010b80041035814400316030b4801c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 818841285 1250 818840035 818840041
    0x2090a020c01150e04030804030c21030b04110d1815022119050c0405040204090b1014180d06020414030c0330040f0e01030c05010311072306 62
    0x20956000d4025160500001e0024582004039140981214081c0c4214902e0070808600031030712861003613521a00c60704110100c0d2010340c844544100c00c020145103500c80d0f11030040011907060050301031820060b9018440882700b1900039116008540490080d16030759905107450341d250340c481400a40d000712b9200020310321800140060740c09110101c140000e200740000e1080c0c120640148100c108421004541c0c0e4500134403005808090002407608009200100d00e40d03803103100900040440c000d000880191940502ca0300803400100e0ba828040c640311480804114101100d18014602d044141e0001e041800a200c4c0e01e49910007030000340c4041404514000403203007484c540d400c1103046940351550601050345e1540300040d0b5107401115032840301113103901d440381003468a140b200d50a06168950118480d44403030350740801e0501d42e4004c01041401000000350002d01021310781442001004030a40d515440f5151004052548030302c440c00e205000407c440d642a0900350517200303541 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 818842535 1250 818841285 818841301
    0xb01030621083901051501090513140702010903020f060c041802040902040906051e0604090c0311180a0b0a080105010e03011806200405150c0f010c021e030c1e01090209 74
    0x1182c9011a414640c40c000110b40a010302c40307a4146d54500c1656803015150a00062002d140a22a2a04400c1d078460001c07107201165034902c540b0421b0180d000251980076410028a030104035941001e4542120060110480813402254280c0e0a280381640b10400140c41c600e0081c0701c4d0343e1002c600c2c6031001c200411401c2e2980c1014040795011107211a6642e00c0160904000c01d410189a601080401c01009140201d400600745c280d02403e0018045646101c3d40d0220362040d540e585214401d08050540b0740760040881c0041d050302444242002c0e9180c45c041d103900010b0107028148070840001b9049540c0942240b04805c1005803a20b4408850345450000fa202901c03c07410001840c0d8000b07400c00c03002005440448000410400003200180b0404040c1c1e4003511200105021341294880140f81c240100c4092480f02c3c0d00410203170070340d450608556000c0b4000d4001680040284280c4902d000032910003031540e1b200c2c09031400c00c1c400e050500414420900940200d0658200b056803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 818843785 1250 818842535 818842627
    0xb0609100e041a06091e090309040e010507020d020f060402360a0c0c031d0402041d06010e06070231110c010b0307060f03050405120d0b0103062108 65
    0x81e00d081004003c00e48640c0100603200d00112915043d141000b00041c1118a2074407450307800410080580345040311810203e015a00201850000c030380d110400d00040c6a8100442003c10750580701404200d461010416220b150241c0040d200f40141c64080404803024180036040040e942030510342e4081042040b80c2025048a00440161821403520012030103121078250b00350749941c640610018424114610503010720119401c0f0350b080c000411080b201005002401c00d01003000002c51906d0400141401c0314015064004c510500c100c1c40140c9503030034440040d60790105109030b500c044040c200340299104051007226414a241541c401e4106d0f0018111071030183c0080c08200d0b907080526075600050311a400019a10140d440559886070f40400e07006445541070f501c16602120712454240c00440303074016126a0384001030780039030301440b0329002007100b103d9042c0b1000040c3d40c912665580701101410303444c0006448031041d0f405540c02c1205055988000710244c4003520b2100c84 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 818845035 1250 818843785 818843813
    0x1b0a0e0a090207420903030b031c03020309010b0d051b0a030b07030216060f0b0111010903020d0804111f170106020303071d0a0e0907060207140103020c01180308061801030b0609100e04 81
    0x1c032345040b90a101030308010a48520680064145506000c00c42d41d045009500082030103500d03558030060209281c0d00c37a40fa443c103003805400142903a00344031a1300420400d43c07504140c4102007a280400000e010b100e00c40f54408007034100181c451001040d4501880c40c10b02c0d00600c00d515002c11804140c046a00800a0341f00a80e0344804410f4180386c214200c1d15041d001401503404180d400d560b85100e9010140c1c001d104003086a040015180030541c00c5020000040304020701108104466034400c0c585080380d800405140e04551504801079201c0c40b010381030100b001040b00710080480742d03400c652440054003401807450950340c0c07100300c813015506550051040c0901c5800080e1940b000401030141c1d280303070385000c008601c0d00c13006400a6020210a1445549648a03126103510916030b8000c041e0090725507400901d0100e003017103d107241e90080d0b40c000e56180c0d401800490401c5101366446102a0ba10a00f82d44031111101000e00048d4407030740b4030880da00d04110820410500c4551 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 818846285 1250 818845035 818845037
    0xc091b0c031b0516051e040c090f090204180c0804020f0418060204090c1d0d02040905010c020109030f090e0c030603010e0a030c0b0f07020c04051b0a0e0a090207420903 74
    0x50f910388030400c10808150200c0b0841b0181c00000107103d20340b42c46d502180d0f01d00b4050508603c2700e50707980c9081c90260441e5102c1e80241c2d07030201d42000540d9085283c00c140804145080090494038800908500030261002e80038455115895107162501e40c410514030010b07001d003002808403071400f44080d611500a9144203800c11b080d543c2c116000b15190f0940c0c0640d488448890319001d070a10201128081003a0f902c035480342c2200020845c03e200d0300682c2c3d82c06500100e070402003420054880c4000606800030800f01034401c00c8a0280c09000542041c01035410300c3d6261200c00009015007000c0c03900c00341c00d004900601e8101030b0043e0941c8402840340300300048554500318480a004000c54460300940c00220041c0c40c02e10b0203034009030f4040c2000cad503d954020301c020f40751502a0004105d510114110788010701032132030070103207007002041c00000c158030f00345031680c1d00e40380042c0142c14220301c42c200040d6800b155071000c030540d0034041c1d4900d008402c2007a003221540034200f414400d40c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 818847535 1250 818846285 818846323
    0x302030d030b10050c0a0b042619080603070e0702072309040b130507180f0b01020705060d0b031b0f0a060206071b02060307020a0c091b0c031b05 64
    0x1038261802401502d054030030040c40b0168141d0410420f44259002442c0f07411113000351001040041c46942d01d060045004011744110102c040e03030060f000036402e0004641d03801c0103102c0d07445403440840314020021414030f4102c0245e01c9200110b840d01100c0d03006009103c81180801c80341c40d0f400140345086a03801d40c862620f40d2418090303d4640703d42518030b00d4102601000140205140c00c0245030807a14405080300415243c5e101c46081401680207400400c0360206502115074150042002d004e005d080708010040d00c00700081e5640c1d216104517070003110049075907030351a11194000041e02d000a410740745032145001064440b20f00e0032010310f20400c1045030000e842d003003510281c0d05031f130f1941e0000c01003a10780440035a819440c000441d82c0560b548034440300141c4846001c2c5000c0c0c082d50700200b80302d21403441d1000c6000500e811202580e40b8219200e41145080510250107103010704181c0031900d12814100d94494501c203245031035081d09541c05c401c01200040d940300e09841c9840e40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 818848785 1250 818847535 818847553
    0x6100207120305091908120a05120108010501080d080121170d02030105040f090f030509030703050a050309040c020609070308130e040f140a0b0402120c0907030603110f0105030f0703021e0301030203 87
    0x50442c0c0d691724050104258003242c40381d00d0080ea00c900800808509080079400c04d14246410751241030309801c070162076512600100040c03a03007007007000e10346080d0f400c1c08440f642c101032106a0401041c4007002204821141807800d02918603002d120310200d01d0b510a6031250940789280207540203108c2d083c025031034030300c00300310300401d40c441c050b81d50754001c44007200c03403c0c140c030201c0c0d85402205005034140210b181c0000020340030001280d80d6031088000e95218041c0508000c2152664079920055420000c20000c0350304020840f0340c2134030b03840075020761105070001907001712043c1c82d00180010311a1000344428400d41d460b9016001f441340d0350081500300c0e001c0d580d5455103800c8000804c61940c01000c01e00502d010f030b13a01114a10071a0444014202c10b000040200f00243c400c000840d0742c8890030300a0002030304105022480c2030b10200c3c0c400494400007030141c40014805454a01709002040850340729804446001ca00140b0f005c0010410b106580340c917a1080c88124801e200c2e2005c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 818850035 1250 818848785 818848819
    0x9030c02181b07080a0c03140d0902091501081f2d091e11070204020a05070b090a0b0402040506041b030e010f0b180405120d05070e010e090610020712030509 69
    0x889292030361003407130241408014042507451b00e046c424210180840103841418101c0c542c00540715030540000049510100c600510444e03080190a6660303120350000390030440c1e40c21017181600590324003000004072070000c0e90306504010382d42180d19802c0d6554a4440c98080c188035200884518030400004070365030340b0a0f00100d842115440390001e0900b0510740540340b0b11350081ca4845c0420007041d2420324141c0c0041c007268012030117080440c0d004642d0100f4484200c0803280d1101c84600246038041c1c80340c95580f031110004000903c00c3c0e455400141d0b551f165a000030001980a514070790980c280108090080d041240d4000030a41ca0012061949010382c0224080a6000740000c10701c8403804146800c0a44010130543c1c2c1d61040c0507c0c0501075066000624000d410864001150b08102400901404852501d41c4c100414002061041d90b500450039030050702c215803810000d40714180503403c1070250391100000b103c66120480505030060010041820125150700b405000055 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 818851285 1250 818850035 818850037
    0x41a240d030807050a050f0a0f090801060501080103061805100b190f090c05160602120c070b010b030709050607060e01050115021b0109081b01092709030c02181b 71
    0xe4050000b42040c40410803041c0aa00100310065052034041d14003c0406040011940113010302c0b00000d6025120b40400e9600c0b452200140006a00078000c03a49040002040d414042c08064501d9684415003822019588000d00300c4e50761000984515140082a80006080c04850795014402c2950ba15801004000a880c140c0315440b40810410b410451100c000344900d030b0300315003400000c0100090900b01c2110800303a281c418480540d981a021044e42e510700f42c0030340aa484c5081c20b10007040040c2102960074151103903085100e4490b580c02c5402c40d0f0740c14040d44450b400c42000250403081c850300c0d400800951400c0d038003d200c00e903a640341819482024460090050b00068020080c11410008040d026801417503c00e415648803024a410220510b070302801c01052140030002c99608035007032100401440503814220030150b18aa10101c1c031004082954540d16112802018017490383c080c11150050200c0340c0e040d50001d900d044805003980e4904000c1100d0381c0050386220010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 818852535 1250 818851285 818851309
    0x609010f0f0b012a0215030610090b0702100306050a092004060f0e01031b031a031218040204090204030b15031204030b070e121b030d020601060503041a24 68
    0x2a54002c3c0c03109450396010022500e80302d580d011134541340000c4d00540da909803940d04860078810029924100541009000152074200c1d0b030a02c003070f0401c1048102c4209064418030b903019240c11600790041c4004400801d815040694800411400401c4c00390980d8000d403034180144010715100700b22510744d001c140c000e501c14034000920712400c52300320324840c100f070700c2c01d4020605001c5521900303401154022192041d0b2140003030741d11503110300f401002000b1130003860000c0d4094401c0245401e0842d04a101c0c60340c0300c00039071103a032240e00f009403525070440d401080e10f42011511103499181481141c2c90a03102e0001c00700c6154008d56883ca80810402a041000001d1515080c031f1030340c881c804a03034000c00c0c2d02d05008015600e00e50075103840c046154100e045e40013030034030405030381c0e80c0c0b192400c48044000c0c0640e02c00a14442001d4000403180d040d2141030820a0b03c0341d45030319096010901800c4400d10034000a824820494000410300078010480c4e02d0301d5100050307000600803100120 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 818853785 1250 818852535 818852537
    0xe0414010611010609060303120506041416140403050304030c08151b0702041b090605070b0f0613020f1e1804051b0408070303020601270510080609010f0f0b01 70
    0x4800410545005400d0460b9500d8103100115880b951000e6841c1226883c3c2d0081d408600200d01521340b09005100303465110300110b074104101c6112000582034902c00804071914850705010701d50f841ea0103400e004941031562840e45589a850389082d0303851790040d00c03040300c011020b48400300fa64280450065641c10f60008a4017040d42c0724044055050892061682003410030440440580c0307990040854101801409070b03441101c0c201e0081c14140142c0c80041000028030100740019024680c240e00900c0e05910502c3c961a030500285280031240d05000a191001803103401e000e05000140c81e1401180160704141454008081c10900c5801d80080d602e0810030911101844d03e9030040b07070041200140850f070602c0c880100900d55002e50040f40300769001d22000c004056041100ca4003600b00307044180f07400b140d01c95071062881201500f0001d03c60305c4100041401301c0d00e1107980c0041000d901112214107001803914024514a90b241e1860f5081401d9005401051300a020301c039041 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 818855035 1250 818853785 818853821
    0x705010f050c12280e0f0303070b061201060e0a0501030510061d22080702040b0616030c08090414060405150d1b0f03051005070206010f0e04060908040b0a0e04 70
    0x1042003e001c030743d21543d492400d021301c030500c450f8a00b0348a41030344407003c41503c400000c00c01803010841c0c500c01d0f5181c41d0348a0b510420a40c0d0010729141e0074990020310541d42d032881e0405104105001d8065a040b40f4007103052442041a12001604120304070381c056025584551290068a400c0d14068007a90001c035014568083d482c0411036452540880d6036048070b16000510811007805884501045c1e4803540c2c0032891005610703052266418900f4225100341c60500a031140b4000c8003140b40c0040c0a110710804400140031a6004a81044500400400c48d03604600041c510910302501c200f40500d1401d000074001b610045091805050014074150400c0300c6641c0b220703803001128181e1390030340900c0f40001404461540f108406584114094401d9000c403c03103580890b00020007141c1158001ca00400890a001c41560180c403000000c07103a141c2c0d100e040c00f40180400c9540100740c9000068001456008180589000c0a0307607075440c070f0700c40307008420031080e00d0b0840300102850345 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 818856285 1250 818855035 818855053
    0xf13050a061b170a09051804020f060319021b160f0b0c01150906031a040f0210050702130519110f030403020f2a0613030b0601021e0705010f050c 64
    0x80c09400500c100d6101c0d12218140501d0324203d2109500541c00d42d8002c2000601c0a02031440c010405441150360f5000b804042e01d05500004ca00101d89003816005990000110700d140c04000e01d0101100081c81041d9900c4865030054400a00007070001c1c0d0280c0140c3c0010000842003c2000701101e003810004200c107070900150200381e5000b8030783c1c038155640c1c07140040b00042211368403200611100400041c1d0600d142070086041c3d41210250301c10341c044c1f000b00400030381d503105080182074040e94408601110b050041d2100d12580d40d01950048030510311005404c050342186d84100d040301c482c9821180916540d0f002d54414010003050030105200d40d0300310800c40005958460300a1045540b001d11542d80305003008209035610658402800600040c60121400c4481c0000182c1d01c0d24a0300714040e00e1200e05104501004000c0030712500451887e82c0700300507160710341650014500488075010f0009a40b40018070805000c00c401900301120380d400f4100b9552501c00000c05086004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 818857535 1250 818856285 818856317
    0x12091902040f09050a1b0e010f0e42010c1a09030f0d0c090b190f0e0a0b0706140f010e0703020409050702060709080f030d021c020f13050a06 62
    0x104a02d009040c00307550300c00c03014000c034204010840c851400359801040c50b40720a280100f18080c0e5800110680084c14010031825001c810b0501c08c640403482c4031081070710f03421101c04a00f0071419003d0200c82c000c0c220066420702c1001c4c9200c07031800100350500504050401952401003006c00078114034090300301c20380d040020200d0307241c0c010028003d492030f01d0540f14012140da00420003003004d6503a503149103d140d9070804104400360000d54003003030071314410016050f0901d8085525004005010700b2020020740070b0307003201c0030383c00005100e00f184d41d071200345402c0030390440c0e10161112070418840e1500000c084038400e014212620601c0c09680c204810010184006840d500415038200030006081c880e9109480c01006a640a000a41405e0100401d000c1c4035411500140d080099640240c2100004541d0242c415540158460802d503409071084219195402c03411800020018110544c0d04018000d09100d64529102240c56102f80702c02401e050081c2e0300032414060401141c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 818858785 1250 818857535 818857541
    0x810060e0d0c03060504120e0924030c04110909130209010b0a11030403060e0607030509030a0c0c05030604110a0915030206071b0e06031002120610120507051209190204 74
    0x7441c05041800802e9640395544011124111410f4860741343c5580b10019083e44206a020440f030210f4541080b03040c58030f0710b51211403d01c4028000c00c11070f61000d1046c0e8409112010041000400c2002002010341e60b541d0340f5801110864407400b16200010443d11080c4184060b141d0041c1025000340c2c2000a010300c0317a0b01126444041c0814052000d203150400c100800c061442000c0200d0034904008074249024800b6040400345424141042103181000043d42c8aa11035031800e442c2e04181400d0020180074142c004607050300484040000344030f500e840504007450103681d20000d55585606010444041d2000e580d000402c0c00b100300301500d03040003c3c04400d401403200380c030105112076813040c070041c5030f0b8031540000403c039080020034075044c041c10004960f0044298030340309410240481c08030004003202e20a440011101001a03c10030f0403040c580d103440310401c00c07800c01d0a400f0700103800984003807005192180015552050200d908051280000007031707451280303d94208005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 818860035 1250 818858785 818858809
    0x18010e0607060f090b0f060315150a0e070212070c1202040e031303051c020a0f3f09030b0411060f040b0c01060905070504150201020405100201020a0810060e 69
    0x489442071141102060300ca2150324445001c0620014003140d10780b03041010041d000340221050100302c03007080764035100032a80070480003030040c01800507038400c1c0350b041401003d00d02554104541c40800708421203850440ca0240d8902e40855a40203400c00782c1100621810000400c46c803140c5c04200005200c41c502128060b10080001c2500c0340b00c40842486e6070001507003120442c4004800b041400014819180d949030901e48a0311a1014450003039603c8a075180010407900558030040d06001115038000c0a520140c08002c00c00b60011303035030341e20780c00140681c50703078810708000c00054003806030346080f01b220380c08164900560b482d626070344502600e83d4006500306504004104080b208078000740301400f0050203442c1c944104007000c03400c4459640081483d030349003505200700b02d03803c070080d101100da24000c1c0c841c0f007005000080b80a0b00850b408150402c6c1c0080c903030150300b501900076081502c0d050703581e48002d0b50754400e0080300b01c02c248203010104016007200c00350781c1010144424 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 818861285 1250 818860035 818860039
    0x30703031209020d1101091a18150304031d01030c360609090f02030606070215090312030a0e01060515070302071809050706030c020607110c030d0201021e18010e 71
    0x285400e00f0340215a258004a00440e401845010040520361300300c0d0f000800b401c212188906400812001103810344a00c4415414400081e9a0042255030f245001820a9141c0362159103d0415103005450500364000010f10b035129228541c2c03155109119240050031544d444140300998481c241409008020388203441a0461008213010b010026496008140035507511003140c1c039085c2c440c0c089038a05102404441e0040050201c559544d0301a02c1c0c0450301201c0e5081261110300383c00c00d00d842001c0c0640c0e010b014a03405850140001406107203d0805920b003841343e00003291401c6d003201d11364002e40342e00c4a07400c1c00341e0204114002c09058018801c3c0103c4405a03120f61b0820121000e41001001064584414004001c010301c200f074000c0c5180e0a0a014041080744081e485140060450013081008401401c00d08420400391600003000f03429507900c0d01c10038800a0107035111441040489103141d8505800b02c2c182c0c401c131840150540407110350f4492510044414044d80e0851035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 818862535 1250 818861285 818861291
    0x3070e030a060c270b1e1e040513140c03131a06010f02070e010b09040906020d0506091003050705090406060f06020c09070306030b0f060a18021b0a020307030312 71
    0x16001886510030322200902c2c81e11180310b135801807030450210070312000c0b00191502049a0402c103501c41101030760300d20041d8034010b0070b04401e150303161031150052000780e55451a0f00300d40070180489400c020400d440003656103a4944c0700f4102900150740d032030300d81e8528807015107000550100744000556000070a495060551f0a190340701c500103000010505c0c2811220b540612a1a40e003017803103542940914006002c1141c6070907102d4007200b07414480d0103d027080001e1b203409141c0d103c2c0c1c080d403e900d501074021503d400440744040c00426040307500a00403849507000c40d5074508102c1c0b0040481b64410300500c1e1a6080c0000c1c0700e2820b00140044809036225400031420040c010981300103041c150b40107000440030002000440c88014000c001814904401032001c111b01c0e5402c1580402c61160003509a00c072040824240061544250b480101061411400883c00e800600342da0444640303107655420302103541500d4032035820b0000d40c180e010507820000030b8011000d01d428030f54400000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 818863785 1250 818862535 818862553
    0x111c0e0a0506090f07030b01060e0105070206030103030309060e030309030f0c07050306090a030f030203070e221a180c160615061205130512090d0611070507090c0503070e03 76
    0x1852600c06800000c80e400d40000c8200020380d4410854421559100d100038011185180c46540498006004510401801d40101d440c5a4082e0003102c180503400ba04050b600e60f503d0500030010201d01a046a189082180140742c61500200f07681c054450b80001d10f14004064103405160b6202400301c0a0900480200094a0342e0a03c1850710074034079040030b8840c40c460742c03500a000c4c02040e003611082c1881802804680340d8480c000601100c0192100010300c04600200c1c1c0e2005095240c00c0c4105042030804041210329600d021340040d42958101c900c5101d041071080a454100c400d0300c41040c0500451401017000042c0090b154061200050104064103d2645c400460741281d0003080740340024100201007845020b80c04613616140303941c0451542d64564840b01c002c0c14521050030301041c8520141c0c1e80090050348650300242c00c01c6403030107500d0401c0c5103810440c41503655010391000003e03141d0f00b901480700454903580d9414507540d14002d060704c8a6014001140e0544190406 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 818865035 1250 818863785 818863811
    0x61608220f060b01080a02070308040201110129010e0402090d1b080105150f0405060906091b040f050a081b0d060b060310050a05010207080304031103013903111c 71
    0x5070000e040d0052801040a43c5440009001d04a02800d0111120710400094001c2031340107075825006a82440c00307199800c40042a80c2c0582907803002e10700765101340c0c4407400c1d580550001e03a400d840d20070307242c862001c107580080000f07d01035100426002400c20f040345001602200040d00b0b8502440c801203a1243c6610b000ca0843d0400c50310200303040b16101111100f0700d001d40100414140440f814002489c0c0440404c0303801202034001030040904102003200114900d40003031906e89a4280f40d51140c2c3d0310320f80000c41300c1071403140c1800b0703054004000c501e041d0013140d5424886001100345095856400500004400c8200c0580340740781c0e0781c011490140c0d1850021401841500704090582c0e060100300035030850300da80f0050555111400802242c0c01c08425201181c1e00900203922001051001c80d0241c210001d590680c1201c0800d424165803400c002c5078200d520280704c0038120705c60b8860640440310b17445038040369141c0c00d00168071155040265a80c400b01c0f40f00c40840c6035010700c41 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 818866285 1250 818865035 818865053
    0x12150902180c0405010306050405040305070209191103010f080106080714130614040507050a1d041d031b01090f080a020a0b010f0e0f150d050c0607031106160822 71
    0x745510080c2d400090400456a041c0101005484100d07810403007428036039809000ca104003040240640c485c000001c0404450070f01920412015030b6080c004c2000340c1003800b00c203502c00d00410180502400010a00481c1485002e00ba603c044004140780d6040401541d100c801850b20242d20a42005450300c841c101f5005100c01440140d0340f400d140100c0408200c1a06e800a0140c000c01c1030a0040502c0c85600500c1c00c00b552071103042d00d08010042402040241c07010341060304408060401042507003000000a16a4400c05011a50300003200e035682820303108071b060f02a010205600c494008207080c00002c21039a80d841c012501400c009a0750001001001d030702818031441d00319810060344070071168440d4002c99111422800b0320308400c040f10403010494410340510900845801000790030044814410802081541c54101d42c0c40c00510804180280b441c0c98040c62020a08031010031400c40a04206504c400e41c81d50b072040e11204020004810452003202404000404612041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 818867535 1250 818866285 818866291
    0xe01020a0815121015030204020304030c0b010905040c030b2a0d0c031404060504030917011506021903030c0207030206040308210c0a0509060d1d071215090218 70
    0xe00d5801052038000503001c90741c509960400d019180081030b00c50100400b280210384c2a40c80322000849610000c4041c2034003c142c2c00080d0000d100005000905400c103885d0000144940c3c0d1043c01c580c0c86446801c240c405c10b50740181545140b8500b07100040c02c401f404c55000310200603451a070311404400c2203011105d40d05401034410001a030f054000c1440c01140c400c81010b090034020f025039116071034400c10340180043e01256442020400b01071158404000038409110340c81e010f002c101030602c3c000c000e40c0d01d0580d6510f0444500141c142d00105048070480400849101424001c0d18203402425680e000e00086000742e90004c001a03880501500185009095540e00c46d031002d40c45203a101540741c147d507041603110082103145820101110814009850301030780b0340050303d01194550280341004200035042c407600c2a8003492400800861003980402c50b00c072103654440d0600d240b0050310000d0103242002039601c05048603030f049442a9480544050303540740c000700004205c0c800079 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 818868785 1250 818867535 818867537
    0xc0b040b010f17061506040e070302090306150f010c06061701090507090e070b0f070204050f0405070b092d06040e0108060a1a10090e0c071b0503070512010e01020a 72
    0x51030040c803442080c42d041d10090201e0080802c5800c4114586503902e14004015407403840d0b0000d02c403041500c410080c2c40050046010482c01c5040103000503010b900210155030180c4030f201c1c0041c10141180404200c103410240141480c0700150004441d19007500380e0030307580103032281800611100d40007140620301c0031250001032400c0c1180780c802e003070010300c0d40043d4031103052905801d504180816620308882e0410b42081d542e0502d80c2c121040d074020a48007a501c80d142000700820154802001403042d0300c0b03042603941e084c1d00c907003062402d0300490140641200403448102c414000868401c11102c03000414a18035204281c00280b45074025000031512010305c10040002480402c034040c0c00003080070742031020481080303070300c1160300844060380c1c0f0981c1c1201c095940c00c1d02444495018104801c5400520318202c200051a64014001140e07841c058020740c9031004209030061069a000601034050b4034a0903081003603801500c0781c00b41c10395580341e0079501195024030062281c82d0345 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 818870035 1250 818868785 818868803
    0x3021b190b011202090c0d1509141b030610031805010219020a030f0806190b1c02030903030a0519050702010902010801151e110708070314070f0302100c0b04 69
    0x100d4501500000010390107003008405454511006030307616403406611591291700c290b103070708000c0e000c1d070041c046d280815501c4400800c000704403081990025a51b418514442d51096110420300c80c2c594040100160070f58541400030604624040c0301e90b9810310310034036001c070b030580181508030491401d11400720740d540e43c0018008114400078950100030030460018140c500d440b500c003d03080840f080381031010170040000180c04c4c6c2c1e0758800d94103891004070b000032100d5900c0354441c140d1036000c0f84c2c4403606250003218585403032025000712485a03910b88090f50540d1283c0c11044090800070f001c822040c41c11040710b034009440c0d44140c0d4442c466a82c00403c1c214158000580080c0045e00012266541c503881c044423350454000035947d0180301082d80c22203512842141c45038101c3d8518100d6000710503002031108000950882030700d005014004070b102000c40c004c2e5580e20740d0f11800010416480040000d4074040d18030901c1e20030786013030182c4004201d03911904039140880d411500c0c03542c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 818871285 1250 818870035 818870083
    0xd12090515011d070804031b2f0a061b060b06130501030b0108160c0318030c0e090c10030209010c1a090105090f07120204020408120d0b030303060604050103021b 71
    0x83c0700340040c1101a548501200d40c1000c000c010649400108041c0901c0400518948940c0d042c803840c96005801c0034205205258076203d181041c00303c241102041d20004150181074904243d00780c0454015860f1180c158007882140d00c240c184132042610140c0d500c0c0da620040703880d0f410041240359034150034021914203010000d001c6441d410032640c10444840c0400c619900c400503503111005040c2482002c01c040c42c54110703501c0320f101d040e6102101901c0000400c00907800a01402e4444421400240b0303590101035075921042e204940781e0000c6c2c510300f501440f6000e0360061542c0300041c54444003c508c0c903280c52180c0c41c0010f404020b070042170800c00c01c10342c000780301c1d19400c15010405405916510703d01680d4584503801920003140519080408541d255411100244050001e944115070804542d65994100e04e050504d0603041801d445140d16000c81200d00c1003c00404950500d4186001100250881c410340c00514130058038440b803000c01004a400010244442504045 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 818872535 1250 818871285 818871299
    0x304080f0607020105011d0402030a2004060b07080703200a290105031b0f0a0e16020604030207090f0e01051626010b0322110414090d1209051501 64
    0x14000402007011649005d006110b84442c1c0c1e08070790991100900c00c4000380d2500d00000c4d080c61000e41c8014100d036140508a00d0119901543c0f44000400700c0b03082004545e140d0400040b8411501300400b0050308002c07402c0000d004504e540074030cc1c1000b024210401c8411011460010081c034190b45150400d16150100c101101e000018040c0c1160401c2241d490034021a80c0c3d1002501c0d98200c40026001c12865511541e03521482602c004000749203a96854482c80c40b00001030b6020182c10541900307002d040340c00001c281c3d020300c0d4103600810410b071518050308020080d07545407918031a281c48401701211400d01030940a240700594003170355280004005806030f110101d1003c0320031030038495003a03542e0504503190f045079601c0b2711096581c0d40f49071201c00300155074410101c0c80c0546800035814440c644142c542221010f0302e00f00150641c0e83c00c0e5030220a012501445144d01c05048503040c184a000c8410400e076401c14040b91128060351418106200c0c00f45051190103013200402200c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 818873785 1250 818872535 818872543
    0x313030b060f010905090901140f0603060c0a09060c150e01060501110d0e06030c090a171203091e2404110909100213120503180a0b040905180304080f 66
    0x80011502c5100d45410300001900300c0600e0b2140510070540c200000306a608207400a01c0108030201728400b6500d4460392a141d03880065944500a1180c2c10000d094950385104076403a540f4240c43c0d49a2062815904907490030a8610846000c18000f90014428455000d02644106120000b10701d0030b051400042003010302c051f1100481d031241b10b8108000790080e09000c0110360540700aa6a030381d800e103180032a8070a55510a070410004040042c4900b4581410302285215a0540c1c608242c102a184014003040c0e50041c0c0d680c02010b5140c2203110046504000c1700c01d20350036540303175172105212003030b021640286144145106108000811840d00300d04004000200c81c031172440e00780264510b664294081202d11010b500003840c000560582504000270003110000c4203600c0201d11300a40c40780c10010354002c0030458410b9600042c50100200c030301740e403c04020103041501e1315202e0f202a29001d004001c46003040303080c0c6101c800c002c0c401403000d4058180240b80d2050325000701458 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 818875035 1250 818873785 818873791
    0x10b010906050d02090d141609090b01060c020f0910180207050d0c24021b060415020711100207030203071e030f0618150c050c0d08090a050313030b 65
    0x10050400c4040c0881d0780c10a041e00c000c002120001a12007660070041000f203100c0e10720140112401c0c402c04640c0d84400a2000c01440c00c00c0c010588483d9510036020540715907041c0100000c440d540107011140c85501d0300c107035a07400240411201c040c6840440d42d400300986070451070240c038000a0000001d800040500c59240000840c5080000e40760366442c1c6880050850810402c100000180400001e0703e14800300342a0316440b0300b0201c00c01d04002580041c040e801d50f56200450051040c1021814500c9660440d4000d081c1c0d00c0c1501490000b1340c44420100c13055518000422800d86175120a0580141a43c0040000c0d60a600416182c000c881c3d012060100b100099184c13004a109440021a984200c40c101518424640240034041c083e0341080b10400c2684d0400601c5510300da10b0f8440e003150f02082008010140342140e580c4a5400340740a01e40c8002c0710045128810155258413201d85426521214019035400e42154003800c0603103540716008074107005122500035000d030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 818876285 1250 818875035 818875037
    0x90406030521120f070908101401150207060e0d0c140f0a210f050d030501211a100b0a0203090307050406140409060b0301020c01021c06180e031b03030405010b01 71
    0x81010040728019040c0d0b500140841c406218440110302c3c046c2c01003007034070050304401d42aa100d12020040100003003c125a0021000001400000c0c09010312501e080c3c90b00d10680c0034240c0c80d420030720240c0307003e1400301b200f94000e990444440c001c03078013500451000d40f82e51015881c00c16000410403c02c04c0400d889280701d0b507201001008581818030020481c1440200c000d1212612410920085034550a01074a20b008605c002c0d0300d85d59141d4803d0f4140c59071401403480f10b0899400f0001c440244110083c945403005080801d0204548a0158015030b40c80880c8800303a00d40d5000e00c15500403546120145e0b2001c200380405181c14071960020341020750302003001d24504a800c040e0944906003650085940d05040401d02005070042ca11986010b8001d650704c881305d40249000354400d00b1408505480c0ea501a0b24003810783c00b40701c0460750b0001c00b0300401c85c03601207824001c110110b91090544070402c07a0448244c40102000c503003036180ca01440e03ca01c0c083c00d206084d51a0906401c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 818877535 1250 818876285 818876287
    0x4080a0b16080f04110105072306070f09052101110d0b18130201030e0106080a0204050c04050121020405151908011a0c0a020306180d0c080f0c0102090406030521 71
    0x40d07041183e08189a11030b401455451410000c400161003e20810310f01034183d446c140b481d0035070591254512482e10014104440e1f040c0d44002c0c04039102c000c1c07810f4400c00078280b003504000e689802c01002c0d014000d03840ba003800304d0070f204100a00311002074285500c880d4010400d615038005510030618034030404d446611000102c5207680180c0d800091104c0150f00c2d51916440542e48240d1110003040c15800c02000050b0300e6003d2540c1c2c51083d010102c0c4581d00317002c000340041c066070058070221803061b1511010500e01141c11851b80c400c0342c01492199a081c080000c4594690a1f5404641c0800d94401d41e201924803100c0803802c10f601c4042d0034041e00d1001040302c211500071b610151140c007000300740c44010709200203060440412020b50705201d030000740540d140d00941403070141956041224083d40b80024156900c0d0705002c000340104000780702d549007490180008011a00441d00014680440a400102241c10302e80060311550f00089107211842c0003d42c64660006086040d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 818878785 1250 818877535 818877541
    0x5010f0c0201120f09120503091e1b010c0503040f1406120703020904060503010e011406030a0507091508010f0c030509011e090602070f080c01060f08060a050c04080a0b1608 76
    0x1070011034071007400280841d03a4000880410407030380d110704503041e44102680b1800c2c0341c409000300150019600040ca2b0700403416112411000090406281da10800140141380c8c0c1d4503601c084044884e41207581400307030400c00800050814401040a002c41501c90815a0f0070b2603034200128055910aa01a840400420070003020300c0780103030b034407002d82d140240c0e84029090100e009400160b112541640c00c04a100034221019000300c0c000450480e0685007a99411003055541d8038070710b01c054082d0700305003018007017900c003030b0006071990610301000c20031903948400003402c6030080883c41886c607070b41c0c1d020360029944c90f001c1e60350080c1d1050000d002e0420401c214608120740c403110312401c40e40d00c01600d4104030098040c2c1390103d4118007829500e80703a6003006061365126100100f010f51030101c012512503551104101590a000020400c5580350100c21004000c017500d150402d080c180000101a1401c11116040a2094140049034103105a2002c01900b400000002303001d40f481c10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 818880035 1250 818878785 818878787
    0xf01030812090304050d030e040e1c0302030a090c06081807050f060912010204030b16050f0a03150519081605062b090b1503060613110c0102070c05010f0c0201 70
    0xda036040070540c50522040d89402e80ca8500d548500e9100640004074100c0800034140c103c0056080701200352410300138001801c01581d265062011003060304041c804e11751000704d00c01c0d405140e010703600700c0000881c2030481d21524000107c2d07034080340c0003640c501c2c204000720101015080e0b916180400034040203040000041510390340c0121103000b454003003002c609542e540601c0140014242000310b55964980c1400c2e41070540440792007080b18644034401c0100c5120341c00b2903468146152405060400742c0400b10043c01d51a0002c07490f44000181c0481c01c1e941d07410b80c10480c482c2080100104a24110714a8100501541c44800010301c0320401c1000e601c407241118031040d051070710323030391280004000000e1a20b50a10700d090302e149040d01350420080308242450007004ca403d09401c3e440c42030410141d545c0822640181c100f0420780c5090f262a40d0f80e0030000c05200800c5640b814550021051030032a001031600b610070f003003c1e400400143d40c00c1619521030413031601c3c280d1142001900 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 818881285 1250 818880035 818880037
    0x10801060c020315090a03020f030702010507030c020d0209070f030e0109080a050a091205010f06050d150b0102150a06060306121a0a0f090f050105010f080a02060306010c020a0609030b0f010308 85
    0x2140344240840d1409440440d074090204040071402c01d00f9540590030004080c5980303074400002200507100304c2d040c1132031020000041ea100c5550580d68180b0b0107070395942c1100c110700341c950103d0700141140f100744010b03a54001198403440040e51584140b10300b6980080c1a06c4040e48002d030107034544108000402c1c018400c46813050500d04080da0740d141008401c4945881c1030713002c030314130b1110f01c00c81d034003001010740100e440c20501241c14401142c9803005c00c4480241d80d4001012840540c080d203074104003682009082c06014010b4403400e8259688140d82c41804462044980341e842800344600780d0584112000340c003900d040d9130701405031035845d070403a0945400d15007130100a10000a031541c040340c0007440c10300c054003c180101d6010380340130881d4942124044a20b94280710002c60010324000e8100d0844d40c0000041c5483c402d00c2e002d0181603070010b0900b0341008200c68514001d61113a00c451001086070b0358035070410910b107041c0302c1c800041c0600440c2c0705912140040001c07c80800c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 818882535 1250 818881285 818881289
    0xb18040515033408030301051504060203031f0b0406050c010e06190504020a24030e060601020a08070206040e09061614030720100209010e04021e07171b0c03060105010801 75
    0x3181100c0750005420080c10007600003d42070004000402c0120f01c43e540840030354104c903000d413401c081d441011410341d1154041c500980c00141d0091000940750000d400203d03140c1c501c18800c600d100c6440e50034a10950f0302c584c0010340801c000294602500209104a01d01e5240710030141c0b000d0708005c012980207010680181c0c0005407540c020ac0d05640e02c40c4d8001c4c0c024141c0e0b12400b22150051822a4000302d80100c4400c04a8504011503402c1040403900c244a02070581c040c0103e100075544240064101d01403d0b0781040090102150032008114030354064990f0300001c20036407030180d902c180c070560001814400c00403403003070040d040c0c09c045007580c0d0448100e08100902000b007c0b140043c400200180c00410700c21070385103101e80d10495004289514080c3da0300940c40c00f0740400e101c01d0740706450803221100c2200c01c80050380d11510019140c014851000703c0c011460000911016800c100340400c205010000d164120354000c00c03114801d450150084c080c603616013000600009014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 818883785 1250 818882535 818882563
    0x30e1608070302120319080702010c0f08010b0f130b0c0706031406100c150e190206031b160b0a18020a09050604020715270c06050904060b1804051503 66
    0xe0000000c150040c41a15414a200d4225501b4030300710010042c00454103454150140d481c0401c054010f500ca050b880501520701e444100e1141d2900301401126803240c00b0500714403106000c0c0f081c80c40010394861000f85904000b10303464081180e8010700b4503800740c0c009418145070800810240c40b08100440d03000703000300c51020900181540a56211101c114018402d500d9500b4404502c0210b9101c1c0c003545042604648ca5070750006500d104915003550040d40c49203040c0005200c800e0004400608850300700310b16070900d0240c031120030240040700b0044035105280001c1102c0c000c0300e445103004840385030443da40320042d10740200301100c60a021342004103031610000740c5c05803980d404881d459540100a0750102c1e100008000042c0034000c8802c400180d5502d0301d40c900c40810007081070041d00200503001c00d0349810402e8810f540301c00200c581050701d80f003001405407105405881e03081d2480d540700002e203280b4001c200446000a069841e122058407203428603480001d00c0c00319030450 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 818884892 1107 818883785 818883799
    0xa0c0c0b1009201218060103060f1404080d0c05090a0f03060b090403053c0901030c020d090b07060b22050c270d12030e1608070302 58
    0x2000641030f80d002c00303200c0c0d07051030392071a10345035046004a407801107250044d048407820241d09a00a0701c445503680044550300c0b03034501807a8460048209048980e00d80340d036505496001d0f58030f6151909648125001c0c1c0a4000d1080b44c2c0c06400041c107581c81240d0320202c045000c000c40c00120f0300507080691100f041d05000b151a4080d9a042e19014140010404645c5055240c517012034070300d40440ca2004e0b0020003c440204082c8488010280c0d83d0080d1b000140c00d4840986102045502200040450545c03080e1602c0585c0d442c0612240c1e80c00c10b605000c0090031500101030740c4216664013040c02040501e001182d40c507140b140510065880c42550f100c107005010120900c00c00d49085410426030400c0541e0484100420240d6003003003503100d8419507400c0c0d16601003c01d0ba50102d5030314440c410807242c2ca2401010040c1c4240390b0901c41d0090b01d4400324800213000d020 = true := by decide +kernel

theorem cover : BRFrame.Cov 818705035 818884892 := by
  have h0 := BRFrame.cov_init 818705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 818705035 ≤ n) (h2 : n < 818884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
