-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3625
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:12:23.749264+00:00
-- url     : https://prove2.me/submissions/cda1c997-2c1b-4234-9a2d-7e29eb2525e1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 651798561 ≤ n < 651978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 651799811 1250 651798561 651798569
    0x17040c09060311211f150e071d0607080d11030405060702070f0e0c0d060f140a0f050f09091504030e100c0305030711010207080c0102040e0f0c0a050c1005240d0b01 72
    0x3030001d02418464032072000340070480d005903a070000341b1400700d100c4216800c514090083c1e910340b02c00420402c0c2000d4210406041c1e40ca8120308184030307503800504000086d042d0f250030000c01052038040810105400d400c111403e0301d4a510070b02c2880320701c40e01801004082c01140b01d900b5540c034248600054080405050813080f410000741480c0510801d52154003e05810480b0350740403940e43c66010b4800340e420094901c41d114007100041ea440311590034508440c000381144034013240351020010100d1008003d05402d0050100c2c8a0842c0103260500c0c0c0b01d00c0c03081c2c8505030404090810701451081165424041c001160710300400f0980240649a01014a1809030a1500c0084c42c09019014a0000828007078000c62813500121064010344152010394049108a0382c89075623569107c0c130281d940780c0b60110304100d001070b5140f0460091031854541000c40c1e040341124107400c0c0466801b01c80d9004000d00c806d200c0c0b600a07404c0c600c0c04001103c2100c1e800400105610381c60010101841 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 651801061 1250 651799811 651799843
    0x3091a030601090302010f050904050106091d060d0618150207121b0b100e090f012a0c0f141f09020a05101106040c0501180617040c0906031121 63
    0x2c4100701c5070342300c2d8003180c0000e80c01500c180020350352402c02820350f035130703602443e5015078120036410070504810064521407031006007800328082071600c2da98000c0c10300d544c6180c1000c81c40380054002c50311000c2501d103c62042000160f40d440c443c104540c8003d524940c2000b0400c084010924000c4c6042030130502a82000342c5031065124101c501c5420036041e4490680b28203032004000d200840400c4144503c0850002800201020060364440704076100c0d841e543c0c2e02d1040300030f4a00c1c5200300076401c8158403070003801212040d01c1d100c50640104105203c2880e0713000940c01c1002000605845c20b9038001c80905106040381c5a00240100c5081c1c0143c50203003a02c90101c3c2c6220384600041d9103605d0510302511014181350421710240b501d140a002d010921200d10503001c01b03002c1112604546456441200400210503a0410000040c000ba28810034840c40840e624025114040003036100b0f1420b1403600311100280b002c1d0720000140d01100040218001e0340307130080420a514420140c0c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 651802311 1250 651801061 651801077
    0x6030606010e030c03010e1b091e150d05160905010b070b2a0403050f06070c061a06131809050a080c030c0105040b180d12090804080a03091a03060109030201 69
    0x14011a1400604d011800e91640c240755060103007242c086584c0800c50016688501545c08550610505807001c1e20302691500c8284101c0040f0301130307407102c0c641002020008210006030000011590b80401600752002e0304102440d030304445c16800740c4c80080c44000014030a030340c0342001a045c035001d1307640080c0c41c02c201000042d10407a091110800c5401421303070090400d02c46144404242d4104d030008031608d206142008500e580c0020b401482500f180e600e00d07507030039401d07650b000161100300c2c10180605d08030303e010041c9030b680c100030301001d40c000d14403141d071289040141180c0c00000358000c2061403400c2c2c0d0307500c003280d800b0031450324442d0810490790f5100d1076040c941d491445081541555540f0700740030300041000c001080750150000d445008509825111441d45401c1103442c0f4001180c520012100c0320500f54024030030850148a600b42010741d90b0400c2c90074401110f00480000f26482c409100002d5200803440c40703240c90f00d0f40303207080d85001000600120b41900003c2c2c1484a19 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 651803561 1250 651802311 651802337
    0xf031803080613110a03090f0b010e060913020306062707031e09020d1209090207061a030105070e0f0a0e0f0115020f03040501081003020d1410090b061002010e0304121106030603060601 81
    0x52107182408a5009184609c40d6940340026032480c941a1003c41c411424840071440306010a41d100c0f0300c5c0340d00103002e0009900d07000700300071440a4200c0310030780e00c070f480300c0000c886908482034a40c41001c49840c04180031349001c0c0002014035085e6070800c1c04074a003000f901e0150301c48031284001580c0c020100054402d20b4801558117010940c0b01580d5280009819000c212490300203041c03c00b950800c0040170320f0748004241c241d810448031940028040d540010b10b900e04140021200b4801522595015842d903218100c100c03011200210408269001040721040c00100b02d0540b078660700c0580071030801010400d48920662050504100034070005c981d04282281c0c1020046a0040c10403801c1c13145490030304245403a454145145000702802650a5280345c02007444155101001502aa40303140410140108a42c0c4680071596076012080aa940400041000d0f15100e0b8840c82500c49500d400c8444032220903030603024800034028841280c0f00081d2150300600c1c00d017454030740140d10b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 651804811 1250 651803561 651803573
    0x2030f0a06151b17070c081204060e0d081b0601031b030803070503090313080604050106050405010f17030c07030c1802120c0c0a15060905130809010f031803080613110a0309 76
    0x41544c00e501200c3c00090410104a100c2898000b25400b01044da80044440d040400d0140280d2050f24042a95000108002d2a00c6070125030607038841d9490038105190402c80500341e449010640f425507101170010b006008a403802c0c1ca04d0074020181904c030b11411a0740f00b408600010307200c00d080c00004804511003140030300569003141c0194031004c12440c0d41d24042c954a40d01600e040c0d0300e6520702030f404600c90800c0c0c00750a0584120141011800d4602800c058442440d02c10542c000c1c081072008a001c5e0000f48054002540180c2d905841c6a0501c1e055000d10040c2e003d1488095104001a540f00b600c02c00b0f80c1a07003d0021aa4680c95101d54201c40d810003001443c002c100c2a221018104600704960081c021394130f01000c01c115541d0b4041540d991482c6204000d400c01c0710034005500650700c01e201e002c822411502e804680c0c25082c44001d0034801c000c0c001140031420890420015007065060000008031102003400403034a460503c03101072242021000405031507290304410320031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 651806061 1250 651804811 651804833
    0x6050f0f0913080f0d1409120d110c03040e33061605070906120507030b0402010c050a11010e1818030c061602150705040b0d060902030f0a06151b 64
    0x900300103150313039031540e10001140c10790000205c004642d26046c2d41e200000c02071011944200c4040000300300742d94041e6284c01e0f00b50006450141340c9921040da65404500080151056040c4c0500568450f81070000394903500301d00a11350028041030a076815a1880500d6107411112108001c0042c0121510041801707441081d480307031a1003021403c01c60400c000001e40b8005c40d580740b10704006a0303455000000f803060b00e40401400aa005450038004581d402400903003191050411000305070703561390354a04120408a09131110b58031048844043e50300030030349203d4403a084030003200802c4015503800e01d0800107042075140500740012050044400c204035515805008225640ca142c0030b02d0030030500342650300807401406811400c3c0e00c803600ca880100e0141d40c90361502802c150400a0300061a0020f0714290f080c1501d41c00e00240c0320105100441c0540c040307403208800c030301e0420407402c252900d95104c0c0404095680801c1d4005030b01202904858000408130b8440400c0d03402c003480c0500d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 651807311 1250 651806061 651806063
    0x30612170a090e090a020a060215240a08030d0b06070503070308180a0605221a1e0415151202130204080105010b0a09080c01050f07170301060c02030106050f0f0913 72
    0x1415020901c00049000110480c45d40d1007102d401210589580c4100e0f1181802d611601d00703407410310042080802c150103a5045a4050042a0f02c51420900050060f4215078410380b03882c2c00004140c10386201c01e0080c8416040d00341d0340f0030719108103640ea00355284100c0300e0140c100b1500c90041740b40610301c0e002c03030b40050403c0000c5420742651414024000c00c41500e0851586000c1c82d6900d095800380e1001d0b01405810180010501003500401010700c40005e102e480500e4030f800f4084a1200500b402601450050580d001e8001c5141058400c461145204c62003582d120b9008009c00b81d50416455555a815548440301030f030404201d201a0081d80c105031502c0d402c0c0f0001094141403c0043d007441810b60344c81d20010b0f683d441145840348034040305140090b604010303580100d05000014986944075001001940c030070100750301081c1c4c00c01c6e000302c800240c0c084030746425071509000f154040d0400b129111064a900320008e1821391040d2800f40c06408da40000409200e0081d07401c00610b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 651808561 1250 651807311 651807329
    0xc0f08061504090c020606031b121908090102010b0a050901060302280c20100e120706030c12060e01120503070b070e010f0c05070512010209130b01030612170a09 71
    0xb4070744618680300989003c1c1000c10041c411000042c0e040d02d00000c0348070b482c6500680c11290395601c5801d006207020501e21160b1103105d00c2c210f51078010400d03203540d12460b02400b02c044d140c00270306000a003565401d43d9403600c9915520014400b662f00c0e0081d0030304692560500691381e080740c0b04414000c076252041c6e04d140080005480169540200d03105035164803a0660b0409101800801c3c80c4e0410360780c8000c2d4005e9038000f40f80d4582c0303000341203901c8000e5000301800c2030f48240c5e454451500f191600118002a03c4902509040d500043e1002c1c52440c42c001c00e0141c1400c0080400da400c4051041c00840d00b483c07903041003400300c1802224003141d0030004541c0396250072080505501c2002a01c1c0e0b0000700700504441070340f445240d4011440d0341c0540900211481e140801c2154040c02404040555003000200c019130b43d0722100d100050420800482d2070405c420016086920380c1d4802200c1180c00c0c0d2050340010100c4210074028110b0551494513401b50318000c60380100d4a4102e0819 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 651809811 1250 651808561 651808567
    0x4110306101809230c030112060504021203071b061706060901090b03070f1209030203031605041d060a090506060d0c090b030720211605030307080a0f0c0f080615 71
    0x28840b0311100403080040b40c41510307851729410082c60052209115120665142d804100c1c002059030b00042d402c90b0000f0021080d0010f9164440d08540c0001402c4608a034039820384450f030032000011301c00070121800c1003a50340c160880c02c20104100240307400d00c2400c0c0024510000d030300a0014102411a00d0b008a890385012100a00490789040180e404900b500b000e03107491003124042c1d08070f40d99040d07010f14110703115540d01d041488040b140d02418043d0031f22000c00d0701c20080070b8082c044c0c0c02c400300e45045130419201340f0141901070740001c42d0783e03818541042542d803221001c5a41c2005082d42c0010144044e120864084549400400a0180010600c00c445611034102d412908441885910000ba0400e82e81e58403050b21107114020000000d0b0820f02d081170b0701c040c2c038444000114070100302080d552081c0c25980708803012404140c0e0034040c404441e11603c19003030200c2000000708208958000d0281000c1200d0b10302c5010000140b00241c2c079600ca0500512809210605030380d2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 651811061 1250 651809811 651809831
    0x735040c0e040b0106030e0109080a26071d030d0207060f05040803040e01030510060e01050f180412080f010e060915030a051f0b06090907110a080904110306101809 72
    0x20f01e10080c41040d0000b424840c0c0e800d5a00018460b8035041032740510030314604001c29109503100d490411001500c110b03440618400c0325038400b00c0c1803045460b42c0d0f44100b03c14181d524034a8a10b0442d0181c0d00aa00104000c21001d400003880816550300d411720312034401d03901030201c550f03102c1c60b0030411160002190008640c8003640d01141a2071181040d10081c18918198500326041c038881c1c0d0003000c0d180d10040180d4242809c02140d90000603000624148134144401300c918000d84d8200e9444009000d182e10340c83c1e01200c41500203080c0c84101480d540361843c2c0011154018281910a0301032002041144440c5240d0003011600a001c1e2402040c1c41c0c10541d442e0340095010521929a42445054010140c41503d00c07218005080c50704080050f001e0240044000385110709002d01c011140071118820050054880c0c03182101c10b6441c0d2035841400199030300b50200b200d80c0c00d001e0051004540c2c070b02070540c07002d010502d01602c001e440a040040000310503801400241d2905440348 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 651812311 1250 651811061 651811073
    0xc0905030709360c121104050c070b01031a09070f090b06040510090602010e03090a090e010b0a0f0920190e0607081801080c0d02070f0c09050735040c0e04 68
    0x240c08280a0000c0c200150364441c54040c1110b95005d008102c9241003c064a2034a0294001d03604540329211003802e0840c150f4462800c00f4003a04140c42c035200d01084050101c0c1ca4201c4107600200e03407005440054500081c1c0600c4d1803050080e0300f54103031228410100d075140d0f002903c00824000300980303000801040041d088c40b000c2d0040030015401e1445034a6608000411900c00c1d41c800b91402c1881e506e0400404018201000641903554841c40426040ea0380c45001c50003400746080e9413a455460800d1400851700c98004070303200c0718820058501079541040130b54a110f0fa80810509803000c1408048134400318540725241e02440c00f080220074000c1410103806144070030b203465890180410010f44042030102e4044051882c104620005185e558001e8918036102e000715420402172a6500c0c0c00e410300366048030f4a456560002c2018040d030100800400030801c1c03107040000c914401c81c03c1c051103600409000702c22030840101e0200086240020020a01841c8010003410640340035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 651813561 1250 651812311 651812411
    0x7060b03010e0304260102040306051f0608041e020a051c02011107051f030f020409140609060a141507110114040513050705070f0809040c0905030709 66
    0x414001d6203059100051400000103ca0583d90007011301e5041c8120850030103090b0b90030302c601400382d54080c48000009106401a1805040c604201d001040320a03003a81200d52b1480d03020604201e018810f01c07010941c408551015000ba8040e0804500010b0000c1541510710703034041a04401d603250f0385071480c0d0012240040d17052003680e0385480000d12204240d543d052500039203034407407041410710004c4125420b820f03103000c0907418082a14140290160200d0700698030003e8041e44590710811244000800d040e8005c0044400e503120741450070100c0c0300030a00f0b004982c50060074505036035241c1d0703c40c141c41c0310f651005903000d65034005074038103c100581882c2019000c180c405401c00c840d51454015141a40d1011b0800301d05d02d004900b00001900020303000c5d800b44102080441c021600e004c0760220202e02405255548014101c2480f0482d81e1072002d280030050100c0c414402d03070b5004504081242c49203a40891101d10295040c080d040e1001300d59151244012088100c41c0c1604100e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 651814811 1250 651813561 651813581
    0x1206121f1103040804092313140114010521070909050d0f08190b21160501051c180b0a05010e0402310c17151e060702060706 55
    0x81c80144080207105616000030b85006041c1e40b010b0000340480030140d80281c5c021004102c07142085a0b06500a610400c01514072101d001030810104003400240752080030700c00c0419008111118000000c83e00180040c0101c41c4101b440d10350b11b28a080020000f64031711060202940c48079540c17000e81c24010584040c0488240c00b0b020015580c9a00a0603003c600d405692241001a910102e40e90403003c1c51072411008240c0d00d00d116025612070007a2501d07004902c1c0341c185c42a40083c03400a00d09811010007401301144a88240050390b40316041da2048a1220048030944d040da2903128043c2030111200c0201310001c00310441401103c0754814024403e50078104566600c94103203d030103840445000e50000c100288241c1e80c3d10640a10740c08014202b80f50401d9101c0e03405101c41501c0c0414030800000d08001d03402d04d682640c3c5e0840d1904640345e4420031040110300c0000c034100c0e42c1340c00a180e002e064510b12244807a2030308402c8500b0254011b1803542d5442191400c1030040002c01a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 651816061 1250 651814811 651814873
    0xa052119021f051b031b030306060a03051e040f030809160e090c06031906080a0f12021f1a03030301050307060f020c031006030303050a060302090a020a0c0816050609070605120612 79
    0x3402500c000d00841100d02271b1030040c2805181400119060b0060b04e000340041d40d481506403030810703020030300c1031199020724070805801c0001c40300c6003401090b01a0180c0300030700c2900502005082d29401041d50310881e2505502080c0c0fa64880041c2402c0c4030010502907000000001040104201c00c0b03111004141c004074100700543d11000102d98034481d5240003071508851100300d07808a01a0a00d907501c0c81032910448506011800302c051790710f104043d04100d0b11f500c0d5004486d00035603000790b128420805070000c41c1198540705c006540ea10b0284600c0090009040c003050480d4401d01c800d9807a501c010b0300b12038138240c0c5900c5503001802c40784001d0300000d1400700030800852860007404102c076001008084a030b05d48c088140c009504c00a0010140501c10304c611000843d0340000c1d1410b1404c4010701000c07071101d814000c0c10b014006100840a8200000c240860303a08641035450507000b199504150303907100c4010a20511085428078040d00c00c2610411001c120301140050410710350f0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 651817311 1250 651816061 651816097
    0x50106030c2403020405090c0f0903070603051b030609070f02070b03040318171c03020403060501120606061e030c0c0602030a0c030e0f06150a052119021f051b03 71
    0x10100f1000c03409030b1700802d83d10061030f07804260316940c1e2801a01d182d03038440b40c3d1285450701d00340002e031500b00d680d40b0a80c0400d4179101007003100c030203014004003441c1d0340404491661900b0400181c10350b0000b003002081c00707170450360740320300c5442045004003420700000803a58070300341400d014103041c00240403807512421002d404101d0000c514420701d500c0c2c0114000340078188088402d4020b4140c11340310501056070a110000c00319034180601402000b0241b00e03070075001c409062040a43d14070740c21060600090030b08500660100341240c036070008051800241035020340504030f69203c03021002030710b654004024030900503402da2104807040c85c1510100f08010804c016603880b0150404869015009000081e2191150032240008660003e00f26030800d51a02c001a82051514110301200b00d00501480c1026504211010200126807a00700c076226080d400100503070340010240664040c082a1a16140e0040003034460300c0d90b48062a0406811113140550f907a013100f40b9041040b00f40c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 651818561 1250 651817311 651817379
    0x4141903051b03010c0c030e0108180d05071202150109090807120203030a0b0a05060406030510030f05070617250c05030301080c0307150e1e0a032a150c050106030c 72
    0x6e10098260541d25460300d070409010711005484c1080001c105502c0302d4507041c055820b10340300340186e51110481c0d8848070b071112080e00b01122000420049402135520107101d000040900d58513060445a6002d404076a0500c0b900e0202d2031406480c0e401000428824180240c240c0c021029600c1a04c4006003000070007a5031040101e981201c0c801d2030b03085041084140001d5110f604016444068010399542c00395580d5a4040d25034006901a202a00910300078020b1941c05003000b0f401941301210114103080c100d00c42c8010740d80401c24900360600c1c0014041f400c901a2000603803264100003038034bc9a40c0d44e071003011740300c440c64490248203000d6203a0214038002d400703480002584a998076501c014548074240b018400901c808040f032500038130304041c078969401108502842c49000c10002d01c510481c0e801003a24403d0314180c400c1c02801005001a0060b10740024000da00b41c074005030040d9585c2000c0740186156080500a444845ca010030402061605585940f030348200b2101c090f400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 651819811 1250 651818561 651818567
    0x17160303060e070905221410030c2c1e0a060609060201050405030a0804020303071502040f0512300f0301060f0906090521060906180304141903051b03010c 68
    0x202e4042c0c13030f500054a0009201c1c0c1c4407030b00101c807824002c46c000090240103101d03640c4031402013112400031440d0851010703c01c011100030044018000d00c441c9103d00d282e50b40480100e882140011700d00c90085070009110405e68410920510060700343c281040d00301011080c0162110b03004c0c0e80041081d8080c00100030340705114082c4602c3e0808091400c06142c004100c40982e0041d20503a8184030901654010800400c11000c40302c20f88000140d640d80f900c26200d183c204583d00c1170f0f2140311126480603070228040790074412410094000c5c01c68a002c0c42c150790781e40444440c2004480e10102d00504181680c00045050b46d01c1c035282e80c500b0984100f02124041054010a00001c11001702007000303040801d0040c031342500a00d0400e680ca1045207485140142c112040c2074141d001c10b00384140d1810f00b1010107500481c0740d0155107054109151003001884c880c40642c0540c40c0203080ea107101c410058a580919884010f94080c100410701443c03c071109069442d100f075103030954540302c0c2c40c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 651821061 1250 651819811 651819827
    0x60b090109030f02010905030d081608070203031b0c010c0503010504060b0309031b01180f020a06030c0f0c0f32010b0f0402070609050d090e0c030903030417160303060e07 75
    0x9050351201886419a07903029019400490308a0500c5906100401e50396402c0c4120304190701380f43c0c0c45000603d4950b844c2c0340c800c00c1d850868020b0000d18030a0044c15076020013160b60103c00c012120740307840903000085003d84594020661103510303203094240e40507400002103048034030440b0700b8407046889030f180300c46920040d140006030381e200304a40c03041856242983c0c41001c0e011800001d1048940d4410b6003510a02c0d00200e0b0614007545903601180340400ba1803010707141c1d0f49002c00010070405805420090301d80340b86403e019010003440c0410488051520309194805255089003451403000340612080184100702000e140760002d51a560500c40c1035141440145440c0201000700203100c0254800c1070152501503d0308007401c04200100581d41180c04a07030749600c200f9203403402070030380018003070041c58600c6010014056074400c00000c8d25003154001710b210000209000c0306000621801d8024440307222115000018190103500060448016402c10305040e0340c2c1c51b4040358114 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 651822311 1250 651821061 651821077
    0xa030212010e06100c080706090f0212060c0a0c050a021305071214010303050708130f0501110f0717102c1c081008100218010809030d09170d060801060b 67
    0x70404800101c0c4a2041c0b05005d02d6501840c11075240500310b0f01c40100340c3d1111801902c503005842060411424001448001080180c003c0c0c03006003072440d5020305c2407280c0d011144c10483c0040803c0c040c40303418400022030943c001d168003107840303410503600007429044513081d01282542403421306402144c040d00009007142c00013111960300715602501c0542100c5000e40720400140003400c161402044464040d00546c0c600c0f26a9502e4580014017034100a42e1104e4203030045002050200320000d5600103445100300c440d46400e00d400300c218034068102483c00340060808801c030160401c0c0701c0f0014400040078007455250001162002e90f61350b0040705e480150304035282d42d00c40d41403081c1d901c03641003032020f600c011801e551b464801e0b1400303201c02d0398080946d03400140b0030403289101c2020300c0a500300b820089241d140200c83d00c0c0d1039018400a01045903110307010030003004100c0c0f000400300d410380000c01e622140c0100700500188070790f002c0c640a0790301c0d0100200f000c00108003550658 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 651823561 1250 651822311 651822319
    0x503040e0c04030203031204060501050607081b0c09010f030b0109050708070c080417011e2003040201020709060b09190803041e0f061106070f0c06020c0f030a030212010e06 76
    0xa4a000e5004002000c0200031814400c0d05000110050b82d00344020500b400c0c0d10003c2d10141c0c10981841c000b00e46041e40b000384102010007103400003845070015503040804400040c8001704000d040b00b8107005012074190390012040c40003080a0440494644c240d80c090352120340b41d80e0300c1e00300038001c032381c003c4e02d070b5601240c1900e0014440724880d40b40004090b20600e0080d04013560384404003a402c5100115217000d9440d00044039120304d0060030300e0294100b00406201c2d240da0103055071040b043c09890b40c0c40a8000100003020b59008101520003094071010400c400740c5c0e1094a82c15035007296900303078891013010213903500d1001c50410880503141604059860949440007200035540c1d080714800103110b05460000d0050740320103c0c0001000692101700c21504030002d500e0600c500148808140f2000075032180c0100d91041c0c41000f440d0388194010f80d00c1c512502918501050000c46485034480055010003c3e58581c0107021011104011b00c465a621000c0040040000301d60007500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 651824811 1250 651823561 651823567
    0x60c110406170615010e0f09060d14100e0106050924030604123b011106011e0e16080a0213060203180f030c06030c12041109090a03091412250806040503 67
    0x7c40d240c000340312500003500a01c2c5404000403903603103065040001c842c051580d080300c0707404000302c40c403401510001c074200d41c0200b02840c02c100c0061050200500a078640c0ba4190741028061041000c45281c010300050031070706039240500d8002d100c400d03c03254442c000384402c4543d0b6010302800380c00051950030b000f507042e519500c80340e10501d40001a44818100304052070364801c00305e0103000c410b01801101c44204207860307600819400d03201d80c03a8001c0304942c01d94420440c26030001d01801c03071018a40c1c5840c400585030204850003a01a1101c1180b231104031500002d1140d4002000b82800840c5080015020541070b04010315040800d44294044e00190028807807850494000d550000703540000504241c5514403400072504111412102c0e40110350742840b00303140454181d40d002103800001c1001c070117566402421034610f4400c032407581401004000103641c1c0c100070b1000084107030049980c441d030b0854180c2c41604407882c40301d02c00110500c0c049176100000c1465407046801c000250701d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 651826061 1250 651824811 651824839
    0x140309060a05060f06120718060e040c11010e280308010510050c1b1908190c0b130509010b09060712090b030103050105041b060c110406170615010e 65
    0x1c0a030a0040180d94084070b002e486507220307900e07400030b095100d680300c404200c94074203103802401070303e20300156404150b0210020059a940090360180710002a540030800a54820b0b0540b50f1040040d041800c550074100c02c40591240004c480070044248400c6d40c1c3c4203000b90541c20207110110901900254101c0014000c81c20426400080c2420be4903000d4582007204440500b44032107516074100e000c0c2e04501a01a03440d25070f55440c01d007941036400a5021340303020001a6a00b5402451080e401030031081758050250300c41c0c055000740700080599549010403203c0c480d10015501901d48038881c0d80c00042441c2c428502601d400650152410349001c0140d150182010507100c5100300b000418100404c0081000c00070303500030352090300007140380e007001d180c00b075080c0308a20380e904010f5035042e80411146130b200c0200121203800081c1c1000103100c007000304006d0700a139040035a40d1003000c10180300030800081c4291040f10304642918a81108000449204010400c0f0940c0111000c149030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 651827311 1250 651826061 651826081
    0xa0324110a030b0f030304061d011b0b04020307030605070c02040e010e0601120c05041d0606030105070f051b0601080d02190b040b07020a050109081305060903070b131a040614030906 80
    0x80300e0340000303083e400c003005002c0001b480c541c45a04030030001100740741a81441c44100086105078042400c4c00808039103100d5940984080302100a050010518003050564070113101c800b020b0358004806124074504120041e001e0034449074101d00641ca0311405522181c1d043c03041141130724208010304016440d04408110303541002070283d80c401c007455000a825502c0c0c1c4503880f9201003140d0400030f225400b098003420940b00406403170188c0d0400c410400c1c0300740e100d1182428240d8a05005441d821054601d02d1301c4c0341110400070146c801e0000200c0d00b0b28000680c00d440a8255003120503002c100d010303886001a4100000708503031003010114000403000d0340102d0313020340644100e5050001a407507550940d4984081958001c000103010140183e40481c0c15004e0b0609a0f4942d00d04281c540200356240141c1c4540b11a0036004910552044503254008005104d000d611075104500700c0b0340803000e90302c1446a907003c914849200e0f00d1864004068030f208800b010007902d04c640e1001c44035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 651828561 1250 651827311 651827321
    0xc180629040905100f05040e1e01020904051504111611010e180f0114011403040f050a0501060801291302090d0503120721090309050a0324110a03 64
    0x21200412080c4000320300341c0340d02e02c83d8620840d120280214003d150061500007a100b80c2c21160003241818100c032101c000002e030351500d070b0a4241c1404808008074a038140240610010258000d08003020b02a1004401050803a003907021942000780002d1b00510b02c0141c0328040c0107202400c1c080048030041003440e00d000f03a4082040c1840c2c4044940c0fa00000d09035450188180703401e942141c280000301c54603e40d0f19001d828800010034100182400191541554849200ac1e40ca03001000608129103281d04442e580d80c0401120b501c0d81036407820501801c040c2c0101c800c00d600e01303801c55846012103903803003a0820501d040d00f80d02c8148001880b03640329031a0402c002c410703020003184049884131010788801c18016005580c41d00b92002c0c00c030354280e502420b180f04111701200e92010032149408502003030a40802c00103070014035407a040d1038101d42c41d8403e0b40c0c01802c5240000c18012010703503480070f50804001202d008501010b10b50105d40300202c44400b0800300340100c0c0e40903030003a401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 651829811 1250 651828561 651828629
    0xa05100c0501332102040902040207060c050307020c09250201150f0501030509031e0a020a0b0406020c01050f040c09110f040b070c0617060906011101090c1806 70
    0x3160a0714440081c100003110b0b03010703c003900300740c488210802c99101c040710340240045289045448180002400d60948401d2001c0c3c4075a54030b45881c8115591035040b104000c0d0711034001e0000880d000d81c040c00d0340d041200c55002600400c0403080840c500840031740e01c510610354007089079080701301140360924400c0004800b990341e130300c1941034103041040107100140030b40d03c0025521410f0400040c152503000e0034003c0582c1c03040c000340200c41070070ba092407c9651156580c68440104080403850f01e00d40140103030102c03a54106000a02138a50002d005208641300284103c1d11040712003014090116006452841d40d00c6c4140901d20543c0c0001e04c8040d044004541808036180c80341c1c1c06a40964001000d40c200000c030342c0200064800400b0007070400c0d040c820082003041320300c2143d0400090141d446545001d0010300f41d07a008400c84001c0062900080040319550300e400200d8201b94010141c410041e8060a034400e02c0030b00440d01600c00303c0320405070050050708011091103190305 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 651831061 1250 651829811 651829813
    0x120310270915060e0601031512030e1f0309140604020d0b07020a0812010e06031209090c040e3d120309050909100b010e030c0d061b030b0f0a05100c05 66
    0x24840d4021060b6000c0d81c40a44101c982068050500c20005812104046035090701c41102010800c0107001d42034440c1c1426406003000561040d0510004108540c11188201541558100c1d040c0c190361551007020214855040d514092820f801059910300085030000e50001c0400102c0000545e5401d09580180c024011038074240c210340e80740b46040e04001100c03410040c480b8010440c1c0f4514400c0381382c003e6030a0f030140941c6100000301024620841070400e016044400102e40e0181c0e040c41160003d00c0350003c0d120050a00e070141141030041820541a01d10003d400b00a400d12010f010118a000f90410300f40254034016500b0b05d05000514242c0922007901c0d000256929440180780c42240000003a000030303140b220b000760848000d001c2060400038204c1115441d034a0014404103444411039400e07000b0044c17881c10300c01130003140c1c42e40c1080c042d00c503c0311451541c06400c00040c01108991415a0340302e000280000180301d8414168440080505a40420300500440c204680030324 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 651832311 1250 651831061 651831083
    0x9050109140f1f0c0213090b0a0c210b03150c040315020708030702032104020a06080916060215010914160302070807210201061a16051203102709 64
    0x3620700d02c10200e0500f856404035582d45071803011440c2140c404051201580020000c2c103002d0784510103890401046c0c49003040d61500d41081440c0180b48015400304012106002c210200d00c41201420385031104c1c03402071060044212522151007241403041c000b043c1458201031540d01c502a444015101c0b18032a15030802c10340000c50000e800a62250406400035070359518454070b0441c1c1c0524016003222500403c1080c031006035900d10a003011900d551501c005207486806609003050640b0095035030308040010009030083d00410b400e091030151034850016603a85d0000b070410355941210301880302c504400040e010000301c00940010b40050b15006003080c0c0c46588200484d4022101911440e4007464609580c070400c40031456910840d10081c011289000c00d00f882c01040080f40b0a00c020002c00c2c01800e000f03c01021440b90b0b42c1050031640003c1025124207901d61003500c9100428004103800301c0e840788500d03580080c00140905a02003890f6883c213210050072003240440d220703100c0c6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 651833561 1250 651832311 651832339
    0xc2a0e16022505060f0306090c030403021b0f092403160308161b14180a0c02100213050a0b07030509150d0c0e01080a06120f0602070c0e0709050109140f 67
    0x4080c1c0124003002400640da0b041540808c040707000300070326081c0013041c1082004000b0b6800b080494074589000391b42d48121050900060341e1040c111901d94009040c00708001c40740e581049060782207440040030407104007055050544400d002d0200c06000d0346195401c000094064008001400c0c51300303501400000260340e41e252507007900302000d1403601c15410511203041c4402480c00c91810460301c00c198203050742d4441d5004100184000d00c8269506e00c0b01c0d815500034000300a18100e0f4a004540d00c4180005074281d025190050601442603400e010808545600c21118680d07015117503036081940030800c00c040180c4400190f400e00c081880040c0d100b800d02e010701840b40d000ba03140c00391417481940005180382c1d40103104061a60503c1030800c00c584200f13048201458104026052100c0346080c11400383c441c080005095180240c000600c0d40d40c00c201030350056041b07a5441c1c500558550044401d0000b500174440300641d04402030705136142c484d503c4103010101030000d00481d681 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 651834811 1250 651833561 651833569
    0xc0f020309060c0712051f02181e040e0105041e230a060f090b060109050f13241503050c0f0901090504051006121103070c2a0e16022505 60
    0xc05d40448072540704614500034600f0741c810403204034081550450902d50744290b030084818030241031078010744d015400d0521841ca50055040445c4001d08103200700002c01e05501c0c004d18044806440c0641d00c10900550a540b90300c800c070007950010f41d00f001c164549801c410b00e25130030703040b10311040c482c80c0f4a0a000543d80d001384020b849507003000103628a02402c00c5810303000c004040a042001422040c080303039445c1c4c8620130740b0a90070380310244000d00c82d014aa0061065016690083c10760b40354000b9059202580001034ad080e40e05291200c01c401c01e029425241c00b61150100719000340500c1441020400142c41d00a00524091135a0781c2d0308d0b00850100c90741911002246855508148802034201b03c81c00b43e00307284034004100407220380304403043c00e01000e415842080030803c50752062000024a44000c0d80104003005880c1c259201520504005403086071038140c91000000c0008080300d0b26400b040110350058044400503925450100c2c9001d00350320180740c40c52002142d41c2e16 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 651836061 1250 651834811 651834839
    0x50906030921030712090203070605130e2503150614090405101a070b0109110c070803121f0303270e04110306190209040b120604060c0f020309060c07 66
    0x902030014643e00e080140d001040510503000060503141800480d00040c2c800040d084100c401c030741b43c06074442070010030031441d044069100d400c0fa007030200306011260b1030078001603089003100103621175a120310030800d6003540c0307182e40f404440e98000d04040141c0c0340103944148213403240d45a101d01d000c0040c00010200c500540350f01a494000701020b00c0070700c031441ea2240c0300f404507261050400130151303901104c1600501520714610344482d40e0b10518140f1906035244240c0083c2503400b01c1d500c4034003095880c0c0145010007902c0c01c443d00401c55002041450707600b5010401e00301c107a0941541c41c02d490300091003424110700b1303840b80e0158107a589100480009002040340714244c80c140b40c20100c2030b0501882070180310750401c0c41446244000c80305070f201843d50404016031a0000b07440060000c00002c100541c2000e80001e28820405010803803a214a00c203003801c124420102d40110740580303404040201580c01000788455901d03000021381106480340e000ca83e4040d48a010811041c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 651837311 1250 651836061 651836113
    0x215100306020d06031b030519200f06041e050d0210030b03030f040801090b0c12070c150507030f1401140f03010603050703140d020d0801140a05092403010c0509060309 74
    0x41b00c900414401c01109000240107500d40007441d4032400a103840b210f40402481007410100b06500b01120019240d0081010b107030300c0010461a1180d5a13042102980040803503514103e804c040d07000300d494030b40f02006600b00d0340c010b400c00a10260100b0103400034229180c07a17980c144014400b213403541c0c604500400103840120004a50150907280c5204c0058000c1c1c402102048140050b10134054680c12080d441100351402a440c0305050400450400c038020702c1d2480c45040c1410802100e825401104041140100410490340701400700c101b500400e0040c001e04200d00c0340b84422924040701d0505404800800025400380d0342d075507452510f100c5a000b2101038002c6006406214000e10240e5016071050014020201083c2c00c0149014130500805414011f20703038a1a0143d100e0b442d8007401f40c10702500c1803205080500c0c007514070f8001844940c0300387e500b08031850040d003410b000e080600303101911824100071105e010402c3c1c43c0c00007050600c192003200018200c0b0b1400001c032490603 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 651838561 1250 651837311 651837353
    0xc0d030618361707080316050d0c050a0e03070302062209020304111302040501020d0c060912121d03040524030411040b010e0d080a050417030405010215100306020d0603 74
    0x402c981c9010040b0390340040100300c05003420302081000c00e120400f2650301990941c80f101240103d080f0950752801780d0280784412501c1c002140e10400d400400800a02c1d286440d10001001c0c50300c00c0665170b80301e034000250811414011075589440800d0b0320b9001848a110800100d81c4070992107080341c0013203809a42c0000000c80200890814048c05502c0007c4468103500d0700781060000b030b640b02102e098000c1000145194002809420790212448070360288a41e82001e0010741c0c0202444a00385010b002103280074800c0b2a5400c402c04101c0b5030001c5100a1810546003104102038602c14003644944100301400341c034441950400190f01c100d12442e00d004441c0c01c1002030000f02d03884904081c0c103000c015034219402d5528500004551540501503e039903803103e0404551070b01031a0301c085181d004030104401c207200080b000c2c0099030310a03402c880c84c1c00d4100348150003002050303600c4030401c60014410300c04038440381c000301002d100d441d0340459000da1326514004d40710540402580d030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 651839811 1250 651838561 651838661
    0xa0309031b05223e1c0603020907090305060105060a09030804030503130509040206090f0111010e0703060510060f0309020a0e01090b03070b0307050a1101090212030c0d030618 77
    0x9022442030b40510a040c0510021001c5a00101c0081a4520404201001007640d02c0a01d1010350000c803203c0c00809485c25407400100d01840c1c001c0c00c1140002c911403091900007800030b61007070000404a0b40c000d801003201d64a00030510220703621656000e01000a1810b02101103906540140b0055108900859440d40e03035100c070950041c01134001c01d201e4401d0743c062001680e41e54082da018620101c0791030303881130603d00059840d581c248a441c42d00b940ac021010080760f40215482040303034015030003404280d0791904200405201030140c1c20100d05000f6400f81d07824801c2c0e0000c0f5181d4405092005213507140d0a00c4401d481d400d81c4400b405a44172401900c0500b418000c0340000c0c60303100d5505045042181010303109019a15400f41003000c80a84040020425041414042c0e005000d02c0548168842a0741d245c0c2d00030075424084e80300745030070003040703912a105110407540c0103040e40400816a141c2a40a0700236030b84c00c0d950592611102d051031503283d042400c1041041d41801e91 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 651841061 1250 651839811 651839869
    0x1011190507241d0414010906080c04020c0a030f0306080111030108011503080a031a04020c030310080d0e0108330a12020d0f03020709020c0705120a0309031b05 70
    0x1000300e15400744900d1880d100d48024070b0305604070310031840c403910408104581c3d00e000404100200515120719804240d10380001601030b03040da1100081c0c40c0c0a106031080b4002c00d1090000768803d211126411b9449190b181010911501c5400c8407811a072401083c0f03103540d0043d42d400c0d0354051100c4100f0711000401003084031000d1140c001580e50404030700c02d01c41e1464403064118000c000d8840145520784500040c0703030f060710010a240b00170050045480d0f10a40302400c1d540e4000b00c68441c040700320a000402c21117800030792140720f020f143d500d4100b6048524011215194082d04100c2c20a01c081c00803040c8040040d49011040000312000708110041030070440c0f60902c6c0d81c401c03234010075516250380150300e40c0e50081514580256040c0a0702d90b040c5000c0349481c01035440f107082a4400b05164812800100384203048030001ca07003010303500d409071484580b00e010111000b8041003000b50304100258078800c60800e01c1d0480851510516640d0b80401c04041401c000c00f554943e100034a0f003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 651842311 1250 651841061 651841079
    0xf030f0609150708042a050301090f02040e070b031f12050607091a0706151a040f140303161b09140a020a09060e0f060f0a03060902091011190507 64
    0x740c3c0100c5510340803000d0b0030240c0b01e007980102d1020300b0101c0344002e2001110307460342041e6068024403002d0020040708045003081c201781c504d0110202d02c0385050880c00711400900080400a44404400c01c1d45036484e004007071107598121400043c2210b422100008800a01d4280285c01500940c0502210710b0b10303c000810207585508003107040b150902a05900140d42000e4079801588103c000902882e2001001a0071031964002c4c0264000c0c0080080e004045001030011103401e00c0307600310300c141c541070f01d01d502c00c2c01c4260040e0964024885000354045c2c03140c44080311402582c104001200741241c0100c959560303084151200c2d15005000c40026900c2440c56120391415030460900d00f02c1000200700710354601c88c400800101d1070508080e13035503084000c01100301c000c010030351fa01d000001e00604da80241d03602c940801d01e0260009a440700c140201c5403203000040c844010400c40d1502034544d1540c051031100c2a01c0303a5903440c0c416030060400101418000c400030200749180c11015 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 651843561 1250 651842311 651842353
    0x9012711071b1203261014060708030c031509070309050c0f101214041208070206100b070507050904030804021f05040306110d09030e1306080307020f030f0609 70
    0x101c00c00c0c0c0d10030b81c20098012001408a901903243c07a00440342c03882d1202021031290f03c01041d0311000b600b9030030b0006510920b20043c04440603511800d915100300c07010000103029010300a070403550300704005104c0ca0703064801941d001c3c3c1c03081d902d064030110180100f0301c104021a5242d0200350b5444288081c400c01f000001c0c2c604108a130304100ca1031200002ca8511002000400301780309202c4142c07044030180350840007032941040a007239520310b01170130b003021103044582d2090082161140811003841c40801d000d4841e02050141a003a0b616112a00c1c41c4c80d03003c0c4006448a004651000c1046c1c0d4603805058080d43c0682d407507942e00d003014010480c284182c52005920b520700d01200003400340d086030543d000c0740c0c0c00030380010341408103114100c0c061040700103071460310340381c917280c4010144c02103401320680000387c40d0001040c00c110f1203107049441c20300442590358000d1158800510b010303154000700b0b6501906548840c9010396a06240c03a200340c807424259000304d01c00000e854010320700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 651844811 1250 651843561 651843593
    0x40305040614070f03050f041e030c0e0603061504020c1e010b100f0c02041e0c030b010c0812040501180b010303140316140c03070c0807050402090901271107 69
    0x82c1a15248003982c62040c1c0c503110b0000101440804240118005000402d450050125209140e0300c007490f462589003802007400110b455440c3c00e540491480440d020700c038890900500144207688038100001003140034a0592544240c0801015010318810301c8444002c015800882da0401741180b0090b00f9200010905401520612492018994402c8548491030200d0824804c0f08015002003405031982e004000c01e080c4181e500d4441c5401c0315440b030340ea4014a81c5c0c0c1000042c0301c07000110b400040c00300c00a022510140305110014961011180e0004c1c825000060b082c0103425111140c040c030320a082d40d44002013001081450342008141d0280d482101c5110310358a0180d80e14a5000901c1e2b0f003a40422900a41316801c1c0500c0c00200c03050b030365846003100d880c1d0195240012158045c0e0103105298003811800290703605007070007519148a0010046c41d0940e081c01081124004210081d02c8000c0039006921052a4244110038458000b03a1030559039040b03c0c1012507a031540d102c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 651846061 1250 651844811 651844847
    0x2d070b0901090608060a0b07150f050712050a06080115080d0f17072313050306070212030a090c0b0304020f090108062205010e01060303020f03040806060f13050403050406 75
    0x4403039860303074000342100580b003090422001d991282c00c0819408041600030405801001610005110f031026039054030320982c407001d004020030f0301b511070b043d944141c40050206002030303d290000541c50308542c1d80001c040000140c440c0d5034442075070030348480b035401b1908d20305a1401813151600501c08028035500a00f06a00c01510003600146054030040e034010180480c100071683c500e200e00219a00310312001e0680c00440b10343c0b002d4540c9070b441032541c598903225040c00000c4900740821000d1007102140c010b02215004540f1001c2294002440241681d17641c529140000714007012001c05080c044a1050b200d180c18814801c24424441c0c200f44100344a03401049415000039040340d1000d80340000c0c10b0b105091948055480e4240f220080041d420702c0083c0001e404154440004c41b800380c3e0844070388103a5a039a07981c480c819401203100380d40000340091001d0503c610751400f101d101900c0400440c0c2d1000c407440848400b13840880000704000b0301040081c1e4845494907815008417 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 651847311 1250 651846061 651846067
    0xc0e040c08010203060906120f010c050301140103050112030c0219032d24020d0603080304050d110d1b050a03021507020c06070b060402040305030c071505030f060d052d070b 76
    0x41d06690010601f5104502c0f0700c54000e07914a0603c44126061000c200901150007007620281081d002400b8104400b071080203d0845984a07026850480304005404280c0e511280c03030889146100c010184d0b0130200748203180a00d40f4009c41c0f205c1c000c0d40074140c5c8218500740e07484859015451802d058502c14441301d041000703d455044800d604c00c81c002050403102c209200703410080e028032501c0c444c0c0c2a141070300c00420f20041d0310003580b10314851030660b4450300c0e041c20141d40304900429440d49683c01001021130982c020f1140d11140031105440c40c40c1d5540c241d9440d441d01040301d000f2401a00002c0031505c061660250864001c05030340050030501e01d140d80459810300a01c072002d4840c00d0444d0101d18282c0790b0340d040740c010b541c0180c01d40e955440a41d402c180d551805115050583c0c0c0c041c4890304965100d501982e000d195455040c1d103241c0c643c40c08000d0251a07100003562940100644403907404a600c181ba05030070390302503448440c101d814201a003000115804007103880010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 651848561 1250 651847311 651847321
    0xc03050709050a05070323071b0818150d0f0902281413050c0405101e051305061b0d27060905010c060b060a0503060f0f0901150201090c0e040c08010203 67
    0x50040b044c801082c01c80070755403844111200c2207070710040c044442c0e6924043c0c06005004006140f00703016500c20a00bd1100c180520052101054015030040010300504c03044110581100c1000b81d220140422103c0032078000814041d90b0516007211206a000c0d000130061450640c80c0040001c03111041c00750038040086a0b64030094941c0c86043d0351f0b1100000c0b02d4844010944015040142c0010b9049914601c05003554082603030f0440c0c00b00c0c5240501000710f20910071101d205207a03040d00c500303003460041400750b00d0300321390102c451810901203810000741c0b08020301030703451482d071b5107583c6003601c42402d00621192551018545148808050200b01d40285209040316002e00e0840ca402c003840c00c10030300604001d0b41c9103030b02c4000040d02c10107055210024601a40b800c55241c040b84d1001000c0151b00700c14150f41030b40000d0543d00402c0b400302d030400c4014001e1013074000070407070b004030383d035000c00410582c1c000f006d480c820f200a00c03042c0800205500302030010b002c021880c0d0700300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 651849811 1250 651848561 651848591
    0xf010303020c060903070b0a0503010e01080a08070830100602150105150d06090515010c03080109111308060a0b06030108061b040e0f1503010207080f070c03050709050a050703 77
    0x2042e40b070540603c0d0002030342c2d401a10100700381c0005240e07e40f120350302d1382000c1d60010060350080c410300089800f89400030600410114003401c07115400b1031035514016450b41d0300403250304500300c0852401e290745c50008008000c3c074030043d4800601c1440540c1842d00c2c064002e1214126040f0000312f511640704c000c44818601314813819100101c4a0400411081c105030185200e1111500c1115050142c000f94801617074001c0c078081d88844180075521907582004503141c00d06010702600140007400100b040800300d920151940d2842d100c0b0901d000d81c0200003495000d025030000311280d0201c410003078501807620801c90000011100ba03072541d4074240107203a032140098803450000003c0100c21180e815003204030740003030071481d441c40640e21f841d0400c107841410072034080290b000d40d1620588240703018402c8401c82d6611042150030305081a49c07917011500041021943c00000050210200e2001c0103d00c0c0201404000815680b400001d0303002928005070a0806041c00c1034200b041002d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 651851061 1250 651849811 651849823
    0xf0c090503010e0a150b060714030d050c0a080f0916170c0402070c0b03070c020d200402030c0f070501021608030709050a030f030e030114090724020d0507030918090501050f01030302 80
    0x81004010904911b07010000d034030f51241c00c5004140f078541030030507100120b020025180c500c000b010f08007c1c03a9503a00e000351203031068018550000340e00c0d90000d00e42d010422019500b02e500f0004640703030070701c4800794240c101c41300350402c03141082617026942c00020308119120312540240d03000e6007013541680d160303a541ca0781c0e4058149196408000114170600c6485c84501c000d40003802a52080306c10b003064280c02908001b060810349030400003aa641c14176001b10b07800780d907804002364a48180302c20084000e4101000448095400704500707a40c40c3c420301c200d80e101ca4010a842d51360b1f4100303044040c1041c142c1c2e600450040000e01c1d0208045100e603005500c580d0b0b0182459802d1200e504002401013150b103030203140304c007009014411920000182c000c1a225003511000c440310241c11741d03807040605c0082c0040142c0c8800c416040072840791018110a5100381007422242e61168a186107d251600c41000e1540ea42c85000080c804240074040d04204043e40c01c2045504640380207407210 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 651852311 1250 651851061 651851093
    0x1b0309031309151a0d1416021c0f020c10020708060a1a0108060607120e03100509060412020a30210218090c070b010503120405130f0c090503010e0a 65
    0x103c00040c1000c5414440d04884c0080c4405c2c0d01045561104c42e1300c4401307002c091750084001506841c0b0035070f0542c00001c08500c0490381e840441c51101c904181150f100400c60816400c5001c0d0754200e19668031003a11107090800c1c07a401509540d41024626440d0610081400c0c90003401c10f83c0b003203038032a03100e41c10103661003081c42c00e24495075a11010481a00c0b0707203000209110100145030050603804030784030340e0f003a200701c041d0703201d0401ca80311341410707184242c0d0401942d0b0000d0b00850f0005122030201c80400c4424010303100040d81940f04c4840e420385810030f80c0194000d184241180b140000300c6094200201d00b032500204100c0d0103045d01c160700e05140070000e02c3e030010701009507021070501401075a4000b403d8801c40e1502c8106004940c00105007103440d25616800800c140c54081400010030b07014400a43c145842d000400c00780081c9010841300c17036a41e5980486442c078090282c8000c0d001c2544403c0c075014500f41c2410300f15041440703d10400e41004500d0000503140c0320100e45c4203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 651853561 1250 651852311 651852329
    0x6130807080906040b071a1f05060d09050d110712032705032401080606090a0f18111e06090415120f0501060b03070e04051b030903130915 61
    0x60b052840454030600c40d03900802c6100d500401c81001308019600e82e24000100c2c06400c3c015a11071034158071603080810b5005160314603014043c041c40c284080a0850444640004a0240c003184c840900708003550760a200060241004010460420400100102551603c0044040306c80e18003c103481e904804416054086001800016001d0b981c2c886c0034080003416602055181000100d1010503014880c51a01e910300001a0380503000c604240b081c1d8005d04680204d81e109640140140401604881100d82d00c440d00c00c010001011500c00d01403150442e207a400782450308008100c994100b142d40305c008601c000000a4840c54242c8501d202c0c00c1d280841e40c00012450400b481c5071a80044103000e405841d043c1c14004020a04900e460065008000c00f948405425595100c121052404105ea81200d10400e04017540318940c00300c40d5911403101071042d01070a004030b5009407020105a400070400d800c40c0705480070810014005040200604038005180d290603860500c146444 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 651854811 1250 651853561 651853567
    0x318030903020f210708070b090f060318030a11060a0c0906050d020403051005011712070b0408070c090b1008100308070c1502031314130b1203070807050613080708 72
    0x40c03529042c0300300c4a204200e400c0d04e02d000c000000d6060342c6240c0d610584800e48100b410019529000c84115403030403401400d05482000c0031800e00040d85e2028144100c21108000c91015082c1c0601c0500440f801d203030703990055440040c591794505000030341000041072030020031b9551242c004003180c0880c2d00c41e040482c1ca0780035002c5000001d02459001030543e0041307812180d203004066100b10705075840c01103405907041240308143c1d9141c0c400307201e44590020800030710010030942e150b445d40c094464138810346040e072265162031444500c0d41c000317103103142c4817880514107181c80200780c0045034107072410b01d40c0c510b0b00d40101c061a803900d11010b00109000a498014003d0013a8914042d01a08a1801c0ea55010745c00003541c0340d0102178540d034014844c500c049164000070503a01400c9038000d0920303455060004000303005240d00030400340c2c0511030240071030701d18000380040c0c13510718001c240d15525020903040240c180741d03009007002400b4006950002c0064840c00c01c5e2200d20b500305000c0c0d51 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 651856061 1250 651854811 651854839
    0x9180a09050115050a060f021b0a0302120d0e03010e100906020c0f0a0c06050306032a13020702031006050603040303020a0306051c030306091a040b061315031803090302 74
    0x800e90300401030304950030242a4001ca440c1d54a035002100c078242c0c1c505000c00c0c1c0c0d60074100d0b809503d200c17820005801201081948100c0d4491020341014000d0808000654a40c0060039596040c2030140c8a5040134290240303054001900180d41c40054000b84154074100f03d0281c1c80b40e00c0d1450b8a5141507513a40b00c401800b4450381692024224001101c0c2c01698010035030f41da0300e100190846001c07800010110720184603d00b664000c101c042c0c000c10694400340c0303514030403103040380d04d001801400703412240c02c5959042d19400303241c440b0b160050b41d0700d03c207005050a01c11405160508607041c050104005d407204800c0742c1e84150189401601d80380d55250441c0a00f019900059010410200c000500001c0f070b039a11f50300d140f007610100400f5548103200000c0d80c1200c0840011040c40c048003846a00740398101e4030307106000900f054035210b0720b0a5218002c5401c1d41003404084c89102c100c100041d054481d0001d0394580b80c50034610324015940051061410303000007801342c4036200c40c1003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 651857311 1250 651856061 651856081
    0x9140603100b0f031f0f1521020c010b0603010807050d05011e0507030e0d090b07060609090501020a0801081207061a030609010b04060506090a0e090f01181101050918 73
    0x180982000b0040355a01d02401c04070303080307581065841140c41010603c107240d80151010102e411283d0700d0348028207141c036103901400e0440c0705154007428440500d0882e08800000d081d000c0c40c80502c02c2c001603c547c1d410140c0f60841d07000c0040c040c0944010801400529000525181140c400302c40150760740e8042d207000c030b014141030040c14a0700094805009e811540382d802940c410411550304100450880040759910307800000d108002c80e484a02c20b00000d078400d4000e1003c1400b0b000041212541e541441e404c8038250903041d14030717950200b00ca015950380304000034010044400144051228090580d41c1c500c0b52110081c0300d242e0310001030380c0010200950a40c2c400b4002c0035031340180b07802004180642644120148141c0c908200440c06c3d180a03416a45900b0b005480c01c03921909029410f0a0494003500090080c031400d02034454050003409800d07107100d13086910f0710001e9410320b00720040300007105c10241880420f101581c0f031521401400b011360b1401400d0300b2030340e4031002119 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 651858561 1250 651857311 651857341
    0x2c0f0a1a0702070806010f03020915010c030e1810030c060203120c1b100e010e031e071106220509010315092901140910270e011a0109140603 62
    0x413055030300448000285424600c1c00100c1117a00130390382c1407296600c6600c01c004500000401e11302280200c50f50700040fa2140e251064140006042009040007070804040b12844c02c4035401e0310b4031145501401082003508048006100d540001c500b4900300040a01c12204010011414500081000145004400507500794101504150751203012502c3d00030001c2c0030300c54840d14807582005850f50a504c2c0020441e1441c1c0740302c9140e0041280b881034001c42541c02400c00303441c0715a03440d442406542e1003d00810889080b0008200000c018410b0181c4011003035221600c11305203000100086802007450b1130301c3c0f035000306000900003203a180a003224602200304501c1e0305240c5003003654000d80b46035040e0503241d9070713031f0071140d105030402c10400b4618049800400e81029008100010500382180c181c2c901a4122240c1c007000025440030301b00c5481d01c0d403050b03441c0c2d1181d001c01402c0c201450208054482842d00743c1c003030750608800c54648240341e00d0690003a00000f0014410704000010307 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 651859811 1250 651858561 651858569
    0x50f0c0c100c0509031209031b032e0501050103090b070c050708030406020f070b0310031202010e06070818071511100903020304030c1d0705030a2c0f0a1a070207 71
    0x400100b80b64500041c825003000384410302078454190060040e01c16001990300080d0014010301e2114000100c040c00d01d0540b51003075805128040e10103041c1c0202000340d81c000c00a41c0004800040c81e070b6040d100342d03030301030b0f1007541031528040055010500907141a80d01c001c2d41e0610001d41806450020310f450141e912600d064000440c0114074280d01294031407410071404101d0715880e032644541200c81c8010ba0700030400d51002d09082000840d14865040040c03c81d000000300140001b9885003841c200303d5840c00010f02130402c02c00000300f003070a241d00d03840910700100f26180c200395051191821144001c4148800d0b1344065031310207020003000801800852041c46080103516002e9502d801c00e001c21964590800b5000ca0700c3d4480003054407040e402481605015180e40724152607d80c8003500000489072944204c4809480d494156003130301c1221852551070b6000007034082c0c1449544550901e070381d004026581d02007414035820926a42c15001994010b072a0080180e1924040b944 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 651861061 1250 651859811 651859843
    0x37030207050a0b2a0f1e0c01150e090105070c08220e010312110c0d020409061509060603090206190c02121f06030b040b06040608100e0c0103050f0c0c 66
    0x104081c3d005452035114003054504c20f15400b44032079009540072070150914070a40f04006115040300e045144030640b845540788400c81e450071660702000c9080d0341065a40700c081507101d01c400c002c9401c000a0455120400e400200b00c0c604001d0703401424601181d40c05408a00c012803260240c01d90741401d10303e40c0b074103000c20081c1c1540d1800d84055111091005940e4440540301b034010300d0b4000d442440c20a021034004d440810151010454441a007482c140d8101c0d40c0e400403d40020103a02c10714100368001c9006e0140e05252050a0342030700c07440e4000c0300c101403c0c03190840060f255002903840507446816014012007031180100c80e41d44020401035803000030240c1c54140c4040208031040b0803403440010308804501108120142e601d14030000b8a0712003100000382c04540000d4140350424002000071502d1540c4050300ba19003201a2a0b0407052542c03900c03c2d40b540e043c104140c042401c42824140854a004040710b0b0030310b50020040140608d0025024000d04c50600c9246540c016000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 651862311 1250 651861061 651861083
    0x5130504080910030911030c0105030103140106090204180b03030a1b020f090c030f010b07170a02010e01020408030a09120209010b0703111005061216170a0606030837030207050a 78
    0x40000d000e03203898603040c0c4600c60070a4406c503440c00d010401106c0c105043c6c44a41c6980d10b550b440c18030301b05507040c264940d956100c5c030116074401c031030004000070001407411441c0155071110120481e40c05044241c0b20307078010070175080e8164100d0322400d40002003140d0141c0c08569400807401c150200e141050b0308c055110f040004051000d0041d40c01050070f42e202031016070b26000402e10310301c0340e41000740c10300c0c400c41c65040809150200500c2500b046100124408c0c03d29550503099800c1600401c20680010501e0348081d54044c1d1084014582032140900050346038010400c204418083d402c100c4c4000200c0100b418090182814500940300c1160001c402c5100f03014000c2c40260781886c03203121181580c2009040001d550f84ea91084203505c0d4030040e01e8040640c0001c3c61200001496015449170305c00401c00b584690b100450250818070b55801381026204407403008000040013140c48040700d0800300d195007000480380e6680d0b050040c0d860385141481442d082090400420145101c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 651863561 1250 651862311 651862339
    0xf15040c110a060603231504060e07182901080921070c150206061905090f010f0803040312140415020106030611272d0f010504051305040809 62
    0x2940c8010120382c007801b02d030352180c2c00081e21080744c0c007448040d0380301d00d40c094010095060344846ca02d5400504c0f8540c002913200c45034040a040c03c0142e4098440310030b8034000040c3e20b6a050040813542c80e038090a0300e14041100c10101840340c2411a0b185c1000381140015807903020821002090001612102e00810403030640616564000d603001c0310489218400002c08100103003909889208903005080d095441074181b00003207020201c040841c498501c00010740c0d40700c60b0b2040d0300600c22008034818070b604022490100c0074080d40486031070b0b0300800c4200040344003e21013001c1000c092a0071885007414003c00c840d28000c41d0420b011440f00c1030300f40c10314150154400c8007100e03c211018002007290151600c5240240c8422042814490200310120030f40e00002c46a664402019103200c0b00c0070740c0c182c813509032800b520544c04246080f0444138628100c0e105030243d54003440c11600d0181420041041200d1001c07403402c0f020f803100c0100d003c100d070b43c0068030680440641100c401d0104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 651864811 1250 651863561 651863573
    0x161a04080406030c05070f060b04110d0605091003080304060b010210021602190b0a0c06021201080f060c1c02030406060315060e09010209010203032202030a1a0f15040c110a 76
    0x64801c0801184c0342040d107280b110302450030303503605940102844c05000420f40340d0304050580410b80e10380c080d6440501d80340901225000d010040c0c1c5403840000c0c0035003483c0c140007428a0140c0a2202c400f16410f08100145046089a034070680c0460081017414105d40180c2c600a8001c003241103076800803800552054141805800300f45c002c039061b11060000711003580482020f8000c02c1080031040007181c8000d4020801c1814003886070700010701d09480680da6040000003038010120030741201042d601039050800000350811101c0e8800c9142003020100079101ca04900e561014035a004000502800781c203510000045800c21442e840e81036201910000401a5005000d40601d880e40031a03000c43c414801e941414006030002c510703603207960a20410404400701c000600a083e113007600c0060318103102590b415407060011805000841905103180c0320010b1800d0f46602400042000d0350810381c56514080000b560006100c9103070640413503408034070f01c04032079046c0710381410321041100e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 651866061 1250 651864811 651864817
    0x18030601121b151119060608070905070203030402010c26031b040f09021c060b0306090c0702010c0809010c0c0f080f06161d03100e0f07030305161a0408 67
    0x2218591610490b620001805003000c0d0500440c14200303040a100300b8100d002d0101c80c9480e624403030803105142c01d0400314450b0070040e4101240d0007078440380c00304101c3e07408100420140480364014051840c02c1d400c000d5481c000180082d0400242e1002d80062102c00326590070001c0041812003410400d11541513410340c025940a0b030120b003070b02148500310200d20192001d403030f82440c21400162401d01c0960181d0007030071050032004002c40310480c9400192107518000c06c0381051003500e914180d01004a8580d0040c94648641da080011900513a40b1000401c0ba1a50009116441c0e00060004031a025461000200710143c091030218a00000000f0041103843c00811100360402105420b9241c030b00554103846604400c41d81c0d0010f150050580d1643c0c1502413480040c0082c1001c0080e01d4203104100b026006541e40030511005041800b040c0c3e205651240104040c41c59950004c1181c4140440d11014002030f061030400c00488000341aa1401c04030110301c0282800c1c10000003c0e4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 651867311 1250 651866061 651866063
    0x906031302030a03110609071220100c110a0e0f041506060801030209090102190c05240f06060c031c0e01050117011407080103020111010e0303131707171803060112 72
    0x441406c0c00a44800b800091003000d48006001784624007000e50384a1001348a407003211081030701a006c0c48504d544039080601b8510080b41c1d14203a504110b8144402c1c034019450185000d040352800034486103090140c100d030080524a280742c11a61340d17003070600802c044c1c0340000d080b250819200140c559031010307410b41a280201c03080300312600e0b008402e508078894582084c12403003003002040541030051000021032130095013514400d20b90700c010313000c05407070070b41d40c00c3c070b04800d61403e1040440c0c0075508240d000c403041d40d8444c900403482ca015a5a40101c90803450303240d030410301003c1e900c030607600f04843d0403024030028044e43d40c42d1000411420503c101684042d031a204000e084a90400c01d110700540081c2c403031040030390840c4c00446003200c0c00c030007070f564a6485600c149042c5008100662040c0601e00700503080b2051460306011481222120070b408110034000b00c4081480c0017160540d00303100e19a00f1303984424101c00302c0862100924103950500801000003034005240c0b030410415 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 651868561 1250 651867311 651867313
    0xf080f06090109030207060f022b030c0c08180a0306090303050402120102070309031218060e1804020a050603091204090207061407020a230a05010c03150b0906031302030a0311 77
    0x15a44201c00542210200400500180c0c0401010007a41e030064900711640006413041e2a600312114200d58000c04c040700c0b1059139500d14200c04400c007945440340d214036060a18044140400544500c2e416000d400c58031903072141005a000744580c0e07403040400055038003000034040540c25040141c000c007402c4600340d010700d4000001c901c0c0760074188203c614240e8180c0790040340074211340701c080a4072040400d10040c00741d100c40000510b0520007084005102c150784003a48401d480c0c0c01e204241c82450202030760740200e141030000603981c1c0100c12041e642c096820307684940e06c0c50761041c50100c8500c0c20980300c4200140c0400c4420140d0020300710240951800d00002110a058003003202c011203003080180c121454500020f50382503018003402e0200802110480e00c40c01d84e41d030604d02c2c260402c45280e0354a4921120060701402401800642c888480b46418649943c55546200d0145642d1140c01c0020000c0d09519441c40001c0440750003074122101ca0081c2d2a000c6d0402c0c80c61480200703a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 651869811 1250 651868561 651868573
    0xe030a050f010c1107090b0414090c1908070e090a021807030524040b0f03010617060901020c0a030c080d0903030b09010b03150409230604030318021005070201090f080f 74
    0x10590081c44c0c2003c001200400801106103440c00382001004450b064650084c2c03503549444443c07040449850103a0444000340075411003000c1004411564030303486052112a91804004d2400e0105101c1e040703a411381c0c12020ba40d034403160050300b0054004c6000750710109800e0745488103031181104e10300c0f59000c1e44007003200d900d540c49000280e607010454804038851380d02120403107040540114114101c05414048040c502c240000c0c25121f0942001042c3c00c03984a44008940040041d1074001034400000c61909140c03200064541503071050103024400880b100004011020f82154111300b5002405c005501092400070050b0902d906881c2c80396803080c00210b82c103818403084074020070149089142c401c40a00501c009001611030580f000e0180a200c8030070004105007210300c0e4503c1c40b010300f00070300e042c1c54040d041340c8811401172008a40c2d00e0452005032074a20403602c20003e60b080440d16030b681e920041b0360045c0d07030f40c00c5400c030100383d0400016030b100c0c00910300382610031050903600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 651871061 1250 651869811 651869831
    0x1a041e0510030b0c07170c010b01121427010c0914010305160315030f05060f100b0901031a03010e010c1d06040b0a021002120411030c01021b010e030a050f01 69
    0x40316090700d0201400402441000c2404603c40a00030100d4900c035008001c003403207400f5030229464008000403c2103945952903e085580c0c0908140441c4511420410041040344000c2d140d0003001850365498660342440040d120351200360f03c0b4000342d1450002d01007003140d100010041d1590b40b20b00c2d00d40599064029000358004e00036140301c0c0b40a9013050040344040034044019203826941245070307225544011000c44c4141400b50207860090000b4401810890505c01d14284020500d40031034400500030f005091405045429044003407801050070100001403682e00c0711039541540e8190300e045919081510190402240c4140580301e8074142d4100c015610810607940400766031020040200703000014003440a00040c20440c411034040c800440c11401c100d9104503016003903054500100402c1180600150300b403035600781e0107081c01c4494800040d680d0030320030030120507081015500c001d50340d04c40d0a410796100001070441d4001000c508150762140f00c0c02c03540c00c2d80c65003404034101d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 651872311 1250 651871061 651871081
    0x613090605090105032e020408010603050a0201090f14150409091a093f070807050606060406080a0c021c0c1101030e0d030203040f1a1005011b061a041e05 68
    0x6051b69021004c030036a4007013a03803040c0c0800c0100c4000c1d008225800e201c082442c2e00e0034803c0201940c4580000c1c044d14034203000151950885622005524002d1071041c04030f000c1c1c6001e115014034003901c8030714003a88080c800407228019500f041d00580e150240080500c140d24003001414001d840014186854030104292241c950700c0b8461061090f6260440f40c21211101c2111415201480740002500c03200106a2980c85240180c8841c0008107030740f01444807e009903a00030390101c561500e86494250007414031100104074511555070f443ca006a030b14001d0004040d80c500a10741d0380e0001100000c090302c1c00c1c501d0041030702c41c4080c46508800c1940a442200c22141c5031030f000b02000b420f8000210003030761001380202c40509001142c0c00c005001c0c2000d0300d10a1421030a4600646842d8028116000b0303a1703032215042004801910381d803188000301c1c0600858000d04042482642030044074454000b50802541013440c204001c140140611400fa4908014920074085a02c5a92040c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 651873561 1250 651872311 651872323
    0x1a150109050a0311210706030b06070b0103081e160b2a130803040f0602101401090902040e330403050f090f120607260a0506061309060509010503 64
    0x4607070007403581c12080c0049040e003126915001350040607a1320044812941012403401c3c00540d95907584201000d01803681c00d80110303007200c282540d03042d007010345680b200041d154040c40040c1000e000041d8880034000180c4e52103a02404d00300c101035035001240f40381090b030610440f00342d8540100d40701003880300386c03180400000d4071030f00c3d800c2450040380850180141e5008080340611507640b120b001400480070b01c003800007004040c5020096520300301e006401c0c903070fa07285503040c41ca290003522020848c5c0c803607102e0f05540054030f00003800e8165201140007020a40c411003141d1040680e50358150010740042c118440030f4518841e03284128070648005a0015100240481c0082c007500035101c21840107881c0b501d500601e03510140380d25401040f0f0038080918288026000f2104205049800100740c00040180d4080c02220341d503401d00800c42d84030302030280301403151140c01003405952400141c4010240c3d8030710540c030440d5540c1503c402400c3c0713445001d001c0c0854400004a500d404695 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 651874811 1250 651873561 651873569
    0xf10050402040e2824060f1d0a030f06091b03080706020306150c01090311070602120a021516020c010503130605070207120804050415050102030d0c05071a150109 71
    0x4004080d00c8204070704000000585582002d0113114100480c1600d5901a80f690a10340321100010140914110210440180c1014061240c1c07240140f44043c1e1240c500c203402807001c020405100030040c0085c1820149034006031182d4103042a28041c0121a84907000ca240300701410080c0d00c0300710151003500503c0d0300c800707030040070244030100100c2d081c0c1c0c0042d503002400500c40c28903200740c4200e1460035004914095156035403829200c1c10107811842101d064400300740141681c92400d00002e43d1070340c0c0c00e003002010141c04100c0400c010b00030045031401219030101c2041501e84040d108441042c0b50420400500c02d46003001726550103581280c0c0618441c07550500a40c1140d110003003d0700000e0030603011841039078000510406034450807035031184906501a5034903e840100400e80703180c4e00c09000c071020303450700070003c503a0000115803c00f0300840c004111804139110a84150052500c0580184c00f004454030b05d4021055210b480f514104041c1c0005280c48070044820f01040d010f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 651876061 1250 651874811 651874829
    0x230315030a030f0509031002030103140f060c1b01020409020a05120a020f030112030c1217100b040e1f030809010807110606010509031c0e031c020d0f03140f1005040204 74
    0x80c0f007851661041000b85507000000d170484012103410072a80080760b009900940700b22110035801c0c412603001340f045050304082080100345030305000750210000c0c030030b42440940c001414240c101700c408080d0140e0b001030251040442d2560904035000c0c0c07103075100b24140d240900c00c000020340039018501c00e59490111480c00c55007940e0030b180b0810094a86038806034241724802041100103140540362117002038041d5603400c903590f0002c03054401020094602c0c0030f0360b015203206010001000050710204c4100d00d4043d501515080107035180c0f83c1c40b00b00c904840802155001c030a00944070300038a4680720a036241409982c0b001001c0310300310000650880e0342d40124002c02e039a984124054001c42c40c0080036101c81c003c2800310204003000f071060080128860020f00c59151078180003413270656003480b031f5541d81032a00520003034640c4d0300281000140020841c00b421a18802c1d4048403482342075900f800303490b00b4030001d840482c031011100c3d10904800d149012410703040034000e58003211130a00c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 651877311 1250 651876061 651876077
    0xa030302090f0918010e0303090d0e0d0f050307030e0306190b060f0315090c0a1b030c050604050c031e03030a05071b3f0807230315030a03 61
    0x154048000c0d50080301c409a0010b1080c038a4440c582d01c0081e258000d48440c000c140c55484166965400c0d86c40c101d044c960a43c00610030490040c0011030105030700d00d01c5103002c00c005c03104100014800c01e400301015000c401d000b151030302000000030040c6945406a290030f101601443d08040e40c40d00102d40c0381c0d4040807002009030500c00070303801141d07014000a2949003041d06441c0008141e4008075500c4408002954015619062408101e5000589007100d245001d60075240035004402c00d22204417031000d0328541c901414810740c1680d0980b507000303054030050304050078600e60301c0c00001901032080c02070b9044189804064081e03403031070f011400095400c51340c0380007030359000b4903009000105002c2d130010800b480d07a074038411010f01c852060143c07081d4a01030003090b455031316100b902c8014030802103210700300c420074860070094910300381d292003036103582d031203d0449219840d2702414940060401d06041c00d207280300d000d54858142803c11043d900000c03c10150b40f1882040c001d0046039880e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 651878561 1250 651877311 651877313
    0x605030910050105030307031817011a010504061d060d0903050d0501060906092310050a030b04050606090433080c0604060f050c01110301030308010e0a0501061e0306080f0d1e020a 79
    0x241c035880b90407040f500c102c1c0d0270745a81c80c01c92403090600c010300b925459660f050b244500c1c3c0394041101800d040207181440c24142401c4c0090030380524120000d0004218514120655845500311052112540d505120440e45460054081d81140146503556820b140010a8881c0700d00a5482290f020707030784404960340751000c40f4101121103882c13410624904043c40c8400d071070303540c0c0640c840400359807215524200140c00030102c4141d020003034810f508007024407a05550b050141d0b0090181150000b80c00c07071030340030785006c450b1545010071150740e00607202c45110385085412004582008d421744090f41004010000184982c1c05050081070302d46248c041c107144120060510091030200014010102e2405200e00da08268400c40001d0003800c01070008111111031503400040c9400c0070301640d414900c01410900d00210072040c08405000b1040e081446034000c140140881400d544044114011503500c80d030401d403118000c10401c070610b45026001004116041245030f001e8007142c00740f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 651879811 1250 651878561 651878567
    0x9150609010c020f03030a11060705040807060e0301150e060103140f04061523100c11090727030201020114220c030818010f0c2d0c060503091005010503030703 70
    0x2c00c0c0c40982e044004080704107102c0c0c5080000f80700c1c03080796031640d0b0300e1110814000791070600002c002c642002800d010400c0031500010350403058861500b4100600414940820700414051000c100100c40c60b82e800580d4152059a03980541402e03a820b00500124030985518201d041d40c4011000718100d0004000c0b072003941c40200e4541c1407540700f440580d074400000004684803002c00e1b1001141c5100110b00789840300340c04024049074200a5030980e00354840130020100785035a203009900420004185074800c01c2e101d85040c50004102e003603a5401d41c04118060380600040380590b281c01241c1c46c14030412000f10b0b1203500180300a0120311041c804030a1002d004090403034040380400004000aa200e0000d01840400c1c88401100c0407401030004200e10307180c01854090000280d408000b09a1510103d40d400060031807420710249a10307110429004103460203881110807420100780300380e0100045010b12401c104540301c0400e0b2030b0240e0102d400a12920354103030b200304070007000a80 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 651881061 1250 651879811 651879827
    0x3201207050412060501090b0f010f0e03070503030a18060e030330070809070b030907120f020405040507171218041b20030f0406050c0a1506050915060901 68
    0x9500c1ca4841d00307065a40444140c2190440d0086608644800c01806004094400c140c4801d0085648450030807410300060103a81520b0492000c00ca0b040c0b035801d405480401180e4010900542220703901c0d5143c2000504080e0014542d00c1280784680000888611070804c0100d442d800072b0207180743c500c0c40c1410041940308603a142070b031550005015034528800342481c03480740b407454544a40503d00190301c241070229541225406080c2070044c000720410004107042502c0c0201244401000b407800c010024010189000b913209050004003c20003c0110743c0c88116282c8010300450034007828001600e8148408452260350006c2c06001551460f0200b40c00c00502c0c05400042c0c425503001184c0040c4488405070800300f602a1030030481802010000c442c1449408003450500c811102e1150161080344074441c00c00402051001074508288143c2d00050f900250b0610311403414400c81d00030384814400c0302c1c410f01881c00003520710200b00c1001c24040b00003c000602d01200200159100c00d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 651882311 1250 651881061 651881071
    0x5092d12070b0403081f060e120304031127190e010f0b1507110105090109150e1e09040b0c0702061c0606020f070b070312180201032012 60
    0x4400c00e6041880100301000400205004402c50440351070542406058407002a0038810ba00c0034500300c9456403c9016041003d56030301d0302d07014001d103004900142c03d5100107004032425000005001081152800000d0b0040506030341c00f42c2e041070301c07890065002d28003505403001f00300004002941e0681450300101c8846009100043c0003504402d00c03821100401e5035141c80c00c0c2d4800e40305506203007801c030522510701070802d00740c602100782d0b0b01c200046c004aa90203040c0040800e1b090004c0e801a01014090048800f80821440c96424011322110307a04c0c48203070040400f5511042d40a0303e445180381940809045001c642c4c80315918115180c40052440040480511100d001651208000c0007a8452683e00a9020300448131a9007180c0440d07000742c1c155804452540b24013000400c100080381c0c014a00b803501c0308114101501d500700304048450002e0f2030070350029100c00d00800c810400078000c0c0d80030040700708503941c90308050108031050f80345060203000c581c0c6a0301038480d146c3c0d444 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 651883561 1250 651882311 651882313
    0x3040c0e220c06031a060403080309011d060106080c120f0a020c12070b060f010f08060103090c080313081605060f040f290906090f03072705092d 64
    0x401e00c800403050007010030050407985480700010411a1076814000d8291042024681d0b0803580305101c0000c1280c0303d02d2000030204540400015020311080d4802219175a10700c0c207a20f44194140b1102d03441c1c40090140c3d9000c120800c01141046d100442598040000080e0700d0140d07866540501030395080092880b00e01540801440c4d21a2a081c040e1034030038840818020388032400c529060304952401002640903141a6594a10300d0303034040b80c1400e1220b006e081208554803840b004801400980001038000315862740001200d100000081c040341052000b6044055150500503850700f032880c0040300504121541403005190440041c80c41100d440da8607440c00340c1e20781910002003410b5112142d10078512004683c40ca000301c1c0d0140f01c013260726201602d0603105000155180c0a00c0e400346001b8151010300c10280c3d2010800c3d4006040d400301d050815840003004008000d002c10f80300000941080c01090f8041c80000e0258003111501c0b481000d000a1100300c1c001c0c02120301990141 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 651884811 1250 651883561 651883591
    0x81e250c08011a03061311090403030605190e070f140d0f11031902040e15060c0f06180c0a05060c030d020708040e061917030c160503010c0503040c0e 66
    0x5464003482582c0040c003100b0740b064450041c0300300301428032200038401d03200c502542100306c0c00600e807500188841350044131492103e450303505086008014503001f80c0d0b0040100308082e000c0a00c0c1c00c1b01c21040b174005c02c503c41f1003559804001c07981441000c0d0b10f1300200c0c0c0040d40316101c41111002400e42c400c0b440c03500003040b241648441d016a070040076a01040364002090140ca014442c0c82c1000761040f455055280c5494a54007041c40c3c44001c213801d100c1039511210800799694001240d40400d40017044400c6403100749100380d2140001d413440400c0810f40058000810700100c3d00129074600207140c0c42d4443d142c0801e100d4035910030b1114411900041094088144041c4042c04030203000701560b41e00d482c100442240104800b07062a4810400c40d004402c0303903019099060217480c14510f101880e085170030103591450085084450700c5018001c16aa6141054040741c4111001100240300701e00c08460b05590910068030040c00303840c00307050140104c02c290754100e40c00840c00c00ca594a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 651886061 1250 651884811 651884819
    0x1d070303081b071b05031b1c0501051e180a02060a0201061a0d14060310090510020a0e03011107051b0a030b0a020c0d03020c0a0b040c030c03081e250c 66
    0x2006034070050080303030f035861300d0480403030a009018080b0b800350109400400c5c51100b845080e42c05054a01c604501c83c401c613008106260b03002c1010741721101c3d400b4000f40800d007400003190051304180b0f068034240e5140c03c1300241100c101c1c0d85e142c15008807280c000d407000103456000c2c400e05030301c460141e074155901c50320000f0307003c101402d0142501c1d03403603081c45803501c0409405e50191698400014810007d100a20000c0e41e008036048614032640500010701e44050b10b401402d0882452100010610100d08840080c0d0042451204050308070000c200d58200003950780f240d8010320700050704681c800d440c0748c42602d80c003a02034280440c0080c0003810380d075904e9072817281101d030480d4801d50540c2c011410440050040049045034565410294288450810869134840b111075000d040b1000c818046400d0021040b2000040d41d0030201100c0f003242c072400c106500764009050b000c0302400998860150700c440c00d003030760940e442c0c24036050300c0014418260707821042080426035840c0403401d0000307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 651887311 1250 651886061 651886111
    0x103150e04110913140604020906092a0a032a0809031606020d0e0f120a030b0904060605030f03070c0302041a040e07061b05060c0f07060905010f1d07030308 69
    0x16100f000381644e0301e5403035a12442d04080c10b9002c10800881903201400f0700005aa0b8000c8407035106006542078815980e40040320940716003464030b802c40d070204a203008407400c0c20440007400400a9618103014440180c95a185074505414811072900c1c0301e44400610903204501d0300b43c01c1540c0034110703402c2401310100c0d003000007408902164400e0380090213860340a058016405070040010240c101c06d1141d11842e600d41c0c40d49641428201c000103886400b0a000358440e50344402c001d8552a514507083c0b0302a0020200c43c0140c2d07109108900741d0310b03003102d80001101e82007030344580300d02840707440d550910014040320300120110748407141004185440300d1165406106001004103c45031130180702408800040c0085141c0c061030518480c00301d040000e0b840e82002800c0b15981c0c1d18240141400114003d10200800742c505080601c0280b0805401c10303800b04e22031130010080d520440b150300720300606c0c1158080791780e0040001040840e000304a140d0b404558802ca0010000040c0104 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 651888561 1250 651887311 651887329
    0xe040311100221151c050a0f0201082a0a0912060504120507020d1412120f01150c140718140f061c0f0b0a0b09060103150e0411 56
    0x101040e6540031a5807503c91003030901c00c07030356420498020400307420240107060b044484180c995008a51010f16045040502843d184446411109644903801c2c0c2c1e2520040b401c44d860b600341d00041512002c680407902c89071402091040003541c01b0343c03015401543e503072240c200c0400c1209202c9080c41c000b039905040306452101c20300c1030301c0c0000d00c1d25040c40d2030000500c9000341841000024009040141c8030800154031458001d070154080c610050031aa29015500002d06280c402c0850f154150b007010060050050000119504030f90b0780b281d4003000e0380305891400c440000e20309c040070b001145034807084482c000001c80550300c0b4103440d643d8034010280c040d84004402c968800c034403038260001d0489940c10164607071a60180d81046c1000408000040f5485908486d03000c3d03442007080031400c90503101eaa84070000c3d079010704e04040c203000208640c0035110300505900e4001036846d8401d02c41e00541c0c00752203068010403428004400721000c13005000b150a44c3d860310310708925a40c1c1d4059 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 651889811 1250 651888561 651888583
    0xb04150e030910080613050c1312110312030a0c090f060f0e0d0b0402120a05010c050c0105060d030801060e01050c01060803090a09060b03010b2104052d070e040311 72
    0x46982e81050402e010f01141c1c100390740ca040012000510841c5d54400c020040e9800c654840420181c0b605080040d0a00c075068115040d04080c880c00110a941040c1d02c0e00070a005c0c0102030b030741100e52401d1688803400881d201d000101c04100142c03140c40c00e40d118071170600d140d260aa0f003070742e21207004819064154100d080454248040c4450007544806044e0f01c00754151035822130700c05996105200400301800080c403c0031042c0e0168101c11003000240d411a8002000348807501e030468014001e03030b0160341d4140070303942804d000414504011400401050f4195a0761000f60700e410700c00c031001c19040c00080c0c1003003010001030603400001d0160b10003070000341c0c0185640d0344c04082004400c0c0d030943c0c40700c80d070141801c00c10404a00704170141d03811205110301165803031858100506032950000400302030076036100144001d104000944541122000c98100d20707265100005036100c60400703103540301640c4298400d03c000c03800c020b481a0080c2c07280c00d00070400d20203000340904242d481d5003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 651891061 1250 651889811 651889813
    0x509010509090a3e030a06020705030f1206090105010f141b1501150906020a02060d0204090e0d0f0e031009030507080403060c0e06070305160c05030709020702030c04050709030b04150e 81
    0xa941c59090040c00c09401c500e240940c0d11320401d407000004203880340081000500071a5001c680c1c1340c01e0040600c100d136101d240c4141140c0e900c89080c0d01c4000140d40070703503009019188442c000300b41c950054140100450b10350312854000c00c0c01010103031556010343d5004045420f600603440f00f000e4100074600c4104102007502c0d62560605100040e40aa40038080b410441c918904216964022500000d030f160151041c0e9035803000040810043d01c0f40da4000c410703140c0f03810b604031501d079004070382d6a50b459000c0d07035068170503040304000321821081c0540040d856000842c10589000040d0300c041d031424481d0038003d0600705140c8451000790000d0b030090700c0040e1160203e1240a6000c42980200da004507200707401c0c103034140c800502d5800707080d0014450000180d41c2d4014450400008001400c4c001c00b124800b603120411140650010380b0b00700e0082c810b5809403006460203000d078500c9101d80c2d907295840c20b0303d5a240d4445240700540180e890000310034444e60010b42900a030602903205030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 651892311 1250 651891061 651891113
    0xf11030406050a060506040e1f0303020c010f050a050904150801110703082a090d14160b04030807120512010603060e0601080702072c040321060509010509090a 70
    0x3040c240300b03941c0003c02000c10307145401c005004542c2c41c4801e54054660440c514001603813900c91807054849415424802e088012400008255000a007444011400e82e201c80303540081c00390a80e460701400d02c0d42d07804903406010405203810113911005d000f606260b18004200c1d5200c0b922030854010869812803028005049014903400031005600031582d6002d1030610b420504101480b0303160440340b0448410300041c02d03022070340c41d00d404d0a682600049a18808107100c0c208a85c2c13020440409620414000d07000144100c001003a07801300c9070006c2e003c600c0e19040c3c2d80c941f00702d907000461890504c0000e00480400f500d2107401c040c0a4070141d10001619400c203140b54002c103a00420043c1000030100401c80c100d44e01080708005c4444050483c451071548806030300c101100d44000141c041c1c09801048141070744890034000c00035a4401000803685e4461031b600030348078030340900754201c07000d40010000b40c1403411441e540508038006541c1d51030000d03602c599a06e2103180b01c00e29400014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 651893561 1250 651892311 651892313
    0x103020c0a0602370210020306030a170c0f010501030c030816080d021c02091320030c0a090f1202060708090d0f050118020a12030908070608270303060906040f110304 73
    0x42560204045070901083d001013041e94000e54540f81c04201600480e00440810201d480401100c40456800400c3d0480d0040d4240b040780240c100c0d0032141107034424880300902c0300006104050581e81c01840c02c143c5942541c655501650201e13283e00c2d56000200801c002141d00c03400a007260908100001d6a22482c8032112800303860544021110300303104111604990340c6449040c6140d205141c1c002ca4040451942c5000549070280711141d03a40c800020001c1c80b100207001080241002d8441c50100e60b01c4022210302c1d0709076800340012120501407940050724001020309805407060020515080014000c116142c0d4000800c440151503c0505000c2001c01e02510800d4032b9140d0706090100c40940005002d40c500b84569035142411441440902d4450840303100030340304120441d15060f0b59107500074590f81041390500c3c0c90210041442c60b0810004003443c2c8141c01400c020350950f01c4280410101d0140075060380e031303c59a02c040c07a41685a2030301410003c80d0780001c0d842d441e403a02d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 651894811 1250 651893561 651893617
    0x509160905090a091b0b03040f020103021b010e0d0f120b0307050a06020109020306181b04091a01030b06010c0c050405090705031b040e060f012102041103010302011701140103020c0a0602 82
    0x7132500b85c3c5070401e03070544144a42c00300c0c0b4060702d40c4103400c042e51b05a0f032002400141e000348245c400d06072055541030241c40002e041500220f049840c124100c55018988110481d0341d000b510303480f0f00000c0d4191818602803c3c0a4000806180c0014140d030036499440c400510820001d600110150751580c0058080d4035091104691000d4021005504124070011003034407038006403500c107205000401c00101c591100da00c030108059000701111600340101429613210042407004583c41403840d00000d815500c1050714501c00c80d40035050100c0d040c100010080170308001021440c0d60310501100007200e640802091400c0c0d000141c020104424080610082e20400b075070a283e207510280c00c0c085014001a07840d4115003855211242e8003204048400103500c0e8518040e41c4181030030740c000b0101c00c00400443c1213030700c01d8075580480381342e150400805500901c540c507840c5500c0d103d0340a4550094004044504174081601d00c00103c2e541c0700c00c22a082008060400010442c0080c40112 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 651896061 1250 651894811 651894833
    0x71d070f0e0f12070506120402030d0e011b080c1c0e03030c060708071106040302030405100c02010e060d0e060a060603060e011203030b0a030209070305100f0509160905090a09 77
    0x101468041d40640c19100410b14140b200d2036220702a842c080e43c070520001e820301112001e040010402e96442c40401c0350204641c0d400e6409034424065070034903d50071405000404142314041c0c403a00700281180b914018074199840381a201d00c0c00c03c0040980200f01400b415440403203054140840440b408030040600c2024840c4034040ea004000d0032019080001d403c0742c1c0038500d403030203400c6ca940703999048400c1d04812848800521403c0306120406401101a01c151642501da17080c441c2071440b422903010341d0210300a070214110701c0111001f410114001c0c0010b1741607190109441244280e06860180111500d920450b9281001d00689600d07000302c0d4010240b816000165505060314460b40080548000301859a07d190440e40d54a6202000b001990000c3c8124134078980600c01038041d1908480d400c030b15140c402000706154070351400ba0b1059a2000c0d000114a03038508600e00c226451a10020003400075451001a85a03102080740e0302c42d00c2100804600300105181403841c0038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 651897311 1250 651896061 651896087
    0x12020a1205060a060815060c0d030501050405071419020f0a0f02090901060609230d0b060405090d0c0602030a020705160806090106140607020409080f040513200705071d07 75
    0x804500f000704580c60740180f219400200c902c1c0c5c031140000301000064580c0c4140a0b02d41103d004682103070303514a80650005040398020754040c8100c2c1d035580000c44000c03010003000c02c44844148480d40821a124183e001c20001500442d8990012104414034214008008a4840d51080e201004509100c0151504001ca110003482424240b41001e40145054082c40040002d020324801d03652022800c10120355601520a540ca22064103040d21060422a960f0b0700844c01e11001c030b074000c01d0000c1c1c614001c0e100c654401d044892035035a1807019500207094541455001d001e1580815024000c40840c103603894800054185003400316401c2c0798004020019a91501008001a1441c0a001080c00408940c03c0f5500c0c1041d200040091240d200003900052000c6000b910003c100300003002614001c65041c000055400d1400301941d140101c1103180c01e00d041a01041d0303a004402903c00e01c1d02c560152100c09441c0c24400d0340ca2102c009140c40c5402501082c00b03002a000450a1451 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 651898561 1250 651897311 651897319
    0x121b030a02011715130f0c0c1115070605091c0f0816030914100609020c0705040b0a08120910110c150d110409051f0506070312020a120506 61
    0x3803100d80002e008001d4610001914000346000203104840410800b00e044000600060000650034000801061071910b41c04203540b0300309110031500d000c0c81071800b407140e01800c054404244842480101c1d5001880b801c50701500740510030008070305000e1140310303180c3e040080902c0d50189a01c491400522103070b40090080f0743c01d18004041d031247c0480d50200d18440070b20070080e800c04046000f48408000075010310526079503000720710f80202e1422100e140d01c10050004648504414080b8400c540054100307500203541000700c1d01b4542c0000b4031030b010080c00160b030107079602c0b103650820490b41c094012010307000036403a0a5240101d02d40032545420f01c1d02c0e400200a10b03400695941580704000d01c44d001002d05120b550303c1c40ca0883c0d15a08155006002c804290b04280c812604140a016110b5007807030000ba800001442600303150000303041002010914203003e0000c0d50340800340680411072000180080b850740c50000f4a0011460b5032402491801040b0440403100301400c02842 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 651899811 1250 651898561 651898573
    0x402150301080c040513020909010b010210060602071401110607020a02041103010803221d0108070e0609011701020d06180b010318060b0325031b21020a05121b03 71
    0xc2901c2c00244440b400506440015050311040800304130614010340c001d510442000800449203819000b10105220a03021900444241450b520503039803d4011340c0d0068ac07100c0c01c00c01c640010b80c0d412450098040c141845060140490942002d104407072500c09a800704002d28214203082c80b80d4550005045000d604550401d00c40341c1d182c1c421401c00611400702c0140c2c1d40340040c294485038000708070603c0322100c0000300840c1d2840071542403294003094016007200007603503055000010b1041600404540d0241c0c241440502d0000801000c2c2c0000c0d0350a01c20fa120498131441640c018200080410401d810010400015990b900319058101418a1394a141c030b0840d5092101300240d000802065540c03880010034508801d0001026954142d640d4002440c10303442d040000303481c040c0b801454841c0d043c10050010068070f11881c2900c0c13682c2c0010868030014002120800b91000701103441041e90b03400082c44030031401d41c1e2003290303030005900a00d02c003038000a143d84031a0140c0c00b030a2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 651901061 1250 651899811 651899819
    0x200a1b120308040308060f0613030318030f120210060605040302040c17064f0603050307061e05010308180114030c0c15040605060a061b03051b150402150301 69
    0x80b204050030042c18040c1c0c2c070300401c5050391022901d480450f4042c14941d04c882c400010302000c141c051100b94049034012055103000c80441d5901c0080d03d07081074507409401e0f40e550300d00c14040c40e19540a0110300800c40c1080d00100640102c800811159983e20340301d50440c01001b0440b1131000c3d0b4001402032000da820490801d040d02d407136000008503058210072440700000312030030410300104941c000c1c41811110310030101103070140040000c20400485c0c46140301c01d0000300c41160101400c2c0f80c0c000e00201c00041d81e81c2c0c01191020840c18040c1c80ca09098103a2102900d80030380040740c59042c00b01c0e920010040c0c01c181d00d2000b5400b480c0c106e1ba100c01100400c41c50b44401740100c8070010300020100c4082c001001141c03c040314503c84174800746014140b580040100b558400c0c816980d1280004000340714003004402d0050007030302a4a801000e940540d150340c004040d440580c41c0610041140e074009000f86072151850340000c01e094a06441004074400b100c0e40305164074141400184 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 651902311 1250 651901061 651901067
    0x5030c011a0108151201060506030c1b07080a120905030609070602101a0f03010b060a050d05010f15030506150a0c0b010b0f070605060118090c08010e130201200a1b1203 74
    0x3134101d14241c81e21020f0844003a40c079070260845800c240e4200100106200f9044981e9000f40000c5011016926150b40040303802c0e51183d0b41803003445141da003c14801030220300302c0b0f00462030512860030320350402c640c3d49003c6801e2000803240122190031a010821046405215944200e8055441003040c05001241c001c0300c0c1c18880c1c2c045004510300e000c94038540e2801d60040d18100d0009040c81d8640d40c0c0c10000900740d0b405810b013010220306003070000031840c503902201415500f1400b03402411014500080740200320003001103910082c01d542d602c50382001000180300000003965044180c040c141403021420398181d00a5900d00c008104102002071084207943d1969482140440c00c1e03194280101c0d540c540c400d540d1100401d08010000d01018550300021607156240c5501c4026030303960301102c40e100011910030010001c0000c1d420700540c8500100c000d10a501d8490400d001c2078088003601d4407143e030300200c1d442c0005000c50b12903605e00189203002005075464054100705156001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 651903561 1250 651902311 651902341
    0x9030206150a030f080d0204080303150f09040f0c0510020d02010510080c2206061115150d020406030b04080a27170109021905040b0f150901020a05030c011a0108 71
    0x5410304e0501c416220401803c0c000300e4080840303031041513460b503490710015601c1e90310948400c81c0d0030b050404002120b007032445042e1040b0308000d1091606540e25100c000036060303e01803c58680c20340c508082499a190a0030518072982e03607004262031042d0307841c0a421100040c1c030f900b48030b0011090400110380700240306070402e20242c1e01424408041140244150b070345004038418030b42061008a0916070016101100c0803041044902401c106190400c880c0d40980d03410180041001c8040020b050050369024964409800040c0403552502c512070040400c0d1006c030b80038032000813584d0b9001e9018140c4425a546a040c02c0c80003002c540c1c41003400d86092040030500542c101030306160107000c0d882006416000350010f13101e00510102c9000d03002d01c43c0152446145003d420f0101e50400f9406d07400b00300000340103000141c86854030b8410070717004254040d0440c071883d40d11400007981840a0010f449002002050070400b6101a0a5a03445410210304002d5000200f003902c2d0b100c0809 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 651904811 1250 651903561 651903563
    0x804060c02060d05070215160e10050f120a051b072d0f0501060b13050d1b030602091f051806091206090f03090d060b18040609030206150a03 62
    0x415640000c90703101050450180007110700304685400e08000000b5000b0842d600700f80c12041c00c012451b552081540c801e003d14245510004000c2000b00450741003010800519100c44d0500070300b8491303106a03100d911f038407642e608440c0d4042c1c84103000d404601402030b02d0b00095810007600400552010507002801815800b5112050365410907090705580628000c0001d410000310400108500740903504c4000d8a5040b20070b0f42c40e01000040c0a84451306a8020180d2101c0180c0c80e10310309010001e040440100684241417200c04a14411101183e1741e00118444d039005610754010700c0030090040c01d8a825000d1500302c0c0691105159030200481c0d6400c8031103c092008010750340085180340c01100d06803a000800d411010611a100254661081803140121050400002d0b071050301ca020f06000c072500282810f888200150341c1d504900d86c1134502808984009441c4180200049016202520700340d41d160a07040c00e055040c4615a8071541d080400580d0340340131004180c5030016440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 651906061 1250 651904811 651904817
    0x604150804061d010c20030706020c010e010203090d02061b160c08010c0c0204060812030f0a020c1605270c091807080915160c020f0306040602091309080406 69
    0x1000a0800440340d103c0f10919200b14071001c40081a6030f0554000e24080f04084013148004440452800f00075503164016a2843d02039800d2030059a9944040c1d000f124030000d055484820700c0c40215801d201440c0300c2e50281000300207c41c00598081d0500b040644030422004882c001c020315503005200b01c54044100780c1231500500e860b402d104200054540240c0351075401c151102c0b101b2603205110402c01c600850313040142d01d955003042552140c1c8500d002000542c20310000e0500030000e01040d50200c0004005442c04011031489070800500001d1038548000702101842182801c601d0088030b03440201000d00e95441031200c041c545a0000c00c810b004100c006034201464131210300c054100c0712000050350f898140000050704824003211a05a0b44c0b080010811f802004440b02c0350240f8404981025080760b400403c40b511100c40000741d070403200f588412807190320104503d078071680c0030710ba0050b11030460f04100000b00d170985500c018142d061021000c04510204102d030100c8202d42 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 651907311 1250 651906061 651906077
    0x1e4d060a0f05130611070501080415020901090e0f0a0c0c020f040203060102013e07121b0203031c06080106180f110a0804050c060c151f06090f05060415 67
    0x100708840c14428000f490003944050140024000d401c03411840c0c415001c20183c0c1c08241e255801140c5005007150043d0680d03003140b020303003000610765000f0300f414841072601202c1144c51740c24131503e0300820741c2c04d903502400060400c21098601d2141010800b035510740040c3c01c2d5416000035041003115040a440780d075001000c00d40b1a030003540f1154088031119502a0a8038000b01003850062000b410030714822901c0107026003081240d01110880d5a0100c01d03001c5808984104581d0002541010f0745444201e80400c1c01607501003003c0c211361078202d4039141240061081000545070158452405603040172804e000c002a0f080f0340c030308803558804001481030034035040c0740017400303002d14222031700711001a404010560001195229070f0154003201e04c0304021070240101d0f481407403403c6a1faa001980b04048102c0c0d01482c494100208030480702100c2e0803040c40c0d00406030960b1003130300810162181049020351003040c000007040300701c03071142c203091070070441d4070603800f861401e4000c001c540 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 651908561 1250 651907311 651907337
    0x405060124030f06260d0e011d040240050315060d02100c17030f0408030612010606110c06030c03061908010908070b0a05041e4d060a 59
    0x9034007150040c10802c051194443d02c001030407981c544840345e0440f050040c0f100d22504540240b20b54406c42d0b006070348041e2681101500b0000700c1d070400400541c055000c0095407626031300098002507102981c2c0208411016048106082003400d44030034058071190801003240c0e0707a001c030b030391a12800700440c0c040d010756034080090740081064000075405142d480c1101401c66014540d030032028800d08601c0c01c420a41c030240c1c80e081c0011103950f00080700c000c3c005000110100042c541190b400b81c4100c690300201d80c555403d4986540202d00000d040520108038070b0030410000c190b10b0801d40300709240d418880e444c10301600c001898140256501c441141c0902000c402c03100c010500400200031181080c944121103503c0620141c48074204200810b8002e01d892247c5030103640d0185801d100400c40c40340c0300002d00c85902e0160360b80c000314020146000000c0624400d107840405000340102e404a28440e082d40c0c02003010380e40ca41a500c2c401c403580d00d0301d80803504100a14104104503000d9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 651909811 1250 651908561 651908591
    0x20607050d09210f0801120203030702040b01050d0614011d09040f0510020a03050a050619030b2806050102010c110d080c0403050d020703020a080c0a0306020d0e03040608040506012403 81
    0x1a83c42d03614072144840c00e9020f07025800301c1034034650070040c0c2d85d2403410303640e5507803180d9203a03480380020354140c00c00c010100040c80c059200045010301030408c0c0c0e090480005042007209c80781c3c0e020340042d4801e01080d521640c1d0164001403200e040c11205429a40301001192108000402c003d201918050440d01072001c01c205032640d000310302406654904400d00002c0c0600300c00c1d51664115400e01010542502c0c0c40640769141710351510f540690186180c880c4c500c1030074080d00c03000c0c4462500d0550550a000d0120f03001e03a10195020100d245450040020300f1203c0b4541941d013000f11400c0306040740c0340082111688040d540c0740c1a0b90308c0d118100e0418061041e5400100f103071040d00303043c1c4002d50300800e80700704490003101c0310843c1c0341e550440e0540f40c80c1d042e01165400001c0741800d000180301503002d0403c0c40d508400000d4011000d5001030f2440e4059008100400e55003c10442004401c00030140908a03060362840c02c1d808504c0d008402244415100043c9900d400506074012304c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 651911061 1250 651909811 651909833
    0x70b0c070c26010b2e0917160608091506181e06150d0f0905010c091e0b0a050d0b041b140a02030301032009070519020607050d09 57
    0x84210101070b00010000c01c0070310060100020b0559400c05507a502c0b03600c0d000c2d1151100d04125003a040760862100d090103202843d50080906028608201040040c00351140c104000111002401c05140c00882c2c400d10203203c0e40864104104601040041e110100d0140e120782150382c001005522204001101240749400505040403040200000c841c800700c0080b0f00e0400015200c02c1c1900c0e00000d010301142039040301007140c4d900300700707010312590b01d0f0703012590030202075100243c0300001e540c5290964990b51940d00002c0c940c1c5005100444220134011541c170360b0300710400380c0545040600d40980c01010b0840042c010b001c240b001c100c800d282c002d1701c841d80c001481041103912107484850441d00c280c044d817001440911101d000711140408852001d100c5800440c10b680c41d60382d4003070314040841100040080d0f00412a01c0340e450320301c4083d00407642d070384a507610340306004e204603603511401e442c41d011540090300b40021141c100302215080c82541e0004501e01c4082d00744010300d00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 651912311 1250 651911061 651911069
    0x30316050a0521010e180c01110c0315070f0504060906031a10050a02150103023d03020405010e030607090918140a0218040506010603021b100608010b030102070b0c070c 74
    0xc0b000420704624603d80c000094160342c02c0d105040380c5a200c030458954888031724001c0c0000365200203606075440d030085a51070500401f0504885050b624240442d0030304006404081112a00300140841550809240c100401c1180b43ca5820180b400744003c150301618801d5005165031280020007075840503841d4a681d031409002e698120800310b02c0205540d001c400c1c0230005000e1000344112205080203602e049030380043c80c40c0c41e043e5940014401943d8a0a64140d80344148840e0300055014403100580b54a000d03240143c0302d618020000d025070b10240c0459110f03400810800070340d03d4008518906581c00b242c4001a95507024100008069904c1c101400b81c4031300401200360010002807040095100341c07000f0b00581900c40301050b86810a5600818942040c0010b00c4003a2203030380034040c0004c0d111140e508110580742840d05040c0035224194056490b1402400300c00030901400d04004000d800840c80d08020342c40710079084202410141040c203000802009100181c94814003074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 651913561 1250 651912311 651912337
    0x115140a1413090c03090b0a0e0f1519050f07080405030f16021207080615180c0a090f080a020f03010b061210050f1503060a171608030316050a05 64
    0x94550500440041c10007485103c102e42d0404c0501005188680100e609080d070207906030a068581c070803c80080d03c5a800e0029080c450041401014281044a04101030f0b00440946042c20082850b07140403400081c0c2b992102c3c04d000601004406501d840c0340d0101041c40c0c0319000c0d844903d4903034110b108100001220140109481c0d0704040d4140326900441d1007115994000c1d003011014644a00c1035101d4012690030400014008880445034215440e07001401c40c081e440380880f040201400540741c0151054001c0754030080c03507401c1902030010f082c00c00c211034011454104800e40c0c0700c0c035440000340503100010f203a0707840c1e840035000801c00c08801003c0300e4841c40e000070f1803600f0040803500481c080b15144000241d6080c48602c4400c9800d000d4410000c5401c08100c9290550019281030b82200108000180d40c0c0803d400152a43c0504800380552a08040000c4160205904030345c40d03d4000b04207020780203600450003a46c401d000d080c09600e03005034140a580034011041e000c1c2007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 651914811 1250 651913561 651913567
    0x302041104080f0a0c0e0a06050603040c0305060601021b01050f0d0c02060910090b0402010c02030a0b0f16080f07031d010c090906080309090f09070306090b0f0115140a14 75
    0x3040500000d0000d4030118800c656440792a601915611a40f041002d011005194414400c60049015041d440045680041074007a5a02c010808a03841214151810b1018160500070044103000203a003080c0e00348004c0c40e101100080106020720340c00d072801d0600c400010040300d402209426291840c448020811900742c818030040d490b82d000f1168070b4414018a00b10702071800350b51040c1c9108540110b0f1132092540d8541c015501042d401800340d070316120701481d09002075546c03903010f032080000c280c0760300301410031701480066650149004414041140100801000140880c6500406906c0d0201d02c41911462820010060f400d4400c5554240007640306515004004030b41140d900c400100041c40e82c42c02015200d005000b00f0395400017221011500c400c200c103261680100700300091322000350390303942e8110807200c0c61581260100c2d18001040340c01d074850b1a00f140140008039001c5200201e94400520300b0004441140501602003441d000b11071013000101010b440100e5800d907 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 651916061 1250 651914811 651914831
    0xa0e2d101d0105100c062306061201090504020607050d1d040c020c04090602040317091008071d0103021c14070918180b0a0906052401030e030f04120309080a2a030204 73
    0x1c2004802c00e68407d42425070010500500748003080712540c0700a00804031460f401c0c17240070b03000303060094001ea9110005100746000305400317100c9866203c0168517480400510003d480001c8a501100b040c0b146282841000d40d813500440c4a4281800c04c03100024054407a2a12500030b0040750405810704981d011030209460343e40c401429821800c83e4080101c0d150301c10101e60f202400c884c420b00180e0072961005d051004461400c0411074141005420003045c50010b810f43d45624440607001034841000680031408c82800e19001006450031014050030074081c2c0d40886500e07000000300703e584290386140403108691041c80b07160300c0719484200b824680c276140094441a1416915146044041000c442c0c03e1080e81540304030340e0001201e601e14150064004043e860003180c1c0b00d010400c900d0110b1080c0100800190200308004603901c1c5031420700070068066a0025100c0e9400080300001180001c45401000c010042c030b102600001c00b0450340c2402c1c060350009400500348120b60b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 651917311 1250 651916061 651916091
    0x15060b07050303070e0a1409040c08060709060e0402040b0406270e0603060a0504210e0a031a0a0908030c0d1b050307030e0604020a0e2d101d0105100c06 67
    0xf42c050b95042d82d81c1d01591014004010941c1c03a00d21070f2102c058100b07041000142000b15015500030300860000f640b176035460241030b06066085a0351030000d0465042401300c0d5402c0f129410701020155001c604041c1442000c5085115a020b508240907800d401461100c6d00d10140c0420808445111203449a4030040f5005150041d24503504c02e000c0c20703001910b080841d200e82c070320594101c1420000b404104049812881c22088008108054411168283c0e25651080d01c02548500c0710480c440320000071807800c174000074200e821442d0030050304070082905c05003500e4003d001e202d50990b8545446628030000c250113503480307200b01481c50050f842107802c10095441482e40e5203080c0f00c1604084a042d854050440b00207510040e5020240904a0054078040c0c0c0a0034600c40c401031101c201c080e200d40c4900c0010390140d902c5000c0c0030055441c2c1c83e1042c1500908002c3c00b500d01c048004800c000c048101401070078064403a204882c1002c502c200c0e640704450780c00c04010401c0540140d511 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 651918561 1250 651917311 651917317
    0x14031509060a0f090906290909071205061b0301141302120a14010821030921180f0607110109090e030408071208070b06010507080408160807060c15060b070503 70
    0x740c0700b10740b0381f0014100990a0040b0010f01203101e818600d1028142003c1000b0040040c040740003611620030081081102101c103420480d029100800707492401142c1e841240380103201400002030148010004000c0c07000403018000c004032075201e4143d8003445060001d000e1001c42e01c18078070100b81488a540501c0d801048154400c080c5000c040e80c8551100d541e8100c0104c841d01c07000701c00540f50f4403075621003002d180c001c0b0b0884103603135401d0f10202180c030300e501811a08600044000a509400c980b07414203d08520400799004150349515500091040c060100080d0410300100400603051784901c0000001d0726046604120b0015400c8505650390058024131400d44244000450794650300081c59220b1944914000d103090300c1551a0184407402800d900c1c10300c02c0502843c00014070601c060806428400d0050070300b1800034800c0345541304640e00c44041d941141e1400d02c0380542c0b0200c00107180343c010300c015200f50070315094100149895070003404509804128001080004002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 651919811 1250 651918561 651918563
    0x2010207080a0c03120e030a1803060915060e010e01120525050f04050c04050d26030420030d21140603070e01150f0c1208010614031509060a0f0909 65
    0xc2141014181710003104581901c0701400d01a4000e100d40b502c4d10380701e00e44c464099008854001c1403141d4035910030080d100c1c5401c080360301041c05991407400c41080e00c541001000300104030401540744c000400320001c0e060140031700412121075280140401003111088460300c19816020114034007807400082d40290081318494071607055036420620303050060a0045151032200d0380340a00d02010010711200b6010111603403010740100050100d036240700c40f00c441c50058030207640c03450149000700c2c610300c0f2845958030402780d0402d10480ca0301d00080c10400501c3c07038284a031007110f07444454003150726000007600d082410680e19007580003407905014000c401c1501154829610f84c01c010020110074050030000d51b42c0820f6003e030042c459141e09403103500345d0a00c5044070ba00b170345581c2c9000f90a240c011020800f110300421815510912910784070881180d4282035044c1040b401244111120800340720700a40ca01144960390b6090000000b815515042c42001d9a2000401d000c1e1265482c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 651921061 1250 651919811 651919817
    0xc0904060b0c0303070e030f07060305040605090f120904060f080d2d050d091e1203090317060a0b2d09060d0911040608010f0b04060f060f02010207080a0c03 69
    0xc00050468001e41c182d450b440360900145056075105041101c8a0007101d00c00756051052801403004041c0074401400035004554001c40c8070724207800c0042c183c1d0700c00b40815005034405000320b042c0840203d90000c540c0f50380806160745140100010780580703271300d0300600d22441030a0400034414900145004141c2055110103182c000414034482519100042580c0d030142e100314064000c1e0700c81c0c0000d00c2c54440741c00d00050030204a07150140b416820b0924824030080080d821418000d102c0300a40d030324006450284017050003940c0042c24403100f80d4960720074440110100708e41ea502d070700103000a085480c00140d01d075601c480701400c4c1420054031240c01401c0d4032905040100b0701100b1191900c0c3d0280480d40f41810039a8450300800f50500306582ca018020342c0300c000e0380e4a40c040c80b0010402c12001144450f680c04401080b00c800700c3c0072501c41c504c1e0000401400643d45018000c80b105070030003031341800c1c0a410607806840313043c900411041d07000403401d10403a08556007000f032a02980d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 651922311 1250 651921061 651921071
    0x706120513080708031b040902130b04140402070809090403050d0e0627011b0509030c0f0d031b050a12020c0a06021b01120e03031f03020904080c03070b0c0904 70
    0x8007070410044010700e01801d001c2e42040500e0210300c4090007550090f03810100422407840b1050300002e141c10a420840006400007010071030b00c109440c883c800b07003403103108451600e850840d1000e68034900004940c043c603000316502080c8885a8150f031000c00004d41246182e14051170000e0030b40c1d00403201024214a407108144d0452000200d0a200703180d80f190307106200412203031241604000000d100103940d04c0302000018030080801496800d50183c0b0349546a6859400b01810401401c01540c012080c4406000203683d62420301804c090305810099091440e460141c14400c240720b40c0607006201e481518008c10410700407400e4003912070303400c0d0703544156204100010900648904001a407000c1c41c40494243c440111000340d05050401c01ca4000c100e91b2800141c03188200301a00c2500013108200e9003054001011101c5102881038103091400c0d5070014100280152001d019402d000c1043c0b4402e0004001b2a1029504a402282ca600e807445e03041146d03a100c007010502a500788 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 651923561 1250 651922311 651922321
    0xa02120a050402030307150902180109060b0f090111030412080a030c0203090a0306050709050a090506010f020d02030f0915120103060c050424180b070512030402031b1207061205 78
    0x40e1040d5401194004d014514020880d121028000420342108620755640c0c010780c80142d44c0c40d040c1c46159a0704001420613585842844000c403650fa0f44840484080bc00c551528082d00c80120b03044d161090030580d11921050400382d141d40900c3c0c01840140607000e201106100f601310240920203c04da030144004010f20100301d8682c0502c401080e0410f142501c2880042c00607040705030b12002500d000c580036642c7d00005007003901903130b104c007003145d640e602031107003650f44940095a1300c4541c1c0010041c05403203c000958038454503a03501408a40811401881d03a2440c0d4580c1100c00d540c80e880383c0316070010304031038034006003880122030691801d180744035441d0040098070122440030048128107a807030820440040070b402c0c40c1c00b0422039028141500c4558101085000d8004a07420036160540d91038a10b15240010700815200d140178130410005980c009224003600500001c0e42d283d918081000c50a80d82e502010048030b030041413404544207500000070071900080032424800d50f114 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 651924811 1250 651923561 651923581
    0x5060d090215040302060304110f0303070c05030f03030928020a0303030221091002030a0b060c0601080f01020f0921010c1701120206030f1306111b070b041406070602030a0212 77
    0x10f41c1c400250081800d000003000304444d945002500031014005060350100c110000341107600c6054122400003000728140207030b0404002242c00d0160b10002986942859400181c1c1e61b900391030071140000780416501c9a8454001c40c61026550103084450200d03201c0c60050b019400200c5100d40c03a20948000b00c03007a028051400b130040010b44098216620101c05039806540000c00d28222580c0f00c104509480d01d4400003060f1800040010b005a03504104126051084200c15050a07038010710040c03031000a104110307444584115600e4030b408900d00725454038004c0d01d5442100030b51800440e01401d030f4000c40301e914520071040041c54182e880c4c2d1184041c100017054069080354090000402140144a0094019100051280c00380760680d50b907506907800520120300001021030400c405c42d200045121000f036410018190136420308295035940d0066104003840f4a00c0800c80b4411610380350121140c0c0790b00a0401c1d035492402c445144003035070005084250000030300f0005050000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 651926061 1250 651924811 651924817
    0x18090f070b0706050f16050a0c0206070c050a0b0f090d030e0d0803090705010306240c060603030504170307261b0d022506140d09060c020c0406290405060d090215 71
    0x6c800c860074080070861a204498a400c0801c034a818440d00b4001140560b80f100e0240902500c038030203141300c440c14070341480480d603607943c040001d18009000203000c1c6070846061350302084017503d25400d4a503007400e0454000444084e299081404944a00140f01815005502c98082caa0444904c00ea82c0c40044040780d003039200302e07001504400c01845030810401c0298201003014680741010748000c0d142c0c14200c0c3e505078421004034400150070044c00c401c8919030601702000304080c6082640c00d4071044203402c50800d03214100b510507046584103280c0c6a040e19031004070408100d034440c69000005980b5034105500502600c01c610035551201d0502869080106481c0c0b42c030141d562070f120701540d204164071310a1120250a000409200445101d10511940075920100d261420001c0103800d060036003503900d0080c0d081600900071414440e6071401e07004110079206c00c920940e404548102c2c003d40d0000c580c449000241800700000e1608469070441c000c0707998403100a0843c0045000788 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 651927311 1250 651926061 651926071
    0x1050d02060d020c01060503070803120a0605090604050408210103021207080d08040204111801111603031b020307081c0f140d0605030105010f030611040518090f070b0706050f 77
    0x101c000c0002100004042e0090000c0c5a06003002081203512040000d003881880d812213081c9034000f150140740003808004079a000100c421003000124100320204a40c1ca000411a5000b56160000706040128401c1201c2402050700d480c3c60003503c81016850075000c2c01e10007a4400c0c0c010b00110752170b4a5001c24004100c848080042c521442c03240d80589455030014030503a4000d40d0342d0740c0c40307034110b40c00e000400d8003010170507a9840580308440058095064070804515680c490201011010390609140d4141c0381c150400141c1d2348004c030f1110071a0091008002c0d05070144413800181307030000040b02001d01c010380e00c000b15034200c1c2001c01c846410031070071038100050b41c2401003111440c0e00401403151700d01c0742c20003186681c1c940300440d0a58200383d2009404c0b070007100c0700f001070055510940c5403007d998010740b4501460400000e004000b11012403090f98824004500000c0301008103d0000c403282e000e80b03654550340d00c80c142c0203802071141a41d4176410803000580c0e100100c3d00032440742c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 651928561 1250 651927311 651927319
    0x3170c07090f14150d0b04030e0303040b2203020906060906130305010b0108150f01261501091226040306090803100503010b0907080c0409050c04051807050909040f021906030501050d02 81
    0x110482c1d11001b0030b000c00030b803041e0280844c0240c01d031030380e480900042000d030216101083e60b400c440200c0c40303c1507000005c45030b00700c5c510f44030500050340c0301824036803c40b90031610541c84c1d000c01030001c1d900d407160f1814801a62208003000040000642040803454000d0704c2d95001950307503001444015a03100c100f1035004442e00f9002c0342c107601514603500704a06000c96450000080d42c240e031045902614524109245565030000560707000012502409051c00070074054400d40c0d40f504400b4409089603515807110010115502704010180e400850700040180301000d0700f03080c002126401a03441c0c01c2022854500422079007414011010648000307003109803e551082c4084410100c05040c088521200b004001119502c3d802120301800084006980e61454130080141220b41d07100c0c54001316080a042001c9242c0101c01d8905615007680c4040c11541c452030480140710124200075880142009508903c00c00d040c01e41e8191101520304000c641d880c0d408100350264103030740c004e42c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 651929811 1250 651928561 651928579
    0x10807050613090c110604050a02210730120306050406050117180a03020c0a150807050703090504060e0a0e0309031e0a08070506070207090603170c07090f1415 70
    0x20211603607000103000011440d08000082c02c80440c07904094058405552301c6d0f20401d10b41040d840c0c20b28482d01c040001400c1820b400194500554550b4220310440c1d403100d030320250500c80c400c800181c19000b142400b01e266500d0095145c100b800005800c2400002481e00d500440c10381024440c3c0401c1c0c0d501612280341c2c1b0410114184e2441c44001c110003002c4a42c044e03402c2200d0300400500c910580329070090111141003400f0310921300219400807584204075004121529080141541c2104a41c608181d03504640d00b8141c1e600801c6610480c0c0040c03510f03000044007002c0e6207009001c2d0704140820300c696954840d406689024000c03c070b60f0b054010602c110100d1180400c560380781c0700c00c0025074104000a0701e52104039001000161250f800c00741c20041565414404d80000d840c1c240803c0210b60305640324103180180d00705034142052030015101e11808070400043d00207004010082c032802e4803a802807000703440c030311160440b48095400415814200c0003a100c0e4640006894058 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 651931061 1250 651929811 651929819
    0xf02060715020f181c0206070501060e01060c1a01060516050a1a090f0712300f02010e12120408070f120905190905150a0e010807050613 60
    0x685600000d0100c980701a089101d0380469280c1c0090008000420030154540c1e002005104220104002251143d4128070b060100c00000902074403009030151996031700c2e072403d85886070040615410904200086200002d28a603101010f170140c64469081d508500ca203043c40d00317646000a02900c40400d0b0103010308101d40b2042050b400c8041d000f1021034410a102d03403291200f00c40007400e1644036045200030090040ea00700718800d0030071a050020700b08189401d860028000780402d0041110f0141c02002c2408194a0001e0070401460b035206000380c1155003020f44040080c0f1170f42030255003806d80307203099081d001c100c021001d0481e1201c145880040340c00589000390050048030701e84024070521002c2081100c2c04540d040c0301d00d048a40c42e0303c81d030b040a00240c00c503070b209911800c9024031003403441d000010f60400315035199002059036118031941c02d41100b2403194041d048070041d000002c151200e21100b81c121500c2406450705292602d09011443c810540082c121242101c4100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 651932311 1250 651931061 651931069
    0x70501030b06040902030a02030103032322030b18120f031512030307030501211a0919030512011203091811040e06040c0f170c040b070b0a0e01090f02 66
    0x2801c114000d0100b450a41c5680c52070b404ca80040e6981c003412540480184105034003d04d440304515400302a4102589820000074100e10612082041c0840d420008650300740ca51b4155001039507000108111901d03002c42542610700781003d11842e24454181c01301b051644880032106e01c3c02200b08158910f07030b07404485184001054555503080710f424412103040c61010320180d402040399a0b004512940b50000c00201040d000f220011505111149200090310142d8002d0134164031040345681513603000000703801c3c2808091045484e4825858407410154802d00610350754140c240c074926140d032500081514810202c0c030050128850070801c2c0700190209041c1e1804102c0510041421019405242c0c0c030794100d60302c2070100300a51001d10503945041c0c0518800c200007232500c0741c4240e541502c000c0021541980d4500c10551207008a2185000142241d0140494500d0541d4030200791800700c102e41011140800458075000340900ba0103418080c9074140741c0c000640750503c0304036401b08 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 651933561 1250 651932311 651932321
    0x130b04080c061303020d14040e09010608030c010c09120b010303050c030903010f0b240d0c0e060a0f0215092d0708030a02240c2101330207050103 64
    0x98449020034080741c1c8001c10108441403150805000020f4240703500e00e030207490030311251a002c003482141000c10740400b83c44401d440445a2149000c00b05494000fa0940105010342003000701d4000040c0f0005142415041304024248960f901c500700b1350f44a04907036041c2e80f20391001300700e00c0e016001000861321400c0905a03201058003500e2522541030002400c65041d808000800c540701c04e031501032464100115801010541d240d5401008240120131541c411403040d124506d664a005031841882041c4030401110050003243d80e80e96544000392449020b602d4090040c8100e40071560100100c20340c9034000d1048a000700105075081d80c1c6102c6070000c0248030512000c0442815400a10400202e00180384100155590b4014000c00900341f08510145010b0074000c12082c2803480441c4c019103500c0452174403801c0c0c84c0c05000d0b0070f813007001c100d149000520307060a82c0082021202e00200702031944400996000202c0040140304442c0c44910501000d038003e48002c103c294025000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 651934811 1250 651933561 651933563
    0x11e1401080717090c21120a050c0109060b0a12050c04020d0e1603050c040603050c0409020d02061314150702040902011107081006050303090307031b050d06050a0b09130b04 76
    0x50b1910201d204202d40c010042140e1000217580701d064050b0907410020b003c8491002e002103400c08094031900c21540e613609080c2e4610600d0000210900b519108800742d82c840300c026402808030b401036080c82e902401c8800c00640c1700e0541d0b5080018028113185180701c15550240c05850501e0f004000c10000f500840c440721956602c40e0b0301001d01100070303c5080c00c944c07125904440030b181113050161800aa180340103014600d000418000701310006501d11141c00300722000b041000d180c0c4042020301c80c0c0d803130700290840c10100e00c041c20242c0c2c040041007a1400e9100c03103610030000b54104002a19820460b150303c10b8100618009070410317401044030b0f40d00604010398050204040c482c40c008055000450582203c1a581e40d030443c280280d800030319080f8011414200000c0c002611100d1314800244032000c0c1ca202c01807218900040940140401400120b1055890500b030016050880ba500c409905e07000f03841c810752034400107803030250130800200c1c540b006003655800b00c1c550700600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 651936061 1250 651934811 651934817
    0x20a051504050106030b040b0a0506030106121506080303040507031e150f0e030c0c0f0a05030706230a031b080405060711010b0604090b0a060504030b3c011e14010807 73
    0x4c030100208141e840154000e0707100d06060690303498002c1036003040b00c5010f0100d80c4643d04004013004020015031844c0c0005400000a41d40c02480008210050400b5806082640001700400c0148000800d100d0100da0044518521502c078204083c98051442d00d0028500e81d040c07109140c0f072041c142d10a81000040001c00900700c1c118504051964200c05000e86d4180d1080000c19202d0074403090b0b0802000055032106410303410000040d440311090301070f801c00c02c06081949100148290021404001c256110742d984044c3c0c100c0060103001da01040c20042c4c12149030303000c1e4140c80380d4130b150304c220b4108000c0c00c015142d40c0c0d02100c081d4101144203d180d07407100322480040c0e6a850080c80189800c00f0000b070301160130300c01c1c0000d48900d50f10280074080c3c240010008078020302e02c030710b6000c0110b040c490302c0480708080810b12004213900c1c0500b840700e003912195081c8040303040103060302c50300340180b0806498188428405002409100c0a604060f01100801d500402d0400e400c406130382 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 651937311 1250 651936061 651936071
    0x3130206130306201611010c08160b0c0a021c090b2205063c0304050c0f031b0d030c0212010501091503050c150d0e0319020a0515040501 60
    0x842104007490458200fa125103648054800f04405011a507480d40d00f0003c0901e8100350111505480242140d00c0c00340c45d43e1000030040106a2044110ba040e00c2d80c400310541c1c50b0390508242d0384940070140d50485500300c01e01c0c082030303021000303c05035110160341e40d004085658032204901071034000313844c9420522141110100b4803d0b0100c019054079403910030794248890700c2540201500701079511007800f9440070481005520b07440c1d9240c1c0507034180c407800400510031300216005140402801800380c140301106010401c0008120310310005021103c40d0001012041015210a005405004504401034181049040c90300d032100e1401e00a042c103070420105c5070041699640700c0d1028180a075074400061144200e2072040c07034114011001c0d0220401d06656441c0c3da11800380c086248200e41e0901020381204050b0b003110901401000140802200105902d030b4a404c02d410703c1c40401640c42e4034500207880041c0d43c1006641080051140041c14011a18120713400360094585540303071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 651938561 1250 651937311 651937327
    0x90b01170f0402100306170a05010605010e0a170c0d0f03080f06012c0325061d040902031615140f03130302070801110a081e010510030608070308091f0503130206 71
    0x40b80b0040b0f441f22950010305064241440c00e1030031074401c2c0e00710606000016080d1386a03a203403880c04009031055401c00310010f041c018403c5252400c0c610800e680034040c3e100d02c408011039680b0710346015100391605003590319a0052900c094204403810360000c2c00d07040d020500d040028449049259402500c0d100e51110100400d0400c002009030f90060504100522241240070401200078050742c1f81500800b00ca02044d01c8400341038040e071038400d64907020a00d040d59018441052494103010380e41c15581d42d94007034050003104040003a004076002080034460401468111049031400c03214452a5503203841311400280c81015080d030851060340700100d0011400d1107481c960550300c804094481c81d4050004001260080c240c407802114a0b4492071101c840306240d40c19124211500c07a2080c0405004030010901e55014880ba0b20941d01c00100380980c2c1001001501b0382900d12050105100c000d00c0d04601e02d89014a0003d0000c00005c1c015503007441c2c201900c036200501e520b00d01111 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 651939811 1250 651938561 651938579
    0x210d0c0e030d090608090d172806050307140901030308090f1516030b0d020103020315030703060f050c03100e060109181e090816061104090b01170f0402100306 70
    0x442e900c0c1c0c2c000c00c84441040c403181e03400501490380001c64600030200d002c1d000400038040708040020107071840500740890a203041029110798454940e07150001c4c44480031040c2c0000e0a810b02c00d01e13010380920000071402d03882d07034410b074404400058044903003a46191360032102c034940100305008038040c401108840c81030501015032644000c208404080c05c0c0994040700d1300480d60840c20a040c900010181d5540722072800ca031100d40c09090068a030740c0c640b802580c518195114055250044110200401c8515400b50602c013102e8581000541d45500101986200603921040080c04d40541000641c04003100b60340c0c40030040c50a40c810643e5119242d480880d0302c1205243e440e00c404551685160359445034040d6800044107001c4031005884030b5040344a00e04d40d540c20040031081a03018001641c20032010050803c40c595603c3e940c0d6000103009003c01034003180014035104030700044c3c03d00141280d004207460080742215860315170801180310803511920040c0b5455000000740039030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 651941061 1250 651939811 651939823
    0x150311070305070209010b03010e0f0709050a03061a18010b0d021312050f031c1d0a08040f12020901091802091501082a1623210d0c0e03 60
    0x1c80780d1222920303202c2034030401c100ea8205070014900c00e101400104001c200e20034400350007600c040d61803400303900e92250845088180b50403164102032071040c00030404c00075074003084c6031504200b6040804c0d203154007040145144c0d10780200b00300b6040c2e0010300c9030b1507a0310001d2080c0c1048000c010b190079400302d01c0401c031402c0c40c2c0c0684416804000e40406010080c415030040b046640059841e001c541c200d140b0421400343c9101c00d03501c0d030700c80340501c1c0364038403141d120440480401102d0075040b00740340940d225480b600810364403880b101d0700050400504091104079960007020301025a003400500c000414654101c03004900b04561004c1c09621020716860007524414040444610000009020385102602e04001e003051000f0b81000c2c81c0705084444005082c0c404100d0340d0b400b800520000d00f00e120000503018048021011664141005c030240c0f960829005852100c0c0c031206401e0107c03c81e0010340bc4000d00100031140c420381071070780403100070801818803130304403d8240c3c04a8a458 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 651942311 1250 651941061 651941063
    0xf080c190f05100b0a1e050d0c06230a03021c0507080105030c030f1203101d01061202090a03060b06040b0309100608071d0a06050d030f030e0102120115031107 70
    0x1140c00341d440c405004090000c1460210a80030034414420408082210010b0f00d104604c401d5126500201c1c201805041260040c2030007403010010840c141041c03091232500344901400b04035401c04203080c00842101c260000300c03ca01c9003d040c0300801c00154065407241c0901c02280489681901c40f4480f0341c0316607405041241e866100a42c10708040c145447c4046e20041c2c03080e80200c0c580d12103031000082491001d411040d01c180c590301c0d00c03609000d920400350445e003000072030354110800e141c0004480c00c0c12941c2a0f620a80414a5000e00900f244155812560844405002032005c240d194020800d414005044249445d035540703080c8015420076210404141c1042144480c01d6074a07000700c030041c181071805401d0161414004603001d60360501900f0800042d440000d504a40d6a44054020400549404810040b03454000c0c1000201c000c07000100f4944400c010008005100b0ba0311000022800400c0e142d003407070000c103500188200700c00101a22001c0078507004111364082c10581d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 651943561 1250 651942311 651942323
    0xa060c081b0f16120f12180e04380903040b04030503090a0f05060703080915010b0909100605070204021e0f070506071412070201240e090303040f080c19 67
    0x80002842c01c003840b0700143d00409030001c64450034808100307120030080c2d031190321250186c0188000d8a05551420b025100340003001030280c00010600600950b181c4240c0c82400e007200c4035220031402072900110b104081d00060b000c1c003001c10140c41495060394120f00340400300ca00b0070341e46120256403a407142c0c00845007030300301060042060502c00d008001400c00307100a1404507040c100444c0550090100c00342c104060b06001c144400024007801d82c5000682d480e03014107686600142101c2d038021502d244c0100300303040000b4060780d000394808064035820303521546800950340800c40a50851004044690003441e00400c946481c0001880a1090105a9900c95006007010b070b04100d0020401d0040c4050004500000141c480895211484070048440952144001280107040c0354407441c00e00505141b0a441007480c106041c001c0312082a4070000301e42c0e0700c50701642c4034082941c000b40404142c40321708002407180b4004e06100c0204204450000440c0100b03144900450b2a090350b003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 651944811 1250 651943561 651943573
    0xe010c0501110406020709021602240a0c02091602071206060e0f090d030c140c0a0605010b0c010c03061409090f0105011203080c030f06040c050906180f0a060c081b0f 73
    0x4c940c061240324000d001d4a40c0031414180d010b4528858124004c500921420b003c4c0c02d19804101c0c600142603034810748084141d1940c0e0b5a440c0070740344030307180401684144011740025032070607000c03060704500c440242d02030082c1515203102d00d40821089a81142c08a407690790118017880c17158006485140790000c40031103411300c202d03250b06148001d12110201070801544038842138000e0842d14044521040d6655034551008405043c0a510100100560f0515000223906011380700034000c98a20f10000b003240c0388881109078200c64403845031a03d8218800c07880780540c0b9201900c01e034000ca03d00140c03800140c2141e00b8a08503030090f00900800f2140300038101c14154070141440d0300052004c452865418240200002000010300040c4a00c1d16105036200342481601520b0000310041c0c02ca544800c0d562684c020501d0b00d01964901074407144010300c070149020f004a004036105600d405c105200300703448503941540003070120424202e08030351381c24200004000d0b554941441a000e000c0b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 651946061 1250 651944811 651944819
    0xa0306050924071e091503090f0b04150b030c0405100314030703034a030a08010911030402180405010b0604082103150d06061d07020706030c0503070e010c05011104 72
    0x30481303919950070403410b002c0c80c4500604941114050042d6035100130400142c4403001000c4002d0b00c00000c004205620300700c482c02c1041040242c09000e5803180c043d0040d44500d42c0c03011012601100c2074154954020480d03000d181c00d040d44865044000030384000e0100d0b84a803103911443c401842e841881d60f00003c0d000c0141075062140b490300c2e0b01c610014220140d50209001c5c58000c0030314103214003281c1c3c0303608500b8000c400d102d151058000340e0280d94480445840c090301201013485413103826800c01c000c040304a000f031000c803803003146d006100410703000907002500801540103204403002d644c0c0d03000740019036851001074802000640002c003442c10505119000c000c0114074910b03070600c002d00c2408803a60304c2220f20081c0b813505880e0200c8110135810010301030222980261501000e1240580d94880c200802c1c500c174182c16000c407821540d41329030440441712040d030040d0024105101003200036110305150741d9040c405141c144640c2085443d0030b401c440d503114090000001c0010104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 651947311 1250 651946061 651946067
    0x804110402040e06090a060312050d14131b0306060b07120c020114070c0b07030519020a0b0117150a0b0a050901081216050703061e0203060a030605092407 68
    0x11400200644003941018500386242c0d4440700060401403140d09468002201c070203080d44005c00071034000c041c83d10600d40c0f02c04042c0603076200e136030f00403807482c108401c21904c64500c80056000d044040690451412075407035051040302c40c10a100341d8450b4943c000000720b040c50146801408070082c18940d03446191503c409240703440d0f6141c82c00d01900c504c0c00800b51fa0002018030111802000c4243d6402c07140c9029102900240c010032000b10010681d0001e0550000c054900c2e2048141300b11000d0000b008180d94490301044d009156410b0f140040c88520602d41c80c181e2800e14904c05ca505400315918040c0d401030049408c507024a0340c8440342e1443c2d01e09441a003004110642d4280d0300340d410008420b0301d0b0315103038105503031100000585c6d800c0141d90604003130442d5040b400b528400c03622807400754040d148203140e1046051201c44d0030414140288212800394800034005041c00e440c0da40e5600180c00020203441060043c6643c00300b40007800c01c0f84170307681180c21210442c10719000c0800b03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 651948561 1250 651947311 651947333
    0x52b030506030109021e010c170901020106060203030f013f02030115050612071806080702060f160f02030f04030b011809021c050c040c050903010b01020f0d0c0f080a0804 75
    0x800e00c0baa04200210700580c942e4054950158560414441c0941d000401a0380e02c05043c5401801e81c0c4103500307801d00c45809603010300b1001c08264000d01c51980d039440220395900013554011072801800004110440117520102c00b001c0380c40305802d540c03d4001c001107070072415251150403004189000071085180a1099200400030160000034080c14000401c000b40504180a6490218030001c01c040e980910400c030300b581c6219980d016102d485402c020310044080e100e2102620880780803400c0244400c040ca0300c02c4440c501c00414a0726080c1048801c42d07115000700c0b040d408100190040303000c1980050018500450005c6019403400300e40c0c4d04007a0b8040711000f6410325060041e4016a511541070900b4907902803104080c610f20f0810300c0c01e01c8082d0f130301d0716881450166552000c07034000028002e40d480403030082040d940070310016078555a4404800380c3c16049118201681401355002655003401200e904100c04c20780d40d5000f0f4164804404400800cac0b2a100704000c0111034411 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 651949811 1250 651948561 651948571
    0x20406210c061407060b210d0305100b161a090a020f060403171c0c20060910020a110d05030103120923030f010510050a120803010909052b0305 63
    0x302c074049014065054180c000d9100082ca0580c81b546240e0003075960f0040d903180b083d0066407001e00030045802c19039a805590824201103804e03d00080d0642040015220454114220351440d105c001055540b0300741e003010003290017500400c1e10101240f900001c44d8410501c06e8020541c1e4555401000700d100d0500c2c82d480e102c0c010400c42400000c10b6641c10b42468403400c04001d4039000302a03031107020503805510b508199071520a0840307140e91300c03d291010380385003003a40e00034a29008440d10748600086501c0c0b03c1c20790142002a00340c0246a00030403960005103030110102c03c1340b00e0601d00304114603031042d0021b0710110050061000ea1914904060b480b424002c08991621703a5000c0c0c000a2440180350300c0150590030415030301e081c8040c001c0700201100800413481d111010315070b02c1800b405541d001c2c409014010810030701034035405001c02d070460340c1c0c5404c5078039004118001d494140c2088515002e145074001c0400c0009208800080940d96480c01c100d01e4030720001c0c12900c0c0100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 651951061 1250 651949811 651949817
    0x90a0614100215150a08030c2e0c0c060b0d020d0803070e0a0b040602060c0408070302060703051204061d010c0507060b0a0b03090601150e0d022b03030504050c0d050d0804020406210c06 81
    0x702a46010000031181c608418a209c00c0740248501d5040b540d2584c8000c0a401c80d0034100414a0302e91607001c0340c8030711034902c9600f04000e0340415005002e85500e04c200003d4021043c02c00c14800300e441200659403040f0549044803003100302c20040340c20b03100303aa400030300d040350301181c240110380d0148000d9600c0100c0303607500d80c10f10f4980180960b50300d001c3c0c03001074010680000d20742e0038507100360121085d403044600281d0490500e464007030010100e1031103d020350bd001307102ca000c0c1c402c010b00a00b19281403940d0307542e041200c15143e00d4014411186015880319070180005070705c50b105400707140b00c4c61040015181c19850500c0c1c042c00d04221a4a48042000c454080c002903a51441081115074040d544200a420022140b480c09580b030040c0e05110b20414002404142d03168016910881c800e4003a40e1035441942d09101a070802d0b9000141650040d840e4071003014450840030342e01900040c80441c04603a918514039400c04480700a141490445031540203101001000800500040c6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 651952311 1250 651951061 651951067
    0xb03240102030d020705121603030b01030614040b0a091404050c0303090d060c020c15070218390a03140702060f060d060207080d0506090a0614100215150a0803 70
    0x840000d403a449250141c9481c81ea0124201c0706010080000f005034941c0d000d500b503503c500c109a520103a0740501c1e000c03400642020500c003506d500c42c2c050b0314204ca000892010724500e001d0204070107800182c0c8803a8000c200b00300c0c0090b06080074040e84414910b0b0090b480964103050500c01c1c202510006245d000340e10030040741c0c03284c2d2107d403600c00c0d4a94003e20002050000c2c1c060880c00c1483c8a40e00030b5106008254184520a5500041000c688221128041c07003190201b28410030004682814078000060a5492034070b041d1003285901c00b540c503540c560400d81e5100300e04500c1d0060315041c40000d40e9101800e106092088081e6004007690008180b0341c600351502802269009241f54050080503240d00c1c00c005180e01683e94060b40700d80680d46035000000d0304c8009000886e0000d20407900d0f003000c40c1c1041e00368816501912019140e1070040310b15041400200e440301300c4501c08520504c1e61080300030102c0c140e00780c010403000040744003540003902045441101c5802041c1076030410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 651953561 1250 651952311 651952381
    0x807020c01030209041b0908010b121e0307060608030d05011e0510090302040212090106060c0b0a020714061602010e010605090615130b0423180c0d060b03 68
    0x401040400091a002d603551007000c000ca0081c082146c40200030b80043c0303080c10341e1960002c2129041d00d026a00800c0054154400c0207066005084592965000300d803d0b01008580c580c18240e04081c080221707494284540e03030307007002c84509034020700c0b40390008600100301c04009c0c019180100041e1034100f11072002d0032410519008a80b058520903a116042818402c1c002c0107001c0003140c00500454131800c00100c040b0341c180c811200c21038035520340300d000309203540100180002c031600300310011110f950b4440e001000b940995402e40350001c8100810500c04070030403c683c410541c0c5810941c6503c40d204000e070070b66810491640d16039060540c00c0c000c80e102c144066501102c100c035010000846186807080303502c114030032128040441e1602107440e40c00a80140704503480050035280111034000c884400c9995110704030b5200a0414110308068144071606800c504540c1c00b187c90200800c440708102e035180d47c014001c0c0c0e5404000c0185440c1560300d2094030107018402e40c10843c00c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 651954811 1250 651953561 651953563
    0x212011e06030501060e1e121b12060c0903010b0d060b0406050604140f0d0c080a03020c0109030b0f15040c0f030e0a02100c21091e0b04050f030f0303100312080702 72
    0x4944103005110041c0504000307d03456070400c0d000030000d8184120340d0b2940440e0b9854901c0160024804c16443c16501c2050410040c94052a003100000d89034580700c50b0007414555205680b4154150f4071389104610a503a4081c9240c01d061007088002030703101602c1c003841b09481c00c0d07602c40752207900280801c0001194100244ca1008003c5034400c0381d809040300010303910700300e003500030340070ba00800c0b0702150300d1400003940d003c2c40e03001e6000c075920310341c640e001110b0f40051408018054541b50010420b00200090344640001041d001002c0703ca40480114007100c5c0c02d82400c000042c54268500324064152285c000d00507800d001629000003250046000100c01c49409070400c1400030500c01444518201c00c414252908a506084441424014201510343c01580c8a8106410307000c404400529020000c0b100c0b8800c035141802e00c0d100403c044011800c9085425000e0302e040051074000c148011446a07440d00500c0c0c90300d904506100e9040c4590310018014401144184a14035030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 651956061 1250 651954811 651954827
    0x8031222050c010309080706090602030f090c21030d0f0510080a0c05240703090302040b0303090a0621021c0c02030301060503010915050303180102061509010b030405010212011e0603050106 83
    0x10b00b82008541d44034146030080852051010180ca41403a0001070f0040101580003907000d0800401800d0490b140c0c6031080da2038020340e0300348940c08000c100c000c00500b810b061620518804000607203040c0004419030105541400300200710031503a540400c18100c2c800a1424040e190003402450500f01c01d80c2d6203008035000340a040c0c0305030180300c508440e111210180032580100b441c407040c2c039014940f60140c00e035446808220310035070030811000a203003000020f440044800420f52041da9280040541d0143c44102c1c080b440d000c02e11003514681c01c00340c0000e207031003584001504000c09101281c1000c41d40f09125000071034000700010400240d014003030300c2c1540d08860340050000c01404800701c40452903071180d9050b0002040b2412149449501081003200c20303020340341c032070743c40000d0118510748601c442c0341d02120f40340043c0003044025010b1640b040c0715500052912022a41741d030f915245c264422a0a1042e01400c000b40600c0c1814000040c0f9440c1010b0280d07504283c07014050070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 651957311 1250 651956061 651956083
    0x503010e060a0807090506010801050922050c0402070c0302090112051e070905010e1b1e07140a0b04050d02060f01031e0c06090314060f0712060803122205 68
    0x40155020900720796840c080341004094003000c5076403a0b60344d0034500d405008100c40032404541000b000050303d0074607003410391180d100028044040c04c0b02e1500c0c0d41c1902e19404007914281701c1d03941d5000e400c0c2c0f03d40c401060460b00460b810f04660b49075104201e45250f050b08008600002442c0f00c1001034070014000c0340590040e010a101d180e00303c0d03172141c64884150b01c040c40e080e080c00000038503d2244191a8082c524100e43c800271510745000421980c0320381164035518010000802e000e504800016052003881000c49203803094050b0000b03807411254902c19206041c912080c44200041041740408489590026181c2131404203003e58460740148809008124240c0029100110260300450043d5000144081c0d141c0c8502c0001d08072400c5000c200c8960030f40ca81c00d48104640010224410014100c102800350345d462400c403201030700c0c1001c48845d41d0711110301080a0505002500100c03140410308116454485840d00102c0410052800c0b1a10b062a012000c00c0012074240502 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 651958561 1250 651957311 651957329
    0x60319051e0402120c0a06080a150501020c0f0121063002010e13050118180f030509030a061a18100312110f0106060807050a080a0b040207060e07050103060b0a050301 73
    0x100c078001102c103040ca080d0407080b076400300005801003241f94010b10024081c022190080016004a440740600710303156000da5030142c0c0c8a54030300c032118034185500504103013061401c12181d4200203000c803130f0810301e40b1840b100386840c0c480907c089640c032160404600400001c1c03181c110704260a54502078545c040c00b9042041040d40c2c46c185031030302c023615402d0b6210354104200960391261a4440c030100d5490b40354002c2c0c14030300e20b20580164528540308194009150303050f0144142e80944466025190301d07500360241260000101e40706100e6520518400c40203004101c8100040104151f00b031a01c0380c00d4461040244074825140c1240c0400b0359138009040004420340340780980301c0422901d45800380d0b110341c200c0026a12810b401050841d40b460b141c00c041034650180c00c1e2820f004864585d000601d090700064107860340d582000b004031902500051600800c1e440e803205840300c2c1601e4812550000400704000c0d41d1501c1606c0c0100501c1035071f103050042c0d40c2c00040a921041c46100b41b1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 651959811 1250 651958561 651958579
    0xc090f09090f080304050a0302100221060a0b0309011a04052721071a0c031f030f030c050f0105010503030f1b061f06030c12050411060319051e0402 65
    0x3040b050401c400822904540020f0702c83c54546040c80d51036041c00000c81c018041d0300340b01d1002811600945840483c00301340002c3d0300403600840b24036018020500b031f92241d0510800200f019003000210300640701d030000401c1030070b824a49900b1481041358501e000c1c42c64181009000328054041d8102550b41030b41020004031160019450840840b0040791040c14501c50500c07c5810300700101240f0307208900c900b0700044c28404140010000706c590b050341050070400294840c994606581024003040000104152640c4454020140b980c800714046446601c4400030302208100401d035410071000280425030400b8003184e281d0040000d0500d802402088044200e1060346d8444409400c0038111400391406d401010380f0364105032010012061034240104003180300303020b2a0394404103074951814111041c08501e00170f0100800603a22115540d421594503526000218001e520030031488040ca440b000b04c5404591020b800b0741400640200300c0e03083c050300002500d0b8407540444040c09 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 651961061 1250 651959811 651959813
    0x70e0d06050604110a030f150602071e0305070b0c1009021005070510020a05070209070c0c261e011404170a09090504060231090f0f0e01020c010c090f0909 68
    0x24155130040b00900120224007a07144035456440400300c214070074814040d4404038090f8203085000e40c0500b40040c3c0241c402072181c001e1800580c000452a07007141088607541e07881d030b2810141c1a40010407101d400040182081c60100301080701d00040c1c1c0300412198205900042070340b080052000c0500c003003c81c40c00d085c481c0c103200f04403004952a20540d90b50305042c00050040e401100200d04c60411080400c1103940300c0d0b040380449903441075012410790f040500300c3d400c0715400c440000c40c8198045040f00382c113209000c20048038038491640700030000c01c80c1d100c90a43e00c541c101446000364080030032000c600e03d10101050840c008040e80d550300c0c81200201e44480c0c0c560449a403550030f004c1400100a4658000e190915020381764202c601d400c010380258403440041c003d50050788902c010700a07161942e00c40030365015540800180204d0480c41c00381591600b4841d100b1036540880c00380d8a0280c01c1c05203040862080c40d046403032900781800b11240140034061800707100c0e030750f0100b00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 651962311 1250 651961061 651961069
    0x50f03131101021c0305060d0812010905090a030905130912080f0c0a09090209030309033016061d0f0708120301030210030902041808031b0c101a15040905070e0d060506 74
    0x4031509d0f0002c00c030b00d03070320110b0075840308440e10207100302c50080b031034400052242140172404040300c0c5d038559a00c20381945000200450380e01c04101c40d58101d582d4800c0c02001440138510540d00303403050303154055a8036100040c018401c8000b400036512240401000502c950f021a840d03050300c003059401a1a506044040780c50350180450650301803198004d10f03900c5400b080031110314400501c07242d50401404d2864401280111034a00c004108070b100780c4d1001610a400c4050802c504500c030000f101c01c4811080e192001e01401d402054100e03c04c1448500024401c40e0314038141003428500c1c65146030b01262800601040039410035603960115021551150040c81007004641c00d18000b107009400c0001007a4030039280f5a428040c00e400484800021000f590825420384004d0042032840d041038030080c000340081440214241020580269079a4407030f0f0f8600f005808042e40c82c0d600b080380410032207001821240501c904c14103c0b4a042e600c2c2c3c3c2e80070b5802030b07002001068a8480b88041 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 651963561 1250 651962311 651962329
    0x60c021512090f2b1b061806060509090303070c0302010e1006182a0c05031603090609030209150f180a06050103050112080a050f03131101021c030506 66
    0x400c07801d050800611001d2640000c0c0d4000724408601600d41c00352030210b10503003013803000040000690510101d18081c2e80a00c1d009403110250b40c4039860340e0051507841030300701c0d168000420201c1101c100c1402c203010546c81454054001900c6402850400386174087e604e0000178403100800680740095802c042c800c0d0000d09408080d5000c980d030b40302080c9513400c0980072600074910054045810300c5110f419a02448461201e0008003060b954905410400f0441840c4251018010792080303603030004030100300400301002100c2020b0340032055468000c1c0481c2c0b07107a100208001c0000c1090015948141c01140c1101000000d4458605580042520b0369405c40d1070643c0230409010800391191610001031080d414202d080041c5604c40340198110b917800c0c060160b4030740030355000c64000348103c4014010050b00341071160806088007511b05083c0c0c81202d820300310b045a242070f041042050507441900c40f0090004d00b008541d280c42c080c1200700c0da005040304240d101d80108026803903170303548 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 651964811 1250 651963561 651963577
    0x3040306181406060d0212070b030a1a10050f0d090f0b0405060a0c05042903040c050f040c1205180f1501060e06030708100b0307030b090a0501060c0215 67
    0x200744052456201520002115100c09541010010940000d070341c40c0412660310541000b00300180355a0b164092001c1c94030203064450a1348a00400031600c11100000385220300780414000c0359007031a1000460428400c480c0084c01000c5801d5408580c94210041e83c500c20f01050115403a00d480000c03882c0600016032001d021400ca240148060008141c207c0c1e12441c004e0b41111000c0c3c495420001c00c840302d111040000403c184000c8c0106540d01c0c043c5c0b1070220750f401c20b80701e02c80c00119103030b5010f034401c1d6402c03540c10f000130400300000d080200c1c1226200078211001c0103140c40a0342c015000903402001d0710112540c4d10001641d118010050949100c0034604035103d4415017443d05541d4801d4005280038100001e000082e583d10541d11001d8a001c0505a281540c0303454070180c40c10200945050342408a1490100e20022040e014620544d03a542d40425580441400d01140715405040d580c165814030005010458205185651580e410340d2030400070803003041c0b602082e000b1041c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 651966061 1250 651964811 651964823
    0x106031502030c0d06170f0c0a0605030a1d1f050c030a0902030703060c0905010e0f030a170f28110c061b0a0507050a1e06030504080c12031008121803030403 69
    0x9000c2100356009000822401b4404200c030000307204035080c0b50392031500301040c55018560000a1040f41c0c8510041c541101c1030040c0400c441c4658000c028100390394002041107580507580740100d0080904a0040001442c4403c011506114542e03105034840203100900c450380b500341078003c40d04d041048600543c2c0089081046064030320004100d0001403055500040503241c005a483c54155090700c41344030010f0080441541d16614081c1452201181c045040c0060204040780c081680051603a000e40b07207809010550b284607141808424654180208042c0708400c41c41d142c0c0009602209100c01c40c0d203191100000c52022880d00029010408a4060420790368200700000454109035041192048242a12100d002580400c900301810454031804010420140a60301450700180510403051500c480002c00504d05100070010381c03c80780c0c00004102c4038034151224000680081c4003d4004e4460441c804003550207001980c1c1410040e40140c003419580800449009590201c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 651967311 1250 651966061 651966071
    0xc030e1503060423060d0c030506040606260c01050d060b190f0c11040b010e041a010305011205070b160c0b03011503060617060a350106031502030c0d 66
    0xc50210341081da5910b001c0d50800f4119420050300706080c002c00c41549940080c0c030b5682c1400c0000703292203010f0079030310303001d21083c0480819418065035204501481020919a2802c8031180c0c030214220043d1003203090b10300e0ba4402d500b001081410080c0070920f0f1042c0c44d21044000c1d0710040c10250b01c40d803021640001e0659915142101554146034a6141c150807800020001d0b110324545545c010481d110504d000409032500d540000701c18001858003a50742c120b038502203002c80b90481350341d1000628002130342c031360b541e854011140988698510a88054000d545403555000a0f0160030f400c0c0d440030610080000d2022405804190403240120b09960354056070780b040d80c403c2c055141201d00c0300c1c14100a282c0240580b40440351035a0f20040c3d6000d00d00401042108007230302c100d0b80f00c905154001110f410018841c80a10641c07055410300040d181c18180301000400320450b0300340d060040420104609401d21201c050341d500000d81c2d02d940c0c20701134018a1003000c4102c51818985 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 651968561 1250 651967311 651967339
    0x4080109060b03030a08160507140a0b090c0a03110301152403060308030c0309011514011214010b0d06090213050f12071406042c070801150c030e 64
    0x540000240d00c1c014041004445649001d250b1244120325612010a07500c101117021070307000002482e0000c1d11072500703174140755460b40c0d86900031684e69004042d5a0040c0e1401003480140000a60080c0d094802400b0b490600e1000c21800022440083d140c0352039207088496944080d0046d00e0313028140826088005c0d2107910203040c0ea0291141c020307417448507003512400540644580800e89400c00107050441c6d80c1c8000701b500b141d1005109881c035548441548041154800864000d00300b2401244091495100014968000b211200540c0c1d800c02c1000c544051407a030f00c560640fa4405000741d6070340c20740941800a40850f80c024880c007480040d0120f842a4200580e0064583c1240d464148104038810820041041030f4882a142c01030542001116440481d0942e030010141449003050f5450203200c001d11114600d003200ca000c1552a0303134414400030f01113580214541042d09065050580d85141082049108002d0002140442083c54024900c0507000840100381d21031103501 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 651969811 1250 651968561 651968563
    0x420030103170301081005040519060e0c0121051b13090b06091e0406050303040905161815032406031116200d12090911070210050d020408 61
    0x744000e6481141e5102c003801001c1c80101168103d036014001450b490a40c03810120007800d0180c01114648100101c840700d190ac511903151005024001c00201064142d0f103960a0040501c94181008148120102c03a0098000404500c034a01200050380b50368003070741001c61444c400ea421040f0301004c118a00f030141e0034103401c1c003955040541441080f1001051041d82c0c0a03960000e6881042c280c1007503c0f4410340c9880741c00b0303102c00420100742d09035039401007800c3d5402900200b03012500e1f101041010640302403040d0072320720a49424510100143c03c0411104030034062040364035680e0f901c1c21201407081c0c01140d1301820020064040c1c4c0d0303407801c0100341960b60340300e5407003c64142401e11440090341c4003580d801c1c054201070181d040c0b51595507514031107030042005400941080c4514440e4403098884d00200f0300c941400c41c8038003840717003000e0100141c40e804082110308084a15414010540503036920948c191901c080e502740c02081510b4074090b01c14019071f840d00c0800c0010300c3c070074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 651971061 1250 651969811 651969817
    0x5090a0e07110f03190528021c030b03060601211119030b0f240c0709060e010905060402030c09090601111c11030a050405010507030302070b071d0d02031009020420 72
    0x2e0b40322285e9409540340841552180903941501c01401d400c9040314941c6186500301601001503841a00d8104100c010640e14500d40c04850000180c0d9600c420120390900b0000e50340c001c3c90900f08080704054820701424400ea042a0301c9405a480764007034031a5014010649040c50010072503200c554100380d000800502c07841c91a5480340d05804004556411300c907007404502d000d40115099010040805d49070940d0014183d18828400e20000289040451060030007801c01e90010700c400d54509621481503600240003203114920420601103e035295200320f88600b03400b5030300e800e003554806006036141f10f820040040d140c01210014a1700c00700749408413240f4885501d980c40c5055042c0b10382546c034000c504010010a0081105111543c0110064103807613100380f0b00503190000c25035030540c20b00410b50303e0b840411010045c156820b51490104228070300300b81c0302040e842c040c83d00040e9691480060010b449682c07982200c0c151748440d0020759604070442401c4183c4070740701c200700740e56034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 651972311 1250 651971061 651971077
    0x1e02060711031923070909060c0207170601141305040302030a020f07050d020118090c030b0f010512010e0613020c250b040302130212070e090705090a0e07110f03 71
    0x10107403442e4000f21450704103500d0328003600401d01c160320b0000d551080d14207991005000c412072060350f1001030404014060600e459204a1010510000f503807000380c5001c1e004e0300705c04885000014414100d07400001d11504442c04404a00c0310042d82001188042400d0b040b10042141044100001e0640000081c1144c07219a401c0311040c0e28a4404981c449041e0b018480e4800c050300628030156100340001d09860308285c41c0c6000035a83d8a8040c011148910f1407600441d4862000e036280d484c0c0903412485008081c02c00340d02cce1400c0030074084e0515005010b5003140a0560010400a4803800d545d00c0c0007001c107950444d55011510001c3e642c13078098200f545d042880c114480d6903260b060400d000d080710f0104141a00780790455080000c40590710a815455a901703220b802d950120b00c45500d805100396445142d44d10703480302c05000980000816400c2400000c20020f0b16075202e02d510303d0b00721003030b080d101c52082e216520111001040c1e00065800c1348075030311040030122800700c000d142c84 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 651973561 1250 651972311 651972313
    0xc0d09060f0e1204180b03011b0207060806090103051509010e1f05090d080a0b010c0b071107060e0a2108030c0c010e0a121d0306011203030b0f030a1e0206071103 71
    0x1030b1000c0d4201e0703600c071320890141c50040707144115214010683d90300a048900801070000c906801c811150175107003001c2e100c00d20016449480b0030030010341c000340400e0b0400341c151841496507065840f00c695840b8000403e410000a000004a90020039881001c010250030b06641040b50640841e01c070744071590020702c014500d0040402c0059a0004003840a5400c6448003c913643d6421030050041001ca910305c0c0c18083c2e01045480000c45a403041d40c4a49156161068105105114146400d0543d002142031041034042c1a503142d030b81d202c020007244ca02c2c90b1708a0760352261810100c0070301c203a000014400783d4084248494130191101501080030480000c00c640d040c06003065680e4580000f0161004100060a0621510880c401a4121101c207032180c02c544294010038500402640700c524508040c40c940c9081692501483c450380d1011111040c030358081e0310020f5114404d0000090042c50100400c0d0107180051514500140d0001c210907103c280c0d81c1402200402034194003842 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 651974811 1250 651973561 651973573
    0x60d170406020f1b010206070f0e1008011d071d0111030f09031015051e03100b01021603021020160603050106080403080c0c0102090d0620040e0c0d09060f0e 69
    0x244d03001c2025102100c1d20164004c0000d9100e01109550030350490726030741d08215928088074510340b54080684104103e640d55070445601d4641201440005100541501305440e014032050350740c01800300a81c15108038450400e0719545005a49081c0c410010841c1800040344030540c41107030748007400290509a003612200440348400030b00700c0e803c0f40c42e1040030300080c860603c00d40c00c201e201c1d0844200301c0104400c001425900280c58801d01044442040751150041580741d40e05002c0052078404030081000708604690020304040100c2000c6010007286829a243c1041d002800c1c8a1800042042e9201894600d90301c0b40c10f0000740c05801c2c040307802c100001a00d18031442145116a402d940c441c0d01c5500c80d0720050009a011590581081d0b409002c000f5081e51203518440c16588138420028200e04030b641c0c101c41c81d0181d5000d04e69001818042003008400c044a410b510440c1c52520325035074103008060f44018041c00340040d0009140100846000010354006150035250348200c841c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 651976061 1250 651974811 651974833
    0xa0509073515130302190807050f100b0d020d0609020604032108011a0d0b1f030204030b0601080405030304060b1504030312111c02130e161214060d170406020f 70
    0x31800000f4014016841070103003c603c424100500e0103407621420f00c040c913011881c0c03a514a007007600120480c4680101805880340c0c1c2407441001d4a0020a07122002c90401b070b90005550300070818805084642c46100030011591480b089070003540d0300511a00c00880364a91000c01200c18003410400314840e00d0001c2030b401d441846d6075a80600e50590a407429001091070b50152943d0702c4819008001e080241c0e24042040a4185000101e40c1d801a100e40c80d41c104010094806040e4034180500003045c0404a5801301c22254803540004012446003102c00c0440d4240c03a50003101032040720041404420164042c40c0e440503c030b0340440500c501303080b2203010f9005100b142c440035184801003503000182c40300e03600641320003c0d00e0203544c1c101d80c2d580c14108000540890f00c214248890013845400745800c903071142c0507108504401c00980f40c681d00b41900040028007a248980c0e0406400c00800408007040c070b0503c0c6407074001d103480f03ea071858080d544441c65400e940301d030300400038048 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 651977311 1250 651976061 651976081
    0x7031b0512120906040b041101090f06030c0311040e040f1104090605060906300309030a0804031406010b0f07231c020c0303031b160c0303080a0509073515 68
    0x50017503400c0307004200145c07120750320340c510b8814021140d4180140c040d00011030040c0c004030f4800400a5031004507052581c07aa000f022100e28078140c01d2804020720082c0031043c9240d201d980c0c4244d000a1104c2c80300d00ea0308242595500020016500c6410605010104038081d000386014000c2520706031021b40300e480800c19aa05a16500c114054845054103007682d241c5d03007042c00140310358098925007407031500464207201404906031141c01c0c0c005001c00070420709240101000f4680310181000394140510200288903000203500c02140104241061150380361141c41a524070584051a00c03484611041d1240501d08881e02c3c00281014180f201600100d0381841d01d5070004c2c06189550750303c10301c0b0b40e410260381032002c1c1142d01c10b01146c0100040203807013150440c0103c0ca070a141c00d01d14540103082d0035000f482000360ba4200000d11100e428002440c0040d20250340c544a101044030131840c0380b6902801c900c110302e14401d0320310ac54020340400c1055940c400d0440e241c42a94600e00c01e9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 651978417 1106 651977311 651977323
    0x1c050721020d050129040b0a0e130c0806040509120f0a0c140f01180510090201120f05101706130c03060507111e0307031b05121209 58
    0x384114051044505c013141c1e4030001c5491409080c0b8030340d00d40d240604450303882407000e0100309504642d100240b009509010400030003503034000c3c01c0000c0c0013090985002c0c0c040c6191001007105c0c42004194084a410b01d1101989001c012111900d0300e507004000c0c8004100540701a400050140780454007540b43c2d0320300802041c0700e01c05000d070071200e021314660070701186600c50b8000550046031003080030212030700000b604001c9000584001503c042c2c0078070715038a001392072982e1500c04c1e44401d020f00308810912070415101c81604007100d070803d8100e5542d61088002401c1405031aa840c1d211511074201604280c1c0e4036503500c0103480040d02c207400802d03041a51800542e2041042445501c40020782c1024024181715032038a910035210080c0c10000070a54035255200c44159111241e580038040b9142c84105101d102c4031500507140a02e800e90030070002c51074100c800110 = true := by decide +kernel

theorem cover : BRFrame.Cov 651798561 651978417 := by
  have h0 := BRFrame.cov_init 651798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 651798561 ≤ n) (h2 : n < 651978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
