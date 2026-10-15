-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3965
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:11:18.775478+00:00
-- url     : https://prove2.me/submissions/eb0adfb6-25ac-4e28-908d-0bded8701e8d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 712949640 ≤ n < 713129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 712950890 1250 712949640 712949651
    0x211e0409182904061116050105010806100e0103020f0d0818120f07050d230303040b010b030c0901030e1c05090901060905060a182c070905150918010f060906091d1009 73
    0x3c100d01900701504a2f04c05100300c3d80c003070b10b03038210f4410005482d0081c0b107e0100da1000410144c9440002221480c0d0041c001900c007030f5268880f541a0b900540c1c803624041c0030252552100d050900d468401050050003418101c0c0a00d1040b50325202c4038811980300b00f48250040c4244541c0640c0c14400003100098140b80c485646105a200d030800c0310161003501c95500009840e0700814122440707040c4880310310703181010704401035005080c440c1504020340700e05010701ca100440c0b42c3e100001c040035031300c545480301d0003082008030380541600087d041000103001082591503070826582240f9160802c03191484a032904007040488032350007514044170012012401ea10b110700039090041d0b01e2a2002811791306d02405035210100c600c0b03000d0304000071070203242c02c201c1c001c2c001e050b112400501001440000040328205000c3c280c202d0380f1003030b008000c204240c0c3e41000308030005110034208400c5492402000c45074003541c404100a420a01400050b4858080b8058030007600d03006004006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 712952140 1250 712950890 712950893
    0x9151015120b06070b01330309150204150c031e032309070b1803060403022b0804060905030d0905010608211e0409182904061116 57
    0x94200501100310072545000d41d004080e06000b030403100840d40202c5001131603440d0141106400030441c048103000307006500e180c500780181c030742200c400c18619035000c41c07603421a090400598908170075241243d4030401080010500a0401e20000c403000d00300981000c50f18101a80c44503c0d070141010125103a8000c0801d05806610100c940251800c07400c010b55840300c04a9407102059850940d50342c081081000701ca03282400604810300080c4402074900280e0002ca894000c080d50701f100541c01c80424248403401090001e000224814400303000c1765000b0304007a00c020005070016010a885103c090140403041045450208202e0400c100c554841e0030102e00911087c06420824060480040412034140350443c0000444040d002d00e00384d2042c041d04100514003042c0fa000c15010f0000103241840b41c8141d14465040c4110060b00841c60300e0007005140c07000d04400d60958a6210610510f0481d00000790f01c00c0c0d01010008905540121007212030107100390074610800003091580 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 712953390 1250 712952140 712952147
    0x40f260409050411010302210c0f03090307031e140711120d12060605040909050f0d2102070302060601030b010201380607020d080703050f071a06060309151015 70
    0x14403d034020710141c401d8880201c011400c1e4850308108001c010144840c031000b03085c08880321074006500c0041645840d0440c203001d40140c00031154180103070004a41c10b4145a04204070b40c2c0ba400190b403140401c91845400508080402c1110012920b40843c0d50410003a0540e81c06509140007070542034100151200d82c1d82d201910717910380d030000e160a80605c5000519004200554055486082c10030b802d14507004018614900c080d00c684c440c0300f1510142031003e01c20b4401d04902035540401c800f504c2001450700c2000c3e4204030b40c5891041002074046a408a41190000400d18001c02d01480101c0104d01504640d072a03515001242e4403400c1000310914101950104005524145030022100f08207042c01052800713500704c600c51000700c000409490003408800d00c40d0501ca0304014141201d1f100e140c00100044603482507101c125203981103104c28882d480f80f400c80d801440e500d00821040d03144c40320714250030980c5840078041404002a01451001b40910711441d020a25010303100a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 712954640 1250 712953390 712953401
    0xf091305150102100b0d1707060204060c140304030f0b13050303070216120b06090c2a010f0911040f06050d06050f0c0a050a0813050a0605100509040f260409 69
    0x1d809445602045030a90070280502d01e0b03035a0340204004240482c61321000070207001081d540140a10410141d00050024030240015081ca503940e01903040c0c091800c01c0740392990f1400030398564001e0204000040b101c0101040241c0e0040c03189210751520380000a81c4e03c10100b005180c1e001c00301c1046422a03000070001b0040008041030385a69544003040c0302001250b07400a800d425103a00000d0060a10006042c1c0000c2c070300380c10301e00d000d610194500c0c05094442c10502e402100b01580c01106009002e801c0c1254421801004204065900c21100740c00f140d0540e40aa41c070360410268402c030a030b0145004080140c41601d084100c0e02c0d203100101070803544651011040c402049a002c0041d0170b032030800100342c551501d0b010982e1002d80304604008c080c0c580000d503034002000014811710080404e01e202e40004101810300d98061507a0b100c82c4c1c0c010500ed44841c408110104010141c5c50700070a810089500b0111b08555450503190041790781540c1d420800a4001800c24055128 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 712955890 1250 712954640 712954681
    0xe1306090c03140603060103080c1e0a0605010603020c101806020f03040b07020609030a0302071410060f1502150c071e15140609090304050301060915050a0602030f091305 75
    0x82200e0b40300b2810f00da4842100391031264065200340010700016445000900c500e01c801d800f201c242d1420b0040c2115060b0b040c0380611020b820001988080012500401340940b006003020f6081c0441d104406950340f601d410007a56482d01c40b0000030264102900d60080305402031b0f815940c0d000140110401940192400c0b44d01c465000f0000b034000740f002c1455030043e2480700c055072500e042c4510480c0a900166010784112240300502401440d04104940e50b00d581e01c1c1010508514241d0901c0045901d1303408040b2103e44078000d16411a404a0b650a003280e4854824126840b101d4100510f402280002000d0070002002c2c2d01c1040b208001c00c003151131140c1c0d414599030315080702c044160385840580c5003540000c80d0114030360303141c800d001d1ba910482240441e07051540d40ca0020742581c05035444207501c0ba5070f40c2840072802e070650f004c030001307408144e45621f007492800310025981d03c80c0e040e02078800240801c00c212103aa58a828600381d442c0c000061001d400c1070428403844100d1f1054 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 712957140 1250 712955890 712955897
    0xf0a08010c0c110306010501050d050a020f030106030516030e031209151801112a121306030e03120115031b0305070f090807090e03090301020304030314070503090d0e1306090c 77
    0xb483c116a242c0000c020707040e00c2c01039685500700680c0c400400041e00c009806d20502980038404066003408040c00345000300640d582c00f05a5050510360080480507030811b5100301800c0c030303e038a072900b80004100c61000401442c80030066648003400780c00c0c208400140060088468123000720000014410569140354030700030800864104a00950b500c2345400e180b4541040001400d008014040d030510001c5101c1c043d038600303c20101c00881e00c1e80c01780c0c0e000c81140c0200c04043c0503a99152284002600b5075000a40c0f901540303c3c10b03039081000500c40c40300c1c02c4032201d0f49084030307500c41d42000380ba922003001094078081d034000001e4080c00703084688400146280c0b84580a0920842800f8110b41c07001c00501401e0f418048048090700341c42000380c1301c901c010041d0030321680303007440198030550007a40e0004004002c001c508110220140148041040500c2401100303240440c1440c131002c1c00d0304140c031051500346d0220f14840e120713151001410b4179100d0009000c0484c0e420000d1652550395 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 712958390 1250 712957140 712957163
    0x22020a1d01060302030f0a0207080702220c0309200d0816140a0f020405060105120a0e07170312060109090504060b04150602030d0510152706020c0f0a08010c0c 70
    0x10b00031030032404100c400c80401030f2041d0201c1d81c1c595140c3d008000c01c502680400d0f05d00150b07078021440b8102c50410507060085654040415001c5038130501c07590120520701480440400e4940180304d00c0d0314191080c50a03050040e0389201d0b60391140b4905181e600020f0151107404205081c0c1401c0b140750419108030b0004a00308103611400700b510099981d0150500c01c3d00f2045400340070003860020021703410700c0010492100300c1c003100005c1c64441c1002040100d01e405032541d02501340191a48424456955000d0080d0b68003c04010355460300d4005000c12420780e240702c0121502003207613100b4007500d4034010030f000c2407103100e4001041d0141c00f5a4103102158001002c02c56840462207404010f800912071202010310642100c0d0300050301c0540000019203ca103078003d0300c0000d040e003a000c01d00c084051000545400c40000c2d40f01462040c2c601d100349044806515600000000d500c82d13040c06950310026030b9440180e60142038072200030011014000303400340c030b086402d89054800503881c9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 712959640 1250 712958390 712958399
    0x405010501030e0a030810120f1401060b04030b06040204051806010816120f06210c050a140f01140d06030353040309240822020a1d01 59
    0x1c1c001d8043c0c1e10a608000c04200c8200c0c1c408035101d040141042100c4c2a42c1070000a400340c0e6584e090280c103010760300740540305000d854268585052403002c540340ea4180001005a078018100307031409c40c0d8010003007900c56034400e00002c00138420303034101c2944480d40c200134201c29036203040701910441e820381300c0444503140d0440406074090031310000340002c0c0c2069100e100d1010140c010b0300c80c0700c14551007c1081c545604116011490000440c450841d404103140705003d000e07071511000309010b94100019034100031303100c940d03d0361b120442c50140b07000c3d070050b1459920406c4401080c1407031100703403502c07100d00300311070005400f10788007c0e030002d01e14110b4810fc3c2c415902d20500501c083c03240f1101403074102c3c0071a0840041403070318501d011100b403a1031841c02020740038142c4140d00c03030395400311030600785842c1b40c01050003e18552040086100b000c5c0c61319404c90390803a0800c209200d42e50f00d003c007140e078040b0041c90309a80207400019101c3c000402400c1c2c0444881c00c0303601b00321810481d0380c84 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 712960890 1250 712959640 712959647
    0x1803030414130b09190603050f0d0f05030601050f0702132408060603060a05040807060c05040905070f02060609191506111c0f1202120103140a08092b110405010501 72
    0x500d0145648034400001180d09500c0e10401c000641d200c8a85c0810303017a036a42c07a2035003001c41590440c001c0d504207807980c907407841c2d001070800d00001007400d03d50704606101000800c0d4bc0145911b4075504000062040e09640c3e80302d01d03d402d518003900003841404c010313880c02c45240c6600d40d600c10a41c0c200d104040342440012688921940c00074009100d159282448035000d8131016006a03010b030307030801101c00856018000c03190110160745406a03520300d450541c4040b584001c01c03081c00c0001030a83c0600d450303030102d0420b410600440d1409075a8503120002d000510000202590b01842d041d0201d0840300210b40c3c00e0201e55036900c55a40d0003490441b841c3d2606222035550b0301081401403900c032024042d0104520140451800c42c021945d200c081004a9020030715201d0100c561000420820229102d4220384100c420080d05603d8000d560700c00072800ba400d165881100840080c5442c0b801c00e004182c0c00c7c1c404154040b811100700c3c1090000000c1a9002501036803d020010819501 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 712962140 1250 712960890 712960901
    0xd0c02090c070f0b181603030f0c032316050f01050f0c0307050708070b0103111201020406050a08090f0d0f17060d02062a032106010801050105180303041413 69
    0x421500c00fa588245540d510030300c418000302400302c1c00703078804c000008901040044110034060504101001c0341903080180c143c4003880f016604200c0b00c1c1c540103001a40c00703118001c16292000c00900260a008900c1625019240c0d40311a24002c04400c4003c2c4100010300c1310981007000c000300425140d04000d1620700704215101c20124804101086d00c6d00d10803001050307407e00511740981000c0482d0340340020a5421ba02c20707949441007555903502c5240c042d07000700703122400e08000c520b010b00c0c0030005010381c021090600c00340710b811400210500011300c00c1c01400e15049061304c051512503440608403401200c41e0074000703161b8010032001150040c0b20b02d4028100100500c80000c829030030482c1542c4400030110340c804200e01c1e5103203208540d40f05074049844450246032603c150211312000740c1c5100a03c24060346c901c90601009907000302e504c17419200c081c039000b40d880c00002e8500e84d00c01c001745030481d05484000340014840410b084c0501081200b291065914a280b5000e07000b43d42 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 712963390 1250 712962140 712962143
    0x51c020705070302190306090807051e1903020309030d110d03020901080f22120f02060f04170403150204320f180906060406060903030c230d0c02090c07 67
    0x2d000c03520500241c036040d40c214050800643c00302c043e180d142c1d030b151804e40c3c0011108940041c000f0a119040040038400d8041003000340d884200140e103003008190380c07040c0741c0e0b04000c07100605040840906100b4400c88681c24406400c90704c08030f070002d600030007190112021025501441c0e00000d204c0d8840d0003243d03440308050351815038503114001030000c0c131000a080303482002036841d0f03e260b20003030401001012030300501c0743d810000070000b405031500c40c104215404540049007040250024000301d00d03007041e080015811042d4a21178840005d00c2243c00244c00003186172243d0440e913511350001c0060b034800407107841440910464000c501213070011364070440740000c18842c0b46410030710800512a240140b41d6010400200b8202403070040a03104508690400b07801c100d21400c00f8003c0200400c61440d004104600c0c41c1c8000b020140e6015004041c0c821a000c5000300e184813a4902c526015501c0c1910138925501c400540501d0200c8012401880c40c2000036100990340d6003507401d4035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 712964640 1250 712963390 712963393
    0x4060206070509060c0a0317010603140c161406070e0427060f1503060605030a030203030a1a040c080618010515091201060b0409050c160f1110051c020705 68
    0x241c55050702514140c005003082d6400034030511081241200c03c024180303e842c0a91900c480d4000ca410b050303801c90700160004403d060926002050081c00700340b5655115000306103040e294100c2c481202d0381c070f00d00c004001e0034a1035116140d880031140415100d0154049448201c0355000001c103100544202514600540d5900600081d4140c00d00400048861080c00c001883c10080103050084524000103204249023000d030a004014582c4180006030000302c008000855055a000396a8440104030f00603041c4c40c0c0700000402d905070b132844010884020710501c80349601c038074018021001194010312039007a020500c01031840803400c0c01d050721409081030445020b08464114150700031207a080c2c00c43c00d5010603011026081c0f0500c1c000d40202e03221645e0f134034034085010040d20000341042e14401002c12980710304c0c9217400c04003100c040e40203c01c0c4520030719604140d000d03a94100b140c180c008084060590b00307280d00c64000d0200b00c3c1001035100385104418000000c82c0908134008019 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 712965890 1250 712964640 712964653
    0x207080a0b07080613060f0915030c120602091302030405060a051014180a0506011403010608070c05010b0406081c0c02060a21060b0702011205060d12032003061005040602 75
    0xc03521503004150b00c1032026100c68016000600c117601100d0155000c01c1104034003000a01c41c2d51603074001c0b1041400d8024011181034203503120f5495140c124841c41c80c0080056100d1000c1001b10713010780d50b41078001018001038001c03003130140010390300443d421906401024000389000803188103041c024820240040f0308181850a004242c00d641036079141d000c64485c1c03843d2031560900214038880c0c03001c4000891103080078400544101d5602d181b1702e1140d8010700060104e10340c480041070b84049145007c0d80404000d050090052400d81c00680d007041c1448000302382c1c4200001d09039896105400d480004441c41c6904460003141d5440007540721504005000116100d942c280a480100c10109001d040b038107040401218000c1c1e00070040c601010030500c0941d030300805418466510100e05000ea403a04000241418090310002040485909592001c15200e0b611041e014201d4041000021803000c0040940303800c2166103520a411090076141200d10134419542102c0307aa4005082 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 712967140 1250 712965890 712965901
    0x501080622180203071d160e040902010c020d030804022817030c0703030e03010c0e030a140c0a0e04150c02030703030f0b060a030905010b0301020339030108030a0207080a0b 76
    0x41c0c8038018602d03400040c10034402c0c003d650103001c58001040e217841044d0300c0c020b08400d1921401001010403040c8440000401c80c0320342c119600c1c0100f40700440e400280891030b03100580d91400d80c01e0010f0b4000c51110000e00800d41c001001d54051f500231900f11441d0480c1399008020100303106108100c81008070004c0015140e250910a1242000c0382078a0074041245403a524000d0190f0085c1d001414030000000642400c0c0700300d076440440c5280c844040350641012a80d50701401400030011502c2101c0800444030074801004150700081c068a480c0351351f82c01111101e0002c0c0c80503110511a10a43e60300c41c00301d403244492819203900610b05003950b1341c5040d4000e281554400800c01d481d50001d0310103548402c000c0c8600729403605c0004498a15090240c00c42e0407190042c2e009078410010311102c5100804030b655002c00889200d000102980c0c50003901c500f40e403d404a5400c00400081100e00380800a848482c680398200c42c1079035601c203070480d51100641d4016044011b20404500c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 712968390 1250 712967140 712967209
    0x5031f020714011104140607030c02010e010c0b0c0406020f010c082a04030605040605061912030e090106020a02010f0302130e22210e060d020c07080f060105010806 72
    0x2039198041c0c0b9422018044401d240c82c03d40c0d5002c0f0421143c2040014148529150099512041001a40c160741000050342e00940400940000603051018803400b61006a1240801e0540d55030301101381010340c14a10b1200c1800c1c0c006001c0c1c140036010703411200d5450b0300e0501c43c024001200b6610003800e5140d1081a01c510b0582a04c240c2c00140f00c000c0c114040704c40100240001c600c11400090cc41c90241009411100050402d6208204154010000383c0b0094045015120070030210036540c20249001e0701e03907034451032a260b040700201c80000780c0d2640220310078040c18001c0e2580b861084d00c60108a040784280780050a0b40d0f5401001070000d00d00500e0b0480d4480d084c20740803941c20f5405c500c1c030742004e080d021003101c0c07200903140c109c0012181c64840544068076402c1064003d00581c0015825008080c50070320100d03404103111464801c00c202c0c8000807d041030585911041240050b9140ca10902455002c01d03090804030310340d82800720700c0c0044403020342c4016110920f52510003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 712969640 1250 712968390 712968397
    0x4080a08150d11031516210903090e060906030a0303050702032521050315060c010906061e0806180c15030103060b1c150b04020d0f05010617040303150b0408030c0705031f02 76
    0x8100c60303212410000707c4810b00c6186061806074880c000c40c2c0d0724041c084101100003c0c6a40e000303840d2502880a1524005a60400e0f030780c4c275060100d072656801c1c500300d1441c0200a69100300044100038020f001c880c81d442d004505001e0041089a0301c1365101503450313001d00c202c4c0b000c001042000025405035000900c02880704008061320f140002190400e820748030070900580d01182e41d4030f01004400d003910112000344c4d007400000304005190501c400d40b580002441d04109401c250004004000c0a002ca565248402071003034030000a00c3e0700f2000190400d01044890324035228003e040c0d07280c440d0720402e00c030180d501920b02c8a4a146e40c0c5e01200c0b521184800342d01600c8910b1550700781d84034000703000303280c0c0b00a10000350308211200070000c0c2c2d50f06901a60910058905802c0c1c411044890258030540506010904400602059a5520b69507200320030500d40414085050700c1e011000300080e010b14011a0382090b160070415448110501e0441441581c1d004e442003080d0341c0350050b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 712970890 1250 712969640 712969667
    0x30e2b02010903300203010803030711210f0408030318010606080103081b12030a020901140f030c033102010e0a0f090e0c130b0109060804080a08150d11031516 70
    0xb5041c42000000304805e036002a001450184c001108009400394010841505c0c0f0301343d5070007408518003240900c96020300100075000303100d0b00082c101e118240d4287c01c4130014000e10048039641d10b0f24000f403174008c0383c29038a4031189508000c0c0008240344100c03d0030341a82d4000c90058030f40740c0480c802c901c007641c4110a140982c002c1154640d81c0114520142d80701c0d090013040542c1d00d0440c0703400107000052428041445240c04e01c0128119078000090f81c2d440002546115941d4445070402c030301400011000040b900d030032609141403880c0e02c28084e161907100703894940070702001c00d08004d2042d0701c83c0035507140c3d0200d20400b0490541c40b60400108020200d081e584202544000700718491341c000d219200c000e0f01c5612419035540e0201e04503000304842d261161540c00d040e0745403091841240b02d1082006950004140840311b034460810641a0081840e04490541d180c007070b000c140c02c0350807140b080c000d000301c8903c1240703a0403505200d501c0102d050b13900109070f0030060325400c03101c0c0708 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 712972140 1250 712970890 712970957
    0xb04170c01080109020d1401150207081f15090504080421050c010e01180e0106090b03070906080a0f05040b04020a09110405091b0315100306051807030e2b02010903 72
    0x4401c0580100c401c03250b001e0000200c9d20b1980810380200030780f4000c516031200046520449a58050b00070440d840038202501040c04603100d60010356013402c07a5104e81101c40c44a02e09800c0c04100000140140103c0304072441c10b902c1000652400008031245010260090300301d00003082c4070390310441c0d4154040005040c0240150f10110803c4144112504202031440200d0014800d440d00115154010301c0300c2204a450361078281e600803d070f05858461102400308840200b51905a00d0308403504e0704c400c0200411151501d42056035482c1c0041e5410390294008543c00b01340b8440c07034003551034030b000c111078202d207400d140500b804004807005041c0c410342c01954040c810074a030103c009501411480f001d0307400c6000d2101c10042491030407a9080141840c00a042140351107610000031490032001d0101c0d040d0f0b40f0f642040e0003400d007036540c2910358003821641c01c40e01d5a000215010100d20708008000395090440309a00b01d4481c180c0180104603c0341d42d81414003d1454072080c0500101d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 712973390 1250 712972140 712972151
    0x80703110f10140a09020a180b04020f0d05010b04050121020d020f071109070807050c07031e051905060423011b0f140f0906130b04170c01080109020d 66
    0x580780e08140490365499a03440e202c0c070b40d0008105010101607046410a2403c00424a00307600240101540d80b007048102d0301046d188002c0c022155110650303c0358080c0c025591042e00c1404026254020101d006581d13107042c00107d0b0361001c0300191403d032881030b120765480c605542032030318856101c16050b40c0700c56004c03c190703100e2420900207001c2c07642902d8500c940311000352408500507500c49002c0e0f13004911035810011616840203555400190500b4076568070b510810045040c910190000fa0824100c011450b1480c1b486800c0007102601440c2502c100001000b0202d0f40c0400038000039100c1c0d400302007c00c0200d0380722191000c4107906a510082080c5c030380031040d425030700341000c010614001d000021084a401c80e82c805000c800c146400040008056500003a9020b45040f00b00a40e00106030380945403601c0003100c901051a040031111281e40701c003049810791060050940e45150600320081000002542802c1c001e4140c59805a41c2e0030281a40003c0d00056042103c451310358 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 712974640 1250 712973390 712973413
    0x105061e04080a11100215040209091603080a140405030706030c05120a15050f090a0c02071d1008070e0c030403140c0109030e01390813090b0d08070311 67
    0x20042c008580303100e003015038144d1a01404005500340701404031015500302c00c2c1114410a07004950650240c0d045428620700d803501c03d0700900c0c1504c4042840030400ea04400441885010005003004d04e4040c2c0d95441040b11402080700e89001e244107598141c1c0c000003091026502a4000079080d40e03c80c038190b0f05040c2d81d10684a10b41c5000e480300400640e440084a0f503451070812214041c01c03041d203140e104403140401103400100300419440c805130b40c8401e54490700d4400d00900b8010042e40c68084032401c03403850701d00f210040903610b81d44015856080080c0001011605004035000000f06000d19510908d1034609503000910407820842498007030301c1d2072031454001d0900e40c020113000280401d02850041c0c040203180000350305004603101d28501034408880301c2c5040d0760103540403088580c200d00840512070320810006003100b80111700210f0114090070030504490048a0501000e016203051000e1062080c1c000b0b0101c0e4410800c0001080c00380300085a804686030403a400040d89 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 712975890 1250 712974640 712974643
    0x201021504111e09130b04110303160303140f04031d0d1e020312090a03020f0f331305010e01020c10021b032b03061508041203050105061e0408 63
    0x440341c40000c01d1019a843c1003490900400d26580a14080000d40c4002d5031a21158180400184000c110302146210031b100340c0c40620590381004880340021741c0b00c510301d10b00680030b41401429084078030210000540d00d02610256103004e950540c072401c2e1814070b441e2100c1840c080c07003030066800121101700030001402d040300c0c440c0e03404401c4018180140240c810103050021a04184011880a02800c805030307485442860032241d040b5480c204d03c08a01c4003140c105c000040100b0b41c004101406541508111400c80c040d104106251590031055180c1107851402503002411214094440500c4207500901c1c043e10352040c140100c0c3c000500320400aa65002e1b4181a04016000302c4480c10366072104821100250100714040d000040e800810304800d6019560300703260150300310303400c5090140a13500000141100d20490505104c0038017014100c41410703182200c0744d03061303190034441180c42485000c0c1a00c000804407841c3c5414a1290100000380e1035654625210801002807580360 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 712977140 1250 712975890 712975909
    0x16020708030a0c050d080c0a0309020102070317040305071e030f02030c0310152916080c060103030e030102120c03191e0b030304030b06011803060f05090f0109020102150411 76
    0x403560748400c0049511320b462070912000104200c10301a0348010311104107041d0003910083e501034900026030440c3c600040f89002c0d0b2561000c0e0984800245400306500b65200034000c6d28040c00c2100c207039079990301100c40c004843c181c94903159005440305100240c0d80c1c0d50852a0140020212a04a8640c000103824864641c050680255940c54500100032182030114024070241c1a1080c041d020405060304c100e2900344680f50820000404044040b50410643d00594100341c3c1240c54001c0000456519030081c0015004150803203111841d51030140225144500e4408555140d525a525210200d0704003900117508281009800c81c03040c02d5a110360f02c03907001854650391801031018146000c40b0800c49443e402500104802c1c008a00c2504010f81c1000c001c0ca080a40c2c8143d1000300e1078114510b42006001c2400c0c01c0000716400c081c0c1e00082d020350b0b42c020a0b20303a1109850030aa080740d48610000703015821244039040d00160400304aa4001d0107460f06980719946000000d07104030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 712978390 1250 712977140 712977157
    0x30b150d02092505280903050a050c01090b070203030a030c051b1b01020703080a1404090c0c1a270f0a150606020601050d110111010c030e010b03070506031602070803 73
    0x841c4541d07000e0941c4041c51149290b401c441c03c08601c1c05170004140c1d217032044510105030581601c0c0004400c4148121205001580c100080da022507006152003503c40003c561007d0000310209008502910040e08460f0020b178020011442c00300c030381e501035000e4a11005898248501400480c4405942c10113001c08010000090003141d0110301900c2c04604032a40c10604560181a05000142e04601240c0c4c3c0c0c00d1281c1400600d00d2028003180350035200e5500200c5109003001e860f030010755080140703412998031030700d60b500300c0c50681c0c02d1921b40e4003000c0314600320000c42d4008122145031240c42a00f044200704068401c41e0110200462031b1901c03500003210038090800d40c0b0b01e640102d1b482018050140c601c058100395143c040010240303c2800c0002d84149101541c1480580c0144e6000c100901d8400013801860450030001d0000c1001d8030481e40079500b09030507a00c81d45004248841540d50080c030a60547c0c4480114410500c0b4200012083d441592004108200200301904100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 712979640 1250 712978390 712978411
    0x12090c031c030c0210051905090607090e0c0f040b0a030507020f030901050d090b040b0105010f0c030807051612030b030d0507020d03030902031002121008010507020706051e04030525030b150d0209 86
    0x2040030ba407c035001c8030340040004c0c00540000c0c01780002e480e0300c41810300c02ca4070005421a0a1386072084040707264410450009901301001070000340d9100040d000c0c150030b800c991002c0090342e840607416030b160318090108084a400401c5042c016600030000b030f210511240320009580340250f543c3c0c0c0202c650a03034080e954043c000c00100060740c0d1001007001d070000140707060042c43e80c05070780140021074003400341401d10001290314070541601464409120f9004841c40720f055a104002500a11620000c07500900a034806150351901880490b1a01f66025040040c01000b0740c604800a103c07a03d41240c5c1401130f50f10900500002d40080e000190000e900400f4604001c4a10101c48001e6800909503074103000420a447e81c0102d071900442c0c0f80307414070710395454502a440c06114441241c40f440700d240440d000c01444400181034514021440c418103141c90400544140794105100086ca002c0d01000041c0781101d142c8000c18030040302400661004da4154009100e400b01110f080591 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 712980890 1250 712979640 712979671
    0x302040308072006190c1106190905040e060c0a050f03040b0106120519090206090312120130031809091502041203030b03070b12090c031c030c021005 66
    0xf480e52800348402071800468a42c1e107070007440c028031000070b0403c1200308140f040390054081802645100c1134100c031002405241d55420042d142907013401c140e011080000c5c11540c0c00310350380c1030610030510b031221418010206580c5403144401c0c035601900e41c11040160920612141c4030000300998040c5208403c2800ca075170420300e00801320368203500e0f50a40141001f050051050090007440c5041100707131004107118101740041110b42c4500c43da400e8051041e0b8000c0046e05c2025009042c404002d0b010800d641d90380d0f203020407402804000480443c25005000c0c0f21007944046107103100901c00e00305030300c2c48800c180d07000006040310303400b94a4207600d6015180030011224603c64414640400840c2018104108000c0428076464014103050b03030380d5107840c1c1650781006040300516000d020581c0d91400200a01880780040d905009603106403141510540f0f00418020401042e00240320000300e140365046010f00243c0b8006015030107004000555130800f070185900c20f01f4503a0b450210b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 712982140 1250 712980890 712980923
    0x130f0c051002060a1512080702190b040503010e0a1a07020a06060b04090b0d050d1d0306150a080a020607060f0e06091b0102010504020a030b060105041d01090c1e030c030204030807 79
    0x2038881641724000b00000303402091162803200e910a03a0203d07040b0214648440075440441d0044000200840d5203403040c00c030004106c00c0d080c0082c41520010f500a1010305111040513995464400008080660307000022420301400580e581e4040b1152044400030151500c2e00c4d0101c501c0c0c2c1e041110746e11070000d03050000c1039250052003000701c400d4440ca5501c009684443c1e49440602c050202048045104041c182d10407e11182003143c00509688450a108000c041c0c19401d800f22240a1014000001800d402c040f403240c84094024007001d2a00305550740b490003c004400c810002c0c0b40e51540707043c001d080108007943c414001d00d00103042c075401031604040040c00c1081c0c42811681060204001601c072404ca410840c0e60007629240e0680300e0340c00507291800b698100c480c0c600c0800181c6004c030171841039021b04030b41610104101e040000c500480d00d6902c1058143d94442c248c2c1c1d075030b040d228400d42c081541050b95103130041c249a12541c0c1e1181c030717900008040d60003031420f181d0400e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 712983390 1250 712982140 712982161
    0x120406090219030f021f1d030c030f0102070605060607050601140a091d1c05091002071a030609070906053a020d0605010801120b0c090904060c030c0206130f0c05100206 74
    0xe0061ba00e400004180c4200c14400401c0e01c1c085211540007084510382c0c3c608192402c014086240c6030060680e80b103d038a99a285000f5080003606545c1d150a20000c1540c3d81804421144072542010182980b80c6c04d001070701480e00e001410365070300011014400200013040d88200d81c3c8103503580540902c0140b00d91481c0e07140c2544c1300741030703100b4080d14070909003203c0c3c02000b25615444161008000020720346030076402e00700141d10050b00384c8140b0440900461042c002144602400c03110201151038002c012039108529001e40d03401b00788100f01c42e003040f5220b5a040d00400c115590401d441703000c008140ca51001503071701540728450f000316210400340c060f030080c03401410b000e04c0c05100a44c501800c101b00030b8810320018104c20054408a42c074410038070100e83c2450406030061589041625041001389400b129010010b4070b400780341440180b01080c1503002d48150444540c51040903180c0302c11000d01f0704400c81c0d12010700100000c29440340303940a0f060109540240203a0305e451003500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 712984640 1250 712983390 712983409
    0x20c030c0118030311070902160c08030a0c230f0115080d02120c070b0406050c100b060d150816030311060f180316061e02120406090219030f02 63
    0x8605100098001110707100507141002c04413501850084001c061102a00e4107001280d00204001800018000300d42c141c3c075011032803498441d40c031118090b0341d00c001081e160b000f50055080000c102e10b03810700200e48400036251b00000201140c4c0308040010341c0312480c05085081ca145903035100e0030071000700181002407a0040022038040d1000e848007400080d141c0c6c2a4003902911240049040d8108000c00c00444000e003603c50720413503456450320400f4040340c204542c0000244102c0289075189681401400ca02c04809415941015000580310010b007940c070258103c002030421000074007100c100080c5907840115071400204a0960500820740f112100c450502540f184041c403d2082c15640c080794028012142d2085550041144500350310030480240d00e001094060082801559030144081800d80941e8060150914029005034000e800300130186150050005000c01c1c0c8c1508802500307440104500803080c4040300d42840112aa002682c154407a410010b0450510b0484d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 712985890 1250 712984640 712984663
    0x9030f100f0b03030a081e01030b060901080d02070b0f121f061e12090b0f0708060d110402070201020c060d05010306060501050325110717011505030601060305060a15020c03 76
    0x1d0102281c00b00100f070750307840340c0790300038003080481000541c4460440507180000166880c030700c6c14550b0340c0d092012001000740c580c18403070010320300009103841002900e07004a500780d40103031440c01d01d08180c00b10075070040003019442c074404000d0350032a001c05a0b041b038451401c00592890ba0943c1c008000d003a00d00f250030150502446000c1070802c0700e008a910402c90021b403a255014402810140703004d86a80c480060680c003182c3c040c043c02c92000b04180c0d02c204440d540b0902030340c4e0f4500801070f1920f21004080e00107400412904c4850500d074008080850043c0101e409120460380400c180c0d504c001e940b4101036540d00014000c12400c0c1c014078004140c241303000c40c218240500e03c3c040b640c1d8a040262440300b880c01c0c07180d05060160f5449040118403100b5180b0840c0d80d10889101035141c22400724080d441c04015104c00110390380d4000c1903850290007040385c0e85c02c06d04190000c080103440303550320a07400000040c0e01c21280d50300f032a0301c0b24141e010300034004060301410724082c0b02190 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 712987140 1250 712985890 712985921
    0x1a0f0909120c160f050a090e01020d09060203040212010c14030411090c070b070903080d09020409120f0e0316061413060c02010e0901080309041116030201050f07051e0d0209030f10 79
    0x420891707555060302050549a40000001d0130484112401c0d0082c801e5180d0704580c281080050b42c00d000e1180e02640c49680280d400c441b1510b000000b00c1c0c00c0300c0b1703103541c1500418118682d0700da130039104002039580544203180021800d100c210000749800c00483e454401010002504000c0112211000e504034400e800c00d91101030856944400302d004401c41800c2043e66240f04406640c2c440e004040c003241c110140014210091800400c0d0b9120381e800b542c041071540d40c9040c06800e000455091650031401c0f41e00003241001d00480d0b2100d91030840c80b518080070300080c043e046020100c0350090005444482020100d8800941950312003522148216041401001050785c0402159400c0d40c0407a0b00003a240d03400c9a0075051801800b40660980505484800c205a0154400d60040c07502e5494414540d0720000103c41d54441c260030540c40e0741c1c2405084180e41c4151010f01901140348030050704010189010034607243c0820446010342d4441c01d030317001d40c00c0c4407442078107002101c903034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 712988390 1250 712987140 712987169
    0x5010504050d05030d1104051005091806221a03190b10031a0603070e07020c0f1503040309150507030c02090604061511011a0f0909120c16 61
    0x604680514814180106a044416010890140219184540801e01c1084190940010101180c0007030007480e0003050721000303000381240201c02f40c1e42d803154010058007024401c5c507410480f469016051940029408181daa0504031180d407098500502800000d03105070201101c041008030315009500a400c0111840c0c1d520b820312044114094011070002100d40b00d4075400208010310390310141a950103038105c640844c240b2801a409140c0440c21103140540b5128071400103032082e22101d0159011007002e1460303081c078202c640406c94004100585100302d2003c0548a40c2c0304440450000342c8050040c81040d0712041845403215031b0780360050400a940e61301420224000202070305c540e07074250015030a980d139500005d028102d447d1420302c8800304414040c2403000742c1c48401842d5401c0c40d03e0305541e0017840c8401c1078010381c000c1a0001103010714090000300580038005040f43c0c000c03280380244d020103810041482003200001040a00200302004c60034611542000031850402c8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 712989640 1250 712988390 712988399
    0x30618090a021e0a0602032d041707050d030305040512040f090b040e010e070306060b03040c0e0a0f02220504112a01140109140708072111070516 64
    0x80d07084185906a03a00511a0045040c02004010700101070390f11688004000c20119404070280c0794151900d880000901080d0344000c5100d141101050400503080c0000c00540b050a0050214050703100140e44419443d000499003000340e48a0503400b2903221000d0004220040004900c0c010b4000e445509007414080c0880210b1601d21852069907116113000309503651360b500c01203032a0a290000c2266803405001d15407078446504c815070310545000000240c14003e202228821a070004002410608061200701110009401c0c1e40c0c90607540c024420700d01115100138400300d551443c00e20040c50000b03d49061240058000342d011f2030401c90100d00d00001801940e96940c14130740398255480d01c0ba0200c52440c965000801000d6081420784203002c00e200490318182c0324000382c00e0001d0484024100d221040555455000600401c00a80114442d40e00410380354280c2c212006000150005c80044e50070010801c822540005082c40401804128803180c1f2900c51203044026880e2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 712990890 1250 712989640 712989643
    0x3020c100516091a0703030b060a0801030308010e1e0c130b041703120115050c0105010303030f05061002060402090a090206030a020a0e0d380a0b030d090e130206040f0b03061809 78
    0xd2400b218031348040800d0040426000c0d41103258124030140c40151504400c420041c1b80d44020300c026000f10785003000115000034030b07004c400d100315445400100d24400100d54440032240060180945000030311102c0800700d07035a03c0d01e1000705201c8500544460502440c0c800d04910300586954541c0200061515040e80c6611541141c1e0110b0015100d800d1214040c0c0d1a84580c0d03048244551812001004244e0541e11240043c2903c4504005968414040c0141030702495546000741e489030340098014a49500301c01e074461100080400c0d2200f05901181450300103a842a03882500810301211448e8401e044010180c4201e42c030786440030300d940b5040424118070602000c001c50b80451007804a901c82081100000d060922044514003450300b94002c1c0b4200e14220b00c01c2c00b030f05024644641c89079072401d0546840c8085401181c5600d0010380b080450040c0407a01b120f01484000b58440500480400404000807001e0f542d25050082100b07000010b2400c4100103404018440c0c0c0220 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 712992140 1250 712990890 712990919
    0x8071b0822090e0106050a0b0d0b10030614220b0102100c03052a0a030c05130303030c08010501110304120f02091303260703090302010b041d01050c180105070303020c10051609 77
    0x2e01d0010a641c0c0c8270741500300070160160010b440c1c0c00c1000025485841c9a051b44031200f1200c1c450101042506901c0810210081b40c442111074a078240407030500a2807035a10001c01c424050044914031b0f0712445800040e252408040008241d440c0d081012105d02080c1990564100080c0384045071982a0107041074000d000c3c40c3c4080680e602c070704031413090155003101d403100e5020395118407240d50b03032500901030001d60946c00001111f4900001d001d5000d103820312a0605007002840c245428580001140c4522140580e1508071088030000580c07200510a030140035402004c81c04001242030260000c0403c1c2040c24020541600315880e0f9044021003a42050a619003ca0600f9107400c00724050403c206405511034a00040404003c1c064440f151140003094000e00045d41c41c0c1d0444134050203040351402c8030700c5102001c680d0540c031860050145900c603050050030280d0300701005141180901103d00380d643c1d510f0078014a00c11140d0040d405401500d0038801d0f00f81005c1e2246070940 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 712993390 1250 712992140 712992149
    0x10090503120c0405040218040f0e03030109150519060219050703030c33150806010e04020a1a0307120c0905012a200108071b0822090e0106050a 63
    0xe48000410b0450707200c081150010140248195110080390304401c00d056001c16030340b4452807500b00080c1407455140500708074215200b000d981903a18000d0208003070020b2400d202c2c8000108840030849aa8407400c4100c8411003040c5100d40074200302010385010650500c0f040001406034007240040c600140071800c3d82e50610b0944408c0d400351510304070282800f902d0051880c00100450000c18284104c0d1200c0602180140001c0d55450403040300c2034680d01411425030800d50040c01114a401d00e01904688058010107006907a400b0152031000c0ea0710101108071800401e100075079600030034200c4188103e2004100350b044142c400b402c3c0094a10a46041c0204040541e0070344541d02c844400c4804800c41c2010031000074a0101074903102101409920f1042d00303407481e42940b082c24180e2181c905030f15507140b03140020340082503508200300c088842d203104014900d4508151600d401a0081c041d006034459801c101407103041d914080000700c443c2c0e00d08902080650740f01d8003030000700d6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 712994640 1250 712993390 712993417
    0x30303040f150e0102070f03020601050d020901050d02061c060e0c040b091003060b04121a04120804260a020f061611010b091008010b01050f0708091f0c0510090503 72
    0x5015110b00c0c100541040748142502c2d51000c12036105101620031010030041c440e0b421350302249c0e220001c0003105800010060f420610b084014400c5041c00c5840c04d044c580010401410301d81098401c4072241004d211810146465460411540204200064016508039901800c003070034164849414010842500d2141d1070700c3c24803106160280d4440d03000b40214014082d5110303100c44031008035003840e090803101e1212a440740c1440401402405010702d900000041d19885002d60031240d01b800584255001c2000700c490b004400c078804080160180d4003546140c0340e01d40182c001c2e0030031010140624490b00b0134020085581a001000c00b480e22960420100f06d8294015003401010b256240c03541021500080c0242000070040c400111610f9000a00509030036000440300c6000340c168200d82010213001c40000a04080064040400003804070300041e07220245030782c1980c80e041d4501c40071551803807110742841000d10041e1009504401d0a000c1d9040503600c1c16542c2c1b080c07180043c3d00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 712995890 1250 712994640 712994663
    0x8010b0720011107080313080309010203032404021209011410060f050c1e19050618150406021909080316080c100b0901060c030c110402070209150906030303040f 71
    0x366809001071681039494181102c1e9a1900c0720012a50303580420007101c078a10b90647e0005042e800001110b165484c1a406075007942ca421811002d44a404250b24000300d100300a402119107491002d02a100d8a20480341414101008100c3c01c40308142b411155000d868010003100101201c201412290280b4094a50350341c0320b80102d0f400d000d0750042e04107a00036800030124464001004410142500c000d80b90105040801210b5910325250000d0180c6c0003900050203442151000034054403a40069540707801d9034089071030f10382c0d004503421280e660f400306811015248803107a070710700354480741010241c3d5400c0c00107082d80c1c0e008107929001c0c00014807920320100700ca01c1050318088070041c41203035001c09079000100c000d003018683c080c3c09014003100004089214140008031507406865032650903019468a641c09211603c0d0075400640810400740142c84036250244030b04101c0e103900e408150002c040103071988015015501c2940244240008107142881c001c00455014418404 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 712997140 1250 712995890 712995953
    0x109031b260c01020301080d0e191203050c0d02060114040b01050d05070c02030d020d0f091203181a0702040507030506010503192307091e060c0c0b160308010b07 71
    0x2028442c1e288004210f500200000508000020b462410320f01a0303164412200020014010740b40650903814a0140c207802d410410395051000000081d8024034086244c104041002450404e03003424810040c2d2198004110089000e0207120148030102d90902524280b100001d200b4010252640c09041d5120302244091b0f000e296410540b0354080e0507120040316181c4040e44034078002e440ea001242c0d4801100c10345521030b40f2000f0a0302e0794000c04400c1e01c507968030111603503d0482c40b0881522050000405c0110040500081c611204050f10307a8509462050000307440001d02980305140c140410b110044e038002e0f0648ad400000500380140103c2c1408038000505042c400c0501950414140b400c420201001802e01c01c41075612130390800d680c1d0f02603002c6d07841c0810b11510001425213030144082885012810b81242c06040020f90881d11081508130b180c0c884a0300351031312120034440904050300465080e00410843d202e490a102c841d0301d43d014040a594034021040341895a90f04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 712998390 1250 712997140 712997213
    0x1e140d1e06030b0f0702010c170703110c030a031401270b060f0d0e1b13150f0e010602060c030c0705030c010504030e1e13111b0109031b 60
    0x10000340c220201404620341ea42041c4070390010075142429459504000107210034014020a001c852003556400c007401901d9003010030601010b80800c1c00c00d5102c1c00d140504002d020003070b016410040001c2c0d641c0d43c2e080d0a003d0111503119083c1e03460441040700411013016003101c11030070302d080103807440348841d0410817140c0209142c94841c1d61003100400c04004075503c00c4013510201c24001000c000304000c1820282c0d27509c0c441c2400111a0b00100d51000003400d009030040c107484c20030134000c10360700c100040f01ca84030342e103036009400d00c400030030010042c0610314405540145101d00140c87c09003081c1418075647d200003440500701a60002c0e01000b0080300f0000c072680150000020403282c03d291070010802000034000a11030131564030b4030421a000090101c0190f5002042c11160348070300e1513600003900e41c95680c0e04503c00c0034010420015103000d031600c05ca00c01070700001603602581c80e01405080c0c119400001a90480c041c075000151030300c40c0f5201018806040078542e040702c4036500f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 712999640 1250 712998390 712998431
    0x130501030b160215070f080603060420010c020d1109071b0204110f131a09030c09151807020106140d0b04020411070501090b0903030f040b04050a0803071e140d 70
    0x50b102d0758a51300c10004a1580002000380940d11542c9215154856404140d0303038000584018200505010906a0308400c0510545a214040c1840792840c1d0391500003584094503c0d4040c0d0315211424000da90a00c0c1445181c1c0d8020600d040284190807d803400000400d22080000d0140d5a1000060000ca0007074043c1d0b4042c072900402d4680c1e0b41030f282400c8050b4601072184451000e0143d541a9010508005403180c0c843c4c06002006401918400c05c0b142160145c0f104101c94600703003410324640c4455031b48400c0c020034940300002a09005100900315101c583c4400e041c2e48143d040799155540e646040d402c1140c000031002015252400003e00400e4002c80e01e00e000e8000203400c1c000c2000640111111601a02400701c807a659020203e840c0e00c411541207407518141000140050300b14081d650300540540b0031070b40980d00c25903411072942e009480400200300303255000c040e8180f03001000d03c054203039854180104594881c24042501440114182c5c90b503c507800120070b0b441d4240320 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 713000890 1250 712999640 712999663
    0x30109120e0a050307050d0320031b0706030b01090302210d0207030501110708040e0414030a05042112120902040204090e100603151107060c0e130501030b1602 70
    0x41458118008064071007900740d6026801092a000c0c0000e640c540414258129040a070100b01018250f5600f16803011440f00d0a41801c5800110269408020000f801609030201c80c0348000c86603e0b40700c217140c82002d1307200c04101401c0000c80b0070070b039a110314050100c0e03605507050900400407110250312888400c03070783d403854890107040404580e400a000700c00c903801403000300310003106102041905c4c81034950140c0000300070082080072230342440d111603016004040d000d0640c040701d15018110f60203801050009040801c0502450b40403050003282032455401d0056003295654036080451b0015502c14284181d502c620204c10040c1d030016444580c1c018411903403507854001c808002c04140d4080c10041c425642c4010000040d80f01c1c14069a400460004190b0b00c05a950009400b45107840307503134014180038502c00200580190004d070300594030360307a013505225400d004600080011049000c0c3c1004010408143c10200850f045410007042050201d0304950030b13868148210103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 713002140 1250 713000890 713000903
    0xa0b100c061805062e050f060d020f070c0602011a060c15010b040306050601080106020a02060703051b07050301050a09020105090f190f0626061e0d0302010509010e03160f02030109 79
    0x2044401c00070080344061045d40d0072100c1e010000a503203410085511038440d2004402c1082609100a1401c0c44646035400d0004088618180d2000081010b03a00040d980c64808e01020645900f04198100150040c0c00d45100801411100480c400c074501d003101161401201c00003142808030300b06000300b04421116820014295a44a460400c0b0351700c944011f650396403409010960661080d0070041c12100035034010700300d582c41b640030404540c1c85900110b00703002d001c004c2401110210014140640f00f650042c0c248686040141400c0d0b91000345030101c3c80385041c013211300503030300700d402d40b00a03210039901941c501c2c5055012609030f5610180b5440c821000c404009101440c9a0302d08040d07030401d41d6004210f0299101c1d4400700005440f000c110290500c0c005a4079003003841c0302d10106a0b140b001c1921034a0488042800c0b078400f1441a00142d440d5803c02c2014030003406541c090912010056141c010400003074014949001c0c2c000701501c060f0b0b4000e00565409410003d9020380044 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 713003390 1250 713002140 713002181
    0xf1308040f060c021201050402090106030c0201020d06140102070b1e030c0405120a060614010f0302090f10110c0a030804171c0908150f0613110a0306030b0a0b100c06 73
    0x280243c100311507503800700d219903d010125010000103018140c000c035400360200801d070f4240042500901070009400085650a2007a0010424107008103001041a13141540004483da000282040351075000b15081c00020040b41020440d4000c0ba21700346000080d0140c3ca0b81c03240d4403041c2d0a4410781e03000f151300c03541042c413880c0c0794000800d0400c031451107510100f103c41c0e80c40007001100046045664041220484898200c42c003136001011076000041c01c0c145d044170044c1c0001d034100c14013103100001680310b1550020750f0100b008101000e120031906614060710719583d8513860310540c00303407013400f005448001000c03600c01c01c143d03130354100401e41207400c0e00494600100515201d118408080c0705500342d856075226011400ca000d41220343d806540c541c1d405003270000180703600b0a403100f0310740d8410b600d04440c0d4000c0007070310451a0a59011503002d03c0c5003002c0c03105900c05001102028038259000102d0341da1900164100403441c00d041030101c43d80c0c02c225008014190008a0781210031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 713004640 1250 713003390 713003399
    0x20d030305090d08040f0206032208030702010c110a1209122d02030c0405100902120f011508011401050714060712020c0703260f130504050f1308040f 66
    0x150800c0303104a442c0c4084a692010700700080721140e50907107028201e00490f0a0001c00b500345580150307801720740f022003040c004206207400c03081c4002d182400d481c00b20000c81889015a0b0a00a080042d569803800403000081100e20540f640004980180a58560000c45910314080e0903610f0051802d26002240c5c011181805100b03d50002e880c4c803418051070020b40201d0f20030841042e51190080d000b40588a4020305020040c00041d080b0100004040000510624640011b1801050550030b8143c9820704a40e42010580c06030040340c052801440e07124141540400e5090440b000314a80302d0320311a1100c01621b645c401c01d8009001030b6103100400c0c0940c04000b440e107000e2400382d40c1d80c414210150520300124060320090100c01c3c0c12581d0208045070420400d480c0c030005003000c1103842c035801c00070100142d120704004400481c02003112240f1b600808002c2c4000c5c0400c3c0e800344a1440c2c958090740e2900001443c000c802014129100300b131024075802e55001d0220078140181b10f5448 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 713005890 1250 713004640 713004647
    0x5031e011d0d0e04330b0d0e070503030c030720040f05190219140903073309150c12020a0b01080a02010f0f0c020d1119140f030a020d03 60
    0x52082c00b00400c1840e0b81c0382c026410548039604c2c0c1c104040008211040c0c0741610f031301131240c0d544800711000c240b117000425490b000307134000c120030315102c0b80000c0c4104a08a4007420300b00140d011503c660401c1c0082009502c01104a43c15250b104041e900880c013a03800e441d070540c2040481540143c0351038914040c0344074a0740a180540d0303040509181d001c0c1c103c4190002d80c440d40e004080da00d145d8005c803103807541c00380768a20a6444070240c0503003000e01103001b107850314070103511146480015001401c00c0360070341c0b0f411070039090071910416001e0703441540140c00510140728203031406201640f00c40d5414440c0c001d042d5040d13440a40501c1c460000e140007541c414225105648102d202d500002d001840060b400b80752983c107071a07100320620201c0058403600050304031081849000c0d42e1a9005aaa05101d03806603072150440f02c4200c000700c0309000c6103070071070441da25a401d2008418050782c20103008840542030300b120610550300f486c1006c6424203034005402500415420740040400d40c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 713007140 1250 713005890 713005903
    0xc030307080d200721020304050d03050702040e0309120303100e070c0f030504050a05030a0b040303020322050d14120613151229010306090611030412110705031e011d 73
    0x10b4520178890311140c42000441210524008006da0b10420040006092820f88013030b5203402414a00d007003000e10b4011070142c0c1e0070550b10307443c984c2002030b1003005440c141e01c0c1d21b03c030810900010740c03c503c1d0100301c100001c0d040e8042c860859074440e001420292240c030f20071a100d5071081c406040e0780a5441e0240c001d80190040c01d118001050000c140f60034002491416182c00070300c1d4519035107554030288d0003548050003103409020b607003070882d8050321502d0b0b00c884114810f40040107201c0c09201c1c01800c020300460380380d030780e103500300200784070681070001d40e40d00200300f101d9586c094104403a03a403008194400921000520359800000c14500c0303442c0d00d40e041c030700882c1c0e1100c0d00d41195081000d003001c2ea16848040244000050000c60604c1d8420303203142e840341c42d0024030203a0f80700380c0400f25041104c1c21100081a080c000401d0742c1c0c4070b943c10003030b851882c0090481505040019460340c409814000c200e070b4003030750010f10400094001e10b03c401180c807070300d0801c1c03091214456107809 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 713008390 1250 713007140 713007143
    0x335090402211006050720030307230c040204030b2404090c0e07050715020a0504090608011d010c020309060c0304090e030d1103070909020715020a09090e0c030307080d2007 76
    0xf22075007000460700c2c000c20032600c078aa03104c0c0b1809017200c0c240c0e4400c89207d4000400c0c9425110620640d0006251507170312402840e0303c151000c0320989440d861070300d00b46c8052040c030700a5006100c208002500d21825940258008031610004009032414040c5010107020444d03003c0d003000d90200c00d1103200c24002082c5e46108940300000c2d03a48220503a814422014001c0080d800307110386041124407940a80348501c80c2d0302d00903141a07954550754083d50300c20f40205016965406031004000e0100d550007150f0f8500307400a00244078403d001035101d00542c07200c0ca01a0100040c1c16055240a008982c003420010300104130000182c0d003c1c0384da03508a400d41c262814074005a16014452183c1608d114205a94504110340d0a142d0844080e42040604071601000c04000c2c03610512207001900d072110584e0344101c0010310705007040c3d095801001001c042a0424100380000d900c012080713030501d039003140c000b41ea50280d65a8040042400746103e8901c4045503455440c0380b0b180300028004103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 713009640 1250 713008390 713008411
    0xf0f1a03010b0405040506180c0307030c263309010c021504020d020d0312050c0c07060507050d0c140109081801020615100215090304033509040221 65
    0x1920b822040c001210019a405401c0d54441400540c00061001100d07803c41850001c1c0c5003001c6005000c039280c08103030340080350280d807001c0c03017030140f00c500146410034074800c1c8103100d4410b08004801e580780c0d2600708160f0102241c201e22094841c215094100b1000c45908143c0e4042c07a01c6400903008200c08000e14005000e2002d50f10b03e1400303901c858600a0b0f4005100c0505501d0a600b04208103450a00480034071440d0001ca5100301300a00c1079a20850058095507500c0590300c1c0b050381821800e030062418800c003400f00c1008140005540c645078502c5040810b85c3d03804a043c80700f4500f000c41c1502d5500c2d0308088190b010004801e003c0e01c204040c0800c04440180c001006a89403401240d1b210207100508400e900e031381c9480182d4000144850060300c1c00818203064581a41004450740740a913400040c04104000d6480c1c0c0001440c1d45058940280400c218502e5800000c0c0c0300700c1c1009488040389513807041c1d8444d81254215507400d0404d40d0030800608200e030740c0180441d12507000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 713010890 1250 713009640 713009651
    0x50705070312031808030606090f091e0903040e06090c0408030730050a120b10080105090c03160f05090603011e140f0105070507050a2d05060d0f0f1a0301 68
    0x900d1111342c100f42c9503801044c9505580d40c490900819401000f529a40308103032a08018907515003040c440d005145001641210300400607002030f2020003d41074000c60340c0200030400841d8080681c503a0008070480d000d5031306895010034060707203009641009145001c00110f007000c000c1460500071a003c0ca0701c0d84842010300e111181c400d0840400c0c41c080220b4401c11640a034503200300340036080d4001084000030310b022101c0100c1c08100c4035000312004590000010300043c82c02210259015101c2c2071800d255203004040c0010462441c4100300a004a8141c280c0300780f4080c5065034030040000d025151a9a51180c220260101c1d081311520b010740c000781e01080e015802c40050f800d41d0800f030370219000c000203004440e20350000d4000d89031400340300d0011075142d80c0e0401182c024440405c0d01807540d2500c80340040b10041c0010616942d0303049460411182d26288182c0d6000039a4542c00590044400c1600b406000380c240205d40c1c07549071040d0302d8101001c40d4400250608182c000300716 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 713012140 1250 713010890 713010911
    0xb2e0e09010b0d03201b0316081c0207080d0f030f05010807230a0e09060a140a0507030e010501080f070801060b12060a0b0309011a012d05070507031203 67
    0xb01c4601c0e4031070319040b00c845000d500c0072038001c000050500848120341c8694490301800f2600b00408088600d0360b604100407024920700d420401501513207032540003510054035207a40c09590340b404c00b800038410258926442c0d1114028004000100030403401d4541c054841c20009200141c05208a00460703e0a408070503910348900c24a4103940c8540000c080041c107183d003603000b80c0c1d00f6181d02e0780c0c1c000040707422508035103440e44808014500d202003850141803603100641012002828410140e2030600024565100c866409410040041f0300041c01d44840074101d018081c0e07448604419130a290002808400010b04070121100d1707241a502000d441c1c481440c02c0e08c00920480540d100d013400728006036075403140c5031500090b004104070100d40d650440c800c05034004071110313401650348da80d0541c2004c1e100f10380d00101440034a003085054001280c040a11081c00807540750110070b2103640701182d8080c0c01280c0704982c1000c201c545c1550390317290058200050080c5030307000a01706441000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 713013390 1250 713012140 713012143
    0x150d03120e1e062a1b07170a0b0f07050417070303181a090301141311010509010f2a0b0103110406030c060509060d1d010e060601020a0b2e0e09 63
    0x20300502038204e0041902116008800341c0039108020701d41c4c4030500304503107040d03400d8060715100810640310140100f50b1600f142018904140d1100315420f800c40107640700094805000e0302ea10a04010f1a010070ba15140021241d60085401980341e00523410283c9000d00300000d500d2040300e100755210314440c111f8403011f8080400a00c1080000c581c41c100c2201306001510280050000140000440409110a04608103416540820301d0b9044444800c144130040190040d41c14003800c01514000130000001c0a1411800c40081000b0341942c1c00b4458503a80c1d0b41d0440340c421079480300121001c20f0300304204554400c1c44100c0d254027104400d494581424012041129040002d449407145050000d9803035a1041940a6009a04003c558a00c0c2c80c50321489804103000b40b000c0e101d491512020074211010b0180c505842c2e40000e080100390781c2d0000e14580c0e41507120a20510b0b54590251650180e01c1e960101140081d03102c0c1040c44000b038410504040ba4103c3300d07a0b40e9161200715a05 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 713014640 1250 713013390 713013403
    0x703030e10020a020d050304150c0504091a06070201080415050a0c0e0d2406080a0606180605090a021b01050903030402030d0c1a0c0d0e031e03150d03120e1e 69
    0xf0b001d40c122045116403640190042e540c0f080c002e111040403c0501f0200b00e0456003260307072640c08140080f40034041d134061486041c80c11a07420b0303020915103010380d00280340e502825100038100200880050100441d00002d0304000842800c203000718101101c90001400905007172a0001d01c14141006691602c01c0c0c84145850b0401502c9000d1002c410903101004080b440088406031500341c000b41c922020400030000c1c034010040054018200341a091000301d0090048000d9400c0c99014082035607180000c9411001c410720042e0b540e10549195540040d0022812025501e08410442c00741800302c01540f140b0f00c21002c2d070b03840c5130309100c080d00c880c1d60583e4017402e0340c9440c100003c407e040380c200c825000031701c116042c1c0c1800601000c8406440d0004a41e000d00e420120300c400c0c0b2403000040c0310940d040507804281c03d52030564140e8400640e0074046502c1449022404400c2c1805070482500036000e40d5000e0080311084100c5503a41c4441400159600c400042401407080d4081180e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 713015890 1250 713014640 713014657
    0x80c09180706051b06100b16140a0606080105070e060903010609150512030703020a1e020306070f021204080a0602130b031501080a020a080a050c0c010f1a10050322080703030e1002 79
    0x80b00311400c00604840c7e40e040480130320909511000310340d02060156440c240c035085a000205090981e529007001940e24642c03080c6a1a0305101c18002034941185800701100025502c00fa02c80b4120b000107030141c03809034400351100f80b03045d1071400c100500004150980f40165001c003008607888551503528805d40c60060016041005490005040c80001e494500511525503884400c0768000034284802566080c0100d00008180000b041d018841a12036803550241c01c0c0c14a85868120f40e2201c1079904001c00081e400030300c40e2208081541c03003901900b0302211540d220300d4903030b12900720520355014180c0443c02c02000280150640d008555006010f80c0c1c940303440b51102c0b103c1902501c4040c21300c1202030414400110245424400c00504640d034a201254841c900d8002d082401c038540846030003042d404440c4070b44540c22070112a00440d000c400c0c07869110040b00c00b102c40c2c40310000300800c2c00c040081c4190a16038142c00492a400704103065414690090081e6012032003034115 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 713017140 1250 713015890 713015911
    0x90902041a21070e0702010c0e09014209030302120f0706090c083003010f03080c030408070f0e06010c11061b070e1006020106080c09180706051b06 65
    0x142c1891140300c2501410301c8460315000c580d2a95190100c2e004e510104544080c0142c0d034600143c41041d500c200d101034040c2c010f80c0c2032210f80d41030941400001d0380d030182d04103596440000c07001500d50540b048255100c014640294004414900108020790b135100650052080103600c41030003d03ca42161100c103a84484c1c03d2a2407803e0390780b440500703858107050b00c5484408000080d00c007410700040710a28241d14031a5101b8904208201d020482402940f1456000384010300c00c00360300c1031300c1d20103603508054420f0b10b50b401c40700464507512032608132070043e010380c510010f0070102c003c0007001602c40b12041d5242e02d07500c0c90011250820300b0700303010b8a110500050764a440c1444002040c0d0150740c1c0c240108440d00000006107000150b90107503003400c0002d010848ac100d192010030010306000d1000f444603601d0b14521a58503048103040501c51130f403207c00700d9400780b00130b946101c110b03d4940c01d0300c481030780d1958094242c0d0048180c5043c61035128000c0300b668880454030781d205020080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 713018390 1250 713017140 713017159
    0x50a031e1b180b1e0c070603061505090d0303152711210a09061b030501170606151c0606020717031905070503040b030a11040302030c0f0316090902041a 67
    0x140c48400d080d1300d0800030f2001900421548009460611090016002c035403004070302240740c00c2c0c04402080d4401c1004007000344c01e010400855030354505034210a42c151802180c840050b5001c2402410242d00c40052440403920200580100c0480d0302c480b8400200e04111408002c0503210080c490b001981c4102c05005031001c00002c0001205074000d600a5400941210117565030011581181840c92101000b61004001182d02d8040e65014184a80703140341100d11041030540e896201a080f540f0918807003d1002e00c28800030191707160044a04440041c01284c50019070081000b0301030f400040c0155000402e00c00b0481c40094074210340b0310011803038130f051101e8030513803c0441b400c0001082030402002003c41c40c1000a44003030241c0c00030310b941d00e0a000d0b8511080301c0804e00310701c014201c10320041001d0b1b6804516020303000410b984601010381040c00183c206031109088034440c8501500208102e01641d1007596014400d031010000600c0c07100d40f103c154400c030101940d1001c00c03203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 713019640 1250 713018390 713018407
    0xc060a11010b1f1d03010c020f010501061701030f020103090803040b04061103010612050604090c1d011e0909021f0c02090a1b12060f09141501050a031e1b180b 70
    0x10039800070101303007052001005041d244002420340345844001e10060b800101d030101244801c1c40740c2401400c407428021040100c2c4000082d481340144405008890000411801d41e40a80c00200d0100d51080b1015a07a00e4185441d01c400c01c801da41c141c912521700403045030581140c500300d906943d007903110460041140424a4080c00f0024180c50300035807501a60000039542d80c00e510060843c0c59030120707103180d84241540031500305900c92441c04101c013422602000007c110070059400d040004104060750b40085140041d501560446004064040040b1a40d1206040184a100b00c41d100f080b51500340000003550345030030144624020060000b40400d02070400486691420000441c28654076030300340082c1034140d484100c8543c0c4504151540e052820842903000003280c185440c0c0d4079041e40020510300811707880d40c1c1456940c40c0107070003e041188600a02c54400c02c41482110040990b0a01e068100301c180300114a840d01049044d107500501d02080d104495000b5003014082c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 713020890 1250 713019640 713019647
    0x702210a09030c03061e110901050c010b12071406072a0b0703051c09260c1e0f1c0c14060f010317070305070b04050c060a11010b1f 58
    0x10008400c0c040d07848800000680050180c0700118084d4000007100e09021411084102d00000c01000080c580800c034442e80310b50300c003522803139102841c2507500c0d10707400614203004007000244190300080901d01001d050700000f03180001e981c0c0300c00c0e4400441517920184101405168801042c1124050105500250301c14417241d451801041d01086241d84200001035075103c0c01055000500010b1001c078900c1e0346204214403c030301c180b0104058941900c0341001c0702e5091074012400c2a1036250804203081c4a03054910560780c0b40103545a82401100d680c2441c1e100004050207070165400056010001064601140122094280201901a20884902c1c41d0a48101d0b0407005450301903940100401800744200e0005d1102c400c2035066091001900001b4410702102400421072800000d0340315040d94501607000e454524161100d240c42c5050180c50014a50091408120b20280a501a9003401e0880411008001c00d4100b40c1c244080880ca03180741903912240c503901001134a12 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 713022140 1250 713020890 713020897
    0x12010914010b090a0c02011113030c060e030a0b0a0e10231b0903011e05060a0806091f1116060e0106141c0b01060f02120a0915180e0f070221 62
    0x284000904e08054400000c0650030070001d034900d04030002700601c00c01c04510f0300707038000d4001400d04000002c400300000759a0001c86100a00650a0401040100c00540c00c60340100303490200751041c0c0140022140d000700341c0c40094802880110f103c041652030b1020806015525807480303c80000b07680c2e0031115560f804955501d070552740c0c4103d070340300900c04001c196284a01420000c90142420804c000620410790000480d0350040030600462500c0080c0074210342032031100006280e000108600010481d100208650410004032081099140c5581d40c00c1c051207100100300140f01d0045050803aa068054402401e81710301d099a50b030300c0c08803504c00906002200c03d4107101c0c00c0ea0785d41410a0300a91201c4c0100b40140c142625554044c02550900400281035070b0401c001400000c0c0020120b215411441c84428517104495101355190405491038225070004c160703852a180756000d1085480c003071600c0c5075030007180281d8400304e0403c00540c5800030b04403190707103c117090320442e40c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 713023390 1250 713022140 713022161
    0x8010b0310031205040308030f090d020c0102100c110304090c0801060207030c0504091407140325030f050703051b0a15020a02010e03190809010e0102060106120504080912010914010b090a 82
    0x4010322001000503174850095109d0242d04a400c4c5640c02c102c41e5440c40d00745000c2d80c0506540001801c41200e907030000d181c40300c60411800124004600c900c05a42070324500d159540305000004020589400c0741d003041d01e6042e0075645104061381c0c1c4440c1241c40303100c103010003408885000000c100c6882d0a401c104da074607000e130444480a036016510703285010390319800742c3c06001c4c01d40c1d1003211924042c04081e208107607103050800b4070300900c55103014052850000800482d080460007051110802c40d0034003540c0d001d02110380a004502000d1100f6210201e1035200c0c102d500800301d00b0384540d010b20440741c06c0036001020480c10340ea005407040b440d000c06480e01480740c0d00d031441c0700400d40109400c1c440c0c020305c1000c1d59403a551000400184040341d22074195403290004002d001d070701158140c1c4400e035201d000141602c40d0301d80303107a03688240042c04c0d41c40f01009203003609000044d804089600e124101504201642d140411b0a0f2142c50207069880744500002480740303030480e0070061508 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 713024640 1250 713023390 713023397
    0x90218070f03020d27020418080d02030a180506060a271a060a091a04030f03110102160b06040e0c0a172805070f050904030f021e010c08010b03100312 66
    0x701c0c01100c1da902420119488400c20000603140171702541060700c101e02c0c40c103003d1000b14090000d280c4900a0b64840e5620304808141d0000010b4000c280b16403108134950120128072159000d1420202d5440206a411030322850030300500258010507508056003d0824906034040313000303082d14060081200c041d0510f15508480210311441d91103e000300300c884010703203606100c94240b080b4644141004604040c1d204002c100600214010034038806906900d0f2030704c2c480401440310840e0290189080f90001804032106001c1003002e400c500904c2080187d42c20040c16a401b03a54a5132240b10320702e03164101040c05414091004248103503841600031200725641200c1c0041e0080b50740180c10741c41c920305103e8102050030084280004070061216681c4030124508140000707010160150004061251402c90841114001c4c45120115104a0140700341e00e0758100c4001d001c0d004803a444d400144114002095031005482541d0042d50f0028201100500719502d070030300300c80400e0b000010b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 713025890 1250 713024640 713024651
    0x3070b01120507030c06051c090b06090703110711010f180b0c1c0206010816080c01030e1c030507120e0607110f2a010f080408030703090b0901090218070f03020d 71
    0x100724400d10180c0184940c0d0f494030b40c0c0d000c81088481c006170710000022006400c12640c00c9c0461100d4885a821000459071020a1b0b2110b90058000305040049a48881c602041010500540d002500300358482030f2242c8200c3c0715a54402c480c8542080c00c05d003440302c030400003840446d1404000e4403180c1070480465040029000c00c1b90007202c0c0b10054103006a0103100103000303c0200f444111000000c0c245581005400c00340316584640d50300c82d40904160383c4e226016202d80d000c02050f074202201c0200c1003030780c448403c8014094039003252a000800c9105448180b501603074030801d0891000d00e006480c060301c03104001c03114030440c0d80d1582d40511904803030031100e0344140720f07414050003000c210100c0a001e4404c881c007020144909903042c00300005030074140c00e40000300107602552000005a03070b5552a042600101401603016104501100801613039400544c04150310900132034000a280d1041c500f0b401000508581e00d4000030b03c00340000d170b03e0030b01a801a054804044001045 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 713027140 1250 713025890 713025893
    0xc0705030301030b010311030a0305031506190804060b0a0b090f0105040f0f03020910050906010e1f0512010801020406120504030e1c0605090106060207061107120b07080903070b0112050703 83
    0x510782080e081901c0540d8030340b0041041046501d00390024140a034050308888509850280003804020301d20306009503004490700c11a5203440c1250390212582503000d0401240d000001c1201e402114212022441c04600070064a02594404200d0324510441031038402c1041c240b1a1400c40d070481541402014000030a4141c504548e40001c2c0188640c1e001c0114650700403c8070b50132000c1c165040e600c84540c000d1000d9180c818440da848502802c04103107035070001c2e000c6001000b20103120b12501e0307810300440c14040d5010b802048044c080395080105a41c8a0304d181d0700b00e105038440c074408a401040d204c65010200d070009030b4000c0c003030309000380031110700c07800303e2810700004d103c258510100311608802c11000303200d00f50b0400d40301c0c80200182401c141000e5903072030840c001d203401e1004c3c800b0074030170100d010411307000542450a80d00324074000703900c1c1003801c0a2080c0c50351804114007000160304504000700307403a201034004124407030356440c140e40340106050b001815107050040c0c200100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 713028390 1250 713027140 713027143
    0x64008030c0304110109030314310512010c0e010809100f05041b0305190c050406060f020709050f18101113061803060b2b03090905090d05030c0705 65
    0x40c801c14054a0791592498a86090403021503940c079a207050100c0c500040c03000c43d50001a83d003a83c050b03490419a40d09100e45020003000383c207031003110b04500c48030613802120307103682c1000115081a03482e4064243d10f40a5a420389040c4010100020400304e83c22384158890400300780c011441d0015190742503400031004090320f481d104d090852540740c00c1400100072000c0d60000b0b105c20350300400030340e0f1415541d85645424000300320480d45980700cac0300c41c01030111900103400180002001005415540c0001900791401c0300024409409501c400058828050081a2243c0919480003200d03590350452101c0c4ac101c8a902a003007441401d6040014000512071100031038800c102d025144e0396070039009070568840f904042d0801500e0020000c4008119284200341c1c1e500c00d4000c200400303410080340c603c800c1c17a4040910a512115954502da8202641c8000c41d4007076078541d8000d42d00c81110405031041540e00e45415405071000d490454415005543c000b1501c8680350301c1c2600d07680710f05 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 713029640 1250 713028390 713028397
    0xb01030c0311040507080402091905180105090f0a02150415031d0d05070204050601020c060d0e0d0e06090f010306091103090708060f13050c0402030408030603064008 73
    0x449400c104a14140103020362000050b10704901128280014a40864010409000500024064541400030130301d802014681c948203160980c40400a6142000103088240c580c51000c5d840c6501c0c0401262007580007081d0100da81c04001c0050040d80c1e026420300c00e103040d814810320301034541407001080a0050b040300c0000081c1c0350f0303004241c0f484202c0c0c0c9107070b5005031100bc03030100d5402121031949041c0c102003030300ca0740c2c1d070126000038540e500c401c010303810a882400720650007840000d0700420482158442d9442408c200f0441d5101104200b06a90a00c400111660f0050040c000d4424510704941c10a0396040c3c10304d8045296a0737501c50600036074915400c00c2d581c000000c0100a00f080c0708204110041003010000c09181c01d0805525a0320480540340e201940780c031150b51014400c04004165401d03e01802c00c540c2c030702e01030034004500c4e0030a4074220b00c20300078200860984070780c100d039280107440c9100705000038002c9408404810705c82c05c00001002140d0b8910341000c10080b00c0038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 713030890 1250 713029640 713029643
    0x3021c0b010b0a0519020c03010c0806011202030a090c1706150a0b031008010c09140d211b0303050601030e0a02090a18021309031205040c060f210c0909061802030c070b0103 76
    0x1c0284d407d240c0105030a440f0801c000c00d04110302d840412480b030ba803144000d004200d09000c010f0790798540c4501100a085101c4000c1d0031030340c4030380002400340c2d0601c80014000c1c2c01001591281d482d0382654014400c00d00070300319407150102ca07003842035503040740065070807a4807110341c41036803a82d80c80103d0a440c8021700074000704004100810202c03400208034038003020216850b0581d042180d8078000074501c40c51a442e034080864007107120850003200c0058200c1035121400b000e8000a00c2c005010342411144280043d060860481d010000051010841c9a004150300e0041e50380d801d0150040054031400d89800040c1704100000d030300c500c1d20348489001582e0020450010a040140800c0640c99032110350514040800010807609400e1005030b980c01d150600301d01154200485030b11070545420106500440c030380d81c0380040294040322150441e9195040000e80d180c2001e009c80348c036032090064030f044035216034440c031400e40e000f141c0c4600f40b04045401d04542d500c031407081c05000d810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 713032140 1250 713030890 713030893
    0x8013012030c030501120807030521010306140402010f110c060301080f160303050a2f010f0513080d2d06080712020112090303020c010905030403021c0b010b0a051902 73
    0x10040303406515024803400d501c070a00303041c0f250303500d01039141920090105000e0815440424040d003010b00c22001c4030f01c1c4070281d9510320f610302c94121209840010a1104445151604444108620100c5a0140700b035070141c599820144c00d081040e1025034950380250303910301803a01c0030328180d034544000e907002e41350b104000e01022a000a0319072605506a03030411206c0380000d41000020f03800301c102c0342185040d2400c80c460303c0e043d1f100304000314032590880c80540001103e1038194101540001040031041d00c06200d21f44801818030703c02d1215090241c91010100f004c205910400e4000031001d0085529184403c24050f80780030b10503c0d40d09181a0f11034a0f850100144001000f62401403da04d24405407000c1d5141e0028081603d182c00e519001038030b5955402c1410b000c0c0d0306032103811b8802e1000788501c0e4075520344252603074400c1c04124800c41d0649034251001707114000c144c08599029003036094503401c00c0820003850304080300710406c200c8100140c42036020f200d808082c20201940 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 713033390 1250 713032140 713032163
    0xe010c051006140f0a3c03051b060f09090c16050a110a1d0a0905010204090606091a040512010f02211e01050f0301060b031609080706080130 62
    0x908210014444c410300c1c501c0b5902c20801400b4060800c030308081d0324030059002c0303060515202a90101c030314010003000d09103148442c000061120200744050f403a0307050020b10b48820030042c1040840c2c020300812200c00345060005001d40c1c24003031842500100402003090034080340922107222010842803c49240d0031000343c800402065030286214200201c0d0000c0781c013414407050b0030204001c22400903440780e0000120704c03075048951201a0f00ca8010000399540ca848284607400f43c02c0368812240010140c85c0000744020300135548001110700c00c080940f40034130b02400c0140c1070010094a488555031141c441c620b40e0440e10081c1311540c540c0a80d280c000d400c420010400801c01800020f840e44007032402661650490115419544110b400c407403d403450300c01003030041c42a9000ba040110b00041072001407080c200d4215895107181c1c3d101c4003c5502d41503a9601d6400a21030000030030315041c0140000c5000d04411184000d1307031030382d000114440040c5009d40d1b070304001e815281e510210 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 713034640 1250 713033390 713033429
    0x2100507140a020f130b0a08070f2403051e040b06130b0f090907051504140625140d0e0f030c09040807050114100906090504030e010c051006 62
    0x10700c1400c07035140100050400c220541c0c010400303402482c0403162103801c100030320b44018000c2d680302c07110040000d05070020340c030346480c181c59903800d8030b0098100300303903407070000043c2c0c4042d4042d40e1742e40010019025029041e021000d5028103405400820b540c0300b164840c3c00701c516203002d198482c50203030456034000d0402a0520143e6071000c00308040c41e900b0110020219100d410403502c3c21401502c14903040e0b600d0340d102504001c410f4102c25403100c02c400f04c62440152880140c4240c92400c500100710f240107134100446840380080380816000403002410a10341c0d001e401c0c0c8141ea008189104000b0180c4218509103086810410003107520326032111aa4201102e14150850050740101102c03c07401000038820100180000c10fa0400024001304111007904103100c4000c080242c0740030750601d001807a50581f55406500b072154941136000500700c10b5402054061901501c9020307190036040011a05020070344816174140c810510380802800241c8035205c01006103000c01e02298801 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 713035890 1250 713034640 713034653
    0x80a030513081204050c0d0f02040b030c0d1101050d18200a180e1e1507050909100315020406110a0305030c0a02010603050d0804050d0306060504060c030c02100507 72
    0x141c100c1211080116a41e0000342d290401c540c401d0210382c0810f900ba41d501d1403e5490200d0b409040d58000c407082c41e104017048a0803555100f858800c0354180183e0100784141652800100c51503980302e20000302c2900400c11013224180001c4042c5041d503d804050f1803000b06440400110071841100c4000c4c80301030003180080381a50300c4501c040c0701c1442c94024000740300200c03540101410b009190480100301c3c4402d0f4800421208130505a8040d60b8140600d0004440c4a00c1208101d028030040c003c010102040424840c52003503d400303042c140c1031428880d50b82d00003132280344c038000c00e52008400304050a0302c000448490300000350f991410400000c0c4003100081580c7d4041d0b0260000031700194005098982c03144140c51516124179003900228003500e015440900680175182d581e61140750b00001a521640c085d05c103d50ac1c00c0c204034021402c0741d1042c42010b001075801d0205207c4584950303c0c07400b00500038038060103540d8041d0000f4031158400040d41d0b0220314009501020003d5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 713037140 1250 713035890 713035901
    0x2120a1101051b0f090d17032208030406050c07020d05070521031204020a0308030405031218070605030a02041703030106021e0303010311130f050a0506041a0d050304050607080a03 79
    0x21000c46400d42400f044110340503030140303200484021070f000c40d541e0050340380c0d80724060350b003600401c40f00c4d035000e0913112200080c0e000743d8011904500d07101402c0001d2a000c4130065a069200400c81d196985a031140c000420015150300304080341004030320302603540d09030a85801c40c040c0d00030b4284507103000704104e450030320310040700b0b4144890032001089020100548201080611000805640d0741c400500c80d81501e07000140101030100504c8240600040900a0078080b1284034443d030f01c0380c40d18480c50100e03905c82c200e17003035009400902c13441b0720510240d0f13003100f00040b0140c00d00e52144000c00198a6100c55840c00c0d6201100401860f6810841d40304515a40500c0d07000b208613a02c02c460b04c91005000c040d107036042d11a405086a11040401140c500c0b0001c020416411443d43c140003421083d01c1c0415400c0c100004075403240b0300b900c50700c80140f006105446088016800380070034141a00c00507030b000e000500000446456000c000c100c3e40f80320b0105c1d40d95541c4e400d400a401c548 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 713038390 1250 713037140 713037151
    0x60e0907030b01090f020f1908010b030405060613271505010b0a050a090f0923090a03080a0209150408070f06090521012f1806030702120a110105 64
    0x144080300401c0420682d400381410346105440109000b804065058043e00c242211034074560701c00200b241c0000003c09210480d98a40d541c1d03490705981c0c800a054182c0000d0350060305c550072000205240e840c110903246044e14a81001068044e0401c81c890744901d0030508080101380074248030810820842140713811003400701e00400c03895061600160075801090350005c24814002591b200130782c040c803004802015801c1c10f00718030940300d50307102d00940b110114a100e01001c0c0104142d0b901d170300c00704980c41418900020003845120351412540710002a21b09800940c6c03c10010540b03486134400c10720304440300348820703036039501e4425854903201040d8420aa2020203807400d001c0681e003c400041101c8040b00c07411800324410300103640150099424101b07561804610b882e911003241400c04c81c2c464071f4010f0f82000b807012a6004628412001900340300360010403481928a452005960400084d02c115507100c810044562040e6200360391000c003040c40c11050940400702406843d5200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 713039640 1250 713038390 713038393
    0x8030903060c030708060d030e030a030905030d140f0702010e0909011e090b010b090103021c050714040b09121603050303180a030c03030f11070606050906011404050f04090213060e09 80
    0x44c9030a11000303002c481c000d0204c40c444d95407088400d040c1403003541d401035034140040903508414681e29000c2c103404224400c881c001d000b00741d9015036030341c003803281d1448280034809030300d20300010041c400350341d544095012070500140389250a626150301261034800c410240c00000c0e5103803c2d075101c4030b209001040c40309880c0e0a0418150001d408a0221411035080307044180d200d005c540d0041e00a030044101c02d1402c1d050b080005810182c264101c0c0e40105026242c01d0341500c6403c20400d06071285004a0882c4481088031162600b004c01c050044481e91500341c401343c800c108417421902146920581d00755201100348108545000c80408100184400400841038250b038054303c1d030006154050140f40e41d40040c95207103040c40d00425813889140c0301c039030b940b8085898500002d144500440e0b00035001840011030f29409005150300038423811b0561030130300e85001e040090510100c0d03112070304543c60b40c4402005865840c0704032120f455102c1c0210701d103400d1000700c026031100240740c010786 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 713040890 1250 713039640 713039647
    0x5030703090b04080a060b040905010e010504020112020f2a1005070315031e021c051f0b131802040c030b120106051e19030b0405101b0e0a0506030108030903060c 71
    0x240d80005c01000070b0740c0c0031601003441054100081e0003080442c0c40604103500741951480891019030080b031246100b603d86051040d01000c80d80708900a0304600c0c00100410000c01038017520264020190441128002610085138000d690501c0c500030600041551a130051000642d0140920b00040c00801e10300c02c2d00901d15141c00035024494081d81c2e10310040e840910040d1f450b00000c021008076140760030741e00440c46103006507884c298010710380f41031408921406203a000501540962001c000c05c1100d00741014650744c7c00a0022450146980c00410308810040e100d41c001c0391040080b0b900e0010304000c02c20280071900b0b880500c1c1c038241c1d0745000001e1006984108000c50310740d009800c4440e408802c01c001c41c10440c412030541201c40b000040000c100000012020b118074441e01c152001003c0048400d0207440440d07100e1078030341e000d60098100c140d12480c800d240c0301400401003c0025950b0001c5052a8802e07001040c040d0400500200c45003001c002c5140c00080b1503c02c1840c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 713042140 1250 713040890 713040899
    0x20c060a0b0d0233030903180603160f2a140106030203190203030412060b030f070e070f0216060e0f01050310031103070305060a061d060d0602090103021605030703090b04 75
    0x340144030031315409414442c05490b504500b81c200c2e41510705014030701c1a43da003012005151b4a8005038030050708180c80c105520464101001a240079000c0c1c0c3d00101418545000299814200380401201300314440c45190410740e40010340040040008510b00c01c000d2450502c1011a5808103800f81035a040810420040e200000c14408405402d44c0641e105241c2d0702c0002e00307601c140c0e480900310302400031400c0c082c084164804203004900b1000c940051000d08215600c401d102e206945521944400184d800da000703504000d60f560340d91041d2215284801200350502299030130403000070f00d00c500600d80c00d040c40c0b88008400c01003420700c00d00b1403030804000105207200d404000c10912540403101c0c01500d04104090185510070207680240c03500c620071800038500c902c42c0700b90483e0901c024410981d0303036410b114010344025000d050144807948891001c5d5100c030100300d0400d5070800400488206841d107a25656200f00051036a0700460b040041081c0a80d8112545082c8100020070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 713043390 1250 713042140 713042149
    0x10e04020a0e1006030218030a0c0f0e04050d180305011b0306060527040608120304051002070317070905030a03050c0c062d04090207080918091b1201020c060a0b0d02 73
    0x7003c850070785c6405a030720186134204e002403002d8800c8040e0148525006941002817039000c08058408440b0100542955880c270b9101501c0182c4005e4015004201d595a0551091500c101c120049401302c404d000d0b580e54869003140c40c05c0109030007803440c0c4106500b000790b1601800008004602d000d604091460018185289507402200e40398003424000080076210340c2c00c03110050038500c0554440c11144c548044181d802160111080d001d07520301c1d414940914401d40d004e41e82c0680c0c440c07401100310001c0301c01e01071002d03103000140482d0305400199680d0810580045a20940d42d244d15040c2c3c04901c00d25100c00c660225200ea44180045e102d020301928641070101b09081c5031030480010319030000e086126507002903840701d0000401d6130501009100511030103c2c15982d0300281c1c8030805022998000a4443c2722107130304228401011802c4001c1c1484900b10000c003416001d29a00d4100703802c9070f000c20542002900501c08000184800d40325005407400d003603480f00102a07041c0e0008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 713044640 1250 713043390 713043421
    0xe010302041a030a0e06090d0314150d210c030801081902060304110301020d0204080606181527070f170a1107170d0b0a14040e1005010e04020a0e 64
    0x2002c102000c80060210290b07034100340448001c80d800c0d1115810030aa00d40d031940c00130030201d03011a082c1180c480c0b101d0022070303680c1e120f0922004810b07200140102007020030302c11900300392402e07003440d240d0141011150945205100094a600504c4031807840d01070424a016030103007038650481d0284000c0e40207100c4c14240c0e0194111403d559a560b20701c1c0000e00c0d080d403038240c10341541c03000c0b5001031a015154014010360702074404031101d55a40030200106250f0410091400e40e1400021402c0c000407103000c02e1030307c90300811088020140300002e082602040c9101030038940385030203001004d0b0704000d00c0c0305c6003c00c030300d80071140c55024032500f80b500d07801400b405245560340784202c0410030100141c401e02d5071700141d08020b051602d100446282c105059000c0d84900d0002c05018502d09404010211468034901c1405d11000c081048020710030424803100a00900c0031100500c81c29100755800303000090441480380c06c1038010700c401045a07400c91112401e0303142c1442407c0e68001c406 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 713045890 1250 713044640 713044679
    0x51e0d02060702010c0b13030305091b0f010c17040f1d0f101805010e010602032107090506131508190c0504050a260a0b0403080c07150506010e01030204 67
    0x150b51600907100480e241c080114002e00910307481418014640356403030b08a25118042c1d40c060156071105000543c0380d245a030220080e15113440780d00d05440c00e004140c0d500031501410100140042502c540500c2000182d20403506200010144074012080d0780380006042448003288010b2100360f040d1070400805000c1195140030f140c00182c4020000b203002016102c140b111040b02640351100901408083c02504125401200040b944a20001c10344405101e0445012265020315a00b40d09012000d0075503420800d824401062035103410000340b00110a400480703150302d144c40c5d40b41d884402041400030403c09400148440c591010840880003d4041d0002a43c2042018155420302c0380c0e80c480d9820810101001034a8002245041d10260340180b0380c0b10070845900000e80c4030541130500501f04000c00000c90080780c407940e0300c1a8070041c4814807500d0070030304e0f881341c510290030440e0080b4040e445c1e000f00410307968000b2000403416028202942060704242c4c85203c0003451052 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 713047140 1250 713045890 713045899
    0x902072003070b04120209060f06040e190929070909021c0e03090108221e05071815080c0f13051614030403020705010804140708030301051e0d02 64
    0x80340000703640a10200004000248032695141d03070341c82d120500c60114001c140e1240c0603000c002400c1c1d0806a1002c1507000006248910f003608280c40d09004503000750800403800060410b9002080180c401c0200c030501a0f40070300c8040c0000c800b4490703e007007250380c4e00559190f084240403505810402c078106441074041c01603100d120480c01c01074100d0141c40a9284182031544801078200b0100041040b014280e99400d131650b0752130408240840c0107094202d05e00c00d1b0065103c0880c1c1358001340d04c2c0701c1d5241008203407480910748602c0d1030200260461403401032408400f11090269204800001310349044500e102c3c2d140c803214580b0b076420f40d8920382c007800642d10145001c6d507d20b880c40c910070b0090001000a4103011484400040e00043c258002c11008400982c0d6401d000b01500e1140b03602d68005c0c0040b90a22004480d040400380045070312111424000751610b400f0700100c006004180011512980340c5030030031013040c2c4080e003002011040c0d40040500b54403410100840c1a40664 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 713048390 1250 713047140 713047193
    0x1502090105030a0b04020c06010e1b030105150327160e100303050d09020d1a0108031606110910030c080615031f0e010303050705011118010e1513030507090207 70
    0x1300420041e2040c81481c0c981c9024500011500c2c8036080040c5000e03020190807003812054122030740307240348804c3c000c603503011038880c02400402d045140156441007076046034120700380301d500c90f4150f215048040d0382c5550708106e40c01e1508030703104402600100304140212625051503003081d60120200d000c05403c1200014a0031101030160304031014140e4050417000e4019618104030b02d02180f002d40c0c2d40351072035440c0c0001a1031200081980d282c82c0342581c0280c14990300d17680e070400034007150414007124102480f5407240e582d114900c419522600f51004540b50221000042074050010146e03481403180c100d0301c802c3e600005e42a0307980240d01c1d40070300b81036081c0c141d030b5480c003100315a12254956074500004020940e0040c040c00c030b1244034200901422880c1d255a8140d03000301361100c00001c0420174011095031080b000d2101c10302001e03101408140f05440742c0c0d41c05601a52198041c2003500c2c100f0801c001d01000180010310f03640c130045042000703c0d0b6510392a0802071b004501003c90340c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 713049640 1250 713048390 713048411
    0x31a040606150c0b01060c23101812080106050406031a0a2301142a010f060806060306040503040e150406090c030e010e030d020705070302090907031502090105030a 72
    0x180c0c0030001420200d000c1d0305004102c000c0007400c203041e021007103805610303100000603e6070040c85800802c0364070211803881011402c0c4c0350710084559048c51801072049101840280c8002e00c10360b0b50300c1c000b01038003030710316403550500541101c00c0c844503008000300d403001040b2461381f2400b550103554041c50085056101c0c5800d918800d91584d440d55400056680700141c02ca0024a03010303900422081007030043c1404000554110420700c240c1e82c0d43c02010040002c0114a050343d400d003c03218009280000200600201d003180c00c502c03019503616075549003e20140c0b0040000c03d6002c1130840042000d885c2591721961a401507114001003030900788003003070005a48100460304810080c2c010080c0300d13030f51b003a000080c10300d07820441c02180c0351049176616908180102d1848081e0200214030b81009031803000000d501442c0151440d01884601000591b44c10584c2ca0064040900401c800703400c60a1444c4105840604001c0c4648100519455a41c000381a070b640f00da1080300004494684 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 713050890 1250 713049640 713049653
    0x150409020907021f0c0903030e01050706110912010e0a020d05121305040605040c020601180b031014090712030c0303060b12100b0906070b0a1b0203071506031a04 71
    0x22410001d5026125900304000785030b0000b40180c2990401d400da2000a00740b2081108070b4005140c920b0005a41090030300210b07000e100350004451041c0b4000340303400d5071600c0c0c04084071407034038214a284400048095a500c1d10120041e80041c1c000001c0003425404c6421923620745410718000c0c016601d01d041352040c0700c0280305103481c80e2038644c0c00c1d039a00d0500c104880b450180d5402114400d51030928041a141010320405e0713542030150300100740c3c40c6d090501c00403903150168600c108064540342c100900751014001e621070518560400320301381300480c0482609440081c1401a15403202500f00a42484050009134003505410211190710b01410103c000d007010390040030484400040080034004c00000e12403080f078100300c0095006448445240b442e01c80c02c0b0600760301910512900c030201d600040003e4000c2d800c2c51000074000000100418080711138141c0c0d5000d60804200b4005000c070f003140e072018203c10010100442400c6903a80e1806811881011a542c82e2140015082040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 713052140 1250 713050890 713050901
    0x90e010e030a020c0405010605030702100e160b0d060e1003290106020d08061909020f0c0f030a0e041e1a120708010e0d021c020a061515020f061504 65
    0x40540540781c1d10401002c010359a00441a000ca00480c54140009650303031240090b28068580d030350141126003e08106040038003640040030340342d4000d20102444464080303503050b005200800c44907899100c1e141281085030056070003e101c415084c4200701d0b50381c51448140c400d403644885801c03024007a040248400b249665070f514861442a0300118a0603000112010509070aa0307494084e41c2d10300e02400500035100c524018541203400d0140603201c0035802601c80f210032080240c3c20808012880f074500034400010b20040e400c009040120f03c1e51258044000c20030030741c0e007480f840400802c40e007800c02040014001241d83e4440c4500140d0103d80b4542c80304000411804c0e072200410782242d01c9648510420302c0d29880e00819031000c010100d9014060700d999000303030400d143d4216100c1c24001c805203051003103000d001d01c4140082c017248a402032004561544c1d91409080140707039110504c442600d02d045d50303c10290303071080f0440012039907030108110140b80884d81441000c03802400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 713053390 1250 713052140 713052161
    0x1020309151b04181a0303042105030301030b010527070c03030207150f0e2109010c05030406020319020c090a0f0b0303030903030a05071407020427050c0109150504090e01 75
    0x8001400194480b1440c0f80040c0310f4080150400084070711008885e0071605145030a90143c00621040010b0358000340340320005e41800c8101c0012003c5661454150f6009810483d00800342d14014400f6051090240e1902a070178000c00384040480380300b41400ca0f500514080401032050146400c061080d0140c403101c560040c400c0004c10000003c0c48090002400e903980e0262a01003150121b8000150300f174981024141380c035920040340260380030306034800c03004c0e00d0500c48505640780001d0300810040009040a80c041d6494201083c1c20800b80d41d14071030b04000315408000d41800030340d84c1242e01c41d04141854800510201a050020050704c207503450a41d150001000b000000c4d00044001d43c4500c1000d0303810009999101c8043d980f071001c0c03132603030005148180014001401c0c43e0f800100c80c10000d51070100e5052000d00d010078210b0110344101da07550007000c40c014095800202460140030403418a001d2a21030200c01030690059102c4c03a041e45459207074231a82e1090a600c4441c122 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 713054640 1250 713053390 713053441
    0x5010c09120b24131b0c15090f140c0a0501090305030307230c0109020f0904050a03050706150311040f0e030a1b0b1e130209070513050a1205010e0102030915 69
    0x41802145440040c01c0a145800064407005421000c1d28886e02c3c180c1c2041d503205060101520401d070520005040c9000304546485c0c0e07404a41000c03e1040c3c5109e560303500d90600800d110700e031940a02884034101c1e48a0340c1481021b04042c4006280441503d500004520b0101524041d109580c0700c03010000801c0b501c3d15400003410240c1d428107421543c40c01e40291544800001c8090905c0240f5004445c0030b489600401c0d48400003034407910080c101c1d08d0003101c0208102001d000130040c08140c07035008848841100c080c0071024200313409002c10540265000700060b0088103010380d00c91003107204010800240d82ca04010303003e03140041c02400c90b08110b2aa2840c07510080703241c02c139200740c0b1000812451510001e072035171465960001c91079030701402c2c2104d25200c044c01901c861b000800400c4440d08907020101320b81e104e041c0d1a1000304103540380062402000d083c51400c5401002052466034010010414440300016940c0c0b05020608482902175aa0800c6103201040103690350051 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 713055890 1250 713054640 713054659
    0x1d01060f0207031b0f050a0608040f0305040b040909020f180106050903030d0609060807080f030406051810181d072a0c23011d061605010c09120b24 65
    0x9030f80e40c07840c44100b40e501d204e010303015031906c4a003040017004443c4076100c00100400000340004034035808d0b020544e40320307090141c00c00fa114002124143c0043c0c0010300c1c0b46035241c403000d00350b203003083c500c25800106440c9910784030388207103125007648414040c00040c0a4001800c4105440400403110500714580c2e040140640369182c6e030b406003c480c81034900c2c600c107110010400400108080e44148206001117150519100c800e95994000c0200c40042d000b00107403c0c42c2980f503000d081c2c1c0041e045543c03120182b546412030720a0300d60140e0441c903012039000c02c1d0080d0070420b006400e82c002d0040e0404d19000100b81c030031100c002c41c6405d111040d05420b4900c0c1d070200144c800c40c10003601d424220000c5480c1d0400750118071030a01c425110f00141040b41103c10b200c0b000e0410000003140030300441c1c54010040081e141020444404842503951004054111170f4000c10500c00390880000b000304061281e00e4004030703040d005d4801c5035014510a0800b04043d414025410884000713000c1030034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 713057140 1250 713055890 713055923
    0xf0e2a030a0605061002031c051504050a09140a030504050d050304170709290d0620070b07080106050a050c1e0a05010e0606010203180321131d01060f020703 69
    0x14001c01e98004d80254010b140d03080d1018008000c0c5c0703141e1005014400021a01c02036004003801003d0300030034281c0c0034021022096200c900813184a40c6155901060041451401603414025800305851a406c1106402c0000703900104445c115070b4104d400046016050504906600c11075004250810a01c00c48400c203a5021550b031007100d40c40780c0700b0050b00e408440381018007030070754a0661b03165104031417078141703460404d204030f90b054000c00001076000c523408601c200c07503c0350b02e10600c0703400c00c0450075101704103001c0030040e800101441d00d12081c1d45000ba000d40385008450b100740c140000403464503100081041650300c81c242c4403d5804103528076140780341e1140b200b084165019420070700e0004c0910f00010360a4056207042e40214503041ca02c1030714900381c015010800e41c0c9030081c0c00418280034598844841e18190005900e5030303400b4000c0600000e5550341e400400c4064401420b076001840c400741c00c2e41150340d00e0504004071030380c00408908000541e00001c1000031000fa443e43e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 713058390 1250 713057140 713057153
    0x1b06020c01060f031704031121010515041107030f2d1e0201090b0c130b180a060c020f040e1e100b0a0e07050a052106040f0e2a030a 58
    0x1000c407070003589681d080e140c0340208505d142c40303140800f8048031480c00e040480d034141060310f40f070081c0c0000e410001c0d06840d20f80980c29510300340c0f85030740340d12035842c5240c405240500c43c0d03808042c2d151120300e1a148682d50081c0c0070424242a072801e22000d26400310300f0040760030f081e0b0469071010022441c14003207400054015180010250a50700030360a540100703074014414442c009800181c600c0035030f5925442468103034000310000880b1582c42000007035031284800609110901c42007142010f4040500780081032040e41e004401700250380c01403c4c0036895456449003482002d9501041c2d8042825a140ca0041500621700c50701205149001038240003207030700320540100e5841442030460f00810007008502d40d02403003c081107010b0106911a00410050482e0b400318140320b400c084040071900b000c0f0212480c0003030105208003c000ca1480d241c0b00300e101210b10110b0400c481300e8038103003032565011816a007003030103610740f849508881c420032501192048000c0407180ca07010b0629041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 713059640 1250 713058390 713058419
    0xd020a0804060f150302040c0512151212040b07031e0903060606020c090a0504261e07050309010f051c0f051302130506010c0c09150f061b06020c0106 66
    0x80c2d40c0740380341461011007100c00d0b004000d80709808410880400c0d0039178081000820f202180d020034400f0421075518810040e8000ca40318902501e1a11000a201020b01c05904000402000c2ea5000b002040142040d220b0035102034440c141032441d2107a0007440d007612444100b900d52140640076107108680300754004120710030b03a0301c501414800746a480405036a5403d01d03a46140d80661484001011904558081035000c0e028603031060480400c5082c86c0710311075403a000b08042d200009560010400580a00107840440465040c58200c50303840b007580b40c0c044c1003e030a0400040300c40e0000d405200f182942c400d41d5106c1e00b14042446140c030402c000348056a540c0c110360341070000048100080c0707040404250340141040741494030b0002500000e02c80109018188000c010701c1c0408901c007901c08134003400507a28002003001034920481100341580d800a03015100010040c0301c002e40c1309152035840034601e851511100524078040c0c000c0c0c0118495159990310b840310015400300c918404 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 713060890 1250 713059640 713059643
    0x60315131a16050906071103010b0402030403020a05012f070c050301021b01061d19060902030c04050f0a0b190504031a06100e03060105103e0a120309080d020a0804 72
    0x540b40614641c842680c60b4043e000c00030f80e003c08103206e501c01040e8001d98141d0203c00040c00003401b6900c40c00010220381058500741e0060303020300643d500300b000910517803280c12618031004108500e282071a840541d02003000b0000781a001c00c1082c100014550b07100c0140c0310081c001d645401d91460404d8050306d611f0450a41d80d1f00306000001c1e06404464000203040d1454198002569110028000500806036904400e41d4650002440c1d460510195010307182c0301014036601d034680400c014a01c2c10f404040781c0704024968081110303150150854001c2100043c40c080c60000040041d5840d0086610103070074184002d007010058100060303001c0c444c10040316164040c0d5591b203c101c1e045050360070141c0c5c050348a07400510a85c900340030264070100c03240c0340201a00400000350500158615615080c18455051407103c005030744c4010100b26594400070545101180c40e6080b5140b1050036030002d0540e900700130000e009501049030b40040d00c01001759550008210000d0800804490 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 713062140 1250 713060890 713060911
    0x50d03111206060705031606060302040606170a2c1018030e04050406021611090a2a1b2004110a030510050d0b0405060f060315131a 58
    0xd0210300003100d50075145030703581c20034680e61680c0d034010911000d070344410f40030f40f0284030620841c4000110410041241441500d000c120701d071031071040c0025a4601d402c0310040c4800700740d045403200c0c115a840d41d88144401008101040c410319001800e600c0c0b0403442401c4510108001c4d070b8440d000403041d80b0403a41100030401040c103800c00980740740310210010002001d04212800300c1c41c043d048543c10500400b801032501072003000c41840004181003c80b4011805240882d69241060b0382c240d010100240521950307a450456802d807041024807007400150280300160301c01d10488900801e000f840480404007112800c0801001c3c0489203040840c030014198841c150419005501780c50708000d00c41801d201880b202070340505001000b07844000307000000040d01e90b4890b2600313000c0502030030b40c090b118186418003d0800e440100300160355800c43d000c1c40749903240007451a0301d807070340c045078a030701c50f105c0eaa144000c10301c4407000944000140c1c0d42c2410031466180149000e11060790707 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 713063390 1250 713062140 713062151
    0xa062d15090b06031306110a21020f16050f031b070b21062e1205060d0201050a1e03051501020a050706030f0b1c021c05060109090f020a03050d03 64
    0x5040c4070603103501c0903032141c02c22020700c0031500d0b548201c40040341d403900c02d2030b003c107065200846640c1e060300103488040004a02201d40420402100c0a2849030100b608065140804039101c47c1d43c207114503480150740d00190380d40d040a1000a1090603040d110b43d5068980e5900800c0301d040b07196485a620f21800c0c040e01d440000c0001402085602c094890b06000303030300403180c403030040b000e0b4802880e480d0402030405a210295480341f6801c182c01c00034911204600e0040c0700000d000b103501031517500c04545003c1c10b12500c1d5442101c1401c48560900e4030350303551800311000319091007500d150001072140c3d5003c00c031082a01604154410780d030b00203902199a9a081c0120b075502c0c50000b02602e1900a198140400c030702c0783d041101204140c0002050891a10001c5540c0e1a14000020f04140c500340c541e070110326014002c2908108150200d40c91810141c0b501c0781c44075418400c1c0b10342603030b6500c00c03082003080a5261000d02600180054112541c0381429521244c100c107110300001d2800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 713064640 1250 713063390 713063399
    0x6050a0e190b03190c090c0903020303040506030709030c0e07081509012607030c090b010c05060c031e071d040c0c0b04051e0d0306090902030a062d15 66
    0x6600280318404518800c4825141000c60034010041001e0319500740c022500701c00581d00e0030503075090711688581e0f0b400144620304243e000860300d032112801d0230060300520410141e54000140c400703540d4212506562912051410764600c132040d40010840716003103c00003809074108003d148602c50544947d100c80da501105214080b008a6145ea406141d03000103000c0031001801c0c5160001e06048004183d401d1480f01905d0306046500450b902c0710154028807400405001d0511501400e082015824a8076942d141c0c031410000c140c022485804000034442e5020110f815070f02050850544445040c0700710018011048450a140404054038102c1c0389800e091003003a010b05016034500103024a03590741c00c0140d1101410a541a10071050042d84051906e40d2205248540c2002880603004410000e002d881c9142e102c0c2038450320b0100781c14003684002c260300101c9a444280064406280e4400760215155240300310030b1480c424401c105988000c2e0322200c25814042085240c0030303510f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 713065890 1250 713064640 713064659
    0xa0203070f0302131a150c0f0c0108040303050709050a0303030203060901060503090c0904050a05060f0411041b03150314070e0c09031f02070f0b0403180b0a0c0309120606050a 77
    0x21403100941145402d031000394400583e50116424203805d24148202450740700004c2d2644040031607414207201c00180d2400c510f1400c001d07488281641001a0020000103800a801c0a600800c060241030b1100002140c6510502c001000b0300401408441d0144c0c490500800a40086070035034000c09400001003201405a81070324882d14011000b41580c2e8004001e000c0c2e2040c010b0800c07502880f62032000030000c0d000b07100740e0388248040080c01c071807460f290138070b9694419458522402240391507064000000c1d4001220020141810085440007400040800c98061a440601035100c000d4101d40e9200c40840c00e101141c145141c805465100c503018009035200d2480c0040d8140c1c00441c40d0088502c1e20300b64580d00910700580182440203d48030000c009800301e1080b00d44159000c02c010803d03822040122002e40f01c1003034a80001d05050100845209840088040c4411035500504052103401c1c1c0601828690518024110f01850054042c0986000b41842415040000700300d0000c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 713067140 1250 713065890 713065919
    0xb07080901090c06031a04020309030c12070b0a090206120408030a0b010302210402060705030a0306150302031b090a2301090b13060311090916030e0111071407170a020307 75
    0x403c10403c20306030f850b2031070643c0181003110324510842143d050045144e903ca101440c0303e201d517034015590b40c140001f0322a0808042c0505581514011f110400c081104000c0b10340c1c0c03000c41e0050000c1e00114030f000060041c01149007014400c00740030104401c02040724069400b440740d0490074040710040f84015010f80c056805501d0502450b0045681440c100381303910742c2c0250014240c140341c802191140e5086074070521701040070a4440c00304002c01291074200c401c4014051130218290701740b0310007a01da203a0755251400a030960100d460f00295407801d5403403000384000320603001c3c80240722214074404405810100e001c030b041c5081c0050002c10f01c1c81111820f00d25080003202031410000240e006043c5490f200d500c03048140109102a152190124020010030030310305201d05402e8802410340d601a000907181d40d042002e1440202446403d54000d90340c0000320701d283d07903010807101d85058526404411180d017045441e50310104d010414001c840e000b5010b13a208141c030764115410040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 713068390 1250 713067140 713067143
    0x70312140d0b0d0507030b0114060f03041203020c010204090b0a1d0f090703020402030c0d060503010b0d0803040f0c03030c031106070503061207052715060919030209040b0708090109 80
    0x26810401c6800000c0300e41e00ca1256020010708520a1401e5501c0b5070307103080c0c402d030812241003280742e005010030720602004100b80e070b208907152498100301c51301001d414000a00700400340d40d070384000c0703803d1107002c1d8041d00c1204900c03200854440c0d0380c1320324130310207024a03402103809040c5190b004142a410075454903a00c8101070220001500c50242000c10800c1c01000e1074441d00400202100580d100c1c0015406035031071841241e1101802c5842c54100e91403175000ca07101c2d80c0b400074401543d071111025151000d40010b605a162364403410601c0c0e2406607248020200246140040101900305407101c0b40a4001d90f5043c050310304007521103565490544040000c00d80900c0050f01c0307071415070a020003046035042919000c542d80c00c04200402c2d15841c25610000250f00300312811040d003144142c0c400b40610601090084410205000e841110003c500074080c4500084440e000e101d115001940c2c0900307580280c0c506818100c0421009540180000c0c0003400400c9034000140114003403039 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 713069640 1250 713068390 713068427
    0x30506041a0907021507081510081b070506040308040b0c0301060e0f01210c0210090b0402060c1608240405100e1603050c01020c03030a0c02040513080a02070312 71
    0x30400c0240c82c0700010050303000c6100301c20000e0035854001d40311601a80d107a0700d0300101c5040000140c50158102c0a034940a000050f448049407a401483c103900f000281241d0a180503101c1c846064500c81c2807005019403080c0c03030900c802c055001d441e0511540c041c60b00310382140c40e0401070307185500c000c0c883c0c00c00107110701007248a2442d1000302903e078108141029403440300041c600303d0071400108640702031165078070f55400119405001881949061100411210341e066071416085d16014001034000c0c8001f146014141c44200094561202243c42c04020340750340d810725a655034190307080d08040203415110b05940e401c2ca619168001e0b80d100f070151020b034004009500040c6104500b6900901c500401004901000c4002c0b10245010704080c180801c0e516001900d4644c860f8407842c0264420440c90950036400485041d003564125400300301034035680c2c0c0c542031820b00c03400041c0c024440040d40500c003c0d0001220000c8910034002c416401c0a440d2080e94102031510922489 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 713070890 1250 713069640 713069681
    0x5030405040506180f1302031516020304030c090218032505040204080316110d2102060f01090c0302070611070605010906210609051504050c0904080901031a040f020a03050604 77
    0x22080170481c0380c0d4058444801d00d903030b9440c5600041d02d8a4006c16801a60202c0d0710103100c40040e40702c802559800d040c0c00118a03003851603a50f50042c486501c1019420783d4085030441c407999811300c07480c00224005080b242c0760703441302d0951110601003103040511001c4007034001170541403070300940e8200c0f0175100142d424442c2e0702641516041449000304e5520702c1c806404134480d50fa00307040500315402802d0821030880c1031b0f4903080201020410200c1503501a404101c484071040381054156400b020001c50013602d002c1064019004001006000d107003400359824000352401d010b40a02406980c01f801284d13a070304031850880c0c045001d003c6015901f10150580c24000303900d452002c510078000000c0c03142858031801d0a0410003949000352154950512050117400c002c030801b5a403084440e00c01d10704165442040c5403050745040c605064540c00100810019a1020807100402030400e0190120704600c0701c00943c000351195000c28940310103e151800d080c0700340500000d601d8000d000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 713072140 1250 713070890 713070901
    0xc0103060b0d0b1906031409010b0a0605070501020d020a0e030c09010e0a1e0207080c07090606021f0e060702030a0f03150b03041e0b0a0c050c0d050d090602070503040504050618 78
    0x143c40d0b00505076400044080d81542c0c0c030500c0d03002030f6006100c0d135503000038240800f840c0c0c4c880c0d50704083c00c4602c03030ba07040c4100103001c1daa52206140c04c503512420301d16030314601362a10502a0003034070315484010340701088424505810061404e00e80b0780c01c6041c0e403142d0700e1041c10004560400c2c09118560140400000c511200ba40d00258030160b04d41210001440400321440c281c1c2d010b04800c5851540c04a8680210380040151030040c1000701c40a110b241d0410300003d51300d1030103981c9000401410b079042c0300302c0b12840d8002c2c1191510700060341c0c000e00c3c1c5110065a01d601c00c034503400c0081c2c4052381c0b515200e486072094a00711450307802900d10907890300032800c0150b04040d00c1600d11400e403072160600c40b44454245c3c0ca40920400f091340c007515083c01c0140407105118604403d0140420680603405004220a0000640c50601a40312035007000c001d8010501d0940c020407e41c1b00242c4c2805200d0004050011180215014415940d8a1007404406400000c0302c00461000101088 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 713073390 1250 713072140 713072167
    0xa08010b030a0f021c0b0901060c0b07121406120c0d020f03030c0604030c1a16030e070b04180605030706021207032102090315060609091306050106050c0c0103060b 72
    0x1034000b00d10302004600e004450300640100e03800b00c00b5040c1d280102c107080001c0e4016a000354074000000719101c040c950314140d4090400071401d5002008020760000242c88a8001c029120210340340340020000c5c0e00812100d081c00780001c2c1c1d00c09106451300102207480b1000011948001c88001d06000760701020342c2d00740803078032130941c08181d4540002d015001da042c6c810010144903901035500c0d0303a4017940d2410160080030780c41941030340010700c0300d04100b1100c058246c0b58030b03050042d103800604a2810181d00f4204100c40c0c01580110400040008580f02c10144a0700c42c101846010060950b07181c007055a40d22591107206d0140c0c00003182c01805d003240b0720207802401c1c000c0c24400c2c00a680000011006149840320028056004c80c801d081030a007009a04079400eaa046015050701300900018a64050401c00c0c0d03200b03240035400500e00460114503103207100d50100040c851540c4450010780503400040380d510701845440e007441c10035803181c004d40381100c055849223443c1100c0e114421 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 713074640 1250 713073390 713073397
    0x13060c05010e030a0e06030a09060c0914010e150c100203090a0b0f06010818011e090b07020a0305030126060c0307080f04080d0c0e1011010c111902180403020109021201020a08010b 79
    0x452100d03276691541c0c00442c025008410800070700340e03030390400d9038103014454403001c600700c0c0000d040289070700d45492141c86101000c510740c580340c11201e44400c40c0043c0c4038034054410a44401060000c01880160400003a5900045100b0045407003c2d40c0c0b10b84142e0040381c42111064005084000442c1e005003c41b521054002da0004c00411041400000304c0b10b80800c41c4400c40166a4a289070424820038404082d040700d81440a0055150f40b910300034070320302040c000c0042c040a0144112034151803200d4414a4501d81010341e00c0d24545200364408982040310350340003007010030b0006800c40f032140f0b000600c2181c0c44004241044001c6041c040100202c0180c1c03010b0100d041200c07101c543d0341141c00b450002155450b200c2c01b610f43c425060a5a0006009009120081c80301490348003001c030703501c1403558864910f69008a01400020020707407000425503c0080712905010506038103402031800507000b5120141d40c2802071038040c0c00c034812010705000148010005200e0340d41d588006 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 713075890 1250 713074640 713074651
    0x906130f0b01152a140709093002030d0207020114030a15090e1011040e0103050105010f060e0618030705060f0309060a06030c0b090613060c05010e030a0e0603 70
    0x80c81041001a034545012440a0b0003c00d5419180c00b141c1c8a100da1011130001c1200c007003032025580100024102580c29142d48005201450740e4007012a00d070320822155008226608040c00303076010701e0601d07070303250b4410002d4034411a0740d01403203140f00315031200c19038592116613004500c0e00074820700d01c40c0290413002d012410000000c04841841508102070341c050000c2c0c400000c0d1083e070302d00740c008452900d5407000e80702ca400c20110b142c2901c00800d0b103001240000c0804541d02d26141d8204809110b16005050708080072030000c018030034150710080c10703590221081c01c40d9645686007901c0708220294660380c8542e04022500c44001e617400740d8164070b00d020301116483c94681000509903000703942216401c0d031010041180c8020101b0030306400c4030913140100906070039511408400304050241039405070000881541e9a1034460403103100405101714141c41c0c0d5204d2500401d031255a8000755219030810078402d40240307001c03049424420003070b143c415038041c0e080c0030b005507601700a09 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 713077140 1250 713075890 713075903
    0x50a1e030803090f0d1b020103020705070e0c07060b01020307110d02040b13020a140a080c16020301020f04181a040c0c0c08060403080903040f0e040807020d030e010314090613 77
    0x145510020b0341c0034030010405400c0b0003035440d0505241c920300b01140350030403001449200383c0050036802c2041e1a602032901507a201c660303003062441c0c1101c1e98000740500211b1010000903900b020003a00c24a8804c4c041803100384152001282e50b0f018800c00a02000350003c1050818613204014544080c4042c01c0445c4903401d81c00020306810789501d02c0b4104580000f0000c1400d40e100504072801840b001c101818100c0007c0e0080c8018001006856040d20000721119020764030009203040b1507005000355900c00024912480580052140c829482d07542d0050008548050203400265000c2c50702ccc4040c54400801000003034044810401c003440960540f24021030140b15400010704403602c020310041c01c091800400d03440e030007020705031242c106100034010041c01821500445403040325450781034a070343c2080303c01c521030b540c4003c3d84100784100c042d040507004002d2070003801d82602c0801c03084070410b401030f0501c0800c807019601a042030340050581740f8203003111880a8020354 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 713078390 1250 713077140 713077199
    0xc070504091b1e06020f0d081806040f0b0a2003070c1b0f08030f1909180f0b0102011802040c0309080a05090310060e070806120327010801050a 63
    0x1590b800c5901501e40000c441d03200382100f03e4101d02400c40e081c60040885200420700c900d250780d07905856640d198811010004058046814441040081840011054103403410382c1001d00c0c0c1a0a030500c40300b804c1f40c0d0405414000361901e015485407030314100d05181c1c0110700200c1c10720000d41d0b070f600007404e2070140180c144280d404540c98100422042c803d0007034030100d00d400d0901c651007004040e404841c03d50b1081001c040301000000646194940203501c0700c0300d0286495058501170000d40005007144c0850700e104803207401c10703003000040c0c0381090b20410068409100480c00d82d420302a0020110001c01e01040050900e41d100c001000c0d86490b001460825664500115500c000155400504003054440b0649020b2040300c00d1812002010055280f800415901d160030081c01241480b20680c00101039465900c1850504125001500d03500c80501405650390300c98015503404900d00003402022950090680381d041e074a00134181d07240c140c81c12201240c500903c00510710100381e80d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 713079640 1250 713078390 713078423
    0x50403021c1b050f060604023a020a0509040b032413060e060702060a1404020402030a09080c0a05070b0408060f04060e370b0105010e010903020d030509010f050c07050409 75
    0x590007503046100d040034204c030080d2052a540f500c0005801684600d1042200168040c20841000c001030008000410348450a070030400703910160124690949000282e5035114582c80340042170b1403041141c04000520350501030554803036140489604001e910241a25901615038485138005100c0c41d880750541101d50780c40b029900a004003144507440342d000d0054480e01031101d07581c044511a010081c184614024220058000e000607010329400808034061601e1303500302070461074014008954440081141ca5901c0300a000e0035207403802140c001180620b5040c04540c102c8080304000c101a4075048810042040c010700100c940e950b40b9460344006840a01054400360000550410708505004500d40110b0390051605481c0c421840c08a00040036122101e040d10750a107030510300007020200507075502c40030750406540245412009802c0607400802000602401ea0b50040c0c402c80e020415540c5004014200d1400c1d04021000c0c40b250410703900c00440d0501a080c11008403506 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 713080890 1250 713079640 713079677
    0x305060a2903100f061a04060206011703040b03061c0c060f1107300c0509010b090109030320030f0301090b09071b031e0306050109230913020a060c0b0a050403021c 72
    0x82c030600c02c8880780400d081000d00d40510a49c1c2c010003a090700e034045040cd0f100b0068592169024603401100e000c40400c455860b224221045030780005030810381c0c102c45041012081d100c0b0720802d400030300c0028901c00b1161040301020700601c405401041402d00340341e881000e12401e248600c60303030583c00c0e0b40d0b43e000c085040c8411550034010030108114500b00340501c03c03074290580044455070800c200881913a6445034081c02100d80500d080500b50007441004a241d05400f105c00c4c1c050b21000c01d03a0540b030f80d0b0500040d4104c445011040102e41035800520802540490300f001c007040000702d0f0044920034901104500510a203080d03004600c4203d04400c0d880006003060300000e03501da0041c4032035608010b203a0080c00482c0c1c10340d168400d070315852622854a213210a40135003d0754012842400a0007442e03034030b0700d074010031581005442d0072000300500210002640c104a80c60045820700c081031103858051909a80075004804410031b00900c542101c1510904000212204c3d04601e0304 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 713082140 1250 713080890 713080919
    0x2132c0f1911011b1101090b03040305120c1911010605090405030a110a02041b0e010306180b0307090615080109050c03070c141e070f05010f0f090305060a2903100f06 73
    0x1154400c0c071042601725000500d07511558010410100307003082403201194000c000d803103250410b07010000399a41d406400303002c00d010317a503100c000b1074000102c401c14040e041041c042c00d0940715802084050740c2d800401103021b800303540103400c682040244600e0540b0520200d042e154a400031200c0041031907010404607000600424600807803403101600042e40269034400040d024070302440468109004d00001c0303039030044100405550741c140009a62410f000308402056241400c0282956a0004090880d03445a0702d01c00610001c0011800070a6031203410b002e4440c1c41c1e070090441e9a09c800a0398440160724064440d1580c40b135030403075900410040088605600394040e002480f5040a1914000040d00041100980c2c0313601170107a0b0b6440038640a03018203031701d803000452420110544510069030009032840c01a001000821422600900065400c615180a40030301c00b00608a030760102071070041e81a00400704d00c0850580d19040b0f4110380c0e0b1142c400180090b41d80800b00c42c0c059 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 713083390 1250 713082140 713082143
    0x5150d02090a03080403020f19053601050913080306060304061d010209120a051228080412020610090e100603300c02132c0f1911011b 59
    0x1030000741801141407911082c02e080720306035480001c114003c50003800443c01ba0040c40d0180109100d6000f0b0044565045e07080e8900d90001c3c0404040c104003064bc40ba0340900a4034020300c000b8001c1090254440e5502c0002d603048140c1d68250b880e034030b0030041c031540085e00940d48035440b5005000016020624425020100c170001a0344600750811300005140c7c003400035806400242c80a80414000b2804001d83d080080743c450b541c44810070032800c02079400d034180e0030b011900207185141c183c00c080424015030284101203403400c0106001c0742c1d103060448092007015500e4504020f809510f4028074201e8900384243c5a915000b88907440c00c86081d64001e0355140b07900e0072070a0081785d001c0c2588060110b54032075a00009101d24024010504240009000d0038882c030f95146041d505e64402c10002c40800c91011204250f8400602e0401140b54200d00754080d050700c14900f4500080c9080646c060325418001d4510305494410050848880300c905202e0301c81504410800b40b00f201c00e40c0130303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 713084640 1250 713083390 713083403
    0x212010302040c0e13020a140a03060e01050604240233010b07050307080d02160b0604051f050f060d0606050d050f010e0a051e0c071103010605150d02090a03 69
    0x6626600410080d10044005101800601c0f02c14080365180c01a00900c0b00544010160b500d84000b20112144c800c014103061031000701040d01c0d290942c0c540c01c50000ca803944042036810381d803241300304960ba100742d105600590075420103000c4d4003141c50258101d0b036441401a101c00d445401d0f03c2c82d00020f02c900810707900d050403164a000450b00c0710100b5002d8981c1003541e40c00c24074299507843d1303a880340d620003801da40b102248407111951207030122480c0260f0004c0e4500d503110145070070011a0016102c0c144105d00700700000741004420b1070b001641e400d500b02040c100c94513004c00c1c400c13036440c2ca00705160421001c00c1100c5180c00f89000701d2006001e2a41c44650700d4000304101001c135040500090203016101c801004030440b0020301c030342c001d62028400686615102c02040b51140d292440400c50740e5010100482030f1031b0315014203092800340f400c410029804004140c2281c1090140c40d0b4441307110190446940040d80241105c150250360043c513110310040007070b4085036182e100702d548 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 713085890 1250 713084640 713084677
    0x180503040b0a020609010b090408070c0305121207020f120915030916080303280207020d11040b0f280905091c0309110f040f05270f03030415060902 65
    0x2866410413103241e1024002d0001c10609441074005603180801400103002c500011448805200022808400960b1b001003200d1a040030080005900d40081d00c458950007013040c000b8615a0000c07410302030341810b4101400ba070260380401000304e50424804107410106641e01240078001030402940280c287c040140344004d0885000000007420750805401030b0014400d10074100c1c46005020107545012010541291009208400038051100c010f54421004070310740c42409501031304108040000d0300c041c0411500c1e001070128589001004035001040c4006a441c0c800301c0300c62001d43e044000c982e030540182d44020440540b2020b54000b602c03074100031084c4103055084411a090200e140c142030160105a88452001d0201c0f068614046c0020349083c200780d5442d54001c8140c40030201080000d420486400100500d60040107103c8007603100f0010191540054032046c403254210040d4510364035a0744911181069482c0000d10355216940410001140d00181a192034014615400d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 713087140 1250 713085890 713085907
    0x2a070206030901091704140907121b0e06130b0703090302030d0203090102010507030c0507020f0310060608060f121027050a0b10061b0213020309070e0c03060109030303180503040b 79
    0x44540000c2c1e05c642090000308420042d03500181d10700210640e08590584055444800035940c0c43d004070380b00e4605038039001000c09100c8103040c0c00c120280040d680d03055140d40c11420302803907109801c03100d0800ca107004401c004802c4404014500c0d1842450004000c0c0d13030b03a501083c40d00e004007001c240503820221314046e1a5a092150039800b40c150300d02071104000049001d0020b20a43d0006070240300700011142554504201d142d050070101c0300c082164540d2020010441034096a100b441480d1314210b074101c45c0f400c900940c818075003803000340c5401d00e5428001c0d80144040401c40045c44040c030b032441100d100d52101d6082b014041d0014103403c0c401403614003d0f0400080c0594000d80c0e001c00180301c080d034000ca8022203150b145010080709801400000d0303000c02c1c2c0700d017900d60703403400001001080c010110b281c030211031300d91606100c9501c030380360702c1151800700f1034803640002c2c030300d090800c0401e02c43d8001900f9145448403146443c0050b484490965100303401800d1000310000e100c05 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 713088390 1250 713087140 713087153
    0x7060914030c0c0f09190603050d050a14070c0b030405070b040b0d0e0d20150a090515192d022106030d111015050a0e2a07020603090109 60
    0x200f4000300e0394210034540b40070000c0e4107100050000c2d15007014001680c2e6114009a122030003841e04401216144100c203480101280d0103001140c0018602e0105107860005140954800c181d120344050321050918018030b4058000800a9800344904c10b800611181c0040003000a0301002d0002a602c010342020b0f8401d1710b1440219540650010203258990707580406104401809070281100c120b00e4040980d151941c0076070a00b142802003010b0040c0e0200c40e078000e000540c803038403d546950303412680700e101081e4220350000d85121001440c2a810350b96912450841c103080101003010040b0b0740b00c045e82200100e84500c501c5500180a10010f41000e6810030161180041c0490519003000865210548600301100348a00320010b0f805141f0140304a000441000741d0400c50244e4038004c40303c406240f4400e0390700801513040086925070248268620401000d0940086030076206c0b0001000808030100e416100c3c1d00740304800040e5140f00045016080312400801c07000b0260402d071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 713089640 1250 713088390 713088403
    0x106020a06061d0a0b040623030d0f02030a0f09090221090f0309100c0807060507030c0c1a090106050a0b071101020f060f0c0417010f0b0114040b07060914030c 70
    0x941c42c00f10301c801d402401019000380c150300a0f07052601183c2c814865000c0b8000e040706811400c3c0b15018056aa100c0a8000b5202c42d0001821402c81c3c0104040c0c11040e0380700c0c00d603003040c040160420001100e0250059048400c01242460429485542d13102c400c0d0481c4c01200082482070070117500031240c8030f031810b203e40c0c004281c0b002811400d17500840341648c038803071020400d004000c0c10120007162030150702c420301c000d904401642e80d00d40c090f1078240c0c01002c0c00c940100100e4a4221042980391280c4503c0c401260300010481030075100b21840200400010814200c1d5901c440010640b078070707071143c50f0001300b2001c0040c940b40d80083c90140d5403180325403185070455004615142984500003031003a08488030720900d00242e1950f03080c0b420240f050350050004d0100c98452901c03040030561000b1075205070356004104040c02d001c01100c040d0011030860305108018081403140c5410000101500ca1107207800291440c915078481d20b0360034015958003400d4100bc65020140c0e503003880f11 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 713090890 1250 713089640 713089649
    0xb0408010c1805180c070c0806040309081504060f0e010c030603050f0307080f07050304090515010318020604090e01090f06090b07090503070e070c150501080708060f0f040305040e0106020a0606 85
    0x60040090900d00801c241404040e080c0480352a1000030030403e460040c21910051f8100449402181d2a230342c2243e620903094404800107000ca80c0b000400400c04645001507d804111134182e6403240c0d02c0e80c0c0c018155400c2040b40007582c605840c0d05001c000d204401c03202d10703962404039019141d82446804c001e09180c00313005070f8004000550000b5080c400b1214660980400c00b51540740c1e0742011451800741c0d4105a902c2c81c608818440c00e20b507408191018a0760980e0b05101c0d211078441d40308140041c0820094120805000500c070b100c5c06500201e020780418000000c00f00705a880300b2100c2c000c41e60b0292101503030303808090140002c2c90721640d403203542424901e030210329010100e641c0c0c11981c85000034040002020517a0f451148038910031158012803004080c040d044030040c000d00d020320036a4014440e6150004111402080e824031840502042e0255a541c0607074144028030024801c40c10490204000715840d60f4400c804ea0103082c0d0ba600400304801c00c1d03d4500219440c03070b0030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 713092140 1250 713090890 713090927
    0x30221100b030c09240a030f27060f0b270619060e0d02090907090501050f0319110603010602061b12072a030804060c09050d14070b0408010c 62
    0x700030700030760340f1800c8034048142034565a107050100b0240d9003c00c20340300b50140301144005000c2c108176500d42c11010300b800c5200c0c400c01c11140c685440e010030b401303000003080154050030303c2900461150790017000d810031040320201e200c1064034001412031034050b901000003081d40c04900e00d07030221a4800395211000340c90800c1c558111314820442039041d841a2002c10107103841540c56074503414134410440354041c0103d411414204441d03920741c03841d8041d140b0a103141070000165440c08003a80d000d00c03400074000c1d0451801d4204a8001074240010542d8001c1c0905540000c540350304000354020090b0b0360261000d41400100d82c400607828058000d00d4041c1880101c03201500b940343c25402015505120014101c081c0144042500c0c18801c4100200e001d44201c041c1500454600d00c543d21601c801c008003981c1d5441610010060b004503a004640d00c9408030000301003200c04401c0a06541c100e0b440c859035031101d00364980c466000490303076035100c00c0f40600c1150084452500d421000b43d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 713093390 1250 713092140 713092147
    0x907090e0a2d0807080405041e1b120203100b0c060108010c050406050f0306031c020d020105010e0f01050603180105040f050d170a27050307021302030f060103050403030221100b 78
    0x58050892120b00d0241007107600103041c40400110104550041c01c0192091220301c440c0417200d00e0301130740e084680b0f0380203003000e014200e20350201002044070006a01c0740628240319098450003500000c000d11000c5500c5500070a0718403120000c3d00019003101c006005560400088600355070a800c15041844001e001c10b000b440d80080c152000940f0725050f1035101d503501c0300003d2030600142d020350454511718001c400701607800302c0c080e000140550024401641c4e01d107041480c0396000c480b00d0404a59440c0184a2850038400458000b85608135085450364650b80d010f084950558086907000082d01894041017030a00021108a0325410002c2d6104c106503d00400580d0040076401d901d03996030b44d480700341d0914002070300f00390380c0c2201e50402442c01e500d03100381e40b5803013100181d01c105160300746400580580e008581c4214111342d40d0750b60540301d5034019009407602070300c11014103400744104c104103c1441005000c1003030bc03083d118510b0504041410010f011a0400380c888403040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 713094640 1250 713093390 713093453
    0x1e150b030402060f25122d03020309030d11040f0b07030c060b030a06020c010213051e0105130503160302040b0607020904021311040e0114011106040204050907090e0a 73
    0x243c10f80d101c0c10400b07150265a66401036101e10b605400796000010a201141c01c80300344520700b01450f0001503643c03280b1100341d515050850b42c10811030003c01003100c03001044580c4a110343c0245401603500800c5030300300305c0458441401e4907803803500700781f030b081c1c010404104600100c548100107011000030b4510748205602d0080c580c02c030901c00500003685074000260309442c108000c0d40400e411031000c64440d0b4050044601030342c80403c0f940003502c0f040802242a20303114104040c803110500401c10055000ca00544061b00a02ca0070402c4012004001403a920700707001e0403683c0c070001002d21099034214810801125013020030f5038042c6106201a0006803280060f01d40c2240d01102ca00029000c40c14501003e03240034100880c40090108001640403071020085050711204688a94005500c130300444405001038941300c0c2561000d80860050304066000e20741000c00001034409182d1142214019103950001115499001c105044c0510010401105405000b02100c50344103d04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 713095890 1250 713094640 713094649
    0x120909060603010315050601052506050c0306060d0b0d060c030c020115140d150905070f05090f130204150605070605090c06030f0c040f120b0915150102011e150b030402 74
    0xd1103417040742c4c10f568101140c0c1c0c0e6030040b402d50721100944447c2d8124610343c1d40c0090345e01c0721f000004a82c202d080c400031406d6542c005003500e124200103840c0604002c40101d040340500214030400703401c1410f0030f1031800480e880f80548029555241c8000c608111400d200908403890340c0310b40c2010916901c01802015101d01407007440c50021611884040c1090400301c1660340050040c03e00113185c2401079040000c081403c0b41240c01402840011655aa040c000490003ca070488a80004240011051003110300307070360102c40c005080041c0100680700340c1c10507490b864002d100071907404a9080c080050398008c01c2c0e407183d504c1024180030109000482c169000c060700440d0355055480000d071001d0038036406d840082115815012b01c643e41c0d10304e02107210703e10440940e050161075001400c075139400512820203a55085e01400309a440300702d034071031554400a28a046540f94075200000114912a01a11411400c0c00162000c5004032a0b1b010b00c8040e844000c90b00b200303008000143c0d96 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 713097140 1250 713095890 713095913
    0x52215082202011d0a12050d1d0603060d1b1e050d0209011a0f0706020d1a01020607051608030c09100c03020c090a230403031503051e0c031209090606030103 69
    0x4138020000c280b1200b0000107191904a4005044458a2207241020b01c240000d25262039034098850440e1003c918034108440c2d00c60410844c1c000e101000880c1c4a4101100c0520b4420700079501304080209080d01c0380006901c9d80d1001e030044286054030326100c46403058900040c04112080e0655081d60340c003050078508148100309000c10303006201c5e00b03500324100854110400c4d8507e0142e0300e03002880d04000940007a45490300b06850950075007402498040a804a0340058000f04480e5032000d0003107a280d4000f4440c2482c0c494a4000c40f80024400b20140d4000d4220041168541c3d60355410b220050f181c450414041004420811020980220702514883e0098807005104c2d5160203441d405052081c03c2104004000ea01100706407003003d41e40360185100350740030300c0702115000d44034054802c240000b801e650016241c0c0d41501c0c102070450452103140e04140c9858845460000c3d0038500c0b10301907008410000030304c00d00c4529119880700c0c3d002004459080c110750564644006200c0e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 713098390 1250 713097140 713097167
    0x212031201080c10090e0a0e030a050a08100803070f050c0301060303091e150305130b13030e030105150f12011e050f07140715060f050f040c05221508220201 69
    0x20421b008075042c0c602d02c1d0095449201c02c0d5080700d5442444810007860350b423201d5035600004501502040f100d40c4000640012681c03940b0046040a501c2d448141d43ca03c0082d4040341d1621802e41c042105403402e001d202c00850198075071064051401d000d01003114506038410824643c90f0600f4008010340c0c1800b00c07144941450001400d50b50004e41404000740c0202c0900b0101504080041d122080304040c4a0a4403d944021142c10782209150988906540b01280841c0c00b61a156031410b01242442c00c5031002000c01c41800700c100701c014211200c14801004101410204280b209528042c003038100c400c5041203049440c1120000b44140e0a01080c010342d5900000e1000610110922030540c0b190120001c004451b43e901c0e01140c61802c500c11580034020300c09414000f460107100c0c40504c501c460700c40300e2811004410400101001900e04540428003031300204606c2641080100400070315180c00c5120300b0612450a280d07240341807030100405000805500503640401c1c1e045000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 713099640 1250 713098390 713098409
    0x105040e040314031006020c042d02040b03090601210b04030c0813060302031009060e061504080f0318030a020a09020310210317010609030f0212031201080c1009 71
    0x64071107282c00c4948044850030308020f1031000c400e009003050021000c000702e50551702100c40e8210301c1e206001c2070b509006150000184003490040d40c2c1924007400e920002c841071b02c014507040e101c501408481d0010f542d4421940c4c0082d0042c4110880301421144401d43d82c030040c100a000c40c0d54041501000403c001c00b008900c482250400c944c80c0240c4040d40d410709030407214030361549001002504201d40354407403034401480001f5420450322070740054401c1407241400131751301e000502c0407422a0b0607a8050140080100084400c03040c0712004441c41180007035540c43d00360f801a000d2601c032190720b86103c2d070840c03190040140d94410300c28040b22041c100258403a5180c0003200c0100d421640300e0200c2c0f5000060885100101440244101d842a112440c180280c11b00d000000e1809009007000f0072103040c028808a48030412400b4003510040c11107003a03081c4e00c10303214210b41195007080a200e60400051141e00d0007803210612801d0196003030302d019041c001d8001c181c007815100740481c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 713100890 1250 713099640 713099669
    0x60106030908090d063222050703030201060501090905010501021905071a040315061a07020a090c08270a0212070308070b1e040f02041806050c07020f040b010504 71
    0x40141100075600020b03c020302c00b01d42407406040c1034001d0b05101440541c40214520400c0c0c0091240c1c924040c900c001c84074940e03440c1d80d80c0105400000c0c00b20007001c2ea0701b10710f03408040011300c01c01244001d58865800410554a42000500700b80c9480d0000b1400e0b90a050050042d0707680044c0c001c039501640d00717584030244140e040160074101d5540104440c230803080840155001000000d0044a10880d0100c0c03100390825454003c540841c00707050300c185403003452040c82054a00c0900035680c0010480500e007540d5440d0581202c050700c2080000c204910108180044100d40e6250400c045111001c0e1901111110a86582c005140240320f218a03100e1809000b600f00010b2000e10b51103070320a41d0b80c050508140d00001c100310380e0000c814070003100003e07151070184034203401280d001700260390303180aa0b420800a02007260f14034600302d044101600c0414914080c0700d00031001c00000703580da1120b50040c000c00c020300c1c2c02d0140c00345007819210345191360301c081158200c1b00b100d950040c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 713102140 1250 713100890 713100893
    0x4080313060809370b01090b011715060f0c0d0c0302010b0a0807050415050604140913170a05090a090f0b090c16031407030206010905091603031b0c09090b0f0103050601060309 77
    0x4c440c420510050b003800041400030a080d0170b540d0080000ca80300340c8805102c9509000780216006040396080122401c2a041c181c907810404090040b54400840203410031034049403207071030012180ba0407800920310305082c100341502849642c2c402d2200f0750341e02100ca81400c213150f68920051080c0d500036584ca500b1911201112601d400c040c0200410156581c0e554149280c1d624a2684000f0301c02c16002000c214007254034000d02402d942c0c46004080d40040700e02040805d608072900305000c4c40307010821079107565218281203000d45100240081c0c09007010000f01e00b1180c0e0303030409600030310400c0305009010b24044107a0302e0b807584180416600041038070702150303402d20307250f08400d841c00c0114444e41016000b06045060354440b120070451540e446401c940d030703016403030030400c90303580c140d0003d10200c0d00c900d0b0700c1418824807503440300301c42200fa6100045000f0903885a03046c03a940d00701d2042044092000f490708860700b040c042c011941142c071034589170360040c442c2905042e40c2d40d100d41c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 713103390 1250 713102140 713102233
    0xa122a050c0f1c0620251a040f0606060f08060609012307110a03021035090d0504031e020f12010b0a171b030304080313060809 56
    0x40031005811441000c6540ca0f20388440038000c4100b0317054542c40307411802090148000140c440d14030080002c0c0d43c0b00714404000285508002c14142e40142c80e0403810304d07022020382211402244142400009012030781014804c03a181138004208003c004100002c240740d002c80060342000048a046070754540680041c1c0e144181290040d6050741c003581c4081c180c2c40000050210680100d55400041c0442c0b001c1121140c00d9000c001e6109040c0c9070514442445020003980c00d11142d1130009507044d01107044280050720700c103d103000c002c1d4601000762400c0d0030300c8100700e0b42c582c3e0f081c01422300d41140d403685803214600806001141c0e03071044000541d0750707042c4010381c0154042c00040040c8800310101d030181074000f1800b03014140d8034000080f01d610052801c245464208090020b01a684880758041140701c0310040e8544002d00010408210901c020a130810392400c8080c29546080005072450100400c3c0703188030707080001d081c40102c5940d20514549150b03504140059142c0c09501c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 713104640 1250 713103390 713103409
    0xc350a0318150c050c011404121a090102220501080103140312041103061506030c0a0905040f02210709180e0a03030b01031a0d0803090a122a050c0f 65
    0x1098910a002c194486401041035409075005906440c0c902c9800401510700d4100d0184002103047e003000100b000501c0c00b00c107280a58860000300e00c0c08601d1030000244070000392100e9105035800600141044007001041c03520141d000c814806c090301e4140040c1c5150350510003d4400c41400301c05410001d03050044840700c0d6a8441111010b06150500900c50000182400d00a10444002c11503606d00ca142c001c0c0300c1d0800800e0030b886c5580d151409030b501d0300010f040a0a200080c0c0c1c0c0031806a4881c0a2030040740707607003040140c41d90728128138400c9400b05c1d0615100c10100400910a00640c84840038007074603800300060424407000038a44004000c0b114000520303009041c225010940d05401c0441381d01f000340e8044c090080103915201340b03010b1102e00b05d9480121a2401400984681d02071540006040180d0f06039800644460b07045086d40c10303100300081c1031030380c0103400003185040c114145d0040b60320843c2004400d9a60a5480c42211012849802c09441c0e0300c48540c0ca2641c4d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 713105890 1250 713104640 713104649
    0x209040503040e090a02010f18060e010302070209011424070b1b1c0606020d0504140303040b0c0307120813060519020406170606090108070c020a030c350a0318 70
    0x4241e0390301d03101c0e004c0c646542c8444000c0740041d40310b00318400c06500c07801119550000113800014045e14058094880040c11403129051580900003400036a84404440c1c2c000e10b043e0001c00c406003201000c02602d1128201266890740302c10310800342c0c1c00c90010070f07a41c40320392011040420f902c6000880c2c480c40c03045074814460720800903527480e2001065180100104030b203041444101e840740410703a00d4450303020341440051800d00c000c0100b400505681502c1c2580a4162803804c0c2d120010100582e00617000f00c4665480021010100151000441c09080c200e1901e2401801e0a4110300498000e0341009003200361224045541030590109891000c0c280300310443d030351540c41501a01245101018070927282c0001c002030001d080c80d500300c0d50881416501e44a40d941d40c0c441c02d4501c403680c0507069800c02e8081c14080700041c85043e81e1000b81088100a01448038514100c446154014120f0b0420400c1d05030801c8101400007030178040c040d811b007031200722600c0744042380c5004000784c1e00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 713107140 1250 713105890 713105909
    0x702061f09090302010f05070806060d05100915060e0f06030a020d27050705060901172a0415031a040e03220e09060712050603031608130504090b04020904050304 71
    0x40b00700c00c00d60154800c9040e028141401d00040d0740c1c0f69801d481941d011035500b07401c1b58040018486c41045603000d0b40d80181c0b083c000080c8940c540a200040b144203d080340c451300799424081c441c4a400503814a0803010481d40405800b5a05021458070702001d0080d503455900800c00039054441500240d03954000c400e10918520300c0700b501d25501e2110707060180d40501440c1c00104040c1054401c44210500c1a1220b03c3d04d80070010100c01358071401000b08001c500c140c08000100c8100a101c0c02d072801c54013901d561514104100d00d011032841225070824186090414401c2c400311001786104404100d80c001409a403105400341140301d1411908e00204200180041c0702608123280350540d2007880140c07115540700b040d01c0e9035440040e107642c008a052840310654441c980c0c0c00550344440040c050b40c0c00c0c0854454030402c00308010b1011181038001040480501e065580000300520703040760103010401190703e400b5540c90000d0006802000f041000509021080040310001c000c20903 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 713108390 1250 713107140 713107151
    0x20a05151006030e1c023309061009020d060f0f080c4207242901050403050a050309040b040504020913031103042601050702061f09 58
    0xc020042030203088500400e070009148021606510030302ca1400d40e04510f100030564009a40011300740c60201603038000441c452860100141c00e0050540c003000101c0c001280c0f5071700c0302d1880711104ca090040520000d0351000c0300f00040407200c840b1000440c0c13100300c4016991140140800081d100b07681103070710f010003405800600d41700800c034030b0b204480070340d404d0364030120ba07120400001c0003042c58052480c11a0710a943e2510641003a01d088210148059407240d11025441407a00d4221311000e492000c001180500d60b8044046001c04d00420000100b24054101c404410a0701914441e10000705610345412580d0b4050001c4030f02450304902160b00504003803030302c2a92031b40865552070085007041904034142c242400b03a130340a00d90083c28071007255210000c069901040c08000d800300084425680d885045c103000070030180c5142d2020888400f0030582c10201f00032905880360060b032400c000c1161055011404680254100207043c40c000c101114104c2c50724201d4214003500c07442c20 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 713109640 1250 713108390 713108413
    0x616050c031305030106210803060103020910030e2b05091516050c0d020f0f0d0803070e0f0312040b0f0c01140a150305100903030212070f020715050406050a020a05 72
    0x28040e600880f08114000e01855445141c80308814180b8505540130045031181a000204001d02a6610500c180750042c10000100009120350041e400c00c640440d5035503d02810340740c024001c0d882e80c05200071140c024815121080c0d00b89a541c80f04071001c00201240e80800d0782e9403c100104540c9510700340ca61a40c04061380700c102e1600150084402c0d124841d051007480c1041a80c441d9031640041000700d0540c600c10a010340640d20001c0341d80d001c4081200c08001415180140d8010b88565a5074400139101109000100d20303290350580c413a9201150243c1c070340c002c0f1800c4030309840424102ca5251001030030901c0352030045030594140c035401c0400640c241003019055502c141e4003000180000d090841182e00110091300026007e03412881c828203000c02160440d41c0840d21910b40145007111041c4079401e91201641e08900040844140c150350390360410400000c1d1000b112003040c034071b000390b0024115101f1842842c040c40300210f00c101042d4001d2010b04407260b0003074291403031b4200c2c6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 713110890 1250 713109640 713109667
    0x110d0321020301170d050a0e0409140c15030c0412020604030501020a0503061f02121c15080105060a080a03201504031214010504090804050307090e060105040e0616050c03 75
    0x34025020424003090102c2c02c04d0000041c2c07221242004d85840d171030149202c02c101e441c48101c009054101b5114042003000941d2a40342c8a96642004080c4c0b01c000d010f0402c01030003444c125841c0421100c10320500919000d000d040340c003240c070508403c2d09100d0703031440811164012a0b102400d19440071400440b020381040c0118440e0304100c5a00001210480e414140005c2000d1500d0042c0d003d00703514620074004200400c29000202d00701140d4407203524589007500d011070311801104a2034a800c20020b442405802c0d001301003241c85918283c1444c0e000f80c0e81b1221000c000c5d04200008a0b590b01c0b036904540c40c81442c070700180070781d503150000c038070107200440080e40c00b03e00282d4105103a106c03286030381c4503030005c2001c0c09291038a507903c0c1000b00006415644410740f400c0c001000001010358003041610300070075400f034020491050441c3d119007480c2050344441c4c000c1c4d04104000074820b001095181d40010f6100c007014000790080c108403030704e00032821808490b210015150501030007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 713112140 1250 713110890 713110897
    0x2070801050c04030f0b060a080a1104050117060403030b1813050c01050310060302090a0e010f03260406180e0705070b150303250503070c05040c0903110d032102 71
    0x1580009100c1c5454580304858240b03e01e10010305413102140131000050b85c80a21176030030490080c0503200344c540b200c84260800625000c103d4401c0400859103c2034106405105d00400141c4482c44420007020382c0c00d601d543d40100020700f015074568400e8050750716000b5100e6601d008001001c00f03841c01c0340c00000760662408044d81d5038811640303281c12b07131740c4100d04907841120450713140c01c004c91802400390007940207040c1142e40135951400108a01083c0040c0c1c80c004c00c00c144050805600d5401e0200104082504607004592a45c2801c1d0810f1207001c00c503005c0b50704624207441c21005050600d480b160441c3c0145030120010024000ca40e5800b002800456000700445080d5840d8041d507610160521100580c15070014042c401c1e161000c51022000325000311020711080009549460a56100150072034841520344070501803400d141c401c06101172041c1c05e000740c003142591145d003110310002d01c0c0140714a0100409004040c803443c050300c10180541c10080c0c103285801d848001940 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 713113390 1250 713112140 713112149
    0x11030f0103030305130804050111121812010207170a1e11010c0201020306030706140415020109140309130e030405030304033905040f1404061401050d211e0207 70
    0x3811300d00422144044407a4445166a1180d01e29140c50300e040010b480e420021580d80c030650185022280320804000022b04181e600d0034002011500d01404110003640c4913000e40369180c0c41030051000041003200700d0080c40140e850001e49070740401d42d04441885081450103c43c4024007090483c01d900084240b14505444009102c10381c4c001d034080f4200e0200721440c0b5810351010600b042100d004e90309045502401809413442c160715141070040c0991107885180c01031799603481080030b004003d264500721610f104091450310128900207085092000c00b901d030255030314208003c111108008036401031601500382c98a9550700d081034001080c44008c000e85a815461040c240c801100010f601600301c0c3c1c1d075501c00724034104801c0c8402009250b0040081c150341c0c0c690005001d50040c2114071540c4541c03008a0042208070a070030002606900680c024111408c030440040c110820303140c0340100d00c104201040c01a03202c200d50040c1040d511034416101d03a6640b0340d120b13502140180aa4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 713114640 1250 713113390 713113397
    0x30d0206041203140402040b0d020603101e23030708010c120609020a0909090f06050f19060f0603180215030103060b2205100f180f11090d050111030f010303 69
    0x1160200401d500742c0700d90014501142040130300140062401c1d80c8110a03403103018114011a00d06603001c500710b80e1054941c45a510b040c0d10042000e0866100c2e065030b0041c1c1c284550400d00e1074a4040781e00407101c040c9480301d21662040289541e28100542c1c002080e2400090000078130281015251f03040c5601d449500b58107050020648603008c0c021140d4140c066528841d440d4030f03000c00b10004202441c0d0480d4030101c480d1051001c14505c0c000c4a0240781e14481000d007a0401c90140f04145159401e0706035a5401c0440800082a1254a0794201c070748508002c1120340740a20841c10b280d0300707030b00b00079408405004458229050000a11b06032481000d042108500c07640412800040c1c1001171540203209900f0313100f01c0810740d0032040d0816080e0b200c110000e901e504030a00105044c0d00244001c0302d4102400000c1291405502c0189982c40c0e400c02500aa04500461a11075007940501401c0400145003c01c00254814803007413aa19913041d40300d05141e080100c00312402e1201f074001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 713115890 1250 713114640 713114663
    0x1103100c0e06040515030c1306080708090c0a120201051902010c0207080624180117100b0a0501230d1533111c11070605030703050c09030d020604 64
    0x31410b01c03108940c103407040100188680a0036040301401580002c000c0070509806100c1d1482140300b824a0002901c201c1e156004580341510005080399401400c01d231459118804142d1280c65240000054170003014542803110041d00042e1040c0c424850300050070102c207001d003051aa41940001144940c5a0a41c0c2c12181c2d6a02d9a0342e8842003980c203c0088201014119207500340c003582c0742c03051407001d401c0400385c505007100c05aa4520036800340540300300b207400d10162507905101d208291144d00500b04001324500021aa110f011805518140b00850250100d074902d4051198010503040f81803a645070040c1c024480982440c8400c00c40301c0c00105c00c0424031151750343d0031420b4041ca441498420315403c3c00117a00301c1c40f00480842c00e00c01d030100168040c3e0b406025007407640a1103d50300103484814207004200c0c0000482c40051900107903020f01c00154480d04480d00a040d0380381c08680c948510144505a12a45540c5503061041d030380001c2401d90041072980c8158050501840c9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 713117140 1250 713115890 713115917
    0x120714160b010302121f0c0c021c14031204020418021215071b03180b040f1a03010e070c110916020706050c030d0905012c060108010216020d1103100c 66
    0x6981900307502c6c082c00081d01c031212010320303025640030000f04c110500c0c000000200a4010440c850107400c003900800b104010701c8410b03c00c0c056000000c2c12081d00c02135186c404041820420304c2c42c0600b009220703544600c5560061006502400758980e0000c0c002e01c500e8020ad007080c3e079a0f074015030803111000e501d40c0c00100c0366801624660261a40414610010b00e00b5680440c0e64000994182d0118607028102007401a04200600054100c0040c42c06c0303a0703411304d4140184c10702e500e4055402840304200610030b1081440320543c0000c00c42c20311188410092400c0c200c00303440d240019400c036445c0e0303040141102a90b40301100a031001d400ba03510040d20b03520f04481501c07030304820540692080000b24131240342c035409640a18011400024a43c20000903c840c11085103100d94100c0c51010b00c0030a4030200b40a140d0050002d0002180740600010140d11600c25034a00070b03110f03041200d400c006025002c008095220300040c10b94948425910b251001000c03010045000600c20000d12130 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 713118390 1250 713117140 713117143
    0xb160e0d0209061c0b0705180a06020a020d050a0b0403050d051003030f1d030a1202070803040509010905270303010807171e2415010302120714160b01030212 69
    0xc009038001c1c044451560341c44081c41002003249044916140d1600c04002c0428150000f85d800307440c42d55074441d030f20a8807500704d41e034040d00102c0701803043d814008108003141d00050340d409041d038103036680c0c1c16604242c00c1040c02e04a40202c00340c003c0015100b080101540f080c018011031031695420041500d4014a22008a801e804001c001c10000100303048524015001d5040d442d15a0301aa804030320860040390505105041c121803540da0801c14580c00382d0180900c001401100008500b1b00c0d2415000540c40b01046c0710301110180e540000c2150380040c0010200d62200d81c0b90a9070398041010001c81d40d0f40c0c4240304091180c015a0000304100003103565900c903402c5804010800b40c5102c2c03410003001d840703034602c82d801c0e071066030303214011082980550b80203040e1607510038100f440c6c0a4106101e00e440c8641c0035041500c10003100c40015491101123070044210301e081e01020181141a0b0803034490700592903017070716607d03038a82d007003003906680c15050724420340380700d03c48040e88080107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 713119640 1250 713118390 713118409
    0x10c0c031b12050a082d03011706090601060c060f02070b01050a0506070b0c03060f1309150c0c0f020f0d151a100e180c030f1f030209060a030b160e 65
    0x208144c000c0949000440c604902070200045480c64242501000c9511358105024a0580e101c142c1e80120040200d5120f19501d40d20003c05e0701c016000510700b0a8841d03403910014010134007400980325003c001d024166101840c25141400215907580325410400c02a010903c215480b40d040040e021030b8a00700f00b41907980c0c0039441085050303161203c0c07110201a0308001c0c031483d0810021110a60349503a00300700c00a400d9007800c8000b581c40d0080c28204052282c015044440904180425202c65445062035175003c5e04184402c8a1034910302c00181d8881c80364043e00d9020200074460014031108403602001d040d4446020450000720f007171080a40441040515444603030340401a56607400345d05009803420000348021001d6105031079031007011200740c030152150703035011041002e80c07020b41c0d51031070700708000310b140c4c0c103281d00025104000344149000c028041d81c102404160b051b1a540c000350081d5a00c090920703102e16000e481040c014100249020000742d00200c4414507050090a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 713120890 1250 713119640 713119643
    0xf0c0607060203130c0e070e01093b0709090b04060b0306120a05060f0a1d06161209120906030213090207030203070f060501080c03010227010c0c031b12 67
    0x1180c103050160315000000e40006064103c40e0020356206070010b40485401c1e00940892421b60000303047c4080024001050046c0d11810304c5105c4e01c041c0045100c190340c2500314420f10340c1015081040d40c442c00c9015850f68102d08188641c4418054050741001c88441941c130081c60070410054550b08120a81701e451090400306d000400115003281081640302d40c4e40745001c0126410b4020554a40385040c204556003c00e00d40000c0911a03808401d008040c49800b44010741c000c07a00c480c41107544c942c0303000707032040d08407166035100f00c9400390140500c0d40c801c0011381c034100300030186401c20280034610f203031400c4000340105c100404d9450085c42628540000c18001c6044a410a1100002903120746016002c0d8031040c0420000a10587c403100803c51042c80040b915501d002c8640f071601314031404081c42030b40180108a01c822082080158400c015581c0c22241b0981c9001a40c403541403a801078a40080780c035000c818001c0d103d06500c010b41c00d280d02da641d00350303035240c11840e10609080c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 713122140 1250 713120890 713120899
    0x1d0c12150a0b0117070305040b0a09030f0813140f01060509010b0a0305150916020d0f08060f0d1202061501030c1e1404060c1101050408120309070e0f090f0c 69
    0x216201481d5940074071051401818070200c3c07a650381411003400311046504100081c0c40d00104070420003142c3c0c0a80d0000d40042c003d0010521135a4045d0000440a2102d010094a40001800e1a142c0829405030640055800fa400d0844050094941142c20181e40d002d42c01d00030001118104801c44038101c0c2d075000029400c040030140120080d040150082503e2041e000301200d0aa8030036020038016200310410280382402100c01034108090002d800042c45140c0da16841000d030001242507202c1c0003260391405650a5000249502c2144603014101c056103000c01701c803c540001e09640034240c00f07241d1040e201e040100450a41d031002902100061780380c28104607407411848042c081c201542080394480210b4203c0b007145400071791003c1c00192070110003009101409484071204c030028a005442e03d4100740b00943c0d50382201e801d16904007c0000050083c0c9400c2c00b01c40081c0007000d1010701c150810010302034042d007003924950034034010102c0704da10000001403089200c200141 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 713123390 1250 713122140 713122183
    0x3030c06051302030616030209060a0c03080a110405040b040e030a02060108060919060b040f0e01060e0a110405060703020f011a030f0601030b0109020703050903070305030703080c1611041d0c12 85
    0x14494001c21b00d01c1c80c1c07600c041c91b409100c0214955a80d40103803043c00c11541c0c600080c801c403410000e101d40d1000d40300c10340b5140740c10100540928020200c0d0160303003040e0340100300c5043c110081401086108190701d25800302040a12103d6404a01c041c100e400e42c100f286c0a60310b559028035110014416020b06171141c1d006c007540040c00e40d030000c42e03002c40300070030005200c1030fa040000c055840c1103000c09041e96440d20284071071a000c1300082c0e00b104207a40e0410154000013002e000700e111b01e00481780700c0c41000c01c00c5e6080600c208503020004404038001d1101c81841100b9500c16041d0401c0c0c00c1c424003179644c00a032202c00003d800382c104c82d008403090130345910b0490030b83c0003980201000d83c10400c1c204070420294400b0040d40c00258480d6000f99510490790500600c0c08001404242c10464100480024500c0c1c10241d8811650428007018004810f900020300502c03100b490f8903201c20102407001e0154101042c04c00941e0300035501c1c1c4043d440201085619100c201c40e43e100d40c1040750 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 713124640 1250 713123390 713123401
    0x19080f07030504061d06090f0106232e0e0915150c0102040e012108070605060d051c0e0406050915030f160501020d0509010c0605060f0a03030c060513020306 69
    0x981242c0c0d007043c001c0744001807000114040701040045002d60f002e0f281d10500c00e10520071000c20175040d0142429000b04030503401c00d00c1e440203040b0040c4821000c00d0720100d613840103a0300d609040c1c1c070007521000408256101c1c02100e0301d800c04070f00190400300d15008445045414190000d51160280380100d16580d1940f6040100480d148540c00030b13804014011001a14401d1005001400e07a24101d04120761404a580c5500860301d0a0820600b500e50b426030009a1040240d48030301d036000c140480d0030717a00c1f84041070542060100150039440307614440e01040c050000998180125070b50344207072413204c990a110035544544601a0050102c0001034a118046d40c40d45000440003025100450702403d246880c3c015040d891003c0c19002c20420030640d0780411071106071701d0b058180541004000400a4072401c000c0741c0c041c05075500c85000a000b50360721070701c0405410b03009140300842074403070a005006016908040b10101d10b040702217400c4012100300036000d03d90040003460305a03620b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 713125890 1250 713124640 713124647
    0x40507090308160c0b1c240306050901020f12060109170a030302070f0b01030b190507050307120905070906090f05060d0221060411041d07120f050a0819080f07 70
    0x1946004d584100c0e880f030000c5994201c900c000e0045900c8482401005089030408108450500f2514440091919507452480e8010600c2c20b088a42141c00000c0b2076540d841324501a00c980815810901c01c0041c1c0d542c9500260740c0d12a0041c2030a80c0c403c04d42c40c1d00e448090109660b0030040070615440100b2540020303100b60002d24069101da010030181007416034503260080b07404e0f001200c4609103827080054a5244c040c8840559807d004203000f2400d11440180c20351201406010400507010f0104034403066640025003c4d0b0b9000080f107091503910b6003880c0060503a40a0050200d0400301d005104100c0c0c0d0148600070b8400070082c1074600b580d0390800c03541520407a4008071040078000c2003d10440180401889507014840008100320740034108012a52650030950f83e03401132460b000d01100b000101070041e220f042781e00030340e0301c0c0d9103040421a44080c454010400d104035200c580030005104041c0c0192002c0c0d003458080410a11000e584480080740d210030140031520000708110312 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 713127140 1250 713125890 713125927
    0x70f0909060f3806182809230109020a020c0303270a08010c0c0b0702061014010203070b0c040305070803041a0702040906020d090302061807350c040507090308 70
    0x8a507040094085081004030740c041d00300d0500c0141e0300c50081407440b464180348028907081d416100d40d400600220350f21446d0544024013618400035903070310512002044500355540c450704902c50132221507a44803c00d2010398420700121005020300300035112507060000960311003940303540007514560799040d03210b02c503e40d417036076041d5101168010000704400203100d80c2e00d03200801c0ea2010000000ca040100d141c0b10050165400c5500142c10081060354812005c016914801101c1c01807840f6100100e1940c02a144042c003054030310010700140b201c2c041c1c01801220702c9903045e1003c240d035030f10302c05459014a10505206509050f181146602c0e40070040403424802040000d00c044903032601c2007281c125441003003260b41d44036071440a064041008a034414506100c00b000315400041141c2c42d0710162040c03002c2004d0b2984501c1380007220b038102c0c1c0340040698020100c3384d0006074500b903a031045200707018040c616040101d40b03502d1080314000c007900e030080c40e420310301989a40f43c14001f070b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 713128390 1250 713127140 713127221
    0xf0f27110d1a2e091502030406170f060907051306090e0108030403031d01090924080f070302010e0409060513120201060e041b09020a0e0a0e0105030a14070f0909060f 73
    0xa07207200400c003031444000d001207035500f1b5402141c42c1c9041110141200001c19411162840c81d2400c02c20720340c482050082c0e02c41c006940c2c002030b54956036400d94071130041c4901103410901d01070303022548607481030784a800c80e5114a80d80380310343d981d080c00e5912071066005c040e0026114100d00038841075851f035108159841850900306090303407064100200e0b902d40d01c640125030b00c0342c11219192008244194003403c2204064101400b034202c0456840381d89100090611a900040503940ea586038004217125030030910600c25840c00210031180207114a030200c0395800190100021248140315681c151111802c0001080c1c4540c0c60706003140115000284070040d20307000100300c0200303a002170003c1d601d0300d0b112804208803500802c8003c0216411400c0040314010040005540002d0354512035a084150901c4808080791928284080b0350400f000641c001240000e44252650003920103a004600c10440c0303c0200d038840d000d0f50150583e03103070610b00c0f09103240482c4981401030701018 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 713129496 1106 713128390 713128397
    0x6030c0f1507020a030b07080c07050a140f1515010c0f060b12030a02060a0c18060f05040503070f0f0f27110d1a2e 51
    0x5106003020030301c507010082001c1c1c200d155420072102c456401400300f41044d5141e040520048505880a400113641280010083e098100541d514550b011019000d01001034881c0f55001d101074400503698001c103443e50030702c0c501c01c009455562001503c1c41d411440d0a4403096004038602000c00d05101c0308119120000380c110303900c00c00b007a500100008004000740003045e1500c4118401107928480011500b0007140c001940c9441051030356000d21403111440000c6691440304a910520700c075440900384100b038010160201c000c0d14919240d0304065030703540000d10f4503510340d0101c034040820aa003070044103c0099060302034508011000b9283c0e180c0903990000d203000c0e103c0c6890501e6003e098191241098001b11400480006610f8580ca00f20344840700802d164809618458209522400b9509182d0a51a00906200da4200450b11003038291046030000408000c1003 = true := by decide +kernel

theorem cover : BRFrame.Cov 712949640 713129496 := by
  have h0 := BRFrame.cov_init 712949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 712949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 712949640 ≤ n) (h2 : n < 713129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
