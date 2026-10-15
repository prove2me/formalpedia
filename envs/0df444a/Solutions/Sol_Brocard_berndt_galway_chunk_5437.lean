-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5437
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:51:52.36198+00:00
-- url     : https://prove2.me/submissions/b27f7e6e-a0b3-42ba-9c2c-f63f75b8d207

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 977697841 ≤ n < 977877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 977699091 1250 977697841 977697857
    0x20d11040801230601210e01021201031103010614061305100c022d060c160603021b0a23150408091009081b01020109060f0506180907060f1101020703020d 68
    0x110805038101c10b4403034101a510b103d030588200240440c0c03012418407079506692101d072403003444c0d07d0910182040319210700c0e00707950f29451414203048118610038464000e0741080824480e91803183c40d10060103034280d607165030340c02d607a800240030041c498200c594402050400c01c0f0301d85074814243d01900c0d000304e81140c00b00c08855403000c103115003c1720007000d01090b03200c0414246412405058582c015030141c60f04504a0f801c01c0d1020010346c3c0020340400d502240700b500410003901c04020b100d003400c00822146001e521b03140c600720124610100c00d00325800090321800340900c02c000c1001d412135050038103410240340510098102444c03c2e4007885541c0348903440c1d0340c41781c11404111083c00019185486a58804100c00f01464100c54150344d02c1e900b5010018529204030b9a85034080ca0340000c19040c500200070448040707440050200914070240400d500b00802c203481140c01608241d1a60100b0200c140d0308240c0081c0d04003000c0d4030101385141490340110341004049907035a56808 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 977700341 1250 977699091 977699141
    0xa020a09050604050d0f14010507090603060e0f06061b0613050d0207121506050913140c030c06090a031a04020406091802010c11030a030302220810020d11040801 71
    0xb10501651040551082144204002090b8940122484540545070501100312182546806e4840a855410003e0340c0a1f10400900b03a241c891880036201000303021456060054100100800c0a00369511038400001d030b000c0c0403420241034950b650311180c20ba0b1100c3ca407040e4401c00087d0441303426680b41c040e58500e403080303610100d119025110a50342c0d40c0c2001a940d01c80104c040b0501c254014010f64515020565070390703800015103e401c03004085900c140d120319107403400c6984842e403a036180d405060b10750380542d40030400000d042c8082e110f2948854010740011148040e039400038120320750070000054100c01c850142c0380701d60b009a8040c01180e50710131503181100c0d002071000502070404464031005601c11418281480d00440c40301d04c0d0b0782600c1c80000e042025802048010950004034401c0e445098501d03484030040c4018402482e51400740655291003020143c4e80d590b0b680040c400c84041c2040d481700300c002000c5000b00f6242c0d40c881c01854001d0420090101325004034126030301d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 977701591 1250 977700341 977700349
    0xc0c3504080d0512010317070204020301031104240e090705040203040818090c1204210e040b1005030115030204150503060f0a140607050102070b0a0c1e2a0501050a020a0905 76
    0xb185010080502c0125030b103103803103040c0501c1151404047c40c080421800005d40d550b400038502a40c01a1030fa0710582400c0000c12044400c5140c0c0c00f44440c801c0e1000030460142d80c1c2d10343e01141c403240010a0290380384175199007844442c1e042180d20910200900c0306000c1600050860800040443c00c20342c2000e80402c0381104080399205041001040803d5000c0d00c1c02c02d030f00e508940b0999941003811441c00e4810105402c0000c0300d400500f0280846405180900416240c00001d072040d45540401007001459407105000e4a41150315079841c00041911960480f002001d45244c5e02c5030000600702d00820030b6200399000c2d845084200c1455040c0d14110746200c048401004a00c06201e0018040c4182c9030000304065032255801c1c0242c0000c590928281031081c400302000180c091000003024081d012090030405105031010b594403401c641003002c42003c8051f280c08041c007801190b5140c0b551060a43d4024000c0d42440c1c2800345855050f0041d02c0b0b9071403075403038284034141c030b58080c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 977702841 1250 977701591 977701597
    0xb010803040e06010c051f3903020912030c03120f0717091509030921070e041502070620070201020a1203090f1a0601030c0c3504080d05 60
    0x300d5604110000c43c1407903004a0580e18854403800554010364001140d40b04902c072040c41c01407540e038840c030380c0c04160740e10500b501c4540c800b41c1905050b8030342c620082a10071031041130b910080c03580c0014100020350f51614100c0c1d01c50300c250100c80d0b0f240c940b05419612500310384920800b041d001c0020940f45010a031403503100d20b54130380c2c500e40d0746000340c60350b0184011701070720060b01030050304074584001550000181c89045610b0066a441c03c400e0148101280780300c08600f621a000e00c1d0301700b004c0301c0c081803600407102192901903142d19242894160b9107012218242481d1002440c0b0003007141980101c4400ca00c48a031061000e07044140034903a41c400d40704001d0050304031039940000110543c003119071000e45854000b84502082d84e50080d4405400c1090781d130b50180d0100503503e40240c440302907100ca07082c41c2c180840e564000000e80030782e22101c4010000b1404c2170204200ca42910360a080744200704c046030303071041c54011000b1265840b0b805102c4003801403445400050f4040c90032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 977704091 1250 977702841 977702849
    0xb01020c0d0305040807060c0b010e060901090c14180a080c0a0905092d0105060402091003050603010e1b031c0203040b0c2a120a08180f0a0b070b01080304 68
    0x3904105a44008008503080088022424864140710210b141c44082003580301030051500c9030b0700121224240040001416401590f1582c004020082c942d00d42c1c1c01d00504403840c100e000305021100c04400e50380d440e54070402040f800c6011030304959021008509080c650020b41d040b05c1400c0d107403100b5580315401d150301943c0000040000708a041015030141d94040c500340140c1d449081081c1a0212101e1050b540010455090b900c540c0e078404203104041d0090740480e421841c1101c0503000c14810f03a040d0b4820000d2540d0b81001030300c45c1d02c0070740101f4014061441520b0b0070013002c500c0c4186d4244031008550013803045a00711a50000f0342900d811004007250025410310b890301302d8511181e0702104d0f0401e124018518801d0381d000b20501141440500f000542039225a00d00502042c030300b03009500c1059a100040384408103031404101c07004604409080e44410202d0b101090b54071005446464029400441c0056803502c03800261809038881d42c002c0016903a2943d440e5643d00030f0b401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 977705341 1250 977704091 977704093
    0x806100305152b06050405120304050c040b03010f1d0124170a0807150b01031505090c0408030f0304061d060c1606051017150406090c0503101406040b0102 68
    0x703800b41940307401e201e58000c4420710440e0100201c0c50800300c14440c2c6a40390100c0c2d50035102c00c02e0004107c02440358480020301d40c8130a50941c9403640b1503960740c0ba5001c00c00c601480e5120000c81d0280c03820341090101070802041484003600042d980001482412441c078115480c141c080c0d14800e0700404d83e03100c03440d06422220b054600b00001500c40c100380b000f03820050310030a045070340000d101d100900300b40c50044a2002401c075818154005035000541514101407404120310302140d80c907110942640c4041d100d202c195501d0000d01407040c070903a0403070b004c1888040b8440516600081c01103108600c00c042c18403500e180b610b2115240714107000c0d4000140c11140c0040d821a41d600b01034401c50140044680c4500d0864846070201e580030340b182d12541d0040402402249500400c1407640784800c00205110010451003956692020300000d10042d00c4107408404d011205031100040d103c010300391034440c0d91808680d40140b003c2401c01214003011000030f60f45181c544910f2030344a9040e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 977706591 1250 977705341 977705371
    0x60109052412070302070317060d240914010b06120f0c07060923121806070b100e060901030209041b0e010b0a0822020121020a0806100305 61
    0x201224030040c1052441c80d442070741071140c000c061658444160080030151401603494045007802040c8000c0c008040c5040c003018001d00c5480c1c0c071040e00d031681d9030b0703080780307003038000710101d0b042c0703080b814503804880220382e040014072018018101403c080d20742210008100b403110003002c3c00284c1c00303828100e80d0004140400521403160001885a01150310030f007203440e0203220b5440b80101c1d440c9001c10317101c0282a08440d1558400340d1a448485c1810100911408201802c085000e100e058060421001e082c807034005144c580c07006491507250701840141451501035031119007803080340314070029413000e0f10100d0f080d4104107a000b13050742e4020f000c0d415159990303225084500d000414103c0079030803034800081d500e181095518041d00c40c0301c52203550317a00000300040c81d006018101c08885412040c1c0c0340406005904182907556082c00e0820141015480340b004088903204990481800001c80c0b0a0b0a503010b90329a114200440e1007500124681d00c080302200d10403103070158800618 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 977707841 1250 977706591 977706619
    0x50a08040602070602070c0314010908090d240c140a050301052b0b060102160807030b040f0803070201021306172715040b070f02030d090305220305010506010905 71
    0x11600594410300030240540792044a65480c8201d900c100815981401e010f03105008011103120240728106211000b40701250281e280d0340c01510486005070721500b050040c80d0108400c0c0071002c220151940362030311001400d440e031400500b1920100c0c0340041d10764000300d20002210380070740e9120011b980d20fa90440c0c1c00c0105100b50031a41d0721805007032038070848224050358800784c1212038151060140032040c2c2030410029180002405c3d00c0304904a01207000c0c0000c1500060752004c60f40c0020700e8a01985603400c114010307035607258001d011a4000800c100c40c503070b0150001c1c4044c0b1101071503001026942d10040300c51164070b0418041140022002c610f4000d20070074030704140e40030542600401003494402c10300c1c0006076020144482d400384200001d0002c200c2d502503000c1d2044c1842c10345180c001c60000c0d102d11a0f150309000140d901c0660900f41032140050300d0600c00006070380c1e6004103484400040140f2144021280ba60800d0002038207944101407030021a01c002e46001000050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 977709091 1250 977707841 977707847
    0xf27070e0d030c030e01050c2a04090503271801080607030501084819030f0f111e120d120f1103010b030a0609110f03070306080d0216090c050a 63
    0x60b43e13450400c801802030503010328061103120010184a01009030091449d40003030602007568484a205e540740c98040d80218001200325400400b00884082075100c090702c10312404110300b40584d8000c5040420100440a40e490190680e0303100d03412148181e682040c100d09440c400d006650030364004000c2c100c070307180e40c0c10301c500343c001c0a010702c000031075480c414001108100c4c01020040741c2801c034070302c4501d0700b003402c150102c0d00c0d2044a40c543c1e40d8116111801e0b289001c05005210004c0240c0e0007041c02580740040d000d0b40300081c03c900000341c03c00c444076580042e00294600c5040b442d5a154582403000410590b00c000640340c0c078010f40903001d0358600408030390b20358085094a4a0000005501440055001e081406091622800d121400c1e00440c0d034283c0210102c6071a11181c07000f8000c1c2d41050320561280141d909550f60f4032024114042d100c1d9a105010701c2c410020f02a4016401141000c1203060a503055a00706960b5550750050700c181203101e8022690800c500c182c0d6600c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 977710341 1250 977709091 977709107
    0x4140d1b020a1a040f0510050406180506030414060709050f010509010302070507080f15040f0602030921190207140603041e080901030b0117060f27070e0d030c03 71
    0x1000600c280581d996568202043d1492000740107802a0000380a202c50300740088110050102550410b82007841d0400c058114895402000c050019100c0701c43c80d50000510340b035010344000780c84581c030303400c062501d0b1a16015900000300b0301c0c0038050000d4401803007091114210786004166441e90800700c0e005481c203a12944d8010b0406408000e00c80100f28200042c170700901d03911005207600000c0784102418a203511a103a24489015018080800c95981004880c3da0300904010303966115540c0061501106c440d0011840075200300c2d0546c0d081010005d400c20380c40d103400501107101c2c5101d0890300d66030f20f409070300c0e41e40e80e20700b24280c01801c051b00510762007846a00c0c1034010001c1c0a1420580040d0b04900311040c086c0000c916440d56414040d800e810745007801d00e0070405440c4002e6240c000c1004207124000d10302511071040700e966401110b000a18000415400c01c81c900348035694041c8210b900c0b10110380703511074284030f609007989a4014a909699100c0300311006541c1220110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 977711591 1250 977710341 977710343
    0x61005191a0c070e060108010b0a2c090a051902091c26040f14010c060f0b040c0c0605010b030906041b051005070606090b06040303050313081204140d1b 67
    0x84024809607940000030083c24000d81004030f0010300615104000610001050700a000c1404041c88030840a80d0443c0c1114060040c10039040000601c08200f02034a4443c1c0f0501035000f00924103210381002590b00241c01840000c89410300900120a407005a100d89140b894110b440d41340f1030a41041401c2185140c2d520a160111704d0000c0d884a480c502010358251420080000900f08804100c910f1100014440c0c85640f10100e00200d00191039440c180740041c12194841980440d82103c039400101c011000a208003c40109110020030001080004441c0d0501d84400030498803520400e80b48540440b00c003e120517903c559501505061040c56030020400c00d807004070390b5660b01080320324040d4650751819150000360420b101036a8695002c85c085502c0d013455010541c036000200c2e8283c2c2e800d07050403549ca440e100c0641410300002c140251040c0c0d004640c082598098500860046000350243e06600300315001c541d499030286800c0202240c24900c01c1402c5070340303220300d0701002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 977712841 1250 977711591 977711639
    0xd02070606030c060f021009170901020f340b2a031602240301090c051b0715080c1206040f0903180602070b0d022a06100519 55
    0x4a41e6030381c0c4046035070026420100c04104800304517002d0381d0341081000c1034042000c03420b20003d990390301c1c5c18140b240e55684005c180040000d40a001b40d00030402c3d108441460400c94200d84010400d0101d520b6020904c41c0050071034001c8007005034240a400016641e212301c003a4501204132000c040050421014070b599680f440702c01c00030005050000d008a0440c0f0f01025540c285c4620401c0b207480e003600541c910700762103100425124144441070301e0544450500002c0d07240c5503035000f6900b601610414520120501c03802100c03040002c54980101c07080c1c0159094244000740041d01c20030070841d081040280244507003441140c00b02a240c1d000207003d00000b4209110301140e000352501c80b80c085d804564050348038070100d00c03110007120084c885403016120050410142d43c03044d1044500311410943c010641c05180b85048103203070f0380c60030600311883c044c400c40a5070030313140c01080302c11050850000800003181d04ac400c03e15000308122200c05140d03103040c604220245000d4447c44540 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 977714091 1250 977712841 977712851
    0x13021f09050a1d040c081506120f1e190f05010e0f0a02010c020105040e0f0411010c030806060a021e0d0e040b1807090b0c0601050405010603151a390c0102030d020706 73
    0x44606c0c148400e6542d40e0014a141c0300c0c501c1c0c400c003880b003142c030030702c403e0481a4444070400780c0d041c40100d9804070104124860071041e00c54400390f54a408051000c1001905c81880040100034009001c628860f01c603100070720221480404050701c40d0800100c4180682154100500540c812803081c0152441410818101074507196501c5074110200c508082c92080d200501080c40000d66542c0140c860904e0281601c04065500070300b915000340440d0300481010805118150081c45005c02080306031205040c03c0c441c201d405a07640c0040c1940d90007281151442d800d40b030400e405503c2400401038041d030788104090240301c48500c0c0c010a10003c0202c10b13100415081ca01c2001000d0020407000140215414081044110341040e480036050616182462072602d000c900c140007150031134100d0100d0002c4100c802401841405240c00d1244900d01009441038100e000200c40e2000d074141c0002200356a00100d90340c1c100e02040280540d105004c403c09a801a070000c0840c68450303400490 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 977715341 1250 977714091 977714099
    0x1a250b0f060a0e01080c01140903100207050703081c0f050408071202120d290109120f1b0806180718090203010e0102040e0703090b0f13021f09050a1d040c 68
    0x81003c080e0490046501301c20500da505690050301b460940e041040e805240600328070000380d46007070368a5030880b15500480d5407000d000e0180200c00003180c200b001c103642c496a0403210032581417401da040405038a0170003070b10507044c058490144119400250f40c2e19048194a0300c030b060040484411013144107241c041109034407960042c1c030040f0032105000c80c20340074a0000c45110a45031050001c840400c1d103600034160b0780030a40c40704891061400c0f060891482c104403840b968000d40140c00d407403e00d1801004e1405040b060070407100c1c400300b5950310340c44402008200101d9140401900d500401080c03100103d242c10b02040800d61204c005111456a8007203400d5803548130f9100a140d502003810400d5038500e84c2242e50003002c0c0d2804012250590380d880751009800b8061884040500c000078803001000a0f001401c030f40c00030521a541c80b29296111440391030307400c40100003603030300c900050b1604040c00351701c3c00d955494441d1000040c07640d00a82c40d4810040003500c40c1e33948814002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 977716591 1250 977715341 977715359
    0x20315120c030a0c06170910090203190b061309020f130e0f0706020613170a090b0309010504120c020901030f03020c0607050114010609050907080403091a250b0f060a 73
    0x309810744113030a141202460810080c00e41d54082d90202c2c0201d01d440f04112903000d0200c0c80c0113500400c050006081e940d14004207280c41402f800c0e280c03c04d21804814810311884041c6203110712821184484041c1c565203400c0292107440d4402500000c0c08140201760345003c0340c46075030f4034180c00c000282811940c0070f01450401c42e0344200c0b1241d0022882800210340c18002181e00074450301c008208100c00d6a60b520123480c900d140d0b0b5140c01c0000c00d50071a4148140035620040807118013140d164103003039498500810013594125040c0600404030320029000d82201152150004d02001c4117a1840e00da00c88084802c2800300c046000b0746032031300d201d0f41c0e0709400b419055020b90000107070050341c80b81285540c60103070065010b02032500c03001c110b1075a44100c01540841300745041d0f40311361184c1c60300b40c461010700d8114590001c2d103285540c00040f1504054000c0c200e100004203050000708485103541e0f800444041c0c1010b90382c000040c0d00844c002d605a0b00b20802910f00c42906513140050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 977717841 1250 977716591 977716603
    0x140901080916092306010c0b0a02040f150201050105100516080c120705210f1305060a020307030e0d050a030c0305070f0f023a03030213060503010e0a020315120c03 72
    0x904200340c0d13101042200001d98440fa1240280d500074042e000f0308110001a140440001009000420210014000080c250140e40050414041d1410503603100e100410304403804018a100541ca08000043d852500042580081050783c84407403800840c101e40300303503030038042c1e50560b0640b404110345200190100700381000c691040e44015122000740c94800d061040c0700c2143c400740c091882003180003101560464118685088103941d954180c0b50307110a528000394001035100d075001c00c2c1da100198001c00142001c074400ea03145d50310341808804100b14076240d1400541a41d00107242180024091001c000019019040080c1043c0059942c020a03024425080704e400200c881481c0440c24040e50116511a00c8540100303c4096000d40840047c03402040ca18882c02d1580e5010606004c3e9040b900c200c020444084851a02c1d1a0f01034941c2d1310a01c551440c2c40c1e5034000041002075548207903402400c00d008016499000241000340c01e518080e075241060203000403c01c2c06690070010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 977719091 1250 977717841 977717849
    0x16050d030905160b120a15091a1f05070f1b031203020903060a1509062303070e070e01051207030504110a060c17041a0316140901080916 60
    0x80403909142615145081101a260709420f560021806100400c00c110a56986000b952082466940c2d16608000680000181798809014601002c42ea44490b904041200f480d144540a03410034145c060107400300d083c0650440c0406150314415007144101d006102084c0107420701c816103100c948070300004080b0100710107050104100204201700c0c550b050344614440c5801c00314140307041200842e449180041c5101c405551300c981d080524501001440003a141011040080540750003084a0104042c10a45038245100b02c4060a80c900043c2c48401d884200c0c031186801d407222901982c0410403071b03034254140101804000f4040e41d012110364412245a5404102410241884009103490400041c080c660b41c0780306201031034100d040519031a070711143d0b01e084000c1d100c020b02420f000d140c0181800803d08910383c0c08440b507000195004090000d02500d401ca91100c0503901440348d040f00f46d610003014880340c00158019002c0c25407280001e410f035802c6070318050f1481d038400b0803900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 977720341 1250 977719091 977719097
    0x4030e130906110f0304060b120f0c090603030a0f0e0a170619110f4f030c06050705070315020d0b040b1516060603081b0601061416050d 60
    0x1c00e400340080c60040c84a1102c00024540c50b008240c542c2c9041d9201c020800b4204e1500d603100000b003500c580c001780840c081c0c41310956203413890211100d80c64001c40400740b031044031103401103401494013100301ca02014a40d1210210081491015903640b02c07010034041c0e0000520b98001104191002c2e400d42d070401005c040c2000786007034100038500b5844520008446854045c140520385541011901c40350580301c4d13590b446089a44091211810705101c46144c0000448d010550402900c0f0303000c50b100240504181e4008038510f5084084010301c8081d210302c1c01c3c0502002064011001007a402d40500266030324607440791031b61050945a8400c955026900080221001045218102d1800d000302e070b081c000f0001010004003100009005204031280008080104401d8544441000351b88104184112541c030f00300303c08070390031400000c900e000c070034401160054404a4401d044c0c3d5119102c21039130002c030038200d842c1604503c1c00c401e5544407601c0203c0124600b04103080aa08a80d5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 977721591 1250 977720341 977720351
    0x1602010b130603051506060a110a140c100e0d0b07020f150a060909080f22060905010e01030504032016091a0604031a040f060906090201110705010c0b04030e13 70
    0xc9801c178500089040ba883e0714640700400e0044594800c030880d0003015042c41d0901550202e50503003410301c00345107030080c000c028119403880b10500c0400c19403141e0320211000d1b00c4840070080182c03100040707600096030000784041c446002403003800301940c01055034070459008000c0d60075620300c2d03c0150851400c40400d010f04204801e0101e01135000600780b8140c0901c01c01c181c990b54103120f8000e4817405080018041513030f0b803003000d00e140c0b00c42c49503a020040c0207085903540c00c0600200300d1070142c1f50009100d540b518005502034003c407405030741c2c03581d03600c060301a524a20300441c0307030719000c50015070003250a000303108000c1424040141815180006852044000901548100d0b2502502941c800e100402c0886e01140b003a0303466140191112209588a20703080244240c1000003d01c241e280000324803d01010758480362906100380c0316841040805141c440c0c0e0b5010511a10b07001400440513800021110a401e5402911a08248895400c8140005e50b0b448400b80340300072042c2d44e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 977722841 1250 977721591 977721593
    0x20301090303050a0612020108040b0a0905070b0304020102070608010b09100e0612100602011407030903020102090a031115310911030a0c03020301060509060a0e09190e0303010b031602010b130603 86
    0x1d1040380000c0c86c0c480c0001c1c0c4800c06541c006008488002e10240240c1c9684000450300c602c160031185403a503001c0180c03100d4640303420b006070a903001624240d0042c41602c1d40402e03158020680181600c5803965400d04000c110000c00ca080b0b090500420100103d5000b1202684c80d90070261040030400307003100041c1d07d0003891007080c003040d6170310040071a810310070006e1400b101520615040003041c078011401e040181030030b90180c4134801405030020000b21000040c02600820300e0070b5403504880c046580020020052642c0c01044801040940d007454200140d900c09115000d1540310250500751071a551400d40d0115500c065083c42c0c00c030740001c10051941007c0c81100d580900300e0900b1800c40d41420700c010010302840034100c1c02410b000801092140c05100540c141c0d500c01450700030b0901c0c0007a61841c0d1001e412004581d81424800c24540000000c01907d06950401c1e1005081d6511000c00b40207000d0300fa40c074901555039850003403a060b1159040502d01aa101401156003451 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 977724091 1250 977722841 977722861
    0x140310080c040504020604061803050a0c0501030e1f021803070b040305121e03131202011509020f030a18120512090a050618070b0c0c180106050403020d080702030109030305 76
    0x29103240c0511403450801000016500c010681f000c1d0780051900740040c3c0d104400c4510641a03039040640a8443c010b00a020003480b2003041c82030300c07020b9030103100300b04406003080c0c1d8030120b200c548449126140c0302c19407131038000c0d4094000d960158030040f1402c41d012000c6400c040f443d40104e5402c0c8000503090003440305c1000644004040703100007500c1d0008680a105019500394601e4500741c0001011035031714602c004420305034a405c921071480c2c2a51081c0064020150114148036074500c480001506020034400d0320002040e03c07454038a503a480625050050000c0d401e18214085600700b003e011482103c0c841e959203c482e00d6581c2d0751403015130500c08500000701069a01c0c1d20a03c0c4190028802140c6660030041001c80d4642d45442c84c0300d0a81003814981180441c1c501c0802e80d52210000054240707154001a01c03401c40301001d4080b00c500c200c0090145801140c001c000401c018103000400c60501c0703002e400d0050500c14070758002030a50311554029070000b92904144120920 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 977725341 1250 977724091 977724103
    0xe180103031d0613030528110d061a10050418020306040e16031703012108161a0a0c080c0a30060b0a0f0809070e040b070e0604061e14031008 62
    0x4020090b952000c03000807447d0401d004140750061441e2002e4505600305c0d02d40000100f441035100400b48550281c985041480c0d400020a042c0714160080f1900d0056000e20120b4003540c4040703214205000b189500c91002e584040c0150b0381080d9030324001c00203246d06000034100b001000b001e003000d4a01e54280b01c0009121880450741c18881040108240940c0340d1440702200ca8142246142242d182080845401030240a108926004c80c0714410400402c02c0321074811001c0f85208034a40340e010000084458403240440880c04540101e00080c4079503019000310080340c94005041c400010641381d41c45600703000c04bc480129403042080180301030103000c0c06002a8a403590420a41540060400070340c0300c407481c14024044085010a40c0c144100c002034088880e4801560610340b4000020343e804850580001c0c10116100c40f207840e1400c2118115400c1c0e50710b00c020102500308210050031501c00180501542c901301d4844112400060342c8983d90701c8041454281c80d100745181844 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 977726591 1250 977725341 977725363
    0x30a0516140d06050601030e070f0801141308030a09080406030b010f0201091e080c190c0807080709051e01080c150403080316090b0d0c0e180103031d06130305 70
    0x1041c1c0742031440103a215021a00391880e0410310200c0c060b00c03048010303001400f24050500c407500440e000170070000c43e83c845180480c0c115070003c0042c07802010b1072610b802419070340c1ca1140704170f0160403404592190701542d0031807101303140060b541c1c0d41d5503554501c90b070050703000502003500d038140d41e180f56800542000850245000a220310780c4682d55501480c010070000719041c00c2010304000510140e0001d60701c0098a00044a01190078a410a40480700c082d0303007103424402030040814514000b0039031008642c0c000005010b031904000b80c40020341030051585045000700856402e010003444e01030b90081c041403020f44800d080050a0007520f1184d00c2e445600c2103001c004c10000202440b0032640d005100352968051074030700e01403c480d580071644c0001d45104000c1084100d021590340400240034042d02c9200140c17122030140040346620039032005581c41d0100c010070101c0d00a00d850002c45e000c000394010010100800203a050b000700e140d00140c0e0381c810310b040c410010200324101c40340d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 977727841 1250 977726591 977726609
    0xe070503090d05032d01030c051504051012090b0633070201020f0a0b0f10080309040902041113080c12030d0c030207060f090b0604110901140405030a0516 68
    0x40c41e0180703101c1d80d1812980c0d050781c10840000005105401d42d003100940340a00040c2d601392100c0000c401c02d4622000780010707500c140c0741810010790761400300144400441c40094944c02d20340f400c410030202802c5000d605081c8000c81c45908207142e80c0c0e1003881e1280b842890041007c1c2810010b000120302029040f444103898900304030040c02090113144410031110030000e998601c40d00c0100d05044401c850a04184107008203c0108030104c0d0206210307081e81c181e000603a6030780e40c4103c11002118070034185107420400c001b000c241409e800401c1b0503400a070000c241e0341c1180c0a20019548030481e0303803240c401d08840074807400c2024043e84c5801e55040703509000c0e06110300015900da2140c1d9501c0d8010301d641d8011581c185019405581c02650041003c100c40001821900c3c00f4002080080f200700031240c0004030705260902c030785085510300004403030408100070b00644040944241c0250010010301c0005660f58080140c613107904e1050380a81044d03503100b84100400d0010390409108 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 977729091 1250 977727841 977727847
    0x240f08091b04020717031f0b070b1312020c121c0819020a0903050f070b0d0b03151501020f030306060703120b0d061b0503090a02040c0512070206010e0705 68
    0x1000310001561810010881a400810300351000000e000340b24040f0000d0003140300e0402070307112400304400303035224a540c2c83c0078480801110307100a50202c039501030148084028800c00000c12505507002d68400d1010030840807041282d142c245004030402580d20040e071240e10034012a0500d22004292942044010b080c16444083c800c102c00070442e00d400c1c20802d10800050108102d02c000182152040008555808030420b004121140500041d00d06c0d11508a191b500c1d8070300012054205d480c1156074a0421003000d916001610b880700e00710350300d480359203e8250743c0300220340396038003c1055a110100031800c1600290410a60f0342400c0b15a030024010003500f0303140d180c00c80742040c1d8107150120090340340300048001000d0850710300f6000413581900344100f1806074040120701d800312000d820303c1018811708032094841103820700d9180e04014103160050810750041000028a410319a04045400c500d800d40b001d412038168005920a41c0100540100406d40580000362483c1840c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 977730341 1250 977729091 977729101
    0x1110a1106160305071b0f0b330301020f0f0d060f08032d0313060b0604050612150d120905060c031605031b06100f121506240f08 57
    0x852100030b500a00906840d8000284501d12030b4405400168010301e5000244500d0f04111030414480b003070443d12007962002007541492441e80c0400315012040301c188915802c0c01c3d503d2800ea00b007100e69605590240f1141d00201c00360070140c0340d041c0900107000c1c0c6640240080f4010f171445a4050402030450360028403031110040102c604070b01140c80388010301085ca0004032084480e1852000c51660003005208040c0c10345225a940c0900948051103d0010f2004000152149110b90380c1c2c031820420102058207244000140e0081021211748070f02c42070000802e09205124034212075a01414520300a19608089610040c0100b682e20302e0511030301d0302e001341e83c031f114640c10746c41050310b29a12801040800c00c111480e0b00d1042d40504c0c248407014460f2541c03000250381014048030841d5005c244525904198422070300050303045041600c064a48040c00010036042ea41c03800c2d01c898020900300c60701120aa401302c80d6903806019030440400081c100c0211500c0d540402203440b080c80 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 977731591 1250 977730341 977730361
    0xc0b0d02090a05061911100c031a010e012c0d030f02061302090103080705100e01090201081b0322060c09031509020f131803020c01090f0b0d0b1201110a1106 69
    0x5e81e054103103084c0f00424030940301c442481c1c0202040011069030400024007240d961542140d0403005841d086407028280103801520107040b40c5030b07010300003204008201131250785d14a0215448022140080708036009001040344441100d006401003480c81d0804000a58104042540b16400c0080e03030300d40140381d0f400103101035011321001d4448600851504144602841000880303001e40030b0402090f0b42800080d400f800500c45c0070381c08121000d0025400e90303400c01180d40c41c0c010760a546891556090250f1300800416074000c3d1040d441640360000040b9103100d05402d0690f16114881c00320321f540707052611100c02050004003607007461100001622480b6200f1a0b0000031218000f0000141c0300510050801501c040da140321950415001e242c0c0114002d4072008081c1c1c2c607090a5501d031020700c40e40c92894403070341d004020304203c154241c1c11154010b120801c401004114a024050038282c255503d04c2c448480060300040d0800c62140c009011070151076020010749078038034010040d2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 977732841 1250 977731591 977731627
    0x9070302040e0a110d060e150306010e0412110d0513140307030605060303090d0b0105040b030303040816030504050d060e07050102010b01090306051806070c0b1509040f0c0b0d02090a0506 82
    0x50b6215210100c4803c030350441310607a840b2141d40c5c00100301166882101c1400f10344241c031000d2100006d90303080c501900b00410914142c4911100d10040b589941d80d503e5100c1c1e1205204004000c400700c060720703d40c5010f11080c0e003c1c9005c1c0c0c2d5610340307808004081590139405948010302840a00424034240d440200c0c00200b280c0d085400020f140e920200401d0841c410080400c0e0b01a09000c0700c3d00070003142c4804230303060701c005403802c00c5a4490703941130541d644000c3c2c0c3c3c0603002a03c01c1c00b0a107804070652085a001c0d91080c9000360030030b651000821280e2400030302c1100c0281d10b620f84100e801c0380c1082003400400e003d00c024000c040310140040c4c06000745010142407a5214030005818000c500d000d07000740107501045910368640030300300130100c422000702150803e4030500401c0403000c40c500503449030b41c801400d05119890b199200c4529071a406411501c01842003000a601c0c2580806449103881201700942c3d030302e0303006c0200080d80202d45c00291081c20244a0100002200912 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 977734091 1250 977732841 977732851
    0x70506221511040305160e25032c060f060612060307120b0f010e0c030f06040b0406080c0f09090c0d0f0803070c03230306010c03110d020a0209070302040e 68
    0x1000c60030301c10414640d8040d00c00340d002070708080e1000800100f04100041d50140c05802803503a00e0b09940c90301d442560110050712041c60f8525070058503a1141f01c450500a0f00540710b0500044017502c0c13082e00419902920380448081003012050f1105401c24401941d0240500d02140310300e2400c180083c8103806112a16003502c94030740001500d94504000c0340d006010308840307843c1c5400061030034001e417010480f8039036840c8907610000942c02c0312074200741d801802d4103011103056944600120354410801030000d6442601ca18800034207032914400c6001074421100038100e03148001c010700c1a9020100c45c034500411015042103807000010628a90052044034524009240ca08010b6038070501810040d00c1918000103208a1542012481000741d00ca5140d10705d8911105650b42c1c00d211404641b140c440204000140d007940c0705003800c1e44024828200302c051603080017886440c2001c12901500581d0064401d402545031000c20103600001c0f61030150f151908218201d186104080c2c6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 977735341 1250 977734091 977734103
    0xc02150a0c030605031c020d0905010507200a091b02060f04021005120a1d0c0906010f09030f06051b130e04030c050f0a11010c0f1502040f030807050622 67
    0x444421a070b100703402c40e41c0240070080481d00900c078a0704022014032250b860040c054441c0d40000080c1d24058445001180e074140c466604010050700c1e540120b64038040b4040380103002440c0b8410565909100c44041c000004000a85a5130081d000c0920b0005da80d07240d0565000508024000d40c0d004c994903403182d41940d10200e10302d2030031380664640c02107545421540a0707041c1084246521580130f540340c00c80d030881c44580788041340e2449444a9040c068280c012940c0c030005803540d400394402120702c00d41840c00300103842d85c940300d01d0051248164201e400031b440b1814041600c510b018071411140d80d140e4024030340048102a45401042e5205c1d0b20841582c0400090505002d0b190903001c10b03820100ba80d00440014400310b841e0703001074004507641c4516007043d4406500c569584040c095100b0360f80c0114000544400c80320040e400302e0710f1a07041d0200030124204100002c500d00451042080c00d48948451070640d04254004004444428413100d162a4000c08590301d10980c1d50455 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 977736591 1250 977735341 977735351
    0x9081b04090c1d04020306151818010207050601181116020f0a1e0b03090d03110d1e0e0105041110020a0501180201140a210603021c060c02150a 63
    0x868182880d10080d44483d14054810008900c0310115402003485a48204c00ba100c95507100d0100c0145114030a0b1495040b0110810070241170012907411074001c524501c0ca8920002d019031070500b6a0300440e012500c0f908074900402071049905494030f40d170b40824209010308121425004168011401c60901513200000340f0010f5449056908101400140c00314280c82e80301c1040d200480e19400307518040013100c420010b18010444242c1c0d003d00301100c080d03c00380780f1008045010f030000c01070111290b40308000c0714074111300328411590304c202c100000d20f0400200400003401c5070404040410980d040c0f204010000c0c50a294044030040708682c25951050110030417850204400c1000b032440d880c02c0540c4030b50401511540440b14030036614190030240d50503461200e03002c0d4155520224941d00042d00c4000403030303550382c0035201ea4860b001807150b50340d40000b03000f061003078020203000c0c4404031075409000c058007540342c1d00180c500040c0421041000c4812140d0b000034032030519980e0720 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 977737841 1250 977736591 977736593
    0x80703051b0d08210a1a041103010510120e01050708010812030601210c02010f0b040b03300a0302030a060b0702090103081b1c02062206110f130609081b0409 69
    0xa0040c010a070f01807111000c949150400760100200300c20000907000d6100c951144600303140c5402800e0001012080a60540c0d02e0081071000742d25954458105000744072540b378140580d54450212034070008000490345040c03005001e4240b90040e00903d840381c1085007880054800041101c5d0000e04c00c2c030701240090303200f04107002091070254628503624100590321007030f5a81500141c2e1182000070080000120100403c01180e01c070190380394040d0045007a903a10071840a0501ca494000310400f011030300920012608140c2c454070403100481d602006000d0700f40072920800010300114030402d80b4010050300052002001440b004149031400202c032030450b01c8000001d1707902e041d10780c110360103100483c40b049421040d00036a540144903050018001005034040100700c1550b0745040380b41c0f401c4986582c0c02401010903100c006803420800321400e0319219004220a030b070300b0081c40c2d41d0682482d8000b40b0003d4154030002c85580500d41c1c4607003102e4051a040013501044400043d41525 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 977739091 1250 977737841 977737867
    0xd09031103040f0b180d060605040506010c1a04030203120412090905150d1b062601050d080a02031b1e1b0d0f020d0b01030c120b070503130c080703051b0d08 69
    0x104d1100f03581c02c91ba01c0e44c02401000b40ca40c00c003400b034620454080c06159210001180e6084001902401c0b1410740c06046c141c80444070103040c0c0043c000c0c41aa840c1001180860744441c400f42d50031a0580010078001400e40e0340f1090802c09032040c180140002d0a0500c5134400700c0702518880c51041031103c40c46010000c0800b003042c403140d6004d0b0b00f541070311303503e41c0d02919451460780c1c510075410854014490440e500303501c040c1a10701c000c001c0c00c804141c94540001139007000c80d0030015884100300c2c20080030381140ca940c080303040b01e10003828603004201c0b0808d505240b800f400354280e400000110640600c440000c40030110544440042a0309824005400e000100300650032204141d8080280005094860305813030103072401503451075440d10039881800106001400a059190100750494840d02c02141c004883c146000345a44a50300c1d04a0362111652042c4210360203880108100302c802c1c0f120740000070250480d8110014000041b40f0803040c1144014248000014030420880c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 977740341 1250 977739091 977739127
    0x180f09161e05040f0606021009120c06060b1207030e06150d0c030c150906050301060903031b05150a0c0212041a0d1a1203161203020f0d09031103040f0b 67
    0x4401001848600f401218000c000e05d078a000b10801070059440c4598429103034040c4d0718100d035028a181e100744001030b400301d425040d04101103030840d4076420002909124500605801d4070816802800c40c1090305000d82240c001d02c0d04041507402c40e608100700c044641e010a91100c10550340d0000d050342500e0a448248000c2e0002406020759000c0407948003094850603440744c129807160000c0e01e80720003050310076010901c100e800050100c4014400207101e05030303540c2c03a00d20700408404001d9141d6212030030308002d040d802c4440c05414041040500140c0240f0740c9908060010300750700703140068528514460381c000c0403185400340d116400480c60b98002c8484014141038200004850b200903402d44164003180c082c40341840b400540480000882240c021410380b6003c02891041c96460000344841440f02c0824180c0c01d2104c01c9204140c04000e004040c03100c080028005041e25000c7c001d400b480c6a03c5c03456038814401404440a4072000600340c8242d0030402c0d40b03032003c2c0c2d10711101402d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 977741591 1250 977740341 977740349
    0x30c05070516060f0815010e06040e0415110c15090f0a0b0f24211b0a06051c0203151201050a05180a0b1005180f09161e 53
    0x407003502400d40c1481c082c584008160f90241c2d4401e0004103407400125000392043d5828900000388001000456004007098000090054055410183e50f610303400c1c100c5a045805540594030300c004030315801c50511541551003040d424031030810801742c090340d580384000382400300c0300d24441001c0350505004002e810800124041283c001d029030340341582d000072043d504080850005800314040500c41020703001540c1240394200c400041c80801c0000114009421410980001c402103648120600c120301642c880c0d0030708030284d45419414000c172a80c0940c070080030400103018098807000c1551040410007165000980c80c2e84580910000301d5101c2c520a03a800050b51084d00c41c3d00c0419003005200b100c21040c05c210075030f907184d2480d007955200e84050000342c21254502000a4448000315007061a605403800c4454840021a80001c55035551843c0c0140c41e9040000c0d8400c0e1099403503000440070068800441030141e60844420b51703001c0d011007425041c0e581600d01440c140c44030018 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 977742841 1250 977741591 977741593
    0x60f0d110d0501080a060b03031603362102102010050403020105070908030a0f1b08091f080411030f0604111509060f130f06030b280501030c050705 65
    0x2561354540490b40c8101c4100c00b207404a0500c80103a07550b14001c407d0b20501c84003c803151500080d030355406c0395a6a4040c010070204c07082040540a000007014005101007240d80d0140d41150600080e00860300c120440000b075040524581c00058444c0c100741204000c1c942050301c01000d40c1c19104032801e50340158417605200714069406040d40301c2d04001d008501a0300200240e031a10b682c200c031304060b540078000c2c03284e104215015543d8030070300021100219521f80500d14004030b2068618240c2040c805031543c0d04041038071406842e1031f01c1c07030303400e5024040303007504006a1440c0040d0103d0402400542410340e80b514100f0591018484010315580c00030036900103103440c0c034104410b01890002d142c0031b40701010011900c95400d0003201c5c00b8000c028202803c0c10b4000d01138554a82c001d0401c044e20340c0d8035800001d034404c00d2503c078070042c12141d100411004625014400c1c05ca03e20380d10b00075112041071108041c0e10700c090180b400c0d29028600455034010b55030040d5480d105110f4001c2076 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 977744091 1250 977742841 977742851
    0xb160510020a080609060402030709030b1021024002070b0414010605030a150c0c0203300702010f0c02151303050706030504080d271a0105060f0d110d 66
    0x41c495100030703120700c540d001700c0740000c564031030720284000c0b13000454012010800a04090000c40d040c0e0421584c03100800d0300a064185c2c80d224000413400c480daa58010048628201c031046280c945d2007801098503100b45c40c6000e008034203040852506401604064600b52113200303040b554190100c41c18181c10a1a41040d81800d00c1e0040441c0c0d072261140d00315502c1c145012031545004920114103981040a1402904c4281300c2c00c402010f0160180c0103200c2d4070140c0f940140c5061000a10a080329000902d425227030381b60b803114000725444c0d128110303a0108256001070382c03c0a54010380016529045040d43d0340340c400310300b501809800c0c0d0481d640000c40d03000324074140642a4000d9074854019036408641d5208254180c0380300303460041100c10705001d02c86c5aa00345074440d840c04042c2c1c40c03d500c0c2e40744007040c0c0d030700d10000d6401040c0e444607198480d51050034006c0080c54010319059444601e0b0204144a40c0e20034000d005514103415181c92030610010001804e43ea56904040c0c02041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 977745341 1250 977744091 977744107
    0x160c030c082526070b06030a0f120e0f060301120c091802031c0503010b0f2a190201020607110f010f0501183c050a0b03160b16051002 59
    0x280b8001c1207401100c01a8108001ea800c41c44400780c1c1c1c10044000300c02c41414001a0355480002103402170007140c05210720180759020502c904003014006000342c4c00740803074440014000707000200c18460a809030085a807083d105850341011241120342c21802300c2050300d040e24101422504e25440242d5032810883c0c2c046070450444040500544200c048a40358140c8030400090f109440c00d120020480030300c01044061501c0c0d0052219075110400d40e4a001a90441650661145525440404942d480c114001e040411481c541d03200081c50f07030050743c003150303000035540c003130040c1a802000900f000d0b420304a101001030400c034048500003407001c001e0900050000340300034483e00c4113108a500c5107440070a0588141c901d490071480100d00f82d004034059036400b40c40e14884401080d805400300700c4007034005105090190305c5100d400304001a28104040c0f074021004070b030880d00303400c2000400a03505c17118100c40103040328070740580403407a0904110b800c0c41c0300050f14821740c90001034688 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 977746591 1250 977745341 977745397
    0x5010807031410150806130905160f03060f05090a030518060409090314030705070f030e1306080705063c0307030e0d0504060807230c01090605160c030c08 68
    0x40c1a03840501011000390b250300310440f03000c00b040c1ca50720b80282c601d103101c7c48614810303001200800e010324211000042c4a050210340b0b101194041c101034415203405100b001100d000306000c03003000010038081070410200e01612136444210044c244640000c0d444c0d0380300c980d03031804c01d600000180042c0d00c5a56410050700940b2a003e400c80014000740000040d9a04030000d69004403400da03a203504151a0790340d110064444868241e042c001e482d8100540c2c2c1c0c0d14440c02c0103443e0b080c148003050301e5113012203840ca01030b00c17034110510511041c480605540304a21124070030814154208560f0300e51402c04086100d80340d86030284805000040210582d096001445204005012581c100032800c90444241c015801a000010034120105800c148038a0902030f05c01102d901d541000048030280e0003495110080040850b5103440061050080d9442050791108050052158000d210308005050540800f402402e00c80314041c5101400200001c0e1410a50b1841c0d610410350a206101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 977747841 1250 977746591 977746621
    0x6010c060b041128020604031d09010305010906060602010c0e04050a1b0503040c0f05131524080606090609061803070f051906120c030e0105070906090b13050108070314 74
    0x1c8640704d82d040d4094100d229520050325060b140760703405071039280c40d2a60101d8142d07001e05642000f24410200206103680c5003450b103402544168000510840245000c0d81503405a9114900f564982244d41c1034841c0c00043d082c0c080c0070200c800103419910810248014050002010308107440024841d868640090040d8003d502441a0000040da21150140144100d02425800ca03501f6060043e050791547c01c80c500e100200501c0720510b54855420b10079044415000303440440504100354001c036000415142c05c503400b0366032203182c1011030010503650305c0b41840c05405510300151040c4040300000981c546207a008090742d512950b50f07162104102c0850085a11034902e081c44034548000d4040b2030300803101980c45d02c1c486845108610401001525604014540c903510306564910302071103080d201e115a03850b41d8602a050040c02031290030150003408490800300b10b50b014100c445003800c0d00312842440c040d107290b5540c0404602400a4100a84421106c0d8041c450701c640d1240320 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 977749091 1250 977747841 977747857
    0xf01090b1203070f0b0a091a060301091703070e06031302121e1c050304020a090e07050603100608180303010911040b0a080f0a060f0b091912051009030806010c060b0411 74
    0x400749480307090040c42251f0040c2c60003000500c42d041640319101003508000d44c8400b000340005040365254503140c40d104c8801040c000380300c500004200015401c00d0300380200b5030b03090b07170303803a05510308a00b0300c0802480c00040a032099070324018031f20000204002c260f8600901300444240c009201c8011070395940218140c4070604090b10380c8c0c904041c8210181c0c0d2150743c008041c4007502d4501541d590080c1050740349143c460091050100c0c0c1c1e40c175800300450040a01c58001300344907181c0700340141220405480044044142041007401c014004140ea040d1804410700080d030030058000c0396100c2c481c5600c015403103c8040760200d0f201d60001c07441c0d0b110b8000c0095522440c1d98801ea01d20031690706000d620800c84e03050009021548203980a0242150094040c0ca14980c0001d1540f00303103541e60380314a4000610510f00f10420905120150f5030080c4400144403002c07860ba000740009000401090400507800c1c4a4028071000b0b0b0030000d90500c010304100408400d1600b1988190303c1502 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 977750341 1250 977749091 977749103
    0x40f170f0418050c090904020303041d040203010c0903081213140f01240303110109210e0103020f030a020a350108210d150b03090f060f01090b1203070f 67
    0x700181040d405100c0c0b0813a44103004602d40f21500381007085141c006007050780c151000f40004503518105850000c000006000007100a10340f42c4100b50a40d4a010103000422a0003101040058100c03801e603509040f00200c441a9903440020300210480400c0001d0491401140d42d9007613020007041d010a41000d6100170b010003d0b0340201039081d00c0001460f404110b103c1306040000c02e2141c0c80141c20f0850220001c100307603900d034135540c410050702c0c40703091900c5100144062206802c03071a101003180b000c0c2425824010700480000003404020100700d6107680000740c100714981700b1501202c28481c0301c0c0c0e0400440500c8100d42d60010284074001048180590010500410004001502c5081219444d80481201c001184550400440110f03140d89542c1041d0300d80352142d000c1e80c003500d080711180e82c5038a0301e800081c0c90000109100b482a800510500040c4d808540c2c90030f06403800000007107030712550400802d0201e4140c0b150b814480c040407c064042190301c89401c5005801340f9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 977751591 1250 977750341 977750369
    0x21e06031305011b05160305120a0b0901080a0f11010c020a06020115050d020f0402071e08070201032301150c170304060605030f0d0c06020c030c060f011d040f170f04 73
    0x6070013a0b90b070810000e00c100407600c1800036900a04a06400120031341c1300b80b40180c145141400485500314042c1d414849850f100c100303142c268181007414500414818008000f55076041d2a950301b90070450384082c000d09012480b082c2c0a9025941c00c181150313014041c1d843ca10b5565100900130308460643d82a22040020000f0301840d002100d5151190010884201c0d681c000040200a500040f000c0b00c0ca0324444962090074108040d9a080b00e50050104a60703480d10f510004040f0303a5040d00c0107800203891081c580b0b40d80803440d84103040d60058800040600301c605001d440300310b035000c0002c00c0c0030300c1e4050701d603000b10100000c1c40c0201c5c8100310902200b6110030403d5154810b45480314240e501003070f407400c40709101d5070703085401c01d000311001441c4c200320028060640d8407400b101c0810b13500103018042c403130540101d01e40c010035500700311201480c1e000c0d00d10302c029840904040c011a405e00c0268061200071500b202c4044040110700ea500c110028240c141500144606007000b181d007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 977752841 1250 977751591 977751611
    0x7031101090602060f0601020f0f03091503041a07030e07090b091006080c0310360c120b030c0418030306090b010927020d092d021e0603130501 63
    0x241c0c49000c2503440075000b4002c0c541d1102c1c0c034a00c001d100200300ca41188505036508400c804180300c860031401802c40038543e0790311402e05024000d103001c10301036a80c0c401001080041403d2000c242000010880a0155500c2c0c081048002d40710100b0141103502402000003100171103640607106144007514800d203503546100407403800b0420f901c201e80200e03802d007000034a103454038030045503c0304805030b1604115884405000e03100b80148000341c164510315050148241103031800c94415000e00c2d80a004000302424028060300703850303440380909521401c100325181d034244918149100081e00401ca0180102c81c081d00b40d42c6160426030102c2c4c5007030400700e810011401244c0c11103406031540f241d004d2501400c5910f04840c00051000d0030180b07a004c100c0c8110301e00090800c15012000814156090700b000c05803c0349034503112003482d041c0444c1c03044181502010139016a011a6100500001c41072140c00002e1481007007580400004204040f03156208000328901d80504000c0003407840c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 977754091 1250 977752841 977752847
    0x10e030313171606050309010b03010c0e15040e0a052415030a1416090e100b091c031808160302090a0e1207060c05030727080604030207031101 63
    0x4041c01c41c040c88404000078004140074032000d024060301e9004481c185105118003040e040c0360f60708850000f0b01c2c0042800920382c4240100ca8542d00120b000300b04014420f60042c1c1030349011504540070380c0c0d804074455070340000e08050340d00130402103440c408a40340400d0391704003d080455030720341032110f0814051f00c15103400710303454001c00d005030201d441d0800c9580e85034901d4200400c140f0049440745840140b070907042809034042c100e12503880a100c40ca60202a00d08041c542010034015111010016020a40d4a40504503566014029a1380c000040411303400322600e20040410941a10207000b0154400d100d0415140d66480e003003030542c1c6400e8503a0700c5201e0300300d607180c48a01e0100d06102601d07003200003030b4121030b11510000d0000c58104425003000c5052010306100389e40810000c2c14840d4030b000c0e0981e200c00502c1c01a14510342224085d150361850485548042e40c00c00a840f40c003198490170030041c01881c2e048501e90301c5c00b460000e45d00d040c1c50004450030a410400d511103540 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 977755341 1250 977754091 977754097
    0x1b030c161203030b060c030a081009140118150b0a18060206070809010f09051507051315030605060d0509100605060f160b01080318011d010315030204050a0b010e0303 73
    0x1e0400300d424006500d9480440c0030b00000b0110321307030100c0c0c10003100040301800c000503c000010380d00c4069444c80c01c040854548000359024000f0b09080c0100c242c0101042010581512003100510707041c001120f80020007803609002c0500f400ca800e0602042680a010207000c2440e600d6543c1882e10090030b805454142d494466040036034890f501042ca0680910361180c1c0c0400c280000040200341200c1d41000e035000d41c0c01c10703030740381c5c0010340f1122140003424442940900030b4100340d40b80c85034140c2800b5110516102d8441088045841c200c0d1991180c2c0020004003001081107031540081c0010000425040d0307410149403103140d1014000c11114003d8a0407a10000c11040c14040e003094154466401400100400e001443d0f03503500140d107209190340a061004c00031512210f07003d5020080c80e85803c492410b22174459880055803146d01c840d840b11250a20b800b0070207070621442076000304050341009501c00d06010403c800514181d01ca100c40b55403d82c4c1e40b04941b43d580040c5038880c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 977756591 1250 977755341 977755349
    0x807080a0c1203120216210807082509210201050306010e0406120b10061106060d150e1c03270c0b180f062a031b030c16 53
    0x21401502000202682c00c101424280641808001d842c891410801280d00a0500c07000800c1812818401e00000f50b0703207039803c40c1d81130418114a2401c80d42c01b41513860010b141ca000c001c000c07000274804000400c400045e16401c800d8030044603542e00400380c103280e05409680d10340d080610600301501115060910001d806844861558072050700442d00180720301441a0041c0c3c84150005110885800040b60240580007880e043d080032208d49115203290b50140c02004035482500d135407110041011500040204c4003e0b4500052b440c01b0595a0b03450302170508080d2a104036060055004640489818040301c2d40c8180e031000e025040d001c40349a0340c441c030001c03910340303000e0801e1a400c44008001c09000f00c800104050ba2900104140c0d808016001c03ea400b01003008403181c1480c890400030380b03000710f51250070420361060441c2d40d45103d507100a03054400166401403000e040c402c9070b0754009000c00f900304413100581581d580368004183c0340040e02c0f804041000104660b42010259 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 977757841 1250 977756591 977756603
    0x9060607030e040c0c08030f010314150a0f060302100c0605010b0a09120302120703030b031005060310091103100e0706090602030d0b0402040b030f0624040e0405030705070f0807080a 80
    0x204494030a2100a04000c1c000c13074140050b0b1110000803a104134013940c80b0380c516001140e115810751600c000030341480c2162080b00c0c0e1102440000d40495402c1003a4420390f052000220100c0b01c190540140080ea80080e4000d41e21561a16401e503018034200f14603030084400303214590380d80350440c005110780d620403400140303500e4080c0203010592643e044818001d02c100c4201c004200e0300112258821402180407c0ea601100303955810140000b100141e41403008200c240381400103c0c0d280c0071004402030071b45694609540030080c40d0381e07091880304005001c952440d214000018020095075140f254107218540c0c001070490b2250b4000c40c160342055008e03609212610100c3d0018240e001440303603025400f0300c40424940b005202446c401c0d132000c00c02075128101201440946080d80d8a254000394101048070340b004640720413a01118026081408580e0701d5050150a42c061200e0080141c01003020000320103003400410016194032505070341296a594800d50383c1d41d002c100c802890 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 977759091 1250 977757841 977757857
    0x216030806012c04020f0a0c030f09050d030c0203120309030702130b0105090d08040e04080901030c030621020103291927150f060e060c12031e0403020a020906060703 73
    0x40c3d40250318a500d80064058805406e1441d6a002000c29412488204000407041c1c103842c000e02d0b40c07002d02440d00700080c0c140000706604001c085450030354800c2c800742c00e012000382c005045450400c1800040ea44020301300c1e850341410318100e61a94065071040e03100364800d80d44030106401520404411201c161900b61600300c100042c01451042d1100030f0b41c480500f40800280d038010210b03e0b0740300c2e078403901c54240d441e68508000b4040b6942091480d08251a208050154214000002441088008441206590394401200a02020051401101c1d403620014611484a90307c0d41908481101d81080808402c1410303e6a010144149401030319040c02c000d10356014a00103082c401c1c1203a101090900c00441c0d01c0c0100529039219045c00203e02c1020085164414000408842e04440f014a0042c1da5400315603a0300401d07502d05414580000400e80424116030314900141c414020500d040c030742402d0294852040c05d2090b4003c0e44443d00141241c60a48111038081c1c1e89500c2e01c40b4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 977760341 1250 977759091 977759147
    0xa0e090a03110f070f0509160e0111070503100207020a0e1b0a1403090708010509011802120a0c030803090607052106062a010b030c1003020d020d021603080601 70
    0x60300302d00c0e549244516000344070303004202c03107800d01210010b4049000034a0038949000c0c14064081402020b010319251b0344010042801d86c04104403540030001d20f84888840000d40c001400e118481e403006901d80304e50411025840c20540203054010b008031406940c2030750307422542d03074194006c0b20f0320145440c1c142c0003c42c14400ca90068842e036071061500c00744100500c850315106520907100c00400c1d074016030341040814000d00601d58030141c260001e1207089028101000042409100244900151440412500d00411081014039003001c1501b884aa4030b0a281c1a540d00a03607507041d19000782c40005142d98010011548581041001a00300103000b02580c0200413000c0d0030b140e0b000b103040020100c100840d14842c2c82107004440513451001c0851161404c4407039180c1e805000e43c005881003074081e80e6803140030f1003440660501607034400280c180c00c0c000744196030517115010310100751b030868203400c1c2d40d044080c24400e4603810500c0d220346005491150440740f0301c44202900d6501c4030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 977761591 1250 977760341 977760347
    0x101d041e0312020f07020d030c110a0b07030c080c0304030c060f0203040b03041104060911041e0806071101061212030f0b03100c030b06041418071b050a0b04110a0e090a03 75
    0x20004510302c1c04e2242c10004158001a20920350303138020342c000350441e82494107008011070780c00384501003100c600d41003500e024080c403258003e070340c0c0c060140324070a101c050034401010100c43c071075081d52080d642e44585034a007a080c000080d010319000180f50207160841240004115002d0700c100b001d02500f195240d071b4442c8810b01c070001d11950015101c4200140d1025240500d421400e075494405884d01e0415030140000446a480c0d0070081540c0001007241c0c2c0781c0443c4d0a0380109940c540940010916402680507000340d5001660703043c2c580c0c9519060203400c030303183c00356918699000d1007407078000c10406003580c0b207186110b60300d80c1003400c0803e00840158003280a2190504001c02c0c00d07601c1000243c200d800035440020300d507400e255010320902d041144440745103030241e103407a580d041002c40100b2200b190340b0b803070040c020009884014230508122540030550320000c5050145498603090440c1203030040018002e00710240089000941414001c2c410852040104140113603505c0032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 977762841 1250 977761591 977761597
    0x60604091e090c360510080303070207150206041119031a06030c100507030806010909090303061e080c100e060403200d0317101d041e031202 62
    0x580c04880c402200304004003501403482c15901490410740d03114500b81c0100286041081c00d0f079026401d03800301d030f00d90041c0c041d04040d41001c10b140000c1c45581e07011610000c0d200701c0c1c109660030700c0040100002c80d50b0000b13009040d2903000f00f01c40701c1d503038407031000341d036590402daa00034840b8140c0d001600103070401c4905801e04880780ba035500122556621810345a40c2210841d942000074002000014241004145250007055614224000300d840e4010001c0c042c02070010104040d641c0481e2050327201d6940340001c0d10035a5410406692189030203030040c011446800c032000c651007144080c141041a001d41214188000f42c185c00c00301100301b02c550201c42c011720341407100340701d105152512200b0190001e1340c400d04500f42d40318000311f5240c408a00e482580ca2084481c80c080000003030340015810761503a0f001030140f400d5100c0181b40708002c41c0342d412080e143c070003210000c09503040103100309014a001c0c99404942110400080c160080210b40103404100c1d0050a40f800221300d03401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 977764091 1250 977762841 977762861
    0xc0a240306050d030e030c2209080d2a090b040605030a0e01021c24050d02040f05070f170c04150302130f03020f0406060206130f0b070207080f0606060409 68
    0x74880d88540020303035001c82420081d0b0000c0ea84001005d0341d03040030441c040d90740a080b62900917200c40141e10000d034090643d10800d070b01e0b07107d80204040100c020700b62100900384980034002949001c00141d4400d001002e0748503500401540c42c1c45082c05901618191008801080d01d007908003c81594203500103044055010b40d102d5040002c00000e2003d07000060122844e0401504240000001d07900003e880c103096080c21046450740e9150485558105c5500307440f186050405400001c2c001c182200034640090308040c00c101100d030b40403680801021240e111030f8603201d08001c40e0710b084002180d540b00c3e014801c01c01402034149400c48001c80b20030a103805842d00d1140d80c408450010154012072048681d01d00600441c50550140d10440c0c01c10b0f281001800e180a034000c0d6518005009032400c00d1618000d603061040c1c0c441d0300d25000d0b070829041a01c80c240300c0c000950f110030364070034611070f4025444011209540030801074041c40d0014511801c16040013110f000405100d01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 977765341 1250 977764091 977764097
    0x30f13030b010e04140c102f0f10050c0706051902070818040c0c020f040e0f0d030510140907050c060a0605030c03070b1608091309050c0a24 62
    0x100190000d4401c0d40600721001c0461141d040501e00480e1028040d0402d9600e0340200982041035220040010301000c91442c1404600094982c034807510301d061101d4004600200c004294a14400500b50304841d81c00d40480300c0d50700c18100c0c40c40c21210b00341c5032114070800420215010415540001e9007040c2d800007880b09410300c42e00304130100d03400410210f611980104d000b8514400480518014100c159000e1048800f80003008102118803140244500440c4d2410f6906864a620007040507049c41e040341c2d10141c00074602d47c1d844e0007044176140003070308140010f103229008a1009040b690303201c007412032051007403040044146000f0030940400a06203c2c0f180040010484940120070380e031400501d06003000103150609082c0e200050003030f84080c404100801000045480008010320302940f8811245030604145c0310384800903a200d44440c142408074440e651150310540e11a50481360007520b0942480318884a82c400c1e880b01c070342d10741ca1015035181100480447c1c8a4645 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 977766591 1250 977765341 977765377
    0x20d0503160507031208040b07180f08011406040b060a05030a021201030318061805060c01021201060215010e10051c05010c0e030105180a03050c0a02031e0c010908030f 74
    0x490a0107001c0c064000c25038403540410f904005011400010040c00c03042481c00b21910314054075640e406aa02500c01c0d0b0410111042d05c280709901c0c2c080a0014005042c1ca401e5159602d20203540038200c0070000d1009a10f010010032642e240906c58ce22805a02a04032403c016845030140c50b0790700010b1000d030000e5000c00c180604c10041c03608550107580719860300c21420300030341e5115401d1800364022100344120018019480781203071803890100c5408a071010340c0c3d1a40703094018003901400ca480d42503421200c00114042c1d8020034401c405100689107600d5507130341d51541c0440c103503080c0c03000b071407141d2249000d02c031605015071108184a00c4610411035141c140c0d13209800c60b22001c4c030401c00503940000c0031080b89805c2c0903894020b40501140036112411000740754866207000c0000341030010001d07800e200720300c0c184441000203400070103441d810fa03801150155101d070300004500d005e005524400f80907600034040030003500c80d050001c5041c04028074811021b0f901c2a400c44600960300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 977767841 1250 977766591 977766607
    0xa1b0810030209011d180316080c0a0606080f010b0a090203040f120e0f010203070c12050708060f06010f0f1218050304080a030206090613060504140d03150f06050403020d0503 77
    0xc401a540245601e17a403a0984000c80d00c4000c4100030060848201c0c901107031740780d12110b0000000d4a11b00c1c0524840d00c880031071a498a44100c2c0300d000c1203812a0f0065a0621003808a5580401c3c01c07600c44009072100c6400d28100f0a0880e204411801e600c5920410305000007040c035405154001e2007031501c5180c001654448800007100040440001243c450407203100b81080701548034060000e000a41c2081c54580c0c46544071945409091031400b0040f4035841403200c1080401e0007421b00c1026a416402c1014404003c29000c54001d400f18895001c3c03070980521403106052400c00039610b0500b00104402c0c210050a880003920401c10b0748803125001007501400140010007410000301000041e61a019050110050034000c640c0c10031010003424a084030000035000b50b002100050554030f40c40d00022020541030940000c1c841c010904850395050307400000021802002c0d44e1a00e5545c7d40c0d1829900018003464000a50038030081006041582515000c2841081548d09001107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 977769091 1250 977767841 977767849
    0x1060e090a110d080d1a04020c06010b0703050f040f08120315040509030d0c02031803060603100209131b1709070b090a030222050a050421030e0d02030706050a1b08100302 75
    0x1000407640c0001b9600c0007550b000c0e8800f0424410035400948003035040000e10295107444640500ca0036008200000c1c00604146c441c0c0202c41042880000d03040e112a01c1344100962481d160181021138421510000017056812054a100e8000c1307040031b0205600365010301000d020060105041031000b8005002c203030401d03001d038400c01104bc1e80150740b0b0b016011801042002d00112031402500300c0c3e0700b0b122064402060146451000442c0036941e450314202003580c400c2540442c212242c03034808008084080c110000303150164640e02e20142e04072952014400020544d40004030358002c0000f0490180d150002e001d036510014503c1c0d0703081da5650080348542c2e8081e1150700041e04a5021805081014401c054024035841001c100c40d20f0300c3c1e984d4248940c041703084114220b81107025545941e02c290800103c4041c01400d07100e00c4e00c2a2a00690750f5040311720308a50f142d0070240065005000c6100c0c0b014a907454032910000030062000a603114207000e0b240818001c8840008409619 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 977770341 1250 977769091 977769097
    0x120a05030d0b01031503030e0105280509010810081e01020f0c010204030c091109060f0d0608010506130b0f0409080c1225110907020309040905070801060e090a110d08 73
    0x1c180d040200b00e0105000005040b100e142000500c481741c214018000b1942c0081588611002802e2980e40c60700b0740450480700010100310401e0318070f840c20911030101d5024001d4030060740300380ca5032600381d19010301c90a2001000d000b00d00d1994030002c494030001c4480841c124880c00228001450012400c4108065611102041c1441ea40009040003003084040b000d80040c95122400c02c000521a41d04001500c102148a4418a000310340c18803a100c00000300d0f614084090001c00c00140d448031454040c0c642140c1c480d1158012414a080c200c1307640c066010307a507600404e1440e402c02c51408000081071a40310590301036005208030a036150017004500b403c601e100c040a619455444083d62081c40b101214240091714010150006200150a169120350449840f0080ea451183c224a140100d40c2d9a41d401824050001e051003408039101c8242e445880090103001e4884510604008042d11f20500756070007500048042100c3e00701c0d6801958004044164a15080d05c480840750 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 977771591 1250 977770341 977770357
    0x120b04021509042301060c1a0703060504090609200d0b1e100e01060e0105090420070c180603080a0804050123070801060f09050d050c060f0a0201111602120a0503 71
    0x80e1441c09104d401d251904211801418a803406c1c10341281280d81e03080050100c241d04076a49901080030644075030080e041a400f501001c1c0040204910a00342000640088181510f452040700d21800203000884002ea103581400380442100000c15030b50526141001030502600300c100e180000d02c004a8071881902405540d0f4104180d5402c00141b0720040070306074084000c1c410300344085141643c2140030703a201c0c1d0701c00721400154000c007d030318450710704001003116600c448001000020407032001307102c4050318222140d260a1070005c0100c24101c0360180005010b5140900c0f60314100ea00ca0020326a105208d18000306001d0032071003103541282020301c507814602040d8400c1084083c3c0c000d48081c01070919244c082030130942c0071030142070110580941c500989000010f0414408100441030b04128050700140c1e54200c0d10444901d42d4000c240c1240055003407114520500f076120065409000e040d01c0081c0841c83d8660030002018000d06004c000340c00b6805010002c140c050010305542 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 977772841 1250 977771591 977771621
    0xc01051602100504170d060f0b1e09030604022e030b010e0904030503010b0c0304081b0307290a020c090c0a140309060103061806180606120b0402150904 67
    0xc4000c0d9800a801c0422003008041e40600d000304100c04a040d03d8240600d6041d40b0800e1583c4900f5440f606014003516006408079a52411000072007032401c2009004046080c1000c1602207000c214000c1e00e441020a8154190b00c0701010034050321702068000240f200f00303d00c1016110650400d0b0fa480c42008074004046a070303982542030300c0d580024042602403021074042c84640703403d65010f411400103000e00001d607040801c4064441d04104110f5010300314080803100003010741d1400e05185548010147c0c028011100c00003000c41c0b840001c50340182c6101102040d15880b10000304041d00b000c1c100c9400c51080f800c0c83d071070301c2c1c9440c00c03000e00800703500c0d03510780c2d50b85180d82024001d1500c04d01440e0310408200300700040c0082c0400d5641c15a41d11807008202d0a2400d03e1170181c003030030000041c0c031062074024004c50152083c0d190090042c420301040c82019034840303032440618070b09000a406240d0701d000180040c504a0070702019014854081c070b0410804da00482c0c1101c01e03100031b864003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 977774091 1250 977772841 977772871
    0xc03060902010e06190f030207050f03090a1a04030839010b010c02090612071503061e06120e1f09020f030d12051003020d0602031b19140c0105 63
    0x15541d0100720f4003d00001603403a6803609000d80c603039459200c1c02d5001c9034200084410440c007900d2094044030810b9030850308441c010003800c10407a480390301100c021072051071729120000f02a607c6640d10b01c1701d12a9842c6050415245861300c004503403000b01e1191103104400d0b04000300c040010501d24040c812500c2c0c0c0100003107209581070849411900c60b0781408003800c4058016520520010f51105090b60340c55154041004528a000340c80d800142000c0e40241007130582e60343c59440b10003140c001d0f4000200301080c90013500c4101041c1c3c0183c100203000f2840124011904da000707071498604030022200101103074046038803180d10b4441c4500560391a0302862040d40341c0303100742c031140800032805003824141c05000544185100d01c40004080d48440000d0482910690100c00854018080c0b81c184402840e0080095004451030480701c0c078841040700250801c0004d403038840980d00e40c400e24007503d001c0d040c1c0381c144508000f4907020a00f000301074050407003070003464001c44150a620300c0d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 977775341 1250 977774091 977774093
    0x31205090d020709060b160f1e0b10030c0b0c120c070602061b1c02071b05041d0723030d0c15020c0c060703120c081f03110411070c030609 61
    0x104014a03075201c44d58681c00c0800900001171100d003150500d60715070500d00300014592400d0407501c031510030b0181060f401c050202070410754402c10f9628440c42552400783c00d40d00c10700e040421082070b003c082d04034813203144180030402e0001c0050040c041c0701c40450700020001100300040d0340c028011700701c0d02c0e00109410843d0580400203541c1058008014446040d03040080d400e4034041c20300c03c8050403a4074942a01180026412100002e40154007024940d000d607049040603000e40c402c880c0140e240140c14510b480700880d4510341070710200f000c1d1071498a40100d000c1e80d030300e0090140010006c964000741e4550f0701005000b00058a03030711103103003032449400e1810328903140c118a160001c5c01006180d030002c1e008140c0480110040316015141c4c502401c0031501c004860683e491030f1450011407000c203e8001c03460301d115505080059440c03000001c60030360412854440149a40801081c2c0d1a081c030b0260012013801e1183c9d003031141401110740780c4003403030702071070f4820b8585e9580c44407014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 977776591 1250 977775341 977775343
    0xb03070618060503131e0c090605130207050a0308060f03030d0903090b0c0c060f04091a0319031b0305070215030601030515030604020108190915050a0b01020712031205090d02 77
    0x1400a005500b4501c4c1546000800d0091752002c412009040103801444104900d401c0d142003140c0320b4101169141d038645402c0600e00a040c98080c41d03205040c00925002012030318021105219407000180904654552341560607001c00303800f440e4042c80312035540e401c0703031400c2016188500e100b100110b548085400d01815075074094100005802d000c0140003902c034000141c440c555103040e244165130f0002d04c000810180210f0700702e109100d0518100c0c283c01500c1c004000b809000440c10307984180310785240c040004a11400050200711510700e2101024501c07101140c025020b403c0586ca0140e0310b600051420400d05854030b0703260008014400207503418070a00e9806401851060682d9000c0c10000fa9901c80003040241040109400111012040c05411002c2c000095042c0440307105890b01890040c4001d51403c0038914020004501c49036600501f1820b1a040c0c010f018054100300d040351020340007030810f8080c00010b042001c0031005d603101c4e40e445030a21307401800101050000003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 977777841 1250 977776591 977776637
    0xf060f18010e150f090907030c020c04051003060e1c0507110901032a0f090902131401050d0f3f080115022401320402030403030b030706 60
    0x818100580440b612a450310790003a0302d56001c0b04100820b450300e1085000390014800c64002941007110941030005107a09500f050000e5502902501e240b5071940d0184000c5401c101c5d54000c0b400e02800c01003000c103d01d60302124102c050710b020340c0d80740904200e5000b148a4401007010000b503001030050107006c01c02d40c080789000c6049a00e14069407554a420100011555800c1c205258903440d020001429a200000078010104000105a81c0e04050402001c1502040e8007550406068558a0002d84a82500768221030b0f140903ca03400d001c1030107080c84001004807948070900315100d003c80c55403284d00b08500c1284003505d03100c505140031310305078100c1c05110f550008400e0501b0703250b07150021801c1d410f4079680340511010703045176041240380c1400c40c449403541010b544080801c459680d1120380c1601e0303804800100700641800c0071420749411401d65500082000c49403040d500c0c2c80c1e002190000d00034940490014030704030001341014095480100403804400c9001d020709404c03864 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 977779091 1250 977777841 977777887
    0x30c09050301390f1d150c010b03070b04060c0203122a0102030f0406051e0a0e06010b0c06070f0905120c120a0215071a070f1218110f060f 61
    0x4103c031040000b00d07001e40b00f003621401103010700c101d2641075283c45003004101800918014180109016049200321141c1e000080703003ca00d5007080700d0f12840d42800156801100c40700c010080c0341c42d1030400d040301c02c809200700481c0d0500521450b0040c1001d110054924850050000311840b1124444e4090607085d146e0003d2290b401482006051400d0411481d80160820008501c684c0d5403106038410183c04052000d40b4800c4ca010b20000f0072040c0e000144400c00d59003144c00b1a62030f201920140d018984100019501c803c0004586603c13035592249ea200040c10000302071519003001500d0300c518417088103010790008203041c0b12441c040040c81c2c51000c4010140003541c40d640c0214400c1e4000640c2403099132000038850040140c1000070800521040c0610501410410801019646100500000109000034802d0101d10038030480380c00d5080499100c0c00407015a0b108101d02c02036015440d800b80448594800315142c8000600208010010490b91203a80a40c00403800025003c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 977780341 1250 977779091 977779181
    0x1b0705010c02062d070c03020418080406030f06050a03060510140d03050711040e060f071809051005220e0d020705120102040807060f0201050f0c030601030c09050301 73
    0x107244000b586500c002c81d49000307240842154000f112120b03142c1d00141c3e880052180a00c0003c0000c28040c600a80d041036070300c01ca0302030001d00f40d4042965200e8402d0500500002020081040050b0099002699039189400041103580d81c980005920a07096482514265255804c200b0000031000212020304401300501c41c00341d8030a030110b000010010781c0107050080000e03410040c002000080001060f00600511245d074144550035102c5030252180c40d018446600403512080c000c0302240244a440c40a840d006441c00c00c00802401000c0c1c40804080c01c0741c01c010540f510f4449900001ea190094203034008025165038400312480b03040309000302d4100500d40c0510540c041400000c881c41281e02481c60000042e100e802485198081c02440c032602c0c400141054104110680101d00c0e0740017085507030348024611400f02e44c21140c85149a0007040001e86641c02307540258100700c3d0301e281102002c1d468102082c04c641003441c48500341003401c100012009107141c040481862100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 977781591 1250 977780341 977780357
    0xa0e0c01030c090506070303021201030f0507080c100e0f0301050c03010501091d011401090801020d050a27020105030c041d0405010b0105120a09082a190b1f0b1b070501 74
    0x5801091500b03d03000b1217205000c00107491007414402c1d01540c010b654003809000c001d594925020410380e800150443c0c041c0202c1d10002107001004c43c1031800120090b101c40850031800c842141c00c1686030310600d0340401d44141e503035000e48003403003181d218003403000d801a07895040c2400903000700101c0d48240200200942040720b01ca2808009a0443d89058003110080c02d03100016608140290001d601d198404901d80940d14540d40140740150142c0f041088030f940030f42031901c0c42080f4141c00702103400d144580480154440d000640d40100080361540c00c090325a03c081110000301212400c11072122010b1009001080c0705621070070600f402c0807403500c0240c1c080f4060307a500081c0140a05075560307540d00d0038041110b00312059140351100c88201c6003092030720100308450b02a10b003102ca00c2090303c442100c00c1710041d44408150090030b021030558404030710410409055202050204000b400044e012100c90085c0c14001401102c58584102112005103850290350025041110103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 977782841 1250 977781591 977781611
    0x60b07050a11010e0d050a0b060a050d15020c0d11060609090601120c0302040e0d080603123705070b090d0c123006050d030e0111010b03060a0e0c0103 66
    0x14541c07000562200e86070411150510040e103090300c01244494001040707509510400030040340520701a8410440b410490300c820040c41086101c901585400c403003a4410080071035a003242c200b60340c0013940405454a800d0b001480e0502d80c2612119010402c0b10340c800200000c1445010740c415019964100c142c5007040106c6d695480c10f101c2e240f0070796814071081d014400c01f5881c0707602640d000f400512140600e21003d0780d4a016120000001403280001324045281c040340d103030200441070040b0360810700340d9103080220b658402800d00c2d01c901100c2c08454202c0d807044040c1c10301c0080391281620348589003040812003d004101303544641080e21110004c90f000f8100741d0189070032810304584a025040c0a94195148101401059010141d030312019055515407051400450009020791640c880038040020902d03000203010482501c201842d5500c9a00f007001b002c03070403030300200d0b10390f00342804241042c1095420141c0d2a071941c0d041d1404039800c005240c803204c000c2c41c2c204112109 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 977784091 1250 977782841 977782843
    0x2011d0d06021809180607140415050a021009020109090b0a05100201060e0c0c07031e0b0a020301060f030b1e0307030609030c020915010905040507050c060901090c1e120609050307050c010201060b0705 88
    0x7d1400c0248034100b0128110150310800341d5020307007103e081d005020051043d000d0070940012240c14014030a031400f01080c01080e02134469079650685940c04810b050515000c0640703040e058064001c0c0b00d00343d0008042c0c3e503880b00d215403a4038540001444c3e9040050109402e0070007071102c01031030b20401481044000016100c0222a007066107190b03c200103203140d0310945c0d6091405000084c5c840b09101d0880c2e1071758001d50490300d041d02ca07258101ca00c1e100c1501640c04e4210b0b016400b00d0403211101640400003e000e20078000181078600141d00c0341c1d80d00c0201e81c02c2007400d03000505650540b004605000070a82c0d0000a0581c5154914554a0000b0040c050070701032031340119105c1010512040c0035009503400c4280700b5043c0c1c2c08a01e85501031b40d0082800810aa17000440048000340070162468040a102d0700700b190088072030306001c81100801e2801130b00712035450b6910405800300c0c5040c009490002d20400c0604550780130392000a0035103030207800030030305024100109000188 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 977785341 1250 977784091 977784103
    0x5030c03060d0602090d0b06010e10121d0d02010b09010509040b1306021b0a0b010f050d060b0f0406030b0612011e0b0315070903051002030402011d0d0602180918 71
    0x6411204a40400b4007460000081e0103010451a0001590b03e0214101300c3d41d51007040c0700c1d4000f03070f0301d807a89041c64000300000c03011039091300c02c0401c0004240da802011650807400810845041c0c5210b501d5415500c00d203020740040920005035076032401c15584d454603006440c01004d0444e241101e9042c15103805106940240000044032810781c00071080101907016104440d20445505c15981d0301100c0e5503803175002102c42103528404006c0003184034200e0403005401d560003c1c1c0080fa071015181d50f0a002451a258502d50240344221b507000190350794095600914415107200c011803c003a410b01a15150b2101140e103181d040015640b043c601d0900c014500e03202c02c0c00041254954100424109600701c5903104410b50940200402c05420036581800c0700e00c5482112078501501031a51b003240400d8800a00181c403402c1c01210b40c82d8560701d0f4035040d100062918035155041c0d52204126480503402a84170091507605104d2403400054465100408007038021400302100c400c2503e0b02c1c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 977786591 1250 977785341 977785351
    0xb0f361501090e19062301080a0614060307030603051603120903020913080706060b1312030f1103120709090e16090510080d030b090c12040809030a0c0312020d05030c03 74
    0x40489642d852400b41c07038100c2c400400b01c2c06010000081003111000b48459a00000d47c0881d5162010840320846846290308a8680135143c00c8400850410007040d036001401c0c010825869000c0440884e005110001000040200d4848c2d800d22b90303c1c3c000e008516400e03105080c0000b81c00200090784603128407075400703500250180c1f820b0b0441e02c0c10002c1801001009401c0d14500718020030740c2e0307003014010003602d12101c003800c40c01560b40d6461070b450750031001c0003000175040030507585c0c45500400d8407401d904202c000f600c0c00c1842c40044051808011144107000440c2c2c0741c403c02c405403907031003212200c00c020000f230880400e289151a1450700306101c0c1c0e0017040d0380d83c00010600303200c80c100000030304050001c1c0d9072802c41244000380036220360071200b4419000e240c0410b21b16074107401200d4886144e100002c0e0656180c0e1580b0410781c005440303494041c00b13100d0070100010001f8903084065885144001d8080d20781c200c000346000d240070176000503c0320801c1884019083d03075050300d0303201c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 977787841 1250 977786591 977786611
    0xc0f04022704020d0203010828080717071e0c090b030c06090609030709091104061d100803040801140709030302250e0a0c120b0f361501090e 62
    0x888400304000b4444c800c0c3c0e40c01518804030011500c50004500d41d2205001c03940401c14408000f11a0443d0003940d04004100f100100490b40000310410b8920f600c070b020140300242003084a845408000310a540f4880384124480c145004010030074589101418200d9820020000c00700046a611002417802a218410103c1c06441682d00c0c0c104030b5210040140a5402190743c503c40900503044846003154030900c214410038207070800344284011100055400c07030084800316400326610b0740c041d00180b0b00140d50f00300442c0106040008000403d51080000b801a1071086801e00302c0d00003034182c1c001c018a0130404c02c0400e82c0043c0d6007039486694143c90b80301e40d28a000304008806180c0c4030a40608404041002e03101c172550005c11015450b403145280310494503c0d12044500d8000b405500034004050040c06084c000326903141080344413040048880d0005e03a090111501d14003600b072200c07044040105032724080088070088442802d010710405e0031300995800c4908014201402 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 977789091 1250 977787841 977787907
    0x2070510060617361207021302090a0806072604020102070519080106030602210615070f08071b1e14060d0905011a0a0f05012601080c0f0402 62
    0x1c4050314501c0601e5a8904c02d00340e0542400c491031041c1c0b8122100c214000600480a4084210f0401c81c1120801ca0340240250000001081100300075007119480d1a04200c0c43c0001051156007000500e01905003a1107900d2102d2040202c45000039041540c6200d200c0c1d20b405000050760005003020644608641c2c50700040740e4240c854051a14503400301905600341200082881380070750040c40380002ca03152502d000207070078011142001c1c0541d01c8035041403041011600d2941044084c0543d0751007450030f415481400c1d00d40042e1a001440d080d20040c8040c00029440c00802d0280c3c80142001e0039000004034040f04182d07107184a07842081518800b1078400e2800c2e9450b030f030484440e1f880c403400820020701c041c2401070080c2503d18014072640721a014003903052030100c401200f02d030588078071406081c1c00c200c01103404900f4419003600c002d10000e0000341c040580c1e100b03580a002c55000500101e602c80e001c00043c04081c0758401d00480c41004407580042d03214202c00028444012082c1c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 977790341 1250 977789091 977789101
    0xd120612021302070206121f090515100c02040203390304030c0f0212060f0106090320041e14070305040f02011103041208190527040f05040602070510060617 69
    0x41c03c7d110365040110b040e104001040240c107a410b0581610b188036a040b004038030b0300c3d011014122074007074075203c900381d6000600b502d46180c2100000262110380ca850083c004040c0d002c02c1c280d07001075461850300c0e103c5542c49007000a00100d00d040540c03c2140d0b1003502c840b006810300c41440701601c06420130090f0b40b103060900481840300d01c0751f83da0290180841941d00c20b07203680c845d0b41c00e48009070101c04003400001c40380e11030071101c025240c110001c500101c12800400d085181001d242580041d2a04101c1043c8d03814400f0710f6810440320030300800c41c468440c4050300b1480d402880c0c7c8050500e0a401d20020801000016070f15690a08180790041d10090207a40346008660024110f807050144000402c42000c014044c00c040c10b1214207041c03103d124040d100350140044164850211200c0f507113403002c0d1344555201201303001c0c00001c0c4004a030749010090f5601201c0940b80b090b00010682d04103c0200300400b01d40c5070140c020440c550410500900303111180768680d101203001c4000c60 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 977791591 1250 977790341 977790349
    0x30203040b0f2a0345010605040504150b0d080906090307240e150a05030c040302062704092f040606200f0304050915030d1206120213020702 62
    0x1021015034244080c00503803003100f42c811540d204641c3d038a408404c603810059039464032440e0038030606840800040b01d00d40100c031180819012010214159200e20340046c8540fa1403103160700460080070407602010031980260140c41c02302000d540a00302000d0340c503001c21388000907600f80f91012107403182c1c1c4007490070000e4035060a0790441060820307041441240c4d41c81d03008491f0002145a220480c01d0350000b030030090140e07a10603405500e02070030001c0c1180107116100070355101f580c140c0100d092580742c5d00031504a40141180000394817620128400740152080008640d0108603001c0c807403d401070b612864002403212107604a03c003034404040304188901030004031003102801c100302c0d007a0313914001000007050b600d11014100781c0c0a6614441c200104a521203403115400441c509403420091161507031004010150781c20781c14136034281c2554180941c40d81064251740b0030303ea0301c502c105140c040703031629480035070a0424180d51800507103545101c004d00c05810b900c010b8641c01980041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 977792841 1250 977791591 977791621
    0x906070c0230010f3612030c080c0306130e0a06020d060f0503030c07060819021b0609070807050d03050903060c030703180f1101111f0c030203040b0f 66
    0x5031059080030880600505070100028507007401040c002d000c2d5079181480c070821a00100c2c82d034112045d50701394980302110240e64800700b44a031144100611001512640c0f4000b41003405030300040d48a40a1840055110714041d801410002c1e05526500b0648001403201c003401002d450b032552a03e0380b03500c100200740840010b00743c11040665941255600c00e9006149900805801e91054071000c103441c200042500c015101010081c64010304022054884c0d000091005501d00351702401d005150f8110b00141503030b83d0308800650100c0c40361500ca1410048000d150101d40e501c480c80c10812094000f031080d0464006807005003019269040440d07941c85689005505442900d0501482018107001140b0849081c0c0d4200144101e18034000c0340d89402c0900584041c0d40102e54101050001c0001c0c10340120505040c03001300440d8000c1400d00c02004410001d030104c0320340d480320005982c00b80303001012640c03604500c0c61501d41e448600080020b04100c1c00142000d0004070a14144601 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 977794091 1250 977792841 977792869
    0x2a020322051302090a1a16060209040218040b03240907080a05150f062214270706200109020603270111041202031905060714030906070c02 61
    0x9400b16030803403064082d5120a0f1054007402c1ca6034400101241070b0342c0c074001850303281c810721481c0c0151102003003038140c2c0b10034041d00d205500308411074042c0d580788014004070b803001c1103600351b910742c00d81000300302c40f4070410103400f0b9040805140311005209104180c00180101c0c00800f41d1204103415140240c0c03900524498032403203911348103112002a0b81c8406060140703004050741e0399a501050640310540d81c80e80c001c44980c00d011401d032140403284000221140c40011080800740d003280174204280c92441000069828649480313403e070504040c16a0010005c00000789407000080000c20f11500b00482e60031500c109600440081d040880000d4000303240e10748a042181c2d05580004884161402c100805c5d50184501300341030081c00070700000ca4941030706151800d10448007600e0251000c0768507000d40c1c2405140600c00080d03156540e070044005001910b40070402a0124050740b5911048041c00e200300250b0400000e07545030b02c040545010345601c0000e00c0851001144844 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 977795341 1250 977794091 977794099
    0x3105010615020f0d0302040303050403110d0b010f053604170307021006080d0801210c1d090f1c031118040b0111030706020f0403050601092a02032205 66
    0x15101c80141d030016000780c03542016825100e1a4030b240200360103c0c070403407200a0200d04240000c102245e12005200018040503144502e02c2c1c00550b102008050709802003103020003030050602c680d00701580425002c0400c90350782c54419482142c10b0326010041910004103142510009040200c907601c9a02500c0d101c441c400e85030b0800c1080651510042c07200d1502d000d1070210f000840072030014900d00c240c00240c68180c000e900705464100d00d0355070035403240108040b00342084c000884c0c1000b00c0d0000d004199900e4204c15081a02c0e03e600e072409810305100703074814001038241c0c0c400815142a0000007100d42041c1d5400380c01d09401400b54103142e050007041c0400e00402c0041c0c0120200407465041f6403c200c000c04140055418000d12000f15995600c10300c0008001141d644c01000c1c030801000f515403c1c01d42d0b036641ea503c0c1407c00d800c0200c0440e25030201c100c030700d0f40ea4409074082e2a64416114261590300354006e64902030800001c032010110384d002c40b000c4041c841c0341030250201078 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 977796591 1250 977795341 977795369
    0x30e060d0b15072102010b030313261b01183c0612060b0f04030b01141f031b050403050601080303150d060212100e31050106 55
    0x4000500105070140705140107210384860341d81007140020403614a20343c418000f10300720010a5440384412105030740901559078031960000b551ba000c0000d007600f0030b8800100c0007218244000040e800c00e015400d071100320958205508041800b04071030005140707034151003d000c0050340040300c0080b007a84811492550418000ca960b20b403a04211140e83c1104110005510031809042801c3c11809441001c9e101503d2041c0034491150300e5070503c1003120b407000710301940c88003001c600550041c0d603040e014000003d41002044500550540102001c605083d01c0361a808040354070050805c400a84600d088601c0001da180280e1004d03c0150a01c1007006203000746400207800c1ea03005000a0322984564000002e4000c0008116807040842110024015440e50300740001e00301d0f0780c81d0803650f407a024000c414072641c2c01022070380303d250320115072603420f03181c4009020700d03801c040c0c140d08e8085c4145061a0301c0c01002c5500150a4040d044002ca00000509019006001507042400400401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 977797841 1250 977796591 977796607
    0xc09090a05060306070e0604170703051c020d02010e0a080912070608150a140904051c020348073c1202010c0602281b0b0a09030e06 58
    0x5a008501c02c400607011192641c5403014155094074814440942c017401c20402401030340242c454620480b0840411070700b100f038480c0d94803410701c40c0b0b0020102422620013840121329078100b06200c190042c0b40000c2001480920f0301507218020000c024021440c00100c0c00100d0311000042442c1a410070141d525117601d6100c01452070364150303040400b50400741c110000501d0141c40200c1156000407813900b0b020605001d00000345001442070b00c89001b0342803402464000450030450340c03c0345502550345c8625003074151055101c00f8403980100c151212011500c0700458400000306490950041240250400e4052a000b4950490f0403610150341411410400003401c0e042c00b020a0066808002c3c4100080d054034030b07091040314284102108200d026502400029a006010b100058602404503070080070035294083c01c003a50000000300315440703950020820f0000c03540c8a0390418000f003d515034190003c1c020742840200c81d45e80e01c0d220101805400c44400d5171a0240c0b5654880d011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 977799091 1250 977797841 977797861
    0x180501020a02010603150b09060906030a020a090c080708041a311a0c0406050c19030c03110c0d020105090303071205030f100506030c1e030a09061103010b0406080c0909 74
    0x280300c111080c050032030806ca8018058040e02240150242048400390388a03020001441c0024006942501641c465a0050386407000410040c02c801a404582c40744030400017003000d80c00921000801c0b01907020f000c0000c81c0d00c41981d001d0070840c001480d0301c0e110714040c0310300c0c14205104101f21007860183c6020004c01031240800303042c01082503809403a4964064080300c2400c030703112607059100700710901001c0d0043e00901906034030345045911092032040c101402904180c810350116261549280030103510900c8401c0c02200100980200f2880f080458051066414000e0500801152050040d2400c02c2035074140e64101d0003d20040d110000044c145900503200c1818008a402c005402078190001030b00407900c003e06107034035554030340040441e590011201c0c02d9078180a4013114513440a04006140a03090703490000586112604d0414111026281c007000124020300040041078100001c2d14100d603058144200d4030b0340c5110510649200d6650b1181d070054203c0140507070070341 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 977800341 1250 977799091 977799101
    0x9061e120607200304080a1b08010c080105121c050f0c030d0c090801020c060f040f3c08030606032a0913200a0302090306091606051606180501020a0201 67
    0x144401030031048030030212842e6203905c21030090041581c8001c108034001441415000300020241400040c00c0d51509405802c3d102c60011b0a00061000401808146080058030100c0c1003000002d10480f8501e100340c20059048400105c14404041005010b4025000c111031002c0407803000e503035445210200d40c0d801000da1441600c0000c24a4a002c108500140300302c0e400c19415800402a50303941c20310080c550b4000800031100c8807040081c00c000211296802c6400080324001501400c0144129540905901d0741d2900000008444800840d040c0c100b1250485c20a5501385d0f960b688001c0790700da0340e8544610310030480703070307003c555440c0c8000700c1d000742100d000e0884551030000c9650140d50207a903200d01040405a02c0c07440041c600150072002882c8a420608001d414640294000303424107500700c0d110980b9800030341038201d00700c8041483c0b001a14080c00c101d810808000f058561400c00c00744000e1526684080e000070301c3c40f51826101e400e0754888000d6545450001000f80640307 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 977801591 1250 977800341 977800367
    0xa081308061e0a050406091a0f09070e011206140f0618010b090d0201030e100e070603060e0f071407050d030c020c013e1b09061e120607 60
    0x805000301080c50100c04411604440480002d2503031580c031541d2120f0000c0a02400443d055583e946052000401c8400e00040c8a1302c135203140a80c03444d01086d0502824001071030599250030151080c0300b2041c590381c40e40d05651081c02d01a06a142615000005100c040141d411030b101160400003203242c5090490301c941800c1d01c502d80c801804011440e40e06000780140b000c4c402c0140f0001c030311818410b050480d80f50051601040200b03481c0b107803604000d404079800c2e81da5926840f0618140d02d08002000040002e0314041000520b081c0c02446a01405841182a6007004001c506031038451219440d800850014440d40c4440901d041c0b65191040d16590020908200301c144805c3d0010a414070b8401040c0c4030030318148040520800d030302d44140881440801d0703080344410040700e250f040c00041100b50000306074009000c000912403113042702d80c8074824100e5004000460712041c0c110407a0f100440042e00716031000c0d02c00101082580100000d0301c1c45030340100801d09a02c011082c03921 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 977802841 1250 977801591 977801593
    0x9030109080a14090f010e1503100501090e040b0606131d04020306060d121103040e15190b070206030a1e02042c0705030c0f070305071e11040b030a081308 68
    0x83c003114403209040d0701603040c91990006000040d04415405040495482c1b4130007480091341c48101015420b46810540d0100600013540406108075604041254041c00000348035100a00e032582d1843c603260001042540245e2000c20440f0072401d2040b0030070003070103d07501604024a5045140030205508460991003442294003040c0181004a042080c80c1d400c440852603061903001c0c150b5080080c2401c808840c40100000100c00443d803000d0750041202c2c001c1014010368880400c00424110950f83c2031154500d1420440340e00118219502264180e4010b80c0742d92300d0543d00c400902c610b610300014203007407804106000d9642c1d802042070301c011101406a076810412004040103000038a004031548880203e40b40302d000388061540068000c104628189441c0d5804d402e0703404c945401c4022620118110b01082560350350788940300d01260304c4c1d101a007002d45030020034001c1460f006000d903a07580d00c0c000440d2414000c0c200c803a604080300c40d954040d07001d211a0a220307944a00e20007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 977804091 1250 977802841 977802857
    0x250c0b0d0f0f140406020f130f0603291c0b04060f1505090c0904150b0c01050c0f0a11010605180f06010827160303170114220209030109080a 62
    0x400c0d68680f281001503a4000902040c0d540c030703507803600002d5008143c6050029400d01014a5503581e50723000c200031b400c0c00618500040e01c1c0141c050b040d02c6014000b00030103801440c051b4551800d0b1841c40300005411103401022108905041d401000040e20140c40d03030308480100814441940c108031104180802d080244c0d00120422800c2c0b20414020a5132141524012807420458030000e030000240041000404002c1c82d44000501c078042d9000c0e000429001c144c00540160a124540c0d000c0d0b075145c2c80f940f500c034005076117004a11402d20744006100740700410180000e82588140d000d4036018055010924402e02c49851440d0b0450740d881b01c0b14410400201103500c1080c145025400c0f05a50500034005406248101d0110222480c02d504c108102412110b005c591440b00443c00b9858a8203401ca51701781a0001c4401600300d41d040701100300e00d80c1c1b0703c4d85440034008440c5901100001d805000c1006200c064030070302c85041d034998203004016003408000c6001348400419600c50780b81c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 977805341 1250 977804091 977804111
    0x60e0d09051203070615080607180e01060c062309010f0609140c07052404020306130203030d1a1302030106122703050c06040b1803250c0b0d0f 63
    0x480d000b20a15416420601050300054142d42108402405910b200034040741c03601495881d1110464480c00010448804022503855160350240030700030904148200390304080001c1c1c40b4240e001c100424aa0751409419500c0c80000312144104000a43c42d40a506000034030034081c150705082480d5803807400d100003802d1680752061440e06401c4840c5440e09559500e41e4044682221600b90340c10b008a615150582000703103100d000c404000340640d44141080d0050603c0c040c0010440310008400344041c801507600041070b1070429091010114106000d00b004c485156102448c0a0300070218080c0003501000715000386051362010b640d0654a1b40c000d00c41581941c04088503071070307a9a10800030011720118811942c849a0103410100d00d0120510302d11803a040044030140c54000e0080e080c04a041e0000c0c3c0903042d1855084011070400c900041c1324040c07007405282e503d42401070b50f41ca40040000b008440790040000187c51525645950301030b80143c406105040740081c0f401034000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 977806591 1250 977805341 977805349
    0xb0a11030105030c010c03050f0f04300803090c0303030c030403110d0c0f020d020d060902030c04020c15100e070503010503010510060210050a020405040606020f0c030c0102150c07060e0d0905 84
    0x3812980c004004002800d5144c0054402d0150b014068007000000c00c030b280802070f8180000c01c0c00c520082c00a5035074624140601050703030701b4112030000416200340810507a50301d680c08071840a40018401d80ea94440840903071904084512083d018013011013040000d111180c043c40c400c85c060b448000c3c1c410303241c0c001546c4420304c41110794003203a1031490307002c0890b54409420380454406408000c42c100d503500062410b2640074021038200391200003180450500b8421b07102c9144064800358104100f03109044c0d2035006800a00129039070b441c0025810324104100312008004000340d81800b405c00c0103006006034801d0150034002e40c02d04002c51075051000e004442107641e154090140b10a5240d04500070b0034000d00361018041e001d00000c9801d03a1148181c0004110540041240000d0504150308241130342480324860f4000d1310600031281d80115079004a4480f948011010341d4442a10400a01407a80081c100c82d14011100203144000a84500c6a90441d1036188040c0da0f00c030104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 977807841 1250 977806591 977806597
    0x2060c0703030c0e04050924011229090d181d060111010e0c040f020f070b04060e030703031e15090e01020c03070c050a0e07020d0e0102190b0a11 64
    0x180004040410051001c28441d038412000380056241c1804002c8560002509030350003543c064040307030801c0c007091002c00c00c030383d400705201780142000d980998542451241005491500500b11a50558560045000051011801940e1404001d40c3c42c1080051076036685108005640403402c05485040c03c031084d003d0040448041410400c45407502410b890980c12010341058144190447d1b40b010b0071200f030040b00b248a81b130f24001c00399440900104000c2c5c030b00100503101c1c075601c10001c00800f050020300f1601035581003c1208401e44a40c50020010880721081c0e00c01400007282e080201a410307080f501c0c855120030510b690a04051680e00c00702c0303074001d4021002d082d601c00100b207000400e0300300e034040340c1040c8001424002d50b4207610b4250703031055008581013800b9a60a0082d4379103c1b0880b0054081c0605c4041280740150b80603590300780444104080c400c1c14004204583c0c030800012952174205a203e14070344119141c034082141c81912114040750034085c2140f244000282a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 977809091 1250 977807841 977807851
    0x31b0c030901030b0d051005090d030605030705090c040f030507050906060901021e07090905010c110a0506010608040c032102060a02070f0b04030c120903050c0609010807030f0b0a060804060c0206 86
    0x186152001c003100540003400a0301c081070b000b02480c1011700c04900305005e24108440b0b880c00102c0c13185041112075007080f814458010600d89000014001d0780c45c00240741090311000e0f41c218200d611803510380c88403401194003d0f13441940702c00001c020803001043c040221070084d158441030761102c0b810011107000305079442d801a4090655895051b01c002e000074001d0945000f07407081103440d008948180e40d0052020703201691110030f4016415880b04c0c1d94580e09000703001074624155507070ba03210744904041c4126010840c000d0081018080e204094000540e4042140345c0b010802c1c1c2001c0c403086041d10a000b015004050000b48081e100c1c0c0225042103078413888005807910180d86402c0c2e0382c0c0700074100b54100b00c180140c0000103440c08100b001e10700c005482d928002859843c04918004404010038001c1d141441a041566008a04290424840d0030081140c1005000000041c1101d002c0075601c121003200c0010b9203500980da241c065070040805126448402c2c1003aa070b16001510 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 977810341 1250 977809091 977809093
    0x307080d121406090a0605031204081e0a060515040c03151e031403131d01090c2a0501020a0e12060c25050a080a030c020705060901050711100302031b0c 67
    0x28558602000c0180e442076417410001802515100030030700d030150031000c011502030300003418450b0440c01c02c28255040020050071889403002c0144a445400d03c0340000d20303071034451010543d45051075940783c4101030302400402402040707110007070142144000004041c00d8180020425040c000a100c4580994502000646d45180d4403d0542d0340c03051012002404180f00c2c224010070f445180100511213400442c040341a908040030301e20304107a00c11006203141100240034103800008100e010501f21001283c800300a07100d40940c21903408000707006520000b00030320055000240201c2c0342001303861554654203d003034402d42e00d000c140c4903030782504028020f01c2d48a132044800b1004010a1160010300d40202c5d0b174030a032401e08651030880e101440410000601a814416082d84201e40e100030004185004046000d52007000001410400b00003a070800344908241d6400120b007016002044079401503000900039081555508815056a00c0002c5210749590680d0b8030401e07120 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 977811591 1250 977810341 977810381
    0x11030a0c06240b070303060906081c03021c0b031f021b03040f050409020d05010e15060609090403080903070b0c04050a0e010b09010c14030c0c010906181806050307080d12 75
    0x3c6001681003400100c1c20151101408a004d404a01a00e001080003400811003140814080d40261036600359a00030988103100c0c4a0800d0700c4050b5808035845001c03800528901e84d04042400d00000c0506484600240705003681c00f41550f6004000d2000d0602301486603801d2860100d071607105074801d241c0c1c3d50921040520051900d680702e902da03a131000304040384a64182d9100380c25a0780c03001c03004515410580c102c01c00062904d111a6211400711105440d18001f600050140c80c0040c0014003080f07206400915081410011030f00b4840d080200400c1e10719264014208903402401614050200b03030b040020600e00e88400981600c0c2900b402d141041d407060300440d12000014026110303000914401d0701003041c03e20080404100788005132a0700d50000c0c0000d040d28030154041020071481c2c0c103a64420070340301c41002c0c1c01e90b49040c0000c500c2c5180c18072404044c050721b4001c2549401340280028004000040700c10801c1c2d000d442d1583c0145200401104451128100400d42c207049 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 977812841 1250 977811591 977811599
    0x203030f03131403090f06090310050603160806150a032001090306060605130b041d06030a0203060108070801050c04050a0b0a02011b051b010203040503091011030a0c0624 75
    0x228099a80314000c48240031980d07a1940361103000a20000c800300c03058000041000d401d01b0402081841100103442945c40d124440300401e64440d0000540300d2003594450210b07503542c0d03082c001140c4240c064000c0c8080f0548801600ba202c140c180d40d03d03404181103400200a50401695103822203420600c3d00c04074048420348076400c030044040f014100b0001c004040005003c3d44244d43c068103d40d52070300d032140d0100d666130f60004459005865035810900003005130324a00318041c01c080003401d060744120345650f40400d19021045800075814040c007800030481e4600011420202d880c4d0a0085c0b0040d1035954901000d48142d0140c5500504003000c14000b01d1000801403040f82c1c807605c000145183c2d4848503540e41c03601c10b02c1517000510001201c43c03440102a90702060320a054000b10724600f0141c3c1d48550b41c1c402c8600d6540075200031540701020760300810344070040c91003031015030f60380f01d068a034010400c004010046480c43d151440a507600d041d5034940080c00400303401c00188003414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 977814091 1250 977812841 977812867
    0x20a0e03060c0a1407150506032a0f0d0203011d06130c030b070216060806010e01051309050603030706020408010c1106040b010611030c01061712030f150a03050f0f010513020303 78
    0x89000310303100c4c0804008020001c1c440e0401090a0b41042000140c2c07424900105070070310210080c0400c1d6807050341d604d0359030a05042a00a4180012a0000d20341150030001c13894851724244040d5240d4a003909142c14001d20f29011003e0000410981c0d11543e034400b0104c80208000350041c0c2045a003080c1070000030046d500c11b45d00641c8a0044451003076040d0f01042400d0041e030001e800091213801405829600040003005800003401c00b81c0c1824600b0000d8141d4203440d204100d1025200d41c007140c03050301c0c00e000311044150841001d5507696105c140d0f090107007010f401500d0019840240300f070860140420140d00407944036007045c0303007130346807200c00c8403070300a0420140c2e01d41c0000c102007900110240b046800404e14515000c40d41a04600060705040c01d0701254103c481c0100100405005008152039200300c010039990074821124000c13a03002d1100da04010b01c5481003942005112000040e40b141c0c6146440003030025540c0c8100318005006070b808000d4155006104801054207 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 977815341 1250 977814091 977814107
    0x20102010c09231c0f03120c1220040807050f0409050615031024240f030212010909150e1f09050307080d060f0302060901030e0a02040609020a0e03060c0a 68
    0xc4000c0620b80104d00c54660108500c5441000b02d440c0d0300200c0941e410150407005a01e5000c1d8103410800c138070100b04101400d03043c400c1c10701e6400c7e140c4d51141c2e20f138035100034850140308412180c0010b403525104d80c602ca903100d40034080c071449218010840501e82c5410301903d6441d80d4070902a020355194a112580030090740d00f0684e178107005040320311804962301d00c110074018141e00d20624031200d800d05a2080c89a20b0340010104039840c52040d0a4151a0a40c07415940c0262a110081c09500d0b08120000c4c010348804440c4409103c000003000d030f10f0b41d040800958090a07601c0d403880c0740c9000040c1186d000e08440c2d01c26801060302c0460280e1100c0d40c090fa9498644008140c43d2884e035a140d0441c3e21900080300c07000004940a2400d03c903602c01d460140c40f032b105801c100725085070001403540c05015140c1e410940c40310030541140d0f4092200d1001d1941c0a0310a001460316049a000a90840d0201c000000d10b6580a00c2c0d003440c0004840d40246100171603030f403402001000c1102c8500e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 977816591 1250 977815341 977815409
    0x30108101107110a031403180409020a050909031e0301061209030f03021e041d0f13080c1e0102271e0a08060709153e0a0609020102010c09 61
    0xd011151300201049042080c00072400c07014014694604207103001c03410340d00d036603000c81e0700951501980e000140c4401410030196001160603000301d6903165a09851442501000741840c02c20b8446603c0f0051200080d506940c00d50b01ca5000d030a04010361031048848880300130b00003032250300400000f180681d0042510b10407840ca0f1956003403080d001d4941c158050303804500421010306184c000800f100c0300e2240c00420b1011064000d00b0106520707100403813100c030003400080b0005588911100304001102145a0300c0c43c16581064544100c42e0003500459903040103e4008151a0319845100312503c000020051540302640b5000302985031202c49103107440e8121407404804104800c04200f0a80b02d0f00c01550342c0305e41c440c1017050081850011106035014020f4000c2c000741e410140111500b81c4a41c20011280b201586503400f58030300d01340800d4890716000300440c02c4180b0102f070700304038800c078002c1e0024170020010000c02c940b0032815100b4111001c541442d421a071307810000c81e41c0a03507 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 977817841 1250 977816591 977816599
    0xd05030c0f041404150803040905060607140c0918061b0c1006080d0c030f0c03200601090b0f10050a0c140d091a091216080303010810110711 62
    0x2103101034140007030392042e00b010110f200c9400301c00c140d52601c1d01841c141170301c198049820080c600022107549001c0ea014030b60103e81c5603c002546030b00c804096821030f0380c1200e00d0100340509020703030544400f040d070b22080c002c04107200082c518812400300070300418651001007509a9400105c1c1c00e0340003510500d41450381c0c0c01c02c681e00b011b040c04c01c00d040070400320440c0001c6a41c900712000d40f504459041e0407041c080d4111a00c40031942041e0300c941805001e040c41c2c20440d8131803404403007980e030411354519045a01004030101900c00211a8103855481d4020400314110f0403c02c000303902060740c0c90307900441022600c1c00981c82000500301107041d0741050641c80016070749480c1c2ca0801050306030700b03e502c107100c02100c1d039500004d104000c01c01041d40307281b0310999008074004e0344640e0200078025800c1c2c7c242103071200c400300462040c1d03c041c0350381003100340d07115050940c40764003e02c1540310301c0c8500740c3e03101d8820b04a84107110a40003194000d03468607915a440c081c8402c07000740b000f82c2c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 977819091 1250 977817841 977817847
    0x7090c0323400203010e07060503180d0e04050402210d180308040515090a2c01143604230318040b0a3005030a0305090322170105090d05030c 62
    0x1864010441f000203042143c88a64130307441c01031020710102495482e06001c0d40d108403d40802d841d004000c5911507581903902003459036a6001081c400150308121503940c08001e554030307100c6003002c503000381400369666455000d01008020410041d0841c04040d144c51420401008180740110146585200d803020b05424040c00c1d50000b1030a6050703900001d54440064111a50f804064401481000c01110078400550600e030061548200803c401805001141d140060f43d00400d00010a09000055803540d11011501540450101500e04071450500b03288950035003080726020040c2c5180c444021030412000c03414441004104100b1586c01c99a00d43c003d006503100c601300c80c0041d11134502446c00509800e6503103403941c450307411341c01482080310320340c1c0d00016401320448445047c2803a011a103901e90964940c110301c500c0440e0b00c495001405c1c1104180121390520088a400c8031200c000c3c2210940396600ba00c0049510404e503411000303070f00c140c050068024540240352922060b007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 977820341 1250 977819091 977819111
    0xf03180612070f1b03090e01090c0c0809030c03060114150c100f060e2401181503061d0105011b0221120c01061505040807090c032340020301 62
    0x101203c080340c821740c005075119500f84448000140c0103030040c071810800b007080c0e03180d58000406040031128010034841000421640c1707680c0421941c02c0e00d2038010f051795040c1d60359643c8060074181c0000141c1c0203004528845401804400544106940390400f070a80d4030b102404410007428024031215150380d442c100480c004a200d0b19441c80b42202024103a0b00c1c3d500214804102c4504040350350420168900c00e22a40b203803510450200c0d079035809188842c041d500001c4d00035202a422050307500240071814401d00109190340c6040756030a80303460a020924425130050804000c1000e90001100b1080c1d4910410195424024280c0c010039103510600105131526280e0220264035040d0391030b28001d011802400f90000c401054500340185003a01d09040380e500d402040c4144001340c0d55441c8500d45460003a000880c22a0403880780c1d0f641748041c00a021070354141952030048541002040a010003075040c00440d0090681c2865502c1c0403a1310703a80e0360425454081244c140d501c42515074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 977821591 1250 977820341 977820377
    0x81002130603110403060f0f050612030403030503100806070c1101020309090f04050106180605040e0f070b030a11070c080615130b04020d0204030308071b1a0a0e0f03180612070f 78
    0x41ca1f00c000f043e804542564802e0ba80300c103841002c0c110034450110a000701314004000401ca0f406c0ba40e043c10669205c5d0355509040c04140c0850703105400718000c0d2002c20004c1540300314800e400300d01c80d50380041b4122854004a0b901e01074080e00d19048100c0c0c401051210402c0140343d5071044c410350000c207509859031070388080100e0b1410300300307400c0f51644d60038803807840c041c01115075a4001400411042c0b0070160010303030b103c4c62481010a03c01c00000450111031040c1c00000e40390890a01c0142d45650900d01074010805920801d44c05e070050701e01054903141c0d9004152034070a0024031000c0814527101e00729005080650701254131036800c20040d001e800050002c2e00081d8080e03100c2484528008601500c4500c000b00100000d40608004e00005100000300c3d551498690040024540e603c402001c000c00c84152980f08034402c5510070414054000010320500480c2580404a2800d810902405018061030417241d40d0b8140d00003641c0f94805e8003007a5050041d803a200c280605072078035107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 977822841 1250 977821591 977821601
    0x80721151d0f13061b230903191e0308071407150c0504120b0430140903250801060e060603041e0501020403032d0c03110102040f08100213060311040306 67
    0x2800410501015900d4007400141b480800c0c00716242d45a1400c4031b59400039131180720342511800d0000c1000000d206001046190320404c41c0e0240304010000890309010306041d10032128427001605069905505445000684c1c40c82903110740e4003d03840e4240200c601c06014078450b00c07020040e06000005081e20503002011100d4028460911070382001d081c02e2405142024607440800008000c01c05286600d00c109150540249400d403100503042050091a1042a403a00d40c14401c4400d040c9000714901407c075100c8012503601510150350351902820307584588a0741c1c8124020f00001405030038000021039125108012115003201081c2070444400d8000e401aa0180c0d80481d0900400d90010305281c0e02c045800e8904413a11258240710700000c8401d00198100f0890080400030140501e200c4142502a000250b407600e45428584905403440e20403100a842030200c0d110ad0b8070314601c01c8030103ca0000107946171050804c28198060045404032441d9076600704400408070300e462142d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 977824091 1250 977822841 977822891
    0x905030d270b07020f040212040f020103111c0b0919020306060904060308190c0f0807021813051e0d0516050706031d01050106080721151d0f1306 64
    0x6183d8540009006000c0b01400c1c0840c2c1e98000d80c070400002640480750000c440c0d00c158810b214616040007403004078080c14007500460009240031441194001107203c0800c072190800310200718803080d41e000c1000c2c4030810307120300745040d040c0340821022600940045500800107800c45203040c0384a40824112812070b842a1044400825458808000484015108804c501d0700d089840c400b0f4440d180c4841400600600000c0000707400011501c5455020700490741c0c0c02c1c001e80f03052a040d148c00407010305400c002c45050103000041c0588100c01d481024107a03c0f010001c0c44a2280c464081e241944488000c516001001e40c5450000340c040101c02d019001c90350303010038bc00820070b0000004038030302c1c04800c13050b0f4100340040c04400d50101003180d00c4000307440c0c0000d122158101852401004111b1000558180007101c01c0707100b03040d2584801c0301c4010a444172040300404008006107001e480c0068001e1107400401d21a80005591000240c01840c0005801e00c040014404200c18440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 977825341 1250 977824091 977824109
    0x605060a020a03020d0212090f01030915060f05040509070527102309160504081516020610050910090c0e040608160b03090c09011d01060905030d27 65
    0x710400f01a4144008250f44505000801c1c80300301500d0103080b80e01036421518000c0358100600c5600d0307842908250719858005207102c0c05c8141c0c0b00044070103448035000344440386030160740c006001e042600c90284038071250070103820f40c0c4e0b05280420098603480361101941100c00c214070030300161040641c80c01548001032401e21589046000c90100030030104101c980c402181690f015501c41804490b4403030389100c052165845540c1e801d07981c9028030b41000c4c1c8603100d802a400b400c1000c02c0c8055004064400c8410409801a2000c0b42d60f271104642208104040070010026828511038103600324401c0d00b08809a59201c2400d40d048a624506080c0082c4c002c01e9050f44500300762040c03101424046c03000c1c1c410700c0e08000003000507070270912900400d07140000008907600400d110424044a00a10b074000340c0d65100d003603d0300100c000c2900d800c0d4414000001880c41e02030f4000c40222140600a00b40401e42920190fa849548150740c81c0a4000c002c01d1800f07045450726100c010f0b00c5e020b5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 977826591 1250 977825341 977825353
    0xe2106130605070503131401020408070f1d04120e1516120201061a030a020d060f1a03010311010c060b040e150906012702130e0103120207060e12010605060a02 70
    0x401d110082c0e59000d095030040c8202007090181e075040303400c02041540e4024030200b8410300604509402031041364050302d0140036403a0003042c81414518680101e5400040030620385a03501e0503010000803d6900400c07691040c40b105e122140181aa80e1355039400a02040440e07011401c400b24592201e80d190140c0c18130705000508200d0785042000103411948020400b00d0708200c0c850700824121446100340e06c0c80031001074030320a8a50129038009030303805020302000e0741d151907005210f5054000e10600300c030100303502d9454082403015a812070340c1000c1c06c0404440108010b403080b0034102c00c2618400e44070ba0b207072005c680b5140a07490817200c0c2c0c10010301c210081c0580c4600000c5000e08401801d401010041206c0c3c5954021503800482d20086080e803040004105402880f640c0011950602e00c1d140004000f145074051504980c0509848040d8055200080340c0b10190382c060030001c12001c0000c2c1c841402c0c203000d4002c03094210f20001607090f488400155146d0800050b000040e8001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 977827841 1250 977826591 977826593
    0xe0103051507120902061308010204050a140105070605040813030809040c03140f060307090f0903030c05030610080c0d1410150806130f0203090f1605010e210613 71
    0x400000051104203404081c503800d0503900103103810b03510a04108180c0c1c941c40010203541d2400200d40d50b041c02c404100c11215540c0780c1181c003035042441402c0c070503401c0c0c860008041e40108a140c21122059640620b00b003455942c0070001c00000d0801d540c40041404030b841d641100d404060302640c041c00c281500e41d54124100029903007603500032000c050416400c507070011124242203400031980080d204040d40c5e004003080c54165658000004a414080841c4100600341c2c07109146900960b400e1242d1440c100c81601c140c0f00c1610b609070440070a410300c801603803049043c035401c804102111441d06411501c10000c0c1c3e203026030718444030b02c444014003e5601000c04448000e000400c0710406000300001c000d000c4120080649004a014000d5401424280d078082000c0e181071101c00c548908115a031a969100c0181e11100284210503000b0181d40840c0764007001c440059641840807600c4c842488802410410340203c1c01e00070f5110052840c0080c000709220705400960a1801081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 977829091 1250 977827841 977827843
    0xc081305040b1e040906111908010905091005101a0d0f0e03070605042117010e060a1202060f040e04111c0609020d0503030c0a0201060806060f010f0302130e010305 72
    0x1144910480483e80c41d10000071048008414150003190001011161405e10001810451a440210010005d9400d001c800b20005040a110043d601d1044580c0c90741c0404003225070640e2826140c1d4800f90400c200703001a908042e0380401100a0071490594542e01c0d043c003901400660350002034089120013411030940f1864800d04548402400800124540140c480c8200440075101c1c1e5261400103061084680d1200100518810b00c082c480700789000007042401e9038030303107061110443c2c3c00001d111000580c200f40a44002003440c61001d240030040381d03040c2041c05040b80c208409002201c0071070201000340004114403a494103252910380b42040518103d2001c0500ca00c180d00981407564040640001c015540b1210014800d001800054002000348600800b40d200000400c003004003580c001d048a8001d42c2c0013030004070785800082c2d4440d80101c590580150783d41502ca20b9070343c810300b02e490040342ccc107040040c540b07807803031803e0103201419401c00000039204000400c20408 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 977830341 1250 977829091 977829101
    0x200d060501180506030103231e1b01140a0311040806070212030403200a0f030518031b060f160501060311040c092718030809071a0a0c08130504 63
    0xa05040286a01d418100007404e10300041c000900303a00440015403007110140740342c013207103800414100c400c02e019203140380d0607194000602130864080c07221011440000003c007a0b030610416120b0580c00140c1c01401815900f0120700b4504060f2a584048071044813003004001801c1d02d01c014040e00d16001c04040e151075001c5140381d00d400010001c100109902c80d400003440c0b9001c09004d40600d01c0081060324000d80d20702e000d4640c4148442d48401c05802000600c05c500c2203800040311b40900004058603910040104100c01c280e007240d4026900e03122000b0259030f05560260740c04c0c454003540c130070110a8100f200308c1ea140c1d500c1205000b0303c1844800b000244801319400d2103c0e071840c030380003072034021944a00041e1125040c01400084816403011402a1518030100010303c1105940c45010b0f80300103040e808541d220001c14083c040205043c41581d5181c034503034001854003840108140d0181c02c6542c10880000146000035503081e0091000c40b1038414110072880c01d00c0100b2013103031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 977831591 1250 977830341 977830367
    0x2070c0e0615040308090405041502120109150305070e070c12110105010b0313030f0e0319020a080a080313050c0901180e03041202040e030f040b04030c080a03050d200d060501 77
    0x80420f0108100107161601100c603451400d40b80842c0c84d450301c0c6400480d212912542c04681c5001080c2c81145030041e040301c80c100c131003048060100d48500b8125001105072400080c0581d0000c0d007040c020130b4042c940060708070023389483d07010404281c44031055811380010b00d2001502c00e4158000c0c00c9000d01410380074100d500b40031407540c01c0018800040fa42101001002e00000c44040300c1c125002e00403d0494130400b4041c4c4000a40002c0002e11071600340380120300c900414600810003013030002d1303650003442e03101e181c140c0795485400100b00c8440110a0449281c80f540b1001c2040340c9500d20168000c244040d10071513171504071056202517424114a0050560050104100c0542c5655490882c19016a40054600d8100780b145056200302c0540c0c031448840003c0c0010340e1b41d9484024070449008220080a00351100100d640fa220a000d01400080d402e1024089180440d880040d0a0003030300125031646039289200802030304025405400c0b10713510002040b241d60425a240840c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 977832841 1250 977831591 977831629
    0x90510030312050f06190b041202041505060708130801020f0309010b0904030816020f0303040804080f01050c07120e1e03070f05030a110312040f032a060f0302070c0e06 74
    0x1600c0c2c0000404c0c60300100400180c401c07070f50601c58454849210f10510003030580320420707a40d140d45850401204c40c070029400c030b0080d85049040c14107540d20204a20940310014500d9180001540390b084c2c40740c003c05800215402940c01c001001d40c000d00c0145005c05906542e991280b07440480d80f401c51300e0912000d801907034000100400660300841499006541000c8d15107010a0000b0480c61b0920729100c00d820b6200004c01d00c0103101e100800b81040322000c208844403503601c5c62016090b1303507042c3c942d06000b107000d00c4074000140c5412800220000c923880d08028212a10001540c0b000c0081424103e1200040c82040c580c101404180041c10001c0c25101d42c0c64a00000b00e90707210051940500140e07401c40108a00d40c0c0c040c082c02d80c6c3c135003041c214681c5840c1c4604014602405610088801c099590002401e009081c03c240071045c560440c0c00782c0c107929101d01554802002501102050750801881c070008070040002c00140254201c11032591812000780b02c00b8103403000c1c0c00b0b42d00b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 977834091 1250 977832841 977832851
    0x1a07030b0405061c1205040e04080301080d140a0e0d06020703090f0609060c08161a270a030e031006241416020d1202030a09050402090102030906070c090510030312 72
    0x40c251482080880c1c03950121700041c00009005080341c490040703402c0141281080004d202c03d0003428400b8605a5a0301c00503a10303080c10610b410386d070000c1d8401d0641d1001d00244400c01000d401000012442c20010308480728188440e59484200e03130010303008901244000d0b42c10300080003981c542401901d01c50801c07882c01420420042c100c91000350000b00750310380000d20345201c540c000b0340c03c1c280c885d8404c00a2282c2c0114100942140404071150388103d2000b560148232012012440806510080060200c21074140c60440d0290380924243c0d400d44108000f00044000c1481014000c1140034905214a11840392600040405403401740030803001401c161034004450080314088428061080c1c2c5940c0310303202107840140348050180040705101030070001c454020005008010881d640c0c0246940c98008200490183da814240168814891031142d42042070080821900900400850954807c00a030645504444003212500c05000030400c0580106107880c0441c1441030600c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 977835341 1250 977834091 977834119
    0x2070b0a092006120907050a03150e01050c070602030a0b030303090109020325050607050114182b030c12020a030c080f04051c050c1b030c0415050d1a07030b040506 72
    0xc074011303001100e80c00744c08080031941d540400c020f4200188000351401c200350780d583c00e00811681c6c1c0704480d020000d0030080814000c41c03040c819584500280b0b843c00d070500b900d0703441c0c00c00250002080710140a90b24614074019507020000f45100344001000840c0f02441441418288100014200c1200c00d1030142020340000032070121040d10300a480540c3c8600c0c0078208980517095040f400000c10b40404144001d0700390319181130a0f80c000790700c21198020000c84800401c4507002c0010320101a0344451510b4503413080c0c200c09200c9980d0f00e07191071b0074205110590103e901c0750f04480c0100c0d503102c85040b449074000100035071205d0141412201445d00c1e440e81501c80c1c14900009001c14034844d5101c0c500350080068541508441007103075080041c0b8000080402040b07010a4400d100b0041ca4031b80e2403a090041e009140342c802d03649083c461805061150a540c401c4003120341c1d83c0540400702403180c4007000c00748101d06d95900070442501e028280720448001510240c01007110341c0440da = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 977836591 1250 977835341 977835349
    0x470607171b0601050f040905030717130b0a020606040510030b0a05100803030106090312091e0315020703120b0616030f3b011e0c021206060108150402070b0a0920 71
    0x28011742c2064602040d411451b14103e0704500c600d41000703111085c00c0c0343c201e103034400e440080c00f40c41d003100360402d041e41d464202000315030040710780b01070040c1e00c090001034150405403c0660440003950240c0c00542e102d076100e4114410886009001c01d13034035403c01080104094140300207180c810701540c55541442030044c02401140005001d5150741c00030350802c14031a00c05440101401c001c04418400303025140d0a4030001840b05403002103048055150452082c400c803444664103482e4903440c00f00b07440490000d0202c9a011030361021040c00664221060001c0e404405846030b568201a41d80e1040301404c0080c0c61348801c81c100b110051b07282680f20210030b2015150030321080144a410810004903020007010510f0b58420b0301c01e000c2124800e4011103508809807084070420b0498140540e03071603031008211626400242034402060508109405001c0c0106002e400503107810f0301501c03400381c5600151a0321004c3c0b0b5803060010203109000750300200e056049200c0701804001c002c006 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 977837841 1250 977836591 977836609
    0x90c090f0f150402030c070203010c050a1719050f07110d0f2f010e0714030703080703030e011407180806070e010c0510470607171b060105 61
    0x201244001c68004034000451812040011240c024400e66903850710107000e040607000020124081e41c2021848418503005009030389191000356503110a103a40d0111114050350f01522444412626004481c408803850144d0391043c10304d48070407000e2303050118004114450700041001c3e2500b281520600e02540324445d1030200c02d60b071400030144039160143c4540c81c3d00424030b0080d0721107900c403003903070020041d0000d03c01e00e020300d004c0c0c401c01d540e2181c1c042c264584904006034503411480003440003680343c0f40030744007140c080c0c5400694030102d0041d16084480804180d03088200c8801007207103181d40901d4144a01303003110381a1800524010501359a140003a00c0d0303105000402070390030140e03440740c003a4040440d0003504580f10780c1450642a00180751107440540301e0020325410306402e18a80724064194000240c1a1440d84119010071a108070395649959019008022800c0031925040c210300c42091031510082c0c0c2c9032040210480d10035400561000c107508034a0040006549181807 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 977839091 1250 977837841 977837851
    0x1002030306010f0e01020f0f0d0207061803170d1e05060f010f20100f051006080c160209070f0e03010603020d1101020a0804080a030906090311120c0d030206090c090f 73
    0x550f042802800040c0d040c00d502e5220010184940201100d2042002511504101c3c2c0d41e00be45100f552200000c44413807810900c24910040e40ca8402c100003482c079180c3c51205151508814205071480c92107a0541daa0b5505400300322480d030fa031811011506100396500090100c649440045600c0c002910108404001ea000c0c4101e1308a803803465100c0717800e4200407001500a030b40e2085071802d02070004001e44c41140c80d0343ca04e0640010401080c0386598405d9036442d45480d03200d591448094100f5501c64400400100301d200b40b90401a1a180c034050300400301d94030307a401211031481d0300500091b45030800600c603a04088042000d611680703c41d9031141c0e04401007044c2962070b400140e02e09402c00d0001841500c0c0020002252200450900d02407440703036403140d820035035a00301101d1407012400054400274201d450f40c0c002d4940608a0f041440c0d40000750b400000c20100000c0311007000045c01d5000da0488410031048500600c60019030560440380c880007400c26110700c80010000800c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 977840341 1250 977839091 977839097
    0x11b0e041d0d0302071208070921080f0d0b0406050f0402180a0339150309150f110304050c120c041503141f090204060f03111002030306010f 62
    0x200307403010350324004010803020740007004490041d40c00c0007004000398040c03a0b0035034010182c00c10a00d00b807403044860900034900765441c2c0420505290f81005012114882208042c0303400204e03100003288070020f4099040c124002948400c0108501c1c02540ca450a040c0e00ca00d00d440d606108543c0c42c00680d20301c40005603030050b20b0702000841d00c425595217191300e9905c0498241d0000401c168500c1c0c1c000100c40d40c4404440400295003c034900e00520022040401c2003003105111260044624200035076252401152280c0c0780d80b22500c200c0034240c010b100e0680c0300d001c20b21a40c180c030b025210088901480e49071840c507040c2c580e903807194000c40d0301d00d104d00d61006003000d26070310400015000342c100a000b04801108040c09014400c164442140d03013000e583c1e41480b000401080d011a82d500c1c503800624400110f849440042c4040d034401ca900c0f03595a5004240741d00c0e0401d0840c051442220300401c101c001d0400c02c40260000840030301103601c2013040203200c1c0d03841058108201c410342 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 977841591 1250 977840341 977840351
    0x3160305100920030a060e24040c03021513080d0306050307030b0103121106070c02011e0804030503070c05030d0f06170a0201031121220f1b0b1b011b0e04 68
    0x400068240034400c84080c2c1503070304040d542001031f080825016040e080b142c0c1001c00d1185921040401d0000848000e030000c2034120040016080049040011010303c1c540b4600d03000307004054201455003504804035a070f1141788081ca070f01d90144596006024110024036620345160740f21441602c050200600e41090415100313581800b906411400f054041c040d03807070340e180420f002002d400100805a0015000b002e501d003207444240071903500310030903940310842561035840540380703a0705c003420800c01c10041c4181c01010881c140054400000d6000011880b40d0b20102c2c0c8206490701ca8105001028160f184e0300800d120006e2080728040e82802c01040d81d02000d1982c05007030045821003880000d1115000e11001010300103144500704401c000d030349600c00840842c2141c481c002c8020130f5540070100c6100420304407007101c900f000440d117905c00040d841e280e02803150b402c145200720201c040c4020311b800390b0100780034807030303030390300b000454040d0300640c00d800405444280d07002d00c0c0074039a15 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 977842841 1250 977841591 977841653
    0x50f150f2802010209040c03060503030a270f0f08010e060a050c120c030f09030f0901053406050919030e150f0c0114070c0201050a020c031603051009 66
    0x80d00003601c0d46030998200c1e02001d1074034002038042c0d80145c400740e1140b4541002449040d00910840054910260055040128030401a16100301c0c040c01f100c000031032004036030b84c410581c0002e40c0180c59400250800d107480d02c40c480341c141178160840f19a90341014600d42d8134031000980705501c59810035000c1410b4882a1580502e807084070340c10407510760010200b08600d102100114042d000e060326400c0700f41d44900d0260384900031481c18101002040148060a40c440d102400c1d0404010310f01c0c10720340c903101520000343c44894008000080f401d024103400c1c03202701c0c400c3c10350092031600a4040042624240c1c260103030300200090500c440100814001d403183c807080403170003e009040d169a01564400c10304140c0119001002030740c20070f10740d00c0303401001d50070036030081032030b52035840c848041380d4010350b542d400a070004800c42c45845030100c40c541e8204013032104204004180d144d62411401d0050400c05041d11142d0003e003400001000910f003903080c1d05821030f1614143c21441c0c0341b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 977844091 1250 977842841 977842867
    0x181d0c0a171302100e0321030606090609040203010905090d0201020a020d050318011e0c030204031a06030f0106031b12020f041a0a170f12030112060209090f01050f150f 74
    0x1042c040e40141155040e1001940c10080d00c00c0001e2040703088400340000e641d002d00d030740034500085890052050020130440d0621502a002410005018071704001c02c150104d01240c10913400314440c50307101d000340b00c2140740500c400142e80707443d84000c1d03140600c56840a580d0340d003c200ba2401300100040015003100c624900110070303122036802401051a40389000c2003a4800307a07a95205289482c2c03140c2006030003031088a04503540014040002c00201d007000a08540040c1000c0c2c02d400780414501d1441070030f210340800386200c0c0d444e80801071044c6207100000007968000d40a00a0860003800c0560740d40c40002a40f118100d070003050910a030868400c0c40840920705c0d81d00454507041c041140b02500c6180c140350f40900007254400034580800a9403029407552298a0650400040c03101103e03905504010300d0142d80054500701b8101c1c0401c1c128502202d90204001c1d0002c010701091903e6000d48415103400c8510502c0c13094103106900c601d1062451078040d5407030004011007035501c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 977845341 1250 977844091 977844121
    0xe060f09150912070f120b0a0902030a020d06051f082a0d03050309010510060503010308091c14061006120f0608070e0f01061d060901181d0c0a17 64
    0x801038810840c56401541281d80d8040c1030250080030f0b4aa807001090900722084075503003107600402511070b1074688c0800e240c014a600003050303806004200002d4017507294030650380b0103540302e1100000c842ca0308441000050142d100c80b07031b038011405001081700100000311040ea5210759035519829040340c26016181c3c1079500842d45d000442002c1d00400d141d0480041d521900c20385000b07102ca42d8070400c15a09241c003070f0090f03c4c0450800c0c07005001141c2040c0240000e00030252540c000020100082e1074032109000048928844660198a4140050000d40e40088082c5034591b48030b41406000384c80c0c1c600c3c02c0700c8841e1040da640f10300e480d2541c0302d8001c00018002081560715940d154100340b10315200c1201c10910750074240000040032440741c03005640c40c14003140102c2d07020720814204a4180c3c0b05000c0d90741005141d40c4039031103558040300711200410045c4981510030b10007a0781080840d80c020b040790140d013800c2c8640f2070304030380020821500c5008100110368642e0b40c20b90f0320070041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 977846591 1250 977845341 977845357
    0x3030b1201050c07140105040c030b070c08030118140c030c0702040212012c040201050d0e1006090c030e120702102601031e0c06050903030705010207060c0e060f0915 73
    0x1600702801d0041c03c2400c5001804201d000e4804038410103900c102450070381e44180ca00a20041c8610410804a2110b21407503804c00c049192400e6150f510352540002500203030450f05c1c41d0f46140280390503080091040102108403046412920729141c0d140402c0360200400c903060303801d4001450400c5594660440e0102d17100b651240503103503140d030715070340c04001c2210419000b440607401c5c00d01c80702c1c0a1240c1500c42c3c0d038142c1d1103a00c0c0c40036407a01c071070240140c800300301c8003031007407803065135464685025440180010382000689800190305c001e0543d00802c48a031219000840c0f0030380c0400c2e200c02182c00c419010350721500a050507180c225410314283c514617034030b1086580c4801c3c0c80ca03030050303c1504a900460380ca0180c01070380c6d146108a41c4a401000340f022030700d0030b010000d80c0d001780081d101c1070200400b624100310558460a00366405030100715902036648070011006a041040a862048180d030f004c0d00309076014680481c00c0c81403c074031034800c2101e10801c200100c0c81e402118011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 977847841 1250 977846591 977846593
    0xe0406080102070c09180c050607020103060e04030f1d01050f0703180f090b040608060f1008070b0c100501180b0a120b040b0106051801180503010c1205101203030b12 73
    0x340f40508005091600c90300810102a05002800062180000018050301d0b00440c005003ca0718103010000c071607001d9103080341496205e1200140c43c02c0641907461040e40662222200401040c0009003145007044a990b02103900c40a4045241d83c0581aaa0b84d04c2e00d00302c1b42d50b915046802c05603400044001c804000c404604004074502285100d200308490045500f40440e1207518100000d645480c010110a51302c0300740058542c1c50200403641c0c0003001c0015091421b6101d4682508040c6180c014042c407000005102980207401c00042007040c0e1001010401ca5041800320800c4403441c4d8900580c0d651100c100c004030703990781c0554500a0000f420f00301c00d91b003090302d00128074041c103c400b0744500e1400340000500b28021821174050700c0e03e41c0300300301c0c1c107012a40c015101002c1010003200800c41071640405c2d161070900c100015035040e82c40e03155080c0c019003070320408d40d4030041160714081d8122108104000e0040000d2100c2d0b42c0c0360801040f035902000104184141c0c0446103051 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 977849091 1250 977847841 977847847
    0x20c0d0218090304240e0603190c020d02070e0103172203110102010b030d12090c031205030f07050c120a0513030c050a0509040503070f2f0a120309060e0406080102 72
    0x2c2e0003000801407085800c003031981509000144070038003050f0b001c11454000303c2e404c80d041c41850b240070401507500904140459410684080c68002103172030029800e4056030003085030340140d50f01000454010400ea46800b0b40b10340c15580c0d150007030344401e58a0014040c01043c0a8121101d14160f61200304400c000d070b41c0301541c3d074100310710340c408060880c1c1d000d5441c200d2250a10705010400c98904016600c90121260395034503074074000c0845034402c2d200075001550100019840e18070f02011141c8030760301d594490401c100c6401074400c02510a0060010400480d05a410301180c1a1400e044500d04e41e0345501034403400b074407548a0800b110807046841c3c04080108442d018411060743d2040c1c40120703059031200d0612403450301c140d90142031a030007802030301c0c002400c0030211003940cac0c4240c030210031011503404089481c074080c410212000c501d07862010701c541424901403005010340c1d0102e004030101a00d000d003208110f03028000c1000078007040d41740ca54880703800540003001401c000b10f603 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 977850341 1250 977849091 977849101
    0xf0c0b0c120108010506031b1810080c0102210306220c0f050a1e0203041e08060a090f020f03030c07091a0301110a0c02040f020a050a08060a06020c0d0218 68
    0xe940d0300c0080000e00d14610400049160641403091034480c0f074000d030080464800501c4092038040104120903840a95042d011070055145205c0e2405500318441d008c40203402e200c3c00c0c80c06d00b10140009030440d4080d618485c80c4000f5003003a0100811480d003032a6403921190701180e201a0100ca20791850784140c400c42015254590080f4014901580d1b2040c518810404c101e0b814850710400c0030006414807400c42040c0089100a070114049004580c54a40e8030b19120940060a007007034250304c00091410444444281b01c0faa81c00f080000041104000c00c0e582d4101e000c1051501a00910540c070083c48580c07820070032184814000c0084480c1c2c42e59a9580402400f01c0c80f6911058000341e1204402ca810140101c0320102c901200751803d06018000850703548822020036030b03005807242e0751103072068681d20043c141040340b03070782d101c3e0f17200d0786400041c082702405800c041c003915680c0410030030305a01044881d403884040b13450140f1541030340000384001e2005148040d04000761010f1003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 977851591 1250 977850341 977850361
    0x405060f0909010f18020c0f0f070602010501090c1b020103090501051302010207050603042f0d0f1e050c060c0102070803070f081e07030b010203120a020409200a0f0c0b 74
    0x40c00500322040d0310b5581c1c03603128080e2800c0c090302c0303162a4035880100c08000ba2446801900080c040350b81201e82a0b84c11441e4a881c2030310480c003005c001d410040c8240321b180e034280513440c050607404a05010303205964a0040c86c0c002c104822844040d07000b000310007168801d402181105401031300921082c2404010840c4840e10700700120701500c44c0e8080011207007040e1081d01d10503038010009040360f0008041a40c81d40003102d600700e00134060703c2050b02d2540d550341410030080d4001c1240b03507600e02071840c06080900b0901540751045a90100c80d0000031b00006c0e0ba1b4050040c2615066240e0310704c0d802850183c000c50100500c1c03e4001710400a81e01e40c040c1c0c0000a041b59580d940825817110802c0d003107014008818800d06040c0e0200040303c49000c0e40182e00c441d5030603c112490b1884401d0070084192059414070101a00003500b004587c14a0181c12120b000c1034003845880410352615101a100301c0c03808000703208103054044051402075400d1485550420414802407922542076 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 977852841 1250 977851591 977851597
    0x20c0c090c1306080118020a18030c061407020a03082203050607020105061009050405070c060f05060f010e060403060b0f090103050d1b030e012012070c060e0913080405060f 76
    0x800d6408000350000109244111349081c1241c2c00d0900c492801c41c0d001c105400070398001400001884409440e480f07054250740707410401180144400100c2904012004090002084d00b0809400c824400c080c0569200104001240d6211640503519401119801c801a59108481e101440e404000000348a008182d4074802c8915a00030450303075803070200f0030400b04544400b403400665010003d00260400d6403085401c00d2141c00c01c0c42c1d007021a41d8030442600c0c0c103d44038500858032001030100300d00b000a02012080400d003001d00444640c0d002003010f500961101804860319801c84040a45544418100210024000728025a102e0030001c0e07441c0840540000041c1c00980d40d14000c0a03040034130b010a540c180d0b02d40c000d8858903001180c1654100c086d65100c100821413242c1400020408000380d411154103031600c6865504002000f50701ca5070100d0240034084601189a070768111080350310115189a101c000501820001081d000e00c0c0c04ca16000030000640d00300c054207034006 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 977854091 1250 977852841 977852857
    0xd0204090b01020d05180d020907021c3219020703121b020609210a26121008030304061a0d11010c02030f010603111e060d020c0c090c 59
    0x20301c000000c441c012a0748010002500001500a00c820850b00003000c1c0500c0c030502d801880952619200d4001482c0642d0986201c0056404013400410261001352146404203035410090703414510365240c0c45803022082c502c01100c1407090f070090003106940090701c00b03c003040400a40c1d180041c14000e59a55054013041d2000d90030100c427000850b204564070352040c00030000c0d40b0b0203642c0c07039402d01219411603e5104e0703014842440c40c0c01070200706131020214112510052002c00300d58100800500051000c0355280c0015018442195008000b200c00c0d021000c0c80d410070f20b507111070304c09401740003603000001c1501000081c00240012504420606068401c9103209251103000700105102c000310000c1c450014030242c0c003940e601031504c0c0c56045d0f001509847c07400c884e211455007120b1107030f0412191850424481d45150511405801c0d441d111000c400c0c0015400c0d000080b0140150b941001f401c940024280b409002c00f0303c1109583c0501400b6181107003020f100c0340710190001ca00c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 977855341 1250 977854091 977854109
    0x140613141f123207150c02090408180418031b080f030612011407210e0a110603090601180f0c0f140f25050a05060717040203030d0e010605060d0204 65
    0x81800107440c5903003c405a071003034a40241007042c070705804204140120320b1031406101a0620310b41c09030701c81c00c040c188554490071086603205540d0f40a0899542100e110034001c500c0c1843c500e401c13a20715204203815503010b00b030005084180c610141400120900010841c4c800803c0101c1c0b603000e200d0145000d92002c0303030481c0344420502c0d0f02038226402c49404800008401d00032410780c070300880380c880760310034000360a111050408030300c10203a46041040320140e41c003800241c0d0a20009a4158412001c00c5032030918500b0407440b401d035684410b008540c100407000c003480100303400990081da0b0280700b80c4010b001e001c0303e002d8051f01c074541808170000400e00c01d110702c0b040302003030714104d0f2000720803211000d0804401d11912014000c0d4044040a2000300d00203103004546c00300710f1081914400c0004010703914001c00000c2c8504d0701409907400340203400c010312005035404004d440c0c00c2e09001400150020320880d030103006d0b06a95010303c1d0098800508200070107256002030043c1c2d03061032 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 977856591 1250 977855341 977855393
    0x405010c080408070b0621100b09010f0303210c11070e270705041103040c23040c12151a030c091e04140613141f12 51
    0x1a030076901c40000b140d00510b074803000c101d0f0b800050750f120b000303c0d0810405000c4086181c02501640038030090054500c649034400d040240300000180540030f00c080c0c05882440c10341d403401103180708582d01e0780002002e01003810800c0250345040c030400d61002c0c25400b410b000034192042c0241080c5100000c0c800c050044038404140c00341e400c0e400038002c840114075100c3d5040e941c101580344001c13103d004d415a0188100008042e80c071401003022013242d40c2c64681e40d038241440c08800c404041d0340714400260300d01740442c034003509102003980c003030300180c80101d030340840411300f1a05003242107100100c1d28900007100340c559860030480c1058805100ea9021503174000400c00074103000c12a5001103c80301005006e009081c002601d905106e585c40e01d42d0f214090102c001020b07a950603501c0c1c55070342010401c21030180b03044200ba1b132141e07944407401c010400a034200038005140040a107180700c0141c6403250b04580704804007000409040d00c55454195503072820106202c0c15080c42401c15002c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 977857841 1250 977856591 977856611
    0x120c111e040e010911010e0d06020c010209100903120e0d020a060305011a0702030a0f0302070803280c020306010b03060613080f070f0e041203060e04051005070302130302090a0e1203040501 83
    0x52280d9141203400c280c100300c2000785200110f651f9039542040a41210200498100141c80c0703002030801c4c010305c8c10015031101040c40c01c2c0704001c1040e0200c0d00810013024400c001203582c02c620950071682c0c501d0004000c2e02d03400045100075114850003500500380580c00110341b030341640300794180c40d2201c106115171540581d5207811405416000380d4507400840c0e0b00c2000030041012520a98440e005a81596a0300d05e03101e1b0854111a25482c011030707182d2a480000107141d8000e00418450f0b0a145800e54656000701c0d942c1e480500840d17900140000c081368440e698102521501460182034042540d150304855031600d00c1703615411450300c120340c030100708099807110002c00c2c0d48240d1004407041d030b1103445211104007124210720070f141d5180004246007407002c0310355104a01910092203003c91400c18281102e100070515420184184010110002080e05240c100c980440e030315510780d202d580020f001000d50aa4090b5580b02d456100341750102c02d1005144924010740013009101c0007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 977859091 1250 977857841 977857843
    0x320090106030614040b030a0c0305060708060d030f08060310020a030b041107051b060706090b060a0614070206070507210b07081b1b030a020f010612120c111e040e 72
    0x45402000d0544c0c00c401d5210103e0308042c0d00007003401c00001c086131120029525000c0303002031b6039001038680d07401582c10040002e402405558000300140e071035042030041a00c1c002c003880c00c41c088410800c4910300c042401c60760100075040144404910441d510345422601030000c100c0e00c1411401542800d0002250408140a841d4516000030140100c02c25a0001c220110840050a5070050090003002c001c070341144904c0b017140c3e105541070456030501d0f808003c66000da59218108209809104030b081f500c0d004195024a80c6c10344265465281d1460040e0804c0f4054000601400260160100450f48500b0016041d8010b207200f4415484010302101c00040842d80d0449412617940f64001c81001000101045104d0b060400310701c141d41455a420355000f03040a07401a4840c20045000d02c1c000c0c03080c031004100302014660700e03c01039a2032200e4800030b03104840030f210705081d051052124108046619601c0113109040e240c0344642010400c61141402d00d000e140b03855100704034088 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 977860341 1250 977859091 977859101
    0x12010608120702010f05160b040c05040513380f01061d09180f0a030206070215160804170412120c0b010302040e03040815041218090b0406032009010603 67
    0x24040c2c1d5510848140e1103020396840e4807001f001000792000061003004241551003690180d445004e19641c03651030320040106a80014003100c03200e009110505000840103450b2607021441c12801d0349007101e850b00041030172900108255000c1c0114000c01080030b45800074603050380e06c035440d00610071130180c080034222422484541c0c2c0010145001c0381100501400c0b21b0b801c0240c1c00708580d02502802c01041c10020150030817800750388264103000810790148a10101080c451203104185c1c0f03000d445110784415042c200c84242b0203850b01180074040b41400b441000e074101d04c003a0707030b84558402c0546140b4103001001da40100740030b01e456051a2007051803090b982e41090007400282d00355000c200050101948020461000704800155050b0038001c2100181074001c1200381490241800c0703040038007410041c1c0411400a030f03030f8940e5402580d1042d0030346a1002001840821020200d801080240c1018214060a40094040600d005400c00d0514010750301c00042e40d83e50101075040e14 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 977861591 1250 977860341 977860343
    0xf05041713090f090f1a0903090102060606070c0509010f0306140f0403200d09030c0617160c1e0507050405130f02060d060314010b3705120106081207 66
    0x4242031010002d4108540144a40b1800b1010010740d0741050354940c0c1d00140d5580c8202c0700c0e0000c100701610007014007000030782d0014000018510b0407000c1c100013500c1303070f000800b060300ca118003103501c0c404e018484800700045c150140030080d09507100d02940301220058401145d003941400e24040c41c6800895500d40502e07100307403800380c00e5241c0d40d405035540f01c220b04445e40b5000e02c00003802260003042240100441c22038441d910301034150b042809095165070010030501c034080381c01203064100c0d5090030f64050b2030700c2c000d5140c00064070000c40d803040300c1d044041d0481502c4081c074036446841e05414000b4520440c2211191640c1e04c080c001503c0040f5100850704a00f812104046182c107000842d21a10040101e480e02000984a10032508103800c1034035001d800d00040303064a0002d109490101c50203ca203c00000f60700750390181180035481c800c082e40056101c40103002d104601c581720142400600f248100741c507101046000340310720301c61102e0520480e0712803800d61129600701c4402e9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 977862841 1250 977861591 977861617
    0xd03170a1505121c050417010b031e01020f030c0306010f02010501030803180312010f0e07030501120204020d0b0414092404260406020303041a280902040f050417 71
    0x706142c4001c100c030701d040408010303609004600d44a16640c0c80041a03c0e140d003100d48606803220b060945010309030300000c410070ba49a14204140b001603a0010300100038141d01d03000d03000c600d8001c90455000e401803141001402c5004000d00c5020650301026500c190070030390b00d00381c1d40d00e006102242a01d80a11001d0080c80e000c00108040015a0b43c401d950b02d04048101c030700d440d5121060a86800d402d911001c1e070741500080502408280c0011142c110503a4607050155506100c03c00e1540c801c00d003c000e12983e03001418000e044c6054004001d412401401000490002d1003071920410301100c00950502802d1600c03000b0080e017070540c1c0003201c60048102c10790360310b40d0354075400b8160003000000c41c01e4650b01003070b560082e000300a02c042d10a03276001d141c0b0790a003881d003180d200320341c8805002c10b20355400400036601c9900303002210b101c010030070180c18007058041a1008052190000c1d4016040c080302201141e26604518007075807281c08404004504400018403a000d403e40740110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 977864091 1250 977862841 977862881
    0x5070b0a0e0405071e05040e1303081b04060e040605061c0608121c06080d0228051b010e0d06050f0112200f2e2118020d03170a 56
    0x2e0a80000d84055584480f1b050942c80d2075124440c101d0542001c66440316414005210741041642c459181038000007032440c0400d140440100144a81c059800307140c04010040301c6070100c0d9941e5800182c010035000c1d04d0155602092003a030640c1e010104003402281c0d00b00307900018540c500040c14050541842007641c10055441d001540e00e18001e0300c141c410035103401e07000c40d00c02000e02441c0a00840e5400803c1090490f400d80500b030811103030203048860049020402181c0d0205107a101903462642040722030041c44016151400311104060300800b00485c400100709440e400760707004404044040d0311582e40c40c41c13030005200d80c5d03140042801e48509140401050700014151460000416102d691001c00000c81c202000e003040c0c0710000e0510303076518454481d50840c185016112888e042c400051051003200300a0002c401080c92113a5804a1500200c20303024148015540141080c0d601c5055040003080d402e0385442244200c0b4516010420400c254454010020380011403068 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 977865341 1250 977864091 977864117
    0x10050904080f0a020d1b020603070305041505011403010f060605090607111c020108060a0b0316020708070b1c02030609040f02011b140d03020414060a090305070b0a0e040507 76
    0x106a900904122181c510500285031072031012405020f40c6003095000307202654080310003d0101c50003072492a2035180c0e1002c154056143c507400c99901c403555050100301e585551510103110030340c50080c48001c61401001094225140210a0f0b010310304800900104847e040c442e0116030311031013104003207a001c101c3e9070390130b0030140040d022043c0991f40c9402c49454240100301c0d012140a0b120200c0504d1081c400115170308818080e0b0880380980780c603c0214103220b1018454440580140039100032060f007a0700c0c05100f00440c0005d0403540041c1e6031143e81c0d54046640079003054a000070943c035100762940303000d2001d2080d24400e0100820f10b41d46500d032600e03240c10441c01103106a04000d0107400e1a090f410b0013110000000b440f0f80c06000f40c0e54003020b0018200200328490704101401082704100c2d00b031003114001180c041c102d8450381d07500400307082643d2038003e83d0b01c000c002d4001c42034009840c004010140c0122600340d22000c982601200c104421244100c1d0307036070b001c201d851120070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 977866591 1250 977865341 977865349
    0x11030c04030303090807050d05030a05090c03100515060d1a06070c090b01140c07030507060c02061b0c0d031116030308040b041704080c15040321093b1005 68
    0x1c84c0050003000789610b0000c0d02e031500c6003040c900c0c6a142c4041034000013440703c82d051620034554014044400b900000b407100d00001d40b190900145020455110380105424101944a18500690007018596541007240b14100900070303840501ca550300701d02d9006480d82c2085411580980e078464950100181041d842c01e0040520724891410082010316580c00c01c0080401840c3c4c1c1c540084c01000d581c0e20314030300b0518000c031903001a410801b0904c00800180c9811058801013020440042c0000c1c0420b241d407450b051546001c85d0b03010064415100c01d05410613008030904007071a040ea00400c00e500170400ba80d540728800200060203a81c00100803844c000010f64019100c0c6030301583c261421142c0d10440d400c540c0056400e9040000540701c18035164028400351f0001c000b0300b40c200380c40c41d22a11900300305403103241c02104003440c180746c0b064481c1080d01c0c0500821824426a80400702072840050441e02859044107090380d089800740c180f03110014401c042a030340c40300265040c0004c0c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 977867841 1250 977866591 977866601
    0x60a03031404050a17010c1404030f020409020603070801060201051e040b10180e1006080717031c09050d0c0c0b0f0706020409150b0f0d1e060b09030111030c04030303 73
    0x210407504040c0404a03150b074075118071034000c0002180088860b42181001030031200c00003411010700c03155801c14012420030b00240d40840760084959240d030a103d00100780504542a0000c0d40a0000000c204900b03400c640074a040e602682d00802580c2e84513141d911080b240000107501c0d42000c0d82c001130000c0d070300400035a480740e814600e09111945c1d0b80c4400358070406071b410500d403180d120700103005014000c100300900400c08107000e1059528058150740c4038180d40c0590410402c60510703440012604204a0f420411030070b40c03100039105030700640750041001080858050150700242d01c40c00b44600e405008091b004070603c070645140c8170031040c49912005001a51150900c218000300b600303440604001c201020f4085810129510714184000558000c0c49000105000c1c00d25031413040341c15120380c620541000103041e008002c520304070b1300300c10303541c1c089145c1028030115008101c2c4000c1d1a5500c0140c00901ca02ca451040401c55400101c4060b90071308010312040020034441e4000c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 977869091 1250 977867841 977867867
    0x40b13020d12080717010b300c07062a0f18032d030c020d030507061505121908070303140f070f030501050105031314030c0109050105010509060a0303 66
    0x8911007481d079603650399082480a00302c03404103050400f04000140c0213050500c610400009600d2a076052241d5030f0418010441c03601c0c02003145004100310085010010031141070512100d00c0c01381342c0202ca5080740d61024500300c83c45410600f4000310002c03501d2241514003015890124520038801c2c0442e03000f101c090700326003080100c1807440040266801c240740a1350060050201081c2510a005e2070900d07100c04501c3d0a004408214000c65841001443e2643c0d040f03420102408003070404490500611034082c00c510b24250700031441034020060700c0100d410076210520759918458615442da0401c128030f1030301514082c5100001008e0f1b13002010310a01c42c2c01c000424403001d500c001003030798045581251507000701041c412959003000d2181c1c540800c9240a015a43c1080d0000f080e500014007070a030210148500c0c001000300074984144d0400b8481c040b03a4507014446403150103010142d0064a0075444d050010819081051009100d8000500000c50729840e59074211180c0790b0300303c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 977870341 1250 977869091 977869099
    0x91504050c041a0c0c03070e360a020405062d061908040c090c050f030712020a170f090d0f17181501050a1511010203041406010e040b1302 61
    0x80040307864240c0f00b2001c00c02c1d8000c00759680d00c41180c3c5000900c0e0401e02d40d07126120360300090040100102d4019441e5209a945034070b01001d80d0740242070a501c8440405031700500c0c0340d19400110a00d00094100c110341e000f110240311a458900c14045062811401000e244d19128030000d450030046c085054401e1010b4842864120341703810001d900c40c0d150b58000c00144900040c482808801455503019180c249030070080c01085280c0505284141e1481d00c1108001000041d800c038064160340c24011406102595501c4141b0310040110340c496240701311241c5c1c4d000105908221a0004910640140300185200c144410702512840400d03083d60007040481241025003080212000f401f81d1140b10854803160002c0300482d04040810340303056040880301c001007113182d40d0120b00f0720844031031302d000048904c3c2a0900b01d41c62080000720b214103600000c2884208290650282c00a03411102903ca20f0390320f900a5001c0c9800688019006000d0000802c074031010034080d445045100030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 977871591 1250 977870341 977870347
    0x9030c020409050c010906021b01030903020307170c010c05040f061b150f05060108070c1b0e0f060a081f020d1d010902040c020c18041b030818091504050c 68
    0x50300250070781e110040110358a800c0714003924102d50704401e00c0d802501090002d0803046000807211564803a0001a160406485074091010305000740b088901685d0000c0c030400d8440b00f440b001408540c0080101803141d1300e4603840b142c045101d14180c40c183c6100c20034805685240ca0701c105c0c0e001103814900b0b140c200c0796600c2c40c8001150621078130724040741440f010035018003003054042100d0008107003605011a580400c10255071104607117584030b5009440b10003243d942d0300074601d006601e412800c1038614510a100742d421010341c910b4445d02080751113003849038458001035101d02c00c20b83c80102c0e441108808a03c6007403a40c01038010910b000b100003e10704010001c1e005417100511400c2d0042c2d542d008440150b0906000f07140400c1200e000800010104101050040d00c0d080d13068076094a1040205040240c2000010541029091100806a124201084194860700d820722810785628080c400c1c40c1044101c107403140140c01d0000101118a4040c40064140240b008031440420 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 977872841 1250 977871591 977871593
    0x6050f07060e0715020c101d2107080c03070801060e0c0a0e0d03030506120601050a0b030c0c01091b06020105010b03070c02151c0e010608030702010507061e020304050c15040909030c 80
    0x2502404141d0715802411425403c601f803140c400d0850b8040307002c1004140d0070f400b045010002c0d1920058041d41c03e00042010f2a42030742070030b03a44078101d501c81c0c00f0303d02c40040c0c052400626908140c4c030440580d00301a07070781d22559080707034220b00c980c6031418402800110a6000c0c074000d04250620b41c01c0c080d00180d0a01c0015240e0061582c2c1140426078030070610a03141480392008502c1c0b2101801001c84d03505000020342030700724900ca0920680000400030f880d106440007561100d60091009200040c031a250645003500c2069040e1842d81d4410300028242e032050096a0480d258501903031700c0e584415608031036034a80c078034050340c00003e0740700303c540305440c2103000700710210700880413030314290440028500b0380d990380f2108121a818550309004516000c000c407019554242801c559550b400d240c400f02600b5500203c2650480c109260144603070103400444c880d501c500d0658207444104410002c101071205038005042c8428801813020320181ea100485d494020304014000801ea = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 977874091 1250 977872841 977872859
    0x8130506040f110402030a0c08130b060d03120c05190801030c060804142b02060603071707030b01030b0421090e0c0c010e0304151b0b0402150a0c0c06050f07060e07 72
    0x819103c650106e0340d039030703050841d066001d40527942016001c00711604030310705922400e400300c0c03000e4001031040c0c0c84540950b0405000300007034030740d8202c0003800740200440b005010303046030000c02c600b81c80110f1312a0005072613846444400d040e00c0d07021420513070803810a1012580808001c0c401c48001e6281c422120035100c0030800d4075000d0050b403d00c09040d9491b903a110000070100720110b8107652000c0d0034804c0070380d00896140c040d260701d500f8400c03403090200c8590740703009200d5201402c80ea52003000482800b0305c0c41c50140c407844c0142041d40c1041240c034503c40040c0509000c110004010100a2108000f00e24903039030402204046142021501c83c400781c04c569946003800010313480010200284e01c04101038907058005410550203009041c4500740724405003030001403420030600c00103000c40d91344004200c0c1004080c0a1540c0319101d07440c0291519510601c2a03a13084588140016040d2041c0110780c1c50180c00c2d10340600f0106180d8a44015000c6080b55128600509402080a0103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 977875341 1250 977874091 977874097
    0xa0e07300c11031308070603021c1109090a0504030810050f01030e0c0a0b0405030609011407050904060e0a230603030702010c050f0d050a0e04020a05040513140903040608130506040f110402 83
    0x200510001d60742919040d071075840c0c2001b0740c0c0b0007400c0c0b41c010f00c107450381b855228203244a080b211a40119514081c40415990780c444c400d0360561203028a010b0150b101c209074401880395100751213050058031006106051141588259580b1605030311324208a0b510a401c007490042401c0100c9607444600c000160200d8043e800180e400080802c041056160400910ba041104813000300061524403100e5000c02e00000d1150040c48800203081d9401e40340d40e440840102440040b1503071741c4c144001004003600e0642c0069520003484041c015044601580043c05110010020743c13400c00c45900558136103500210544807030164440300c8038520310a00a8070704010480e9a015500d04101101800001511180c580180d10620a600031103800000f04c07800e03610b044a5000c039020b104030b0400054001000708108a030381d80400c0c005544400805041038403419200c0504079070799240c0c4907450109800000d000341e4002004200031401e07281c4410f5040b40a0410310354400420f0000c141a64 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 977876591 1250 977875341 977875357
    0x81f151101050c0c06150307031704030512090102010c030501060e0f03010902090c070201080a05072c03160906080109170c0709091b062d0e0a0e07300c1103 69
    0x3c2400660200f04a00611115500c5113034001021004002a40400e40d1180c00d400000c113080b04031101d61400d0401030701550f00450744503045031003440b4008400da0300c0d41c0010b64a2400b40d0700b064061050349010303004490507100d041c0c1d50f101c61140c1e440100111500304e502d00a405550b101c0c00000940c80c1c107038030340c0d109042d0380d1241035580e030462000404240004080c5a0350384c1c503040a120003507a00c4021080000e00e80748440502200c84080d0300200c0a40070030069040c4035441c4034a504a9880c00c0c3d4a0886912190400400303660781592801e80780780010041c030124442d09940d0110200c0000f5082400350b030f10403503208545030141007044a600d994251040e228282c59138480070302909501300501400e00d82400395150500d458440c4010b801d07038000d0030b41c034013040442003a0f10452034000204402015110b009940e5004505101c0b000d0303c00b003001458513403083d20030640c8240e00c011401003541185400011030300c6460010a000103000c01000701e5103250b03601c10202000a00024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 977877697 1106 977876591 977876611
    0xd1d040203160801290d0b030a03081f061e020a02060409320403080601021f050108010c020a052505210d0e0612090f01090c06081f15110105 62
    0x1d0120300742c1c441d030540309c1ea0754190700380750b0b1000100d80212200c0407035044541e400b038801e801e10642c41c040d00010078604035000d500d5516020702080c5071140f03441074403c801034660000d00d496100c1da12500703403030762954802420701103d89400e210084d00e0380c1b4100003900710f90a0059400b03c008001809010700305000a059900901442c450304507140c3c0e0840c51644195100c00c001c013000e028400f000d41c0b811380300807040341c000100480e1464001c002018440d05940c00c0d0f49103c4c4580360103222081d0b00d504001020b4480c521040940000d520b142680e50a008202502e009076840c1e555040100300e040c40a555254082110405007509100700d000740c2d203511034149000c00601c05010658078000b9008107001c0e00d21072160550b101350352000119101c40e01c1c4007055001c1310784c1280c1178038a221400c020360f080c868940082c3c0c102506203100341600d45103449003125001c503115402 = true := by decide +kernel

theorem cover : BRFrame.Cov 977697841 977877697 := by
  have h0 := BRFrame.cov_init 977697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 977697841 ≤ n) (h2 : n < 977877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
