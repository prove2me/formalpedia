-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2165
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:50:58.630912+00:00
-- url     : https://prove2.me/submissions/be3ad1aa-c7ed-44b0-a97c-1e0762a8422b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 389208633 ≤ n < 389388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 389209883 1250 389208633 389208637
    0x41407030804060f020114040507150e15070201030b010e010806041d060403111002120109020f0d060807080d030e1c02030d0e0304090b06030709030b1f09020c0606030703081903020d020706290f040b06 88
    0x3420f40c0000701c0c0040c0308041d103a6370000d4080940300b66000d0145480c80801101c001d80c907405694085142203020402030f103000d402144050300c03158030700340c0d61140442456103850340554080d00491040000c07094103d41c140150f0510119900065240180c4850040c804035014401c0e465020750128903900400040e400f00c401005480206102341c5441d20502d980361003592054000e544a41c0b103000120381d0081c0a4800701d0020400a0040c0d40c04c504102c042e0f604031040c8000444c0400c220311001d1031003038800c4502c0594008000c1d81c460341407c05260880780412082440741d10140204400c0c103034086494010fa0341c1c0040c6150068654081c0030718a904a81400d05008040b41e00101c1d04820540c080c0c0b5013820200700304d4809842d02c0084c03544a41003400082e00740c5d0030400c0890f209903290b41210380450f0003071400516046402c500036080360416101110b20b10f46403030345502030f40d41c04c0c000800f10508a524900910150381e0025442c8000c2034030b924007030764031104444420380d69001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 389211133 1250 389209883 389209907
    0x3020f040909060506010807030b1c030509030d090f1212030906020f270409050d05071e030c05122b0e1e07081203041407030804060f02011404050715 66
    0xb400141d02c0780c80d24402611040325558000348000c400502c4941c0f2900540b80609806042d070005450072404001c2e01040101058081c400e080001da03606460030825441c03140d101e5500e0103c002c1c2002c41401c00c00845602c9440441260421900424581c11b03c600100080d0300b000203589401d483d00c200030f4050022880c00610740440c541c00f46100d00c1c2c0301d46c140801c106180040d40e030506070801c0100e52120001403c0b65000000c0e0b8100503002d40000c10034240905071854000d0b0001e00e1120a40e0b84252048000405144d4003504210040051036800c0340c9068210f42003485801d4901c0483c181130384188600c41c85281c0f03e10320070315143e200000f44410300d019138424409140b61107811034003d44880000b1b100703220000602007808294582c075545031307420355032841d144d80d101d0071001c2994000d900d41c1e502418100000082007000240001c1c1850b07280e1150250a0071006400c55103035031b0b0060040d600710700030400020404241201999070344041d000c140d94107000d0481d00c180c0d0b462 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 389212383 1250 389211133 389211149
    0xd20011404060e032109060d06030203100f150503120a030e0f03090a15201009050c0f01180e1f12020f010201090c0e0c0d15050102070b0f070303020f04 67
    0x20007140729030f8442d04100d4545410350448420750f20301d0f02e20441100d550005140e81d05000d1081c604140780c0040100500320a448002ca907094032a00001c1c244020301c40b0324180c09075140000e15003c0c6a80c02025010032070078903298811454400441e8580c0c0d140c00f1664020034000072a40c0b4820300a07849880d205003501c0c1241c0500b4505001c059882c0d00000f445407142c01406000100b54400c043d1b100c28681e01980c580184400100c1c45940130b0107070380e2181d01c9901131880c402d8507841c000d20822034007030301a41c0200b540b02c3c442d0041c031081244127032090b4100b000d039184001036408400302c180110b5080c0c000c0c0c10070550f6113203428803448140d0f504041020702c030a080020b103210041d5003075840500803502d01c02d081c044880123908940700b500e40241503820b5400100172a00360204040e52190f07092503054a8680b826881c0c004589a680411499021014043c082c65070b0400a140c00391071840700382854100d0000c0480300502445000074209a000110107445460b20400d58005214507 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 389213633 1250 389212383 389212387
    0x1403060121150b03060603030403080a180e070905010813030e0906041805030406080f160e01050c0307030302030a05090f1c26041103030310090e0312090604050c0d200114 75
    0x2c0c81044003d82064107026210784600130114946140c080300300c07806ca0ba803059441d89040c1c101142650740c4500440441107a54a0350000108240b418040e28800c031220783c0e540d030405041000141202c2e10240814018601d5100d1501c006034102c1049070140c4001c4076524103d945290000f405440f03041c184a02e100c942c02e002d28101312000002d0070941e00180c0b500102c07a5a01c01c44480d140400700c2d070070410740203094110801301d40501180c9800413810314142e2f203480d5003001a0f629503403260704d003100041d9002040000440040c401c0076044282d81001d80900035004540950302c14014200c1e8a0210400000140b21802000d000b02e40c10104c12000800804914030b2500745402214242c80c1c00404201c2010740d031a0200c02c0b01c0c03044075401880007501e410052804002c00003200102d00314441002142c12801a11000912131000071000f012540340c140350140c1440108440381d800785010301038050024003103407460140c1d07190b2446c012a2070100f0703000489040010104000100f000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 389214883 1250 389213633 389213663
    0x20d050601030302011103071e1218110f060301170c0406060807030b01030903050d0e0705030f010209120c1305061804030203090315100e25030906061403060121 71
    0x808162241240c0c043e4000b0411034001c0102202c0c070303120450394480041c21111284d18542900d595503805050545001800010303050b088404a488051251001000400100c0c0070001d0880b00c107012604240c840c0d0b14031702d032118081140b40c001801000c95000074010700800e000c070100202c00401c1e00040c024040072740d803007030702a041005c00c4c0c8008000a09141c404111035000c0e002e244100d0381e240d540c0c6480c101010440c10000c1009141c2c1400c98000c000000800d0754007000f0602410210000060f41c80e4044010801aa107003014500c0c03460300a0b0503c2e00b02c90355000a082d411300f010740c1e40030585607981000280c148040302098a40b14100d04240420b142d80000500780e2804c041e01150302d00003c0140005401c942111804c00646282000b407041548c01007110781c015241d920320921004000300c2e03241600e14856020b000007541c0700600e0061045900820780100311498100264103146ca001c203480b600140240d04080c40c50801c4541c02010151010000c0c6030040707040710400f04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 389216133 1250 389214883 389214893
    0x21e0a0305060103180201090312030906050f060a0f060516030504050415150507020f0609150304060e010c0f170403020c04020f0714030a02030d0903050409060b09150f0406051303020d 81
    0x1520312034002490006200101c050400005c5880d0350142c4036070f070300c061440e9140003404810a00f44d00070540c5800c03000b0001809401a40e00aa01c000400c04282ca45038081c010454080c0d0300c01620006203c4c0700704025074101046a462030014820f00c4002c029600301603030144102d0303004030b400070b24201c003a000e141042c1d42003e0548220300640c0d843c410360000100d0307c2d4041c40101075444000086c9003100d901e441d0b002441d0540e0041c0092a646029942e042d9640d0404caa041c1c5941d82c40d9602590005000c0c810b0990150341030030014011007188400802078529245044000c80040e800702d030134117000700302c44940310000070030956480314202010034035a008038138100e030484c404014080080700301200303454401c2029030055060103002d81807540030b00000f180560901004110114500266002d2138010784940c0b2401d641d1000d01000f0b02017100c01840d0800407011051200b0140c0c0308100080b50221010b81c81c150380c9403d1192030f000700400307440d800290b00940744240d2104000b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 389217383 1250 389216133 389216141
    0x120c0c120c0a02010e0328060f0507110f011b18050307060306080606090103240b030d0933030e0c06070c2c0a11070506180f030f0a03021e0a03 63
    0x152007170340e034001105d21a000f0715030750b400b4110f000d4101d9400d540b00c84c82c20004035802c0f4a45280038000c0451035400e070340b183c241103900c1030b00c003880005c40420060742d40c0d0f0340400c0700c400704502c4280204030134070a004920010b820b94500402c20480702c50343e0504610391408690016100c001c0507203150781d03510340020f0010206032040103c0d0b03014050000b0b080345003882c0726504882d0450401c0400c0c00766030070080c440c014000403200702e2950b2585c042440e42c408001801d44520b540e21018665400c0036400700714504070050489103074001803007005900e41440310b081c140011606022444440d503015107400c00490744407081c0c2203440403903500141311040304001c04586d007248980900604000302ea0b40c4103c001e60600758210484000701d642510b8950140502000d610360003400e0014665a40c1d0a01c07400fa81d910601440c0c400503000f0200050290f6400d100402e40290b18102000c44580b006015aa107103405065000c0750100b0001d88203183c201000d202040f00c03998820b02e50f0400350044c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 389218633 1250 389217383 389217403
    0x424060306060207080303220c1217191b020d05060f0106020a030e01050d110c0a060b04180b04050a020303031e06010311160c0807030c03050d05120c0c120c 69
    0xa06184000803001c0c0042139035400c0d43c000700c2c040e5195940f82c0b0a521f030928850b0038146640801074000d0360103c0d0f548039569001c1d1990b21021001058141040584000480314900c1c0400c1c0030041210715203650140740150515034148085041c0e9648140c0303903440039820010350440482e00900c810860080340d00d40c0f1820b80c41200d40f40c0d03642c841c02c0490351070001550060119078000c80c50081d56000700c012f0b00e4000091000440e80e10310011a039560348c0c1000c1d9160000d60b00190698080041a0180300c405042c1a541000801041a11624030030f030b5458020706a50003680104040c090b052018821441d00901101c1c2d0700e040640711072a00c01d00c20583e04412408a01c00f045031588070380105007441060310016401c0480104054204410f08d840407200072a60728000a0001010301400005502508414558600d181007690401604200101c2084010403081a14448141c0c103660080203080b40c03243c45c4c8400c110090b00e000e51030400f9410425000c21a000310080000b21041c0f4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 389219883 1250 389218633 389218637
    0x20613080312150d06020705010f0618050c0a12111e120105030a0201050706023105031501030c0323030706061d07020309060904110a0305061807020c060306042406 72
    0xd03075610041e00d0701c3d0103800d9054503440409440c8807804079500380c000e029034030301030400018503400110848003100d0056205a20310f00c44001b016035080b007548603899000645c100c906203480244040140b98400c1083e000c0d004c00c5e661b0420403020104001501c1a0f4040030358000103c1c4860741190542d90003000b4401c2202940f000003140f10308001c12003582d070303d5068590a0501c0000d176a2000a50481840340c1e800d07418040d000e4000031028801e0a841811201015441d103007404181420b00c81002d80c0000d52644110041001500400d0030008803a0419a10900d0607041804024801c0a0304080c101510010030264140032050340074030110303195a100c2c07641856010040c490051000c0b505000981c0040c4005400c50030040c00a0100d29001003000500354904e901210082c0c20403202c420000b5512070030802d450911410003a0310712840ea407118441d00c1d0445000b03580720300b81100c603030040c40302101044481e00d96400c6402c194a0644085941d4281d5909102810b601c03032241c500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 389221133 1250 389219883 389219917
    0xa08030103031e02030a050a08070201230910050c04030204021e07150c0315031101140c0303090105074b030507020c06040e01030807031e08100b12040f0206130803 72
    0x14004d00000456006e040261601390030a4004c1c0c50644441100501c590255522842d074001d2440007001d614030010b420a507400400d051071407415282410842810451070300e800e082c4959008100103480440358120740140e50b03071704181c80c0d24915906084d0321340d0f50f09001140c0a0100000c02580490f00c00f54803a00300000c4031115001c800307030f031820204214450419003041c0080b44031096140c6140c107060504860400030b0b80c2d0b07040995444044805210b0f0404020b00c140c6440038000c954001c1c00034981248884010303120840d00101030402c00c44584040c18440e03e00703a010303a03241c00c0300703640000340004216a01c002c06405040c045646900500500c2e020818030f1800001352400d031402c14511980c20383c21680da8a5079540b200c80c0039802e022165400070301030404176040c0d1041c2e44503a5a08502d90034103420f001030006031174214280405050020801c4444080c2225070300580018402040503400d002244140c030940c8d841202000801c0340c0801d0103c80003008103050300540c2d005407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 389222383 1250 389221133 389221187
    0x20a03030f02090105070f06060503030d021803031921020403030c0219120b0c0903030c160905070e1009050312040303080f151012051003150506100c050a0803010303 73
    0x101244624615031380071030024402000401e12200101003001d00c42c1b14000f4100382c840000916542120b0398803402030b500000c10507014030b02c60034041550300c030550085060000d00c49240864070400c0c019402003100000440381c00b11001c5480d0041c50301c1c0ca5104555490b21303410300070304551a6480580c0100c1800c456115010b100311004412980812080e0003d41c080382c1d1000f0708100701400f1401040b0050000c2041a0b44c1403005105e4200d400c0700030301030085d0306541e804446440340c0c003441e0110710700410000c540303401065601c401e83d070894425249919181c0142d8102c0280c1c0c0040b0b4051151841c0c10484062040041003030702d01903210301703809540f210780310308078500104c0e8001d43c1c1910a51a80382c29091640178400f01042c1414084110012004884210392007102c100000900030a81042030042c80c0e0307a540d00d500300401080c040303883d185000c036480d0800040d00f5000c10440021b80c50502c081404000047d43d804000c5c1952540e580c1001051a02810710003030517400c4000d505 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 389223633 1250 389222383 389222411
    0x807030e0d020c0409020303040e010e040215030609011a1c0204170307020f040c1103270306090705010e04090519120504060e010c0230010c0201200c07080706020a0303 74
    0x750503107004039801810540045801c0c00040d01624104a81602c001c3c03001155141000302c2ca50302074004184110070505c2d02e801081161000c08030b4224587c8003c10900403141c0380e040e500c41c15600941e018000201c00d0300c00410552080c203c1d8100c0161803100c6500700c0301080c1d00240121005914010943d0500c105001d803a4840c19200942c070241c035414a001c0e0741400d0b00324864070071031030504c050201c01c100440d03800d552020100407203940d8202499545c507256036004c40c0c1008820f60044c451445c0c010885603954103240201e13410700082c0c0584210590300c0d904114001c0d030740300c001e940d42240b100d82100c209010341c00c000c40314141010f0002207514421802d44080741c8869855540d003518000041d40c2d4680b0074141a60014840d41d0718160200300c0001062040440700c500c501403510030403890b400c40700f01661820440e414102c80c181c3d080c001258410340c00c0b28102540340e840b25100c0741c2074036002d83ca40c0090107a006600c00011203030340105840c0515806614240102131900500b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 389224883 1250 389223633 389223643
    0x203072019120504120609030212030603061b1309060812030c0a0503070509040507050306010306050406350f15010f060c03110a0c0b04050307080303130b040507050a060807030e 78
    0x29685845180c941801140c81c2c001001d84801c0300d4180549001d448685600003c0120842515182e881d0200742d010103604002d900000d1104c0d420042c00c604002c00041c1d207880014200c0480c4003031502d00f070780b40214511704884208800e107240c90841580d820500010344107900c90318031140105a03540040c000d141d400c480c80341c0300640c400c07490806030000541c0d6541020301081d08200041c030001c00e00e40c840f445028061030840c1c99098681c40c10100043c00c0e5503564020b207000780d0520b2400c000780c1350440d003c00c80c103500c14103d044054045500c00e103854200100716942900c94200000052240030444207086204818070140316070700e82803401814140340c410400000c0c0c11001810201e403142100140b042560380030b41e06501c0c155282ca60480c0160b0700413002c002d90003c1c0c200b203245020020701c001045090095411403400040d1a81030b014801c034068aa480c0100002d01080810300080001c1c0c5001040000f919848a03c001c122207003c0360100082882c103100e09002c1000043c2c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 389226133 1250 389224883 389224903
    0x20405100e310b040b1902280905091504020d0204060c14030a080106080a093c050a08030414010e06190b1005130b030901020a0311070b061005070602030720 69
    0x7450106480d1580c503078001101c020700c1c0f42d03021010804a41500706c258001001034441300c01a41e66400700c0d0454100511070318150242c280b0440707040820054a4100100c1c1d8003215954505840d82c23590740102e0041e00c120003c0b078000c2c034400507000c41c0d06600001c4403231000303000c1c0c0411a0039400c00307507403d41c0ea4410030403610081044400104002440f400300e142c1e000103240d40210780144a0749d1842c5440c1400099030355490070217040a007808002059107080c0700b461000a0280c0012a1900c0362039403102c00c1f0251030b04400000040601014804480d200d0581b00001c21030820030900b03854441e201503c2e051484818035080b20030215490003107641d085002000600c87c52808201038034030380d1080c01c1c1d02c480c2030141a40011350074001e20180d1b10405200c030004d603407400110002411a400428402c011035010320407900401d694402aaa204405942c981d0701e80d0b0034600c0a031024091407400515150000042002e00355000800e041c0e1250a071065100c8400c141000039140c0701d07170320 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 389227383 1250 389226133 389226143
    0x20706150f0b0d0902121504050c0303071e03022103071b030203030f2203020a0210091511070b04170c121504020a080f0a17030c07020405100e31 64
    0x4031803646840748503404044100c2c17006000340c504448000817103052201c0c1001c0c003500a00030008101c184a010300080c040356a00f00c0c0a03501d008080d43ea00f01d2015984040051300320080c01c9280304043c020004400d20305e003003503960310030004600b502c05e00e81c1c1d0089a003200041d020950001c085400c0a4131012860781c10380145040d0340d50840340d003039640c000609480702d1444800002d1000d0709812121384515009070b014200202281c0140407240181e0011103080202d500010050a08000704548001c40980741070040e40c44410000d91508101390041c440c0c107240090001103000906510480c041032000035208000b070352000300304061390821200b4207190040114612000e020344000ca03800352000f0051501c4c0c0f5281c80e42e4524000b500010100c0c0c1d903204000110501c0003c6d403041d406c200284004600d5498801c036078440354015a0f04c024001d40d240c1010401102107091490090701284126011714239011404189030f0041500c182510781c121500b0382c1c206400229101c500075041303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 389228633 1250 389227383 389227387
    0x7020c04060f0e060a0b0307110f0a0c0b1e0a0504150915030e01091a071e05090904031b030f17010f05060306011b08030618040302060c0307030f020706150f0b 70
    0x3c2010b8009144004200380d0340f02540320740100d801c542c641e028500621040e541e02110303000003d1020b103030940140210700103610864881d00080c0d000303c50081274400c003020040e181c505803521001d01542c2d0620035441c40501240d605d081076070000240040790b100c050404003d8112441c2501c1c80d103c240143d6a00b146814582030855000e608106055440100001102042e0b071b11040c001e00c6411100800b515080011f0010555001884c84202c80000041d40315402030008003030711900c00c41e14020b00034612540002e0916000700392404c040f47c611020308007921410b10780102024080032260010071203031304c082002d807141422541c1c10b8910340040004218100030412440da000189210704000e0072000c0c000140b01180050034460b0711074452540c880c1010001c00514045500c0d401c9401740344d09041001082d8000340b4190460380250b0107649d039407034040341100507003424401c807203140c9d00006c0c0e140104411a4008101c0e01e000f40e00410f601e80d12400504000c030502d2148200501007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 389229883 1250 389228633 389228639
    0xe1f0206070f0c020303040b030106091706130309080d0c020a060e1309022b05010b010804020f12121b010c0305160e01020703140a0c090b0a0311030a061407020c04060f 74
    0x600c240804104240c18803440400710f07580040c0c07440d401034025112510000c00100405a08108100041c056982c0b80b90b000c1c200484c0304070b5540364000e0a40c41e03082c0303918400106050240b02107038090091501500c100b4418640060b1541680c10822800742c0115400051524803071040c581d50900d00a00c0d03000c1407103035807050a0280c0005442660300032a0840c84200e00c0c40342000d02d1090301b818643c04130840802d428401d003111000c00300359050214600402005130340700e00c812801400200c0c0c01403811070040380c03043d142a201000c1416427a40008000340f5207c10038290b2502d000125009100e504d11208044040c0c56095410075030302c60f25003d003803104601421050001e500c06104440c0515038a841390200c8116680e010541a00f10640d103000b03200020f90f550b1301500c100c2200b880066440400f003880740c0c100d80300140c602200301c0070050780d954042c4040790030319810140522055800c2c51400100401c141e82c0030015211341d130098052800d0500415040300c2d40201c1da0088070785 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 389231133 1250 389229883 389229887
    0x30406020c0f151209010f02070309030f2f09091204060c0302100603060b03010b0102010b09061302190206063102090301090c0b031005011103071e120e1f020607 71
    0x1003064410354801c01c3e0516215403003801601400003d0400482d101082c00d068210350300f12040301c0c0a560f0b6650040203060701003070704131074060708880c3c0c810300e540d1a85000741045102e03d004400b0362078042855602e1602c4106410004900040040300c403507425460746107500d0b58980c0301c4c50403010444006d0104110580c02425a200003234001e005a07000d2007000080c54007124840c0e0000c442659845c9200f000a090920070581141002e0008005601c4048001398401c40001c01c40d92041102600d641e10b1008160191507460940440040c19066009406034403428103c6003180200d031002c20003115100d4050b118401e8514440c00100310716031626031800030b9030040c0c0c440c580640d2030301052030000e503180015800600d041300380140c4078107064600650b1b4568640c08103040008a83e41e00c60107560102c111070302c07140e024406152681040d00144001c1c0b10308100a880714461913503030640345170005e10b4440300440c02c460b00380844045a02945a00300c04016050060f417180000940c80d074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 389232383 1250 389231133 389231149
    0x5100605030a0203060627070206010906090c0206060f01030902270c030c18120321010b0901050d151706010e010b03040302190311010f06090501050402090105070303020715050103030f020f030406020c 88
    0x40c2c5d403400d12540b071f03048000f00315903076001c0e2400f6006070700100040206018520901303019102c0c002013400a107407641c2009542c0e84020b84030b10300c00d02061180c400141c1c000d0f400052140c2e400791012080024070a404458110310780605c08202d8112070000300010309a1088920801024507c54100000500707413059030340c0301342140c0da0001e51082c0040b100c4081003018040c4200451f585640d04011452143d44000069100b45004117050111040c2030381c00106441404901c25000960f013460494241c03407285075907118200c410748144d8a6103034450042200381c160380207500f40488590740c440001c04c0e20710040f100a40181c01a00c1245544a00d464440c11001d000e8908403804404003e209801c4403003030401c0032081556018100494680d6000c1c840c0140001c4408504041c0040e0002c4c0c070078410500010105a03002501c0c01c02c00c07001060100d03200301000f504214942e140d29029200000f05a03ca4004d4410144021840036000088909441455001d4032082c821501480645 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 389233633 1250 389232383 389232409
    0x17030a030203090102090a090213090e031605010209040203090d0f0f0525200103050c070f08030a0e0a0c0503101104051e040207120f08040b0c030612070305100605030a02030606 78
    0x4d540030001105240e91f015044406800d1001c401651140703220240b207505510b40d440900e00906140c90707003022240c04402d9501d0300c02c0354154000302070114545940248148000103a01620105c1401014100001c058078401e1281c0ca400c1e051000e224800d03520005044050800078070100041100700035248680440e00200440c0040d407a00103941c1c24500d0152010340720500b40303440001b03032180e40c0d01d40181c0b50842c3c2c600c1001c4e494200e954540e0a000380505c44d0240c88164000003244502c0103950040d030ba2403070610152900031055141c2022200b0782e48c46107601c02c0c403948107005042d001511900c000882964100c0707250502d0242170082c1d507818006441c500890315440b81006407506d00090420610440d040a1500c0900e100506075010211034881040300040801c80001c03591444160000c1c4800e5580342c40350b4404002450705101c6040d40c3c456401103030b07070000410000180c201040101d1801c1030000f80d403103a00381030b980d018040001c1d50561241002c0b0741903050040c040071360 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 389234883 1250 389233633 389233651
    0x5070206092101061d060405072313050f0f0f0a05270f0f010303080411040c0215071803080d1103090a17090108150102010e0f0105010f17030a030203 66
    0x1030801450000c2d90301d2250b064241d41c5001d1aa0600c400c0200a204003006080d1070020103801210003140880003080040026011340e07a903c010400b280c6c01900c13000304624002d44460000d82a0380c000c0f000356000464210000150500003054919007494142114071005c0c0109860313000c81c00802030a81c400a0025070041050000400c15448050118100360154003116038214111070107030115560003002c1408203d0280148440b8844801c90941180c1d0989040d00007600ea508050314001e04c144a9144d100c2d00d0f00452048140e00420401c50303080c0100b1640c20150b80380c80341600c071061440070520050041000a000050b10880a46504000d052000580724a00b02c0700c001c5c1d9034000d40c1c3d105080d503c180c020f2810042c02007441da03202c0205540003420312142500103000103401a0000c00100d805c5446070700c070313a4800d40c80909203054070401c40e1518000490701e01d00801c02030190040c4030740300e03460218180c032505200304c000c0303484440114900545914110001e410241800803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 389236133 1250 389234883 389234887
    0x507090e1f061802040e1609030f0507091d01110a02030d0e01020706020a0522050d0803040f050303070f0e120d0c050a0218010e130c05040b1c03050301050a170d05070206 75
    0x60700d0404842e03080c3d0021200f180069403281841030140c81c15400a201d81c80c0c118000084081d40765100c0c1d00c0f07804895204000507400c5400c0e10b0140e041c50030382c0c0c004000161602101c0013511541c00e0101486c0c9040310000c00410305000789501042c440c3c02070a10161740304100e582ea102c58a9071240394551901c8d400141050308a07614813040c0c3c0c0c0002d882000250303010510301702c0c1d40505281140308034601440d04149603d4900031409100031080e0240003a070004c8005000d201c00190113107512035000701a2076403494000c0024061003c04000340d800208400d00c000306074102002000c00710403003207000380b20107056202c0c2100d480012000440300c9004ea41d45040040c0c030341800b2001ca04c0001c3c00840080e6061140e00d5400d410000d050916070503aa40800003c10007010098090b82c0c010740300810358010400118907070700c180b92012034a4a101651110030f00d68440c1c05541031395400c5810ba00381d140c0e01c054150809190400100036a00001d00070784c180c900440081140a02c054002c2d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 389237383 1250 389236133 389236139
    0x4060e0c0a14120702060a05090c120a0615180509071a040b030403020c09090a0c05060307090509041406090a0b16030e030a0207090e030418150b0304030c0507090e1f06 74
    0x503a05030003c0740201c07074201524050212680e0180400b51b0310180c00c3c581003069245ca811010b46d145100c1030402d000b42040b00c04100c84440c01c0c05014107440e04400300780501c08007001401b00c0f140d182e00c54110f034081038061038000c0d80b0703d034004e01d40640f070600010100c89040801c03011614a80444103490718000700300004145601c540518400c6010340c01421070031a410007803145035140201551301071f8102441c030f80d0008554403105002d07910180c0e83e50343c59a441823002e4800312443c0d0483e540c46040c000c108000c024400030044e4400c1d050f201950300716140c20b9691035503440c044000505001c0076400041d5109038441075560391100c18600810b40c94030b06801227045902031320280c40180c004020511012074540180c00d2042ca055009500d03241c50100c4d0b080700c0760b540029281e0f4407501c0b403503031008d20072044080501038080a0070709581c071301b0185005800d240c0035642c120350034000c99500043d0344d4a1403140b040810203031710240c8085200341000403107483d0424051030010340d440b0008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 389238633 1250 389237383 389237417
    0x50a0213110301030b062205070206011205100506011101060e09011104031a1b0406080403080c18040506060f0c0d11060412030b010c0c0f030204050c090d0312090206161104060e0c0a 80
    0x3c6010311f003031b00002100e0034403100007814038005802c2100c034560008084000074000048000c48040c0012000400f0380700c4000494540110b900407001c5903003030002c08076505080c2440309025501c9000200842502e88101d06128080c9102c09001d243e690b01c032003150001c012070955484210079200c10341c0303041c4030700000f60b254006801182c0066420710070002015008000142c011400071b550794100740c4244002015054401e860380c0c09a900c0d100801d0b110b880e21030540d40c0c0c03c4a48480c0702c2d1034400034030016989440030010840001c042401103074040c00e011404c0e13400307680c02c01510501c02380e02d12825405440c9200c00203041016041c95500496600740c0c0c001c029001c000700c801d42d031501d540100000d1b40c00c007410a140d11441003010000c581e80f04885c4070134243c1d0505005820314030614090f00140f5860401030b4100300001009011103401d41c1e111910030784501c4401c15002c070848140000c0303c519000b60b80b0703007132482804141101c0035a0045e019003551860884002091840b007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 389239883 1250 389238633 389238679
    0x40615140d110307020606011403130809120c0a0f030b040f030e090106093b040203100e0d120203060f011404090e011409120331050a0213110301030b06 67
    0x20ba098100d1020081c031400c0e503070602c0704d550441c0c02440c0c400c3d00c80c0c0142540d054288001781c00c11062001e40c801003010010120306a60444400500146600481e50b4034151100e1005414500c10340b800030000c030300c1e206109d03101c0d400c2d07030b03041010f14180d80d643d03554040752107426000550030b12058030401d8810360756000d50507000c0d0a09541d00c200703181c5400d40482c0d5203075403102034003408244c0480b030402c003070080030040d0f000b083c904c0248255a05c40d800881e060150380c4401001140c01d0441c6041200800100360304609220b50790750091301c00054280c02280010380c0d0140e80032841c1c410306072480d8420300c000110840c2103c50646082d0b5101e9001c811241c000c280c3c00c07500d94485107074001700c410504180d507010302c0b80f1002e8106d202c2d104413002d601e44001002e4100c40512140d90079441d2002c0b80b000d06441c1d080c1c08402d401c190683c100303195201502d0908a108038103050030070b482c0c0e00c106d004070880450b41c40401c83c25030342103a6844901c0301c0002d01e4903400001000c40c4455680403201 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 389241133 1250 389239883 389239901
    0x1020a0f08162a0c0603050105010914060f1204030216090614012a03031413030207031401061502210c0a030507020312160c05090c031f05030f07060e040615140d 71
    0x84a0461850008046e0680fa01644110b050002c003e1080050341d40c02d466516080310115213469468a03822407252143c01480e603980181481141040308040e0002a91100004a5041d00f25000d5880802c202a90114010005942208110400300c0d5016000044980001c10281d000d005442400010540d0a942c42640000d4a81c504103110607000c2000f20703048600d998100e1000d4055850103944c60007144001001807c6031200d664407214290f00440180208014000f000c1419040c025a074000d0002045010030700011100345032044042150b82182c080f102401404400391410303610381d00b0122050b0303010302402035030b0083e0800e8440101080d207600080c0078041a41c5050258480b11319410160045141c6824800268260010b4036440301d00c1c80d14042442804100c0c05044d00c0c029805aa0144156010f00b032059a0100b00f807002d80e1201c0d5116020307091140100700c1581c1851140c0c0c1544680280320046151042807100d00c001c10a608681c03819000c00081c1d0b00300ca0703001c6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 389242383 1250 389241133 389241143
    0x231204170a200a080309010c08030a1b030e190c1703040902030c04030c1202090a09021c150f0b09060607240902040506030a11270901020a0f08162a 65
    0x4102c5424902c0c107089880e002e861a80300541c00c100c60b1200207000702e500c0c0319001d090004040300103108003a80d9003005030309403500c0855201e40050404050064501e05044082c81d010742c112144056008021841426410407141200344d884d240201071524017812401525000c1080045002003940c0021130164140e034840541d200e1a40c1003640c00c1d10029000004028900480b002c05a6500040c0b541c1003000e116000948007080e20004800340c40c44602c01201007030000c2d03000d00740103d80a0071602e03494408401d00101421b051070b401103e010a41555010319100c0210b62142807c501510005105001c6240c0741d1001d2402e41107080302e020380040007152141000400c50401d401502c1d08084282c008150131405503948401003030307481000130300807180f0204060000300f8444071100d0719018031031946140c0c106403000c42c0c0031327600c6070307521402140c100c034a0f40300c200c0c0c8201d00c01b81c81050840180030101c0500003044444e10b83c0c509000044905c8504100510803400703483da00918850 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 389243633 1250 389242383 389242433
    0x112703100f112a0303010608070311090910090605030a02090406022512030f0b010c0f02031f09050d05070302031801170901090b07020f0c01050c070e04231204170a 72
    0x50100f1900c8924a03114000c40e00140010842c403900042900d8000d5450f08002c900812591001c0081e4024040c406610a800d1400e12030701500c178082480c00d88030641400e202e0182c444c030a05545224003d802034002c001100007030046035040e40601101c911400104489602c50007001c00003a520400545d001c045200044011035052b1041c5611480d07541d905010210550300064511030010002900f50300c08800c44d01d0466a091103482031624510a00d0180c0001d8207042c0b0f0000c2c0b080c6a422070303480c0701301404103030014024415100c00d550b1641c0210b2600b646c80c0c3d2844c12021040080034140025050009585910f96032200d100d00c0d600c8000245001c81c50912400701d0350050030031030a40d04182d041d000d00c2d01e4041a0f40002c9402801c2803940c802c038020313440d45041555400301c0003c500c3d61b4140030410000802c00c0100c5c85c8034440c01040480c0000300c65803074240754044012203410800081120300e1007a0a42d103500320029050b50b0034945070b0780f201c0720209601d0450861410f01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 389244883 1250 389243633 389243677
    0x10e0a1e061e0b090105010c0b090a060e0d0329060f07060f051e07050406030e030f0a09080d080106170901090210050c160e0408090a0801112703100f11 67
    0x100f80708840c40c090084030a038890b945880700207000d0003403824018084043d4107000546060041080701243c540c401c004000742034201ca8200d45546d4000c1c5a10002410400c01c122a2240d2030100380110708602041c0304c10402000800200c0c3d88880d2410428800601c0720310041200c6120701c03903050910043c04111450125119126402c1e181c60050300300b1101400c2c024219840403d95007a90b403a03060000710448400c070700c07600d075004100800b4615040000d07500b0aa0ba03000704650104c0301a4412a54000b0003280700751007000c3d09019900000701d10615180e141c3c110300c080716422200b01400003134000c90302c0d008605198035112900c004074400041105480704c0400c90340040d000f0410890411500340748134180b05220107040600210008100344040d030340ca4001d10401800f955000308060f000200c4213440c0758100c49aa48640003440704050b001c1004a021080c00d0000200a0802c1c0c1c00e0f1054850000d22100f1501904c0c3d030b42d503070302214a1a020790010700701480c0304580c0402c0b18034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 389246133 1250 389244883 389244941
    0xa0317010b03190506030a050a1a010803160f03120f1a0409020105090d0512121b04141e060c060103021e0108041716060c11010e0a1e06 60
    0x80180d0000e1000c000400801420f40c0c404074480b40e203075000341c1d00820340f038446900103807600301c4441001c6c0181c01001150810025045041e00880d00012000d5079035a9aa0311890b489006480c0388080a455255600c40024604407010fa2502d102c0c0c2858412000c0745900e402c11a040240c00711441d0342d03102c88640c000310045c0714008902c84201d8091040c8001980001c1c02e500403d0803060003080500f0204e0200101071241440d10600f0040c0746448054003031400182e007000b034491039201c040400640100c003c4800440342500c4211003402d82c1041742c041400154280103003550541c66009481d905503641e6600181180c0035868014001c650440c0104600131603428840140c4e002c1d02d00d40c41c040341c1d810248a552140c1c0201500074030030801c070311440f114420715180720b50089190042004018150f40b0250401c4446e0b40d40480e403c000c090070908a42c81410010f80319405140d4860000b4100c000402c01c40d21032080003c1130403201d68481d400ea611404161543c40303803120b4048803a40c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 389247383 1250 389246133 389246177
    0x60a0e0a110a1a09040617030d0203100302060a0c0c08060c04050d050c040c05130503010504030806060a03060e3408190221090d0c1203110c0d0e1302040e010501110703050a03 77
    0x91000c82e87c1c541030b03202015035030710030503080340c1c5040c0c0c001c80020b5007541082c8030700004540240401d41e82e0306a811005000c00c103800402c54026401c0b01c1c0c0417a44000008115110b0941e004a9624050400c0c04000070300c43e4280c0100c8551088411088a03925103020754160b50003941c445a40310b0407042301c010548985904885d000703a00d4a010031010950085c1c41c260000c0069403d19502c80700c0200480240603107400042c1c0345134004080c010030315504040e041020030000c955452002c07a0741800c1100b1580c0c00d010600007040c9502003000b03031000703020b5a80c030601d83c244014070b081c80310b400c40920f428401c1e5000340e45220202c00c2100c01e03102804090910403040c0f600c140c41c000295158081d01080b074050000b016031300c90b100c0e080c541120045620382c14000c012105200801e800080140c02d12400450081308590007a0140310003e00070b540c2a681940d1210806a0074540115500404d00351080110320810300c001000c1001031001f82d0805002e80d0301c5505004002c10703028214 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 389248633 1250 389247383 389247389
    0x10e0d020d030f0e060417250b0c07030f050904061716060519030203061c0b04030207120b06040b031507120b0111100903030b060a020f060a0e0a110a1a090406 70
    0x40c101901281074130000b184041d0b0203035008094802c00700c10495a18014002c60001c402a984003480c3c1c03040341c60844411150603882034002d42580e665804056000d8090b0800040104502d0008500303280d0184010300003c6002800002d035031640c9000140903034280091041094000744c0101c40380810b204076a5010349010f0400328a001d9103400090703425207034548007800705a0b012010072003641d120440103151341c290240d150050701355070070100070001054900303d016210781038000039880f500d40450840d19070003800a910319a15079060201918540c00555414000c40f5110200c5691021800b03010303001599a5401c0c0d0309408000504507110031404a043c007203450b50014101d000042c5840402e41a6200403401100c203103026400380c0f0498008aa1014011940b21405070f40001e288031480914000ca81c42c40d00c03207424080448480e2503500c030858000208100c0840e00c1d8226604495201402500c42c0c0c5a5a08500086150300343c080c1c003915800180080d0945814092117001e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 389249883 1250 389248633 389248661
    0x91005090f0102010902091306110703030b120c0604030f05010e0f0d020f0a0c14031c05070c0504050c0f03190501060e09060922030e15120c0702130e010e0d020d03 72
    0xc2045d500090140c1e00c1c0200703000004070303040d9042e40030403a5a0304440300740032440b00195100c0442d89400390182c4000c120440c0259904200007162036000584000c1040014104034030701421512204085070204a003641e00e5900c3e0055a6882d000c02c0140c08111003402c000341004124454000317042008803a80002d1a51001d00848085171803018242c003103d20301e10712854041120303c0803a0030718110b00305e0880800c40d161651142160424000d00c5100d11030f040d4016096143c0c010042200c0040d52811301c0b480080c041004031001500040d07400002455440450031911125001601e400360800c070300150403424903034240d0030f0200c0b00c150460011212070b00d0300c0c0751805280c07126074001200450005602c40b528005e05000305490700e80701030040c1c40c0c0654a6010410a1025803103032100d0b80741074100c58000b61000392108144d403040c81d402401c034407050000c501003002500c06e0140c81284cc0d561103500c0d40c0c00a03001c20007003c0b40c4015030080d12481010810150481c0c000d03003c4005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 389251133 1250 389249883 389249891
    0xe011412010605060f09040e070806070905010302070c0308090d0f0c170a051c0c06020c1509030414010305070e18061e4623010507020f030102091005090f010201 71
    0x3100742d482c4c405598020003400001516048003000080c054a00102c0608240c0a0004046880440411a00c0c1b0900f03050b1140801d050fa00c0e00110124030820b90301070020052403e0900008005600034210104d0060002d20404ca080e00c0d00f02c4a18002c62085941e052020700030496001b000c0f041e91003403e0300380301600e040c0c10795488458541d9101148012040c00310040c0e0440103004031481c14410741c02c24021512912158603945d42c0c0c40c01d075100d005000a40384001a1500390000440301901d22030710445144440d0100190042c00e0042d00100034010080d00407052074454221501140712600e0454100382449070034007003004494005c0e00d02519050740500f4154503904040c42000701061081c00c809609140c1d0040c19892001c51205a034841904c1c00d00540a901503810649800411000e00c0d00590004042039005480e61540418000c2c4210005860911200d5040d00000f03000985040c400c0c0e0300044065201c1c0400d800410000b050b031030010306169096010300302081c00200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 389252383 1250 389251133 389251139
    0x20a0506060d0b1612020c0609010e060717060d0f05010b04050711030901050d0f05011509060512010905090106030c0602032809050d03020102070203150603100c12020906040e0114120106 82
    0x120030031200404da801e40c891200a4541c0d0307a07100c1d080140000d04052011901c6a61075201c2c2e0f601c500b401d0b1450440c40d0309003004856551000320729a40580102c1d01c41d9190300c11070400300103100200410a81e07000909075200700104200e19800c0001b5407142d80009641807036001000f01301d88001e8540b0080010490069100540c000116807180da001d0034881d40300c400d607015034005031002526241e040c1c3c3c10200005245a07203120218440310440c0c5030070703003410788810003114980603900039140021081801042405c44950110727801004100c00403030340d182c0740d407070310414003200c0da00c1440180e1001800c0040304281039120044890a130b5418250f6a51920004041c030f640303806240e00c160140042e42003054000d504542510364042e0554010b1512804007000301c160031075000e4001c0c055180f080d40c0009a0b44150700078128151155484002008040707802500a141d0ba03507013001080001140d031001554050740289007180d0b0411751410001d0901000d6603001c80d900016a042c44028 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 389253633 1250 389252383 389252393
    0x507080f10090f060506070b06120a0210141209030423030a062315011413180207061503020a0b0307050f09060f070f14070e190e0607020a0506060d 65
    0x1408881802d580800c602844030700e030304024403407079110740ea0142c3c000900d4000c100c83e8103400344c4603404c100c800c400c010403030022035178461001410083d401703400e204c0002e07840e9014141100001911b441c2190500c2464000a01401819202844c1990010038100082070081c07113002491040030307202109908030400480d030303107100c11031004215948131691203525500c2c04800b414001d02804082d0001e0500c140480c1480420300d00b503c1c00640c000c21000c550760180300c1203e5a01c1d00e142e603101c1d03009180041d581449940c1402842c80141c00300f12440100e0080c2c01800c0c00c4181081380940198030354410095284569400071124076018010020b040360400d00340c50b0304241c80c400459559001c940041c80c4c40c800d499030003008150105490f010301141140e0410b90a114000b40c003014000103001940d921000e01c41e542d1078507040c40002d020301205041080c81c44030030407000300707425110a03015030500400325940070059004450180c1032001c00c001164000c24142d8001c044201c5030b03150 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 389254883 1250 389253633 389253661
    0x20607031e020627300703030c080109050408070b0411040e011e090816080d0e03031f0506090d050a0c27020405010c021c08032701180201121e0507080f 67
    0xc101c60000f024240124403000e44105c3c504144819128a944030303a10314010b0010403d00e10804c1c0003035400360004c103802c401d910510b0b005542040b0610f060400c07030350315804c9046004000311941d00c640c25503040036441c1d0707020b940c510f440d80c2c0780040b8082291200c0b003c0465a44121603c4150504a0440205103c40212010100080301c2000a54050304002d0344a20a140107013074000e20300b002100c18584040081e40c0034030071805040c070801760b47c0107a03000d18007054003600341e109408102200b1940340533842d01000310b102d030043e2688550f0503200c00300c80828650220740528054446241c3c2000c500310b540007028450072045081038203000c00201003c203c1c40c8024051412082810300003c0305682e08180aa845001c069070b9181004480706c001d44001010481804001110301000d00d040c007c518103290000e4264404c0b0742036800465481c0c1d0140842906903a81e64040ba5031158607111400240d010b890001c41d00e81032406000b0300c40c96000380410000f00440081c82034800d02a10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 389256133 1250 389254883 389254903
    0x109062d061b020907030203060405130c09020a120903091703030f0c090d05120d0c022808160b0712090506040615080f010b0102150112020607031e020627 68
    0x203820b0400c0403560302400101c902d89034020350b2114280703040094403a0b01d6002180300f6a8140d40c18001e0f5152441c030a90b081c000200001d100c0380c0660b2040c040c1c11903541c0a801004500e20303003450308844a000343d0003200c070540c0c070540c00a40b1001c001d021285071000c00151030120f5000940c81c40c0340042003250188409460800030900009032142690b80301030f5032444480c0c01c40e0030b03602c900f80840240007042d030098030560306190900c0840c01c03000d4004240c0c501c81d101e11159081ca07411401540031504450914201c982c10800d000c800c418a1911416030012841210b000a43c0e05101101408904e00781d80c0d021426801d020104001034808648690495401440400c04644404c0000c00c3c3c0320098002c1c2c112481140c0e03908100a005403c1107082c0c1d42e0a03001d560b4502496607401d00c464500340180c0b103144065201040041c00c09100809000703000e03143c4400f0a00c1c0040907030341c4c400c159410032030059101d0700c00d03c000d4407190401c0702801d4446071580c40103401c800000302c3c0c5030001a4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 389257383 1250 389256133 389256137
    0x170c0d0b0402091216120503090904051f0603030305060a0b0a0f020c030a03090e0f07050f0a0c1a0906160c020609040b06040b1b07060905040e0c090109062d06 70
    0x100101040c1e840d1901900c8418400078201d900e40c10f810840301e80d50300405440d07455050031340780000412034440c0705503800c0da80c0c0060155291030000020b00600d0345000d0001c440c1b1348641981c21205110480485c51596072500d40482d8091940c00e000302900d40c042c20640c440c5d01d01540800c90090f115003103450398069810007001840614a040e0300300210150b40a801d8010140800205903011000c00242c41c0c0207a40d405032503c030600c0300c0041c44001c032681d0010440c108108420039103190301501c1001240d00d0003964000b03950356140d400c000310818258030024200c0501654210a022881e8800303400b0008848904111070000c042411410002e0b0054400180521040d00c8a400401400320050720191f5a40d0b610861903070780d41c1c0524501d00d6007181c007521039044401e01140c4003044900340d584512045040c0390400006000031210102c0031710030000501115102c05402600900d4680c40024030185410b614a902054805890401d4000c01000030480031114000c601561024 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 389258633 1250 389257383 389257391
    0xb0a03030810081605031905060609100f06050c101a0f12120c0706020a080f180a0602030c0c0604030b0126030f0918130605090703020d05030a170c0d 66
    0x1241c0094480440358100040c035025188414a913180b500090104a44054048404c80101448904140642c05c00004c1a540141c0f0101d081032170149895600304007401e1848180d150f4031408010b502ca900e03841500456004070b80540c3e00c2c241403004007480003e5003000c0c40035100c41aa0840a00701a600c050f01c034030004052003155440b400070881d0082d00d40d004581c090319101042d980c0c640c102e000d110ba541d100c1d19401203000c0b8400300e000340869a02c109054113011450994154540001d8505503d02d0440b0841807420f80d01c6841c0c00001f0312440d009944d0310441b040001d42810b1400c4005c501818080100300b00041c030341003c090468940c40005d0740c0e00c1c0b81d41c90a2498040504a0200e810700c00810f0400407080c00c0070041074107130000c6416403510b26100c3d1151406070700171134031844900b03094041742e030104180e44c00c00356000741100d05488902c0c1c1ca950004ea0b21803400300d0281c0d069400400d1054107507070070064000825041000c08010b601d04241042c40511981741e49100098036 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 389259883 1250 389258633 389258641
    0x70b04120815061c02031021170706020c1609051608011a21100e010608180c030d0206040501150302060f0f0d09050f01050a0b0f0423041a0a0b0a030308 67
    0x101a841041d1540034015580d90401200c80f108a669030b006640200080d112a230044001c8a10710780429036101ea41510658607031404250103420118040c1d4001e5020852a0031804080c000240c45c80d9011011800041c03c203c0e0010803220014803d5a5081c43c0d120b00b100c4164201c5078072811260a81124204884071100d43d851601804508803101c0c8980300901d4074424041c1c500ca48180aa2804814159501c1c546210103240078420880131803600390200d602003102c00c815028400d2149c0485144d5590b03000400d00e0007405a094500581150082c8010000f083c02041105080358030518002411900052503d20901c2d41c499440c94000230814110050074050394008000c07030703200300072601440c10444e8845031440aa110107520f0a40042c01400031882250b0038504007800a681c0784440200b40402004250741016146c039008407008410f500402240d44107920400020440d10284009440198009021808911b0814800002c03680725100f0740300803079806140050098071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 389261133 1250 389259883 389259907
    0xc12020d140304170418200a1b0b01080f070f1410020c031905250b0d020409110a1d130230060a0902030c040b1e070b0412081506 57
    0x13400d0b8000140c000e00114001581c0c04810b06415500881040e0601840041c0a40031034801f8580b407040001e12014001c900280e84209104154000782c8090f01c005411180c4030000c4c0b00409a0000140398006007006440c00400d000040092440d5250410860b0034910f0301002034003124070140c001c920b43d50380790741c60f14401c00401c88400c102074240d407102c4642800c078803801c2c285041c00760b6891061070b008000310000c3c1c00400d810815901540003406007840d41c41ca045904c07144074001700700d400307210200308407026200307652100039a001c0241d0b40300300c100d002503d500404200c44201c616440301c05080b98076400d8290080703804a00b00103a03120002130032044031011070902c482d05c0401c1203161300041c46039004924017607031003116880c1c0c5583c1c0e146200740583c4000c0303c2c0003100120a1004005100801019101603040c40381d503030703034000e88090032112940c2004e00199110a404810702051044201010010b00f51078a0190707143d02d00342212442050328000c0030340c06198001841100c07a8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 389262383 1250 389261133 389261153
    0xf150e0618090d08010e060d03030b0d02150426060609060409240609020a02150a0908071b050402030f040b041103100605040606020304180f0902040203070c12020d140304 75
    0x40d8030074081c0905400d00d401c0480d61001140d8403e0042003d2900205801105102140c403440c0018460800b108660360110041c040c0418200d410050190f84440103079160104485450490043e881d16545071809803003a003000240c02130800708003030a40081c0718402052443e409a03050310101d025446d43040110303008000c8144080c01e4a403c5070b080030000709800300d40710000c001c070b05c1702408000c0d1142c907003004a20401210501591203030b4801d8031044d0722550301c190300882c02000091000c10700d84403102d060b844620100d0300c45d403400662132944020080550302801e025135045080d403600c10200e040c180b802500161110789840c00150401074203010582c081400541921b096204143d0500060715890050510541c10b010000c03a0715440001607400b254656017003043c00d9011080c41300c0c000c088841c1c40b00c100546500c0c8890268075540000d45c0500c009541e02c4020070b0450901c002055001c41702603045420002070f14030b86680c042034045070600c2c410506581c0b0344452800c05404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 389263633 1250 389262383 389262409
    0x207020f060f030a1d07050d14160e13020901030b090a1509050609030f1c06050627010c0c05040c0c1505040b16051821100f150e06 58
    0x1460025140341c0350307080540518000c1c50207040c10f0040710001c80e0031031780254454050000d40d40c1300b0f02041020380760009845034914000e1800d4600c1c001101842d605101c07148100da43d503c0803c4504004215181c945241d105080102c00003032455507600040307a000c010b01c0060020140000072070381000301400074003920341d40140521411000148180081c00701c00300700751a10f0080b00c0000302c100e02e0120445084035142c0a020389020203401c10395200070004091500f045a4420010400751034503001400c0100040e000c04040004a1ba0083e990340b000c0811103040140f802c001e5800a40700b40d840c0d400340c0e84121000b00ba6806100401c0381c16680c0d40d4000b41c803000c82d0a4102130f41f20300d10b41c06207000f280034aa1070f00495a0b885494141e809a0881c2e0100082003000303134101044812107442254003008040302e104030341860042c0005004149080d4140d04143d100c2c039400b014030710401c0301c0b61848402c2803010311281c042a5121502c075128800c60b21041d00009180c40e03031035455071081 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 389264883 1250 389263633 389263639
    0x3020c060103030e310c0912050a060c050901090b0a12050a050108070e090304030209070e03010207030206010602070602070503030d090c03050604050a0b340908030a0e1305040c03060207020f 84
    0x503a695034103004056801d0480f200b03000d0703c44003814a41d400e40405030308640f008404811071094880c40040720041c010842c81804001504601084543c428001102058018001007001d543c060074084100c40707041140c1c1061090400c905c007542c7e40c1060b21041211810100d0302d4503401c4110381603413031040a22740c560016140104102840c0354580c00b95068842e50b000b00e59a450301c0744102c000540050f50344e50441e0384140803c10051500782c034a071f680085185000000036021101080c00d9800c000c0c421005a0445001480640d90400a0030000c4c40c4520085c09090b2406000c01e80b01e208000031a00c90301e071520140b4003486a286543c40007141e20500305d813200e16145c1092511148101c40481d45441c01e400803580780d041c148000c1c00d8144040751103801d182481122081d01078000c468007403e01c20340090000704120107001030400402d080d101c800c81c4150000130410b0405104181c10034440c50401400b01042d040b00d0108192640010016610601800090440d01c01285035540c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 389266133 1250 389264883 389264893
    0x4150b0a020109140123060d170a020c09060d0b09030c03041d280504060902060d200c07051c05060a020a0809070302060913091406160315120303020c 66
    0xc40660541c881035019018a84040101c044071901070b0a0380c02014424595040d203013240d05603c01c132a03002030341028004060100b01080baa031188100c0062076011042105d000c80d605004c00d4040c848400860300407204800e071132814100054902d80a0900034220102003000210244810001c5807006010702045985442e1b580e03500200035070301c8409008070039040310046900700d240e0001c0200d004042e0720460703102c44082d050703690041600500c2070707a6494031000214050f850300760080c500c451000d04045800701c221844160002141010780c5d800b041c0c2008401840c4402180356411740c1d0044826940711481c904200303400d44130140c0003400070700440701030000d001420f80c0149002d51582d260701100d43d403050511a01d8a14502c0042d40001c42040703001100c2c0b0742a0001280b0300021240041c6059042d1646464032140038030200b401d5000304280f01001d0b0b20100c1ca50034800300340c64244a441c00150004810503442c1c1b2580d40e0781d4031030001c8442010301a4046d604554001400c0320 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 389267383 1250 389266133 389266147
    0xd0f110703021f1704020303070305031f140a170a0201030e071503020301050f0d03020604030e150408031b070303090509070917060a06050406030503040521060c09040c0c0f0204150b 80
    0x200300e80f2000c40800114450030a4620514110101c06100c2c81c0c009001d5804c10141ea2000d80309584000c007a402e643c81d60582d61401d00007158600c80141500681004e40d064030300b0144440c051030364100c851072920312030450052400000302c5065003a420703c0c01007480f01680d82c0540c50075015800100044003031841011a0a91640c080e504850044441294204005041c4800039984203409401600018006400f00f80102411602583d002d070120300710001080d015112a0059080074165410026a40740c807002045100b200084800c2c0c05010203034903650740038098503101d214150007038030003800296103107001d401c801001b407200801651504e40341c1e17204152030702400c440700645286000d102044d1801c142c841c96080c0d07607021006500e424100300800c00d40e0800942c801c00020301004034410141030601c1418084c8d411880d0154407080010208001c0c0d6101c00d0400042240110380c8401041712940040192a01500c0010f51780c002d03525094441c00003504038a4031607030001024 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 389268633 1250 389267383 389267419
    0x2040e0a0f0c0f02060a2c03071a0f04150209040e0616030c02030901050d060801021204150209010504030615080d02210405240903010903051801020d0f11070302 71
    0x220509040c0e4220030050300121800c160350403c243c1c402c01006074082c00000302c6000c0940d00042d04001e02121207400314102d1450280b01d03040149003c0c0c103d410100c2d1120400608240d0400040032060b000846482d100d13a203080724000003000038200c04103000000110040d55070441e0f810080c054801c2c8259942c2205981d60703040309540070181106081c2401d04207030701c01e10458a8000d87e6038050352402142100440b5560040300000c40304c1035a405000415200920082c072002844070700e114110700d001c1c140440341740864408102d0860040001c14a56a800b80454040e40e42c040c40028440c42510012000e050303154010404030301c00c0c0c114600059400144501d0040c000800209405452480703070240c5000382c0c0306054010300c0480c1200079903a04c502c41d503c02e07512440b80140c1000320220000c0c2c250b4148000c02d0300032910005003007003002c2c0520000500400c081c00104105540040010001c1c49104071130002c1140b00e030500c03003d840382480528000c40c2c00070030070385801048140c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 389269883 1250 389268633 389268641
    0x3080405010e030a03050d0e030904020408071a0f040e0a140408090f0d0b160c06020a120c0e030604020130020d200a120f090501091b0311040f02040e0a 67
    0x2800340401c0b2150250241441d00241002d01c00b54156a02800e00c01103040d0310000e40a0707031099540b84d00060010307000d942c90385d00c0504000c00301a402000610300e060302c04402041a00039160320060104000c0014011a1044a0071a03013035181100c9280e03100d416903002410103801c0d800100b0480400e1206210140c80038068101040f02e4486c100c01d1004104420f283c00d403070006101000000c005880b082c40205100300740d41d081d00f041c04c0303034a0a503952013007242d00100300c400108420000341c0300803c0f218442d4569001e01424081c14a03403840001039920200203000030f04002c80d00a01518403c145d40e10f4060b2030100300503120011020700700700c0000c0d4011116104042d85000c0c961058004010b9400010304043d0040038075101000d80111601c80742111409403058031b9070103003240d0039030038440c010b0581d0080000240134102c52070700e203051451300c0c120044210300f01c403003e2020030640800c5100951040341c0002c1c001c102c000c0084083d015540c46501c2002074001001812401070300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 389271133 1250 389269883 389269889
    0xd08071b050a2d060903020309030303040b0f180c0f0406080a0c092f221509060e0a050103180c06080a05010e0f13030915030c11060c1611040501030804 67
    0x700d42d02504202c803c4031206a000300d100c81c0c07103181c1d14030140d0007258603076000020309130084c030559241c0b40b181030104e032450713000b941c04980140c8880c042180500b0404d400603084032010142903988900f20100d00d9544540201051140d21407441c4000c15648560040c2d00422001e82a00c1880245041141e10408103100300400700d4280303a400444140c1c1502c00800b40317003101e16100010442c08114030400d4020051004060144811107290040350041510083c04070041c00e21341601c0702da10041c024000c0c1d51090b0705106070204a092907684500050040d031b42c083c41c000403405001045543c0c10b030f9403520042e10110012402060fa903a0052805100751080141401181d907203014515000d0b0040319040d00e4003089101207010414103000d4001d004c1d0082c40d0007807085441e000d11640005000d2140e0021035607a020708002d0580003000d24603404e0040e0050071b03081c94a0f41c040112032094144c400f8010b00c40b04000d034204100c1d16812444030801038820002c1cac5d81c403407810003403d501c40c0c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 389272383 1250 389271133 389271143
    0xf1201050c0a02070b130b0a030207050703080d0f060f060f0201090605070507051b0d060e01021e090a050405040c171f0617060601120f020409050f060a0806090d08071b050a 76
    0x304c00816072084480848400d910300ca402a610345d850034162540c5600500c88401c10960200b00c4100814400c2048002030360207824011707034808401c4110030490380c0000e405260307942010303010000700c00c2c8038003000d0440f501820040e801d0400110128010704400360300801c0f0600d40400e000342190302c28040c1010911500480d0719043c103d21003880900301201d041e175845000e905a90000501d0382c0c00c503c0c807040001d00090305180c04054288500050800030007008000411910340720328181c5c0c01c510040c40169010081420a42c4030a02c120328a80030f204100d4601041c946a551420030a100c454060010200a0106850000b0000d0507592082c1f0f0b1440101110001010034080340c107502400d816125141032040310744040c0064083c42100b00320f650707030900002410700d0280c0100e522401081010000c03600e450810440c408055401c0110203a1109003005001c00c4c0c002414441141542080c4d102d6039280d250848800745a041c8010303105420481003030402400141d400d0000e0310403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 389273633 1250 389272383 389272393
    0xd0515040317010f06030c09050907080a0b0a23190b030103050717030d0f110409020910030501080a08070f0f0b04050106051f030203061903050d0f051201050f1201050c0a02 76
    0x900300c01e010b40a005903100d4540100c0f0400c40d0034040d500c154190b0089003480003129603100700045080710111109400304951408101d28486c070342c0b00e92041d103101101d1603c0306a060a0720140e20740008150f806002c0003c00400300c5035903e01d811081b400c50525243d08040d0f40700c12111000b50007e1004171028420302c1c0b03010840d404100d50101c5902c802c40c000f5418500728000f00d6000c0e0140414140d0256622404551010303840c500030400b8100761400036903112000403e000365110880d03200710070940341c00d005001ca080007050f480320460300120002e4441e965410850340001048000034840781d14a520b0b58100448001079602c61401135000b040300c140d880301480004c0d5016501d000c2c0314003014030281c40040c080d0b80a941c1112000e41403084441039580e030501041260f0300243c0700766002070100800c0b81da025040d00c50589951400601b001624414a220154180680e510034114001c12040e00d45650350720311680c075038003c007c3c032140c10a40c40d0f074085a4003200c6003030014040d03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 389274883 1250 389273633 389273657
    0xc040305010b1804030c0f0605070c1406010506040b0c2d0d030b01020d120b0a0b131a04030b040206090d030306080712050703060b1903050c0109091b08060d05150403 73
    0x4030f04420720240415090300d140707655030f68007101c101e1500581141d81c035020410078008a081d030711420340f0031002904d90610060741070900307100100e58030031442c40e164403550050090b9107900064500310750703400048503241c13080018040d06011002c80c50f0505006c1c00c812803000828007000ca05a40c00c43c19041d50701d00303d00d0910880940f1010340019002d0303404082c4080b2501e00c5001800665080308000044005560000a8080704c0590010741d460402192600c0580d0741594900300401d0340c000280440710b4610140410790045100150084606200142c1036403600300844513503140052912a4000c8a0701c0c0180c01030031540240c099901c03c0480c08582c01e042d040c412070303240e50004001e003810340c03465441c0406804440005900215604448400849284580d1028622680c043c101480c40c810004200c01070541c410a40f15042c00c00045030040820103a222800c003500e4071220582d2142c1c04035150794107001c1e0091503413040c50816041c1c011600d290500640c407940d01d4000c4481 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 389276133 1250 389274883 389274889
    0x1b070311100605011205070e0918060405060618010614090d060207140f0d08060409030e0a06110625080a0b0604030b161e0c02010e041b110d050d09080408060c040305010b 75
    0x8002c42e00c2c0004a14051450101440c10380e100360f900105204c03541c0002b0340c002c05124104a02600c08507241e5101c0c1080c08010b1400c8450703032513603010076010440d4541c5401c00003005440900da0440b00401c000403410490740b114203074100c04980008040d5900d4130b81e460071001200d0410140003041c018032100c600009404102c115100400d699032000649070fa1042100510609100724188560001c2e050040d0304c0742e0404100604840c1c5500040c11080c5928500b84100145021b402d2003030346031042c0901050050781c0200140390319100d000c643c1c41c0c44c1440e004100c004c034030716031103003010500004001d5550344641c4505034510201000e801c0d40d16003502c038070965500a10b200d640e920000743c0c0d11032040d51440429401490100008100f1102080c101d880e041c480c02180180c0c408104811038214120031800325114005010b001d8409100070301500911100500e0103403110012018055110301380c8016142940588a0a062226422080d5800751104803469401c1c1300d5000050303d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 389277383 1250 389276133 389276141
    0x307120c05101a04020c0304080d020d02060703051b0a1215050f04060609030b040c030b040b01091508070b09030703060204080601061b150b03010e0607030e12031b0703111006050112 80
    0x1c42982c0300c1c3c100e64200080001a400c00140c43c0040d2105001c00101c603482003044440e501c07201c3c0c0107045440c00d00c580080c1002001400e000905042505103c04400760402c2c1500f0720b4090002107890300070f006002c550050340480a11036103410148141112a0342c0785030402280d100302c1c0c00d0058086181d0034801565020701c2a0004038074450001c0001c40d000e807000300c0e0300501c1900d034140041e842e955008520601903c080c4c0e82c030f503012001807110380764511500082446d4901800401440c150f441030382c411650103101c0c06031001040c0190780d901c04000400c0a5030340540259140c545800000342e540c1400d11039940001c40c0f8900405d814144900074095541d0406945000c11448891140107070806684c00c40e09903583d408000712a540a202d498000e0469503404101c031800080824a0181099020a140d500810600608100711140c10184100502c140b0b5200da415080036903c3c2030400c50301801c10701807800c3c5940255810350003401aa1f409880e00040c42d0341c00c0700039108071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 389278633 1250 389277383 389277401
    0x3011508010b0306010e150d0b09010603020705060c0a03090b0a0c02070605211b27010f02070e250e1009270209130614060c0a0308090307120c0510 65
    0x11401000484c100f0351042500c030a401401170304a908440800f40040181d600103921154013a503070b03000303040551404101013401008a460f0660610000380c030340f10303110a400b9201d030418400015000400307501030f0304011982c40d002410000345161002d00540500307103600c02c0c00010300440901084090043d404d5807600780404100c0010b100221030741414001e0003508845441d2220204000044003c4000b007800d805440d1401005008040c000c25100c500301076624180440c0105080747c0540c00034401c022030f00030080085064541e000d40703a08a403140b0881e040818540c00210307040c1900110401c5e903001007981d00d10b95100c4990700449001010340201d01c105007038829000044072324488004890350030b0400040c5040e09100c00034641406103200ca003e00ba40b50320040040c5900f03140200e00e808000d48501c1d1074031782e207000c10684070050300e82c004003032102609c0840e080450070000e56010943c032030442d0b100c1d80e61450024003500d2250b20201e94034030440c40c62056078180d5002d60540d0b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 389279883 1250 389278633 389278649
    0x5060a17030301150203040b071103070626180109050d0e10140d0b10090602070902040e01170f0304120b060301090b070509030f06010b090a0b0901020706050702041b050301150801 79
    0x459003480c4075401d0104c05055034108512040c000822120001001420446d01c0f61100e0a00714008100b4141006107552120307003809026002c8684940c002c280124000200250001d510b90318030f60070003140c5008c10003c4500398a003004034001c010001035944000880c94076030141c0e03d0070b400e08120300d030100351020702c1c0041c064060b140f012a0a81e000341c0f142441000020400d92204001710b0025022a8034510010341c900e40c08110090701880990007500c0f00180075440d0905000c0b0000f10420103104840a95004515101c07400b503082c001c0d00a01d0801d10f060320b90f240d0740c4910f200310502d90140180d9010f0040301c0814118901413042401705a0700c04101d40a59403000c030140c9090b04900385058240c050302010b5810000c0602c5164042c1c9000c0020580f40c082c03910030700032181c01640064200d03210400110316642c0c1c0000e60139080f42c4580c0b5186540f8001403000c54046c0040c10f4030f41c440f000040d6050000903800202440c107944800c20101442840888111205c03071007841003040d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 389281133 1250 389279883 389279887
    0x3301020d0302090d151509052401180f03060c1803060e1608010606020f070e01050d0f02120f0f0c3d03050613060605030f2805060a1703 60
    0x40380350180c0c01816031220014284c100c0c21049485042450030200035494003c1d942e003540b00300500155100c1d401510601344104801d280c07400c1d000c8641c4440303080d8010480d807004004034060313104150035400402c11103035030344009540752030404110070540400c032881414503041e00c07440c5200e80e0325125070321178041d00504031915688501c40100340e441214082401101c084c0207a0b00c00030141540201803030300000a1161030090000e04001401030404200d800c809420491107400b50720507030541d00300b00d610b0340c0206d00c40d107031014100c44100c81c000c5d080700e1010320780140340902082c02d50b4200d50000546501c01540b064058483c468010b1403603000c440d20080380500c0c06100c1401c8000524400380e000d441081301c0384035070700c020000c3d03640740065240c02c2000201e080c02c05074a072100b91412001d12895042001c007504500008088a440301c042000003040c0003020000c2c5041002e00000b00300041300b604001101400c030450302140070304c60244000440840e0000c24032802c410141c0070318 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 389282383 1250 389281133 389281153
    0x806101b020102030405032407020a030903060507030f0903080f0109020906180d0804260106180504031710030b1b0301060807020c03120706050708060303092403330102 74
    0x10304015003800241e04601c8280b00204132a03c0c108040074a1340c0070130040e020201c074500c40203e0100401801003046410104145000980084001d825658070403000304807681c960600318020000941490f8103681044003607414903400091490041c0e0401030390205aa03258550320099110303600c4c0d0307107400000401c09001c00b003410703501e80340d24000b000f00f0551035840315803113002c030941150300202c0b85402011148611310309010440d0100f48030354002030100514040305101c0a18442e0042040c8a4031080041e04151241c4004440b02c3d0700c80211541a0410900c4208110351900007119000c9045010440c500300c0221100075900c0c08403e22883e581c01c1c000c00300d51401000d0306035001e40c40340c1c2445159587d01400751202005e00f003929036444484908200e0142e400103805903003848112002d00c2900e482c040200c580c9504141c0e00703c0d6103036420416124010204103107ca002e5800402403114080c044000e4606000080883c0005080c1000100c1c00d8410081c01083c00750344915000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 389283633 1250 389282383 389282417
    0x170403020c150f0d02191e0c0f02040501030c0614092b06090503070201080a0903270803030c040510050a020d080a060302120f07090908030406050a200a080610 70
    0x1401900150b07142e6641040e1500e050b0702156007003101c0c042c51113500402c40058844481d1041107088190f440c040300b41d04008030031204001d02103070381001001386807007001d030034407000c600b50000483d4060070800666070f49040000000350140603000000701ca510344c003d610000202910382188000f00400901002900020040e5258900e03243c40300540c106041c01082d40c03840360000c05805a000355640f0080380c40010104180100305105507803810307602c140840d60080203d080b9610000b40300080300340021001d4000c2035160300008061000104000310900307480007410403600162807001d00e030200300c00c0540740ca0180140d082d0043c0d00504010018900c84c1e0251030300a0318407075001541e00d8a036004900e015180855014036907000107a0056440340c2000113070000c00d4026400c102d08443c1e80e03a0302c0c4051201600c0540442d85400100e049075169a0111581d00c11002082d0301103085000c060307115401c50b214120104220400040d103030306049815000c0000141e0303802012941270085 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 389284883 1250 389283633 389283649
    0xc01050f040b0a1803050601030c051e01081906090605120624010c060e03120603030301080a140705030618010e06010b0403022211040f091107030f020a050d090303170403020c 77
    0xf46010021002001d40c0d481144070031a00145000c1c0d07001e4a40307503045080c20029801150b004a025610701ca1507001051004000038802d130381c003441c140d4581d4480e0400d1400040c8102c803d6490742d46019000030721003055520980031a00c2c2901c184882c84141e4132003e445890840301503648116040054006c0050420585059a414180040e4604450701c5110880e901030b14420318070b610018000c3c0040b0002c9611640c8404114001e62840d810312102d80d0b296200c03010001d04080d20307960300304069041409240301900010b000c0b9801813414040d50458510071072464205540381200c10784910070041581810ba90840e101e4038500740c65a07003800601c80c0c5c006078a88480404600e15803043d189400341d54010103101640540b61810241d12950264965000d03c10f540c0c07904184923504032545003500d464a4140c02c261000201044080e414545201801441c84c0a0180040107640d0801c100c0000d49000341d491801c00507070362039485115041510b02174096844119229014580201 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 389286133 1250 389284883 389284897
    0x71202070b030c04061803050309040f0603020909071802070507050904080c06090105070906110c060c0316080a0e01030b24040807170c032b05090d030c050c01050f040b 74
    0x20440304419a500709039001600180c50305541c000001500708080da501071140200a100715006090051565541c940d0300d100c2c401d003550241c1d07160003082e20250f04a91204000f180c0142000700240752000c801070311180c0c85e02540c0b030111101ca102041c42e68080c82607495013584000140101d0341003000300b0110b104003c10880700c07908100700804900d6403c0c0301231401074195800210362810001702c05400503c2c3c0350462020445402c501c0c0401810009040800220588415a8841d02045094154402c00034030070701c11800e05801c1010400c2c00002406420280e0344d40101c0d045181c0011801d41d4541840c99034090000341120780d0700340300340e02604881d208404940c0d14280e1350b0704d0560704201e0a58012120ba002054801203240c0d42800314102d1103504401030b1003620410302d102e40c490301064200e86a0221110030442c01c25016100300e0341e031070074010550340c818002841e0003415841c1c00c030002c6501d402041d43c0c04135194066020b440b030ba92040040682002c1c00c5c00f1148065802c010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 389287383 1250 389286133 389286137
    0x6060b03100f030b04330510060c082514030409050a060602060a110d1406030d1b110f130b040c08010513090f1703010314070302130c0306090509030c060105040902060712 75
    0xf00e10381c000080307500c021b14005014050040340c2ea20b00100c0441c5100100c1d40a5414400c0380091840001c244404980140c011001304a807800c1c100c0e11001118051091b00411280b4100307106080c98400202a10031603030461002d101c81d64468104030241c40d420300c40e004c00750b880440468591001c030b03002032049005012080c6d0402c0c0b4410607500903502100002006a40c05034148481410248107d0100700600d0800354180401240e00070842090f90801411b0010300950350395007075550201000c2e42c040000c080400303180e0b140b241c81004044030502e8601c103a03c0e1100722460540a010a1412150000d014042402c8422070b5840508018a01110740c007450003c0c0000055456003a52030100a866034503449606615140c2d0748100d080c84600129404900100016a01d644440021440410340031815030710301581a4040c080d6a00901502070810003080301d00d107400030280c846250786400b2102070ba6602d03010305c005c580700154041d40180c3c0820074100403c0b160100449444c0c858 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 389288633 1250 389287383 389287433
    0x70206040b0912010f0903030b030109170705120a031d060108060106030f0b060d0203090f0c0f010c11040e01200304080f030603070806040f2307090f0906060b03100f030b04 76
    0x481c1c0c0c1d2401c507100303d686456446d6039010200c4c00c1c181e140c032407035420704415802006110380c10b03101c00d066400c0040c0d12036090080014580100001442451b400c000c2c407003c81c0d5101d07a0070110117030180c207103441c1c01d01508004104c01140c1080004400b41215044400391a1590a00d00700301c001e400226100b691103601c54a208600b034690381d00802c0c6204411030300503100d00309003213900d04110507102e4608045d40045418000c940d2218000007000d00242070003003284400789826000302ca03211002c3e0754001e24008114800700e070190080740e2048040b00c4050216400c070780d0340244a0201f540c01500008040c800507102e0301181d4019600b01d2030050403105070503501c014051610001b00c40498038500f9401e010400c114804240c903183c104003860454044410b6005566107041a00c01c11491503200c0c01c0075106006182c0c484415a60000800d01440c1c0c0c8032400d500c01a0302c01c0c1c9948482c3d40c02c3c02400203208141c05c59030803d50b50311140c418090344864603203010046111502aa00601c1d03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 389289883 1250 389288633 389288659
    0x1e1829270303011202091e0a0504020427120203120c07060e0313090609140703151706191b030b01050f0418060e070f1b240e0102070206040b09 63
    0x8100040d40c004e0004490801004105106000711420003400054510f450f0b030582c0303c4801c01c000440c0f90b1040e01d04000207020359407400001d0190190750350082014211403003298800304480340842520b8050a00401340c0340310004100d90302e100d81120414000c1150011502c101d02400041c14058014200442c0c00c81280000f24110391008101082c080840c2c0400c120128650141000906110400b0040710014880c000d003550001441082015600e00d448845042d0114048000d080c81c003c0040700002581201c0e9a6108296415804e01e60128085e41c04a080360040e402c3c9040d81d21000103032045000c0c0142c0140003180b03082418030500703001481f00c1c443d0b6240034000505250700d0a1407044c103448168000c03212107410441034901c500042003a0a49c001d00014020301507480c01c2c55079248550501200304404403c0140944009031200c10300c1c001401c1e818140b090030040412400099003409401c0b441540d40094000741c0901040200d21a014040c000d01c05001e040307910351b160 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 389291133 1250 389289883 389289961
    0x150f0b03060315090a1b0e012c01082406030c100e03060a140a0501061b031101020c070e0106050406080f091c050c1605060d1e1829 58
    0x8a800d8540ca0f0f1281c100802480f41c6c540e00003864101e695045c1c0c481d2814910803a409407030500034203031240c141c0c001590000081c0800c900c0302d82080800502c2c3d039611054266290891003400b04111105900c058a450003160300160003090014020019403540405011010b06128417401c140316820031241007a4809001c098401d07000800c0008091075440e081e28284480505403244081c50314006115007500b11b440c401c1071044050b00e6000c601c0c803624003115407180354022a0280d50001c5084038001d0030001c0c8030000d03102105440c803202d0382c84680850302c500035032040f40001031002c2e02158150741d035038005c25009603900d0144c0b0b80000b03c4014000e104c40007100001c4c0080c100041c0503100040a0089203480f421a2201c010300525020014815019011000c502295220341c481c1070400030045182020001d03440a122800d9446200070207800f05000c2541c3c40006404440c03c0c40c2c200780480c0580780307460200c02d130107034841d146800700c0001c4903c00040901c51003901c06070130700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 389292383 1250 389291133 389291173
    0x1106010f210506102d03080d0204090213090b0303160605100503031204031407020117060301021b0c18061c0503040f180c020a0f060c0903150b0103150f0b030603 71
    0x7139880005032a56616148208580c140c00c070501c80b00f05814044801c03612050001da040403690441d105030b40380c90001e002034009200b6a44200495480080d00c1e00c01092200c503480b04503013452208001109814050503103900c11801d0301000060b5195503140021056030040740c1012440c0a0303080840d4407180440d185902c00c804a002807069401004201a4801c42c8075600300d45500c1280e040c42e41079800a05214014039650001c07a504a0024085031000d5054070001c1c0b418004900b542403606030020b407a2220441c3c03c80c0204400700d00c0d0903c00754440300840c000c00001c2c100d55400c0001402c64900f150361003004480c0e90004110010741020262903c03006000064110005224004000780855a026140400b0364004105040116504041101103030303403c0507006c6005402c09030203c580e000e55410051a00e190145d010b902c0c01525400250741940c283c0b420004d0310081600038143c40d003a44652030481c6d103600410712014201201464000700007070300320382c1991040f50140d0f100c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 389293633 1250 389292383 389292391
    0xb130c0801020d0b030c06040509150307170d02071d040510051504140106020a1b0b0406050703030f29040b04020c210f180f030703050d1106010f210506 67
    0x141c0d0041240454100f0900c00d8550b5041c08030f0041000010781c8010902d64003c0f8482d1921810fa4600003516205224800050f075480080503100e02e0754491005c0e03d80207034002c248807902d103c2d0b945000a43c50001658400b901c9803450000000080c2e41841203090f0700051085034140101607108800c107100e801501d000307501144440c0f19000400c0b0070300046846101e100410b18420394010804280c010030a82c0c180d039000481d880b03100056030020300031010700303030702c50380c0710040018000441c590700401a00b00c01d03110380d40c2440000c41088000341a80c44004882007a9000c42c030a64071501e00030000440100c6020b04041401c180080000b81240c0144c0307881885038000d8030449802442d01c0c44400350464054030003605244034400c0341070050180f00d0201400302d25041c3c009034960344904462500f504003c049580c49601e030315000751214400d060300004540d10a0144680440c003240c0b4030705983c2d041c00d2125005280c841d10840c103980714800000e8048400c504580418000e01003244a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 389294883 1250 389293633 389293649
    0x3050903070e01090b010c0b0606130b030a0c090b1e03060307030c150801080a03090509061807180506040303051602040b13060810050103050a030c060e0d021605030d0c0b130c 77
    0x3903600d48030084d070907148031000d4541001200ca9442001a18041c40542c00030819642240c98000c189441420000141c02242001d00c0100421422040c240c12040991000365203400744030b9954840b2080c80e000d20680c0c0c90004103107802000b404141c110140d64805802011a000c4a9070b03a20fa03030403450282d41003030380c0480d4981700c2c20360f5403a0845140381c010300104000b0000540113480c01446011180545803040074010301086456803205080b40001103107851a10060400180c084c04030340209902c1c3c00640508200090f04c2e14200b4169811240c26441e02072911006442202000f09480740c209d80c807075625440800d1039140d5002c420b601c0c4041c29000600c003410072040a141410301a10014502c0c04e100c018070003c2e8000c108030030801d0345070400b6482d03450146030040c0031700390050079811b25200e82e10003003040c568006183c2e0403208200750342c044030715214030a140d26109041c5805001c2021035003100002b400d00e60981d94408240ca06c200e4800361680d942c016105880e03400840 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 389296133 1250 389294883 389294909
    0x4170106031101021f020c01230708070e2209050102040e010e060a1412010b280b1e0a021c0302030103062a050c0c150a02061008030301120305090307 66
    0x4000b0340a03650485040700740010180382440140c1c5001840e10066a051002d401042c10460410250041d554501d0500b0704052100110b03c3c1034249610b0442ea52000030f8132900115182500558488050100103040d2915017099491000010502d400007a0307481555100c850000c02c00070701c0900058500a06007003115498101800654000900000d1250244881c208181c060020700034200410130303101b10380407070001024940100002174140e034104c00620018049081114100c0070100340f2200c503031050b99140c4610034024041e09501d03498403159242e42401440a442c050030614038a441214031502004400d500c2c0c5410b50349441c00130a40100c01481000312602500341d0340a00994a6a06440b0f1101c1c1c0c2c0400c0400c40052405100001802e0841840280f20340c027003d11000d0682c09030100205250316441e03108428100060064038040768080c6440050350040300c000800840c107503420301810b003a9900141508805200080105c1c1c91151800e0180000400c4001c100318 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 389297383 1250 389296133 389296139
    0x30311070f1410170a022505101e090302060105040b030d1d0111060c0d0c0c030905060f0712080103060e0c01020601090906020c030304051b01080903091504170106 72
    0x40d2502089400800c40710740d00340c01c1400681000154104411402c4a6120000039901d6042d1000060303240c04505420580c0b040002069480d0000c1c200201d00d0b4580464a03001007840d14020416003100030329980002c050708034810441d400c820707820004030034082c502d980d41381295000c80720354000072005a0020f1b00100220f203041c0c4a003940c0d40e5010b9002c4c11a1200321503000304a20005a20900c40aa81c030b052588646d100c0ca001c1204007503010111507103414040403681e120741061821049040c01c0100c808101849940f20110f141d9154880390001804c01c01040360a40041b4081903010400317100c020046120042400f504007070b203481b1407802c0e504506041c005d4403113a020311040c80e4024181ea00c41a6400101c0a04503550310a000400c1c031864a004406442908048a03c52101000748814082c0200b48100c103022261080340d0500c41e43d0005442d21801151a841690414001c46545080203442c1c0410481c80c514a10315150b101c03855645441000014460140e548580c14 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 389298633 1250 389297383 389297417
    0x2041d10060f06050c0d20120301081e030f0705010b040f0e1c0e040e0102041502070f092c0c0a1806090b0a03021012020d0f2003130c050a0303 63
    0x10002420061600920b0085c1034005103035100200401a01000040e070100c229840d031592140d49400010b40588411030586018800035230400e0040d84090f020b45034004504403000070b20905030b425110b001c1c40c00c109450321042e03a00e403c406001d69a40d500c804040c18a50303120701c5162034010300c9d6803000680b40781e00b1074004d00d0685041035030030320010743c420522099504814910219442118080390203100c0001c2c0a0290055030f0040610f250f800300b0103522a5004501102551180380024401c1551055a90b01740d520221403400004005003001d102007413003d40d04d0036464034080450300c04c0030002c2d010407400400b940c84148002d2001c821941198858010180205001c01051103c2590300c00081c84203661071000a1182541c50300700e400b19030040250b02d05007605808119250030004518001a185c01c041c401c101501d004d90502c031060b501d5070200d5821010041c1142581d9400030304000c1c1000c0d42c0c2c0141e5a000d50b000c0b0000e22039503008005009944030f40c1d40c119403c281e032100707 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 389299883 1250 389298633 389298659
    0xb07080307120e030d0e0a080f19050f04180b0a06020f01140f0105010c15050705040f0501180303031a06030a020a030b09010e0a1e020307020a020a12030503010302041d1006 76
    0xc400300440c288003c2a405071000820740304008041800000c10f0400801c84a07e081581031000301900c002045960750751131030070042e20304e40c403005110f07500034500728004444030f01c2280c0d410607954200740b0040c00703115080ca0303e60041e42c0c0070450000e401c00800000482102d955130101005038040d0b118002640c80c05c1c040c03500901c0702110000d486041c907080140c8041e805011b25030400c1451000781042c0000c3d4840f880606402c000200b2042c107086000400301d07032141c0564824841c41e000b0000c0d10303520560701c0801c05010f050590103081e003183d40c100d0247c031000001141080804100107110b0303aa100c0114010205160010b0351008100f43c054243c40c03031090402d10500944004003c004210000f00b503000307070038040000300c015250a000d244080400780c01d1a0b00c0b8030100401074202d4000500c0450a0b00031903881c1030055035220075054407610a0b130700030300090081c00100011b003007a8101101e2044d03405c8a4000701740b140340c00c8038074001440c821030251640700c14041002c1c50300c0c1a8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 389301133 1250 389299883 389299907
    0x50f13080d1407082223010503010305151005060a03021b0f0d0809070e090d02010510180e030409180b010503030301060e12071701151403070e040501060b07080307 72
    0x412806030428401641d036140a01c20b0040c004e22400210320b000c0780d407143c07840252544203025584030343e92905200382ca0120a9580c11040c4c6c180405024400d40c001c00030740c0c1c100c030303408030042000c03011030b40080e81c0d25030002d440000087c00700c041c00b15650b96260b002c2e20003e00c0755a00140c650707403d080c90007805801e0368041000c0307400608000c41c90714000301d00c0429581d2141070030205a103070321400030f14103811903104804001030201401413042d404114000c060760070707900900c00e5480d1110810b031814401d120301442d104035502c204d040c0c02c246400c814510905c903c103407030901c3d58032510503040c2c400d041d4059410b0140520b480c8104120003843c140500401e40065080d981003c40241005083d6024244181a105c01310b81e4030740030802c032040103031034610320600002885140c1d1501070401881800c048a682c8400480e2030341c0c1d51034804421400060042030400e1903d44c0d060846400588180c409540300c6c4004100c000c5108020840c05100703160a907035130701e0904801044801545 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 389302383 1250 389301133 389301137
    0x32a10230c07030f0c0809130e0c0103060609051005210106120c21020d1b0905010201090c17030d0e16080a0c09020c0a0b0a14061207090c050f13080d 66
    0x10082d4008641e022001c6203c4580030308112908605d01e0800e0071840c0540101e4070703030051001d03103102c0c46941c10350000142404000d003214654101c12005400b0740e15a0b000d54000150605800c00c89403074400c0c200f00c0540340d00d040c81c900d4800040903101c4040d01421560340351110040041240d982d000307100711500700c400d030010010f01c8140000103200c000940e082c035a0151948807022802c401660403070740300340c4030303901c003000a102e01c103500a014441e8004000b020440346400064a0350040c01400f10f41544030412050140c1480110318451020b88581005840148005a1103404501c03952141001d10001009c01c100351400ca420000e40340c0d0030210140d00008030080000d0241640e40c0d0039903c00600150710b88a800403107a16082844401602d60360442061101110315980300e020300038040103144035266506800c1c0600502c26008004442c0d00c00041000380502c0307a03110f00500c94251401510781410f4a50011854004207204403a441c0c05c04002c110002040040403550030440c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 389303633 1250 389302383 389302387
    0x90a031b08040522090302070905010801060e0c0a030b10050c01060611030d0b060c07030605150d05062d010303030c030b0301050c0405040917070803090f032a10230c 73
    0x280d4506001d4000d900c1018043c4507030f95040030401c0100070b1044694401c0c0c910411a210490030025680c9103c0e1013010383c0103251030000303d4610418020601580c2a01c442c0382c04e20340314a40d460b0107a900144a68041503076907880d4a1095036410045007542d00c075941c03159260b11042c2886400c480260b4009018803a502000000702c102c044140e03501819035050002d515104607000c05c40c0344c0305944c50700c3c1c3c0c6405500b001008000751540701070f0040b203c00504520340c503022400e0055501d400c010240c502d40c002d100041c0c0c84100145030f020300c00c0c502580010701c0070000c0a0940445000c3e00b049011a40f203c507085192503041c401c00701184002c6009014138100060014850f10031802507900a0740ca8141c040240504080c1c91100c1d2618010075659801d0759041c00c1d4595002170f078802186000b01140034444841c0002680d0040b4151152808a0303108400014003903519076130b0401e12405070308420b0044060611504800c4c003c14002303a40b83c00c0d000c00b118502400010001c040d01c01301 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 389304883 1250 389303633 389303687
    0x305121f031101030e010c020708120406020c0613051e010305090607090b0a050f0a03060602150c0f0d0e012a0915030c2016050405042d060203090a03 66
    0x80300d00140032070381c21248074401d240840b00128040c044506003100d042d803c110a00398503035800074a5504075003581d0191440c010440b00000c605201d03501c1088010f034044410f070056460207100501c62813803418010744420756604041610601104010b0403c0c641000d40c45115503014001e055201c140d0f031000e07004c0b80c40c089002420340291805070724088100419880c0030903000340201d41c0c3c500c048001960b15040c411a00070050a0140100d0006008400c40e1040c04501c4038125070090909442039414030f481070400e40a907130800400e0a501d1511640e000f50303c03136402c0c0b0600c6c4c1140d03c4803602c0e91512000911081c0190702d010440c030704200e0900010032800301072101d61040340c2c00518002c61400c940b000700300c0b9642841b0610148850a03c50003010b69030380000c1c815131265411000441582c1c1d280104030854808a03806002c800d05a203104a8904215450301402c3c141028403d0705e4041d59121541203800458905560303a01102100041c9508401144440342c0c038002c10840f0900c2c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 389306133 1250 389304883 389304931
    0x90303050916060806130e03030402180106090504090f0219030b090a030e040c0c14030403060c0906050717041205010e0106081218031f0515041b05090402070807030512 74
    0x850f40706075010400a00d011420030703920002c0d208801008600140400480d0711800d41e201c0c1d1085d14101c0c0f0a00300f01641d81c910483c4100310074101c8110740c90340f42e403051501084c00301400b0341e000b04507505c00ca440b92080050341c485a28009464002c80c18103a80d80c21850480340e80500035100005507031010260340c002a1b40001e8091403400191000310341c0094005040d50305074078565005212640e070404621000300c0001c040e0080b61300441003808840340341101a911503545004d03d90008008126000c01302d104040d481d921031b40c102812929042e40c40441004590481c8011585651660b01003114890240106009407544030041d0085e0484c3d40300000f424411500580300c036004011089800e60340a0001c203072485e003400c0c0399411001c40350700c0b49002048200c944c0500804000b000d2002c60610340300702c440300d03007509140940300041c601c2c055400c1d400032106990300540801c42c81002825a01c0505841803007521140e458450742003000d401444001c1540c54444044516001040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 389307383 1250 389306133 389306173
    0xe01231902070f12050a02070e04120807020f030a17150607140705060703050705010e060f07032c0c0a060c0209040f0302010209031c020c010504031104021c050a0903030509 76
    0x160300c4250050380c070780d9a4078005603031039070522028008051150314150442d4000000b08100c81c010703801c1d02d1071140c4683c02d0042045040d540a824058030b4014078120b94001c00850380c1100540c0110780115142d48061851a844041824001740300c904501c104004c0c44440150005504404180240300000c04500540185400904002040f000307411254506101410280c0000f80440b079440105080150041d40b040000703c8bc19072070840c950307403000c4010400a0041e0180007215149032190034080f00a070000c1640c0420040c3c140125601440c00300095200c4645801d005d400600e011070100f044122040d4890302c140080314a105005903111001158025400a41c000000605041c100c3c024049c8120135501440b484070010001c216421452510300c3c13075907089801084100c40115140d0003148401092140b0811a0544a2400e50058070b00843c070240601001e01c1182031000c2139500035921001410350303500c3d81c107051643c540030300b59210070b000004010f540e40c0106c4081c00a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 389308633 1250 389307383 389307421
    0x30d0809030d1104030f030801030b130210050306011103040f1e030f02060307030621060b01020312061c0503070602040602010605180a050c04090c0e0405060f01080c0c07090e0123 79
    0x41c6607540c0d955014080100705440107107412092000e0809801d07c0d029044c41403e001c2500c40701144000243c904400b18658983c80b58094041c148080700390710b00b40c1c3c5e43d810151070325061141c4411141c010181c1080540000c114000c003002005183c8156010215403c401c1090000c201140900124204800d00320400b5815507065a0343d594118007240100041c0e040ac10301103640700c540c00d00c46090000104810703400780c1d03001c212015a1000680c3d2344d01c075044c00900ca50601d03100058003840c007502c11207150150b424030080050525a1031038207507030101108448141c0c0c085400e1000f01d40c24032510001d00403d039403224403d000054104ca00b5500103090090580c2c485000808030364601c410340f002819011030074062b224016030050b10078184808601d00840c0b41c000050194900341203d408103000686074004540c5441c0101d4407250700c44100b44c00c0600c91801d0005800c40144140c614010901000003a901c048034020000703800b80032041440448003500303000c07075116005050b10032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 389309883 1250 389308633 389308657
    0xf1f030308090c0d03050703030e16120f0204050c03071d060f0a0e0a060f03051f060c0f0c0e070e03150c070f0206040306020301061b030c0b0a1811030d080903 70
    0xa541c2c814908a140520381400706402ca00e0b900c1d0920209038020002d400d089209480600440c14070300f00a5035038101c464070707402c000041e0700320401911000c0105008003d02842410740000c001d03070041020383c1c0c815141c2c02d850044c0082040512035106110310b0300340c03981c00d090711070134009080095218003400007484600c02c1d000400c102850b004000d00c0680700c80c0980701d208026500c1801500842c3c80754190000300f0b051900240c800e00780d1000e007103060b102c0c0326600c0d43c0709820701c1000c0703d5021071010110746000c1040c0b400408258030789000d03401800010107043e00c42c07508210043ca030350501c80605000394400c03d03000c001c10a001418039809122101c0340d9861725103504005811018481000e500260b0024022003440640e80065040c0c44054030b40340030754005521003040c441101180540050010700c408000980c0304082c6030b802102c8001c1c04900084841e51081c100c0200c8c80c4200e80501c0c1c41e106003c1f1078103090003daa00e0300064103080c4800d10b07150202c162680701d03800d074280e1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 389311133 1250 389309883 389309897
    0x6030d0503070e032e02030613240b04150309020a030201080c1b101104150503040807021e09150315060303280e0402180409050c10080f1f0303 63
    0x40501c43c1500e001050001021141042041154142240b41140d94800458401036814601c0f030300f64002c5a01803080078129204000706000300d1401403980c0d000603400d204c0106040700146600c54900c2024100890368599168a0f26060001084006c074107001414201442000580d98082686045980a007854425039031103422280072840b07507400c50802c01075803d1200c0c005107000240784104105036201080a075440d90402c900d117004910032542960903400e001325015206202450f0064800e942c00b07410300d0342550021b891380e05030f5034400c8517039103210f461003189127017640c0403e400107100d1880c0e01100d1070110100c1d40302d1742c64441070140c3c0700c00e8101140c0f40d614100304a0790040d44417907650900f0000c1c4100642a2510505002c000a040c0c40c3c0d0f0001ca890184201e403482c40b04841410201c2188a003800040e004c80c250550319801012190700d8035071501690078162980302d90703e0f941c852a1281100444d0781025100c55000c040c41c6c80350710202603505a805007981c0d05428902 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 389312383 1250 389311133 389311141
    0x1e010518060f071a010e16030f060906090917030c0f070203122b02040b0a0809070e07121415130f110d0c0f0807050d020702030316020306090606030d0503 68
    0x29502d2040c0c40a0568044001901d801440550301c5800d8000302d842c444040581d070f807035101c41c115000c1030301c000416002d8503040200440c00380c2e00107081c610342c210010400c150742d03c0b161000c544e4a81d1102d07407003035100c5000804000118002c00242700e481a0b44d1425400d02400801540c003ca4045200c80c110010743c11066540c1001503034000001c145995aa42046001000200c5244c81207102158401d143c1c162152007280295802d40c0d10700350041e400c00c0f0654008a462070009440c118070381c00b6004000c10608840c07420f1600c60483d40d2645600c1d04036055900c0c084500b00c4a050555015003810300c0402c60501d001190796010803110134813071060210b441401441050428000f039071800650848160700040a0300700040701d00400c01291000e00350696008011460700400580050006803415000d0000350021020f10301c001801e100469002c2499a07205120282c43c003806140e17014114501040100e0384200e916000e04114108003020a540e0b010840e0b5500c10b01c0b1001c0001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 389313633 1250 389312383 389312389
    0x4060e04020d11090a08030a020a121704050d0f18150512010e0a0f051509131406040203010e0304031101050313151b0e0102070317090901060e1e010518 67
    0x28581c440000e80b41044030700d40c5200c040c502d039030116004900450004d00000b606090100075103c4640031a0054480045140d950000d04101d085004041c032694201c440e04010040080c1c91056101d000245a0040305080191500090108040801c11204c0e46807d80c824100d240c0700c2240d09160b040010030341c50a0068a007806200c0790800206190000090952200044980159511001004020944803418040c2c590440e4041a101c01d5100001403500741252000d50000c449502c0041013451070b6205c450312004990041d4090340f048091206500e000e11604410b14000002180b17014515500e84101100000c1198184000407000400040400e40f0b5002c1c0150710030082465075408000800003403a01d0001c07003a140d1605041803403064010000144a50700507001040c440740341d81c1d84d075401078046243d80c8055000c240a40310058a590780500e0203400c158807500e0300c0300050000d0241000c400120b80c01464a03114041d4034a9800508803206003044010244000d1401808 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 389314883 1250 389313633 389313637
    0x9020a090b0a080f060f0906090703020f0705010605090c07050d031e0e0a0b06032814061e0708060a0302040e1507030204081501060f05070606030507150e03010903020304060e0402 79
    0x1240000680000b04065001d602c9800e43e13104030381c030002d03a001549441061000c50302da5102003d803c1804400424158507250366200e6200d01d2900d0054645071ba100140d81003508500022141c90303444260074000c902c0e0120070560b20001400000e810001c1607100c0a50341e02c01e6903145c10501d942c0b2080c144d8803611030701d5490700c4807100c02c10500400c4640242240c1e19441c0200549030042c914002c10114940850916041c031800707442445c541d140955410050500d020084408a804103200c812400081c802c10f4400e2044400c81002502c41800038010b4081c0200300008002080042100b1a55518070001c01d4a030184c81c00115071441e2003c0c0c40c81d05030308004015000d2400c030200b2103590780c96001002034541c60000d43d08624070081c14180c3e040402c3c0214404624511003010035540f0a5015011050040c00c01260142e520388032542440c0c41c43d00040d83c02c01c90050303410f0819400c1084640340d014198000c00c0140415100207440780214040c840820141c0150b640103680c481d01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 389316133 1250 389314883 389314889
    0x210a050f1b150f0406120c030b01020d210e010c0216081c0201090c14040b04180b090709060305010b091e190b04060b0c0708030412060207030c050d180f080709020a09 73
    0x41c55a139116110840600400d0303905000540980c18001d070401c2d464480d0280c105581c0042e002006080c13241c0600351403c04c2d0501307001000034850411001c45000354000c02d0349c0503501034000a03c01400c507000a0810054601c080c02c000e01480b01007000060014600c2a0322100d42d2542c8500b01b1400320490150100d0080038054400740c0c0d10100d0400001e109007101580308460402c8040d42e50070500c400d8500d20700b03100d18051000080400821100300d402d43d4049000020703642d60a03110000041203450f59001174170300c0d030b560f040000540e003410010301350415001d00d000c0101038502d83d14214644801422900c801c0180c01048c2005032042d00302d104a8440100140800c60711160501c080b50002c0003442c04a100d41c17503002030400d030003004540035660b00c514106d1208140e0b8945101941c002c0710201d08119603150480003040080c40801c2800030030707039a8128002d1582c00e84c3c1614201075041807681d203100c0b4400700000f802c0002c5500488040c80e002688031900400c0686a04000f54 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 389317383 1250 389316133 389316157
    0x4081e18030607110303010e090a15140f13030c0c1d06090f2a0910030207210c0308090c06131d0c09010806210a050f1b15 54
    0x4540980340d00c4052124010500095003120310ba40e07550401252003204407407000300c0a4000300010721040190480700399100064800312440101c1a6840c000610019042a800035035500108500b03401c092100302d07005400d124035150541813001ea02030049038030420050a000030308118200b0080419228401448070454504605412005440b1660b1048a4262046200100094803107400b00e0b42540614408074a9900c2841003902011800b9800181501f12407400d00c90100e503607698039500c84800015607000b503201c211902c0e02001221003035041c407404200034045524681d40c090340510b4801e42518104903030752603203200709043c4001b4004064000304005480c0e20103021042445080381e034a030400606007648020440340e034070b0088c1ca010000810811540c0b0075584a20350060b00940d00401c006006600203092504650b0704d1052800550441e08000c014450207116080c540d91800000c4c20b1703400718054103030f5200c1c200c140b02c07184501c11750032800e00d5184000082d0754664040c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 389318633 1250 389317383 389317387
    0x10824040509030c1911061621030c090e06040f0e0601080105100602011503140309030106091b0513052b0606050f1914060706110918090604081e 64
    0x5508141e07100d40c0080c84c050301510030311141518080c046540740c15134682103c03419482502c1c07182000307a240e211280414400201d01c600b503021407442404566030058030301180b6507080340a031000e01039401e107404490500904103400c1003980c4101c1c80840e40403604460005a010f800d8403000d004208034101520708e4441c080c004544854150b0105014a51941d000c0319025a503850888c262054115408548116401f04000060091910801d403094110075a4100134000d400300342192200e80c030404000e926224200550070003108450109002e40c60006d01d050300c1a60100000591480703500c0c05041035840d044c4135400812440f0383c2600541c050324100101e10300700213001d0007440c0905480340075900b8404506107485065480400b100c581c00900d07261410050381010009514100e410060421082002418520a0f00c1a80d101c40e6a40b40d16101030900780200c040c0c1c00601007100c0b0134840203024102000040c0c0c183e000d80e01a46d40c079541e5200d01840c0402000d5003000d110b00301c00c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 389319883 1250 389318633 389318641
    0x3020a0207090f0b041803090902070f140a02130b1509030708031b240609071e170109020306181905190e0d0f0e030c0a060f090902090108240405 64
    0x554102c041318540440d02070041c02c14064079226203000210008011400e43c4804204e55078054016040641c020b0f4035106400941d91a5040d84801c0e01c44d01180316000880107504500e880080c00300840c001070000c114801e0f00c040401d590002c9044008400c1c6004100400996002c01030300000d860304d6420b480c1c541c00301e441400d0640200c145041c52501410303030f80c6090840f50700c400b402c1c070011198a108640d291203050180e40040a01000308100a03a8503821158207480045502c8940c0350b643c00f8145110002028800c11041e0440711100340104180000fa07921001c0901c8800f8110080150750348603403003140d0000c6098810102d403542444100680180500441d14a01d540760109010410200c0d203410b4444112440b01d5012615a4011071078092040051801001c0d028044458071a90480040c40c101e5541d403103200040c41160080d40c1a99020554400411a0f41d1095007000c2103800040c0c84100020440010506542901c0031448202c1d0320090b12000c000d0300401490038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 389321133 1250 389319883 389319911
    0x60c01060b071202010506130906060b0a120e15040305030c1c09020414040201050f091314011d0105010c201002010c03140105060301050103020c0f0d03050615030702070603020a020709 81
    0x4001402d031a00003125100f103440500600400b44140c00051104011042e09841d80000740403a10050324001d591740d0380030688804141c0200140c044070344450145a41501d0001c0179107515070582982034002031000c0c1c0318074410b03000300394202d90f250600031784036501d06d80d0290b01d80c0115010400703000d103015400b401407202030348501c215500945043c080c2c1901000b110280c2681514000c0c00140c0c1000100c40700311a00010700701c0000010010704212807407541000039600046059681c121175000100b0603540340d5041c02d0040d003403120701400742c0e46c5080c001030506e5044d1708000c1c00c9a04c0302c2c4080005070a0011a413400ca490003400500c1019a03510000e0082407018882c101203880c01c4591014001800f0030a0304840d0010855440e41c2e09240044010b034219000b41e041522032140c0c0c0e140d2f50344007840310343c9124101d0380c0d001030686000c10412a450074a00104c6007524010024000c072190701042400c299241820701694800c4164022440d00d245580815541480c181490120713403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 389322383 1250 389321133 389321137
    0xe0f03090f030f0615040e160902180a0311040b0108010e130f080a0801080d0e06070602070f0c0b070614040302061b1306050316020106060219030c1a0702100e070b0702060c01060b 79
    0x21742c0c1600d0420140300d441c3c220503902c0e0940007220002421000040205448a400a201c0d039801080304a6810860300041038403501d080c1c004035901c500032903500003e0305241c400c40b0910301092804450551404031031010484001e000f030304034104046c10100038050712188107514154030403502541c540540400a04442c005e000d841b00d14041ca09c0b042e03001ca031088948035801c0c0d100a10651a2201c555a014000e40c045401110826001c800060218031030056540040445109241d0b8900d10b5140c580300701c410b0503e803140c104008400344130105c1d43c002001c50303018800d0503e040c0355803600010702d092070085108102100112607030101d4030f5544000654003464211030241d44040b01c29101340e007070b984140075440060748200010301c3c0a80c1c8481c0b01481660090509045c00c1d516921103885501c0718045400e886100c03003080c0102d0035410083c0850510b00110700b045510f0600c016161104a140714000a501c000f14103c0c1c2996150030846920030101c5000b0040242c2c1c40f40e03d03040c29 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 389323633 1250 389322383 389322421
    0x40204030c0e0f0105030f070506070c0915060f0c03080117010906111210050102030f0f071a0601180e010515120711070e040b01090c1707020c040e0f03090f030f06 72
    0x4000b04500005d80ca06000441c0c4030125001005480c0e2281480f0503c0311503040040190340341d4440d0080000e0f00401486044111301c0d80c071011411040c2401406172a100f00c0c2828241080600c000350390104c1e92044d8003038103442d81006c1a00a0a420043d524050901d080014000500d402d80100c072120b512402000003803400c10410302941d8810740c1d2600c24855500c01c00e030242e041081500701e0184a0001080441c200c040550309100307035511950040d201c13611080304040d01200c1440740c0c960b007040d200c10100383c00981661165080810380d180300c500610842d07015194015051603d40c11060941b130754815400b07009803403850280070003800c82c0d000101d00c07490390040c0b820114500807801c0c2c0281c440c1d5084100424142d00e051075400080401d0340101041102c040d00014a035101500c495004480c26401040c40c1c000080400089580f5400303401800e82c05166100e81d620b102206032106039004645845601c0e40100c04642845d10311501d00c01a40075100c02c01040b840c3c049007041c0b807 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 389324883 1250 389323633 389323651
    0x12011407030f0b010503010b090f180a1509020a0f05090d0b040b01030b1f330809061003020a03020f061c090303230f0402271b0702010f0e040204030c0e 67
    0x4003c64001c0107541c603200a024800044a080040525908020121060040001c0d054440c0c0b02c00c190482d0114050030798402052549036401c861f50211601018000fa0051030421483c2105405010b4592071440000b4801e101c00800d00825550b02c0c04030070400749400608401d42494640350290f070718002400116040204078010400424603c40d0812480e60780080c00e450040c02c015110610300120080e41c1c03c2030000e40b103007515200c41c2c9900da9800d00c07010b48401c241e070308000020700e080000c0140444a09411400100301503600d2a0f0043c0c00c898060310745000e84c41c00c1c200840c00c40d120310071242c802e070404d401030749603c0841540000841400382e5410020322402030791842c280130060310740514000000001c903030541a00c5040c190490320060140f220014941c545c041104205421540d40c0c41a01040111020707256280130300000c03104903550710340451580060200c0f10302c003100700104455078004015644465040b50040c42d040000c8481c5142d0707540ba43c2011040448003051 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 389326133 1250 389324883 389324891
    0x30904060311030d090303080c0702041b03090c05090714090402040f0f03170301050a0e090124033c0501091a01031b05031b040b04050c1902060601020303040212011407030f 76
    0x500700d4411445d01080d01e41c1039640c1011a00c503441404100e400011f0146d81c016a1102030080c0c907a03a07144800c5060401e618041014119070034024110703441680000c1c0149500c2d0104081154010310108807802c41b0a807460f2aa0f080c48081802802190043c5601d502c41040226189410172001f40840c5d00c80c1460101007260102c61000078003003807049980200d81c1400520180301101c90855115020300c0c000a10704950141002c6201440050002d00d0030500a050041c41441c10b040c0c4000c4004202c900300329211080502150104c0e0b90500d80700c0003d040c1c8860802c503080d0404500706801520000c030440c03014885200604084c84225011880e42a600400e2100c0d40c0c10350007110402009403004189401c008080b01d2180c0b0402507020780c0c0e60000c110340b80d4461090900400200140b103455006000411030350040409030760302594001010030041c3c0ea800000c503540030350b06480c41d01005190f00d65041c0900054205149122902020001c4966059000c00f00c0c0c4124001c081c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 389327383 1250 389326133 389326153
    0x80a0c1808011d070315020f130f090608030309030706090503162429040f0504050105070e030307051c050f030906060112201b06010e0406060911030f0903090406031103 74
    0x2a030381305101e1200a210032041c07048090100d0f80e40c0c0c040c0100341c600080d11840c101c60400000c00c2c400d0b05820058820359000018411181c0324400c480181400d000118610b003003120801e076aa01507000002c10040d140c0d104402040003d1080e14000c4a4010000044000d03500e040489020703000d03140c60040c1485120088040c0749070061000d661848000c046881003240e402d690600141c5070069045510351400c0458481144240c0780304502030303c00051682080305000b009102101000c41c800d600c280884804948041040c180c0c0e03030718245031881e240f007180000355024007552000b408104808820040184000701d07029101c0c1c00c003646c82d00c4440b03064151103c02c0710014081c01c005060544c07154411203819100824035146440c01c01c28181c04040d12151410100b40c0081d4100310b442410f12040007003038043c00c0302038901034400380204200c190001c4400e000040600000c0c18000d00420714240c0180b04642e0200e40c054401c0c0410380c0c41e41820380030810480b614a000e0b120f840262 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 389328633 1250 389327383 389327441
    0x303090c100c030e0102030c0318040b0402030606030106050c0a15090b010501080903041206140403020717010203060906010c0c3c080a12020708070303080901050601020c01080a0c180801 82
    0x11604881d22900c540700301c080e1907141200e141003c034030710a0541c4810071030840031040070009002868121143c401d01e241c4908288001da071031840d07a90340141c0c0180103000380c80c0d4614040d40d0546199140441d151124608198038000c01242c014210710f0054486e4401d942554100f10b01690240e401010f003642c2c1e680045030014000c807204155900f09200078000340241001e11004a40a268007080060001c03d80910f1b404040c1d4048005d40c0c40100104404684a000c0d001030380a448021421860100040307483d07070344010107407410080b0750309850b8104000c030202000604031030000301c01400b050048408608498000015a265802c4072881520b10b400b00780005948580c3e014110102c41d0340c0da00d00c0c1001c5403070403640c1540584d0310701107400c41040240c1d4005600aa603906440e04040c1d01c041e0031030303602928140c11034200d10490344561760000101d80e0001501c4400040d100c0752440100c40c0c0c2d03400d9052130311403141c1072000040c408105401860140c480c4607806030264406e20720f0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 389329883 1250 389328633 389328649
    0x30c0b1311011e0c15020a0504051309030f0f17010e1f0317030c070b070201060611151b091e0108010501020706021011040905091006050a0321030605060c0303090c 72
    0x1680280c0f080c441c0302d00c403244100c50f040da1003071048510740c1449610b0000320313040c0d801110b890000158081000c00880c58812041c060542e00e03034804100141640d100180744182881e030b0007090103501109c0d480f410344590071710b0f650006c0c402078080035035845055510700c001068540b03000365a03004402c6022415040e40b0365080f01d40c81000300c11800c0c4455a039a14031b810080c10044501001d1220b840031a001c40c555034846c45669000103840d134101507000d08541030281045a2070b900100d104c11007106c50300c040c0e0350008040001c0d07180e0b00082c0e55000b401d40c4214100181c0008042d080d860011152100303000300c0320000d0329501c5480e030f2500c0c01203944400b00e200303510040c1c0c400d260032510703c9100c8e4400300b00c0741c00d00d68145280640700c2900d44165101036406c1d241551002040c81040380f441d121780d1000c0c0c02c0486c1c0340300e001d901d1030715803956056803141c0071564100303030000040ca03480c081e50010000f03000140950352601c4a00b0784264898004880d20032140c007a41c1220289031424040c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 389331133 1250 389329883 389329907
    0x30908120c150c1210050913031b0519030e0a05060a05070b0c0d1109040e1c11030405091003050f0a080f03062b0507050301050c0f07030c0b131101 65
    0x50580310890080710079900e0b006041d2000b004070401001c80042e20b20002144615803421524451038641801c0c042d840e50010720b20740504010300800400643e102c5130043c0005003040d01c0400c1c81159007400c0e0708002410241500031082c40c509082010f811902100360560110342d01804180d448081c001c45214140000c1e00090041042000182150715115000b01404580a0034070400801820840d0b4907014600c68065020442c80030134503050007040722200620000d0b04075046651b014103540d00706030254005000503101c9070401007908006850003060010005102418040401c1c85059843d00041c2c1d001d00540c2c8070500c0b0076038005890358400d82e002c42c2051030308003010408640f54202400301c030b034000461040308038894202c40350564401005030b9012203041c86860000d142900d260303c83d5020740d0500c410001c404030114244e468001c2080c90350b40e0740c0e14003458101d4603400944001080d81c81000107004c0402d640c4004000d40c0d51050f041800f56141d103200656604501072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 389332383 1250 389331133 389331157
    0x70501110705010c150605090a0614182d0a0203040302210a0c0f021f180806010b031008030a02070e0c070c23040212150a06021b1201020703090812 65
    0xb07400c000025217003100c03c2980300d5030400b00044098880700080d2142c4402d54003040725a403108405e214204951702038008145080380c070741882203031601900420070401800449070344617042c0c1d03480040c026150082a145503003422910907143c40d8403444000c4d001540c00f940140b040000c00003590306030719081540240110040d5040884010080360103c071103030411030300d0040101e040f40050b101c283c507050807038103201c44050344440d18090090400f00d22003000c0d6441780040c642040446000718445054a403404447d50b82c07580c1e040c5003510f5450090b03105c40800d100000f803140d00290b022030303000300380c035041804540c25031105d000035403d6011f40e840140c1107680810b0308100c240381c007039920b4800103100a501c0c040501540001412070300500c2c203425850b0315007030030446406044000744a8001c01103078a0091282092002980c400d01400c42030b860001c0c4403170b03422031075845d0901e2642c0035804000945d42c4005500c1c00814500382403182c086640715000b10368030904a0a410344002c41200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 389333633 1250 389332383 389332397
    0xd0f0801090c1101050f0103020f0d0c030602070309030b070806040f0b03030313050f010c031a030d0c120306050a240302040605090919020c0f0606030a02012f03030907050111070501 80
    0x4111035000802c0903001c01400e0040c041c440180c80c400c2801954805d0345c42c01c500030301962450041c800350408420314503205488042c1d070100090341d0b06004d80c00342d0360030180c01a100d148919003038034209080c0e0009099644440304020070b041d03000180500c5950282d409000c43d062a1025809480f6500e41155044e08180006640b40386213564041c0c0300d5020b0030403901d00403c0180d0341421181e520030b000340040d4803014042241c10a090340b001b500303501600106445880d0a000030320b02e1000d40401015582c1248071103a00b00d1007030b00110050017008080711515659842c0001062403803583d5400741c0760b010004940301e58021304c01d40d011a507003034991515100f040002c00100284c024503034004540c00000c8040401801e2001e40001c0210390010002d114100704107074071703101d4010021442a03000010940060b680301130300316440908284c01d03400f4441c5151003107251000d460403000c141c1c8004003c00c8010040040c000e400c40382c0a0701c440071200d410244441d110003060003258045804 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 389334883 1250 389333633 389333639
    0x60109120501061e080106050607020f0607060b1507021215010512010e030d09020a0902040b12130f03201203010b1312050109032007030201030b0301020705030313050d0f0801 77
    0x12800303081100351080340009006a110080f5000c00b8003e50300302d2880184046007840883e07030920942c4081c160440e4407909001c002e900040c0907003040c0c40c81c07501400c800b181d50010071019030449403c61100800c1080f003205500d81c1080703903030040ba10607807095405040b000c1524601042d2640c4d12160390303100700116070801d420b12a600c0c68003041390f0880d40d038170994510011020310240043c2800c50001080d20340ea5401040b0b029041a0016203001d44104020080301c0b01e403d0448a49040c000107601060341c170f56038244042c80900f64007800d000b50003030300d960415502c01d02c6042e80c80f54440c3c006100210800c0741c550b1302c0700400380c000780c0000e0410050254458984c040d02d01c5038500182115401d840e202d6100203904001c208640d56134450350000c042640242100d000e559422084440b0700d001c881344660348134030341d12000e4141907840c656024035840a4045410f855000412a9507a003401505542044000c2c102036500e03001d40854800300d0b5101340202558040280d6030070190b642 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 389336133 1250 389334883 389334899
    0x926030403021c0c0b040809040606020d09050f0d02130603061b0203090d020a150f0905010507050a0f050111040f080f0c0a03142a01030507021f02090d0c0b0d14060109 74
    0xf920140410031312500320310160002d004122030520a80c4240f003016102e500380303030138802507030712035000041950841144007900130b0b48401140c086400c1110300c2003105050704081812504141406034100110307010442100304580c00c19421284194002c0208203140d03644012000c01170718480006030070400100d403085c80e04c11140c007515030001f001c4408040d6500310b480c0d90441d2852a9802046081040000381d5070890101d400412081c00c00301c1c030b40155952082d132250700c0520001c5c8201a114400410f01409600c8140c40f80c2d0988881d964072510341880100030031241c4a030013050304c01d61207440351448000c10340c4580e011018011010f5241036542d1020301141121007040c0c1440340d0a403000100d0385052840040e00c0c660031482d5070884640e4001020b88000926080555000da0014241c1494010700d0150300c0300104001600d9100e1140001c12000040101402080401401140350a01c410040c4503524182100704042da203034009074000941d0840748680401e800700780401c1031f00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 389337383 1250 389336133 389336173
    0x414010809190f1a010b0d0903030b06033c0f04170a110d080f190906060803090a060306050d0605061908060601020f070305030d090f06092603040302 66
    0x70320035080e202c1c1414048020912070040010603608004039445500500c12992101c2d11180c00343c09000c0c40a40c105a4101141c0c81031090042c03103541d54088020074144a0350101120290060900796a03050015001011803032111141030454480380420034020501c0b0718038a0059480d0206240c03554131400401000c2d10000d0056585001011012803483c404400034a21010780f6201d0502c00410034600910b0300c50b65043d020207105e0241c003130000c80907804031003d6001506001020900241e094548040c04450400400040c140303080841c80b00700100240440010a917018003901c0da403030108030251030305441010b40150310610800d0100e500c580050340e00120241040044e001d40010a00a0780b45503070000700e142d004a020700c0415a418400c0d026241890b0008000880c210b0b2203454580c881c0401c3c0340709640c4d860b8080340c10030040884090701c40d600100c041003001c0c4107080c0001604000c0b142c6c10101c580100942040082c15410789000f55010313401082000b03040b00e66a0079013 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 389338633 1250 389337383 389337391
    0x1051320070f0b0c0417030705100522060203092509020306010c0b040b06031b130c0e03100209010801050406060f030b060d18060b09040f030e1302121b04140108 71
    0x203652900140c0300410540c1000f14024001c044450b90f40758505140c1c1d00d101c001c2071000542c5500101700f08800310358000381000c0305210100c4000340079102c488025807494450b54510350f21602c0c508103081804016030107148511400810740e841104660036941d0222210403061a80301d040260601c0103082d0341c0d025543c0010181800301902c00303682c0f100b03881103100311012509100d0040800c0960f0038280003d201760141112592000011180003400c0f1070b010010100a55a072111603500c00791280c400c4240106c40641605e00701084007003850040e40c040c001903408614031a00004150606118a808844e0142d079541c66041c056071044016160f43c00c2034586c0100248240d614800440c401c90304080a4401b480c01c42e40c0031850484181c50409503000d1040400d04100008901d90034403003100b0301e03854500260030752079140c00140208002e4445909192010660f800540c125050860289030b9102c0c070b00c691401c00200040151140307006241c242c00c85004445059401410183c2e04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 389339883 1250 389338633 389338643
    0xa03050901140903091003110f031003240506030a0f120c05031902010f0204030f0209040503160b0103022e0c0201050f03070509130506010507030e06120106080105132007 75
    0x8410408108980360202079803c80500c3e080002c0c24852407524040001c004c0e040d0b810144500d00074807400d400b11b03006000400f40d0b150000800035540e0000c0c00742882c06598401441039920035890400c00c0138044810705480700624040103c0d60710b140c002810145298400c403010003046940d42c4030300d881d50a024045080c0300c0c5103001c807000103030284058800c071911076008011149050400070700350341020791210f0341c0034030410003400440c2a942d0000986901038500b046c554681d49061880c41c841c40c54220643c2c01a0013449082164500701c40b4101c138000ca0700700d840e80b026500d440820300f040d50420f04041e0652211001d582d0b01807034511403010b00505120341807007034001c4c200e20140d0049840c840041e4000600d101185000c4c0c5007440344004000c0d042001e8905040040c1461003001c201800307001d4000440b0045a0b1080304a925031113916a0b200071a50b59030f540500703160000e004040c0706543c1011030351002d018030310441d01d9024600413034140000245501c3c4030598421030701510 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 389341133 1250 389339883 389339891
    0x606041a0a0608090115180b0324010509010914010302011103120a150b040b040e0a02040b0d06090f0e15040501060b03010e070306050105090d0204050a021603030209030705040e030a03050901 84
    0x20980e9800760000007800d80d61602d81c810b00e00404001d084507402c480c2862038038040b00b0140485650b105400500549071303c00090307601d2050000a140804404251341c0c00d40a5400c03184982913840d002c90f040f25400e94841e04a642c0b1040b01c44203071487c04820103655030015004001543c8100303901c0c40c0e03503a80c2e181681d1602c124035a800c24450401c40c1c00140041c1c4541b189001210350381408001000d55000450070a4142018280a8071440c0b2601301e010b024403010440705c0034158101d80040043c0b58885650f9540302260bc0040c20b002d204400d9142c0c90f184c0e66a5808260340204a02e4100d800301030200c14106000f400404c64016105480319940c50f040428024011001140645007c1c600244903141919005081e9503240d000b06040250910007520607485013403403003603c3e41d8101c0d0007160b00c0d030b50550002d00a01410125042800c5e130b1240d04024560140d00070b00710000140c003a108015100d40a010907204a81458449a40104160540140300c0d80c07200c1d410000c0b07140003003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 389342383 1250 389341133 389341181
    0x5150f15040b18040b18060c0a030f0903030504020f090c070212010b0904260a0827120a11150f041b0315050f01060f14041d040b07030509060604 64
    0x1540040c0b110f150032040b948480c007400f06200036040c22960080c0c59000307411041d0203e4501d1619850f024240317609103540801c0301c107005c03806500210002101040100b14458013410020701811083e2020780c001c3d400c9100e207d1441c2004e40d0390301e21400b240c0d04210b20705203550342803003075003101c0001c16000b0b9540c1e0001407034995111302c025800343d80a2141c4d600d52550400d46c0c0b000e44040090411401082003188281440c2c000b60200e038014621340055940c8084804880460900d00c007400c4e03554001d01e8071030b030300d50700200001e032100c52016070b1a2100c62245240480c1c0c5c80f548054154840446a1f0010f10500a000441680f0620070041c1d030982c0040c01030702d26489002900125804000400078040c01341a47c403039079601c640600b0f40351174194905071005e0403c0c200a4501c00c2008004c0a1810095449200b1100101a03040a010f00e022014000746168103054400700c80b0707070305c0c048045040c0a1187c0101c40c0900014006800d09403101c0c802c000007080021b0702040d035101000514 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 389343633 1250 389342383 389342389
    0x312050f070203300c131e170a020315090c030a1703040c09020301090504020405070f32031f0e10090b0406090e100e190f080f030108070305150f15040b 67
    0x50061744520324064968040c0060b8104000c20342d0480307480f80140d0340e5240708041d00480b811013220b0902c10f80c800000c004200c041c0c205004090040d405218840b10b40aa03901801c0300f00c4e00c120b140c0000d6841c800c40c408105501e4a00b600005049040c1134800c00312042114401560020700c10310581d0406940d4108160590300245d004503c029911020881036007058000d25500c400d15180100151900c000c3c060306100342065040c00c04000400c88075a612181003040f555200c0c01c4503415100d01d454620516102405040c0141610841000080320032031200d20f10b010784891415030003818204150707a0010090340c50501c2d4003680f603610000740704601d07206210141074240b0240010074a452a4001070755a0000d12a000350301415248080707400c1010700e144125400100710103411340d141400d5030640210111118002e800000009185c0c0d4005200710859101d2010745d4103d1003110404542c1389400c6441c1c8500000d040e001941e00c1d540340701010320f515801000062810401804 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 389344883 1250 389343633 389343727
    0x2030d020f071403120604090f0b0603011512120f020304090213031406150a05060a030911090903130614040909050a080d061e080d12090b040312050f070203 69
    0x2440640750400182d40000c445d06011040e4032000a03141031204490590703d602c8400000100030b003002e1400c0c030100c1d00651f0290007810304001e6904000000b6900c5408a40c06524000d0003142c1c29401010342940c071a0003003442c00300007003581c0c0146081c2464401210040e5103e0002421508408000417000031421490b1081301c149080c020f014510b84461064500b110b05c200b0f00e8400d1440361410030866a46604851000c4160319011034400c005203003040070190154185a03006040400f0800104400005403035845048001003a000e40e45220030f072100001070a4000700030038100800d1105042642100207050710842c00c07115070459644030400c564100030301c462042d944034481000304a9007181001e0070600c002100840c1e080c640760f00c941d61001030500ea4024040d5400f0510580d00c04d0303600c000c10103500142c02008514107840c000703064403000501a6000b0b07141c00c01292101c6400c20007944580041e8004503d000382c4000400e0004448881070703440312140c030401221051803905 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 389346133 1250 389344883 389344913
    0x106090c080a270809030a050109120c230f1e0c0a0503030a0e150403030c021e2202130f0e061c06020a030603021c02090603070602030d020f07 63
    0x2400046221500000030028840a008840501c3c2031802015210540b10b940401040051422a20001c03941c41e016820380980b00c001c035490700400b8201d005000043d00022200c0c3d10a4021300840c1d05600002c0d40d0120f0150000780059844008030f040202105418001d0b00700d50710111400001d034010080d2402c51100c0b0304200c0802c9001e0000c203d94010000a0703071300c03d4101c1c1e030464920b0410000c20f95038003d0014a0003007080342d07104c03804680c0300e80d09100030866a120540fa91a512407c0c0909010850368040f8090840100c9030005804081000205174200070940203120108444c3d5030142594006419412039080091240c108034401d2520010f001c1d00b6000d43e0681d251450300c402c0e10b0001003c1601490003400e00c00310040812886045055010000580f03511007602c080f0000c000c2c940009401490718404a031400b80c11000c900300b420710890300e00bc490ba0b510000e140d1a500148160300c0035034030074030105140c1c2c40550040e1056942c19040e003070608465895007400001040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 389347383 1250 389346133 389346149
    0x408070f050f010b030c0406180207022205040201091502030a03050c19110f031204030c081e030411030d4e0e0703110907030603060e1605040b1c030c02030106 70
    0x994101240c2414028040510800c0300e003000310b540b81a0b00c50f8028202000860ba89e03d40c001010b01c00c540d40c2c090950b495802500614000c011a504c2d00c4008240584e0240c0c0410030014001a0306c5502d03041039261000d15a0256090080030b090680150101420741c0e90181424800111400700396007804085010750380e0349030291003150341e510f42020400142c400654000f0401c03000600c8546214a030480d601d4074181921142e035041c010298041d00107450a030818080500156586640185000e1b5001e0352110f04020003613001c249d076400c0600409808030385e444d250f09055080303001d83c0c94034852022a100142141c040c0c4820300013142200600103600740090010040c2101d072107000440058900105000c50031521003044055041c0001841840e0300800542554170030703008000119030081c0140080824003001c02e842da4005404141c0007052480c000440745080c0c01001003081000c3d2844891103180d0f0405010002c0703504040e0203002980307400d0030041e1001d2040f0030003040c800c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 389348633 1250 389347383 389347391
    0x3030d020904150305120a12060e190501180f1b0309140c090105060a02011407020c1008010f090216171305060c060106030509010935040305060408070f050f01 70
    0x50070421048600b000c2480b00c055074000818000140b00040128090620704100750f110700303c4090031202e40244245040d00a0b00306000081c0700661800c69501400c2000e00c1c8080140240c0c4040b812100240718000c104107442030300b400d03070a0b416808540c031105140c0001c10201c1010f42d001401401c00711030080020b03030314002c82c0180822014010a07000000001d0408a00b07201c00103512000107000b414480c0300d002458081c000e000750300c0180f85040c0640f035090b541c50603403c00380d1156111211140901408016019810f200c0c1c0300d1a416205810b08040c012410210420000c0d0020040070700c015081d8084980411880303c00001309455040c7c949039107160040f49200b110303403d80d002034001d9070240555490104007040d80c40c150340c0c2034580082c0d50342c2c980c6141030241400e1071019145a9011480d60b0841000d6444d03000c0300804c408070884171205490064516100d2844090803035040700780460000341c1440018503006005414640c10b507005c54484505048012480c86016992 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 389349883 1250 389348633 389348647
    0x1020711010e0a080604150e0d180b09010804060b060f041e05061801180b040b070606050603040c18110f0702030706082406070803090601090e190206071103030d02 72
    0x2c003074900c0385402e0b0195280c4000344e20305003103941d440700c000d0001401180480d4034005400d05139030105e85036000312404c44130b2006840c60050302100c52103c003180a000f00c40800300300d010101c004c070f130400715041e5180035041d81c69450300340050200e400c005038002d000700212031130541d864001d0006030a00708420900385ea490480f2902540f5154011400707007405000d003848488100080480185007070a01c2c070302c142074441690602401c0c03038014854046000c00c0c041240003174034019100041c8903900030000c254841040101e540011034009100103400107040c0000d00e00c07114401194805070398003081e0742405005075803254000c3d020a0121920120f01d4905610b020042d80000b0015410510001c0c00d00302d441c1c4e2031508410440c4040d0603408103c100d07040e2a044200c070b410640091050b920707414000b041c3c80e02c41e10280714801c2d85a05203d01c02d0390404001c1010084110b95040c1c0110801f4158248482600714081c140c640c1c0404130080070040d2014402000461407035140181c0d6152 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 389351133 1250 389349883 389349887
    0x504060c0b090a0c0b220f12150c12050a0509190303020c0a03031a2b0c0302030102070302070e1008060f19090c150302090603010909020316121502070c051003020c0102071101 77
    0x10b010307040402010040d0b01c081114030102c1c14048103444c0c114065a4282885040065427140c0203165140480d160400e07140c480e541c8110088410342d031041041c0450344441e803440303003030320400d84814581341c01009d41101e00280e54017888003020b02c45d003405810b114000108900b0f08900300c1d01036000c0398440d103240036002e0f41c00809140780c1c0411961980c00700701d0070701000d500c04016486011040d8000f020720090110109098006681c018001c0d5a161380c40c3c0340080d21800f6605c5244403d25001020516400e0022060800e5403080d20060003299541601224a420054605ca90400703010006d5150400317180214031a160241e20f9001007145040301071801402401015001c0510501c0302c42002d42ea1001140e04581e0703640720116030348103036000280c00c2071031140e40c198075110305002c0028041c14440190b594180108022018844000c041c0c100380d100c0d20800502e40001840c060145141c8696405200e04031481c0c014100440035603800d089900000041e20b1203610700b821124a9a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 389352383 1250 389351133 389351167
    0xc080a17030f01090e0a230c180703020a1b051c0e0303090603041a040501050105030d1706041d0a0b060a1202010203030103080901121a030606010504060c0b090a0c0b 73
    0x1040c0e44146074990b192212420b0014001030207040701003034403040210406281080080d1440d43c002c000c0b48104144001c0d180442e14600d400d043c0c01b0b005003940080d4520307100303580b00f08001d8a02900c03122a601c0c1c00d02100258855203a810170300c1f28460381d0600442080202c00c200c2d070712032030040c80300720f241d0580034106403103100c400d804002c6810080c0c695070301c001c820780d40f80a000380c45841c0c403500c6600c4d0103566803012817468006440d414041100b07108054004a040314425401d44901d001142022a2900e1482481421902c01640803420b5070400b40d0110750381c1900101e010a00c1d40c1603003000d070700b4210541c8081d280306054000780440c030318000603200010701c0084036920004485a00107074aa02051001400000e000702e48040d080c1d0107440c55210325240d01100b0401038998884440701d15a031420360034068420301c00041c025501400459081d80d100303480c0c80c0558410b680c1c2d0307102075220047c4030b00c00a0140a09c2c21000401c4841010050205d440b5100d482e81d5042c18801010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 389353633 1250 389352383 389352413
    0x12050c04060b090112020c010513110603040206091011061806150a060f030b0a06030c200c06090f06161202010504120f05091003050615280c0c080a 65
    0x114500301c4100442040c030022594085000e003001c40105003034140f440d00901440c00e81d02820b500302020040b070704035065180b4800b00d210fa0004007a81c0072030814801c45001c2110002d4210004221450003880d020b0742d60b10290381d1a140158540c80c06a20203400c190064420003e60703030399604000780455051250035070001420380191500c0d12900b0014900302c9451165106000141240d034941500c02d030400699242c2c0a401089500e41e079010050007880d1040000c800038040b81d403100410440846c07414643c0c80e04c60010a00c01c4180d0080020f07551041c1231490f40040440380204079030701d900000c0c1c03290b80180713840940c40a01c603080032400c0051458600c0d0846e490002048000b84085c050040b00c00c0a51801200f00b14105805075864481c039a040c90b40109010880101d181e0b140c0c10540c81380d0010f50307a60641c10800303d01036040740140740f0004144140c1403c00342c0108814203650b80809400d1402ca43d101c50781d0b0307c5100080411340c1000405401c00c4010038140030f11b02c8010503507 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 389354883 1250 389353633 389353639
    0x10f05040503030c1e0415080916030b06010e040f0b182e051816050403051f02070c060c052418030d060b1308010e07061b0b0112050c 59
    0x81490281e4840780c883c440146000c1402e440800e071040d048400c403046040145034040042d680315202ca040380e5015421840580c000381c00d00740022100000419413207007a8405640600c80a0304540e1950b41c8074000130002410015480300c1850f803540c03580a000242e500d81c9a00150020842040c8010b400040e6203000e501764414043c0246111030144040c0035a2100a400c0c8038100b16400034a00008a50b00595100088003038555260031007901c210b000d801814201c004080441000780e13580d0203a844080c25640042c500c5070042e07420ba921a0343c10b07103202c000061401c8020354900c0031307690a680104000541e01c000840410404100310084080d0803250855030804211040c420008000c00da1444001d03c8240381842c0601041940d5640421450502886480710348111a58009500c42193350044070070000314404103210740c43d545e00b800c0014003007950401c5400d483c1c081c41d03403a48034a803030175038220f003804a00d05c0400e8078040c08105810003a50b2a042c10003038a400c4d034146203948 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 389356133 1250 389354883 389354891
    0x60e03070c0b030a0209040507050d06050f060a030510051504060801060315091e0c2615090c0708040f090e070e011526040b0907060903030e1c0b0108010f 68
    0xc0414240d0500004458034420401da036941e907540048068080e0003003da4000341418140201150004060460385140103c108036083d610700c100070840c46501c0705c01c1d800040400c08041c00d07920a81001d68419211032020303001c140c2c0c803c00704803071009000c01c1000001002c502407203040e43c01011103004002502d0148500501640150201c2c14940315058500c3d0340c45140e40d1005036504025103811401100c00c10410158050241142e03800d52031b4902c2a0a0b8a80754a054414000c52a40642c042c4c04186400040d02c1d01446202c0c140581840c1c18080203211200024000304c004101801c0810081e4056074680000101900c642e5400700c0c040b9084030300284001d581000807581107406050800c0407001181106480b03250207034098840020860724140100424050303428081d0b441003074105159036803060400d0301c46080d07000c2ca0000440001041010a11a80c1f0381c98801070010b1103c040903001e1a0058074140342030104840400703500004110690007032003011038046003910140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 389357383 1250 389356133 389356147
    0x51006240509010c11120303071b111c1b140f0f0105090f06070602090909061e060a1e210201051209070b0a030516030b01050d0903050c0a0807060e03 66
    0x70300680110ba00700343c100100541c864041c40740c800b003100341c0040c0140002890784c00149261751250700840d46107011a40213900381803907001ca900081c62507604900301402581103c401c0110100b01c22040e200601185000c19000c01c90545c00c01150003a015003154810307180c2008040480e1b21204200d115a06100c2400ea8544806008010f0320100346442942e03007500d0f83c00903403103a542a4039070350130200c046210020088554010200c448003152040180d5545092140d5110401c40784510a1081d80001e0a070309a5a1152243c004000070171030b000c655160140b40700d007902c0152649a448804100400400884c06131086000b2412180c52500014580020380b2a100b1050381805c070002c81000500019401e101c514081c20705188071079a00c0315654002005013070240c0e40180d0309020101d461210034020300c506104980185c4942d401c1a00c507040c424000c01d400e01c0190103001d402c018150701c0c40028000708941c41c0c800c2a6030781d1505036508120301202c2401c800c000303450780108084 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 389358633 1250 389357383 389357387
    0xf030a05071b0b040b1f060e15070f0f081605010516020d090605070c050306040b1902040f050d03030609110726030112170f0c06070c081603020a05100624 68
    0xf0b9540725400502d902c15039218034143c1006011b0040142c511310b80100001b10f20319a0081c0c02c034404010031201c0580e1036000d01004c108500c684400100000740200130007000400c25035550341309500440e046810300004a0501d6031080302807400b2105a550360040141d803a460040b02820303002e040c401403050f2042008090481c003002c2c087c6406201c404030724070b42001044032003000580009000c2d65814185850501035409084d5090180e040300e190042e0a82000e0b442910115040394800104070b03894103060008144001405600300b686507200400d200b0640d012f80712100034900300907907840e04c1d03d06020700301082c0160f5400c1c86029550801260407043e10580c1d041d160804490b0f0411015132914008182090485111a0101040501c0480481006030034501b12000c169503055554080454072503051000080102006001072110481004080445144240112041000c01d6186d080c81c0c9000b0881060b4010744600d402c4c8180060070030302602c0300418046080400300b100d0f0300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 389359883 1250 389358633 389358653
    0x40602011433061902060705130603050606070f0309090f0b0a0b1317010b0a050405040302070b09030a0c1502010b0102070b040915090203090703060608070e1602030f030a05071b 78
    0x400200c0c078090380107401007800c1c003503880b440c0101c1c01020107980b65a6400c58808001d20214000301501550002580c101d000300300311454900c101c0d031000e00301c074242502600180405020303150041401c2c040700e40042d150300080c9071042d000c2c0d00c9132907520740707010a8001500d00d2406140103107810160000a903032103000380300d425500c8102842e5103520034801c1c52081c01c1580da04c9031504440c600c42000d0340400c10362003580c112006a035815180394582c0c05002c152a001e603001070042e840950704000704031b54031000c0c03c400c1c00f004058820717a42c40358450584101558001c91452400c0c03000c0f0b41031182d02489540782c100303001c0c000b401c1035914012414209001c2e52048000d0192941d4072056210303051481c2401422454404540703e040801c0241d599800c0c9000071240ca40c0307009008a1800030005041040311160100308010f0703070354003a00c8001044003103040300c10341c071091003040c82d032801c050042c5101d0340e80d078440003802e440c08003401840354600c10181209880044040804144031500d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 389361133 1250 389359883 389359921
    0x20f0c040614060a0c0525090c120c12020c03041403010606091203020106120312050108030c0a03030b030705060301180c09050108070c110316090608060c0913020409110406020114 79
    0x2000d98039134800100a07200906000c200030300303034041e8507040d0035840190078142e05040d884030b50205000d40c498100c0d074100ea0074151180c001c105802c045034040032458002202648403031808a1703801d001242000305a03003281004c903101d5040401c042c04041038110301d2468400086000784046403078008081c09085043c000c0c0ca0b10a564a0190400c0c94000d4000900810b00c06c0210803104116044c02040c500b090a12803d409042000000d201040001a502030105003400b901406083c0c1c0d409500800710391aa0716003600a01e80002030076540c40005c1c500030070301000340c40e01a8a02c9606107040340c1e01c62040c0418030600d840184201c0c0d81c0305039020340c081101d041280da010700504007810b20120f200d1086134140b042442101c008101e0003007041c1104c48041041c400706031074042942c0c84600c200c4580c40205030510503040d052800c621001c8041340c3c2400c2c014035058503022003e0940b801036900704035484000504100a0307509116290201981680100b000d080a8180d0300030140501 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 389362383 1250 389361133 389361139
    0x102060c0a0f1206030b100312020714010f02010f0606020c13020f0f03060303070203060103080c07080109050307080319021801110109410606010905150316030207080703020f0c040614 81
    0x200210b0f00b400d000340d0200002d9500304075610581c3c80c248801030491080c07808110b03048950003101110b543d0002410005540040f008031444002c4400111011580042d0230300071992110018960b0035100e220b05406000981e018041c900a00c20502c420490600c01c817501d04ca00c1000030440720a50002a05c100344000340d04580d494913521300207895405801406035050003020700000801c0400f03401403044820b207409640d00240d44020301803c07211040b070054400d810405c0004000f5110800840d80130f80c52a1a08610981000c0c0740e500300d070041e81940c45084440b41c80d040c1190f030002060507040342d10340300900040d003c030381d6988092180e041c4800c405140d009a40309140d59200c5004e24880d40d05400e03080101000c2058590b103802c152102c13404142d50300c1010526042c90074161480441410310350380b030341e2240400c07040f91201704148941050303828422803000404d04802000f0103070080c0d008100c074a02920301c040c1442d40600034140b00e5464240100038040b140290105840300031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 389363633 1250 389362383 389362397
    0x609040c050609270f06060408030f0306061605150c04182a0c020f0f1005031f030b070e04020307020c0f03280b070c15091703010f050102060c0a0f 65
    0x80c40105a200088003466070004a6540803d28900e005034015803060030012040405e0761101c5d42404642c2c07103140503031072642d04108030108081131204001c541114010b04540d150818030f654008a070311240e0000c031016040900c03005403074200203039515040b1030f6180d1200e02d0030b843c180303600c044441001d400c04c08183e2a545070b07105500000e41c0041844219903084000c1d10442e1034000c000c0e4641a2040307105d040094950070b0641008d074044050f81102801345c0c41c02441441c02075440d500300408a04140803c2c10380c045001c1c074056182d00080d03205200702d0308641003010002d05000c021a41c081c0c000c81c41031042000031940001d1402100b601a01c5200084580385c000ca41000c403458401401c0c0c02d9490249803000d4202a00d01c56820f0003901c000044d0346405000311555694000007500e401204c603040040390b80d43d6803000300d000d4400c809c005041d030704407a640b10841d0000d0f0321070031100302c0c8000c0800c0956014450300c0d82c020441241350f442c02941810190400e43c22103691420800c2ca = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 389364883 1250 389363633 389363647
    0x30a020c03010606080609042a03060e030a0c02060f0913141302060d0e15102103050405100c23010b060705061501020f0f0a1a1e071b0c06080609040c0506 68
    0x5d078640e1241c0c0c270020420810304000d410a0a10264501d03071004858040c0f81c52500d04c100840071040d200101e44a036600c035406a801d8003085550b4100c8095104550000c202080180d92514010340441c2c07040000424100d01210614250341401060031200e00301e15035034040141d9849040361004c2e68035540c001440f82c107800c6007074508210804800410b885c003005100307206400425940c101d03234000440744811601d000c1d00c0412841103050080204800340700c240114940010001c089280300c1c500410600b186881d46407a800c00010f83c800315032182a601c400c850700c20f015100c0001820f9800300d207007450343d544482d42c5000041c142e8100c20a41d44844003917a20900c000c0017041c1c10281201c0039403001c2c2103034640b01d40018030219403031040c0c0042d824112078123402c01807282c13011011400b088040c47d210343c83d0180c4010603103800c22158540e15860f03421840d85010b10240a00b545a00180c1408000380817100c0191459108a45031010400004e2444000c84280c1d0002c1d034410391100c0e4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 389366133 1250 389364883 389364893
    0x1101030f02040e0c12070f0804110d080304110a05040b03030f130e0a02120106110a120e04110d050f061c0302070e01030506070201060f080304031106040e0702030a020c0301060608060904 82
    0xc54002c2000285a441032000310100d81c4064440f0545511700d107100e90711012425181c0c61450003020340810500c8000601040c1c0c2ca091002c3c001c0c8002c0c04000c8442a00da480743c5183e03004980c11034848540c079400c3c40280c20f04200507800750000340e604005401000b40007927928040ca810341068a040011200100d0241d20a2900105240b404141840c1440d03041d1324040c1d00500b210300444004400009070180c480c1100c0c010710f627000d030040c0c0b820300740503100e0386903902d03d41e038444c0213200a01c00011215100c6c0c0c032450b4588102034a001da105e035240d040c2102a10350141c131a0030340210310404d000003a5214a0b04100300502900014018955890140d0a052440e840b07050078500c008000001e0000201c1c41d24810b038469030003004840d48410040316121010300407124035a0081c0414000241d414101d0195a82c00900c00342c02c0542c0d41081c01e803807810071039260005802c045002411150100001c0e40d0341d100c124001c0c0040703400e00b42c004041c4d5500800d1940f05110000214081c0300b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 389367383 1250 389366133 389366137
    0x70602031309050405070b072d0f150e03040b1210051f09050d030509030c100234061106010b0306060f090409020a0303030510082407090909060f11071101030f02 71
    0xc0410742142c540e030003402c05002d0354030315150441001150340442102409ca584450790b9491303100000032595138640d1500c00c944013441c810520441d60b1403400440342241080540010411040d03080d1b941e20300e00c0c96400c4059009401c1d41078400142506001d55610380034842200606040f14849203a0200c8007212000c10715031003507030015003003961407050503408230042c001100142c0c21a4003000c1060180201d280d1401034610050700b0010000c2c1c03000301490b0062000b40003040b20180305400c40d40d248081112994000000310b00e05104080411609000c4140142041d00d41c0d51700710310b4040041076941c46100c40c617200000d40001c001005659030b512411083d500549445895922894040e000b0481a6820b440e60402e000000410340c0c000144036556465901200102d6003002070011510603010704160203000400c0b2020400300c400380301c0c1e480c40314051100841c41e40c4048048100b03c400c140740380c24401d030081001202040c441c985600382800280f07030003d802a48503401100034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 389368633 1250 389367383 389367389
    0x81b0f0112021204060c0519050c1e06090115180f020d0509060a0b0616060c0203040b0c0601140604080a02090a0b182403060403080c0d0501060f0207060203130905040507 75
    0x95480483e0340c071503031080144203500c0345214880402100302d000009032014010310520b4010030b8401d000740070310a8400c0018080c0e20941c0c03400c560704460516204045200020007502150344400100145464240500c2240710900c0810655842c14107014682c510041c080381002a51911113042e0004000da0444d1007560000c8800c00590510700c5500740c465100392214000c107420704241c00d0b440c3c5407100450b180c0e03141c07505030302c01c1e0302001d955103002030040094000c0550000307210000320720a07071500804010094034080d280d558148540c08044490018107607025260900080c400c0b1400010315140380341d0100d034040d04640c0ea013010003016051010419400c160310605143e403c0742100c4002e401100e105041c09224134525030148561074020807180d515601000102c2d01190091034a40d402c04010390295241008600c40701c01a60350a91012001134000c07003500030003550501c40d510190040c0c0c40994903101000207401094910390241c50b011a41e584003090410a04000050007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 389369883 1250 389368633 389368667
    0x507080c071109010303050703080a0501050d17071407171203010905061f0c02090a15060507031b0c05100c200f120d1d1806210f0106081b0f01 63
    0x101c1e45e1a07160062080d08008011000305220101003080c1e003a05000c0c40341644c0001d044804840e000352214003003003c0409a038100901c00704001808034090b003210302a07150020004000041c5051401030800c08580040825508040d8084030124a007108890441300080b0700465039850301c0000440d000c500e501b00001c160792070f000031041076400c580560ba0413402201e41d072046685002940342511030b00c01001d104100002070a1000754029400b61050714040c0c94400420805856045101254640c05032500d043c031800c00c00161030800300d20350303500f030f410b103490103100c5101e944410103004519440c003200440c0c0c036041e407030319203481d01074041100004000000b8174111403135954542034001003080001d10301c1c51511504191605c044405104003804840800507401c01c94044540701904c0c4580c0600041c003585400348070b4444203c15201c3d0180580780c462503c0c9210f41c00c41d00268046400c0c3d03084400c00c808001c220004103810a00d05441c0c03000494600f0f070040728450006442a40 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 389371133 1250 389369883 389369899
    0x81005060f031c0e0a0503030a0516080d0911060a0c20190e010b16021e04020c07060f0c0201020601050f030111030f070210021801030b03010b0312030412030507080c0711 75
    0x200c0009141c1d845000700b041c13511034a180110ba58140300180d0100e00030247c04d035104002c6035402500c01e8005000e18040e80c070001901100d16600e908050b84145054081c542d1280c0215061060102c0e60010078401210342a28000003074038007404450f0440c0d0301400f00e03250144550000c1c2180340688416080c020f1529000364100300120001802600581c030230825924000324110345c80908840109800783d42116000005608204c041c81c140f00e445050040401c000f203000740c840e0300150400b07241d42e202509650b030400100500c54502c24803110104144001071201503600400c1c081d040d075506407003510003850004042030140030340e200b0041982c200002005401e010003461580101c104d5801d403443c0324545400385099000b0788280642500b80c40c0c60000096002c0d038402210722402800201c0d2a110304000207040c000c5952a0217030b0312400108000c04c114071040340c0c100350501c60404200a041001c0e0003046c10748001c0607105076000005a21041c44042202c0d080d20800c0100515 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 389372383 1250 389371133 389371153
    0xb100801020c01140c07080d0c0309080d050702010c050415120e060907060216060e0f012307020a090c020303070507030908120c1005070822021e090a06081005060f03 73
    0x14000c10010708a4a1982242d00219070800c17912011114544c0d0899009820851a030303a800000300720700220b480905d9550780041d40003802c0300e00582500080c9580000c0d170751620007000780c01d42e211703500300d0800c0103030400050003440001c1880d6a046011441c0c5820342e25401d0041a006015111048065110722404c0060075003001500c001543c00c07a0b402d03604c101c040d045402c81100114044c0382c0220f64a1280c0440e6410425140c0d1100c40051400c860284569070a00c64a0305400200780c2c1c103a24001900003d41c01c1c046003000060001c03000c10042c80c034030541d000b912400041c4c92001000740c001155000e0610450600015105c0b0300c1c255041d074111403120401d0343e44041d1958500e4091403843c00710402c0719100341d5118062580b5141078540d510780462080c0103101403450401c1a04018442c00758668902c54480c2181e52044003803181e4200042050469009101e00785403410040107100e11030300420640300004c4001004038280d102c420000c5c81d8000002901b075094400c031403000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 389373633 1250 389372383 389372407
    0x120c060204031e0210082401020c0405070e010f02150c16150605011b050c1002070f0b04030c21060213090207030e090105120606120f16080607050403030c0b10080102 73
    0x1c42c50481c0b0845d02c090f005100000140c400c22400c5552002401d0083c01e018900003003150740300407150052064901e4011030400107403c4500507910980080c0e040c240c0c40402d96001748034020f80c11034500041011501003195443ca000e00103000340f03082400840e2109036518402c0c25513030b0035079021170908408403080300d070740780140340078800d160004602c85183c402c400341100221601c1c0d50007901411342c0102c18428007624248040ca0401140b060060000e0300c20001001c3c20090000381d03503c03540c0c407855030400c503000a0041d0400d6248103030034401c106107503025692241d50359600c00740c00340e118a440806544081c40560000e502c072400001c0c21030805901c1034012001c042c00311803006071640c80d8000d00005850311041500b290340018042035041c40c00c507008103030407602c80d02118803440141c0744c0f480c1045201c1c180c5111002941030244100351003442526031290a03803801c1801c1c01d00c0c54038020f050356801e4501400c1c00c8040c87c0403030004080040c07000040c2000c0c60003555200781030900 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 389374883 1250 389373633 389373683
    0x403080a020c01030612051e28020f12030a0c020607201216050d02030c03070b030f0a021c09020414010b0d06050d0209061c05060c0a020c030a120c06020403 69
    0x50b90000b40b5002c000302e0107134502616070845039048801042d180d0300388400c410071508480940310a40c4990b034a80c1c1e9051240d0383c240309c030440c070485100c14615218818056000d0391000c8152082a0190340040120000000d44090030002e2500006030364043c00400e086200741a0050500d4101c40c5043c00e0b800308a0515000c50721054929880040b00020890348800c1c4810303590340803041240e0100568904a40221a4503000506a40c1c00346100c0b0000b0b440c162055100d401600c0c40801008044014007450544c0502400c070b0a51401c00100030244030518415406600075039141030510a40d1115881b02040200651810300656111550229541c02200c0030340d030010304154000c02d840c1040c4450112580d03020b001a2080d8817201e0800119501031903000c41ca50300d21010320b001091007000720768011501e4a800c02d555002c44a0028201050415001d020303902940100000404000c1d01141c0b00c3d22524007079410851a1034410041d104580c000381090680400c03a681700031141d95 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 389376133 1250 389374883 389374903
    0x1005090403030e061303020d05071104020403031e05120103121112030603010605060c06060d14010501060f110a030e130608010204080312091605270703051501020708061b0403080a02 80
    0xc11240c0c40c1d45c50a003070194050302c8080c001d00580000381c8080c04103005401400046110b00900340250180001003012a0030a51066001900c001006074002d03042400c108180005442c103e442c00304c01424148c614101032000400c01c0001001c00c01a41c3d10a620072118200e90b0000c1c1c606942c0d100080d50b00c540c00c00d4920a110794a403110014251509008598000c04403402810803599a201000424103164005036503c0c0242c1b250b05410103420b1281a010300a15203070300c0311036003046000520700000d0f8880c1410b5588801250300203e6004074803100d500d030007101c400144141c02c443c054090002648000004d60010030003180c400c1010028200390350394a464040a541e814503815030b10221182884000414054280043d0510011020500c11119944005180303024015000c50340b04072007802c0042d03682c0781488070a01381d2240708040b00b08244010f024090628480b1078580f41301400d0303155140009805088000c10340c0c02030b10015500092070940f114143d15001c0c0d26009941 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 389377383 1250 389376133 389376161
    0xd020d06060612021806030a0605030d030501090f0203010b031311040c0806120705091807050d030302030603060711030a18080a051f090c030206090310020d0902031c050909100509040303 82
    0x58050014203000d2090f100e2440011714400c0d4240342410921607a50320103031100c06035948a950100301d0392800c01900030b55401c1c40c0c0e00021150714010100701201c01b05955140c0c158010401044000d000c0400e9030b401140c607a21b0702e4411000e03864481c0001b001e43c0f0110307800505100c0e901c42c0041c1c102c0311840c801c0f002600d664444031020004035483e98a20300440368042c0708c442c04a501c900c100820400c8101690b822034500d50744541c0090210303042c040b001c500191b000800c100320b41c241407182039000780c00ca00b0a0340081580a00f626103900a0540040400000030612101d10448a0034a0000c2172041c0c2610040842424078588400140120000b21070090307501e0302c2e10f03c0b540d01c0341500c201d4001031211a180d06560801c401039202c42c4c19968540300c0d801c400301101020348001d02840100480010301c0b10720728030515040c280301081c0d240782415020030402f45640c010044810a5104544c041100d03a20454564a02c80894102c6900240854100f01c20544c140d0312a0039000250 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 389378633 1250 389377383 389377397
    0x18090617120c0d08042d02031501030b061903060e010b030f0f07060f20010f06141c05030403060f0501050a0803161704091104030c0b0421020d020d060606 68
    0x80c10300710301c09101d2420440d4940c0e020050364080360348038145030307600144036040c1204084c0c0c07206a00300c00c1c6c0900c0c07032134065070703480c043d015004601e010003650203400c55034405001c41d585180c803400029900209440e0103801d06000702201c481034411000040c40d4007003401c2041c1500940710074024490300c810140230748030300c182c0741000c480700080018100700060000c080c00340c14050211007403030303685c104141805050030340f50904103001c5030040440c102600000562008810107030003502c2c0654020040b4030b801c03600102403904e0305c04a0358041e10300d0702c000c14440400c2d460964030b903100c0c0d42e00107000d0302e143c00c12649056600f9013001d412250200c4d40706007140d88594500740c43c0d20400300c080c0c041c10300200762800060000c1001100f980c0034a540309090590351f603c0c01050301d001400c1900c80550000342402040384046241001d0f0020040c482d043c00d0500d0f50301d40030003078001d0714840001c03e030005d4a000c5550f0150002076041c0d025141000000d042d140000c0500b44034059100071400d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 389379883 1250 389378633 389378653
    0x30108011a0604230d021e010f030c05220b12040c0504050c07231203100e100b2203080a120e0d0c020f060f0a09230118090617 56
    0x1c40029a403e0710940012501303510848040712821030202d00751580c00c07041d01d01c0c020b8096a20944150984c44844803441c0f80036142e00001440b0b5501030303151009152500942c0c0310f9690707008084e41c459104801d0749182c0c000140c01440022030156001c00203000d0006988808184014142d80c0100d219400740380d6016150702c02c0000796071003203812140203a028003074840031918071410814076440c4516042b80ba0700003501c019042501550480f9079107540003090081542140710200010112814155024105100c104200400034030420300c400d140411241050003402000403810341403560006e10392aa68540402c083c0c01040340d20004c951090030500c81ca1219000d811404140c07030018002d40d4419481c103031080c82403410166000094106c2451071511244004d0940703441000a90b5111a03035502c2c000d0a40305140c0213009841650218101000084542441c6031182420282403683c1c0480107801d600e03246500403403659007082400603080343e51684070003170713615070380700f652202a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 389381133 1250 389379883 389379889
    0x702100b0a030b130f020301020301080109110409030512150604031a070c03081321270f06050d0209041d010f020909060609010512100e0601111005090102040b030108011a 75
    0x10303451102803c2c000c0c003200042c0b0038810050701c1000441c400c42c5070210600700c5030046030880c2c000340c001d107805030354400841c03090124500d0782641c50700c0121001e0103c0c00e6250342c02002c0e40500c3d56072030350082903900401c01115004900030540038020309039039143c0340e590600301c070410001c03e8400c80003090f05010a804c94481c203c05002550951903100c0d5a841f01405280e207121014010380e5002142304403a07184100c8110fa041b0b10341c850355140f058081c004036111040c080c11340d200903188540310408122001e01c844e880c20880300542441b9403900008294600a489594440c651040c6081d0314001348070f4070b2159030f420310a0380350005c110b881080c1c00380700c080f4483c0c220003580c40319400c000508940317041001004524810324019003485038940a04a00103001e581c0c3c1562091031010900c1449480b03a4140c0d4420024a420a921221b010310203407601d0b1f6011550104c50744170340000302c500340250100c07070090110b0a2900d0703507580d6404030240200400b65828445400c46149407103580f0b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 389382383 1250 389381133 389381149
    0x40807030306090b0f0f01120213090e070e0a0b010c020d030f080903251e0c06020606010302190309050309060406030e06060607150b01170a050f07090617040611030702100b 76
    0x44d0041c0032079003c2c0d00460b00700110188481c40203810464103107441c400321101800506148051000403900700c9040c0f031282d00030707524402e281c1c20f02c503072211800b08800a60318080d10b0b084544014002140b84410004844404011402a4104282c80049402c0590040d04030f2044c008613a120406515211a0366840c0e1151044020b102c0309403030064044002c4000705501c086102d0704901000144980085510b226489415508a00d101d41c04200c55a0188110360f0b00030800d00e0110700d000c8025040d080d1841195100504159941f0030400400c41c003001100c40307c01c4000e1005840d255a280002c0203441640c4029500d402841c001c00e43c542440c0040e9081e607a4405215911184a1480c00e00184940001c190401c00c0c1440080c0d000c44c0d2040f64036003d03400c80c1201040324507001c1c0010640010140080003080f106400030080741d9440001c08038084030201000d44283c039142810000b415502c0c46400d120780000052002c0160001245a102d940402050100301c0d25001000484 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 389383633 1250 389382383 389382401
    0x21060c02030304110f0d031103040801050702100c030902010c0f0309091509060e04050a03080a1e09060515090c070f02090106020606030f01050c040501050d02130312030b06070203030702040c09030b04080703030609 94
    0x4000700406c4000240a490388400c0368400c401142c4c14159103101c0d09080d00c4050300c9000168005d10f03e20310244469003e5041580384170700b01800f5800555000070001c10080c840648070402c0442c018003014480c80e0040020410704000b40003055039a07214140800241c460001e142d8907062000a03c0c003c280e00b4148503d81103c0502070400c0c00e9181514826030041034041030a40c1d403003c414142018a290240c1814403420005a1540c81d1a00c1f90440d040a4072031205030946001c4a5041d555400d02c2c036501c10031480c4419100c0b182490300030788408841c02d0095000448500100700e00782d000880a100341412011a10704044421140c2e007218000d449184241c1e004100a01595006800a080c001d803050801482c00c001900c480380c00d0040c0d41c008943c140c1801e01e4080c1c980750315008104132524200c400b945802c43c1540000d03039a00c9000710007401141c450050707200b1107025094100007550401403141861a00785402c03c41540402c20450100385040b4010034104a1480703842c0741c1c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 389384883 1250 389383633 389383639
    0x9070e0c07030302090a0b07050d09082109010c0609050109020f10120b010504080d1215060e0d0f02090a20090f010e030106090c030902030708010e0721060c02030304110f 75
    0x1e020315640741203020b50700c990440c1ea0068403402c1c0024080d4804001064101e0085018000b00c6817102c2004081c5941940408804d601c06070559640301c80101400040030640b9022940d201c000310300607513440c000c1c1100542005c0c508110b000910130107401c00c0f001a88220b88280c001401c0908001209c103240300b000c0005501c0d44548a5140c020342d0240100701c1c1c05041190a0071380c0ea001480c03070b050364450820300060f4484e80f5550905500d00405055400740c4500085250810100408119110b01341c280b103100704a020005001d03000200c51034081c0c01070144500f52514941c142c02806c84c3d00303418500421041a00d51a000401c02600c03c9010000c2c030301081d0894000c0111044441c2d00074680d85956902000104800144207040c1d11030180d48001c603003413005004142c1007185960211200b07904250911050707103000f0601d00142e84645489000000940c440195031600b5268002e015030300d00b0106996494000001c1e5201341c2c07107000702900d00c07240b0105000803000c10581d9030f60 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 389386133 1250 389384883 389384887
    0x1d0304140a060815030109021c1a0105150f0c010c0c120e060403060506030c1002010b090c0424020f2d0c031906021908090d020f07090c03090c090509070e0c 69
    0xa801c0804c0701c0038100203001000824030503110340009540c07428125542961800d02c02640040141d810101081d101c100c4060300059807421010a074040c0f100d440c594804040061500c540705e2045060b2540c0d20301c084001c116070412180d025106400c0c0c04000c2d01c40c0c0c4440546180740714824140f544846d50080c001e41c9c2010318559803800a003001a00059042c050045040b4490f2151510883c0d84201c542c004035401d0354030390a100a0410180001c044c00c14104000e202c400c101d015130240c020040030a0501c05441c0000c22800c04400811a00c00c50140c0003003d610402081c4c900300d060440c05c041a05941448244144d070740350654106501900811102c000d107040000342c0d46400c5025100c05458400546030540c1041c1241400303a0201704c1d01400c3c04400f0604000000c42150140010603024001c05007180d5510f140d03214540181d038882484400b42c5119811a0701c40e01d070f100305003d40180d243d00300d000c00703403400311103082e0b50b407046500010740030803003010060140c001c0d80b01c954 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 389387383 1250 389386133 389386141
    0x30903021005070f112119080d0501060518010e01020601060f0e03030715051303080103082a1b06070209010504050a061a0c100b061c1d0304140a0608 66
    0x300c5144407003812000d1007003c0c081c00d0301150302c41d80360b06885446521030503039540c00e43c010401a00e03044511012151014450703442290800101c00c003440c9200300480007400103a2402c0d40142c800d10b0031300d00d48542404000980d0540100107410303039070b2000301c80c02240703480d030001180c000301c0034650180144d0006004210706800b510035800d194659160643c40d1011803404030340f869001010440d405aa03078071048076620382903c90f00c0c1d042991084070b0700c110070494400402c0407206007c0580440c60020b01e101c50000448130906070b20405c00c80f90001c0d441607000c40e94850305406415401d0401c1c400c014403491810300111900c46a0040030780036642d0130032041c0030081c400104100300c0340e60f507000d0124024102c44c00c0c01000908030188982d84902c00000e5904150081e00026031403410550608515030b0b840c01901c0031401003e400440265628694074081c00c0d281c0d80000c1c442148079401d040c00d0202200400a80707001400320340602d00f00c0014048080a18070410340001c00520110b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 389388489 1106 389387383 389387389
    0xb030f060402090303040e0c09040608010504050c01050301061b1505010b040f080c01080606030a0f060f0911040e18150a060306050f071d04181407080a03090302 71
    0x540c00c01244202080d40c0307001c0c0b1f01a82070b1009129001446440c0000c0c05e50301c09070780c000d00c24020141c1d140003c500822041d034090300c103405124403c049550040c000c40b03048440503170780c050760b0341e034031000203c1100092002101c05000441c12050350180c14043c0314040c09014101c50380d42d614005a80b03030038070050f0784000c150750001281600240e8010b14001c1c0d1100e001d4400b0340e501c1d680d00c05c0400042103614132061080d854408042445108091803c2c103503009102e0802808141004181c02402680b142c1c1041161042c0020301307840c0103580060314040150216644040101007445001d13000b03c5001640302e681d41810400e02c0340501a07990080400504041d85090643e00100050142058456a008a003101800c540c40e80c0d4404000d501023440c1118046065141000044004c80d142110300d20a1907000320700c00f840411028410381c1d04d034440e100d5062441e0f0038 = true := by decide +kernel

theorem cover : BRFrame.Cov 389208633 389388489 := by
  have h0 := BRFrame.cov_init 389208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 389208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 389208633 ≤ n) (h2 : n < 389388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
