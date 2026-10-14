-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1325
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:23:02.394162+00:00
-- url     : https://prove2.me/submissions/3f57cc0b-3510-46d9-b449-495267758f2d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 238129496 ≤ n < 238309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 238130746 1250 238129496 238129519
    0x220c0306090603020a030b07141603080a0c120213030f0602030106020c06070f080904022206080a06030c0e1e0f040209130506071103040503010e0c0901091407050d0b0a03080306 78
    0x720011034440b480080c0d4070944140c01000418100700e4001d402900a2414a0030a003614803903030b920f98440ca81e82d80c80e4a040c0b01103103091591050342641c0040c1140401d03c9200c41c0140001d11414210768004901b0780e0000d503014050644224a00c0116444403901c0341c09015424040000e400034412030001d4047c1d480044841c1c40d0038002c0780c403090b40c490100004040c1c030381c0b6011215004070740c090360026400c0062000b59091584449031450800c0c41d08100d55007440710040450380c02032b0450010b68102001400020008807003007050ba040c007000048250303941a20780c50100c07600d100d1f0480031420501030104000c4880c0c0c40e548268000d13203050340c007511240409110b1a2100e40058420340280700030030f50342803203001e074030110b001075104580c00c04c0c0c2c641c80000e007103803e40303245101d10f640859181e26040c00c10340103150060510707050070061601f40c2407003c40b48440080c40107007000030014040080f5265580420f1103004080c10442003d40c80f8030308030140394001d072070b01480340044110 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 238131996 1250 238130746 238130759
    0x6090312031f0b07030c0303060b1c0c05030c0403080904020403020415080c19030b130803010906050405220f0309030b0f04050c0d050c010513090c030b011d0a060806220c0306 77
    0x2c1c082d085a40c0941614580801a01c1c219409503003001d04a04051722040c0016400c3c4118003c1c018440a040e24618880e0b2511400d00c11101e11021850501806004001c04220100b0643e0204c07500070507165603e00c81240000d000303106e5030300000e6000d49010070400f049400c2c22540c809880c410070440e10f400c440c80d000c00c508070700c00e41c00d04400054512801e000141c0d034880c05507001010070b034000c68250b00715920540260402d070070400ba42c60f5074101c204000c0c42c15024250f0060a141000400c2884507070f04411950084040501811808a0b0440030180300380819001160401400c003038900308a0a0203600e10740c113a40035070b100d101e0910302981a02c0d1400e40f229a1541c8034004149074003ca038015603850b0007082900a001031b66410000f00040540200c01e68200740b540c00283c50100301d40050880700ba401c0e01060019110954030032503885680800040c0c610710305240d04603644450015a45403d4031164440c100c202c40b01c441e040086980016010080303a440c24048142c4a03c03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 238133246 1250 238131996 238132051
    0x7030c15091802092d03070f0312080601110307050d081807180b09010807080d110c01030f020c030a0f09150212070f17030f0a0e030304110609031203 66
    0x100b101410811410854201255000300741100340505880f401900518000002103d40682c01411490350310b00c450551500313100e201c0180120300304c0c298400703080d9141c0092030059104240d00f40b2000001183da81e03805000d122104400c00011a90b03140721a1401680303417014103103c800882c808001281e0310b1201d01c814000031014440003040003c0c688180c4005c2d010114030104180741c2d030317002d4014a03615008001c0b40605440d4000340141494000d1451400c10001d542c502040091503a2280511001c51031010542003443c010444985c68544003009210303042354081e140c8000145400c100da0403000c01c3e401c0d0305854030343e05001990348220850441030b0941000040c2c02604014243e00d890310040c1c0981030042186103446a020317924008260f01080e0000505500881040f40d4440c2d00581598007410382c65090002d101800051030380c90001030802004005140c010500c0c0d0b440d902c0980320780480040031150245460a050b49040c3d1055894082860110000c01c140e10305c0314 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 238134496 1250 238133246 238133249
    0x80a031e05030424020906180a0503010221060f060d0c1e0f2a0b0a0b0301090201080117010f06140301110703080106210f050708100f0603020708090307030c1509 71
    0x514000c03008800808042d051340400d604291640c4c0d0b0038451a0b85030784440015104180c801c3c09400079091036002007145030103490744100d100741e004009078010304000b5260480b07468501c40303200340c168582c20001002803a110114641100011804105050041c0c126101008064495880c010000544509200d640301c0700d180200341140049a0300d94410b412440000d00c41305441e4062001001c440c03041c0241c0b02000340c1d00e042d0302d403080c84018036043c81804010f910803402000041d503a0f41c000307401d4507014425424048607100ca150f494500c20f4000d040e104000c0c600800005407181091100c00c4581c90185009600c1c01c40e001c071046c1036010440d4103164154540c2c0b10207038a002411500c414521070210601d8080b00b1840840403803a010720511802d034204003090034030b4501ca000b048500005d1001402c240140000c10214400b000d10605407501e918000da500e1040d030520040c02c2c4149070710f058261246150010030b00c41000007080645501600c051030129090004845403182c6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 238135746 1250 238134496 238134503
    0x1c0b0402070614182e06090608120313030e030f151503061009090c12050703030e06130306050601020102121f0b0a02070501120b0409060902040b010c0302031b07080a031e050304 78
    0x41d075400b0740185c1503070011070381d092400140c0041c1070560290f203409461981c1e0152032841e4540b501405400018410034541844803402c983c15440e100300320103090b010300c3e0b0010307080c081c000015034280c0d2001e1109400000c0100211a026080c1d02c0c3c1d01c0044101c105c0b01004c060034402d002c0c41603172a02141860103465070b540060041800c12400310000c00840800b140d06183c441c500044201c080400004660300502c042c2030b81c40c0ca10708014084c550185007451181208000d425000c1f80da0740b840c00d0649400503800902c55940c540180d00a10801c180d110388030103200104050f101343c0c0c030031401c891109604850001c6030348004002081c05030240c51030140e0008802886103520440340c41d0200c5503400b0000c01c0d5800a03001040c100d039498081540c4158544070711100307505041c0214418001d00b860064030368101038034001d4aa02135076001001070591005074003042d81041101401038020003003902c2d81a8000c0c40e020b041c0c0c0e042c0c1c01400000c0280300354001807442c06881902d105a40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 238136996 1250 238135746 238135753
    0x109050418060b0a08120910030605010c062c0c031006051c2603041205040b0d1a090708090c0108011a0a031415091b1c0b040207061418 60
    0x300342d42d03600c06880d02103207803138101e150108000b4a00c3d00400860a0341d03103002150765900c0100005004440204603404e6049c1350501d901040180d92041c020044140c01202c00074001419035804480302e803902c2d140c03141407540700005076031900002c6114241d407042141240d540150004244083c0d6034140314465200006600f219161b035940c6090300c1da05845144824203c1000011100421003110041400c0ca03002100300804c01184601c0c00c038580045043c01814140b400780340c0ba41d544900c0e022107140035210610030701050b544000120802c080148610b480380707805440100321540483d454030a911414111581c1d03035000da4003540c140c400500808080084058440000390301a56642e4201907072441076005100b61200800c0c064803d0b0079080c158480c2c001c04011506c1c0340a441403848066890608034644009012105682100303040c9880008030240b042009003e0490f4154001d400064501d080004a03800011070506400708c016031500c0d080079050245a0160880581b80d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 238138246 1250 238136996 238137041
    0x6030b0913120c050f100501050f01021507050702120102040305010506011704410f010606050f0a1b06060b091005030f06040b040603020d1401110703020c0405100e041101090504 78
    0x140b09010301e00c18107004d2011690300d244400f008500e070000a41c08480b840e03513601c00510540c03074141c215001c2d0300000d03c000c081826054040d440d01c150080d00200500c40002485c204548800040f02e195080020007103449a82d24100320b4040d0000f224441c1c0000d0b110382d0b0050304000708280340341c0034a41003000710300300e4040000e8480c0e2080701c50600e621280b401c1d1001c174101e00c903014110f0960103400f2000d48800307256524079a0940e41c0c0741d0045020b104c0c0c1402502c12040d450760656403a2549894000c001c282191411040c3c80d0583c8005002c0340e08212022a0031a0700c80d008041c0075405075004040c0101005080f10300780001c0e9107010782e81d071444000c2030452a1a80200105210040c0b0000b070080e03480e4002412952095030464008092006000310325000380300d00031003090b50070045440c1041c581d80c000e4407070440f0112144a2030340d800208240b044c11f200b281c0c0c043d12445818218905107400c0c40781c040ca00c9070404034000350b44298041004d003040d01400c180c580401d802082c0c0701 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 238139496 1250 238138246 238138283
    0x5030304030305090f0f0909010b09180c060d020c0303070801081605101101020d0c11010e1c050310050d030c020301050105190909140a03080703050114060304120c02030706030b0913 80
    0x241d181070b0700c3d15401042d80c8001983c07961481c07e118000c40540d4000103944000348140b10000d40010180c4010682c400c0b14140751501c04036600e600514200c80c0a503559000c901d07480024054410560b041e48004030030010300a40105245040c2e48000003241c560b40e80e00482c8120f002c4075406004d0300039000a4840d1512405014103c3c5401e4911001508203940000c1250486400e45100760010301841ca0344c1c4007640b004c0c8251140f9806071000b51139030340703020f0b4240402d00598080c02030070010008005003c0d44405000030f0302030311009043c009809a5805c000b0104503162206a01c41c0d481d0070000240341c540301c922564080310302a0681011441d104020004060380c40040d502c0c1c00d0085e00d1240d006c001030250724203452194456100d103060000c00102140e6050f04056040744c403280705601c855460030150303a407050344001c824540824410040f02c0c000784504000f50140b0480d0b01c0800c105805400040e1420811b841a04850766181c4000001071889034000c0c2c030480700341c115400c0303a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 238140746 1250 238139496 238139509
    0xe060703120b030f0d030c080906010e0601084b0f01050d080408060408031803070b0408460201230601050403081303020a0501020114010608091e0312010503030403030509 75
    0x42c44401025204240000d00d92103040840b03000114001030b03074401c0450001500a9005608201c03000010318042d03041504291015401415a40c180151140014120104119111400396281910043c010306e4412080039070010070443c5074072258052518912000d021400d50705c00ca645020800059107800140800204110020f030b40b84441084041040721081040301d0045114034080750341d902d0000ca10143c0041c0340304e1410110b4004004110104042014464104e60007034580c559596900c1144200500d01080d054041c4495246d070710407030860595050024401504040c9102101a40c22422100c4400500e116550f24200c3c1ca0200a4100c80490b03001106042c25803400c2e40340d0f1540300864000e4450b170660140341d024140210700700300600340c006007000c1c0002c1c0031401c285081c849200c07030705004000070480d00000094140c1c00400c0108040141d600341040c6c1810500706031500c981c4140c8a6a240c070000500001d22420300000301d50840307030140d039424103000d41441000300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 238141996 1250 238140746 238140761
    0x14030a060513060e030307050d020904060e070e0f0d0c09110c120a031b0e0f13020c06060405010b131a0d0e03072a03080309010216050a030e06070312 66
    0x10588200020640040c005100303540c00344102820310400c0c04643d15100d001d9640c45a4000003541050091064054001c0d065030407a400318038000d80c54129001c04900204003a9010700c2e80c0b0164941030101d19030f00070110382d400c1c40055426103d884940c40901c40c0100e03121800821050701c100040100b9545a0f01014499030502c04152800340e822000d14030b0940103500305424620002210a000d40d017610130700d1741c0d103414120b0103084c208908030041c104c3d2000c101c446002d000643c02e0140c0039600c038210300071004d000c51421525610642221a91a0001c0741c034180518501000440c000d03190400b40e400e04118a406985c1441c108108410803001200c1003498407081400200020b820324094069440c81c800000c40d16540c1e01d0403c00c5100040d9607100804626000324034025282006032882540d8100d00e81c0b0b0303500d071a0881424020b202e800c0340045100d50540c807200406c0404600a20080d00a0380c41c502d20300184001c02c540c52040d02c9000700860018a044c18105486400c00b15 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 238143246 1250 238141996 238141999
    0x20f04050114041a031807140409150204090b120102040e1f03080307080403021506030705010f0203040b1305011103031306050702100f0204051e1008060d0507090b01110d0914 77
    0x1400c00ba61a03130001d2800c401e8800300145a030000c4104849401600407030070351400d44000500d05189040760010403110b007a0035050290307466600810a0154404244911780d8042e0401c550702d907a41d0016000411078980024400c4403204890240d900e81402079800f034521190070100703503032941000d152801c00e40c8005000c80f0709019000001084441c4081c41c40b941280d02c0f809240d1070036160003800c0c00c401214a10483c0150014401d141c1c8000030030704103603942824a600c0c030080d000c10603880c5000e5a400452009400200c24500c1d21080315400111507081c0c84a94501d421181d20603201d0004075800460010800000360202e207994100310341118260044d500a0200d4800b9141030381c2c00710442c81c0b40c05400107401c000f01d0a06c002c0501c40c16411a1004040100c000006088407280700b0b002400c02142c04089220ba80d0303465000c101c50b981c4103084601c3c5541d10555540508600e54009002c03403000300c1c2900a05c40c020414a8444046581d00e09059043c1504880030b41131180e80c06 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 238144496 1250 238143246 238143287
    0x210e04021c0513060203040302011d0a03090b0a0302040b0309010e0c0109140411091c020f01111203060103180506010806010f14100e040603030305150d050709050a0f05010e04020112020f040501 85
    0x3c501003041440158000d40c02540041030310100d038280c4800c0d40e45100000c840c0d903031040d61044046907115003428141d90b80030310303032544e254200c21049029000e607401203888007000006200c201030055000f5100702ca180f2080c0c0e1005030710b510064615202c244100c12403010b002c04480928a0035502031000040ea51809504000244000ca03408401d411714109200c1d40d0903182c44254904070341c080210b1402403070080c0020358104601ca4444c002d03006072142c0008040003044041c0c1c06508086020000e26005040152160410554a004c00c7c450400c880c01490000724004040301d089601341c50744002104d1840b4050020720084540d454115070030031020400d0105156030f98060840214001c0d500030070a400d107814440005600024134038483d04e807440704100080c0010551400b182e06100c0e000503150f8808202c100a00348206118401030318110000c666400f049015a0041e4001c0c2e994000d05040340502108900c6201d4520b80d5102007440100400e41c410801081120000240c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 238145746 1250 238144496 238144531
    0x30c0a1b0f0c05120a0204020d0902060319050108070b16060b300307050622050a0303140a0902012304080706080402090a0501062307210e04021c05 65
    0x30988000400d800316038a07410480500c05200c4281c4000001d03010031034010000708165042a981d860000764005c0c0103a40100b001c040d034443d0751b80020095900a818166031349442440c2c4007200b41f9600c14447ca40d03142000101c0c0300c510000e040c0b81230340c0cdc03079018461500401c0903155685089150301201d413907072600b100200f9038880c2c86940b0100040d0201d901d00b603001d040c407408480d40c56405c0d0700340150300500400b40441d60003c4d810340c0003202061b00301c0c816801065001e00547d40c210015040303208a40c0c0c004101071f4903030f00c117a0794003514681c050802c0e16010321490544a046101900262401c034200d03d58034161035903510f404142d21500c6103043c0e0741d0444581010f40c0c0e0b6200ca0042103001040009504044940e644e11504000d0b080140b50705084001d00b1201603c164410164482d16091440717040d40c0040315001e0f0b0b000404c3c1981c4c50300010511440416116804000502880040740b0506250003500c2000c00c040c08840e0748101c0302a4403000800d40202424001401d03540c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 238146996 1250 238145746 238145777
    0x3030d050a1b020714030309090c0a110d08060405070e0108042d0f020f0d0b0115110f07061404210602040b0f030601090b09030d0c0201050d0e07030c090b0303030c0a 73
    0x4400210142e6009040c1c2c0c07618240d94042040e6a0300c40b094040c0d0010081c044041c1c0d61642c010313900c07898040d007032912502032a00c110707007040300f0302c44483d40d510412070008091a000f11109200303440440d0300b400a0303554403004442540490b010a408144010040342c001981c440d9081031402074461700e802680710342040800300e90420700c1c0c1510a041e0a85250307042d4104034120384419401039482c1800e0030b10590301d8071002101407017441c0c2491100401b0101442c401da084107018480281202c04480d52200b0041c3c45072014440e0360003180102c030991068041c41c1d004d480403202511250b00035000902071009140042000450724282c1c01c020100309500180050110003100d101843e40b20704d440d02c00900005250340103034514600c14400f1212680e0002020040e06040b80750410852502e0301c0142d500d0702441c9240d5040d18100741c031601d800800042c803401140c6c002c01d04100220350b101241011206034100c02c0e505030700200002141d1210020080c800e407075071460410104503200d03c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 238148246 1250 238146996 238147031
    0x5030901201204170616030908070c08100608122b02030702030a0e031b1c0b07032306010c022202030f06010f0305060616020409061b021b03030d050a 66
    0x16102c00b20b0007040c14098002044d030440e0391050000300070040c074104a00080c0300707401c03000162010540c60304541001c00c00780c1c0040d9010b907071340000882c0e0b005403101c0102e07494003507440401e07100c1c52600100003000d440007d00890004200b84c002ca103030410071200e03018804c017002c0c00003041c48072101c01d00450034135a03c0150f10444c5d80b41c0c040c40d00d4480d4150001c12081c07010200380d219500001650b4000b1104003140200c1820407611000d490855155000007241860303400b400740854035081080880e096000f84558400262005901c00208282c044e0304003000d0703c916001070000602003006003404403081d4000610401041480452148268143e900c216515482050b088c028000c3c1560481c01d0b0404007005c03030078140010300e0100e02041581c000d10365032030001440301502c10150348640c0c0c480c03c03002c0d80220042c0003031040c3d00308841e01c0214024201c1d0051280382c0e00032030702110416104404d02c4000b8080c0d031401c038034000c464019001c048c0034806015956215440c0f030103440c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 238149496 1250 238148246 238148263
    0x1141f1503090506010f08030301060e0301090203101a0105070809010509030a0606060e0f030d1409011101061221170a0b040c090306050a0b0d12031e060e01060306030503090120 78
    0x903a00482c0040541c0761a0b418044182c0c4944c195162240c411b10008a02000392130543d0a00d107000a81c0d034194000184c003601c3c101c83d000c0d4140c081c040e2051200122030300105012440640c01d400d2603981c24004645612500c030001c0d00302c642c240515441503100c0c0b0014402c1110003001c03209540070980760b0a044400a5004102241e0f0320010051141090310031160b01030400c40150100600c900c0700074000740d400034240300366980c0c0002c1120b200d82c0984040600c19a041008010b52503c07000c94810000c010802550001d03a074004202d413004800c40050745a081e00e0742da0808607140c00f00c0d0f43d0f032007001c00780240385080e80b01c480c00c290a84070392117480c50000043d51144d030080d1450421000310782c4094040b204040c10316100602a4841d59280c5a60075400f00030561003081e40d540c103c00412001d4222840450310005120480c5102c1d0000d40030f443d06102c04000d40c1e640c4550513811a20030380f00081c504d0700288480d07140c075030240c2d011032071901d0410a44a1100c41d601d41150600c40007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 238150746 1250 238149496 238149539
    0x1206010e12061e061807050c03040303080603010e010b06040b131a0d0b060306010e01080c040905270102031b0702030c0402030901020c0106092a020304090504080901080901141f 78
    0x880208a81c0d0f1020b181c80c1e94201e0010728144000381402004902110b00a0071840c40c030150110203e200c15205a0484070f601c4000020b0701c0d1220b480e85801410054242d48e486c0c441d600300b8464003088001803094201190004003140d183c186030030014003550700425100314200d42c600078001110030889031103e0a0303038014481990380b1480d8010f14401ca9080021942c080c441c20b1007000b06a9800c150b00b6800603d00f400d20b40125a80d1000d08000352003030740c1007030302e059040c0024081d0000b086402d00d003003003040040301c244a140780c02d502802c138002150040b5100c00c1280840303c0038900c0000504959002405030340706800c44001080070380c3c0c0280d0b40070300d03117a50004880361840001e00c20070000c0c04102c0d800740602280031413a00c04075001c2306502041d0110290100d603001c1c4c002c004071402802d07100340610441c507041c141140c440d0040f003a00c60200c0d03542e40018a141006105088201002c41841441c1e0f880f8080480b8520141c80c0b80700000d8549841d0103d1344141a00158208455 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 238151996 1250 238150746 238150753
    0x30d0203040210170a1e0906050403080f0403020c01050c1504110a050301090c03020405060105070b15010f030c14090402070803010906080c06041a073011121206010e12 74
    0x1072a105004801104654980802c140c00c8a011011a200403a051700f2a82144010961904040055a0807510391075030150701840e222214042005580000380329a01a84410140d40d440c0320b80803a5a900890f002001030700304410b001c040d0340c0140013801040c0460350495001d400940401005103809440a480c50b03200350b131b0b80a4052500707180202c050807054009020300b000c541e54400000320a800001e211b02d0701c4ae40061001d9100d0010b860340190032648c0c056a50820070810485405000901d50010b1103c10400c502a030082c0524102c1103e1039480d14180040c550034030700b45800413000c480e405030b020800e5201158003034010710b010700007407640090098078060f800c518000c441016140500c1051008025990301a2540c00410b40100c1700f2070303030300c100030325002c1660340b0180d00700d0030310960600d0661040580111000f416045544400088240d007490b1169610712200f01105040c200b00480031010318810400b0350000018108030001181d00070000c2c3c000c0b02c190500c5600c40c0e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 238153246 1250 238151996 238152001
    0x4150f0617030403080906030c0c06010b07020907030204060f080907080706110c03060720010b09180705150a0c050c030715031b080a05071e02010609140c0301060f0201060503030d0203 81
    0x482804200e2000751400441c50945581c2e02e540301c9004070094144102000700003e41582c80381800c892000318403900359400f42da11030303207140e00d2500001c009a000300c02c80300000340c040c1d000c0d108460503120b0580300c1784007443c524401190a040d00500c0d0407040c0c0100f40340020f0510040103e0b6014080a407903da404503500d0306075910780110510880c1c0b00b940900180104c198100840d0000340e8a501c07a1000c11384d54901059000d480740c100e10903040145072041180e541ca02c481c1c204088040f070021340750215556401c000200b80d003003016464810b4108001c1d4041d6004044611400d803180d02a141c0705ca20110010f0305007030440d842040c00790103d5102a004075414400c1d07842c640e6086800c01c03919a80440c2c02010007030010030f01c2c0e81c0b5030394a8000c1401107018540e0711000c2e20200a29884031115034500a02a2246108515486003010014580c0085080e07280348941c411001d510b003035a00e0110708554058540d030041007555a140d0b00418540c170705200811500d020400c015a0b03e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 238154496 1250 238153246 238153259
    0xf0103351801171005061b03070303020a18030506010b0d150b031801020309030301150513060e0f1f03020a1103040e10080102090127090e060405010c050703080402040504150f06 78
    0x240340c0c0c00c0c180e00040a1050070451011300a0300781d101a80d005481d155103848416924859240c0f094030192003a10011a00c6030402d64950001c007109a1035030740740c02034641c902000d10100f20b0140002491030304843c00520000c2021409008050030407800410928903500780c03d9055029074002e1201002c0000070400c2e0f1710300e030790082c4421440304002146107161900c0d036182c5900041c000c1081001c40c1003070201003d0310610a0340e00501c4013071341003110995901d9026141c8000c0d00b03202800744c1050070f194641840c043c0c1d9480703514180c44440900d220780f0480100c0013035000080000602c501e2407501d14004c03034208080d00241c681c0c019108004d044c1040401d00104183c2c3c0900142e0b0f00400030314038941d91100011010106040c40c1008104000741c2180b4210082c0c0c0241d40150710341083c054900305c00041e502d000c1c40c06003000b0485052080d1044510340319003140500410416004140141803d50000da8881c0c00741c1c074042003032800e010101341030321403500481050b151210b50600c800b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 238155746 1250 238154496 238154507
    0x110108060a06090b0a0c15090213060303090317070b0106020f151302240d060f060c030804080307020a12020307050f071208030a0609020f04030b0f0103351801 70
    0x50040314881d90941c5041e078010302040381d6001e41d0711440400301d1100041e50182d4100304560340d020b030440040340d400440c10341c000c207103107503050b446024001003c0d95681501e00c5120213a030303010b41d500c00e500307070450303c40008403510300b0007a504c4a8020401d00740400c030349420084c040d00c61580641840141c03108040e1428202e5074042c841d80305043d0501418159030300500481580c10b50300b0469282c0d04c1c003c50f081d2030142030000c2480d2240090611a1007402c1c1e4400303402c0d5800c418240a040e5101d000840c0c4214100c0c800801103060000802d004c50f2884000c3c0d0780c4400355104071000071266940e8851090010140c000150780040707a50000c10806002d0762100c1c1c6009002842d02d1454030707000c2e43e104c40c1c22a5000c0d09481c000808507015240b6a0010030141480c0380c000c2d55523030340d200e61001d0a58024030081e100c0e00480400316041307121040301d0714100c9402c80209252070031950700c5100400c40005132841c42c4040c0d4a840b01201040201800c1c0c0c01c0da9082c0040c2c41c18400100140c103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 238156996 1250 238155746 238155751
    0x9090f04030806040c080105010c0f0b09070503070806060a0b160f03110f010506010f03090524011706070f030c030207320102030c0412051002030a0b04180f060f0f020403110108 78
    0x10031800c040345c0061481d8042982030442d002441c0c940c06803800c90034044101c5001c41c40c082c08011242041202c4c26100098032411640c040d4200c0e401d060b5982d003895242c0f2400c1d20000d0b401803103910f041002c92030850261860101c401841c419180c1c582d075403c8428146103a003240440c902505d03501c0f02c000d00b4040c803004840b0000c001e120518190700002d0024000c03004042c1031555403961402800010880e240d0b401e00c038483c501c61520010751000c070542000340b0400c120940341d4080d40049103408a0f00d240144c42e19100d0401801d4441004e078050001c11000c00c081550034004d200101e42c100b0544100034025142010320024017006c042c800303c6010010782d40603030042040c81400860f82c401c48048502c24000310000c1102858002e04141c844a42240d1860005c0103002d00b01d20198000c9003c03082c1240d003008501401c101c81c99840490040c060400300c1c4a2140c200440c0c1150081c1c000440074942c005900b801e180c02a04c00ca801a801c00c0e214641ca039007800542d940c121030550b4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 238158246 1250 238156996 238156999
    0x6080a0f05190203100f0314070f030803040f1106031303080105220b01030e030c0c183d0803120708090303070c050a0803041b06090b0d02090609090f04030806 70
    0x4000c0c5010000c2c00b45107000c1d03400803811a940080051010541400184c014007080c0144c140d4a69690404124513030110840410074000c1220010310a011141c0150850354460301450641c2e685881b003042c0144210015180364008140101d519510b1000a6100e01c0c03032082850200c2c511810000c21003441600102c1c064003041c0316400403c50081d0714000c0d250748000020a84510381c40040380500302c0f0801009070352102140081008001182d186a115000c1e04c1004a6240e2212140d40e011000e503627401242c400343c407014440c0c11a11800c405101c47e40712088100076a0f4004407055403510754408041c903000030070034481452111b18231036000360451910030784034140004031a4070391202400c414180402c06684c40c0400809001c0c00d0304036900410070355202e00d880c0c10109440b0012461140d400f518459011030340c280110120000c0c1c0d09403415031400c3c4010000c0450003580a014040c0e4060000d00c4148100e99503c504075110764184003034000d05092a1402505540001d050715 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 238159496 1250 238158246 238158251
    0x41b1205061f14040b030d0801140402030f060f0301091707050c1e12070519052d010e030a080a03140109061503050703020706140105011808060103020904020a090606080a0f 76
    0x4200c000310302c00c0080c041d20842d403030742c9401030403000c0041d00a22a120316203400d0f000d1010b020070000d800420881c1202d108400200e1a41261000c1000f28402142d00c2e201c0700603940045034890608400502d9a40b001400000d0042095250540907160140000481c4000001c2d0b010801c070f000d01840a0b120b0302500c81144150407401904910454070070b100e03015500c80c0c00d1480840c1020000e42006202c080c04543d8a0b23032035866031640715645805014042d0b94449504030000350062484003080146202c101c8a80d60000f0044a484184500e2503501d80318602940300840c104e03070028900100c6a481c0059019040d802e612024501648800d0f0300038039010b010070001000640f80a01c1c000f091800003250b40e00c00c0b1341a4002d02920750041c110500d01303031000d4000a070604040d0705845003626406060030701c0b006a20003642d014054800582c0084004000505200c0400c3e0313045440281000c9a4036240c07828a0b084807a82d610a00004d0300c4001440b903d14054030a14140e8511510103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 238160746 1250 238159496 238159531
    0xd05010305010b1002010e0304090e33010e1005040b0301020c0f030301090c0203070c0e0a0603120c0303050a060503070b0702060705030d06061e052205041e060509130308041b120506 80
    0x245d6849000e544110880e05d903e444903c50f140c2c405111602d071044207440760840504c03e0b14442065680c4cd160716910383c441c00800410130580a800040c80b40c0300d04c0322000d114504080900000e41612800142c1541d0280040003901c031707007031189004071540782006540b00e40c9006014000d0382c2d1200000340c10340d0030070440180418140503080701035407224040e02280ea100c03540c03510300030507180e40098001c1204010748001c0680c00103803401c1203030107581c1c1030050f920b500e1959400c4801c180301d8607615900c55402000305890071005403a1682c0001d054500300803503600c440e815948134010181711b03e5070301e4500b4010b598014070038401c0e00e641107420441d1000081405405486803500d001100711100c0b401c03440c1d5030a00c2c0e11610107050040c0091105e44145141c11100e100000b0380304840074200103010549040c80261588580484d00e0500c00b420f0a0351019100900085c01c281d400440c0400002e20890412120400034a0341c2140d021480d495410035505012002d084000b802100051 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 238161996 1250 238160746 238160771
    0x806030a06020a09050901120b0610050403030e030102090d2f0105090108040c0b040b0c1e030f031e1003110406060206061512010e07141905030405030d05010305010b100201 76
    0x194240d03040c0c0d00140050303854000d8001030300c1c0320700c0590145501c071025000104801521001588002c1d10920030224580c50b01800c0080d100c40ca016440000340e002c1c0300030030100c0c0c0b04170380450b481540940018030740300200380840e070201d6000800b52824500e0040002081c1524102d81c100b0480399000040c0d610442d900083c006c0c451544c00c2410448000b01280603c200c08071010000d00e40926110341d6035a40e08084903d94120791401d031818021a0711440b207100d05100d40420300c0c84800090751a08040c0d6800c0746441c1c0001e002c2000040c000c80100c152440c0440b64a406000d101d41c02c01d0f00203180d450044042c90071341d80c01c030f4051030070920100403031600000c01e25001001201ca8042400145440781614000e00c82242e0031048040000070302d07140361041450140c0807035941d138899a42000d031094403512911000300b02e0030400801d00420207100350090340c3c01522540980703240040d0002618259002a0420750f402d9641c0d4a08080503d0008109280c000300c0340002d1144808406 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 238163246 1250 238161996 238162003
    0xc03010605070f1e050105160e0907200109030201052d0106031a130e0705060301060e0405071b030207171f090809190608010b0c1f1b0e090106080603 66
    0x19002400e504480c0c00341c40420410701c800316180004c1c00b04200690916080050282805641682201b810407502e45015441890001c504071800380404019407100c82c1c080781c40c107801c80903a0040b04000341080c554034100f8002c000429001c0d41c008100c42c02d0251480b5201c84c1e001410b21064180701d42204d0902081142441c112a154107002505800e10144050301c804c0560809901800c1082000c040881c00e601800c010a010740c100e99100b51120103114880c8020301401d404500b00c500010032505c1c068000d154089102d1411302354400d01040b00d950560b0b43c00004501607001800d051009000e001d40310700400d142c0e10010062095400041ca0303d207603407005041d44040d11910a4400d1051031000c80f941c410000d01403407032011480c60548500d032840c3c041c2600142c0b440000244030341134607040e03032941a4214043c10300031a1507074400b02c0f0f0b17041901ca00455580c6a440c00034040c030700d14814002141d01d50b182d40c1341070010704040080105050304440b0a1051400a00c10180c4001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 238164496 1250 238163246 238163257
    0x9200f1c020303040b0a03050c0a17070e150403060608120d0c05071712070e101b05030f0c19120c02010c0b010b041410020d050c1c12050f0601020d030c030f09030c0201080c03010605 80
    0x10b5a90072f043c0d4075642e5045a018212202042c1c00044200c0c080f0444000000103204990280404100c42902c44d400c2540320548210088015030092020309c0c80201d499000400101842c102103140203002d80da01c003030116102211001c01c2c000030450341c1c11208074102da59070101c103078a08030301c041500300c00242d900301d16480300d24200011710451780403200c4041408040c842d00401100e86451000b10300c81800e5000c00701048282c010380921400c0d4009400784980c600f50710007614a90324000c14801c030350f6080000001ea04020150100c1da010809801d220350192540240c441c0e550340c1002d41040090074000c414500410160043c83c0c140d5501241c5010100107910f03107e6a00e0320140e9036107180c10320003078a018004d4040f1020802e0075400050003420209030060901c01a0744803a070203a80e41c0012a10940503811251407224030034400e0740700414103140350500003210314610101c0411110b20f80011000300c0c207202042d206660300a9020380d84007042c0503145155604003d0000c0490050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 238165746 1250 238164496 238164527
    0x10e0a080d0f0318051609090807020402030a150609150504081e031b1f021908060a0305060f07031506050919090f09200f1c020303040b0a03050c0a 65
    0x81074040c0482ea20a4200c800f030103208108040e130061107810003a03200c3c020304d000d000c60540c441c000000c150340750340140a02303182c1205e003c3c1d0601b0304507024000654001808400c406a40e001710ba501240c900d0001c1740030300380c0ca075290104a07061003c03160018802c003c0d00c50900006100400100c2400601c9079400c03a0080005401003e180c0340e1036141d800390344031441c41902c5904a80407075510000b000c95806801215488660094042c40c0f012886801100944140550f01c8203210720300a5000ca90040e002034000141701e40e80ba00c929051050560b04260490340352000d215442d5410302869038100c550056028419146c698040c2051044840080c00b846107115500f600d1101034450100a00e0400300500114010105000003018072800031981c8010043c010010410307d49500303480c012000d030410300821103020422031481e090f80d1984101904208404005807014005400208003a0f14041d40b123080300c03800507080ea070004188401c003040c2032202d2350a0581c46003241404448 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 238166996 1250 238165746 238165757
    0x18061807120c0b040605031603060617190c080f0612061603291206010b040306020702060405030d05030a0506010314010b0a1812060b0306310f03030506010e0a080d 72
    0x103451400e110b009015a000010003080803900242503a045401103114018441c00c0700c42000328a001542112036501441000441e000c0c00c0c200b01c500b640d000c81e0381281500051601480c103203120304040e50041c0d0b08400c0020740500a1108101654030b5003a000030045039103030180840024215940c007002089621a101442c1c2940c41444c004d1f400f400c071102c001001c407010711808084045900c610440b031035004070325003028070050184c0400c1c681d040c0c0e607200304507a00e040d10310f4503018080c1d00b001805030703880fa40410000605903230401500310840710503266952640780980b82881120001064541814240a40600000140b1007100e0541d243d05903803640342e214144040390294000c920b079601503154a4408120410f20b203170600c40103846104180282e08441040c5501c3d201c0607101c6414a407816101001c0300ca061090f840c407880ba0500b01c9003902d0b40a91144011054820010790100760f40d4028004996400030620b507200c00161410f00c500761a1001c86d5503204034550b514400c129 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 238168246 1250 238166996 238167029
    0x30c170f06131104030b010302010810030506070c1403030a140109060e040f061d030c0f12160f06050c070204050105030109110103020a11030301030c1d010602250e18061807 76
    0x2c4594408114940311100c0d0584480c0c880c60210501c50003030005034041001200003c4c002d076125503108007030340e40c80000382940e62500b50007680d01d01c0b920803046808002114681030610010009103214608423040440c1d021203250705103130f0450b0181c1240440c01d0510400307011040d4000e0b00720741c1041d400480400c40b140703d0b080143c001c010600303c8080c5035000d0052803946110005c060f0298007440d600f82d0f444101d002c24603e40d42c5034040307800210a2401d0040d289650b0120b049101000c2c0505000300b02440f41d42d0302c103400c07110111065600008003044080540c10319114542c00340200390000c21a4610344e07151320300c1d807130000c800450406400003540315500348141c0b030860000d9620000c0b00c2e05c95844e80307449080c480c8140204035a0b41c240e02c0d903883c2200240482141207420a030054803504801d5020580103803408500880c3c807200100000921010701c00381c080c4180c1c000c0c0c040c1a10403440c1f141c000e0402c480074110400724a043d04691080d000c0114000080b01c1103134285080c1007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 238169496 1250 238168246 238168279
    0x31104110309010c1b0201080105061b0f010608070501030603021c11040c0e090604050403080f0a0b09010303020c03070f140d1e0320030703080114010c02030706030c170f06 76
    0x103200680d01000340c400301006001c0304601c15000b062810744542ca8203c0b298204a00b60000080311443c0a0b00180482004104904084004181002004a00e80c400c081c1c0c05d48001e00c0c00070820b0381e00301c150f9034a401c00c1100840a10980e40509003d28081c48414030307680008810b1102410f504014545000c011020000c1646486141050180040c8124241200301038141102030030814011004800010308030314007446198440d580c1a21a510541c0b21201c1801500c08001d00c450603039540c0700403004040d500c8000e054001c600c00c0d4010500c0c40c112000703250400d92241d0100d092615800e00034003c0110400b5480026841a210407540d0201070428070342005004498400c0140040060000e15a10500409040410240e0038007040080d01045036640b0410001400045102005020001400c2c01e1047c0320781c030515207007400c09142d8000034140116a4400780100b82d841103100015070f049003140c0c0c2904000c3d298a1414a0700c44994120031900400c41c600c24096492000c044 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 238170746 1250 238169496 238169501
    0x30c1912091d0612190b0a0902062b060b0c0d18050402090123130b040302130207030309020a09020d0627020306060706060b090f04020705071401170907060e060f04031104 75
    0x1016003940481d020f161290405825000c1503c0003074401100307420007d1a241000d001e480b00c0c0310380c05850580f401d40103c141041c0700545c46041c0a182108041840da4015607016810151025000c000c0c7c3c0c60b0341510440d4a0828060306d0902401501c9a042e02d407148440e141908460003600c000d6034680304200103c48401500e921040e01742900307400040416040c0340584108a903100c06503040d1034a032942110715004501c4002e51123201c00e000910340c450150007906002d0f200f8200030a22581907030001d00c0300800740d080b024440b5804122004110010300401c4010711035078201060100e001852508100100841d00710b085800002149468899004454445400c1101000394540b5030b00700c54000d80c03281d24030310320511850700320941c24901442103602c00d55000000380000c41c50651082141d001d5032440c98140060081d003010080c01980019101d030340e450001e42041070510704041c0443d005955000c4c0105e0041c40402c2030010b0440c1240c0a580e00b101c0108403091080001402 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 238171996 1250 238170746 238170769
    0x111b1c060501080106050103060e0f0a09060609020c0d02010617060402190803030a1b0914120709140a0c02060402011d0a0504020a0f0e060306060a030905030c1912091d06 75
    0x10345030000003c1c0940040d4001400c3d03540903038082c00350310b43e00c1100d0384140c00309a41130351000480c8800b041940160b50b000140d0030384103a001082403a90740b0340751400c80c0c029070302a407140c0d00300c0c40d02121482c1c2c3c28412500940304408120007000c40442c101c43d507420b4000c000900504507640c034141600f25a083c10300040140c0b8044941c0c0703140000e001030162604d0502a14204205d0340d206820b01d0145801c4c10903507400350307414254429098104000c4001c0b600c4c1d440820b008260703001c00e5401c4503001d548100340c0c4080c000c21035401c225030b0703c0c406c0306c0c2e4141d8001e0454002e00103200c0183e90010740c5050241d54a054103900b00c1003030000134100d07038895000c03560040c40095030900701500441d001d0074488a030b0316100000d0000105220052004880c441c1d440310b810420002268040d5000702d070554015811a8240710000c500d162138040b00b403840040044500c0103e00811451400900c20401e1a280c81c085081c40c114201d007081c088100c40e4140413440e01c1c001011900d4a071162070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 238173246 1250 238171996 238172003
    0xf030711060c0a141b310f20090d08030702010618060602100614060c0c0d0804050a0b0a080402210a0813081c050a0c0c0e07111b1c 58
    0x1c2e42d0350080c1c80c01030030002502e80300d00003a021780c00001580d00045403c015038031201820f0f4003840e15482400e02925825040085081a0403401d043c81000741b0344600301c0c0800380000d000442c503449400d15400711601840030040c0f500100820700c000c2e00c0301c004400c0f0455200403826101e03102c081e0300fa0b000d0281e5402c11a480310820340c2c107885c0241745400040440e8035580a48200c0c100c0008200c058076814042e00300c5404000300c032611a420010010152081c5110030355400400010004110400e0306c0c1003030310044c20215040c0000d160850600008010030ba4109190824048000c1d101000050010f4890b070a0b8000c51840680c3c5646615204d8115105a0b00b0301d03440c034a001846500180e80b6120234107130301103007ca0221000500407000410706021049a000307403450444455000b0f0110310f0812402c40000c0d000140d0040c0300c500900b10f080f6040442c1d10341145d00500e604020415400135510015842e41440c0c92020308106400d000c0d1403005a440702810000105810603a005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 238174496 1250 238173246 238173253
    0x1d030d0c0f06052418041203060506071401060e0f01030b0a060b13090b0a030c03080901180e070212042306160c03050601080607091509030f0308040b090f030711060c 73
    0x24010840e04e011260302900001402e00e01d40880140300f603425007806071906007244200410041166645d0308a081009890041034490300e500120b1195000740c4412500300403000c02c40310760000c00f07004681c003809040700c480c182e520344510464041001807001819030410070000c10040601038101c5406801d0b1135503180e03521201d12031021150a120720400042a20f080c0401c00685460030181c3c040341c9e04942c903994200c0c207503180c40d100c0390310000842d0b061205602a102c102e0240c580030070700030240d0640065141c0b601d0034003e418002c0c86041e03454034080070072041c440d400502160310110034082d468100c00c140c07104c01089251007030121a406e0a6030441101c01003084020014090340c1c0b084003500c00c141d9032100b80f142d80b0001a1520400710700410400c0c070204200c1e461800401c070321490069800d81d40c0352902e2950a56459083c0d0000700b00c0e408000c2407106d07800c02250880ca000300109003074040111003640b640201399005140d07241e110201d8071207695140560f5600041401074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 238175746 1250 238174496 238174501
    0x140711030c060a0c0209101a031e04050f070b07030906050c01060306150612020f07020d1104050c04090e070807061209020306070906021e06040201260c0405011d030d0c0f0605 77
    0x2504d0002c10080491040141d400040c05e40c03814844070408649428980300e510b03e29118001210b50401042c4450341440c203050400696905400f03640514001c03005081c8210301c5455007420800150004421071608003c0c07030740020361052201040341d41c9490000d442d1041c480806000d070402e0352014091604041d0145c82030341300b1090180071101d0a0701c5d01011040c0b0410440c0030381c02402c0c030f20240c0c400284600009820132141d45051140716450701c034440707088040000c044450903130300141c1c0d030000850284501502441000811080c0301300910305249825100d03a0b5511080c05010300b0804202c0c9140600502d54020980c3d0940c001c09a40c10380c5000d680050102599100304401445031001840300400c40300c5040000f4145107014004541e1590015150358a031042010503070080084984020071015049030f00a6041c0d414013a075032031030440010002c062a1b80c80d020b11480716840600161350004110110204504003070601d040181410400348400341c1c405400e041c06c0108 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 238176996 1250 238175746 238175767
    0xc160503090102070504150b0c0a0b04111e030618030d0f0b0102280620070c0608090d0210050406110408011428090203070801060f08010507140711030c06 68
    0x505102002a400c40e018130f5610010881034030b001449805d0003505c0c40c507050042c0314441c0000d14061000c00c04517080c07103481c0c0e07440c1d84407241c3c2113805650070b0400b050381c0d00701031409c03400030204102694200240480014000790b01c95501403e0049000d04070083c5103050002802910740e5899058020400c021000c507840b4040c04400d514503005000b0412020803c44803202c4a1800c88200f403020310084056565000017881400f41903110b031030000f984c0030644e0034040c1c000c01080340f20301034180e8039034a4900d010302890805007001c40190005100000c4041c0c2c0050340c41003400c111200412141c4480c10a200280f8100b0b102d0044540300040120b82c40c00150015440d059002083c0030580daa0f4144104ca404091004003000e444840100c0b211300340c068004087e024001415038088640d20040c0b2400c450995200c0c4d041040540310400c600603080c0f10f80d581c402100d0802d0066841800c440200c103110740c09006080b206600a080341302e46007004402d14041c0090800740d5035140710b48 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 238178246 1250 238176996 238177003
    0xf064502030a0c05070c0303030b03010b060706020d06080303090a0f02280e01050d02060313060b060a0f081510230a050301090e0a0521090a030605070207090c080a050c1605 76
    0xe40c0722142c207081c002100300061090303040304d4050f034016004100207811950124050601400b42c1079156488544410072551190b00518080d07120350001652000b20000c050250342c01907103c02c4854209200b0050300b01b8012a0011b41c0380d900c034442d40102222480041d90340d03050000700c502c0b60320b001e080c280012080100c2c4a002e40c0c0301d01221325442c0c1e907500b041203842480008000d4100300180046010100c0402803600001d11600340032400e4050b241c0400c20503000488064001040100c6e00c18007a90025081c41d084080481c08034003951802c0c010500d40c2d425084901c04201284400c07004000000441384003a0000c080000e0f5160014003005185030000c0c00b820000d1860107141c1c5c2c0c0b002c0000101410080d030b002016010b2251501085a01302040710368100e0000c03c04c020001c4c80355030303400c0d0041c042c600c12040080c4034100f503a40240741a200380c0028020615100c01910402d0704152640d9000c0170110010034550340d850300a01c8280070750740b8020103d0500f00c400604012020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 238179496 1250 238178246 238178251
    0x12010207060e060c0703051801030f0c020606010e0604080613231b0907090501050f0c1c0315060c0b040204090b19050703020405130e07030816060f06450203 69
    0x1042103031104d8440c0a2501e8451280d0940140407a008003c000058107151108013144e5205040004440c008003106d001030343c4040d401400140c101d107080010940c3c014840c805014002c1e1006402c05081c404840c2e40c03950081e0020801030710003100c0f102082030071040041c00250540002800e0302a07105003540d12003401901c80e000b17402480700061a400c151182c5485803120350f95940c0041d00c0c000054660368030144454400400400003140085000c04c5161a1012101d030038038074403a1300b603030000c0458264444002c0580fa608808001566009012160841d040b000380801a20b89200240040030001c0c8005c1a404201082000b820480d41604c1800c550034101400155103181c8110100d00c254087c442c4c1c44050740044071004c1d14258440b071f14001d0b8240132518841e8407500c41001c07603000b4800c11048244031000240400c0854020090861002d000920029080001d4421300c2034280742240054241003801c0c083e1180015001c08030401034504103456080c0740100d940296004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 238180746 1250 238179496 238179521
    0x50a200301031a070804020108090712050705030705011425020a03060504060c03020c070e0c2104030f030b0a0b03060d060501141906020309090403020304050402040906031101030606080c07021201020706 89
    0x35642d590703c400c2d00324440c10b10803092a9100e03640c6135515030040d80c1c2c0c2d410203080c041d9144201000440c00b030b41074201c1d60b000540145d0092070301624203000c141c940401034000e90704000e80d40341c4421103101d4110a544015400c2c00d41581d140000394812001491003100182d07001c1c908082c000107208050b44014061030040c0c1c000d100c00948500d05030180d1103a100013440982c40302104020605039218515001800303c0e4145190070142070581424400e0001c0c1038401a0001007800308141e080b48481217214910b00f024801d2a140100003183d00190f480b0b15543e5540000001d070a90780c5030410441031a03032142d020401541c65003044100e043c0010070003030050803824a40300780d40d25407811500481d001a40250b01d4040610144880710034090b03c120150311042c807010880740e9071400504054030440b60002031251035800c2c400100c0d072840c0042c50525240c00400d000599208030070582c0003441451240d5601030501c0840c82303901c1d0b004a041150b5101249070300c01c101494001c100d80161 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 238181996 1250 238180746 238180763
    0x5120d020c070612050a05040507210812012c061e0d050d030e03090901060c0828030609020a0210150305030f030f09030c10270308090106060207120204050a20030103 73
    0x15040d00c21004c98000340c4012700950f000d04004c1118030142c9090507209030b042c2d9600c00600c041d654560030550841c1b224910f241034643c0051041c64081e8481c12046010300704000d9014828110098549102806c114010b12030f081005003003404400c01951800c602810512903209141411519207c41801d440002401c02c0414440c030349001059a509030001000e04420364a0410140c459959902040318818018003140b1950004085100d518420030003000c0c03d140107081008044490640112481c948144201d03441194001344401c000b181150700094508040c828022085880d540024034600c0001550020380303140a005d1800340051051105884c3c07140440c0b00c2e00c9002d04045010280d010b0300101c480c44900780c01c8200071070b140314103c544050958058051801580505a01003480101441040c030424410000102018400b6041b90303400c0c25050541d90781c080c40064812034841e00400ca903418554800c0f900c405864402c42148900b00b00b040e161030b0424403003a2500607 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 238183246 1250 238181996 238182001
    0x501051011030d0c03090803010b03011a040e0f0414120c01150e0a0906110a020313061412220302070303090b030103080910020703150f0e03040305120d020c07061205 73
    0x1e018685044100c0c5154010b1400c00c1c103001d404100030811041c4140c10151204240000f0480660040d0301800c0c0c842d6079655a5070400c250120083c2030108900440101004101b02ca640e5024403690000003880b048000d54880b8107165120300c50001e001c142901500d1062000458900c00902e00c9100540007849900b0340406402c520035401e1041e0341c8a180d011f030018200d0f0100d5840404840d110729800125000c5201c00700f580d40d08042503000140e880082c44d142c6e0071007100036050041541b45000c55890090f0348003004540242c0b40d400d0310000060021851280c10f6261900801c0960007040c150301045040080d550540da1005a01090000201040340070020045030b040e603401207081440d042030301082c018807018052658045001d00c07500440094400740654800741c868150100d00c590032907080d10119600f4680885031940100010400107102040000c0c0e1500c0403504241ca03a2540244500644200200c40007603024642001c280c180c0c0010f03200345080c0009a00704200d9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 238184496 1250 238183246 238183279
    0xf0308031506310f1503090506040605060f0d02060d090f120c14060f0601111c0e03010b0406030b070c020a0b04090f05071b0b0c04170303060907021209090612030d050105 75
    0xc40b0075002c2c0103c10080030505010051724207030025a420001c1c5800199041d09896007800c00400f074408135115030f1980300340200c40c83d000039081104081102c44281c80c26480d0b001405501ca01c1c0202090140c480d0194400d002c4802507030385415420510400d081c0445450080c190b010f030003411515041c0da200e214032114000941c65200b881c241c035802c42141c682100645185c0c000c074480303c1d8584110303c01e00060300c66800d0056002c400c1030b20340e4140000003a04150a41e0380e10740d4064000c91610307a080010030f5008980701c0d003080e11410b01c3c01110401e40081502a441c42d0001103003c540050001028102c56004d0208000d03179060802481d04c400710101c4004178002040032041104504503000b1401e1014a150002c0750508501c0c80c0c5640c2d1305031440c489040310105000c40d00302200700841d070308000c0e4082d40d2041051001d059544120004015940030f210f059074040c1c0004000198240c403070440d00c0b60313000b902500300c030f44a900060803c0c000d0442402070a000320300540b07404488 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 238185746 1250 238184496 238184587
    0x3011a0304050a0215041e080c0d0308010302130905030304052d0a060f0204091112060a05180c1b0109030207060212180a0b2107090f0308031506 64
    0x142d6001000c2d000781d04040e020400707200710801c03900f10414010000000d1044903850f08010921840080d407200c01d00d000229030a04080a0b01c1c1d40c090546280361000180c0c1c0722141505603681181e2100703e10245d12803040003071412102c01400342c40700209001c240940094094020381da00d5800c0c070300c0b09050341c0b0190030803008142c00e100e26602001941000901d981c0040140415612006007016540d41d810000e540e02e20b0702c01941e9000005030b001180c030201d490150302400550b004030030140f500c000301d0f5500700c103100807005000450b1302040005c0c0b403a4049811402c9100c604c200e0785801103000c18028550b80d03101720054442c0700310014182c0d0000c14605402230840c5080f50800c05000b039120310100c01c0900156100501c070070080741c0404404094070003c501c00b100a410182000070a8942d910050130071002c2c0000410308110210918903c40c1c1501c0e4040c120b2a120707100c1469000f2100d903818400c550141000c1540c2083c82907003560541990701720340c940d10000b01748849034110b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 238186996 1250 238185746 238185751
    0x2070e011e03060209041b0903060f0501080604030f141209011a0108060f0307030b0408031801060b1903021b0607030b04090510051f0e0a050603010209030d03180c08010203011a03 79
    0x1c400007604020804200680d02420340858041c1004c140d043c80a141d800c40a5040003013070002c175060283c14400d00203103204d1b0705842c00750040d0070811541050301941e80e510000f4801020046801e07003844040b4458ac2c500d00501103803110150703d400d44014820841d090454042c140781d0718000c441d60008210400340c55a2041c1a1605411603d8000c14400c1d00c42c44c0c8092180c01d0700c02c031400040003842c007036a005d20881c05510b2503500e0381400e07540742c1a03c020b4058400a142c1c1404c40c2409104202401c0314800350303e0460180180450f588190080e01131810960494400126a8a1107401c08103a0034820110f642d002c204920682c1d04100441c0c12440020300f081d0300504940b0b850340c0c2c59901454020a41070755082e604219050743d200024034a40108070781d8071400d010b1200c40140c0740203c5400c454224025030030112080e0100e640c99503020411002c058860021f40400c2903620b0500e802c40341c00c017407101070841c3c950030014046d5100388030307044014040d0718400c800032140074290f90 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 238188246 1250 238186996 238187039
    0x6030a1a0103210f1206120609020901050d050d0503041103030a030603021c0b040602070519050d0f0503240604080708010204180204051e040212090f1c0522090c02070e01 75
    0x8040d020301841207800c0c84045d0110354800784c0e140d6001c2612989040700344000c034410340380884c01e00700c50300c1400b09100040e801940968822451000015408113000107205120314060381c481e0b4032810141c0c0c1303503030001d08110b8040c080020781441c00b540c183c0041d419640241c4000750040e03500c0300c600c0c51620011902802c00e2460354080380000d0907580007403500d140a00116043c501002c4070303a80d01c2c911007072802c640319031240007c1c3c807501e6081303191888200303001c1c10b1090641c46c0502c05c4000007010b800316102c4012402054081039960f442c10344015011010881d06501d07210f800050007580315011b04070500510382d01c0c1078a214a1070080b81c06403840640301c0c118003890880340f00180951903c040f0f9000380c003844010003c50544c204c1510a1003287c00a01c07030003119034a01ea08040030b00d500d40380621a148108040150030004031240d03c040c00407208105910301c20064058143c5402914400d400d100380d40343e966900048041c01d84414885c4203080c2d9995240075070241701c0452000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 238189496 1250 238188246 238188257
    0x1d070b0307140f04051801090f050112030f090b0c0d020f0102090f0108040303090f1110020604020f0f030309030a0624050a0e04020f030f1c1106010e06030a1a010321 73
    0x205010b203030403000d8060035039504461070601d5281c0740061010140000307402545041100104000c5200340107140c400e036102101080316504060b000481105130035400b500388140c152003079030741e40d1007145880003c110240c8010780794604200142d80721130302c0f40c400780011b00ca00d0b840803042c2003042c8225000b0940042006101a80140042d903214200030000e40a040c0d072142030b540440c2d10f00c00c61000c1c0910a11056070014284820000c900780003040480c01c56001804000068542c2c4a2000c4c517030508480c8808031030038640001e03107140301e40c1c5000340e054010840d8820400100743c0010000220000800211185016407410162403d1182c15880701c07207045d04028151000f40450740050000c3d2000445042c0340c00800d2030700c00280b01d80c00803a400140680c44c06424624030040064540c034000c5408407240281c25580c14044c0181b10b0700351074a5010884903601040302c841810b600800c4064130580030f0b40d803184540b20912059841c035480d80c41903000040400c0d100c80c4201d42d6030329030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 238190746 1250 238189496 238189517
    0x3270a170604061d01050901020a120903080f0907091103010e011205030304080d1803080601021009020a051002160e1f0e1b04090608060103140616140d1d070b0307 72
    0x301e2003e000076564034800310400c901c02404110080c042d5902c142591400540d88032b100040042011101038148269a468500b91600096000003010b81141e1004201c2c0c00301d031205141107062040c190303c00c04030303245064030940f0a9030015014504840c580c00840c1a20307030780d8221100f00c0d1801a43e00404542041001500040c84040a0300c000d40c0300b4400099007840c08845040c0703500410005030f0115083c01d041020560b4100000500000320403424404e44109501281006909000b868400c1e1107100b1001d8503e40f08115003501305124010800ca84c90b5074008080344907000381d4211075114001449107440203101d00c6081c007281c0d503507043b040940e0350321418000e461a840c240c000ca41c9104001c005180d448a000e0f4a000d0a8108080c0c0110752641c504422040c01015981150307070032040410070712400d0034014000103103141c00c0907408004005d410241600c1242010440d903890440300320001ca05194000381004000c2046178102d6458100d1074040e0301003255030341c1c005543c2241 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 238191996 1250 238190746 238190753
    0x120412050705150405150c07050105060319020609060d1506030c1d0f031c02101505010f1202040b0403030305070f020604170903070801050c071a0601050d0e03270a170604 75
    0xd410384c4070340078005580d002030000c8408510703030806a800306001100031500d9070070b0110a205042d0045801ca0007840503101502d800c82ca004006000684039800120b20000503484120171640c00844840041000d041d0704c900c1d41030031400501a800011b0301c3d21415010080c01409100300040d444a143c8201c15801d00c1000f42070301181070940d405000f980318841c12995446e00d0f08985c1d2040f070b0041c101c0c207020410490129601780c000d19207048046841080b007030360059600400c0c101c0510f001881101001711480180c0300f907910004004200050000a240c2d143d4807550080d0160381e0b0350800f2211080080365125419078001c2c1030010b01d0980040317200d00300c000410100341c1c00340507038014564038160319085403011240c40c44030123400030380a000c00018880050301e00c0104e640c00d07119800d226000815a0213501da00000c860f9440c4403000c0040d608009664a03007884d9403c164491070301410210000f101132081074041c0c2d107441e401040c049203904e00b40c61040038078002001940d9403502c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 238193246 1250 238191996 238192033
    0x90e0c0f18030105190c090e1b07140307060606080610050a030b0604120308060108070806010c080403020d050d08060409111509030d021f050603061b0f120412050705 73
    0x400c09110706000004804058034207000d0948030b0780016580c4c24074500f84e2070388042964540d194450401035190824001c035501c80181d5504151000d0a9101000310381c1200741892050030b81c040d14414694a41c0c1c07654410000c003c01c269072041030103001903030303a410741506c100034166031495101d01c800d10307103540356885080900a4490380c0e10340814224000b402190481d030054000c4061101c000440400703040e040340d4081c0c3c01034000c2c64051428600614001c0054030050010381c100011000110709112240003618055600140007c900d030002d898115a1102e0001c11600400c50200000e4400d180c00e11440e05959005801c13184410900000c010260a1450019072300e0034080c080401a500c00300b000f402c0d0100141c00070710884001c984503581c144842102c1141141c10300b801c00880b9280416010b40003552000c07200814000c1d1018984a40a01c0d0070118a8440119500584207005140700d8082c60007480300e2030a1203c0070000710740c640702c0d43c3e4000d0042ea01c00746e0032007201d06508 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 238194496 1250 238193246 238193257
    0xa110a020a1104110c0a05060c070503070b06030a081b280305130812120a02090a030308130605070905040e03030f010620070b0a0f0807020705130209040203040303020703090e0c0f 79
    0x41c400140d500051604408030381103080c001500d46e006281d01404c022081103070341d03040110002180e0600d0410f035901c696900c2200001006030031007101044450310304000a20011b0740c840394007a1608002143d0041003240000030190b41d02c60095600d03018180864040c03540746003020b0519514055460a0313900b907020603015032032101501000201e240c0244803440b0143d003000019075496010320b84d8a00d60b900080c007024042403041042848540e6202c0c030ba80122036060621a16582c0e82814803110601c118001816107070900c0d0800c0081507006408806444044404110b10700a510000b55680003c86800040c400310b040144455805004110701d25001c031684100340c0f0001003101c1c0d062102c0e07644040c4002d0000320782420341e1500100309542040880ca440101490f109800a644200130700c6105e0050520400d8220360080c6601100c121510142c0f0075903a90405240c001d0082d80009001e9001a0034520045050300c20b41016034043d88100902d1424410036001036003841c1d000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 238195746 1250 238194496 238194499
    0x90102030708070321180f020d05010603140d140405010e0303041806030314120103060507020c03060108060a20430203010f0204060c0803101d0a110a020a11 69
    0x103014071000074041d400101052071103607a6890f050304803c2d0640300c410309681940a602801d240903084401100c6c82040642500070462841108003070000ca0390710108058042c00b15400d1400220900030303094507290b03010f40c0410444002800a0100716140c62541c1000040810100400c00a42d803140d46006161240142540e1402e80d8a0005441145038008031881d050703110b0724100103140d0811400e034403111040d20700c0c0e40740c00035282c442004c10405010050900d03544501140c0403500c204241a042c1c540a000c41d88d003035071030300301c22542c032502203540100c0f55041000c2e690900c0007603590043d41e40b89144410741403c803101031700e000001004c00d00f034031003a003518510000850388142005006401c0e003d119100820b03401803500303690440c3c50481180e0700400040269035401400403ca16800008903034990303d40803c03280c007111031540840c96041760b09004c0b90700701d201d07500890b01812110008015440b04034080382080d000314030300303103001d608040d01c0341c004141c0d01920074642000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 238196996 1250 238195746 238195753
    0x50109020108180304050432070f09061b0602160b010e0c0406140f0d0f02070309080c0f0f040b0301050f1f12060e0c0306070c02010806041a101101020a050705010b0a08060c090102 79
    0x5c6d8423049268501003400036035200c4803a0400d01ca2415009880f0b0080420b4604e030040d10f813414040c002e054038162604504100c3c00404140051202070380c1130b00c041212042064440d10b150f0708120340d407000300303004001114508101080308000c9180448003200c4080c0c880c06083c03d008003c006641d04060000d00040000b0841010a0b111621074a08980c81c008801030320b40a06007001858460543c00000456001c0e06c035910065030b4404440164034011a00919031113030107408500035040e04010f0b0750b050360800c1c007800b56022142e05107521800c1c86407100ca502c0c03a40d14011440100c0d0340d100c0e0300029043e603003021012a83e86d4001c600507040d8a011560624103a60100340341090480f603081c001a20b1801503011580d10050392900311000310f4043c41842d001c25001820400c88645543c41400300801c00e4000c00d00510645d40b204d020348008540b200c4d03200002034902e900c0340344100c07002e518012401c0d041d880d007020b840d800d071000280107000300d980c0c804141e0301c1ca44c8643c00490540c1b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 238198246 1250 238196996 238197041
    0x20904050a020409060c081003030e1504031203090219060503010e060102150f01260c061e070c0e1e040b060a050904080c1e25030f0501090201081803040504 69
    0xf20303540076a454081c0705420010361441d80c0c00f4002c052600140c03c525030307428031358020804668814040005da803001c81c1e0920b21401c0700746109600d40b045078001041e030070700b003220550001c0e015440f0514580c020f42c0c2d801c1c080d410b088091140b40d80e1900900d0049082840103005400c0068103040c2d00200c180111009040041502c542005085a00e95820105e6000500c5400305000e20740c00d0344400c80c0090760170540342c002019100c10781c040085008404c0410082820384400c02c0048546c16000c520f5580c428090400300544001405981140842c00c1e0216038550701e030b00358520204919002000c8551201c1d599440c0d00c1c103000d80204e43c01004068003103202d5982445550003a803140d0606550f030410b801c0340c5400c0891402d490a04000b12040c4050418004141400341580c0c414406002d4101400440340e216003a4101500d0b9089002403001000030540c1b05a40c03060013604d506802d5600d2143c0010340404101c0400d4258105020810150030203070401032007030707610414555089 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 238199496 1250 238198246 238198249
    0x60302030a06091401060501021509160602010b010f050702030307330207060e060105010504060804060212090c0102011103010f180b04020f0a0e0a0509010b1308070605040f0b1303020904050a02 85
    0x1045018155003607983d41542d142007100c00d440580b280c414240092001c545001c0005c2d490710b8000826801c020039a2000680140003445100c04912001652513000742d21200003d00030100c46e004103000c24145805011400e0240d8182c9002c1a4014000c518003e1b9956a41011000019032400c641381480018008102c40d10b02c01c4000007050303880141c89040c14148141a103044400c0d41265401840c01409a40d138010101c13001c0d5411800c09460a44681c98092700030f1088120031410000f1007401d010b154440400c003802004403d074002c1c89603e18500700390f100303840288030b40c0c5051060036504100c0c0214500382400c2c84d5003160030000e035a001342408102603034040246c403500d401c40022207074090307504100200071500040c1c0766100c04a082c14040b60361001c041c09503000d021000304450756402c2800d413076100075020b4601922009540c605014005411601900312546403115010602007055401d03180020f017110710300d200d04c3d80745030244401c2400c003030410343c0e890285001c0314025 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 238200746 1250 238199496 238199503
    0xc030c050f010915060e060d0c2310020606010203091c060501030308011715070c060b1f0e12030406140d05010f0e13020d030e030a02040509030301050a0f1a0a0306030203 75
    0x1c503140c0021030501c1c443e150401200c490658203240c030720719000050000546500e4000d9009000380d60034012010315017400754100c00c66a110501803210310000d903813002c0402a02e60312410003a210000e01c0040b080c0d041c0e80312a00ac4541d0f80c010307031050106100624102d00c2074280e404c8589000d40c07150001740c44003010380348241c2040d004181904010820990032080300883d0750303400005000121403e1004c0c00121701c0181c090810440301d05904400e001c065405203940c070380300800700c0b1840811540003002c4003a65041c031201140b030032001205a4146891f4401038440850050752400381040c1096503d141d4034054907442110500c034000034203041d4400c490103030501d089114150b529084040300401d400518100490000801907001a00c655102c0943c20303a15050008103050050042417802000e0900a903005061105015202c0360100c02181658016a41e21083c2238039010010b8074841c40d407084140c003038100d0544420031042003002d004644003d00e8081102d6503642c0002c2d19 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 238201996 1250 238200746 238200763
    0x40603080d0e190b04030e06120708091b0d060f140c131d06151e03060901120f030e03010f02071109010611210903071512110a0c030c05 60
    0x2021030752002e021404a0040203403025043c4100901c54060034250707628240c035040580024144144000750514965408007030b1100e410540c80010428a82440000c000001c1a10a46018010a4125405440c0512240034800320107803000350641e08984d076180003080e480e1b4070700501e07960310789040d130107003000000650090504004450700c8a81010440f61900902c0d401110007400702c41c059161080e0715010160700900c11100d00a01d040d0804210040f881001d15190200340d00d0640030006400079070185018002c26110310010780e0f03c0f00e9003074072a8480c10b4030180038070056211100000b84280352500f02031074068004541106000044416600040411500c201d100012292282031400d01e0a0040c810303072626911900f0111019900c6003203000e03d034070190101c05a10300d2950091800c82d01d9910010303040b103c440b035481c0150390074042d480c14920002002d04d070101d004802280101603c3c48002c9803594548414500c09503440144203138101c050001c10941203011850503c04d105 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 238203246 1250 238201996 238202017
    0x1270e0a0309031209050a120c0803030705041e06050f030a060810060314061504090c0302180603060a0203060f0d02030f0a08030109060b0c0a06090816030203120609040b040b0604060308 82
    0x1202e0a045150650342241c070204c9003010170088850400c40382c3d40300d544440032216015180e04508801d8140012507003c50b030441d16080c440001441040c6922000900071642c01070000540581e41190002d520b40003481243c001074018081480d044184100468200030780000000b010341d91000f0035418007424840e407940310341c7d49140c1081800441c4507681b1619000801614051405d502200e80e0401d25510751406141d03185c0140c420000700c01c1d8000b010790b40042104180300342c800308903846401d040341c0c0c10b030080c0103c0020a414003114000c0c0c0f0b009800c014400420f4255a0081c4005004601001d0364980300d030700c5200090b0081030140400060041c4042640c0c2d60501010005486466004980d202000c0149804564012441c20202640140d001c64075013001d0510740c05130300801d031003140e500c400c000c4080b040640010003000c02402c3c07a0280b02151b5145010424014000c681c0904001480e0f00050700160100402070f601c00340083c0001015030f1a41c0311010260441c14424 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 238204496 1250 238203246 238203257
    0xc03020105210103031e0f02060f18010203090a03090527040602120f010603110f041a2101030302070504052502190f0b01050627060d0c021b04020301270e0a03 70
    0x218002d1a21030081c04012a442c06d00381210b07116001f000b507450000900c00040d1501500c080707003800c00a4180e554102810300c00030354403404c010100548441000704100c0c00b05041500010340c07420178003407410302c031400c0705040c440202c03100c3c1102c3c1c90994000d0046a545a00708034205040740380301040381c0280314220081c900b0758100360000c0c00302c0d081c41c2c00d003030864081806149030182c0303120308440642e801803400001c81c11100d02c0001690045000d500ca0b030540e0040e25148a40496013407a048a00039400c50b0540740d91041407004441c402e40300303000c0e22101c1c00e0f00120406000e0300b52a40301d031840d20403648803034450008803030340c0d4440030421120444087d01070302c24026054041e6025040440c3c40c1807800007005d0340b0b4000310004030b02401098482e0410810507a1302c1c2c009a941f5001a800e05110260000c100251203100d1160001e01020140f20540500d040c18030070340307041c2c902c100c01031640e6401000c10f8004c510403440d110307061191222484ca0404030140b02c40c034100740c0300e9103a1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 238205746 1250 238204496 238204517
    0x60206241324180f150605070312091a100317090127230409111c05030307030b120a0605060909010513080c1005010807050a0506070c0302010521010303 67
    0x42e01e010b072000710108802c80d8070450041c08440e1000e24500500c190001c40019080100101e0b24090941d5a0055948403d400b4000440e60782000040c4940c500c60741e1001c03070049003804c16004441030450054089202402e481402085aa200b0303600203403641e162041c407650f84c2e43e5041c103c880b92402000a6040401c505100b96040390f03da0001140c61002c818590b100900387e10790900041c40303254620424001002c925219441c048a101da10160040c800903400d400c142c82c825401e03c071030340c1c0030341740d80040c03d000707d80c010708692071440d44040554a182c0f1412401c0300503140b4180182c2c0d1040000403000401c0740c04114410a01340b14134400714492401c5010803a00c0e403002000e2610030390502e0b040148443c8140c2000c242c85a005241c0c60700ea01d207403201146030401c12504246810325080010a070752500080d508100d41c401ca40c15420281c68805001301c50042c550000d140c900e07050300610040d8024030180c406444405020302000e0a60400c0200c5550280c0c4180c000c80e1681d2302 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 238206996 1250 238205746 238205771
    0x30408010b010c1a10080a03050729070f02010e0f0c09070513210f0b010f060507081207020307080d0501060306210204050403021603030915090602062413 68
    0x29030518a032003400c200fa41c00e2400e849a01c1058040d8501040303d1054070f000a481c1c0c5004d510910240c48541d045907101c0700e031031602400300d82c1b0070795083c0c5668001100590205219280c0d840141120760a140d14503166280c00b52180c40700700030b0360130075035403950204000c5440802088000601d56130050410030862130070b110085402801d4001041010020003480c083c42a40c484100c80050704440c511507180d2007541240031020000511602d0100100c00c107122880403214161020340110110356541e49105541d54442c2c44c200900c00001444555016100300e030300c00d135200100d070043da0302d004d4183d41e03400e0050b84103004c0c0040c8640d5950052101507450320460024124100b42441460715034250310084031503000c4020721580e1280005400c05100388040404007140f0019014215200c0c035002c0c00807555070080c0080c4010f840354615079030b8410300003a0104d4a841d005030910352103580c200c641417261034250f11070410198004c02e48940342c861442081c1d21110b00000384055030681e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 238208246 1250 238206996 238207001
    0xb0d0b011802030105010f050315090901020a0906050c0d11070b04170106050f1c15051303021002070b0105010804051203070518010206041101030e0709060905041e050607030c02031b03040801 84
    0x101242041d910501c014001c0340d0b040700d0202102845401e004c0d0304ca96030700780f595500001304800c058000c03c44405100480e101500038005a1130301c0d8843c5980e09403945001c5074180102e801d89100396212100b00c112a6014001c0c00301d81040e03c1d002c1d561507503111041031501d98026801580c001e0141c88000744180400e100716400750600f112058483c816400000701c40200440000d44040070016080081000c0e07003100c550000c2c1002d2082c0708900d402e82c20204200d95158054000d40a452070040041c01284200c842050744811040c030541d0816004454180c001401180c2501c60f8099103a10020000051840f40e5a25901e20b0707030380d0303040c00c00c00203400480d41d46040c19548450180000580514a01982e440c001c1c40c001406c010006125850080319a1044071601d01d8444040f41403107003500701f11320440c05440ca00b403003071615210380304424440e140080c01d15000740020031001846030b00103045210085c4122801c200c1001640c0b4207982007140416080c0d84002010000c0031030a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 238209496 1250 238208246 238208279
    0x50606030d020c0310020f070c06020f1009080f0c0a080c07050109050102030c06010b130909080315150405010503100302120d0207080c0904060209040e030d0e06061c030e03010b0d0b01 81
    0x38030107828070400c40808a41e8901001d034005c0081500851a015076100340c000343e038400780e0046000c201440d6074000c0a0344506215882ca03c49010701c101030345204141c4c0c01401000e6034800e005610b0804031110804c1150000885501240500070b14a000724502d040945230b0390340103102910a091030000051300c0ca1003103900c4681550028085d400c800040031410700d045a02d4582241c0d5180c0d034010b180000da2000c4c1e00600d80c3c140c54a54031005200301c05000e18460300c5034413851940000c400d0100208454403511004110400300400d00c011b5228001958008101c2c100200600f40c0f03d6002030b00740341d12200301000719030000c2c0c0030b6240c01c1d5040103903100030700d103503009483c2c1681e0744030200e2401d081c01840138012079000101c9507556203881d40500b14000355442030766203540c900c4144601074001128501c08a00c035003000300d441b514194160050810104c100294400728954068404e12840c9c4401581556141445031198407141840300c02d107071144928101c03960500c4002880351420 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 238210746 1250 238209496 238209523
    0xf030f07090e060310152d1703040603090f060c050d0c0e0a03140703052e0b0109090b0a08030d091a0f0c0705031303060b120105220215030405060603 66
    0x82c424882c0d84d8601040e0650984c40c800004650f0081d4aa502c6010741d0040d40841e16512981c103c03918034500f1440c1031200200d0071098904030a83c0c0f4003205d440d818076100102c007160010001044018007940c81454032520403108400c44450644a40c4211103100004d0b202003240000c003010345000300d10803168101e001d400c000150440c000085403040b41c0c0c50000408560038085078101e116001c0005000030f503403142c1200e40c0640210251540c03980070741940c0703101054144a0708a040d015009642250070181d490a10711854641c4001c0078200d1040000c1c0c2014541034080b0341644148002d0a40ca580d1070400b28040c0e03d5880d00303542030480d95100e048d500c0141014032040200030158660031803c26510903031103581034200315041d40709a40c0034180088514000204001e115003041840381d508444031001c0b840304010300350076100c0c02c075014648809540780a0724030380190350700450054006041c2001c040e150384584110b0364426541523070300c2c0c0e00c088200030b8280383c01c01070b10039403545 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 238211996 1250 238210746 238210769
    0x1606030b010e220e0a060e150f150603041109040b100801050f070e010216031a0c03062b050316110607120c110d0f0b09070501020c0904020103020f030f0709 69
    0xa43c11500000701c3d5901800f1002541320703110010360420400101138050b03080b403404c004845102c0c45d42030f1380309000c0340c076400940100d000140c40c4a802100d0300c3e10925481c1d044615030f542e140204144ca0303000030805c496000702c41c0c0600e9940c0d140c800446105602c2484590070508082048071081420b80d0700402c11a030401c400c0210b0920201c00007508808941060010001c075000180e003805c03070189032003040704090613000040c4400409003035402c41807000103d03001c0d21540c200302098030084400f1604525030800780b030703c0d1030821807400c1c1d03d8820182c0010660041e079940c0c0da00b1580b1001c0c0c4400740b001d0012612003400328142e285038014408440e03940c0380404941c3d0781045c440001d0100780910038001200320620400322150110200700502e4180710070101e00e0405d05401d0400d4050710f0b01c121110020b40349980c002103100c20388130140c0040550316803032020031000850062003241055000e00c0300300080d001c00790155000381c4600280c0c4083d441c0440000b0582e0816038401c00b90010b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 238213246 1250 238211996 238212019
    0x522091d070e04020105091201090b10080c010e0118121b061202030603070306090b0f0f0903041205150907030b0901021c0b03011b020d0e0a08030a111606030b010e 72
    0x103448000c40c0e0301e02841c00b05655541c001a55076000e98070080b500310b201d182c080041d01d2410361008610724412201d4105a49503840180c080c500140101000c40d4070074548100c0541c01900c02481da44014540061103000040b850300440f2400d03403210985d802c41c800c1000812000d103414505895102c0d4a40d034405240c114020505020519907400317150340000414402d0714240400d0019580003182804800018038141460100c200d078002d284540517004030b090501c403e1a401d002d01c060304000c50815042c00c003800000d0340340800031545440b03075006e0900c41120349911140b2500004010344a0249541041011120f008005240591040144d00e5183d0304800314003404041da1070300001e04c0c1002d94013007401845001e0004a0100071000c1d4220640d5000030400d20450803a510b204500010205100b1011042e004180d1150810300004200500c41d003054600c10200e41d04848401821001e644c903025840c2e0000f02c0020303101e001401a558004901c0c290900c0165074021201 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 238214496 1250 238213246 238213301
    0xb1c2108060114070f0b0a050a0b0303090f0105072316060903150902040f0b1212191803050d0801050609031e0304170114060105030403050403030e01052209 69
    0x1030003000181407001400c00514140c106400751040c442d030000c0c501c49205110b003404c00c080c8500703c0b0b04c440c0c41410314001642c290060301400300b004401800a60625841c1070400c030142680f005040c0c1040380910032000820003480d0311110408501001083d041c01c040f029609042829003614100e0030f686408000300380c1d20041a5080300d03049500c60600c41038400011000d010349400180d1701c10305050035081003c01c1d030b607c032252488046560a0041c110103036100c0e210b800a03591a40e0b0280107003c0094048401042e41c0546610b41c40c2015844910403901d9411040740d4105950030f0f80b15520f036942154001c0c0340c1750702401c41240c0d014108800300000a0740c42110040b80c0d6150314507001d0442c0300e04400c0003960041e0480700c05680001202c0713001180200341d00c2c05484001c42c0d4a0020810550042007128003a40e0035645d4640303000d08644080d110300c03503941ca1031810440108505503c21350050300313038000b020b04070010400746803604040381300b9100d0421031144100c03962001c48403803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 238215746 1250 238214496 238214507
    0x90606020c0a061e05040b030a1b031a0906030304030804083702040e2a090a020307080103110a05040c02030c01050601090602491d1507060b1c21 64
    0x5070b15a01c0030b00000100ca603035017281c950140d58003812181343c01200f800487c905581240d80e80103041a6a0840343c6002c04c011010703500001c00a14564809079446851800c00d00c2d41607900a8001d02100d00c1e1a540c1e558082f5103074451760000303c4d55042420345640d040e4418200c0140d941011010b82d000c0c4518800310400d6034a8018024031880e0b540e82c0e075080301c90041c81034007840d002016040009140ca00880780c0c001c0650a41544109035a000141140c072961007503d0180d009035680408607801c0d03a684100981c100e264095201c462558002643e83c0c0e5401011800f03aa82d40c05503840d084045a00c41c20740350003900c2181800384852092149075400200281e01d41d007210880f00701c00040000c0301e0200480f44d40b04ca05102c480c000c4080b5412504c210880290025541d030306c0c160301d0036641010f94040d0850380c05901036940c1150b155851304102c0a0144117004100004405a0b032900045446100440b10500c4000402a01050180c0c0241e210b01c6244103031100d032503000d12030328000c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 238216996 1250 238215746 238215767
    0xc02121c09082a0d170a0314010f03030c110a03080c0c0904031b021906020120040308071203021c05070905030a0c0603230f181f02030c0f0301090606020c0a06 70
    0x500d01211410140b455482450b0408038942090813117952848400c0030314082d1340710040000c0801c2c1400890401c038a15804070b941290350700072051702054195941190180c41400702070b2000104001d29413526660010f501008501c07400040e82d0f01e241c0c2c02330340c0341015400780f80707184124038a004000102e50400c20680d00c1050310755281c10202098400105c0c2030350500c1c103280400d440c00e600800d0b030940543c410220540c1ca40c0102c10000e10100d00854180310310b0000811076002480480c0000f46003c21441c4028124103016080400d54841880e40108403880c11701c83d01d40b0307801809201034000d001d000c0940070580141040c004651100e0310f000325140305643c10182d8503070b200c840740c20b180402a5903410290940c94081e0034003090020707502d1010f444000c42c950f034080108194410021384142d1480c82282c0049007100b002d0b444000940000385400b41075182007243c58145c00050008502038042400b00054042c2006402490311009003c92405003031a21f4080c0403441c1c001c0350f02031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 238218246 1250 238216996 238217053
    0x20702010909240b090301060807080c100302160c09050a0204230a05060a05030a0605060a020631030207090f020705030d02160b04030c050f1c0c02121c0908 69
    0x40d42c8208152440c80054554107030058104868004030f2505150001040d202c0b900700d000f4007000d80c58527860341c0c80d514907110300d03592a446011b1810340750401c000411301d0075200c0d003001800c14110301843c0442c1c0603aa90101e403440400d0304144a0100700703101d11500300d602200114185030901c120840c0c40100004c50f800c8a009032044e0448647d956010318025020141000b92607078481c01c800f6001d6041543c03150500d41c140030002c40c0604010054071039004403940240050340700c4685403208030000d41042c0c441c00e0444400b120315024241c114000c202e100e83e000b002805c0c9004900000c581c1c0a40e5115061801001034101182c4000701ba00c0d56034030408001660307142031980381645103041190003010b4820386030421042c5600a4503c5c0303041801481a298100310003003c25444408031001080c0007201c42c0442401180300383e4568a50b24800303040350303414a09004084e89003c508201012130b592030b403007250202c1c950064400b00100220001042d0b1119900d40c200b01300a2980e0000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 238219496 1250 238218246 238218251
    0x50a06050c160f0b161703091b010e060a021c270303090b0a0203090409080301150c0201050414010c05010203010905010618120308190e0606030c0901081903200c0112020702010909 79
    0x5c00740351a05c4040c15104c2ca0307000078507904130f065054201c13865401c122082c40700d50207204841fa00c5101c190fa1810600300b0140d484200750501881005050380041d41c6141c01c41c440d500100000c24545000d5900c240d00d103407140c0c4500201003808419400d8a00014440040341010400020313801945800c25645540c900e90b4954a203448100d00e5402500c1d00d403540a410300716a90140090340000758140c07075442139103106a805843d82941c8840034400700030300144081108106081d000030701c4011601051400844d045a5903c440d42640c10a801c030401840d90390004010325a00b1483c920b4040d15000d8403011824a4442d504888918000d0003800780702c0141e0005d132aa07201d103041000700c2180d40304c0401070504a0b1620b1503941d00c084034145c1c06407043d89042217051904001c003504a0301c25500914032005003e48111145404000480511204201c0c812581440b40ca0708078071196030b0402003080700300c04e00004000e03a01900b507100d21188100000b601503640440701b0400c0d5801403402 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 238220746 1250 238219496 238219507
    0x1d0c1e0901060528180803160b0c070206030415050708130b1b0a0306150c022119110a090614010e060903031c230406090507050a06050c160f0b 63
    0x60720131500c00103074240300c5181c07803456104800c0d8105616941c014158400d00d4480798480650321780d0381c45a080c1c01d8409003440e040031400941c4184005501c800b00300300c214280441035002c101c00c1d410035130f821200c600b00504003c109403040d2203102c0c1c1c86441442c1520881c1002c10b20808048000d2038040c051101050004045402c4c100e1000100e0038440030b01996200040300050007095603000d002c0d074404d1900d00d140e80f81703131049410940960700146402004c9510a01548a0b0903046d001078640340a5800c44500c1407210200c0494001e0040044400c042c00e80010003114074055041003409500d0000240055407008004400002c02800c2c007443c10120400011441c1c025107004a60601c00021425402145018407841003c641c5070240040c1140411900041130400e81004030b194840780001d010441580281941c03d00031025200095154400b00700800369640012000c6000003911041390401000840c0c00180d08406c603c428509002c820302156405204504c2e22130030110b02c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 238221996 1250 238220746 238220767
    0xc01050313080d090b1305070e0702030d02031003020a0e010608060919150803040b040e0112050604170f030c03160206161809020d05010312170109020c011d0c1e09010605 75
    0x4105243c54215218185c5460b158030b10206a00003404210303280d00a032400001d01150303c1c0401c90003041c40b40c0196040c107207009a420001d400007841002c0c64007001c04004050381310042c075580a404050900840c540c10448060056603014110a025030021010012802034004c1244c4c1a44104240820070900b210f00380a000c54440c3c215888034080003030300048028620004204440b41c00368428a640e07078800300c0c04c00e400742c0c4180150131038004800043c000352507808281620058040e5487c18140e0744d10009400e41c0007154203500d0204000b05208082101110940000c00070348010075161900c02040d81581f420650404c061104c111a5492003007140c02d5008094021800c0854940035410042000303400c0030710050750300841c20280c00244621501528609101243c3c621501d13910b0400c0000003513106603002c2c0c106558900d50355070b458400e1103c441045c0b29000042214214410401c11b4424038078103450b07001c001c00c02a41810b030f128259860704481407410040d403a07004014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 238223246 1250 238221996 238222001
    0x305090f03100e062d040803060a170a0b0105061905160f0609020a050102060f0c1812010b0f0406050d0b07030e0703150c08012301020c0d11030c01050313080d 70
    0x41482e1800e1903007000304100001552403140d1035801d820b02001d900c1d113800709161802d83e02013104180d203910009010a2a060040d40c10610142402c0700300e41ea200b980d40764490f00c420481d83c05420074900701c0e0501890b4040e89025180440d170443c0390004042a0002028040d050034040c403001140c000e180c00300c81e0740c03511091a0070003507401400050b0b14000004000140040340b0803c020f4801080c41d520029602c4c0c801c842a00d00c0940d1601e441c80e8200c4650480712006070100e014271a2015580c0f50750b0b443d80111589070001141181015080001c10041c1c240034601441c03814070200616510041c84240013904020000700d141c8440104030003615200303044034801c3c81481c0c400810422016200d00c1c4903a0002420007449180d50300895445400b0f00c40c000007111006041000103c82041d01c1c481da02050044a40c21081000810141181ca800549900041c440030003414201480815070280c000d20b0b0880c61454001c850604007241c0324005881c260010030a551101d201d40d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 238224496 1250 238223246 238223263
    0x504120605040c0b0d06030c06030209010804170f1804050601031109040f0e0a030f020f162606090a060e0c03060f0a110304080307020f06040b0105010f0302091324030305090f03 78
    0x1d0003501d80c0e60114000060180c140340c882101e542301c040c400051000c0c485d20a540560505030340d440b0158a460300c03402c01110a15151548606080201d40c0360a501000248425114202c04030140c0502000300f10481e00000c1289040c142060b03c80c20004400c00d0459241c0e0208032800212131006182e11001001030030003440403803148102c00c405154100140188a56580d0300b1075040e9400204a1070300ca00c5203600490740386412010910440321211805c40c445500f1508203400303080d10146003450030f541601d2480168120316038903c1886054012043c400102000821440040c240800d0380c8010044c0001407400c2030310042005810315801030040c0300100f00c1030503168100340c20f02d80340c250f02c280c0b148005445408503160100401198151180340c00c0b899000d4641c3c40c00c401542d4054010055004069003006490099902d02c1c0c520310745004000800a40c41401048403044c50754100b1755111701c40104001000043e40c4141100c2a01c0026101e2100601030140404d181c21540e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 238225746 1250 238224496 238224509
    0xf170c03070b090306150d0822090b13020309060703020715060e060a080d021c02010204080a0803041403121f090507031a01050703080f2d040b01060504120605040c 72
    0x82840020316445042c0180255072001c4041c1d42581e1950340440040c0300304401d8180d003020a140e80a4081000c54019012511281c0004280019200012442202a50400e0407400c1d590414405541061001964801140c0000310b14505080b0202d03961a48000c1c111010103400160700405c004480e48000c0d8030500000c010702200307445d2012885401000c5400c9401000801c00000368080c0010341c0a40c2000590040e04180000d140703000300784c103004050300043d59002c03c0006106d010800002d41c445000b0004981c4a091a18065100c0702020302e0300303001e076031091221507155012001ca144d04104070300b02581100200213000c58000c0741c964001c5013400d180c201005800744d0140c11010302046500301d5101c0e40105000152110f0240010280002d40c00e480040c145001c2c2d0b940351b0b07030402e042c2c0351918900302c15000f5041c04c10781011100020182c044082c40100040000045e014080c10f082090400d81007041d03071400103041c0000940f1280e21361011a00303002c0c0500600014080e07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 238226996 1250 238225746 238225753
    0x15090b0a0506070305040806240d020f0a03050304051005030f150d0812040204060f060c08090a031721040f060f0b030d030b0a090204050f0d080d050f0702010c02070f170c03 76
    0xf49003009007403500315205668141c050980025042d10340b40750070465401d01b070070003045c00d000404240844500340c14402c0383c100101c0d0700c2d90341c4e03190b48844520004610071001940d480c0d04000900452038040c240a1082c01001d01c2130000d1039a00001c1c5a901544251281615001080005010441200c00a40f80c4200050041030314000c40010910850003036030140030b1309035103a9001004400e10320500c0d0014411015180004640c0c03402011002d0740100f04e42519070303d0ba192020b0748003880082c0c072004900002c10319a103c117201e10081400f4291918103001c1d2820b03849105000100403401040c2c1d40d80d070100300418004a030b12468080310068101c805002c21b90b24003a00610340362100c0d5200c0c8202c11b50004058036a0f00845059034809820801140c0e0541c06001d03031201c024008981940c0d0501210400c2042d510840d40f0500c3d80140745609818001c0019003140e425109400c21504644014400b40c031001d000d03a0111500c1182405403910743c01180d50034850140c00c916410301 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 238228246 1250 238226996 238227007
    0x300f0203090907090e090f07050d060e121b030408030301090e0102190f110118030c05030d090b0103120309050a140106080a0c030c0e04030c02010e1305160206090115090b0a0506 78
    0x590080700d003026039165017843d2420f6225848029518228140c2030354942e8031210061106080141074090401c1c82001c0106e11003031594030060420101413000d600016010650300c405a05484840c1c20380155140590702c1c0c00c3c1840703051612444140154010140c45050106c40395100b581201c419407c07004282840c04401c0748010a1803144144400c005120307510b542c900307602e040c401e01c460702c00e9241d80d03a103020400765002e88200c8001ca4003601d0901040c801c5c07544504a501644500e40c1c4680e500111540c11448c11104001c0d00410050800d460030700003500240b4001500d1510b81c0e00700344a1020324234030100250160036250010101d038001c03800c4000412090680f101c007a40e00c240d114401e070390b48810755540c0845049402a001800500c84603001d9400b5030705410346040050400044106204500000e5900c180c4400e1042c4ca0319442c18907810703905204490f00030440800900c004c002ca035610040724400c40c09641007507907650003881020382c1c3d40068140103044c044c20450310361 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 238229496 1250 238228246 238228261
    0xf090b0a030b041d07120f14010e01140609061504090608030705070503010b150304030201060e07020c130209010507151d0607080108070f030809030109140a300f02030909 75
    0x4002e000c03001c1d07000b02c3c00c105180d42c41c01c0d094500c18144088040003444403d1404e90300034401c050000d826075810404044100109039a1240290072040c0c5000104018880c04416803c40b008100400340d402c01c181c2c14800e050ba91141c0a41d000841152000182280c000c24800e06116070762290000c40e240c00e40006070050040080c00d990760060003660b41e01940c0e80309040c07e84544505040c2d01c07614003d450088018884d0266420034028030000a009890f05400185044143c0300540540d1000040d218540b500b270740741207007404128409500705061503002900d64010f541d0000e10004600303110340090358007030b8409400f110000d541d524180d41c034600c0080d10f850081e140000020b00c1c4e1400400c40c044002006d0003141c00308443e52140d2481e588030103109412a0b04402d80c50754803171590070003107a4071040c800c0c4503101038000342a07c5100da107001400405090500800b0600000341e0111041e80002c8080400e552810b11706200502c07070302c04900314498023064645c401c1c015410301040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 238230746 1250 238229496 238229501
    0x12702091908070f050604120201050d0f0c05090301050709061202070302151305060f130209061c030f03060f0312081e0f01170118060c050909010b03151203030402010f090b0a03 78
    0x201c0703070b96002d03844c0c00076101c4003031200a2046014080f59901c0341c0c04501d0042d40700d40003e14850b0b02c9828001580c2d6034200706c0c103054469064803640054400300302c404040c0f41c00c0c42002d0300140141404040580740c41e5014144030801081c011000da804604003003414000c2c003414003100c55400004110b46440040e0042c041c00501c010f44040c41508001284a41080500360081c85014002803c1c004660308226082c640180301e684c0041b003d03041c1003001501900094641352090300d4007010a602490014100e500d030b540b0075195200c0c101810404074001c0380c501303110090705140c605036030703500c03401382c820795810b42900c1e100c0d0404e5400401010f10607101d48181a104052a111002c0c2c0c07142e283c00c0e090b14855920703a0400c0a45041d10000526140e000c1e580d8002642021402c007038082d400212208001d0748210061a000410072414407103a0300b040d080c41d402159120100c011021990ba500e000c010402814042c0c0f1055000c6140d004031409401072030f06074803041d519000d10000601 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 238231996 1250 238230746 238230749
    0xa0603060f0b09221b0915030503041e0503010e06070e0411030f1b13030303110a080f090c03030a020c090106020d0f050a210b090c09030a0609060e070f030b01270209190807 76
    0x10b00b00d29091840c509200480c61f10021a41c200c1300860510f818914150900c62911489245000d03a441c40051151401e00503c0d0001e080200985900c0c0781c0750401908945124100a21607490802c80400c407020b144c0680e84c100599541c0040d10b40e9407400141920b00030180040c03003001000c0b40c0b42561070042c0d4001c0f000d4034480e41c1c05120410240403007405500890400c0710200365100700003203880401e02c10342c540c0080d4050885004221084c04139041d82e1200c18244010303001516034004600b04268514010800344c402003804484203d00281031074034401c90101003150004003003610610500300d03108a41c030b05000c0d1074401c03541000c00c54004c00c4040e1400f03000d504001e00007030b00d980c40481643c01c0400041c025040944060340c60100400050800701c0b10907584a00c0700c072100c0d008001c80350180c042c0c8000709200d035086003400224003505030301100b412802002461040010615004d034100d03484c4c200036850b403a090740080d103040b80c0048030903068001054001070f9120001013040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 238233246 1250 238231996 238232009
    0x2030d0f0e01240914070309060f020d060e0c0c030910090806011d07020a1e020a030b01031101021905030a140c0a0309061d0d1e06050a0603060f0b09221b 68
    0x284041d40c6061800c00ea5aa045c2c51501e103a03031510000310041d0017500704411891051900080a4540308024404c03030b0030048100841c5c40c2d44d10800c0c8020019440015000381c044201c041c03c1405c9a80015070760301c140818a4041e9090003100c405e41c7e40943c031000040e202003c15a0350b15a103819945000040740c4140400090180300841d00726400403480e0740c00e032a04440e12820f6154101440e1420010300002260006090b50b0004040f501c1c80e0032490203148201e038820484a08000020b00d0283c55480030004d180c41c64040ea800900000b08450360254141054103c540c5410103504160162050a21050081d82c444804143d404075003001502e04945030041c042410310301c012507031600811102e802c800d002c0d00c020041803113040e0b47c1c0f182d03c01c404840030442805540e0f100c00d444051f650512082d80301c82007881000003d000ba07910090741c0000802080320741500044024001900003900c0445c114000d02c2e8040c540e48200902c40e030019842034090380301061034490b0034240c1c4240d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 238234496 1250 238233246 238233311
    0x406050117010504200f0909010515070f0309090e010f0509070e0109050907080a0c1406192d020c031908030a020d270b0901050702030d0f0e01 63
    0x4109503008401a00c250308800d004809a60700300418400140451040810503040a4049a03c6105c4004c014522884050f0186454264a0061029140d8182c00241c0300302d5a080d0345880c440300c01c00a07150001d80100c040c030303c00e80f814101651080002d800007685542410b0130a822400c05400050380062124800c004079602c040a194454442d802032852154200004210644140c1c2259030060001e00c166102165106140c92408983c81001c0324002403400d41003120b020031764104d01104006580452426001480c8100281c21030070a680c01d21035415031000002c0903062110a4040750b0640844408a5101c006542c1e540c0040e4420711070312a01901c0c80080c02c40800501c000e940c0311010b5070958480054800180d00803020503031103d95241d03403580d0070010b01e00745440d66604070401c01c402c000e080d081122044030300030316102d01e40c0c0c10300041c0868998004200d82001d00d9181000880c4128a030300e04000d0306003054a03418135824044481d46400e010540a0700a1202400d80c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 238235746 1250 238234496 238234499
    0x2070c090f05060942100801060905010305131202070506031014040b0d02090702030702061b0d0207050a1802040302030307030f111903081e072304050609010509030f0303090105060406 81
    0x1517040510344000000d041c00920550034a815003030701620030400c0741c8080f44000310b02c2c108080740c0b00003120720842c4005001980100503417900801c107038003d031900b07285c24000d82c80c10185400c0f1246600c41c00134191207046225200c001d1090003240b025103002008070380e8174100007143c030803185440d0089904000b2200340c18602440c00340300305800500b000e0450210409035808016211000038030705025408200400340059945038002d00000c120340810340e100d00c0e0554822864039010740c24180542d84554401e102541d980040c0108442184484a401282600f1300c04040d01403540700079054031000c180c1c0d0701015008000310180c8003c40c1e440340f88a070074a10b202035940442000c0c012040300c5941da41800b1911448040313070b004030903128010704248841c5080d010f2a40c2100d840d00002c0c00c02040c0b020b02c1215080c0f469200860300350b8941007904007800501244590b041c2c440c10b01c10005904907040d1000d01003011000c00000559031203250144c4e409000e44021500280310320b140410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 238236996 1250 238235746 238235761
    0x405030a0e0a051c030c0b040506040b0601260705300f01030b01050906210d1e050301140f030601090207060f0507021f06081906060b030105090a02070c090f050609 72
    0x102c107400ca5000411a4904080f040101c0d84558100941a404c01511000960226101c0c201751402030f8410f40042201d4a0282030441100314042d001904014030300c10341c0c610402c100040c41c051402e2940c00255552141c6000343c4151041c0074a000024040c14101c82072072009072508003c043c81503030880300d6640c50303146800c0580d03024000141040300d443c00501282c20980050f03507000001402400c10342e201400c08000d101e003c0902c14810f5844079016031041580491650110700c6241030200c0300402e241c402800038001401440c103040340d10091440c07903669035840041e043c00050160781c281d584401d0804080c0d4008202550b165045c00305840d184e03880d078426903110340c12503400f60280d860203140ca4125502010005005c0b10b40700d11011982c2107013030000039070500d00b2600c101c6045a00386860f8059403d80e600a901844081c001041103481c1c1001080c1d000c4000d42005954092900c0c010130780c050b441d0481d1019518200400c84116015400940112011108103803982e41c0d0b02c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 238238246 1250 238236996 238237009
    0xc08010f051b09040f1d0d0f020c0405060d020a0605040e090a0305071e0611040e090303040b0402010c05031314030f0607020c130b04020c01050f070201060b091002010e060405030a0e 80
    0x50700115803440d8000c2c40429080d10401030f20582da0020808103103089400345110580e20003000281c5900c03502c1800c0d03086040104617106144840b401c00714103210302400c02a4130b692161000a004035101c40004409554100342081103560061800d4580d0b601c540c001010f0f50428000d8541c0e41203228003250300090002840ca442a600d55501d600c2c10200ba40d81b1103001409601541d050500807076001c1c0011041d0280b1942001580034054856280039010b4514213409002c0d45000d40040042c40081004640b8031507100f074080c2000d200b46203072490040e25505c1641d03171410341a4005400403e000a4402151080d01c108500720381c4042e241200454884600340e440382c0c0982c0c007041c9070109604103815448148003440c0c40019004d5a000e001c101039a018402c0400e50b659118108041d035002c1c2805503810441900c02009620b040180c040c51742d10405182520801102d45411030b240c0c800d4002c1c0554100345002e13605030b42464a01f4030741d40c0c1c001c030a40c9000710301541d40c519158103208 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 238239496 1250 238238246 238238251
    0x17130b0108070b032415090f010e03030d1e0c020706080703020310060f020a05010e03030a15140118081605010201110f0f0d0608030a0c0605070305040803310c08010f05 74
    0xa004152864462208090b003096007001420241d400070b403105803580d600d50116606c1c40074a02c01c1c569585050b0303420882c0801c03402840a050101660b0b410343c3c103440000a4803c04402c10000088007010728201025030f10440d5502040182030a1422181b0740c0d02080060485005071500d001540b1078000540690004580f040003074080407404019543c03251b0705100c61441c6a0054031007540c1d15485440c2940c0d01905440b6040c2e200109104840003184034106100c40c648140d1007415080c801c503401c4a800002540e41080600082501d045250b84840c0d0000c0ca114000c80356030320009407072840f04100c0c51103100c0c055417030701401c5e45990035000201c1d02403400d40901307a4502102814060b0007600040c0c100c3c07000c2551050f000c030340350b00300304010405001c446e143c4c0040c0c112189040020b03039000a10640815082009020020314542c09607078114900f9252038400e050542d404070b10044d81d880c0d10140b211401d81000c410321400d40484000c1d503101c0002130080302d071042c0c440c0081d10b906 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 238240746 1250 238239496 238239509
    0x9120206121509071e0e060408070914090a0f0f0c12031d04020c1f020d0203100f06020706090b07060e0715020f010b0a0308070812010b090102010e1203130317130b010807 75
    0x5c400302c690400d48160088521817070001c00c0c450510351181c1d40c091601d4501d400035614540e480a201d5180b0b004101c02d03942c0b0010050003000503040c1552107410017958440028108130054000d001002030b040e04480182400141340f020003035a82c1030052420b1911101c280d081165a40d400301182083d00850b15142c6458005000e24940c581244952904064844c00c580da4203100e024810505400194015544070140303100321410b11400d080c142c0c07015806107003550700900c0f00b00107084e040100c08048448600000f51a05901e0500070040c0c10401003032080c40c040c8000201d05048600000d4054107082c1e030848810840f480307940f40c01c0307403016988164400342c11a000c10004a0307210040c001070340300e002c50b54100703200150701d62003480082e0003100301c810000c12148019642445210002c1403a5002004407048a0f61a141c4a2201608610780c0d00200f074030002c00c1c140512407040341c41c04401c0003c1058544150003150f80190258101d40740303002c41d00009140710001403054261400f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 238241996 1250 238240746 238240787
    0x9130b011b17070302010209060403030323070f030c17070305010f350f01050f190b010f120605060f12070203071208070c0218090c030d0912020612150907 68
    0x900101c1c1d4940e401c80c5034100c045640030448c405140d1501d202800c01503100f924003040c0703680c07213030b4a071500300c039240101c5c100420440c001c10110781d0b402003001412601d14180007415100540c01190034000406460094008134024865401d9041c1d101c00e049607000e81e03241c031582d9102c0300c0800f10400610960784000309050064410301c80d507a0a005c0414800c00126000b11220000c50380c25214111019907140c0b14140801220304241c20041054055180040281960b8000080d107502a00c08254003081401c0400c2c6503050b071180e0101014050060615454098850002442c1d91111306a1400302d01d0b2400801c0d2182d0000050b1111180e000300006240c95000340d00300c800810007040134041016046600c0056200c0040755010701045001c400090b141c00108180b50810510100c5d0203507000ca0031000f0080e40c07081840c4261501107415443e545918000940d9501441c03da912241e040b01041c8400504403941c1c00d061450300341c41064680e9030f54082581c0074205c03c50144030148 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 238243246 1250 238241996 238242023
    0x20304140907110a030903020f0a05091303050c070e10060f020717030405091602070f06020a03111c0207030302010f0203061503040f0b090a1b0b12070509130b011b 72
    0xa003141c005903106507686488681c114400300d040d8030700740d00b990084d00412070146045c0203508001c8141218908182c0d825010a89880f01050f24100010808030f074040c21a0b08010030113115104994880f081081100d030019103408041c50780000030f803a02c5000d034819a400144460284c41851009000f680243c40340c10314100301c0c00c81c0d411030a120494503002c1000086800d039608400c0c94064042c91583d07403640c640f85603010349001400e40003021070440c2104104902540046c500070b486615242040811f044005407a20704800d14802d0720b540a800d410000405138000b9035082128065802402040010750301001288426100d072900114600519241c03490f880c401141c01c144903402840c130b8070103251611007944038192031800c1d2a07008005a82c3c01e1001c8042c940703e445c544441c200150030b141200c050924031900000d0720917440c00c40d0000d0407250081c01a9904000041c0c14000303840c4150408000a0480c0f40301349000c1000703101c05d03000b00c45c0381002105a16901104001455 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 238244496 1250 238243246 238243249
    0x140d05070b1e0a050a0e03010e0d030c030f060b090a09061202013510060503010e06040b0102150f010927031d04020c030d0506030303041e1104090302060a0b0102030414 74
    0x5a02105100b40300e00d5807035506445000c1030600030241c09509640e200d450359a00a0b00030400302c01e040e000d03407103603051110b8406864408608a0b114206a0400250100c0700d0641500680010a0301c1a4032501d8058001f80f4804a2001403d02d0041110f1110300162103030000b03c2210a68000c1500403c40c0c85801d50055001e645460946035078540b068100900d04000f1031002201109600410707680c0744d0501c92019545160100900403a040007400d560602a032a85ca00d10010300c100e11032515100707c4a407990081c451020701419000c071400392450001d004202c040020711131914507a24203890800c0e521f15001241590f900c0030b0b82020b0362030701241c030112449481100140c00342c9118204090140da924401801258090b801643d00c072113920800000310b960007040b06001ea0801c100300000185070360009100c041c140b80c080280009607090150021122500440d006454105503005042c2c0004450744a070310a000203201d001f000c003004a869005a1146100c001201254030344107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 238245746 1250 238244496 238244519
    0x10215070c03050403050615040b0f0105070213021603030b010905040b1021090507080105130309150c0b19050c1c0e0c0d120306050d0809010c0f060e0106140d0507 72
    0x2228040d10f0101c0c01c00d500c98880b20300382103040d02e801b03600c0c0c803540c103440d00641800d0042d41d400510880e0301d620110f00c0d40d00003810a01c142c01c1d009120300c03600582c804003041d083e03040e556108500500718600c01107074035024004161001d800e502098011600040c5440c00740642c0300d6082e0090403003204440300b2201034613003480386204407507456034814100d008003060744a01c00d101030041008124082c94800c042b401c43e00082d041e44051f00c0c1f4000c80401090300b00c402402261403c80c0c898020380d050300c13812112102070a00040a4010310b0f01070254181c150304540300340c64440c0c54104243c0e15a0010b2409a02c01d44d100100c0c01c0c1056043d0013941c44465228200011105003920035404002e00080c61880040302c1c1101c122270a00c0701301b000107515200b640c000d08829504084e41c0c069940381d00a0350701034000e01c0341c100a10411000c0402441e26000886070340d211106000c0c5103a071301c10702c50207000140034080c400c8210484040f401c0c607200300b08110058101d40a0141036040040d4002d8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 238246996 1250 238245746 238245767
    0x71107180504060b0306130c0b13150201090203030f0d0c080702060c090d1509030909020a0903060e01093003020f0711010c05150109050903090a14010e0604030c031101021507 77
    0x4032155602981d400340d4030305102d464807e500d40c0303004013200344161500030f2862240350040070214009200a4101d0110030b0300900a907005400c2d1501c000722081c1d0124054a070460000b90540004266507606e542244080c19000ca4201d006000591904c14100c891540480344840180c0c801004140c1d040121001000c00c81700203018446e502c229a00c60031904500e9100384140790340d9505140042c141d000d10000d000e006000d10651502c609130b00018580c0106000c09402c0315034400c080e10807102e0951104031181c4d40a5400c0c0325900794052410418042151000c03082c00020b0312400e9210b2082c4211040e13040d00701106810040e25407500e0b00c150146110107411710000000d180301040d420001010311540700408003d05605100035030003580d40290000c90076900a02000c0050f0355072110040c1600d0640400a40c1c0c007804400403104528003611081c1c000e10005004018064a8511081135a015851038001160342500483e65000d00c0d0720b050711039107002004034036038500c60300c0c0f41c44 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 238248246 1250 238246996 238247003
    0x706020a0309060816210501032a120b1e071106060d0206070b06030312100f0e04030518042705070501050f1902010f1d06180309010810120308071107180504 69
    0x446d9a0301c0386101c071040318820380040d941070103c2c545080d08441c102206154a4052005c400031091402030a100f45684036640181580c0f05070300003c1d18440c001c400480340d00482002c558407401c06a41c090f2207100204075581c1c1900500000500394206140e181d1540356000c0c205a1425010b510707001c03400030f80540480c1c1e240c01704010040010305c8440405000d24408070b64038403668981015511842d61503400780000d4a100700400c000310f5049000d903403043e16249007000d200b00e444c00008006000c940f032210b807500d03404000c1c10300741070a01003143c008034880c1d0211456a6158801514039000c3e904603a407a43d0420044802541d03040f1107800d6520200d40000708048008070f020b2030960310351482070421401d0526042d0488070003000850b800c00c0e0260301810390305058448180e200c0c85203c40c00ca050190b50340118440b1800b10410000400301c400d41034035500e0241c50000e19400f019107a07080050140001d001c000000446c0444c00c031500104625084107842c0703240d90203007070003c20a4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 238249496 1250 238248246 238248287
    0x3070f02030c0d1505060102011107030e0a05060307020109050105090303090c060a12020412050c0d120c0206040f0e090f0312060103091a010b1c0501030b0f0402060c0706020a0309060816 82
    0x42c599526803101c0440440d200d4000441550942e40f500421100000e0440713046a04180d0040885146801180e07041c54151420700001c02084e000710305805001c1d40141d400182c00420441d0b025070650107461103a00c070f84020301054660b0303d40d0580d41c2c001a03a8075009500f00d40400401032800c1401000315100c1400e0045075416030031408412600190f1080090100540c9080300300641840480364240302101c0400d207017a031549032801c51030715161000081c4104c5d41c034047c0039551500c0c142d900900300303503a050a6061700c50408111034642501c3c1c1a078284200803c0803803c00d00401995103a26080d403106115555141c01180034000c40034040c0c1c1c0c072103050f5103201c006005c6100494040e1119a1800790f40d0102c0b4814412000c02010400d5411854440144000f44414011a030070a1f0b940c0000105901c4500000300b01d8412103c0d03a4407540310307002d800901d044d000b0a000503080d001e5260b000303480f6a034403000d6618078021103640080b1614048810303010750154401010000c1c0600d41ca = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 238250746 1250 238249496 238249513
    0x10c0e33030406020a030c03020310091a090405010b040c1e03020307031d06090601050f0607060b150d1401051e01030e01020f040e10080a05070e04110d0305070b011703070f0203 78
    0x25480d15078001d49043da61550001072030300d003054043c010301160504030301d411071075450162041000030515004082c40b03e61074400140c0d4400010201840c0c0800090401302e881c1000d2504500074900400361074025420300590300309460103182029003a0403034900107454000c0d1050304500070340c4001c0424007415038900c4400030250548100d0800710032150b00400241c1080e804075850540141c1c84a403042211303403452002a1240819250190303807054010403020b48101c00200180091406190740480108001c1800c3c00c2a810092012450f244071a0850362101c00344078248034a8204c200040404125145465100350700001082c58460001410010341100301401079100e580001080303403109051094038a41341c04080001c01281004022010031941c52903214034082c840c43c11101003100009040c0001b040c45250720400040c48110941d50303510b4060301940141c5019103101d4400300022456035030142e900302c0c505451000440c2403a4040da43e41080d800180400ca07010f010304980d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 238251996 1250 238250746 238250839
    0x1050d020c1e0a03030b190603020c0a0b090a1202010902010c020d05070902040f0501080108012d0e0a0b01380f040305010c02070312030216020f06070c06020d02010c0e 74
    0xa01412420140001d03200f410032a040040c00d80d071100100920841d40600000030072040a5440c40441ea120700300541c03540740c0c0801da00e0800c0e05207078001d044070745180e0401161600106480032410b20030490316081c241f4a8070200d00702ca0300740300d000b80401c640c90504000f600d88041c458555520400454047ca500e0f0180030059800c10350001c98030024401081c04103680118290307000d40810f00c020003510380d544c0301c100c1e90b0340380340ca03042e600d50340d903000c840c00080707034150403a0064009030003c80e60000043d141505030301c03409218070032030981c1030000046221144007501e0f01610381840140b00c01410b4030404803441d4040e58512003460820000003000400a00035146054899000b500019185041080102010714941e504061041100c00070307849131241c050f860a03805a038501808500c060201e262841a00f002403c660281340d400074101d136000805000c0c142c05907001340088600d24105907183d458003900c503a80f010ac1c03201d0101c0308442d081002411070041c59420146481c0c07444 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 238253246 1250 238251996 238252033
    0x60904061e0606090e0606030c1c021c061710020f07050712030f02030f040605070201111005011a0403200a170c15030106020c010c081903050604050606040501050d020c 74
    0x100c40203409070301c0c0e02081101139003184240008200c01040c491071441c0c40f80c002003640c4030081c40c0c00000c580100d82e404102c0d014245040c881c0d00c100004655a2a80200c40c24022003501da01c0c0c00c0a42c01c013800498000741d00000486204150b0000300300b0422081c00c00da010f9008100350b280400ac0600044021510800075540203018107000c1c5189289642401801c00c03d1080003041594070800501241110010459089903103070301d002900c6241910040310800070031400c219291140321003a52414089a1125040380e0b4103442e20180d2070242001144a80a01e110142404000d100c1013220000341c0d9030f030804a410020910300d1103d0710f818100000d5201c244000703585911840e80041d89081400d08017598110035000300d030440d0f01d4904000d42d9031109510310350410030484110301c104480a016109850b580000092010611010040060604580e840d100320b060802040842c10134608a40c161a011b940f02c0c0e20b410f03076500d00403000c0d50142450060174803035600d00c3d100380703c000e4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 238254496 1250 238253246 238253291
    0x50f090d1509060b040f112d0f12090c0303042d0315140f07051308061302010914030a080f040801091101030b1002031b0705090106090617060906090406 67
    0x9101c0010218106014041207552005026881b10301e009100401078480742d00f40e52464000c80c002d00f4000c913006440421200b0140b00f5a01040800b003851040302c0203020140012004000306c03006c05039200b86101d40d40c2c4a03142c01d03664154104000600021a5000a440580744102e0100701c00351310002e0106410301032540159186140c039014402c000c0560b00030020280d0403030b007001030f441c20014030400b41c0c142c02070106000d20100064600855228490719030003800090180c0d003084c6407087e03100c12038030304611003240001e65200c0c01099010318008060950b400c007130010055039109a07606c40086e400810a5211008140800190311b07a00b4020145000d10955101204d01c0d580070025059400c03c43d20b862044080700007156040e036000084e0707070302c4000030100320211200014605040c840543c0185810000410020038500d0700070003e801103c5060780e407151105c6001c00c0c01d00c2c0c203801c00c0e1803d035030040c1c0007c0403038024609400c0c1540c1050003482c2c0004c07000b010425027045540d03030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 238255746 1250 238254496 238254503
    0x7050d1515181d07080c0a0f03080d02030a23010609060203030405060f060d050604060b040e060402180c07020d0f050d090f03030e120102030a0e0d090602060f04050a020306010f15050f090d1509 85
    0x11111910b040140161f0020580d04140500305415507071402094010390000742261075000c000101814220340110a00c141029140100d45111024240501c10240600c0e00464007080300003968500c00400c4034400c581080c0580242e03280c00040f105801d4001e41000d43c4040301c0010003002c11410320000d4001c40c424800043c2d2270901c03d00f48815100480e00030341c40d41e0007880801000d81c4544030500140d2a060b000c013a000c0c0c0c1c5500d80c0040c00e00a034034021750443c0e40c8102640401494400001c80107008504882000700d01980891b1589081c0c020003410041c414002c0000902500c03c60344141401060f40d4000c2c5034007000c2c0750881c0c00c21218501902c0c2c8404c40ca40084805001c1a802c8100724900080c18a00f4064042d695003409000c02d180800c1e407400040c1444014031001801c103a00805840700ea59607444201c0c08040c40340550b140c0c80100c54406044140a40100c800050316040c945060400300000c01020722181c1e141940c2d030201280102441711b00302e12801b101e0710321 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 238256996 1250 238255746 238255753
    0xc17060106021e1906020409090311060a0207020d030e010306091a010f050306060a1805030a050f0105060301090b01091d03041e0b1303120207050d1515181d0708 71
    0x50010003d1500c044807000b5030070454040781020304002e000c510303211840800007401c01e2004c01d03490070600034820342c1d0040005e24070700100c0314205030b4840105034101180d40d0403106151034041081040307120b0504001d61040000c100e02c030000380108982050500141000103030b20303030341c0c0407090182c07611030b52040b00d103881c29030a00340190380100704503910910500c0c2c05829407801c840800c080313100300300c1280113000304104103a123151541c040201c050100582610180c034540d26000c1c4c0d54a541c21500680c075424500040c02900381442840009902300490420a0f464000250300a081d2680d0600780c840307035404462620101003000f000100740764200e0312561400880310581c0c69141d80c010340700707800b420000642058580121072065030780000c0c10a40041d48403205915010007540318540115004461009015801c0000c0b5042080d602e8107011114456640d200c00c148140a03000e01c1c02c03440301441096007030a50141d001c8090f1400405860a03998507850f241000c40e500c5101d00383e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 238258246 1250 238256996 238256999
    0x7030905030d030903020309060d0605130623030706051612080a1104050915060d09080418020c1e0f060f1005010c05101509090f02011b02010206040f0c170601 70
    0x1c0c10000d0740b0124240b4074040100014995000f03499124909010340b08190110301c840e07802030b00340d00060080c00024902c0541e14807841c285c00141c0b00b14403c0e00c8070340320551120710a04904a20244550302c00034090712046007851130a44a03a00410704081190b80b1200d4020000340c03810b1000d00c102d100c240c541050914005840c40150b0300c5094500c015020248003c020984a08040c9a04511000340c0380c014000f004000c9906405880c179020006070404801906100c03003d0001c100f51440c4603600180c0040d81c00c01d250607482405180700003940540c0008414802c99000401200071140640d107014004010051030048255080d00c0c0c0d0165440920900b03403095001e0f88002c0000b8240306100d4800303600c800d6142e80501602e01105c0c2d48500c01c0f0110007568ee40d507400608444e4604012071a1107003810914942c40703410403070105000504540d21980345003c402d0056034160300a1000303503695079070710900d049204011100c08621403c0480d81503aa04640c1c1b040e10710031030043c2030b80d6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 238259496 1250 238258246 238258249
    0x50a14070c03061107170a03020f120603070f060c02040f020c0304031401150b030403050f0d05070c03030e19060902270a0b0609060403140a05031803061b040612020c0307030905 78
    0x80300074201d5000881c000300420300006d1990300c054540d900c1a0a41251603808201e81500030b0b00c0340e106e81d0000b072500058882400f01075901d01600492055040320001c507103030581c00086030749a02800012403894605400140740642045c140c05203000d4000d42080400c055642c99500070b07800c00c036048019041c1807001d031802441a00070a14084540310000c501c1e00403000520b100251001c0d040020010380d05034091500001c48902c03080080c001c102c0740c586040000c104481600b42100024141490b03110300c18000141b10030202000000d0041c82c4100e41d8850700242000402240c22a10f100c0300703846540580320f0610010f0206001e0640d451501c1b007120012a221185094030920042c41084055100c540c190350a0300c0c1c0c000d83c0c42540d45080008545801c036980d0b0000c1c0540302c002440c4960b84a006560060000144d04031405501d41040c10400036a00d4682c100104d4000e00c420002d862142042c8012001aa0703801841c0442c030962940c00c2d43e022180690218131b42840c10800da = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 238260746 1250 238259496 238259501
    0xd030309200f040b010504030305070303140c0a2601050409110402030406060f0e01031e02030118050d230d090c0b0c01050601120e07030311030c1b0406080d020a03050a14070c0306 79
    0x2d280003100e04000d448280f00021b0101d00440c0000743c1040400f107021001c0600985c455400b4000650306181c0ca490118036158440e03009509290025030524180c010041c55508881380c06030071440041c02503820181444007c1094560544518550f154031044603200e500c0114061406400f02107200e6040003c24000c901c920703801444900892401000803500c40c1c4980030601e2600c00925030300103100e000290240002e8066002c402c0d018411410402c8030001d9a0031058045071129611100c561194000710945030000c06600c4070304100c680c0042081d94130940b659841a8080d0540c15203135131441180380c0149905403116075603402400713455038109034000011181e8640502284104203d030319100e1406100040c00c1c80031034400c004101c24240244c6908405500481d6100d84a41e1f07140303800e14810030400d41c012460081d000c60ba10001147d400303000c14940d001004030201c00e98045520364060520481000480c40c8110048c940080083c00040e0042084841990450400904 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 238261996 1250 238260746 238260769
    0x150204060f020708070905150913020306160507080309070f0b0a03050a0b1e1f02010b0f010203091e06090a0608040c0e010f0902030a09020303120f01050301060e060d03030920 77
    0xe5503c40081085803040000b1010141e981702540852a5194500080510f00821060f42c0e4000da81d4400c10881e104881942d1090600850807140c45880d90303035440c001c039010a8403140008170100508004120640021900021848112008156a950000502802a0410108080c1c005044140d82c1d5050191540100900404000c0202e0350400031707030501e011303c0990a100c1c1490280b45010390b200960010007426840c60352038024108040240206240e42185100301c2c07000b406003115520002c107980351504007500400d40110000401c410a98050000c141d1001d0b04008402c0c0b5511600000e100600081e2191025070070146094103182419401120b1800c414000410040100c0901070048590340180140c4d81c0d11030030070b91030103410002000303074040c88000b4403015080c0039001a81d10480201d00c0000f0a6600c07081003500361002c5103c0c1c81d10619105020900c1d03443c1c18401c0c2c240300380c413070f00b00090242015075540a5610300310a10052081c14040118101d00300540c0022 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 238263246 1250 238261996 238262027
    0x22120501111c0b15030112020405130b06060c0111040303050a030b033d1a120d020c01031802130203090c01174213140615040315020406 60
    0x1d04001c041c0d00c02d5401c2194400118900c9902c4540c01103843d100d014541410506844030180d413903840700603c0d421262a444101c0c02580351034005002d40507a225a50b14050740f000e110003085e142e100c01c06c80690401e4050098655031031201c10607031841c480007000114400d4550307580f282c4076220003808803049a46001d000e86c01005040648240b4801010440103000356280c001c51482c6000e8402200b4006480390301500d004015028440d61024451409408079050981c1501c488803540d15404c6e07030050940940d0282403202640d40c02500031510003d1124043da0440c0c0c002d40003d08680e030024104590b036a400001d220096400340400e05051800307091440c2e04910110100c2d001d10300c010104200c0004d1000816110304a0034207849510b03000760400080b146140b5085105034025040240c49400c1c0e104615500c41c071140544002140d074a44848215510282440001c01c0514400070b404031017000301100040d502080c42036400c280540040c0c0b5142401c2c0f0242c541d8480c403a051 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 238264496 1250 238263246 238263281
    0x5070f03030f2a02041109040501080a060507050f090f01050705010c09090b120721051f0f060b0306010c15061409010f1802070203011107030804061407090b22120501 73
    0x59142d03000b150110000f00e0790507580016480c10350f002140d0300380160400c440d0310078108400000e000100007400074006001e540200045e4480d540142c584e4851140b9011046e601880100c0b482c1c60840c0c005042c58006040c410b1605c000b682c4c4150845210054880200380001d90900010340948260108080103807025540c80c85004a90303543e0320340b18885d01000d4545000c1444102903003141038598140d01c502101d40034001c241c40c89070300d04102c2c14110480c500d0524106040d80d40c0d4010303401196201c84d1303030a295854000045034403d00c3d8103010b9914800b410319950034580c00d88910700061240000400c0100500000c0051f00181070b0300c82000801d011400703000b070945a403400c400100c18094016550001480032078054003200c52a088007642c08280d050915421002c081d00c035a100b10b10403c2980400d8441104000c01a04c00c080000c54401090000503071006c01818001008494185262951302c0207a00c40001a04030340d240050300b28080c030800009000b40203a081e4071403020b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 238265746 1250 238264496 238264547
    0x10b03030711032503051009020a060c170f0d0f110a08070912060203070f03060f26030301090c110c032e0f02090307060903080d0905070f03030f 64
    0x103035490165440260030035444000c80481990104040d55010442100307400303a29108200d031410b08000e502c016603850150b028624805540c1d0300c41d2140c03540d0b0041100048505161049641d4048180111030301d9130b8469080d1007007070420010785000c01c0a005026581c142c1c26108406407504109042d84031428681d01100340901d000a0b41e87d0080130b494000c1c1281e680e5041111035078495400007000d00a48601d400600003a07030000d5124520135200c070401c40c200706100320100e0b04213104240c6001c0891030103001c25400b01d45000204a1a0103002c00d0007900040c0e51401d5600030b9020071401559046a064007a030032455030311640b030311040940007200300707440420b4030f40b000c40b440c50890800542070381080f0450131a40c0602c409100808015030f8684241040007503014440207031003880b9018000403040e00c238034058400d503035120410500f845035207a000005022002c4c01100e00e4000d058002c1290450380380d4410085000c0c0c3e07104c2400c0880c601c005050310149103042c10075003085104 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 238266996 1250 238265746 238265749
    0x60c0f0a0e130b0301230a0903050d0c050403032d05090103061d04020f0909060402040518030d05100f031a06031c050405011b030512040201022e0f05060102100e030706020a080f0108010b 82
    0xc6d0294081015800803c250603145411951841950840b42d0820f203050500d6800e240e006c001303003090724802c0e21400c038004805e10b400c040038183d04181c01c110040e140e40018040340f00704094541d041040c100881c4050f125000c42420803158440d490300403002c2d01c100419807409040b4460030b00710540d2809900d042180c116034582d6401000a030040341c0f51000701d00702d0380e542800042c40d0f50104080d01c0e142c2840f200c1050160200b56644683c0d11a007550109003484603550314001c4a40c001c420f4501c68030402003280c0aa40002c2c2440d0381401016412480040e20800552101c0882d9541ca55641d0910300054035002c607054144000a42c980d0340c10001a40000860f110820349071107070101c0c0c7e600e5200403450715014444801124007800780005174115014403040c40b80419000c28000c1d0510880b0440c101e410440303140380107a1020f092002e00b05015800500c00d02849403e0b00e16001854484078240d900603032422001410410803c041d80c40b0598200d03002d0541040203000d41400c040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 238268246 1250 238266996 238267061
    0xa0602010e0c0a030c060807201c02010c050a0c1109011509060507020f040f09020a060302120f090a030f091d090f0f060c0f04050904081209060c0f0a0e130b0301 71
    0x46c503001c1c0f290440100e8111f80c01010082c1c1400f1294903140320480c020003d80e61208503103807004a032005224003080c4254018024a450300200c1c0d0354450a1405900c01100d070007841c42000e60350301044540010007901c481c03a0207800390208401b01aa04000308000030460081c2c0c0d8024410003105014200050740c1d1000404900b02d811100401c1d403001941d007400081880b0700000358081d020304400281d440d01034000e040c0b0700113010800f04035550b4070013410000010071545462950030a80310f50300020b02840a070300b844a01450070001194960000d81c241038420024049050284000c21414103401c0012400010ba4079020b0900c41b101a01e01c950f8506028ac05041c04020104031602c41820b20381c01c2d10b0050600505e2000b040c206030805140d00d510055149040010100014030702500000b5820b005001c00204240ba1030482885000f80f0340103a00c840c0108407104050045d00c4e13460066210b00c0d044909130001d940c007084000c02d421202c00c2d03440640f03186140f440351080e58107001d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 238269496 1250 238268246 238268249
    0x1080c03040c1a0d0f05090c0105120a020307120207033c0302030606070b0406062c0f07030207060504232a04150b03060f0607050322050a0602010e0c0a030c 69
    0xd03240c5241c040710708503c001c0340e000d99070242526610301010100b4500307141e004140240000000d5541c4220a040112080d1082c1c014030400c07180c840000c030b03a00e13061719070045a000c2d20754500346001c109a1407150080c0d90148400360b00041054003420385039155414500c0c80b0b0300c5001130040340000001c00e15140c0d500c042949005141d4040009540e507112071003103640050f4443e9440100d4582840c201009200c00d001349015030921849401f43c1d041c19000b0009220001e2099602075034881c2080003991400800c0101095000c1c000c000004680d070040a00a41c0b08940d0f0030405001c0710305418132000b0b090321200e070b039520a281070b4648100512448104090641c140c58070300c5007207008100a0100c00380d030f02e1b030180c02108001409100c0301d0091400b501c400c4540d102c46c0303105041001694000e000700500f540e00200841c1c0d0052a1051100c0d24244000d5240d020a50b134660000b0b503004569480500581d446025030580e80350284408000041c0403980d981009007903440e50400800b15 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 238270746 1250 238269496 238269509
    0x2010614130507090b0c071410050304060504061107060209011d010e0d0c0f080604030e0102070302090c03040f080a050a030f09030e0d0602090d030504030605091f0207020a0905040303020901080c03040c 89
    0x200c5003c00c4165209001c01009442000412950b4280c0c0354800c0d45c2e190824851a481006084030310340703040c9408152020000c03000d9864600310740ba5901d5140003400003034011145165141e41181d030b286480c1014140b094041c000c010307110303894003002600100b695407912502e0b490820203107555a0b00043e503245032207070a44600740146003900e864070307695440e5040301d82c1408a001d07000828020004110744070310b01c240c0d80c80d00c5031080c035070041ea50f408d020302009501035500800503464459250107176503c41c0c000c0380c4201c01c401c22603d55030f140ea0b2003841240c0c002100054228044d58050041d02c01c042060380040051940988008102c20600bc1059103d4910702c0783d500d05100880c3c066a0300600014246010561a490301400e150b100317100032142c042c28080001c3c5020002b043d04a4040d405108255441d0140303e20754009503c520301c203e13031208070130002096082e1107204080c459807013628010b9803007102c0e50016208207170050091608000400c100000905000b01e0203040328031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 238271996 1250 238270746 238270751
    0x80a09300905060f2a060117060103120c030c060e030d0e060c0f0331140d0801060f02010f0f090c0803041d060d08120114040b0d080c0316120201061413 67
    0x2110303251a00c001446401c0c001d401c44118418036180d0308041006d40c1218407850840114009048031a502c0c1e03142403001400210712f00c0c407000711075030284038240966880303842c000c941c0e0609580c440085a0f0920b05840b003d900c04600c05801001c80e100780580841c40344024062864682018041c51003004121400803001201103030340302010b6a14a00b001c8820450354641840002c110314903500060808d481c3c03030b010101590749921010908044003000c5655007503441e07003415020346001c00100340300d20466680e102d0303a00151465202d40c0c40c00c8440c0100206440803207041c43c04c9004180c1d0030811158104100c108905010780308506028030500c2c1e01c2401c1c580d1035000007070250540020181240d880098201c003202e0b03202580a040c1c60050105201085181c410321040f2024544840c0e000300340c1c40c1c6070a01060100d0003504107400d00b10300704c1e0b1800180380c0345085001400701d4120360702e800040041200b13540a0082e000640200a41d81070703d01039000c002045000710200000a03181e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 238273246 1250 238271996 238272007
    0x30213030807021906050901021207030e090c130f03050106051503010e06030106090509033106032c03071a04081803010f020a0906090b070302070303080a09300905060f 74
    0x4036101c1c84214080ca43d140a0301308a6130b0b0700405485984504001401802503510180b480b00082083d10750040d05542da14080c807080c9018801d801d00c0c003600c0e1801815050150350b4050342400391401c041c080d0703030000c1e105580ca10b00e07241d401d4900e07030307003105104aa640710880f0b41a100501668115500c001d05405241c50380c102103401400c2036000640b446007480c00300007001c030000009090083e18a201c505154589082402c0306450f07402d8640d1400d19001c0080004a00c030741c01481501c1c66001c190082580702002010411a611010003121b42000c507a0b1002c0c49103054848404001104c0190514a03241d0340705d84a5105d2400d44017000510310758201c006840035030191705010700c0000210343d6501d0300030b8040c6c425143c40c800c01e00002c60f0b03102c0104603104030405542803103a140d00100200d034210340c1c05840c101c0d40140a8891150344001c40390201d0072141c03a400d07808030001820b90340d071000804c04102c081c01031980f1505100b055107082010341c42c0c100c1242c03ca095100780840e100c9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 238274496 1250 238273246 238273249
    0xc03241008030a0905130b1509030102040f030b0403021b01080105061b070f0f0b0705100903211406010e0109060503090a02060c0d0305160f030b011e031401050103021303080702 78
    0x180c041d000341c002480003242e03280a094105a400090725802c0350250046460381d1503407800c5e03d0380341c12040e810989400c10b0f01410386100008d4464108000c0c00941015100c0340500c2c1c4101c1d543d0300c1600c2c050180828002030680600054018180100c00a0700e0710100900180210340180314007406544002588142042040101300500d1500415030792159900c2031050f8a5209031700400400c003001050000d90b4011050450304516030100c05004411213240701000240040003041e0203100071400745451894601c45200c01420792800002050790380b84884440d01d0f00010300301814031840c440200b4850ba04019000304490b245c0c032740a0741c0c0b80d5030030081504090b80307e4802500254003203103100c01c88101089814041803203030b9080003d0358800e94100070441c3c2c07444418010030141c10302e612207188650040c00403480c043c10004807401c640c1800c041c1c131100b1986130100007695081c0e6442c1c1d1200c291181e60041009180650418006407103c0000c031410b440001c1008000040038400c5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 238275746 1250 238274496 238274521
    0x70b0105010c140d0804050706020a0209040611040f06020604060c08040b061210021602040f0612080309071d07030b19060e120118110a0b09010e01111b030c0324 71
    0x150351000e010b03a4080961380c80081c00c0c0100c141ca0456580c0600d4a022458a10015480f100369400420845554440ea2500002054490114014010f0401000c00d50381c41c94480c09d001044c2a40c0100941e1405003092400c03104c800320107000b0400c40030144808550b04400880c1c03ca5800c4581c0d070725005801d13509500d400c15045040d585a40007141c0b14100c0641c42c031510000e203000341d80a2184040c0c8106460032501103004090054010915410214080a000c0e581c0145a2400c0342c42d0507486443c941201e000c1c50b0a2064031035003010400c4412076150082280707490050315203944a090207180d20020310700c2c41c0505401c004005040d010159504400c488648800c00020000c81c201c03034a410f10300280d131040035689131010350107040e00c3c0d090400e1001e08460001292a00340f00d614030044461000340c2521a040209064030841441014030469502e08040c0b0b05091400316442c041c5030900240b641d03403030b109401102400d0402c5500d952066080d99031090340c90b00c2c0d6030b44c40742ca9144 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 238276996 1250 238275746 238275773
    0x4050108010b13240210020f0f0c03040812030402040f0b09071b1505070f0f090501120f06080106170a0807020103111b03040509150a06080a06030b0903120c070b0105010c 75
    0x1080e1a040486204138030b1014200655007050780d09480e0b0b612502d407050000e07449080001401c801e0200046041c034820000a0300c20803540d901039a14150350303401d4641c6802003401c018010b601c000428002180380a2184400491240000380140003902c00002c20080c0b00501e00170500981303124582c0001c6040d44d00280c400c0d40305035245c0125400e150b4074402002c04447c1e88000c0349982c1c5102c0300705401110b004804ca000c40c1d4840d0311403804c0030011501c001204240c0d98100361540140b01c0902814041e03d000b9140c1d40000003407191a00b00c0340100103c1003162041d0fa50000c1c640714020404a20850311042d80a08022800792480f001140142c030a1814051528112407030041c03120b50048010401c13200300700d6800b81651540d103000000803080030085035211840c0300d0104200d80c042c80e011a4410401c01e00001c0196898880002e0781d50101c94205181d0000603020520108a2401e6604103982e00704070350030720017a560348940110060080c641444403024803d8100b0512a00124 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 238278246 1250 238276996 238277009
    0x31020a03061d0a110f240a050c0f011a01050432090f0403080106140d1d030d0906060f0b18031014090d0519030218150d050c04050108010b13 62
    0x400548050414038010022111042d01c64265280c03d01d01524041c43c21103030300c040c0d51b240f41d141c10201c1418141540d0100102ca13060040612002011702001d10443c0c0307a0141e520000304d0180d00b903040d8440c24011542c1d51328144a0180000c0c0031074050062180d10650308100e00c0311903101422510008002130440c0e00ba03003e01e001040200d060184642103009512035141c810540e40c03600c409a483e0794800340d1040c4540d100780286480044680c1041c2d1940001595228120085081c541c2c11640006294400180c41d900450b0030840c1502ca010002c040340e402c440c0034641001d440d04168481d4140700041132240164110803584d083c0b01c02038101480c04000c22040411460b58020080112801f00c01c901901e40300b0301089010b05d0850b00c41030004a14404102080074081e00250403001d0091003602c84e142c170038402c50b140c52901c2085481c540202d1501d03800740c03044050956030020018181e602d005e00c010022a42c0003111641074401210301c25031070364400c555000d9800c01311380c00308 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 238279496 1250 238278246 238278253
    0x1f0f230a0e18070603050705090118080d05070b090303010b040308030712020d1a01080c030a0c0509040c050c07080f06070e0103020d0501030c1703120103030c02130531020a03061d 79
    0x100e200308500c9202c000300325040b82074540d955581c00c01034040340ca0450744500806c0041082c110710f0741c40303400d59112070307017000d007818511350b071203080c0306280c403260f000c418020510000740380042c0002c00041540c440a81c20095180d0b6041c2400032516009500c8000d03d640008408680d0a03070141d44552075095504104548410100b0603c002030411f080381c400820021520030121548550b0740144206040240c0e140740d521542039020041250381c00e104100042481041595078840c0038000c4514210381c0c4840e02d400c03840b00c119041208940c801039150740544a150f00810012030000da2010031428011112104040147c02903c620700d01c1c0000b103440c01d4004410450100d4105080c1c500003102418442d00c441c1184e40e8a100d03449600c40c1c0f0040b0359004000291103400c100c8481803000d0203418030104040804025200207403013541c0801d14600c070b05204035040214a0b0441c2a40300840721041a164022a11081c0ca42c000500300310b448440c0c0313041c21011050782400701d80d4404200e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 238280746 1250 238279496 238279501
    0x3151d0109120e0402030f2202030307050106080601150903031b06230a0b090109050a110a0c02010e040606050d1d12070c0e010b0406080901060e1f0f230a0e 69
    0x4407000c00110720304007010035003410540d125801c040c800c0d2889501f0f1301e1802100d507200d101c0804040407403100c0f4400c01c15000308140300140c40c240080c110322445030700041001401c2495880c200303001604032240c0d0b0310408007884422541310005404a85c0c041c100100b00840c0b0b200135220b9004c100030054149820108101502c050507400307013a1901c0300c00340061154464071051002d0f209806c0da00341c0c3c411003600041c0110605944000c1c6c00c40c46c0c100c00007894403c0740340c5a20040e085000b804011070b64040074003040d56002249010404c0b400c4400300704050030b281c0040c005000b81050710905035034841a0304800031416040ea010819110b00f11105c0d00c02d02011340e102548501412240c90405110015800031400400e6060700c480d4100d25080c5802c00e141141c4022004020304899034945038001004003646030664040c00d070300b41c0c03c540b03584040c2d400c0000205155000c50315503158041c04110031202c840070030f0401d450801d801004400040e0005003643c442d82c0110240c2e9800009 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 238281996 1250 238280746 238280753
    0x60c2206110d0503070e04050a0204030609080304051002030f0a09020d06020d0b031b0a0b0a0e060414010206060f010e0d02010903050105101503060f0512101d1603151d0109 76
    0x1d0740341e801c80140c1c1150303503001001000b00c5650201743c410700085580200004218503054100c50791148031300c080113051a503242c440c807013620312001d0705880c0510b000051000340a81407000d4a0440c0482c2001e51442c1024022107580c01d0000701306840141d9501455821503503203c6040080743d230043c100755100c121000c4004020600421058864483c00807180100c5e10030b65420300701000300405d5410010318100145845500006c0c4400800ca5500c1e5059501da40700d40107031000d041d031102010b0b1a081e40d0000a03241080243c0100c1c41001c01c0d42c030070401a80e116000022905050f5514400d0346614401030f00d070159550030090042d42020100041c41d204412400c2c121621150b031b5251b07514002c0829002c030788050190b4240414402014000c40c00c0c1800e5040c002c1103580f0454a88410342040d0780112031001030010001c100201001008010411444104241c1c00048107849443d540c0c6201c0304502880e00c47c907045403611002c90208810701050500207224100900880b8110314 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 238283246 1250 238281996 238282007
    0x140a02090c0c010b0d02030a03081305152e21050a120e010f05040b0703090305030d0914071d040507080f0a0303051008031b0102270f0d05060c2206 65
    0x10856241d50718001040d1044c1c0780060612002c5c0d44c0103005404408010340341200c000800070828111440c984420743d0020b2801c110056988244400880050405034002c8a00540300110150f911041482c2400e4003054018000300b01ca00800074144640e40c0003000141c00129900098107030b008112014082c08110040a600440f456032520000b9840400640d140040d043e10500000e40502081c45544100ea0023801141d010f802e00403109a03036581c40615540c04800000c3c5041d44920400003000f50754400c0c002021014030252403004d060003400d00b00c41d4084864a06a00d40d00d20101e418032100f4000340000d0b0840406503140715014624456482000074000c0300001d00d001c0c00526240e02c4400c0a80c2503c0720303e0051490101c8109111081016030300c0c00400c155400c1068a200d0082610240518400c20400c1080120400100002c818584103031274002c901f8007203013200040740444d00340d5110040d00d01581d180e0444000b00090030310307a1a1642000e121241d404514190800e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 238284496 1250 238283246 238283257
    0x10e120309090106020a050a060b0f0d03030b040e03090d20030f0d0f09060e100915110c060309060105091302040606030e06070903112716090f0b07140a02090c 70
    0x26611004180d0344e80341c007244d9881e00300c0d10144c0729400942d60500060b20700d400074115510014400710604254000040e1401d524150403004643c2d22801e158043c00c1c64052401828180405542450060004248158400703100280004c1c104141e50b51001c400c9401007110500180c01c03110003014020981d9614580e60b400100443d030100c441d03901242c89011904261015541c620f038081060b0340c14060000d0750150702c102405511800410007100700c5824110008241d51510b0000480341a8942007040e1051075070300400003082040304c110350000e0150704407003060f10a51074503070310822614500c0d00b0000c030083d409401c280d0009011a81504110341003007110b0b055035000c0e00c0303066040d02c1388201e500c002040000150351400079032500f051070808001c40d00051200c80000000c540041010403101c902a42282a401d0f003616540818698060400e9800d00c10005040c01f8045030b450250350401044000c142211500c00c03c4103122003405154083e002c1c03030381381c28805480c00254025 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 238285746 1250 238284496 238284499
    0x405120c0a05070b0301031a01150507050c0306091f0504080a0e03030d020a020303150d2004020d0501030f0c0f0e011503090b0f0603010e0c0108060907170a050403020105060609061206010e120309 86
    0xc40701090300c4c50020488e0781251107201302e40307600d001d03114000d4449805c110f00990b081c2c01407200400560f10103100981c8100d130000b001d403141520b0380300b0a0781409640c0f25000156441c15003080f0020f28603c0031119110404e0078400b282c10305110000f0310b548101e4000000c42400801d010034020740000c040d6000c1d103500c0c0e0003407080c45029020320007030300380c3c03403202400c06920090140d21039100101d403001803203005480035181002c1019054180d400a9000311460703030300044490240102c00da403101c05801c1480b400d05640c0e11717000d240c04400724180034202240504009482d1101e02030740c0580f4100340d015800043d585407030240c489110004441e400d02950030704406051020004ca410f045501058481604a4a46d941840100c01000304004c0a000c9095211818a110301074024400c500310b610100360362400d0f10f4000d0075548040c2403140901c8080c049008180d6030141520b1480d880d03c800d884803580c0300001213078541d8036030b28015009096203141c248a0130002c402000350440 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 238286996 1250 238285746 238285763
    0x30316030801051c0f06050406060506070b1b03010501020a03080717070f110610060e040f05280902090402040f0f020a0c050f0d080c07060f0c0914090405120c0a05070b030103 77
    0x32103050034548110966008000c170040411450018030144d02094005004640008509803a1000719403d5805600280e0703540100b04c007003050000074180150010154440d6050843d450040083c1d912001c3e0030000b003d108501d4005112a44a0104180c055080150300d010a08040303201410340042e061034200021004000c041c10701c900011218005d0414203034140841d0300c1d1440882e072510b05d6016080e840350316850742c99984409401803500030b0760321510921140c031394042c00800403110003d00c2d03484c09081c9460a005a030303441c454140d01540642c0e0110340702000503051001088844421580300e4408a14a0410307a44000c041000e1485070341102d5000007a9203c195944a070300110b0000a03601000042c4510854000340111038883c43c8007003105c44a0307400000030360f500700140d400000c15000b000c008031152200e5041c1407403c10750b07101000d0304268890680743c20640c40c1c032113412400001e03401c00c0d00311f040010083c01a000070684083e00d4941c0340702c10030f507070080c44160b41554 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 238288246 1250 238286996 238287019
    0x3030c0e0a06230c010f05070813020901121103060c0c21030c09060717070b0a0504030c060230150901080a02011b081201031502090307050f03031603080105 69
    0x50a00700d14080c1d074019214203d08248030480280c41d03280f0305081c000c07003000038020540c1e5001c0c240141004618008008601454002001040100010a800f018a40c0c40b035050026841d2000d02c241903682e0700081d954580b20320b040c81c06040300240c2c0340a415124020400000038500c101511200114400f9100802c00c8001b514003030380207007000901440e00800109018203034490003001500006080c00d400c0100c139483d0b800074103004012990101c40001083c0c400c1110b0711807550f6100d81020b00030090340c14140c0300104101d4040c600100f82c203030b0024205182c40390348a40c0c055040310884006805100002040c803500c0c2c0c059804401d40000c00c20300c1d9001d07140c0000c4960594080c07500070300207584160011a19140502d0041c80640c400d0385400c004141b400000340840303100c5507440013903945145018160342507840001080a4418481145260f801040c94011144111904080790070050b001909601c44d440b12a0710000e003000b5080d04164015101604940b81194040440c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 238289496 1250 238288246 238288249
    0x60402130204050f060c1e010204051f080714090a060c060c02070e0f101206140108010b0a05060f09040518010e06100e090a0c08151807120f02090403030c0e 69
    0x80c0650f01400e079205844104240c0302e810501c000e403012208140407201c90600010000c55807503804840c0005e940d4000900780b10030b003070504c1e89154660601462040450324683c0050101101804240420140704600e4400d085035209481c0311590052110b4a100d98585002e8030305010040c00f240c8041c20826271801d01d600200d03411040300e0460121000c83d6440f1002089031020081c192220f0700102203010a82c2901160181441d80c0f00c1e48000501c030340001c02040542c44141e00043c030507030421503004182c0c0c0f078000000701160b02c1030340d08644511500c01c20901307500481520700d070442d1500d0108002c84041c18a92080703082060002c0128812069425480701801c07214661304111138081000032a600c145003d42c4110200180e424aa88559401d01910b805a00421507680314514004420a840001f580c020000b010b22041400c107003044d0a845013400e22540c040564884d40b86001c0c0b14106064000702c0d64001c1c08442d4901d41407401034000c1036000e4007240040d01c2d0400e4803006 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 238290746 1250 238289496 238289501
    0x307060608070302031e0307050d050405120f07050607030c050610030c060503070c110d14060702100510030209060310060801020a03050f04050a02040c0c060f0e010e070f0e10051206040213 83
    0x50744d1300640609088080309080f8440910724003017600c1c00c1d00c004c110520200b48144130601c1061100d550701951146000c04000940d003084502c1c4403d070704034590600c003022000802c0c204130748055441d9903d44200c0d06041e592044c1c01d00c000390850141004100c16540c040c4000420340e88903004a010b40c5031252800c48550104840e04c0c1d010400340d40908000c104031440b03d441c0038100902d915450311840d0b82e46910050158401300300c580c0030100340584103406010010f10300b08e20001c10442031030081c81c50b0000e5800c41c440680034080440c081178803918144100c00030080b088038140700c0b5507925076140e4000d5012071101e01c002490700340400d01001030a031095001e1f0f50407074010134281e82c2d40c0d0200002003203101442c81c180086140d0210001e101805424142c2e58825030000e422190003106600351049112500000d030403448091055565445c0c450701500d4060102d032403107607101a281c0c91324420903004540d03c410b130f03a6091900d41d0700c00a03a541c030441c42a58801403003010105c00005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 238291996 1250 238290746 238290749
    0x50111030c030307301401060c021c03030204080d09140d0b041101121103151005030415020702040603080705120c0a0b06030c0a06090e0702030307052203080c030706060807 76
    0x207800402c04280b000d4070507145403c403501490034000f940100c480340c0b442c0c150342c80d50140d040c4c96180c540b000032108020006ea80144850700300900074030f41613800a00310710045c3c800c90100c205850307440c00c2454465070545002c0e003240c60071a943e1103800407000d02200e01038030406030449515514000c0604009544800741a4008000000764a5a6450504202501e24030504100000300d50104420250280a100051081043e9500e0500190404100a880d03003080e0140c18507030440b1403030543c05402c40350304c660400d00500401c1c01305120840a0704c01d1407400f9600c1420328030040207000c9101c1c02000640d214904076140002c4200100c1c24501079013500c80e00703a42014036150049003440c1c113455407000005064548014159000802880702500448005a25020700307010004000c099950407005e07900042d81146802080244544201c200e400300c1c0d5007040602e0600920b50105502c040c507030101e00310392a60031440710150350360420282920038500385000011480c10108a100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 238293246 1250 238291996 238292017
    0xa080609074412040801060b0408060601050c01140f0106110706020c1306090f050403020f0105100515121f0605040b0702090c0408061005040e030a080f0601030e0f0705011103 77
    0x4102003100d02c0705a2251295116140380b0900380d0300c0040b880901c00c6000c03507600002c2c0143c031641808501403c480c1150002d0308440000c010920004c81c00280039507000d2000d20703118cd030f195240d1917058003402e4410701c1c1d00c907102c100320300303004506074640d01c0303641a911280d988506a00026103002d0f40c03005070380705240140c1c0048021348e80c14144110410309080c0d044401150040d1342d4030588086900010103403104554403c01c0c4410503505000506101c03001308001c0c4030a0400b040c3e90f81c40d00c410341c07141d288110b0b0800e142da0601040c40044e1744000c40107005401162506910f0464169102c1c4e1900301c040306010300202e00640a601550107444e44107003160f0500241c0da00340200404003408520141d24241b0000900070300400c4900e200d01500550f021400d442c150900060307032903140c5906406d402c04c1c0076240c40c80e40d000c500d0691050911031004040c3e1102c10061380100840b4840000714090f100da84100210006030a07000c0b5002a643c1c1090300d03c1e21704050b0349901902d00b04c003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 238294496 1250 238293246 238293299
    0x20309040e160306020c120706020406030524040213030609030c02030601080a080f030604020436020720060f0406090806250c03020c0a060c060f0501080a08180a08060907 75
    0x500200f0095400340c04030320340180443d01f580e00601441c8032950000c220882c2c04680000d400d01c2169418001ea542141225a02d56002d040100d581324035240b007050414003407036021440f90404422818403070000c0d60400f00402c080000e42c14024442c8008281c03e9001e44a918000180341c2d42c00154204c407150080103180c20005140090031441d4406048158081d40900010035888c440c0b403000310740c02000d2020346140344107169030000c41c404100300d2410014070500002000c111098041030210303c0040c02d05400c01c0072031000542c4d030b025410850a0440340443e0104581342c1140720b840c1a12440342c1120686d9840003000782c88504545402c90034411005008035285008a110703030301c018442e0050381ca0101c8044007180743c40c20b84d54031600000b86e415144006201c00c500c0380e039401a9608800b4000c1c7c4d810301c176800d0365035130100000400c9500009103407071682c0c002410528155400030081d18510760380b440416681d03402a41d220146000e41800010b0030b94658491030820840306005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 238295746 1250 238294496 238294499
    0x9020306011403030f30041101030b130b012307060605040203220c0503060403030209040e0c0f060901050d0603030201050613050609040803060102030c15092109091e0106020309040e16 81
    0x703c1d41c81c0d006462031b82814102c140800c0640c881c0f00800c641e0500310724464804524290418120843c40d01d25101d05240c82d09002455548824900741d214403203a51f804940c0310b840c800100c0b106041c0e8102c0b8114098210281420501c2d540c0090103043c2c0104024003000780c0704c1d400c000480c4010383c0e0711102003092101c00f0300051800e0550360105800781d00b48a6202d550b03940420b01708174084900301e00095001400e100189414420042a1007081000384410759144020407640d149804805100e4034000c00d0030001c90703201d01d040b5408141000420700c05c0c030740d032803502038080c200070741d00d04d88036003100c00415603490803601c2502d101d680c0003089800fa64803540c8803499503602c00b500c4a81140000c0103c400b2404080200400c0707103002101c5019680740c00300c001818000801441e0301190b00c08400d00e40325000c2c4006035204550304450244564072a821070401c400144486c01d4082d101643c000501f403900440a031030640c0081d14203201c0e4910b500c03140e54031480c00f51203401131484a240e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 238296996 1250 238295746 238295767
    0xa1b09051504150b070606050a08030703200705030714010e0616030e0f0d050601170109080405060f04080708010903080c070201170901470d120507080d0902030601140303 75
    0x744460440d4001010f41a07484140c41c02541d444403034142d900c00d4655100300150304050002d00c00501902d4003842c1040100e65008003100381c00d07500100d54200316550100030b500c00384001c0c40100f000804403548965900b90380030140f483c2c846050f0100b600515110784034108a0b048500e0507c014101000e0700c111981c054940020000c040b83d0003088002c0b070803001d80c460f0302200300f0f40340c0910001c0605602d8110603527100308082c0c00580c8264100b02d9010001001c810a88050300d108440540c0c6641090941d01c426008990003600706104410300090946419030050341100d0103a038540095680708035091887c1c5c460010000d0001d0008030610350860401141c10f5080f80c80d00c000400c3c1000301c5440242001c2850b10a1300340460070556072000507089060850f68034400f01c1c4540030507040300c400203203a500703980e40140456502d4903443c6a5603218208603060640e2188078181c480500c03060001c0107010703004080303001e4032a4000109411041d019640340000340140158585444c510 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 238298246 1250 238296996 238297001
    0x609090d05070f060e0604050f01020f0409090f02060406051201050d021f0903050d03021209010504260c01060608041e080301170f0601060e1008060102030720030a1b09051504 77
    0x2d03058071440803450300d95001800c94050041c0c0120503e004104504240c20842d0400c0900404842c0076841000440381d1001c1010070b680483c0c0609000050079811418401a40c403200500254050000280498504c0d0020060140510046a5407089a0f04c0f042030001102c1e05050203035010f040c100e007820440b9900c0c07210b000c0b4018079181902c03007540c0e240d0360640350139945d11840e0046500868103650162079000059809070510000b400a42001d0311194004c3d240030702c00f02c1d0710004074581038103404404002c5485038103a8000800034141e0f2507200a09450054a0440d203904480460b020a90800b840d101091030304880c56a2031030f442c0c110300740e0001070080c035950301601907d4071480a001091100c18024001600c4201c4c40381c40740000c200b02c0102c8880c841044c13203503810030301c2240e036030000580e0b842c80da00c2078080303082d2103815001028101c113164800d40e0511a401440302000400d0701008000e0100440000300e15481e4101003003034170350480e140c40c0b45106070400084d5500d40740c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 238299496 1250 238298246 238298257
    0x30206010f03170a0507121101230103121e09050f010309030e0906130203010f030318060f0e060421050d0f1b020d0203030d0204030c0e130308061c06060e0609090d05 73
    0x4d0074141c1c038110302c1d80c2e40c80303400c1f41540f056000403c1034074102c842c041c6400c0c041c1c11201410184440c14410442452032440d0106000141c1441185202038010900420241440310750030440e87c03103840d4001c2001403203000c0d00c0c0603050040d100380038080c40550003401441035981c1e0588171100c01101340818040f01041c001d11a030341c402c503140d45107030400030300d4401103020b4003829004009150543c10040c0c021040c4458018ac00242008200207031303980401440344401c0c603440c00388101000100021268044c9030008032020f0251442e0f84805442c0e00014039400780f244065594034059440c013a6043c01b40c0842e5480030400300c05009104000d045c48041e6050f10080802c004088a500401d00c0e5070051003216900d00d50000b030600c00d0055250403000240b048111210440c549401d01c40754001072101c0080034400458042503141d0364a264410500c001104100e00100c480e06109002c1d0120b40b046001113151000410f1083c01c2202103d44a03070301c41030080c684407400030b4080301d49a000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 238300746 1250 238299496 238299517
    0x918060a050d06020d060503070308030115030207080f0711041a0622080d0e06090105120a0e2505040b03031606060e070f08070306050906040f091e030206010f0317 72
    0x110a030105440d40c501404840e8907008500c01603c2d041a50503680481e10a17400980c800d80c8140c000308000b0b200760088038191103040749102004204044181c000e8024581c006144200200d02400440e00e0b02c2c018080d00c5005081d201901c0369500c0074001110b51442c5800c181d0240c03005001d13010f050038070017001284480c8110226840c0c01c1d9100f00c2c480d8450760844002030b04107042d00e101089e03000d0b00c2e0001c40c4808036405ca10306000500080c1841c4982036150020300c01c001d0000f0050805903006110000402d42541d89504003800380145003c0558462800c0001100c0e000c121800d1610564120b100042d0055241140c450b080380f450710032108040350300b240c41e00e4012036500c9014141a000341d603140c44008500700c00324070107000041c008182004051030110204943ea0310400383c1600701c2401e9400203038400a8001d200d0107800791038405130502c0d05000c1410810f100102d10b00316014040d034251510740c1d803994003800c14bc0c1494800070300191301918590100101190050825046 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 238301996 1250 238300746 238300759
    0x12033804050c16080712030c1103040806060405041104141b0408070605130909030e01080915011526060f010f08150414090a060c0e01020712050111040905010812091806 74
    0x162503644420501c0300746c00900c0008c0d03c6020003c0300a802c030321228903d0321548051414a400e040070150394074401800c0d81d200716140c5011405011016012200040300900140094520403144031880801510501c4680600a0210760b0141c02d40781502c00f611004800b5201c0607142c9402140c49411044080b12a410310040c00500e010541c807542d100103200b622103c0700e820250001510380c44005043d081190010f115810180c03c04040d00d5064034010f11346102403030400102200d0002d080c44038203100d62408a41035405041e250805d500ca203500b11802c0c016004060700440f18104030000c0a03020510364008074152241c83e9200c15892540607000041c00c0c040c1042035520303030038241d4160391a904120102000e101450240302c002c02c816003464800707400c613480000c0d40d810043c410130303403208481854803040040c21341060303013000e200441d05034540e6101e441d20b8008000030702c40e183c95403003158811480080c04030103039a0201c50003482800001e400c02030742e0351070340c03401041294000c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 238303246 1250 238301996 238302007
    0x6020a11100905120615040614090703020d0e07080c18010e280e070509070c02010c081210080c03060106120b010e030105070c0201020c0f090412033804050c1608 71
    0x2129070400c2c6404d0240300f8003c0901d030070200d0005849201810046004a050260520603510034064114034100c0c107590004507552482c101328000e0003501691002c0604120141d5003c040006408098031000c030203481d81c00c16880c0c100301509454501c0c808031442000010008500f2284200d81c0c07100d000d482072064030902032074180d880300c803030945118a20395a11031212011820406040605426520090b00b030400c0c107000f0706000c2d0303080030007410480c1d400c100300e040225100c19990440c0340b2210382c0201e42071840715000020454010480c079449000d590340c2d0f0310b117400907281d81280c01544035045000e0412840702c000c1e202c0242600d040c000e00030041122501c091040c40e00c948081e983c1c81d20300800610009060401200f800c61041c0c140030218019580c0714141c0701e070001c4e880440070352a4000340d10140c0141403041144060f802511190b140c4c0d000c201c81548080034200000549844502400c0000b1648140c80009112070b0a1065851200e0061040c2540a004100550520 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 238304496 1250 238303246 238303249
    0x60311010518031c080f04022b17070506090106050607110409022d0d081207090f030510050c07050a020906030709050a0213062a170a0f0906020a11100905 68
    0x420440d0b0303e0f640400400d9010719913254441c1c8000e4100b0030849014100e810140c00060803c405228400440b1500502081c0c000307446603058110668003082c04107004400000c12102c0c0c0e040107000f990075006041c0001c200c0c06042c8542d000341c42004106605206403038a40c0003040e0700c4014040e800c030340d845014501603940d1400240340707020f00e02c3c4407800c150280c2640802c0181c040b9001e40c09001494001c0c07001a0261040e102041840c02e01c992055840101c2110781d040550b110182d1032070101c4001c418001c022a50701043c80c00d842c0148504e4842401c50441445840000b0b07116030030203041000103241c00300b2516007004004040310f00540e00d07007401a003110300640b001015182d000840c124402600c05003500201003074100403144030303c44454082c4240d003000722504500341c2104400304004d600d0805504d0a00300c5402d84c0d8551240031805800c8030882c034900c0e000718061403000908035100140190101c0e03448150333a4100740c1001309020140301d44550300c20030b0241d50300d80400d99 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 238305746 1250 238304496 238304503
    0x50a080f04300909060609090509030906040801020a0306050901122003010e010b0f010206390a020f07140105041e030602070b040c0609030218070c0c091e06031101051803 75
    0x507245051103030b6000ea03020b94080c2400d441c0703600250855003042d50410685401500540449041000200e403d595001d100c900b184101042954880c00118011540103c1580580f240c900f140d102048800e89a00400813410002d104101048070741094020019a840d4140d500e50510601c035440c04c90701940010f0f0a54501c80c480340066035580c03004e421035107070000c0c0010800c84e003070015214509044103d003401242806050241c2004000c0300c03500c076040c01060544600d410b24200d80c6600c26194025210808a10011218420901c010030320300c0700c407801c10020030700586401e0f01c0d19203800e004070003d40c0402c0020300081100d01000012944a00050103a40e2040720410850303e494034154070469800e4102e001001200801440184c0341d1194039460781b2010f11010505699098048071240b6019000400c440d140c0700c80000d0503203542c1c200b1180341040c020400300d030501c8000c14100300c0345144009882001400c0b9400c01c5540120010301d002c94501c04007803210010380740460b16 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 238306996 1250 238305746 238305803
    0x30c06011e241209020a06230a2a1505011508091b040902060403050a03120203010b0403060230010f0e0408030601030b13060f06080601181401030209030a060c0201050601050a080f04 80
    0x232400d908901e006040d102c004504410491080440c101205540000c0009280409500e01103e409547c1440e0a10000041300c01d02e9120f5080541e2200e02017880e03025090070b00c203c9030070314a107420b0205450b014400b40c41c8501142c2006040901d074425000814011504406401680d500214009078450400400245014034002d06010700c0c00d2500034140112841c14802c11881440180040308403002141c1c02c59030460030150301c50048009001002e07400003247c1c0a51805417040003842c44214104504036251148a40702c00ca54410303040000402c1298000c00306101000081c15640c082c4d44064041d0b1700c040c140f81c1a261381c0a034007204031142508038030907203121746204000c007503840a905075010780203107000c4681a1241e40038000c8540c8034000d01c0d16201d1082c100e00078591080e0b05441030b6039801401c450441411f4103000c001230400015000041d42400c0001d100c3d54010021155640410b6540310403a55500861403841e640140080b80e185103801c401400380030301c40d00c0b1100d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 238308246 1250 238306996 238307009
    0x7020d0807050601050109030f03032a021c050403080f0c0c090c03090d050405090423030a081617160e0a030b1801200c030c06011e241209020a 63
    0x81c0d440d00141440c500d0800168003150401c44c1c0302c1c00500025140c1001c041005a0508002ca10410400880003003030402854803180341005040041501d80d0025426091031204005850018000c3d44c003110303607210394040a00624400c00000441803101c4008145075140b401c00c2d50110540b600004248200607200740105200101c140a20320350240007209203c2c100b030420390301d42407030407011400704c0341700800240c030f90030180b687c204020380c40c81c685040c00e95025080e40c1c0e60301c000c054090415041640d81c00244815400e00900c00c0303014690260000300d032640040501d5076240b45604143c03e05029075004c106403024070404c59242c1000c00400755115800700d103030918110f007540c024a0703d4603000c24072980c1480222188911110b0789100380c0001a00c0407603a401c000300d030481c40c3d8031071f44603085071070300c20301e40005080ea804500c0c3c0310b451b14030f0958915105640b44d00c0d182200c13420100c00701500d114400c4214000c0c0c042e4000100c040c2c7d102e240420704846a0700019910886a881603 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 238309352 1106 238308246 238308263
    0x71802071a0a0905121e070f08070b0603010e060708130c0e1005010f0e060a1b0b0a050603010b0d0b010608060a031209060e09040b0c030c07020d 64
    0x1100310608000c510141d03818000c03032120081000302800d49045c0078801d03982d0720015910301242c000303150482081c1e413070f032091080c54802039006003022580e103030032014200c0001d0044006000024050000c0f440680f61140506080d10001545c02c3d034650088001c009005411460b142e400100394251009520000e1034042a010600c2d00141c1d1744034050805c000c20104690520b0081d6003003aa5904807808298005807540000c000c00103a200100340118850310b80701d06040444104091054200300c001600da04207405001e48282040300c4d21030b0700b00000d600b424040c0145421003980c0d010404002c3d0303154440369000602488040008070004030b0001d035a50641035002e5a0040101086440c0c2640c02810140c1503100301004500040905140c074909111854401d981194205081d550b0384000c0d000355610003440207001c0c01060140801607120881c1043c5010b103c0c0854 = true := by decide +kernel

theorem cover : BRFrame.Cov 238129496 238309352 := by
  have h0 := BRFrame.cov_init 238129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 238129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 238129496 ≤ n) (h2 : n < 238309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
