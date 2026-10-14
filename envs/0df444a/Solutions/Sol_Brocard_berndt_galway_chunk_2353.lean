-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2353
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:27:10.628425+00:00
-- url     : https://prove2.me/submissions/f2f8f6c2-a898-4e05-b387-c3900848fe79

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 423021582 ≤ n < 423201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 423022832 1250 423021582 423021607
    0x10806120709090f050c1f08070e060c010903180317181903030f0f021b1c060e060a1e0203060d02060304111201110d0207050115080a030e09040201080c 67
    0x30750061242c02030900c01d8070b07818100381110404030a0141c038940199140d244452034212140b550007203103101c2681e46108080c0007141e0000000381100c00344003415205904641c0d6020281c4030842c0504c00110f03840c09030b440c1c0200008130341c0a407000149909141880011800300e05400707403030591808036031102e485842c0412076030800548650041c07035001546100081400c0c01c681580e009440303444012440b070390221004220702c0e03581030058010001050300e240f00103803c0c44880300c000304010124201d0024005012100c0101219041e40e9240c01d06501c0009215490740400140400c00c103034400040052542900d6903646054603500000088140c0e488203002c5242a80203010a901c9140c1480c3c6000040120300d1194841c07440c80e40b076100240030500542030700c45100c03071019003032001109203c0003940240070120345554031041c02100081e10307602ca6030014600c81d0005c104036052418040e01002d804c00049008440c41010800942d030005045130304103071940c0300075544802041c81c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 423024082 1250 423022832 423022843
    0x6091c0b010f03050c18060103020a09030803100807050d051f110409022a0c21030304030503010501122702010c06060b0a0f050301030507030f0c090f051503030901080612 75
    0x241142004000898020084100701080c0d07440b413011242a408178000308051501c0f0002c00307460f86a103a00004526500c0303034000e801169140d041c4014000c1d01c0e0307603444c44c442d042140c1101c414580301c030702000444020010300300104420790342d600d41003007140c0710551944240480c00c01071210001c10200700b491650300c84240b0035801110706031215214030400010b58041c20086582215013248030503040607005445030180240c074014409522880305201d255400301c1840c80310f8100000941c01900001e1004501c102d20030b03510565250f04000c00504481005d0103078144141c5002c24000d4030205c204820525002d0b01d250741140c4901c04d2004942c1e14614001c014529400c02e074000581c0354103d0080d29448800791500c044440340b041b400c64150000344005415039010545c10004140c2c104051000603005172001d0094035111010481580d400c003030b001c01801d503183c0800ca220100414200491300d03040700510700d00480100000c0241c00082e160340d210304010315060b9900c0300e04105 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 423025332 1250 423024082 423024139
    0x1e051e07020703021302030f04110d0203060a02040f0b0a050403061109030a0c05040b0f0d060509010209030f0607020705040c080a1a04090503030402040b030102040305070b1c0e060a11090609 84
    0x400501450031280c025110341480c4000c82c01003846071820215249075000b602d00c03401c02c94440740440c2da540d44a02c403403c0011000342d90409003002405015840500c4400d120341150400540d8880c58120400d1000c01c040d404900358070030900015204035800000c5808582c3c000c0404509070750005110096071140403140c07a494032500312940100300d0350035118403c82c0c90444080001c001044203000404400b1490142e101c4030b080c80050001e40650300c596005665000014206061600400c1c6840c41030703403a541243d841903040064180d1b0400c4904094001900c0078000c1401c2c01d40e010300080009820440b5151303c8010340314000c621824005104000100103000344961810019100ea100741c0c0d05a00850410100c241c480c2414021203046070f51150041040318541070103603d41c0d401c0030b20f0082c4904000740030305143d0149400764026414041c00685050b0810455100c00c403601c955901820720300c1070000e09082d6843d001602d040000030f84030040c05580302007000044e03204a91 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 423026582 1250 423025332 423025381
    0x6030b0a05012a02270712020307050a05070501021204050a0b010b09010827070b1b0f0c0d0c030510061e0f060c06091a041401060f060e040212281e05 66
    0x28082c8210742e490b58140c41c002c4006d41c82d494400814280203500340d1200f1591300d8049030040000d040401c0c480c00080042a00034000141400c88901c901c0100075000e0f81c09452580c0003400c0b400a006007d900a8010081344865a00d0f1008050018289210040002404044800006500707003000360510314650041002d849020f0f07240d904014483c0c100950000a0400192005856400004600e1403201c140c40041c00041407000c00c108029128400031615903c0d18800040012400c10800b000e03101c6d06100804c00c10304002111002c40f849140c0100b660b81c490008000d04e440d071003c0c4506442316483c003109921074a0601402402074500000c0c40b01d514079031110003203040100c00d00c0c081c070720030007079540c2c40311940b0202400da90750390203218605402c80794100a114012520404c2e2101c02810144c1045460150b6031020342040304c544286090810026546c0c401c0c1154260349101c81c000c040114450f4080d070134080e215180e000001040d43c0e40c0101c2c0880242001e28140c01d200c59 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 423027832 1250 423026582 423026629
    0x120607091703030402090a050c0403080f031b090f0f041d060718081002090a080a03080406061502031903020910020c040c17060d02130606030b0a05012a02 68
    0x460000c0450899100780c0901c11071020400c102610048200c0b070007035800600346400380c0c881c10520f500400c0041d00f04050803104100020020311090007410140c4c580121031a143d140000d00c916101e8000b1043c4140820b08208038404c9507101d2000a00e0321100b0358040803003007800310100d0014100076800302c5201c1d940c0e6003250b11400d40000c0f2540310702515540e4619200c402c50907104401e03220701404503260819a07100d414400300d03074060425480002c00d800030103581d4000345410b0541141c03058002504071010002480b40d41d006082c0200744505001c3c0c01048440d100a4583c06116106400704041d6100140e20522a8040e031f00141d80c010304070b800801c84802c01030360340c034100781d41d80e0300aa0034039040101090295001108481d1900b0803901107588840401c1038500c45080200e0b444645101d400302c0303194462088401520464034001401e41c000000c015400e200765100d50f0401580345045035620440d80c7c0789214101c41407024000b03c02032403001850100400001410b1100740 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 423029082 1250 423027832 423027841
    0x30807240612020406240c030905130506041d030d1a18070206060102011a0907140301090c09080613021e03010207060b12070302210102090604170f15151206 69
    0x300c62a041e42c1032080340d0400c0856564000003a82d01c00c0d00c0d10000c14505000081d4800380d000b452010704907840ba1605207903007900c1f18000351082d0b078041001c2d00d0a40e0358004000070790030b040c401c901d8114400302c3c0d61034002000e0210955030b446501102406241c645807003000800d81510002242c09000300400a4150310b03140c0c00100c11000c135440d200503c5440041040c07940184620109506d2200c0591181325940080c03024010001e0160020883c50041000c08028000b01641c041c209140c030110700d81c2c1031103800800c550b01030380020301507401c104180442c0f00801103c84424a40c15259990700802411602e226890100341c2d241c2c055000096144c100445507200c020b040d10110741910000301c592100d2030341c1700b090340002500414220050010712400b845240c0742d04c4140d10000d850040000045001500598014425401c2c1c0c8004140c86480902c00c42040f031881d1001041280a4880d003500006000303080180c40c00d513640d4041001d85c4600404085140c1c10f14201d40f01803c2c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 423030332 1250 423029082 423029099
    0x5220303030c08010b03040b040803042301150801020c0303070c050f03070f0311010c080a020d020d140711030f030103020f06220f12030206150a0305060403110c0a0308072406 77
    0x3a16500342c00020390b48400854801c1a0328181c9001f130f900411080c0c8030340c1c1d1390b0352801d4099002409c20340308401441c284401c0d0301e4990308000d103121003100010a5201a401028480b21350750340294419074014018045a018000140c0e64440901c3c0b0b4110150301041c1801c0741482000504408980800103200003401030780700240060522a55030012004c408400503400c0b20080c1242c80002850040414070140540d0041c3c045039846940040c03030010801e425908951050417010203e000f20001c0040158010f00d041d00b09404400c0076601d424600c1158004500c41400024844d80e1100495141e9032602d0007078075541c2802400302103503101c08054074204020701d44039001d51142002c8000c41c200d42c1c140000708580342d258000781941d8072800007140740c1e0720300c1c3d000711a0040017405001006c140200301d0b0501843c040d07180e9a5406404035003071802d01c0c3c031020116004d0000b64804100203907400e0221441d19802c044540c5109840300068910342c0c2a031903900000d18102400420b070400c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 423031582 1250 423030332 423030341
    0x4110712030c020d2d120f061a03040201140304051e1e070602070308091c030512100f0e0714030a020909011a040b0705100f0507110f030301060522030303 68
    0xd095001c885003a4500300d400c8600c0445c60000100d151012072a580b400d49000c125410f01c8821410411030801e1018594001c68902c884060380003a1600720810034102410401c200350440040d03010318519090700040c0001440b82d540100031400080000d05000d414030002e5110202450003205120900f8a81a507400d02d815211000210300700d250f0012000c000389000c105c54140c2c001c3c049561550305e400a113030300041d050607040028901c50043c815402485500041d100307031106a104d144002c00b10a0150001700a815a502081002c0c00a0400d1446410440d1040c24a5155503030b500c10040304c02200c00800498404400b106002451902c0d13000b80c01c0c5044c05441c1d4500903aa502c50101c42003100500500c0d052130704100611044210341c0c0107144903030040003243c0300c065020715020700311002c284000142541d603c05100341c040c0c1c0700324010200c4e034103070340100030305100850920348a00c010302c140402d00c8800149000482d16904402200340784078801c40001a035a410040d001c0c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 423032832 1250 423031582 423031601
    0xe030d0f021005040b06010e01020a02060c01090b01080c090c0705031603080a20090114040803070b04060606020c1e0a080a120806030d0e040c030908030406060812180411071203 78
    0x40c016030140d410002c4075481043e22840d000750300080aa101c1000540b116000c5905403411801a0459400540c80d42001070480c500310400000b805d40751414060b06820060700300c010150041c0b9011000b03070340c89070b81154000d0070180b00b6595500712454543c0c9940b20300544a858000c0222241007810b030810ba600c0e11035031075000180b0807288006810301e10004c41c1050101d038403206000c6104694483c40420b10040c4d01c1c3d00440749400d484011142c0345400c4082c04884070684842080100b09080c066000103007800d000078a5840e4441c000502000716160800040c19100d2181c0180c0b0f41d101c00c1041c00402d40d0304240d442d43c2c01c40c3d05007544000c003002e42e000b011803021000303d1441d080000380f10700c21f140c05540749800104400d0401c4090850b00001c48105901c90742c030300f40416424801503000d5442030b000004c10344e01d004145802e041054840700c2c030312002030111792a500c1800c1404102c1c4441210000360601c84243e0724445402201009800c00540220b0248a6505076101d603520 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 423034082 1250 423032832 423032837
    0x7330e01021b0102060408070614010e04051b030c0f1311090415030206030c18040e150901020f070b09030c0102070f1b301b1e0f0e04030e030d0f 64
    0x2d1074800001c1400000409071040c0140d0006001030003285081c80908201c41c410030b00442e190141414040110f442030300680d4002c5050014441004420484201c0e423030091680007410030007242c0040c2c0c40e030401e180028000d9420644454a0fa80ca228941120102000d01000818461004082141c000112190285240c0455203400d248220207110449034000c184915590f50701941e403000b41c00240c2107000048902d503184c4d00e95900c0e80150000320030003030b008104e840d00c055548801200c014000071320700d0f481004016404c00e01c203000c80306135039000b5403400c10546440300381d01d1840c8582800000c1552000ca0482d08001d1024a0315150a008100156280c2c8100040c00c05e03e00b00f900c01e004080301c4043c585001e152002055060b40d14001132180b40386000c40d2100c520320b0480d05080d030040c0c01c0300b100c02d0040d02e0461400f0f202e2102d00142c4c3e080007030f003045828201c03c10b00e0f00030101000b102400081c2094420a018224588045c0c00d40d1113400024101802e00c4130a610300001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 423035332 1250 423034082 423034093
    0x20f0123060a0509010b07082506050f15060f040305010609021903051e0603010b0a0e01090612050d080919080301062007061d041505090c07030207330e0102 69
    0x191030b01104082c160f0310010803d0025034602500c0b556154020340c012281c0c800107000d1204c441d12180440000ca142800e0460f0441880745442801c03200e0081010703403101400c01c01c0c80021340032401901100c071800e0300c1443c5d85520418403da0759000c2c5030b000802941c00d2150114000680c0d40103040d01d50850144041818202001a801d440c4d046540d000d005c1105410000303141858104103800c20301c0070300000740202050011403210390030b1350882c4042e006007000412a4490398401d00005180c0d079507099035111500da42e0251102c61856580d001c222190002c0340c40304005101c00e10101c4031224035800250660310701010b2541007442804049058900b00b84101441c1e000c50b110702c0380f10807000d001081d04080d030503250070100002d403410040c02e85010303d507607455910811407144058581403d515150008000a42d000107220010100040c0003030000a5000104401620b1102d5018000e00f0851048141c07031003010b0032a142c1104411966001d141d403c01002c01c1d1440081c4c0c00d031103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 423036582 1250 423035332 423035341
    0x612021210090c0c121b060207051e012007030912050a1203020f070611190305010302041a01050a0503090a02040c0305040c051504061d03030415020c19060f020f0123 73
    0x700c49040200303001e01070105c07110302c0e020928800c0000d151100300c4001034001700419622240200e0704100c004881c0d41c0d019000c1400301e501e000f0060b561400c0340c5402405060010810080d280c13a9005c40c2c1390201e200071807440c08044c002d410030b5001e010b041c03030b11348442d207600d00301299030351b0801c502a100020302c150f0b00d030712140c0300e4000c035030101c00141e1000e03240201554800c0d004180c41124080c000d5804d00485242c6502129403001c15000b680e00499107504500400c001ca071080500da00c00043d80d0f104540441e40c101e820345d4150b240d681003054681d81c1d10410b42c0e04042006100035030040c58a0310701c02d14180c142d408140100c1c010402602c10700c0e102d200340027060034061400920309006020800c1000d10800044c40030071800080c10442c10b004030b0100745141c1164220303501031101c074400b01198550400400c1e058000c12564810642c2c24801c1d00030003020603004040c100030082110902c028020851143d2240c8800020000700400c0000c44500308030303000d02011030903850400b14 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 423037832 1250 423036582 423036587
    0x12110409230a020a0518030f0106090b12060105010e1002010b030304090207030215040809060f0403061109120a020f09041415070e030a02090a230a050105040c020609070612021210090c 81
    0x8801070a41364440340e00d418516801040d90500c150302c0e6a80c1449140301442030707010b0a004040c001c0142d1807011914404400c200103c4224500b82e4400030f51140d0b00421183c3e82c4083c20200501c1d050785e004601200c007680480c00b41440c4083c841d01444005030011704040343d82d0041a080380240c1c265115140c4d0401516500281914003800d501800d000700012407510a005124021907028141d15050380ca6031240d00341c9072070803510380481c4408501d80f000e0341003960019512010a40180c88001820743c001100031031500c0c0a1070003114060300160401850700305c08060301c00b1501c22210885400b80c06005510011a08400060403c001d40d0441e406c0015610540707940c001d0902c03c40e55101000007008180200da46052190440240c1500b403000c642650300600c544075000c1159814038007808152100001c0b2642198450010070040102c041034402c240c0302e0798070300b008010f0340410458000e4002c4074865a80c00c81780c80240440c241f04246910100d88039203500344402008000c06 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 423039082 1250 423037832 423037837
    0x12090606010207030210020102130b120903040e0109020306040f021309060b04060203030a0c09050a03030f0215040f0321021b1c09061803060608062512110409230a02 73
    0x50300d000da400104180010b20b454a40b4840d04410381c400181002541400800c50400d154000390000d540018400034541400c44480e0b070000b00c8074001c51030946082c1c10340c00c038000d0502c0f4000d60780f0350110102d40c2c55903494105003191889482e066460300c0386c0b000e0a1540e881036205458550785040c030f00140001d01d00095404842c5503801079815952420418400b401c0c044074403d080214611010460755110029880510300940c0c42c40e84080058801901e494003c1c828107080608001c200000510340300486111107505143c41c000314581180f03050710b01c0c8440700d2007914150000c60030407000e80b440302d4840321213520007040310148000402090313480c07401840c110700081e030045000c1c051540940b03005140181030007803e41e01c55559458400480d45560040c90303254001c8014001c803a0050081c1a10309104187c0d050b186807400c070805000500c4461201c003d4031b803641c00c9144000e02142c10f89004080701c1c2c409004151800c4400002d00819403158103906009001050054105100303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 423040332 1250 423039082 423039091
    0x40501080f0309060d090803090a1208040c060e0112290607050601030b04080c0102130e181902040b030307050109140f0a030509120d0f030605040515061c02030c120906 74
    0x2d5494411160244032141d440203031400801505c94030000f0016200340021485400540b001c0c1104034220b24100268180d50034048041003841c4051001240340f66820900b100d540b401d08403070075521318005807030341507186240d41c540b80d15103903240030550407049480309244010145c020311540c1c031a003082181c0c042c80c9006802944604018800500f040c44119009401029140c4c1031030b0036041e40307900366403006088003400381c040e5008002c61444c0c0000d054010321200e03440b2000d0750a55007c55500c20413099551800d0140050908c2552510780c05821107400207019260b40382d0407402c01a01908182c3e200721403e959021003108610404100403107e808018060241d1421a40f0212404d4004a180c83e920035411107048080c0340342000340c2d03c100c88454a448115585840000c0c00b1503140390310003030269040008014803a40c50082c0603440e04c0c011078056072501c034840380d0806202103501840c140688000144041010100c0151500c00d1200c07041001503075034402e0058690f00e0594 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 423041582 1250 423040332 423040363
    0x30e0f01140304140f0a0804260604110a1a0415050424030e030711090c04080c061303050d030b190e0708070201020910050909160503070e0a0308070b0604050108 71
    0x101280010380410026110280c4d6442200c50011082c01110300f09443c40c40110340c06c800014041144907a522059040c0e5200c81818000c0a0340c1e02242c1c644a4000030030040c103103440d031982600566102c0c80140301a005030060300704880f12101400720140d001d80070392844030700800415205070b4820811502503440c12071a020000340c50b201d40b44006011100800c06058035800c1c403c2280c02d041011b40012030044580c0d440e07004c581c500340180d0080140060098142c10441484504000180b210440109a03182035642c0004179002c105c10141d90401070990082031038a000e06c55041d0090f00e2180d10032071703540341c0654003105035903003001043c42529000316500c07001625140c09480c4565208c0c0a40c0005440e001c0c51000248003410020340c043c0c04100042003410382c0d41480c1c0740c407540c40148100303080700040c41800098003a00006080d00204480c4d120000c445440d02e80e240001164080e03d125107400756458071030b42c181c2c801c031034480c0035030316100000070340c00c400044118104981c007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 423042832 1250 423041582 423041587
    0x9030f03110904050a020703030e0c1c0812040c080105010b130b0901120608010e1015030b0403050705060f06040c0806061c09150903080114010503070f110a030e0f0114 74
    0x24006401410203110348580036202480003142e151110300a10b40710f070584010060740c403026841d020307013207c0c9114041c40450344810901e030500d03141c00305400021001303002005c0ca40d082624101e0020300c503d206c05000f242d0308100317020800266581c00401d0710101c800034081e503038840171007400758003e81d0305280c03500c00000c40802444c0d0751800186812841858407060700305a0080c1035064405c01e40c0904010ba64802444007080800c0c0080600d66041580a100c03001c140340124100322070a00000d030000582e10041400c040c0203200303c2d10707030316489016a001c52078401c1a006403001c0456205000381d0900c884c0402d01c1c0c6c0710f110010301c161402864140ae0030850300704001e03e1104d640d40000d403561340310040c01c045107011094003e00002c0380800b1804800a04c0c0090030310b401030f4469403001240e00c03541080f9a03044000d03030ba4082400d1500702000213505804581d164075801845e4001d01601c0324002c140f583c40284000b10b48010755161190003000707801151039040980c200000c94109 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 423044082 1250 423042832 423042857
    0xb01150f05030c07050109150b010801030804030303180501051e06192c040501020405010e060309060a0522030c02010816020a060b01260406200d0b010201060b070c080f010903 77
    0x16001454020701400141810004c0701e03590282110380d20881601d000c1d044280440045500d40281140c080081c81c03d079129514556868a10740a0380c0401028592618140b00401011005004905030040000d020a04042c44081c1d805030740307000c12410641d16400040c0c2c20b4140000c0181000044090340511907140c004994004802d10b00c00a283d01a80282301c1011a00350000300c0c0500d0280c030006903640d00e003000240c000040580801d014400520400a0605000c941a5031100060602103503950b540140c009030110580c0c03014840c2c18800341d03481305065000240a500e54400c2c1c0301d90700e4a4803020b072884517030306002011000590000c0302000c001798180d0044580c1c480181411183c106074050011030204021035040c501103540d100304010f010603400795050b050441000035100c0325035552890403912505080240d116180c00c2c0700c1140303910035402180102110040c07162145800d00c0c115844e500a48a1951300f40b00d80c2c00600c40e000c1061040c4071000d0f6040e164400d1454a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 423045332 1250 423044082 423044087
    0x120e030604020f06370306030c03150f050a0b100e0d0822080d020106140604140f03030408030901031a01020303040b0712090c181109060c07120f0b01150f 68
    0x8500f01c2c00f0703410500c18414007110240d032040111056108460455800204064800d41241d109616000301401c1c94420008110b0b140c0d40102540d411119403d4410345001c41e0002600c404c0c8644c0d40d10324549420481c2c0c0302116484040780086c11144560342150380702085070b030308500c0d180c0310390300c0380c43e0000b50000209017070b000b0030b90029401c4030240c0c0da40320505241840c5080f42d00c04401900020341810300f90341c5c20700c507c5015000685402c03005148042c0850000d0046004090240c0002c40d42c8444036501c0c0320ba82c800d032240c0142241e0341c858903100c0c4240c07031360001c4100a010a0800341e208503007413031445100c000807074123a004500b56641c41d00c034090380f00d00180c241801e124100e02504042080c1d4003c0300d82c0240150b880f440f40c0d624107910700c4129005070b56035248031031901c042c95010a000b102201c000d00801c4514a4841e00d008400600303001342503004100d20160003d12600b0031820403407020307465014810381d018903a070f24000e410300c0d2074844884d00c0010b0b00c600a0a0940f90 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 423046582 1250 423045332 423045349
    0x60a030605130e37033b010c020303120903090f0d050c1c0c0b03010303450b0412170708091912050f1902010e040f110d09120e03060402 60
    0x10743c0011594004d002c110f01d80b0410107440c1d030309800003007142c00100c071401c8482560840395400c4805890310541d0600ea0822030142201c40c460400c181a11318405540c0c040041d1203e444d43e40c0440c8050f4140000c5040d07907680f0043c0c1c068064030000340f00e85400c0c6801058500101d40100c050040102e400081009500d80b10b1420a44661558840004600682c107080007400c0d00c40384c4a60f5950460034060300500099601d092000083c40d04c0000c0012501c06901c05076942c01e101000c0890240d1602698103001c1d006002c484101080000e2042c0f2501259401d0038040c0c1c4179585140302032071000340c09124485000e8000d81c4100308c03409507801c0c001c055482070f00f4407440444020b621140c90f01001800c0c40c40c203480c56400388a023400004001c0c0880c0d4494850004445910702042d40060301407081814450310543c3d4440c4640c80d501c4403600901910b0740014401d17552414500e0811000b400700502c15200e1f02202202001000e0203000303404401c44d0028020304541c0d440742e003006580b6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 423047832 1250 423046582 423046633
    0x504150507080703020303040501110a021e030c01020d06030c05010503070818071706100509100306091a1303080601020105041e06110f04060806030d080414010b060a030605130e 78
    0x10004111030408a002e420240044522035800b035643d03414113081c46800e54940508c40700c00d2403810010300540c61340000b0340d4880301020350a04200702d0400c4101d9402c500a203510b04166500011301ca6005900303650140d01600c0c8a0f41d154113406407614011610790000300c0da00741c0411000e0022440010003000382d81c00b03440003241101c0e581616120141111802c82c0c803105c04541c8240e0500031224620064540503100a580c4144c0c01d28100c00410101c0c3d00a00c00584216074483c000710902422880115400c4031a801c041c1c03035810415010b14400e40c5100c0150b002a146401140340b0758410f0080c9801907410600c0d00800788407481c0c0075a60004841c0d400c48140366100007008210507628040d01580410700c274a180c0b260314141c03002d03040600042c0b2482c071941204401448080d040030b030154109800900d21a9070010189106004080b1800c0b11035201c000404e0707000807207a0681101c0d050320070a6a110480740080344840055403494544039100d030b04140d4039072014404d0011044202d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 423049082 1250 423047832 423047837
    0x32003042f0d060f0506030a120f0203040e09030702032418010e0601090e15090d0e03070f090609110c070b0a14030c0c0c031902220212091903050415 66
    0x101000c580000d0100304044802c0700c0c0c83e0307102d600302400503126200c1d07160b1202041c0c0c0a41080000d03aaa0160009a41c0d40d40d00c080c4148403840c400454420007e403406480b04100c200f1032400e0101c0d00640c1d94000c500c0c00c0344a481080305180482c2417010038100344a000b40b6031034130a9241d01f401c4000076075000c0d800c440999640c44e5200c00d007030f800f08410b50007015104000100ea040d4944d031141000d42800f803131900c007075000041c00082c0f100007035a00fa0a104514240d0300c80d010480011f414800164048882c80c03c0c2c0c0f90010440b80001c0d44024101e0f0480c15041041c0b0304200821003042c0141c2035072840c035800400c03040201c00358020040500448070b140c55107081c2000c402c8844181c005550300103d0400c00b02c1d009074059410000e24141660450041070609548900e070114010722110090040080c0d40220071582c03802030540a0303009502000395260526400a500b44100480d000c000a100700840c43c040f070800e00100740201c0341c2607a01c241c41c0500f403000c028445180a9004000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 423050332 1250 423049082 423049163
    0x7080a110111150105030f0f0c06070602070c1d0f01030f02010807020705120114151e01021c0c0308011a0a03020f070507032006250f060c03200304 65
    0x240041c40641c00c80351103d508510154101800d1603d4003028440380700b000d0384072141e010107002c1d0004003410200c83c2141c045564691616044019014041e0010403c600080c1c0104191040360303072450110130b625070510610796660110b00041c00080c800508642d403c041c420026502c035001d80c1d80c1c40740b0140101e407803150780d52011854141c10072600312030595681860a0341c1c04040e506e0720342c108826440000014207202c000a64a0380c03a10a520140794010740700482c182d0080c800d130f0804180384481401080240b95014001c11141c040480009583c4030001c40c89460300103015480498004201d8100324909070254002c3d40024480d8034040014090b413000240100700e0f04001e1486070107040401c0780c090344040c4442900c500d409110305810b0080001d481101120107103c0c0c90441c014400030441c43c1000c0341049090b046c00351001d82402c10f4190400d4154016100c1400c0c02c510b850b84840d40c00c1400c030341d680001e5500508494205034a86402101c0c900b61074400402a0441007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 423051582 1250 423050332 423050357
    0x9011401200706020708120a110a05031206030c0409030f0f03142502060103080d1e140709060201021201090b0310140a0e0307022409030f0312060307080a1101 70
    0x70500040403034030300e4103074080704050007541d9040c00f51070010081503000b00b0708a20b11718110700090240613000e130304005448022850059040020407615904841074954030200540e201408510032a03400c1c5c060702c51403100000c1c03410b081c490007a015030140d503544041d100030f610445481c1c1480c1c150004040d2500703d802c019000c0208811f028080c01003100c070001b42482141905110200c400c07a040d504004e004001052104c2d080715000700036000c00040d120581008960350901090410080b079250a141000282185000c64091314080d142c1040745503540400700d0a034800d46a6116034600684010007030243c041d044240151350040640b0350a100207402c1c01c00f01c0c6c8503142503150b04003462003445442c400341c0c891f20b00401c038080041c600d0190642c010440c41d044181081c0380c94004004c584928102c64429034946190090039103401c10318001c0e00959a0b0000c0007010783c21041280850582d181c0001c04008440d0041e01030004901d6548661840c104000001c0d4103000c100360301c05 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 423052832 1250 423051582 423051617
    0x6081305071409061c03080c0f0a0306080f1b04050601020a0f050307020a120b16031112060a09051303030b180906090d0503071428020307030e06040509011401 70
    0x4002030100e074041524150750348010408510b0021301424003600110000d2160b18800100c2c00100f55054280211107403180c100544492140030904400c021021070f80905407a8141c1000c01120742071421200a444003920054444010340310000241401303003010391503400c041d00a1540400140180d60000700d00380c580141798407028004441907000040d0303113821894030040c10406040c00145070f50703038842995200340e02940047c09402d2107005650f9203c00c09403003a009021103015698001d9100d50b04980c14032450902520310510641c00100c000c128602640300325407040c00c1c500c0e888ca40f08201c1e510140c00a241405603160020a01a0840380310b4800c4c054640c01040008018811481c0c650a09810320700c01c01d06c080100a010400d201105601c404840340c2d0402d1452000c2d641d038410218007080e01c000304c045075020354141085102c7c0303036000300c050b100b80740c06070329011a800d003c08c00b0480a44114014190310501c01030052084060f0b5000070f203140501814448000428900c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 423054082 1250 423052832 423052843
    0x80c0601031b0603020f0d0506030109080d0903020606040e0319180320101e0909050a0b030d0906020703031b021306090e01061412100e0304051f02060106081305 71
    0x2524030301141e504003102c07494601201c8009100518045080500e40044884e2030300c505034804c420b05403240c0100d086598290300000759503602045075a6a0544405244c0262891890039000b5001d041c0000b001307030409010b180080d5030795602030741c50001803c6030f0480c0c40070031a4500080162003c52081140070341c207280c0c0301030343c01080c29001d05a5000303045080c42413404001c0340034290019060700403c2e0080c100103540c1091103100d6140d40c0b44090200d88104560348a614240d041c0740034030115081d16131118035440d009070140d441e0540d40820540340505103100d88001a0302801c820008603104815000030101019403540b52110f041e000a03072525215a0085043c0366a61000c004c042c45034403504840c0e5560a00a00185181024035100e5500c0300c00030b00c3c040c104040c01c0110304641807001403034001c82c103a42040744010040310743d95a07810a008041c050b0a140c1008203080054141102000201c0d41c01480b90742e080c840c1c1101d01c2e44010709040740190000b412140001e605210 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 423055332 1250 423054082 423054089
    0x506190825090533011d15031504061d0109020a090302190503012706020c0a1a0717043302040b030a0b0405060a0314070509040308100b0f090409080c0601 68
    0x181e0907192903503892400e1440002c150000c40c0003030b10070b805502660012042096a440003024044d1b02803414046840d030200a034003c8510400003040000110b070b0a550203517549401d540401c00252104501101941d8100201014080c8400100103c5016400611400c1c40c540b41c40b03143e140c0c0d254080b0368440c070309106c041c0c1c49a07003c1c001405076040074401c0901e00012107940c400c4000f030442e40110b4403880040054261900020708200c500e40821204050503030154180b0410901c900d20040002c03415154040050f121011041c48000000d01d424011030304842c090401150311007000c4403000c00b40c0e00c8007004000c6450101e030b8400c52072010b0700c010084c40403840d9403032034441408012901040d0a952140303103010f042c482d407a2500c0760484207599220007000050b5081c941c8045c03410060b42d20641e4408a41d00c00c210030981d00186c0540680c04400100088507202c00c2c0c105000d000e09900900c04101c18400b01d130840c607040d0014484140034100d40f901e4000d41d4002103003001026007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 423056582 1250 423055332 423055351
    0x908150402180a0b120f060703111b0703020a030b0403030509060412180302060309010605030705040207030f050d060801020a0f0206070e032808040b040f0b0c030301090209060d050a05061908250905 87
    0x6c1c11105d07104000c0c07042c194040350302d250070080c030555403249006034040e643c20000c2d5400c044000303850300f081c00c00424000d1500189040e6140e40c1d40d141c091060341044400710006802d00c0302192140a00003841030160341d101c40314005416848204461000300307074081e03c1181c0084c4000001584540780114000c00050001040c114188000c0c9440c10610342d124601640c070400a00d404039034092204400000701e460550f81d540e06003e480740140c0b20310f42000d440c039480002c08082281e0030203000e06120201d502503520350346e03c1000503211004407403120b0b0b0709034001d84030301c4011007040d1080030107003141c544255443e00815101d44102e5000354022703100340c90002809010040f0203400c0717100100100c00300a842e00500310211501d074041880303100b0754140c0101720700300700390f40d1241138035032840020a04100500e000115100a00006e491023805015000b0901c5070040060724840d042e075645800810201904114a03541e0034144140300c60320003802070001c1001c0c85e250140314010208031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 423057832 1250 423056582 423056593
    0x40506010603060501051e280e0406090b1e030109050313030240020c010203071701080118020d0203010b030a0c03030f110d0c05010216030908150402180a0b12 70
    0x700c000d4200d400036040b0506005003030181000c0c0f50036400c1c814210784400381000e503c40340083d04c140001c881e0300070300030f254034100382005601e50f9010150800548040b034050044d16503e10903402200c400680803030700501582c05003003450305d20b08002c00b0b00ca030024000090b42100c0b5111582590000080c246040d0400070042080d8075100d00c1c551030180d00705041b152400740902c4250301810503843c488100d080c03091500f0a072000b81c1d60540d0354842c0c1d8040259a01d03d41400b00170441103c00306856130101401002050310b103014440c0700d9896250b0804403010380c90716000c001100396411001c076031540d20f880d0070100c107480c140400c40d0024070a134000b0700cc0906519010f481c81d42502c031094108400140604000c0d08002031301604c0c080942496201d19a903420a01c0c068413038114802e2031120204208020550f10440740000c90f04202d041d14807100d050307090390800b04401d0320080d40c4100c9070300c018420070303188104c500d8000c0a811400200307080d40d600482c40c40d1000e00d005644d10b8001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 423059082 1250 423057832 423057839
    0x4120503030610080609180c1201140a0b01020a0204050402060408071215150b0c070905090304080708030c0c0613050306010b07020112050609070c060605151c060f03020904030c0b04050601 83
    0x82c0c02ca4143d5071010303080c10007840c42d0103004500c00040082034020f000300ca506081c4001030b42400360301030540006d00511801c3c41000100740c0640118070010000021110000721a405244103000100340c05031701809c580d5050380c08200280030041c000740da1100380ac00c0300064650042200300f009107881d1003140c5840d01c0500741001c10720b80c20000842954140502400040c9401a6240540d006c03509940c1c6ca40ca9070003042d918111460304001c5c50f0b60300d810305100040d83c001014000302c900780c00840d00310644034404151a4050f26605204640c030102d2034010510b0500050806241000307c807144c0291340e40f0010346050003e0703002c0706105100242120a5581c0440c06909201460505024a051200c080740042c07100400c503804101401e414107003041880d822050080c46d0003414040640c51281c400c440d47c0d840980098200203032103a60700703815800c0b405003000320350084294250880c60745d000e100301400010030031403c1044c0030910000040302c060740c540c001d5001d2030050035039605 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 423060332 1250 423059082 423059089
    0xc03120c010f020c0d140f091302090a060e0307060c050304092d27020307172b0305100b07170d0c03050426071e0b0408031902070302030a080606041205030306 70
    0x5020380c6e50300c11040c00c000c03100c1c0c000103801c225003016006946581107032640360580c1c13009000320f00341e150b440802c800d00007440540c400c600301d010a80440c02d03640c0709581c4d50020b58540c010840010090303002400b08111031003142c0e110300204100740c4401240009066100c85880703000d8000720310303525034074100710328400c201100c0105000c5031802c0726048150140c0000360364102e980b10764202c190308110ba22030120320620460480b980280242489502110a1001c082580090a00c0000d280000080040e42000b10f64011104040d95240c40c1548549851902e81000350000c03031003040c00c0260340e449019504c2032102c44c00c80d41e0390009440c03c3c00d01d8080b00c020320312260030500c41800c1c000c4410201d0801c080b0b03900260301403034060030020002c400c82180e40041d07001030b154500c0682004140801940203601c580048042548003120850080049010319130b00540180d01c05d011034460b00b03015544403074004c18020031050400755503000c02d16403005410130495041e000881401864207 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 423061582 1250 423060332 423060347
    0x3070e010507030806130e010f0605031204152616021005071b050f19061b08010e09010b0901090606030e1b09040305040911040e090c03120c010f020c0d 67
    0x4024640350340b82c4116602c00400e2000d02a141d1803003410781c4840c0c40740c10b504540c0701350300c1516a40000d0000c107490180a200402143c42018001d0154801505240400f00b0494080d41c3c5445070a00c0e20390880f2408403485a0f41400c425010941000f0900c107829048a58501c07814010201c6030920011143c02800e02403800e510741100343c05c000c00e10241c01c0e0041004a1058208c00d6020003081e0fa0b4104503251038a00d00e80540240942402ca60b402584000c0000050703001c1c00040c0050034528170a010780c052988905000518a14014001d42091805e0660840607240002c60b96010450000303a802c402031f81310b8040316030784890401c1401e8140c001c101d60741c0158005414000d107512080e240c1d5042e002c00061003280036600040c20140104196405171485000c200b0103042c00000d40e07212a84140910001c030f184681c000784e0018400200d6000c6010f010300504414042c0c06207021244c1c102c5800b0907010354803000d081c410f42724507101400521125200800010f454210301510391f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 423062832 1250 423061582 423061607
    0x7030c15110606010c0c120c17070501020703030c02030a0605010b0307030e0619090c08060109060311030f0d0302030a0902090f101211060708090429040b0f0411071401020307 77
    0x50568000d0004001081c0b256015400b0700b40018000303010724003015078008a0304074404c020b40c250310450074001181140c60648049402c0c1114007540703207002940d40d1038280300b01801640140e6003030001078803503a40039072110301c060200c0d811650304e580c645044d9082600301003034104010040002d0b082c0d0500032017132003401181c060b20705800c040361000c042c025280300b519903d80c0c0760b0b00110704020303100800c540200210381c259182035071260015006420f00b4030080d9041c0580090720000b03494081100090a051340008064030b035403107501503001c3e4200801071409290389200f904056260400c52921170300740c0c030107008824501847c060500002035040900317104d446241030000151100024070103141e0403100f8544500307191805509900c1040c161580113424860718081c1c0f0320f0900740464504084102d101e4043c0e10210a1008541031305612540c0a080d01070f810444d400c080d0b00802c000c00000704141c2c80c00c86140c580c030401042584004505e60740c000100f00382ca550083d0a010310 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 423064082 1250 423062832 423062837
    0xd0e01180611091f17010e07030b060405060d050c190809011b021009080405040f0e0c09130204050405070308070302061623030702100e030405360403050c07030c15 72
    0x1080041e0001c07481c6a64510f1030000e03c4200d00b604228160b000e002d8082d169514241890155030b107c0300502c029110555060020a0a18400c149945000c005039400c0d120050402401d00c011440c0f4040034000c054a51030100318104a079a01e190032003030094104490b40e4550340703c6410b0660800c3d0840d00000030b501e60703e185985102d46450380c0440c3c0360102c2c0704ca64001041e41415070500d07034002d1003143c1c0f1695029141c050071207a446101e401c8208410300410940b02886800b205100028008444d00728206071b14401d048010b01d070507440160002d00502c210750980d9142e541d180b4443c0c1c030060080e0301581c08441000742d6048001000c144903003683c50020010041c0340c80c0010340c05814440002002404000103442610800069a060703070b5030a024070920000500e17181c0c036544140038880c00303050000d00d01d000c0c040c81e101d03d14080703d0300c0b4506404103031560040c000007400701502c00c4080200402a807409840b08100c4013019601a9503046015031800201d64040c1c2d00c501901400d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 423065332 1250 423064082 423064087
    0x1709010605090a151a12180f0d02100c030e0d030603170702030c0409060b0a06050a1d18130b0a0c030b0103050910180c0e1005030319050d0e01180611 66
    0x1011201041e040c0403034061542040303c5c1c0c00080714820050007000017084030f1010f58030400c01c11401c8244070400a00101c0c09480110b2146201070f5120108902d803a00944e00140c0c0007908003115900c04100c001c2d513841d0000310100700d10360b21420301118281801c0000e45900382403051180032009580c87c40c4110302080d1601c3e20715804240c98403c04142e241c80f8550383d40d84202403148607046138480450080048028a81300c103005000e640080b04c1030170006082c0318000101e0000358960205009000b8041401403c904662100ca02001000101d40d68882c03065080044d0300060200c2c00b80300c06160120308008440002801c5600e0341c1d442d04d0400d8141424420b56a0002c1010684549400008030b5000707100d911000c0d0344c4c4018100140303a014080310008103160410030560042c00d0003144002a135588008040d0b613070250a01880c180040303030f0514580b107400344008005a0041d00c0c80880d8940b19100c40b80d084070b842c4045124100300500d80c16007044546d1040e05000c2705414032103070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 423066582 1250 423065332 423065351
    0x1020f06040b040f0f020418050105010f0f030212010b030d120507051630051e1e1602130e01200f22080a0c06090b030703020304031709010605090a 65
    0x11a880c0500f000d0003070088100308005102030140011001034007e04103000c920824201e46c14000c144903829036865180800209001c105c0342c2ca80000c861004800c0107202e41140c0070065150140d000d070070001d43d41c98083e09542d403018050001c0f04900d680702c00d00300041c1b4000440c250382d0000c040c281009420446a04482580c820711001d84c3c0c1c01c00080b91415900010502c1020f114059500041d085c02601c80100d44e400f00040803001510404002e00000103038480d5214003c990291aa044100204541007840300c1d010b00296102c036a03440815080d80e4022881c0c84120840c08500c103a00e071100186000c03400d0044044c0180007180c010003429076060392a4841c0030303405540000310b100058250742e40080240c0180c0d060441d08407003c00d1940e45040c00d580b15100c40044982070500f0a0004400d4001c80300741c41118030712200549550f58425045000b980000e01c202c09000141c101058002000642d96102e14945000011858180720401c040d081e4010b203004641800c0c200e4a1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 423067832 1250 423066582 423066593
    0x61b02160f0306090201030b04050a0204080f2103070c021309112d150c0102030118020f09040c110a05030301140411070f17070308060103050a0b030a1103010f02120601020f0604 78
    0xd4210b03500048001003640ca1440102c0242201c1c42e446a4080e04281c14403204900713030b82c02081160000c204036006075142841e0701c0d8441e022000c0001001002c0c00500010010f000d0080d64444003501c3c1c4103505d14801c0d4005080c45840302c8407410255602e00d40308007044040803501d01794040840e40c0ca00c0d11035050801590794000210120709140a02d000400c140e12208800c01c2850f030b13500c55403606c0300100900035000b5002440f4440c1e0081c1400c00d1981440140c0c403c4610414203c05007500c0c001100741408080c1c0880218007040161b0a281c41c001e0f060144070405001d03100341c0265030380b94501690705c0502c0a0180c0b02c03e01c206c0c07400c00c1d0003009072110710071035059941c000d807000c56200ca00e0416000301c1140e080130380401030001802000301503001d121030340b007100b00b40c81c1000180c4409014000b2034022011080d01a4003801c07240e4041803155900070f020070342c01000403031260010158601a0703040010800c10402281051045560b0180040d0243d04110b100034881741c909a02c84 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 423069082 1250 423067832 423067859
    0x50f0c070b0a0912210e03060a0906050105221805030a0f020c01021f1a0303120403080117150903090d3f050903070302060333060706050a0207061b0216 67
    0x5540922417840c2c046501809003d500c03501c88001002d80d0480d04e4051030210240071035410468155281100100d4103180260901040700840050044100021a100b00c014141610741410344080d0700c3c0840700081080009084442403580c0b0051a03205100004c0d1900c1803100a01d8155081450208a40013020700800b4440d11503030700110341400110031142040300b00721590f94140c0400105107000c0c0f044422000d0050348603944000c0c40e0ba80e034500c166075920036140380d070300150000c1801e0041d80f103e02080d580c020301e594068a02e00018440001c04c40c1280c80c40031600011651007910b4240c105208105c0c9035482401c101c8110343c91152080840c0d0720f00c1c0311200c14003201061020051301c5c00c0218502441c3d0240c409030340c034140340614440e01e01100100d00454078500c0c03841c81e198101c031903585000c0a0058507071807c094055130744d9005404010f10402c440c50b800d00049000c10b2841c05154403410240314401044800c5c0c5000904014a000001d41c0700ca5100030300700042c00c5503001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 423070332 1250 423069082 423069113
    0x1e2901081911041409060103050d031b030c2024060901150c060204030803090105090705150711091305060901050708060d03050712050306010e04050105090106050f0c070b0a0912 78
    0x741c58020b08010010f00104404003054003890100c100b008215940050546c2c16240109d003110140d1070203000480c10740c1e0b40c803c804084110f407240070307403a4140a504071000c0c90520703082c000703a000141d05401400c0403070640320949aa0045040c0484015110003805408403155030403410f42c5441804503500131010f2148540341500500d20701441b91040c0c007056000707a4049420355a85550b810a0f1690350019100f5001c25482c04010412140b0002160f10403950098445410801c9000c81c0780401d800408041c0c8200682d0300349200c0030b998601405e81b02e50480300009030103807040d040940c60420010100985170780741006001c0f6081c0c04c400010352220b0100d0b080000000245011a00d03400707940d81c000d151071001c0e190007041a070020041c620510302a642e074094240003600300001d4410a120b240c4d0003c80450040c450a0b104000900e142c41d0044401c5280c040040040c52800040d50f005641c1c821000c81d420301c240d5802010f140081080d520b900110214640301c01c602d180c4d8401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 423071582 1250 423070332 423070343
    0x230306060403080c07030b0f0103060c0e0a0e150316030302010b010801031e08301018020706020c2a09040308160207081905010e010c09031e29010819 66
    0x90f21381c01102c017002510080c550090f210b12039801c21042904500d0f6082c00100e40c1d039410000c010f0307041440384a900d03072100c800030000c0440c0c41c0342920000300004040e210b060840c1c1101c0240041f0780341000151310800626248141d21461803c0003070071150149145c40c100304143e4010070125001d503e076031018000800030b15001590500d0150034900c50b504102400c950f42c0c04103400f135018001c0c0d80121881541d00c041c0d26540d1100d001002406950207000d210722071404941101005076070280c41903d02ca0400141703000e92000002d49480b8510310083c0301d420640c0c2023035801c0c40351104e08001d02103040d142489a4103041da40908503c3c4000c0c003600031b482072081c1f010304441c403c2007040001e001c01d409503101c00d0100140154517100400098900d0f60030316001140c071301414450b40800c10034982d21806554219520716503451704c0340d1891402104c2c030441410208144006c00d0321030748100c5007100903602c1d40714244520b200303050b40700c6032144d00050b441424005865911030311203503006 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 423072832 1250 423071582 423071587
    0xb06070b041406100b0d022a06010803211f0b0a180e0403030b04090b0903120c0a080f07050c06070302041401020601030512160f290c040314150723030606040308 71
    0x550fa80008e01038100b802c21500c0010140141031400e071402c41c40c403550038600381c80a503070300c07001b189a482c0305040c003130121040701811402c028103081003019007011449000d0180e0500031040c0d000680f10b250485145600300182480c01d4603004010041200d10b0008180c081c6440e01a81d1441040014005420701d6244da600d510341d80c0c0c1d01c1e1320803000b003540f120000100c1e040981a8030f82e070740c00140707241d541001e0742e501081c4d003e4400390a4548124182d5103a41081e55002d031402c0384000c01a110700180203040c4004914850140441c80c46598295270060301c480c5003020950800c808046114150740001c0014004030780b0104018822030140480d6503501c401818180218940340b580107402500c150948000304507213034040d444440903226003032041c21095048030036113400584101a06c80d0b002c1204100150201404800788011442a510100100006040700c10012102803000444403000d031290710031240540d1014a505200d400d081d840c050303001c0341c007031b1280c0d000162007410007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 423074082 1250 423072832 423072847
    0x40c020c121c0302181905012003040605090d05100c120c0f0f0c020405010e04020405250c02060705060f180d050405191203030e0706031e0506040b06070b041406100b 73
    0x407042c0f107120b08030054080684030540d001d51020206d8507000c0c40d0f0015200c9418541c8505960b2880360a8002413030245191170b140c8035090350240d1003400d1030794000322114140004208140a002105810500d021800003030b0340c640180300d0003000040d60702140c0340a143d031900c2c41c2d021300200402d10b00ca062541d072400610720160b50342d440100300298002d042000218500c404580400d000e1403003aa41405551510a101c3c0110888518207651200307030455010300140c0301da203469100c180043d0000345400e4507520b90a0034004221818140304009000b840f10010b946800b06e080350585501810b19110711410003045807040d440355900c148298005190b10a000b8074000c4001c24070f0003815a1001014a0060046c156404c081002ca010b0184000340d13150103401551210f0340b15149242000040f02a03442c000c03c8054140e581003552004080313059121000100a441c0c0a02802a840d00c3c00e4a0011105403142c0308010032500700310180074511601104581c103803031116151507151340b034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 423075332 1250 423074082 423074107
    0x1818100c081f1215110c12070305160803041703010f03080715060602060a060b03130209190c0c0209010f1a0703050c070b1819091a040c020c121c0302 66
    0x4254112501441c3c14011542c10804410100c3e09000b51011062051401c0359044003094001c540d1800740a0300710400c51060741181c140240f0782075109c2e043c0309050119104110064074214401203134400c42c00010321090000c0081c8501c0e0426250174124034640c1001140e0085142501c40205606000320707030789040002081d64810401c0da41041004403503610315000b9074880d0244d42c0c40e085140b9150340070810b202c0d6101224071070a018103c035090054640d080c0321501d2030041941c48100d001c6540541040c0003030080800520a6981e0f210b24041c050040003800309041e40162984400c44030704103c0c900b0380351580b09082c4150503116454002601741074070310740305040006010707015900c0049040483c3d100038224040e0f03911500310107003242c113050100c3d4810001410300c101c11005020420700d560b6402045521901c0d05d80068020b60b000e01103010381d001800580d0150700107280c4030b080307800c205002003404002d02c0c1c001e2040e03018034100c000b1182c1462a0a108058000403110003841 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 423076582 1250 423075332 423075391
    0x50f042f04020a0806120d020c0114070606030302030310050a151437020102090d06021b070e09010c020303071e0903080c060103030306060521061818100c08 69
    0x940c0507000355615000d10800804406045900e00c0c0300b00d01c42c0c00d6104014400050700c1800042d0740d0021700721003501e01c005581c00031162469800305501007106600044090148000451294008603201c0c00c02e004040c611503001d030000e41c05080e03150800c00401a1b54280201c106c00c01d4202a0009021040d90780e100d44101c03443c034103030140284c0307170109503643c003c120140540041180d1709c0c4580d50407004074243e1103a8201c8076440521713184100c3c00300c3c4556005124807480420400000003001c2a128145003080c3d01081058905c24100082100c0038010001d420503140b010314a1031402200c003421000512680ca601c42910711600d0502c94001e030020310140d41c200d409240c5031884070343c07c0c076034a91007400100c00003400c01e480000c1aa0017002035680705d2076442040440d05400e012481122000280465880100f880100d03100840b40044103004400b00c011103100c010719405003d29060504028005982c0b40503400310500c2c0d88100021341200040407510f80c04100c03078001d080f001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 423077832 1250 423076582 423076673
    0x606020a050c060732100209010215060324090f01020a170603100f0c0f11070513020f03091c050703050304021e03030a020d08010e040210230715050f04 67
    0x41c50491840705d9600007040b4052003451007000c540344250741201c10b1050380101d542c1180580d2092800000702c3d00d0780c059841d4041c00240448040c09001010100411032220a80d10400010300034808004024006660700317192890003940340107101c95005044034401c0d004400904980c0021036038594043c03100040f0940e10f11024002500d610700c25a006040380c5011501080f03081201c403c406001380c00c82d00300110101d0140003d50b141c4000e110b500203900752068810341e401c010409400040310065405031000c6001003413030a20742890310b07030103c1c02c40b00444c060040c10300140002039408001c50394420b9054402e11800d01781080c1c60360f40207103001e04060340350002068120416a00143c4400481113030340c6c8071040c6981c0c4010312032410301c0c251000303904456039500003440d260040001161404002200701e010302c505940310507064000680840b41400f1144100e800d0711a203000b15034102102c0d01207903601d82026940d003925042d006400c2c4001685c0b000140038032400c152840e001c003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 423079082 1250 423077832 423077873
    0x601050112060e0420100813020f0d050c01080121140f10020c0d1e080414030301090903110d0207090f14040803070305091603020d0c08010207060f0606020a050c0607 73
    0x1e03041031700c2c1085146000c004044c2000314001c005450918044510302000b8078203803a4200f40da120000328501c0f010f90a88141d8000e000c160a1800c1c0341c89010164007094000c0002d40b030fa4000311000100a240c0617484031031035900c07100710817885c1070b07051618000703d5034040d6807010043e86002500b07040a40d2419040118000d800700300713134a083d840c3c00820b81d031250303401a501c0340f40360b991080e17a62101a03401c00318402c01031440c510950340184411b5800a01400d0750216a00001c24a1459580241c10855486807100e1000702050341020011000c00d103140e0142c0082c14852000950382d0016201e003c81135516880ba006500e080366000480a40e41d02d100ca00f021300d800d003403488040d8000c0c0e8440c40000c4c035140c0000c103440701c0481d4403d80400d1503032030601e503140b83d0340801509424402c01a18074144151000402c2c8a0900c02030401501c5081c0120301c40341c14146176811988558000c0003950000c4100d040090804540503503c024101c50f0b680c0c507401e407410000249407005401904 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 423080332 1250 423079082 423079109
    0x20406030819020c04020f030c0d020906070303090501062715050409030905120703080d020a05091c0317060a030311070902220b040b1b010b040c030905070512060105011206 76
    0x2d801019420100a00c00a80c088455441020741408101e1065030604000c3c40b03030500114103580103550040042c80c0120301c016051010702c60000340f4550001c00101e002c039545043c04000c0000c03e0003108010620404442860340804180c50740d8011300d42c01c2e0b4132401d0364881c004004850354210b040080c2c0302c05403003080010340c00d1401600b01c0c1d4150003004d1060f00b64940c1e00445100020302035007501c3d80b1061050a24a044038400041e4001d01869001e0105c18480f41c00e4540f2110040440da00c9450441400c1030303c0c5003409048850349110f003c240d075019504011443d11388000d40012a9418a810314031803aa44030054200340c41c940018100d01d0000481002c0f000c120300c0006421700d186a040307405140e6907a0340d208a0b100d0703842400c0106500307101036900030381051a603070b4090103101b001181a03103519001508a0300881e50034404a60ba4138009401d000007000450040d16081d02c440b021080c03107000e00307651814140300d0581005180030381801b21120b90303084a001031240110444 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 423081582 1250 423080332 423080347
    0x1060611060108030a0c02100507061521030e060702180903071704060909052d010f0503011515090e01030506060411210705041a03060405131109040204060308 70
    0x408820340584000c0561103240c0c0045008400402140d5404906495042e0070000c0b41e030034054051080102c3c0e0381403100a115010200f00d2600840940b0180300d404034050608128540ba00c070140646042b992030040c150000020b900320058038001c0c0c80403a4456121f5900f440090b41480000c0c090a01030306020040c0440b0440000103480300e42c0c400c01040d504a4038060a018540c0258412400064001c01e42003140300b0070341e4802c5030000084405104080710000c2c95100790728042840440c02c5501c000100039074800c0c2911440038200c110000c1c42107104444141060001c1030085800d001400000700b80c020b402020600d00a241e141c2d11610340d9a036900300b4540b146021107403c0d000d00c0c1001ca54206401900080700e280e00c1115402c59240c62150540f100d2240c1d00400c0300b400c0c03020800010410a4110b82042c0d0002407070380d034032582c034079054080c8800d83c0c0000e046c2490303006e0401d140d6000218080d10328088640240d8803030340595290300004020300032580c0f0280c102240000c003203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 423082832 1250 423081582 423081587
    0x150904020c0312012907060e030318060a06180c020c0d03090f050916110c030709020c01061422110c0604030807020601350303010e3304090212010606 66
    0xd02c03540303100780b40107400341ea6106000000b8a40140304420030003c000c1c0c5c2011301d20000380250110a005650005400024407891445c582c020b603031009074010000100741070000100240e580c0100c0041c0140303d0740f468250548c000504000e00c144603140c03141c0303440164620030014200341c10030043c000300600056090140006007140580e080d90a031001002c2407c0c01d00d219480c0c0074032145c0b0350800d10003e01103400c59180000310700d10007160084558402c0c03265400c2110201400c004400107903160384040c00c840c01c440d4150700c502094142016111000d598039504000401c0240c0441c1c050001d65084484c0200050008102c0c0340d0008140042c21040004010f486644280c036081c8064903000e600340ea9a403001d11440c4c82041c074050310b0001c01c0c46940c094000c45d5140c02c4050781c000650541c0c045c1590800d800416044580c64100082a81c082c80e9400d1070f4464090342e800703000c1100303030a00340d00919040b8090103280c40365a40004c41d1224294000008056070003000116181c5c0e000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 423084082 1250 423082832 423082837
    0x1140d0501032103091a07021e1f0501050f1e0409060606110f0c0d11040501060f0f030b03060a09140a060b0f040501051e030a1e030f05090906150904020c03 69
    0x206001022194200f4800e02a03c103551009400c00c6000c3c0f04042a5008200d40c4980240514114050001e206c0ca44509115692603401440d102801c000e1081801000b21141c0200380b0321000d0341050010400f0780c95a030342510000704240c0750758860704c401303610749403042000804070b54000f8a084140d40c1400260351041040e100c00383e03039142e6000540030189503500340d40b00780d560703035508030a00c2c80d00d0a1912038445400315100e800700b07140744200034001804640d000d81c2712a01080c4528004030b04182c1c80007600004c010f460400300061000440440e50b91f8200600b84550070703a4480c00b400901142c4960701200111a104803049101d007486d0640c00740c9006186030f8003c2d08903d8203c00d0078606402010305941d00a0701210030081141881e95031044520b12680d05400391f03540c50004130300d5035100c1c1c91200d00e0007a43c807440c003501483c0c000c00d415288078660040002c01e01c9030b014140c4e07a200c000f0342c0141c000c4600d900703042c481b02006a5544103480788940c0c41440084c0310780750070601002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 423085332 1250 423084082 423084113
    0x50f0d020c0a0923060a0b0c070509090307120f0e1c230606060d02131707050d2001020115090911040c02030706050712090b1006090b04030201140d050103 68
    0x140115499926003404094940c081c804481c109600030701340c5400990a2201684072800400340c541c525030312101d801d40c079800701e0078009241d0800c1d00b082c0007a0620048540d04400320b070000754900103407500c0e240f0790703100c603020400100f200311010944110700c40c0e405c0c40707541f2000404680c1d5a038110b1600d01e00c06d40c8121001c4544a030b40d110f071410a800040b82c0303141c03103094000213803035107030746000c10844290301040318549815800c1c0186500320469482a0000e054071064500c450111101141e103052030951200b841076142c0d101050000d46100360010f1b0390340510301106054902000180c1c054421098aa10306d00441900044d2400a0303401500440307024040268100c400d141c18001a07a102c2621000960301c1002102c000546650110b41d20500754a00b41090320322403007803001590918403056461503090024044400b0000d505031004000e40d08200740a545032040c0003069015621000c1d06002c2c00e03906101256070b4800c21190b07582d0340b90307008100641c1c50703262a49842c4800a07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 423086582 1250 423085332 423085339
    0x60307120e010213030b06060f0c0d030b09060a0501030e15070504061101020906030106050706240e07020607080105060d060b030a061a07021302030c160305031f12030309050f0d020c 80
    0x2001401401c2062003200d5080c1048620001140e06544481c8005507002e0106500b018040001c07000d000c0b0392102030036846c00b03c0005014810f480d560020140c0300601442ca1040398041c05008465607000002d000712102030a011034051094800503007455410032204500c95402c0c0c041000280c0e22500030300603201d150f00da011000b021140d0083c01c0740100e1035103c1c1c1080d010001031013120b00810192807100c0c8180b0000c18104a2241c031101002a1840b2419070400000303c244819182c0c0c4030031300c0d44580c00344000d101c585880c6000400c1c00c401032103064041d1300700003160841d0071070b2900002d000e000c0100d030f000e65a0a0003800080200414410103040122503d49004420054800c6410454000f41900c1071581ca11400000a52014010200308030b01004880b00200100c054250b0075402034450b99107030714005074201e404d895000d211502621818800b0b002c0703001448051b200041e01494002040c54a03850403034500244140712048900c07a28000d10010340c0d00003000700500b00c0c10f9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 423087832 1250 423086582 423086591
    0x30f060a0c0e06220b0d021905030f2205010e0606030f030307142a0106230105030c0705070f1806170c120c0a0e0114010f0f03090507030206030712 65
    0x189000c03954003210b0041260b00c1041008140d030403ea203644801032000d404540c451802c1d507140d0b40b0080d164011881c4480468002c5000c1e98007040041920541c100b4500746180780d890600380182d04440014040c80840c1c2c40c070701c1400e0340da4000842c0442e045500c20700800c1010681d0a6003035548500b129828030901c074003504c07990b2070b071400320039640560f007140c0300e0050762401c1c18078840c22a004984030300000400150704440c071b011114903410003034400c5800095902e04000c0c18002c1d8100f805221520801c101407034420690b40b08003140d1744404407800480c0c482c8854600300e0b040c2866a0b121010710b01984034042000802014070751152003098008100c2d4a964416004020660015403040d0340c01000b101503103070034004a91007011180609a80700d41d00898006000e4258507040a0031214518006110440c0c0c0c42c0d074040080c81c000d0903d10409000d071300e030040402e800410040101901c1d00148000c01200b04544000745078000d0881d6140d14010000402106040c00000c104a081c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 423089082 1250 423087832 423087851
    0x1f0608041a0a110c0109050123070806150415030b060a090618030f031106060103180305030612120a02150108030a0c0f080f030a051b0306061b010c0504080d0912060507030b030f060a 80
    0x2040340c509e921b00120100a96980ea00070303100090000c2125410400a003410440403a50380001c1c400741243c04141d4091141d8006e0060071948588803540c007554081056118081e000750010080301c0651400d03043d00980001620513a503440d500041c1300741e81882c0c4060170140c228115140c050044012204039950b004011001d480121441441e032041d01c00000c00401d105200560344944094003001036402d107000c505141c003100b500d0186c000d02022031806082a030600181c000c00c855604107001650503c40e4181c2c0342d00c6802d80c00001d0200e030050141c20000151600c0001e650170480054503405180007100300c982c81201d40d02c0b109840c0030b00142c507050203800c00c00c41119014210b182556903580600c001c1c0e070321000b40c0710210000581d811041e030009020780813480c2c0c0581e94440e200d07071924040d03d01d402e00d02c0d40f26200788285401c041c0007050350618140f100940040300442e00c0c0d10740341d5013500280314905c03031590540902028040511310000d41e56002d400800320400100c2c07032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 423090332 1250 423089082 423089111
    0xc030d0203040219030c05120f060106210e070e04020111060a0203040309091401090507200a030216240306030f030806030f010b15030601030608061f0608041a0a110c01090501 77
    0x5404000d080b00c01b03080c0d0a00003820b080f00b07240c15500c40300084030b086036034803401d061800760300341d211000203500d40c460f1110240f041341e801d440c41c050340d01d810300098240059a549070b59550050480c60031070040040c0c150380c442d2310f51102000c02c44040d50170509007000414060361085409801140506a001030744525610030b003000c117040043c10f04120b9013022074410103440080c0c1520100083d040070000b01c0c0c1c52220301800b5a5422030018104440603188c041e0900d00c02e80e03003680b4040080503040081c445299036903214405842d11010040c403401c4000e034010030441e00090401d000d00720101c0109500b010300c0318010103080f403c031800310402d0020b0509940301c040301d840e0001c1400d01c1031108206604084d6400c2441410042403054840100b2840c0072411074034070000316103e0072003841448640d41004080c01d164230f400d20143c500758a9101107001c8551501c1d443c80c0304070000440300b0b201984105402c0d50040c01c2da80c1c0d00c5a0901c200d40c0a4100074100388c2f115407800800710912031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 423091582 1250 423090332 423090379
    0xd0b0c0a0914031903053c090102061620010506010201060e0601021203061f051b06100e1b0c07050103060806010302010e10110d120c090501230c030d02030402 70
    0x4500030028110b00c6620074201c0c1d54000380c0704c0c044060210a0007072405440540c590050800301140035002001a07131074a04020b0401001c0c0008440c60030800c0c0a0240d9000c203105510102c3c00c020020050700801040314010350b03078154003009891100b24a0260394041d08258040e032000d90091018549985840310455030035030b00d06c1e015a100442c1c0a0b00709000502031644054001c0c03043c0781c0341ca02406040400618280340800091000440c3c80841c0e007030116120451407441c0c0184900d280c0806c80d0901c2105d2400b841e06011803c0c070001e410320341036143c014502c4000e918401d445a01c0c4002c02640c400c0c0b039000b1140820304044003c5169000020018100d1350142d40d0740c06c40d03005036418400c0307411440b2182e004001c030003201581c81c50300401c1048030321005662000d88600d038514580c022500610114420003424800070882c2d6a07101c403080d95148001c01d810220710002080c00c3c01644941541403900d8013000c00d5402c604005d940c0030b50311890007502c1b412a400c0c280d00452031101e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 423092832 1250 423091582 423091619
    0x308060901080705010c03180b0301051903050a060b0f18091b0d060e12070305070c050102060f04030e010e130f05061c060b152b0902030a110d0b0c0a09 67
    0x190302c2454100103541c030540c8903a0300903000b41000048c0704050503c1654050349a0010045580000010043c40c01d001d59209001d10000310541003036825683c4280c0c5480310050b01920154030707070f6800a113954480783d094140d818000e2240412801940e2001020507040b6142e024500800b086180c9555a01e01d201c500d2813401041001c102c0704c2a90788070000c2464603800103ca1203440001422485110000c001540c00ba459482c0c5074489403a1a83e24811240c100ea070440d0131820600442c20094030380c1c1a00164141061070f940646400101d800a007980703106948424480d10700c00c40314200342c2c0f250752540a61074044c0019500c0d9002c1c0321440001c1914cc0d401c0b000b141400c08082042948401c0384020010708084089154050030383c01c1c2e402c40600008491a05641900c24480c6429010110600e003032040c8101021a00020386030240c590020706800740c000300848150f43c840345000941907000106601c2820400341d914056080741c0400310205030110000700e00b41e407110f40400101c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 423094082 1250 423092832 423092849
    0x806030d0203070b130c0f0b0409060b090d03111228090f1a16050f0105010602160302040e0c0301020f07050d050306091807081b040605060c0d08040f020d0605040308060901 76
    0x1a4071010320300345e40710488503815170345035030310150225412a104600b40c000780b5a490300c05c4d4803103080079104011500e40b81d0020003245410400c2c42120786421040321384041e010708041011200c8154040d00301440316001d0300011100080c0710f0329801c0451030701025040909100d031400310320081d040c0c8030300303510380a005011380a2480420600b080b960000c64100d00094034141407071507051a400e034004007608111102c0c1c004e001c0903201d01a00740728550042c0083d10040110800714015003d50501e240800b03809651980d00ca4a25031070301304040c2e540120003a008540d01c0040310100c0c04250851082110a809028550b000f400c0c45a0705990103003100408044081e1900c61b02c090110140c00c89481c134601450038006820300b07052002c007005814119003110365055110810040b5642a0403a80c4100c0f030600891000e81c20009000d01c1c59402e504101403562118244400d10280c03a4130b00070342c1b01f1459511907040107065000306015034400d4a901509849400400c000100d00f4042d6122 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 423095332 1250 423094082 423094103
    0x6030e030a021f0906050f0103150b060405010c0203070b07030905030601060804030509060a0201090c0303030f0e160b3403030513051506061605030a1404031104020a03110a0806030d020307 83
    0x4003943d041412400140c20464005000b0180b40c0d075020548104482e2000240d48280c0100306020007480e010701c00c2d11140310100300d1b801883c0001055400b0354061541080803501400f4119102042002701400c41c3c00b510a4075101d0300e15000784101810300038540240200703000001d5541c001c0b00020f00559141d1a003e0500c0005030511185030440c104c808119905c0f46c150342c01280d0300694072000b460003683e000c514110f45c0d05910068900c1a11030144036403200403420720404c00f0781070780d0058800300c50b005076484d9101c141c2d0301d1800c04440c0342000c400206481c0c4c2c42d2840c2c070000d400a03015100380c03002c0c4825610119008080000d100010303003540c012802404681c405140d14580c8504024010384c10001c041c0780303000444604035011206503000068003201c0540003a2b000640c04e0142d039003185003d0940d580d4940d4190501d65950060b80c01154035100d850103900084050b03e03110a41d59200d0b0880c0c400245a043e05031034560180c00741c0c91654054601c0802110070045d00881850f1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 423096582 1250 423095332 423095353
    0x304030602030a02071a040c0501020705010c0602280c02090f070806130e0d0507052b0503090304051e040c09080a030818060f040506070915030213050a0b0406030e030a02 75
    0xd01a42c0700400e0862044d030300b004440c0018403a40c0e060041801400b28506880c07409145c035180480007904a14107541c40890304000907a07000702d0b0392541640c080d00140c3c035200034140b0030303003180040701d42d42c03055081c000d803000c9500343e02c0100300d89030038021902c482d205e803110501070070250703000e0303a90030700152034080069141c1c02c0250814030303040c00c1c09a000403901c0c10302080d2070400c2c10b41d4000c1c0c2d0014030b0002e0b00f50144070080003d2030701c002c14201240318000c04034944442e07018400c9135080074880e0110002d8184c110510036103004042c042e20f100700a02c10300d2203501c00b072050101828070541c07400c441e5074451407142c058901524000700050000e0106a102a18030002c0104070400b08840a0b130117081c006014000342d401040c0e481c40a0100d414285051401c24100820300020801004010013003111120112405071030075003401640e46841036400d044212840d001241c0020404000207200000b1400034811240aa601004107101d08100700d500c030b20840c0f05000050f4001109030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 423097832 1250 423096582 423096593
    0xc0106140a060c0c030203030f040905010504020405010516050a1502190207050a06050904060302120a0b0c13030f210e0406060504080703170c0f150609060d0308070201060b04090507090611030403 86
    0xf48425010724030300089590b696000a2465000fa064014980408074040140a80c98040d442c054141280d042d07082a0074100004c00c140a4111f0402c41c0c0500c40c507008083c0003007030010300205500284040c85003d001c40c50b13940a54004021015500d0141803203000043c4041800c03010f6440007413020244514112088441c2e41046500ca070340180d03195000001030752a4a6408180700b9944040d100182c40c1d400c2862400c00e00521002901000704085072540314a50802d00c04c1da54000c81c80d001600440c10303d80c400c410b003400048168010030030124209500100c1034180c240c5c0c21102805856111541210640624450002194002c08080c00010002d42002b11400d007480b036402d04000761110014a00940c00b0000f184a4200c01071140a5159401d01070b98400340c107480500b03450170001c0200e868580600009005c02c072149001c41c00c0a4800c4d008075000740440e00f0141d44854441d9540c000510741519031802103403654500041d446d0252000e100c040a02001030340c14146551240c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 423099082 1250 423097832 423097847
    0xf040b010e2209050d021903050418020c03070c05120a05060109050601230301080105130b131104022b09030516060b10020c09010b0c030d09150603080c0106140a06 72
    0x1180e100030b480c010004420041d072050b8a0000d008034010418401c04070406801c0103061018a0b5038242c0e85451140829080701c11201102e11880001c62041c0050311000000e01804429070000c0c080054075205200c1c030040440180d441c102e800c480a007181c1d37000c07a6545e0141c1e0000030425044140100502030700d40c0d000e154007079018181242400340c1c01108444c140200e4910f0740715400080010701c11036009203d240da002401c2c40c4612104a101d448071a42903600800d01f013100c00c1711940150402200c141c50b10200c0da000382c001c3d91500024840c100e22a1643c00741c0003401000401e0300c40c03502506000300307801c40d03030076444040c6409000040603018081019003a2034030b03034a450b0038840d103448002c107011030004180c0c058280e401d01030040064004043c0c2c80320030458010b109400c03c0070008000c07180c41c51180c0c03034005200e412914085d4052100714411800c05458810004140312403400205900d42c518002000b80503281c001021644006480076038110455130300510099000c1c029 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 423100332 1250 423099082 423099109
    0x50711030d270506070309030b2d0403230d05090a080a11070503100605031c1202090d0c030803090610060c080a02030c070f06030b03030315062b05060f040b010e 71
    0x3030b446840d219008218a83d0003034200700c000035403465042040c00b40b0300113450340207100c0c0d4103400d105102c580c0307141c0b20100f10304840c810750313616000110301094061034241d900b07030b070542006d00c004519800882c1000d03040302d1000310169003020002101014041620740c03030580e011f40100c1c00e05001e10030854001217042617001261061110100b41e0303aa040103459245a007904001c0f4100d814007050605102c06074a000d10710246c050041c000c007681007040f9103654194020016220203003000010721b0713150040006020b02680c8040070040c80009402584240208021200350b51212007440b041d0011a00c112800120816180000a00c00e400204891031251048a0401c0d00d00e444c600e080412590003260b60b40265082008416014051002c030b801c000c8002e5070552034800203140340d070249107001620071140056201c00f001c20011001c1da040b03070404130806c4a0304560380481c0040000b42e41441c03007a5074100100d589480e09024022200304181e41c0d4080000290050011540c820130 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 423101582 1250 423100332 423100397
    0xf150f0c0a06051005010c030f14070609050d0806090405030d020d0902031b0901050d0507091d0f0d1407050a020d08160803060a060314130302070b0406050711030d 72
    0x80391a01041001540341c090140081c440c204501d0494216041d584003d05010156107840c02080e041030203444420300a0034a1007103d40c50700c0280070544241d2000a0a00e4501039502041c00000500c507a1840300c0c50300e8030001c648510082200584040310010001d41c020005180118442d030060b003061014a480816400b000b0f81c0081e05202c4501e030250280301003c6074008180c80d00d040785600620003a5104c5541d0080e90b1140d50b2100b10318020000f1035520b40c214110700990424050621200c19416298404c0225200c2501d80240c601c8150005448810310390b0f02d00c00c800100e900b490303071010043c805112150b00342b001098090705d0554010400b40581c1c410300c00c0642681c12503901c924440e603a40e183c003108002340c4140d290000350030180b40002c022010619616026000040d8007400714000704140703803c91401000340c003e40b5022001190000e0455001b070040c2848610070007064441c400c14005240c0d1f280c2a002c4081c0024040f0130080f9002c3c01e003020802881443d04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 423102832 1250 423101582 423101587
    0x20070804030c14010305070302131205031905030f100b0315130609022107080118020c030412050c0405070e0d0204060515091c030c0209070e030703200f150f 69
    0x3070701c449080803120f03400040880c0c4161140c004941c2e00d03218040d0311940d039050460404003203109510201540303000d20074031080c107035103a1010310200308107594068200c80300c2000d80d81c420460080c07031a04281d450090641008001c0f0b6000d800d003011138030580d010400024110758440f030b4415841031080c0b189079000304903100120003081060080102400800f80c015a441e80059204510b07030885d200d00c81d000c02601c4092207441a4007104840c1196110340c00340407816114601d00c0000c0c41080341000d4035100c0080e001174074560850078840003034058419120141180e00038001523510403201c041c00100c0030012015249880a881c00301c50740060300010b9400d480b080414851181c490546a01032004103000b00c1e140343c02481d031901c0c00c2c0100c0b4945807562140c3d50107030040c100400028842c01c00200010f14403031082c0d5050440e0400181203440865403820415248000002e852050454020600000341051200002252405402c1404000603501c00100d16002421542c0300080c04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 423104082 1250 423102832 423102839
    0x4020c070320151806130f17010c091a0403050a06020706060b0c0d030b131803090f080606100e060d050105041808030613060807030804090b030120070804 68
    0x104150405980b20307086901154200780e00348181c806030910100d1080307105240d041c441c02c040000b61942103a40e20410150201100300107040e50141041449800030320303401c00140c2852020200c030894440d109224646e0b4010040d80d403c4c2c810210300e0401003020300340c0170001e1101c4522402e952580d0300c0304080c1095185d685a508240032151309032002e81e000f10b480001c3c03212174403d00300141202c2c80179500d440805142c0c1619071a0180a42e402d0694032030000301d5640f42e4262110003442451400c10070002e08054940644144010940014000031350102c0c03c030190280e07940030380e444c0c03400a244aa944500300600310040400303845c200300342d0302031142d03180d1110009072007140d50b001004a15503040c80280011504a07070440c05a071a007406900022400e800c0449401c00003d42d11624903901002c030100c0135011507880b1503018812482d00000303009261028005682c20301b0410710112400308105402e807621501031900380413440440d0840da00c0000e0003044054400c680c9503003030965 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 423105332 1250 423104082 423104107
    0x8040816020a180e060702030405030a0803310311030301060207260102030c03150103180209091e01020702090108060903030c1b0106091a030a0b061309020d030509012006150402 78
    0x40101c11508190781341c00380c00070003010a001c110380c001824801542880e01d4240069580d1103400000b804041d00040401c00d0920010089800c0c170074a0070203018500400310451a1041800758158001004048440c81040d004000c80341200c060368010150542809100c086a058420f85100b8480021900341e0010200380007840c821003251403240c1d00c0f442c00c1042c003420420b6900d850350402d460800380d03503d00074100e030340302003d80d0b0140e50600e096541c039414146406605800e194424941c0c070050440c4c0d0303105400805d04544203844102c0c03c3d9985030b1140d0740c2c0f5007050720741038461703001800041c2c51110000040c0001401c0400c0036615602001c3e181800c540b201d030440d002d115215514030807082d45c403103000142808180c0081c101c445d265141c610300d2032030160505106141106400381c0244041d0089a11950004c00070a28030003a07180c050115440748030301601050585510302e942d0043c5007044032403100b00a01610081d640d9014200c3c842c680c0325030003984103500744621001e041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 423106582 1250 423105332 423105359
    0x60f010312050c4204031e020a060e070512061506070218040f030f1e030b01051c06051f05120604180c180c0210020a02070e04060c08010608040816020a 67
    0x102240e000744461a01c4080082d00c110030712455074580400e2030174880040d500000c0815007008402201c40d99085681c022410088404400b170841410001017021925001c6903060882d05e007100c43c03134a11600b19900d41c0d1110000c4440c40700e200401a001e501b582800c00080c8035a600c02819000d030888030074520542c00000ba00c080d0780350b03000c3c02402c80405801410084400065040089407a00b103280c180c4c0a01d2002408001055200c200d50890b41e4040c4059544200720a452101c1e503d010000d40401400c1502c101c512682c203e0303009000140001c2c401450b00119552242e00d010541e81801140c0100a081c054000380d44060702904100b80248408040e4411000c90400750300c4c000040790305101b034022401c20149030869040c0e08a800149031010058041400740c3c8400c1c03810001c1c0d00b845010b901c42d41c0e4030321504c0100810400551b00c1080000825111050340b0790f26030030111249401100d0082c40c01504005e44485410700d0f07491240340510041041152a0b250385450203002c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 423107832 1250 423106582 423106633
    0x406030524060a1202100306080d0c0c0605040b040b0c070f090e010e0115060309111f0305011a0904091401020f0702010905030c011e020109060c050309060f010312050c 74
    0x20546036422041001c958044150041c400302c03038804001d0b0516519610400748003038002d2142e0345034458000d41c2e80c003941250b00100101800e42d06140102100641208180c6070100d4480404560204840e80208151340c161070f15000100d003860700301980582e00360301462090801d03201d12000028005a241c80b180c0207404182d20100c0c280038402025425281d00081d8040c0303d905060043d1000c044103080a01219050718011601c0348140c1841400e0030503800328241c003c51003600c0110111100c0002c000c22909690781000130341c2c0e03200b4150034001c051580c41c0c640c81804001c500000c2ca4907130440e95202e0701501d1403414100c0c0c503102c080c2c00c81c1c1c86480c071129020004a2107200359a000814240200f40c03c0d008ad08840340d0900000304a14200c8845a4000e008001038080301c51003540b01002c1c0c544d12070030030815500603d002a00642049542c0000c0d4825680040d649007030f00081d01c1d0403a07501291102c4100440c140c140d815411075298048184280f64241d0844411600344d85a40d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 423109082 1250 423107832 423107863
    0x140405130f0e06092a0907170108030f03010302040c11100b0a05040501050303160309031a01030b010501031e0203090102131401080603120a0c24050a0509011a0f04060305 75
    0x18101c0c200385205441c00000c1081c0a90061070401c0790000d00800d82d8581c0802140340502168490081844103003c01000250020b400000300809150000c40c2c651400703036440c001040603030341e44401135a41e03c103040001c40c0c1c011051004100509080e0000480b01005080049861a070641241d2070304d00b4010808450036143c4c84203901900308804134001030b00059906100720341c108000700b603a80c4030719262180486207805440084c0b42c862810000915802130901140080316922581020800c0c0820b840301c40b900dc0000440d903010b0720804a0f0004821811036550407861241e030001d4200410303003405075400700950060410000f4514015000410742c9816a1802c0c000050000d000140120302075402818040e1500c0300000c19124080c426282200752584249070001d80905864208038010080d1080d90404140c1600500e01c038459800c8100b103503a8403003c1a6007a0303040b450741c0e010030746501409161030741401c02024101c074038050000308145507640c4d00d840c035240107002050314 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 423110332 1250 423109082 423109091
    0x7140606041802060414060408030a020615100c240906021903090f142805010c020313140307171605011403130303090803090a020f1f14040513 63
    0x54524151103100e07998441021410040b02da540d0100c1c0d5588940e0048048042038071031259015681ca1080340d000d885440141c944801c40004042c3d501e05040da08181460340000182e0814100000901e0165540703681d054586c0c0007a07111811005060410144110b559a4421100903040d0282401840c03144500580e125903d00c21441e500540c03210403410181406200350204201111801ba030b5034014103c42c440621002c282c520f010103403100048055004c2001c0124694502c002c1c41903940200001d0046070640101240c40e032103601307503042006020843c24401e8400500039601c2e646800f504882c50301c0e403158003140102c103441c0010000c0b41e00000600c07070800841c0d1005001000c0a081c540580070024010b14a2400010060124840400b0b002024103110741c10a0724641d801040e841e03075900304400013648600315000c0580c0514141b051654440c10140308a82011901d200c00b4042c14807516821104455024444d481c2c080080c013011a0756031b50b00c10101c4403940d0306600061b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 423111582 1250 423110332 423110341
    0x40608011d070b0a081f1802220e070c02030c0d05010903090b031017031b070521060114030f0106150905060901021c03020c03270a03030c080f071406 66
    0x246050b925400600440d2400d00501045640000d0308503048001d08540c07a042c8a100b41d22200594465480468202c010804200046100d0350007000000c08050036010b0403074024003080400a128815907200880c04030018800303610907a004100c1c0d51008094a440d4130525002400d498050002680c45940d80d4000c80c01b00754100c1e20103001030482007501d6045190004a501e00d00c5400d10821128800c00060a59005014011030f071039203251030390800d0101d10201c0c1c0140d50b04014044e5a00407072424461240000e180d40c0740701000359170316000305200da0030b24503a1041c060300d1038043e60305845032172101030410b4401e0003110054801c030710241e50750b500c42c1480203102441603484180107413810820350310166800f040d49104038645118400c120500354204038000d2190100b425030b1408041030100480a5032b00e807506880d10b20324590582101c60908010003146e81c3e00c00100810712421000c1c0c0050b8100303001c2c0030203580041d021800c1502d0368a4000200c1c12001c91000e0a030403100410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 423112832 1250 423111582 423111641
    0x406080c100801080604020105130b0307230412110102070812070b0609010605181302070506060a2c090a060c0c0c09020316031107051c140306010c080904060801 71
    0x1c0d40812a190007420340d4507101c0300039240ca00240c0042c3c104003000034000c000c082c50750040310040c06c84500c1c140c0e680c13406030001414014202031184480000d4007801c8145a0300100303580036200c00d00c109103148407013a40e03004032041c0740f0313883c00341503000d02c03500010042e0040c0005042c42c0d0310403188965412181c036205109043c000c0459100f50603600c010711425601c28151408905608601081c84001400141e03480701d2100c80c102c2540d00001d070490130040045026802103909030f618512540e103c420341d004914052410320000702090b6031492207034141802050f0060003403000c0e14900c0700140c691320305481800b03101e000861007003000e101c2040303071240e0f074a0010003018170110708504000c20303a02e60202c40c004103001015112000704402c0344204080360442a40202141c0c0301403a4081d0b10101e0700800084913003ca8044c0325490100102101100d210382d905a5851400030300503664144240c101030307002c60b0016664040440c03100801d110314140f0788800401c000c0b41e0000e40468 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 423114082 1250 423112832 423112849
    0xb1815070f12020307030f030507170709061209030c0b0a110403110907180911040f140112060302150f270f040213050f030a060612030f080f071209020406080c 70
    0x45204640c000c000d95004aa4070200c01f20203180c29240c0820f55840700e4900301c5910565100d10440460580c0c00d02c20030741e4000c19410120f40154448800b489201455101180c400c41406000705511000c8400001d138004100c0d42c1c420711002d00040c04204015461601d90402c1c0c008480071590b881e51085245004850294440700d00d150601d004140721841000c2990984600300285072500d02504006840c10181c07009481c883c205805a83c0c0d0f03442600191143c407040c07007804075842400d4407480300369500680050b01d0f00a0101003011140d041003441c42d82c460f0b520001212030901c001208a4202940560034201114403480c501d00e651003000344010aa1040070710a51040001d030350f00510025155040721812201180c0f1121180040382c10106003c1009000300d242160104590800303030156981140079540d2610079914483c070136103141400303039000c1c107141c1d24030000901080e200b85654031440c1c03140b110204001c202a40483d007616107036040010382d600b0000c012401750429414 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 423115332 1250 423114082 423114113
    0x6050a0503031303080a020109150203010f060906090e13050d020c0103050709051806030a0c0602010c14041809030e0307030303050f0901050f01090902010216120c0f0b1815070f 78
    0xb0318984007480e20040800c1c1c6140c8030041c00a8001706601c6c20941c004c0d03010310320311034101d40004080c4c20204817020095009024064080c130b400c01c00498038900c182000000d4070320319103507000001d041680c0c41c045850001d05d854031020b0003042040008500780300b904030300c12203a002000c80321440c01c005016640f006107110200012403004100c581d4801c0e00c9001d800782c03118689181c6448000120741002800200505042d1003d0704c001070302035055101309820603c65542d0000700403441200400c1e03109501c2001100040c4465079103510515a101001d07072480b030304004403c2142c1e000404e0500c113060340f003900840d644d40c00300500c007460b529110344c0c4541c0e8007000704810324115503030a8110f4010f00a800da010b54492010045900070010b041e00e1005240c000c5140c29580c0c00c0e401101e11344c00d00100c0b01c81c0101c0c040060501c851040d01c4d415a960214042c0c140b058051460a1701040020358681c0b08507100540c1e106212488010720841e07026440006060005040801d1500903640 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 423116582 1250 423115332 423115339
    0x30e06010509090d0305060409020415140d02060711012003041802040f030803041b0308030604180302070b0a1218140715051b010e2d030304030c05030d020301030606050a05 76
    0x400c102d400203000c07424141c11304182c140015161036440c0440c0040c05490402500240307052804211807143c12040340071a060340d9001d010070150001802120040540003c4d0410814043c4400042c0c1c4800894040001031502c0e07240f035110030600a403215002e0940f1001508002010300c018007050022000c1301d903891a00707503c1c0a00d80490340b0184500ca11001e0700410b404000308013001781c0c241810039140d0050140c982001e031a800c00240551040ea40c8501c201d18203442c1c0d500c0b2542c080d2408001c9a051f030050b00b00e85240c00003031903003584444050410089100b0105080340c0b03092050083d02c01030364030806170482c2ca514040122502254070940d03240d20400b000c22481c200c9110600f4100c1040c50403d459862a0041b02401088940e0b4840300e54202200e6076101c1c80c001640111400444655515141c6411040d0200c80071066418040c1e420400000b00468001c4000900d580d2144003200c0c50b0010700040f900890b0001c0c0c004899594440c0030401040c0341c1a95000d000c0c09007103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 423117832 1250 423116582 423116599
    0x2060f270103060605031e060a0f080705101e05030601030e01090f0311060c0409020d0b060a0c020f0607030c02040b030a05120403051005160309060b04020f03010e07020a0201020d0305130f03030e060105 89
    0x207030740d5102421f0007440f040b610300d0000780c0022003d484410285c0020403410074100d00c040c1c1c688150135180e0740917008890180d10a0a006212103206460a0806001c0ea5110032160032900500b11119030008180f00c3c10305854204440400c002403207042901402040055103001c0c86190040400c5450b040c0060f103030384203500b800f50340c2c92100122400c413640e82c04010b0791482264504001307012444000c0350303c920049149401182c2041d9800c5a0a01c00c540190106107000100031345400303844009400550302e03208140040c1402da000024503007005084a990284e596a4140780c4201038421181802022070108200a030400c084564403100500c140418648240c04944204901b1040009c15803030700d4684051000304d500c10500802c001c2c10a56580c50858a4240168400e12400181e42001800907001a1020075002d070030a81c164050107203d40942011006040c0c0540001130110300740b10a0350015120720084041c20748240c0b0041804c0004a0245042c100164411800f881c1d11 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 423119082 1250 423117832 423117841
    0x70b0106081e100902040305100f1503110a0306020a090e060105070b070813060c05130f03050a0305070c0b1801031505030715091502010608060c130302060f27010306060503 76
    0x90180b07840410a090014151661620056152003c03650300c5800220300c00200032007070041c0031441e00d04002000b14140149810038030188115960b1002c1c00200c1c060030802031000403c0c0445c1d00348202030040040850540300d45420301240d112140001c0407415160003000b402600c840165444802420300d2410000141c5032006001401050b007005c00c504c20b00041c041041c8502c10091070740d04008100a260451000030741164407080d2003c0c01103104400000d10765148015440c01c1e40c3e403000c00341c407440c080ca44d030665054001103801c0711407103410300c0d01040c030030788210241803510b4030101010030001455001600302c401506414a44040001e402d00080d200004c030502261508543d0346403800d80340d8001ca0b1040344907001428452906680b001d601503054000800303a80c0a8800c1d40e0b100d072955001c400003403281e50b40c1d00e844404045402c00151410070043e080c070306020b626a610748000200e928500000080e82803000ca0090400350700e895030300d40310350005400c00c4e0400d1855800d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 423120332 1250 423119082 423119101
    0x206070314070e03011e1d010603050c010c08190918090c0e090f070f0504140f06010e0f10080f090a150902011107030b0108010c030c2001061a070b010608 68
    0x80061244043c0030302c80b5101c80203500e095010303280c44005130f1a0405141e42d03484411019181006001d00080017441100c0c584500620400003129031260040980e142d080c4010368060080d1041036032202000c1c0990b034900880380d43d28080c5c43c0020b9841c40d20300303401c00e40004155002d01c115024140c0c40e04a0034000566244400e40640340707503070881c2c1d550359030340d444a51034407503a210b903400903001d14000042c04101004801d020b0b0384089405101c2c040042000b0301c5294012100040400c2800c000300300f40703500694415002d004081c1220303d103411004081035100d480c0c1c44001c4001400303201001424008110041d17001034013503018003038403803d07034842590f00d028a500038409c2a56685400c01103a000752071061003440c114066801c883d98904000000348400d204840055007000342405186220344150030140b003441d00ca80e0389119142801c040e81102421030a031540d9621200454039040c200c203a8034103c50090400d036541c01840c03070302e40140d0300c06901141c00e1142d05000d101c0e0911 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 423121582 1250 423120332 423120371
    0x106150e060a0c110a0902030a05130f0305070309150c0c06090f0e0c0903010905030c010605040c21110c101808030105190e0411010e0a08060a020f1e090102060703 72
    0x25803910b00700c0d0303a445013818826201d0072500c10781d1240110500080c80b039016000b81d84142040601080f590340d50f901020420703ca4144010005003982d01c2c842e0010740600b000d05072460080c504000c0b03854840d280c50000045204a06002c2428031544204100c0c24410303141c05070140d86070120078035203000c1c0e0020424410380540340c1000d58040000700840d0f40789056680c1140300400034412892141070207500d9034030940c070f03060030355007444404a0103007494021807042d00281da6800c0001840410b406400403003070f1500c040c9094403414404d210b580300a0181a10080201c060b024492006010030221054044085222141d1001a0000c01c0c452000d480c1110015204013031031030004035a10300c048503260040c004501d072460a010030300c0360508804030207070743c280c0f078010307190002c8410041b01c2c0031580300d9054903520440000715009038a401400c8175489240d0102e090144180c04c0320308409801e82402ea0b494030109400320325681c100003054101e821424100540d6109101e1a480398 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 423122832 1250 423121582 423121597
    0x15080f011406041e0204031a090102030402180601020a0614100806060d0f030504090f1d06040203060a2007050105220f020f0609120106060909111210030203030c0106150e06 76
    0x2903680300102059a240c0c44c134204544a50082d0455485443c0e10b0002d5031051030755401d0001c0100800054400c240510071a801a50010004403503d0201d603000100d002c030050019045020300400c07000014041d0042c1c10f01e030018030780300281e03c0c40c110300d2100080103a07500c0000107074001800d0068503152800140c542541003050f035110701c4900d08040d41d640c8140c1d441801214640350366811145d01c0c03948008005020781030b20f50400c003c03201e80603a0301c8a003614040e5254000c1d0001c20441c00c187c2d403000d823041900200c400003c00e41103c0914190304105816142039465508010116401210080701d00520405104500b00140c603071001085117944024002ca2000d2221440c60fa6402e00fa03030a0001c4c01403280800000a014040c040c01407480780c000815010480447d20142c140110300001d00c0c2803220724203121000e11a00c4030400003501c1400c0d541c00c603400100141e10700340f00402c401031030704001050541c9040d821000c6140d01c01940c2c0100214081410340036580d8100300c40c2c3c607 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 423124082 1250 423122832 423122839
    0xc0605090106050f03070e220b130224180307092901020d0c03050703090906082a15090a0314070611030a0503280c0c0b0f1015110115080f011406 64
    0x12342c01d05185c007995030401e081c006445c08040c5010000c02240c03151034502c0403403081daa9407807907040c031034003000100c5141c03030510621807000d029140000e11204030390100d07030100604030703542542c2e108038a0007100c070004020000700000001d83c410302c29500d0303411807605000307100a01c0303540a0020000e0050011400040811a000a86000f030501c960160400340a80c40d004000b40d980e2100696a01d0a460702040b81502517200c100c100d603170380b50818258007080500782a038090340d030b195900d40c60350014030340a9011190000c04004110034500c2840c000c142d150003000c0c03050610300c02405103003d000b001c5146030700822040031042c0d440000d0301d4101d0080100e60500080c042c041141c00360240450100e02882e02c900e8070083c0b07604c11341c0c1c02002d600560200c1c01985401c0d03d111080f001c12540c812048107a440c040100d2038009a24030742c07044151800c800f2070181c400000c3d089d1140719600b0703034811382c0c4980e003441504000c1c000c8200d46281e80c2c008100b000c00c8154034101000000b40070510 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 423125332 1250 423124082 423124111
    0x613030311030405100801081005060f0d050703082b0b100f110d0503100f081e190c030308010b120a050903070503040b0d0b120303040b070c0605090106050f03070e 72
    0x98036002c20075200648001000181740014094000b0100007007442444c00da4450102d901441e40851700c2950300503100a004043c03101010b070148200409031403001c8a4620504c00000041032000014140084020580d4a0360052040d00c00301c52140415001142d585040c1c00000c80c2d81d24000168501c0d000307820180d10703040041c1070940394615202c5d4882d405024410501c0340450740a0b0007941f0640000803418100c0d40c4807644201503800741d00868145500014141d42052080316100306c0240d0340008681405002c400c100d60f100360800b0040756039016080040c0209500040094054281900b16609000004404c1a00584040c0c0300d91410759584022400c03002c0d0a0044030529500842140c0d560ba030754010088481e80074202440c407440c80c001542c40b80389811020585120f86400080d8210b0700c0b40c2d115207207101006040381e800c0c007503c01009000240700c1e0150a10460511000003045c625000034000410340000e0718034480d03004a94103001d2683c912003800c0e00050794152a04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 423126582 1250 423125332 423125357
    0x181e0409020a03241d032a12040e0a0c1d06090d05100c0e10142107031119120905010528061802091908150606130303 52
    0x140000119000a4080d04d52206000c500b0496154810000b203044030b81000504004190040e002080d1024801150001c01888003448950403120b4140c00d01c00c0700c5207040e20003201685280001241c40d10102e51000b05041001c000b22110140d0f115205020601c02c50b2250400201340d100c031515a070305580c6c09007246055035201d050a9070603208014003042c1c240c112030b0070322039034035485400168407017410011031134903c9109027410240e10700c0241c40c03445007070401c4c0d600f5145005a10905480745009002c18803004041c40740c01e41d80c03c6d20360990b00381d207401c00b50002015030b824040c1003042000304001e200307a100311701108040095040c0c40c10712505403554072000050903208030060120b41c00e100520403503008034000c0900c1c0e14030125100c043ca82c00341c1c40480640c2c0c82c501c03070540044c00300c0905000059131b0f90018841404003c0c0074080000c4003036900000b500f1a500140c0095011242040410380b5100015401c098200c580605101e04c0460041000702c25000090030440d5001e6101c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 423127832 1250 423126582 423126589
    0xe010204060c1e0c0f05030f010905060c070515010303031d1f020c1f0203160215040605090c030d0809120f092701080d030f05040c141203040b181e040902 68
    0x1d00c240c03644005014221381c3d40b40d44c00888580c450242c544240280c021080078003030144500182581d1140c06000c9541c1c4000801034141c1050100b81e84500850380000d24031515444628041d511903100007683c40780f0a2960002d00075a0290120300e94070030301718800e01c0d040b22020b2400400c1c1418000da42e40440304015030404402c000f003d05000312181c0010300c0580340b5005540701e90800320f525400c1011481040f039507040c0106aa103081651000442e0102c0c600d500801c1e40009020101c510903024038021902d00864440c520703002617101c0d400e00180b114103000b0b0a0a034100101442d090030043c04804140744141e1003c00e00c50f4211a2920f620b8602180408040d42e1482c1d001005941c1d6461001e030302c0300c01100c11000003e10704030b100c8030a201184112409950007944040c0501d08024844c02c030000e1100e04203a018038220800348400300208010005002200d4401d51582d08042002910a08066085120783c134000c0e80761380d000c405000300401c10700017103030003045100050000c0b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 423129082 1250 423127832 423127883
    0x4020d0f06080309010e03120301030b0406020903061303030501060c21020a051b0103050f01080309040b0f040e160509190203070c02040609020306010e03072105030c0d02100e010204060c 82
    0x4805030141000000240c4030000300241005800a0703c1e800900700c040410140c0b1030701002c000400004061006002043c0000c14117a445845054010300d0b001e2404000380c60180211269040c198031851490201640350150318010030490500340c403034503015603580c5004091244030003071103092040781c443c403a4402c20190700c540b6007210903101d40300c0c480006c1c0303c0c005d00c80e441e845021900301400319400ca15103603a00f6048905040240d03040c071801008100151602040032a0b10070742c510202c1450386d881d442402c0301143c9a2000389031f040c00c6640c0415a5440980c07005100381d480d1010011441c0e2340b0071003035503241d681d5100107a43c1d0781c84080a035145c813010700c0e01039005403410002280c1005030768015805801d090301c0c1d0401c444444410541e0b244502d020344a45040420340000181105100b022141841a000c0c1c0b41041000e000d010b1500c0000c1ca0f00d170300107a1210b10700d142100c003544134011204418200952415040aa025008095603900149003010b981101034004101605 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 423130332 1250 423129082 423129101
    0x30702031818010303020f0c09060f0d02210304030212010504020f090403050408010504080904050901111c06030213060512070311010e1201050a0e0c060702090114030f0102030a1d010e070504020d 86
    0x9002c03800c2d612824001c1d950107800180040c9071055801500880c6464801c003442204024542d102e00403040d010b01420032180941241c1040942d1075034269010041e5a822031200007070300440d1a60320307600400c03028040c00b054880481e49031030144400742c1c0303440349600c042c0308095858031000d0300d0303a11b022901446541d00c00b103195480c0c10148030411809000502c20030404a40521154640d429503a00f210303101c034041105104108000381c10b4007c920800c05513421903401c0003070a560b0781e40100e01d001c0b04001040d0101e40d5a40c2041c4081c0c84c0010000c120b4039620030003011070314215074512034480300d40550981400100001c003c00d036940e100c21281d6058a0704000d0119003081404207000d8490955a5621402407035042070301130400c0c1e005e480007035400800030b0000f03900c0c1012007202c0792881c0403503a0309400340e83c2802031001404d0000b117007d00301c50140010740c810703140c4051020b4003003210285256410001000c002c05d100064200c143d40c01220300507a01e041e04103810000b00340418 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 423131582 1250 423130332 423130369
    0x13050405070b0d1a0108090616120e06010302010314090c01030b1c03080f0604140a0f02040305030c160e010803072d03020f0d050901120903020307020904150609020307020318 77
    0x80d00001d12007403904440d0900a0071382c00e08001289402c01951540d00854202c1e102e940301000041e003d442c400008200c1c4107480c00e20910314224010000c040d9002c001400403658490340040086581c0362290154040d2840074906040c09d0941c00d107070b01d402c4246000f50415448020070755680c2d0b82c44054150304607000020145003440c502e00607018060232109000b443d6104000500d080c1001c3c091441d1901032410100c401359078000c942e0f8010b005d90081c9102d801d600744030110005408100501264001038024009840022240401c41946800c10404a807145004010030000003040d1000d495210740741c2d01c20020001c1c0d44645802c00000da44c819a041501c451040c0364020400940007070705002902c1c0f28040c03210381030340e40c3e201c3ea040341350018068041648000040c1d6001483d054864410360385040b07580d40000328224001c3c1d509581080c031880e90f880000d0b00c58811240101802030045d4114540810046d443c2e01910740c000c00100c0310b21100420603601d11051001564245 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 423132832 1250 423131582 423131587
    0x150604061d0601210504140c0f041d031c0e0c0603040809010314010906030203151303121b030606030e010c020717190b060a0819080c01022a190213050405070b 70
    0x203c0c8248045c01050302d0a40741c1c5419000089070b503c40c0030481c985007140c0500480c11501c030a600b40b100600034040340d4a084088034240384407801040c0020188500391054400c01d0302d1700000c4100803038080012b41c0d6030983c0008101112500d0301c0e030589501c1500120702c039845400b400300690150041400e141c07401e00c2004004120b085072644650141c0340290100d41d8280074040900840d44000d845c6a84250100106000000d00c01e04860854000341c01006c00d00c1100390746e0400480c8084d180c1031003c00e403960700510916906200301d0352040d0103007000340004003070a10b019407244440e008060000b01140d5032411019002c103e20b0004400b0a255024446101e05140d4907182050354080d22816040c1000545100c0c0000c9a07606440c0c050f803928031074040ca0351507020319845101e44080654007400f409100100341c40c81c1c01d140302c3d00000001480c0c8402e08081d82030098002600e02d805080c28420f00140c0c41e040742032419044905030004046e103c60038441e1070101598090300c00d28000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 423134082 1250 423132832 423132887
    0x21608030702100b030c101403130b0c12150103140a06171506010c060e011a031002040608190209151c0603050c041d0708150604061d0601 61
    0x110000c612641141d402d5400c00a00d03081d0300400c0c0d800d6166100d5256004c03000c484803d1901008250791104c5904100d01d01009519804c0540c1d00200c4502844e0100b1a14000c2401449810103602001840c8214542904034816003c02200030303000506008036012040550f03406a0f01c180105040d64501c9800c629048940c08042c1c00d942c01585640801c1d00d1a09072104800228004d001451020003075043d13844400459880301049020380e035031a2206030003280e021003071207104540d46840600e184082ca1400038503140030141c6d0398003880320b8810041000060b6005210b15005022460100300070b640c90000c1202a0185014030759225800b680c01d0313407001c42140d00078422031321000908042e282002d000390040351024400640980c1225090b0341c1e15140c00c2c4d204101b032168403d00301402e07420b0421050f02d030802941100340b2079441040c82c00d00307801c42d1030170f9194442ca0480d4140b02c81402c1a00b485207400301207070000007520744c1c40c0100302968042e20324003640030802c41c3c40d085070820 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 423135332 1250 423134082 423134093
    0xf030a05011a0303040605070f060f0e010504030f05030112020d020303071209080c030d0503060d05070f0815060a0302150a110a08120604050402090c070206040909052d071403010216 80
    0x3140d0b0980e10740303480c240c158035401c020003a102103410a0b1222820603a030f03900d0365219024605011502140c0e207600740360401c0640e105405010303102e000001100e29040c41c000c0d2001d4858031451080c85414001003004a0078444802d4000e641a00d4020118000d440480c1c6103004c0c03420014491403031641c9000e0300b540d001e103400b021149050221900540042c041c180c0718413071080c080c00004c0c0c04100094950030705d41c901c8900e8a1042e02102d82441e070f60310045c0c4030b9070820707000a5030b1074200b21140c00305510b0313015070380703400050480701015400d00d10b60010b104280c000d081c0f2070080101103407071003c040c0039a40a551020404082d5011048070f4501400036501100c0300000980b00c1c40702081840c10944030b003611455000d8082c08040c1c0303458010319429000000100d038007110401001c40c10441318003480c2c089500c584000e201c001042c0000048560320004d40d50b002d141218112000140000b174244202c442401a0211080120b0042400780c81500404c1ca000107001c2d564404201 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 423136582 1250 423135332 423135341
    0x101b0503040e10170d0e060d050c04140301060e04171209030d0c08101a09030327030a0f020f040b030d080a0c050a0903021315030803070f050702031009020f030a0501 73
    0x1103400c80101d01d02034031607102d040f941314803d08586040d4840352102d01c040380600c814401582d0005d001900345040070740300c10103485040b50340c103402550120341000031803403030070750500051720440007030044900303003003030088668402400904100040d8210041404c161000c5a4100c00f0b889409802442c24101d0581e8035400b04402c03642e43e500e41549200d04501c242c2805002d9209614841000c0745070000c02245801c1d408420b09060004020f201d8040c0c0e401c100800c3c4489030f20b1103d412105039900d040c080d02030708001d040c0c0240c208400c254006075141e6121400a80c0c1102e4a00d10544e902e00494001e0580581c55905849520078501c0072581000080e03201c1d40e807041c0240711450102c0070488050103803a00410202d808a64107100525100784842441140c001c00082d500b92200800001d80202d540140d5685c0c5001007400755580c0e101181d1901e04402e800e0051a1410383d5011950f21064031010b039010315510031400d4119902d441c0c101400540050840e1040041c50503d1402003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 423137832 1250 423136582 423136591
    0x90a05031902090a020327030c03040e0a1803080c1309050106030f051f0308071403130617010303080105091308030709080106080607050a120f020f04140906101b0503040e 75
    0x780c0f04080020520801d90080341e11402c40302ca000001000c807902c01d1400c514500506103000c0c0014800480c07164800c0029100800341c1d084803042906041030080111043c504002d058102a0032401e00400c2e08103061541041d80d00e002d996807103c5a1402d03080003541500012101401c0c000000f4206a164200f00300030b03000003104221f2915900c00d514880c2008030080c1c014110000801c00204080a014054a03801403040c01107400c02c0014280c1198005807100360402290b103801e0240a90141c5484a003c10011b0744892950541c2c8014154010501c681d61041d0300758070000303070500c07541c4100c00c3c2c03111740c010070701a264100b018001c0c14413512401050503542ca402000905924001455401071107191542e03031811520030340032035042039a4510524966110700310f916201e4450b10044c440f180d164905a615141854654080107070b641800b24401e00851003031068560f84c003152103482c13841034203040c000480003c1604007006003514010305980008240091210b00306d2000da0f104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 423139082 1250 423137832 423137839
    0x12090b060906090415020f07050a1212060b0306063001080c04050f040b0402032e0f0207051015050415170d020604060b0109180c110109030c08090a05031902 69
    0xe42d80c0205100365448100c0700508140801d1400c05003c40c0ea40c0d006000407182c420020f0f00d40781903070311a80d240c0100040c0c21202400010304040030503038007400b204545624894244019813404401e008140405000d15101e40e0000409808103d0742c161400c85000342a4141d454801140f0580e420a403c01d10810b1701c40c0c011051744c00304915091040b544035242007408014503450710340b04c091070140010800c17a0180700c0e0744000c0c3e160105000c1c01d046000412024402c55000545905050340c45804d61150303264010f020042c00664003190000f04c0010003000004c0084000c0004206a62160700454000c0c0c40e266052108108020761a0150380011407400d0079960451100780d6a2003020b403980300160050004500040c206401081d00c1a805140281c080f6440700d0582c0c0180c0468a401291300d991800010686a000041c030030042810700001c0051180d50b46002d8048803808400030408200000d1038501c543e10007101501400d009421941002c900d0400858090514070341a4070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 423140332 1250 423139082 423139099
    0xb09060a0e010b031b06280215010b22050d060b03060f01300b090c0f011110020309030403050312010602062d0406110307031a2e12090b06 61
    0x51107814010103001c4680030f4024a1800000c098001181324040b6556501010070041e11ba40e01e80c03440080c006400d1511010303000c8041400c1d001c0d19000c00500561440e2035480010030030301c81e41406882d0900100880c41c81c400300c201d034010b1484a42c6802c519404007150141e0343c144031071903000340d00d002c0c410380c200e545a0f00c0d2000140d0303841c0703030911504030178030300210301c0c20010740b01c1e6401c0d00c041000614151000c2c40302540c85529850040f1407100711580709c40300d40c50301c51502c0403035035602c0002030030140d001c00031b8085a01d4880a4001003005600d400002040c4042820002c6400135070708401940d031201d4001600074101d4000307105d580300510030b00b00030920421055000001e6203c118016103003001d500d00114450741c3d4001c1040e03c6039542d400000055441d944019841382405aa0024030b034203201b01c03081d4101002c03031041070242100c04218981401d50350b540080444030044e091201044108007201c5040303185a0740603101e400c165001d0200030103a071016001c3d032021581c000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 423141582 1250 423140332 423140351
    0x4030305090420070b1e060d0303021317010c0c15020c0f0f0f0d050a050a0c240209010201110909010306111e030a0b060a0807030f0207020a0b040801050f09120306010c0b09060a 78
    0x2036212030600c2d282e980d06c0c1000c002c240b442c50188805105148241000b600b424010701820781c20340990384c00880781000c007001e040d031064000c0c455846d0708180c500b03045410620703035115021064107100c0e16502469000454802da010b040003403400c5a51200f0840381c016511200302c90302c8106a0403200c0d90b0b44070703500042e6a43d034040c00c140c0740d411015544190900c07411139421501c140140350244d1310441c00442c28484004194030070b500940f86c064000d80d40c2c8081c0c4000a08480d14042018004038003481b1a41c0d00703030346031002241140c0e041200031640d0101645140750520035031000c4480c101c4c482420020322000e00380654440c100007042005480c0011003800290b2084072580c0c000640a140081c50050003540030003d01610001c0060030020f1943c040703800710440b60406201c45401017000c00001001740a95584400d10641240071410011552a951407240711141d6005c0c01c00301c0007824a034800c004411103980c1084c01c250140c10703c80e8811ba1208400d03105080820309001200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 423142832 1250 423141582 423141601
    0x2030105090f10050a0b130b03060603031c091a0403171015030c0e0303041e120c03080901051303030c021003020a05040902030c0d1410090b010504030305090420070b 73
    0x4401482100b01911540480074038500040c400100385441140ea80d4074044001d45407030750f120400402c0d965000030b00c05603107007c01d4507200008140c2031080c5c2c020003c0104280140880c0b82c0e00040f140400700c1c0d0220b02d441e081078084694410403682c906502c00f04020b041c0d00600080f02520b0041e04250b480e1a40114800c07034010314060011601e4030f202d03049845600c250b004000f080414604100c4034501180080e0541e40954030901aa0300596040700e440ca400c0024800100712410925013444451f5072428603c0e101840041c06004001c034a0140c3c60b406141140c503840079070490020210385a1070054007585201d00183d0065003410860000d49019208542c0d2026181d00c0711428180f92560540103075200a014a0252505001c920b06445060280140b0401c01c42c109080c10b2402d400c0c00704441149909c01e40010742000418109640c0002c111003d5036090b00d480741e0385400c00000f0501500c03070b40d43e032400d102800c51281c6948444120192003d07a01c2103946400310746991005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 423144082 1250 423142832 423142843
    0x160b10120b0406060f180506060c0c01140424020c01181505041502011b020a0f0b06010c1202030a2015040c080607030519090c06030f02070f08070203010509 69
    0x40e8000c400e503044415012480d030360801540b040c403a0301c000c1005034a4240121020105a010040e0010002450301002400340242588074100390303030682c20228a612103650360303590355800718140301943c0d8002c0051110b00048070040c010458807020b0242c080280d6801d8001c420032194010301036610f142016601c100300341c80700c0d9035015007800846c0741416540b0202904010302c10086c4403041200140d23032060250355030b0042d086600000f411b04c1c045075401c00380d030345100c05030821500702c00140c1e0300203010f4540f200d9a0940141c074141959a54a0058852ba0144030024042c02c0d0f450f072101c107000f6030000051099001c03958840c130aa100442c2401489455115022140d812075a06031582580302c24882d40e0050040b0122990703155146005410808240c2c0ca07500000d444108000194a0040c05000b00503003514041080315900d440b04294000c482c06507000b0981c07900e07162011206990145c45070a50040450b800900c2549030501c125440784804034040d508102c006018124040392 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 423145332 1250 423144082 423144089
    0x41e120e01020a0f02130e0a050303011403062e1e05040f060506040504050703020f040801050105090f0c0a18081f0b03030702030703080703092102010210063206160b10 74
    0x132111800d00d4142d08202200380c41c0c011501c0c103e656454091080c640c10000140820701440146949506100c510120103418105040c06580b10f00e042c00744070b40780702d600386125140e2100d62480545400460324243d440315030001c5074801141c02d013208000318881c01c1d44100c0d6401c41d003c00450342035180c06400e0b561540305081d03201d00e05100400080c241a000701340d00c003049207001803500386101c002043c650041d070480550b903075681c0c006214600b089a481500101b981d00074546601d03048000301018407910307105804100c1d12820000d60349081c581110054864001075a40000424458032032030845802c6404080f41442c09800050070f012048506081e0058054043c0302d08503120124070368010344003103042000811000500801c004280c0d0000300908290384e0154099000083c503003925035240b080c200d40b030101c0801216030515041244594942c003198016494207044880f580d02d040c040d07036040800054081e400175403800407203000c548035080d084007907201da02c5c072264a400b1502 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 423146582 1250 423145332 423145343
    0x15080d0903030305100504292b050f1e0111040806040201231314090609150a0f0f05100302030415050c0c070b03061201090c0e041e120e01020a 63
    0x300c080c40480c0c825045994405140441002c07842e60340c0700420101c0b02040c81640d103050f20059801040c0180c1020794002d2903045800303100c1802154502a4000000444d1403034022681201d4010041e061182030f14044101c0d003a166204920161048010f4501d1030040d203a5203040d83d0310f0884100341c02500c05690341c400040116a0f50b5500544560034201010000214420040600d1000840092400781d1401811030885d03840e02d04122904400807072041d110700355841c1008016100c840707407035500c06050070464407104804008640c2e0754a140d040341c095800540c0f400f14881840031000380850b4810760b03018810418000b4200c00700e000c01d40f070080081d0820121001c88200e15007056420982c10403507a4a8030754100d0390320f442c000c0381d5031124804510100800443e0325100c14007011504201e0024460008242d880f841110310600030f0909080884010074140042010307031031030071015681844005030307403070a0081540c200c1c1c1410341c00056440981c041654070205003801c80c0359210303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 423147832 1250 423146582 423146597
    0x70807050607081911010e0c2112090432070504060e01050f19030903090b0c0303040b071b030504050310141603020d0c1101060503030325091815080d 66
    0x90112034084c4014008001013010f06100100b003a9000e100e210f480030329040040050340692003c1c4001594000b02c1000c0410000707420313400b12a00450750b1801c02034000e290340e5070b8501203000240180604843e4242c01c45900c0040e2401c0f03d007580340a0203180e1034a85451140d954220200c2d2584518018040083c8400c89400c3c0d0702e50042020344060f61070111080d040c512610301901e01c41008404070b00c0080c2c0c6800800c0203260b0060808070181942880c0da5290511917000142d03030b0f00c0007034002800c0b180e403400002c4c00c05105100c3d03944004141a00144c0c0140c8a040040603500540aa1482400b0748007003e00342d500d4901c120307207180b6400310300c0c0399455440280c0d00d0704d150b0314907400d0400e1540812510310050324038070846c8800301064444072184500c1020f010300f120700c9600304030f00950040080c0302c901da288a0500d0b20603405400012000223261400f1505000d03140d211417036920000c0c26540001c00350360000705d5801150844240200d42e03c0c402c10f1b0740da0050b6100180481c504c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 423149082 1250 423147832 423147847
    0x2c0d02301b030a031b0605070e0909030a02030703080a020c0a030c151a10090806010f030c0909080403170c060f061008042103060510030b03060901020f090d030c06090507080705060708 81
    0x50791703d030300310500340040340c01140b50941c481d1019203004a5a1800058001e0f140209902c2c1000b02560042c10f0b0000440c10031507125006980e03445020400340a001c0361200140b0000703003540445007035101000a90f01400305500d0042e000381c09801046074800d0411051141c01103080c8200d001d5407036441c9110000c0300c18032050001c80c1780c058441c007040015811006c6107128003045034a008000342c004141c070f85881c506058000610907009950702c1d50600e840c0030040780040c002e60b01942d400001c0c86c0c100080c0f10180090902c80c1c000480c41c03d024010400590900501c1000c1c440c0c03205403040d4400d5803145104942c50b9604640c02000c11040382d91440780050017400c0145000150300700011410780b2000001c103800000c0b032100e030000b6103401045686080034042c058001891034002d5060035100045000e01d4011120250b004035000030f9004103240c42a401c0104085c1c0000b030401144105050140e10741e5864020390180d403140d080e000803981040000c0380d2001c2d030010720f00b500b400ea0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 423150332 1250 423149082 423149087
    0xd08060603240909070f170606060f120a06030b13050d08070302040f0314012a0507080d050f04110621130218072c0d02301b030a03 58
    0xa84a02d0342e040b04401c2d0300c031a10b4840807401c501842c4c0481c000c11034140342043c0b51202c00259003007000301807090240c500d241c2e04002201900045c04891680c1c580c04500191a050300810207003a100c1c0c9040705c148141c4e0300350740c2d10450540e80544d45400740359070341000042214685900041c015440406c1041050344514030329904035405140151034244d070742060855549440d04192443e01410000441d003490912550110314076180c040244482d00c00c1b40030040d00300b0f0444800500600141c410f042094000480d203142196150420441c10b2820100c2c0d0100412a0b04a510500155800e015850031500303680c0011600060601d6141d504000c1c00c40004000d00094405640715020f4401651072048500d0038040800c101801c40c5021000141909807100d0700c0c444c41c650401840c134800308001d510034410041503c1001040080f440810001c42c000b014400c034042c02c0b0340b0030901031500d038003c40e02800b0b0010210340404c001290540750a950010000b58182d103c1c403440800a0b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 423151582 1250 423150332 423150361
    0x50105030a050c09030327030c101803060501060206060f01020309060f16060207080d05010e103c03051506011b0302030d0f0b041503170c100609020703020d08060603 73
    0x2c490610303e4105544840030901e50740045c2d0f19040220300c83d48040b020129840141102020100c004007003000d0301d0000306188802c0034021a0030084102d400c0070341c0d417008056000086900404c00c00480da52008000d490348400d071403451003101ca01e030715209250b00c0002900d00e0103200070700782c80c41e141c0362511100c20350b0300c81c2002d07407080a40d40c2c1d41200403a56030b1029004c518018a10076079074007000c41c0d135141241c4050f0040c0020781d01070f0301880010b005a07a10042621511441c0d441a480307049009048445440a42070145034003910041041c0404100d0000300d91040c011540f215080c20b4240c00864005c86540d40040c101050181c02445400c03c6080014080c0c01035900e0404c40c1c0c20b10606507480d03464800449915224448001d050611400c01091440304d14070b021070b400c542d583c030203d00300c1c250400c00307020001c10440d40c40b10f000d0000340c000020007001007158a42c0e800350200a50042c0005501502552a00012040c01406018441d40700100798a246958501c0040e9001c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 423152832 1250 423151582 423151591
    0xc040608070501270605030403110102030f0f04051507020706021e0a06020f0d020a0e0a1413051e0a050405070609060c02010f090306020d0b03190807140f0303010e070f09050105030a05 81
    0x40442031004004d045040c40030320080c00003036996507070360320301400d01800c2810621401c0c00c150b8410010840c03c0d95005400c039070000180c0a40010766150b038244903141160700343c494803c00b000c035400e0003116500004d24800f00c0703c1940070f842d0160044241c000c3c1d508408807501c2207940040c2034500010b11650300603c1c1c40203608c60031a0509400050720800c0b13030007074105680425081ca170011502d103401d60828000300302840740340310181e21890200d041c0c2a010303500314005030745540200b141003000340705000140c8440c10000da2207240c81d1559101800f001c0c3c50994403801480d00200d00c2d94440e0100b01d0907580f05841d4841000416401110f184040c1021070b003c110610305e0203c0060514001007004244021001c070345051070508160406100d605081d140c208a60a5a000500c080041e541d82d0764100c100e5100607500d0803412801d290000c10081c455000000010a00c500c40300750f1a4013134200d550701d4030341143c0c04034016580c200310b074000c8901051060001032002c00c0281c003c4c5900 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 423154082 1250 423152832 423152867
    0x90309090c0a030204170c01300f0e0d0309061a0303030c0f0d020403060209040b010329181306060e06090a051503100c020c1921020a060e030c040608070501 69
    0x14203984050307180c0c110221b40c014075400d400100344e0401799a40510902d0104410681008a880740c0016015440d0807038002c1c92410754442081070004812079000c50544403030390b0f050310030345070b0f01c000000c0050600c1c0700101d81151070110840121021070604550001000e0300a500d10346454031141030a40045035500c0c58003100f00050101c906550000d08011442414096215207114007008151446690920704262030034000d8103407a030070700341044402003489284c0c0107148495400b01315803840080b64010501c1c8403c0501c01c031080900d448001c1d241c0110010401c06440702020070700303408181c0740c141e80600507101003400b8288a42c802034108096480c103081012081002c20b00304802200c5035400aa0f0710b1400c1e042054061200c29580c160840e0703403c01104d036007240e10f89011064000d208100040817015070114982c086026900c43d0010440d20b001c0b0380e203d1004009060700020180640911220a071507402e090080c0d006a5070340001034483c0700d080c0001100c405068039546d400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 423155332 1250 423154082 423154087
    0x3040302030403150f110a1709030306060d060302150717030f0c03070309120908010e0f0a0f0c170106240804060c140d0203010603051806010338040308090309090c0a0302 75
    0x1501c02c086c1c4109000c1c161105000c50303d03802d9a81000c1e262880240340321491003c690100628203501008a0f544907404176040303600c0b061680301c00f40c028a9980c0000750805980f9070175002e045403c401901c9440d11500b07140c008000d1580301e00c0031701c2c04190780100444051001141e103d0090201640c0d003c101c42c64005034000880d124010100c1103680050040f40c0d5074a01400140c0081c042d010350342c440f81000f000100750340c2000a43e180140030014111840111030281000300c541002d5001b0412000c036288000302c40520a402004240701b0351030103142c62000022909089101c44c03c0003041510740303c002d80d4854441c10003030070242d050380c420010300809100802d804000548040d184008005840b581066000313011200007030100101a03c425100381c1806ca000151141540d03846080d000184011043c0240704883d0208100800b80c6051890700c0d6600b00e90152612682c080c0d920301d1226207401422503100d220b640101a00450420001030039007680400034603950003c2c0c81d0051 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 423156582 1250 423155332 423155351
    0xa0305090d110607060c09050123071406010602010c17010506090922030203040e100b0301060e04060b0a080f0a0b03100b030c0405040f0b0f25020a020a080d03060b0304030203040315 80
    0x11a55030103182c3c11030b000740c1d80311b80c1c0d400c010307a101c189000500317802e00f4040d00398140200070503443c000d1010410f10a50001a4034810401c4074828405e2550aa0741121920b584906002c0c0c00f0b010052021800907e4420350754400c079030b09580d070314104d80c400f03481c50307181400d000103104084000604022642100c01d40111070320b06048010062a402076000c0c5403600e05103803802d6280f6001815540002c582d0074414040081e03000100c1b41151014181680e101101201040103800c170307a4004001c1c041c001c42d21944103904045114860700f1034584900c12036440b0b080c2e0350300700d4003402d10840d05544900c0303203965400119401201c1ea03800040c22202c4c98901d0344005401e944048404036110440d50070f58408101c5054000768011116220515407450a404540300c0b00000503845140442c4240c00100313914000c4c03107803000301d6401030240345415031074064a0759107045401c0a0000280b804500043c800c901d030040d280513079890f40c0911705e42881d603110030041c120004189403815a46020742c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 423157832 1250 423156582 423156589
    0x10623030711071a0901050a02070509040609062a0c03170a0e0d02060705120c0903100203090d260402120706090321090e2d15030a0305090d11 63
    0x118818a071903500c081600142c6031402d0308181403a4007201c01e00300c402c101d0303040b00c01c1074800f900c038608070071310b0700d29200c01000408a250000d5507000fa5041040700081c00140300359900300081141c0100014020b10380c1500c0d11000c03042071102207580c0c00d03440305031441c4114460030a03046140c0c028644254101d0006642d100c80480c180c40c140381c000e82d02c02174105201c01c18010902d002c10680080c03d1540b8025030050310522a001e40410040c4035100040d00202684060381c89140000c0c04458000203d1004039000b5030041c1c664480501c01d80c5030082d41c451098404102d000e01028100384000c1d0310900c48201030b48044d00807039000c40300c055080b26507101044608003e09180d80c6103102d051450400c031241300c8001007259400d02052602442080d04a003000048540000000e044e0341c0d10702d000502c51031402d640c001112412103019140040340c881e01c05025180442038001e070b01442204055440031404001408240188400035061820710040c501c100cfc002c10702001c041e01c411002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 423159082 1250 423157832 423157837
    0xa030f050c040e0106050a08040816050a030c060b0d084501030606030603020907080405010f091119030b0c070c03080d05100e06061c020405090702150a02030c03010623 74
    0x51440c03079000403404202c1c1c48001c046250040410b0304003240307858104100108100001000505175640c005001151661014483e281560308042642c2800000d407030b0003804d521500b4000d690007810881c1460580c50010300c260250b590180003149801d903510078450304498403d524410303494030851540d03040c1107018054032280305001461121800d48000240455010382c01c0b40081514164042c401070311081b0810360010b4160800b00c80300c0d03aa520340a4090208950b42c140e00c1c03414a210082004249040041c81c20b20480d602c0c0401c2c4131502800800c3d404510004c2d22041110707001c1801001ca05004111a60195000307244540d140d4940c20080d070b06c000e0004020954640400c824149031042c1300001d001c8088e01c54506007402c81c0001c4143c0940040303200880c6449041008801c8194119002032030b010f080801c052400f250007a4490800d50f40184001e04280001581d001c01482120303c02d40ca030344201c0f400d40e420054101c5086594044401c5d42d403061080034280e040401c0d02 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 423160332 1250 423159082 423159091
    0x1515080a03030e070b09040207020301290102071e0e10030209040308090610050609130615110f0f0a0308060612010b04060e1801030f1707030c06061401080c0a030f05 73
    0x24103102080c1c1c9030040807102d081d00112041c1e0000c030000e1000302440300031100c0c4a2422200581c6802460001030300610003400110701c01c540b00c0c4c80a1007001c0c10035034070040c014026001d50741e22655420301c1d11544102c00c80d400301000c0b5442400d00c4201002400950011000301604071210384903401308151160a803030a902203180d42081121541c82009030035480400b8104c110429031400c0b0110700303d4060140006d216850046030b40205601c203078014001480030302014020184103d2026000c400c0803030301850300740a0010600c448060004054580b407001c00020500b596003520222500800500040d80c0403808216814059911401080c00303000030041d4141d0b25403500101400314544050103600030800d0a141d4a0070f103490211960442e904107103c420340d01e105182001c50020070750701f500c41000010540a0601d54801e20102c0101d2281e4410818a5150844030b201c00c1400c060984c0020004c000061032800000d01524040029040104008200c00c22880c10741c2d40494 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 423161582 1250 423160332 423160349
    0x150a12020310031707032309041b0e010c0b0109051b0a111011180303190306050a0e040203030901200a08462f16050d1515 54
    0x80c42401032029444d03d5842c0b0540c4403074070a16050403964090020a031411242140307208207204400001c05081c01c54112100041c030401422921603c0c0ca030605000d41c10400c0000c4443c125002e40b540a0441c0c400341c40d07041010b40036613130f20b0500444050240203180d002208814400d003c02c21021101070f04112529840e0761a005124141d03083c50010140d00c1e0032022414015610341da01c04c2ca0080f03c416001005c020681d00880c100460314505c80d4402c4054040c450052161075198158050000d4510031529551056079840081804642c01e44020358950010080503840750f0240006c1500107003412041480c407428040814100102d0305415198044001103501c2c034041c00700c80c40712001e111403c1442c80840303055a50500c406030500000c0c820020301c4030720800b0900070000c110381080c10504c8a10038000c40000d600f41c0030442e43c1600d10510460f443c2c0d12646082c000010b042e503502034110001c0d044640c654103500c1c40c03150703800c003081d17907580e0745540720134203110f05d4030001c0c20145 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 423162832 1250 423161582 423161611
    0x70302011e0b0a09050405120f031501050307051204053c07050a0e061f0e04050901020301120b040f1e060e0106080c130f0501080a030908012a052206030f02040302150a120203 77
    0x2201c1662f02081d19002890401c00208104520250408e0550b1200c0701d030620001d450743c1d180e18115180043d58181d04000500c0c0780707407001307210403c445d0362049405206140102c403200e15034003560341c00c010b0040b158442c1455606010318562890044e80c070000c014401c070344246860700c80005072010420b040d00000c0f41a0701001d03142c00c080c021181c218007a58001c51440d854204184800b01035800c0086c00080e44c10041020b104c6076182480003650070945110084900303802c81c00c00c541102008880b070b582802006810210181b00310011926404050021142310300204009940700102c0d12445654500e0030904245441c480c0c14064400030340102034102160030064105000303503002010341d80c1040035160700950512010181c0078160649800307041c036004003e64440c090950351240b0001e40780d980000304901c0103015000c0754180d46041003000b202107a05010f910650101039000a070700d240c1c1400c6040d84100606907104186086843c480f00d0806010580e0b10a541a41c10355021 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 423164082 1250 423162832 423162841
    0x1d210601050a050a0e0103030f140a0c11030303100b13090f09300e060d23180601120507030803070903060605010302120a05100b070302011e0b0a09050405120f03 71
    0x242d00007001c0d040031a02c5400440c640f8041030100b42c0140002810404469000c407810760250303261315048146418266240c00b00500e00a1140340ca9403025910703d42e00c42c40081040c20080100d0340540c800d090042c0b991405c1c1800c85c0e5060303220380d0100c0c0115240190000d00ca110521a07850385070750008000c01d0801182c00d0204a0780010024400b07103000c07902d05000c00c80060b040940c1040300a0030000ca81092000c00a5140e0056071800c4200b1800c00d2400c0c00e5030020003c131010140341d491031b1a4100d880d841c40d103201e01c00d44c1f858114003d40c01413006002804428a40c000303d00d20400031030340310640b00d0b600c04829400c2502d0642c00b103907203290240308024041c082e601c0940402c0c60114100461302848104420014000320512503880011500b070181505502b0050421070301100c0d91100245070007030082158650300030b0384094280400406500354011218800d10003007003520400d00b40041c0d14003c20001c4c0040781d40d4410b905651041c0070601300580380b000b840c403999540700e140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 423165332 1250 423164082 423164089
    0x5010c02032d01092609060d0b010909060801050711011a1c05010e07061b12080a0902060c0d090f0b0f030919060903260a0c0210050f0103030207060f1d21060105 71
    0x8105c0c61401c06607200b40302c00000c40e11000165111022030001c046150450000160b41650084d000700081c58209040400c0c600300542006009584941c1e4011340070781d034507012a080700c0321480c440c10054030110a00c001c1d881c0540b5161485070885841d010f0007074081c5c0d9803078211046042032090320f8008540400c10f80b600140200b1910941c0902050300b02010340c1d5003c9805d401040070b0301400f0b01c03070000c101071101d40d0f0b00c504903003603000c1d14541e82c5211510310165a140080c003001c00142c1302c002d010410080301c580c00c03000c03100c46a40e004d0802c0a018581480740d04001c0480140c0e11444689003a0080e5598240c1c004a0043c02d0001b92494181801440b04501c507080c001c903c44080c0002400c0c44080c41a1a070001ca02440060081c5402500301d01b04000c00024907007441c1002c0501c400da101100d06581260700c030760220343c01107a07070b61020f40d510000f5640c030b0001b04041c000755400c0d00300188030640300030b00001c140166141c850014070882503c12000c0c420300d9031002005015906 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 423166582 1250 423165332 423165383
    0x10020408150a09050607081504090b0a0b0d0f030806011209030906090b03160e0111120c010c0804030203120601030e0f1006091505060c070f080a050705010c02032d0109 74
    0x31101c42c420b100120301d544600d5590800648800c041041a00c0040d440342080d6104880ca00710080061103080c0c103605010012031019034007542c1c41e501c0c01904020b2860000f0b05000860b6121040c40030382c8026072820340da0140003c0915042c414149040043c04400d4420649002c0c440d894405109041000080c030103d5030742c001c0019a40100b0038040c4204080300d0107142c3c2140d629080e81c0701d08040300103c40d085111410071103184140c044954444031444080c0c4203508007440200080d000009c002c48803030500303540c054056001005803401d450005000a9408541818041111b0780000c2c120341c41c00a1a42d4643d41035008480e111070b812046000c2c64004180c9183c09100c0b0529010343c2992000c030070309c00c1c5031107204000707617820040105202000c0285032045040820b00d542e400c0590704c0d240c04101c1140c4500038010b02181660199030380b01c3c1d5041c0c001d0000c2150380028542c901180c8800500d00b55005070b542e1358519100c2090103072640c100d03c918045c1c0c8054042c01000001d22 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 423167832 1250 423166582 423166591
    0x201110628020306011d1513140a0f090f021209030c0c0f01090b031b04180f02040608060d32011401080d1b08070b010e060a030809060a021002040815 66
    0x2500400c00d006640c1c1e40030628001d08854045050360302d1207040001001c44007d220210102840031032110721080c00e035440e42c0101c036072803440035000130958020060b0701013645c0104608030600035800e120404040d0b124034400035401100501c0c01038042e0407002c00e4482103513807a2003030348001106040502c05001a0200440680d6882c07096050480060140410b034002c046460b01c02000103141d012000b041da916440c50440403aa0302c54071141582c808840400c0700400c00c1d0b04003070855006004a1003140c044509540d03030104291201d20810036480314003601559048000c9009803150500e10300e048030301c1a0303140000c84801d02e41c84003103400d40c0d0203601040d50064014004001c001c03000700d0601000d6000c0c0c034006c2003c0e00310800131902c4910400b1302802c0340401042542c04c001011001c0d60594421510000d02955003100f0806803003020300000340703003075000e112440603410510058a07440d4583d0058409205110044c4401c9810540c44585c040c1c4c401440c1d940000204501c2d0b5410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 423169082 1250 423167832 423167911
    0x150f0402180105130b060405042c07180c051e18030a0206071e0f03030507090e060a0e06030a021c0317071b030c1202070603052a0702011106 62
    0x4643c509000510380c408501c0c012802140c81d4029825075903581412030740501b0000f00100220304010210030b8000c80000e06240942070869180d00025100003501c07821603240800c818050b400c00c203540c10181c00040014018032106201000184469000040b550701d180031806da02c2d17a40942d29881e0300b070105c0c01c0c0c15000c5d40040d0131400250300d030032040302c007440c0d08904602040c215214000340362100c0504040c140a9a41c1d201600f0144d0640000340540f0541e56454125611a020381c0c043e150142da09541c0081514400c000c204030340400c80358040001000c1e58840c0e03803140c000c500322910b0381c84c3d40030404050348400d82c101504583c0e0120480310f898410400c91078501400344c91001002107003000c0584c01e01454080501c2000e81c0c56240358064000f02c09481010406503a6550034019200424103040009040c03a51a08140c0d8000080000b1600240e01c0e410080d2059488410264100250070b000c407411590100310540c0103c41011403500c0c42d501344020028021910301300b0000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 423170332 1250 423169082 423169129
    0xa0504030216030201020a080c03040b040602010c0801170c040f020409021605060c0901080c1e0d0b030708120a05090f03071508070509090c1804051311060a1b05150f0402 75
    0x543d031b00040046106911050007551a4a001040351442c020b076885110200c500160219650761306400982070010310f900d5003035041e41c81e0399101180c442c03880b5001001d64040b400380d03001c1e0300d466000f142804401c085c005107056222050310080c1d80c80f400d880e520a5001d0a000c2d010040c080180e542d10110303650030780e03060000c203c000910307603100945540ca40340720108e1555034503d140c101500d00000e81d561071550382c0c115280640c0c05445908030240c07103030180c50800a40c0400101ea9034803148618040d00d41b504c0880c90041c2d030706801915240784c01904401400019840c00c000c0d00024182003802c5036910a4414001080b1010040900f42040024002034400c1d8880300c50b80d80d0007000380c802c0251125000395000c40034142540c0786035442030908e010b01954450076000103c00343c1c0980620b800d9501c4040a01010344516403484000800c40201c1804080954a1045d42584240d05840c036201c40c0f0041312141076002e44151200b0170255052008510b07008007045400b01e034400200c032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 423171582 1250 423170332 423170339
    0x3051b0f2407200c0907091d0606090103240b03041b120204051e0c0301060e0405310c031b050d0c050913050a0c05190305061315050a0504030216 64
    0x204001d80ca090703100c000500b080d041120301c0310f090000a5138001c020301024110302e0043c100502210f07907441140740d420440000d007481c88540d41480d80c450603003c0c0945103000d144130300450007070640403000012110409800380d10380c0015198a0020724080c0d4115072281402c1c01e04110502181c070014150500e001e6003003103042d0051001148442d0115800580d40c1e48040420f03200d00c10a0b0480c1c2c40c5252a007041010014025016606841040e9511101d0a0310390050004440741a41c90036010995090481000e241106c000402c003103407070880c1c41941c40581c0d2101c1a03c006034000b19000044045a100d0090002101000400d4102c070040241070f1551109100b008917030240e01d01138011a00081d4400707610080302d654466010046030490410b03814103624200c0c45014440c400c6e21080010445080d5a29011f016282c1000150540d52a003002c2401d060282d03140444045411b400c12501c1c0300c0203032042c03a200340001c08021809240c41d1a00030b041a0004a00340e420306403000d000d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 423172832 1250 423171582 423171587
    0x6020a1a070e0303031906060509011b11271e150f130e011d0d0f20010509070f080d12110a0203040306050c04060c03051b0f2407 57
    0x40c01011402503038040c0c5880341da0341225000c00003800715400d8400001400208150080b62240c110407481080107400d4031200704442c0780c405d0005072400a0607590705450120100c91982c00150b100d030401e101e40070f00d0039010a02100c02c40e840e003620002106034160741c618001000782e07031140c10142c00809c40309401c05060388098019200d0405101c0d044a0600e150719900110312040e035000340080e10400f03800c5610380103040c070256584203650810340400740c44050729100910b20340c0080054503185450703500c2122285280341c1c140c0100b143c008900307054050001441d00200140d800080340320300c1e061a100c0d24100399030303018070400304904000b0171111102003445d9501508502d4100074817892440580c0c0a4090920728900100000800c50704003500000100200ea200f40000d00541d603d001d0000e20300d0180b889100c021580d1042d903030340000d100e04000e19403407424000c11540307000c0b410b4079a4034001c2d15040c60300da00c0d885184079528500e0000c400c0316419520603128a218034000a00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 423174082 1250 423172832 423172853
    0x6060402070f0f020a0e0108030c19050c011809051320011b0206040302030609070e01060c0c0603020a030f060602030a02010f061a0327010c0f0f02071404092a06020a 73
    0x20380f810036407080000440d41d80040c010f005000d401c0300051556102d44084d40c0741e90200303500d0400e038811001340700070141000120450958010000d86520368003070b801500c00300c80d0500d2030f40d00c2d03a40c4d6580104180425109407800340701500d002d1850780080e0f09d8922802e55804840c140b01458807403500d5120780e401090303541e101c82d103c087c01c88100341e5807011450500454000a40c103000b11410401d44030400071310f5030300322416003640c0c0c03140c1d90340c8900954011540340c2020340050810002405024060340090429900038075000078a40851800201200c1d8030f81c1085005030000550050080c2e0b090040002d1a845031108210092900c410b101c0743c080c04032301098440001100040c11055254075110141c80c02c5d4410f03200c507040340e2049078000c1100c00c00344400f00b016000c54200140c45140c010b0a600c000d07800610355182804590340100c03102001e00f643c800d40743c80c40800000c1069208915901c06603d1481e40305800c0e401421000c28150407a070119401401d00c0f038081410981c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 423175332 1250 423174082 423174113
    0x3060b180415020c06090604060c05030705070605071407030909050703020f1812030c0604021c0b060d02030f1501090e0a020a0b0903012703030c02061902090303040f06050304050606040207 83
    0x400b1010990340d2400c1d029024990000d440ca00a50040100640001c140b0b948a144608020411048078403800d907018003054230f21000051041c80b08100144980d80309039003184e45400c025002ca500185e5640c09684814001c50000700104400c010f031803900d010300703500144142419400c083c04440038000c240a40c0201c4843c140306031406041ca0346504001400140f2208141c1e80c0c0c4014100000703560b0842035604a019a180e101150b56461000300003029207640310050319419141c0c84100050034054074030a9078140a40440140030403030420054900c540340d010300d000c0a6142075007031800c03100e5902d00274003150400030094006035109070000080d90403104626898041c50303401300c0d0050401d21004001c141440005001507010384140166039882035500b401812004503040741c58110541d51001843c103e01c290310003000040d0060310003410090101c034103069581040c081002040e92141f8003146000091006012051011643c4902c007036070103500d460802e82c1c44504400c2d4019 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 423176582 1250 423175332 423175343
    0xa050706020d14040b04120305060609100e0910060206090a02060f0304030507080313060c0c0c05010e010215012907120e030a0f030809150609161803080403060b1804 73
    0xa000c82c0e0700300c4540c040c68500342c03030f04a40c0005107401d01e042e4001d9081a1130070b0360150110040c0b400518400d0150a00c510400b500b0641042102800c6c8100c021504d08008103000c02d07003150880c1900c0709180984520a504000c0d4034040c68604060b090110251040310030390048458000961200012a0840101300d00ca4640e2560b46003000c407964000c0c03034001400b0040020a002c511201c416150905900a203810032030815043c201755004025003c0041420120000030000c0f90700501c603030b5965030340600503a05840c910350103031300c02088242c0000303040e9020b150403096140710740660050b01c511a040d00c10300c1e10740252116203180c04c4500e0701400300700030072003072403800c1c1c50912401d1011540442d240f44001d80070315001e00300d03020850f00d400d61441100c1ca41e003848a0010300050007024064480d0f0610344840491078011088420071906212a00403071020b10180002d180e0700071400360702000e40302c60031031070594283d07805014058410a075600c07402001c5503185003101d41003039011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 423177832 1250 423176582 423176587
    0xb0f070504031403070b0a0203090604080f1612140414040f1407021e1501050402131502030306130219120f0c050405030f0a05061602010b0d06020d0608030a05070602 73
    0x164049425110310707040200201d5400199000030303400000034060041c89280c4011031592040d02880c102c0c0000c848420140d4800408034000c104010b000b00040c20803e032810b032514410b08078005d441ea500d28400c80743e420102800959030b5070300141500c5440340402036546050b01d8070490441791502d84280070702c2a0b90b290010b158807512944100135529080400f82090b203000e4402945940785074030700d80c070b8480202d010402c8040380440c0016047c005000c450072640d09140c141300003500007000c0d035400031040f1030002c110302015016000c003900e025401180d0324607041003403005c1c0d0003d0302c44043e6024018495040300354400c0c400b0901c1c106a031f103070003009903812070742c06e6024210a03400711080034503094800040d2503200008000b6500c00303504880d943d035180901213a841d68240c02c060265000000465078071480d0140710440d0398510f00c00880c0384841000011501002d580e000c4844960000301d450b198032140c01440c00030045540658105148128040c3c8140f01d540001420a03500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 423179082 1250 423177832 423177841
    0x102031204060b0f04050c0a0206060411040303230301030f03021b0a0e060102070b0f090f0a050d080304150204090b010f080f1810022a0703020a05040b22020301051c0b0f 75
    0x201d84210307034840700040040c1701b0307820300c0c01c040343e1558085001f40d4010f005200000d041030130f0501510400b56241100d10b841c052942d10202d43d000508448076280030032040142c071002c1e030a900658041c6001e21481e01c4030002c5860045d00d4500c5181c88074a5001844100345c800b661105e0510003221406c0588a00d159102030040782405020780100c090184045683e68500c00130b41c014010a035002c0d41c0c6002d08a144c0070400126108511441d54800304140c0f03000d0010b030311003010b142c0141c8140f001840030301065601c00180c1e00203800ca41036140d40c070050000507690000c0c0103045a140ca06003d0510b0800050b0300130a80d41c010001e189000b503043e2621032a4034100300804003a00045400c44d01c4030100074101c81d2000210400b221071007c0c0b102070224000c1701084e401c00b1281c0c01068410b8403840e00050002401806c01055403004070b036540020341d030b081c11200403036400384584016941d6040408201c410406150286128220303c91403000042d0000400d0307411101e409808201175a4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 423180332 1250 423179082 423179089
    0x9061d130203060f2d0a0b0616030c02010e060a17070203040306090c03061b0e190b03040f0b0a06050f040f060302031009030212091e03010b0d11030c0102031204060b 73
    0x980c4100a405100f0030013000000b040e119420360140703800302441090041400c1c00c0c91208180200d0400081d10b00001094900e0902e920880b84460094040303828694400c00446007800600d03030580200e058000b5410840da44103074948640b03002156082d060405001000b00341e000b440035540452000030340421442c5000704141c070001c0d503004c1001e00c0034411518060380550700c0c520044422a060a8858101040c40034004a6510140d034400c611b51440d8030030002d4203880c8082100e00f500070610082000640c1034021071140703000300c0500c41c0c0321400e445c7c4403522074401821135002d50b2408809020760741c0c800110b0040600111004190b10901192030310091126920080d07051141000207481502207400408105000f40c00769154500500b41c010464403540c5480381d4064010290f000c0885200003008001800140c00050700c500440046000c91020f000181c0d41030381090b03800c80042c5010820000321803800c0c4081e41c10003514800550007880041c10040c00d00b52a1018109582ca = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 423181582 1250 423180332 423180361
    0x7030e04051503030711090c1e0a090e0c0c0d0905220f0203010321020c01120f0f0c0c02030f0c0f10030b030d0903020f0108100b0c010612030302030f0109061d 70
    0xd600405985d5192081d1134101b003034403002d0303103900e028a0f0740300f00182034083c099090b11032681e0400100856000400d4141c2c4c01c991103005a00c0c00d1110a00d400310300d80162450392807007550f030200700c140d0ba004001015490302c0f410f66502020020354180900840e100e880304013100c0b0080008608259000000003006802c0441d16981001d03c0440000180704030484094040d0f4006605100c2155a0300022070311600c028980502140c603009000e1500706065100c0c0d400c07040c1c03a850015403e0190143c03d000d035501c41140070001810081e101e41035240030710603030782c81d141c00500800d4107080201c049006900c3e500748180c440c00000c0298203400b80a6000500040700050035501450603192020380b00a47d0f50000364003401401d80d0480255000f00c2c40700e40520b020000d058640b81c50b1540030702d00341e0300076040f90342c1304d5480c0c202c001031500070b0300d250f40d000d140310386c8000d80c0300c1c074144002c80b0a00c103050b4005d50300d00d810a902000102012240300d040c40515185a00c03007561480b84c00c60072003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 423182832 1250 423181582 423181621
    0x110a0c0305040902180a0f030b040f0201121d0138010c0c23010201020306090a021b100e01110403081905040e13060501050d1a070c0803191107030e0405 67
    0x3c1d0b00004140740746100010003600040c0f81191000740c420b4840000080d2605503010084c456000c1902007404200c031049003205407881490290640b407011164001990300301040700d410549145140c000401c800c1c065078190121070700104000110912940e900c40150030b80a1002e04201400d400c02644a0f1030181e03091500110041d0800e070b41d80103400c41000b6800441d60324000d42d1103d5450662042c02241d00902d002407090344141c540903101d8000b54041d0200d000c2e040d880c0703000000958070a200702022003110744c80000e1300c41c19240e215800d503004031103821000ba130104070a200060b0017500340c0c2c540944c0c400c01490076080d082800d46180c4215000111052a10000c01c4581c01c2505200e0812601c61141807003241da9402c01c0c00907894800500404d440c164145002c190160300303180039800411840c1c2201200c00039150101551b00a030346007802c403011000b400c60300000300e018030310410640030100c5203031807000c0d10010291400000c4031880360f91190082228640180f04c0c64110 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 423184082 1250 423182832 423182849
    0x10f0c110a0b0606040b03070203030a060b030c0702121c0e09060108252d020c03010b0a1e030204050f010602010b030309090c090f061303062004030f060f0f05090c04110a0c030504 79
    0x348d007004a400f039502d40088825035409814004041000a04035054034014642032544e142081e442d0350811805001014012a0070b114070007050400a58806a6500700300907610384844200b07148051040300e980040415050000e00c0060000124461502600310300d4504080c9500c0d076a11402103d400140000d010351074090f010314410070f08a242c1c000380f9900d030142c0031038500900500130700d8283c520a42213564031490780401003003c0c0c0310707000d03d00c811501c40ea40124582512580002d044483c2520640d42801c0440c0c014044141c0900c101041c0040c12001181064400c4002445804004000200c01003012800700c00c5034580045080c01120020704840d2162104e4030656484c60a51009480700c03410003045041040c0c901d9007020959144a900601d0310307095440c2c6011a01e00c5403c1101e1007a500d4080100350040b910850940c074201138004a01070614001c03403454815801101480f4a1500d4030040704049510210384000c7d50704d080103801c03403d407410103032950f0240343c9c8031300e00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 423185332 1250 423184082 423184087
    0x904030309210809010b0109060c060204030c0f1505070b04060209030c03070b0d0f02070f0201030504080d0501080c21060604200c030306030706020f030708030604060305030c010f0c110a0b0606040b 87
    0x40c022518090000e10502507075101d6150792545030131401da505640b456401b04900c0f18051113240e214141a4030064002c0a025103411b80d03ea468503550702040c0d01840c0c3c420031000b818481016000365506400080340740035802c102e040d403a420001c0c02c02800080180d6400600c00c200740e00d05105050049800905407411655600807240903a800960714086040c40e0000c000324410683c4259101150454108200e041450f80107500612010300305888045081c0480c2400d6a1030f8041d07680684446d20240c01041100d60a00440b0780c00424003103244016144107002c02000011f4542d401482120080b84c50a0111601c0c1040c0c610b44070f00c03010002002903d841d0203c00080214000c00c829006ca628940d0b88000498850810403100303a00c41e0020807058005c038100502450300858018800543e03140c0c0c983d2654a164080c0018214a075103403004090b01055070710800560031803509184105600110480c0d4075111403060081180d6160307801b06400b51268000d0318047d051a034511513 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 423186582 1250 423185332 423185363
    0x3010519031202060702010b12060f10080d0f0f0e1c0c2102120d09060e060f0a0804050c09090a02040207080d02040f1e03080a03020315150403061b0e0904030309 71
    0xa4032100d088179513001540c00e0500d403048500f044400075681e06140d401600458031452146492000c0180c1103030440d0b84490b4003c5140281448800380201183c1c0f6a20207880d09280007a02c60380d550000e502c140304401844001c144c6440c01001522a5450848450442c0500e8042990400e03038120b90912805d0000c0c00a01e0700400514a1035076000b2641c1074441c40c010305180781da40c1400b140d8800000c80030307041008440e001e006007040805000303110504000d2030251182c00c80e08110b15070000a40014180420301c24240b105000c142d60607640320000385000366045680301c40da2a4000e000c0c5a000514003340700341f500170b403003030440103000c2590b07125a00c000d5116148500d00032000c4040082030400b0b485d020030860101246c1c3d000051600340003004006800070740008002c001800e000900030304065035440501a660031616282d69111410350520340c04460b02c91200040080c03c0000801010360050a4510440e108a8403042079079118a0708a010380481071008140a08504149 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 423187832 1250 423186582 423186587
    0x501050709030c09090f12170a0c030e010c02121c02030a2009010905041a10050c0d0e1813060c080105010f0804030c02012006010b0924030105190312 66
    0x7001200c1c0610600d0750455203c280c0c20044615100000384800d0802105d080000c0c0e020311103010820041c244501041d41d5149071061601003280e0900340683e880019011480d05841010110454000200840488544041d40e2035982c491910106200811181c140182c0000c40800108000000f551203041c900305001c0944a40f800d40318280b03010030301031280c0071400c3c02a075000260582d41e2007802854041400300400c01459091000d0130340d4100100301c1c0e12600d507400c03807000c0302d640c850b070f51480540d0110b030074451014071681c20003840d165040e80c1503407049075142c19203210720059a425111742452801103440090018009070810303076614005031308114058100d9600fa00e0f02c03544a03070101c104590004003260b0050105540320340c1e100155200e0001e00d80d402e800c00034401c440341c0083c8100346c07803c00d0136800300c0d070700540010b00f45a041c244040c0b080031b1020441e03111070742181100c1d041481408140141d40c02180e400442c400f4069022003d1002107802104400a40300d404000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 423189082 1250 423187832 423187847
    0x60b0a02060108060f0f131b1a09060409180c030f0b010b0712082205060402030d080903030f090106090c0206040204060515070206030915180d021204051c05010507 72
    0x82001601501000003003025001c202c2e0303403140d404403002210f2956400c02d0035a00740b502030320a01141c440c00c4440000a81c031078588032203031844160a107800030b10f0204880c801241c409000c406040c410710842c105901c400003900d05944102c04003186083c070204502c0c40b0110400f1002c6e0000035032407800420301264031030f04022140030b02c0009050741c0c1c07203051a00444c4074443c1e0060210903100b8604855900c201c121540013440e0841a1a8000001885251198500c03c0a80e80e5070031180c140320841c0390400010b028040c60b4101108039142c0b10324403035120301000300070305d10103240d810001d8102d01080d40f00070094040c240c020030100780b01035402941d50204075800c9002c1c17071a2007800704282c40d102691058645003020304525104143c0d092041c40d40003d000020944201d00a6182284002c0016071007140e200d040568002186503501c7d190190002846055400200148060b070704481304490941e00c0503684907491606003801801d008040801c09003031540b8140500c19103075400300c0c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 423190332 1250 423189082 423189097
    0x10e12030417071a06010e15130b040803040e06040905030306011107080d0302030105030607020a05030307140c0615010f0302030f0103141f0605101106060d210e01082203030e010204050301060b 85
    0x90725a9951245c00548645010181080d8004070f03c0090f43e102d6000c4000400c04903110b0045450400c0d0381d00308411381034110380c000215542000c1818002c0da5803c5190b6540000121424030500040c1c1d110b09803a4440034040904003e10784001d062002c200f00510300007402d14400312142d46005080060094100303006080c801d00030500031550b603503c0080d43c6990544c21001562640e2220f1000792407910210744c0c0c1c064090400c4c070035241850014403000e8070a4480b03588502d25000098001002510182d6080003450310500034084072451710120181036940c003440000001031480321103450141c0740d20600c1110800e41710324070320b60440c9410210403038034181c1d007441c0000d0b28240d06540352107106d5030001e125400007002540a260001c40c401209003e21050080c038500c10800003400c0600d00903203400715004841c01c0b22207590000101c1c0c0d1000b8030020388024900503040403404842a00000750405440d5150648001c4080d41114000c00c0d00500802940f5650204086503420141 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 423191582 1250 423190332 423190373
    0x5060f04020f01020606011706040e030c0106030b07140a0e120d09050a151409010903080d020307180803070b0c040f0e060a090b06030a0e0a0c060e040e010e1203041707 74
    0x2d9040d40c80c1d50000418600030301051b1180c0c2041d0a1010303a44401000080c021a402a1105c000034a0702d081400201181a003100010a5140c05c50818000c07400e0041c6c4175008000f5590038000d0342060381d0058504140b03851404105210500000802c46101080c02c09842d00501110218954200384084201da00684054001d10f80e40c40d0700f101003043d04a4440049807120074202001a50307607000340310a00d0141485000d0544a81707542c01542c01c4000219600c40c0e00105019029400030b12400745d254024100214071410124195128040c144004042041c120089208560124240c0380906031146203c03844550343e40c030303054000e201030b41e0440c0505c11414000c20403c509020300d07005400e0207054585161200344100e0024281c4d03652001590040200c2e0000062044031110300030091a99240500740d491410401203518012500d5116890312011101e0b03140003107038042541000c4030696850f40e503941030041c0c81280041c0002064070300003840c03030200040e000300d26858141c0308 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 423192832 1250 423191582 423191599
    0x303071502090436051e0706032a031817311a070c0f17060f07110c04050127050f0f0c090a03210e130b01050705060f0402 54
    0x11007409100b8901a00704003101c0d03030703401100c402c004049040c1c440c085e1161040302d040388036200030010880b183c03401190f15a0000641044042d078540a160301e4981c964460429407104a101000c01d904c111008a0500d91545541c0715002100b6a4009070580c00000035021030058101801d01075000a40c060540b026510340744500440c580c88005010070606200070000307050050000101801c031071041011300d41040002d000503054603501c401414210710400485040004580c1c07480495103c0508940c425000c001c04100c04403080c54110085042803842450804811810041002010780e000343c2010b0000a541045403080750003070036510741010304603010b401510292403054a85c03203080c0c01118080303981071a144440640150f0a00d20f694500004c420100304160410751059400030041d0440c2d0074500040344044110380e11528151031b0600e5500001110000780d02c040c0354900d5070303581010440d0f03401a401c81f04100d801c041241c2d001c2ca85003844400d144c0741110103d00400c2c58 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 423194082 1250 423192832 423192851
    0x150e03011e2304140f03071208070c030905060f0706060f030b0f01080601031104061d0f0c04052103120a0f0f180308090705060406020105010807080c030d0e03030715020904 76
    0x402c0e07207042c0008403480c211926a1142d03140c0c50210000c00350b00740030300d001e902e402940c0b241c0200014161a03126481075004245034980c09402704000074200c400340000703920210000703075001020400381c410440c0c06d952503070383c0842160120300415000421180c42e104010500c80b00604950007103074401c281046c555524103d5042d0800800c1c40740419035803007440144002542d00c0c000ea150800081c00c0092002e9850300048205da81039586003e5481d0f0074402e10281c091043c41241d80a5021000a458036240902003a022001011024800444045000740341341e810f01c201d510000303803c489020103003003007503042000740144000b0402207841d00b2150110303454107000b07003151103014103912054000d854800b52102c0d00c00070312044a6010fa01c00102c2c85594940150001d041140d00003d1190704141d1040e03d441706a82041695500404000201d60340004000e03c180b0b4aa24040380b2030a01000464a14085c1034070041a8807a03c500c1442c1030115a0f000d0b01082104480134040c2880 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 423195332 1250 423194082 423194111
    0x512030d06080c0a0905071205071d01020106150507062c0705010e06070b100e150a0f03080f07061e0209040b0a03020906060f040e07030e1213150e03011e 68
    0x319032101e550000f44c0d1a0b401c10410302c065004550115141c244080c11507498140c400888408030b60380c20200d0300001d060300202025a4491606010a0008219503800c1c2440300f1410101d01001c0c0c810000d001074007908009060f002024010b2017401c50581a09140d503d44000c184201a203008520410500003010b61241c800140300f46130140c001031400006480d5045038980c002e0182c6c001c403a81c50300c005980d040f43e084a0344074802c103e01000c0c40400c071804210591855900c851030385443c0d801c00380041429103044031049840d517071150340c0d140340918021000e011000c501465200d410a509252000c045c2c00410b9001c0c821181080440180c408006d52941b042c0000303504001d0840c00186142058070081030100b1036012060f0a2a5a41091840c0310500b140c4200010361202c0a41d0701e016402c106a681101041118605250b203044440201090300d210796249807002072109404a402034a00d4018440c0c090000d000c440c001e0714003103201e2100703400220b2a01b490031802d80c17103c04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 423196582 1250 423195332 423195343
    0x30d050f09060708160c0b040b070e0604050a050f030f010507080f010e1311060904020d06240c150902030d1106060102010911040213380c0c190512030d0608 69
    0x2103107501c50001c0b175140c070a2803c005116580b420814820711414801c041805062542d104502ca2900c242c02403400b0040181a1081080c0c452300500302807200380801d646641c24a000d441d015031303060070718002c0d00c40002c2c6800e0040b650718800d546001c050044072903100c0d18a510038051041c0002041c2d0361035107201c0c00d5401c12501c0345003207840f01c4503840000703283e8040c103a04004018050303418020441c00240803680400d20039414599200f0041108444081c1402c4e1420b6204046520b44562100e014100800c0c400c030040c083c441f4400454040e00032039100c41001034000c0e0880b01560056040646a1902c0c101c2c2a509842828006901c40d84140501007a01d0741c1b004c55000501101c10601010b9008941d445000380f0496401040e800c00ba0203840c1541c00c204203600420300540c141016420b2010383d462a00a081045810011000040c40c0c0707040c20380c184c030f4682e14103074611022980040b8940020f079204004107000240e00034004060124044420010400c1640e00d111320f940c0c0300c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 423197832 1250 423196582 423196591
    0x10905010b0105090108270f0709060608060904060905031b060703060f150311040e070c0b0105010f08040b040203010b03160806091c0809010b060412050c150301180905030d050f0906 80
    0x290080e0000b800e41810352030441f02200c58014060000301d902c2d0b411420400001c5041900750301103031041020040b50b0050100500e07050402d100c144c1000b4021403034268009201070400b81d100c004a00030414104119111441314640c0d118942200c01c0e0155101d170015151280003e0034201c011888003000c81444080303070143d815103007000003903c4040c0c015200f80418403584050a1100140c190b0428500030300c1004c0c9655038040c49102c51515000b5041c040e040181040b0104c030040035141d8022880c10382041e001404105260754610000b80908000041182c150240c5400c0c184007180d11800c51040c0c2e41d042082d24041e680d10601999100030080d0042c4440448000342c6400c10b008003405a00300455000105121250b540821100d03031103070b4091101da007104100c40b002d0100622005045034070444500d04440b407409031220290006008070168091103894400180310a5401040b400f42c0c06400e40c5d03121980b0050140042c00d04880d4410050007290000c1e07410340000c00c499124 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 423199082 1250 423197832 423197837
    0x90301060f1e21051c0503041515140402130e1614120402030f07061706100e0114120411030d08070207060c0f1a0604060504020a0206010b0a090f08010905010b01050901 74
    0x80c600403040c185980710002c402503070305000340507000000d05c52004641007448150380312203690b410a403821004950360f02d0b40c255241440c1c080700c01c549904c546414021125542d0040f401d1070819000100288240c4082a50a0210a00c0000d6400d005c86101d803003001059604000c1411141d01510306c10440b50000492044c10425002070303c9450380015040750024046640c0c07040c207800c1c0b061920185070011400701c0c2071404510920700550060300d0380200240d13040103d070040580090301003029000c0f09414000c0f4909403107085520350041e2480d0b0000c4040300c0250341000d0a2003583d01014030045d5010b0301074001001030302da0056042c5405121580d0080045601d401000c89084040c10001c5400e1061221840c0105040480103a41c6001c00c4c3c41800450504004110072902035a202d14080c0f030060103c0e80341c40d500070500741e04464510307110981e1071160080c1151100c403282c12100f041c12240902150041d815407002c50f000c1e00c240b008014007250040152038500414400600 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 423200332 1250 423199082 423199109
    0xf02030405130509010204030218090c0f0603061e060a20070b0f0f0d0212060906090601020709050a09080a110c0a0e0402040207050c03070909050c0a15050a0203090301060f1e 77
    0x30070b582550200e82d00151041c001402e20380c0f0b0b50b0020b41410310541064164044d12028408070180602640d942d0290488405003401c0c0c40c800810752500004001078031031401255250b05000d1b04116454541e5002402190b50303a02c0044c000e84003401c444e100c0032194082d460056803802e000200307076066841c0c1070300103402e0403e24520440d13240c0c0701880701d0844000602c115884484140013828000410341048881841c24000303000d00103500410141c81030802e0001d010040e40c0228854050719001c840c00304490b41c44600310700c060110300000420548e00080c0e1a003400360312640003040101c0410590f5946070b40c2c2802c002081120f0701035000c0309034184c0045001840d00f40e004090051241081e02c44c5014018006810950f442e403080c15855115042c94042042c24400307607002c02800c413454914581441d04401e410401d0160341c00600170b00140059aaa00030000c1c3c84612000900070f00640303848a42195000603140715482c0b00720203101c00f081140b416001c02ca015143e20700c0d240c88 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 423201438 1106 423200332 423200359
    0x80304060b100f1b0c0e24060a26090102040f06021209220509070f140f100e0405040506010302090606210717090109030f02030405 58
    0x620507520070a0b030784545034011190689039040e0303281c5044a00f81d10401241d003004640000391182e0991580000d441e040c1d0303410a8414a10100000c0c0e088008240d01e452000c000c04a00ea4041401d0201c0e5010034481c441038180c0340340300c02c85441082c1109004500001c0203844254580e5000901401207100c8404110020907061000f080c1c0810044e0a003c603e00600ca101c0d4810840f14290301c1404071840c900391540f803800340c4200641d042101c2001d56640e0144550900302c20f003a44002241d010080804150140c00783c40307020305918610400c100011201043e10900c201802d12a00e00d80302c1e403003594800c6100300700600465041d8010400c2c460700c01000140306080412442140115617182141d0090481c0d00045607503c130f8030b80503a440447d42d1904c444110405040214084054000001d0f680c06620303040d45440308000300302d0b2039101c1c500445400100012022 = true := by decide +kernel

theorem cover : BRFrame.Cov 423021582 423201438 := by
  have h0 := BRFrame.cov_init 423021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 423021582 ≤ n) (h2 : n < 423201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
