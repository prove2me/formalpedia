-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5307
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:26:05.684794+00:00
-- url     : https://prove2.me/submissions/1f1ac264-4e57-4413-80f4-87487a1a17a9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 954316546 ≤ n < 954496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 954317796 1250 954316546 954316549
    0x120a0b13061a0c0c0319030f05040e162a14030f120907051c060b12030703080604020409061d0114010c32011512030e0118091a3309 58
    0x224444080c0c0040440745180110030280e400c106c900403084000905c942c01700140d0a0203081901c0954928960704425540c5052203141c1110188104d0410001c0080402079007c440403580066510000c460103061503081c02c1503640301503d01c0c1301d02c3c480ea004000b0803007040d0303045042d20600000319004410a803120030350382d0710340085030f00142e5000e400320140160031816852040e444900c500420720402d40e040040081c0114901804065500104007010000e03100384062540718000030001801c0585840070401280c2e0700e504041c1030300d5031605c1c164800d00001c1d4007050062044407010b211039640d210001b0036484030108010b1140700c1c04007504215400e0480003008040305900d103901c821206c18421406007a500700300924001e0303101d001051041800200003038260301034982c062003124020045800000012004110313000380e842c0440d85450034050071800545c07a03c100302080c0004802c200110030280700d411050014864040341050200f070101b104003c200c2c0149031640680d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 954319046 1250 954317796 954317803
    0x50d0f050703020a0b030a0f0e07270603030306030b0a0207080f090609041a10050c1b010c17120a0902130203070e0306090105040b1303080a0c0302120a0b13061a0c 72
    0x2c2000354040d550707107008901050f0f444080c511401381e1000900ca01c2d007488072400304440890503988484c3d00001001e01c008000d00c0d240711740c0c080c08404101c1d2542450390b1014129111504100d00094541004000b44175900081c00d80005081400b1890302100d50358000c030302c0c030800040c0b9402d00000709003001c5966444040c1c682100e4040c3c418000c081d0100340c0383c2d07140d981e0b80a03442c1c852149094144600d510800554124245140040183c50303002d02800010454030091141001070b808020400100740ca4070001d900000310800c0c9894a1014562501e9050010612204075180c0307140d0501581d074102c204d030000d100030800141e070b0341c903070307041c01c0f56602645d40e8400c2e00340c4950414048035200540c0503920850041c00c451320151075100440e00b071900c030610b0190000b50000041410b082c010703484102d09000e075044c01444c200316600d50842100c3d04272031001140341c5e1411500254107008860441141003074000f0801181841c1091020b1040849008900310001c903c0b00034480080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 954320296 1250 954319046 954319049
    0xc0c02030a1b0807030f080d060816140f0102030d1505360601081506041d09010b040e120d1515020c011b141002041202041104050d0f0507 61
    0x601940e01c00350302428052200140585400d030486540c1000080c0d0b8400411240b095985c030400c40309410000d034440142039004201012041503485500040c400310030010b20036a42c030002440d1291a1806212409904005090034025440310040c1c00050b03034048121062090340c174000080764560300c1038501c604010b03500002e4000d81c0c031541c40340d111000b511b2035031503030300f1a81010306002c84807104042d520f40058403c83d01180d60ba00101340a04003089039000d07004800b0303042c68145035855001c4c0f030400c1500951031412101e035100f80041a0001e01075034180300001e032000d04c140394044651b0341c0d40744120f601c2c107052800e020a098030006125044210345030b004281d5403906d10749500c131100d183c85080e800fa00162042c02c0307000c521035000d001c46006210391070402003010581501d5070500082e04018500c024080c1c500c03c003400000398405800606824170b07031040011100c0c03040c4030498018001216002409010401c002e0ba24204141c40e0150300082c002980b4000d440c0c0305180048a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 954321546 1250 954320296 954320299
    0x1d0f040615060306170c0a0b0711090a09110a0810020d02130b090102210a05070f06091209060306031e03090314060402040f0e0705060f040305072c190c0c02 69
    0xc407a0000350180c0c1600031038107171034400c800007136a00c0b15050324a40ea40444d02e0001d401a420700c10410124000a0180c414103010340009280e00e40f0000018203400c06c1110041005a600d1082c5001c1c07100c2c0c85588241804180c0b030300612141040403c0b50b5800e0a2008283c01d282c00003020b108221141e01500c0c0b2a04040302544525500c1c0d0340c0d00282904042c0c030f00790041c4135061640d9a9514403010183c45614210902854102c01c84070440e0a580280c0342900e01c44500c40041001512078443c407182c0f04d025202c0d070f40504d0310340100100814200d5104030105030428000f40003141250103a079840d60f1101441c8800d0340300318902960742510b994006410790320241840403085102040051242d88200c404201856640030b0410450300c1c00380c03503d00ca5074091300f010701450400000030f0451114000840381031543e25a20302d0310700304c00c1d07401109410078076401c082000c4c0e916864410710002481c00800440c500004000a42c184c03503540da004250f01c80701c1c54003c0074002c50690b42d42d680c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 954322796 1250 954321546 954321581
    0x60e0c03100501060e0907050a0c08040b0d0b01030509010e15061804050f0c010f080f0402220e1c080403081009020309010548040b03130c1d0f0406 65
    0x3924801c14010102403103124046001e1000c14101441d080c400d041c0304103016202c160800c031000e002114184000300044070705030000c02001c101d1540300305c003524855050310f801103000b07007402000405980006d028254540c0c14a210680d0a08010803080352052005034640265601c200000ea02a850f1106082258130501e05000a016010400115080c00c40044500100a00004598031004291000300003005a40450043d0030807605013900140002e01b01e10111883c03548046006202440c001103950f03036240081e1003c4ca003031202d0511740101400c403407200c200c0c034003028100560080000702040610302c00100c280c0c01950324100500101e98007152a0300e40b00010038020403042d5030248030034000c071900c0e84c1c81701002070044840d1349400071950980c032030700c0c3c05440558480c0d400404103468244000300d034a00218020358810102c1d40421070900c031180c10200714500c92074011b03d20120420459110320080701ca641e540114190400d0340842d5a107080510007041c0e01d03960100d4148 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 954324046 1250 954322796 954322813
    0x16150c0206090d0504050a090b042d06120f080309011b170610121d0a0302160b0703020601030f02010c0c060f020d0822031101020a030911030c0904060e0c03 69
    0x160300003030092049818004a0b1480740c16080c040c0d0f080c0c015440341d01d51007001e50303005100c1a40b0580050341766080140001c2542d01503181d480845503d428031981d030320701d00001c4080f0540c4046c001d90b001810038424200300c00c00c3d5600e403c0d2100c40200d00c054841c038070000c0401c61480013584110f071000c0204044010080d03090000801c5441211400364005c0c5210000c034105141114540244965030b4540083c044200d070001d4014250b800c00011081554461640305840140000341d0490f00c26401f07040c1200c0058012014200e440d004100e03000c4040c09200700107074002800a056903000030000720100410b200407200c0c0c4071a0303030006203190340310b1038001740f8941c10a090401809071602510360701481e01d00300700c031190001c8407250750b00400e0b04090003012941c4070700214058004c0c580000c84010307292006007a40c2c804254640003e599103503074014002064011401c1e000c0850180c1f5000206900041c48050f018101403d099a01c24685c041a641001032080760b160107020f40c0c0060 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 954325296 1250 954324046 954324071
    0xc120f01030c06050309070905060d0501110a260f060d060e100b0103020a0e190e0c0d06050607020f1513030302150609040b070f03150b0a030614061615 67
    0x2160284011200501080c1001c503000b40250166841141c0d04401019118903000780140034100c054091500881031001030008148207018040400b00e0f0b40700c40c41d5407034105034030040c1001c2040c240e210100c0c8035600b0b2440010b0080b4051a00454401200107142e1103010000f150001241001095985007404403076004101007865080c448400d8410021410900019030607840781d0406080000c54a0b1003c002e285054001d4034070b0307103003002007a103555902c40244500c18401605c019032104008910314480700380f00e0050070b016001c10303503442d820408180d000c60800307807010801611070306c1a495100c5003201d542095039040d1160f2044569095038a04000e03407119400846400900c00b50380000e5441d0408521080c000d81e0301451010032030303031145411119119840405010107442d4000700c02944108008400600754008000e40d54010004010381250345580c02a000320740000c440c2d503e5540c40b2070640302d68400f5640028002c0c446407915404840121a400c0c0d0b01900d4005400343c803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 954326546 1250 954325296 954325321
    0x50d1107092726092b020402132c13030c05100b13050106090b030c071205030108060907080c011803021018090902030a14160305010c0f0e0f06030c12 66
    0x2500a0a5442ca00d070b0b5000b2004507454421328003c20b400c6044443e080c102110940081884190403103000e010408640d40058141d0340300d240c0c5860120312044060280d20340740b00e40200e450669445108141e441c0c401d0344600007074010030540804036030b01114410f060003000c1d403007425a40801a0707002c0380500304981c0010300300c0c482c1031402040b04d1010940b61103000d203d058180d5650351505005585030001e4200c0341d82c80100b481080390b10500c0100b00003403082c030714030402140948805850f903040c00d500d40d280100c010f064680f154006541000800c502081041d0f00100a00e40449600403408510146d80c03480e500c025080f80034420001350683c3d1083e81c00140e5415400c5910010307981d150254141c6040c01d0010350702d074110104040c0080c00703135820b483c2c10521034404d40302c6045980110181000b074550055a5036511400c5034580d95511010503540308140f81840c0703040204110128401c001c0c41c1e00e0681c001c041c0000810071078038542050301c2c0f05000720325190600d854043c040c0c805c3d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 954327796 1250 954326546 954326573
    0xd0302151f091a060a090b03010b041401032d061a36010c110d0609060b0301140126031c0b0402090127150c050d11070927 54
    0xc045601e0000700754003032076001c1c060b0b4070100c1c1009142a07290407010440c3e264002116841408020034000407110002e60245009150109240f51218a8200003158242c5054000e5040505c0c0452858902140d0080c0341034004024080845800c00402058000c100301e410a5070312580d984110315104a14800811102800480300c0d0080c55240d4010424445808054890401c449034405000d521500d091040d29010b03440d54001d90469501107203038841d000c0300c142c54864403410050240685400fa071f001c4901c0a4000b0000400c0200c5052000719042c00b9210000c3c640440203030106460315400d900301140031003681c1d6a200b918100608000d000041000120b00781070f0482103500d00780c420b4907268001038490009040d501103411740100300101890080400d001030129162034480c0c845c0c5c00d150100c3e1100c00c0210320134200a49442c9110300800100024000b0081c10340350301142c0501280e1720340f040414041c9246242c0701c8954048062012101600c0d00c5031814040d0f804400c40c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 954329046 1250 954327796 954327841
    0x7030b1207120210030608060a090c030b07081005090912070609050d090905090726010603052409030414060a03110f07110906030309100903060e0d090e06030c0d030215 74
    0x901e00d04c0303078400680a070b5040f40b1680005400100002e0000c402d03d800c400b43c1e562180790001034840d10781da9280c4c1c1168080d200500011801b204000c1c4103503025140e0400303002c0840d404621450010511a65950150400f03540100003040700010401107410481c20341d68880190b690381510310b14018401040c51103444240713410400450400303c00454400191102564564146003000f0340100789034038624088245990b03501e8000000c143d09000a075001305201901000400c520b12000c1c1c0e041c0e1025000f2441d030f4004100c1040388090b404410103200703e055031160340714152060b0a50003482085540b00d5000000110410020264001002114031074440800d0110002081c4500d60400b01d40c00d68255104100002c001d190004900341344480030314024500c06e48030365816041e507201c03000141180c1c0c090000341c541250403043c840046d20032540621068500703440001da58041000030140a60043c0340c030320050610a0100b0712604c01c021400012900308031000c010300300070784680003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 954330296 1250 954329046 954329059
    0x30103061407050915030c120109020309010e3712021515090408130504092d030806150909090616020708120d02090a06020102030417070b07030b12071202 68
    0x1d141e03030b4040c2e001d903844044c01401c60f45802c091502d03134403500d40c07000c1c5c460b0005072001c1c4880c41c241d29000c4c41d0f0310f010f00031000c005031700c0c0d044c002d41171402d49072490045003180d00300988042e990110708280000442441e00d0b28900b00b181c0f20741e009424000e51002810b404518650ba003035a0740c00240a070302d000c029406568050361921440c0c0f2240303408400c03ca90040c181e10100b000310b5007000280a20301d000c001400076095590340018112407007800201c440b03c09481c801c11302076265400d2144120b603010025a5080c140390b80084c1120b1008000c644140c1c0c408024140c2245c41c58103a40c0c90b45005040f02c00941041c14285664080480701c8016071409820b040300f400d4804a440d03001c0750581001410542155151001a0f4202e0307085500a25402d009003805592010742e03c00c010f051b03540006960f0305107070410780058140d075481e2410010f020004100003502100d04a503015080d46800544102100c000070311140192000301c43e0b920410001160710031031500f030200e81d80e00c2281d08 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 954331546 1250 954330296 954330301
    0x31b130b040317070308150a05030f10060914070c060b1c0b07090b07060b0f030a1401140411060901030f060b0405010225030b07090506190f031a0d020103020409020301030614 77
    0x100340c84c0c8601c200080c009950000400e90184190141c1101c40c00c00a004101413074688010a20303255209070354505c03940c070040e0031014100240c8036050142250580502c107184c4a280e0000e55281c01030111010060031b01003c1061002503131140c440304900030001e04501d4841c0380c1c0c1d43c0204106040039160703000302c03102080c4268094402c407001c91f50311001407030030030010781c86800040194101c02d6400074a01c1c580070b045a501800440b05140c843d101c81500b00c20850003180c00c5400c0b202440c140c1e4000d2a09000104005200030480c0d240c0840f0f5050741c400062004801404650182410440c2041000714803d59a800680140c60081e800c0740d02481c22034020a510405004511010310400001400801c0c00d0b0031099500c82100d0500c180c1c2030380c0d10b00201d20681e1200356815001140301c00e01965460748003100008014003858184090000c0c44450a60700461031105031240c0b110040450842e4026010b480003004020f40842d225a50383c03d102010307100002041a078030346030745c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 954332796 1250 954331546 954331583
    0x1e12020d080118021605031903050106050403140c0405090f10060f030219120c150f0215060f03120a030605060c121b060a0608071a031b130b0403 64
    0xc030184628915078032110300da440c00b0468594407403480110300c01107408100141e1003501c07690010749628400d1009583e1200400043c440384850f5038155130406040000404c0007660001c00c1d9400d40b500719408410381c150900100745481c4030200c0741c0b50854144420071004860110704109200e0910301503d01280c540000d100c111490750250440c50b020400c07080c8050b0400c05250258814808050b5882a40703034801d516645001183c221003034545d12000340000658424007100209860611030200010044081d4944d10700084481e400c582000c0003460568590130b40303139a031400140c25560031000c800341200d95540507006500129041a0b80014141040000c6603060340c0700d28064203c40390480c0000102e42d002200c400c0c41c01c41100e400100c1d800d0107010140c00341c10380c242e001443c149400d24031401c00d01c0035030203007a00d032210400c00c0741401004070881c0e41c080d058a100101d54000306200c1c1c503140c010005070580300f02c080c036808604a0f01a00041055074041c60100d03003061403810 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 954334046 1250 954332796 954332803
    0x10e0d12030c0338060706020c0d090312080a270b160f08090a060509010903080a0b012304030f03050a1404030809210d0c0b0f06010c02060f071e1202 66
    0x38502410703502d699480d134081203a0b18000d040340c9100103410718440030798100142c01a04114800d0702c40079400500c80700d68000400c400f0525003664100503220600c0c1d41c880d4000700c068044080240410040059038501c850361150303a00e084030440803840720341c401c0b9683c540b10001100488401c100780303020034603285140442a44006203540d6203d40140030000031030740b0002c050b0004038035101d0583c2c240c0003d0203502503144aa480500006070007100c5090090a00e0405015824400d1501d5030024440e41d02500480d100d10a840c411248044001c031125044c0c801e80d0b1010303081b2014008404c04040c1d102008004120040d600c0404541c2d00d101e00840364030a6210048c840441008201d80a050000c001c900039040e030700200310407502e541086800c02d15200c040c940001d824880c00420028001801508105814030031055440c0110010300603010150010381b081d403000c40e4a0051103020700031142c20075400a001003000300b680382415490b0f02c410310304540c40540352007003400052000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 954335296 1250 954334046 954334061
    0x151b0c030c0d05010b0a031415073e0309011106070f0f032c071d01210609050106061b110111101505012615010e0d12030c03 55
    0x4001d081d904441c0000c01c140c581141e50b0465842d5218a0202c5591b600c0c60b15100096000d040d03180e40800c91581c0460070030250412400840b4003200034042a83ea02240ca6201e03041107000c0386428080600d4001d030700c1250142401c40d1228140035120b08100080040d00301c4600c00c1c3ca900d6000c4403804903098903480300f242c510002502c940704a80f80d9610680c4690901c00581c1800609004402503014682901c101190884c69034031020a40da8081000100d009043d1684031040c00c110125040300080410702c02c03c2c0340031165840810403121692900d0070f40b90b500280c10440b14501d80341c910f020304103600c02c41020400c1000d83d803000201c410400c203807155000c02c079074070004281d41c01912800b51b0016a4011845499050207c42440d40b0502c281f440c041061180301c10704d0007000410300c80010303502c41d441c5c56814501c040c04221115080d90015501110858903010b0900100c1d1303001101c14180d030744000e21844910600031600340b030750910400780d5028800041182015400d80780e41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 954336546 1250 954335296 954335299
    0x80408060919111809010603151802060a021e1b010f020303040605070504180e07060e0d080315040203041202010c080106200f0106061d0108040f0f0c05151b0c 70
    0x302260b00000c0c00212401e40c00c450081502000440d440c003544c1000c0341c12108020941c0d500d0400307005205070741d082c044082c0d14444c0706001512401803400d981e5020490000e024410105442c8900f0f802804290511b00d0244407411000500c0741141d96a142038801e40c84118060060244103035220f0301548007440c4c05600110714688803a6030f42002840e0040c440410040300b07210200b98076103400644480c249401401013039540c02c58060700e09141c03080c2c0c0050103200701350302d4201c155290001089801e40c1c00c8101d9544a903103480000c0302064890032401d90141c4000100310400000340140300003085035500030015840c403050103503110078081c080c10303000c205940d0080503031280722101e00c1c1401c461442610202c02c6800320f81e601b0340d4000d40050000c5000f88800c02a01940d1701d607155045074003480c2104090900d603e40c01302c0e00c2400c4201500c501e0794020290117200218900400800c0301409280c07204140c54520500360b0007041040c4003508064000040e240e40c001810b10001c0740 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 954337796 1250 954336546 954336583
    0xe0603010b1b0615040b060702030a0b07050c161401090807050d081201080f190b060f061207080106090e0609130201020709090c2d1518030804080609 66
    0xe02000040c59040003550003040b03510000b8040044506001141c056403410f03060082150201c030402080e0350030f20f0170560045038140280d1001d82d60000360050038580100070b0000944034003804403041c0c415000305003024812411201b212041e142010421110142040d00680ca00381c0c0c011286080c2d2031141c2c80d484d5020000a100e50300e0030340351980035103114524140c1380442401024480c03102c2607025495a4004032000080c511051283d003140307060300c456005041c3c449590702941c504014202c240509000c813014050342e20b404d401c40e00c050310240b256400d10b00e0720603401003100109004600004820090010780000020120342c0200d000405080c0150348007481640d8244040a0990441c441c000d400201201c40b4030500440500550040038402c0c00c0c01c40940240419861144c06214981e100ba071410101031011010b50b5007a42c50855004400705080790101c0c20440000180034407a4000020810980010004c940001c400d4828550b00c4d2a88e1031348034207010400501114 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 954339046 1250 954337796 954337799
    0x13031106070831110118080601050a08030a081f0504021317010c050711150409020403061d0a110102010e030c060a0609020a05030a0b04020d09050109060b09100b1c09120806010e060301 81
    0x9613888459240018107160182c41c0070701c3d14985001c000201c0c4e100740c80e190019030040c8440c0c18020001c1c0080c280003c001d40c07601d408040010071a907401804030803000094011198004d0309401c50b1001003200810554079051004110a40c0a03820701c2070309403020020035800710326075041c080c91604000c60b03120300d81401c1c0c0715116a0384981b000c50f00d0f04c0c2d1103900f4800001c4002c031810040d0024019000005855604500e40700041340c4001c40e001400035a200410004550001910340c00350349c0c000305141c100f800000050340907000d500c0c6072a041d4080494051101c900000390540310381032490044c0500c035601c0041d1000c80c0300b9008040c0014800304000750055400e42c001c1510803c0152005152003c23110b03101c81101c1e040c100c1100d4994403200814240302c500d008038621840211440102c50404c40c40b862401d51107849254407507003010500c1032100382d031107001852106d014103062010400074500b4009a82d130540c240343c0415040f0010a807694803c0d00d00c090013041c05010546140d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 954340296 1250 954339046 954339053
    0x90c0108070f1404031a0121080a050702031615020c2707090806070c0209150f0f0d120507151406221a0310050f13031106070831 57
    0x410158043c080c0c10600b0440080000e40c0140b03652418400800661700c2035040c0017134007180940941010011304000c1c030a00020030345120465107040c41a06066070785800c81e201090605018501d0001e210140b4900040c0545911402105580480d400c0d00c0e0389140d00c00401c0400000d0300060f0300a03c0d0388609213003146a10b64200b6801c4105403c00c0400c299843d2680d81c0b50a408440c0310380010403060501c0e08508201d2407c54104500499201d01002d060001c540e400481071035280c4649017550b1810083d480b0103811003011a00002495950703a4400006001e50380300910440d403140b43d0360081e154001c0c2d00c0c0320341d001d072142c2c0302040111911501c0800459a04201810198414804142156031000c1c8107031010f500d45e4900e04000c1d460441c00309810b201c4a03014203040207003403800300f005090003420403aa20258010098942015a0900700c0c2c1200511640c0b14161044509100380302e6003048001c1c0c4500d00310310f010b800984207030629400b14440c03141c002d80001d0f202c01c15030002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 954341546 1250 954340296 954340307
    0x9020315040b01110615010908010b031216080c0d0e060c0706050703171602070f0b0702130b0907110601050d1a04060f0207080903010b03120403060b0409060212090c0108070f 77
    0xd0400500d4981100400c010711241485c03010b0b588100c160003205a0144196000b04205000744500e200801921a11030082a1110301d4801084446040014001142c442c0f82d06816000c2d50000000c40d140c48c01d0080d07259880c105400040d02103040c9051101c52480c100e01122103d42140001e010700618000c0c007990a900080c46c124140b100c0310f880c0c00806401511214400c06e0980040105164490170281c01d101064000120384009106c050000d44418030895032480c4c2d0644014500c04180340c04c0000505c011480c1e0303907000f6807140a01408c2035100102041102c01c91085d1a070507640e0780304200c418005040000c00e0590708030200f5001c0c079040d141c281c0d80a07011300800310f0240c146a59410481e40203a008440301d0001040e41c0215003424498a100c40406400034950075000f41306034409401903210007000300c0d0316140001c02d20344840e040b5151a03540b20380159140c01c0b09280501400f80226607081c0a0b10403206942119841361a9050003040d450702d400d00040c0d281c4100301e60 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 954342796 1250 954341546 954341561
    0x605040515101223190218060d060b030f04060608030307120203091005100314010c081f03020a1202090601140a03020711030303090a12050405130f0f0504050708070902031504 77
    0x4160780c3c0c1c14078212030301c400720420050001025000d0080c0340c0302804e441e45c2c10850001c2c100e028818001c5003882c054410303040105000441d403494031996000c1c00c031070240160783c226115902012040c0f0803280000c0421074001e910888013805425121510140d4074001103e208001402c8150407515484003030740111340001c07964040c0c51600803d1a41d4800740c4400f030390042e0148a17000c0c420818055000c40400c201c22003035000b8080c0c1c7c200b003c8000d02400300030345865001c5010031410b004588100380031000940e40a8a000c1c811a9500c1c40011030400c440c00903030059038850001003840d0312a24465440d25249880c040c100701d41c0c0c7c1d008400a400c40c400498811f030300d004d00c0a0300c0340d80410255110700d40d214024601d601c014503003890307007440e50340401c03040c04001d100600803580d842c08031031003583c481e420010f510032038140703054060009080303102074030382c80d1005100505c030000c1105c40a9600c0c0e10100d13a400d65540f011501244400c0340c1101007500c10121807a840d1505400118 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 954344046 1250 954342796 954342827
    0x606111b01031a120d120e0705061605060f0615090306010b03090a0f080d0c0906020733200c09010504020d0605060a12050601092301120f060504051510 67
    0xa100d44a0390204840d4640e000345130340145d10401076107010341c6d4030a0500c1400d002c035031001e2068600d282411a0b43e0244d5000d414800c07580400c02000d2542e0401d241400d00e40c12404895060601c041c803070310803080030f13500c00e4051740590903101514010101111804c0e00098000c100d143c1c43d141c40207040744c00190018501d4094520f252022401c80f05001903800e0062450594a0305902000007c41d00319440200c28001002020407030361f600440c3c000304684c00d0184d01d50a05840c24201d03407078040e008007650217090030480300c09105d40c1e0103a01000c01d8100c1000d00d1003c0b48140031281d549a0401d202c260340714080314018400741c18a83c0140c01c0a00c0d5521011554646440004410f9085202010f002a07459040c800d07108100d8020705070020000c0c04e15a4020b4280340c9000300c0d210080d079984021450400080e2281d1f40f1819900050880c400c0e0700700888811901a0b60182c54103106440c401c40c103010103c2c10741c420f802202014110001c000f07880041180c00305890b80e030b0a010308103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 954345296 1250 954344046 954344081
    0x206070f110d050d2f030603070906151106160c020402090604030b0915070c0210111f1a0d031101060f0f06030518101805030d0606111b0103 62
    0x20075245410020a00b07054125118581c60324400c0714a681101c070036a841c40ca8040360300c10920501c15080603820f48501c0b80d0048903940e0794840380401d1a020140e400302e035007075140c09000222210160201d40200d0341c50380c0c0760095401e12510b0a0360b610000d032906650740c03070642d140582c61802100180e01151002e40003500b02201d440024040350000c1d8826500814040100104a80180040071402485178203100c8541400e210013018504070034802405810484102d644480c0900b001e43c4a09283c0d030700312030030180340c5051139024000048111a200e400d00207401180e041016200c1451400a0003540500c0419207041360306c40d040d00c505510b15582c420000c03410301c2d4200c0e003107006400c96030100100b1500c0c00d20000d048400050901d40c0c07070640954415a08100803e548044040889006c50707424004480301001a458403070050151000180703240d00d005203500004c0881d20203031181207400303210b40b198988175101803d03402070305032901401e0034140d8080d5010700f19445060402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 954346546 1250 954345296 954345317
    0x919180b16120c05040f0603050f01050d14060412031505150703170106050711043c1a030609030403030f080a0207060e0a02040b010c11100c052a0a03030206070f 71
    0x408080f610602240302c001000001d050001640e8100100000c00983c6000c10017484c06a403130001148040c054075100300c0d1b540e0b00140c1846581041108a404070105890203400c251a0074000310040c01d8a480c0802d08200921014208014000045400c0034102c00316190f00500c100713140d0340c4444011018402421a416009590700181c0d0340600310a844e02980c42c0b080307040808041078405803840c8102d04107521111040c034820f613203402078040030030302c005c401001c3c011140c04a0419445210014540f000b141c07642c0d441100e061081e428145c082d5a0640c41c2c680119403a0701c20703400094042920140703c1c0340b60610401c2d0341607000c114001e0040c1408560340d038000903078007001941402644004669015480d2510038020401400d0901001180b11a59000a165038240b2030301d1241140062541a013070282e000e800c46c0381e40c0001519810041007e00c03c0c0c041c4c00203110942144a000441800e60070184020000e494041e00144000da64248003100d401c40c60980300820007014204 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 954347796 1250 954346546 954346577
    0xe0f0108061c0b041103060a110d0f06150c0218070c110f150d0e072d12080c01050108030708040e0619270902010c080f090919180b16 59
    0x3d50740d008501c0303507540b803501e20407181c1014500304015140d8002503180911004032031814004450b441111000c02048203003450704600010311a5a000c000640308940d84000c4003940030500d5081f140c82201e0200c0941c00076002041e810360125198408107041000c0480030614040b00c42d120404d004040700c218112103004100e07032101111905032402d4011401810b006c04a000e01d001560030200100512490560490610700c2e8412031004184002428076428005c4041408064507205513004180c4049141c40d0508d68802000a00700d0352a05d00049208500402150803994001d1252402e241c105103021041c20005051103901400c03c00800c500313040c0c5041e22030700030b05440758004184a1648115090b00000200f4214101d18200c80000181e8000a68080c400e422111803505c4845400c0c08010b1403251a26082d0301049800070041d0142c000101008036041190b42400303092041c108525514030f03441001000c2d2980c61000520104500d40c034007010780d00500e071090b2980d12080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 954349046 1250 954347796 954347813
    0xc030a0212070b0a030c120506010f031a0402070302031b30070204050405010219020c060403081308070806190209130c0224090c060f090906040608060a0504030e0f0108061c 76
    0x15401000c03030b81b41c01100318021303080040c0c01c01c8500014410300c020b28000000030047d1018458500030715540d0308522501c101d10002c41d010403c0090011942d03011a030401035520382000c010341e9180900154008816080460a054484d01c841245403105001d8115943c1c90039415107002c411480c140302d4003015940b607000301070050340180700050b510889000d004104003044413076170095610030628030095455400450f02125040144c0743c1d00c2d005a4904003e00f01082c1d480383c5800c0c403e250021854800c080740c0c080c05024072036030b403c5420281080901c281d0080d03030b07a5154000103400d00c85480d11b0198101038103ca950384140c031140d103d80d183d507560203401020242850303800340d420040b40c00c00400c480f2440030fa044030081e00b070102c0c114254403a071140082107402207084001080040e03c4070f401071406006240e06545079850142e900e1401400122416000070f00850b1090703d00c0d00340250f800e510900d06079940500c6949074800d000840040764070290401d00c141c0c03110340219080d031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 954350296 1250 954349046 954349057
    0x20607060f050a05060109060206062704060e01140c1b122a0309090a090c030204111e0a020705150702040c05030a11041212200a020a080c030a0212070b 67
    0x2000000b01c0342020802542228002040079040c04070f66001070113016000a00e03258044811540c00d43c040003145405a444414803180c131b90005080c20a010030881c070341c1c000c8401d1614400c000c0140000302d0b65241c2d0285800d50701e041003000c040100d0651211a48900c211294216040b21818014181c03003200561003000104140c019840c1c0802003403031030f0803840000d034500c04003d41c2071880d20030000b40f4108025000258050362201080100400c0d05d0800c2c4c021500100200140d0019204000c030350b40c0310f20f4200a8000c5070312501170302d180c0d5003000c4d5030240a03603a0083c420030f400c0100b405a031030020f80d4240c0c44940280304060040e5203500441480b42c04036510706440741441d4220006854400c0650580c540c070a00c000c1c003404a198910f124204d1700074141c6d20102e15602c9040e1040c5a007900c130b039443c5180b602030032441070740f0018070418020310a9800c4103131151f442200c0e5460b60144411141c0c1360300410002d8016203000126403002c2a1440240c918080c0c2d94210b40c005a40403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 954351546 1250 954350296 954350321
    0xf092d0816080304030c1211061b150103150b061c020a120203090624090108010c1101020705210d1b1b02030601050105030703060f0803030421020a0f02060706 70
    0x861018907031000c039151610040c28a1001141400d0856032842e902900318010751200c012402c20b5170040c401c0c6285411541e80e8043c0595541e949400440741003080ca4103000401c6106a4404980740d0b64070103000343c106da41000a4541142d1a203014001030320030710725200c1c0d01000030b01191005200c5040c8045c04807004c104c0069890000410151900d0703075160090b410b841c4103104100340d5440110303180341d020040c083c01701d146080f1103001081d1000020486504500c1e440c0012610540c151b21181c1041c105072128a966140c0001d10340c00d074800c014006003260480c03405821119a0340601c88004070086010504104411790b2140c100c40c1c44089011300e00403405080080180c0090000f01700590440c800d0440342c019030042035031000c06214007410480c0001c0080c080c20320942c040030140c1401c0c02e9603080c80d80d4900300e0594070340003507030141c801c0780801e0400382c1e000d02d9106289104030f4203a005070184c0f40e8141c40c0c00340c115a0a1009a8102c0c03030802680000848900c10382107010302 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 954352796 1250 954351546 954351553
    0xa02061c14090d0e130f05180316060507050f03150f0d020609100302040b0706061a03090d080702150f07020c0306060a05040e07030605041202010c0f092d08 69
    0x91840d10039081d6101c601100400320044000e010040002141c100f580c0203c60400302d050a50000114545001007024181c02501d03200300324458410a07044107001e4810102122012100c020915840c3d1280da0944664118071150b81c00014015070409544801142082030500200055403015a4422692000f01d1411114841c14a01d02090402940803054481d00d01d0090540d000c10303500d00c6209403e51185540301900c40a81d84250100c80150102c4003503151032300c14900c6d000010341028061286001c1e480b680e17545180da40703102a41e1040c10354000a1800300b100010940720280d02070840000c41c020440302d0840031160840003401a0303804040110300d0b207801c400003410800b003918114400d070810307000c0c0540c50f07954901c07610a450003100c00258071560050006e1400301c0641c0010001030802c0d08000900036169907030018140c460f0002d10070f80c11810703412107103c0e00c81082d10000c90140c00061000c0241d11044144040c070034990701140402000284034800c080764844e001652 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 954354046 1250 954352796 954352837
    0x9021f120b032b0f080103080d020c010902060a02070e0604150b0d0f23090a0b15041527060503190305070f05030406020111030f0c070314160b280e0a0206 68
    0x4c0e8460089805440603161041265055039200081482603440c0306045640208111200000c20741c440c0c803080e54014882da0b81c50541080c0a9101c1c1c0c11881410310b00514240013650504080c0100942129405c1c01490007074108400c2d076100360032083c0561009036407044070060031a00e5110708612414480380305100900d180041014600c7d000b01482c03996004405c0840008110300c84a07034021043c1180e40d90208407041c00b150041003540c241103011000c3d510005024001c5c1013140900c08840f610540d44230320046501c00c251079203442100c2e0941c1c44500e0b09003901100341c0e00d40c510588241340036480c000302503c0d404461702c10f001041c4c40300c0d00006010401e194091003040c845a601d280d525084d468480100b81a80800030701440382e54200040f61010103200711326510342d4100820702503807a0f90154005841210507444c045480c3d400c0400403aa4180f1040c04062505c0d110007841c000e0400c0c0d134071100010308040a5050805e125450b04040103a9504016280c40100c0d90305c0c1d100c035070303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 954355296 1250 954354046 954354133
    0x20f0d0513020f041e0609020c06090f0d030b150712020f341802030103150e0307030c15060303020105091606020703060203100b040909021f120b03 65
    0x441016011900360081c030448140180c0300c6112494414004a42c00140c0704898090000480c1420005100030351420342c0200fa07e440b59400b50003108500800c540d0355030b40302105a0754410400d0401e5045a104800300000184290040040600040d080c41280071450400705d0301e58100400071503001440b89000f03505542d0400032042c1103008100145407c3e1620021000c07001480401c00201a030a0190003110948022540000701030038103074000b89000c40e1503800029002808112005039140c040e541101c505801103013681070304c000246280030002d0343c05a80449010000b101c1407241c0c4c00d04480003c0301c600c20f05d0021402a0000318052400c00c40140c1080314201014a40340c0b00a80d0500425a0000711041038951002d00140e0702e072641180c400d0306501e194400042c81400040c0800c002103981c201d202494820ba5141180042e022004615140c1d40b9403030070001103c4100d9205000d11a41000074107100240a61f030b0989910100340c1c9101164007071000c04482a0000800038 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 954356546 1250 954355296 954355301
    0x90b040303021b01141206030a050f1e01111917071206151e02030702090c0c100516180b030c07052b05090102010e060106120b060c0a12050409020f0d 66
    0x845003d181258105c404030300d581004d805940f0215612850141c0010b050b07850802940d81d8298220048488948034000840d90360321440e00404902030300294014251141402482078120001c9000c03400c000e2141e28420280c3c851410840c101301c004001885010407089a09005020702e40c0c84030512070368510700e0307002d80300c040d0311210007500402102e1500740d40c03001d04802a540090b80c81c0e000038580d16422031130343c0542500a980004403000348007410312260018a00d50b1012001d4818a0341701c1412042110b200b1140b0b034099448011050023000d1050060382088030640060040c1562142180910350308211030b0060302490001d88103052283c10459184004000417aa07010f4059212040400c1c1d8a41203101c024054013242c42003041c0c0c000e401c600800c0c1c00300d2080300d85545c0d40f0b03031b001402c00780c0c3c0120781099180f8015404001e42400012115001c0c8100d00800000d0345594504040040c0c030010308081200c04c1c440840c1210131360004052411035089402d440d0865080840c04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 954357796 1250 954356546 954356593
    0xc020c010c080d0506130f020a0e1e0f011101062d1a070602071a1f0f0b03040302070f15120501050f09060609060a05031f06051207090b04030302 64
    0x510485500610000c0c24520469801500c83c1002150a842c1d84001c40c4c00c0e00e510385460442a07041911400e10080e466024003e60360f601d69901002203d40780600603c6882c0d1a42d0740c0d6018a84074a03d1494105a00c001c02240810b1400344003040f004030147e82180c078207400c0b5041d660302400c6410b0315000e00c504414489445c12110401c02882c100b03a42a1503401400b40c10b01c0d0782804a8820148100396060380d2103e500700b20210740500f103a0200c15101c041c1180c980c10483c60b10005030071003000d00c503140000d441c0100710081c88a030804c128900701d40c1004000720214400c800300071480d030510000d100c0082c1001d100c00b90303420601c3c1401809124866080e0307481507140070b004118aa44600701c4400001d81580e5155090f2540d0000c900b4078410b980c0c403190010000101034aa040d400300003117104480c104110600d044000c0700e1705d1500082803080030006030052154100d602510240160840c000d130134400718103580c400c00d000f1640c10030b500c1540980c2005840c1311a18000c0880740f034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 954359046 1250 954357796 954357799
    0x30801080f0d08160e040c0806090a0506130b0a12080705010c020c0a0311040e030a120f020703050703121812020609070305071707030606082a1e03031c0c020c 70
    0x22003480010b1004025550040055a56032120801900901c0c002c419216840c0001390040c41103000c031003406800c0810a60381d05004450800000702c4500480c803429005140c01008460009076a038019005021303440c0c40035500031410b03080002c0c0700001a88211840e1310520815846040d141401421901c144000c0c00a6401044035102180d842d0410241520b1340100d40c1c0040040c3da4001c03400a00b0401e022202ca44000110380b00110340002200c04181c0c00c0081c1840140b00c02d440c030805038080c03000c006000c80c8062194200103801100c0c1c000034810301043c000390100304920000c018414282042e640914540c030103400c201d6041c0301035603000300504c0c014102d1614503610540d94504d2407060608850840380d8503840c4000a0010100460308824203021041d2555049030b11410350783d03075000d4001105407010810144081c55001ca68070000e01c00a00600c0503441808007000c010f40441d80f500081290400d0b52201c2d110304111071540e0f000000314100c15541c080e07d40350340107034900d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 954360296 1250 954359046 954359053
    0x273a02071e03020916110601170d091a070512160204060501030c0804140705190f0e01030308060f0d080c07060206090c0607140109020a0603020a0806060306100804021903030801080f 80
    0x284056154100f4450b00f22017154541011100e83c100e00329200255079001c004503009503400010040a0503a07400741c1c09203014280d038001005d44c20141e031381e50310a114161140c8514503942c1540e0300b00340080c01c00380380920305941c0e03440c400a00780310031540a408072212204a0540301020340c2864400c070005014282001c000d41d02203400064480e01008100612822036001c0741d074041d080c04e200080c0201001742004542040244002c01c441d40c09001c5c0500b41042c226001030003851221010741281c0d015214a10191500720503c03501c41c1401900030303086403c460042d000100c1c050300078000004268040e04905d030030301c14000c0c00d000c8040d202a0956209119040d072642e101401c0741c90159204004c12444001c8401c050701420220310041e5000c60118400240660140c0050114000035a6110300c140e0300d035002c000003030205030340721501f061070442260003c03800b030050382e50020f0004124800c3d4040050398014105150307001240051485001080f078034a00308158044084000c014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 954361546 1250 954360296 954360299
    0x121809060102030d0e100c0e040e070b0f0d11030a020909010f08030a1d030d05040e0105040912080402010905040e0f1c020a0b2508273a02071e 63
    0x3503990046113440b03003105941c0c1041c9006403204210441c142d0401d80b0091129911907030000d800c1c2211601c509028604058145400420208460003540c9466042c00c0c10a00200c41946035500550b48142c1041c0e034401c0c1805080d00e8440245100c4c48032007001507502c000000a020140303034180d00500a45c04561400e00070f40c0c3c03010060b201400c44901c1c01a0b0400a2146054041c0d00d0100c103494150044a06031a00365901000500542d10801d10328003080c1daa40c801d2000b162a140d4000e88205c00851a003d00c007841495115000742c014900110352680758000181222840c00c0c4080f5598049192440071010070b220206004c100001402a40d018100001e501d8600b80180108407401407000500e51202c803445074184466051114085103019010103014003600303a40d603c00c01040028042d403a048100080e42e241d2090301d019040a0705141c0c901d10348401548512103040c0c52040311a02c181080b00503c0b4400d5a196004101040ca8000640801a000c480715880002c01c0e810 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 954362796 1250 954361546 954361549
    0x18030105060901091521030f0c02060406081503071509060504050f0f0102030c01020f07021f09170a153608070f0501020c07080d09030b0c03060a050312180906 70
    0x10341a0444e44102c2d00440d0010103007070100c1050b0743d2504100340c041e10050484a403884c4030b2030410141d80c42a01e842007200c0745070000340c5281d0180c950096200904001c24400f69125240722034004215004a0220560190002c0d0034002c0d80d40084540c0c200d00c40c4052407066200220000802c3c2604045181c036003003001043c803408820058a00682e092162440035034800c204441b0340340c551000031500c4554031b03c81d038540b0340d11103c4180d1052400085030002c4d8080c03000340d0002d4248075219121083d10f40b2035419101d5004496039801070090035081c00110b5800c0380c2e4071440c00380131a40000c180c0d42c0080c511144160340c0750030407402101d032866000c264221901d0040216086003a6640b141c41c9441d100b85101c0841c90700070859400842e141c02c55a0b80010380300c09880c00c0c08180c500c18103c10f002145c030f0160b1792002034440d080c80c07000301c0d8aa240d040021904000060700e02d200654485001c2480c004890402c03105c00c20b00010130030344101e00700f03242405101c0126105000380c06d0080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 954364046 1250 954362796 954362809
    0x30c02040c2d0c0615030b0c0c0735011113030b0f062b0c15030609052703070c080610080c09070e0d02130b010201050f090706080c040806010b1803010506 68
    0x4001030280f59100350400b03a4104170b00d03030348006651000e085161494620311644d4035400020301d801449c0301e40000803071082010522412001c465135030200c4d8946070681e00003006036092016100955036034a9000c4500303000d000500084070b140e0a075401d0b05185140120329550001c0c10b92050090030024050940d0b035802c14a00010519200340541005c551403007043c50030015401400d2a0072000005070407034900c12040800302e2151810000c55947d5440b000c16610102d41c44c0f00f15600d4a98601084800c000607044200c030004103c1e030500449558044250720701c0c0c1c104030389543c0701e1020081d68000544241014010010107444104a0000410b4401d50090301e002c0a12038107280741e411a840c0e0a80e040c40254004150010251030740d5110b40040050743c1059006500300f100050054504541c403d0103000700780c00800d0414a000c40c105ca01d5400981107404090701040006401503040107460301074004043c0c103542d02c4100045054071040305020281c06a41010100002c998524 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 954365296 1250 954364046 954364067
    0xe0a030305070f081c06031b05060d0915110301081c02030703050d09060c0302031f0f1401020a0525060c200102031b2401150507030c02040c2d 63
    0xd070361005800941c548581c10380601c50000318214507080d0659480d91054000b14112401542885400c023192074a81c06011054010181c101d40100700e400082c8880307071702100c051406016949040000302e00c040080d02d00d0b421100c160418080018804007500780070b034030f0035501c03038414000030000303000c0e8040e4a071b015400014040c064080340c202d82e074910b95041484007940c088003c00c809581b80d440507001350801e444031407c00815aa1810494072a640510241c1d45542c03204085545015000600c81042c4852581180120220440040d1003080b542d43d40c1b00c00041e10321480c1d4040001044c01682c2035015204028420480c04041041108101100014403100d20700380c0c0400750042c4e00c4c500c20800e00f988560002110a070b062074011503121140c1000036400301140c9200c80355168281421300500c040e244400c0c000d080d083d402200180300d0765109007414055600d15800040440c0e210f000e014020440c001d4102c83c000c0d6410030b02001d050141e0f00c0514031500d042d14010014101c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 954366546 1250 954365296 954365303
    0x60c0310170d0305100333020a17040c0f030c0302040b0f10110309030703060b0307050301110406120f0203090a02030f0d090605160506070504091a0105070b190612030e0a03030507 79
    0x4e03800071620340c100c1c0501e10405180c21084101031000c16289512090000102c412080c1d84404a000454020781c021140c1c1c45880382d44400310540c4c1c0450b81100701002030803c40340c03400f0b000740c0003c0c8402c0070040b60006601404e01d0b08203691031801404241c07510804054400d50b002104040c95503607000303840200103401e20b08000700c800c050340701515610481c070200d985032180c03a80000c2048200c0d04810109142901075840c020350311818542618041e40c14035940850034841480034a00c07814414010248005001c05c0540d81d101c00d0b40c003241e009480116154008401000950400300b0000c2034210084009000c802d80504c0d000341816600d024910400900160a83c3c41c010b14412415080381c12005641540c200220b000c0c10543c010f00c4dc0c0102242010081800c0858030080c0e0110f50380107840707541c90108182d440d006c0e0080c00401c20a0381d601200c0801281010a02c980d0001e445000da00745000340c81400c015001d082c0b60141e26100d0f00380c001c070510010381c0c00403d40d44070320303031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 954367796 1250 954366546 954366551
    0x11a06030f040321020a0201230c0f19050306041d030910121d06010e042102100501030b191b030207030207030b0f0109060801021219020c060c0310170d03 68
    0x403103250071a50131065105003200110440c0c1070080c00ea18940c01001d0706032031303a00200b061a5102c41d1a0001c8191503651003031100011000800703c07460240181081c1035028541d07032408000c13003c0300507826103201d2600000344000c0308000302c6042034401c038210755803c010444400d10341c00e4070055481c81080d1007030380201aa07401800072217000c3c0044000b42ea031440300503c0400620100c415580710760359400c0c07102d07100d00350000881c08110106640615080b0483c020380f0000070050580441d0031030803440031480740c003c0741d0401001610a042c0a584a400300980714107060101101d41403580110b880030b030b8908a001b401e0400051a50039480c0e0807802c0c0503031644840d0a042c1e040480d16440584080c40c0d1404005410b40e0080382c8a0590780e0307901e020030406448000d41c81c200c0c01011220356031103240c40081480e804c142002928100c0d8178101c09441c0090008038a03040800136940024142e001000344a49101c0e14031003540a886107103288840c2d1409061901e9440364015182d00500d135 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 954369046 1250 954367796 954367801
    0x130c05040b04020403020a0b0c0601061b02011d0d12140a05040e151002010209130605011d040f02040e04260d020f0d0c1e090f090f150305030408011a06030f 69
    0xb1142c2c0c05542c01546c0091102c503000f6529040c9100079401151400b507580181e20002c0381d07540c018405291208134502c810f0020310110350040d94136600c240d51a04000d4200b00080b0b4080d0b45034200c000740b03d4801c0038007800e803204002c4040c0401c55100e10b80841c40409015882e015507019007500c08445000c4045449608c03407440d2800c65600c80d205841d00802d00d4800201c005070150010581d0741e00649903043c00850480170141240c005000d00c5000030719a0040c8000f40b2030b01e801d041c200d508003c000042c19000e002006089030300c55846400d1520395241048140301c0c20107810640300130140740b60ba40c660b8040025003030a20683c4151103040341d0200300a0703400748018041d90029460601c041048201c2c070000500706070582c1c44a55084d40f080301c00000264450f80241040380d440802e401e08207030070b084410002d08038a00b2210001903880011110980c600d040c0d10303004600407030103550b5550a0440c03080c00e64044000d94100103603541004c5146031030324011241c0c028241505440b0300e4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 954370296 1250 954369046 954369049
    0x19051b0d0510051503040c050d1a180f01140c21040c0b0412151401060522061e05030105030c150d060f0f080613060507020a0b011508130c05040b 64
    0x2aa043d00031035006240c0e194441550603441d001140154007445404044981d0307102044481540340000030b00d441c06001b09441e5200117800119000084012540700745403007540c50314038105280c5075404a503911004440070640e81280040e800c0000d02c00c00500c1c04600506020a840040d081309400c282100300007414005229500300140c5403c200703441d9100d640313141514003501c0002d401d41d81d41c0d504000d01d090510403845503241a80d01081c241d45140e107010000d562640064454040348504240100784002901201710b003e0a0300380c1b189600c0240a145c0c460486044d0003541c018484104018880c5a5000812143c011401c49042d00c1e0b0301b60312501000240a421514000e075801e060002c1a2132828541c484140c564103148081c4259075625800d81d40c040a440c4890f80310224510000860ba1503080030380c0c42070090048a2070b030001d6580d00c90132600d0980c0f000b4035000d1061401080c059104440703640001d071400300340b1404d20345500c03540d40f08034017840354074441c658032410b1f810345 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 954371546 1250 954370296 954370321
    0x21306090b0906100807170c090901090c09031b0b1c0e0f0a08090d080a0806041a011b0c0302030d020c18040201020d030905010e0304080a06050609240d080319051b0d05 74
    0x88054447c08400780d090500c1902d4607a040030765118803500000b4004100c00c44d1030311506d6112003640da28a6400380c82d40d1688481c19244000301d9114185214001c03841c3c02d9004010220018400b56001000361540e10400c100d403920030056050b40c00090b10389010840000b84290a5034200c006aa510407007000042c0008298040007444544042078040e40a0741207214503210321029917091010081e44001c0380545500781910300e0220300700d290200440c0c0c402907514140c041c4076000c83d82d4a0b80e00ca80000e0310707200ba450780d440d00682c4100100041e43c00e100004000b412034140e101101410160f001035102e2482100c0c1e24105030766420f480f030900900350041120241c0b200c0075644d465403240c8040d9140c1840d003105907070701814540070374041c0c2003500b0060310816a010350348596249241110240341c41e0b402e900c0703600405032852400414032410086001d00c0503103800881c400801c5503a08240c07100100201030802a0001005600410000300d613070320b40307000c500000c46070303100c0e111142c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 954372796 1250 954371546 954371567
    0xc070848040606020f071a22030c0b0d180f030e030c19091b0219150c0503012c0601030c030e0f030c07090605030d08070c021306090b0906100807 64
    0x50042c205900081c04a40209502184022180a40300030a40b21154074504d40d80742c641c075042c01c0004206100000d00300d084840d12556200c02c1d1003480903520b031990009002690404d001c686000103100c4540001d40c031840010f412030f42d040d81b500d501e50342c8405031205080400038040c4411842c504a503550140003004076402c0042c4280c20114140503107003c514420b0181e16403031807600c0300c02d03004d01144c892110141c80036540104017105003041e0307a0820400b0f509040b940a000f901c00c2c070a829456001e95000108140d40c2d60f0380b298909200302817510101484000e26580c0c0400c01d10305052082505540007000703003000701e00c504200100328020011142145007600441140118446000c401400d01c0c0045808641c0c10940718000c7c0c0040340c142c1d102e102d916511030151a0049405007065540c850224182501d902030560041a001408103e880c1c1e401540c440c4240907801803886070b05e0300048242c2d01101c040c50f18201013844401080c5484040c4400d01000031034080c8184040d11 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 954374046 1250 954372796 954372799
    0xa0608070603021c0e06090c0d0c12051c0206071209020a0501180305100e07050a180906020c2409010b0a03150b060706050601170c070b06150c070848 66
    0x891182c1c22009868080544a50341907000e0300c02421810301c2c01081c0700d0441074000c1294080a40750801c51164403e20030800c03030f02030160001882000d40c371801020741c1000c082d000b030001460046001001d11a81c010302e030b22041d207015610300c00750302e481501d441603e20078284032100c040c5540603241f44010941c0010014868941d54910b03000c503903003000d6010400c510403104003d44600c100140e04000d4003c0080701c2252030003814600387e0700c2c1c02c003d4040340070f5a001842e11160080781410705100240c4444c0d4075201002c400014503040f6952070740b06880400800c40c02c8a040300140102540d0b2002502c2c1f00c80f0740c0ea07460305154050380050004240182003990740d640701d14015016100840c1d655012510b109240c0d24003035055140c96100c0c80c0b80c102098909411640c0b4a0704034040035008036004500ca4040c822203181560061005900f510000c0c60741e18074001e000352520b6684000701d50100811000420b41e007804c244004000c1684885c04040358400e0703030001602044852266 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 954375296 1250 954374046 954374051
    0x102070b0c0102180d030c110a050a17100b010516050f150406050a02040302010806190b0c1f0b0303040e130606030c031509030f0e01050418050f0a0608070603021c 72
    0x70240c610540c001c01a0711101d910b60080e050480040002c502e10340f02010b0041158030000d207000035079409910070300240003440c0f0130b0100d84032004210f030f950a40c1c02c01c484584140c01840c54150080166603d00c10011074140082c41e210f0780000c00500404801c44030447c41c031001e0604019050003501c83c2e50084104880c005084102440d03121881502e00380c03041481e02000c07500c550b4541c0201c40030349806840b00c082c40d82340e032000c0c0402007000c7d500c000313059031840d140800c0c0c021a071801484071241d807400900f40c1d000403540c00301050100c41001c920746494582c1c3d418680c0c4021054904441a0486803001d96403081c2803d45400048071009000500e491800310400c0003c010030344c1a60300a074a0031040405100c454030803640000c0c0c0c003030b0100f035803480d40d0340809200b40d012501d100e03010714080c2e060560341c907000140703101b01c810008005900c900170400c0f8110404e02142d88042c0d20207003406441d14103042039032100760303600442040540002b404c0d044110701c03658064000340450f608 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 954376546 1250 954375296 954375307
    0x603010504241409160f12020913020405010303021b0307180504080d0905030a030605030d090504020a02070302030f0a050c011701030303021e070b0609010b091305072f0601060305240102070b 84
    0x1001d171901c400702180940c40c0f00d000c0340480c0ba000680c02e80b0041d9035440400012051140c1c00300424070f40010890303ca4942685541001030b11140141c90095200e50010b245942c1c2c4a40710014180b074100005000ba440400c00b00005211601d454082d6485800f002034551103e00f050003e40c40345c010304082503400c0c01c00003410844000010300f1101800da804202d0280c944c0105030b11500e0311800d860003c0c0200c482031020b89007a0340104002e00d224011941c03020b90386d9000c6410100d0b9804246d07035a4100800a006204052041c0e1400d00710901c0c00d4191090a48080030b00c0001c1030201808040e800305000011814043e6903400041c80c8905840d00c40403d840d203c40022003c03215580108400800019060b1000d0203075004054002d10440c00140e510990324000c0000600410401054102c000d11f01d002d4217298400030320200c10404070350108103005600e80300c0103902c2030f000c040c40e0104025488450401d448201c0803026010180b0070142d0300102c0c42c0c9001504000e2403070320700050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 954377796 1250 954376546 954376561
    0x10b18040c17090d08070f210f180c05090c0a08150d050a0c0b0f0703110102130305030c0c19061107170c01032913090b160806030105042414 62
    0x10003c01000d000d5417040440d541e200320468034000f489840070041106804288421500c420f900241e10071000790000750f461341041500207a80a032890840359038032850b600401c0c00715045020300030b4203040d01c00f0486806d0400000d80c039441108000400c010041022500001110806225001c0c000304041811101030800c40c0d120320503080110340f0351191140020303400740e59006482c43d59500804550401c5c03c261002d850300f1000c0d512401065500708124a24402c1c0b000c4418003443c05030300115140c0c0d403410481e40c0307030038003011602e40328100a103088401154000000000d81e01203151000500a190f0310f01c3e89440002e4001100c00c07100c03c1300a2200c2078001829203000c1401743e8050005907000c1417140c0d44442403a20042414102d00082d034003508181188012008220800180400303aa4650820880c019242d0300d401c0c0450035101c81105074030950b02c5030441d008030300810160400795a200c42c60754640007a006090340c40e40403108440c0890384131740c01164101100303400900e001031703 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 954379046 1250 954377796 954377803
    0x40c0906030c140f310c030e120a0e211e10090503030a091104020a0c0b010b0405090a1d010c0203370806120708030d0606110a02091306050f061908030409020d1b0215010b18040c1709 80
    0x500dc0c40700d02c1008a1081c207032800f03008131b15105403c14061407458582020300d8001e070808071415102d0880c0d903d031461840c1c43c0c0d48020a105040e40d61a8895107980303180030405504103034808813141105010900150340c64404461304008050800200300e44140e2100c80c096030b079100f1420007546000c4401e00300036004401080ba0000403171a4800c0d0aa0071544d06a0401d040c2c40070905250021800341c3c50716016040458022a00511a010059050007201c1c82c24141e5005400a41c00200c0e0780c2d04c04040314060034019002da401d00001501c500e2146a9942c0080500603204100450105030b04030922294403000580005061140d890000c0840c0c2284205030340d5036000d9102d40d45040c2c40101504040f0007a2401d600c061442d00c4d00d840a8040650802c1813050360342035035010901411b261152660702032001c142c016110315040c0c0342211ba00d4900c1640700400101c0100100340e21801a82c0a060015900302d0300081c2c01c82d9210412160011400c1211400700841c00a0004091002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 954380296 1250 954379046 954379093
    0x40903030506090601020f15071103030405030a080105010905031c57060e0c04140601030606051809040c0906030c140f310c030e120a0e21 61
    0x19500003e054440c1d000480e660f21419245a61540204c0100c0545040045401e604461603240082d2200c0201c80030504651080e10110303096800025681c5246420030092401807000b42460101d6628040110752a1400c102c900781d0340108418035a8400c070700481c5010003100701d80140e52180c0e0503401564940890000240038030b0040c101c80750844004410b50600c601410725503080401500740d5440004e410a02c813440c6080c01071403071030030380ca48803441030235119940f010340c08485017803203400541140c03256000242082010090304941d2142c450460240c5002514842503540e030340c0c144400440da03503401c4850310074100070b400400d2140741c81d51141070310b866a42800c11810000100500400b02c24083c0d6080700c504040390960f030100d01658040200300041c000840300402d05a80d0031100054050408a5038a120b03004002e8001c00540c0d002d034001020b000d250444017000a017011680001035440741c40301140034003c0d0300300390348855410b010f010304482a07840c0f550300581c0c06076240c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 954381546 1250 954380296 954380299
    0x30a020a03030e070501170c0702040f09020123040b0f0c240f0402030703060b06280e0301060b0d020f0415031e15150e1827250302040903030506 64
    0x40076410343c41d8080c04a815000c44005071240040c0481034015107140c808024015010404140300308000750310b842c00707150150041d0150002e08041e544c8000350400e80b81500c44c0031070010100500042040e01c1c0207c1b02911118907500f0385070b400009031040144106010030040740240c4802818010a5854030000140030b42c42c603100d2540c2e40031000856480880d8043d6260f4042d002c104042161680300954003a00684494900503501c0d0b2188480098590405010012000c000b1030340d84e030002c1c0405001c0c030120700a2200314030b024200c0025009000c00f00c3ca14a900040172a0098480c404030382c002d103004401c12210307040103c0c0190050903030031a2a052003091301d420706050381ca10b2080114007440f143c0a03881940c10326201c80084403280710800e00307101e41078090342d0a55440c500c1e0a40c1c5440d03202d03451401e034506154400030007180716182003861210352000005036500422003c001d1881c1107548000200d40743d004404442c00d9900c00394000d4684074070a4140340d8541c0003944107060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 954382796 1250 954381546 954381551
    0x27050105010303140c30160c082b09080d03020418020405100c023d0509103005060f0f15030408040f1205070e06060306061308030a020a0303 62
    0x81075000d40303903031140e00c08040e841c1c6c0142005040403071320030080c00005c0a462101c5c01910340b01c101991a03e41c0000f0b10317001d491040000f41c100b0850f04040c0312010702000c402a0452000a2607481281e040313802192110444006440044030701c506c4081c0000c011074801c44a9070035070341074058002c1d440b82c0200004501914900707000c0c0e4940b80221001c40d40041c000141c0d211040c5000c035480e21502030304a90045a8000304000d098000c176483c50030038884408648144c400010740750603502c62114180c148101845002c0c26680c40c20140061181d050802061b01d02c141c84030b40d4000c1503102c4c4c15803002003080c1c2c2080174201880d40001e100c1d51091350f505101200380390401101003591300d9070681c0180910b10001507001000c002c0c0d908184501d0160f400c180d00c405003013000407055007080d0340e441c0e400a031318010700104210440c0141b80d04441d44405081140210314036201c0106068043c22001685030b403c140c0c0890341c1401000c01c01e00303903900d030035148800a444040030407058000a0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 954384046 1250 954382796 954382817
    0x9091f06120b060607050d2a08030a0203090f010f380907110a0c14010c0519150e03030601120b09160c020d150e070f06030e030418020d0f050f070327050105010303 72
    0xd8880300c82c0203507400032740362411a601d010200b400f80d40020200005801413201b00804030100b4043c0c070349070610414010a0704190341180310b2018901b601500c815040850b140d85c0314544030300c00e642c004d1800761841c0c0c00300c1d5111182030f40c180342e014012900600c039410000052000b84040c05040c1e9002441d2001c201ea00540110751240c6030220160444e0016404440301c01200c1d0301c15181140704a2400c980c003400a000001201c0b84802e41200c240c1000081210640e84001c814141c907640030010800c07006075101150700c13528000c2a20417030f41050302c00340e82081d020342e041c1700d03560781d0050104608030000c0c5040c00c41425034540c64101c00703083c40540241040301241da030041d11070703940c22103041620b07044040380501110300c2c01c92100c0c002040045850004e91180c100125142e000140e903544840c0c0c05402200c00d941710002c10245040140007046a040c0010758024055140115646102050318146088883d19400300e0b030151030545001c100c411341045048034002d4480740c4086 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 954385296 1250 954384046 954384107
    0x821011703122e030804080607050403050c13020405121507020d08060d02041d060115050c03090121091a01080703051507090509091f06120b060607050d 67
    0x340104a0500400d0309044002044210041e40054034503903200c03101103c10f01c0340d074902d40da42151900240c5007030800040c00d2040740703010060700d50404158500145821310b0364580c0758561001003200381c41403480c40709200a54046806039000340400501c4541c07030103490b490040d0b4070b18148001c444144d081600044102e400410a0340d01199280c0703c0440319662081004a1000d150b00c080f0782c030a82c0c40710070034042c40741c25124401c0349000f41c00a00c55541810004c1e4000664141041c041180030400b03081401d0001c820382e0744224080c00c140240c610078801d03400c1c0403142a0350b4407402e240340401c001c051000c0724403501010300b40460300c94440e90f202c2c0c00c0192a55098000074100e5400846440b181150b0010081d6101105140c080c0700d05484000083c00c0319002d5842d81d41d0341d805000c01c0c151400310100d48000d9249907000400c4814130703099203148808105000503042d04031102c009000c50300c400007142d8bd9143c1c03003420b440d01c903505a100600038424080120401d121401808004d9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 954386546 1250 954385296 954385303
    0xf06090c0703030216060203070f02070b04060905060a030f020c1b1203312c25050909040b01080706020309030a080306180a1a0102030906070b0408210117 68
    0x2000101100d61800744682c400b9000303035000c80310000c03007442500b032503a0200e540b501c0514000c0000c1e543e000f0224590340c0c4002e00d42502c5800c00044401c08000821509070132500c0c440803244150b500ea03848240c554801c0c2c004101c040d60381a0180d00020305070740091700c08a124142e00703500d60328100c007501d031038003c1c0700501d5200c02c004d495980c4100201c0202040d075080d00076403110000c01502c0a030035095811408101d81e540445e07800900013580d03800c1c0d00c5030990441154420f0b844421001e161480d8031109500114610b0300f00ba41d514040c5400240c03054044850f1a58040d00c0c1c031000703041c94545000c0303c08091042c032409005810011900c1d038804421100340c070794000d00030005203040e0740352011250f002801155104910145000314299020b9105204041d10074000414548107010891490317400616541150002c00c906030443d17482c0c2065401464211074114840d0307803103140202e0b983c4030b521003599640d000324207444000c00321980d211b030694045143d40b15449103002d400d2580d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 954387796 1250 954386546 954386551
    0x120c10060b180a03080d0903030c030c0c1211032d0403050a02061b01090501050708151804050328030614062b11040f050d0b07111c080f0609 62
    0x3058010010740b5141032074640900c081a6004089564080e500c0c0e0b5607051503404801080c22031601c0700481d90915402d4851258600b650742014000710003046002880511507200c000e0110f42a080c400142600c9610710314004046402126075030354990300051036101090103851444242400b5468000441906980c1140d03840f1004007007128080c1e0800100740c200d0600004105001c100b0b01d60407080134021644850b0103100001043d06055000074160640107020401c0340000c603110f01711980f12400c02d0002103041030b01c80301d9103454628100381103114440c0c03520000c00c41d196500000340d001e50304204c21028591001c008040d82c5180340021900c080c40a00d60205081c4071480301c2d18550070f0620501011a12840280551800028112202c6054080e0500304c0401c0611007040300320350000180408a50103486c42c1b003165900501100001e00c40d00030400c0002443d002c0c0701c01001914002c00022081035106910284000c0142c0422101d03204124041c40201d615801c05d40802070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 954389046 1250 954387796 954387809
    0x4050c01090e1b07080409052703160507030606030c1728060f15050a1a0f0d090503030f0919120c0203030d020d0507230315060705120c1006 62
    0x19441e0b43d07158a40e1241c5500b901d01984680320800c02e000005625000030000340403603501c00151402c09800515070140a0315820140441d031310042001c14030000203507918040180780700c0ca040011450070700d05040080d4401005281000b8001c020412402c020740305a840c0595000c01c0c0c201c0703203124a5a2284a80501030141d680d00b03400c1c1d103000c1a00e0001050250181401284e003106aaa01e48201c503c00e00c140d01c414000c806042c003c51030302e450500010051062560380100b00c0001e154454421050207141c00070001503807055074159900800031180c0c01c40203403a00c0785060040500420300031259074900e400b40c801520400c028408404220030782000889855401c0000d0903643d2002081040e6070511062020b045451038500040c2245406090082039504003100041c00c1024070244d0f800001c0c0c460340040d038030008002e0a890b030088101240790007004042d40070440394812004090664003803542d140d004500340200900403848154122100d03030800f800c968085031094060503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 954390296 1250 954389046 954389069
    0xe180910060f032a08060901110c0303011205100501080138010f0302040918020102060601080f150402040b0c010e3c1207030e041514101b05010504050c0109 69
    0xa0002c030f40c00301580a02c0004d5000080411a0501c10a441c0c000d002c3e805480154001c00811012010038003c1a05105085a11070b00b8102e4005c117040c0c903408140a200703000d202e4640481c09115040009400e440002c5d4401c000e42c0d42c55181c45801390600715500b241880d0081211021a1a03103000e40d0f58070b00c1c0d0f400c0c00308881e11352400110390681d003601c0621304150b020300c000704090440b4802e0104402c071141d82403642944901c00a030408200a00c8141071001480400c1021500003c110340d109500803900701e109510070000034020300403600820200c501c0891301c0c1000e014154400e14103101c01c8070072144a2104c1518011104951900c20440403484081840c0580c40c04c034407000070521110f041c1c440016102c3c2000f1820303005864103400083c1140b005292903b0603100e003401e01800325072a036040d0ba081910407030181c01d11a40241c090341543d03130104582440381000400041d14145d010070701d038000d401e01c54041d260a032801d80d400c0c040c20002c020300b50b004002c52412100c0401e201c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 954391546 1250 954390296 954390299
    0x804062702010c081b1e030307080a0905031c05060922020915060703090303030506040501032a090f020409140f0610120203160806030a020a0b0a0e180910060f 70
    0x4640b00c2880f107004a03807007075050000e1a5800d008003030703001c081c81226004101c4104c034020344000d90000040ba0000540080051006650b4021034036035000305590404281c0400c245085869440b807100c4078102454050402000c040480d001680103000c112000055600c44001d217201070155510782140015054000400604000d0b40d4940d0000031108001054007100b0080340781540300b840c0880000d81c20440902c00c15030175200f1250006001c3d5001c00096055990316030590b0b5104000d080765446880b940500383c0400031055020300224181400500300e680c0d4060040d401034010000c01da801c0907208000100c005c1961392048074243c2004c8265151541407110003c09030314598104820328a4603900e0071030780d00046015403499001621400d000741002001800c024200503c00c4d040541d82ca80582e4a903c420019145001d4106031ba40c030500d201580c00658180c0c0a9802221520201a110b00b12a0701a4414064902038034010b010340d2640e18100c3d00280602c003820958041c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 954392796 1250 954391546 954391549
    0x70b070e040c090806070e1c050d1e02070b0f16050f07060c020f090c0d020304030e1c05060f0612100c0e0d08030106030c050c030c011a01021212040c0e070804062702 73
    0x1f01c40a41c2a80640900181c0c40000300c683c40f4004046411ba8180d4844030000d54021390000c0050450680d44a08c40b00d0035500500c02526030b607907403280280208010441512a502d01d0b001c0b00e031208a0840341d003240c282070b0f01d041929609a40040c4140340150480050303180d0003070068040940c3d0041680300c0d078207018020052054006840c0c0b016030f030001e10800544035064401980264040d484000d848850750040001100d42d4000031010080d4040c095000101e000581c1500b24180101c9071850f40e03610710101e0b001d02000504562584526036001c00505240d48c00912220f240d541d82c1075801300e01a05000c0740101c1c41c50001d00d410420801000b9052080d4498000551180740c0640f070a080384821a265412044441149035500d43c82c26000c21500ca0303541510003400c1c0060040781d03031031060303841e03060180b14101c0e401c44482078005010000c0b4030f003513040a02140a0640a0750504076001094481c0c1258201d481360318102c106c030094031300e4200ca518051030342c01d1140010700c556070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 954394046 1250 954392796 954392807
    0x16080c0f04020f040305070b0c191a07111204180605060a0309060b0d050c0102211b0a14030307110c0604061b020306280212011208070b070e040c09080607 68
    0x80c00b181030f80c1c14031020001842c1030000c0d0004159103910b454451142030741c81410140e008546200f12010050014005100402114000d44032184210915511094252a05031100070801264040d5204000f8500301e410094820f13900100301d00b440f003421700c048460448045000d11944800b0600c1540740843c4240c0041e141c841c803c003004a105a113540105600c0180864100c980740c1003100000d0705564100311202000841c905d409849050b200c16030802e034440c1c1c550071009003c2d810880100701000700014416158044060320f40c030180ea07003000d0749a030020303101c02001401d031f1f076880c90280e000044c1c2c1d980d0304140141840c3c034140c074242cbd042e245030340482c11104503440a4130714034025a80a22a69101d424003403a038a0800301580400100e400d80c200301049210f02c180021010919600800c9041d40e480d840c08c0c042800c09030400603000e015000002700b40a07107000800c0209544894242004102524103012541400000707440c1e8000314000e0784096845100041c9449201c3c2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 954395296 1250 954394046 954394057
    0x301050d03110d120e07140d03050405100c03090b030705030705090d0f0303050703180807030f021005070e0a0902032e08010608030a110a031e0e04050916080c0f0402 73
    0x381454900c42400a41440c1880a2000690f0200340364007000500f08030f490080c084640300d00000740401e2400c020600095851141050307000e850702013000717001c040c007d008075005044010404005100c220070010200118003004a0008406c22000600380744804196401420107442c2d02d8110f0ba00d0035800ca80980111a282e80c0c041c562500ca2004100e00c00181c02d0340c2c034003e5902240c145404800030702aa03031a4100c2d180408828140b01c000b0030b804000303803403d00f541132a01e020740c030718480003c0749040b9905a2117200c0c9484d0400703001209030022101701c514201130301c41502440d03642c02003504a0104941c0750003140301c060b100c1060341884030080c070f81012140070b20001c0103440324030301e41c21100590400c03c640c0d031000483c916441e030050482e40740c103101000203000014103554000c0030a041c180e050314003030b2070b066159003141d40a81c8005500341e5001d0010030562915804041c1e55110b1b0340f075442d41c2da601c90381010070103440204425500f581d0251020a40645d98402d00000390b105 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 954396546 1250 954395296 954395303
    0x50303060621071e02030f0f030a091e030f030504020603060409140a08041a040f090f0b0d11040e07080a0209060a0e1f0b04032018390301050d 63
    0xa6030b020381c010900914400e8010030080d924400428807400008107403180d40059582954004e00035151a904410122070307424074200b5055460740c5400340258003400c12510f005016200a181c3d2400402d40286207095050182e1354500421054010079001c4643c1036078003941050042000500c1810240c00440031144a240d102da11074921b50506d500b096484003044030000790020f000c00c030045407400450496286154520301d054034058120092083c42d01c18051620b4485d403c04404030901e07840a400c03140c0140500400910b0340c0b83c0984c642c2c1c924810244a280b41c0804102c0074080041c04c03c2c15900c00e131004000c08420340d0200324036610010f080c580d02c022280000314000c0c001d001c1780d90084518400440c0444c035110540c1040c48604d4201d120340f10000c2c8000c00200749061440600d0b0311800640c07500091000c00400c1d480701c141c44080c6807160300c03401485000d9403150326148621122803600c05500030100d080407050300d180f807200c00031103005100500151501d100403c000d03911 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 954397796 1250 954396546 954396577
    0x406060f080709030b061c1202010b0f090601210f060902070b0a1521060905061b0a05040506031e070f030e01090c05011404090e0c10020c01020d030c0c0c030b06030c0d0503030606 79
    0xb2903a40c1285100808e00d540c006075100c14041c082400e181441c104050300454204200f840d02c0c00000f80400c1360b003028001aa004410f045c0c80290182d0712288000140c144140986070b12455244080d62104200701e901d00123110014a05640510515038001c2100c544200258608202d5041d1040d11000162006060068030400600700c1c0c804d081e0f403680300e600a41030a18040003408000400120424201c500401202c2043c0c0e41c844111000c3e0340c0100c414a84075180ca443c0f07040e5215442c4035940501624030140241c01e03412845400044020781e500f84107945141e43c8460a07035100c40001000e8443d104414081503025100c1d403058204810b00d080d040c40d94580f0100141c80080110010b140c002035140380340b9040102111034806440e000800340006e41500003903413845a04001c000705075950384410300ca42e00ca642140e103c00e0304103d0020030b0644900f080350307144606445c054440e201c0c10f011603a007800d0042080079825005006507065650b02010302a059200e0502c0b42105c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 954399046 1250 954397796 954397849
    0x315060d15090603050d050304080a1b02031e010b0d050703080d021911010c1b170c0318040f05040507060804050109150509012004180b0406060f080709030b06 70
    0x20120503280040c008214080b40c242d00d54240b150034003450741451b0013004000c20820010480407404c54107541002d00d00b40f4110b404090700502c03100c004560083d454020106007202038901e400e5242d2078500403400810121501c0f02c100000400907000003401078002030f108001054030380018100030402020054900240c11200d280c02d051203204420126810205200c2c03100404d00ca2307001c840d81c4a003407041c0080ba460080e0381c042c0244007002441e004203a00b00c00000d10124041d503003102d040a0451352103080704202d00030380034203049145019900d00b05800d0f03d400300324020340d4011074028015026442c1055021a144180144180c036150340700e0031203030300003034081d0300814840e000c0c00750005250610008050940780b140201d50202030f074615114841d016044101e4040301da1541c904910450b038540f2580140603410710040d4030a280c0840061099044071303500c41030314202e070399882d03607551421026500c407031041c00007070035030700100002032091700344840d5008a41c3c0410b1210311100c0f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 954400296 1250 954399046 954399071
    0x30e07030804060c2f120a0803010f06020f030a090b0304030c080f0324010e0402070c150c0302210a031d1b1003051e04170c010203100b0315060d 64
    0x15401070f4003103000035203022100700502500c0c1d0300c54000040905200c0c0700c0b090090044941641d0070a1000e032185400706043c007005501040080c8003158410100c50b140e40c1e6481440780e19512038454903015000e1654003100b44517011040711260781c0b9a03200c0408480c100140d80e0000c0d0001041141800314030011320010542c10790162a415248143d220740e40d05d00001800d05010302c0340c051141e501c282c040300884aa8120b003d440c82888152001a151301060a00b02020b650346e0b8001c03c200c0d200c0040b03070a00d0707960142101c41081d010b6001c4038000440c50121900070100b50454800c141014001038035058802d40200d00c0d80c060489402d100c0590000e078050414a4480244088102510f01c0750740301d040036640c24019001d6800c0c100820310f084440048480300c40d050003d01c02c94803a000800704400d94000c5040c2391360780412146c844420070740f154001c0d842510300f14403803040c050303002464568140859205142400344c4440603c00d5000348481c2c1d4120f00343c1c500700540c6981090301c4a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 954401546 1250 954400296 954400313
    0x8090f060103060606030c05070b040b070509041a0f0a03030903020d0303090818030f12030112020a0f06030b130b06090904150207080904052a0c01020f073f030e0703 73
    0x103103003e003000107000c5240210203000c581d03501b0400d0051000902c07091001c81c1444500e140d015806c81d20f0b01d0000c0d5261881100d03c0e100b010151170b8000c0c41c00204400306030070b08c466454100f900b581c0e05040081100c0402000c040c00313100081c00200902c10601c014140701816034000d902ca8100842e40550b15958a0f06503080b03441a252020003403d48415240b41c02c0000030358900740d2401400801101c41040c0c0c49511050003055401c41004506000f1501c031141104004c040300ca51b00d0343c503585c940200401070100b0001c041d105604040c2030040d2010f0178841c0b0500032500600300e5180002c3c202c1403103003298000b4000d44d11080f407048007428102503400104002881f900d2483d5640c12640708000840d000641844030207500d42c1400507410505e008001c0100121040158645081020140c0a4132410250242c401c002082d40e40410506032948440c41d45003205580c84084258044010010310342110b00d041100d9208601d00d0302c5c0641d1000e540046900161412951a0303100d60b140e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 954402796 1250 954401546 954401549
    0x60917030a0b09010e161d09010e011a120103060506040603170408061005030c1e03010603210f080a0207110d210c08040303080c070b04110f0603090a0308090f0601 72
    0x407640c54481c680d006160000700240034086240300300d4a5401c00e00e40c6040b0801d0058600310511550880c11898984403c0710a440c0c44001080306000c1e603101d155010300d510f428032034032140160006241e540d44204100b5070b42c0c3c0036418100c1785560fa28503221400a00b80107001c40ba001580ea80300807002c1185c0b410002440b03111041e089980709e01c3c00060a19044000701140c0105144602c103004998002c42c11001d5400d04a9040b8010480e09060105030200103000c140c1c550710740b260001c10022002603418140f035014403441d030003141107107050700c00b46801c20b00000011600070006000309801d40c05480c40c01e004005025100c06414042550342000807001c2d14407800700c5145c0c0c0c020050581e4502401b05c210328005c0700441c40b50352155a28055800001c09000090f0001505018032030260340d1240e41180761203180781000c0c10440030f0381c500a20110b0082c40780c0a0702c4d03020b509240c8120b0b8040c20109008004000154604460b860000b41c912400c0d4001d0324041c500c0d00500304226070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 954404046 1250 954402796 954402811
    0x303122d0203090f060f0408090102030c070603091a06010905090a1118100c0b0f0a0f1a010206070203070b01030807020f100207091b210b15190302040b0706091703 72
    0x6a49040c101000f80c680040441c240511703a0216007008500300b00c81b50200d400c1540007c015440d42900c20042c0d0079405085503c861902c00e10710000380060307064022a0055004100481203410860040014030748121070807804281900000c001f1418180d46050b84041c41ca04000b40c041418011881c1d15400b40f850829613a560b08510300c2c0500e0000c0e00700c6070140c1c0782d090203a496a05030b5990102850010f04003014003e1040c0003074070b40f0810f0742020910082c080c2003040000302e4a01034454040c040315046005120384c6c000030f00058000000c0306e00d80340d0400407520061386140c0e580b40f0b0940c00b14800b20703000840380450740703120b444241030000e030a46140c001e4218141403042e58070448901e002070303d000d59232007100c102081d81c12400140c5072014099406109050700000540500707298840107812590085401c0400c011140180a400380c20741591041140c1c1104104c040e40294020035210b07804c200b0901c00040c0b15a44480d1245100340601000181e480f2100b0358590000c481a0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 954405296 1250 954404046 954404051
    0x9060d02070b10031e1e0813080313170f1e01050a090f0201110a0804060309140102031005011d09040f0b0a05090d110304030803010f150201060303122d 67
    0x601c01c02440684490b44800c007022000030326461501e03000201c02ca41660f00150050448036034081c042481034a2419421061045000141511f41401c03540d00200140b0020a41320401080b080404002c603000241007109010070703e42809500d80903c41075054219040c4100355486045180622a006081c4002906201209400036403507080d501d0040c410a009032909166800050000340d02c0081d0903028030b418141142c41c480e6880c44d0941c00d00002e0400e42002c60002000c5605410003025503120300c040e03080c0800600f006500380d0000340c40c5a9000c06040340c1c180a19413185818103517606407000010381306c42c0c0070000306103c4581524265400314216802105114807800210703000040c0010400980c0b9109086030380b1a48501c03004010010b56200c0640428010411f4402460704070040698a503522480c3e80c0360361125110b2540d200d0382300d10548040314010302c90102225010740b030700c400041c11546a60020992501410300300c12812002911848212142d100b03510b03850301c0c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 954406546 1250 954405296 954405307
    0x8070605031909020303030c0d0f0504110a090b03120a140327032a01020d0e1011130e1009020c07060e15070609061e0b0a060c030e090a0209060d02 65
    0x18085121002c1c180c50700c22401d1050001c0180c50000807203070302c05005081e264817024464640b4010b00440041d0550060408040c40140003a114003d00105000ca0354200d00640e1501c0c41c000f075507080340c1c00580c140c0102196a000c0b02c0110000c003103500e141e10b030010702b12310300b015000c0e543c0c2c10030340e00075516080c14000004558180006d050000c0140c03402541805100c2116a42807041c0b100c1018038081550144402240250146c030800d0a11800501070040c0e1036040780d0f41e94100b901288075a505002c03010360090040002c440e1485081c02c1001c1819040810322000d81c2c0025102039030030541c030600081d20225034030280000a03c100081c10040d45401002403099103480380d55849010002e0340e80c0c1d447d451104c00c440410740c1c01076000c12a0301b8107050070700c001c202c41d00d540110021501101c10120304554002c80160402321039081420740c07190780485208081d1403000340440c5194210712400e00d0841c900c90b0b41321030500c2c009403a1418960103c0c00d503802c809200c0d9400d60f00800d8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 954407796 1250 954406546 954406561
    0x30c0b07031229031c260705070303020309070b0a05030a0c03060f030611070f0c0602100c090501110a080414031009050a0f14011107060b04050129040807060503 71
    0x16180701e4400402e8082c000801004082056181521064461000558014000c640b824000381154014010501c81404107002000e091011034400c011449552540d41004000d118001940190480c0e69690308217a00c9981c150001d502c0600f602540b131155410001d2508a00700c010002c001040e6665602d07401c054580c00150b0300c2101400c401e2500f010410310400a0308076158084179049000490351070031030305800100380700340280505041d950418050034821800300c0d200440c2c1c0315900720f5001801003040001240e94041281001072030701041008150308c0758090300812111441583c08816555440d48402e03442540035844010540400c141d1038942404142030300002c0407828415807000c0e584641e12003281c1e4000620014040c8003450501000b62040321040003180007c00c041d103a0402c0815013a0807581d4215034041c28415144403500342801454102c8259810a0010220001d0300916101c100084540b00311414080040e81040401244008100c207840340e80c0d49041c05013 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 954409046 1250 954407796 954407807
    0x1306062102041a0f0d06110d02043b0a0b13330e07050f041206051f060809010b0604170609030f04050913021206070320040e040c030c0b0703 62
    0x40b00004511042e6140c40545458200d000c601344125030a2040d2030892800d42c000344034003d55015401000300320160303000d9081d07000b4419948030001a8083c8041d61820080d420b00080481d0404003010425010404030084448c0c0c0210b5a904041904850b54012034846100c61509a40b40c1e40c8980a4207504000000005503019008040b9001e601c03040c0585000c9403803501c036107484081103400280a00f407146003034840451280030041d96555540c1031040d5a003023075001c160b5100b07140c400480c21000c1c041c0982d04004039400d000a18052034488180ca4418000700360900300e5480351048105a41c2d201d009002800c407056040c3ca0b80c01004c03900301c0c5400e070014807506150f40108002c002c148601c000384c40c2114411038220400c2c0c0d030f802a00d0a440300400e08003e40103071a1f040344030900340c40440d00c0340c81000181e404121589481d24211150301c00d034501c100854500300401e026816010360b48980c0207018054900c0d069551350749605001030b1580c4100e0000301702103000d004265000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 954410296 1250 954409046 954409061
    0x1050d1e06080c0315090106030b0f010f150e0103050403020102160f14030f0313020a03080417060601020102040b0d050406320702150105100210021303020a0806010e130606210204 79
    0x10005081800c0c2c044042580c41d00c51000c080a0200e82c0c1d170000c2d12080b02500608095548109481c900d030501e64101a0842002e020728040c1107426413021032406010907840c140301e28a56506510340d207800c80154000c0c440904198115502082401c828290195000e5144c47c801c011f541c00c01107143c00c103012444980358203c202c1c1d401c02c00482100c5242503081d26044401c90b5058103d040103440065a407480d507034402410402c001c2000680368400f001030f03031437a803410005c0d10b1482d03599a004908038850380c010109031100a004840344104d071a84080d40c010310030200015213031803104000e101c1e140c49404505613004515512880c00300000c00b4280c004d41940001c0110a42c500c003c00c0c49050305000d028003030103501040b031111610810800d041c480800c241150b403280286480031404070540400d034050030710580001510600040d070281292000007100c01240c45001210007001e022030010b0b00c1c002e4460001068204800640040090b5003060004a12a2600c144815103084 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 954411546 1250 954410296 954410309
    0xf070309051905180c030c0c03070f0809010e030c0a0b0f130321030b030601060e060d09140d051c0c050f1206580506060405010b2701050d1e06 63
    0x6040074411782d00c0990080d40e4003c80c01490b03082d200c1d5400703a1824036500907080040d02880c414032450040c009583c000300907009080c0ea545150342c110000b1306070b07280301000c0159004480c4080800124a00801908401c0d00c8159034603d811060507030680c3c0012580c10a4034030f141072481400301000034000e000d80b1204242800d0054560800c00a515800140b04006c280150040e000c101075490300f00b203519040d80b01300100301d52842030501400501045c0c8442c0b1580c8501041400000e0180041d5451910724468034680414030385028006460003000c00380a2000074001180c5a01c01c01c1301600425000c94034241c034a06d09182040018000014450b040c88030702241000001d55203c2e4030710080500e020400d84030350030412414003008140c48090010200030a2240400c400030a981d80180412102403020f80d0303c0e181c80008522070280d640312842480b00c0702152280e91441c0300c0100030414140f041c200042104030a060b81c034101d00c402c815035100524103503480c2d890711854015026 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 954412796 1250 954411546 954411589
    0xc0903080f04170708030a0305070903020603041a0601021204050f03030903100506030606010f0203070308180d030912050324031002030a05041755020c010f050f070309051905 77
    0x83c1c170000c10740324800e4680f01001c0685950014041381d0040b981000190b50107400310780c0c2d074681420301100034280d00799102160380704d00300440c8040d8400517010580740c1440c2c420918081c6050200800380c600e42038426014041444085259902803120012000503010045a1450070038205401c0140007498a4140103150070000040c5500100341c03030b8415818107140d18503450380610040000c40745807003541c0c2d5100344c0700407112441d41504412000d62003040070701400c0c21212820795a0b8042280c410010340343e501e03e0b41210358403801100a0100010b401d850301c03242d0000049090303900840f4618003413130b2200107000420000800e0309022400201c0d0860410004000320301108007001048503080c586c160616161036224000c000f0300101803000701880504102c8061110342c403840120025011714000a08554052a410f00c0705103150341e41c440c6091443c40700350103141c0001400350700300700342d0500100b4140c4031060300f40020106680ca0140051400b810001903120005070080040c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 954414046 1250 954412796 954412799
    0xc04030309090b040b03010e030a180b0a0503040318061106060306040809040e0708010203101e080a030c0f0c0608270d0c1713360c0903080f041707 65
    0x9600540304800c2d111a2200440d18281030000035014010400900c0e6141d443d280020540e900000020002a031484e1924406600184150140030303505e441010042c0000b0000000d0840c806c00081d83e019203c0d082c120407500c0c40000a0003d82c540303420040c08111030841d000f50303100040000c6075202204400428242ca056a241421801800c141c01c2c003a9449010f07603407042d00c06214010103883c07500d000b15101d1400740303501c204020082c0b1683d0080101c0794001589850300aa8840c10f482c00000109003c601c0c1e564202c03040c3d407009030160347c400c08850224002480400d5001c000782100e42e614003c9041103035903030f06401c02154002c800c00d140400c540c1c0c1c01400100310b40a072060642010030042601d42448040340d0f141855254035058001001031244a90b170b41008141c0322510803113808007041c12007420402d500e94480c0c1d00c1d2498051800303002c403102130300142c0c07000e215841d100303801d07603a00d03516010a5000520201c0d41648081814049101c44240b40400460000c00910103076 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 954415296 1250 954414046 954414053
    0x28020f060a1d06160602040905130b01140d1a0a0506240313050d05180a140d0510060602150a0506010c330c09060e0a270e030c060c0403 60
    0x7199450074242e1040700c1c40c1c000c8515661900c003510803148205110742d0094003a4a441c6000750711a007c0d0610180c13a01c00401d0307805000d180c111014135401a074000c01d590070710a1040302050f4a40281761700008100004c80050300d5040440e0610340307130b044a00380c982403026100040e244000d1034240600000c564600c1c429448035051071603401410002d40c1c0c0e039240e0207021426900d0001d00504a446110080209079500c0070080540c1141050010082c07085a410452a68020703c0b4078640051030a104488520700b034002010420300c84d004507581c148010220307030b0540e8243d50000015812042034034180680c0e0708040c0f9800090203000300b00d140f4040300007900c07111992801910048440ca031402084810b008500300080e1900428500340d16445020409403014168038000200d400c1000a00d50f405a507070000840320040c62054101c0c00c2141000c640b592114548041e80c44481602c03043c3c400520800104400410180d56501031051007103141c10b202401a0304146401c100c1000403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 954416546 1250 954415296 954415307
    0x180f0105031012060207020306070c0c05010203460f0809011404080705070509010315150501020c100e130b0307060f0f0815090c0d1103010f03020904020328020f060a 73
    0x64903510f6161948007003050600500a0194040080d018413600b07050142640e048001030302c0b1140b00d08000c407005ca40300c40c01241c0f28010320321050040306580070310451000342691fa0701e0309113070410b0340484029240071403650a0803d005d0b17124085144880e40030076844d0301042c0c0c640d11004100080c066500303c1e2a80d185d0352071008101800c0d03410081890410442c0a115020042c00b00400c160b0007940c680c10480000c10850880c5003032036150813070000700410030005131001c650058024020300d189810a1001000340905c003c020440f134ee4045004075642c100c2c1c400504030f2401c100080c1c1403604014075251180681100003805103001250905940c03000b105117402e02140740c4005c080e11440300803841100baa80c80ba0780c0c03280805d010002d0310394200e0050048050000014840c3d01e00d07081800b0f403548801e024820040300c2c1480300740302600b04110b07041d801a2003c1d00304c42c1569114510486481d01544a11842ca60400e02c81303425072502c10f002450001c01162001c0c031b0800c5e1000301804 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 954417796 1250 954416546 954416549
    0x506030d0c080f161406061e0f190308030118110403080409110c192013050c130902090f01030203060f0f12010c0c05010e0a02091801060308180f01050310 68
    0x1a0050f00240c2c031454001140c03d10001680e022240502c03002c0d014480d503480da40100c40717560150a00030400f07201c2c43e80382d0b001d8640c201406040c0d080c402c0d41ca0000c0c8540305441600c40500d1524050001002071959001907000b8405884a52000096131f48001c09664640200c00c1d1010000e210038030200e510202100c0464042c1c6400003211100c1032100380050080c05400c035054042c1d4103d92044000810003407040600c5a030203110a103242d503c0044144070b001d2061600811002184e03440d03482e40d0b5103c507030000901d135001820140c03020040e8001c102c1a030003400107940c010070040c03420305141300c3c82c4030304030401d090643c01c602d031030004100710129100c00b09104014407000111030f40c858141c000359401d05100203010030007040401400400750b00100301c503e5840c024030782c418400041042411070364020041c02c5140c60312030440c04020252050380b0b00c00c0d540c900300000007942c16002022001c00c0c800700402603d0032903041145c00100001f40c207051250420410510f03c241502910 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 954419046 1250 954417796 954417817
    0x807080f01090c090f1b030c1e0c0b0c0c01110c010f021824160b0604090f0323072d3302030a060302031218010e010c0203060a0506030d0c08 62
    0x21760055a80d14440142115070059030100380403520780b1201552540001e105889a80c440700100300c402008404c1601c500b145000000301d80410110001e80c0103e000c1e900030208141d110b041c8402c0c800030386c0c210388000079000484540001c149009020130700501640b0140c3e01811402d02c0e262040c000b0b050840070309054819502d00394040d042022003e00c0381c80a05c40304050548031505488010f0b07816402a005407090200c04000409070700d0706010300543c13130b90700046940658156a4054034a4854000c0b200c3c40e600e0681020380b62217014070702400090f4001d030701054800920351210f80c05021018912241343d6070003408100402c9080c284002c0043d00710100202e903013407840c0032103001c4101500c8599400e000009005411f9019000042660300880980d2003101008106c41d42030b11030318a20b0004046c00e443e078074010b0340c05440c8035280d1f07401c181000c0705000e4070b6030b001078142103084a038981c0560b40d0300144003090030108000307480d0100038101070805032a00d0311107002c1c9020380342251 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 954420296 1250 954419046 954419051
    0x50103021011031b0f01151a090d05010f0c031407020a0b100b13050f060a0c0b040c0506030718050a03030507060b04060f03140d0504050f090a150807080f01090c09 72
    0x40811410402c100e442d800900035882c00d00354580c0d12010f0b15031040a0000c4091b40c02c0c101c41c026079110b1080c505044400b1040b486c0b500001c46580b110b1250016410503512100703211414001c10428050180c074040000400900c4d000d003804050100c444001004a80504400c1008625500000c0c484070301a00b160803034403943c2d41e50b00d4100c0070b503e207604000c240d0361010038007506c00031807900c000080c4c410803a1600701c10178602c401e12480b4000d043c88600055400c00c00030380480c50f140b00b695000b50050085d20190303038940c0081206580180c0300ba000140180760303908904c0462105144c080c0900311016a0b415103140c900400a000f01c00c800350005d40e0b2400204813990b03a5920100050040303201103150541d403401c0c545202810281010300740d000700080e03980346c01d10076003c55050380c200401600b103414603035050198106c00204011051555105203400000284503048000c1a0f1000148205c0f428000c1c410300304500100381050350380c1410b480741e00044d58003166900b510700b07001c0c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 954421546 1250 954420296 954420317
    0x19030e03090423011a04060c050c0a0308031503030307020c0616050a0b07020c0321030702010f0e100b0d0b0402010810050402040e01050913081602010c12031e0501030210 75
    0x460440c8614000c60b544140b07001043d003414030080d1641e070860002a4070042560f070b640c0884240c100c0c0e2041516488031070170001440444e004000090640707004000b1500c101404c4404603000200030780044d01c00000120412550706d00b4083d081040e000c00303034003450440c01c0491000e9075a100307900c030b0584203c001241460000c4855181c0c20701c07054000080301c0340013a990074a1040b42000341d90784d000501413510003c1c1c20b030500062003070130a5444448a050a204031540d0116508060300c50702c2155290103d00412070040d001e02d0298482d002c01800b1440c145203855002c032840000f06034069a08021400302161003a0f00301f55100d82c080c00c1040e035580e50440d000c0c0541c0c0446c2c1083e64058404100819280300b05000c4ca4162170f01590704c0c0a55481c4c1200704401fa500c150001010080200051090454189028a801e9106041010a01c5c5c9aa40e54420000c021055480080e40d1280104141c0384035559891042482e940204003650540d00403800e041e0001408500744010800d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 954422796 1250 954421546 954421571
    0xb010b07051002041508100308071713081e061b0a1209050304060f0c0210050d02040f090b012616050706410a0f090203030c061b1903 59
    0x2004429030490074003103584a0b2a0f1002e02880200f05d24000c000507081000500428500d1920360190307600015454100840c9617569607040d424a101c02c81d2100c4107003d02c00d5082c0c02d054440c000b500c82c0d02c0c003404904c400307115480103018034102070040b40d605c004280103484040a20031540c00303c001000568448401c0800c0d540401c403110b05d800c59501d0401400103001010000d00f00392042e56540081201c1498801c840c0380c849d030040658803441000220495034003800040160007100341001d420165200d0b02a1a03104640d4400041c1d02d41745c05002342c0c617613400f10074800750160000c504110009000e8100030700d000010070595802101150010318180114113460b00d05034003200c1804040a480f2000e1500e8030403c4d8080c07a000c020301c40480d0405440308200301c40c21180c0302072807155035601410401400c502605003804a41d152490390240e102800107120440c8101c004000ca4104003002d06001080001580a1a801030280c10680c0c0c408481c01003100d8458500030895255400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 954424046 1250 954422796 954422803
    0x4050703140114010921170301080d1206080a0303020301030501060f08032d0313060605102f0d020f061506031515040f0509180a02060a02010e0105070804110d0b010b0705 75
    0x100321142040c0701c03450340c21103004102c1c3c6c410300c0903119501008200720043c1040180380428050001c4075000745a940690794132035410705010340704c0700402085507075070781c1d446074200f81400c03c00390300080d000001441485401d00505004007450100441e0051800c1c00098883c007a902d240030000e0741c41001c180a00406070340c40ca45280a248000d9920b0822480d100104403108130101c609600b001000191890f08495544a0702c4054507a43e004a00100b010540201054540141c02c04080c410601d031540400c0000002030040c1c004100c0d010091000c1884d101006021100303240304099007001d80c0d1940300c1540d8011540c0d804840a100740040014500b240c500150044030342c000c0f40004900c1c0c003c512a40c11a03005440c104c82c00d0307d0b00c044000000b01040c40c60055503219414203801030504600400c20101c880c0f0000401c024001806401d4a1040e951200041c00f44c600348010303c0039245405107600000c440140c03507403100755540d6280c0c0005104180821201091030014082d092 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 954425296 1250 954424046 954424049
    0xb01120602090a060c15060e19020c0a030503010503160302031c02100c03050a061202060708162f01030c14031003020a1806050604180b01170411040507031401140109 73
    0x2c248000203a10303644c00400244440300107444240f5504031100b06100b00e4807604041d100d03c101420b01d00d94480304c807040b07072103a10380700216402d42c00c121020003005e00703228120702c05100342d81c1d0a03075039454482054941040410148000b100c06841000160342c0004c0c0e05c014107080e240c52211b4500704000681c2843d40c0c1901c90070300c03a800d091840b01c10702c2e41f5611041c400c0340410401c00280c7e4840f0324194011500c00002500000208540310205890303034040c080c00075544228010b418042d658004800b00d070316211800400207a00c003c3d00c05103800810b004800000e180401255003441801050000e800c5070500031000d0010114180803003a050440c080c54000d031100e2200d598600d41f08191821801103035508900e001404100c615102c1c0c112002c84880300c00c2501045030384e4410344010550417100a06102100740510007540303500103414441d90090b0142d141d404180e000307103c140e5500504040c101490500980c150380d42710361429041da0704254840e503a4000340e100680f4000c116 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 954426546 1250 954425296 954425299
    0x10e090330040501271509060207020a090c0207140d02150405121005090708070605160f030e10300f0e0303010f05040b010f0509031515030f0601030b0112060209 71
    0x101d0801083c080c1c150428031030083d4600c04001540c0c0091403003c400c100100c0b0080c004000c3c84406011003150303070024103425000c4c001c010f00d018110707400141c02c1c07501c0303600201c0340d5030711205100704080d01448a0380041c90052110120090650000b9650200400c1c1c000d02c26401034141200030080318007902c0c050b00000e0014003041c2d00040c0c002d65600403030044404510b05180010700c01180204141c01110884802040e542c1d080110a82c0e468100c8541d55090403185d1052802007104d40d1000c0c0e081d1402501d540030a00f2540040c4400704c89020b140c0e0042c0400d1848807141030303400941d2003920304001da4200d05004451404403014055404204540d5401c0c039040054405000c80218100c400c400c0503003450755a92800d11003a10039408405021410720801500700502500c010301b1707640320040c1070b540020030380c2409001c0d00f601035442101c5007000840c24841820300304510000e80107600001c05c0c1c550b1660742c2e0180038403070501660552503d5208803030300304070407034041e503145100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 954427796 1250 954426546 954426637
    0x807050106030510150f060c031d130204030b0717130501020d240915090905100c12230109020703051611040615080c13030605010b04050405010e0903 66
    0x44004c0b0001d80380030707184040e0310450600c0c00511040c104400108039426629042d040d20503546003075074121500c100150b0040102c2600c03801e1542e40041c160302901c0b40140060f02d1768103608005400d040c000b0705e68000cac8491800400d040643c0c0c3e152a1744d1001404403821500100f503c1c2c100d0190041240101420742403c200c030403880780322040300100c0e078215a11007107040c0e0380312280c00640c0c0f44201174081c40d030715840c4140a132031466008960032130b01400071186001200e1a14504546041c0e80050008040810304103071015540510200424981041480d4101c0c1c0d02140c44801300c18455003242550029080c1c08040c020381c141d030100b005120101e6199156424010003111a2610b1300d44190f180100200b80444001c140c00749410f096a00c203d0f41f6500d880b81c14441e03034080ca4541c9030380c0c41902d07800000245d40c0c1c0070320b6000e01605202c2d184c9552a14091000355170043c2c000c40001c500e030208200329010000240e507001091020001200c402070410b100c440b0421b041c55144601 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 954429046 1250 954427796 954427813
    0x5040c090b030f0108190c03060507110624041e1a0a0f060f0302071a060a0929040b0d08090a09063201020d1202090a06090e06090c0708070501060305 66
    0x245020381504882945c02510301004d00c0c6124516034480c066001018449820402c0c00855020340c4113a0340607525040500102300640c038090701d448000c480c0aa0101041d0300e20361400141404c2003070300c966050390140017410609182c5803500001c0d5110481d0150f481051030031030415075961000030315000d00b00c0c0482c0354545002c1000035840e8010300c0003050b07540d000d05043c0d6100f44202d800d00d540054200381ea41030003200c0100320340c00241c083c40c3c2c8410768141c00700d80820b040c8103c0101a4803003404450b02c40100b0a01c250313910264000d680b0561a10107440d95540320150581e09880d4001403c0e5900c1420b040014207011640e0052131006240000110701040c0d807803400116502c070707030800e03a651044880190002d20300340c0141302d005800001c0000b480c5030084090a01d25804181302605001d070034004600d0000c07840c1e114100003020440200b001c0ca11040c0e1164000c0c109541c95025440c01c0140074610340b00c0d8210080424500280b5101808020341c0158051948402a160742a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 954430296 1250 954429046 954429061
    0x7150f060b040609230402030601110102161110021c02031e070b0906040305090402070503090d0b010e0702070e0c1b010914010e010603050607081308070609060f0b0a05040c090b03 79
    0xd0304140603c20215105503404285408040d026005003103451001e9039503155001c0a02019400140c005d5050003071103811040740840a00140c8802d1921901c1c060b110f08113801c0c44400c180918000b02c3c041d2200c0c60b1010f000d20f90115590704003815a24540041d0280904202e10790710610402600340809515980c10f0070346504020050f182c015050130055450b480c00341511090140c40050200310104034dc40c2a504040e0040c05400340100300740c03410300c05544003065802c080d40034100d4001070404014410002140c26032030700300466100810340a410b00c150601186006007044030031201c085007141c0d211400c0d01c0a00545244113000303224405030fa241009207600551500301c0d0035400d082c0694080f407030510400781240d80140042000c0e450344541070300c2104002c1d10403400c0c02e2501111384041107071400240321441c440d10340000c448001e400c010085814090310489060305203106020795030388044081e015280c088800081030460400152000c90080c0c2c811111381c6008010441c85 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 954431546 1250 954430296 954430319
    0x30702060f0a0b0d150f05010312270506130305031c0b040b0108060d0204060803120603010c0318062a1106090106061202130e040b062407150f06 64
    0x16078240d04031604940c0350980524207440e0300d00d084940168086086601250b101c07204483c0740300290200041c105110501c107001e9074002d03002903444150141c084c2ca03400c2c0d40f00947c1004050303221500741c015001500e100c1c8400760030b4450340340706078404201c81140c050342041000065500004890792640c00008540103001c18903607420f20039180c14414216070405001d00c041001c0142d4510110790303507500400100d2882410181d0b0030550707800b0041282e22040006162020070400d44000600e0110100742c04c0d0b4042100403000c00d4140920b10802443e1040600046a8445408140f09030343c648030803c20a80f000084114400400780e1245281e0400321500081000800b0303a40c03c0d13600c0300d11080c2618440e1040342c00040030034210300f50440711540900900c1c101c0048041110750703129144070566000703407401e03907c07030135440140b001074a00b0ba412156a61020344118620004c56039210070b0a0040040c041d01c03c0300080d04418502007d64041d040740744003280c0070060140c44090121a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 954432796 1250 954431546 954431551
    0x5011116020f0109061224084917010605040513050928020a0e090f070303081302030705090a0c0206090a0c0909031209290f070309050f0303070206 65
    0x60b4182d40d90080302c40d44a01018401c0c4c94154490070306400c81025114001d0803a200e10031201a0040b081020003040740e02600010101c040c01015000004a01450724004054010b0702c1451354041e00c040000c981034480d1030001505400c00c00b104080d403401d071603290200d801c0032103142c03070340002040140d0002d0282c425210155984800c00190003ca00105c1d5000d9030107042d558030500c100f000d134030310700040301d4401c0d403400c0c60800c141e64480e400b01b04084500d40007440040210800c1003150320082145110514210740280805459070f10040d00851010b07001d07082c29640c4d0900007083d91003c10200c00242400b500c007008a150040400e80184600c003100401809020042840b012001500110350340e00081c11440030740c03801c005d54000f014906d008600b800340c50142d00380c0050301c41c8140101d050095110940c072081c4100100c45140c000c0c0304411211004506010401520482550f880b841c00d08001512000e2410800d140805a20034454140320020402c5005540420490b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 954434046 1250 954432796 954432799
    0x9090507030e16060f0c1a0405070f09054501060f080c010f0206043201020a0e04050105031605040b1f0215060d050d08071b0803061504210501111602 66
    0x240307105c0b0400c4200c03806000c1c0c48000d00007229680140601c203102c0c1e00300b283c010381f00390b044901181e80c84440070580e00180e4040c0000c0c030f0717940041111070008646201d044000410070700001c02010007a0f83c0c103540790350141401041c4000c0e95940300c0142507014001502e5141c00c2c031b84020390b4828840e03603540c031148803007400038041c103080e0b80b400c07400060036902440d4042e0f00c1a0841a00d6a100030382041030654042e42d00a602042c50203c4000f03100030203400765107640d61149000ba0720180403d4400c1a07110f103000740d1001d80801581000c0040403429100101c0f40403951401e0b920018419100385a110351041c41e02078884080030740c0000d0302840104402c4040c000b01e0342c4000c1045500707084410054415003119084c0e079074682c07080e60060383c000e004d4203000040c0310151215403419000a0400c0720b6602001060000c0b5162000900202031082e20303010385800d0402c141503402c442881c3c88514501c51005044041000039004940c185013815400c54440c40c0c084110a0800c3e02c007601030b07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 954435296 1250 954434046 954434057
    0xe040204230c0a0e0d03050904110405031902030a0206040f0e01090204050603040311120a020f15010b1903110d060303110a020306160c080a030605010f02030a09090507030e1606 78
    0x1089500e109180340048961000161550b100b807a01d048590141c8240003c20403c11404940740d52411130325200c2074080c3d0f452a40352284d081c10301045446451030301c0b060071800d0204020a540016402034402c40c02c0307030120f10b04459480460310748905084005d5004001103004280004900b602c0f800304c9a00c000340d010542d0717840761550708078419801800d410840410024010034020345045851b44801000ca442043c11280000c0700d603044403940c030005801100800150711820414800b52801000c41c00c41d0035494586920072174800c0c1c807103e01100070f05001400819000c2c0d8421703844180e464111654954a644200c0005d0031180401c90106800c03900c0d074038444400181c88000b8940c042c00828072510358000d540e5943c42c02d4440d81007081030918001c000903400710060000c0341060f03240424943d0800c0c1c00501124241c030720000c00c40d03205001c20000e455010b86040115054088005403e03210820100e001c1c000f2610f05807803c2c807030080c10044d4071080a000808484050303603503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 954436546 1250 954435296 954435311
    0xf0614010c0218250f020604080c16030b19060807030204050718030303060509090105041104020c070314070305060115020307080d060b0a21060b0301050f0d1406061f080f0408130e040204 82
    0xb52107608140705c191005034070200000b400202c2c030800800d11081c20000b11201804030010003101010180c1017124040d41c540140082e840742500c0078048890304240c01d02000341010b480750b5903221103100280c8100d850b400401d15880c050300d1412000300403044c17035800701900d0742000b80281c0128403500c0d0103102d603040051007c80040c40354500850b80400381d02c0814004100b0000a50000d00340c8107914050000700100082421505000f0300740d4440150070120b00d103003051404d00005910001041081020715a1080d90120403580c075503034400310072600d5604201d03141004040ca0741240d0041c0200180c000810b45d00420b0409804146241c203a0050b6142c0b0001e500b52042c5201d00c542c036010502c0180042e1400d1445680b980750b003e0224100621a52145100c0101d2401040c0d46500a201405101d0814050380c0d08021166951002c90780000c0c100200110401001903802c0c0040c40045020030000f04102c0c4c1d01d041260480303c002c26183c00803a9145071081e6012807186151100c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 954437796 1250 954436546 954436621
    0x1a09010f0f050a0e040204080717070605030c270603040303090606050406080307150f11030f0f04121b02060c1515090403120e120405040f0614010c0218 67
    0x3140700780e501856503031a003031815800c0c05450143c880e21382650f000d902030002213001c1d901000084010b10300d0340b45402403800c0405030a800c1c00402c4e000441041010003c218912150b80111103800d51a03407520300318045c140030082100303101500c01c81d9010f5000020712040c580c1c10340149100e5401050108507240e80c920400c0102d80351803141d04200c0e0000d10490f03000c10b0512440c3c561110b21000f022900d015a680100c3c00c458481500c0e002000003c002d0000344242e000420360b11486545441d807041c1010346803403948030301001403c0d04002c441100c001940240c00c1400204d55805880f540d2141c400e0454903071075882c869010242a2100f01c001864851948044000d826000c2c0400200d40c40f113403021206640180700460300142c84240e040307502c1c2010401c05881500c441c01254a46003000c04000c203851203200241e00ea1410700340107000c0042c4900050a215909080200e02a05c061010840001c0507a01190071400f5044c200854106005001002c24a8030380ca6082d860b00c0d45d03903 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 954439046 1250 954437796 954437807
    0xb03100b03060a140c0711040f1d0d050415020a060e1b0a03080304120504080a050604120320211f0b0a0f14070209041104050c0c0606090601091a09010f 67
    0x1500188204414020485c000d100b034004240d002d009101000390200d010003c50243d4a111202c030840550b42c13007190410015507107054001d00d030342e04041d02c240707644000d00514901560003203291485000c6200e40c0014001c2104184003540300006000c0b007500c550b1156104c3d01d02580c5400109040b2094110628148030184282c95001011500310346950b110310042002020502e814814200400320340e00d0010440d003002c803445640142003602e0145400301002000320706403400d03d030421071000e130600004500440c5440740b982840383c43c1c98484020790801c8008495851602103407909018105949402a0010600c6540280c3c101c030b0303a511039000c1c00d202c0c070407050b800150301c0301d11086100d1090b103003070f42000410510f590401d8010340000c3d034802c1f0143c030112100c4c0424050151641030030b00441d5880012105120308000702030010035101c400041002d03110703101500014240d680140320500181c1a43c004d04001080743c5542c0c1070503640918400c5003c60342c3c244100480134801d9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 954440296 1250 954439046 954439061
    0x142104020f1210230f04030e04050601050d050a060f030503040f060e0a090509030d1a01120e030f0904090f050a061a1008090109051c18050105040e0a0b03100b03060a 73
    0x3880102000080034408070001e0034a141880d8484802e0420b60548111181407680680045d101c5042141401e01c2c0280c440410302408a014500300f000308940c0382e800006840404548481c0401d0035910030700014002c110381d412090021000c0e000100c140100000500240ca41c0b46003400c00064507020203541140c261450154015400030080c02030340d00d141c100503000386482c411030381094030101181c010384040900c140c811100110304200503603404a0352000000550000b00309050710030040075224440c503d8405600c100000310350403d03490f0365100303110050f0042c8458400301814a811740d140c0e40780020503110b0f44d05004da1851034088041200c455a28000e11074500c41e54090000d40d01c1c0e12000f401000c80c0d5598400401c0400d0060101c1219021007484054107a41c1031100a4002844000c01c80704003c00712905120b6030344c01c90216402c1c1d03070040c4c050b1011036403058113140240000305155501406500c1c0c41c4030503540590040b54425004401b80d503540e46d0345030425400c607000c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 954441546 1250 954440296 954440329
    0xc0b0a030911063f040609060c1806140702131407030b0f10031b090f170309010513082d061b09210a02032a01142104020f 54
    0x28410415050840c65015609414120050461081c4d4204851244034002c44040e140240c03261030a00401032a84102462005541403210401c40c090b41c0e038000020701070290009002211281a1000311608240c8140a0f070080c100c0050040750102580904900100141c0da85038500c0840c903410f0090040c42150320b4040d18880030716400c0400c201d00507400341c2042c070038035a07651039030560b08003401300d041001442500c7e18110145040681c890303103410f07584170022140a01200606000303021045451000c001d10b4800e480b140400c2c408c0300d0288403580903040611408150002c0c0344681100804082c0c0c40d5181c0f841040c0600c4132541e00c403641124030003020409007621804015024019040b17098010701058039041b00420307007040148040d94103125503401440d8000452804100449403541d800c240082c40030010104010b4144446902c14140040f248003942240c121354180c0da60341241706a00718000d200f400c590b01000c1400e4038140d004150311196182c00b402c2810400400e6040d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 954442796 1250 954441546 954441577
    0x10608060714160b040b0403081302330304050d030614221d06091603020d1205070b0c091905010f1b0b010e07030b010e0109030f0c0b0a03091106 64
    0x845004030410381e4400c0c2c0502d40c10f800c00580690216510150b44c0748a24880c21a6450340c2c06e05085c00b40103044024440304010858800340300c0140c855100e0f045149001075008220b132102c0507601000103c0f4100903014500010040000740400064401009040c0f80c400700541034882968000080d800140f641d08280390005408078544141d00c3c0002c1c14a41c400001200ea85050349207411031804065080c495220809200c4098001e000042d05004d2101c40c480d04107103581d000c140b500d1101903029040b1000c0e0f60044000310b005030304036886198404000a0345160400a400d140e4200c9203040d405540c0ca06403440900e60484100401d681058640c40400340e04000119109084c06c62204080034188640000003000c1403002c50181007100d0203840c0614140354014103c646c0b0340300950401203551200c11181e40c0060301081584d820088a805071085820242001c81c4180e0041001040025251080540c5648040c1e40e4922880314000d4200322242007244501440b0314100781a81e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 954444046 1250 954442796 954442817
    0xa0308070e012304030512070506070503070c060f1a040c0206311a0c041401120e0a03021e01150b0c0a05030a080a050c1903020a02010905030f0c0106080607 69
    0x380121001d054214051401080150031803504040c4120f126422103000c04010034140b082000900c410340c0340200084c0307070905241c0301b6281c89940b40e00281050044c48000400b10760b03994812180320a08030b8000e0000d00448081c120700d10018280c1800c24100059502002601d0303203400d0045074044c1103954001d05880d20340b60503000c03000008900c803e036100c076400030450000743d02d1802095854050032840501010b11140112a000000e2030b9598040040100348032401407829010400e45081ca802514662103111340002440424015100c620400701c00c9020140d0014840c01d04021a0700740305991090084030360700f80d54660036507096002144c101440403100c1c1001510300d0040520441d030041d501c07500d0f81c81c250707408444a000024030700803c1043c854a03902071580c008141d03095072450f0a082d03843d07200d40390b45501c0c3c0fa0400c00d500060031050a62003500610340260300802526a68050242143d98075480761007071314040e5081c41000030b0401404500c580c8201c0440e12402c0f4001c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 954445296 1250 954444046 954444061
    0x105090a03240f1a0a180c450e0f09120d0f0c08040506070c020a05040609050f0709030503040e100e090a2a140d02060a021e0a0308 58
    0x5804000e044030076920002200200700304a4090200b002c080e65000141c402001084d800b004851940d1560048912540401c01000d00581c03012001c07000302800511400140021103000044000d41d00f0300300350800d44125440084210181400300e0040d23002c0c100d00d1888000c0220410300e1080102d103140101c0002ca1705000703002c034583d0008800c4240e034030898a14121410b140c100060704101d840c1e8034030142150b03012621407550703001054180820b9a00d016651250780d0305000b081d0340c1c1042800001c500864403609140c0018000042051090980f1445800300900c411205034800c2504100401d000b03038010f0380c01c3c000360784d00800a5843e20b400c10000c101ea0b90b201074100514150940b00024045184900f10b6005400902c05080f2416880c10030000c03a1001183d81c0d0170740c0c10f8a62034406c01948280328142150301d40c8120f41c10a003017010028164520f40304001e500300000154101c4106d60101340304407480b80d4480b0941d0090541c024407a0358103246600140481c100001103a080c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 954446546 1250 954445296 954445313
    0x80309030c090121110612010e010b070804120212074106031e0c03070f02070806130302210910050301060804020f03011805010c0e060c12160b09030a08060105090a03 73
    0x180c09001114003200140000c06d03801d5009800c0000070440c04001400700009002245004010201540b420101540c442c8001c2c3d00c00d5110342d0380c0104520b4071102c1103403501c0c0c0c01801d15000040a9901103561144c20119140210907005845031040b10381001a030608100107001b08114100200748414000c00e1040540c00908200003200302c444240340c0d0401034124003442004049203103600d80c00c0c1a94042d0400f03100700700281c19500441401c0c0301000c0700040840d404400181e07140800926402c00b681489400700c10760f0203520201c00d0398111640c01d10003e200300030055070b180f80e15980004003150103010038000c0200181513903001c1005480c00d03c012108049004000203122010b04188160b851101801165a03944840d040c03402c80f40c010040b41c0108009840480c0380c100060810360b1100078200c0303005540580404c5060450140ca05610015a40003c52945609141404030b580c1c3d0841c540742c40001d2181000a10f643d4841c0d0251303540048040d190244442c2907a450a45 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 954447796 1250 954446546 954446609
    0x20f060405030301150c1101031806020d0f0b030c09061c060f0204140612041113051501081509040f08040f030503040e070f120507030f0c05030f010503070f06030c1404080309030c0901 81
    0x200c000032b0560080481d06501c0108258002d0100000d9150308103403440003940d4500184611a4011120740c1400d0388035641b400303030301410842d1000c0c074032240f40506040b415802d60001e000d881c500b83d6840445041d07a4000c0041d03406160110341200c024504016075881207200b02d0030b03047c0c5d03024041000100b410054000341400180740c0c00e81030307118440303080403a40101e840010b80f1301c21014095180d40c0120410f904810259800c50f003828850780403892010019100910310504103c4540620501600b6280030b0520b60600b0210320b036070390034001da886d000746c0508458245c0d0326010488860042000403288442d54480e0004240e480101100070007000380103005140d142e00c5ca4a42c02c0da2540726454444030070f62225522401c100d4500c64481c2d038141c021501070f501031390050103002c0900840d01c044420900c4e000c10300440000e003c4419044100101003c0034001c42c0100701000040060681c41e10180e0484800c00c03101d50401c10101001c0c8107103000c40c29414210641141e00700b42810 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 954449046 1250 954447796 954447821
    0x80a110a0213090b090106080312090c1804030215010e04060f0f051e0c161209031a04150b0105040603020d15030c0602100b0a0501080403020f060405030301150c110103 74
    0x184503036540e40110300d402104103202001c0320759410141040040107130100d070704051044003c03c9800e00f8100c4455036031094803034107030203a10b17070100058000d00104a00c3c4c1c41103101905035024000050b00c2c82049190955003100503019028210109070046101c840c1200c02d01c0201d0200d039161502c1c0d2000030551018103040403611407602002c1e100daa406810f02404003210403c90350070b21050108207482d0054140b020f0050204440500340d999022000394144e000405400d1414034108144c0d1840e5280e40000c0055104103248581050503540d505c2c0b01d03602800c4008010600380440408403075128010364046a018003040c82014401e5000c0c00700e001400d100058400988800001050942d40c02110703071824031403042c80707020340c14002100300300000c41090208815250000da041c0145004080c100411000050207043c8208942104414184240c2e10182040c3c10040d0712588240280c91f0b0503519043d140c05c0725842108a89403103900851014001100c1d000110094502c103800c09 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 954450296 1250 954449046 954449053
    0x120a050f1b13270e030f1c0509030310060c030237120f05032401120f05090c01050c1002030c04080d020703050d09030f2d060b090a09080a11 62
    0x307100d00c0c0403100e060340c064501400c0f84500802658486011495500d0324502c0d51418480240101400001903800340c4406400c0300c2e4841203411203d90061f04514148080c0030700341014002c0c0940007000650150400b204800000c0340c403801c06481c40198010001c0050740400b03034600203c6e05da4080c0d100701c0e41d002680300180c01d0010307a40440a0000d080103565035811450b5016610f80c101d008022425110b05280d81185000b0030f01c1142c49c402c01481943c120540c0f114258241e101d0504030b00c4041034940101300b81142c02d116170004110850b4600c43c28454a401000c41d5030117941604c200c901440000d204844d11600148041c1d0001b90501c1e0300c0e44814000410344420a0040001000e450fa004004851542c204186072503001c3c0f00d19420301c4040201800801e6021854039585900020000151040a9455803a05c45140c030380440c010620f4034242c041011a4104000003002200c92080e80d8458202d078000f120304401d0010b12410b802c10458409a00591f940c04081503c402038 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 954451546 1250 954450296 954450307
    0x801181e09060b0d0309050405150d060209041103070c0506101214070b04060206150109061704150f0b13020a0516240b01111609020906040b07050102120a050f1b 71
    0x401c180d40b8180f076007100800d40030f40c1c0c1031007542009e2042c0c2c0c0e030003500c00b9841030004c0003090110329902d805c2c050180c0802e40000d083d40da12340311500405484035068a406607a441d00a80080c0303a8050303a0001c440c54014030022030540e001d00030452094402c0104203060301802a500d0800742c40c000003040b8203030b0151003000104500088090030013085c00b03801420080c40c0c24064040e45050f01c001c0c075818007030455030038807804c1c0c0c0c054a01d003141c452a9220310310342d03161810701d12704480898492104490810000d4040d1824680024a0305d500a0301d1020700c2a4840f031710340050b03024101e41c0c040019020300c5078000607c60081e04030701c89401601492064858002e482041508000c2e101c501e441e10382c00e00c03510959000312600c0d0f401c0c01880c05400c8030402407254a08480f660700c1050f220310340101d0310900c1a602c2c102168018104224000e03030710615451300394003030741002180c4103694000d000050400c139024001c8500c116041400d44084d56078104500d50030408450680000701001d106 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 954452796 1250 954451546 954451549
    0xa0902030c0714060903030403030f1d0f0c041a0906010908030f030609091c050a0302040f1d1f0320180919050318040b0a03030801181e09060b 63
    0x95010305070700d01c09266200c000d03051080201400d4400280d180e480002048580c200c08800c0d03e802c550715103000300b00c02c02030314501d01c060315000f808035070301310400c00113060038140025405c7d0540d441d80050381c07030b02ea004c0d1007008100c8042002515106101204103031075071031310108003907000e0760504100c0c0032584c8030b00d2858a960040540b070300c01c086000081c041c00d440c00540c076a9009400c0c9006051100107501c2c00f0610515104111081c000b000c0340c041042406a01030710047d10550450405c0c0e982d64a19056070b0020088120440c542000f0200d5011045054a150072a41190007007200502e1903817034442d010803903409a0b42e038400e1404607520030f941c0c00e11800c0d4a80c0c40c01100045a0401c50680e42c01c14819a5100e8140301d00c94007141c002034000300564501d813030b42030380301410ba401d1100443c010700f038041c4025038031035403c0d80c02000b0160808603c60594141d80044c018401100710301c02c0c00c07510100301c44800d159564045c2e100485207500069042c502c9040c1c04503242c2007420 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 954454046 1250 954452796 954452801
    0x304090f180803010e060d15090c05030a060522080f03040305120405030a02060c0c330910060602070608190b030d02031e0702100807090305030a0c060c0309080a0e0a09 74
    0x400484002c000000104114851106910740010049803002c44060303050383c803000f40004100c503a1100d26110924141400320340c1c0071040060102500381c0d5203409403803030a0700091008450148494682d81c0c2d0b1101c0e80c450040c1d10a02d060760150030186861510b100100403030b00010800c030704002c4100f00c0400721840088005000c1c81c400c900860300d0ba86000c0d0003038144003004100a01c1a03005004401c13200c00c00041c00c0201d084a0915000b001c10008000b4681004503038503c4106004072092200c2500e00080b0041c0340c1850100030801641c0313035401280c64a2061243c1030000c0d840002141d04070384003c4c006064a103584500150540001c0d0100781001c2801c8900005a00f0124003168224010b0b200e0744603401800c030b801d40c6800b4013680010300b17078802d0409072030802ca810000100b040f8003c4406401440c0c0041c04c86e03484550043c0001c00c16201d10100700c420a0800080000b142d000f80290900130b50b00c00e24550800540f18402ca49449400c0b202d01d61000150a0000382c091403071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 954455296 1250 954454046 954454091
    0x15040f1518080d0506030c0604140a05190e0106020f0a0b0c0d06090c09050901120f0321050103030e1815010203040e0a0605040b03210d0204051e0307170304090f 71
    0x29944070f81c8560b0701d0f00a200403200300400d0a406a000015056966034410048409940c40080b5100c05064100003142510095400c115042500000c04106100000d03201104454a84410002d540c0e21208126103440c070f00c000d0100c0c035900003070703d12000981e010f01e4554401603100c2c40a0408103014010002c1e00c2c8a6840300281c1942c0c0c070001c6650720350028032040030300000d03140c100b03103545000500c3c50500780c3c0c00b40c0a0100e501c50240081014410902080c9020503811030002089101c007110700205406c0c40f04a020603040c1e0100c2e481400c0c2049010030241c42d80003007040d02e5070340e1048038000c40c4440d01058118007040101154074000400e03100c0c0030b1443c23100300280190402c014001200e14807441c50b0b219078050581c200180c244400030117090101414102e842e01a00480c2c40080d0003103030015540070600003000202200440c40341d40d001c45044041b548481d030354402c148005100c1000100f16038104010034000044540c104103d1000c00c10b000144554001e8081c03501045d41 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 954456546 1250 954455296 954455303
    0xb03241e040c08010b030d0203180a05060315040b0103110a031109030d2003040e01090c051b0f0d051303110a15020703170415030f1d010e15040f1518 66
    0x116400740829002489580c5c01c000c0c4c10f50043c60740d0190f9a00107941c0c1d0150030265030103071840349080c50b210b440b180d5003100200b6018105075201e00b0440ca402c0710b40f03d600c0d417150f4042c902d00840540b456200e4000c8400e1552005003091401314044c8084010b010340820309400d0010410182249841c00c121540c00c00c3c01e556166442c00b4080701030003000a03154802400c41c2e91091005000a1104507540340c11101c0b580360000704040072050030794007402400c030808411034555a06203a4034101060b40d01d0b5400e4100c01390741e42000402003d4816004022a403030490110382001d100140352824000e11307400e40105012425a600c011124044650081c2e0b1070058100f08820000c00c00c41c0c603004009855082c45c0c0a0038941400a0344402d2000c0003e0382c0c0416468078800d00c080e0841e544201540c6041100c41c9035040d00c0d01c600c290203030011200465051141140c542c0d000d40d2401d01d054022507000291000140c4c1d581c440e00d19408911400c0400c0b1503842d4202074000301c40842c0040381d10711 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 954457796 1250 954456546 954456563
    0x60f030c21070f1a031009060303050301031214030105010e030c060a0908061003081602120105010603270c06110f0607020d0801090e0a1b031a0603010b03241e04 71
    0x21800c0703840c00c0c40100d50200c0107050812400b8002680741850341c014600501c0042e944a5560b60b03401ca41d0201c0940c4080400c505d0300f80044149940300c0000c6042e01e0140c07034086140880361004407018816800c40f400c0d0210309000600180d841078002038240c00000f000c0f1100200310000260150340094060f00100c4e4400c0b804000c4100c051110651010240c0c0403000040d03d191201c1d0faa61260340c203200c22001036030701c00100310760b0348046a26900d411071000300160b42c1c480344090000e210045191030a50940f000e4050145c00008100c41c8043d8020348003100c80d0714009003524102258620034119008504500ca61f04008100c1140306205e05d900521800210110240403160182c000c200e60b80c1c185004103051a02c001800308030340b9440101c80c00060000b4096000c108007940009142c04200c03c44500001c0e5061605800b5090860080004041203010581d541c41d1001c4200c0c0002e0401c0f0b03c0071f0320444802070459009400c411141495144d581100502200880c0e00302c0d01c0300d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 954459046 1250 954457796 954457849
    0x6200c10060608070c021903060510061805031c1412040201030b0a140d031e02010209031005040201120917040305010c08010f0f03061a030f030c0f0106030308060f030c 74
    0x1049402240700812a42c24405814141500018007200000c0400381c0107a81107402454105c86039040c02c0d00554115000300140c0c14101609000fa419502c660b80016011180104502c403840071600c0440303100900410340c4150070141d065407100c41c00000340a02c201c03c50031202046a010042c0707441441c1c0318002480c1e1920744005811909441c00c0350340602e404c084103220b8091500030095801d0011644100c240358189401c0301c000c128030031800041e10030740d0009024070360150080c12046400f20706440a00240d400b0407812641d003150042c1c00134040080950030440c40d9402910040c4c003a035040b042010394000c0880d40765000341c0c0201c500b40e54034202820142e6100220602400014800480703551404d20445d10550160101500720755079000500c41030504202140604031000d82500d00c800581c3c42459141d810080c03d00d8500e00500404d1140c1b844c040c861001940c1e8141c5070307590540c941d03d060091161040c1002a0075100f03507902512203694074500c104645201e03509110001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 954460296 1250 954459046 954459073
    0x9030a031107140f21071d0603010219120603080f12060306060604152f0d0810060e010221130506040e0a0510120c06031a010c06200c 59
    0x800380d2040b0f80d1440d800100c52800e50f02d04445155000086680f00d01a40c0588110113003418082ca20720b81601c0380325400291075129500c1400300396101c20880c5950790319007081c1401d0344100c00c451118001c0041d0f06080060043e42c1c444011035003d600001c840c2d4403130717a88140e1035015940301000702c1004224981e011b0b903030741e00140c1d20903002e42c09056642481400b0980e41c0c012402001200f100c44244660900e00c5015003a840015446242044807401d444004148070b080980180c0381c040c120340450124001d14456016140020401455a2600408589102c408480301e4118040c541000410b40c000304440121190784054996603005410b6424040c0f508951280d4020182444200450001950116440f41040401207140d558030507010f03d0441c4c02d50405071070f18030315081c4003080c0444403401ba8140c40035500c04000118407403426107003001849105c6400a039a4018590009003550081d00c8903030800303110400c090541041000007138102c10040a0503034003808243c2640c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 954461546 1250 954460296 954460303
    0x180e01081b01051204150b09010b0a02060c070b0402091b0d0b1f0c06050411061204060b04060b03180f010f0212010f061d0f0d050f010c08131709030a0311 68
    0x303000d0070803600c4d00c121308450451400b0000d00282100804014000484840f60001910840014440459980c440102d0b07103440d0030076501c01c2d00502c609000181e0007034060301103e00064008103440c1d45030307803203508220503020024054940c0186d840310b07e4000801c154064a8403101e062000300303241000c1d0080c017000e0280d040320780401c204841400030030160442d80840409402032130114290783c0c0d9040890000c4004200340c3d40120300000e4415090090742507c41c0540d114500c10711040c00003034100405d030342c554001d5401181081000c10412000194240c0c0780420341070a035000520f5289140d801c5400e03041c0040111500000c2d240700036186032000501503e060030224010509010b00203004050b800d1400c0c01c040d041c0e916503011650f5a081404080344000c040c04100c2d0002e1504644802103ca010030540d030030282030860240c080c2e2040ca1160403000f00380c2405243d04d07100c041e00660020030014060608000c102c1068405004c070b028050b00940320049a8144005141e1a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 954462796 1250 954461546 954461593
    0x20d06050a0b030c09160305060d0206030103050d0801080a200406050a0f0e090f2505030a080403060c020a02010e27011d0a0b0618031608010c1b12180e0108 69
    0x214800c21006c0100b8030480104260780b442c5986070024031903403040c002c10b03100120075002039400712001c00000204400081c02800c103503116a150701103a60390f449455a580c41140c0010803228091801440c500700922090f00d200c0d030f004001290f81c41e625404a00640700d15088040503025040e410310003040340203182500400c60500074072101400150107902c900c41903010014110500c04048600c8014804143c0940320060582d1420060380ca008072080c2d00c948021905582170050041d0014004603107960496010303100ea0340e041e00d0303003420024214415030f107194001180080c00042404c94031501800f800c0310070020156121103440e0440c4240008000c0b01403070341000b10500312900d03a075090354541e041c001c102a80d22065580000c1c10f1000c0050130084034000c039000000c0c0800c1c1500402c0444029071207501d84603d0204680f0703400d8071b04540c00703801404d001c034421103081d105200c1041c803030240c0c0002c00d00744d64403802c40800c1c1c280203030301c00143c40d0310501008500000040c140c0c1c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 954464046 1250 954462796 954462799
    0x41407020c150304020d170d0c030515010c050d0810170c0406170a061d190c0504060308071202011b0507061d0a06050703020c160f121509020d06050a0b030c 69
    0xa00f5894140d000441050f4401c1004020303c184034610b0485201c8031081c2e80c1c511221b44000d0180840c2c1d050000d00a2000b01e503840003440325280c00904a50050a490308074503000702c09400910001c2c034080c0e0b140f10340500a542542004034000501c520345841c201844031046004d000c082c80d000b010042501c0154105803641056840086100e890014021920f1035006201086100f11030707100c845403414484141849000307400d4880900b0454030640581070340f1a544070480702e926042030004440c281e010083c4000c40420041f8046118140b03030003035045030381c400460460241c0702c03079002e544081800b0201062010420504000d620300681d81000c10003201c400320301400e5004560303502c0074020040c5c5000d0741d0300c01040d00c844c4240c0458022461340000c07034807188401b41d20008013899034410790784400e070346d50703408100994000c69105185411007903454004503e5402d020060001500c102c0c0d00c480d042c0d031000c0010b0741a0150038401c002040380043c204003c03109041c18081c3d80704500c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 954465296 1250 954464046 954464089
    0x50309100e0f06030c04060806191503050c0a02070b1e070b01030b071b0320070b071a0402012321060f010c08042304020f0c0f0102070507050f041407020c 68
    0x801c18560251400c84e800b5103002e00d801d440d4270002c184901ca051150207801044580041000700011550034500c400542e01004140d07101c1881c1e10050048500c14801600800c07402c012598251001e403100080c050801084981481ca600704c3c02d0380700e00e1b07040ba210312001004009101900e40c417294024960700348034065018050841d0b210005d510401814803000444004011040c11650045603404004803040d0540b2a8805c1e14590070005084868035000240c400b446051b03003155038000d44c0d06842e40c504040c0300454030390000c00c51200c44000b411090140314440e42500b036a079500c0e0381040f48400d48600f02103051090700c1d0411141c0710b06001d0a07202d00000100b10b0821182201c2e0710070424401008001f1400810314410344078658828000b0420701d150800003001440003d1541d02140c10f501c0901689501f0707030144180c050050340080d40100301c50300702030120110718100184005940040c7c80000e2100345001d03101c1c013005034040101d01c035503070034140004e0f001d00c90380008a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 954466546 1250 954465296 954465301
    0xe070302032a12031306120b0321030c0c060703061802160b090109081207080709062309030f060f011e05060a0e100c020102100614010c050309100e0f0603 68
    0x2050800102c440e00d079030007a00001c44012410b4010f10545020a03130156002a00a81da0f81000300b00d4500d0800c1600750514124862400780380016404402d411000315a10050328442110012504004c1c01ca1140113000c00194150700030a01ca15880b41d080d40c1c50004699040c0041c00d08880b44100601070028810854000ca070300141c04a03290315a071190707504461fa0713901d2886501600709140d0003071040e1400b003040422900000c40852054500740d03074582843d541d942e0100d8914a69100710300200d42d01c3c40020708075607107030582500c548455100ba140380800e00c40200380b80041c180c0c0300c1d0901d030700f144c014005e2191248500d540100040780b42d0989800619a014100d445039114551113070300d000854424081c02001800c2070007038010960300403442d80c0003020341007000d4503008a0041c0202e4207229a43c60403486241e0a8039242c0591000c030010726001500e4a8480d81c000791514442444120100d9440034018545228030380d5a01c0d04240104052105c903803040924a031040105004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 954467796 1250 954466546 954466603
    0x605030906040f03020c0a0314100605011706010318030c030e1207090216080708030405010501470f0a08010815040f06060906170c0f0307140604090e07030203 70
    0x10115001030f0089028844030700d55180c26032400c002000da0356008200240c0000501003606010307040103800724162500c552071136200d00308460417401007a020481f01030819105140702c180c01680400f06040009482c0f00551040f0144a80310703004500040d00b0070f401c04109607010361140e01ea14030036a40144001c00480407940c480a90740101401554042945089100b00794000096143c00c91056681c0f14240d0402c43c4503030f0320450f8151640e40c00d1400014103d440c00540080da40400708040000d017140208007604c0303000c2c0101c641801950b00c050054000c910f00c006001e4003030558265607803034103446809800890141d10110083d00031a603000701c60003082c4c9040b07074000d40c0320190141d09030b407038548840200305940001803054a81100801c0c5400d81c54000303560560390000711255001ca1000700072120804003503071905038005510409c100c6042d02039420700c0d0000240384e0341c101900c50b40940c00322254100814070740c2d40404801c00546c14140000c03001d003c0451862411a0766110 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 954469046 1250 954467796 954467803
    0x706080109020a022802122406220609230406020313140601051309240e0102070506011e0b0906180306040606140a03030c0b091e0d080106050309 64
    0x301e0a04001d400182c4502600e100b0b101e003030060409840354140c40818528101c400020560040b0300030b107022600c100d80d5500014400725410f24a04403180004150b0000c00c4042c4005080c064000080d1f107440840002044d00600500000040c000f80b1140f138910128255240c02419000f4210740305085841503841c1c045007030b4407927041200582e0300d0301d802800c0407440510250240c1145078540c034420755400b0204096040360b404692543c0349011090003801100d10443c0001d08082258480c000c0c0d01d0041e15200608a061302c400042c50320404003881e09a07070105d18103d0710354100c800140a03184803100c2003c05000300c90f05d20342c880c6082c50140152842403c020070b10806001c51040700380406285a0358600501030140c90703150800703281241c09402da43c060150b450ba01d0300440d4100d41058600c0004a80d0160381c1c1030390a0f02e19489160040001415800d924006c00e41c0c15600d003208800c01e180b210302d02d20000c1c401d40b801c600009050240c180c1096080200420911080703d1002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 954470296 1250 954469046 954469049
    0xd0618140c09090a091a0408191409090603010b06370906081012060b090c0f040504021e030123010201060609050906120f030c0c101b0f0804030f020f0307060801 71
    0x101c40010f174440441c00d1850203030700d5080300d58070b15407801810001003203001c0703010b0841480212000010707810404c800307461154050358440f80f065020301084101c0d1606041080e0000000b4000058284e0340c003012424640c40402820550400d9000d5110810600840c00e0785121410740c08250f0040c0030400140310382d00901c148401c0003910400300707056881c600c1c0402c004000b00741034080c604860f45060b0000c7c200094400d44103041200c00030b00d802c1030745800c07109412914580c0c185070a050000700700080d084031401c01240d00341d0410024280c510303400154040c145c04c0d1061942c0c42003207190418001c3c41e40d000e4504690500c10104000380c2c014100780292203044501002030344d00d0201049084903556902000d51081c06602c13000d100f00400104a02c55000c030680f4984036075201802444266964100c000682d500000c111000c150a6500081d41c812060540040031a0312142c6190304540c00030f480c0c102c0d2000c7c3d03920440c94609540d007080e00c4103034054103103107181100150070700c42d05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 954471546 1250 954470296 954470311
    0x50312040e130302010609023010210609030816052d0c010f060f05030f0d0f090801050c0a030b03010507020a0623161418060d0618140c0909 62
    0x1102c0b0340082600030b40001c0c001d03002d00c000842d11440006c03903601d900311008900c0003102d40740c611240900c204e440c00282c842d0306020900509103140c2425407101e02e58a03c00b0720408220131080900241203801240c0d200c6000340d4400040b410121500c1c0318540d100034880040c0002048018100038003050780c503850180b2489000c214401c0c0d4001c00c0324501c150a00150f140d4030704052900181c3c2c0c250301507419640c0e41c5000d0158aa165400c0c5982e800114602c014280d000c8580446a0351080309007801038210f601d08540070302c0d9651503e40c2036450554005d07801c14800301d20542c9655143c8100d60081800314001e010a05140b000651030b000040310181045441c0c106050180c000310108610020490700c10745594540f45003031001d4803914030150360014080c1d181c2c0c0d29400b0b0510713050b180c1d2018264454040020300c081040040e80c8003031811040d0700c3c1c0322000010380095040803c10b40700070001011a5030b10a0200207a1500c1c4020400d450300c00051102e00015100c403120503600c03d03034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 954472796 1250 954471546 954471571
    0x90c01020f0c0f0f060c0622021c03050f0d02030f061c02010e010e0a0810050f07091419080c010f11030a03050c1204032006070c0f030905040510050312040e 69
    0xc4a0011501c4c416460110507004400001c521006402c002403652040703502c1d00c40a02290040810003c4c065000840a540f0413400c60315107014980208602c25041e11900303006213009655102c5400c1034010455095002e603004c030170429108000c000c0a1b5110b0717802c03242464032030031954901020f1240910082e0412030f00e000d050346541d0240c1550300d16110020407032007525540d200c001e030ba40d00c5280c02018060b0304100101e10300702e00c1c43d1821802030916454a08440e800c110300e141c002801415180c0e4014801c41e180c0721400341d0000b800c00901f8041c0046c203200c1c40d1420002d00382070b501e0a07402c0100404808400d03000900071003900d90301550340c40c000c170303450b140c10390505020700510282860600300041071000b0150003044d400580c8401904040d05204450066a2940b20840312000428404044100003418190700100d03e1403190400301d0009454071b010900700c232002c5a0909078881d6070700e8144070900d820401000b280d0251001380c4d00d014285018021002c801500c05101d082 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 954474046 1250 954472796 954472819
    0xf170a081f180603050c040b0a12080d1802030607020703080301121103241806070302090d0f1202071703040312110d0314012c09120c06090c01020f0c 66
    0x2a102080052a11541c0c40100104050302c601c02001c0c1032200f140d5610500450580c1d5003000c2c0660700480710014010711610340340c00041c0e41e0502003198102d0300342908020715a0070080301d2080303840b004d509a800b0b0409203c18414140b422101400400035584003000400020f12140126815503481c0c0300d02800303640b283e2500e0f90003c050458041d5240c0200345a080000d5280307240301c0d0401103120101d0354282c907204001c024003560502c0204441d041700c0d0003d41220f000390000e1071000400713024160030309071944a090304840805002c6501c0c002075402c00032056030400c440c03400ba081b120400b08101240c0c58410766284036a00c070090030003060018111841c4d00a0a105206003401c409171050b06601c000010001c040241e824050a48030000114043d031030b40300c901c24481c4502102220981c070b0041c0110081e130000340b0205843c89605000218414000090100c5400c800d0081050b410074000a0703050410450040d811540072813002c8400c3c42001500b60300300041a6550705407031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 954475296 1250 954474046 954474091
    0x190e0f120a0b0c0d0c1107030b0408041d01081002161203150b031e04022809090303230705030a1e020304110f090c070209220f170a08 59
    0x340d01c078840a04181100001c00c4089001d0100400c0020b0160104001d81c02c0200000d40780e0244100007000241c2c08180280000341840000540040c018042a030030280c1d02d040c0740c0c121a40400c8404003117044180100601c100c100079100491300044803d42c185141201c1c1e0001444070640046c111104008010b900680250b10502c44502403a03a0464400d403154080c0c01e181e4010b94019003490307803000c140c05458082c1e0700064041c541c01884203420101e00d0058a00390549a6001e0381d08042d4084001034901d00e80c03090001c1c0e144a5103010030041070390281000801220f254410080304034100700125070380e000c0120b980c010f08030306001a29650b40d4180101c07405c0740300303020304101c0c0c400400d000a100d54000300540340e4400312001801814104248020417100b55110414120180075040040ca0f02c08591907010751041e100c5514408503191241e1400c41c02641038400c0700c5c8400c030035020310111017800c0300c005001d14207039480d0510340080140001c100500800d560140d00d01c001d52107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 954476546 1250 954475296 954475303
    0x11070b0a020f030103050604030215010e0c0a110d180801092604091508010c090f05270f0915011a03040609020a081606110c01051c02030a02190e0f12 66
    0x2c00c0107880c041520796850b0700d0207030703030304c00c81035034190094400c80240d0369004031180d81d04c505170b0705400c5456a8903101c0d400c814205400c000861420306c1035a141c210083d51080010084054099682e03c85031609052101d16490564008080703507410310b02d03110082480c80c0c90001000890f54080301d141080c00b41d8514850040c0d03008040040e00305a40144a00260680741d41600c50080003000508007009090742c84011900c40c121010019090410061420030348042000c07646200e0420030440199545440b4a4200c4003403411090100501040000402102c000c40d4003400e487c60065041c500001301c0840d5170260104188000000201040710036002968002d5000e000300030407503143c01d480c0d42c07200c1e13070142003032412440c3e22000204140b04141e4110310780703074034406440304043c030703d00446081c1e12104100000506804040c40405e441d03100a40c03103603848510058840203851820f82d51101500340c100c007002080d14051001d980c600182c00d0b82010119844076840b03140b88000d606 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 954477796 1250 954476546 954476557
    0xc03250605040614060d0b07180b0316020d080702060f100806070c03020f01110405040e150405030a03050601053117070f082d010605060a0f0e0411070b0a02 69
    0x1a041c102440100211500065400c445088100c40039544010a000e031042c19190701510308054070703001c40e04c80383c0180104c80c8144a0f4034101300350b094584004d001150b20a945074418401400b450301220fa034103010050000f425490303c54450308094000a540314809003c11003a4401840402c2c0841090031440c0c00800851050381c001c0c2ca0300c03203400f4000482040c82a0058024a0a00b0300e49000c1841140618503c520382e00342814141000d00c801000800cc80d402a4410100d80e8840d000030030718000d01c66403041000b0366490004040050a0311030140400d81800400d1210f5450540a4041c1010395041410b0080b41180b40c1f002c400c9441603a94810110b1005040300100c030b844c1c02007545c005440c280c24034900308941c3c803041c03503550708007400304961000c3c80d45ca03688c861080c00c004462540e00c0b00304004110760340c03200d00095540e1f0020707240c60302082c60747c8004055544c00c4100e4008826040350204030030400c80007000182c0c42040130040a03100c014002a81c40d001a5040d6003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 954479046 1250 954477796 954477803
    0x90b090103020706090b100f150e030a0507030804090c081b0c1501060513080c090403120b0a09020706140606041206201c0b03031902030d1b0906050c0325 68
    0x24210242040c1020b80801d41f50b114078454602804144400520b503641c08545130f00240502a0050360300c101c07581320220b029168140a05e24000001c60700c00c00255002e0360040d22116541c5280595401c07ca42d000c80142003444426010800c0850217003920200200981107059a501030014940e403d08010000f40c0c800d915514001013041039020006c2d0040030010882c0007c0d25440e011090364234111203000c190301c0480d0f0800a000284180380200003c1403004006ca10080808009130602848da004203140c55404a800c07001d00010b802034090034140c00703407515510f040000105205200f00e01848062009141030702d0100811030b8401391151482031030f16049880744810103065640302a034194621003400d030812145083c07502c500c003880d48000300110b1520b42004640d10070380c5490000e2109500050014640ea80c415000d251041c91079215081c81c0d0030303094000a00000800c2e000403080140502c0f212004445c008103c0c0c00d98006000b001c40020031100d88142e40200c00400203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 954480296 1250 954479046 954479051
    0x1009050604081b060a151a0a18150f080609060904031d06041d0c030f01120609060f050603011b02060c0c1c020a02031b030c0925110d0f090b090103020706 68
    0x104240d0b90b1b400f8000d61084082c8098a4650b2404810f003c4d090440149111010801070040828000d1a84900610303401c1414002182d5881503880751005100c500d4001c0b0303140c41c541c0c0d075849501400e020762051080f0303100081400d104020603184400200014281f0400180d80b443c0c40141102c0c0312161a402000166110b84400c62085040000482c501c8503040940106410a01f00c10640f80304d0420100b03400c2890b86440d29401c03000b2030700482a24010f54410301400810300600500c0040070001901140740c0c20100141421681c50102d0544920400203d44100da5030110700150004054844107403103c10b0281e40c58204042c0032003802034103c07042c02480640d90003103655500b0600032000d507184c0002042403400c1c00b507245000281d15401418907144d2502d00401d503030703030030510b0380f100c105100c0c0c0c1e0860003030002c20401140a0210340b02d40490001410300700310500d00e0311014500f419285c191540003820b070b42c1c124001d020071074401041160031a4840d0707060703400050300441d05 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 954481546 1250 954480296 954480301
    0x14040f0e0d09080f031912110d1a0a0501021e15010e0106180308090405100302150c3f122422020f090907111009050604081b06 56
    0x1800c031264600c506102c0d0301404c40c070940b81c54008001d40d9894480a1041c1404018100003207e083ca148504564429602c13418542500d500c40301900880b00d0302d07100000e1080b9005291240700001c4580240304000041c400e12259a0208054141491050011405030902d41d02241041d140c031041543c103040f202c000190154080038103074100d50458a5041d02c81400f800041d1500201d404003500c1c08a04102c0244d1500307150707210036480309880700718134026a1030f54009503240d0000b86403035200d070340d012038081381d800c1007808080c80c0c0380340300c0f07400400c001034902c00b8048036416480041c200070300229203450030f00e50389401c49084045d20800300d00e40e440e20075804c04070040e2401190000f001c0030503a00c026400e040446040700541d01c0383c00038403481100030b490f019501078090029242400e00950340c3d1502c4d82040703507018141945072506121068a80345143c598054860300a09003415884400f040e008201d25801c290000d031003681d1030984400c018409102c41d4220685c038860a0f04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 954482796 1250 954481546 954481573
    0x15120207060f0203060a0f061e171f1d040f0302030c0a050109060b1009140d0f0602040515031501200f0a0210090305030909250203130f14040f0e 64
    0x1354405d00c400c0fa0240e80054a850103102070889501030030010072540c0b42100c1c0f481815800300d04454485180680034203200b40c20103a080207064038010711082d000622110b00340d004d1090040640109200803d078840340e009800f82d10100540090440b07405a210700c000d00d48284102c88a002c1041c04840c00c6424a10300b5500030040e0004c103403025443c085099180d40340c4100b20f0b034160701c2c00b5501e0040705403c080c0d0b00350700f0841c1241d16a03030208030760045c4000251160f00b9811420b000e0400161aa8508801d22400240d240340050a100f070400c20000d55100e640015403030a4401c0c07804a21959002c880d10040d4454402019054441d034489508582000a4180900b078801d55198006030b00c00c590550780e844003404010710710f070000e101d00c1c0c0d03d03414284002a8483e1204460181c0d4140c0200c0c1c049928035081d95120040c1c0000440400c200c0d00c40302c8079001072140010700c1900d28944840040408000040c0e80e11641d00c0d07004041c010389045e04800840204203081d074000051250 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 954484046 1250 954482796 954482801
    0x70503071103120c031b010e1020070c060c0804170309010f05031501080402030c060c0723010e09060a0305010e0a02011b050a0b07121407020c0a15120207060f 70
    0xd440c00d209206500c0c00f0b00c0310000140c2a50440e800c88002542000d0700560003050b081405601c0d011690f60755029800849000c0082d04008074403280c0004140c50f80f5030a0440007852000412683d843c100108030009135400e003800700719400b0349001c0244100cc1e02d005103052050307a008030403a00c822580c5c001c00c110080010710004809880301180005044400da072280400c030348007491000c0600000c035855010b041910350207403004054541603440e4000080e03070b541020850109076805160244003950f40505c040005400c604003e00d400c10900d00000c0c04528100d0300707030340030342034000115610b5259175240384051603200000b07000d0000342c2c1c0c081c140d40b80b003c00000c0e0300046103c12100e04d10011003001902e426049400b4003001c00e4680c84518081102030961030402c195485403080da4541c40c07003020394140099070b2403401400e00d003600034600004010340c00d104c1d10040d8410010406022504c4d80e40009a0030103001c0040401e05440c000c0c090701c1d201a044506060f001624180e159 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 954485296 1250 954484046 954484073
    0x509040c120821040816030c14070323030a031109121c050f04060e011e0201050103230d08090102041827050606130b10020a0b0106020c060d0c0507050307 68
    0xc042000d018041074550703400d0b0410035500540b560004100001441d0102c0058200c607e000b400c200c5030307603030050f9a42441107911506158654010746018420020703207421140d01c1d400c0c2e14160f900d100e101c02c0080d681b80d204601c40c1c20113050b582c448075501c60402006880303c8180040904080a03041c41c212502c3d81881100d58607120482e4600400f41e07806041550645113030420130038146818518107a0b0032184c0c00704400d05100c0c90a1040c43c82c000c031900d0a40152841d80d00200d000d514600d071160004030b928a58000311640e9803002002c41c90001440d1310f21503540d04d0140d8498446e140c03424024460354202c0c8102e401c2215490b41000f10726000b403204030444104d000c005000c0c1d1403100c40b948904072001007898008001140d41890000c0f680100800095400614014400e0020354110f000745608009600304c112001c0c20f01502c81040303801071007107001821101091200142d4140300d0300c101601c01c2c4d03545122400401e13105074103071581643d0107011030307a40ea10181804503403810700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 954486546 1250 954485296 954485317
    0xf09080d08070e0a03051b04140103060605010e0f030a0308061f11060a06030b0a0203070909021204050d030b010e060c030c060720010204150e030115140307080c09010509040c1208 79
    0xf80300c5601070500b000b8001c2000ca0f600500078202e8951981a01c50346003c1c13a544403544940c440c05000e1640e0740b041c8105000310704c074090005030301c1c0c6820f001502002da04451244600b0000605410f103440c080740d1281c2e6540d0614213144c02d03030794207800128072500114210503003114800d0388882082e0450f680c40e1030504c5250403905030381d4820401c4001e407060750000800009601010420004040e000345d0741102e0b05040c000017160719000f00c070049030000100d402c0740544480078802401018880e848c41400c2c035280511102c2624800a003a20074120f0000c0d000386000150820100814401c2d601554420400e4407903d0414250092280c41c85100c4814a11400300c10401503103014800c580844c0c08113907104a40c14103001c1c00341c0e1402c40c850003072a01b65407144580000310050551b00b801a1022030300c98407a20100301c06051038006142c014080d29404400c1980d207e5580003000c034112401118840c0e21643d035407524070740c0305159034407405540c0b5074009103100b0040408003502d400980c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 954487796 1250 954486546 954486557
    0xb19031d1b09010b070b07020309060a0801090b0f0f012019020307061107060806031903020304090e030306090615130305100f2904063201080403050a0f09080d0807 72
    0x42501c10000941400e00c240c03030304180204505e4002031800651164004081d006176403c00ca80d400124200d03600844013040054210801400881e03054403880c0714081c0190303118682001c044000c202611803005085060200c03102010881410000310255980c50350000e072030303170810410500300ba102c440c804200d12034043c604001c11154400c601d0504503070043d400400101d80340c0b100554460001030544d5425002e040c554000d05040424040811440303540115521840d204140c0c0844040b02c4170610260010020300c04c1c075582c0e1801e0300360031883c01c0345c00301152600d115110421784122050030080002440c00007091140104000c04c60710924a0705002100103510340004980101e0049141c0c0030080c00841640300e80701d82c01c4011801b01600003d460b540310145950202c4600041841d0704001000010320b0003420001c90864030420f08018600e400c1c2540c1c054200e0280301c0d41035042004214500081605c80c00c803002c000e04414050b16a003010700c2000070a50781080355010003240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 954489046 1250 954487796 954487843
    0x3020733060b1305120a02091003050f0d1124070e0a0b09031501060c171b03091009030302030f0d060302042c1903110c041b02160b19031d 61
    0xa002000103410172030a4040d05401a15a080100201c0d0181001400c0c0d40c0880380403001074420411040c0c284030740002172145c003501da51b0041c081c01350741888a049030061490044000e07010328880c10308400915201d4500d560b607000445003140b00403a0342d0b0703011002100018111a00c1c0000f40440302d0107a081e030307255032201f02038501c803060207100318800140c0744840180491410411580414480b5046138540b000a11601b9135440c03101d071000000390000600290f0b2441c084541c0c242c201458282910a10b146071006500d900800031034800003000080c515844030364640c421000745a004004100e620520b092181009040000d0301d0340148040881d00c1c0c054900268504400f1070300309a00000343d80c1c40d50100c0e130100c0d081044412034405c140c900c2c440390707559010b80402103031031400196070b444801500a00d0807804a140b0309001c1040c200512405012504640031105400034154801e4080a400c17001450311a2204800f10080c0080b07a030058404544490703400b100e0070480a07101d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 954490296 1250 954489046 954489049
    0xf0d0b0409080901210534020c06070c03150c080603490c0b0f06060d02182e030506090a05060a030c030302160603020733060b1305 58
    0x1101c4900703001e0810142801600b4580d0b101d2a0300641010396400c1c00507201140c0e40c03405050f2a02501c07c910b200300c0305a0102405071700d01d1901070300b14520b124440807c0380d112401a40f1841341200d01c60082c80300080b031500340900d641c46036004551104141c00c1c5008424009001841400805070014240b90046400c504d00020521820100810f860851a69004e007030308024040440c40d0a04205400d1441d146050505803481207003055105c0c00c001400030301d0080340f6030b00c1c02071000d8140b41246052201c0c41e100c01c82910b200000075400184e403000c90005500ca98014005900d130301440e642030b84804004060803401000c0e83c1b150440130351107503020094064460480d1070340d41181141001072075500854102d1500000c0207480035034916140d0710740c10100c601c43d40058000d45d10140c81004481102e0180300014445403a04500340b4800fa5211001c1d00c0110b0803100e040ca0240c1c0141810048143ca40f0702d401003052010403d035640d58006088940069602c0030340200c0898001940b03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 954491546 1250 954490296 954490301
    0x1605011e0f110102030c04060201050c12040b0a060b031f05030f1f110d0b09181903121e0509070f15020c15070b09030f0403031101110f0d0b04 63
    0xc0844600003100e14141800d42100c80381c0c90052450200020070036007014070b080a2008601503050001c0c083e986500380400030342980c1001d098501c0ca40380402000c2601245415050707000365016000302c01c2c1e0f40780c0c04120406000960050410504000207100d84103c0c2c1c0302c102240b0442205556041540c2e4208040e150b00c0b188801211542003000d442100c105141c0d616a15054494000222888001c8890030742c2d0700700d155007a007031950352a1405110720b0001078480c0c0c4a0700c800c04280c0744901c4558a1520703014100c0d060260404c4629a501c1010f018564203003100d020300da0200450000c82c400f800346030301c28144a40704940b80c040401c12102004c0b40c039009903080e03505203440c2580340c5615100b29203400030490045015036100c0881c5039441c5c400707101c42c401a12080c19102d9103503041810644001402e8408123900c100700303c041c0a0040c9080e11b048980609041d001019022041805003001e080c1d01500100c2c00940c840041e4070b0040584040d6004800403c4988044000e0004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 954492796 1250 954491546 954491567
    0x21c0c0f021b0111070e190f112b1a13020307090512031207050405040c230a0c020603091507080106091406090919182a03080705160501 60
    0x1008a0404812406501441d01e2200b00c4604c02d003240d0f1142d98603e01070f4503480c4140c40700300700074a0400140d1b151071040c0c0682034054800300d00030801c070b41c602074020206100ba0003408aa400500c1c4141450a1503400c1000c41716210a8060003c0f5141a00800700649100c00c0107200300601c07882011903280b58426240718980d10344541c035000342444100950007022030080c031220310040250301d50b0292411004c81c00782074651038a64640742040c003000152403190101d0001c101d445892000802800c680110310800001003842d40e407942490122615001461301940084c00001446586500060038102c00c92260344050768984800000710341c0c8010a1140c80000740740c80d030f8103001301081500d00c100514402824145041c00c8440841c440490442c1c0c030350358001d110340d0071026802e194000c1c07020000f6101020400c000c0c41d6943c203c0e220340707441e103500183c40800c030908080f2018241000c01454000a009460306003619040b03a803040c1211000380c212511800000d034550241031041c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 954494046 1250 954492796 954492823
    0x11703090a03020607080403052506170a021b060112110306040c092706090308090106030201080a05060a0e0a0b1e1e01030213060221032503021c0c0f02 67
    0x801c0240b641d020440b0740d80140b601944c508104020010000b5803c004001f02d1269a040400c2c260004009040c1c01c0c1c0340c01d40c05030003030141400f000264a02c2170906164040c91100c001038840602031808a003a2541c109180402e1107000000704e11380f040e548044d4039907441001c246052100d02d100341916164162001061084a000306110b600a241c10a0b401c003594024511500060004076200e2403c0d8450191076030f40d0344210520626900801d1980d0101c0d5240080c01540c0c59580000c10300f038001007440c02019a2200840c080740c0c1d640d0101d000401c0c1a40702c01c003450810b888150010003035111814450301650305181042904035401940e8403c00824100221102844003084800030000b410704059007003080d4181202604111000f8200759401080f040c580a801505261140130700d04109200030300412156100d521a0b034901c0e000000000030040100d180254080c3c003c42c801000441c142103003504807005541d200105060140d61480f840901c0000b041c0c0c0ca0360b03c801c1046 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 954495296 1250 954494046 954494059
    0x117030a03090602210f070203180f0420040810061a03060102012d0f1b0f021f0515040b06041403031e090102060702031c0f0905060a0501170309 64
    0x2803050354041c2d400041c60700d0003040e016142400c020603400302c00442c8030301d40c00c0d120b40c02000d00c44c88400810540368040307d02c0c00103603d1f150000c10300c001001d0079420010302c00d00300d880014a941d03d841c5c100711030313507400302c2c080184c011421580d00440c1e400c240540c1080b4482d42458100403010390040c80121340701441c0b0490350395503400118030960300c01040181550b40b180c0020a40c004d40851795102c016000c0c1c112000030598200e072006031584014a80409418101d88240402d40d0310b400d80e94141c00386c20400c2d5000c07444602642015002d603440c5006031808a030501c2d2100664120520810394400401c5130034a0a8040104890032a188035420040900c400e00618120410304410110010304803030403c83c02c1c0758030b0b0b800f16034010495200360402165460107540c041040c00c0e0045a075001a500b841482039200d078171410a828483d0406460340c44403124007001d507000c0100280c1003400d840c4549403c2c80b14001810080c454000c0403410041c02c01c400381400f10948290900c010640c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 954496402 1106 954495296 954495307
    0x2011b020a080c040c090311010f11030a051e031902160f12180602061b16051617030304060b0f0913230606120f011e05011703 56
    0x1719080c800400e030140b0000d0345280310101e14500a10786000c03640c8004400304d60380781100310411000c0c0400a42500c0142d407040003088d5507000706540055184c0c8800401d5614813080b130780d075200091644610694071000b03030010000c0006404e14001d242c01c06444003003005c0d000800490343c2d0440c00ca403184036141c1014490003e54140200b80502d2450030030044d4585500a0019512240300000c1d00f0407540c6000a0b50b6100c580003c04c00b06486c03c61403c203603903a0100c09a02440100080000344016168100f6001030315044040c42c1103449070350307a05024204083c60158440c3c407402041c900d030388075003000754860100c804510000c480541410340b40100d0042145040a50b84003404000000000d00c458000b4425036015180d03c103001885410800846109901c55080000748041c200d454401040f010380200c4041051f0f90366041c0b8110b01c424504620003994109220 = true := by decide +kernel

theorem cover : BRFrame.Cov 954316546 954496402 := by
  have h0 := BRFrame.cov_init 954316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 954316546 ≤ n) (h2 : n < 954496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
