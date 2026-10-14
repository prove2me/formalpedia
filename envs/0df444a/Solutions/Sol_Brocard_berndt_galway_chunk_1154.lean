-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1154
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:29:28.835626+00:00
-- url     : https://prove2.me/submissions/aeaa37dd-f9b8-4d42-ba1c-729c9398ca3b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 207374100 ≤ n < 207553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 207375350 1250 207374100 207374129
    0x905030f0a020103110708030c04090f1b0302090d0f05010b010201110304050a17041d0103151503021e0a03051006090c020d030c02031309090507050a0612020a05040306140f0709 78
    0x400450243c01541d1745d03841c540781c0402000e004907945000441c0f01d100041c9441d82ea440c0b80044110841c1c40407880c185400d03140c0050440200c8540100c4014a65949409619581c0c114002503010690120003400d105011409104000040d00102c0b900d0a00341c000700410305d00141c1c5010644401c6800410941005036080d00045e4103d0324845035410007000241000d849001440d40c1d28141c00340c00107503030b030030344010010031403131036030280d610706501d0001d00030b2089595003004410000d020080c821311101c0c45d600380d1690000c0489007500c40090001e031031540e42c0e040090300cad0310814101c802c02c1800c0c4140031410081502031030714040c529a00915401003125011002030440140c6142113020070000000c042111112050203041500c40001e0440481c1c0380891506455500c418001d0010490400c119a0028a8000c1d01900090b025940390200c4400322103d20079500024410b03071503c5a0300e4510030b107500ca580d2042101c1075000c0015268000240d07107032001032141086940246 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 207376600 1250 207375350 207375353
    0x51903080d021312111002071202030c09070f091202130203040507080f0c0307090c0516050a0506040605090606092e0f030311060f01060c020f0105130807060905030f0a 74
    0x300203080351055148014101000e0702d0910341c0e550819071010f409000c164030108140b149851003605140421607640c1d9072110381402c040e40310304091080c2803400e049805074a080d51418805500c0310314005111070840d14080001030181d00d921242c035400100740020104062040c04000000c5075001460855005003052000004c2d40c0001d204664900546000080ea4041004255030800d401c50280148000c0b40003450700e0118254441c91780303503041015805d42250020201c1c0d84207859000158400507240c2002460700c500d21600401900c50301e0300b004284140343e0701460003160b2200c240c681d0303a1110350412040000a94061a220103c00140d070448400d610074000a1441803910802c0305640e0b140032a600d211030360090300801c504401c80c0380392003014401c440d8805a80089002294102840107023409110580280035001d240c0e4082840c0e0b004005958500b103001882d828900d8450040300e0700d901032486040080b03080c0f50004104c2d0314000c2880403031410705d40024903408005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 207377850 1250 207376600 207376613
    0xe012a0503040f15050408041a041d0c0c030a0e12010902090711070b07050109020109050d081c060509090106090e010603080f16080c06060906012d0201020c0f0604020a051903 77
    0x20000c2112021000f0030301d25268030085c040d0f42c1c0706901410040e03860300d261401e1035400380c0410496010004080106010071144030081d5010071000c20200540341c1c0e21464007a00c2131003142c0100300184004074034101c4042d80620b0a0210740c03015611120052a28820030f0701b40c4a10004c000c5d80b00f403003000060b280c2841080c450561b400035000710b42d1225030b180c11250055000300340c1540c6d541d4540b0b03041d9040d9600041880010b100a407090075140619464041c150b0085810022110500c070500009049094014a000e818020000c220a051110480d8001c040d10b22543c0782060500d200011030140600c940c1040300c0e00016014580b1071944505103895206810209400d10740c40e4440020440c403c01509144421038001d00d01c5050038820015040401090641001011204d00241504072014038805000f1901d40c6c00480460003c280e02900901e0030720702c928071621002403080d0400240007805a0f000341c652039000740e140c0c800d00600c0d60701c0201407540300c01c030307181c040002500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 207379100 1250 207377850 207377873
    0x403081602031608010204050f060723010f0507050705011416030f06030501061205011401060c1118090106031407140d050a0c03061a0118090c11010e012a050304 71
    0x10003410f8070040c0703d0800041c01c5120440c3c1003800d16030b50119050029041105012082501c2100c409091050945d5043e120003e11506810981e50690304034601c0002501702c4030804100100900c21483d28200040281d04a884151501d6080c400e180c0d9010503071742d1040340200300d241601c0c640d0070203131541580034203a07469039541c110380d4840740040480d00a101b5000034000100042c902200306051450070f407220a000d24102c0044003004010094001a40b452000c4c2e202e21030b8840e00710040006000c83c400c8150f0080c10140c983e00b0081101c40c1075106005892080f800b011038014800c0ca03c5a035140c0307501078515410b0811808404900d01002c60f01000351050084486000785d544d5404014065075204403400394039120b11400d9071134085452080300d102882c00000d105907010011140b050380344030f103001082d52903054900300351103400011a082c0369080203208503501e02211030700134107000d0207021000720b0742c252842900d0751280311000141081d990307086c255101d58407441079042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 207380350 1250 207379100 207379103
    0x1060807051606020d020a09170607110a0203101d060907091d03070606050a06030b0f040c021e03070b0903030714030a02040510021b0103090b04060b03030702060d050402011404030816 81
    0x107a0b04154800510640000c080701c0d0070b0040b0260b2030f0000d001c40540709424035048840080d1100010200c06480010b40917880483d5103444450800441c500c141420180d52020f034250145040b505480304042d0041c86c01c1040c40b480d40260540c1c165151511030300e0030b80b03040c480c0c2d400a07601042414807603000003203030746d0040070031103c443c203100c440300e00e19031010604075029a1911401c200c1d0380f506070304040007002c1d82d084c2807210240c0000003c2e00c0ca001c262a1300d100316a070b840c88440081c420003100d2a04e0680714600440040a070003141e03580e4110010407a005d2564800080d0014000b200350b82c002d082a40f070b40c071801c3c101c40e4400700d00d07504010000490030389d090000080640d140e1020b10201040303a0098148050b401306003c001c8d10444114906042c00c06000f940020051071489034040c1c2c000c41c0002da01601179001a09511840c28060352043c1d0104488005501c1c030f46c0150f0149100340c0343c441c0c01c14a030400c0017012f4059403102900e00b000a0000200103000d00200740340c1c0d02d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 207381600 1250 207380350 207380377
    0x5060d0b01051303051515030604021e0307030303090c0f051806010309021f11210c0115030515060405040b040b042a09112805070c030b090607080106080705 69
    0x603d00000340b49180c1c3c00c650017601c280e8415140503040020748100c282d0402004041408074440010100755079910241000380989014070710102c0030104071041500054008083e165120764070704006014000c2c0e010207031102a681c810000d50819448590021140050701901c00c2c4045001803100d4a034000384040c4c1410748070320003040140d860002c11226505d14600c520442c02c0311290003003010610454cc520280d02035401202c10f1111144880700d07104646403119922440d00380928050003003007100e80c81d120b4540310b02008000c408070395108011407490055986545000422054841c143c401070700d8100d4200124003c221030360310059103c1e001d5030724010014031a010425043d04601180c94220400000a004082503801450160b62500c94240d09055880a41f03681c0028480011004020042c00460002e40980d059030b160701c5d00030303401c000c50503541d0403c900d2600c070448100d90503000d200f0003d01685c1c02510081d043e44c0680d078030400303240e84451091705d00b030748101001c2490 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 207382850 1250 207381600 207381607
    0xd06020904050406020a1b020a09090303060504090c080f0604020901230d11040b0d02090a1e0e160e130201080705130f05010806010206070e01030f0605060a021b0a05060d0b0105 78
    0x1500e4078014070f405280300ba0b0005035100d900030001000d41a0b0721203521042d418030906080540ea0320b105c000e003611514500022020107a28007580108925804075400134241082d0701c05004410f09403204641002c425139000c1000f00c1110780c1c46160880f0b00070350090845005004620b04141507194074000c290319500d486d040040094441100501c0403a6541490002541c050a15010304a104102a00d05460008242c0d0020310720480041c1039440081e83c0307036160283c0c079009017100c1c52030700404401080942500c004450302c0c1c49a02d11881b4442102c004002140221807260520a004940b5588041b20295004452108000c0c200c030040003003d01142204c0b0b801800e1020051245e130202d110507500e0180003608041d13008100c030381550044801c1040d015000108c500c40710070f0900e0f00080451310300c150f600041c80c007500a107810010100e07003484a5500000c59400005904035400303d0540c0e041c040045079038a60050507045041800110305c050b070b041d00140fa40740e0307050401505 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 207384100 1250 207382850 207382867
    0x1603020c0118051b01050d0b040b1512060108070e0409151401081504020a09090507150206180321150603070c060507020312040b040c0b130311060c0a020d0602 70
    0xd4031055500090307034812140c03010b81001020055a01540c4400180d030095054000c0081c20074028051100c8009440f486024a29512a80091141c0c0710040c041c1811540800d40c42c0190b8200d008a001c113407a0385400304000358040c21046201310b10702e54560944080e10300521024251071038088442e200080c3c0c940300c1031031550141c04c90510f00e20007080910340c504541580342c400c0d0f0003070040040621b070081c0405a103991512005550350310f140461241da0a05c0c01c5840c001141d40714024903180e81c118811586e60116265000b4402050008545c01c81c00c090151648150100b155480b140907a1004042c00e030004040c0d8412052542911f01d5103000000c02c2c4c1c2a4412141d100001d410030800303508008140c41659001070385840214101684090001c1030440e01510140c51055118001401c12000d4000e24001e8117618400c0340d219008108000c02c1c04c50507000c200c8840983c403000040c3d5090400035034a060342d13036074000c06600030b2540070b000c44115181c0c000e840142c1c00700704886 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 207385350 1250 207384100 207384103
    0xf11030a022d060f07020307290a0c0b0a0209190506190302041208031609030c05010507322a060a0c0807200402070506150105090901030b0406060e0705031603020c 72
    0x51300000b002070540c1d55181c40c41018100101a0020b4035801000d074511649100014030b080390321203400b44055902c2200b15029620030004500c002c21640b11401008004806500584244e002c10349455407071400c0401d0b803801607c014010940c001c0c00c01d0101d40111807044003507405418050500514158581400c15450910230310242c0318508000180401e0300e40e4044095041d5020303260000345c035811656440a40c0820303109042c10060042410401c6c007140300071051500c00d030180c0000900c00740995a0b842d021982c10311035014004c9001c412400e9400c6c541d1941c100341000751007060707482e6010401c10305800440300e40c000c01c02c0203408280007403080002460315a0140740100b9010150401508d010800001152f014a0045c0600000207070001103550b08200b80c2504162500180030048509024201545501002d040000028403e4004d4914000c5016031414499151516403400004100307036880c60000741c3c200000341c1c8c402c2400807880100c19182c50091301c8d0407110909607 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 207386600 1250 207385350 207385357
    0x10080303040c06020609061b03060109090504060902040b042c070f03030201050a05010b040510120f0906051e040210111614010215010b09040b06160f11030a022d06 72
    0x2c40e0149900300d0203100d8682c041220560101ca918000d00091400d1403c1403424210754800108849020001c20f500d41e0280800c040a4510707074004001620b080c0c00e002c0c001d001c1c900b41c2a070062340340480c6010203003854061004450300d0855519003056050003240c8038004c4094402d80039004801d00800c20110315518030000b10f000b41d0000c13031203003011480c0b101110700c10380c0401d0b04c130402004100300903150441425a403c1d29810030600201c0001100700241410206800505141692072000c010542d130109010f9070b04014005400c5429480d20080b004040c0d4010358404100e0301100340703403885000c1c1c903e440c0c21000c0c01e950102c2d60b021034040711140950080f4072183d4010300744a14650781001245980c0d02c02040c1c07411194500003000700140b01e9403804030b00494840c0c14a400c50b46802084032802c55000380d8200108406040c420800240ca00c821a200c0c1114080c10005150005001e6041a00140500c8010700030001409011041c450f19103440551040f070712005a45d600081c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 207387850 1250 207386600 207386603
    0xb040e12070809041404031e0e090a020c16060504090501050d020f0d06020d0221070309032106051f12020a0203041211041406042306040c050d060b1c0c0f05031008030304 75
    0xa2314500005903200f5111011452503640400030390711032009055544440356a0404000200140d0710907041c603207581030114450010504014050000421591180081c4100c51107a142003007240d8031340c0c040058410707681d44065406101c007460304401d450203403901740d06148030f01c80041c54000c0180d858001d9800840d21017034400170f5002c3c5003516404a02200303900c200310f841c04120b40c1210b030360301030031041d041441003151240200094150446d240d02960280000030300c1c080c0a41052800c1c4506910301c6148400052103810518211420318001e5880720a21600038604007401d0950503056490801026103081548090000c8191100d10900000c0c103280c5049076070a141036802e000c00d940c81c100122240140c1e48110142e80d402e40c1d0764071a00040111008900d10341005001c5a05001d07030100580440e04c0d000e000070b8080100d40c010311004141e00c45014101d03040c0c441c0c0d00101c5a10243c01c42c00300700c1040111007118440d00042d60700400300301c1c0d480030071902d8082c554075642003141d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 207389100 1250 207387850 207387857
    0xe0a0b0c072031050603070902030903090f010903030507080306040f05150f010e01020c06090a0816051008040230010204030302030c0f060606070b09010f0f0b040e1207080904140403 80
    0x1d41881e50030310b403001601414070907846400c00220408528180c620b0070508403d241d6445000c100d2941c0e060100714010003030034009640b64240341c54041d4a0742d00c1400011312455841e1015425540201150301c00c41386c054444c5800e0442d1034481c80040c0e40f00070000c82d03103d81d440001d1003003d04079201e9240200d0781101c0c03200088201c0030134800c0c000292110903050016000c1120641c0c2e0707001407000348440055a040b5101c1c3e04080215079100f0f1203800c066a54007828103584c1203802214265000c461701190b07a07403100108050251110300042d540a50085031210030035000302c100c007650840c40c40c0c142c042c0b546000440b031452401c90308150402c42c01070708001072614541c03104000b121524080d2001030710541c00c2c4070001a2240c856518000e0201d8000c200181e40c194080d0b100c6052228400070078041034000e002190024500120444d01c03035460120040074000d000a06842508044131601c0d250850713070f403120511030b0050819158403070b48503105506100c81130400c3c0c1c2c1c041c9202c0c1e00c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 207390350 1250 207389100 207389153
    0x903090a1d06062502040b030a1a0c03100b09010c0516050901090605030c090c04090903050d1b0917120a03090c0902090906121e03030108010c02010e0a0b0c07 70
    0xc1c904002040c05840140304007000e005180c40184996801c0c180c000541c5807100200104d4808100034040390014158180610740070b8000f800580e8116018800c141403200c04a0380e94050101d00034003041d104d000381d41e0f0710100700f40080d160758170043c00455030506000c02040400e944403880d01380d100300101d428810411081049040802d07032075015080640301400f241d410680400c0c1d9442d00d240381c3ca03200e0001040820381c200510b0045a003e008945003d01c20200181400750290f03101c80c080484091038a04492101c420302c150fa240080c8503541c82e004050314020072500101c02103406104203004285c000030729001c28a0007030100d202e00c1d1314042244100340c10000107281680d4090364000e030040014250715580c8d210380c0c6500c0941191481c003071a055480240c41c1076002c130b1640d006a0840c0c042c91004603800401356048944040003407208441e01d807003c03406d030303020b4480b010305540c400f01203c400641410280c950001e10b2203a0030742060b510391142c00c000ca0030124841020304054 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 207391600 1250 207390350 207390389
    0x9061201050711010b01051e0703050f040305030301060f020604020a05061c02041806060c0506040303050408090d06050a0b04090302100e0102090613090b1509040c050c0f010609060e01050306010b030903090a 91
    0x20700485601d05c00c00d0901500b4440c00c9403201c030030740048485100c80d02ea80015002c0070103008009486192010102c03454686480b464810f40d6580280104004035882250000e0403038030000f0315904c950b6000e00415225880c08040c0001600248d0076071a03841e520300d110009465540c03010700000c2508455804010036800c1d80d02c811a00280c125a080002442401021800004119070071651614001a4944d120b05050126000709085241d00105904c604800d014154104501900750f1441c01c0100c9400d04041000700c4401d1100240940c2010344600d002c800076501c400c0d03038070032104005440c0004040000d1280e501140303601c80d01040d089000e00c1088064460341714a0304042e2180c0b520104404100c0c07815009043c8454800c030349907901411003a00c030b10191440c0e1a03480d421100c58884241186010b401c85000c1c82c201145071003400900100e0040549048035409803350009900b042da07803029551004006040511040012000729201c6500610013009401031000b40704445 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 207392850 1250 207391600 207391603
    0x130c090e06010327020303070b010803280212090d021012050c040b0d0b01030905030d061409060609100c170c160510030c031d0105090601120b0609061201050711 71
    0x14080504062900d00c6507a00c4155005130140c2124103924941c104091a20010b480c51040b00001804000b050000080035880003004c1c00c03035002c802100155a910110071064040080b4407401c005070320040584e15419001c10083c40d14502c003a02401ca4602c15402240d03d8905440c030403000150500c2e0405559260b5119460b041070002604a00e03003407400070780c11500e000b1141f800121683d1b414218000d607010703600c0b910015900c10103480c0ca95030540c802c03030b00811551180c204a421100818160343c60185c10040c41440003c00302d038100010081400070f403c44e96440f4806010f0302000490219a0b0b90b08414a200f4031804d1242e0b0701e000c2c00c00c25034208041520084034075a400001070041d0b9550359042000d1030442d240c0054441d000503002c4020b01404030000d84c64410341e500744810305070190403451168030f0100c00c03218180da94401e000524140984050060f04004002c1822860848c940c560400d038028990b118402e002c1d9442070844109444000c003040c5e00c2020481200300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 207394100 1250 207392850 207392879
    0x3090e041a0c070c031e060e250e0a020f040b0c010b0f040510030201110c090a0c0306060903151104170607020601050303070c090b04020c1b0108060405130201080402130c09 76
    0x32007015041064580e521080b04c100c40c000103086c0007003007070580c020300c907010b140c1114950400820f000700e900b03202425417181210901d01c500103400320880d00c10250503660040448a9480c01d04c40d480c1d59204859000b9013180c044801282c07010000007a84d603052002824181410600004520501c5410044181c41e801401409141414100003025040500c15803c81e031b020f08140f00a0a20382e18403604103004d2406a0380c0c00441d0030b00780b2410104907171101c9001009920100015926107105540e404803070300c1300915502040b010200f000001d508464240321000100300d00301074403180400480080d08189002c0d65210004202c00d071a81048044d00404064009d940350007950703140c901c0c95118a015552080d40c440c07441042d291100e50458600c08240c01c140d074444070740b05c0000400b410503d4005400102c91401040c190b2500b8498107010349600103050031036031125070040d203219000500aaa200141e40b02d02e05008001c0e0007010700086d015039882c8c520b03905000c0860710041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 207395350 1250 207394100 207394111
    0x1050f040f0603050133110712050706020606030a08160206030f060f10052a030301031203050703020307120c180b041d0705030127060b03010e18030301050d03090e041a 74
    0x16000300c40c1e601c082c2d80108001d10008140b1044c1c01c0f00c3c42003481074424170001f0800000611401da800607600e4480c4c82c108201d0f501c1101a038044550b40e200490f03543c54151290740e4150860b0240c0307000a4264270091007000d460000048541440d03400049443e00221055840b081a500801ca0f041c82c2a4008000101c81119120905582084010030601882203200110b03ea0001390038501c800070681d6180080c4050700b265600e40c2c591070250f10b40342918403000c3c0840d043c9001300300c4550003402900d11031062035454a01c20401051102d010380140c4540205000c40040c0103854484442c900b0b030040c1000f5842207a0303852400034100001d0b0b0021a80104121800051041072507208040341d044801442c00d0501d0382e0003040d00000b8a03505501c41d46000d6240200000c0e501c00240044c60407103103600e003107140303d80d6200d40d400440e441c0c50103014150b820802c01030000c1d01e0300c400f13140003040c0a4a001e25080c2e4032000c05550440d0306032415180c2000b402617800d00c60440012031036214 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 207396600 1250 207395350 207395369
    0x60305010b0919020d062408100e06010c1e0507080c03190b09030409050f1b0a08010612090807060b03070f080c040209041103180606060c0c0603040201050f040f06030501 75
    0x1841e1140f00c0100301450b01040c0c100082d0001007104600c1c400e078100201604500308200c442008580aa01d2040c0110f207600c8081490000002d2541400141750002c60b100482d5218155440c04011510344148010441c1c00c0d15103204110001c0d4611240d640c07040784100014440181815440d51030314240910841c807076806200c0d40d20000c0310810000390140e90110541c038954841d404003030700b1401180c00142030549083d0402005464a40c01d640c0200e00b0280c1e60840707441800c100000c14401e03059000046216a001001501d2241421022902c850b000024411000e0f6480020f264031007001a030b4102c0d21030520040c24a42441060000c224510b01c07001440e140004060322504514545c520903580070500c10001e07102c43c0c00407800e407810048066a20315040002c8400103010a8003524148500d400180850801c14121854024504010075005000f034041001e1540001d108a040040070b0100c000b540303c406015102400843c60341d4403015060060040444038140d0001c002d2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 207397850 1250 207396600 207396619
    0xf090209010507060b0a0812040e06120319020c0604080a060b0901080a0b0403200105040302010605091302092d0a051003030e0d0c21030806060307021f09050d03060305010b 76
    0xd603030424102c60400750b221a01040001c160b00008031080e4039981f0aa50720701405e201034801482401c0100180d543d080c250301000d8440c0001d105618941c1d0306010000e0f0b10070040f07624820b000c03607203040c54100188104c035005050200480c002d900590300c0720380d00c1c2c1d0041c15100204036141c01800071a99040c1c2d00410390b5890108055550310680802500034128500420b0030326118001035501e1240c0860004031000c19417010b40d0081004580a074015481c045021076586803104d6000d0041e00844601c1c4411071441e001c000704108082c03c0341d02c132104403d034481e070346000b44030150381800301b0029030071300b00d03c1c0c1b490b03011081c0c8100416941c9010181c000c18000241c01240c100b80700503007642c24140c840c102d07180c9000c01402540100c05c0e04040071a03200d02c0644100490301b00c0c02d01c26601c0007055128582441107a00040c1c1d03450000d80c1000d0320501c0c040035058080c081803002c4020210700342e405506c650b4182091140540d002946900090050180074041c044c8170302d105442c440301c0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 207399100 1250 207397850 207397867
    0xf07060b180c0309030c01094e020106050d0627020d0803070516050f0706050c03030606071a01030b070f0f0f081018090b10060804030f0908160f0902 66
    0x61040000c0c84602c502102001060074078004106036403440034000020002d01d191402c2215041e841c59490790b811500124519500c0300301e101c501e201d0341c40408030f0600340b0a81103045540195a1400180031590f0b02e420024072540c6400000601e180200d2001410034500e00f0703902500b03900940c0b620300c150055003242c00180ca603031004051244c3c0182e0700d6078498492000440b41c41c0308a801401001040d0072998041c01400f01c2c132218070031503520440303150583c0ca000603540c50150380e00c40ca075150420300002d0440e04003580180f003001c0c07007140d455150b01e82d80c08050301c02d100300780c20644040044004200b01d09400c030b0a680c01d0740380c280c1000710b61443d03d200c4c0180145030380f6900500b08643c0a0100d500306103002c000a0280c00f940d41e20720f01c05000c1744844401841c0f04002030b5000c400400c082a50710009186c1c542c00d644065132050095907032510241d921102d0b03000c10780d00700403800e0310001d000e070030520003040d035041d0014180d42424540f601da503526107056003095480d00d04c1084090b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 207400350 1250 207399100 207399139
    0x5010e0f1507110307050f010b0a06120c210204090b1516032615040603020904060209180403080702060a0c0e090c1b030a020d020d080103150f020f07060b 68
    0x5110300d00d21003052003142e035210300031982c10000d04066500c502c400300c0c0d098100580850f11a60300c40c1d940d0b00800c40d48140e0300c01c103c0d140402384900c40201302203012038010495590402c4189251505002c85c910401d0180c0107802c180402c2c804072282e03400301e020b00a5980074080c103520700d40b0031a903034200010305545031070a6200e04000040444076146c1c1313080806008000c0b000c032100e020807074405082201042c3c8107050074205c40020b64009a13100d007415510307144c0300724001d076074029055001c0c80c2c2da1503030b50304c009501c107407030460384004080155008030241b142623600c2617200340e0301c1003070300e0410b80300191803c140903042540da179040a183d0445c1a9200d0301c50305400d4002c48103070915442d0005500400c1c07055030580c4001c03014402100010042c00002050000c0040c0d00b180c3c00401000d6040b40c03209041c80100e8005010710b8010400b0a15000280c8020300200c80000340b034800c0c650200089a000789071107100440080b031910240001c2d0302c40c40e02c1040e02aa04041031110305942c01303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 207401600 1250 207400350 207400363
    0x301050402011e140a02070914091c020102070f060902030d0305010308250209070c0506011a0a03050603010b09010e0711160515040806071206081906020d020f0409060305010e0f 78
    0x202e05510f00c050010009610500b5001c3e1000c1088001d10355a108104009444074064080ea4180a080000c45208990700818641c071600485001d002c80e4003a062010310040b00b038001e840210342d000c1c45103002052200080108991240740d0009a00c0c0e141d10526003000c0d4512600c8082c0342c6003c0041000c00c00c0302e4103d0b109440313401c15100008178092502d420710104000060742040310842040442c9030811038504040b800764040340d4040c1e982d4072002d0354040d40c2050350740c2160b106000c648141c82c0681c100f1508601d0080c004204541a400450b624803400d030302080c210200341050000c10340c9c000000741c69240c0e81c0c1004e41144c410b003500d0180315894074441d103406146010310403003640c1640c6040c0d074040d02800040c0e03501828090300080c02440d40000c0d10310900d103040c0300011011000a0401404d0407030461100100546454040c000d400511041d4030450b020841ca40141c3c142c40020405403000d42400116130f07040d4203006003110604407080c009640500c260254518001504 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 207402850 1250 207401600 207401627
    0xf0112051b060f04030c030501060b03040f110a0314060f01090b03060402090703090803010b030f0c0702030613140d1805090712020706060b0c06070e09130b1b070c0311030105040201 80
    0x3600708400c200e0010aa035440303982c103181c0349450003040100802c908100d107481240d024000a120503a2075034455113262005503002403044121001c100c0c000b900b00c1c804daa800c108000d00303c0d403c0a076240c90345800e03803256244400307182d00702e142040000c0081d5540c050140c0a000c504100d074a0020002c650345010190001e0310591f4407000140c0800d100790001c1c15103591004103207440b943d4841032203a0a070402d84182003c5602400043d00803800c420075250003640081c002c200e030751141d060b5103081d6205074009603404c0505989183c4440310402076001078a00580e14007505500d0074201400c02000783c0c008a10540104d014440b0f003651001c03800c2428440300c600182c1d180c00a203403400041003c0d03402126102c0000c282c12600900100340c4c00d01c10b01d001d8a510404000c02e00070400411801c032008079600310481c9109011070a04425075074024101400455082c140e115101c80c1070f00080ea040310600c000050074000c0000b40000304222070415402403015007030a500103071503004281d26 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 207404100 1250 207402850 207402883
    0x120305042018060303090301090b100b0313080315040507230307050913021608030402091b1b100603051e0615010507050a0605010303080615040b2a03030a050f011205 73
    0x452032644c1c0c00c0c4112501500010020014802d2500d030541010703e00700e5100c040d16013521400102d080782002200d00c91150040c180020810300e0381c4210b56900b010300380c9592502010b07124045500e07070b80318450044410b0346031b5005d14494150327050441176107500340003002041882808007058000c0c0590b542a0005c0b10500802983c06101310000d000d0418900c400d510500b10100c1840040002540071358001d4420504a43d01d83c810034004c900404031070241d4542c204400c0c181c400140c0110204050500c0031fa03a11010b1084204c0d0581d0941d400a44094015582d110310100c01c02200c41c03507003040390000d800341789850548694542000a43c45042c80b00005000c0e08104090103150f03503866003c0b80c03c11095840c0c2c00c0042c841034045070a030380526100f10390080ca24581d0700945080315a8048041c0c0b4125409030340d402ea08406a1034190800c0c5c51382000410100148081c42c454802900c0014051030000e100c1007000e6010307480604130030400c034a58008030f00c0205800c1080c2a8032030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 207405350 1250 207404100 207404149
    0x210060806240310091b030602270a0306020919080330040f020a0306050a05070e0103060e010b090307050603010602011a0a05060706110c100624050d090f1203050420 73
    0x140707a40b8202c00c515136042406c28800d408030400c145a0f000d400f20100c1e555551000c05803916001c00071080d000621075020b40340803020400034105400401c0740000c0074241008012620030791102c40c071016003000005410104400391401c46117034803010317200c104680403060324010180b41e0890b014050400f824848008101c0d4055441e0440304c0001035910000410580c50020b500030010582500d80c84000b84c0c06120380006588240103000c03d45003c44100e021300c0c1d280414254a561040000b01d405009081d0002110750320800518021b2170700f80c00206030500c2144151602c5601344104074480c0d59000824001c94580c141601c2e085a400000054442680c0030189114040c0e071402e4001481281c2c00102d00c49001d03003050088414505e0a0742c1c1071403103c240c44242c00f43c00074544e000520148244401c003281c540028a9140c05800c140452041c2a03c2d90020050301c40440d0010a0b150001c0c08200603511032540d01050312104081c000303010340c800044d144620a0400755180603500b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 207406600 1250 207405350 207405353
    0x13150e06071e0b0106031d010606090603090c050d0b0109200406050705070806010b22140607030c1e0b0a200702040605030706180b030405100c021006080624031009 72
    0x54041150043e003005441e201d540c0c0d19403000700a1325400d1009400100404d4001e802d0390014000c0f0b005488040d12000340daa810400304400401c131a00080d2051007003400d0000c2c0c5c40c2c441000035a21217002c0d105102e11981808000402d545803190f100400e18000300c11074100e100c4e101c00343e8081e0307280c5203441c0350f840390300c0e040161510401d07401030140c0307000d03150001943c040c055000300011081d40d1a90140d0710f680c042c80b424888081e203e0a40c0c074503080e4020f00c896241610041c64014441e04000b802c030b001540358250340c0512642800606200001c00209004080e10705507485203103803800348400300d4058900c403a04200041c03e4403d4150204040c01195195041031000e00000350889803800c0c0e44100040c807916170720703008207100a10900040b49100002040300e1046400c14002d015058000703040314020445a01903004601031610000c1c59440d1070301440340104034410040510f4100030307154100c5602c0c0c0c9802002c0e9210b80d24480c030199140440c070001c0041c0c1503000007800300700c1c6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 207407850 1250 207406600 207406643
    0xe01021c0207053705010e090405070501050307022b0905090613020c0a02031209091e01031b080a1a0a2304020f12060906060d020d1403040b13150e0607 67
    0x22441d80705030450a0007841c4040840d004c0c54201141c1e4241d031101000c2c980c040500124a10036134000e009508026401c1c4001e5020b1001075400408610460307e00410910702201564030861002480e45010707000032540c5940651a038000d0181160003103070604010700040c0b158150071524080d46500460018540d02c1c051064141c03658015060342c2001c0c3c1d621076240f4281d808803000d6031082c81c20401042c81008800d06101c0340e04510303089600142d085855103480d46003400f0042d00c40c4150848089410b1900740305104081d4810180703111000c03886910f940044074010b2880c040f80d8648803010070700c0422040444204440121002c43c991205d00200f10641c200d00025034011740c00003805007049500007603262181c40c8040c1a668591502ca0070010f8000596002a42c441102d16490002c150312001105600c1c2401c1c04a1340f038a561002c16818a82058441b0450120802410444040315040c0c1b20741191503032401043c1c40c1d40b03901c00541d8a01907800050802c40d03000c4d4008041c1d00a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 207409100 1250 207407850 207407899
    0x15040801060b03061c05060f0405101803140a050403020607050106030506190b010201020910030b0f27060607080403030c0312092108070f0c1a070e01021c020705 71
    0x100001c0c8400703a1141c05040709a030007a0707400790041091070704150720101da0025042c01c10380d10201401154882111007241110041c0c41500c06029072034260451071020300ca402d0002e0000d459071103d40d400c41c00d018181d0000307404040c0982c4000c10124011550000450382a03039411030b92030b074890a590603c07500600c400d40005050340706070002e100030010503101d100030101c2c0e40c200901c407900c0305a00490030307400350001e410341104041700d80c0070465010340c01c1244604405083c0c1100341e01520005449407004421030311282c0c55280d070503901e000104001e96030104050791041cac0303000c40590314622144510f200240820017016032000405102d0917500c05410015401841513a506042c402d040400042a00842d140092944110700b80108800c0e8425800c41d00c4548156030801c400b40c0c0d4141d103e08003142e402003112500141004600f1013103000d81c0c078998550320052030030000a890324656140c21100202040159814a98006035140945070291104a007402c000d40501c0c80045 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 207410350 1250 207409100 207409109
    0x604021c0c181d070e06010e041401140102190b04080705070b0708091305070801090b0409020d12090e010e0130030206040b0c0903060a02030711060106030608070f141504 75
    0x8403920b004159181164100750307a0071540c011055071110510026603035038503a034400c841c042c400c001c000458640c0076a40c0440032600203080811880542072010120400980005110704000c2c010111556410000c920310980e490700000b00302c85407038451003800a80200020000c0e040010408204103080c010301c0c00400d80141d031180c44002510b058500c58020251650041031180404000130166026840c002e10040e1a0f00c0302030707402c05c00350402408000d05420380003600c488030750340161070703060901c42540d00800301e0030000524004020403010a550000b40c0e0243c0d40d400500c000500100e000d4119006808400c4685282112603a9900000309181544201d1161400185500820541c1c800c0b449184c0c498030b41c1e616a81d070b031802030040030911078243c3d0180d000140303c0c180b42c0e8015500906141000f0900d4205c0141031071401c40244c104200107a110101000400d0b002c110354005030079803500c0c03560054140502c056240c5501f401300b42c4681c8555003e81c0f03440700103500711005070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 207411600 1250 207410350 207410369
    0x1a090a0314150703110304060e120f0309010b0906150a090e0c1305090702210d0504080703030e0c01050a0f0e100905030c0321070c0e0a0e010e0604021c0c 68
    0x4501c019610b601c40300b809141c0128044550002081207200380b084c071302c4500b280e0644904540f0385132161030080c40c0e5868075814600c1104c030800c0300c2000c0100901140010443c42603924504001c8042c2501d043c1107100b4090a0300c10203201181e0b586a8101403110781403458241c44210100003150315181640c8040c031041590340a00242203403040c010302c0518048844e10a4003540e039014000f400e4411591540140c10007200d01c442d07081c0b840d2482005c514151040390400700130030340540450f081980c0840f00303041300255140404d07405000311300411500d000034040c96181e1600180a41c41550350880800c0030311140039900d180110080e000110000d065140110410b03080944100494054144284103c903003100c094903000a01e050043c681c0e10b2603440301c070040786002440b6003001e60b007282c150100340804035032018000304c400c3c4a00c0e050320011840d02d80c80d409203421140681540300854000c0720410002da01c44030040070070102c1c0c1d0400350324050701e14103041c1a8284541c0107401130 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 207412850 1250 207411600 207411623
    0x4030807230309190e130b010b0306010e040c020312040b010911090a0303030c090b0f03040b061815040e06040506040c06110d03020306040e060a060609050a1a090a03 73
    0x52000600240194520598034806180544400800c5002001560345a103a00030002e0740b0640c00e100401140c9028010303880131074113880b02c0c2da05201c0c40c030441c0c010703031100d07000b4201c0300a01240d00c100c2c038010007000c580c1c549541003480008000c1c03040f001c0c550303004641707403006002c15a2007002215035400360342c2d500c013003682401e00d40203031100028410391406600748403101806d01509412201100e000030241d2064601d19a0150050308102902c0c005101c0381c4400081d5034880c04000300f140c02001d448aa59038502072511604440014140300d0049007901100b90003160480010741c0c00204c51101c0e81241d00e00800021301801d40c2001218030360148009100c10808002645400f43d40f054045a440c0d82d00d5040403100d80c1c2c01501c0070f0317101c0ea2042c50072400440c000ea00941d080380c0080c0002c80c000b100c40d40c4940c03500c0d505441c9400d0580d55003800b0000c1643c050404006060b0481d05ea8400c545080e1880c1581c6c030494114010a4000013660070070369503070190040083d81e00441d001c41 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 207414100 1250 207412850 207412853
    0x16050d0c0203010b0f0105031503070f0f15030c0203070b09070b0c0102040312181710090b1009020405010c0305030c04050d0b1906030b15030a080d0b0117010b1e0702060403 76
    0x210518240d400c0380290300f007100502d19850a104c0c1002481d406a590034203507074403031038004401c0d102114159014010800c0c007241d2800d0b00512100a400041121420382d40f41240c80761018a030301c4910403c05203858a0070b9140c1c2d81c04011904030b1500030610711040d80b520380c80390b807c00c200395010055641d80040c800c01d4600e03064001d031045174000c0782c883c24005031a2000f501d142c2502c40104411510700780c0140841600d9414500c00817400404494181115004070411243c0510090b01c00843e04070400040002500801c0042c08100708194101884c2c0800a03150303002d4210000c043c80300100c00641307070a096400741e400400006149040320203150600400c0d40c40244e4429200049010b41240c40c0845070040d601100c3d44050084071075500c2062107540c4481c951b000580c5030140003000c0012800c07010183c1403428500e400003d005c020040050404401501e05020101018004114076010542910820392010800c0344504010305c1a109503031041c01802584840040350120 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 207415350 1250 207414100 207414107
    0x9070e10030605150310030b07140a031407020a200d080708071506080307020607030201180507170619050c0f0c03031008010525020f0f0d27060516050d 67
    0xc1101c005607649001880004c0c40c20100344012904681020740001040000070034807003029901c0102454691498509030100d04640e90010302040d0002e515001000822000301c203515401404500003015003d42c190359041d012044954443c40c880c92039603000045440310002100c4082d88814065503a03420b80c42d004002da0410780080c0c464000304c041c0090072180a100d0794041da080800111f04280080d400c00c09150301000080302107548801c0544030080c19002e0340c0194034455005051001e0609140d0b1190140e10031100e140340d4841428000d00c910143c0c181c840c1389001000104866480c40c20074800c0e403041003143c117964800001c4c0641c440d000803018501402d09900d4010307107980c0c1d0b50000c500340e4000b680c0d10000040445454500c0d105510b4007407108116500590f9071007403c62400504001101144800d02e030880d42c168031a565010781d42c0c0790500407901040d40000700178004001005400d00407002030090000e01d41d904050941d00c1e03081419449401c036102c1002115004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 207416600 1250 207415350 207415361
    0x6180207060b061606050a060306151503150510090305030304080a1d060d0c090b28030e0a081e0a03020a020d0815010804060e060403020303160801030c030209070e1003 74
    0x70344105180c1040701d5000e00e41401100d01d102010200b16204c00c20607104d0800900000c3c000d01c000076a203240c00000182c00b40a65401c4841d80c2c92003841c6c0ca4a071107034902c500708003802c1e1442018545003071a1940741c04070300c0c0902640c90035245581040d0b56904266019803841d08064458031000c010082009080f800400420a0a90341d0680300c80345042800680c054045185070f02801c14051014450a2b0364010004000b562406c40100d90342d84440502d40d5200007034491850b42e00f0480d804582d080c1151001e0070360030615080004064042d51103444180c0190010259280040c0d031440261028003c0c0c40b01c91505c0b514159644007000340580258032501844015000c2c3c400f0b10003841c5e000e00c810385d10034682589054440080740004441c5024005d20445041e940c5038031501c0d0a580800c29244503d1181d0021603036400c181c8181e5982d01c20601030740d81000258001407002031072020a2404696050301c84000644400b94256400d20448a407190401c01d00c82005c00c9550341074000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 207417850 1250 207416600 207416603
    0x60d020c0d0e0105070b2206060f03020306060d0804180b0a1d1e010512030f030709030b0f010f0e06130507020619110306010e03030d09030905100f020a0b060406180207 74
    0x1020b85402110b40151810b00a420010704034102d200001a001c0701c4520648490040030072100c1c181082a50f65002180c000c4c0d0001c0c240407451040520071810308000150708194221090745c4aa022503462010901c2540168840171610112100902040c1e41011400010081564090039141d000801075101190100c03050702c0d0041c2c0204030043d010558102c4101020854014143c0c04c1c602402003098515414040512042020700059031002011794001c8403155101e4840341e01e9820041407212028140c000d0610104004002945800c01ca110817136650702ca00d03522590798000052026a403003035850400a041c5404c010119034003103800345c410004588601d551b149181140012a003500065401120b000c2002c0b42d0b082d8051004040c4484c401021030789403040390413501050b180621411000310b40700c40d03014011031404041c000d05041d150302c1d204217400003003c0025900c1d110f001c005080764210701e01160301d44c0c07074903041400030306a0316a0444c80c904089501e94001d40c01001e0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 207419100 1250 207417850 207417857
    0x4201c0501060c150e0304050306010906090e030a09150522170c090c031305100203010603110705030703030504050c03150a0606021501060f021e01020a09080601061706060d020c0d 79
    0x200307089003c0d68959519070340125007010304c590042000c0008010181c072888043c4018000041c00340d908121183c0070340382032240419058500b107074540c266501c5540c0d00007690024072808405c0c80d440710900040302d20501d05061440c1e9808001d03103943c803031000040d01407040314440b801904ca01902400443e402c288004c04080840d40840d510f400301260141d50151003403001c84e0302040f032074002d1904071082c04400d50201c4400da907041d1800b01104010324146402100421415800d4460341d294815038408007403030904907503505600c0744181c280080905540c0c1c1c001c1024403c0400901000382000740072a442c0501d4008402e50001003110520034290403c01c01040140c0302080c1d2044000f280220310100b642009416901d090301d00055108611030001c4000c002e011100070118102c0c5044c1c00140e5a03017035a000100001c0ea1a08034411036440741004002c0581e20010b602c0c00002d81d04104c00302500c0ea107000803161710a12000d420040d00208509080e03000108a400900d80c0c0341e02c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 207420350 1250 207419100 207419111
    0xd030f081b07020607151b0905010503011a07060902030f072607211b03060c03060803030c0a05130e01181802060a21151e0504201c 58
    0x1480704040310019110500109424884100103081c86006001c0c92403007400c0c0b0251860040e45841d04560f030280f00c842c44904400d00019540d9000403030540904020b01c2c3c641d18542c1441c100b03008221200503a2b02461500060322000d22810b07500c100320030b80e4002d00703075402c61080c220203d03030316000c9000318a40c030740304816201d5400c1e81030280c0c5400102c0c81e10240c45840e1900c02601d2403581004103000149142c12540302c000b07040c40610380009200c901000c003016046003403039402c130340d00c0c3d6107840145403801e4000d00400303200106890340311680b081d86580e5600c603400c0c101d60902070000040320360f40caa5034000c204400c410700c125050b1207503e24150806003000f500032050390500c485003c20380101c0441d43d00503081450003000740c0110388c2012015240b01150380d010004464901c944540d035107900c0c06c0842002941c40900038444500f200c442000045800d04200c00d143c4100d61003550307215404035076004450100d00354820343c606039a403030b10040245c1d1102d0200180d2035005a0b407608 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 207421600 1250 207420350 207420361
    0x140d23070b1207031d0a0302031c0507020a14160e1803070f08030c071e030206010501030c0509040c0314010308090102060604090305070f060b06070f02150405030d0311090d030f08 79
    0x81c82500c111507040d0114158540321598180e00a02803807804c00805e04e444041c1107040303501046850a02480b96005640c1d5201c8100240356014050392101e818504000c2880b000a6001441d240081c0c3c00010062401420000d503074941001108110160386103400c001030665105580503105d46040103151200c84080c4807050b80303912031004003d0106039000c0b25040801c080001a61344181c4078042107162030503a0701d41044011040360900c20354160f10000e0f000301030b810312000e801400e0030f00307080c01080c5900c200640103004405545018a2f074a0520031521842508074820608900c81951520358403410402c02c0da07407045003203074058420840411aa410b00d803041c0c44059415503074040c24455190356115204a9503c015181c881d00c9001d055003d030703642d0b4020320440e4880ea04240c2d00440a2060000c03581b01408078403803490007404100080d03100400c10055a688501d0000b03106206040360a816000781800c8680200d4240a030404164101d421071492071010b860b0207003150f032503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 207422850 1250 207421600 207421619
    0x7060b01020c132a1d030106090e030d0b0301020f0a1409120f1501060c0f020307180609051b220806040305030906060d020a0501050c030405151902060f01140d2307 72
    0x13400140300117004246004124030441c403601100110080c004281280c0c1c0d41106019900d0b44c2c14160400d40001030070792244151441282840c50741038000b5402c003c243d864070b01041c020983d0302d509002e2000b14404a02880d8421902550030044c807106a400020540036540c0d4050740c100c01c030724422442c1c4107148801c03001e010b504850b0240e075042501c602d903641340c800105030034800b2a0180b0030200c0208810321542405503140c3d1080000240749031804c43d543c800d130341024001426003e80348658418040d081700031510040d001128444906a00384844907031035029500041d4140030f1242400b041540c400e00860046c0303030480484d05543c40741c130b0401414000c02d007030003540a041c002c07041046500a0019202c18807054058074209aa0f03580410218a02000200c06503000040c1c080388032901b40343c440c0000c0c2114801090300d4580034414041440042c0209202c03e243c52074074450a40e03600b0404014650b01568100d112a11503045500902c5101481a0280a13400d00030070001c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 207424100 1250 207422850 207422921
    0x1704150804050a15090c0b0913020f1615050403080f1e010302130e010203180d02060411040504060603050115060f050a020a0b0a06051f03050f040807060b01020c13 72
    0x2c100020b881002d1903075840304100c1c201342009910841c1ca440500c000704a44401d0701008003e0060450781c2c40b9100d00c00c008100c8400c0010050031403040c040840c0105004040d5480c030701d501f0320701d045814102d00b000000c0882510980d402c003070801c3c0c200010160b0144085004440d8240d0b10107440d242c203440329aa82d0854800740320043c1d0810010409440d00744140303e10300d80c1817040000c07110703500d03078983c0d0990344110b0b01c12890012416030301112000800c01a051444144007605082c10326542c1d1510303159a04200520075900d8001203828000540d218400a6a001000300040030720130141c08409980c61148202140000305800300050141044900d901015070207441c50013090b54400c002e0850103003101c2030180ea82c03a0080741c280c8a985403413490030070042000e07440034a030303e80003015282d00500300d20742c50789900d003440002005202592219540b1500218842c582c03880100d1900f580344006560040e08100010b0f0411220b502c02c0c00307481d1072265034030f07070283c5851243e50403445e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 207425350 1250 207424100 207424103
    0x1815070b040303050a020c0d0c0512040b0d0c0207050a120b0603061e040519030503040521040b1c060b1803030901020706140d0501030605070f09180c05071704150804 73
    0x340c0d100020700064403990015601c10a1303800010304000e0200301c01840d10540500c200042500c0301da101c0c0c244001080418544800380c81c00914003410541d00030b0702401500c8668000540754184480118000c0c03198801501b4090100950135a8581064108400c2e44070705803550440c00303010440038200441e800340700e0f400d4110f140c2e05088004020412412000300255420302a40d01102c08400284d1202d80741c1900940e101501ca01b0700381445810b020f01c0c0680201c110340c8805100720189035032029901202e0982a080752a400c3c150091540355440101e40300d0301e20b2424101041c000d800300080c0c108050352120310160080014141581c0780b04005400e030169020070750400910703200e03c00303603031440d000c440c6401d0600185107419420b030f03202178000300c3d5403a1721401000310342a80004d03600e11101503880c101f07a034036240000c1c1c280c003000415002d200c0203840d0264401014001c800b11201c01e80c0c00540c41d0005001c0b00e0150f07016030014007030102c0180804a071700008510440d011402075 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 207426600 1250 207425350 207425363
    0x130501030b0409030518060c0102030702011b030c09030609030e040e03041a040302150307120e010f1407091e0f171509030a03090f02100e010801060302041d06030f03181507 76
    0x401150046d01c050801d01c1641d500c00d50410024010076070a00103107001e1a45a00042411440480e07046101c0110709a50010586801c3c00030540030b500070710319400c4903008000050008480d00b011140220042152a0403d05101590041e41000401003003182e8a5a582c2041c101d600070301c811491195110107940094400c450100b1505040015a000b4100c0d0400d002c1700c110b1402080306844000d412403055954404081e04016560702074848800341f610b000404c5494034000c080c210241070f00918159924a80c2c1002d0340c00741c00e03240072020304458555403926560303501612180d5801e00c0b050a449000c4e0910040d6490318844141d400740101102850404804200071001099000c17001c4e2050b40c8020118000b5880b00d2411007502d030701c40c0e540c05640c40c40140001d001d00d00185c2c4100308140c0b041000708840000000380020000d07a0008070900f9031184c00000c1c0c5081c050f202070b00c5082c00001802022907141d1035010004450549804802800c803400005060040600c054080d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 207427850 1250 207426600 207426607
    0x10b060403110406030b07030b03010507080106120507030e032b05010303051b010f0e06070905010f300c11121201060f0c0b010b040302040e0a0203120a030e03130501030b04090305 79
    0xc0c89802d00c0d1051840050400240720396207441e021420b16003600d0800110717039166440103050a00b03001d0280d0000e12828070408039450b2500c02031042009440d47c95440b50380d40d000c584001d2003900705104d024001c0b03080f40d4480b03940c81103501048604449000340180c0d0307035903442c100c1405800b415040b80d1309920307001c0c2030022080803010748890302d8608207a20756075020300c01d0100d070b25031246009011400004180616100c0c0c4007034100e10309030300305605000480b1607000c034103544050380001590705045605041201645601c1c40b030710342480b200c4449410f04a1440c52168042c81101c40003a41d0302c219a50110300803074003101031060840c05915450104018420640a4161521030043d14035051200c103100341c488604c0c0e10b01c207170040e00c00a00001410020b40c9030600440200c4e20300c4401600c45450240c2c0069130322030203c84081e05000e40854250080b42c065807081e5800d0700458241d03a5554601580d4228103d21809000c2c00300745070001c51a102e040c00e00c900c0303100c1035254486a15 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 207429100 1250 207427850 207427853
    0x91d0f0a022202030a0f15030b160e0405130506010b040308040608090c040e061e010f061b060603050c01080f040506010603110405040216030305060607050706030b01030e1501030c08010b060403 85
    0xc0c0b5401c141c1450048600314400785062035200131846100036000018032071048886800644520348095190304d10140c1060010403055000c198101001d000c81072881c0322540d00c00e030342440080d400c59910034503010070010762070415007840c801144100c2c141c0340c00ea0380f10654102a80140c0c08050003400d0184800e020440c00f8034140d6421489200407190070300c2c1c0d82c10000c0d090b200740c011150303112707007005040c0b0521003882903d89090178103c0034111920f60503c2800e0108180310b1003070100700300200d288240540c0f44806441c5055821240078009251079042040e40c45420541c01800188800c00040160700d1092100c1c2c01207502a01510169123055000c03405001440c1c00071071041000c0000190680e124170081c42c1c880c20035500170300121794a040250031900002c0007a4010401000844c00280d40411070905860b01400e0000d440071000004900902280b41041060711440c10950150110004600e040701e104020740081035840340f40e039600345c8100906054100b80240306c10f00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 207430350 1250 207429100 207429109
    0xa0b0f0709030f06060e0601030b030c0d110913030e040507200f0d110c03030c060106030207080403060906020705060a020405010f1103130e01030309050f0607021c0c091d0f0a02 78
    0x360001414980780e0640c030784945901c420b540a02000f11803643e510101040306180c1e00f841c0c40d40c002801d080400a004150001c2925420403000582c07107010020030b604104a0f002c0030315240d03114040c00c50310b143d1401b05681210500c3c211400e5000c980c00f80e8a050f442d150070b000b000e1003000c80359150140701a00c2c0b03005083c030b00305000903103585011700340f15128000000c11091500c1040c6545812071056a20020390601000384c100134041e40003007021900c80c0c0300c00541030f411510107160040e566105420010800d00464000030005401d008022060000640140031090700bd001034816a488001d85041240304505c5064042005050a180c3c2c0034000c0d850801e0b6500030905403441d00c544010100416410f07a00100c0d5103182640c010720605520020440c0500829119074025040c0d542c00a40207002e8104000d11451400450740c440f2300e4007180d151001c03035022f00700170181511b68006902805005410703031135103101e801c8484200c510005138045040f1250001e0b015201e290703000d02 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 207431600 1250 207430350 207430381
    0xa030e2d0a090e16080705031f0e12030f1f051c02040c1707020105010f0e070215040302030307120b0a05060906221518090f0b0405190e0a0b 62
    0x6511406400c000903540503207000e445603044541000d814509130074810021506541e03003000c9803079807201c082400591070000d0a080b20f81502c0798240c905440000c650405448080b640d10414068941884036080e038850240d03004d120f0803020080c42d071343d81d01c07010031981c000a015a44154600d074000c01c000d05005200035141c1003613400385c881d401002d40100742990039600ca032100080700d04000741c410400c54642c4507008a802e10081c0400c0d49890701040e21202c0600075081347c0405c0d0782c0403920a500811010490003c04602d00d1400d15103428007a484c9c2e0006c91b0040007040140a81156400e018131600c0c080301001801078050f981010144443d542009041540003d803c101c45812411903400c510300c010030314100b00501904245500344070503080c91115091212540081c040a0790013007268040d20781072800040c4607124043c03214060500100b41680051a160602500000d81880c40d1038001c510b49050200c600701b8141c0550f542c20441d00600345148542c04101c1d002d505c40090f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 207432850 1250 207431600 207431689
    0x10210110d110301030203060f0730050a0e060c041d0a02210103020f0402090d0308090319080406060b12010b030915010b0307020c03010e0c04150e0403020a030e 71
    0x300381040d01404408080710a411034140d81c000010004008500c1c0400550794403003507181500000e810061805401242d103804a03410307802440d0520f100000b40c10201c1c03251600303245820300a9040c140c442034018005002021114010744000892043c800801c440441d074940e40c0801c50f144107602904d40d40036000c0c0504280c135070200b01c4151840c080103001c4040620340c10303100600754510b1041101c0480c1e5400c1d460700560060100c0e01c05941e071180110442c0d60142440b90300b568a014800d420340c40b503020701c60001c0d2b0250b9007400c0002d034004109032090344900000c012190703d9484100e128094003812020807a0081c0041c0702a030500c50140d900002e00c00215050480e451051420f035030826000709103070f00c2c808410442038507410045042d00d29000d6008019400c0e00d6210241c565040c440c00c1070065445003046031086041040640c000e07e011480440d032418075140094507501c2901080d000219010060000c80c40d14080c07003200c40c1210504084100703103080c0035200750b2491901 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 207434100 1250 207432850 207432881
    0x90708120f0d0f0903170f010b0a080603100609091a01150c08070b190f050103030203030610020a02120307020a0f0506070609030309020a060905100201050f0a0203061f020604030f0e010210 83
    0x2074454190014004d07a03290314440d03221515a1565502115a44400102032125040704500100315143c18a02102d4148282d40b415a40d00d50702e00300403904d0001c0140c2c241260624254001071000082d50004200c54440d401d2810200500e210b031f2010314a0a02413841000414240300d080180565012004140704104090520202d5100c4089405045070031001c13a401403905414034104c1c0c0c0c8202410b00300e012400700203950560324021740d41e000c01480c04e802180c02703104801d402030080100d0b400c900c1d401002061003448074546291240c03c5010202e00a04000e48007058490744040038a0940d1005000c076800d10480b501c030784025048429040c0c060640d16490940540c5031307007a02801801c0952140940e8601d01018041620010b41102086900d41818030032400c240e010982c3c5c214100c6407002d0380342c1c2c880c0790004040c400c3c00ca01c40d007a2100c143c044001c003070341c0202d055440380c0e020f43c0319101060403162003669094106821a401a0880e9090b24003224003a44100300b840c51500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 207435350 1250 207434100 207434111
    0x90613020f0d05060301020a0206040602030a02070503181009030b040b060d060c090305070b071104090501061212020d080f0f0a06080703080c010501060203040609030b07050d090605090708120f0d 86
    0x120090890380404080c850790360780000c1001160000340503030b43e08080154000c514000400c1c100035160200504000d0a007034000001c184040482d4050b14551600b03c800d5a0fa03503a02c10b00c07804030014003030761018058030611040c145c1d01c90050301814200c0e50083c33594000d41d6503e030f071801001e01000f41669400b4600001c407001180072407060841e003035141c0d21800c00540c203600b400c030703e003050035072150311481c20810100000440c1c21040440f244802c7c1c0b40403500c2d07501d914041c5d02410458004020b481411849101170103a6a1803254450080e902610006058001c00312052401150002c000100c00c901040d03540c00ca80d00d281e5400880725500003002600c2d46101801c000090748150f4540c03d02181cbc0c10717100d1400b8490a030041005000851516281c808060150f240030b10014280c85210070004051a0080c800c036405440c685504020240562504200030300096812421034410500042554a00040c00a00f0b0040110815003000c01069100419070300003103e0320840c1c2e4480 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 207436600 1250 207435350 207435379
    0xa050708030403020a02030c100f030203090c0607030801060305060f0105090603090708010c05070605010e1005010c061103010e18010b061606090f030305040302120a0c02400b0105030603030301050906 88
    0xc102850055220394080c001e0100c250041629081401d1110762142e2034400c0e12100300d5800c50498000e00c612410056240c0c0da80e140d54070f085c03960180803281c0003400050803608141d03020880c070f81070303510035242000b01ea05e6031803d000c2c890f900514400e0125004200c001a00e141c030340c01030340d442a500011070708199142c2e8030850954240701c1e103950100320046408010800d132401104e000d80032109019202d40b0706400346542a505901c211414441a08248014890640c01c030070582e401001c0015901d5a4421500760306520485803254112400303840b0382410003040c020340c01c8400004012904000c1c0842034203042c000660000c07903d242d910119030740000c1107400586a294003a40b00042d69103002c1c01c02900b040d2904540045180d001c01842d05d0f41ca800810030458150190ba942ca01b483e003105024842680c00641004466000c803021000d0004405058102c226042c83c02d02c410580580199030500096511a52640042c8018009800c2a54165034000401070250b07007a03041d803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 207437850 1250 207436600 207436613
    0xa020a15182913030809120a1e0503040807061e020307050604150e010e010c0305061903031d03101b020106031e08120c09030105150d110a050a0b09330a0507 69
    0xca41c01100c0358000415501b100d86017039003114024003000805021105800d54448820301c00b0342d2510001c03004201008400d0000400659002d00407101c12100c0080e00c1e400058205d00901c40055410349089100881103840071054135900f81d40000100303c00d80300c0743d403400f46030001240b440002c0e0340d9405d042a1459401d0140b1501d054100e4000a0100d1400300001d00791074006203a01d0050003001c003002270f13502d447d089201c11240c052070010a0f12070104580c04d0a03c605294440c0e251085004d0328610025582c851982e5540490403236041c101d44180c10303400e03202c0d1480b0181c55610700e01040d900c112a035081d001d103190f20800c280fa29040b5114054245010240d80188960304040703615002800c00344076880e00412401c00c001003440e0814001007200d415103100038001404140c1640d465111a03081c4000707844001d000e07580460b2500203802c00703500440c14191007541c0d0341034050b11442c10b9502c0501c3c49000d0358074001c443d48056070003099543c000b900490801a0800003840421034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 207439100 1250 207437850 207437887
    0x6140f010e19090e01020f042d0b09120106050307030809040608030307091503090f06090611030a0f060f050a060c0507031b090e0d020316050a020a151829 68
    0x101c015051100ca0414200000312075113a10141c945a1040080c1480b015480f001d40c0c040b181c80400c0f01c501e030101c03003403200800f1680325068201c1801244d000b00719a020710014007a0683c06440744070f201b11500703103103d09031501c40c801d50b900368001d0403003480411a0751006040d071000c0500080790306591451103504d5980121004800907010300c005224008540000c080000c20501d000e000144464480c50301c40400c0540003800b04da82ca5060000b00081500002819620185002d0700c80c13401000200150048503845500e85c1e01d440004150a8002c01c403400a50350080e01c0c040c00a41411011b0714191140035060303c06100d654070010019040308200520030405030501824503292030602c505a0f6a11049072146400a82d0b54440c465800400e45041c01004080c620328441641406402c15020110103034011003003007000b140c801c002c506044054802c030f50f58027800c2c04002c0c141d00106072050085220701c40240501d440c480c44100c10312480c120740c0811451405150010b088540314 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 207440350 1250 207439100 207439129
    0xe0a06121e0615030209010212090409020d0302060a06080604051507020f03040b07020103060b1608030a1103101a1c02030601051b070501030501091a09040302161d0a06140f010e 78
    0x40c0c581c42c0601082482e800c0624603003c45003015401c01219100103500e4094000d0308424440000c201d2401d00c1e551a00a40d158540140c0a0000300d183e90030000d442d04022100e048105080600002c1c9800b000200daa10668000e0050700100f50603d1080c0c00e0600083c0c02c0608500ca81c003d03486504c0c40510003000141489034406640c0c0140d4400076090b00e001c0d03031040d0b403594402d00000380080b1400c102c030711001d03500241d420342d280da1b6800765070028481206c0f258000078000c402c12008401204180003030364503000300a14100280084036010340b00f42c00e04040300d01500c0310144480b10050300590340150f814100242001d982141c01c0c26502d1410170351102a5000a074100900d50305446503a016107812030b42030008a01c4c0700c00c40c502c078403030711960039010340032074170000301454401d204401401c840210b210a100307a95402c40700352108500951805980c1800204030081820f10890044584540003841c000481c9010400c8403040b401815040c84003111890354196264400b120586 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 207441600 1250 207440350 207440411
    0x30206131502030c07090b061e0c0a0303020403060b030307030f0807090b032403060c07020f040605090c07060507030c0e041e020301170c030703111504030b040b010302100e0a0612 79
    0x9113120220240b4107025540304450481c07a01d042d000403621090215580d205001c0c038802e00b54050143d445d071452054140583c141c0c000d095a400406525130018400c89004071018801c2086030000c042c7c90b84180500100443d01c00c01e00204124003c41d182503200e80c2d64240038022641e1540c510180c2d07402200e00340c0e6401c8042e103210310030401c201d810b1501a40168001d12031031510702d0f8036090600c100031001c1c1c03007003840000074020355484d038000a01504002e07010f19034504006409405c550015032040751040c0c2054001a80703240701c3c0c8659130003011241d4407086004540e800380001441d180300300c00040d98030244020b5002c005d50005500801c110750b00d0845524071440041d0400340101c05643c446e0700011406c1001c00e603017100e03501a00c2021203560100c1948401c450500e481580e00c001c0032a0154010402440190802c26048900070740f25010b40410030041140c40521501e022940001200c101340085403041c10700b0307160301e141c0c244001007842c0d06900d01a810058040711290380c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 207442850 1250 207441600 207441607
    0x20f3106050706200f0c0c031617010b010e090a0209100203090109081f020c0a060e030927070f0203090d0605040c0608040b0115051903060501140406020703020613150203 75
    0x41001c2482412052880b0394082c4440501d440080c80d110301c40c40c06210510304010442640902c6c0500581441039002800c0b60802c6020800070650751005200c1c030441c00fa00d08000d03200d00314060003100100c1c20140d40d01041c00a02004000c24100040c0c5041c003a240d0034412862140c0312211181d010480c00e400440e00d81c070102c00010000c0d40190401c441580040a0050408030001c00380c610408070100007680742c840c00222070f4503005281c88e02805090a020031801407580200082c68404004e8950090b1400c000c0d100d0007190b0403118020141c060b0f0800011080703407241d551050112291b1050740d2a004488000a000c061030280070748105640302c041c403040200c1c189001d0001c240354201035086182945868950200501c59040c0214514108030860352180702126160710000400340f04640300c1901c000e0081809000d0b0740c2c0807541112040140c0310700e00c800d440454800381c0c0100b55050940d400c0c003180390030a00c44822046981c00b000306920141d180030890903446a8010b40d00c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 207444100 1250 207442850 207442853
    0x1905120f0a05070e030a12020f07030609030e060903030706050403031e0509060105010c1a1b0403150b0406050a0302060711040908030915040201171902040b070c09020f31060507 78
    0x11900c0151019040c0500104e40385582d443c0413403114542508441220b03403405805400340d0901c4903482c403004590203041d001000700909980910305050180d510040002d420300c01b4007602c0d114036041e1b00d606034400c0c44024001040380c1c00c030540c46446481c000c1080100441341c0e10000c001c0c03455580c4c0b1161a40c041000040d010004540100001d00e00031800c030f64161a64403c1a8007104c00142c0903840c000061810640040c41d048030414650741c5568480d030300d09180780c000460b002d0302d86007603007480406482440c09000d20710a45400030100340c941c915683c00c004180d030080c00100c41c0000451040c00c0c00b41d0ba980320f5454910300440b861a5a8a80201c0540c148010070141d01c0303901081906100250b40d02c00c4c40401052040c44c40540c02d500c80b035100000c00d800040d80141d0007800050f01180c4000300350040e201722840f408090041c651244880000e90040101010300003209100300f00d00b2410034590030a003070b02400d404116980b0040d1a90b0101805034114201080c400140d000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 207445350 1250 207444100 207444121
    0x50f070b1c020310050907020a02150705060907031713051207050112090521090409050706020c09010b03070509150d0515091018020c01060f1d010b1905120f 69
    0x80440c008000c6155103800d100c0403804c202103000c0d2500a024400c00179600d18020051740c0035003a0020a00700030354041e50300180d000e9002d04800c9a8501480000c01c070318010001c0c200060300d9006100160321903015088981d035400c00c1e000128848141240010346e501d41c0104070740d42d05114805000c1007400c03d000908901103103aa0f5400c3c0502e804410404101d005c0340304070314801080d086096151010407520315500902440360303445072030f1130468010002c0000d480b804890441e0282d4a5a440c03510800122017404d10480001400800c0020410741c4290001c00020b8002010b00c804840c4282c1c108181d0f4000006141302d0f150b81c0e600b0701400c1060895035000d035610468591609150180d03040b00302500c180300e0700c0072052228404417040c1c90b643d010303590045c494400030003605958480c0c0140b01c5443c1d104050f61400c41d030380d241a2440c0c0746030616051380c01181204c0e1400d035855191005585d00059800c003040021b1000000032030301d0208040c011032111180c61240e003020782c040e5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 207446600 1250 207445350 207445387
    0x402360a0e01060b0703050f0a2001090b180a020411130b03011e051c0c050d1128031103010207060c020309030d020f070b031b04061101060f03110409050f070b 70
    0x500b100307021702010002076801011980e00409069001d6120050b0100607904090059038040c3e44100c0d25021010070101540300ca04828081c02d4400c40b140ca03074000714680f0031200d501c0703420f22760040031300b410250401c2e41082302d0815248241900e01415103000c132414030015000365040f444000010003207149540d0311a0042000151102c4d0901e142500003880004601c91841001e51110600d070b0520050411101c01400e000d8102da01343e00c0a80740c591200104242c045100e0701d00220f5007803c17016110b9100903c0c2c0f98903240c0c140000d0840e141d5214110501e909580c0c0341d9020020080054420700844002c60003d400858640410404044c01c0c46600b042d44011540a072031303036212019002a81d0800c50b15080c4846980e500c2d141c141620350b81c00141d0f0f81c03404200008001640e694008455400c400c0041c008100141e1035501040c82441c0368800a8030344440e101003500350380b406920101d400d51141086800d4000717119842405c00c08035a118060218011038103801d0b0b00344d9080c64 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 207447850 1250 207446600 207446609
    0x100303030c02060f1603090501180506130f0b090109060204060c030206060306090714011b03020c1305060d1203090204060b2a0d030c020f0304030803010314060402360a0e0106 77
    0x78203c1071400000c42e0407030b00e00060958541043d50229600d0080c020741c0300f10401da8006000f40945401d030030458111000710941100c46200d42c1001800d400c18010350301c1503442d40704084454140c415180c0342000800504a8001e9545e0703610720500123010743c40140000d10480c0c0342e5032540082410045e0038520007d0004e4003d804c04070411008442c041100020b4803c402d29407000c0d0902000100e03000f640d8400146c481c0121303809484245900000e00e01c5421100300c0e00f103c0405d50601921042c3da800307a40f242e401285440100002446500036240035001c14540042c501e8940e030002020748065901c168070b504000561700c12104403c1074460f00c8090041d2401c0d801c0b2281900487d9501c10300e014030740c1055503070411202c07824805c1c402c520900c45d00303d044a0316a0388070304040b11603620a120491342d40c3c0c190203000300c281d10007042086c42185c00814518103d000038801e10b24018a09412551940349000609501284010200c0c01090078107400111880c0d50384c205400c49003036030403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 207449100 1250 207447850 207447853
    0x6050609060d030f050405120309030d0c0f03080a091e060c09060206060d03090b0f0d0612050d11030d060303020c04150312050706060f0b0a0f230f0d05100303030c02 73
    0x2002850385480e00440011503051034610b5800c50101c00c00c450354001e43d04810303804508c035030142d140c4100000143c05040300440940708a210300100c2560589600308004094401c81518040031a01607a00340da808ac05003a00031030300700390039600d05110000c4184d00400800301d16911230240003152084c1d41c401c1426003800d40e1028108440030703541301401810349200c0e140e001d6004040520805c00b0030700030007443c000703142c4542d841428800c15030000000002003a150001c0052005006244040342c160003102403e4201e030192811588605066021407980c80300300702d00100c43e40d281c85164000d5009a01800010949a080005440800781d81d030850b41c4c40c400003800818076080016858034240e00700181c2d00c2d01c2c1c0d46010710180c203440e800b003215011040000a00c186a0900401c03501d072003503441d400c05940f00711040c0c2d0b500032940d11102c6055501c04404100054400c0207001c041c440e512001d080280c1e2000f40420303240c04840600341d0b0000c3d500c040003096014000e4100c100034600 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 207450350 1250 207449100 207449119
    0x2040b07032c0d020f04020d02030f070809210d060503071e0806010308030f19050c0a020d140315030a080403030c0c0909020d0209070c0b04230105010f0b0c1204030c03060506 77
    0x1001548000c3d0140b0064400c0f0399060641e8503503602c56044407281e2010344802c0d0b4403450645460501c0c020200d80d440003040d56a400214180d60200383c0f0340c00015045500c078010003904072840b40c546c004001100c03460742e071410080340700e42d01008000000c1c004054850744074100074140180307464640d805105d00e640b11200500010366040256942300e1040d0b40c5600d07880d980c14180c030490a0800645038500340c544420300910551220007410041e403142c00b2150401d13000300c011104502d400d00140701e245824404640504a020000041210f005003154541340c0d0546415034181d109600842c04121403420440800000791405030003450324250400511032141c001c104d0f0075a1b006c00c002e00c1154080d000031152402185902072094010102604c60310b00ba1428040c1c108241c9402c043c031110002c402e010f0140305028207816281c1940250503600d103407240800440e000054040c000d07024a108064001c4040c9000d0002940a8440d843e021491810000b040b01c0024110134014035a20 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 207451600 1250 207450350 207450437
    0x6090b0609090103060b13061220010e0f030f1c11062404060e0727050307030638040513081602010e100903120206100905060402040b0703 61
    0xb8503030385046980056002c030303201c403042d0300080da0007145a82c2c2c4001c6030303d8810003061030482c806043c240c03103100780d0940085e1419503181c8444c060380c0e80290750000713411840090048c20400a01407100d000642120740c100e08260940e400d20344182c070601610030503804002412640f01c01481300660042c006000036040c2000c06403501040d0000c901c500e0807030904690040d8030785a200310700034141101c8510f03103820718040003002c0f804d034030502000d00703114080d1310505124000c61400840790028020586103140da41c590025014446d041140d406406100520740b0651030460106880f01450994681d2031060800080740c074081c150300c4451120001000000d0080c60481d03121042ea8101c0c640b1242c1907100403288401c6c0d6590054116451701c80c46200365421014000640c0e2045120480c1110b141d0340407603030f80300300b1140781854803403d0104121104d0103038011500103074050005031915487d05a0301c000796020340b104034001011242d94180c48013058851002e400d0200e103d204045505 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 207452850 1250 207451600 207451609
    0x20d1e0504150903050d05040605040215030c0901080405100903170106020102040f060e0a030203100b040509010c020a0b07030e07260705030c011404050d29071b032106090b0609 78
    0x441c2c000120142c3d1502c42505240c0101d06903500403450300c0b4140000e1030580360030000b524060354203c2c09042e840c20704405602140d01500d205401580015007490418401102e400320090019502401414038001c1602135901407845858003944520f10400110315842c92038140507409503007164410710050145c0c1680780c00c910120340c10f80c603240214994820000b41c81c00010751000398148101b03130011105100d141c0040d030b40180c1c203d030104503d030f03200c0001e5420b0b01c452401da800141c00c499200400202490001c5070801c150303242c00610010000c41d00d614110981d000b22801c00c0c0705000512800d2a10081c54041e03040d5180a805c2d05450302d0046950b9540000606052000f4000c2c0022418056070a417001401e00a09014100c01c05007008084000030100240c04054a80e00b4100000daa4000710ba010b4a1265114008418428411418843e42c40c100300c0800002c240d541c135115030072005008085d61040c0000840c50320b814221011501d190180600810050100c80d41607a50b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 207454100 1250 207452850 207452873
    0x90914061302010f050a02033c041208031e07021f180204020f0c071e1e0905061206070e0f10050d02031308070302030304020108010b04080303040311030d020d1e0504 73
    0x8817410b12549a9034410700a03402e5019004800c44110f03021004c1c01c021034106e0301c07006510250000030042d141c0c00d2441c640013620075405841c0d150001d40c250100000c042c400256446002c0801340000112800c241d0f4a2030f0800b5945000140d001c0b030490700007204040c410000005250108104091403421a04c040b29030142d0043e01c00c0342d010071100c1c1800410b4084604c24001001501c3e4504e844100729940116513a0045c401140c0429001c0741070760020164012120749440503021461905000e40c016150041c041600f080101b0810a80c1e00f20410130300d402100e49850b0301d141c0032000c209121000320071480b95403052220150a4041d0368111080340c9210b1110100540e6079901c00800c01000311089100812084002402c0d01c141540440514022403003607903a40c1160b41d03116a0403049000b54012820a0b0300200042400240075032444400c0d4150138003034a040180c00ba0100c42280c04c0300301e4a08000d500c40c40c10b509081d030310160205007061414bc0030081801c103030300c60310080710 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 207455350 1250 207454100 207454127
    0xe070504061b1e02030f0109080310141e0a1517060a350f0f01050108011a040b1801080d03200301060c080c0d0906030e0a05060610030609091406130201 67
    0x218001242c007503440a00c9006c1041c14050001c3c00050440e01e4405816402110a0310904035210800b18a00114a94802caa0035000340001220444150340c0344115061200f601e03441003c9010002e454824504080803044441d103c030400c0825151a48100c0903005203000c1c0304075103200040c4142e01c50110000c1c440b52070000003207e02a0a0040c040405e110051010210305ca108400c28103030800044e4081461200c3c0000d1159982e505141401d03900c0001c071032181820001c100b84400d0030658000000b940004280780c0d240f4a070719a00c005154800e070004000c0340c020881c03840d00250140516031407a0328024415060660400806e0042e00043c0900c2d8100441444500b082c0301141003a6400103e4140586180c0303207800002800b1800c4c0b91290030302203414000d0402003910007003440c40816802c200035100983d100d4042207030b840600351015080c141d4480c80403401c0c4000740b14000e40710384640401c0640b041840345070fa00e046401011b8100340c031840d1001c1d80040c0d92040b8805003c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 207456600 1250 207455350 207455393
    0xf0903080714041d06030f0105060607080a121a04150b07020d081c1b0e1f0221030403090b0c07030f030c0209070c170406020303010512070e070504061b 67
    0x34034845100107140d10869011410b8000300c0e0382204c032941c111280302402000114202c401e08041c440c517240c01c1c0d034800c40d0465441a070034806500481d011800800c840d80e0a8070313184c440e40b100310002608441101c00c804401c460707104210b0700701c0d0a080c0b050000d00806c0c08403d520152800c03084500901c40e01c003000380241c01e030045103400c0004030003d440c1041c0c1183c403003501071103480d90054010b04131041060f54413000c03101501c4031a401101034100c00840070340303030980f140e000910741e20841100c0c0040c1d004602c112600d80d130407440e050407420720b481150403000380c2c0c074206800c0041c6141d81c2da400c40120326204105404500750005289402c41c0d0f07010804903043c088a040564902a40110282d0490000780401101540c014020142c2078420303848018130300b60030680724009004901412003d64001c10041c40940f424000340d2190f14005011aa10141ca074282003000c00d03c20313500c8001041011404ec09040e4000b002840094050341c0e6880300401562244800e420b000740305941c11b03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 207457850 1250 207456600 207456617
    0x40b07031802190e070c0c05040c02030a200f01020c060603030316030c0c0b0c0a03110f09010c0804080f030409050901150303030213080f0d080f0105030d1107031a07030f09030807 79
    0x10481965501c000804010503600303045c0c9000c1030098200100380c1412540442c14010203d03c038601842030302e0002c0d82650007103003000c2d1484020703942c96044001c507440385d210850030401040000c001c50355024210b5000562038004a552051070050050a024400d410900411202041840070a11a22058580451181c80d0780d903041d10f200b240c07041c0c080c1154041008000030941000f00609001c50650340401528200484100960158002d46454420704019080c00b9610a40595001c00e0142555503d000e9540b0383c2c480c030b400014000c0b548030360000300d02040b402c10a84107282e48255200c1c003d110164688400c4c8e100c024003808000d083c141e000c6410302291883c01035490140c1500812691450941c0800550b00c0c1e00200715203000a04100005d0340480c514926076048480103402860004074048003030351180c1c0c4182007000c1d00d10a80d18004081141c031040e0146c5d00518403501446820700711401030507a41e416a000344020300700b2483c0e000196000019503804070262608040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 207459100 1250 207457850 207457879
    0xc010f0c060b0405150f090106080c0702010e060d0504170f0706021c2405010509240c010f20070c051207030506150a080f0709020d061706040b07031802 67
    0x14421405041e0700289050b08001700e811481d4071034941d08400b01d421a00710340350201080b10b4050240502030004010801007250544008054000caa1050400c045c9031250071020810580104105907492a102c3e0213000500c0031803200c00000402c03146400b0301c3c0c608103180c43d03000b07132060140044c000c070b90011300d1030107855441c2045010314014440c01d010404049800c1c401079440740560365845084042c0000d110b43c05202220a0320402600c000c95201c08800c0b1401660406020f05070509010030201540c4042840b68481d05501d603000081c40e9404194151203144e07403235610948071141041245c02160024645404030307101200d6101110030110102400e09060307500060041c82094140b0900d84a640e0115210a0b4240e80a003452507846242c103658000010000b80a600026000d01c9818056001802c05101e941804500305aaa60080d44107060490070760303c464002c207040c0420132003241003c40e005003151600307025081c100c10014203080900b010082c8581040814440c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 207460350 1250 207459100 207459113
    0x6050f030a060b0a090e1302030703060f09080309061015020a0f020307050307080c1f050412061407120c0302030108070618090204170118030e0402090f060c011d0c010f0c 75
    0x200900540d0410f00e446005a40300a094864240681e08945183d0000074050080c0302540c07207816a00200100402450341d00ca0100514008400d003000780d4442c3c03840c2000c24000e0f0000c5000c0c0f00920011f140324541125131101da40c0c210b030050b0180c00c5510584000417980000c400b135611340c010700c03509000b00d56403000a01e085001d81c0116010f000b098000506904041100701e6a1117095861514081c048001d111051404070012000700750280000c3c0721088040a18140c00c0380704400020340e40503d00140042d941c0c080310182d0000d00841e02c5121032844501603103407480c0040c2401d5045504001e00c2c01d45403881e81c0542010001d5210740407052158141c910001003a4074001103540f66194091152501a44a030381c80c180c1d82046403140e65a000400341c3c0301500e0300b660719001d0902e00c510802004c0d502410300c0b80e83c41035403e51841d40d0396444000800c00003100c1000041e42002e1340f0035200314114003446140954103c4086c0c14003a07600407030144031104040c5054824140d0920b80349 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 207461600 1250 207460350 207460361
    0xb0c0703050d0309020901050d05060118020d020d0c322109060f0711071505070c0906141507020f241b16031b0306050a140603060106050f030a 63
    0x292032885182c5070078109581503030001800794025100076034246c1e01c030020301a040280450042c41940702c0d400400052401a40e884150145a0f0025140c021200d4100f002e0340c22440280499990300c101807aa0a5040508144003140181c0d143d0100e07881c564080c09801409060480b5107400050401a04c1e201107220000703000c0c04045104031030038130000260b5260307011501e000c4226220300101d4003103400b0300c0c21346641c064624004c005140c1015002c803540400e8820081c00d0210078030101001800c410038900142203d0070b0700158242c988010165a0384034151300c0760240008614003a01c000c2160101c803880758050340d442d500d9500701c40124860003800c000b4051801d404404036110030807070600420095840c04c80003000c02d03031207052098940321003801b800c1281c10080c0c410800903500c62401c0071004c145006210940e50b590f101c4074103540301107072001d00050f47ea060701486800d04803034150300507134258001d061a6041c6034003e8802d2103840f1801c144070360080000742c1404001d8010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 207462850 1250 207461600 207461603
    0x41a15060f0703020f1605150d02030405060712020c0a0215040506070803010501080a060509060121060b0409060b0903150604091211210a030504060608011b02060604060f0b0c0703 79
    0x420350707207425400c451070454005400440042c060700c02c600300300020004420107a104600c0501680c2441c0004024081402c8a8039000c001c1c0144820702c0c80c0b600724030241d4400c2c3e014102400a80c034040c1c400802802d000300400811782c0c4140715200070121b00040c0c541c1d0141e0305540d92500c0ca00480c1c0000741d40e0003180e1005510010015906c4104045a070283d4102c07602a2500d84441c0c40714002c2005942031809500e800c60841c9000030700d20361003070301408048611a40038005010078071149500b41c4000741c0008812032030020702001102620320400005019a007091030030010b0031400a620b500c02200f011411942c108045038480c0e43e030b41d104000e016440b04d4084120f0004c460f01a0120000400300703035241c09112900d00103d5202007000c2040c1c901d4400c0c01e441e01c80940401c1e8002e0001a00075900c0540d59800411110024868020825030501e030368208103140d684000e2625100a060324011030401404000300d40451101c28207455051392520745a4030100305462409105034070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 207464100 1250 207462850 207462859
    0x50612070602030c0607080c07030c0f02060d0e120a140a030e060a0902010e0406030210030207060e0609061b0c0307020d060e0d11120306210f0d050d05060405041a15 73
    0x4001540d540000003088041d1402043c5c1d8016030390308106480c1040100c99090150b54100144c200086c490508041c440b4425221113908100035004a01a038001c042c5146a681d0b0b143c202c020514800c000d0005140342c0074030800c0c900a15000d0061810038200c00e1945607d00100300d1500c00c030700941000001241401c215a1145004c00c1c0207406030a82c4241a03002c00d2440d02056401d09081c0580801d80ea00034100102180d01d40030214020f500091041d00c80a54400c80b4081528081c00f00c00d015003a010010003290900b0411090911400b0244440c1c1900800018400f054042306603000035030101c8800343c2044003402c28030080c000700c01100b03859004041c101d03070120303400c45141001c21105034101d03054140780c04205401480300b03480c0c496225520401c00355502c00309140c9660380003140c40545407000d00c44446145850105d1007400c5c0030882c0458002d80842c19442800d510a00884081c0424200f43e1501d0b1107d0815604c140222540200017078008043e100764200d16040c00391 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 207465350 1250 207464100 207464113
    0x80703030615030c0f14160b0106020d0216060503040305250516051309020f180702060f01120f0302010b060c070302090a09150209010905061b01150b0d050612 70
    0x1400034000c0c0030300d0244080349048030b4030042c00a4403d200307050070300d00c4135140c51052080c40d0009a400007010741030310191b41c20401c80f54100250389404194024402d1012101950600034040d041c03100030035000c0c04660143c50031046160341807024204603400b07420240d036030351a01e007800c66841c0b080356106c603140a00404480c5d0046088182c81600358010000d035000c0b6140d40d01c0502807890341c3e1054980c03044003414904c5400300301c1d5225188407440103140049401c0043e0114009a0b1841d929441070490b203410044a982c046c0481a03110120301d09140003917041044280b601811b141c0054000c9086913413000815000b58040702a040340285226194004945100c3c1c1d5140c8a000c00c0340104403c0d03003c201c080384c2034003441d046540e0292101d1900028103041e9002900141070041c1080701c0001e0004075501c50303000501c64402c107801c015032500c043c040101c1c00d42e00801c0c09200352108802040000c80110301c10307552088401140403482e6210f440000d01c07030490380702c4884074901601 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 207466600 1250 207465350 207465353
    0x180f020403120906020d02150c0409060807061b120c030c05070b07020102070b0c062d010b09090f01180b01030b0a090204030c060905010e010806040f05090c030c040506030d08070c0807 81
    0x607510b85014400d81d500c6002058492804a843d945c0c2100b8500140e030003002e030501d140d1416542c0c1503105003c0390a41d070526586441d0801619103540c032440244c0c2249905000c0c160307001c0000541540001905c650b50300c02aa03518038480450101081040300032801481014425071103590710710341220860703020300d0b201d008905040e03201d0b04003280540b01e00751001800a1513001503c40001c80c5e10f02401c2c8076a10307000700f49212224003024a2107140010013400000e428210344038080d00c0c0b404503281c0c80302c0c005410700070b1105010380500202c910640041280700c189000b0b450342c0300c07000c0101003400c0d04518016000742440d40505036021002410200350000c0c69030282040703c1c090030301041d4543d90342a0640b15440b15005560008a400b80858050350180240703030740080d4050000580d90a605600c40d080354816684104281c0104603401d8040c0b5080003da0303a0301008403403c11240c00c0000c002543c0f880240300180c280040200003450700c80c011001e0505058200b400f260342c1d003226 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 207467850 1250 207466600 207466613
    0x702040b0d050106051206090604030c020d05060f16030e21130b0a03200706020307120903020f0609010b0f0405090a050a03030e0106060c1a181609050c0c07180f020403 74
    0x164005c0c14001d0b0100d003480c8203891030000720301c1c2c09015001c0141510751900e460807140f007281c1c080d007a0382007540c118440000030410007440d03228004016042d5030382d080c0700d818580800c0c211082c1000701410324195500140e0046030000b0040c14000da80700316103243c05412900c502807049011500c607a40b44000800039801d4006000034441c1c0c0d40c04100b010030b05030050407485903002401403048824000440050341d039500454000589041002c61050000c4001c01030300c00030b41c0d0490050300f10102000c05000c0c01c11103c0c0c3c105010100a210802c415000319075010261307038aa07445140c41e2004522000d10501004400710b0308441039800d100c1040c10050702511620400000946c0380420005405220b40c10854a5581c0102c0000a590300380c24058040031000d00100c010140b016000c2034400c404100c42d19800c43c0c80c0000800092501d0420fa0895900402140004800704065582c4840c04202101aa1401000e0407078040c200ea00d403500804040e482e10715030910000b00442840f10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 207469100 1250 207467850 207467861
    0xb030a050606042304080d02091521060607200d03080103150207030e060703090b03180705030111041e0e0a0e0d0f08010909080903061e0c07030e01050702040b0d0501 73
    0x207440070f00291440c02c8580049890302104480000603130004180010210030052220024000e0b015081071820000aa16201d9080c505040c074100024102022281c4010f29024999854016000340c075140c00410080e10544100032b06021041c441d00c000d051040e0401d04401c0400340c9400e00303001c0e0381c3c60302401b0700d6400c0c0400d03540c0c0010061074524208a5000311807125501d81d850000b800018020b1140c030b03400c44502101445101704001c01e820f5214809184500b003061002440e40600440351030034164160031039802a41451310081c0d6540580301103500311950040e040340c14083c0d001d80004124810f4104080f032841c8030040c05042c0300c01c3e0300b14450751960403094481a140c442c0056440720031900c40a03010880c07580040001c0c1400754002201c641c01551203610304403c0d8400241030503070459100b100c0103070000c5228007405501903050b0703010075020441884c103049600c001d0841012070800c11b040101c0010203170110344a54000d00e58080015007902c1e1000800d19215000c0d02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 207470350 1250 207469100 207469111
    0xe0a020a170105010512222102160b0304030504180b01090501020d0e09070309140a0c060c05030708130503100603020f01030207020d17092701090912030c030b030a0506 74
    0x44800c00d41d07007000626401d41e94125030f0140c58441ca05101c0c00b180e0030000300300a01d04080410340c9125124485035013107580a0031840f4004a0b807049062540301c081c0f41d40c0f9401c10200310740c083c0300d41c1c0d15001d0300d02e00c400058960b88254607803260b80e680b03411580c612841c0c020030100d4420000c0c00c218460150883c03990104248c0b80d00c50130300e03124401282c0c0e40b43d45a900c50001061200031200c94249026400d40000c1d4524002c61800381030f480b10300202d000340b00502030307591005009009020350540640301801013032400924074051a00d502d0707640c1c0298400607180403400030b40a83c0500e02e42ca6000e004180150644204884078201f00f40245418402a4010782d00c03c0e03048451584244200d4105540c0188040036406103070b15070300081c881140440003145001c00c40c4040c240d03550b04101c81c80751281100701074401480d0349070f104c2c50b0006900c10b18449007441219000659243c0440a2a4105241c0028125044001100584a280c030030316054092000301c1c0c0b06004010683c5803149 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 207471600 1250 207470350 207470357
    0x306030111030705030412090f0b09030c01020a0f110102160303030507110319030b03030702150a031802060304030e031c0504080c0f030c0114040801020a050432060a090e0a020a 78
    0x800d4034880c070310315100c21101e4000085003000040c0005291000c0305225410340d1410a460540300c0445081c818456008400341450103e4100384501e800c01040140e0442071020f03017032200040d07079150410101a40300030055061441c1121080c5d208001c0904025100c11401516550782e040c0039004100c00e841440006e034120708c4a19101c00c0000c21100e0080d13078666909800c440c0048200d00a2401e500388640c9400100111030150b55205002e80303112071400071681d07980480e00405000c0314401e908036005009048115409070b5102410f59a0064240c10b001820703400c1400042d08080482459040141d5282e03a2841c0c0c20350f10030b0160007616600340403250582641c1c0200180754071403510b2035500d5807200c1d841d2085540715502c803040300d6140003005401d25032645403260980c1c00c079101140010b5000301e000c0107070520031042e0601d04c10000f003812030304800041581040c0401c401000b4050329000400e4501103100c0c0320341d5001404900c14150301824070f85040b8029610081d140c1000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 207472850 1250 207471600 207471611
    0xb09190b100305041101030c2316120f090317030c0903100221060303191808010903080c07020f040b0105070b10030c052209140d033218010902030a0803060301 70
    0x1e501074410104e0050742c644030380c0809d1440360303000741814625210658000740240040c00c00411403114001c56544182001a940c00c0203141c000c00e40320404600c44104400e086082010031501c1c000c030390314200c03041d8580d61b99603a10311243d20b40d442900000f070f4044c81107031103206081e0419030203400b40b01840b00d001c15006108c05030b60100d0000c00d64950360703d5007003001005016603e000d035100450229081202c0382c00800a0b4404900e142a0f101c072100383d44600c2c071070040642c04502d8540c441c0188a0032824200705401050030b403070044003518042c80d552095000c403a030142c015030b030189030b104d181407a40d40383c1110122088007051004942c407003040c000104d0b5600c0d0604101c001360842c0003240d00040140c0340102e001d480710340340c180c50111086881461b004818069804400111f84010440c44040680f010000c00e40006d0750404a898a0f0101d8000c0740341000d40b5003001aa40001d2405440d545426004000c4580004d40c10b2191740e61150030070482c03402031841a8000c500801a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 207474100 1250 207472850 207472883
    0x3061906090b030c0607050f070b0c07090501061b052107020a080d0c170d05090102090f10020c091803070309030b0609390301121103010b09190b10030504 68
    0x42d81c80340d0080340e900d0381007000d88001ca8180701014100300ca000300c04586a0009100c10300d4240050354111042d203980014040f890280104003090007014a030008202c0da61610750010809452202c14091501001d44e402003440030401180601c00451310f66070350400c10303c400541d025070090707a00b01c0c01200c91070400a0040300200c1c2c4142c40351525200e03040d8481c04c1e66500c0c24060172581080c240c3c0e51081c01006503403a80e910401d486a00c4071000182d61700c1c0d0603c100003013614140d4080d80304000709006008090790110301100d140c10191580030054462042d0280c240000600c0218584000706c0d0130b07000e00d6440154041203900600f682c3c541611030406004070800211107018025a50442807552203500c0f28203001030340104052000b240701c0300c0744040ca042d4400e03442250035115420401050100b40802d8102e81c1000305c0003080781e480b0500128551070070040c0540e004d45420000c0704c0d48003100390001d680381ca10050507845034141c00b43d00600103110954055484540942c0c0020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 207475350 1250 207474100 207474119
    0x106020c0f0f090c03040512071104051003122a0305070c1e060c020310050403030c020f1c0c05070b03070207090b03160b03070302040f17161401030213030203061906 73
    0x10941019261400b144d5402240c14031642c406003003140c1c68800c4042ca0000d4841e82005400c50314440e1010540e100c3ca01320400c030640d540a0104c04058001500800024429201220342c074400b6041200d04003a1000b4501081d40010703034507081c0724100d01d202a0805a106001f41081445260210000342d242c4d4803c03041c01851802c00c807000300c420030050201500910040d6540e601c0181140ea06800a508210550b04113a8045000c60340b00d0040c10f001c960140010b00781d07010507000411400c003101d07520245040c03280c2040c00c20b001d03032003a80074140038040c8600720160418041041d03a80c100100f000390b0340d940300d21a110074941740501188051801050307025000b83c1040002e1101420810100e005510281c202400e251382048001070b4215000a613200a011101c1e2010080f0400c80045047c010041420f401c0e0000f180414048500300116543c171504007860010f0301c3d42948107800c00099402d81019501d840f034a410800d003400c1c4403142c1807007900c5800003402266079502081 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 207476600 1250 207475350 207475369
    0x907050a0801140f0705091c140604050601060c03090e0702070e0f0604050601032a050408010e0106090509060105010c0803041b091b02010b01020c040b0a0312050a09060c080a030f0e060106020c0f 86
    0x80000380c0c00700141855440d101081c0d80c00d00d0031481c480d80d80422300b6522845032600f05d20384440c29820001c01c01007400014055980181030b2401c081d03a1680e81036030001d2011207203005603903c42c2c40043c00310b08258402c1000901420b4001c0c00c9102d1420310110389200030f9021030f500380c403450500300004c03400d510a0052441e40404208048a074051040c81c0215540e0500c01c075008000003840001242803003406000e1144ca1309900001d107190500407c0c1080e80c9004000e44807030340c0090010005030b40c1c002c0c0400b000c0b50700000f8858403500d40c0c0c03804528018180c550f488201c000d951010a00720386980c4040d8283d1017819110000701d00c1c43d0400d81c2640d403103444c1c890160b0402c00341d00c0c0e81c5050903003050680f154018a102c1c1610740302d50f510401e500c000061a00044c601095500780c5d141c20001600c00342a40381401c035511741c16595484518480c02e0f110700c0800d030f290381580061000c0c5130440c20040c01b5640681d4060740e100c02000755176600d000d403620310a81d03d0000c0401030f400e004c03046 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 207477850 1250 207476600 207476611
    0x216230c030d08070e03010b1009080c0f09070c080d020a030b011b05071211120114010b040f090f090506041203060f0b16050708070f0312020d080604050907050a0801140f 75
    0x2480040d59455201780e4540d1440c1c0e42031038040d500d40f28805820741d5586408500781241e07441d0505190708040c005881d001d107605220380104841d01c42d09074507030748001240350710000d2072038030070008031380d43c9440c496500890030ba00880e42e0000c941e03040d44503010b4121001060003070f6207942d141201004411355411000314064016040b400050160f610782e4054005528050340c0b100301144050f101043d03070004c01d1041da0280741d42d141c2c00a4401b0300f20a21703a90050168469250510717040c040d80d0101e03880284504985103a941c6140481d2609941025900750b400400383c130001c0c079060074503c424075901684180000d1800c0341c04515440c07000c2d001c1050398445400c26080c0101800904d0090440303c00c04e0368588245200040d0f994000c00c040d001074541005140340c503516501c1d080c4000c001d0040c008041d5001344840100d813a41c40640a030384164215800f150079124120038a0800041d41c1140d40c201000f07400c0031030b40080540010ba00d02c0a58904400955101c07080746008002c169034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 207479100 1250 207477850 207477857
    0x60f0e150d060b0a05130516091809020d050607020109021207061b06060f0906090b0409030e040b0f040903210608060f040510021908070302040f05040216230c030d 72
    0x7940008a04140e020040402001d001c1c02c1c0c00d5034075480060900311461801c0c0344401c0d22501003115a401000701c0c45000071181c100707814414145103028051a03111a4062004c40d81e035546103042d5902e99034400c2ca0030f504542503c995082c08080240a0300c01c4403020b0340910340484800e081c0d80c000142e5041121081d03a60310440c0c101c180020080e020091a050b02c4054a0f00b00105000e1f01d03a624120040c03201c0000000c0503450128054241c138403603660340e0b2246290400c060040b07504102003000c0030004032000107003059031500040003841e510307280700c0c0c22502e010040820990082d2a221580824880841d403585484007010103490381030203000d141e40c205001180d1030315080405070380c00c44c3c4160103486020101c100c201c0100d800c47c0003058461039804020041b41a0001c15894218180340340079890039082c810300181e80001841151702540c0c2c00182c800c40b41003030f4014040e0f070076400305400308a031007800c03800c05010003194940c83c0b8600070a80c0070000d61a0000d400d4004007004e0b00e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 207480350 1250 207479100 207479119
    0x9090a030305130804080a112b0203100c03020a0e03030c03070f03120c05041509050a051c050d05090907030605031005090f0d081b1602120a06060f0e15 67
    0xd50440191601608a66644000c0030a8200003055040034001500454000b04801d41c0c19040060b1514018508640128001c54603500b80b182c80009404401c00c0341d0000710f900f60340740c2c80070030300d040d00081c0441c1455140c84000e074071711a03141c0c000705503550096582400022800c0101601d078460181c21003000e500411800000440308100c1404d4640241021402c5c0e020b92056902070b140902450000036200041c14030080010250040c01d1a03054905031210906042c00f05000c98510b0280340d114003a209080340000610001074541a0f602505944814000100181c5a50454242d080c41b9911201c005403140d0700c0392041000701c034001001840302154002c40074000303240c080d00000b098041c0303c000e000c0c1d41104214807012100d01d035a40003074519014203420f0303140307995451407a041c8500f005092449000c09844202c0c2e650125984924a0941c80d0381c41d00e415149800146180d04200380080c14a402c000904111051448101c0c0103544440f01300ea86c0c03103042d252241d441a0b000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 207481600 1250 207480350 207480353
    0x2f030106050607061e05010306020406080a090b0121080c07090606080405120d0204050d050d0909060311120f1b0102062d0615070807021c0804170304030210020604020f09090a 77
    0x3174104084c0724032490002c5040384610340c0700b502620426041955152b40008041103829401660f440e4013400302c450811508845035901003081006116010740340c140c02085000d2041c4000c80c4280d165489108107642e4bd90002049072500800d20036284840d00d00030000030000d0080541b5881941c1c80b1000d4000030020fa4003168140c0c104046c0016090b5082c40081040d80350240140022801a002884030180b00c10000b48010a990040c441c3c81c1d040c00810000648403450815918070100c508030f1140044042203803030450681100c44a910501c001c61b1503117121304401880c411800e0f03090301c502e91340b00842d240d08030100041000140c0020260700c6003180581c0c02c45904058014008080d81c402d110090480b50041c140585841d100000d40b01d0452a200000300800c016a030200c12600d20543c6945c0b05074015031140504d0081d1081c1e0310140c21600b070003204c0140d6401051020f000d11603c000070340c0c80f079040b10f0890154414602003005890003030510780c4940755110040100c14840d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 207482850 1250 207481600 207481613
    0x10c050d050c09060d09060609020a020a1401150e040b07050a090302040c0e0927060c0901181a0301060f02070b0a0e030a1e0308070e0108071103072f030106050607 72
    0x204002c90601d4140100ba40c243d070740d13034010007184541d0400030425481d00d0030b21900700d882ea070703110030401ca2040003088445600421403410310382d0061042840c40b40d1000080b400f504403141da404000c0c00a45010680c580e46130f8140703000314000c02c1d4000302075441c03150544092203280014408a0001d490820061400350000000c40390707249010812007040300003055086400f070b04c0300f4400e180c44402d02500c00c0c20004110320717036040034030051100c3c0c140015942a584102d441c1c0c01e04200e200c0240b070340c8c40140035880c0700081290280803c00240e4402065003540c2003170050000244255180880d91440050600c00b07442d07450100c40d29000404109071000b40d01011940d07014000d482406000c40c2c0d4402a1041000c7ca501c0e042d0303181006403400408007640200108140310f804103160886903400641d00354027605500b070240aa0140110040c030350b00174035074020300010001c0515001000681468042c002002175400e0000d61010105401d803041c034000c1d250400000d000c3c600204d610b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 207484100 1250 207482850 207482861
    0x603051504140f0f0115032d0515060f01030c0819060b0c10150308160606030f1407060509060d0203070c050a060b21060a05060f06270102010c050d 65
    0x4a100301c40041901c01800b1400c1103903451140d100ba0700700041180b0140303420b000d107840820249114440301800c1d551418100c20700711030b00700f004000c1925a02d00300c28495941050094000003201d00a0b41c4003d1050b1500c8000c4078101d004111402c1c24007440e50180c002e00c810b8101c0707138a4001040d680c103006c00b0400034071441d045140a44075a80000c442074070f540184070100d0789078094500750b0549400041500d4a07400d05554807000000100f011440300b00c04d840300d4852823000d501c9070060038241031380500902e070800350902540011980401510000c40c8003851981000d032242156288815102030103a0260b50b60400030400c80e065a40c90154011a402001c3d0708068842016a0719814030b020895501214020b98035900c041076890714420440048000600a01c54103030750b00c10064503000c0190444690315104c6000c511503581e00040103030303c240b0107801252100000c1c440a200100f030711920303522a0960401c020444d51046c0500124030802d80c807642c0c6400b100c500c3e180c000b0b01c1c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 207485350 1250 207484100 207484103
    0x509032205130506030c09150d05030403020a150906050a0314010603051603110d02090a03080f21010303050a0c0c0e0c09090a0212060d0311120c010b0102010b0a140a0302060403050f100603051504 86
    0x14009508c007121961403044084d4604d00540c011a00d1710704600c1804490ba0321904010064001c5548512829900c0350b0760074140c07007140c0381c01e80d140d0300100d50030fa0141c03061244020218103010004596154194456445005801c05c1e400d40011980000c5c3c1c00c40c1c05482c07107032820103070412820864801d035400511420f8400781c91140c41581c1da481c0c940494000d2244a40d9003140010340400450030140c0c2071200d14251100e2a590754510fa030003034524807504030340780e0030f201c2c440031848240142003000e80002d101402300c02d0710a00d00b8240d41002d5a00c00c1590b14030444543c004a0300d41040d0f131007925110a001c01003102c8903101c102c108002e964a500d812001c01c0602c0c0c0d8038400110b0184810164100e0326481aa01c41d80f031081d4813402d5030b21400d0b10350704681c584800c01e0455903810000e10102d4009c40320403092141703550f0106804902c280c20287d04514005000400c2040c00500740c0c0d01da100000a07162040186d802c40e80903203005204c040c001c0e500006000205298200c1200e800130b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 207486600 1250 207485350 207485371
    0xc03120e1e03130602060f071b12050c011a1c320307080a0e011701090b0f0a030f031403040c140d05100506010801050406180509032205130506030c09 66
    0x110210a03e40740c00500d07500180f005805c50001d00c20420b5200d05d40980010160a2000d0040d00c42101c41054840624002e0140c04080c0c0030820050b000d0822101c1003038011001b030240000019244200c400c0451003180140704076441c4441c160b514001d4000c40c960301070200c1e00f000030510b6008000342d0f021030340d03400d00c1c00c0c944604901a90b02000101320241c03082e10500c0d160013a504001d000402c04103581418020640d298000c844c0000c0803c5040d9542004001049103915010030f003c1980390101a411001c58180401841f101d035124600d9284207030f0715801040280b0190b58518002660002e00400c1000d40c01d2081d4501401201c071008009000485500c2c05a20307014500044c05000c44102503035803040c0845542d00040c142d0250005803002e000c1c003460004108140038080710a0320100e40d0310004501d820509000f2034403141c1c01d03c100c9000e44425005001050740481c4990742c404d1198200c06541c01c0c1c1d150203801d100b404018003520b849001e16040c01a6403100074a5021301 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 207487850 1250 207486600 207486607
    0x60c020f0f030d0c0203070510050306010c0303061203020a05100204030201050d090821070e010201020c03070f020d080f0c10060f03020d030c1506050906060c071703190c03120e1e03 80
    0x30342e2010803801c0034000c415070b5104091101401070500b01000c5412440c01641d0449001d00c5182c1c02c5012203030801c10038684070304084000e0408070010445a00000c0d020010400e0000c281036001034502030042c040d10681d441801340391791820483c4070750f1100074089081400601d02005003035200c04c0f40030380074100e07261804603180f50340fa800030314060707812000c0300008043c800240d9200c036040380e6189080c00214035003400009116528020007000611840d034058821045449120040c0503072548154003c0c1c4a41240c075202c005604250503d01c00d520850107440c1d20b403e40742c029102201c41c3d182c1000102c50031038092104025001d4000d505000c02041c06000044500480f0101e800390310f0b070b00003a034500700810082c1c10301003c0c0c41c1c01e2050b0000c0c0050b0300f002d207000c80c03480e0883c0c0c03078148520300f07100307038040034604600403000854002c003100c0300c81040c400e4002c00f102017660320941e034505000800c81c05003011141310303019150140d408190021501c3c150381109601c40c0701b010045a04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 207489100 1250 207487850 207487879
    0x30b0103030c03091e0806061503060f0d06020d05090615010f0e1f0233060f011413030c3507090e01270302030703080411040c110f0304060c020f 64
    0x2501034800704406685a000e2001c0001c06c2090101c943c10070801c80d092008171042410f03075481030002900c2c80c0c0c4900c0b506960780f401507403103180000c3c0e615030084040d500d600d11070307084000504041351826120702074080064104184400e26940c11081616a800701114003003084403040c200340400354001e0800040b10807040c46080340a80380c102c040e4018000d030007a00305449000004525074801e51481a0b9012540071074155040740e001c00c0c143d4110048940c000700413135480740b4140401c0f9200c100084c400c9a01544040d0b82c0b019a030240c0034004410b503880c400e03001c0c040f140040c081c046d2014109500d4a003006014800c0d511200c5504680c80562240d400d0000c0710581e20501d6030603950b41800c4490301007168580d8618012400c0c10089034003840d280a902c0e8810040d0050800403480c000408100110a02c2c01c440c2a000c1d00410000b0030206024084401d1041c40402c14410000c188803030880000403141503601690380d04400f03210b6030b4203000d10510100521503109107149048030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 207490350 1250 207489100 207489119
    0x2040603050a050f011a06040b031b030a0614010e061206010504050a09020310060504060c030c03051e1216020c01080406020706240b12010e0406090602040909030810030b0103030c0309 81
    0x205190f01400240c12130100014226086078035119040c990303030741d050000b004599202c03001d441c1141c508070001a039903a101d0f5000b0b41d19020291010005030341c003000b8000c50000701e40c4a10300f035840c0030301c2c07410401e4071150054030b201071114070302e65000d0380421944400644a0034040c1e0000b030b044c1441c500305502c1e90006200c2001c16000314034036540c080704115540120310815002885141042c81c98681000801050b02140303071406800c0c00010b24040301090b00c6042120303900b002d10200382c4e0b0039034046111403042e42d00c2042008815041840030404440080c0b41e94a10748100350028400c82e01c01100560760381c04000d000fa03850940c00d02038040450180c1c05060b4500903065200c0114119400101c280b042294001820308142806844c5014200c00b480303a0644443c05851b0740707144c1c3c403071410380041e2100b40ea00030100c90002c140000c031100582c2080701514443d031595a159525980380b003110301c4aa100c041d00806000d001080464040d50402100500900e056808581c9a40c1801e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 207491600 1250 207490350 207490363
    0x90c0d06091b0e06030705040b030c0705011404060b010801050604090f090c0f061e0f0c0f0f061a0d2001090e07080117010c080103060c020304050d08030105090105030f190204060305 80
    0x2d002410380649030901d000e81c071844642d902281216414154100580e001b041402240900700344254004041403c07814401c040d181d11581c00b4009022100c2e0600c03503491052fa090341d040341c14604001400002d580945c1106068403405009241042d00d03211098000c3e1120158004000f59101007440105400c80901d00140c40d001d95800c0b072452604d1002007022031042c843c242248845031112035142e5000300c0f03210809200d454425000c81182c14500400d00e48980b00401d0000c02c0d0f0081c0c401c0020f06d4002c14020042454040542030a480074448040ba8a0100800c41181050b41c464030780700c65082c15102a1040c5440f0044c1c5460300040d000d012002c1d625900850203150040162540d1a140b0b99442e0411100a204002421740301a000b194103010040c54240c50318502144507108105a8000305002080303400e07414210305000d02e0640c420300807903000710400b60011030907050025454031400f050000901c000f000d503075120f0321914001d800481e4809c1d2140d000002080041041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 207492850 1250 207491600 207491621
    0x1050403080c031305150313080405100905040e03120103020d060b06070302060a0b010306061d0102120a200a02010f03021615020309060f06030a0b0a140c1c0605090c0d0609 76
    0x39690b882501d48082280011640a24071030304400c00750a84a00807102580c3e0031081c2c5600b005c2016234589001d0645000e541c01c02170700110404400c1c0b400f542d10414450071540c06407801c21000040904d81500ca03c00d0540c010322020100004000500f400c9505010003401103c00194080300e02c0009415540a00b506a0050b88504244607800306070b48101c1005200900b001c02c00c0c14a865006072a0812803c0004d1441403505444841039009001c103160313210315408610b590304d030700860103032060a4041c0c12003c400c0341c445402c80f202000090050610350140c4409080700d800b0501240658482d000c40d81418611b03c0d200e00001c1c040040d01c41403541400c0340981c5034540001203501c1d18100400301d001d0300706030b0801e11070f007901c0203c2c61140140c1c1084001c90145d8030745a900000e000550a0a0110440182000648191540500a208050900c640e40115203036054402d0b18040d00a0f00d911840501c041014940302c81c0040072110320101c3c000c66a07070f41c0d07211400c0854a07140107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 207494100 1250 207492850 207492853
    0x150e0f061903060902090a05040c0e0909010e070803040b030c030a0204030206030406270b15040917040501230901120b15180607050c090919030210060b07021e01050403080c 76
    0x28429500b41c041c09154054043c102046080085e40000181c0003c2944900f5005d20307564803050a0300c0d8440d0a031400320030b0b4060902052801c3c03000b2240d00034907000708408154080d840010880060100454088a1918001c50f09541b106080c02d001e681c0050001c1c00c441e9820400000180c480002551042d40105400036446100c404c20b03447c2c91081c0c20102032041d041c0c80009000640e05540603801514100101854450318000f00300200209030001c0c2c005403100c003070310010021010042c01542c44c20b903685c0303c9401054086c290004080c8405111485040c00194042c2d48140d001e04401c3c45041c01c0854881180c0c008100303920b20218003031a510b840040e10000301c120350310715940342503011707144603192a501e500c0706ca44440b03524090714454059600440e60341c490030012400a8122000108405881d81c503000e9030f070703105d5402d00207481e9003000750000e02c0720700140c01c0d02c0c919600a0000c0c2095496000400302013080158614180502400301101240e190030103814018840380 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 207495350 1250 207494100 207494137
    0x70b0903030609090a050a080a0e030a1412040608060f010915080103060e0309031504050a0506090a0204051008030307030c020106090e0a021527180a1401060207150e0f06 75
    0x78425840300084c4410345990101c0340c034900040b400140b490060380c11001d40f0742c0311003607079004945e405074500e4419030502c5242c181c40d00707000c4144096541000081c1c02c48450103880d01d20726015005621a08000c00d0840c4005207980c10700e20b040300c101030740502d0010402512120074402da41481c01055000406040042c000c10003284580041c0109400085042802d21400242c0d035142070500c0c803500d064144049401c02c18204560720640f640002501e29500d45106015600c0c000c0080592080e802c2c20007141d81482040b1001e000e445901c000745186550b036540a4000c1c00410014501319944c1d8240015046018400c03080c00a5551b07002e013903065828010051050040c0c540034030b42e114100940b07410404103ca01501c00c91002c000f8000a840c0b2800140032240300c000c41e040d4240e1070304200301002080e80c1c0046503804041107842e942e40d032209000ca076a025640540f00000504524980f0002e0081c544080c00c08002007a030100308602001140c625008415407105801245 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 207496600 1250 207495350 207495361
    0xd030c0c080c0d02121e090609180a0b0901060c02010e01121805010e0607020a140709050103140625030b0d08040b032710050402030133050105070206030402090903070b090303 77
    0x117010400302d018a00d01c10604014149590b07000c182c9810186401281e800242045581c5802040d6101c8141c020a800b442403099102294800c030b003103031107024080ca080d00c1e101a0349001c51129060714055035400040054990054500481e0010728a061101e40c80e45c80194000f64083e030a024060444002080c4071545050360944003407500041c12078000c0d408102403554001002503403260000a405072485038540402e040181e1900b0001000b41000300101c140040c102020000182031022140b00d0b90320300700301c0400d100922480b45604044050100304903442904a03e103940d030014000032409040e40c0c0d0b42105580280d0200e002104080b08101d0103248917583c0c085040c02c0906004040340300d01d41415114800c88503200385155442c2c0204040d52001d500c0620104204100c205500304000402c624040c171807004040a54011100422194456000c1c1c0fa421940030305642d046480b84d40c2040188a002030503030400c3d00c03041c007118011071005c200c02400303000c010026580e20b0401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 207497850 1250 207496600 207496603
    0x909080d0f0e0c010914010c0c1707050f011805010518040e010f1401060507030f110a0c050a09020702010c060207050a02030604080406030507050f120a24080714030d030c0c080c0d02 80
    0x1540642030501017101010400f04940c012041c0d1100024a8507000e002d03094a002a004442034102d1107008280414082da018000a075403016902c0440c0c010310782000d40b40044600c0303e0645091078015500d41010066540101e000d4100c81c07031210103400c58800600c001ca011241c8825107400aa9142d0840340c00e03c4040b445448103040c25817907030301c3c050360500c24003401610810000504005416031200780c0648103016905840350719005071450f50f42a0b0508c01c4a40040d8042e0034801d258443c6c000401074042d03c2181e482a6040c1c481c00d4500366507886680003500994825281409802034035001030b6414011148524424090607841d5030034000010f084402c0288404103200003017080c2c480041d4400d00341c421380b0740c8186404032540d4035802040c020305407885094031905003203044240440400c00f41c0c07d06403000320080740e0701039990700f0950209a011807103075034040c0c003c1c022251816200e40c0090104041c9400d000c0d5030b1116a56a402c1035601006c0045085d401c440b0300300200660 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 207499100 1250 207497850 207497863
    0xa0e040b0a0806040b040c03020d0b07020106060206060a120f121107050618101806021e0c18070311070b0601170c03070e03150103060b130903090909080d0f0e 70
    0x10306441d140d50050522030341c0e541e6150050320285c00031800c00001010018044148800303580d010380022105c940038900290b03550300a0350860003650920001186540c4001101442914000c1c80500103514203003070b0399000e03c410901070f01e90710030311400703500411700b200141148102580d0f02e04814211001c90181400d200d034002d54401c1204102c1c42005402c0b03030315107060410701102c0c2c101e030046104400f0b45031000d4032085000d49600c1e604001441c42d40220f0f420700d5400c81c1d9030710741080b010925031160b143c00f100c03011258042c0080791a04142610740c20300c0d5902a4080c01c000a400c041040078080c00d4220380021506d881002042100550340604c206900300c5480740701d40782604191649942601000f40010200010008042100d590821450b002c1c1c0a090042c212207503180d00704440070340101c01c07906000d03640340d82807968401094800c0f41c0e1196055596266294105040c07240a4440150140d501d000306000c10a0b0000c0c00b072290700010000190b000500c2c0240440701c42c20001d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 207500350 1250 207499100 207499121
    0x32a010c0212070f0518090709020c0a02120d031a0a06050f0c0109080703030c0c0b040206030c0412080901110d02070902030a060512010c0305071403040204180812090c0901060219060b03030a0e04 86
    0xc0e1007409010003107d00140030820703030b20788500158035081592045443c1405864010358040002d52451002c51408200c0203031110103503809002c400e0301500e821074000158044030360403c56041e810004c4074400e10140c01c40c0d4003800659442d000310081280d095404502054800000003c0c000e41010781603c03560324061141e081c1286da86200340c48024800310b000740045e004400020000e0500302114044a0240c40c42107070212031140c0a05142010360400d0360074030f012817000c460400d5401c000145001c11454280d00601100d42403d02c00d0000c1d420180142c1d030082d45540700490195100074502c40409410400091214960100141550f0340542407400340700d03600070494a40c2d03907401e003125441034041c0c9000c601d801d209256800480c0307003801c01605080e0081401070403181050400f50144041c04101e5458451010400540c10820300c600d40150340251504002001d402d5980c003c00b0b4003540c00020401c0308000482d0460340028203100004c0c4c110400d004035403806114111851 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 207501600 1250 207500350 207500389
    0x706090e01050f0f040204050312120901020301120f02031507020d030f1506030e0a140312011d160e0307180524010c080d02070f02032a010c0212070f05 67
    0x1945482c010035210b140c107107201c901401c0f0058510b100c1d602c550301110300411001e01221207120722580d05848580120401e0311050308004081490910f0500a9074142c511010f01c100c184500c0340d07030350014030503c45401c0b80c00d802001000e4800402c0174651604c2031103250081c00780e10596420080840e0701c50340388c030b06406161156407420304180c07440c03c0d0150b840e94100042c42c0360f03400703100780d282180b106002006440400c1800400c0e6a020001c6c0c4842a07880c03000c05c0e200d0f600d03001015144802480c9084204031000c0000741c03800f40d00703441c51212112a081100e0202c8520700400e06000c410f410402c100110304071040482501445540d034480c84180c941d0032504600d1400034120030309614020b042081140c004024050458121741d105052000119074421180c0b50601c180868880d05074400e000e120030745424840c06002c4803040c2225182a41404000140150341741032107400282c0e04940940c1902e0b084030700801050015240c10085c0c0c0505519100030000700001121480000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 207502850 1250 207501600 207501629
    0x31a0f0708070c030509040e0304030c0b07031b080c0a0506061810030803180114100e100e07050f07061b1d100e030109120e0301092d0f05070609 64
    0xd98850718640d00420b0380d150000440c8410304040b1a14001d940c2142d5000e440c040c00300d0004c110000c0108100c2c1c0c41101c40c0c40c1000d0740d80044030b10300e0248110207030204050300c1032000c802e01c0ea240041130041c07081e6012030610384c034071481500d4101c802a04545130340c03101050001c80c0c900500c3c5112030402c440880c82c01c40c501424018441c42c080c1c88010304496020010403185d82e00c00d10b8940c0c0c4181d01c00000c10100c42ca80052411004c000c0e6104400d0b45080e850101d104005000c00500c5a06058004d080300f907e402d038003554014000b002141004014031140394034942c084000c20840340101c80c0803503c400003010100e07604103d00c2d020f400340400f0f2240c11080702e81190003000514400c540c4aa07601440341170a84a480130b060340c0c154154a0515078004000355000030042068403a40c6d4212144a0482454225081c0142c05885100070381612184005908200052038102262507401c500d02641e0305855104880402c403041e03040b801081c000e03e54024408002010815070b02e151 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 207504100 1250 207502850 207502861
    0x60509060f0d0e330a20030114010f0c110301110c07051f09140a120b25020703061104081507080a0b0109120501060312050a03060906080607050d0e0106031a0f 70
    0x40d90f440701d80740298413250078000901036002503003c032801ca0381100c5044901c40f450045600c0d50741c000d000312010032030180034002c1103500c2400740489034101625101c5800c3c5894031120304501450010700ea01d592660310728401820074002420040000000400c4568141410000c10700b445804600d40c01580c1d0341c604034602d500140610840b1040442c0500000c50139010854050f20380d0442c011305231410b110340301003040e03204607035200ba032214044c82e91015003840c03c142001501e005190060303201003c14000301d855a804050503012140e00e05191960751002c0c0c50a00c03000018044081010b1000c0004a98210b00115400120910100106002000003a042141034000d00080c0d0100e2402001048002d600c15006190003a005400551074444020070340d602c0b0800e11000607080c02d40005051140d405100c1c2610102c8024020b50765910408490039000401c01a00300b544601002d0b9100c84c0038464000914000d02000d218000c10203246099144043c0031250101000340800c003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 207505350 1250 207504100 207504163
    0x20a020703140d0e090403020a050a12030b09010b0a050d0914030324030303160302070b09011b0c051203040203030d0204031101091502061501090824180304060509060f0d0e 76
    0x703113150030803140d0b401d03192140d050407494064011001040b520800289009010001848044001007176400340110300c9044181b066009003846125520241440b440341e08031f001c2c0002e0469149800c100040b008400e0300c2c0c50b2859200c1e03c0d44c0c51a2500008140318105e035081c10001e05041c0c0c1d4000200300c1640307140220759a880b004040c00340c18416203588900309407103601112411500304001c4001410b00e40d4845000307200c50310b94020221002c601810a4a0241741e0803403100ea041406030034824400c0598941c50380c001401241c0c140002c204480c014203140c8080c0000d14003402000340051105400580306041e203404c24030b90414008030f0074149550008a0b01c5d40080d01e41e10300c5501401400043c0e0b0000d0094022610a007c1c00382c1c044070043c2c0c4041070500c40600c400542000d5140c00c8110b0303a0703c10400c1d00341441c54100700814000e59024078014100010040c05041c584040f480032113031150003003074100416a07103c0c0c0305004001c5d0100000d0120b544039400d0711800d0710802c1d0380c14 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 207506600 1250 207505350 207505367
    0xc0a020a080d060e090c010e041404062301060306080607030e030a0e01050912150a0b011e0c0c080307060605100507060b060405040603050d090602122704020a020703140d 75
    0x2060340c40c0000d210b088440464006200518134211548281c0c140000455191120113003414000303501c1c4400c947d130500c3c00d4000c04844807030030355010070f41e5203030f03900c038034025002d09a0320002d245901c2441410b82600b56100390300804082e5000140350703040107542c908082e4013500410070942499403c0c0760004000c070848800312910b04050000c0c501050040e0f442c0d00070b066003183d0101d0f40705004000c513140481c0455000140e0901e00c052983c0d800700c0d40d002c030345a018000c2d0020305074200e0f0a03002419403441e100546a18240800b4452055603400141e15280e00302d00c226410100d00102004141e00a4102400302156901e02600b84000010098080d4050203440261549858a1130703445101c1220301409029000384000e681303c1c20001e60300c0c1803454845000031005000010390500c0412080c0151341090b01c410b01d440900f99070342612200b040c54410b0980f80c2c8240e0103a080d51342c0e200514045030329801a00c1d00901e581407050290422441c60242c0d5000581a8000382d80d11050f070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 207507850 1250 207506600 207506603
    0x70f03050702011e0603110a0f060c052a030d09060806040b150c0303010e0a0203070c02120f16090c020f0706050c15010902090405070c03081503160b0d050c0a020a 72
    0x30981c0d11100708a01503d0f602010404c0300c0e902030301c0c034183c0150702d4000800380e81c05400700c011407950310011301400301d03110310a64500900101044c02454440c000c49854240104211004002005844050a0044e0232419844030000c0d110290b40d04003404428101e00481c1441d008403407070003070064070f140401800c0030320441c2d0b6a0085120350341c0b801900d403044e041d4004803541741c0fa900424030f60390794420f003d001d0b004010700e0001103c1c07200c4c5000301c3e0301c03420310b80d81d031548160169070902c0354074188480c00305c40034040c981d40002444003c1140304410a5403c058010452412003103008850405503844110740191140288800d00003a800c0c0c01c0301d0722031030710719640c0107600412400c00601c0c200c606034003481900005200ca1241d0090320f131142c802c545c10405a02c0c0d4202c19200f800d04c213031000780420743c0d0380c000500030480346028241c030250103400d0341d0300148241e1a5005165445c0c01c036118401010504c01004110740c490281d12161404000317103003d2049002070340d1010107100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 207509100 1250 207507850 207507857
    0x170a02090628030b06030105091b0105070201030207080c060106030b181803041a031902070b150321071b0506040927050d030b01081b07050307080a02070e060603070f 73
    0x284441031500700c0580442c018016008000141c0d107074030f00a10310300400e880c2d02e44250308110224840b0780b0042403840c01c00b0300c0c07917008400c1c80714010015280e41d00641c106a040c15400d11040c1c010031584d20052035a00c0c01080a46507942c1051400360460758091402401416020b000351100072072010400c0d0469200c0000d8040c4044d090f28a40c914811030304014100c920721003903407508560003405540030340d1803500c105080c2240c0e00c904204030300a0078000790048640001040480c1c0525200500b440005001d0300c2e020390401c810102165000220440140740019115085c400044030041c0b090031758860b441e81c410710b00800182e8030300850050700e915640c2e8101c54441e208400b226078222011a8840002012003424013540700c89010701442c01090800c040024958031881002d4420880d102c00424181c4604050b40f140740c01045048840340700c01c0140398085164107001c1c020300f624503401000340d141000b42d10641c290010300141e019140c00d0003403004040d008041c00143da5030629 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 207510350 1250 207509100 207509119
    0xd0518010522061808011e05070c05061303081609060503100504061202091501120209010507020d0813090e06041401140106050a11071206090213060f170a020906 71
    0x64424048107000700c040c40402025000140c0c00e81203a4482d901c0e0502c4c0100044042c0d5503d1040c0c2607071400e1003011041110040d00c0b030341c0304d1801d52101ea0015030340d2504140340b00d51540c40901e84001592032011136007151078554201540205020380c01511564064002c0108c81d00c050f19a45e02130117118180b1802000203210442d45204c042c000700b4008005003c480c5c0d49400380c40c400c40d46004264003621038103000400300700c142180d030802644107944045042d801103010328025008100301e9410040104960005661000386055045000320510351381c82405440c641c4101c5156480580c40c01d041c15003441c0c0017440031580c60ba115400c28001080c0418256989004001e040084031503a14003400210310715901c40c001d4015083d0b261500c2000c071015000003541c4290500c07905203c5103400d10001c00040d07041c6c200889451000d003001000c0c0f0407504c490f0068807d031f5000420000c01c028000c101c0f004040c02020504144100070700f003905055000700302a90780042c000760042e140344 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 207511600 1250 207510350 207510367
    0x1a190303030c110a030e130b1503060102030f031906060f0e0d020a051e03070f031104020c120703350a090201050d02070506060301060b0f0a14041d090d05180105 71
    0xc41010303010f021a041030350b070907109500e0042c02d02008010410b000380503080e940140804076200701c92000c42c00414140c014441414045019400142041d046000922802c6003004211018500502000a0441c00d500382c2e0755107a012100254001810820007080e1400301d1900800600700a19041e607140504c01030303500100f2005030386a40840e0f00305028154a1407110b411110440980d88105d055900403030b6110710b414400915400094107070700c2c0c189204140c92030168010704015030312006681030710110301840c507980d41180a095011546186140448100c01460322002d0a95060b03182d100740e060104a112050006003204091540d5445070001c0d603002d00c081d01d613881d02070202595030f010a480d04585811050782c43d1400b80d800c20002280d800b4040e01599008482040c2a604043d078555040700e2a22982980300b40c0000304103c0811b65686d405c90320458000d403a0744a01c0a07051420545203856000c03000300c3c0c05c0007420700023540403848105191206020901e0402d0f1510300c1c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 207512850 1250 207511600 207511607
    0x7091a031225020603190b03010c020c06030405010b04060608010807060306060f0f030e03040b040905090703050d050d090c1214060103020a052407050114011202060a080c0702040c02011a190303030c 87
    0x10040690301c80000700c2042000e55100c2d45007103050b1486007042c041147c6110034503098a10304e201040c0582c0011485548034108040555400740c001c9001180e0b001040d408181215003075003080c0c0000d1410170051001c80803c20040c40180142c1c0b0703041110b5807030900020000403104410b1010401403c1da250700041c800d801c0f60000d4003c80d01a60f030356503035551180941c1e522074410300b0304071400c110000314032000204d8101c0c116900800a400480001d5104403890352002c550824036954548005010070380083c4500041c000441c989190201301d401c00c84c00c1110400101e0502c1d51098005200585a6a21183c1112000c0d205955901503c2d02c52802038001400c01c00020840450024103028054200c00141900a25801511b03600c4102c504204412000040d401ca071003003001c143c0c41882001d040b0790110743e44000c2810b000896001a00f5954102440c40c0140c0d19090584c1d040310520070039148540c0c013201d000c084441c2541100400c06024030015041c035a90349000d200b010301 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 207514100 1250 207512850 207512917
    0xc080f0108060708091f0b10090f05010c020a152c0f061c090c050a08070b03040b041106030a0b041b0804060b040e0a06062108070f03030e07091a0312 66
    0x4507071b510081d10240e25400001c1891071a15403094400f15850603000380907091110035244d21400c60322046e4188401581d00c0b0a00c03000032078002a00810004000101d0002001400066078070000c0c816004022040b120140d50786200d01203d8113500c3c0c035665074408100e0301079218107460707494a84c2e00c56a0700440c90760108a1a4558500307006022040100c05101ea006070f9008a54200071680c9a000c0300355540203a0141da0744c00c8038104045404a8101075039070354014442c483e0524525040004601250819500c0003e410b4a0304c086507190300d0715006103940c50303e0890200e050b524200390000d1101c03002a0025003041d9940e66001406e803103c2d0000c042d1044080d041f10f4409070300346041740003007189204004200b600350055000d0079a1000c14400d91a40003902c2504080c40e503200c14203030901081c02241890354a40c55224050003c2c803e070b82c000c04003524006860b402180550203035941d80503140d40710341c00606940d030100001c10b0543c0d81c0b580c0c00454444442511490840d00c6c0c10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 207515350 1250 207514100 207514123
    0x40b0414070618060201021c0f18030e040509061605070c030c0b04140901050d06020307121e140f1305101b020c03010c0e041e0603060c080f010806070809 68
    0x6038400100701c00e60006589541c2c1840c50000c00c0e030f110b545a904031300702d02840d144029055600c40e1070080703001040d00600841e44142d07030b00180c0302081c0110707200e05542d2503e0440116030b00381580303145464940300d000c0d0300260f01c6000e04001c2c980b4016402094060580023414054041b03203100901c201d2005c072001941e8417408a4800d107448500007030440d0450310495002c480081d082040f20305120000a0480300050000341c20100c0c2580c1c3c020207900001c10050800c40c0410745141820314900840a1442070120f03003d030070001440980d415140741d640c50312203144140040c0002410b55054069000b00240711440100d5440e05d852410042c41ca8180860f450400c01d01c0d1248144d507a00c0d05030300320611703002ca4412011a2080c0340c241d8004070991000314414003120035003410542c00062011170088108030200407022003100032900650400c1e58060b507618a1800d0070383e045181c694202c82090803010184d8034106c5c619035144c4000784201304100c07648002c50714141c020042040401d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 207516600 1250 207515350 207515353
    0x250c020f0d050c061602090a0e1c1803032601050612090a0501020307120e0f1e010603060908190801030f11060705010534080a0504050f0d02030a170906040b0414 71
    0x101701015030001036400c0a10181d02c00c9070700c007000c10658641031085c1c10301a0040d1b0b0240a0795803c80707400d040000c3d190b10020051005203882c222120b03c545282c20007851003511440b82d509864075588400d000100580c140b0b40600000600aa540e410142d800444094110b4469650340300e20450601880500c028402d41c00070003486031ba55004080350b1140d60900c50300300f03d450340c200c54960340e40d02c60910302e1425030054225040f081c4c4290b208580350314011070012030348503540e9450340122801d03545d041d1a9402d0119141080c8843d8084107500f4034403914000b1259411a01c40948060181000030a01d4043c40d60006160b250503003500c000d0303908030008011a142900c5448540d5280e0103040100610b009900e83e011218002481c28050543e6907455860b603841c1044401000080c0c010703181c0e403280304044810365400300510001164503601541e110700c801362000c0c24550a4800b1101c501141c00100095020001003442d072180d001030000b0b0481d211800c08070040d0101c1e10300d005d4036 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 207517850 1250 207516600 207516607
    0x715120b0a180209040c03020304080901030c110d081b03041203020309010b06070f030f020319110a0f0c0e010503010b0d0b04031710081014010b03040614250c020f0d050c06 76
    0x280c0b141580942415401a2014000c03044099800c900320700c41141c005006003400e10204030f05501c65400251001d8040c140100341014101500d4a000d80342d012100000300031904205000e040583d020841183c19062070781907080c1b655030b408040e410b90f86083c04260340030000130200b5109401c07034110701d040a07101c1552030440d405c001c44c80c02d61284061300415003408003541c0321071002007128100b0103180d040300138103810460100c601d51900345072189148941d0700034402003804015982c0c0745501c6000341e171081c1c600c2e040103440c1d00203050384060b1080e41740102d20f070030790340f1500120075046074414800344280e950b611302992503072001181074488c0324280080000704502d4900c0031068a0b2a1001c0f1501d001c2035017125030541b4404030280303074031203a45001040090200c80103150060f04c911030102e502c0e00864a41401808110382641c0f03030040d40c010f00c0500880000c1e00c810004254545140c120619030049820440b240200b2800b8801520a00d008d012003401b8000e0b100000400e410341c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 207519100 1250 207517850 207517889
    0x240c011b0824060f0c060f04150c020a060f0b09092406011107080c010201180c0504110d091b06020318060d0e01090503030a05180c060f16140715120b0a 67
    0x1a43d04140c5c1007484174031072a40484c080800f1980d8182c46240d0000020840401001e140405407040080d100158400c4010000000f03006014814104000c0d076000154500c0b00c000704101c48002600c0311110782c0000e200b0b0989410441609594181c40750284402ea031103c0c0e00499805410000161240c018130320023040001c1d01040c0906504d0f000d0b4000e2042100780d00f050a80f03403c84c404028a0640c4106e41008079007456003003000ca80741481541400d052100313900d00203644407220111200600d5040303c0740761110380090f45000d010240700450521311861700b20b95482c2105404684580c00100d0b0305411040b058100a11340050300000307200700021881c2c810f0b034030f410554009810600300000500c03800c0200c000c0d04000c425070b000502c100e2180b42c00740503142d44920b41102140400300010740d01c031035040140c2c0188504c40d40480c4030b030700844200c40d400d0142c980c0101160700c10481302e998056520590000d00358883c40c0000860310122070004081040c55800780c40703d030021441c0002c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 207520350 1250 207519100 207519127
    0x1509190e0f0901110a051903060e09100c030e03071b0b0408011d030f040902070f02040608030304021912022214070905012c240c011b082406 62
    0x601542c0204000e108014a00140808900a2051034030001d80c1c00e0001400600d4000c143c1c80001000d41000200191540943c04c5405021112994544c0c0415031480e06c005a070310880070b51070341c0c0f81340400c400305081c0c045946902c24000042c10740e0800740100d094408640d00c00e0f04c013326010901c0303941e8665820300f0f20b0291480d070756682520700030800940903500001c01165a08418401c401e031400341803890040094200c00d400750b40390840c01c3d20b02e1005032190b02c0390102a08886004540301c0c500351041154202c0144209821902d240b082005040e01041a010b0f02c50b87c100c450340f0101c07044a2011b0f0445a0f001c0c03407841c415003001c00e5000c029900c404668010007440d52145240758440005580ba4250030f000c801c1c1d0000100e8414007100310071503940d0000000184010224540c09284080d261002c2140500c99100029580c0c1c0800703092203110740326980c681c0c005503081c981ca100642442c0d001804107940ca00022a04c851081e0780861100044800400050b100d1081c0070020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 207521600 1250 207520350 207520381
    0xc1a130b2503061a0a0504060809120d06030b060a0b0d0b0f090112150c0e27010801021c140406050702030c07080703031d090402040e070504050a15051509190e 70
    0x11101d0300020540100f0740203400c0718000d20254840707d01d0989004000c4071807000007080018640100c142e84030a4450f001d00410035030b118440301081450850800d54a50b10303002c0d12640c482e10007502d042118080150030303a400b111a8500001d200042030740882c808141603001241d0281e6100000314940140c104100007090080c8051a002c0803541d034003004031410b5060b004007007402001c1e00d034541d251454000300c6104221a068000c101442d50301191480e003030300814050f9401160300080c4101c074900e80140046402c10500c0001c04141860045450142c0082e01c1c3c2c6403076000040c101402042110a0800c4200407a490203654010b40d0340c407034445020480c0042e620752404103d0055010041c00015002130034501161501d03401c1100501d0a01040b4085004446001a25a80c1e502c5013621030a11400c02040c00c41049c1ca01e03010002507500310a11505840300303c0d00c500c101041c1601c2800300c098484002910105d9000d203100c4005510036080044004104100640b044100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 207522850 1250 207521600 207521609
    0x40306140a060501181208090414090615060301090218060307031a09091c0341131709040204170c010e010210020d021201060c1a130b250306 62
    0x400c0119110740045171500c48003d0025000034807458140200245912220b5a01e8420355002d8503000210020509484801410341d07a0000b6450411403844001e00c180e0790301ca00501c420030382c446030040000700580418001e001c1c0e603a501240081000d5440a520661405c0c002c015980300c1c6002d40006019103000080b031409030103541c0500300c0c28241401854007551628001d085902c01a08054100c410030241090415071104803039000c10061072070302440710340b220304c40d840da0320b0503980034000c140a4041c0c24421121900e08101c4051005d4011054003580b16926610078546401e508156000f20090329074801e100003800a14082d055002004c00b00c0c030381c401e942528640a005482d0b00c40f40c0702806001da00000d0468903510750303941c014881805210310041c14040c110780001c5108509800440200d0704045600080c42560030744400c2c1c2800215110500d8074090042429110030844020309410440bc04980583d40c41d00c1d00fa803415041080303010140304101c030001c0c0034114500c038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 207524100 1250 207522850 207522871
    0xc0a050c060f0a0302030403140c0d020f0304030b070503190c031d0106060e1c0605040507031b21030203160305030604060905010e0f090a050f1605030318010e03010204030614 77
    0x12410300c5007090801e0b03a040e80c420703090250a00901010076006944018411010042a030710011010036940c000392500c8520000100011401c541001c1c0c6084181c081070803044d0310a000070070000305461a070035884601880d00c681c8a48880036900d000c5071841ca80c0288450507c03400c03840191b4075501c500d6643c0d12031410546200e190940890132226030f800341d100024030252021009040508030107510f00c8920003060b01c07459041e22040119801540c084883c1c0c1c0003403504006102d0b40040c610606030751102d224120318640380141d800030303102c06894011030501c2102807090600a0056524001882c51030005480051400808a90046810600ca6403901d000440c0296444c49031034142c0e03140c2281e004030b68803010006030900c0c03001824046903219040300c02e80001d0080c40840c00d00842400100305d003c40c2e940032041c00801c07942005000780d01c244044100f45480c146502c05244080c01c1c07641507100e900d0013080c00380c410740e08007400d13132070400340030f0080301c9124100785109401502 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 207525350 1250 207524100 207524113
    0x603060b041a0a030201031a041a010e1009050d03090320031e07050d0503090a060519030507020604023705030d05120f091005040506040b0906010f0308130b0c0a05 72
    0x1003400641d0148910f421480aa0382440154040c1e8800560b0b0030202101d8080310300780c03000140c1924081404100156403a040091095030048902021844111032810898190201c014403410151042500c5544c000070840e0034107001b101c599000d59000301705130300281c0c40d1465081041e60b0841d500c500903c214043d240d1411060112010304d1304e1118042c1000a19090801c10543e059000c20340e164041044580c0700c0d0f0ba236246240000f003402d62201c50721081144091210541000025018941400c0410000a60214607981d02540c102d070301018100d8522112790561540750383c14440a55070244903c2459060501740c0c2c02c039502101289d22003404030704115943d01850f014801c40c1c1c480c840110740035a860300412940030040c1400c84011020590794001940c0d000c0d1010395150304001c00b0b10081c03010041e5140e42c0403d0303550082059500d01002d81c2d621002d5440003030203415000c188503040d0200000c00e5801007920350001d584892242e00a01d0b221010610304072164800d01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 207526600 1250 207525350 207525371
    0xd0c080603030324030106050a06090e060603161808190b0a02090303250507030c0806090c06030a0b030f0627010c090509040201050909010e060117060f0d02060408010603060b04 78
    0xc01c40340304104c030340444c914400301a4092880700050104480c1c0c19501c5140105068540c079080b100144007590303c000c601460015141c0c52120080c0145000d00810001c01815141466400c0c600041074034200e10220103040c0001c02460b0190824070140c00b038919208451080d2000882d802c90044441c00b100c1d40392142081c0407442011082505074009001c80b01480f180c820b801c02060a22f510340ba881122580e442c0f5050016075041203450307121030407042c421480100820b9900003050402400184c005a00180741400002c141c0303000360762204100c10850300d09000c5070480b0150032046134850b0405105008640380c13040e0780c12440c10618104c003a400c0005000d01c210362032407611030700c0c641c604001c148052098020026410310608200c4451981c03250b0b84202c0c006c0959414541c903506100000500e1140130100d001100080e55090044030703503d000c0900702c02c981c21240900228030074404950b03e4051a40401c85652030041d00205005160300280003090341213400700000103e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 207527850 1250 207526600 207526603
    0xf0207030b010e100f0f090b010f0806060c0a06050c030703050f0c040b1b06130303180818010e100201020301060f080f0a0c020c0a140301050109050103050d0c03050d020d0c080603 79
    0x110300c030207050038041e030300104142200111810740084244041c2070181707480d106510005000c43d07001d400b5022400c0d108105048203032241200c0e1803000d2030f00514480c4c6501c4010310b192006050f86108440c002011000d0507800c0002c4148258031800521643c90040807070080d51300102c4001c804207081c5400600070a01803100310384035070960310b0054249404d020b9240c1113600549215900c101d66203800011140c020400c8903c9122081440c02c00c0fa83c3d6031600a09840b00080e507001c0130708054111100141d04031054407285004454400c0025460f03c0c012540d001800da1129003000c540c12914100d140c2c1900250f041c0c460340e80b610700107000389500c1111f502000725403100e40c01c1c0d001004603150070940c0c1c0050303110502e140304845000c17510300005111a00c0561002d5004207005511031382c1400e01307000c1c450040210f40801c000301e41c51901da154035a43c00e62006401c1010440c0c02904040c000c8054440d43c1c40719141c11515400030f00c1440c0e0080c01da4015400c082f070703c010700090442c0740 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 207529100 1250 207527850 207527863
    0x50901020c0a080c1504230705030d030e0307060c080103110a030b04030503060102070b042702030408190203070b0a060311040b03071e05090a050613020702010f08130606090c0f02 79
    0xe100000c0c410207005854540d044d4120389126440c6000300c400209002001180d05401749000d0b4140c101001144048415902c02d80b4040b4022038001e84010042540c0c04100c21006680500b404a49841d40b00c41d96030452050403402081c0c0c600d0048c0c82050b199010503100d058a10513424015105845001c111158186100c0203002a152100213000039201302c3c09190420742c1030040710103042e01e40400100c590040c1c3c124010302c0b83d0201112120301c9241c04203004000c113200d070443c510304181c0c031441a2407203010110700d0380c090148c64901c01d140c42001144d58454024030291241d0a212003800b000e041184025205903000200840c0c0919140c4a60003c6510080050124610b46410240a94005105c260240440190004803620350004061081c0000e03940064039140038404c214030210641000e0100c14418020382c80180d8000129101c040d400f4280300209079a080b40c0d05502c5403050400501150400c0f100045003043c0d60800016141e151b00d0304500750702d030503a003280d4502 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 207530350 1250 207529100 207529117
    0x2030603100f0f05011401091703070323040803040e06010e010806040b01020102071e121b030302030a0b0d03030b031e06040b0a09021e0a0b030c190e03010c030204030605090102 78
    0x4001000005842090742d00000980c540350784041208a00000d00b5030440304264003e1440005d24400074029680c002c204001600d08100600b074040e00c01d205540e507071b0164100c0107051105100109000040b210022801c8000100c18039a4903038403500f0080d00ea4000748070345070058000d040890038543c015100c0d1003076000c0680d14180540e03910010030002d03104a80506040d950b0030404800850b01d880c07402050b41100000e40140c005081c641503000241749003640040054100440742101140c002004603e80c05240142c0c903501e51006030320052071265040c541c0300528000300300403d905508040b410300703000c4042c5c0320000f8482400c540d0300600c050712030301d450300302d180042c000940002484e500803201c018001110302003a030100e203082d0141160317080300301d06880c00d90000b03140450f034900c0542000035206045003410394009060340108003200c00d90700350102003180800d03c14030a0111400009009001043e091038001c2e000350710501040e1105803c14001640ca0f0805008030303040b4a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 207531600 1250 207530350 207530353
    0x5040617100f061802070b01050409030507030e150c101b020a02060c121c1820030a0c140a0b0702090c03130206070606050415060915030e0f1e0102030603 68
    0x1c568502000e801848000142e40005503607202c00306048101000c12003031603e84240050341c50000741001012981c0507403102c4e11841c10b080300e0400182d03121060303d40e81541402c2c00c60342c400301600043e61321030807803c2146800c070001c0341d00c801c140400030b45c10005a00c3e0300c1c410005e4401442e89022070030864038083c4050b034403280111005007404030041600c0100312007034605175003080e05145040d48c00400c1171885824a18210842807002d0310540b06088152406011100816980c42d4240c40c03d40d141c1440800309104c004200361010b00291891076480301e43e00d20f040340ca030300c118492084001d5485000b10140840031542c888c44e081101c0c900b07030b0000d08911440d55500007c1c8035540c001000c040c1c04420155030040103071075070409410894820480820440d0900c0240011500c40001c1d145c1d0350918040c0030001e9a03005402101a50246e0712455000c0c56030170390581c05401c403503a00348814840c4c900300c02c80c54140400c190304000340c2480305030000c55a41e9841c9090380010f50b4020382c503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 207532850 1250 207531600 207531613
    0xb0304030f030b01030e0c010507081207050c0601091a10030b090a0e0705010c170901020f0a050307200a060e0301090c030b010e0c0f09010c0c120b011e0608010b030a0b09090705040617 81
    0x540d8000c0000d410380510a03002249040e42133400440602816030340303100881c001190014409200f80000c071f000d80f004c00e07800c01801c1541c001c03c4400700c22190402d80076144c20f0120070744041c0300c1c0d088001848805401100281460700b080d000405100324048020301480d840811380c0d61040c0d922007001030300001d1320640c004411500611540c01459414190311a40f585056940d0301444040c030f0705805000503640351040c80c1409031600d0811011440c9030007000703006059507034503891804140c840c546403c68103662200c0111340103051044002d07240d00418500081045505140346040c2d030341c40c0090b84165107668015041901643c80001c0348010203100d14000303544681c0400b00345900401d1054840ca54400d0f0602c010181c0d641e0555000c10004014428803510340c00100c41d1000c40e01108001c2d41c03070b24000411494060054020641e0000042501d070070359034102c0c50400c20b00400c40826814905261991030307103148a02400307a400e21740000344503000e03492a0100d90344400c015100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 207534100 1250 207532850 207532873
    0xa030215070905030604050a0506060a060512041b08010207020f150307030b1503070305101e0608040c15091802071121030a020102130e1b0705070b0304030f030b01030e 74
    0x14940c000600290410858003000100c40d94200107003402203004202400c2808110b007400b81c10804000c040d070740202180c02081140d26400750490b03120050980100842e51035500e0b041c445000402c070340a0408071429008550020f065006040e0707076108483c100c0341100d0b80e1051100400c004800301001e078034140009042c0034002d0708041480d040003090351441041c5149c80c070300560406d0f1007500029642d070b010480b41000f40d0305a42c014024020301151540c2203031451200070a40c501078441040b0455000c2000c100c4c494218901070000c0329096600144450b4004101402a01c584080440860107a610380300320f80c800c6075071058000600c007000c0f0080c80d00303110341c0d200c0003070410381d4220900004070034490b021700c0941b000010540c00507903651055140312528039116042800098952070502c103105015036000c0e46026940600c858030780c5440e0a119050242d10361145d88640f80010800041660203001c15101c1c14090310100404001000114121046041c0c1c60009030701c0b4000050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 207535350 1250 207534100 207534133
    0xc0302090c07061404060b01090b030a0209120a03020c09070c0c051e0301060905061005210403020f01021207080f0609041b1d040203070e150d02010504030f1103010e0a0302 76
    0x9500030100325041e8600b222550310704003121054900b8001d800541d005200800440780241100000c0910301140703c02d08111481445202c05003078450020b50016096900303403980b000d0426080000400c5c0c0d841e180135810040c3d25142c6419140c1c2c410001203000a402a005543d40040b140c0c100d42d00380d0781a82000240003101c2848008490010300c00b00c003141d0203607000d00900c3c0c06002810320201e040d040650502c0101c1000c2e081c640140941400b100b4500c2d04420303140c0d0940d4901030b004108544032814107a04000404520704510f5000151001e02c41d0401c2001e2070241c00544e4506000c2d80d11401032101035003007680d407aa400798560001c038020412841d42c02c0c0f548451a2b00b0050010754a20080d00407180c00701e0b4200c051107040041200703500d01400303000000d01216800101901d00b440409840541e01c40555104078107070800c6000307691003a03017503030091940004030103542650f50500c200e00440c00070f440e41c0703e5828664048003030f10000c6101c1341841c0d4190000c00800b5602076086 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 207536600 1250 207535350 207535369
    0xa1506021c081e040f03030e0114040209060105041208030f0105060c150601030605030a06050603120703080c0d091403130f1503051302032d0627100c0e030c0d0c0302 73
    0x41c0f81d0082400d01d1000403440e40280c40340941d108020301040440140f07005026510700903c00465640750450560500304801144d603400340d0304840742501c41c1da940006032054021a0088001510207283d041d04000c00c06000710f001e080e034480c9902080e0b80e03800c204401d5100c1c00442504c103030411015200001c00804d00e0b00d03007004050402040190310703040800e24000c1412400c2e1a01d907142da0902155003400d01503550402d0004d103d507407401d8031a46024241060203003030416100390010f55803000f1041c1740d00c660b52496000d501c2c02c0319440d4030601e00399680c205884001d0600300c0d580b40021510724000c000022a8006e40311084019056002030340113010040a41c01d5448400381c1d400b0050744c060003000150f014280300081800142030f646410410340f01164100c541c418401d210192100b54a0602d1040110b02d40340710b1034078940f4419050410000325491340c60b050803284c1c18003641184528806200560803901c12201080802094405408016005a150724018000b6003440b0742103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 207537850 1250 207536600 207536611
    0xf0c01180201050d0f0f0c050d0605040603020916030902360106020c04090c09060923040503070204090312060623130909030903051203060f040912110111030a1506021c08 75
    0x1034119684011b610903282c650040400041000070680382c0f0704076500c02c80c0003408094a04118407411940070400880001e000300303003148200d00b001503599119404c101060340c0c2c05032a400080008010261040b81c500c0030100a561510141c111110f1034100c3e03e504890080d4010180044400b01780401011291425500c1602036103010800700740320301030034005100c107400c0040c5420b55201140120100443d409103907112020520000c240c00105444100390100c1d03000604100303d01e0151801882c5044d803203003040c10308100141968025010035070381100301031800c038010002004801e0612074040c61108640811005020a1005a100102c0d00307100c1c0c2000e1491a449490311440c00040740207060001e070002040182c1401d09000d403030304000b81681c051004404540d501c0710510b00c1d0b081004100144410560348030102500680402c104e0010159541d04203080f4500241400403866070340d0100504000941c584000b40b154580d0b9224030340034004a429403011107844201406 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 207539100 1250 207537850 207537881
    0x70809151f080304091508151005190603050c09300303090a03020c04060302010c0231050405010506010f0507030f050d020c0c09070201051314120f0c01180201050d 72
    0x508590340c01081c0515000740150100868650b4642005402075075220400001e90100084040000740c1d00081d00705280301c0b07200078900725556180381000e40c0440c2640081c1d0701290320144602c400c50304035120b4003921103035034040c002a502c102801d441d81c440d03114804d03000034800e00c0010700300c14900c05055150541400585921000846143c03030358000751003601c8241c01006044003007640401649012900541c1c0500c000340c070356000a00509031100700a402340b0035090501500c0310148041180050300180c80b13907250001c2880e040d000700300480301241c4e590b1901c0d010494a41c0134403c0081c40c0d00c42503554034607140c015a0122030f404400380f15a014403006000c521000c48042c0050820146040d00a020062411041110a20018002000356450708007404a654086158481c5080d00700303110004a80c01309402503c3d08084502e494407800010940100c00300c100d00083c070040303100700024001c40c440ba03075012449440301d40d0024041507003001b1102030b8005540000000080084 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 207540350 1250 207539100 207539131
    0x301110427020c06011d090d140a03090803070f0e0f0307230d03170f010515070503040504020304060203091501050f0f030c030a03030f0609020711040207051009080403030807080915 80
    0x260807032a1130401c3c0c202d002d800200960344e60f10320f1000802aa8071198600040c01c60600e0302c14050a40c0c09402c40c0d00b03500070400030344e181e01607000e81c0056449507840b0100e40d80c5c0c3d180c447d17401042c5d2006e8089038000103035109591707280c074904501c12444145000303001d400001c0c903040648401e48030001c40099183c88100e102e150b20394401c108201500e00a4480020f1751f09010200b210400004004c004401d00540051006881709052055682403995045a8541150410a1031400b0f0383c1d200d154410f0000003007004000c031540244d8010640c040494604201c5c0b0700c2c00040408007400340316001120a40f07681d00a140240134103a01034000303004d840903d02d604000c00d003050303101c09080d00883d071111219130b52425141718000080103081d40450070060f040d41d5100b080c100b10762005204030340104424081c000180400c106078050742c072003080380c0d4010f0320304a14203404c5484203401241c40c50300080c082c207000e040c180d4421040f52010f0301c02200d0000c880c0300c1c0044050980300304601c3c070b42d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 207541600 1250 207540350 207540367
    0x1511041a03040201090f0608040b18060103230f010207020a1a120a0f0c0c020a0f06140c030f07050106030308010f032303090613030c060c020904063602030111042702 73
    0xc1b038990003420443d0b8400c40c0e01d107400c0c1864420312402070200d025090a80c008445180000b0a00c181940e921062451039200f03032611911401035424259200781c011050801d1580342c0550050550301c1c82507500c004001d58070020380800b0741800901c91002c0c3d104001010b11090040515540021303404c41c00131700c4141036000f0004072000000d030302c00860000c0703004000f585000e08a400080c8214000d01c4645400c0c000d0040c52064100150711281d0804100c03402d00c100180141c0b0382e4502c840d1b507016111b080c0d9051040c083c0959100507408902c80f0000814203a40000104080e6078204040e40400080b6940030038140030080e100240e68001030040c0d01c1c90307964902c01400300045040807090900d0860034002c4c404005a84507a0911031503401820040e140d03040800d900907045000080c0303070031042c402030864031405482000607405850018903640c11031480e40300d40900a9000700200244c11129442621070350064800314800720020a0410340303842104044180d41020250510642 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 207542850 1250 207541600 207541619
    0x5240702030307080f070209090102030118110909040b01031401060f03030e0f041109091305060723030a0204170f03160302030403021503061e0105030f221511041a0304020109 77
    0x140814136070410000a001b401e505e880c1020f5500460740304000c40c6503500d4440d481c0c90202407022400540c0743c40e08050381c2e00c02281811307100c110303001400b01202c83c642468040a0b100090001301e07482c11244148404c840014418002565090180504844d04545080c0e030341a510080981e405505075502003c0c54440c0d001341411329040d83c8c0f05076281d025160410060702c800418543d02c4401015202010460000b4010b0b0800d00505210303c40580184005650300d014240000d074503440081404882000c079801482100e811102c48210320303030880d070400e40310003110015040341d6109111444800305188148100141f00340100c902d480c0d542e9001c039541028400c200712003140b000c82001200c0c20107511a822a4008903440b26042c407801001030300c10700024100c0b00541300d00d2400641c1c0000c20364002600ea0b5007100c500c10300d600300d91a03d0f02000f124241c0c0504200c0c01c0621070000300050206071030a8604143c2090315a4030010140f402980000700140d040000c01c10300004c14026 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 207544100 1250 207542850 207542857
    0x501260a0c170a1b06030e031c050405101b0306060f02100c030605030a150e1501030618061a0319032001110a0203090a05010819091103030d0e070524070203030708 72
    0x82d8255920b1382d40c44c28401504980140c01040350942081000700c180121998000b0314550b07040d9800075140c2c459040840c544405000c00c2c041140c9421052018140d540b0540c4014103000c0e9030a0041d00d449540c229a6103001003241405070b40f0144414003e510981c001d11956030003860b001402d26981d00001c4d01d418070b40b58094440c0d00c2680780307042c0c021045000c1c41007542100c1d00200f404881c91481c0d40100c90f41484054040c40d65100681d4610100000102c129a0801028080103100c3343e080e0700741c1506520b000c1d00c0b0b0700c20694123002c1c0241001242e41119015202c0144a00c16100715149940d42c0c0f103020301c0c60395a18040c0e01720780ca11290240110001c56401583c070f51201c00e0138000d108003140c00085c18010700b4420070400c041c042c0d9803641c000100b1384005c1038401c028502420070381c400101c2c3c47d5145c0001719405118a0003a84200da11140c184100e03640e89649805001c00c0d201200151407400380c02002e020400030100300140f461601c05000c90f4501501a251600c0d140c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 207545350 1250 207544100 207544133
    0x10f090b0918010b041d1209030604030f0c060203040821091f09080a02060109060f0302060f0a030603021203090109050906011e0507061a0405060a0f0501140c010501260a0c170a 78
    0x1401d540f02c806406c20080e8804144080540ca4035041440002954500d00104010100001c1c40300f802c4000e8484c0420714480c0e6449076080d91a0b043c18503001c68207400030088a0b80700c008410f01d12480c0300310b9180712400b42084001604d0000903080c046803440358a071802c0500583c54035071400004007180014581c1c0c60040d0b003e03107095410700140c4000da862981c400d0200382e42d045018070140c2d80701c000307c400300f8940f00c10407591480141400c0e0060440360b80042d520011852034043c0e0000301000070801c4403400d0380e03405000782d2214100142c0b028141e9545002402c0040c3c0811081c0c00700c0c4200e40c040c1c0d03c40c1405810105d45507545c00a4070078080c0c0811041900f8614290345041501446410100442c0c49400841c04c1010000013106244038050401003020642c4c6041c1003c1012545d805c40b00360000e110f95070315004d84001c00d050200030782090341c06800201410725004110319130301c1c81c2d0060040030380910301102c0247c0010840300b41902402011003180000c0e841e0941d80c0c0101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 207546600 1250 207545350 207545381
    0x31e01020901110607050306010c031b1101110610030f021305130b1806151504140901120b0105041d010c08041203090309050d050a0203030301030b010f090b0918010b04 74
    0xd01c80c0c0d000041a203075104407802c800794041e00034802090780090a4a41c85402841c0081c0c42480e1400c0498001e4521001807a03400246001d410034054001704012084200f80c0381d034801c9502206c0304c035a59120840d10420100c03526142440002d4217103200a02d86800117042c03400341462140350104503170088e14100c0119149111a200f00300c16500300c1540b20080400c00070701c596038250095118000206024004280c880204146580703500d4035281c0113411445103a103540c2c503021464070306c0c506046024072a03040309000056070004400010340320355012040744805e901e0a424071025003102c80e01016102c01203005000d80503c02d100708403d40300b1958030b510080c102401c03c220680214450f02c410035080507081302c04680c2107806241252002c0d5489401e2040c1810018140705e410b4000030f501d030000000008c1484120000d05041c0d401011faa1502c3c503913a01e15407001c4510520030395400102c2c03600000c0000310309540181c0e80c040a0000400c1c415107480005086855440703028094 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 207547850 1250 207546600 207546607
    0x12020a0207030830070512060103180c03060b03071d1003020405190b0111070314030c1507030f020a121a03070609080f030a090506071a0112050f070501080a020702031e0102 76
    0x4190f841c1c1000f090b6241139034024145040800d4010170030320990260f40354008812011642c640d110fa07020540e02590011121003501d102e103400511001d5600c400d0351803c2c200340f0265030302d20340410180308890048509035941040004c4110b05070f01c00600203069850803250000250b101e070f000c1c0611450030318045020b031083d00c421090465200c6002a41042001120b40728100c4001510006a0760402c2601003111004000c49203184682c84c004266401404c07230000d41d80b44040780007400341d045d9850600c40300d0594040e4008900643c04c00d0030005500c0b5a02c0000c00c40e0907442801c0039401c08101c583c48031100b001207881c02415900030000a4042d038030070440352409014005c000d01d041c801441c81c1c0448401c0081080d1602e000d018401c0800141541c00c101c01000d00384405120459003c1e081d42e5030b0342c90070701c2003401c09000796080d00840100300c4001d0030100300c4600340d5805850708003151b01d6440224000350400d8008136054841c000700d1110811510349041d000a00000001da034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 207549100 1250 207547850 207547897
    0x18021201150914100e060d0501022206230a05030702010e01060b031e0c030c0f07150504111f12060302030106030516050a0305030d0b0f370612020a02070308 69
    0x24001c00007030507040b00c8040c00c201401803c05c1c1c002c1494002c9002c55045c12900d0060811740e009204690543c400ca40350048042d481c903003183c0104c4100c82094403424a11316000f541c845401d011007213a102c10403005c100241205000350041c40d0840e070725200000700c0c682a00902803c468a80e0822003004002101700301c40c0014008800f0420300301c1040d4000942005c402e5143d40340400341441021490100c1c0c050300c0b200d401e1080c0d5910a410000e50700c5039440355592030000706415902601d010f5401c0e2034405481c1003510010000e444111a013084140c104202200c990071a01e140013070322501c43c04000050f80e0300340138a03400340d8007400140500c0032683d282550a50001e501044c0244000c00301000445c101100781c1d6100c0d4051800441c0c00d402070750000b40d085031001c005552080c40040342441083c000c801c092044ca01052441c15100d192410800c024699480303080c1c006802c44808040101c401c4c1c0207849081401d004075804140c50fa603822805810040358000321110780f009084 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 207550350 1250 207549100 207549131
    0x311030a1d03070c09020a05070b010905040309120816020f12012406140f04030c060203090306090c0a05130609050906250c14160b090901050301180212011509 70
    0x8511081c04020341c90b1455903565840380054a02c100d1003901c0e404294002c0e00c0380038504940c0c1c0700c3d0340008031030b00641e1280d64600007040180c0f010390015901400205604408017441d07188190042d02050804484402d0300301c0d0a41c00c102d08a1b040840c0c003c40c940c40b038480001d440b07003500b014000811103540c80d051064500d03030412480500e80291180400c00150003031080c102c0c0404001e15660788200d2403051004d0b83c411039000800350345003180001061640400544000780c0d00f101922400d85600b4080d41c3c0c0c0345035400c4284da0009211104010a2070026044541d27031020301c00c0401c84954a8940100f12001101d4240860300200f08203c284001c4001080102c4204400600b03003c518050007000c441d50010010702c3c40140c118071400c0c0c9101005034490107503541c405481015214000c114042d0001c4d0f200a004400c50800856186410700032100000d010005000d4003818503020001c0d4034100c007500e00500d550f600302100501904444260281c4641c000104100144a2210 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 207551600 1250 207550350 207550391
    0x6030708030d021b0606150c0f1204081b1f17040b040201121406040c020a05010608070914190c1b0c0608070302030f0703020a17010905010305070f060507060c0311030a 74
    0x4c00c3c1900648104045591101d80407907110002c030540701d0300d401038220003510708230500300708145a200e05072510078140d01140081090b14004020360320b090315141e501810101c40381c28002c2e440f09007190314068542004690000c04840d620b008420004005801c5415020644003942d00b411444108015035030007101c00d408581701340c1d0040003800c045030032110f42d05a01406c0326110b540c0303c24002c5171141c400c01000b03001c10b802c40c008129603907031a440295511450b21520400a08084c000c169051f00103109038454040e0510000044080b81c10f420700400c10086e17a0303000d208004082c802c006904809440c8098400d80828580b1800c00b1030107410880f00901d19020140100100801e0a03812030446800482d40d080160b114200c510301a02d40403200701c041c2c50f0340301d4000c1c000280988140c010a0490b0f0141040c2e406180d10380112148c41c0403d4015040810410450000043c18560098028401c2450b0010342030740300c0c07040e8010301da2050340d06054403a1204c0044441032081c1d00d1a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 207552850 1250 207551600 207551647
    0x3280b011106040803130201050c0d0908060610050706020904140408030702060a02030403020d0c0501110d0b0a0e060a140a0b0313110907090b07050c030109030c0303050702030f030a0506030708030d02 88
    0x4103420f00d0b05540b4000e003880003e001e902e450030900c440808590090094950303034513411040e10403076035054100a24030600c030f00c584201c41c803410010071803078101100000390b0380b0740583d18540b616400c2d8a484000c2c0d407102a805e0341241e038862810500521100c049405144508111b42c0d07603080c6404020310300300c40275100005d424410400c0c000000e0700007a079010600541d041c5651038a080d4105940103029107442c07454040d800180030307030080e003480d803115108610440b410800d030360300c0b03139822a00000120b603015045540742c11b0501c1802404031007400345840040000700840c2e00c4004002d502e4200b9103464418100c0a4102c200300015602549075040048d41d02c0003076483d2030080201078210368803c07a40c800c6400504d240a0100600c0420a14480078009101c200c0283c03400030303d903100709407081c0d0005c0d1509012403907452010044404e00b070020300e060b5003145c4584c2583c000501016003103541c50301c01d49000082c11035060010701000748050300d00586a1051495520046485108 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 207553956 1106 207552850 207552853
    0x1e06111203102d12050307021509040b03010b0f01030207060603021f02060c0c12091801141203070206121b040807030c061805040203280b0111 63
    0x35504100c07003800c14504075200200ca620202c1543d250754035004004075a004224400030120064411806001921301e000d426500181605504e0700d00318254110108201c0030901c2c00b4800c00110130019030083c41100d100400081c00c0d0b940d00d00119041c56070109141e411322200d43c2c81040603650185c82e800c60704c1000101920005e40c0b0b101101d00500c40e050000c0c00c80483c0c6c82c1a503e581c1c40d00c42c001c5c40707141d038418191102500007441803038104550300005201c184559000c41e00a040000c0d140304600d002a092190601310150900003583c070411035140143c44680072209a00118250551607884001c160115520401103c1c0403030365001c00c002c11018404078010045a02c200340044100790798401c19900c2803400c4921410055605c4010040e0381080c0c0c00a662200b05c405814101041030286159141c6006a400f00003075a9241550129600600d03800c190281c080d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 207374100 207553956 := by
  have h0 := BRFrame.cov_init 207374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 207374100 ≤ n) (h2 : n < 207553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
