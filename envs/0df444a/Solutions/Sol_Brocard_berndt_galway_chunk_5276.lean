-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5276
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:19:45.893499+00:00
-- url     : https://prove2.me/submissions/1f6c39c5-de11-4c9c-a482-bd6acd81b701

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 948741007 ≤ n < 948920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 948742257 1250 948741007 948741023
    0x11406040908160b1008070b070204020f0408030c030304111f2f01050405010b090f01030f08160318080f1510050a0305161203210b03120c071a030106031107 69
    0x101050188110350140078205c1410350003841541ea01c1c2c09550351115000311079000e0000c010001c014545a070040c0070764102240c0c6036003003e540310241400c41e08400341701d181c0c42c0c200104001c01c000c902c0e6200e0004100c01c50b140c0b80f1000144000707050a8100c626500f0502461181e0009401254002c501200300c00c401c1c04003040e9001c3c1c40c01800b8060559007207a5560900c1240f81540c58000401031040d4031001d074160f0b45038a5a125420b05d1085042c00340e60039038080003001400d4081c40c5458000e18004d403560501032007125000da11170082a40850700b5504510007507042c9490109488145111003001c81c90340d5180e16000205442603035210075032104296134001300700640450081c04604081912031003440c0d13200710040c0305555443c80100000d00c0072040c521480303030301e0400706000224090000381a64009010030301d00214214002100000031800084600081003d0f00c068030301018003400d8504480b116510500041c040e200526481e40c5031490420320b20780a4401c03860304a000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 948743507 1250 948742257 948742297
    0x7111c0201090209060103142202100f1404050f011d1c0501050106091202130b04180203060a0c1e0c080a03140709230a0504060f0611011406040908 65
    0x64000c080b0108101d001e814028006009907000744651290501086403419180e1349035080c0c0d06002c4c1c18081020341c420060050880580c503030700344407480480709454605c41d084201d500a005070000206a40429000300410301c69919400848e81602d042800e095807051452500c40c43e0090324030b0155508444c0383e54901c48001094030580001d86e0254000b04110b90300c924044403905040e000300e5142082405200c0c006003030103984801c030b50001e2640050510000d0002906680300d04282d0348015009085010551900384042a00841964010407110b2210b8501070095824641220f40031196070042e854614000d0809289680d4441c010f9030f644c061130351000e001058058090b1840001c9080010b5546000758000015216116820352010001555541c07402c81483d24040d00f00f40720b8070002440351240c0c0038001c060282c04000d002101d0a000c0000c2003100c4405604401c3c2e1704100f0390b60508810150003e4000c403003070b9004100050582003810241c811448100540380350651 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 948744757 1250 948743507 948743563
    0xc060a0509090903040312020a0c05060a05070606150306080a050a060915180c050d21120e031209060f0a0f0603080d06080f0304230301061a0c0111040b030711 70
    0x14406d40c2c1c070600b1031f40049101c00b08102c2e45c0303080741800104039610085c4203000d0b07031500c2c0300980038014841c904140b425005a40f41410703a5910350002480c402c02d512000c3d02d040d058050b090140038560001e0039100200c0d241c05564003035100300980143d41c0d40007018203004072150f4031070001c20920024007510308a4043c05500341c1210f001561812002e020204483c584160a41c540c590445640141140d03402811081c501c08465110180720002c00c04d105a40043d0240c1c0841080d0100a15200c0001292a4401083c0200ba0410a8010783e0400549652056140c1d4110072128000903d4065800d482001170041d5040507201d8440814202410411900b0900c02d58100e4810780d01004a40c113022a034070701490041c101c44107940235011004070940c10b84010182401400070480755680d00c91600c070551035403000b0000c20b50000352041610700034020400501010180c8610300303441e2400c070380807034040a05184c1c10840011111014020304012039214103500e6554601c0e0011001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 948746007 1250 948744757 948744763
    0x60f101a03011a0906030601080628151103030403030e0304210c090b030a020f0d08070812060d030c080a0c0b0109020417030c06010611210c060603070303020c060a05090909 76
    0x12064080340c0b00d400304400c1000070742d40c2c1135552540c0090801c1d411a00d80c600195017003070000301010303004105811a01810b6945040b4020b9601c054480c8224550610b480e480c8100070180c4101d0500c10780c409611101280003003101c1d441601440c00003454000760a21a045201d640c1c00788040a88500d1080122114495948940d030f120384000d1407410354414000c010384501c0c0c1402c80d0305401101140c009410b104841007644000141a00520845079a426003280c01c81c18055030710a02c04a841060012079802c000e40080040340c0095030600c0d41d507002842c03000382101c020072000011401da41d4090042d4100004107506c040211025a1100b05900094126100b4920700352400e0a1100d403095004c81290a540019801307000c0680c285003040e64800b00d0240b064040d44210440080800c000704da01d00341c02460021004e1b9540c185985103413800341c002c3d101d5407181e000744c181000000e80004200080d05d5041e0f510a4540c2d030340281c165600e00a036500c041e003108003c000c20021040c04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 948747257 1250 948746007 948746009
    0x9140c091b0f1804140907060e0d08040e0402010f021c030e0309150a0e01090b07021002030f0a05270109170109140607140403080706050402040e0a0c0620060f101a0301 74
    0x2903c1c100070a40b5264009458485c06489101c840c0c0c008100c2031080a00c0b03100c429102c03000140071800b03c03e4456490400c81e52243d0300490f00b10003024103020840da406440660644020303c010301b11000c100307000441c6c2e02c800b8101082410345c0c420854003011014026603025420042140d00500b000c0c1c01800b8840d4094100f02000410468008000c1d6004980c41810350f01c1e07050b0414100304542c0e00f40501e58540a1221084d484248400054101c160300105410109075850a80360440086c442c4020302c200c042c00320344108610741e10038041e60300c484840300701c880303510428502c00d1102403039500514000038060141580e15589039100e01c4005942405007551f03550b40750745912800b912074401c0c092400010180c28080180070042500c50700102c0d0081c2c001080003840c561014111490201465005c0761013400b481d00400003550003009402180b5900d440000c4140709504100b521407200500c2d8521229064010640300141148110060040c10800d8044881c03508443c00403600b003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 948748507 1250 948747257 948747259
    0x8040309081f0608010c0203030c0f070b040c050406140603070c060615080405061b1902030d060923070905040e03090303130f120803070c020d1509140c091b0f18 71
    0x10b00d40005400c84e014429400b04684983c040c41c1903803100c030600c07a40c82d0f01c020841005000280300940103c2d8207182103500640c0303e014000720b50741c0762500380410b40300cac1703503001e00e000e240400c201c02556240c2004480d032000c5c0c030b4585990450f180d80391100003055070360021301409020025002c41717503410480c414022400380d421515156660018410701d11000149048441e4040c003560000c88810600b08070245031078010740307052104040c5800100c403140d9110384030258030740e00c90f980400009582180d52060344541c00025140098000d0700310503991003803600895988150f240c040b0014000d9510800d0700600ba02d640e85a9010000401d4041d8007070a056203282070000901c0c060740b4a9500005680f00803401d066030ba6400040e40e5141e000d200c00e036003050070129542c00240740b1000001e505450600006103c400324100741e000c81e80c24841002e09544029211084c5a44100c01684d00103184003800081c2140c0814010740c5005010344040c0c000d1010030011201e5500e85000402000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 948749757 1250 948748507 948748511
    0x1e19030f0504080a0f050c1614090c04050d050712060509060c071a0a0906090c060f030b0603010e071103030f06131505333708040309081f 61
    0x800c50032030811504150b070010100f0b441040481c1101d40a0b03515507a1603a03081c20680d0070525404021400c0c0650840b1021a88003000d80912041401c021440501c07601524442e205203409010b00c0c8403072240d401101c1c480d02c0c0c1d18144008120003044041d010307094119864070f0407a408d01e4104054071040c0c998400034001d50001400c6040404c06030b9901d9a00060310500100e05c107944024044806803010b68213603160418000425518021454403622801c2102212071419000400e01c14030081c45030304040c180b94400401e580c1d4a030079641901c01c041c0e080d01164580e4581a0b46c3d84181d02d4002d40716000100801000341d00d1a62100d21582066845a0541d00b40e0880041291421240030410481601007031040f400c004e03000c0325148440e40c0913244500610390407285c6100c0d4400d5580c02c1206e0018002c10412001c10340090701e182c60304480c0c110125800c815480917400400701c10100400c1c1e03400681814400d250810040c000c85003510702030109a45c80300741c0f42c0c25100e14403000c14 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 948751007 1250 948749757 948749771
    0x220b15070c0512060a0203041a090f010b010906020304030816020d0609060c05070f230115090c0e030709050703020f03010305010e06090313060503061207060203130503070506030105061e1903 84
    0x100f0b10200d888164043c00c1c01038025555150300c00c00007900b0140c401d40c0d08005805407184d01f102c0c0c002c0450701130300c0081d0080a10010450100d802c1d102d200091030304102001008004094002050310305482d0f100701071549030000c810003500750150034040070750301070324074030900b02440142c0d44602e04076802108244000a50103900352504d224016000300060b54030f40300c0f280401c0074824a258200016884000081c070303400c0e9207a00b0f40d903060003003c80704000c459082010070382c00d101d821542901030626516050b001c0340060b4076001c142c86000d1044c0c0e01c9500007505103200382d0480304074540140310035840f96100c0c10b0040c02440a10b02c0d5141030310941002c02c04036400001030380c10301c2c0e0b1880005001581000e00454181d000a0030458000d29030302d52042c503c80c0c0601c280406811143c3c01940c0340c280c1a0a00d030301412540d80200c0c040e821000c01440540c80300d90440e415140c040d9000c0703503a203001c00b03a10500c400001c0b0a0304512a004074840310740c100c0d00140031084c648666014480c007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 948752257 1250 948751007 948751009
    0xe131d01022d07020108060915032a0d020604031e05030d061805010503070501121104030f03021c0509090414011e0b09160c2d030306080606220b15070c05 68
    0x30310403d0742c081c0c04650035000040140c900007880c02ea10800c019034045c1d01091110210f45420303442c032220410b201e090b0041c641529107110140d40121003c803601c0940800c29000b0810742e1055001c003074039504409500348000039020105e180142c0d440812695140d844034130f00001031100c0e001c1c0003450854100c900c0202d52690080c0388c1a9500240a40703c00351411780103640300f0128610701180f40da04c846440c15801c1d03172200908021401030a03e107810500c0e902d002810440c0f00c003140020104012000a0783e0781d400029251004401c0d00c1d40001b03915281031a2510007183c0d8000301507582486001e0242030102c240a001c20040c4840901c0703001c00c16001c224800f8411034447c0c413285900002240080d01c01c108030203e007030040d44009220b40c40f0501000c0c62494895a080144090004100030140d151107418018031104001c0c1078141003100014500002c085140c4003000c0e008140203062440650050a8204004060005100c00b14817510701c40c1d01705000130740b0003681030310f800182 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 948753507 1250 948752257 948752347
    0x50105030307210309020604030b0603010c0c050c0f010e03061608100623071b0e0a02070308070e130f1506020c0a0b13030f06020c06070e131d0102 65
    0x11644010f030b80c2038020324a452500c0340d081210b001000c03d6200d01a50b03015898102c010f102841c01240201c0642c50b01c1001c6c1801e6a00c801c04070f50812030300460207004502d003c80c6c407030000902140e604010a80b5640129002d02400903065490f00914051200344000e203146951010503546515030300307981340d080320780c1c0704a8240300e9100800c40c07a0880c503a06207103060403000e814409445050801c80291544c000e030a0702d8461045002000a000b804492b100843d12517008072612000e526124a41c3d070001e0a10300d0240c581010f100c2852002030b0503554880040c071100d609043c0812002c480a901080581034041c1b070200c42440e141c1c00441c001e41b01240900d40c1c41006402c194803a8a88075107001c240e070003c18508000c4060010100008241805100300b680c000d1002603181c2240c600075038180f65000e400e103024800c503880360b00410344501609000401402c2800a400c20308400d070150000455072004149510005d18030016110040f10441050500c01020880c08425640091 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 948754757 1250 948753507 948753517
    0x20d060608160e0a031703010305060a0204030f1103121602150310151704061409060402101206082b022a0f090c0301090c0c02090a0b0d0b07120501050303 68
    0x4490b8807101e144039506025070036072214101c010b00400ca010359603482d40c00501c000c100307240c01c20781400401002404410410640c000004400840c903181c40d5980700310b1046000c0c10010600b1180c1c0b0b03043c9003166814040c41c2c100411041901d0b075103074411495014079500015080348a0500d0789540e070780c0784001d5130a03213204048004110802c0d80c03c01d50003508a4084409800800c150030342036808510f400e04001e4080c0788240004110241c40303140f4240742c0c00d0014000c1400e6840502044090f980e658103140d4000502e0500182e05003940308604050102600001010b114080070b00003c0100f03a8030741c45d48440581082c2a518601c210105e884140ea0140c9481c52003158a40101a1b4031700e409000702c90000500ca442c415820f040820f6910f5170407502000480340100041041524a000c0c40c0710042c0d26140142d2003c00e1035002940c0c02d0809002c20300303d560350f00c44000c0d03947c0b9500c0b0900d1800390030001d4484989410000103045400d021100f41c2c00e24105400081c3c907080001c20b4035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 948756007 1250 948754757 948754771
    0xc0d06091404060519090506062701210804080d0809031219091505060406050303040e220206070b0403021005010311040c030609022a070b0d0209031002030901020d060608 75
    0x45080d0b02c1d5500d586000e44000380010302e443e202c0301c0042e045410a071040b20320b454400c00140405140c24400c000c90020240710301c03d0325044245518500811525103281541c824028141940310340c00149400380b00c0d4204001c0600c00001404a1045400103200700a01399035a501550360382c511801c0c0d5100e00820011596015400300410144450702c034040b000700c5e950340d03400582d224040d124001c50010003034940d031300e041c0da52041c0807003814a802000007422040c1e008602d02490325040301c50103030005003044004010403160080c0c0c1c088041200410075002440f16403100c0f010304210000c40010b95040b0094441c000ca8510050034902643c2c3c1207070340110b0f0038598914003001b8440601030000b074140070103581c0c03200411460308504c06042c09002d402d000e503440ca42c0d42010100003000300640400701c1c4d8020601000000401c2040b16080701c0b01100140e160520040400d2134180c100541e850928004010002034480550190410340b4070040103010003541c441e42a00ca4003002c0da403003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 948757257 1250 948756007 948756041
    0x10020c0105071b0303020c010902101808070f0b130504060b25030804030509181017191707120507061505030c060901140c010e160501050a030e0a0b0c0d0609 69
    0x6080405d011b80d015205041c000340000c14400340360b80c005010640013100c081d0215080e0404000b405030140034600181152000400100b42400340704454a602c40c130880072305080c0082c00800d203035400c03c0f4000080001810500109481e035002000941000017401c0303202d80308080320511201c1c019650000c154240e00d50500c2910785840c225070075404040c296801c040907460051600304415005445668005201e20409080c8100c001940c1c458142d0b2000640c846182000710f200410b0359000c600b54012045007254142007448060740c003540102910200190325403100a0360000000c0c510544103600410030b1800803004210500014010a030701075025130300c00d05030ba09200c0010200503005042848984081030f0055100343e00c0340121803507507511250040c4002000b0040c0c5a18801c401400714866030506000174068022042c0030810903440d1125400c0940081c4100161150440006c1502e843d01c0c110003001d075400f90140f00d0b980e5150101c0003030860064494078800414000398 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 948758507 1250 948757257 948757307
    0x1e1407021c0c14030316051603140919060e01080103050c0f01090306020d050106090b131707080601080307020414010602120d0608030304030315120b04080912030a0905040c0c0203031b0f10020c010507 88
    0x21100c40d04ad040321040740c1c20f01000400fa5950340d2400d8140d080c44490f448001c9503040c03500092080100b058614107214450b0018000980040350300c4124050903102841d8112203003004030340c2c1b00007a0703101070622880061110001000780c0c0040d41070b207560703445000706141d0b0380b0031101484c811106083c05c1044081420700481105806130700f001c01d604000c903101140c4900b00c05080c80030a0380701c0d0290b540001015000c6040c1030042405511070030042003555031414a000c0d49600d044080342c000e0b4a40010442c41d00c074201d9110001402c0d000702180e03200c0c0f4083c50054020901101c1070074007503482e2540054103007484d1002c2024a54001c00405c202c0c0c5130380d80c540145400a422181d0311020140311822803c0301080a01460038030717039613005081480c110030300040f40d40310710002040240301c4515101503207000085960801c6005243e00710f00031114041c80c00c01d48080007429890041400c40070a42c3c14076000383c08092107440080110b0384560b481a203101c002e00d800031507581c403c130b06 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 948759757 1250 948758507 948758513
    0x1c0b010e1509010e0f130b190f090506030319120509030a0905190e0f04060501050103140f0601030608031303060f0b0f150d1e1407021c0c140303160516 67
    0x851031801d0f6501030141c0b0000b0782584002001140e4841b4100c400310781da255070031441e25000c01c0701d82c0010b204903000c00c0603d0800705c00398508802d0f400f5812030385440310081801628100202c90075403000729100700502540180c01001e0030b82903800818614100b1010401000001c0100d9110090b143c5070f480701c035468401800309504410bc02d160300c561111030b00180f03010700260307100c1c030a4002d0b1a684ca038901d460301d03107102126010b80000303040510b4455460100d01000b130b525a082210f4150401055990000482c0505441d0304940000d010105211500c18950101035003039074480c0c90103210103c1a03102500850390035481c3c56500c41c08603500991a4100074140e811080200c0784e00320b1a0201301d6240c0c0080d2440b440c1d0102140081e44c017684143c00d098030130107010040f1040f10021a0414900c000c1d030702c807004040014030511100d282c00d481c0d03018100607120b03503501c2510004001e80d5164019107980048506400005d032503181c8042403442041142c101d081800c4038540c461100361 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 948761007 1250 948759757 948759767
    0x507020f0d180f1401090e0f07210c0e130b0603010905041b080304032f0f0a0e190b010504181a04180516050a0312051c0b010e150901 59
    0x36a035100d410810b0940881c0180c41c1a030940d0103030036842e05043c940c46440000400811107540b0030401081320304140800d9014141710103400c110319161420b0001406030003840b46041c0d1400e480f10072480c1c2031b03584156031740003000b41c00f4001303040380c1200114058401d00c0382518680f004c041e40c400c2c0d040006201001d9554013154003d4010305192402000c000c0c00d0940d1105a500b009580d58000b040070000c01a8810728481591001036820880001c0840017961102a0810b03003031003665001d642c1d14081c1c640b074440b007000700250240c482d00c6040400704c000451404142c0c005a99003050703c3d5601c15402081220100c8100b0158800000703250034018004020301751411806c805100c1c00c1e0324a030b55650054100740c03103200950002c0c0080c1803400301d03c1d04030500c08449120240880800c040c0c0d4030b020408003101e030040940748001c1c5143e00300702c44c42d21441040c559803c1e0100c441b0298081d40340c0c800d2030f1208080c4c03129082081050200413043c4052490101a40c504102d8458294883c4c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 948762257 1250 948761007 948761027
    0x219050303270d0827010c0201030b040f020a03020c0f010501060516020a050d050d020705190b0d11210c1309090c051002011505040902031207030c0b18010507020f0d 73
    0x300d0007901c42140d100000751030741801500c240e07140340001c25050186016500e807109006910001c00021703071032001c006807101d690600d010703051541c0c8121a500750b80f5950850701000340100d10840d0344004000300a40207401c1140c3c04074042c0300d90008080a42014400c0c10705840040d00d0b000d081000c8800d6003c0c01180c044801c80c1c1014284100041c41d4540d03184035481240b2840103040c405200d03c10091614805500841c0700311003200740c900415400712010020343d5240301e01036a88280c507942c04c07400380a10694260a00b0300016410100811816040364400101030aa694079103c03005a00311500034038103511103041c0e03840820404030500c1d90119100e644100c0145040e15a41d50024039170603082d0301c40c20050303511005640c600c540074005950107010b048908110b0803c454002c01c1d5601015580610031040000300c2c5014580a4611940941e50040c11103203076182c20b2100002e040b5048000000d29800d04010440241c000700300d0004001400000700080c0c103141008075491030300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 948763507 1250 948762257 948762307
    0xf050f09091606030902011d010f030e030f0705250b0d0b1f030501261c02100615091205060f0a02090a0305010e07060206090d1d1207030219050303 65
    0x20060109689003102c108000281425240003a05007a030340005800808191040d211000041c11005d4440e81c00001440340309445107000911540b2000d109880c0d40310300050450b84000109038481008800152307514a401541183c0c80104510310318480d03031981d28040c00c112000f0511001248080380d51000b20241c2005291345101e504074580b900d4060101055800020385940060040d080f64044d0706802c02c41c04c9041c01260b0220840c401c0c4c131460124185560000c85491040b0524401c10505d080b2034030305a8101304190f40c45800c0d00c203c05180d100030012440e0601d0000b0301c17000c030898110796a0742180c0508404e0343c030b2510440c0000d80041010424540c2440078025545802211401640c42880000381901c001c0401514055084d403159017198007000070405e4550303001c2342c00c00d2410164100b520031a040740c040301580094880b41710707801c02880c10702e0410040700002c1080403a4025100c04912544440c9550303641c07100342c000c01c0e0301580208210f80600060032030000701400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 948764757 1250 948763507 948763513
    0xf061312090905071701150210090614010605030126100c02120706051812040e1009090b060406210209190e030a020d0903021c0204090c08010905070f050f0909 70
    0x2440300c00b0501107030300c00d440c0340c0e0010b00c146101d4640091280c0656015001546112268001125000b543c0301030074494818482d840fa0903000070002c06800208510907000074084503913844000040c413036042403144c0000c110f030125840b61808024a24495002e01d020043c2403020b101340422005004608020b00c2107125a6400c8004c3d5260f00740680905807091030081200d003005101e60a1442c21041540001d820102018014800717440890b8100e8a0640300d5000d0340c0c1d58600d0a030900c440503880b500e00c1c942480e500e20f08001b081c101d240d100c0c4000b00da0402125031a907003600d070181460210104002c3d4100000805450015041c0d40e000c10001000080c4450388501c140a0b0380140d981c102d201d0b0700c040380c030000180d0180310546101c0c0a43c50a081018030390f40002c0c69101c078692124400100701c04140d800d54131076801c20801340e5048081e1544040d0f84a40355402440001401e540501a114001c9a0702e080d0300d03c000101c1d03c0040c803401022110108001d040c60001d014600684 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 948766007 1250 948764757 948764759
    0x60a0c090317070c08030301060f030605060315090405070503150618060a0b0d1b020604120c0507030f030c0f0308100803120a020c0a061a0f060a14160209090607020f06131209 77
    0x40000c06c0114003034500b03581c59204945e192003000d0709941d40c0c0d0700001d00c00c0c4028000c02c004041c6111404044900486100c4032944490400034145038298108a406000c3c828610f01030b40b400710303030180c000c14043c1c1c0e034104101d91541003c0380101c1e040d00c000d544051031200400500000402505000c440c200d0005040b0a0780310303d4551004c501413a00002d078102500700000e000b14031020500c0340d407550514045200240c4c0e902500c62200d0300008001509a40c4c00800b850b108100700f8204075440503080452114500b4042c1011500321114004407040813400325000c0004000e9a148433244d144401450300e0703c80c00e0710b01035041904000654460503030058049200c40c060404a56105642001c1c02d0407180c06109031483c00e82d15090003142c0822411120725401080228072401e12136246840d4850813080c901e142c20070f100041e501004032020f006c00ca181c082901d46c05041260215103540c100b200f0703000d45483d000c54140e440d103c003910014010480c16072a8000c150110310b0011546 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 948767257 1250 948766007 948766019
    0xf120e150309070513090303050c040f0303030c0311030a0e060a09050c040908130605040806060105042403061a031e060d0b28090210030b0a091805030309060a0c090317070c 76
    0x507003011015845d9180c2d13030040c05041c3c06101c0c0c1078002c58a000040d290a007001c1f6160280700c0c2030704c030040800d80e07030b10042c8112500c203510003a809102c01020680d0381c1440c2903141e01412a4480e4520203000d144003180841007039100b102000c592210141c0604814541000000c14044906584050003040b500411805450f141c002400c00c54541c0c544036420100c4c0b4a00d0072400608890500400700420300c03605da03103650040100503421807070450200d1042c00842c06443c1c2c0c1ea0000c0000c0740000c0c1c15070107042140028610510322200290740c1e04900e1004100c980606031143c41d000340c01d41c000000410b010444055105c2001001c0100d5240c040945041c0c144a0803403402c4190782d80c2d0364030004c528049440d402d074a01c0b14a0144a400c0e9203c0c006031805000d40700304558030341c2d90790641c6950034140344d0041c4055000fa083c0c82c2c4901e004604640c48040445500660600d0580394445250087c2c10038002d0f0707a006611101d42680c04001d542c01540058800e40b00b0070280003000501c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 948768507 1250 948767257 948767269
    0xa032306070207030c0e060604150309051b13020f090904050312040b180d1202091507050d08010b0430020d0311101404060c0512040f120e1503090705 66
    0x24803000d0b80180005031443c1841311112204d60005a2054812028000e05950350f0043c2c0303090b40d110000b88a02e03480d00c54000d800400c904900101280507040c072031070510700310202000e01800f081d10303141d01520078107590104903c00c1c26040c190020090050313041e1800c001c551780707921074481e008a030314044005003010b000040803101128121420340400c03200030004020401a80c944e40300411240b15801e0008e0508036419004001d00356010409007455034844e0702c0c0c1c1048022030311060703980d5481428881e032103819912481022800d00000007501400754001c440c03c0b554800d412000694400203041031491110381107007001124801014090707a03a091850580c64440d40f01d103d00f00500c503200d0f5003010450b014204d41e0601d401e82400701b1032442015140d00c00e602000000705100202001c0d03d0701c3c0501796802d041e590100d0108801c1142d41c41d59030003514020501e203920790702d81227807c440301a1080c0c0ca59800000801d088590528104099600308801c40142c80c000f0361a000420070b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 948769757 1250 948768507 948768511
    0x902012001050406110a09270608030d150b03040f080c010f0b040c0c0b1302061e040602070918110f030318190302060a0c0602090406030303090308090c0a032306 71
    0x4001e0355558207000400c0000d1084e83c00c2e10090120b800d091960107440500308080c10300ca0b071114441c4907040690710712940c00d003580d0100703c04c1da820422941c481c003c40340d5a070003402c2c2000d250b80c50310040c04003417101c0f075080746c2c01c07100300a60541c43c50383d442c0d60380c40c140d8070401d104403141c00c01804140d510030028001c1c01040e6041c5100040c00c00740e00010002900c5100111106018040064801042180109503808600e51300003100c10400f9101051a81c41612180441c2000c0482100504a605402042200c4145c0d08031540300341c031084c4d0502222502210510b18424032518100051070409007502246002030a5600c00550700c00406d080d944400d40080720003a0040352030005190450303041e5071106070301e080309404600316404500d091050044400900805450340070401400d03030101c54038078501a00c1801025660318002c0c002e031040c000201d0105120f40c1c0000ca5410000442404110b40103010402c642e155441d5007445184405c0e003445248101c0200048c0181c2c1002218 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 948771007 1250 948769757 948769817
    0x507060c02060411040e1002090303070204020304140c01030240060e090f010b0909090106030c0f03052506140f030f091204030302030a05031e07050c0f03030613090201 74
    0x111490249020302100c05107a6406100c3da01c0c00c60018082c1ba40080d0344100310100700c6005079104c160000282c618029014001e60041c00002000100450164807405104510080b00d80d800d802d400150180e02600003540c501c1e8151514940341001c00070a0030301c4c0b042c492000d0f00012011201d0240c598461a08080c020945031142c0320040d04040150fa948040480382650a6505111940c40c0d9032203580750b018032502c103660100c1c6030501c003903002074011a4888504050309644400d81401d80d0300520084c2c3d40c50003002406030a40305a5401183c0c1c0d0031341e104030002c0396410041b060364501d001580304412a6028860f20180c88000b0300154003c0e0713a008a000e02c00d03c0e01022513854216404540f20a080702400704100107500001520000b0b1542e09165803250f8a240c1c581d14038074050b100d10281e11000005004006800100030500d45074480d00f07817504002c400403425503d110a48940e42c118030140c0d250745548a5540c00507603e0703841450302d048440d04c0043c010300c02c450b502e1490 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 948772257 1250 948771007 948771013
    0x70b040312060306060510030605060307050f2104060e010c0e01081003150b150a12020715021602100e010c060e030c100f0f050105010c020904031b03020c0411070f11010507060c02 79
    0x2440140340c47e4140725035021440c60180582c50424000c40c0302d031b010107041e0300c0920002080402d2050307006070994170484250342c40003068403102d40f2103a8210b141940c007070300c80604d004007001011006000c0c6000150080c1c80301030f11a400350340111a02040200744c03006000080c1804000907451070303409094800800e80100781d862845082040301d007c2082e5524010304100200030081c0d8000c11943c0c02c0c1d11303103010016201d403584d0038688100001c503401055041d2001441108203841030318845401d034025158040007075070030082910301c617086540e0b81b0301050b403000000c40042d565400000300869400180e0341003404000e1154980114210614031403a04d590078959022031620606101a03038419050100c0d501d0080040e1540e81d0b10500039008124040004003403501900c090000d80c20300c410543c1607102d590070001c0d00c60a41c5682c0901c6942003080794409422083c0540d08025004144003500a001d0307610201d07206a14507401c1d0500c90b0a018020228000c2d1181e0b070780041d699005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 948773507 1250 948772257 948772259
    0xa050603191502041410050a08010b0919180e01020a09091a030a0b01170712140f03161b0b0327070608010e0f0712150302121c0e0303070b04031206030606 68
    0x104070000030100001d104007d0140f1400c0c18056024444030f0444075000c0c4031543d41d1030810003049034500d000340c0241c0076203c12200081c44458202c00114209415681046440301c101c00c03540c00d030710035100444002841040c081c085400c541d888860800545031507011360251140c0481e042c050255815140620000c004005003107003030400110160600026000050805044544508043c038001d8040f1007185248204500100400040054404100e0341c0700c0d0400d08008409001c40e1404441544050050207600020781d0344030015a4a2048032501716510400b01c902202480e15840a84000091603400c0c850814400c900152140703503030307400b05581000b5445541440113452050400e10003020000483d51124100e900114245004a00300442c042e4010030140c80703403c003075480203905900314800500003c0042200000152880328060345003000e4030b1062074100707000d426030010000350000881c3e0700c203200c1d8028882d0030b05c1205040c91640d40f5084402c1904126101903855078 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 948774757 1250 948773507 948773509
    0x190b0d032007030c0b070318090b03011d1b1504080d08060d0302060f0c040b0c01020703020c0a031703100e0702072d0e07020703020d0c0501080a0506031915020414 72
    0x1121061031503454005003819880c513904e0007074400781403050040c04600803410004151168000f0110b19442403100e40d0500d8840214400500b0603a0550b84650310701151040c40c090391103000081e140e8180d002d407610380811031100901029010716981c1c081080c400c080b1421048001900c09041c4100052115844048020300380e907074082c01c0940b09001c00c2d142c100000380d0010701c190340814111410251929003c4d01c1030001e015540046421745004a5900458001507014001450107603003101c801d5041c840c00d01c00d41d082c041c0005403600c000c0340c031086094503104004680103500d02c01803501095443c0b0288003405030a0f0b41d070790010b0f08a290100f1118600d1144005101450b8001107901d0201426030140310b0040e104880c0d075403151400080c2018003d000c200c00954002d42125500f01403491300c20007040c114000c80380440d00031b0010403070000c0c480c401d10b8031546002d00204031408144521001a00c0500001c8a03000c140500c070180300f00c103e002901c001d1903225010207003d94400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 948776007 1250 948774757 948774797
    0x1209071d04030801050d020d02010e030c041a030d0509010f0c0c0308031807050f1c14150414030a05040b0310051c030206061c0308130245190b0d03 65
    0xa4005c030b22420440c2501c0d00503035210321980b41695424200700343c41c800c05601090034500d8506101d98014034014140b50040c00040000b801694201c0a40c0c0002d40781560680d170764010400100d000460403910044020f020329604114280102041141c0340d40d00d6484104a500c100c607094082e41842c041c508080404008802c0604000c0f03c16142c540a0308c000b10714002403020402503008070402403d41407141008214020003102d00984018cc0e001c002c82400380e000540d01142c00291480c0002c4084101000b640d0301281c9980d07030946413614000c481601c0313420240501048000b049000900c513642c089080e40c44543c1d01c03606008c40e0000742006401e00034010801402400c3c800d80d68600c18007050001181264581040b022548030501150b801c0c8150f0070340207401c140c0da050240c61041c001c0030000020020000d812282c4120600800b244001110342c165404025401091480000340544e0014040102c03001917050035180c0021150481004c007a80401d415800110711b2602c51 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 948777257 1250 948776007 948776009
    0x1e153f080f0f040839040b091602060f0f04200a08010e01060801052502100203090307120507120f0c0501180c1a04090c030b0402030a1b0c081209071d04030801 70
    0x14018200210348091701d4018082c000101c10300001050071800b101d5681e483c1c0c00004091000f034003555451800b05c0381d403010310b4003d0a010000d0b01c2080001051680104255031280011404102e0b003902c42d80c1e10184084030740a8005e08103010108503d02e43d813100814400100031500010401200c5071551600f1903000f41c01044860f410181000384910b0381140c0384d0240090f5004200002041210890404000312905001d80b400081404521030000000d401d0035806811020008201e0403400d685520401c2802440b40b0848201c136000c2d1401640d2914114100e41403000c000266a501c2500b101c03041e1443c1e1003ca031404600300c05004100304904068540840d401c00000e0301090b180c00303280110b1146141d202d031201e0100107882d00c6900400e1100ca0302900c19512420700c3c1d080240034140841d411440d6900d0300c580d020a0a20515000b42600d4201014604d01040d24200386111070000746017100c28420400d000403042502c0b0310101020f0313a01508070384541064503008080c0001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 948778507 1250 948777257 948777283
    0x519020a151802100c020a0f051008040b06011d0d06062405070b060a0302180601030c051809060d0f030f02060114131e153f080f0f0408 60
    0xe02640e0b580a2050300d01c2001e0100d03011501d600d80125131035011111011090402500017610160000c4c0040031050201c05450049990002c150792480b81120225400c5501900c5c90b1076031004594594007030002c400c0c203121102c001c0c5c600c40c00d50754045a041441400100c6120b6691141013180b100c852030340c85221040b10303c80c108104d000c41402000341c01000e40c00340a0030301c0140440c64940c1c0c2c1e191200c00441c0d02800e80564103406609c22946841e007101e140d80480e081040c24440d0600c90821100000c900301c1d011540a800c00341401082a801800c40e5000034250604502069949e20540c0049100b0b5503055010122a400281040c030184d00a00b01d00007002a0b0305a03030382d50b086245210900d401c40c0021400440c000410600702d08d03040040c0c0480c80c06913241c580304a100956001e6448034850303102c503008807001c2e0b020f02e0010301d001e203d000010300d8540c3da4510650750703540030310310300850300c160805448184088203640012103048403100300283c10032403080140200041100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 948779757 1250 948778507 948778511
    0x70b0603061501140c0d03020405131e1a060d0c0914060301031e02120f011d030313030210020301060c031209030e100216230901060e0d02010519020a15 67
    0x10030b410541c000d4840500742078140003801c204079401d1001c140642e03022540001c00c46000d529116030142c003e501c44e016090142800d030426140c41781c1e080c00b07101403c00a210350710b000f0903540c949080c0202010640034490001b4242400d14903501c82d00981280e007d0a4000140180c203620042d080f652190700c41c0e540c40140342c1030448165500000d4904494004600c04459596001d80610084010b8002940030001200598500c1d07800a07402c0c07041d080020080003060000c80c800e01010840104540f6158020000510320385d10201c90204014407070300441e20b0a8100356540c40c2660400d8100c80c001402917103450040c140d0090304814a00300d000820004841c041c0c8005080600390030101d402002c400034800151403003027003860b028202000c021007070140c84011140107145440d03942c0000300d1010360030303001e0791401c50303100740c101c400e00d0b151030804000480a000480d02c0540d005e03418000305000c0c09804401e0030311254180380480d4054100da035407516005240406c0c480340c020b100340c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 948781007 1250 948779757 948779761
    0xc09060e0405030304030804020f10180b070f261206030c040b0d0b0c0904020414030706172202041103190c1d04020435010506010804150603060501060203070b060306 73
    0x12004030840c1e401ca505440c00304ca01e69a17a0004c00c03a48ac00c0c451140fa04502c1c43c104030800340381c0c09298104840640480000320690b2203041e00343c14003e403c0c01030005a204482040000e84c80300b055120f6410014128030380341c0307000181c1c04907a00519002644500480c0030818549414065168408400c0307404004441c0f40001151598102d20b4000704400107020228454000c0a0281c0e1001c140041c0190341c0d4a4403000e41151400748084114080d02c00c407030020402500a003c941603405441004540715a24428606445a04e0100d440115207404450740c0151716a40503020544440d0f19200c0d60780d0500440402118168241d002e46551415140c4c84e6115401355801d01130040031044022030040020024000b80311795482501c103502c403000007605040c240d01d550100315072034031460001854015501400c0c2c940466090340000d200760001400070300044400c628514680c5000201e107520307542c50300d080b90800e810400150b400400c1d86030800c0300081195a00007001c6e00504054 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 948782257 1250 948781007 948781013
    0x1170a060e180d050721141902060f01051014070206270a0806010902091f02060105030d090602070b071a100f05120703060c050c1203070908160501030b0105160c09060e04 75
    0x1145c24480b925444e804103c0000d449210b1004518a60722403160643d480303840790070b07440b000100302c42c100e00580100303000903041c44502e2f8501f50481d07030f000e01590308821042c1011906005c8992054003040300a1050201603103411005d4480d85041244c0018444940714141c0d40c0c0d4420141d0151184490321014051f00002007030785411501e0049001d40c070f50f40c004001500800e0107046021030524225001d400c0e19a0010341c0034121801501038900c1d02185c05411030301c04080780103090146c1d01540b070400600c410f01e4001e0241c1401403200b184040016400c0d4008170209949100c00004000c46c20b1094250500d40340c0c00901c41180c4100341101c810000307a44840780351001030701c09903643c1c0000c0360040c0110704407450072154005890400401704ca40300c01c04e800542c2e080001891a280108800f800002e69981d881100c00001a4003841d1500440240171a443c005040040074002c01d01e40c80c20b030901c40b0684130700c03d051070304031181040c01000488100fa405214800140380520002c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 948783507 1250 948782257 948782273
    0x21e09010c03030b03030904050907061710150905091609120218060406030803090a0b0a14040b10180e1203040c0303081e0f16030b01170a060e180d0507 67
    0x71641e01d400c0226000d00c09000103030450140c105115081341c101410003801c4c20000c40d20800750740307558131003900140b41e80c041c3c002e80c040c0c116000105030703030b0074003051182c0b01a01c0241e0510202d1482e004d1285521070000c161208800d84c3c0440c0e13015003072780150450a0f00910000b0240c914980140701c601e5058002a03583e0100e8030701000b51200180c0469203030344464001034041c40d0040703d1781d41d40c2d08050700c080c2da4406590754251807110820001c152103000310f018a2020720310483c004881034a0310f4548104e000702c042c08554016840140000e0748c44c4515900003807107600c0a02c002058034010b8140741c00c04907003601402860100b0820800040c203031207020801d4a1f010b140082d919510300c21209425141218220107502286040000c0109140510b49c030441d1000e0819144041011040c1c050755003511266011404507036140055910b8030103080d6216480b800c01140d030742c2d51518109141501070302c10b484c0d80e034522154030722495802c1103502c2c42c9261a107885480d001d0542c940d456 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 948784757 1250 948783507 948783527
    0x50f0c090c071709060c101103060a03030f030902090736061b0b011404180b0c1315020a02030d05031b070501140c03180a0203122209021e0901 63
    0x2e0680c85868502c03c2c0560704050310001e00000d04501d59070384452101550b12100c2c440d038420102d0030651408080300f040ea06603030060740c0c058442e42500d42990380541d840f0017882c1e50a020155111b0500c2c0250382c4440c0380030301500c61622a041e0f0000005c503100110002640a0541d0050440014984198510120085913114600721980e9108034024500d801c20050005d040c2280d164000300c3c0d44034822000d00003450044800b08240d41242d20080682c075071120000d800b24100c60002a94004540000d00540c01d55144070000d058a4121950604c000c4001e010010382c0000c0074201142002c02072003030100503500f45981580751800d00c0314a072581407015265004000b00c1e40c8802c001c1c00350008501841099407510131440c000c9844d00e17468008440716030020005540070240e540c0d000c01c070300741c4035074000c1c0161200010030b071083d0006922a80b0301000b5109494a41d00b054010500244041c2c2030201005d40d50303865901d450107a0380800350002e00740c0b40c820000c100d00d90380c0000401c8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 948786007 1250 948784757 948784763
    0x70c031103160801020405010e030f060a1805030c0102070203011104120f23101107080315030a0f060b01020d0306050d0224211003080711031009050f0c090c07 70
    0x4001503148000c68103094010341e01c580301680800c0c001c10300500640150042e2002a80ea030214041d80c0310030103a50740360103802108a5041300c000300302d82099640000e060450302540d031701d0f2884c0543d9181c44c916807203003000851a960104002046103003c1c000c4c001d110348480656400d00b4140b00813000802e011900007044100a00100820008107810645403082003400340d201058a01c00b00d2500c1d03072204205200601e1070803146211460a09081e10455a002040b05046a40e01065034104010b0a16881d0f81803243d41607100014403000e4440d0310700ca2260301e01049090741c00c0d00292404a6183e03001c4107040c2012414006602c40d1103040e0a0190101e801d4010b551700d42011200000c8250b0740c80c1310f0300000040c256103508515040400c19041d402480b6a01d90703c0a41d821f0440346103002c0140f14a10070404000401c0b2100d25069010000400342e43d600c040704500d80c4106c40d42c41c50f0440e040d40203a001d408214800b401050503050080c0e03043c14691030b20022812062103101c00c02 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 948787257 1250 948786007 948786023
    0x3150504021f020109080c01091214091c0605160801090b010807030f060320180c03010308070c08030a030f0515030d03022503112125020405040c0603060803070c03 72
    0x360030742c80d1007500448156900000f000da03440403440d80360343c0a008012415900c0078904140303038030b1507481100300300c28500d01090b00c60308245401080100408440d654982040048008500481d006106090044403200c14003043d01003140c40180401c00142d200b0300002c0d00d0510201c41590300450000d6201a052030001609802c44a80e00001c220940010b0303c4402400c010740c81805c00d051110240000484444101d0481d01c403070300c030300007004603905050780e40d05000420000303c07036602804090707204200703081d1220340342c0213071174515000510340d0800070b6211b040705001c1d20700900c91507402c580c200389201076401040011a94600c1d03800c080314209030740003441203070313540744414034a020902d45104854030010a00380140f0b0641e602142844c0d600895000d4206036680f00601c071a000c0040150314200008004000300c0307925801442c85410a448843c940140d0755032207441e10441c440d0101c00e01c1e05e4142800201215804d4203d01c045ea030080210350b0208042c55811400ca83c0d0103007038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 948788507 1250 948787257 948787309
    0x90906040f0e0106030501020c0f06010302031e1005131101050a09050118350601150f0905090a0e070501170415060b07030507060b10051e0915040315050402 69
    0x1001c1c0240701180502159503e4440b01004006042d002044101c602c2c00458000c0710035a1110780e1100c10a22000b0340c194806000b105100c2c0c151200440c516001002f039441000314a038000341962411644800c815121415010030480211402041c000d820f182503410704103040c001901c02401030082c036060088400c6000015000385010b84080d04c1d55045924412075055030400e04028540564140b4888043d01d0a80803600003030340d141201e240f07024010740107207030b120191f641c02c14444a490400c080301c000840e068a80140c414020300c400c000c0000e0b03202e4035200e0035041c030805400250400001030611001c40180005240e0865040002652a8030020b140003000381030b554000e46010202290030300502d0703003001c041e0040c140900c800b4800b009441c1c3c108a95010480d01c000003007881845803490250b485140e00f440c01212101e45458508400e0001d83c03d100d035000304503209075001906000300080c403c0c0b0b0120186074040244103a09056000840b03000c1c54501c4c5083d00d12000e50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 948789757 1250 948788507 948788531
    0xe01170c180406151706040209010903030809101e050c04060c11060c0a0b10091811031f09050114010305030f0310120f21020d030e070b130609060509090604 69
    0x10080c030050030300c0c490348110300340d00d030f8001707400c520300074605083c005030010006e089400d16000b1102014016903c051665045036420303a92000c0203845d540c4139105440d41c1c03134001c810387e10501031080f81c00c00400c1c000031b4620088506071500109500311144052100304100da03000150004003991054180001c0880c0304003040f0740740a0040507403024031500004c2c05c10f00480401c118061080f80d106a082c558072450303d80203594400d440c80707504e41099140c0c9400302c4e442a1051b80c004800400390b0304079160601e0303640d01c070b20007410b00d2484080e5502502400c004c070074403614030030020340700c1e1311041036240d91605501c0b0301603000c0d06e8208070400000284445180b0030818080e01208201c07008950f041e00340000000c00c0c050040722000320750b0a540c0400c0302900381c80b80c403030305041e070042c0149a401032040b0050654882d407400e65104987c800304080313541001074155a00c0d1400c0ba0b182c1c83d854a480184401046e600203000d00c6020480e00059403101d062080e40108140ca011640104480c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 948791007 1250 948789757 948789761
    0xc02030c1212030705070309061707030509210912010e1903090b0a02100506031f0c090513051608190b06190c03180b0412210e01170c1804 61
    0x1242c00e6407400400801c01020740c1d08140940712041c041d5940e004407540700d01c1e003079401c01503860540c241c00d030346080061041840703038000b1640032040405607400000344404424540125155165071000301140e02481401c4c05502c02c018421480700900001c4000c0042c1d40d19164420041c100d04044082c4180505001d5003444000305081c0b10b00300c2c0d55030b403162802511340b641001080401418940400c0307480c40c0001d18002c075151001107501c200d07070081860380e008100b002c2c0e050007844040340303001030380d41c3c1ea10202035000e1035040c0012409290005c040c1200744100c40c225000d00c000b00c401e100904d400210482c0399111084d80000c0c44c83c0350140010010300501e0f0b101124090341070031907a0016070003200500e00c00d10944400c0070011000c5518207203068940500c06410713400340410407003600d0070b07100f2440b140c3c002d0300300300185102400380ca198411407500510120f04024804042540d101064000841403080d01403228180351030150080e1080140c00e01e082c00016881c03c11550340d903 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 948792257 1250 948791007 948791023
    0x9180c09210c030f0606090b5505030601030b040b04050a12170109020a021f0626060c0f161506080c04050c09010509060f12010f08010c0c02030c12 65
    0x4100c0079980c1d9032032034081c6071135104900c1280d010f800e080700003c008060340a08004400014a9a01100b50f008040e80075504103100280c0c0c410240b03d01500904046581000041c00c00a0403c20090702d0744812800d1180c158032003400fa0388504010404101221042a01b00e6480500e404050319541000d40c80d00450360400f0f031000006082c1d40e0350594204480c8046950030a844d0540b582c0c2c0c8034036040481c01000d46200158006101d0070420b054a1000031010034518900090300315191014400c052551a1002c003440c0e0410751124446031040040740d91051025000c2444e00080c21002d902d18010f20311400d00300c80300c61719440304004203101c500342d4a9002641c2040056501d0913800c1c5d40700081c10009000364130304804a180180f07004100da0b10100180c580e20319001c004d034103011866000c100700c410392b184280982d180c000c1001007507074000d00c1605e0b2211070660038400b11034211030700340c0e110f5418040410700e8031006803008680b502000c8811900a014900e007080d5141c00d14080c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 948793507 1250 948792257 948792263
    0x5160f06110102073003152907080a1704020d0809011e0806210703080a050d020403050706030b1f0f020c0d05011407050c030405100c021009180c0921 66
    0x415400781c10401038001c005c2d00c1100d8a050000d00d213103400081902165070514244041c50b1859805000d07a140c4c900016141217201c034005040848404047c041941241304101c540b0500003400101c620352207078010661000040842050b03081560002d900d90752603000007080c5910214201c02140c0c06419074812250100341101c8590003100c00c02040c0c440202c4502d4807540803c500070030401c0000340d10140100d90704000306881410b50300c0d444150b42204031001c040040030440c221021101e400a44000c5104034000c1407110f0500c000a03060710b1aa0700d10a002c1c1031003000d603030050707086510300b03d00c1c070103e40c00d000740395441c2c5860490400e07807408141500502e902c0844c1c000c0140540c81450640701880720031059440b0130300200c1d203600c101d4003140196403041c8002c4c4a24608424400f1a409150621282001d0154081185101c010018802090f40c40f90104140024403400300f6001e49050350800c511400303244058507111240c041c07035080380500e08102c607201d07031100590f8003c035030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 948794757 1250 948793507 948793523
    0x7061a060307030b030f0111030f15031f0c08070f120f020c1e01050c18060d0c021011040b2a0a0803040327030201050319150305160f0611010207 64
    0x6080b4030080c01801d48003e01c14004d20400c250064110810301c51503000c0d074942c0340388a296481c3d1a03001c0300c0c19180505402d0f040ca6525166880f90b43e0304200c0d094610603003038080c41c9813000090300c4204441d281010b40c400c1c1b140f00e03001c00100d07981c410441e203007508040c10304032111081c180e0400300605107000305400351440000d6504050200080744540f82614812004e000c42e254135086090310030a840c031041c880e900380302c003644000c0c0a0303051b80c5c10248042e1031a410103029980e0780040c1c504110f03c05002d44c200403d0320054002c20301640c1101910611054030346032a010750b05415200d0303d02d900034680e241c0607103403050280c18000001c541c42524225200001a4101402c199009507021404140221000501503a481d03410070120750130781e100400400d1a41d00159041d62008000d100040045d4884144080c00c910404020540c0b1950180c00c46c2d0440c6041441c00c1e202281e15101d00c0c1d8600f10030040c01c1c92001d14901a20780d5854040780100c900c00c040b501a00441c400102490 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 948796007 1250 948794757 948794761
    0x50912040e09070906174c050708090d020a02090c1c06060f0206011202060412030e040c02010516051206211c0311160b07021e0a02091b07061a0603 65
    0xc105d4030344c1c4006044211068808135220009410b2440f25001d44111941d1072503c607500c0d421f045200c80c10704c42c245103407818501b001c0e5000702204071482214100c010400b80410701008a0080100b003282c14001e0004204640c440e4001a94510008001040c2348a0024001c1503201c0380551103400310140c11005e114454440d60040c1c00c0804007103011005100b04400001c07035038120884081a540c0181c10640303801d00309800b180d0708054111041d8148a00c50210445940300c03403241300a03c6442e50300018680c00c0200c1030040402d142c080c0c840c00c102c0c3c01d103c048501581c02d034540d034202170111454800051036070607d84032000100c1123410b00f40505c1d09410004086410034141b4444581d8082280988806c1c4003075050040022106511080309014070000340326405041d089145801240c0402c0c191000303824501e4025042110540c1194582c0c030b046003440307d590303a00446031280c1c45150410318642c2c0042402400c1e0040c0010f82c440180108502d40880288140c1601400107942d80c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 948797257 1250 948796007 948796019
    0xf090c030a061b0f1b020a0308120103020102070504140f04030e0901061101053409050a0603090218160c0f0b0903031b090a060e06040807030f0303050912040e09070906 74
    0x1e09000303c0b522948201039852070302081c41540501d8000c1841c3d2903001c21820140704980701c0ca10f0111040340c00000402003c804142d800303010f00850348012000442a40c118800241440703010b600c801c2c0514101000700480c0108a14490351140342c0c0008902295100d05040300c07810701040416030032140510001c10072950116100c1c0d02c0c8401d010084c45261600314090701c1491001c4a114001015440c040100311a080e800c84480642c43c41c00c1d485884d16600010030015056002e0400300381d95900d50421400c2480b21940e0752120000781c01c00500d4200c1240c2d0f40704940c00c05120800610701c08031001c000c01b509104001c0364200703401f41100d2404000e4181e03030342e00030740b255524032913061084004408103008480da680c02c0580105880ca00d0120190707140607081c424668444001c5c0000b1445000401c1070034001e40c01a4085081500c050501908980303020303050050941000042c100d410445c07101321000c03140401002c0c410b07039465441d01d90804800b43c100781c9080341008000121 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 948798507 1250 948797257 948797261
    0x20a0f02031e0d0902040e16050a050607060c1e09061202031605030406090606030b090c031c0309080c0604051f06060f0c0501090204240b0c070909020303070506130c0b09090f090c030a06 82
    0x200702c0788c0340c00e510009480d0b5082000b1207105c0c0c03080c0c6074810410084c482c00109650805a520046420110000b0340380082214080189032860030000d0000b42c030400500754829814001c07000031600440c81c41c01c1146001c2203061003081d00c0004e00030004045000c00445900c0841c40d03d0b00440b04200c070648910b41032a14050982d400b002034030400c1c208006514000c9405451300c44403000c80c02d102e0811103800c0d4041d103050f030000e8070005c1051011a500350410311205129510490191000c40d00000380c40c4203a54405d66014503035440d10f003061103a80c3c2c2040102041c00c249080c02c14030b650b80303407802502405210b003000303404c1030a2141d1b10203820005580703c2c0c1c040b17550312400c014494840b03007130071003078065812054000e0b40804820070100751a544500035a6001078281c0b45044015201c0303901e4450241c50001d004a200171400d010300074080300c075401808948040078a0100264005a4401000b41c0505c1c0d00c10b2805c4045900a40100f1071302901050180aa8500d07036120306001e40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 948799757 1250 948798507 948798523
    0x140d0207050114010509100e06030f100b03061006080604090638030c0307050907050c0f070503070609121106190e04151805070201020d0f020a0f02031e0d0902040e 72
    0x2c070008400001708461802c90840341c403c8600405e202000d42c6860130402200e1009000e00390180074280840d81070740c9091010700c070004030706800420080a0305003858a403000082c40507070130301c408003001e104050340070700e1182e0000012200405c5400250800d10001c00e0f200b6001d070000002c4007004120310110002c0004108101e20060007100c1c1100141a10350160b40303140c5034980c02c610b00910140c0743c410146a0040c2592174280d0500b10004c076101c3c545449900300008580c8012801c106a11302040824080c02e800c0c6008002c1514003003401e80c50000e80c441c0106403212000842555403155803d498044150000100c8904c00041000d000802c070801224000c070b082807010400040c084c00c82c0001c882111202c160300420800d618001064091b0082d000c40d5000c00600f40101c03000e01a1110715030180300c00603030301d480c2494044d04505240c140c1200b55001441040030310b92501074500000c2c40310207003240e0340d500d40d025000010101001e0080d4440d19040706041d2141000134294 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 948801007 1250 948799757 948799781
    0xb0a080708150607031b06020304031701240302070201022b0305010806070206040f0c050301060312180b0a1202042102030f1b040209011b050d02150412140d02070501 73
    0x140007a1154440c02030ba42c02ca1008507900030f002000814002445803114507403c05e40c55280741654005a07941405980c000d80e4150006903080c06100200075240c10141e0042c00203140140712001c200c900320080c542151b01c40018568041203540c1564001c0c80303210410742001c0300b8841a0340c603e0068402040403508104002450300340041030b107080000762540100c0181e00105032940d2555500d60072092010021510014000c00008007a142401140065031060b04000696005140014800341d020b0300346900842c480d15040005082c2007007104e601c29440d283c00d240700d29209000308041d125941c050744050003001c1305030410800c01c40d2480c15061080382510b13038201d50895000e940340d0f801208800c420710b880e04801c1b124a8154014030f21200e060509541d194020900306051a00e8000c003a9a41d4000c0c07015001c14a90611823404a140140b0b04249181410740315490354048804a000502c10b0b0300c2c8008260068240a50300381800480096640d03810b24a0000e01901e0003080309 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 948802257 1250 948801007 948801017
    0xb10210504050616170f060a080303040609440c0f03031501020f06130f021c06050a0c080406020a14190905040513020f3601050111150603070b0a0807 66
    0x403130302e0703031149a401452800150030004261034168000035466030203800161b005102d031000080295040c00610310450003144000394004107410080300007001d0a0710702031628034118004139044160540e03440a1944c26020b0300e41035041c40d0000a0621a16041c03041510810014042482d000001184140090302030f440d1606c8080005a036248489500040f01e1b81110b800120842034a14a4542490094007034400030107007500172440d141038181c0304428201900e091002401000d029a07078102d440078404000203402d04400801082e4040c01c000e00c81d80e000246e0114040c452442c02c07410342d1000300c0030f613611451440b00f0034440c100705444c00c01150b00064002828909480307a9442681070b58404c181c20007403a8204400c5200e041d94070751b440b00c04004000d045452080810002c0040c814508400900862100e40444016484907040000400200080d44004901410101c14882e1007c800e40c075a00300180c1031200c40e42103203a1802c004500c44400560004005006003225112 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 948803507 1250 948802257 948802291
    0x4140c030304140307080319080405031303030f080135070e18010e03030c09040f1514040f06050d020603100312051b0f0705100201110409140106030b102105040506 72
    0x1b60a0301c074000c0e4038007452200c7c0c0c015121071340d09000300d502c694802c2c4240b05503071900d407400700c602440d442d00381c0007500081c3c01c070000504130540002e001405445440c4000c05011000d5090081c2c41d03520b003a10f075800c2405908210b4000400b040400042d1010038221800c52802210f03882d5510800001400c1a41c02d0a004003009000442168011125150319502c0e054512040c0006400b03034500f000300051340c44841c0088a4260440c50000c0c00c04003003145508c4480c3da04200c1a952040720f80c01c0b481c0d10300401044140d0310f40b844900c0603681694481c4e12070341c4810300b9061241c22540081c00c1c0d0f69a01103210324041d48000240b0020246428441d041400070021998501076040242a43d9010307800c10322441c034154145030315600d203520010807441e20728107120245401c00e501c841491a116a4030040100c0246103144c05440545800c101c0500754a000a03140304500c1441410301080769a4050800925201c00308070b10075045040c4801e0403c1d2400660700c88045450300c1e117021080c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 948804757 1250 948803507 948803519
    0x804050909280c03170c1002031e090601060305040c030b04060c030f0b150c0c060d1d0a08030c0f041d040c0605070312022503031b05070b04140c030304140307 70
    0x140714540c00f41c1001501c5402401c607074415041c0b1212601d0302403421801d00400d00c0c803204c2086207420014101c00301680f2030034030728101c0c0c00c0d15605401003450b1500070f100b0895020700004055046444030303d408205501d4070f042c07814000c0800e0300043c124588a2081100344003041e000340b0001c0c4070660301080420880300010041f654180c0101d680400007404890001031180050078801c40018103940104000100142103988600744910382e50b5103484844402c1c800f82c00440e800640300c03001606503a000c56490b4402844020042c03810791001240140c0d1048910342507801601c0e81045011181040e42d400d0f0031048400c03a0201c4c0c400703010080c017050703240c03040094955941e07054a071500b0030354a548056010b900040403190f890400301d81004c80c2440b011140e03024441c002c6c0c03000210f00940c103400418181131065014207200b002c05c0f4140014042e0045a54000d070000d429000903420449e10b0350030070a960b0701c03499142c44041004078501540d04a110285d840840441fa40030340e441d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 948806007 1250 948804757 948804823
    0xf01030206160201090503070620011104061b0b07030e1b030a0b0a09050703030f020c0405071e020a02041505010210181b050916030b030109050709090804050909 71
    0x10000075081002400740c18a03604038035002a00b0075105040c05104107407100e01103840c1c44816840300c03000070b0002440300700000142040381c1c01483c209000388601007801340e07070b051a841030384a070744100030f036450824402c0b014023070b0394400c881d901c240304070403a0030b1655000380600054650905c407400b8050382a41049116801c0b01c0c80400098083c1c04590f44640b140203010800408544171551203240b20f4000075428001d01002d18840c3c0c5890955503c0710340003d00d03100c001c03103540780514901818442c2c0540c101507000103031800040b50307240d11500b10304124100b0302c035540025080760070282c608100b2091300c0d003100c2c103403542a42120b04400401c1d89640c1942c0c0d42c0109600c200b0759290228001ca5641c61002c000132160080c5a818a5542c0c00400d102c060202c442454035001c200d140141d0642c03501801005000407802404080b01a895241c4c075181c50f441a050201c3d9100d505804001400081e0350003004c004210380114600318160586a6440812481c08619001011601c10100d9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 948807257 1250 948806007 948806009
    0x2180603060c0d110f13081914030d1d0c0406140d020604030f0f2a0e0a0b0a0f05032806021b0a06060302010f170a090204090506040b010e0f01 63
    0x240100744503241c42003406400c2e4040c8095902c0140c48001c882c95071040b03007000704640341d1541103840e84c410948410104540342500b086003150013004d104d001e403101030880c105c500d503007000d20100107040a0094520f54443d4070030504200741400c4d01000d64024200c00c120300a201c01042d10f011102c110f04020480d15140214210020351111954480c141105490107461000d400586025140d80ba04000c0b444440e20841d29540c10001200812092010300700b8100ea050f01100c2c0240b4039245101d010200368042d102d0540000740c000340402542d604030582c0104058484204d09031519480305080400303025185c028405c00382c042d4642c01500d8039150160070019001042000c29646120103984120b0028003c0c5c00d00040c1000e40450034050403030414403480001406a00e948001742c802c0c8460442003003072200c0c8001e07000721445003d5015070702041075600041e4041141c80000e0080c1406032010307000384258810401001041141d2074165808110105526524041a41c103000d8003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 948808507 1250 948807257 948807259
    0x7020c01140706022101090f020a020312040302120d0203180c130c050d060b070b09010b0109030f0c0b0301290f0706020714010c12110c1c1707080103021806 69
    0x7441c0384030310741201c60030103040d005100e4007000d85001d88041481202081c503050a44145541600401c846100741c0300b01401689110015402c04040c0e410107502c81c081c26603007100f03040722500010101842072104400f04071840301170719140e1f250790b01090025002110402c1165500858540d07a1810010b041140b03500c3c0100b6000b10341c41c5901040c0068a0203280d11340500c001400581d242102c2070041c0009400c45030090f03601d8660398200000f10440207081404c40764034142c041c615903680a401d00040d41e402c0010440403098500d0120321034102c1d50300c8a0600440072001090700a00030110020303107000c05102c80301515000e5286810340c850fa150360340c59081c0400c4000000352054015006050184054a6141407004821820340741e81826203400140c8051441880820303900c00c0c88101d01c110f80b813150405062a07a600d98504101c01c0c41c80801d050300d907034021610301c51003c000032548501410402401d01440151258000b0301080388a0409034070002c1c1200d068200035482614 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 948809757 1250 948808507 948808517
    0x10612031d030d18180e0c09060a210b0708010f170a1103010905010c03020333041d01292e02070b0f090f09010e2706040c060807020c01 60
    0x40c101c0c43c1603420500030340845103600200040045c042c09110400c000031132200d1008620305480300341d01400c0c90785404610f4410041d002c01d0180c143c031100c070b80100740c44d007004d910174044180045030b0b8002d6420031401411203002e04100406070b039006451504843d4107018000045403a1440c500000c038104010300001da0040b401c45011440303031481e020b40180c0c040c000044400030b81e1111420b640d88200007802098001040c09140030800b410b646280220144001e95450901c01041c41022850b072284c5c030541e1102c0301c01c56460b2441b03a801901031074942c020800c50103646070110051034401c107016441e08074401c08111034289804060070070b0050540000c00030445000c1074052403410644901103100c2c110740455002c4500c002801c1d1000b2402603151146880010000c404000310f5a440c01800048010000810b402101a03044040b00442d01c442c8007942c012092000c040e4a8038074954070a000c1031005201350744801f10242c9005640c0c0b21000e607038070300c4240d070303614011180240091 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 948811007 1250 948809757 948809773
    0x512030412030f2001050f09070302010e06070305160c06020705090c0316021f1a0d0507140d0b0f0615090d030c061d030d0b01020a200d05010612031d03 67
    0x64800c3d0324039600c0080e2814040b2510b5072402e0205000964042c1c500000e0799928244031190b0100039009900409282c010300050382183d0009140740882d007000c9010b4031022440c00105400f40302a103a580392070a000340e1701072506003024171a40e0307014410100540100300740441c160910203000340c8103903840310701d09140d919958940050041d801d600c00045018200c102d0700d01c1c1480b12060041c501d640c402c0421901402c2c603041600042d02c080851050421003500400500c01180c8503040340c00042100c4900c04809000c00d5803460b00c00c000822280c07400b01000001c0c0d1445801134091201582c0c00982c210710070403201c43c00d2081001c1c01e5800003401d08000d000a20910030741030150301c15500495103400c00119021500c0d03c007000328169070030100e44140c80c8040d0b84120100030001344000e00b145c2406807504100e8000b40c050907014102c1140072901075803a150040390440b035003c002040500e1b44c3e07520b140102d240649080740020554450a00c0001c0040343d031401d0244000e01410742d607 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 948812257 1250 948811007 948811013
    0x160b09063303030f07030908030a0207060f1e050d1415040b01030b04140f0f0f060d0614010801151e14010c050d0e0405180c06250c0512030412 63
    0x1410401411540c0e18003060840d51540b0144050200015004119600d540c01454068284101038001d0000356000303106203041140d00182e144100c0d40d440c104000a010720440403038003002d403182e00010000c2103402101c0700c03540c00001000507048100c820000c00d014ac50640c50303c40ca050300d408440502103070300c02d8003034981584090311980d01410005000c80315000800e01761900c1080b00745107800503004012006404480da607a019648541c27030364507032904080c42c07142c500c000361944d07002e00d0003804818204040c41d44090701e45503081500c51000d40e500d02d1118042c2c2102041042c24120309040000ca40001c500e5000e409250f4048508446003070410b0b55407c1012000c0290420002014000104006000f1128240880ea4405100f502007030309001c01c0d200041d16280c22011092000e1000c600c001c03601782441d6604442003980d502a401500503880d02e070b60014403c502280210700b003004142c0314170a04665080d2030296a411000384420707204e02031881607441841e4417003c00000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 948813507 1250 948812257 948812311
    0x705010503190501080c010801050d0f0b040804031a060a05010905030c0d0c0b0f0a021903320c030d110a140702060f07030e041407140d02040b160b0906 67
    0x40208070181040c1d04981e0a0b401005551080c1d0004480e0340181c2580b0340079503440280140508000d0720221510300c265a5808114070341e130100640310701040000720341005201401c440066801c0b01e500d5204010b08110310841400c250b51300342c0318003014140060103500892540c422030344000c0c0079095000500d014030402075900c0204407810100c41e10f021850110400160001c280c17650041621030103d000080e10b0304080401000d0154100525800001c0c0d00491540c680001d8106a401c501c0e00d500c811a8200c0c0c100002c0c1034036820214880761660340000107402c0c46402c00c4802e00c04050120144240f1f849007070b148800040341e10100c488040c8101004040c154030140c00c00340740419101410311141c00c80941100001c100780b500c0e100750b1905024240070300c465007030351a10500303040f00c024100d5124082d000d055010041460241c2c0070b02581503c008261a104451380c40900e941c0b1071941c030740c0b02d040445a601088010895041c0300007103240c4110f1000c280309032640080c000c6026 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 948814757 1250 948813507 948813511
    0x240e03030712081605030c1602030f010608011505100e010815100f0809060f07200a03020307030206010b030f04061a040c050c120c030a0305040c0b0a0507060513050705010503 77
    0x2805100030406200040c500c54402d500c10800307a51490840c2c204107550702806039280741030200704802402840703111008601101c0360840c0c4425040e901802c540f0109007402c20090216103203510f08200012456019000403105081d00c500d11840347e07860300c04001d02a50606105030000b40c5001c02030300c580d4054030032690841494500700d0700e51145540041c0466000344d14040010300c200000300001908140c01035004a0f03804060511440c00f02d400000340b0000600b410f08000b19003410518110410112403c0c000d01c0c002a60080205400c01035a6030380036110480040c8100800010380400307100a8900844080d070a14404c2d0f2150388910b405013030a2a0126281005005510b070b503542c9912030510351480a868280d01c5c1c1c51100b18141c200f800108420f10380301c0c01001a01d5000d080841115000304140c20002095212070034030700b00168082d0081260380c000081c6e680460f07900480681012485500140240c5c1c2da910150106100a884c00505d1a4000340c0140070560042e000340d6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 948816007 1250 948814757 948814759
    0xd0b0d0b01060305040c0801060602030a03180201081902040503010f0207020f18060126100f0605040503060121050307060f060609051f1b06020403050c0405060d0b09150f060a240e 79
    0x4426a01c0d1f1380894210f620320f034400c101583c800110308180613014024242140c020403d49900c0103401d80002c1c040c0f543c010a00145400351510000e6203081560584010301005030017004940081c00d0701c90000e51092000380c2c4102a101e42c00c070481e01d407a061000034800404d02081641c1c4443c001503e00c0c0202c410b9911540000d0b00345040c0c035805000040d0301c544034100100b19042c3c50940c2c0d2007071020321500301c0c80400c5001c120030b110644001400504585040c00c03030015060f91440c80440013842000010903500000070101c0511025800407a03c00ae04240700308000c40c0c0e1008140c5d000b41251103190342010f640382144140d18030501944008282c142044001441942c9946804503140082159a103078040790901c01e20100f0025a00e40060070703201004942006400201c4504021500030040501400020018101841801d600c00e0440c0712991490034028119813941500300d84282c00359054040c0091100c00da4850320000742c0d04e0f80c0e400f000f0710102e080116449038401d03c1e62 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 948817257 1250 948816007 948816023
    0x3020a09020d09290129030c0408070e07080121060b01230c120c06010b1e07110315070f0e15030f0907080f070b0a230d0b0d0b0106030504 61
    0xc2c1d0040b134144800c3c903821500002c40e00721104503c10a0360007101c2d041e0403003d502482d80240c8400850385e8200e5180c01500b00101030346030350310100c4c841040c0c41541c100e0703500d0b80140907001520000d2002c3d5a4000c00d019261014542c0c0c80721003480524040003845040d00b4800c0c500d00780880c04a038070004c104001031500c9801444610b2025800d1103007000708004c50003000030140b889040c00d0007219450303c14406a9441d150b04040c41c03503a9a441070203000c41d14003001805880401c4400b40542601170700708841a258091403d120716440a00c0703074800d0080c09003800b800101018115440d10032032564440c1e180280741700c1000c80351400c195031001d800180c1d18011218003c480000f461140e00314000b40391039031514a074030364281002070b4010f4019900440200d000ea04001c6406026141e6203100c19880d000b44140807030300c034944485c0b0118007464a5002100050b01100200794100b00c2440130f018060052040c0101c9080c61440a4001010741c401030001c24403d030441c641045c001c400b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 948818507 1250 948817257 948817271
    0x901180b0c0903070303021b1e0f030f07060801053606060408060a05040c080d020705040507050906030703151d01030f020f060a1d0d05100e070f03150b0a03020a09020d 74
    0x11904d004119002600581d0022a02c50301c4842040581d0000410a031526502e002081032107010815616004900c00c0c030041f44034401a0328108080240d213005081125a02d660b94040513244003002c1c01101e003e02100b07491010842d0070354003020000613546081c2c20b0f000740046991080d800014000941c000c104000000e5070720020406107005100d10080010a81018030b0222120807956100004540003200c0c1c81200b00d80204070b4404945064030041225a2184000c4511b441110344c220381c420700110038811219030681c0007540c045d2008401e40d51342c0b504c072a1005a1348403030154200c41108a0401400025041c121412150748094445d03c2d407064050000b40c140e4104035800c0000034504034103070301d1024030a40700108451040d10300e03241c4c521140d00e42c59107551355540c0a031000c54607030354a825070000c1003019100800d400407015108075144d1401001c609914180f0703805c0c00d810f00c1c03058030142c43c00801401c101c80d4004c0c5041611032800c00040080c3d000000e4500c8021340d030b042 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 948819757 1250 948818507 948818509
    0x1141f0e0c180a0b07030810080a3915030501090b130e0c0402040308070b01050a050f120f0d2006250e041409100506060a030e03091905090901180b0c09 67
    0x40a0031817180f10f03848115039450022442e0340c01410692040701e00d90700c05c3d045000401d60b124500103032000f8841c41014034402481000d00c0e03081241401c440d000d512458009034845003480c0070741c058609603909011599031380310508240c407402c848207a0711008040c421000707514580d0000540480e914180c560741c10016000034100c2e0002e5106959101c0001240401c00610b5410301d03003d0032048854070400c50070080071411010301081540d000f8140041d10340c421400810078461006582d104071040c507100ca2100034040890200710b01802442d079a02142080c0c40490420300c11600d640400b51074030981c442140e0351088054400050180035144020f46440358007800d07224110f05210080c1d50b0030110441c910305421b0b0344032800824034110900074660743d00b100300c0d401040c480c58049004c0354181090b07411481841d4111368081c1e6102d113203031300b6517465000d581c0c03c845003100c40c0c0826507104c0d03204a003030700c040800c001c0940c420b0034500c0340022400c00b5a1904241025031751403e15141d48 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 948821007 1250 948819757 948819779
    0x2403070e010e01031a010602030703081e01030602090a2418080307111201140610030b0402071a070f021c120e0c04050a02040812070501141f0e0c180a 66
    0x3030049020b05103004010300c244055030000000164161001c1422580741c40070007504c9001e0044010104203801011504101c16a125203280d202404034401032941c1d6894103000940c04252000d000d0612201e000030b0f0315028641d01d0109010564200360801c0075410210703800e8800d003030440d895951000c03000c134000b0740401c09065158402c0c04103444089600302082400040d00c1809041e0361304080d4110054285c0c0d4003900c0e0001000e4614900c3c3d401c00080640140101c0102203400c02c2c8041401001d0110110041c22003000e0102d0304107a030b84071100110303000d000000e5040c0150384a601c442c3da01d980102100d69031003405103444e4200c900605a0300c002e07111503880d8468198403490341c0e40040d20302031080a4004503002d000310301c0c00d4503000d401c1d5110f880e06d50301c0304111440880c0321420300c40207400c500d01864800100c162285010704590380401140640d003421000240404103803404d6481c4d001340140b100410081c1403100f030780d0105801815151401e6003004162000242c000208 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 948822257 1250 948821007 948821009
    0xa081303050a0f05011103060102030d0b03070506122212120b0604030807110f1804111807030b0d150902031e10151d13050709020406030509062403070e01 68
    0x60003c0070b595807803d08020f401d4992281c10303418144c10400a1005a0303030000110740c2000821300000c10740c2c1441000080c181001ca601c600d8021400040c4080e0720001090745038880ea000c0c04030480442a0458442622101180c00920410180b03001d0700610740600202090303900442e6001c01d0180f8240041034107034005600448030314402007400810091000c14000010409a4410554203104e00008104024036148115a61304900100c0c091190480080d141d1190181080c4d50064a0505c03014032800211150382c0020300d03210480341c0c4d81c82c01158400e149a0044c4402c0d002c0d058040402c00100b03070600040b03038588a40f01c0120740550440c810a01c0ca90101d0020b0031111101e808032400b0f46100e503500641000b40c0410600c48018030807451003040c0d4017a085105150f40d4250035507030303401002001601c01d201e1850001088038284c0c004006079005035a0910050b10703040c401c560f41e010180e6603540922021000062240c404071141c0c1d80d0104000c040791441c581e64565044100b1007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 948823507 1250 948822257 948822263
    0x2010c050a021c11010e0f0d14030f070212010213090c111507030b060903030307080c071502030a0c0c0f020f131404050c0a0f05130204090e0c090603010e0a081303050a 74
    0x10110301030f41403002c00181c10002000c282000c4460550718000503111035090300480b03201d0602504850140005090700303030f10016503a0102c0741d5aa038120f21802d07564101003c120b00c2000004404d54800b4018020395242c4506280c0c09180d4030305140c01d0201501200100130200701220090342c00c3e0300e10405c10341e0082c110028605003a81000003008050700c503100c46031402181d007008031039180d40340042269031008851421501649400520032103510600f88043c0c24140c05698035100c0007030680c0118002c24141408000c2020801401c2d21400c80741100038001c02c21741311058000d42064040c40552040c014800d5a041d8200c041110881d1200f943c0042c444005504200c20030504208055580c4003c480e0031400700c0c074000c0940000f01079402114041c0e401e68511810074582ca40681e006404910428841240c0142505a072045021b001a10030914000800d0060806110302080d588410000e03106800706519a140103601c603590380349842a81c1c02c0f000002c41d000340258a00e8600c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 948824757 1250 948823507 948823549
    0xb1c020a0c0501050109110306040209031e1506010c020f01031a040905010506041109060322061122060e0405060a3809090f041a0108071d0403090302010c050a02 71
    0x90745051550031204140c0145046514007202184c9a4072907074140d0b0303440481182c000d0307038400c407041c00701781800c8000107501c83e88041c00c3c1a000b051100030656601c20068440380007065621a001110206141c0d2030280d005885104a02c070a03522a400c00c0c48002107041e407a0101c0c01011010a0071182128410b48503a55102c051154920741401644c1074911903650782030400c0b9081000454511015080c61020328450003002c0032854100380f16500a41c01c204100115085224024441d5101c4007001140c006103c080c0103515080c004190161002035840c2e841102c0e5007000e01008220150285178807840010740010f4901c004c0e1a203481840000805d801c8c05141d00d2240082680c8610100740d102c401030121709516201c100d18148d000d8141d1800c1d43e41903e4900f42940c0d00c1c8030107100306840340000780010030b441c0d0b03002070305004a600d142c0030080170ac1702c2501a2215040c0070b840003070000f43d000c2c0f4200003541c4600e0341c1503446402402034807500368040c0d001601ca0300c03181d000c22010306 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 948826007 1250 948824757 948824777
    0x910170d0e0904020a0b030403020708010207060609140705030a0f321b0a45080304031e140102070506100b070201140f1e040e0108070605040b1c020a 66
    0x60380504940c441e040160ba03552110304040d4002180041c10740a46586c40b640440003400b4540708018020003010030b140215a40c1139181400000340680d8011079141c0c030308100c101e00190311568545c2d441000704e6a00c0905641f01c020100010340081940c04240e542c5581000c0b06841400c250290000c030300e00c5941089060013121900700c1c00c4018068204808000480c000c100000403c0f03030140300d82c0c4d15044110b1086950b103000c44003445070f2032540c000d0308502d640c007810150b07a40c0071031a00c1b0942004038100366200840342d40da203d04c1c000200340b9940000c421352030000452400c00b0782031041c07111034030740b0f11500615800c90304841800c1da42688054180840344c443d54a00101030050022040e1506c0444c1d000070b050b0509004418403207000012f000d585c2440d141066800c04420458561b50071030800101d12540d801601405150350b94050001400d040c00246100c100c0b09151500d0381054a010b5601c0704541000a41c0c000500340b40204a00605144c8010035040f40907450300700c504 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 948827257 1250 948826007 948826033
    0x506060a0c1e0b2a160f061e1a04090507051e060a080106030c09140d0602040b04060804020f04050912070c030803090105250507080c07081c03050f040f02091017 71
    0x240010030303080c416040410113107085c0c1c0c5441a0a0940300c1d000a04c540c04c103091480c080000300051603404558114100c5001024262034201003c06407106003100c080010303000800c03040b140c0e4484c00500c264001c0d1800c00c650300300b40101e012074400e80010101ea150401d800304607683e100ba440301001541c500e00602103d9014840c0c02210a000c0c038100880c5818890261340051040c0080307842508100c05080c10001240c04079005003149440460700c4a40d00d0402800c40a000e076000c80c40f0345940c2c2d8a112003070526204884c0b14501c40001402c0600b00001d491300c1aa01c500d8040c0c0700c15144e10740c00710200744010700542c0a10044d5000180501e403a6180c0c40c0d044880c49030019880082c20040e1081076845016035004070b0304800d0301c694039400c0c8096546000890783c031070700e91802822450306004404a540c60f850b41d6982d102400180e95803044000c40302c1007103d00400e024801e004110140c1004034000d40c1c0141c029900010316a1150001c41e440480c0c6480049280c0c072030b07242d0843c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 948828507 1250 948827257 948827311
    0xf051002130e01080c0622080106090b0a0b07110108040305071a0403020606030706020d030b1c0f022b0305220b0901110f0703060902150a0e040506060a0c1e0b 70
    0x414904d405032401c4c100e1040016518801d01104440d0040500c010034003582d024a4220020b121010003000001e03502c17840d074009041c41d0010148601010100002c504210304202c0b00003607800220100090741e0340340150750441024000340c0400000740001c40c0065400c0141c86444091456904000c1c40e207460000d10b4160014600741c0240c2040104005081d00040c0400380c1030f01505000c64012020008244900102505072800a000406003420300291500702503103c0e00903501079044204c102c00045140d8810b1020081c185480c000c04400b0a105001070041c403171500c2105410710260903d075500340784564111480100000445428560b0829007008400d80c2c1d540241c460191000c04182e00c68885100c082c0440740c9480b0b00504658481007645021045d440445844500445008080d083c401542034011482c1c48040f6522785000c4080e201d01c20b0240d541c6035071b0410309a440310481007000000c501d01c0c0030510803800c0054103076491103224a00181c0245c5101c403901c600624 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 948829757 1250 948828507 948828509
    0x2030310060f0c0c1214010c0804140a0f061a01210c09120507170c0a0e0c0c0304090b10051207031e1d010b120703030f02100203010311090f060a030f051002130e01 72
    0x68031f80c07510f02d103e004030781c001e04c01036806604220100c85100e152080c46e8108003040d08020565142407140c0001c201b0f140e40040491041c0605d210011202e03e001901d2410351400c00a00c0521081c60889180c00c86801c5540c0b805035915010301d1140c0e4032042e0b107003800881001180c050700000806e00070458414603034490814414000d02d4240c2026011603c042060f0042650386e20035100007481c6070062104480b140d00c101d804883c0d45940d2180d1142c020705030710000510511a605a1b403183d14071800944004c541e0240880324a51610201900208266031150302c10445000565040042e00d11929240d050240040f50709080b804510301c0c21103045500003885981e4a0150f1580c90307400098000c29294142040618800e5022086e4a070030840e01c0c58102e048c1c00040040304120188101c40c130001c4003912041c1c42612030b0094101c41c50422038415030801ea0403c010000310b4203546a2166a0b40035405440041c805981c1d003400381d0f40030300e20f800741c040c104078020004c211038118014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 948831007 1250 948829757 948829793
    0x3180f0b1b090409110604060215070201050705120a09060c0c140304030503071b2303010c0e0112020d020702270c03070c0201050901022b030c02030310060f0c0c12 72
    0x1400d8050590044081c60140c031207014003c0d50380303451800801c080884010a128070040a80381c4881d0380340c4d0003c0d51500060034040c3c2040c180008141c0450050181502400042d01c0740390910014a04850312200020041f07400b55841e0340300c180209555110345a90307403495070385164002c885800c008256201000e28014683c3c4200300400200c0d8004c81a150300d291321107580044003c18000d6200c1000050b0000e0350294002040c00b04c8222068140d0103030ba8809400034410300001c0b04041d10705071194806140840c90b2400b8112010115038010410660308040c01030a020258000c50750250f0886401000c2c40d156410b0300041c500c60108507503002c1540c002c9145580b40c9400c00400d039050629000b4144040400c0404640c0e000307203c200000441c1c14034080d202004e00c2c1d40012040da00c1c0d458000403e00d09111f4a1141784040b0849106138421811300c039529240c17030700485250140ca02c0400c104028000b002d13000410030718215004082120f01c500700310945040402100c9002d607894 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 948832257 1250 948831007 948831031
    0x90f0e030903060103171b0303040b0a021206011209060e03030403110703031d0d0b04050a11040b22020f030106030204030201120b0f04110d0e0a1407030807060c03180f0b 75
    0x7018607640c0010b08103064941c05800c91888034003e843c450704a0007200ca504100880200c40340010070700000103940700394021a4503403270f20f80300e4001c014200c0c8102c00001c030505d204900010f0555002d804c0e032074940815900c00084a45880d100c15003100e0000c3d070041c141c0c0d00300200348000d1540c0941d40c8007109032500c002c2c110075851698050069401100d910803402d801c4800d006070b0380c2c0da11f40d035108401d4100000340c04a140919140303072164011681107915818a203420103c90406220300400031001a0100d507010003d961070030321100c116800070000c1c507002c03c003a00210300f0300e102550003402a514050307140e50031440007508841071540e10f0360246d450302c3c0d071101d20359650b030700d84802542d4155000240060b48800c2414281b04400da0019a136040c00d0307580e00101c200084080070317a400703521400303039400107000f0352900c9181230321016008000901840d0701003402c0d035001462a00342810002050070750180110680b28042c0c0041e6a071800d00b010460901105030b0f1001c1c0d00c07603101070751 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 948833507 1250 948832257 948832267
    0xc01051f0f060c020a09020a120e03210603010f0c05042c040305070f200f10080f10030209181506011d0f06040f052d1018090f0e03 58
    0x301082541440c0700b260108070104090f00d09544884203080042c0142d901c007550b44d801040c802038440c19210328141042c91918514982e0304401009442c15001200c00d49545c03101405600d1403441009020700740d141d581c0b4450081d800055100b685100b0401b07480e8251103a02e444035441550b640031456042c60181d0000000042c000c0194069201c2d030705080c0603444001e1814104020704075078100034505808244440528861200c085940d2201199032000002e070003014405003c0030003104c4d5000c5500b6030007003100c0d904039442c0f10340c2c011500c40004189568a800189050500f41c401810388400301c2d40c090802c100500c201c00007a207403410217120034100780f030000740001d641c0811000e914003203c0004800b680d50301000f4040c0d40000700300c40d454585805844030701320228411140326411504c0d200c24039903000006a90505030143c80711024111020912058843d2810150100454031061941840c15088500060004403034000754180e0210400401c44280c060a584164401d0203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 948834757 1250 948833507 948833519
    0x203090106051008130206031312020105010503010f09111212030f060a08060403020d050d061212080618010e04150f0606022515020a0c0303050a090b03011421030c01051f 75
    0x25415554139030540349a036a0f907407008502c21100150009c02482014a020034005040c0e054000354141c8100b10002c101500300805000211041d103003000703090307110260681a9a00e440c50b819224641a642510004030800311510000d5204960050841132908240015030818503842d03400b03001140010300060501d914040e60f81c070030091055081290000721041c2070106038002000034100960f030580382ca240d51030f081c80302c0014032040c103002072440d00000309a817404101d1070505400b480c042500c02c1e4241140100c8600c401081941d02150103035504c0004c903140d00c01c40205035180300c0d0019000d800c1c08002070a2030301d60f0003503080210701358610070001d1182030840f000310703640500342d1418134031343c144142e06044a105028003c1900743c1000424950080c006103550041942e40d0280d858642810444900003070060500c5105803803040200d41c00c0a4000c00c0071141d00082e00e441560742c09031614039542c0014030048107a512901030101400c00b001108891304049030410300c002d400c1c45 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 948836007 1250 948834757 948834781
    0x1e030905150910030b0a080f16050a0b0c240f06030c010e210a0c06030b0301020f04060c02211018050303040201140f1216020c03030301090c030f0203090106051008 72
    0xb040d100e01c030390406101c14010a010f035011210410780980720702c041c181d803002c5c03594070f071045466654901d004a46d2072016120392480100700750303038008000b044032a04003036584c44550030510815449200d0108404080004040103480403121007182050783e1403e40c4006d402d00708080c01d003078060f41c0106a0f03603c16a80115141e81654429109500c1200b207410580c1c40c004601c0784602014042d003a0494140401d491444040d51600c0e2030a02001000c802814200e104140c00da1150f48010310060001c80d101d03001ca450028001044400c2c02007000b043c0581c1c3c07003140d001d14005a401080a00007a1615001d41c005558801840545031151500c0340d640b6488010030003410000d40d17601c1c002c0c85104050545650b12028503206444410034245401180000d03941c101c44000040003404c580d910000d00015040c00c00307406942142d29041911025100e01c1c034441c8281174440054204075441031001d18401e9140c2000421090b10700014405040d081429450411a2050400004d040e501c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 948837257 1250 948836007 948836017
    0x30e031506060903010b06040e16020a0c1a190302130603020304081207020f1c03050c190e04180503090405070513060c0809030d1e0c0b0a02070804031e03090515 71
    0x98501d0343e0b4850765840020300502002c020107522070f10114011984a40c01d580765480740c400c104841c0100c201d640c10590380d82d40b9140c40113044000850042c0040348001462030885070400d031403e418902d01e03075038840c01c2e4000f522100f00040e0340070864402d42c015050b0002d0003401507003400c628509150700e0b00b2582d445242c01246003001104003180303c180c420040803082402190039140c4040348032031043c2300c00c0042c0c0c07030310310029040201081c41c505c0b20300211003c1c00d01c800a50841d40b105440c00b0340341c0005040c04c190b0b20903510fa40101703200c28121200440c0d144104007440d80c42d0711540402c8101e6001405a10401c03906100c00b058032080303810b02905454503414000741f111880d2610030298815120a55010b0188640344654541c0010420300443d005000300e8009034400d80013103800c500c10320700140003c9070401c0440c07400e64041d4003d003282805480140d12742600e03038413951944a1455042c400702440400790f42c00340743e840241d200151100302d886510209100040c1c45083c050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 948838507 1250 948837257 948837259
    0xd0b0708061f0221130b0301030c0906120b0603010e0d021011190302030402060912010e060708070504051e0a060503100b09091f0513020403030e0405060108070c030302040e0112030e031506 83
    0x40d000900c074584c641c281a101d0400e00b0000141419071034925102040e0004c0c80111a20144280045001c0c6034074084c0d075043d55900c90414074000040d07240e21001120252001d038165590b400c1708a50a2400d2050308100c600c05d030002d0440348017110401080360300b5140c05504101c824841c40c40841054071048990310f05614026860342c80d60b0001541c248140e5244580c4003001072156079541c2c0040d00080f080c02c140b13105640c0c0641c2c40742070a07074082c801100d0410000e1810442488640b40c4040084043c603403030000c41800320505d00105440390b09039082100814008820425404104503406002e4500c00110900340003140000c46d00d2074038080d1000140c2100c0d505280c6035840c11b41c040320000e110080c0702d010310090415981e4000d52041c001980044d600901100e41c40c10607010341c0380503200603540c00c0380e40e68919a04070303400d070031500c4228100b54003004001079513512658000e019001000c0d032401003540e24500074040e44c202000d140e001c1d411100f1600464002c40000c583c0c0030038 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 948839757 1250 948838507 948838543
    0x90b0618041214031303170c090402071505070c021c032a05010c050406090f1809050a0c1e050909060105090c0c07231e0d020d0b0708061f02 62
    0xb40c5102074820101400030011603e01c080104410000c8603071300d00403410b000b911a5143d030a030300c10104a906e07000729254a0594030400c00506581410360041000b80c1c010310204800203620700c0028284d80c1c0c01e42d001400070b50f51881076400c1d0f00d0800d20104081c0c414503015850803c45a40c00781c411456104013110404810070044108039498010390101780e8854004c00441e40c800e1005007458000d801410005421882c1c04214014580208400c1c0c2d00404100d103556600340046c00d01500101000311600e0007007141c42000a01a02203030700203406070f1680480a014921402d41d03405102d6800306104a03991000c1c8005d411001c82c03600d054500a94140c1002c2d0f8840c0070034120f600c24414040611320540b080011510759207020300300b10300304848a41200301da4402c200304204240032502c01e880c4c0d5410301909902c1c5081c00202006074400b401c05504031001f07845510204000316034240100d140c00040026524280707010708070300c503400201721800103410b200003544c0f02e12601c46164545 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 948841007 1250 948839757 948839783
    0x714070c050d0b01090b030307050a1b050909010f0f0b060d11040f06210b01021005040f080d020703020d091401050d09080309031b01021213020a18090b061804 70
    0x44490309450015050281203800a14042e2502d401d8600c000d00c200841c491070254404614600071086407225a048802040f02c1403440e114520304401c440c10544c10000c034a500000c20381c980b120454461407080000140c042c058170078a0091303540c105d94000a0a103081c132500700c180e40301015101c407007442d4140050700d1646c500041010744126004214030380040300700002c4456200d100034104809140480f0b80130400740711198162003069071644d0150b0440598502207610795032010707078428050f103030f50b6106800300e488010460344032a6020341030b950000b4445c1d007403540400040102241c140b40203c0403c2c0b500d128800c401c1e140011443c100903001a404042006540011840d917420407075446e580e041034040d0a5a070350041c0101c41c1c401d80c200010265014062081d240e007408101800b090035940c101c1d030982100c0d04084200d0340403c101e2404a243c041c40d040c001d01c80c2c060386070002034107415400d10044020303006003018441c60400c5400b030407084209010300c0c2c2080d072040c0b001d0018 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 948842257 1250 948841007 948841013
    0x10504230d020405270a0507180906060306061d0121020f12062530050f010f14060f0a02151e01230609060f120a14071407 54
    0x2071074001a51150030f100510540b2045c81c42d42c031543d500f04c001e061600c00c00090043d612898420400751054108040810800840c440088580000c18500092202041d59040c1c115921030f0001e844955644209208410701040110414940d04000340c1542d0b140503580e00326801080d1030003040148010b442411500c0341c02c4200011000141000c003000c4405000c0c507540c00045403601c10389294460300941c07100040348422450100e03580c40080a808281001942d840c10348160301d203030090000703000b41d0401c05101d003c0c0074000c12000c5494a5151055000344d65600360001a00c0040685080b5102da45800444404403092070026440e07490410040c5e0420101400d00040074003420308000815804d03200164100c4c3c4d40300c0c2048201c2c0d0321032941d000c000b651500c0c3d00c2c1521884100310030403494114060403400c07038002c03c00d610380030718010614101d80002c6003011100c8180c1003809141c4900e802f92150034251225000c2032450484801048a0903800b81314200c0f4400103469018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 948843507 1250 948842257 948842269
    0x70608061c030e03010605120f06010b131505070506040b0a06080c03070905100b0304050a03020d1b030e12030c0309040609092406050a0e0601020d09060906050315030609030c010b01050423 83
    0x41c82d000300010074000300038035241d27107405050f404081075001c0c0c03100114543d1303240d50554408840c1c004d540c1a403d410300c0c01d118201c4010140c27080a010303042c482000040c4007000708030300c210300c1403052038032a04000d00740c02d055aa564000c1c080310b41002501e011107840019000088a408640200b0715403a00c4204540d12981a0017901240d24000200300c20b01800040c4e01000c5c0388aa8211081302400003021074100c43c01c035095034480c0c40c0c40c180c1040070030710944558600b0340c001040c00c50080b02c4451540d245a204044016031500003052000c41d030f1826100308002440702c11020301c04010140d40c1c41c04084107441a00f1504502c1100403180c041c041c1e404200502405001051655181c0d000c810311924201c82c580d0051250314501c0b400c00d403045075404111011611044c02c6582410300030b9039a900010841d40848101540702d0311030340d408200351401800140d01941d074940e0001040c0703007036450aa01d11414072104100400c554402d20b0390300e8010141c2c080700c085200701c1042c00164 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 948844757 1250 948843507 948843509
    0x60503091510050a0f0317130512010e010e0c0306010518190209041802041b080c09010c020306010f030c090e060a0b04090203060403180501170703181202070608061c030e030106 78
    0x604200440800302d03502c1c1848009400b41d9003c2c401088048111035000c202a1040c0c481c2c215101000200400075400d0032ba1309119028200000412012080314640382140d4840107040881e0b44001050411400e0903c02e0b64003404e0241d03000c4d0301c904a40400a07801366000b4241c01d1a021281d0f07400108105075606071564075800074000c0c007001c041c88020381080702c000001a4070940c82c00c25201041d040244003017001c3c2a0301e444131000d0796100f101411840d00110300385418041051282c00c01aa000d01013180601a07000c4403001c1207003182008041c9445a8110102e41854030810094003580090300c2540b08400ca84041010080d25000c030340502076524009401d4420f0030300384010140c01100300c1c20950a000c03a1b42640c40d549000440c0c0d2036200000394044005610007240301c4603c01e03040241ca61404980c00501d0b03007041d41d034843c440604111503070010b8000362410f01415034003150302d0341c004074100d0385a0724503104071101c030b180e50000160080600500d0300140980f900d085d08000c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 948846007 1250 948844757 948844759
    0x6050a0807034505061f03121d010e09010e060a090e010c030c020f0a0803060a03080309070302030c010f0c020402090a0807030b1e06030c0d05160605040504050718030b1b0a0507060606050309151005 87
    0x4480d031250820003400701c034401c000e00c444c9c03c2d202c940200d9440d4031425510400c0b0740000c0102040e6440c0a40501080341c0142400b6007188a041c4003217603a0140b400f883e10340b1002c020002400c412904401000c5800c42c44644003150003822060b0444000020300101540d0050b02c81039803034030b82e40002624450a03604c0200a24000320030091901c00c049214000c6034001d4041d00e020742a40c07030045441c00302c9035802e100820482d20707030807000d4181a0301500c01060090721140f002a200d40384a4580341c074070740c4201c4204001c8010441c3c089400003a88901100950f401500b84c202800040e44030000f100d4007a001e01e2403140300000740a020001d40d2842d0a0f6034035040551a207407580107250764080e011300ca00483c1054007240c041445060100414807490f16030400c034030300f95550b4080781070010f0101900852450180c0484107000e01c01080c00104a4403184d03603802d080c0c0307025819039001c0d601c4003003840400c0c02000b2001d480869000040000301c15400440c0e40d40e4a0705503100381481e0001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 948847257 1250 948846007 948846023
    0x702030a110d120c020a06080c0a030e030c0a0f03090504180f052104030b180a0f030311031305011401080607050703030905030a080907090606050a0807034505061f03 73
    0x9180d031942281c010507080c1d009448010b041e1f0f84402054966000036950146501d50030481504d6182c440d9008101c05c003000001e480c5045082e0040074a00074103c00c05480b002c0c10340c18900100340e00500341100602041c1d90070f004245841c0c42c045a50311140e0b102401c1720150441d800300f040418848800c089001c1c9440150481084c10f500d9050303089408111001d03418440811400300080c110180038030036450040c80020704607940c0440c800d00c3c1d00801c40515883d02c03807220302451000051403140150141500101010f8103109096036603413031040820034680c00060103c0307040401c03072a60003082c60905a90b6400309280440003040010b1000c2d10303034000420b01c5a000703540541c5550207404210104c910b96500c0c2c002400854005100d00d501240c0200220015280a0350404d0380c030000d5420005950b00d03070b84100c0070020b0500c4440d4410405122003029400840079038000c0903003852050403a10803069601c0d196191405840f01f949011589100d40410000c0742e119405140e02001c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 948848507 1250 948847257 948847283
    0x20f12012d150302060a090b03010602101d0d110f01230711031c0209220f02120615040b0a0525080a120e01020c071a0702030a110d 58
    0x214010029901d9034040c00441c119011040d800c903020b000510629005a10605490343d0700b0000700d0351200c2200f0301440b24030400003e0010345000910b00a0019401a002c0f20100802d080c0855000303002043c50640c4282c00241071441c0028610755412035414040c1ba034451034005580b402070642d00c400c0f200d40c206001c107500000002d6240600c818449441c00f180d8403010400c3d2500c034980000990903900c01d12010030412004155076127031041c11040145084200c001003014026920314002401d10401c0745000302102903c03a5894007040004d045040103203279403c0d844030034006082c8602c034035602d00f104090121014222001003241b001505c1e5a05001c5c00050141e03000030041d03282d0309034488010410103562540d03c41c070701980a43d00600d000c01c0241e09888400381004071840082d5505040c40180c03c00b44001c01920040c8002801824507110034200411100e1800b05640b64040c84808010789000407400d8000354050b03104581c00c0741d044c020860030f509444d070180001d015421 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 948849757 1250 948848507 948848531
    0xc090409061e0203010b03071d0d050c19150c021302160606080109030c06020a02010e030c0f060907080706080a02090409201f180306151707030f020f1201 68
    0x40b080c1c262454003061030b0804018000b0030012030000f4450324048080400004880601c180c6209081e40040d031a4640d003000603802003080072200c405c0c1140e8561151841c20b0071490580e8400c61207003540100c2c0c0d9402c90a007401c0c281c88820207141c044c180194000c00c04219651127034130600111220508640343c0300c010103409071110f9003d00565116181c90004141408107000c0c2114140d05031303c0b60300c7d0601c0c099803003800a500081380790046560f590340042c2c5c2c048003403004020040304040100400882130803000e0404101811302507966114520030041003402140c031508035a101c1c2010300855481e095200040c2c851303d40352540c4149444404c1040208154252400880361196401050f861030140161000c21201800600c0e445100c0b45850320701c9210080c51050f092169401031030b40d01c0c0d540000f0b0703030b00142d02205200c042507001c0c000c265282520128040c192001450b00515540b1110109654018061300403072007000281815240c0c8084d1140d0080844000c00a180c8510 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 948851007 1250 948849757 948849761
    0x50a1205030f0c061609270b0301050702010209041d120703051309060e0c0a0e0603070210021809130c0b1312031706010c02130c0c0f05150615120c09040906 69
    0x100c00000301440d000152881038070540f41c42099400b1049415103040044c5244420140103d11f003940d81921582d0204003078500b03000b46c600a84481e0005a25080c0708410403080c1c642060001100d4201746503030000f80c080c0003603c4070b100c05a108005a68070a03906046805200f900b524001ca84065840051240401c0d4480d904841740115071410300d4441d142c40320749600c01c4154103130002d200b6010f008110324100b0015034100344203004030b980045504110106a82214072600604201012041040c1c2040e9102d02d900c02001c10100f19001055944e2002c240d0490080030800070000c100300346c002205031145400307484d5600203e1583c140c2440c00405840759500f046045519520100300ca650041d9070019000c1d50041c500100a081c818000c001007032000543d0080111584150003c2403d844d01100c00b240940081c2c400d1106031505940f41c000007601e454050310b003118000303c00c42d1400003501c0c00140c1c113200c500940e0310b4103981059180900303149150311524003400741c0c003040700035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 948852257 1250 948851007 948851011
    0x306010c23060109050105012c13020c06070509011706040914010f062c0c0717040812030403120b0a080f07050418050a0201200304060f0e0a050a1205030f0c06 70
    0x26049869584c0c0b11165a0b06a0303400f803080c0c501080c0c0d0071001041803260000300d5035414030b12001542c0c52545090002d07960384ca01c0301c01f40140755400103052038206004d01c00d40d83d0081d814184030b031400c000d600000f00b006003485442a4580c607004045151a905c58005003d008d800034401342454081110140c001c00a154109080510b043c00c00144c8074001c83c9000906002c0080c80c90480d2442c10b1141412600100510b1030310608022440014208003540d61882e0a1824120703141c50410a034246040d84d0a030003000c1a40d0140200800603620008501c1c5a500c003140100e0704482c0f200214001d1801a000b2816502070170a58a5120740002010720885604407030030302c5403c3c1310751507140a01e0144040a80180c01c8281d2800140d4000c10f41104812000715003442a112481102801c0d6001500b1170340002e03040b0140b440d501ca0b8042603280e200310b811150540d840d403402c800100984035034442e20030300010b10300c00c9409000061050f41d070f0115015010568404940d00303095294901 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 948853507 1250 948852257 948852323
    0x10902041a180727211704030c050d140a0b06010e0f150c1c09060f0314070f0516050a0309080a0803060f040b03030c0c0f0f090c0306010c 61
    0x2000801d014604807446603140144210f442c2c4141e5045060fa0140c12000c06405032403074000c80034030008100c1a0b20003c07240c90308240151511005031450640303c821400001006d401c1800c1c00203102054012680c50210707102140d22007250840e918008140d14100c7d06450300c4e07400385281b80018070251801c103a2084409030307514400b050042e010416600e4103030f03150a030082c400e00110300486181c24000c0c1003010026003125245112400f482c8841c030b5041030002c00080010320200a02e6400c1950b003220304141d41024842e048481c040c0c00c02c8a80c0081100040250859042030364500800c22500c40c80c5041c0c00564910f0340c1814034075602e403d268070840005100303000000d60200c0200d00391640d00e0348070000038510f48503181007008102c19402031641c019603901d40b2001036a0700300028003080d080384014209403100b010030491211010140d00740100038403000720103d80d07640e101d030300e92243c0c40701c1d0410749944070040101e82e12195130380010140309400a1000712012860054407070410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 948854757 1250 948853507 948853519
    0x2030105180118050a0609060b09180106092a03060b040f0314010209060711010e120d110f030d090809220b0d0f0f14030a030b03120306031e010902041a 67
    0x10103c8208444040c43c10260941e0801400d10b0f0001d5400e401c4030b80d9542c001c410101e81070140000052103031105440241501c54800440382004c07070203005060061440c039108111804100301800c802c0c6a600c0f6078144800900b40035100c0c168003c0d4007145c050f21540c60219212501d0b00103a54100d500c50100344c0300c02194910004000c0c005008480c1c0c00704001d020f15041038055910504842d1600066505000000d0b002940e5511580ea07850700341c1c24031100612075a1072800c40602201007594041c502a088070700c1d902140c0d4400021100300880c4440700189100e05820980024040c80c90120b50042d52040d91101c041c1804810300909001c144003000841d0701c0108001c4414101e0900401d4030000361100f0003c281244245000e42d401681201810440700800300e08592194001d400400e648130020200c80c24104126501c10580314600c0c0d24500348400004c0d41c1d070b070b9072002c400e20107a080e040d100c03082c1800b0740104d041254060070034010041202c54404000d0040f06000740100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 948856007 1250 948854757 948854771
    0x610030c0b07031407060902030a060506091003020a140118030503090102120301050f09060609091f060503010308031b0f040e0601111b0103240f0504061a03070509010c020301051801 80
    0xc5401c1c00300c4003600d40c0743d03c90300003100102007102850b81201405131405a9a80c0f825400368134144854689540b1440f000641c1b0f280c800b040045504016001d00a04c5203500d40500040c0c403605540010b494200d100c00070707441a1980101d5040d45411003080c1001803800c400410010000003511240c9070036000d5412085e40010200b2090000b4410303d58440a000c410301c0440c18008038803600100042c01c1c103440c1076092404200c3e4940280c0b290ba1070b544020420040c140c0c0d00b00781c42405008285400e914651454031246d03400e00014100584014202c0c4071000c10300503000032100c0306036204600c151038035540d1450801c9c1c02d4045030b8041c0800c001c501014a8040c022810030b4009075a00355402c00680c2041c0110014401110004503e0f41c00100c102e0741d10800700180c1000f00302c03490541e0003050510003131109a4000da44806021441040110328084644041e82d5101c0c0e49445c0c00ca031540241b4004940c0100d01c504041c2d0107501e418148031072451400701c0c1c028401c070084000c1c0300381 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 948857257 1250 948856007 948856019
    0xb04030f03091203020c0f040f1e0f021206040507180f05040b060a0503071805030f24090601030f02031006080606040b01050c0a080d06030c0e100e010e0109021b0610030c 75
    0x4400310f050003001038100326a40c500510300308460b5100d050001c0d00000751404003a001c1d004a482c09000c110300d00310b5032014908040313038900442c030300b180301400c003503040228007424140d03c9540a003030540310301e03114030018011a12030010b010b9804400f80d0000d22155690005900046030350141c80c1c002c0d42010260a59800c0410442d12028070599403146956141e0400f11080c219840e00240308215640000074035980c200700443c04128004040c00c2d240c01101400750403a07070429050703809800000f04000454802040040c11280c10184c801c69801c224400203082005094070004170b58601440402c016a000a4142c410b8100759000c00034040004015503480c020800c80300d41c036a001d2801c0b4000078807804081c11301d002d2407400218460b520381c2d50f4502c00c81c5d0ba036042882c0c80703228102000000d40d035151a101c010004070b8000701c07103941802c00c42002910305001710104150002007204000c082c05240500000c2101d0990f0003c4c10501c0041f00002113a00c400c0e1504541c220011801d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 948858507 1250 948857257 948857279
    0x20106362f0f041511070f080c0d020f010f02030d15031109010311040903030e072c010b070303090305092e030209030703030e011b06060e0a09050a080d060b04030f0309 74
    0x303503001045050400703103001895a02d41c80401030810800c06a89801414500c003005450b019147c1664001d1516043c04100c529007101d51208034800e100c05034012015171111000010503640070300c1c2880301080b4040e4280d18600c56201000e54081c07404000e59031048242901409591060705100b1032084010300b0409505070a02000c1c0200c000c000035000d862403e903001520291003410b000c1001450603042c6400c0108907449400c40122030584070710a284213420700322610800c503580c0040d07941011501c1440f0300075110000d0030b050391107044a0916003d0320660b40259001130038080031034000110340011a018544103003c0c43c1e620081951100c0c01790081c1c45640c00d01800400c0c0746031440d24120b800d00c6e02c40d5011414440d10460f0590103800041d51141c440b400f4200c04074100e850b1a0644440800061848000d54602102040018400315902045c1600415034070b1700c5064051a000007012258450360310b8040000313001041110044201000c00c1c000d803181c0383c12554941540710 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 948859757 1250 948858507 948858517
    0x1b08070335090a021215011a2502130b030d030c08191d0c1306031109041e0605100e0405060c0304031e02031207020106362f 55
    0x20004001c11002485807246020554046420000c5a070400140d4001c141d00140624510040d50000f03205000b00d8181c444001c2e00401c98001021190b0340c00c00600322060003100320100050f851403080b5004d00f031000c1450101103030000c00011b00001141000300007000d00102e858064001d019155038014060310801141000a840310900703665503100316a50507601211801080c0d0307445d68400004411040d400c0030102510009044c500c502c4810081d088852141e01002682410024400100b80d800300b0303120b404003070b0789140e0070ba00c82c0d00d0801850b1030030b040e42c00c0b15810710240c0c881c1405a9030b0070090040640e00304940586407244540c2c3c0042c0c1b0100c0c0c0113800c5c2d41c819030100b1080300320000103550003800303480c001d0322503500714961003511100e08454000582c004218800840200d041064022540d13000802942d03280c5207400c0d1905140b2200326000350101c0c11185102e2148102c10011070030700d5642001082000044403500f500d55041100c10107019140d112050010707142291 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 948861007 1250 948859757 948859817
    0x3050601110d0503090f160617071b1104020f090406050a26030405040c0f1e021b0d0c0306021b0706050904020304020d15050106030e03040f05010f1b080703 69
    0x400308541002050f1400d40c4042e000100910845400503800901800043d00401e254213042a181d86007982c010b0000c90002001e03040d50540000380f0480a1f0001100e841801321b910708040f0344115400c02e007038401000c02000d500180006410b01080400e24020b051140e03041302c0401c40c3e151240c0910074100c3c820f001780002542e1000364500d100e520382e03601020340c41d400005c8920789503e4802080a541c3c03a24115000b003a0030507050007004e074200748115001484504000c628014640000790380d1420381c0e20008d03401c82112010051500e500105001040c0c1040001880d0342d41c0740741c41c1009500c0300c1001043d0031003c5106082003c000701d030290864403141d45041c00c2c0b400705002c101c002e50010b00100c3e486120800150001104580c1609040f9551000015958580000901559011f46c0b0011254004100c1448032190007103081d41501c03406c0c40d0002ca06200d01c08103030b840c0c0300b1640b240410108030480030010020588004d0450510951f6021090340e2000039100344001e00303403c05 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 948862257 1250 948861007 948861013
    0x71a011802042904030602040305060604050601030921030f021210050102030f09010e13050708041428052a01090b090d0f020a15020604111203070b09070f06050a0305060111 76
    0x2910f9420b8500000c420b52004000107039280c107940742d8806040341c0c80750344220f0329a0040c1040103c41e00d0a4491954491420300f000e204280d0513560342c0c0c07008600c0c40c5000407051840035458810f588a54170003440d102d110301c000c565a000038483d002c04000103c030045440900c0c03120115080d40b000c02910b20180c16903140d103081100e40d0b07006551454821144540001c10035280040c046034071700403980070b01c4007070316018040d0030941000d0450401554082c8000d034040903000c00c85100d40150038202140c0700841e0b8000714181d2030098104940300603c000d600340e99681641c01e07200d01d415031000c4104262a901411070341c0c1e101840840c0034007000e06a000e000b41e180d0a020501c1144107500c2544010314400120361a00811090608041c00c54401a8031100070070040100f0071110f840d0541c4104c40b03401c2c0b10448001c202d03070f592084440050420341c1c0b190204049030010007401c0094504048412081500d885008000b0303000007803214002420080401e20650040350095040d10b00d02c07000d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 948863507 1250 948862257 948862289
    0xf020d2415080c21041112010b060702040506190f0e0f01270905031b1e0c1905030319020d0c0312150f030b010f0b0c1504030203071a01180204 63
    0x2203e46190410800c9410b141600419081603000300d003042803196224030032000c940c90f070714002e00a005036245020b84960385041c8141015940719016100020f504031400702c0d031f40c1d85040c00f003084408045404003a0034415100071840c1d140c10300300c400c103440042546130790395901e01c1e503206d412080a20501000c4568140f40800360043e158a00c01d02000e01180400c0880040c0d03940c0303103154000c800103e0744e011003209001000409002c1494010320440803411036003540340cc441c1d224209070220500c500345003400c201c800c100002c110030085c072004081da078541452201101c00c6000050030b0100600500545110780c500541c18222043e425503151140d130b078985c0701e203c0024400c130f11014690b00d10182c80050b400d070500c019100914806c640512680d4900303001c6445491054002c0740780c0311414860b400030303c1c10009046d0030040615042407420b49035801c003a4290b10460340040c0c440c03201c22070301e410000020440c00d0b0480d00d01d4840c0c1d91004458169040890140303000b40e083c00c0b6100d001c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 948864757 1250 948863507 948863521
    0x2061617060d120e040b030102090307050120070e0406060501021c1d030a0f140a030e04020306060d09060507020c010f05030f15100f02100605130f020d241508 70
    0x4400c60340100040d05054211000342c0300c442a0084000a16000441c040700c24040b41c00c00307008110180c04298000c0d410040c5100000e0345850560013441d040040c00c03041c2e03840c000035120800003103a0300441658440c80d151245024806012201511180d0500704005119440041c0d03124103e00c4145010483c3e140d410300484080d040d9940a070300d045094445007045a500740704e1544018410300c1d2200490307200d440c002400b941690361a94207904100c8401c3d010039044081069400d9003103d0041c1e907a5034050000340c003030182590500c0141e14118210040041c1580100e0041d600c4d90200c80f46083c0c2031b80110388030141c00c150b21303002803001d1011034a542034001405400c10701c610280c17100080c8a50100d03440e40303550700c11100014a40e94200030741c0e54040c4048034248900e40c03014807690b420300c00461758246a1403041f0451700ea44040c0300700300c0c003182e40c1030302c1103080011024041d03a800302c0c00116807007030209442d5003150110741e000516070251700c1000c00541090784035a8007580e2909 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 948866007 1250 948864757 948864797
    0x121217010501050d0c0302040503010c11060c03091225150f050c0f0c01061a04060e040b10080402030a0b090708062d09030d021b370807020306040f03020616 69
    0x10122080c11f40910001c1410f607020300880c82d000d4140d5507a8010b00705424003091400d034000e444421440300c100180500b0400210390303a02c00004100a040e034820500c0d03943c0810422840c013962078400c200303c8400070825804d40821181c00100720a0006002d07040c0d80c04100d40d8240d44801d901242000040201041c00c000380809200101c000500d540c0d451211546105041c0d90f50340792404009001d009150b0440500e45c02c410050398100680d064803400700345501d04065100c018082210005000c56a040002a046070ba101d4500b0382d0905115142c96620f0300d107400307440654050380c0009082280500c9480c00c2940800e441040760f445035001c00300c9058406491482180070411911016015900007025206000021020043e00b8410505d0400c900003003c81c42c0d08000030900d04d11400c4005040303005078942003804180403407034600503001c0d10500c3c0d8000d416005220402042c8003003025401c083e07038003c0c0c00b6940700d903541d0340004c110028844085000f03d01e030700402c442c02c03c03441 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 948867257 1250 948866007 948866021
    0xd0f0504090b03030702040e030a090915091d070303021c210207140115051f0215090a02280e010e010605031902030405010e160605040b0a0306121217010501050d 71
    0xe004c0e40d14181c00d81d00420140d90984000c0592644002035040c14664024503c00082204d0341d002c00c6001030750844c01038201118422240c2c2c040d10382242c0e01401482540d0720002e03090000c102e40c082a543d20380652030b800008130441c00d2000940c144211103005284240041c040140c1c481c01c8a0b07044107151000f500144402e07140000312036000c1071081d10910541c0d0150f154510300c10303001d07440c040402140c485c2081c000540c0d0100c5000b0200c1550700040c00c60403011400c00303841150358401c51400e2078042400c80c003941c443e65103e82d5409000880d081500c41100d040e9070f0042c15038488103010805202880792400421201340100003143c07041002e0f5030881b0140008001e98440c03a030f41c240581c1c200751400d55407650348402c0a04030382c07010454190401e00103001e01061a103040300c003038a44d0180340f00306403540f0130001d07044a856109030b0180f00949081e001d2009034500f1030400502d144200100c000200f4103c012031000000c40c00401812610305946d104c0c54002158101006031001c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 948868507 1250 948867257 948867259
    0x30a0c020312010914070509030604121b0b2406070f020102030409050f060901050f012309030703051b0d0206041809170c0616080103030507140105070302040501020d0f0504090b 78
    0xa006100c0b14803031440400d40200811400031910040400d4650741c4208060f0041041c400c0030094801c1c680c03000700e0b040f9840340c1c20182003030079070b12401d8041d0341c0c95901c0003074816079a1801c003601c000c10a241040f1030040d9285010342480811080d2075610900c00d8041c840d502c02c609200401c0080d8180d00c0c103401251040c81681c3c14a03980d1250941039450030340342c000740c4444100800c031050070048546401004102c0380e880403105048000390900c6808085001d80b42000100910094000411544414406811074503580c2d5a824140c0e110b040455404682000c4200f4514040ca000100c29201580040c4014038091030084840e001d1100040c41d0010251942c8a041c0131900c0d2011010440f82c4038180540d413007c00102c402d082000c001c1c08042c8040319088070700901c1d41d1184515040d40e070306041036135944409040c40c10302108030a1092040b9820700042210440d8142c002c0d00488400381c00702e807602620400d003038904c0035503010840d00142c1c003400108a02002a08121a0342e00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 948869757 1250 948868507 948868513
    0x80304060b0d08070218070e0d050c061206180115050d151518181d0f0115150206150109030204090c0f1d01090504150c09080709020f030a0c02 63
    0x4204040b400400c8441000d6400020201d281410350822403a110f18150320303411014860b07e085c0c2009030504480d1404280900c0c80c0000040802000700050342e59940c0081000744c40f40e441000d190f083c01c1003207504501400d1515542644202c183e001a81690b0001801c006000e810080807a01c0d9040984e500410316100c1c156014549501006040a0507800d02032180407800101c015118030444000b401001c0d0700e044d020004078030251702e81c4403030a070300c1c02001c503072240201c90043d1b26279036042982500e070052080140c0d5044055000c42d000a0a10b43c1c810050303959280c600c044081000408005a000350b00059034900300c0107154803e210050400030006922a00403404071442c45804403094080303180b082c00351181d841c280b140100713860b008038500d0441d017840110740c10034180301c0d44250642311400b0030f04102080406028890011004118030b401e0000b00030900e10041c0301c6c02c050b50241c0b8002044280070390003125404d41c8144515483e5460b900303c054000e1441c0014201140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 948871007 1250 948869757 948869771
    0x121c0e0105132405070809100c0b13050105100308182106070905040b030d210204080c0906030106030c0b090a030605070c02190f03150906020301270507080c090a08011d01180f08030406 81
    0xa040c08072079400785000d0003180f2f0b0050094a043da003100c6000d0009445120404c5007000029074082c00c5810151800ca0f015038681d01050210319034500191008240f10b1102440d81000d00c00001c020713101d000c0310b60300c021203144e0707840c207002c111108041c8098054200d000c40f5081e0b00d0041c9501c1c0c403002501a8101910280031412070100e0300503821807076540c1c0224884c0380e5280340134030340c460300b103030048000704906451503035400c07139910040c407030540e00450110304c5030900d98500380c1c2c80e0011504607078148040d20740000c0003400daa0300d04804911542401e81c801d0203a4451515075410b98a5100c010705050741152200e5406c4600c084004546507140c81600f0001032131400614000c260079880744482031300c041c01c0282c0d401c000a00f60101c5a207030408201c18194041c0307659401c800d180610304d580307520200100381c5505040d005030315503608114130002480680c11501c0c7e50804000001c0140050032030080c1d0752550203a4000c0c02e28940742c0f0309000414106001150402e115060001c0c0c24 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 948872257 1250 948871007 948871013
    0x1205010e0c0d0c0e1203070311030f031b04050a030b07081302091305031c1b050f04050909030c0f0726060f060d050d090302121c0e0105132405070809100c 68
    0x903030441d150b0f1701d9494002255450030141c024142c0c00204801f4400303541020b0300030b4420405404009c2c03000c0c1d2414414640e0201510a48040310090000944440f41c00c4d5220304102e00b6012003500c41100061412001030f61008184558201d210340c000c1c50100f80391100340c04000312441100d000d0718540801c00c0410f00603000b5103a11908aa1111004205052800711110700300b11309807080000e1141c03c121100e43c800402c81101d0076298121100c0c0b48a0315a851001c0c914001d60000c02005c1c4946400854140700002e0101c04880150240c0c40000f00e0301c0c840c01c954064140c4a9491541c40400811050030b01c1403c00d9900050191401e559400f5a8884929041e8840b461070040387c0000414070941c02c02d004800c0440800400400e407244d02c8014949a1021003034245007000400480081c0c81d0384246c08940240d41c1d041c80c1241c1c04d40d1103203401c0c10b00d54000451840c4803042036078010145801082175812264101141e20b04252080080c40840440461a04208081805c9076000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 948873507 1250 948872257 948872269
    0x30b04020309060912030405060402150c010e1c2a03180e060906090103050d0c03030f060902090a05100207092c030a080108010e0a0201030e120a1205010e0c0d0c0e 72
    0x4140380c0b00000702118109019403a051410019403001d06081c20810040841c000040140e04640c0c1918031101c104d15905641105000d160741c0c030001e03542820340c030017a44280012008000303031b2030b1800102c40394441c01041e1142c6d07544041d41032094092a20b200141c8840c00c5c820ada81034001e04201c801200c00100c82c501e0314280342c000301c00038689501030004a06000c100142c1c0880240c13854021541940c480035601d0340d00f51508410001071000c0c402c101482034012194002003203505100d010345410201d0082e40019050314000c407140300c80000c131464248001102c904881d005403a00a05014101d0060a00303000c60b202c00000201c028104000700b20a0805403a50101c00745448901c0010018440e0300181c0c8880026810040b081070329900c0031a9804180f40c0c2402c0c0041c2c201a0454500d09012460305114204503000c1481c425854000892050701e0006c030350204100d81c0c80e04402d40300c01c082515211802c2d641401a0b2030310a21642c4401d45401960501c2940030180130000341c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 948874757 1250 948873507 948873511
    0x17070803190801062109030e09090d0e1e010809010b0901120209060a080d1107081605180c03150d060929060d0204180b011e21030f030b040203 63
    0x8030661154441541075503101000e1400f608140c070f000c0c0d822903c00380010034a45000d0f083ea01d2655696117a5004142c081c800c0341400c0c007005400c40321140b920140d104e0720b50710811100c40104180d10b0000340c051420b641d00c0c11080d6102500001d16101c01030045503030400040246440d99600d00d4446410356503600e07914020f0150003100310910209205205101e8000b5007a18080c56411100780700349603022840015020a5162459040e803d0307170051460202158419041c0c2d0086c0d551004141e00043d01132415104c080e00c0400b6005100304907007401c00c40864201800c1c0700d041c004514034030201c400c807013035003a401059803410b0041c645400d803c80c0c03d4030a040b20f107080203001003424803c0e8100b084400000c6004040c4d40c0d80b0b01080803510b07224910030002e00c40c41c0c0c5c4200b800708040d035030b40201000c80d81000b8032580940c0c44587e412003d02c060410003804040d1075600041d00d50300c00c1e01820800f00a90080d2411100341e59040c1c9540100c8490441855150300c806a0103440b07070306c080c0d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 948876007 1250 948874757 948874777
    0xa02370c0b1201060e040b0f010305070c060504140606011e0e0a03120e01090602010e0c060c2803020c040603030e010f03020d1104031106070215070816061406091017070803 76
    0x205514213840580341c42140e48817180158100030711404513503580e90307023100200000e0030003040542d00d0718411600c01000c40001400c0621b020140424044050321400303010203101d0403610725071541d0b0010350364507007515500000020081c0900d0361703030384c03055800000c0060041d0180300e4840d00c80d070300c040845444800080005a007401c0801d0190380c8010070380021310150000304100500c914020b6251310320301903100e010311000a9840c0c2c400e90100615000790081c1d00300210b0002000c890b4200109111070283c006118203072011505252500c030702c808aa6051300e442030880105401503504005000100b428540c3c2400012070b114182d0103007188492036000481e03500d5045160248600c048607100ea806207e00340040401600c0e911980901c0c44c01900c00b20781c0341c080c185490403141c41250801c0000d00a80810201045140c5d000340e034492400354050603050703690201b84080e0000848442031a04042c80c410415603c8007020643c05009500a80b281030740c803001064a10740c0820115 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 948877257 1250 948876007 948876037
    0x309070627032103053601061e080610050405060d0b181b090c16170301260c0d050c0306130c092d0f0e01020a02370c0b 53
    0x4100040583d0340303680d250090a0504200c503050041c078203140206041c1490f44000002611600c1c1500b554441d20402401c181c001e11419458907040788420003458103884030443c5140d0701048205022981c188180440c2900c24501d074580410000907043c00ba00003608051700020040c081031404082e40d10a96200040d00e24a20880b10703000e143c00303801d1039000140035490755194002e54420110b240c100e0460340005440710040a0344043c040c4a2080003401c5079510030100c0101caaaa40245d8100c07a400000081c10188400220183d21407041c101e8180b5000403410032403602c1e00180c450507240c000c50450310060250f41c0070a1400c84182e41c4040381e0081140207004026544c2d244c4005410b50308000e000072910700c2401c6076040b800741d0901c0d1800d0201506041c04160b5a800540105144602030040400d001a014001d40c0001d8825006004424a5900c1404054035405404c00b03804107071509030542e045290f600c2181c01208035a078400d403100002d801c82c40e04002c0c0c0b0740240d14482d5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 948878507 1250 948877257 948877283
    0xf05040c051306030c050d0203100e160501030e12031521240a1a1914030a08040306020d0603050a050303010518070f1206091802040b0105030907062703 67
    0xc228802d6001c03600d0190150600d8420b00014040300c0419040b95015174915002e1901440040c1c1030016280e140c1000314074044101e14016400540106a59801d98401c20340d1501c4d03100440542d80d9901840d07800764801d84d03150101400d503030011607211036040c01c01200c0e01c8070400001d1146129484030020a039071425042c8849906200c070303040107a141c109080408940f83d0b1114003025000300441216070391248801c00c865002c103d00012040010110300e0079000c60300b02110180703018028a800300d0120b40c0d00003014100000c05200d1150031540c464242469655064085d6005642e41c22006442c1e41002000442c100b0140c0c4038148a030700515201d40c109800d105540258044040200c0245000d105000d60060408c01c5890324926041041c141c0941c1204013401d03d03070f40030f500b00500c0e252807840301e1801c5a030881941807080302c0030700880d0303101c500459450000703803442c0c030003034000b00420040740d40a0307401c5101c4002d41502d9201c03400c000b51485599886d05da0b00517201c02c1d40d0000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 948879757 1250 948878507 948878509
    0x613120b09010b011b0c120f031409060f070204020d090f140102030f070e010e10090905060904030203042309250804050c0f06090406081501060207150509040f05040c05 74
    0x18500750320500001c000c022040c00f07400000c04071a02c03028a440703411280c1444074144403442c049400034105100b05441c0403081351130f05c410708110f1140140c0001d0a080190b00150080000b01c80159500420b902d0400003903180d45112903001e0340c800c0764025400c100d050098070003400b6038050b00e8025200f0f19210015410003050340d10840c5964400c59104104001280c0b92000500b07402c01420b10300950314190000041e65030070141140546e11241e502c8500d14100e600040c0141900e803200b8050004c0d4a03410700307000c0d0400c02a1402409604140800d000e002c1e00d2003007a6031103400004418140004010101e001c01c40c2c1649c040c414203c040104000700310100d143c005d40361800e0700e0202c5c81860652600c0c0c0d142ca10070340c113092150801110010b042e603160003e440300c1c8d4100602c1000701ca959102c2d05940d9456030118503607009030703d500004d00d060012032610304540300401400c0369005401c808030f601c0c0e4442402c05030b20581c0c030700080400c441240310b100d100364802d204241d00c1d941040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 948881007 1250 948879757 948879773
    0x415032003100308030606070f0b191103010b03190606031a03030a0903060b131107020f01020d1211041d0f150303070b1308193b061312 60
    0x400414103142003080c89000c042d007924440850750001c200945a0329071000282040c030404001800303c24865010a0501807072036031071805030240d01c8660f00e0f8591003007070030802d4954040d90150700c9801400100702c1c0040703050080da442464254030f44a5440c40d9400c4804980c000e82120300081d99034080782406005981c0d1169840350110011800c008880e403000309440c40c1800f000380055141c1110302030039100c01c40a50032808074002c050140001e041c41d8502550450402039105800301d00d580142d550000c5080c010169503a41e600004a110301895009407001c030310b4003004100c04101c00a003146000f1340101030416418000b840a0034443c07000c01036000058900d50405605410420071640c001007103910403940056000c1c180da0700d00d49051041005140d000d0191800011075841805120044000e10801c0d5100c4480c80c03200d0911035040f840c0a460f4280009014010b101120304081d041c04800c140020300040c98070401c3c240c052103ca51542c06010024059000d4104001e050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 948882257 1250 948881007 948881051
    0xf030b0906240130050a05060901060c03050a021e0307030801080d0516051e0703060c080c03061210021b01051305030901200a110f0d020a150203041503 67
    0x490300e80740409000c48040141e000c0707000b8460500c40740030000f058a001c107400540c601d480307400700ca82c90150311001400240a00b1102e900096107081d000034207c1ca00607100c94182c0e0f03e50381d1060000c0d8001d80e000d803402ea01c0101e0400c154800d80c401003a203d059556071a0006d02060b02035a123030b4241e86000381c401e03501a0072a084940100b41c1d02c0131901d9029054458668001d150b81340715030041d09201e03050212204411600d1a1040c404000d0a0b000084003001ca0380b02d124104010045ca0608840a450540c0da102c020081080071078070038582150003d00c0380750b40c2010303200031500198001d4201e9100c4098092264029181030401c8242840b0b1103030701c98040c0700110603501e016580d15860b4400c0820a40c14000c84802c3c030305600e44126008050865070108070ba4280200d1f041c42040034003880c660a00c503081c12625028117003403008181d407020350701500c00307074619040c504c03148416411100c0e00021481309200020381e06800c0544006170000c0c035240000c00304038900301003106001d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 948883507 1250 948882257 948882271
    0xa06210512162a1215201315020304030302070e041a0c220f050a0b07080f040f091e0e0703031202070c0f080c0d0308061009030818040b030a031b0602040f030b0906 72
    0x20b00700e0400301c4240c0311901100100ca0001c845030750340651f80003880c00100c49811204400c18920211321216070000000c0040d00c1c02a02100c040c0341e0380340c03d072550203c803c0341c001303003641040c180d0bc1180b080c40c0f2400b290410b405603c1d40e030804da00d44699022007485030841c2100d200414804020686078618030001404050311618038250918141d44101d10034850014201c040005030641100c030741c01c0984010b010840c0c100851030740d82c0d0710b4040140c800400480703140d101c80800010ba031600c1d44205612002c541028109581c03650b00c05413180c0076030811031075404d5020496000020840038908024140a003c0710500034100307a4403500d0700d5031002e892070103045c01d45000800700303420141e038a44c0f14000303d8100514060900341160711904075840144006800704031141881298480b05071407420030349040001c24a55000c043d929000c8050150105400a40341c0055440049211503114081c07440940b40a0740c95012004a4000b13a100381e59034543d403c20320600d00030601c415078100074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 948884757 1250 948883507 948883511
    0x20a1e060507030902090615071e0b070309150b0f01120204050a09020c1905190309030609111f0504030809060f2a0c180a06210512162a1215 62
    0x88554815110342c0704080c00600080038902444ac2201040442094007950010304800c05040c0100054003600411302c040703c110400c00a005d170344005a05c129202c83c10020501c900a000c1603005613426008062246840e5400304030104440e00c5500c160070040603016001a61044031104440c02c0641b00460240c084000d901c42201064002034620041c118170f0b070800b280c1501501c1c0542d0180b0721680010601410034058409001100f00750282c45901036885101040e0210404410f201282200e00040381c0103010a00c049000d400240500803c054203c51038040310310240d0400b5080300b4201100810010101a6004032441d00008006142e20045c14503503401000079069a124401050b540404000042c000f803044e0b0304090300603c01c590701c4991000c03020714500844000d00340c041d074241c03040d82c0185603160800d82c02c48450038902303030f6201e040c0691a07580810a00000b460704041e4500007500c1e00314070350703149280001013020040510b0b00424030300d854034000700081c0000b1000c40c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 948886007 1250 948884757 948884779
    0x51203040303090314190c0e15101d061909230f0f100f02070609080309010c02180c030403081303020a0206030a06030f0b0a1b020a1e0605070309020906 67
    0x1942080c0d82009803a071080e20303003071001680c040544c6000c413041500415120f54080303003001c1c1f04184041c00c051f2614840f8030a0141d03100009101f00700c414090207500890b4002da40c0c40a9881071800580d0094281c0d40d02110807030300c2c400920180c004401e41c1803d8120401c0c00d00c071560f08403d80000800d10046280000701c00b42104007840c040700107216000d104140000545a55850100607054400401f901c62065040340c4c001c014006c49210390000d1b100e6440b0103d101405659418102c81d0100000c510307100d8564011a59404400c10413600040310f002140d02003158031110500c1050b60b103000e030381ca901c0e2a080c0200283c0c0041c15007100d020b02d0070710740004a503001c9410807296405680d0a540c0b83c481c074040900404040d030019102412501c0004100328080c01c2c654081d4030400030503c450560880301041c1160101d03210070151f404500302d140001c0d54904224440d03200c0049410200b0f2180d00c502c810f86104940c4040025a81c049407000c42ca850308889403c0788080c1d40e0003400c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 948887257 1250 948886007 948886013
    0x20f0d1b030509061c05010602010e06041205090307060503070e0a1508060a05040c030608010b01030b1f12050a0e10050c1803030c070303020f06010e0610110f060106090512030403 79
    0x20100c2140251188004610300c009041c050070842c0c41901e00a0802c642d540c5240304805810224025110040340c200130001680c98414012102d80180610180460b51515038492201d400d00130035a80a10500740400802e5940602c11280245a10340f200741c1e50341ba00f810020010380120140d40e2023031500c400280110450b00c440081d4490b0203050000303203074403820000740c0701b00c0d100c0e440f03aa403150401e050515429815000388085401c0d42000744408481000107505a48072048410740103c04100a140c8414140c20701e4a0101800d09201089101c130034a407e0030b44108a9030884420745640e1000b801840402c0007484200120030308002500f00703007071201c00e14800d44200c3d43c00c41200c400d0701120b43e942401160000320481d4102d0380055582e18001c0e464100400718030324280240800012504000c084482c410580280b40ca01d0850056a06a07049403450100540340d10442c0c900c003441c00010803800e4040c103c141c031264540d5240101300600030b60749c440b1100d604d80080c0810000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 948888507 1250 948887257 948887267
    0x7030801140109090606030c1d180403032c16140d020f271515030a18030503180705060412021201050c071e121b0c0305030a020f0d 58
    0x540d4881000e0040c00030382080101c030f08075042d8200e441030a00e40100014000d0701039110100000c156220071109010800142150310300303c0350850b4114000d90100c0134144100245907900511905000a00d001984460a2540682c1c031509815910914144007078403004c00403811480b0401442c0040c0072b060000b407a031000c403501615070007401c40c41040e8085684418141c0c08807240546034601501e81c00001e4805a120b41d0030001c4c00d5618071002c65603413040c0c1a8120861107000e4175410300003d4540e00540070b50700042800a40c10755a07084400304030400501414038900996909407241401d43d014184401ca4002c1b112003907010001c05c0000e40c031914107907000c95803c0525101d080480b8001710b20764100008140c29194178000404c000348000c0d0005d021020700410f0107404080e0401c80559220510210103031200c99000c90030b6615520810410841250422154100d011382c0e55030822200b80541044980d90004503c000f6040e5042100c0f40c107040441b0003c0c400310b1129100942 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 948889757 1250 948888507 948888509
    0x130609080c0d060507050c0a0b01050127120213090f0b06010512060904080c031201060e040b0603130c051005030a050915011203020c09040f03020d02011112090c090c04091107030801 80
    0x3c040e07600d440005241c20b00070002e0729103c12504003a03882480030303446c01030100750f003d005941c040385511180a004550102841800702140c1d18940c11960038800310040b030795801a070807a401200d01074465070a000d24080e4040a92003005615000180f529028030b0040300144001e040040034041055071440428046400110943d140e400903101d80c01c055000d480388410600c071a220000c0e80203030200e0301c1551070b41201c909940d1810800141c4c1c0c100b0041e07410800f402580800c0500c082041410220710b001050b030b01c10180078804964035000320300025610000000450008800c000c83c02045008069000598030043c2035031162030341d0b48207090581800b40707030402c000900d43c580406000b00701d010b031060346c010041d12103460240742110007030401c4041100180034800d001da1030b5500501494046035002c10009003412031900050b454a4402000b0f54400c0c410500003c19a89a03551194024402c0f8003415542c1c40c02d140044041d528821458448070004101c203001080d40b02d00c103e8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 948891007 1250 948889757 948889763
    0x130501180e09010207050d08010e0a050f1503250f140105070321050c0d1409030301060f0905060706020c0712050d031a0a060201060602101b0806060708130609080c0d 73
    0x51841e4503980b020030f0080c02446801406442000c47c034140141e0449180390403900310112070386450765620040026100d040d505c00650a940b80c012410b1004401840c5150400190031910000c0d5030380440084900004600d00b150448000b081c00048012032450024000e40d100c480c1510b00200002451442080c0300031b0100078000c4250075035507560505100c0c0004051000344041c2c1080d602ca048680d1201c0e2820080707915124014440720800c0c107009100c0d04144c0040c1d82143e00e400400d030340501a13110300354104941484081a00da82d24405409894014140142c139682109401e91401c0c003d6040a0948600d55500c0700c0000c0000034a20701d81a00703443d0216010403c094070509100303480f90a50b901c80307090480410361031750541c05030b02250b10a9084404000c20740b50000111a00c11101b56800d134217440e100c02e055801a008241c000c0801340c52603140001030f0312003804540062044412002c1c2440f801c02c24160301c190301c00c01900c952406000c07020983c200240413807105070381c02 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 948892257 1250 948891007 948891029
    0x151101151e0902070303291e0d0b10150c110d080405100c0615030f021e03100e07060302031509090f01023603060109110910020313050118 61
    0x8074a20000089018000c2080c0e21007503450744d02601c2c1c06405004940040b04140c00c100f106103100d04980915011041d03070151100610900c518094044611203082064100c114900c5642c0010107200318203102d048038400c0105060b051158103614003200c041000100009850702c00b011034032041c00500188011903115009040c9490085000d00450b4820340d401407400d01e01034a95500b01c4480e40f4400e1141508100b81c1000c02400c0f02e00307413074500006d44545076a0600c1001410f2840c001805100c14034031040d118142000080d180456494880314040c0d1141c9412410a20802c40c0d8005015142803e50451902c104900c4c6c41080000e020b621035400790001c9440c00c0c00600c801e030061a01c020080d541d503000c0307102c0c00040075402c42441201401035104000f810742505c41c0001c81070320040c0500816403800c80300401405106019070b403003c00c200030603445c40c0e407a1486810070350310355005540c036004440c1803940c000909030b1210381030061800070200c040002e0b6210105030f030011551 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 948893507 1250 948892257 948892289
    0x206010e060109150f27030813030605100e09060106141c0c050c0c09040b04030807030e0d080a0f0507092907110a080d080711100615110115 62
    0x1250f01c02d10a42c007010f840d82020f1403001440340d000c40d102e2107500050300d440000a0703245400c940c0103050300c140202e90b00c151040a0000030682c4008201ca5510029840195500d07a103881c0e04071041070704c1901041c05205020443c1211001d40301e944035444101401d0a50f147c44005484d5100b0046601000c0d40c000441404107446924100e10549000200700702c660240720026140c2e038003041c00c1226a100b640350f12005c80c501703288414422a07012002c3c030515255680c1c15500040c002d4000414991a06a11092445d04010031842c2c611703143d58040c0c0a003048039880b02100d901144402c0b41600746170822036600e0b004160391b811120310a0240803840d00141e8100e040000c00840d1070780c00344000501c40280301e01c080040d00320550840e1440c4040703540c0d40b0502d907100441c100c9580840c3c62440065070040c001c50f01001a4081c50042e02d0300c040340c0c0703156402250000d40242c0d1564000c2e10070800120f0388401d0200380090f43c0c1313000700704d002c0c80c180060300300088610800d0100f07000b12130 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 948894757 1250 948893507 948893509
    0xd0311101410051c080c070e071d1513030609030c060c1b1205090402031905060910090c0c050f0a030e0d0c2105030c010515220f110d091401020a0206010e06 69
    0x2003211b80c5403040c981680e19550f150003000315084001d90340d440c00540c0f6510701f5400d503201c4d0004602a540010880d821352461001104c01e07a0304064252144110f50300030002c0409d40e6401103081c0c0b50303c40c7c2e6400d508546a4580001110015401401040a00f401e019034203d2440b00c51a400c035042441c11550040004088500e407040c0026075402a0020007032144a849200c0714012010009209002c0b81d0307140300c240b0000c1c5104484040b9615015030307040000c0f070400d62144800d05130030306d403e405000b00c5840312403902010b540c00041560020b0304100a042c0d001c424032001200440b04d440a000003900c503191004910700502c603d62540d50310f0003107111240c0402d84d4101c0e134868183e9480c1e402041c285030081008460307070f00c1c0b10f03420503080038468580320840e0306500000c0002c031211104407240200003410394090070301e8810354501404101b1580d0038081c003145141d2240c04500c0c500d003407403c5080004041060801c0c2ea0040c00794460090300410341328156801c0034104011555018 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 948896007 1250 948894757 948894773
    0xe01080d030914160305120a020712020a050d150b010926071205160e010302060403140a1709040f050f160e1305071d0f0d0311101410051c 61
    0x2a6071103d903100d50b8840c00051352028120074102e03800f03142030b940491400c55070000c152152400320401a040140107002940ba0384600d0b21040d4000381c079081605407503101083c0c0f8061603038002c3d69850b0030040070910041a9002c0e54100807402c1c40c1514280345840c1c3e0075044c2440c4035290207044242a020f035812702908005440050075000c1100e04800c499080441e10f82c1100c4041c001010410700000c0341c682c000c0c0703140358100d03940038190624280c03441d11068108043d40b0210300e19806010348007030100340e181410800f1a00400ca40c0b650700e00c0380000b000100d8188404903c81c4500b080c0c00c00010b078503104d1110b907000248220100001d0b580f403070b04480d500300500da841e5104002a840c10701c1c00416a01951080c49039455164291004960245e018808600e069500545a0202c0f854a0815a000220b018401e003440300404036a5012541000c04401d4080032150342c80d000c81c0040c03c07540c054182c0259a45421604950920000c40d010b18014a000400f03900c90040820805c4218 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 948897257 1250 948896007 948896033
    0x709020c03130314060901230411121c03090209221515050904050715110a0b04022707050a140d05060102101103010909110a0810060e01080d0309 64
    0x1036603046103143e144c0c0b0700816140e07203951a20849101d1000007072111441440703801c6030200704502000c4226114001d4002100f0001d10494144c0300340541c00c102d54441105019100e942c960140c440c0358206085004900e500940c03020406003080101c4000d80ca030040640c1d005007000505e0680d2003140c16080011902c040130041111082048801a0501d07a81c060603040c002d01c18040f14507030b500c10801030006001c4d580074085401810081081d100c078601c07005035004d940d08242c203000c5c80096100e8105020103005490100a05040000714076020325504501d100044034100e144000c1d00c0441034850000f00244280640040c0f1125194000d40584001c0494100b550f55101d120952000c041c020580b41c0c180984610304240d06d090a0340d0040d4200d040651041c0703415686000c0c1f00c40d020344190041030710001500d036555682910303040c0b14640a80032100040c0303138280c08420302d601115155400048801880001409002001f15002a4410151802152114403404e012000542c8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 948898507 1250 948897257 948897277
    0xd020d0e060715110a0e0405061206150a08070603050118231f14010212091e1804050318031b040c030b0307080708011112070f02070306140105030d0c050709020c03 72
    0x2000c140040402d50080d00703228101000e48040c45140c40c9c64040c445100369600502015402400c0003404407407006c00c43c0ca00e51107006000d0b410040e82c803050a4140401c07601b2a000203a150b800601490400d5000707500d100d454140100000c0e0300aa1800c0c10030244030007100d4a80c50508086002400c00301a26040c0f10081d507100440165600200c0c404052180c4842d409800f0b006540101d0b250060706aa0829101070060090341213818503100c81885024001c9034442c409450520f545030002c0100307807287c0d01c650019581e40c2040240b8248010200c80e080d03220707a1000d610720400d000c41e03450443c1d00c0042540c1c003265580c80418142c5c003030400140f5554062284220000d02c900c1d000411004031103100d0020443c4507007032000444188294803500340840c010001184886100320100c010500d601e205903540c0076101da40d40415a0b4200464808411007400140050316042c0300c155080c2c030290030003100c070300010b5a03140e84609640c42212130469022920721503050307050040302c200c0c2c10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 948899757 1250 948898507 948898541
    0x9080c010f0c050328030b100e040b010504081606020f0a080f1c0e01021909120209060d0503070b0403260105060d110c0318060309030913060302120d020d0e060715 72
    0x10001845c090510004141c200000d080114030f02c124200107541d075a41c003519603101c07601c4010060600c00a0b0554284060401c18104400210282c0038400300c840042441e51207034280d460b1000003480c000486080b85140d0700b151200b0000a4112002c4440c861410842c20352150032036080440e21413071401c00305890b9418610040308202065009007056091840e90501d000d6458400300d03400c0d40f05000c1c00708464070403140e800152908183e01036000200402c3d90308290019580d55065170028401140d0703c02083c1e041c4801c058010403452802905803e04d001c0000710703051500d001040600c2124003d4200260456141e4410f030404520b00c001500e1480e0384008503151280c2d41d520456400000e5620341c4c09540d81031904030112030142203503000460030501e0110800c0849201e4010088a2590350703400000161101c204410b051550200904600040d070040030b4100320b4101002d0082103d0b15a00820f559104020f80b821590403400c680c0d803000340400c592005090450156141d04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 948901007 1250 948899757 948899797
    0x1110606100903021f08090c15070c050d0f030905090603030315120a0510050c0c0a06150f060e0907032715151d01060903080c0c06180109080c010f0c0503 68
    0xa403110b03030b558411541a80c48110b9a80c4170350170a41c03100e031011103c6600c114900d4030341d041c12703080001800c031a81c050551030403080c0c1d43d0400100c154000f40c2084400c60f20b107030341f28018542c120050500901042d25002d40a240000c0002e45030310004080e42d01d0045440a215200d0b01c031849107004030841242100d2000b6402d041807540c1e0410090301507d1035007860001440701c2c0041d82603034130851400c1c0080500305020340e0f94002600e85462070303041d000401d20780000c0c3d200d41d480e60503000b00003646032206054982c00a000555200030000e000b0300d410515158040c1c0304483c400e03060091668000d080300d07952860a90107082e00904981d9000c0d06002c10101c40c008003d404100b141c1941c040c17a03a0780910035010812907042445088007088413100204041003401004008605200d01510858a103003000220b03103401c41120343c2040000b0030242107041d42c018814102500005c0002c040907940100000d0101c0c4512a0090403c140e0003400c404100040042e640141a0a81c848010b2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 948902257 1250 948901007 948901039
    0x5030c0304050925050a11030a030b10080c03010902070303090507030b1012030906080a090c0f0906051f050a1709060604050a0c0206062107230111060610090302 71
    0xa82203809041e11508800010540d015000c050800003c02c900145044d0307074203640c134280c5080d080040403500744900201406005042800200031015075501c1c0024110402e400303000c481e100006030041402a4082440407400100042da41150314011000d680c80c002c902d01100a01840c01c4002c1c154420224007104205010316018446c0c4e00481e0081074095490a41e1800031842c504003501190520505102c11407103a45881d0348941082e6000c28048480e0744d91002d0014158003008010064078024010300c0c416000304001031908842c2c0000c12202ca106020b00c103207018480d10140440020921840c038042d90758058007403841148819649848160035842d440c00b01c2c3c040703114510b02000502916031511610401203440ea00030005552000140040d0324090741400401c2c50711034102080381c101c20801d290280c40100c41c2813a140c10340342811580c85000c030319454188201c58458912040d000101d075503100004440408200b1f114130429501c0d0b0746560400b80d0014110b060380000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 948903507 1250 948902257 948902263
    0x3060b0103091b061119020915061809010807140424090b100306030f0201080c0f04060c02031207050a06051f08060403110708030a1409060c070e1b0f0c0a05030c 71
    0x204c413019141c00c0c880c1280340c001d00d521880706010780d4039038404908203c001743c10700000b890307840b6100150340f0344401c002d0000141103801a60500e005442c25014032903003070a003002450300401102d0010b050181c100300540c18010041c1c881b0030701840d0b03140804038080e8062030450070400007100d4044011074903200000d01420a000e0b00c04c1c000c2242e0090250000d120344505011690042c00450302d07000340d58011a940c16019110310003410301807100b00200e4000300000d000400094454864204407803060504001000320303820b090390010f2004101051010501e030006990102c000103107540d412080d04c1075840b5080c0b01c20801c1c0c0e40040085021980002e620340070710302036110416000e0b12100410381c0c2d04840d00480000f9001840202e80e07050240520524030501c6082060034141c0c2800030541d207802000d1030740310359803149800300503002406000300d0700104c0206560541039170000c58010326210b070001914180400081030003c000c0140642d462040d80142500d0303854201c2c0e64002d81d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 948904757 1250 948903507 948903509
    0x70314071d09010c0801120b1302090a06050102061f121707030302090906030d1e0903200909030a0806010f0e041d070f140d05070807081501081603060b0103091b 71
    0x180c5503181126130b504070b90240804134101c1c0d030483c4089401008655840e050701c840509803c1c000c0c101100c070344005966252000f841000b0805000807240d01d801e00081c5003550140800e12002c4d400070350f4081950350307501840241d400c40c1e450280700300701a203080918076860300340b14010740101003012400c150745074004143c01a8110740607400c603103c40f82090780718000716092502050315011212459003c07201d403414241d0321810255142503490301c80c041840402011071300514501202d4071000d141405440f80c2000c0c0c020011814200d018401621281d03001d0035030744c18040c22080b025070140c840c0c524404807403c017a00500490030620549200a25502a1606a409125000300780c050046c81c080307040790000d40c108200c200803501405105169003c0c25100d9024895000c10030801c0ac106040c0209081e070001e03c4010080301d41c030484004103801000081e00640290400c4060744402d04080c0ca4004900281002006005078000d0410b0000144600305020140002c0182860034030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 948906007 1250 948904757 948904771
    0x54120a050f0c1f020604060b04090b010807081e070b090a090e010903110f030313020a05100203030403020706091401110f0a080d05060406060813060b0d050d0f02030309070314071d 79
    0xa4074000c83d03d00380c81403c1104071102c00040e403001c000100420380e190022442d21401500000e80010583c440b9841060240c02c400060740c4a080104041d100400c208515410210080078408071a540b0240d200d1f0300b24421185618004103000d0a503550710745502008007004c00003040345161082400d4041e01007100c06a0101d258244140703060702c0301164002d801c2d420b81c40a1842d6541b003500c5500d007194502c205030f03000f01004202103003030f4580038910002a8000d40046403645440c3c540286849056005142000102c0b10704010071204103400e806000030908120310140c0306040c480b403408290b0400c4040500c07600a54400f84003244d4002c10400c2d100701001c1c8074580c0c800b01072100b551082c0c0f240000145580340000e442c3c43d15240d030841002e01c51580852805080800079011a200c203030183c6080d0400c5812507809a0440c008144079802c1d4009582545058956541c40d100719110217050501d041070803d003460030502c540e20142480c11402102205406c0e0703440d0401a040f40d040e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 948907257 1250 948906007 948906019
    0x60d0204060e0a061d121006060203040905010b070f02091807060f0908060c090d1b06090e0f0621010603290c04030f031454120a050f0c 60
    0x202d0114840d40301c1d2011414621700c42119410071006210b60001754680d102c1c2e031801081020f101e20613617401343c0340041140354011501c2d503080c10b44c020211001a8020780c84403030704000b0b820000c1c4000c400c00513016011a081c00b42035603481c00900d60114880403005860082900214200d50030402030301085031281d0340c03002c0e100d480f0070307007945d4030b00c010b413038035607107040b09000d183c20034648544204d56a61050414400c1070b148868981e042401c2c41e0000e402003603580006201403071710f01c4981640301d1304001c000030060805201141440c0f40009070310000d00280380880131210300940141006540c840b02d80d503121a041c05040c5076044c4219a460b9191880d5008108006001c0781a84d0580f40c000940180480041ea01a00c055680142c5119121070611404400320712800030007058543c14920607080e031220452500343c2103802640e01e180b4240030401c0203d05140400c0843c000700e001d4070b150b540400d22215951030804011001403140c03150201984406c2004142680d4894066800c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 948908507 1250 948907257 948907259
    0x21804050105090112080c060108060a0c021915021e07020a0e0933090a06050901020a051b1c030b01031a0619030b060a0305190b060a030b060d0204060e0a 68
    0x2044140c03182841281c0d80140194010302011400b0452082c9103841100c0503441e0051842c41719050074400d80c4482c0181d0404420461180e4080c081c0c000d48425503c0545041094040d94201c0c0146500011f03002000210011100301d0081d811603641c0f480c440407414503082c41d088082410b5010141c124043c006050001030071244200410b0300480c141d02c0a060244140c88460b207a52075032040c0e00001c49007103188408504201101c0601401180c00a860328898900b003103401c0e60300c09008908182e1041010054880d400016202c07410000840d007100014010607440c680110b0005030649289140209151385405903c0582e0b5500e082e02c003844500d0362000400c0c84000949411a0440801c01c0109100c0f03c4888101c2e02408030740c00c0001e040e44031040170620320b821050110700407031365440c1803010712120303011446d0b00601511000e1096070946004a181401509400307401e05464141000c0710341d9800d030a070b40171001207507021511175940c6c2c4001456030000c41e11140c0203024480d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 948909757 1250 948908507 948908509
    0x30e1b010207421b020d06050c03060a061d01051b03033405030f04050708120703080c03040503041809150c0e0306151507020a031101110307020d03050a05090301050a0218 75
    0x3410f6484805207445005481c001c845220125203d801c0c412684402d0103401309000481e14030900f400307a4091820251a45030400078010500c501d078000c0410300c04817409644e502e8501c03059020081310203290071504d0700c020908100401284115400281c0004030404ca10b41c0f488502c11a1412944181040030500185011608088000188001640400000342c840d00e0041600340c10070700c01e60840703a003603940303030f0f00542000b541086804102c0800500d040605911481e2030f1b03005050703c041c82d40f0754207203030baa800eaa9101c1c0d485404441003c501c0780d11005105903202021880d04942400c2420010700001c00003840c00900070404070f28400060300c480d040028005101d101d4103140b258241440004010b05480c8030300300880d140004220040040c1c1f603840540e03005621525240e0015002d20b4000f500704904031241410b00c0c0e000344054000740e624140d040120036017600300700c0d40d1b4031a410001c603094071424502c03070742543c204000e220004009600500b0816030813500075a40c041f10b94 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 948911007 1250 948909757 948909869
    0x510090c14012016060e0406050306060f01030e030d0c0203070c1202010c0212070b0d020a020d05070b040b060a23040c030e1002210f0610030e1b010207 67
    0xd00018001a50040b104142107040340441c24203026403411242c15400740113440e184142d441d00308a000620380e1200d10128106400b802014260480c090b002e82e140160102d0b00f020b105003c40c03410191114811102c09205000b114409864110140841070049002a41c0ca910154044484d004c0503a4005403515510300743e80780e8181d05940710b852034004c1d9000c005400f00c0440000505000d4580d0000303001100c08004d040c1020a0040961104050b03200a8280185102d1030400d0000400000001401000116500680c8030a8030007103904c1d20400b096441c5090b07002401c899203140340052103560010002e40c480c10044805105c0010b401c68120701b51a101950303c0020b51107070740c1d03040c840308254003d05069540c20300e00107801c691218104030005401d40b20460086820004c1c08030310700f070613019000800d09c1c2d801e060003019000c0c042907541342c480f01740401442c0382c20b0000c40d0381a0310030301640d0002c003211050740d010003d2402c40301015a02c6088283d620080911250110b01012 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 948912257 1250 948911007 948911039
    0x12072901232d0d0f0b0a0b0d0303020d06050901081509010e0714031009260310140a031203020901020601080f0a03080a02090a1401081e01050f0402070510090c 70
    0x10340304515a401c45000d801d0b04401c0007080a010b544100024003007030329041c0740ca00c000c0307028444500e4052498246401e85031005486118414206040d80c03484c0e80351540c494190690501d00165a0201807101c100244110b0b00580d034428480c10000404203400544803d0041c2e030001e481700c00e0b80f140107246080340d07107203104403040360400142008071031001072160103038040140541d600440807020b00d10444401110840742113000c081c80940712134030401e5881c83d0085517500700d49141001002244003031007034410054840c1941c04c40508680f201907081c4000d41c0d002c00b0491100c1c001078805400713500f04101c4180180300e003074000910088001a5070700c40080000140180c55030549003100c48080003012003e64580070070855a41d5260312410b40010b05c03d5035a00b0a9038440d40c00018409030b4007030028a10340d40251105c10405c00341e0044281120b004454541d060420107003c14064080c140c40034080340100d50141c1f001e01119004503c00da03115210101e90261201c00c859000c04217 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 948913507 1250 948912257 948912259
    0x7030e01060e0a15090c05070506070c02060405040c0224221a06150f030f071d060c0a15090201080702150c0703090302041b031b021207290123 63
    0x34580100d450907034a64845142404004e0b641d4400d10b482d8520760f02a28049182ca4001480c00a846402e00800780070b60f913040300301c0740f41a281d0601c440c2c00242540c0224000c4520a40e540c800281c42c0e030f4001c000550040d007174501c20010440130032008820111b012600f8082c9165200c4050450700854041203000e21391000d942a0a40480808080642802003500d41c00060070041101304240e1f40c00503003c8c420b80400c80c680e881c40c0c45601a45da03c2c4c07000c0e040005008416a8044581441c0150600c07255030980c1c407561030b000e00c0001a0320b480000003014010041900ca40c0c000f050307982d04812a110b000b030700d81c601103480e40c000403a5103500410b85009850402004210f01000c00e40c02402220b000e4038051181c192280c0018040742c0f40d00e0320481d0781440c5200384025540e05400f42d0030706196402180368400c04101c601940300d0030309900c004c54001c0d002403410208680221400300042c011980d130040c0740c191800c00389003980280140803101584181502c10409403c01d4000d0f0408 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 948914757 1250 948913507 948913529
    0x109050c0c06040b0403030605032a04091509021507110f100f08040201022103090c04110405130603080c0f1204030f08031317180901030b131b0303030507030e0106 72
    0x91103444d81021078002620803420180c8440002407265800c0011850648a049410316010190004200c018008a42d00c501441c01c1c240003601003a100c079001c10503001d2291000c160211284001415403015095940004101007014000d20514103049286058203590196030202070804000c40a1a0b900c042c1001800350031010a2a40c813455100f5002803041c011210a48604541d0800c258195400c00200000100412007132030f004000e0840c41ca40149d0b010000181c07107107481e038014802c034002d00e0300440040b80a01c60700e000560121004540042c0d071030b5100e02d09081c1c0140c03a40c03001030320280581316000b40d8019807000d0718121b80c00c072a4031400400303088200342e84219a9801c01440034511010388018540441c0114100942c0d034440da486c4980d850000401c0450000c01600300d01d0300602a82006000080711402415042501003010841c0e600080c50044110411103003003004904046000008140d05500503e014000585081c0064a156100103088550501c10708400c48 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 948916007 1250 948914757 948914761
    0x106030e071d0126150604050709230a0302030106031b0605030c040312051308010501080717071710020f180301020306090402120c1e010f090f090f230109050c0c06 72
    0x4180c601c46504c0007940341d4420900c4010b10600117040240f091a028a000c01c0801006100d242c00d104040d40840d542c10b005000c4c078100076100b080e040f44c002c84161220030781110340c3e02036039601150300020b6034002c0090100345d4881c600f20304540092810072104a600103070106035079020b242034900c6000e52010039420103245448110780c4c0340e111070f02d080030300400f008900c03104400c1ca00e192000d80804070012070a035140042c3d052030083c082e032100c01083c192010130300c4c500d0008501c2404541021400e00c000100c2900c43c0d504201102c204040703010b100050b44c1c24416a001c02900760031981d440c0d186030b83e45c64442410b0903440111101d5a2105400300002e0051801900c05202241132100b150035412032440815942c4400c42c074031843d800044d90071000d403985d0040328007024105600e425190b40e4940012000604c0d031901600384120707200c51a003900c81034190302503401c4102c2022000b46200d9a6089806808000c0c002c900803941800c0028451440d00c000312824250a90000e200301e07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 948917257 1250 948916007 948916019
    0xf0507030614090a0b06060f07050a050601150215060303040b0c0c10030c020d1202040b0f0306100906080f13061a01121503150b03060408130602010504020f09040611030106030e071d01 81
    0x117400020481540103405012170003580c142d440150400510410040c00400101d041451411205a000b0350381c5441400e0265032895011824641103141802a00825215000086d041d0f024a400c0144151000b28410002203800104807625501c2640d41615895004c102203081d00e50f070201d007a0250341f001035001d017814460400e2200000714010014107240c1c803104c031f0300c0e01940320340c0c01925042804000d125143c9001050402c0c2000b203428500542c034035010028184240081014201e0001d1100040444021401d441c4142d60b02c00c1c0208644e14400c040c1c147e00c40d054400443c0045e00c007034009940d040140c851440a4000581000300c070a01d548e0b600c41d01c0c1d040503030804e4141034440c0c4419929480030496030b4000c0f442541c0041d281d044424050181c014154058000c5a041100780005600c2e402c01440120b01c0c2601c0b4400687c0d11070401c400980b82d010341b00741200400000000d03403070303a1590140c04044103100a4800080d41d8155403120080000d8400d000000d540004100c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 948918507 1250 948917257 948917273
    0x60c0914030d1707030b120705031504110d0f080409061706010305030d0e0c0324130c0b0c0316030203030901140c030105010c0f06020403030507020f010314220f0507030614090a 78
    0xc44084c502d400b10300022000089140441c0c0d01c01d0362966a4050003041c807181c40c09002441c101c01401c0c0341520a490070361100700070304c010780708254003501c07403502003c0038404c4e00d0182c400150f400000c0c0325600ca6886200c0310080805100780c4001003225050208084004144241280c0d04200110304160014134400000c05200f5a0110a031082100c008007a4906011180b913403401040040c4203014500301e4803d60b604d0040500300d0004c41d820032070000803c00080881640c212590180d111410a05400d10b1481182135a066014041e8251000c1590000003584070b010210001e109585801984442a050945410607164000e00043c8000e5210312615203009004242d551014a61070b22790008903400780c0c100742c00003040003508200f0741c1030502030a003c1000c00e01e000c00a0134070b9020030561111029100250401c9031002c8248081320714142c07000d980d50016030345140798206180c17542d0b64109520085030740c075048c04000d80c1514103122942d40301d00c404c4d802400203003105030f4503290 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 948919757 1250 948918507 948918511
    0xf030e07091a150316180b030703020f072003070617040c170322180e0c040f1a03010e03030a0f0612050d020c041112090109060c0914030d17 62
    0x6880000b200450715640b25a40c078a03460307400c801c905503030f4103003007828103241c1d024089100d09100c0c004101c440e00d210f50b0f21074501100c0f24900c0303a40d2281ca600100303c020b40314041c000e01450402041c140d00b4003810398801c064070f4086072440c0e200500203070181500c61415110340c0e8082201c0001d00d400f401400f002c0ea40d8447d1040320010104c0b500c03001c900c0400c2c403010f41d201d0001c0e407000c507028010305e9001030559944ca80c80716145040c00c2c5841610016003c01851011b41191602150308020b8010041251001b900030400d014003a420040c020042c0204e00380481904112070011485040c1032040c10110440381010314034668480807040042c0110b002c21505440d13862400142139641041e051018901c10400703400c1e45110300b48004d20700124105a20b2160381f400140c0390648250504590780f102038103010380d03615039031001402c4c01000c2403080509040d051551a180a9910404440540b4141c83c1031801c1700350000c00f4995200d207051410400300b1290640c504000401980e469 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 948920863 1106 948919757 948919781
    0x130f06020c010c0c06120902060a0e0406092c0a0c0e071112090d0303060e042607050a0809040e0a061d121801020a080711010f030e0709 60
    0x1104c0c0541d0b20894080c0030542000100c0f51030aa0040c5044c260020038080d00c962a2080c06050262042001741c4514075100000c101c042451080c10100a5145440e400711047d41d40a1050b80050041d192020b05c1a820350380001120743c035025021f4040341200b407009041032035019150701036080340d102c940c1d000710a802402941031001c1d60140c09040300d103d18aa0140e05040d401012103401540040002d80104000d20501c080907070701811071041c0441c541c0704003202c129450f0145050060840d0480207581022403152400781c1102d000c014000070740f24610004503468000100d4088030210740b144070034502d0f07401560b2400c003e041d092002d041416403d01e5131103804e1007514911624045505d00c0400e06034420400710901e6503120041558802050401c4502c40700c2100d510381c002004503140d500000e20900454107561000301c0104505420701c040038005e40f000207811 = true := by decide +kernel

theorem cover : BRFrame.Cov 948741007 948920863 := by
  have h0 := BRFrame.cov_init 948741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 948741007 ≤ n) (h2 : n < 948920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
