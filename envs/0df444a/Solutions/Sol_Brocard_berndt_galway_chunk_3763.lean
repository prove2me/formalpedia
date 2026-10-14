-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3763
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:36:12.5031+00:00
-- url     : https://prove2.me/submissions/58158757-7846-4c4a-8502-a3ba2cbfed3d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 676618705 ≤ n < 676798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 676619955 1250 676618705 676618727
    0x3031505031b01020f1902010216140d02190315110f090d03050c01060602061e07140c07091d010b030a080d180b160905030106030f060f1d010912 64
    0x115401c80e40030300c0b80c0c500b192014690b42000600540c0e041e40d03c0b14201130b04100c01608402c03000c800e0b0211320421503905001c125090001c01248108050501040400359250082442d0049040d0b6812106640d100c5c001810b483d407160542519498481c0381c0750203c1450340c0c00345040e440c1400007200140144078103813900501414203240c145040602045608074403070600346c003841420400f8402c00f44082c080c0a01400300707030700100240d0610107031400c0d9a644800c0001d201a0012007400709060384014008803401c1e104080e075031195000c02c0d8450070001c80740d01101c407091415550705550342d00241c108465003442c200030801d40d0180401d268444980d600001e003094020804210410100d42c01142c01c681d10004400e4050200d90300c401100105a4401c0c10340d4454030704510000d9441004203014200540c020300c021483c6a6a6640800d1403500040c841904c4041212041949500c04890608003900d0503050303010040c0304030f00a0100300001d4505070002d180c084c5040d4050740301c103c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 676621205 1250 676619955 676619959
    0x10b010c080304060906062c0a06050f150f12040c0503030a020a03140715020c010c020c06070222020307110f010b06030109051302130e060916032d030c03031505 71
    0x1c41c50f0307515510a0001c02645070304a400c1c079954640824402d40322284091101005c100328030810850001d2588820401401c2e24100380c01d00030140660388039210b4020324080b05840c0321b11300d4882f83d03400c501d441c00342e844c202900f0030002c200989014000d01030341d40224010905d0b42c000c6030721041816240e1265600c18030160340990b40d448000b92180c00c00504040c280034555040c1170640d6540c1d58500c03001d5410800f07064002c1100c00140f0800c2c402c4403d1590980010120b050110004c1501400707030200203032040c80360319405001c642340c42031740640c85c801400c3c0443d907a19151f100588416003140c6044041e208a000d40074620a0501ca0301546540060507070341503a02e8945280007400d0010103007950183d8000d4940016100d200e2114040d406030b41e00480c01c1c011024032240b90580040c00c08266902240c00919180c500c10503000642e5046690000a00e203110000700300c80d081c00c040790b8408080130701440d0905502c585034001c210f100e5607043c00400702504030b42441380641d0086607 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 676622455 1250 676621205 676621207
    0xf0d1a070225060905060c0f013303030801060e0a030b09060f0a020f071401020706051017070e06010c050a080304050115120309050f0f06180f010807080a2c07050102010b010c08 78
    0xf20041c031b070540c00350800301d00810445105e900201d10090a540580740214100808500381894400c0c00100139041c81e11900719411350703107103562070040001c5410710602c0c0601c20030000c503e41c951150310001025540140144480381403020340196501130498899140c40c0718100420b02d100c00c0c034000c0b134050642c1c074506e02c2e003000e17090707140c0c801048050741002e000ca42d0708102045c0091600c1c050244500081010080701918082441d0290044d6841201c041e40098106120ba001d2a001c1c3c5c9030812420f01e85400c00000624180345440340d20000038001c0d82000c42080b080000541200f80080f4600c0126011710360303a501c00c114202d9001ca0018042004900c007442036081408985814035402410b5900342490304021801c0c9502101e019800060b0302890b200c840d00301078040c00f0210700f0038078005086152075500141185030150520f4080c4d034642940302443d020903000d544c000c445008008a5544941110554440302817140601650078060300c25055070041c0ea0a400440c0c210001c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 676623705 1250 676622455 676622459
    0x130b25050c280519020f0111030d0203060f0303280e01020a021003022203061a061602060d02210903040807031b0906030b040605150f0d1a0702250609 66
    0xc1d0040c01200034621488541c02d00b444070104000701320720b1105201c100c4440030b000c4503500501144802c9005c880d4144814016103030354a100010454100c180b06280060b2262624400501014100b5201a9040c440400c0703c91400e5158608812408080f0601070701c41102000c040d500707480d01030102c9000d81c022012000150404203070380d4541d00f500e458014074004d050782003c0d95401d001c40c03410741c208440940900400c5858443d00d94400c0c103043c55031104000e12000a00f0a210300302c0e8860014202d02ca4071801c64440806a8030400c1103280190340340c030400c0f0784584440200702d415403017840d070761404154202808400c0300c0c1690710a00190600c00c1c110740300c0040569605000407250041e03128005102c41082c420301010314031070410001c207400c1608002041d20400303483d80e1070804c840003d8040980c0d4600c1040d10340741043d0f076040700c80c211900380314401e0909030341c00760b1845800c41e042241a81c2c1c041400c840c01c03066009034038451403442d002c001e08860346009250101d0001001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 676624955 1250 676623705 676623733
    0x406110c0f040c09090608070603060801020301080d0f090302270a06031502090f03060708070807050c07031103190c150c051509390303160803130b25050c 68
    0x100c24944003c42c1000f00107299200310100464440d81d1110040c0d070001c1106008640d410b008003401000c00c24000c1d4115410310001c0354a03220808030040c180f204401c03403000d107240110350607002035400030301a400c0100307131415002c200c1170203410000c45034031503e002424182e481e10585003620340096441c060300380c403a0aa07a0080d4040035400e603001d40708c00c000c40c00d20740e81041014414810340d9142d03021814111000b41c031018002d44034009006041c40300d81e032080c400041002c00c0f41d40040039041c00c00c6106000c030381401c49011943c0c0298070514000d0b401e0004000e400d00c01ca500003088000041c0783c980c8216880310008200500325082644c42e600c070b441142d00000d811406800a8038980d400c01c40511800a02800c0c410700300450b445201e00443c8500b18000102010a401942c580300103c907801f90200d407030030700c0205503030008004a50005140041403901a0340440c103208141848030031009558a9001801d4188143c805030120441c440d00950301c0b94a01800101990801d80304 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 676626205 1250 676624955 676624961
    0x1020a0f18090e010213210204051b0a17090a0b010e042a03020415061211130311091f210b0106030b0a0b0c03160609020a0b0406110c0f04 61
    0x880282041c8044004118002a4428004603801e50350006954040750001d01c130401c40300e40c2c0b0500e41008120700700111601a6200090400d034100c1d0000b500d03a0b2400400300b200100ba079200c01d02a40c0100304101c6d0140c2210003101c0040070284040120340d10704407115a070b0142080020709150040f80100035801c0c140185a800500c9040550f941202031268500040b195a40315140908820820415070500d032081d5014103c00d8610200c0306828040050200c01100ba1400300300e56a03100644690740d044d82c251503040c0400091000301c1a83e80c11702c608894419610144030b40d2410010644910000c070201141070300c403021700c2e01c81616180c068100b22401071820002403105201010000702e4074440c2c41c7c042d007501d071000034511302d2550500c0604007040d000740f80044001c1241140d000d50010a48031120600c4100c4003460800d071811401070704203500c0003074001410700804200c80c3e40030001380094440d2950b070880102c2880f169240d56641d50524a9001641030000720a1400e0a030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 676627455 1250 676626205 676626227
    0xc0a080105011211042d0623090603070b04060f11010216080c03090402120103050114040b0a09030509040e010c110c090708060609031c17010e010b031f0e0403030e01020a0f 76
    0x11700001e211810407441d00d12807192882d40540303103550100810180d908601c02d40703018100c00040c0844411109814210380000003142c5845041d1040001300d1554042002101500d040300303849031202e41c1c442000e4070300d81c03d000d0f1960219071750041b00c01860405100340e90500d4594502c2c082c41c190203481d0340b4060361104c000b245050100f00b143c800151134500003058205040c2c40034890541c9035040007401c40b1100ca0b40f81c00010401030504c070128101403580c50b042030b4100000254180503140541d094422520ba0b10741140c148904030600c61410f41c041008c203ca1903c07219280383c0540100340e180e03a0090000366006810700003081e0103600c108001903020fa00540b019181080210000c2e103050608940306866289a20058030340c2580040140c0b607480070420b0180e02035042110780c015003231050080c616440700100003c1c185811200c1c110941c1c602054004c4020ba0b02c8001603130488c0022141540440e003002c000440c400f0052085840740c40107551544d4000c841410704807080c0b0408 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 676628705 1250 676627455 676627459
    0x509120f0c06010f05100f0e102a0308090f1203073b0d020f0409080f16030212040b0a0315150509041409070b0c0a0c03050c0a080105011211 62
    0x244290961928108151406410b035401900b40c580d00e0501046128030031b4005c01c80400c09030009190499030808240c840000f000c50300b8650400c401c50301214000040d0711601060181b01c207264000d908980c9903c11698043c4d6100e00c40d135031b01e949401c0c4d03507035044031a81105030b8081c00c1c4618800d961403003d590890000d241083c510740c00e034440320451040c5076961001e20880e0350070b00742c003901c103038400c40c503110405a558400e01c2c0896000900b607505c20001c0c140c003c039141c11541c802c2000b030004840002000c6c1d40c04a032036424041c80c0a10b0000940812805446541481007200210005440c2203c1442c22118035100b00c11404030302600c0d1440c1e59403040d008c0c10002042442609490a030394201d0f5654140c2c6905088007000103131140303003145002c001c040c00240415070f8004150707607043d18008411240d50f08101c100440c50300250351005046480060400710804c41c010821807010901200c0c04031241e42c40d80d104c6800c0711400e00c1103501075a0018210000204800d0000003180c2c40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 676629955 1250 676628705 676628707
    0x20307080c03073b191a07020405090f0105090a0f06200c0114150a0501050a09050307030b01050f0108091905070b03010b0405120601060e120a1a06040b0102010509120f 74
    0x2018014072100010700c003200603404d54000c201d6000c00c07104c000b00545403000f1211400b03013910340e81107002d03130248500800e41015080200011501804411201007c2d4042d10800051034594805501d030740c02c603050000c4c0c650078200440c2125400081e405501750b04250751090480300381d40c402000b05203d240b114410985a03030655042e44c8500701415075468280004680408900b00c0da03060741000800c070380044c00c0d048440b105030351203031810030b81980c000307007443d0303540c1c080c04501a122080c00d41e0140384c0c1803003030040210422400e82c803010b048480a8607030040342ca03450b60040d1901308003110980419885010580d14508400d4010700c034050090040d164106c1d2626a0300d900c681c002d030000030b801c0a00050401003810030380e100503016160a000381c55594180310008010342c5d502c100b00c5106441000450700992818412840d101e40d004102038810071840e541100844d00884802d8481d526102003414613500600509109102d8070340600300008550004900c96002070b4100105c0e510 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 676631205 1250 676629955 676629977
    0x50910050f310e06040522030f020c1801030602090a080f0a030806040e100b0103140f010e0108030717030601050c1f1b02070b07321b210c03010603030e040609020307080c0307 77
    0x7030180c0c3d6107d60300740a6550030794015000c12001c1e00d800c0300103081d50300440c101414100320b0303000b41c490181074036403050015a1350310282c000a00040a50741010b12240245003004011141c006203405225210f501c80c000290303142030401084410390b000c11055034000164180242556901052081005040010b01d840c100d08030b440d036008048901e03010240303000e80148002155525024010051a0004d510700a4681c0c0ca2070b0341064105103e4002502c00f1020030440d0380030b24203407441c40320300c3d4045580e101141d030744c030b5480c148203e45040c102c00d290114420068044950b011a07001c00e42d001030035054034044d85903445d0b610480050b036045081034817422800e100419401e8641004003410f10301200404a018105019030480036600f80095144101a89441004808205030307100503100c0704000020050428145020890740755107816000b0007019040038950301200c40c1500c080001c107403281d001208070720017a200d47c00031034500400258015000002550700c00b4240c68031040c202 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 676632455 1250 676631205 676631251
    0x10080912040e09190c0e0c04050907020610141c08090316090b040c080c0c0a0506130c050f0303030c0c15071d030d050910050f310e060405 61
    0x1d085a0441c05290320000c05000300141c0802101c00c0b42c94961259482c80c10440c0d84000d13200900c1c0c400d0700001e62420000496142d40081613030000d0202910080c02413074980b800a44030303502120013032a000400003000c0345030414640103114030f0101400d01303590110310000f42c2d85001744054003282e80300c50800c807603012130f10706025041d6900b02304c0820300002c50030450039400352850000054003c61800300c210b03908560240000d504080e10341d0002d80d1390a012440c050418601d0400074140c1d119507000d100194081c0c4014500310750151048040030398942007000701094030a0803480c0e05900034008568050410b0009004090428041304d501e4980220003010b44e4600701c46e01e130045084403202c11017105080401c81d0440000b1005481c1c004003480010b412802804111b45c0619580c8a40c004110700136000c07036000810042c5000c1e116050380d00704000490014034403a02c58100d0541c2c000c0c403001d11000c090280e45903180e58080c41d0303807441c0c10f10004120041c40ca00d1445400300442d2050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 676633705 1250 676632455 676632457
    0x2601090e011508030c06071d0904050c040920010309080904020c0a0f1a150a060305100e0c0304120f0203030411010903120305040507120302060402090703060b0408010e060a050610080912 82
    0x10701c2403801864840201134822030411400808101c14841c5c91582d0724a9284844101c9403581c204568000743c0d4ac40310300344945400c01004071a81c01c1403802401006110200c070100115800c5041c040498075458801101594400c5000400189060100c4079203403601e60082c0043c2401c03181240d01201503900d8004443d01e807082c1c02e80300b12400c496205a0b001130549400c0d44160442c04808680c00050701080403046203124500405548001241c0e1840c42101740b0001085c2d0340100e083c0d1814100703c241165407040e142194014841039001c1c0215000321340c190f13424602a000f0314295961604c403802c0c111542c4140b03074100302210001100242c00030110143c07107203c5a4002440d85010300c0c05d1480e01c42241c02104c11a0310100c40000025800140c55502c160705903004892500e0750035081c0c0c0508074a4006805445001c0f0b000305881030158030481400c0d110404a541c0c076216008035204540e001c0e0343c0d554101c6041031810201d54042c0000e030780c000800804550500700564010211 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 676634955 1250 676633705 676633709
    0xb0402150a09050a0f080c0d0c1502010f0b0405100b031b04150f0e0607030c05010213030b10050f010e040504050c0a080d270513020c030304030305072601090e0115 72
    0x441c0c11102c0900180c14455085400b0f4203540d000d400b500c600b443e0000303558204464003d072241ca0303200d01c3c1f0404c00040c0030654008000d1000312000081403588043e019041c0c680e031080b460f42c074141c1111258a4207004860203005441c685603405400c0c04240b480759480101510400c0b200001414134400c1b00100500c024542e1901d41507d85e61300038001842596519000310401ca0100b0340b9a0141ea100c0044518040e458104201c40352858034000d03002e0f0080c0221030004a200c101d0020a04c800500003900ca014421010020746403544108200b5815a10b1200d001a14040e80241141800e80c01281c0141c0100c0448254035840b40000783d0900f0345800041c5150841085101c2c1150400d541864055101c11401030003038207602000000c0780d030751084a01c03401c4101c5c01c0c080806d11a9040780c44034201281500c1d075903c0d060078068054982a0360314400034011403d05001c800210300720780710390317000c44c1d9094a0f96440c00e200700020f854904c030641c9031340d583c0300710021403400d01441e0040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 676636205 1250 676634955 676634957
    0xa090c03060c110a0c12020a1d060a09060803040506030403110a030e0a0b03010e1f03060501030f02120a03020a020906010e060403120905030a05070603021303150f050718030b0402150a 81
    0x1400b00c03041540200340c00340c6800465120340c840f0052000091074000020242c52403071101181e442c4513400000d5010100e584100781c650094803065111314221900c061242801f560180b00d47c581d940580d81c11600c0501c910390341a00180414049403030a20020358025020f0700d0a424101045848241025044c1c03a003180071a4115810b190380d41010000720340200308c040030071400c40d8508a008015040020800e07000c40c08510782042514000f0200407010b90341124080140e90384030300d071047d04260100c409a2280040203142e50031b0030000510712040ea0345c150b0240544a500303a0038082d0110005d03024350b0620400740484240c036120500a080118001c2c111400460f4030008050003400d03141d00818003a03003285a0b0200400c40c0024410201d541034a00143c0e1120303044842a461202d50700001d10707642c0f10421407000a103003500004400c60300c018040009880c0c0c032009542440400740d48040d01c00b004c41040001c81d0304541d006a00030700192000204044010180710160b1102070014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 676637455 1250 676636205 676636211
    0x41b03051909170a02030712050715060311040902030c100c060e0712200a03060f2f0f040b120f011a07150b130902040b18040305030a090c0306 63
    0x100300d0301c254060a105412a00804129080641d1a1258081e65003141012800c00003e0200d81d0075108104841c18107405c2510b98990020b01e0400074820303404005c044e50203100340c0c85030402c14241480350604803035000444100354400d200c2400060201544c050745c0c58040c0003285071498450384000c1d0480101940c0e8a45e0804040c54004202d43c50b841209107243d00001052156440c41500502c0080d00104a4807008080705040c1e9444030f04035003415003200440d000001006050307041800e002103484d50a102100d425600b910509120416080c0c00166500901d0a03410100c0000c0c2035511981101c149480e40799100000143d0186000d41401c1d1f00302c404000030649079841c880c1c090120302d04cd0a0b45a5010340c0c40400c6409403040c040e050441c8844091b00c100303210b9000c0c8241401c003900744819000c420b4000b500900d004002640613074104a10640780c0c3c50004801002c41c0350070040c00660362610b0301c08036002e4000400c09041c1d0345e943c14140b004142e640044100540c8a02c07004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 676638705 1250 676637455 676637461
    0xb03010501092313032001150e07080f0a09020406050306011e0611030a08070c020d1202010e0102031b03041511040303090b1809100902071109010b1206040b041b0305 73
    0x41503030103011020f5482c0c8a00e01c02800f6544502c0034161000c1501807502c1a0039681707085031000304601310760500307007103600e8102d642040d082c0355552203003100c80001800010356100318084d221034034100d442c5850040c0400c0024030040442e071015100318000392000403031a071100c01107480c00c8402c2e0081d486d400101c07180700c440003100c1200170740641002d10784503001a01c4003614503034038010740003968140f1250340001405288507504940b4060703002022040c011880d4100f40c000044009000d200650800c58501c8200740c050080341e0142103852250324900c10725084890140e0409041283d400c05468486042d42e01280241d401d0200f500341450b0b030b55403440c50082c0121000e9071125480450a11400c08040d4034015002d125020580321b5008030742d03514150f40d6200302d040c2c1100040382c0c80495154113011030140e0400001805480709801c0341d03200c103203440f8107008811000c045200c0c070100040710b03030400f6000103102d03402c00b0700049001900d010340605400c0420405c000007a070340b4410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 676639955 1250 676638705 676638731
    0xf04091a15040b1b06040b09010510080a081308030a050c0c0d0305070f06020d09060608070803070507090f020702060417060c040803074d04020f040909020102010b0301050109 77
    0x40580303112411105514440d815400e5036041d03000b03e10a101d0051408140c4158401c40646403000b00300d0100141da660345458600080d00341d000381c99190180d80b0307040c002001da800e289412800e46040c40014454000305944522846c0d020b1080714010600540340051482c07802c001034030300e4903159200d041d101e0614442c0e0500e0b1003c3c14000501c40c0403003041c1c0e0004a0341140446a81030740203480440004461308010000c1c0c03040f080132400e068644403120050140c031364054001d42c3e000105544480f036451030810340d28007c1d0b60014102c2d40011008200503001c0703500100d40344291480260401c0c40039000641d06402035400a49110000c0740d00f44e013090340500502e80e0040c0741c6800d0b54101410300080d01e68901a03148014225040d0070035120b06a4501d000034000d070101c010a0038030301d50b02a40e0350b03d4203043d61194000003032145c810042c25032415000391004080c4402c000c81c2010300e0208a44003a0600c2c80741a03055550740c0500c40301e641c40a0140c0b80c040d20700ac42020800103450f501e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 676641205 1250 676639955 676639991
    0x604120201140f0a020915040f08060a1b080405011503080309010506030f2817071a04050c15280f0207080607031508070303090e071805150f0409 64
    0x2080b861034800c990400290f040c003c800240c011140f03140068a942c0304802041e512420401100300520010400040c20305010030850306584030f4506903105030702e81e0b000540aa60b01d00345070130850720708450708844491140c5021584507000f80c0011400c2c2000901500c2d0100464100341d9294000000300240101300340a099000801500180301c0840301800043d1280514001040442034a001e44040c5200d10400c04042c3c0360032418190110384000c0c4c00070307142d0384000e404a98840d0800c65811101b51460320081c45250460050548448a01c003002094444a4012020f98000340507025068a415080b0810b841480a55100014221001800781018483c1340c104540c4404014007201401103152900083c450402252403001d0407103003880303040d07136030090840c620486000000307065010300d04404036001c440006c501500c404800300d401c1c0382c59a03560240008400410819410003003006840000c080c080342d030500f40407003541010350340729a1281100f240c6030b0b0311007080d0004040d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 676642455 1250 676641205 676641221
    0x2130e010203040c061e14090a1d0105060a1d040f0c020105060f0f18091e010b0a0906121401020903030705011b0f120c050906040603091b06050702061b0604120201 72
    0x1042043c132000500d0645806c0c0304440710040308000902d401d044400070700b941960285c240041c0034000e40c94a0310740f440704410038a420100e0301c0101c18000074150a00074100d5490035010390303c100700300d042180388100704542d504496420559a0070b041040040d40c1c8115000c0d0f0b0b1a550011659003081c030308005060741c0303031000f03903100b6a0300e10000070b415526a4202d40d00a1145800b2113400d41c1c4000c0c40c2800c0c00a02d00c40e81a031004188c42610098106502544250808994030008961904d055201304c4851f400346142e20f415031301051012400074011200c0340c01000c00050f01e80902d103004681550002d01d03040b540e80e034480d10720410f8418100b800c003413075900614100f443c0218410008108400e00e202c0e1204441e40d8181c4211001d10650840c1d21464004e40810f640e0360380e8100c021300505c5010425981c441d0700c100260520008181c00703004542041d41c403030341010081d400708040f0f44c0c4018044584400590a500c11150060020f24400d50090407542d000701d01d81100a400e440c138035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 676643705 1250 676642455 676642457
    0xa021c050310050a0b0d0b04110c032101031707110411120a02030402030715020c0a060e040506040903050d0b060d0903020d12090b160302280e010503090a0b0402130e010203040c06 79
    0x44d03405000121900040d25280d8014800114070003111034007040041c4820004050303030032000a11029110710000040030060040840d004100c8003e0424480c0740600303010003040151540030030380030001d801c0c02a0a41602800744c8c640c9404814000804030382e05090304602c1d0801c003060301d00003110300704000d6501880b0808154994541540001c0d00c640c0c03036006107100000760b00c0340c00640c3c1d8400c019500c00403202038404c0000c1a229038001e454418000394151095040100048040c01c0c00e02803101801d92585445040c01002c02c0703080c000d80554584031350040f81c02d01400450b0b524900542c80168000e801034950034980101c010440c00702d4128030b00d02c40b400c2c403032154001a01c000a1030703880360008080150741c21175a4012030291168480000300b803607140c01e8a80040342e0690800d0090405615142c058120740d034019211400304442c00710268004005500101d05a4002141c0c82840280b5008e422403c01e91800103c580480c4078400d140e5020040004101c80d00095070f020b0551 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 676644955 1250 676643705 676643719
    0x40501030f0210090909030203070c051c0b0601030908180a210303020a1e20070b030115020313080303012c13060605043306080c0a021c05031005 64
    0x540d250031070302104054000340100500c41c10301000900c1251903201424100348103004030354950074004d41d29040340c0c0044c1c0e602804000c0004031850070350b1282c0b2a1480c0703111804100b01d400e880d140c06414005000358141511040750000040aa0004291030030b2822500d80540c0f6101052105c0031400b0b411052101e603011440c030007a010301d42140c4c4050390380b43c40d0150369805010011100c42407070101412240520040301c51030030b50464280d00e8142e00c2c00300741040c2c402030300102e03a5594203644141802c0030800c00051040e510440e100280894403401200d01e000c03940c160b1400c0303011301c56100700c13626040400140b140c1c04506882404030700c5038407138070f251064005a1a8a00c040f000d4510512002003c584500700501904040d000302401042048540030107055101c8080c0304a1500180304203401214030903029400042080e1440760340c508480740d485825425403035010b16000300a6104d00c0a01d480e0b54506511520b030b8049541c1d80d000d440b810032401c043c440740000d4010301e00c1160 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 676646205 1250 676644955 676644959
    0x70c08010b1c06090f0f0201080f190e0f061f08150105191505120a060815071101020f0d0b0301060812160f0317010806150424090605030705040501 65
    0x1071200800400320305080704480c6000382d280f51602c0140002d65005010b904180c104406000c507940304030610900030b0b00e0b584080d55840864966114003210310110001000d08403000082e010b07400b150340c200000040b904030b03002c039180c0c4034503205044510b054010112800f540d080e40c14880c41400502a9000500000181268000e0220414002c0314040c110038031402005141c1002e10704c0c020b02c0d2400c3c05420040c1c0122008045620650380454003514034004998907404911440d011030758080083c0c0707078400900480c1200402e0180c4039000304041c0d6220702031460002c0c40282641401c501400307a4030030752810010207640e044d444061181e450000204000c23070020425a02648070201110ba03203554001d07414401000c0360f040507203240d1080c80301c1400c040d00062210300905104640000300e0ba603400900b039903001c0840d00d01c00801e2000340c2c0f44400b4140743e0000300c000011801d510303040c143d0760489518040c06c1540f02030030240c0c82c0d0000b00110300b0f041c041e05010385010b5500344038a41c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 676647455 1250 676646205 676646209
    0x60402100c150c0c060c0f0905010e0d060509150f15010f02060723030f01050108090715260f040c080c09150103060e0c0d110c0d03090501110708070c08010b 69
    0x59440c02e81c0302c040075210041454407074070a8203100c0b002c80e48203000b0800340101940042c1000300b4203010b4000f094024801260070360082019000b2004010034488109180307036502d0780500b00c050001052440b640e040c580110480c200700d00c1c400c0e100c00203800454980410318030765680010506c00e06000310100100303082540851a26444450341c10f0403802d1592600b0541d00c1403080e5940d50302d200c0c402105009006070399000e9181260750903a201d2440341c40c4c00c0591502e8140d580f241040761600c800c0b120700ca02c1d008202808400c00307400d0202c1c10900b0505440d000081081711100000103590040104014150b10300c10043c1c02640000e0040001c11404181114405003540c226100c0703542783da50341d41e03200e50040c10140141040d68400c40c10400c112401c903401640c4929590b90800059400226000d420751320400c105000030403102d00780d0802540140710180043c0e90a54880d02d011350110a050001c254052041302d1541d60f902d030a04004031075082d01d410409059040040d203411603 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 676648705 1250 676647455 676647473
    0x3021b0303040b0f040927030e01050d050a051b090f09090a0602040e0a1406090103080c0a06020f07030e030601080d0f0e030105041a07030903051e0714060402100c 72
    0x20660815410501458840028514012070f440003000400000f484181308040f50090012a409190f0500004040c280c8651076a154004120302030900007452202280c41862410b1b01c440d410704115140140310440c80b02a554219030520750310752100c0c140488003010100c100d501185440301d80d801c210015000804040c150614544601d030b40c5804140054000d00601007a283c0c0032004541e41c580c2c80c030a1404c4288121007070302203d40384c40140714404003188030040c4144c1d00200000500d070f0a69443c060903410414209086105000d0064002103403071005083c410302030444c0d0b60301d035042850024075402c64600c03d54041d81140c00100f0080704009510070740d07900720307080c84498907102181c00c94000030401021640b40d0f0800c014001401410b011405005c1e51000030034200381e0344e0080980a0b05c00000c0024001801007086100042040900c40c60011079900c9252a0843c0d50311042408e84894900010540102082c4421071a06140c0a560380141d400c120310014015200d5000c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 676649955 1250 676648705 676648723
    0x1b060902010f170601110c181e0c031b0d05010f09110c03070609050f010c0f030c030509060105100504081f061a030c0a11031c0609110d0c0e0a031b050405040302 71
    0x41c45002d4004640c135040c1840054140c203000b4190054030000c5441c8d05400613000d840c2440360f0351300091400706c104543c0c1d07c8141310780c040c1c403d0103245d40c49032030319164103001d50040080884010b1001e03e1540311140100d41c020051072420018407400c100500080b244040d03800c8070483c800304040c84c10340d0004000ea072303c070507080003002560300c2240c2490340c01c10a400c07200e4220343d480c04c0740c4c13954401d03004014001088810780e810003442031a488203400b1190103070340306421395000c1070040010b842e0507103080b0b20440d080d1030050704280e41ea4034941e00e0301200319281d420580c800a02e0019005084c81180c004190440410040404003000c00419200c00b5003218052500043e0600015006401a800e000b54a40c1200d030b803024400d91005242040001108110b4108203000440d15010700910800c403a1000b401d03880c081070307001c141000304454800003040c03100c00c050084103aa18800200000c6024102081200d8104010441c0d50b1020b41c102c507200794500014040880e50001f541d401e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 676651205 1250 676649955 676649957
    0xa0506150607080a08090607091d1f060206090f010902090a0b04110408060603070608060609061e04170d0302030c0405060c0111160516061e1b060902010f170601 71
    0x1080201100201e003840c420030300090722007480002c0c0754a407540e204c9035103403086035103009030f603540e8030380c0e4600700d40c00307442c5118040c150860000008208013400380d074560010480454110400131580b694400c4e0101c6030302c00c00c0581c01407000c00c030b000041449040340060b0301c0d0000b00b00d08200381d8005250110060000703081076544035850380a0342c41d00d074130014140103d6800d940c0c030b907a641c18096650740da046030300b140203000d015400581c0d10b00500000340200070090400d42017025400602240b42c2120324542115501c000504201c2000d000080002d00507900e116086900a4030b00c040c80c002e0064620020144100108004645030a041d20150384040752126540e2282103500c6000d0b10b4809406900000d00140b8000c40300642081182c2083c0f059054411506030705000a01d50304081c8504000b00b2002040387d2101200c880240780c15040c2030400401d040b10064100308103401186044482039500d240307000940d82c00c20303030443e0f14542910b0081c1e0303001c1e80c142020041c4040a80524 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 676652455 1250 676651205 676651231
    0x10f140f032550090a0c1106060303030a090201030b04050f160806030c04020a11151f05030d08070c080f070606052d150f121803040e13020d03091401020a0506 70
    0xc81600742548150f040428020082032180c1800f00c180d800070640a49a00c000c508100010200c144001c105a0300c40c2000501940c10340c0d035600350172005801c1400c4120704040c1e580700780c00004c1e5504e1046c3c501525107007102c12118078110742c8000080000d54040d1050010b85010400240c1d0005002281d10b041503901580b6180c1c11001602c02402c103a080b4001e9004030b0003450700c5a4444c02c220b6200f25281d00d40c60111404843d0b1002e43c0000e6030280c580c05400c4080e83c0e03c0c4203030040782d283c1d81200c01e40c5800040922140c48121580c0c01c06c3c56049406000003850406106440c010100907090031200d00c0c2540c1c284501c80400166002c403000100e078100c0051100310307510038240030b0b002c0c880c25516a81c0c410501d80d042d0020380c00a100d02100b60504008150040c82170201a000150385000542c545410300c104600140c400602104510410000c480c0050312801030740e9440c0ca100c0d444003003034a418158031250480b01d614207941154054a00600032500c001b8140b6001425400f1203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 676653705 1250 676652455 676652579
    0x50f03180303130b1b300705071205120304080304020901091406042c0c09010807050a033002010221091f020f07050312010f140f0325 59
    0x40002c2c0c00718584003801c0c081c0d903022020b402c0c401d85140c0d6240c0716030381c40e0b06c0b8000c5100c1c101c1161401003910150450f400705030140070304c0400320080b0303144a00030340483c2c1911122400488150340126002c0302c1d502c0c0040300303101c21810004001030140c81614000e104913441e00805462904008000b10b11458503540f200031043c3c04c104034a545c0c454800c201501844510780c0c013a6035a240c18641b030380a14030820000404c074001040850030307102e0042c21200c0300d62031901c40ba520004542c4080600c803010005401000c0001d00742c0580340c50301e6800150300c07014803040c0560010545100303044207d80740000c01025140110701c85030907404001e450003141504040140003406200800c001c400c100203101070500c50008090711241c0c0000c207008403141c0c0c9400303411444010f9486000da0752088c04001d8078192a10b0002c0e84a10300005d0121144511150060100c20034003c1143c00c95010046007401580c0052a0141c00c801807801c4164172005503e5203903036512602d0800e400c0d118801220 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 676654955 1250 676653705 676653727
    0x409030c0f0221030901110f0705121009030305010305010e0a020114211023010f0807032d06121a040503040f030632010b090a03050f03180303130b 65
    0x2076204488640f51400390030100c00c601c200d03620352082ca0124042810340041c550300b80000610b6403101c20104025040311443e150a2022402c5c0200b150703004d80c0600440e030045036000c0d110303200485003c0d50b40400c56500d9414140e00f15081d26800d580703e40c01c1000d078000542d8101007180e01d0040d09400303151b951452594483e036a000d0015094080340440001e101c0f400c100d01100e001500c09010b845004502d840a05040c0d104850403164003250110301160f00240c01400156440480c030300300410000d11002481103401c81d100c900207540c0e136510740c08141c0c500682c455000541911060b1403450740c5140c07aa100140b540c00c900d080214049170005081000034001d540040c00603410420140b03890303150410280201c1d00394070204070300301030340c07600364520b440a20400f60b1108003500c40c86900300031400d03200f5480003100d542c100c030440d8400800141c0c2080300107040c5840360042d40c0c803440120007801080261080740e0f84654403d00082c490307900e10b5442402122048804180e8490110403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 676656205 1250 676654955 676654969
    0x905060f0a110301080a0b060118061422090e030a05040312020c06211005010f0f1e050d1802130902010c0609030e0a090c0f0309020d061113050409030c0f02 69
    0x2108200800400005240b07a000106811b100d0312032080034101e561054011034000381c0c41d001c94036103249050b008002ca180100780c401e03040d0250011040c58141503c0100d0090035029003c403d01c181502c1080004984910940e0100d84114000d90b141c000f04a50090042c011400041c05101d59074800c00b40007802000f10221902c805008191200e810400c17105e0020a8047d2844c01800e40d1030008103c1094000b803081941c80c16111b0842600080c0c4007140c48014004800062025199000280e00600609618812107698540c2d546618110811044d12004400740d40a0340c04035022030f0043e5100085007180403281040003030180014001200c4000b860070001c3d220528200d4107006140d4800c0c001000f440d8260f0b4102280766441c00040122541e03100c04000288007008032102c124401c1d00680400c40c0000c0c5100036161036030b240c4604540c100000301d041d00c00002082141d00c100d10408000800c2c0840c0d00f003100304201d842c0a046204a040004c00701911454100c00b19a1400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 676657455 1250 676656205 676656221
    0x10f2601060323070303350901150e041a0901060306021611010f1b05070308280306060f051b07080123090d0806031f05190905060f0a 59
    0x1a00a00a999030b07810a607110b4222216000003040300b0110b600b035290320000700d003021603a05640f40c0350324111142a03804103407540450540d1100c18800400c00b13100009113498041e80c01040005884001c64500c0506204554403480040c443e100c100320104040a10084120030300d41003000c4075580310401d072030042016408c024540ca10100c1c0134101a46203c4441005901c5041c807240c40818020055400b6228614014009880540315510300300d031000340025881d21030800c54044039100c7d5295560740e0400505440c0c84805940410f4110b0405d100303060050302c150608201d03503402e01000420451940c0d02c0311090200c00036181d0315007007000000080c01d041c044103603480381e91120507080c0a4010780c0c8019011003080111604040000303403805c2d00035035107032000b051034103201d8070240c4400780001c014a07030600540324a191408034040125441094003880007503e4640a000c0d000e082070308990624007603240014540000b04c0c0095541c1d000617600758480816a1440da000016003540e0b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 676658705 1250 676657455 676657529
    0x11040b07030915020a02011713020613050301110c060705030708010e100914150f060d0b03150403030504030f091d15030109111507030203070f0602040504060803190305010f 76
    0x22002800d00d0344d808166100c09078400d80e1000300b40d109604450310610010307160350000103204c014460062030070b20002c0c44103586144080d0007440e56880000c0c215001d48010311000580080d08408208050103c0da03071245480c2031842c2036003485a030040450505003d451003824070b00d40401c4007602078400410003010340c1003042c4400e03015074122030143d02c405c3d5640c000b0700c20400181c6040d0710301552030003d8090064070003400c14080c40999009042d070104102d4042c0940344213401680031244a0510490082d1008a03440c10a483c0003090380512000c40c50030030401e00000c0c884104181314140070b54004e035040300010703110b440380e010300312921082c200e42c0740d80381209a00800101e50300d960032008003220050001c18011211080c81d104001c0000e006030010040e0300001208c40402280f5640a1000141080d4681021808035201038014080c00d030320214100c20100c100742c0c007a041a600e0352800b8045945030242c0d08414003140c1c003c0100e0207048c0c14494128600e9440d00c581d25602d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 676659955 1250 676658705 676658729
    0x2030a0b0403020f0d0207122006070c0f050f0d030804210f0306080f15100315020301081b0a0513021e03091219030513150b0f0411040b070309 63
    0x42440e01035a68100c034405907645016a801d0f00700d19500204a00d01100c1c004904105440c40303540c1c0384861201009c00a45002d18103040e0500240c54841c09400d03250702c21164106224204252420b0712109036010300d01c03c0c40c410a102030315841c2d207400d058005905003804105921146008981407482910249001194050f00900c26901035541c20035250251801c104007a25065031766212101c0b00c011a040f5070210054050b648400c51a80c0d62060f24054201e210079140e0765198480d0410785e498024940d0084014040361720103000540c000c88010601c180380121090110b10480c003d445107920885202119204c4d4590940403100c030f00140382e000c44c20b103160600312038502d5001954801210303c0740300d804081c0d8605040c100e0f20980d0280c4002c0c0c4511031250400c401401d001080c071441d085440b0308000c0000c8000d20811030b883c0e2504004a0750045110521a003101c0645240d4412414408076185d410325400440e0241c5904159455442000d17081c00c1c0c6103c0a15030101c0e0540344 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 676661205 1250 676659955 676659961
    0x2011e03021608130b041d0718080d08071719112701020f030f0a0c12020705090c0403020d110a0f0f1d010b030a0906061e090506101b02030a0b 63
    0x1c481c1000f44130382c0070b01c101602282a240e0b68100c01c18003447c0502030003104018107440000304420701a5600054900d010540142c00c8161040e1010041d401000b0b140d00a180c070806094201d004a40d1212244c40c2c044042d590b82851503100702400b9000c3d4880640c00050410b003824581c002884a07007605152542d6a0008180c00c0301c54000700755603840500180d641307084a58070200301e000060b41020000e5040205440b004503040c2e202c40800c030140000f00c551100000d0302001c01031140f400c80e4000c0c1001a10301400c0c0300310799030020710000748500c1c204420b00046e0ba451010800303e82d0811307101e0b4040d503903807400f16a500005030400b002c001003074100042d04951031a5044140c0304442ca841100000e0001074032110742d8280074010700c810003031002a03091182079001c000c032207006101c08a01036550b20041010710381500680c180218002109104400f060700425070001000da801c0702d1740003145540200180008202035044944007030000e03041d9a8100a00c290140d0031028045c0181 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 676662455 1250 676661205 676661213
    0x115020d030917070c0806090604030801171f02030a050c0a050a050304020a030606121103031206240301081b0d0b04021201020d0c0507150c021c18030c050a1202011e030216 76
    0x5c842032241c480148159000103200b6000400c80038003980d03058075415100d90070314004800070044040040700380d110302d1002c15182400381020028a9425401c0143c0d6820008410070036224010488100c0f40f10802240100542c0300048808011451414580b25105d51000a00c040c0c02c0d50b0000d0056402c1c0701c00420740010b416003086810740725203c92100c07401d1060505440e0b01a4106031101d04a0540000e440390130702c000080b01d5091840c1c4800c4400100307a80b0a000340e04280c002c0346480d400044030300d403504808d54024021007400c41da07a40140d40d2a030386d941e0040c100180000d000d43d00c150704c14907201800750117503424001d600405002c0140421301c010402d4000400c21742d01050311a111a80080991017074003604500e660240450403034605d680d100501c0302e030b103030502007010401664081c1000140f440c4040c512600b80780c41000c0c90001000119600c40e040480c07502c0b900188100140c2c0c11060104d0411000c0e00f41036aa281d150350150002c1c0a003c05140e203c1000f40b04281c204 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 676663705 1250 676662455 676662473
    0x50318070510080f010f2312010c080601020706020304030b0a0b0607080a0e13050f011406090a17060705030c0a1b05031305090a0c0507140c0d080301030b0115020d03091707 76
    0x760a02c2208a6607a80ea640c06c401c1e40d079040344038006860000c0c07a40310700c0e401c807105900600d03540054107a000425602001da0b00f182e020300307a50b41c009040301083c403c1640c3e051003200010005031000754241410f5880340710f0741c0c81c000f800c05e480f01c03950381c0c50041240d00c65a00b41c6060680002c40c040e110300c018440501848403002020388198103001c170015800480e40b1416004003030441420381c1607801c1c020002130207a41507914681c042414402a4615683d01ca15400074114203016103004190102c249850440d0250450b000e006080c0208140c0304d40321004e58100048501d0616194114441c5e00f040b511103c8401403c2c1d8040001d00301c408400007000c400031903205072200c1d466544c0e9204040e04485c04a048003001031400c010b1303480413031140348a08a81640f40c1003503440444da2000003450154001074101d400c824007100400c1408000040c041c01406041c0c0b0035440791640950080d118941d02171a4018940e44010040501c5080d200c2c213011040405503181da81c4006003485591 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 676664955 1250 676663705 676663711
    0x9100207080d081f030b040b1b0409020405101e051e0307020c0a0e0106320705100b040b010509010f090801110d06050621040303090203120a031b05031807051008 71
    0x40a100740210a5145008912480c116070b0041d41810160707c1d44c0d0b842c4481810f01800c01d1075408424103051507220300c010b0003080208102000142e41c0e929100078043d0000400910505000d518440c12120820b06800ca00341c4481c10f14000d6620b031201c07103541c42000c01c009105c070138541e130110411042c00d40000e00c03080d464500300c400c6041180e541c0d0341c0500141090040b50000f0b001b40e00301d41d0442e01800d032403000b40c11034100200590240003410813440e402181e410f5800d0361104020302c05210562003030843e5890151001d200c0c031055000085c20720310940c4c0d0702e94104a00e05400c48010391048450b03102401d009402407009000091540e01d10f0f030041400b9054561600700b0004407442c11504907840d08079002d0040d18901c1c507050064034074031402002a000c0c180c80310b0001c0c0041c0d4091141144049505031141d440b00080c8130002d085680803001064420720881156003404c0e08031090380e500506460784010081058a149810035100350301c0281c200d4001a030001116420904a80c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 676666205 1250 676664955 676664971
    0xb0a120f0522110f03030702091f08010c0e09150301060e090d1e0e2b120203030603060613090c0e04061b0c0215040b03090f2109100207080d08 63
    0x111048a03251040748194030071000801c2032107090f40c2820103051246108021400040542c1d0410119402256000303c04481181c4540c010007120f0040c4c0349185e03008406001e43c0d10007080121038000340608600414400544900024000101d91401c01c0702101d445400c00f034001d01c1150380d6550101b80d8000c0c01e480b6041240511011444040d2003503045019242400100211311a0000d4003030782c1c51100310b000b06412a012a900513850401d403840d180301c6607a4480d65a01c5072445041c0301440c03800c1d0903000800c540040046c8101c9640c0042c510780c1000e012a440141d1a40700d40d11440180703e00360006200c40034a00c03001695650302c1d10020310543c09601c0c00e00400d540c0c100741074100903030020300d480801c0c00800120054288100710040c0f610384000c0c01071509880703614001c02a00300b1103040c000c0d07603c445000b0942c10000e0098820204004510710203206850b200541540a4090040d00030001c07181d0f0fa65a0f00d1082140c4401411014103882d28076203800401046000102e40c1e0107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 676667455 1250 676666205 676666231
    0x120a0b1c12030e0a0c15050c0d0210110403020315090106050d0317060906101103090d2006090607140c0d0c030b090606090408090a03080d06050901120c0b0a120f05 72
    0x41c0d2440004ca80d200803103074003420039029181040b90170801210481819000c11078180281006c4080401c818660030324250014035600d40b460b04801c2c165408840c41c03818002090004000680f40003d1468480c040280e803846150360f03140204e401010540e102c0c6500134600b02c000350506130040c074a00c80c071400300065840150b0342c040a1003900503003901ca054000c140c1840380001d4511560211315203000d4101580d1521030031000103000f200485e074050312100c00b14105a46490b51814003c40d48450650b0054105200a000100f082c0119000035003820031400d003103542c0803001e10640312115002004031604000c1801d101980c0d856501048801e404d100c0046804000005615482020010800b54056543e81c3d109440754200c80e031000d40007400d0403000700005d034000e006800b141d0101c40b400151645440b0800011450603400205040e1190306104042100a4041c0e800c0d9030503900020794401205200f22520640c50010202c0d452518044660744009a045103004030700ca902c0d0740c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 676668705 1250 676667455 676667471
    0x109051002030a0c0602162a0b09040b0a0504020a09150203160f02040b1206220816020d0b01080109020f030c03070e070c050115060305010b120a0b1c1203 68
    0x1000500000650080c09640240030580695201c0c406800c000c034800e00000d414581e81303081801d011a06020111960321400d1200a5800d036020940032a40300d03903450301109989040c40901051141e0034100d40101c0c1ca0b1442c40c4243d498000c1d000004140140c0119a03592400030000e1048181d401000ea140c5002c500030039084d07200000340c44000c0802c28031140e0b414041d90b540e815607039000004982080d112075805c0e0580d9600d0404c061003200346000b801041c40c200ca81d45644c0003900182502c540340184071040407070104000d490b00b801030302018544450090000461a04080c00c000741702c075090300c1c0089803a2406410849845100f6580404840c1c090f10425803240d10b044c0a071360300355110308010000c0b644101111074000f200750510a140c42c4d000d441e01400d4401c100c101440d1030801c4003041100d5075251180ca4014404c0451590600810050344d0700ba0340070241034205226240c402d01e13107080e1f440200e21aaa518441c0140301003416520384150709010803a26040420716100803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 676669955 1250 676668705 676668709
    0x9030d05071101030906061701091b1206021b0a03031505041103060f150c160b030106050a11031b0a05060615040e09010b06130305060a1a010e04140c0702010905 71
    0x341c0314110341c020288400022224011001001d042c0000d40e021a204c90001072607991031380d881c00ca035081e00e0303002003800d01ea20706010580505002c01c50b02406070610040000000175102e107040c0c01d82c01203000d07035514690700c070180904c90340c44040d0030140200c3e000c400c10903416900c800592015890180085c0d9035030004c0204940383c000a14030807950070000100249081111604440780061515094019803114980c0c3d1b504102c0501800e40e00040d81801c51119140d8044010181203c07003515560400b0001800c1d80100d80c4411f0030310898034800403212009005850905c100070900c10305030120455541c2c0c4e2000d803410113540c03601428000c03c1d01c504002c800302000741100748002e0714040c6030001c0e00a01120040c03440d8403656891250a24950325900101016807146032003a06890840c109142001400342441030980e09d04010709240511a004402c00c40f002400d215640301d05407008500030b0039a0700042d2680310010010400354260ad1406420118001e903200745d9810f4035541 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 676671205 1250 676669955 676669957
    0xf0b041d0d030618020715020d020d051003050d1803080a03020414030604021e220203040302152202220c110c0a0911040f030b01170a11090a0905060c09030d05 70
    0x41d480c000200c0c01c41c14010542c0940042002502ca80200b00300c07e0703030004003078080b40c02062001c002c0940025521a1401c85c501035690440003906003d9071282c5169a00d41e038517282c2905050500c108030141e032180c1e01d80d0312800d070015500b060b8855915030b84840028003e5225009480d03810003034072101d928605002070203600c42c42c3c0c0680100074034072101c01100f844030350355000c49500107084000c200c080020071040c1e82d10304464020150b00e0f81058900a4141513180e1250304ca074400718401c02118100440210580502081c1c4d000490101400480c071100e107146a03110001c082056080c1c0c500405034412460480255100a071400c540703a107460b00d42082401d22507221400c14403c4c02000305a0b48910180e4181c00019403030a40d4a03840d5a800c0c00469005803008041c00d001001405401c0f1844141c0f050860302134100d4002e01d0f27595140c0d2298440303850b030040c0980310015510054560081e0300f6250008101c0d100d40c84e06240c640060392100074030034001e0240c2000000d545001e04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 676672455 1250 676671205 676671209
    0x1f02010510090e12221511150105040513050a030809010b0607050a080c0a0f122d0804050f0a0f150608060f0604090c080607140f0d0f0b041d0d0306 65
    0x403001e05645000c001c01d0811580006824640306096404003818098403044241c000b04024806a031003454022006047e200e040030700780740d040c0c01402280711a103040090050540b030080301d0014154a40e4280f4903901e0580000060203449198003601c14190068003080c81005108000e01c80300491400340401800b42246c0105213034800f6580c0c4002544010290660010050844140701415256500c420038131031415164210380107104448181d0042901090030100c1102202c11443d0300f540d00c550482c007407000420071072400b000c64100715041c0f00c040e03001c03001007085500345012410900300c1d5103449542158252840394070403010404a020b0031048a9000300074000da03030749445d03800454140c000c2c03815900c5507a0310521000154440480000340144d0b4004003440d182209002d4001c0d030100009010882c000c0c090f2040b0003108070225080505070810205010f210a9840780181c1402e910780d0350b2040c1081170640c4510781c2507000103807280e00401161400325508905a003255494 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 676673705 1250 676672455 676672481
    0x1203132d02060d0e070605040602100902010c0f0201140c03091804020d17120a05150a05060306060a140a03020309100c0c080f0d0c030507030f180b061f0201051009 72
    0xe032403500007502d0705102809000030111800310b00020045641403e15200750483c0b40868804103050000075410409500040f9002c4400c200d00540e54002070400d2800c405c000307201c2c80111403130030f0440e482010001c49003540405080e4445d8072040550b40c490b04400710701405544c7c1c002188142d02189a0703014021038015181d1980c40f0019110000302c4501d5003030b020b46a100800071001c500900074580e501c180c141240018060070002200c480001200024921511007141e00b4499944c440c002c50383c22081c01c5034507541e41d90b22010103481600c85840303000741082d4086021003483c3d0301600154800c4800701d056230710401079641c103c42102c2d03040c404003002070756011600c40080c54001c010008210040c0040b400c0030b480b50208810340c2c07412000000007035121010300680c3c542500a820b00344103118014445070245074500701c0360405400010700360a8a120200e40161201c681a00c050440249136080c1400300c120040d0107040161040b00314401c07403a2000802c2c10f41403080025119403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 676674955 1250 676673705 676673783
    0x4180902150307170f0a0b030303390c011406010810030f15020a0306030b071d040507090810020322210e0a080c0a09050705031602120313 61
    0x4a4107000c0716800060142d02070040e000ba0040c4c2815030042e400d031040c80441052034044c0392424030a810748400707201e00d5029034014420b010704928200c1c508503810248000900c281c0140c0100007004c0d6040d04141803914400254150b05c05c041900b00106030b405440c1c840310103440301001114090b00481c0c214aa45400348024000210b0010807002e0b03050003260320541d00351103210413600726804140300c880401e5940e0001c20400c20300d00696540f085250078120340d07140212800071540f15400700b0341c92040c0e40d100b0005031001c0c041e1560601514458003103915840f04141e41400941c005da44204115080d40400362005000c1800d80d007215a00801504010380c0b145488102c41c03081e08070703510a001c20901070040f9922002489001490003000800b01d407500203041c42000c08494100500032030503c1d04000c417060300035040b2600440f003000c01010907125060101c1c2003000d0310310b699520b80c1000086c0060740c101c9210024049000719441c144141442c01555000b20810301d0083c0701941c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 676676205 1250 676674955 676674979
    0x3070309060c1505011203020d110d0e120304081f060b0712090314150a0204060c030804171c0c0e0108130507080312070915230d060b04180902 63
    0x110406011a8192291401c030340c202c0d002e101980f0035140240c01c2040e035050520b444030141030f41040000da68003110f043c0303640187c0e4129a080c1e11461068500c0c3c0901200c05020300d6541c0720212070984c945c018000783c0391a00d8407408002c0c4c898240034462403185942c091840480303000e500c02d030801c0b240ca07064218a031400742c6d81c51240c0000540d90f5002030061004002001c81d4a041d1503007900c0c5107030001380c07045041025851400300e0014107541c2c5100c0c070500c010b01245800c260400001e03030b01800e004600b95100d03e42001c040e04e041c400c5802c1260301081c0c080b0b80c030100920030704422000260038041a00070341e8040b034801d5000341303c05001444142c0840d41c00250401047d4907140118117a812443d12b81581e50329503485180b2904140c681340041015460748802c5103c0604403002c1e0014032036801550003400c0e00b078004516a480c03c503000070308040d05003480407201c4a15048105004040d9140310180c0d464109220306007100e04c1c5ca6010b000f50780a00c0c481c003409290b00a00b10b1106c94 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 676677455 1250 676676205 676676207
    0x142e15030503033c01090b221b0c110108040f0804030b07080108061501030c09050306090607030b10080705030a0209190602070b280309020d0b0411040e0c01030e1c0207080d020307030906 82
    0x840d086500c1d042342030042005420150100000c0c49522108000300ba669507a004240c1c4002c4107500360405c1081c0207000c0c1c00080c0030313642100c2a0001c24030b01000f240d255810700300c82d08003d11304010020200054004100401c5104080c810413603a03d5154150fa40e0f403146035100c00d000c0740c1c10844442c042e2010389407036020307901c454071000044c94108180ea8980b40401c0ca06001a00c0c1e450055026008000c02242d040c050241c0185c010350b007070303080d000030030201074416000544407000344000130001070f03080981c650549001e01c4000384880d5007400d00c0000541e008440340079582c0140107808002c1480c000c01300440c4c0403100000c00300c04520a01c014030000c10400c644442c0d042607110010700c3c007d0703a6007080403001e541c0100c46a25040c01c061800d01c080e0501d011410780500c0c202a0302e041c0520303001c83c80700d00ea0b80003030901190503500d10018904060340d1a102460040c05149104155036000030542e05940f080c80440d4a50711a001e0240d07501c1c002c04030000c0002d003102106201c81 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 676678705 1250 676677455 676677461
    0xd0623040206160c120606050a1d070305190606050a080a0216080f0c061f1203050a0c0c03020a0803070c05030a020d03110c0904142e15030503033c0109 67
    0xb18043d200000d103403170311500e50b00030544c40d0400544005456010030301092420388000c50050590a50307941480c00207224000ca0800020401d005040e0344000141c140003a001d00f00302c08004c51401048220b844a0014106800402415000648600004401075000e1003200c110884008034052001d80303650310f00c0f00c15801500448030042003807103200c41c0c40303808110b040c1c001c0540845072003d03a410086811488210396100c0c1000c03410007000080401d8102c0d0071a940ba00e120b01d0f0503140b41e0000e0074011054152a80300039088048500700268014021010b0b2034294450a05150350555540030150346220700d5101a6001d1003240c002000240642590285e445442c0181c4400003c032000140036840304139820350b4240c4018140003031542e01413004608400e0b0b0017884020078800a161425100074601030105c440b5900c0900075a0288842c444800659211049a55915000104440101c1c42c144100c460010f01070341510144039148050f18045680020f59509030300c1e0500e8400a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 676679955 1250 676678705 676678747
    0x180a0b030a05061005100f090e15090f010515040302060f0a1b12122a090b041410050414090a06150810090b031b0a050d0623040206 58
    0x100d4401d525900000074000e2080c684501c00720015500614a45014800c170308152030030035410003102e01c40c003031211038120003000c00b5103030160743c551041c1d5190000c41140610080255a0007007a2000700410496102101c90603601c0543c1c40d00480d59002681310242d0050340402940302c1c00c280702e14140d004101e001b40c45624500d2800007811418040300e0b10100c55100c0c029240702c003900440e00003194110103643d0120705440340c104210ba040c0c0300e060005401c0c0c2c000300a45800308841c3c19590301d10488481c0007400c81d290065589560700e052002600c07824100c11030041104000b010784960003002910300300d0b544407450f19403d08038a020410340d000011328640f1420795560012404032100040e440ca010318170313200c001d11420b080e50540002c01c00daa0100115070308014140082e614081000444071141e000e410a4108151000904505403600010342240390003034000d05000e441d0700100082d441c00288412a00d0031010407a09a800c03c03200a90400da04100300501031101c4d82640b01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 676681205 1250 676679955 676679959
    0x908010b06070219050a1401201e01021b01050412030c080a020904020f0a0c0302060f010f0b07140d1e0903030905120a060c020709050c030f0115050405030106150806180a0b 76
    0x58030342c5c0c000740b0b405090303402800202c20445010829540c11402004080000d1030300721600300403010328955221201030541050115425241c8842c80c000d40540b02001011078200410400114801d0b0007170100315030584401122045040180e40248203060100b5110340e5083d0041c1d80304109040650722020003142c01075400c000200840b01440f024081c400043d955141d4007044504000340303030440103003409442e03010000040240c000038940400441c2c482d8090f5607200c0e4001d040420303200d0300020f034164050080c200105056984440d03491041d0f003100e9558001c0c501003c2041b11001c82501005010401160b414001450f10b4001c0f60718441e84031007280e00c0302c040c99035200160348d124080b080140c0c0c003003030052140301c105000b140d40c40352408a9103820762500b02c1e17442d030301c200c03040c0701c1e8000e10650003e50001c41803140307040f5809800084d0003449a5075a54210701090130b8003000c100000340803440441c2c1245409503505881000c0c440d0105100e84560208000900324a00b50075 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 676682455 1250 676681205 676681249
    0x708061905100305061e0a150c1a090d0e09190f060303110c030c06030402010e0d081303030806040b010f03020c0102040e130606051503040609020111030c07060908010b060702 77
    0x4581e502ca600c40d41c2caa1003181e4000c501401c100003800020110032a101402d50044261103030552501c0304840e040701c0f5810500d00c0500c1d42013809513030359015444007400310020705074a41d030307000b0b85810308900803205a0108e17221405584811101c009650030915800b041c2c16000c28020314600c40c40710310710110100001111203180c594039084460035442140424010300b10001070003018083d448486078160043c2002a1048000031810301c00200001d0501140c0490722038070f52640406518120741c41030702d50b5a01d0914610706180380307144e440100c0001d500040023552038141402044228001a16001e81d49240c4020a070081d4220030b100414543d402d01c000140301b82041da600c0d010307442d1121111024078860808500b6900309070011805015107440e06058178807680200c0b81e00603002130b80095000c07064401212802c4042404c00ca082c800841c0440400d10041a03000c111442515a10300f0790b950780051509070b42011140941c0008140711741c90150912003401981c1e8981703d000c030303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 676683705 1250 676682455 676682459
    0x8041703120f0a1e050a0605010306061b08040e0408091e030327100908190201090315142d010f090e0c040e0f01060e06150702030f0106060e01140307080619 69
    0x903016100015480c2c6000f42e44540601c108806e8620400c009400207107000e02c001c5051003005072410388401e0000780452040b040308001e1040c51400d40d00174080c0e5006056403800e0030305010f10950402e800340c40c031400401130509402501d16000c069000800340285050845210124040c80c106521001074550390304201045507880c0c14503040424039940310312410754184030303c1c80c0c40c09000c405c0d800a400c0050058002503a00703c460081240e07400008202c001b51011040310191490710351102e0344e0445070003482041820201c0444c03100b030f000140c98020105507408500d00038021b125810210201d11018003079002d40ba0088203510b241344085600c0b82c8801004681240d41e103c8030981e072508292140c00e100c280a005a00082c54000c03204500c40c107140c4001540030010060021107407100040350390440d01c09122034141d4295040007045450303501c05015114410703514002b40012201c0c195480a80f00441c142c9009041c55034602d08981e8401050044038111192210328a02d4840c0f40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 676684955 1250 676683705 676683731
    0x1a07021e07031514061302090a09090b0901060b0307051e13030b0c070206120603010b040911040e011a01180803030403050d2702040b060708040308041703120f0a 71
    0x14a6100c5455401050018910305003090041c0382010300462060910341d04041030010038544e40d41100080f210403c4080b44691410000d10032a61a990802c20025001610520075840b008465001e205540803560b1415602e9080302d040e40520303180d0f41c00a20108501d548624042d10464410041c1c1e03084000c1c1d0352030006200e82100c003d031502d2007a555824001c100801d2181c42d01700101c0000c55007812603903400513100e4011000e0b81c2c4c102d00e0800d4002a1f95a400f50002e4101c118058804c00c0710b0011400c0144907008a00e225034015070903d911400d00e0b9005104044040140e07001240f40c08012000444103601000c5100c5000d515039600403130816424401035004501c2a15a40d039550b60445440e02540d0f44809030501c42c00e085d2404161022032002440701c42c82e4121000500c4010940004080380900c0b01c2c043e01c0803c000c50f0110411119500404c10340300803016400c0f1254403000655502c1c8141248000e0044180c00495040c400302c10104d034001806860202c1e18140f1005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 676686205 1250 676684955 676684993
    0xf1404030804080c24090d03031b0309020301050c090a0311180c1905040e19022b0f020c0312190e150c0c030a20060c07110a031a0702 59
    0x201840f10303000400020f41600d01440f621090340b04c2d580a800c0743c413103646011200740c000c40700c0e054050419680d9070003c243c402c1e40150011031202030320600001c2003083c000c00811224130124025864640072a0454040307a0940d10700c01e400074100304829040d1354640a080740040d40d42070b0004048003101c0c175040000c5400c02d00c110159040d840d1100d024640d4442160208070301581400420407052205480107103810b54006800081a1a1030fa1200300b1200203225520040304042c07282c44040e442111007a03c2c030210b00ca4504018030400390a890340d10200d1141ea1541c11442d401005203c80072240015890791117003c00b404103078140701d014000020345030070003501c900c1e079084000c95004040b03200005a40140d8010724403410500310400403580c901c69240da070130a1042d601c1080d40d4400c41610710680d01451401901e11030b05001000c1c4206400008044a004a00c008010020708045224800300c0340c00c038110b08400c81e0b800001080c8034901030721060840c010301040a0745c188011b4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 676687455 1250 676686205 676686209
    0x90a060b1302040b0304110a1a0307020708240c03070c0b040c0e1006110c0105041a071406190b06030601030b12010903110d08090a1b08010c08011a0a0f1404030804 72
    0x5508035941b0302d06490048140c20381d46100610030b941400090001d8031006148840b003001110055a8030384a11205a10b0311010303501010340d03889401c4110a003014248880217001400c6801c0c1c040c207480d000038410b2640400c4942c02c001980c54151071020615480507582c00a0240c034040500030b840d0011092a550100e07211501110703030103010011310b513000e640072422075402c40162603100140000202103100b540b04002001c03000c0101c11103124100000c407170003603610041c002c11000011000710388804c021500700440c0d8002d180c2141300382c80d15015004510600920051541e03a41000660040403808a2290001d80c581509400b13880c0c01d20501030320701d000392200243e030040c5961891504541040c071004221004050081956001940606595114040f650200c10320f0840502a02d00342d40981400d40c00c01081b58a2140c01150081c140c50300b5040200c9885402e80941545105800381c1d00e00007010520300c0f2082c2031162101c134620700c10250703c440c5496a01e4560380203c1e003240d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 676688705 1250 676687455 676687469
    0x131703010902070c0b07210311070606150804050721120c020306071412070c0503040609030506060d031707090b13240f0c11100206040515090a060b130204 68
    0x11914180180c12809400401782042c0551421030075650390845040034141c0e1040001d0b80c03c012040b003d0182d0454100030012203c069118501c50800d400502080d200b0b01952800b428940c41009100b86c1850384501d0f040001003000c285003c8034042551401c1d403109502070545c4103d507000880303010800d96002427503030300e406404501e401003504243c0061f2440e0140486403645030654240d07203081d0341c01c001500d900300c01955a10f060641c1d03002d4800c640189580400107011504070f41080080c02543c1c029000c840d015070303806050000c00d010b00d2502034041000708a05248038034403109081d41c054282d15140030f030650f84101c036409d26048008140418410100140055884c3d210196003009c0d445106011204180740c000d080a40114042d400b0800904919410b111284546800c1030402402c40d400450400200a48401381a07400319854016544140b0038150108000c90140c4120130280180c403d0715a83d8078010000d000c4e2403a00f02a901d1803001034000c00f84007800040040c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 676689955 1250 676688705 676688707
    0x50a12050c010b0a1206020306030a06380a050d020a08120d0b030a020616031403040c2309070c1403040f050a06080c0306010c020609150d150509131703010902 70
    0x403070501600392414100400e018000341c40081104002859084602c0c5421402c0140d980e100d030400705e8105801c8040c0030300410308000511311000b00710a10889201794403010442c441030a03881d031001e02001c242c040380d40100508030900030740c5880001450b001d84000d0015280036038414140d030605909601040303101c18007150341c840740400d034040da0802010850240040503110743c00240103001b40d50f1000ca41401003480e2100701400346011119200404aa40b600da203802e1502119100780340c001e40f214404448001040e44000000076001c49800400b03100056035044400c4070401d41044082e40c00b07050080c1c64003200d18040c801000074026070028100c4440c101401d00003080c1140d804a010004480d04110300d40f48042d094039000f0000346050062007043d400001c240d400344140c0d455103d440d080c1000d5100454100030700102e10707141c0080c8031600f10041450040002485559040843c1000061041d030451400d011164070070701ca1959800360385102c1c940d080d0802d82041c02c281c4c0d4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 676691205 1250 676689955 676689967
    0xa0b0d1202010c02030702030a140f010f06090f140721020412030e0603101203050c0609070302040b030c010c0605040c1502100f0e1b0103021e0414030f19050a1205 72
    0x380c280540c01e004403d40c00214907141c80d56004c2540c800c10a040544085500c0200c04090b000a001401c00e1604001c0288150200c1003640030061515108850780c00e85090804001014240180e680d01c06984104900b19514400141c5510140781e4804544190400b40500018124409080030340b491005140c07515241d0314003d004401540c4640f4452101441003003840c4c0303881e1a4038801d4031000d4078074900e0050503181c240e480d8061f00c0d42000d158040c2c40200042c00000090220442c1e00855041c041c4101c10300601d038555007009003460006410345109030109449404c05500240f10f800180c1d21159a941c080340d258540940610040e044040820228411402108201c51903004200401400c0c0c26649030342e17940030b0810310150809280340208681c007a905680340d11103030003000ca550003625071450005d81d00602803120040e18185023030140d0b0a0011b00549403082c108020501d110840009140010220b00d04035583e101d14408080081d441c500f01a0b00c1100c15164962948 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 676692455 1250 676691205 676691207
    0x40302040c03021306210212070f0509010207050d02060d09140607020723130c0f021501120305180d0b06010201050609071e090e010b130b090a0506030a0b0d12 70
    0x508038040c1c030303000c05005018a5080a45100b403e5040fa65941807200095400701203003107103400d80c0101844290700c08284607415850300b0340410300c960a00d9071011805903113460f0030346860080c40d146034010780c01aa014000360826484e201c800b58001003641c5c0c14400d0004010b41a141680c0c0119640c00070b060359026222810440740d07801003842e0000e05004c3d81044800749105030003401584400b0300416142c52070b9118031411110180c013640c1c0500081025900c042c01410b0994850b000511881400c1000480c05029403030507a0b001a0202184207000d03117080385e958020703c242e5240d0802c00c14590000c0d540d0310641c400700034482c13002e05c3c506103082c600290840e03c0080000e40103004120401517007642c4140c6201c2884203110150700e000d68910000c9031000a1908000b8002030403000106000022202400301c07502220b481c21020360710761854111601030980e50315005000707000c060010780f8084019603400308900400140915044002428031508030405417860541d084500c004a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 676693705 1250 676692455 676692461
    0x141c0f020702100c170a1b050d201b040b1002010614270606120411040501091a011d120a06050702030f0405040911060a03050907050121050403030b0a172112060f0a090204030204 78
    0x605202c20080210004c4c0d07265054480b14541440201030748102f10310300d6199560b912800000d90050704e002c0b030f442034409010307008081a000c0e583c16803005010850031454800b031b0034240c801c4115800d010b07001d03800f858580e0040c4081c018503070000c4c080c0a103503076a52001d040c3d03038800c2e0b00a02c0c9169210042e802030004440781038000e441c80b5401d11800514006445600610b400b40c2840d00001e180c42901c0c0344004102d02c054501c1e44500c090081c107521355000034402401a01030340d0100210f2b201d645003603035a4030580d45030158131981804208601d02e011303400030b5500341c018400e4200d080100030006801e984001c2c40400030039503e006008200c00b0401c071f00800f425081c02c3c07078100f5580f84852003034059840840002c01c16100c0c0001030416109400802ea0403e010b08030b00702e81500c9540f0000040e43c1c801003542076218491000030030f0390030310701040d101e00000c01c0104d2034082c02882410079030b580140703e5a0003610f13580c42d548248d00d9481c0004002c00ba49040103881d0707400c510400c010717 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 676694955 1250 676693705 676693727
    0x307030b070302120705190e0f03070b0403050613020102060403121508030d06090b0f0d0816030c03020d03060e01150207050901080a0b060d03141c0f020702100c170a1b050d 76
    0x4104040c004003940d81c20358000b40c1c480c0ba1f00c0d414034009488100c00010b8030b414082004c10303018024000c0c0021102d900c0b01c00350095034031440544074642d60f056a450340b44010203038003034010303800080400c000c02e00960103a403110521300301c0855050300c081910681b0b50229408256998800601642c280c0364070b1203440d010708640001801500d9a41c3d0004100f0301c4880e10642c454160454000d04002d1024200c498480c403a824540b51001c2a00780030301440300d020020b0340540520742c10704918601c00e101d000162591001a0b40e030a07400c0c1695001c0344541d0b4041e110540c840c0382c0c00407505680c3c4100b154001e00c0c0c0d0720b0060641c0802450080400d002c06000c20b4040c03001c0d07200c800c0c00650081c0c4004290003110203200e0325254500d0038007c07441140b00951034494076007802c4450003001500240307290f900a4a090010600c9280110781c0c0a41c0c4000c05805012004101c1501c00d02c0c8600911520a43e4034102c1581c0e0703080412544000590f400c111400e0f07020042d2080b0a54205211040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 676696205 1250 676694955 676694957
    0x705030f0f16030e12010606020c01050c071e2103080c09010c1a09010c0206060d0303150b0a050717073207081605240a0903150f0e010209010c0609020307030b0703021207 75
    0xc900e182080203590ad03c0317551440390500c18003091422890070200007040c02820b0b00860340070203003d203a21920383c01440d8029440005409030308030302080c0606119440190341561403562035511030300051282e402c0000524100b03e549494040400d551045006000100708040c095030b040c440c0542c0d0031505d01808640035034001004020b0030799290031005140329010f007000305083c2504400d000c100a56501b003845050f5000c81d680e4007050340720001e405030621401070701c1c10000316041c1c103811a000d180f40c001c0101002011102c04158940d486418030742080c1005140b00800c081105d00700304060f0001c8007190b00c2101c05803c10b00e0440003800040c01e098550680014030440c200010213034160042030200c1d00081c42421081c420200d4000458101c400622412420f10316600501b02c00700780e0300c404504060000d0010501842299920032058440e20001042940c8500c050450600c0580e4140030f116400000b06400240851144060b9540140d03981003603c80600e010130082e000c44 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 676697455 1250 676696205 676696211
    0xb03010f0606170c070813031203090b04020424090504020301140c19021002031501170c1c0f050903030406051b030f060a0302040f020c070b0705030f0f16030e1201 72
    0x140d0740c1c2240341600201084054410b0320758070300b168000c56100710340d0000c6c41031000051060908402e041400d0a4038421031014141f80540b0350704074191048800c1c040c18015288011038010701d401e0307001c00550384010703440c0180c4025071a5514462000303030b80030302511030b1240104001c500c0c0030700c15100b54504820070031100e0b041c03100c81219240a107250038000a024100c0000f1458000c000c10380d40031070703182c00656891918070f0700310304000a40075503940031034040c0e454103400804a1004601c11b640003503030b0509210070308002d035110201002e4411303c0c183c0c3e16210100944207600600f4400e428450045569051602e4414210b40700205101e05003e2080c02c84100b45000308100c03034100078120160340860b00d564000031180d40c91548029440b174903220300c50348264100e8024144020406082d1042655100301c000000d115000009040e50010000c40550b1440c03103024002920020200c00c0c240031100070074903a10b0702c02d070b0b00c2a0003045403840007050074540881e0b00e84c00405020024 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 676698705 1250 676697455 676697459
    0x91508010501050c010b0a0f170105090c01050d020d060603020c12090d030e1c12090b090a0501030510031a060a0902070b01050907210c110d0c060504020d080c010b03010f06 76
    0x80428206009050400800051000b040002500040c2440b18003d0607520304640e1a1040e8200030207a20a5a8180050345210104001d062145912448004e40981024090380300110760315400f04041040440c0d0901180030b0003030451042001134641a2801a0f81d01d5a881405140c0b00035594110ba1285041040c560192140300c10303600c1065040c00c06d03021b0940340800090b00603100c0ca465a8400301c03141d0b041403d21610100c055841c04032500c0d84c01040b034480b2000e480500c6050811500624030440412195110781e2000d40d11202111412010300c0e229a1340c4000301000e068000c1c10140c56405020b203a20f40441100c1c010701e0101d004501d498141d50750b00c0000801440790f076105c3d02c0040c001403d600d00031000808006100c0500c64418106000b40b18010084104040006038000880c0c0c0f10346580055503208240c89070716088a1900596a41c1020b000010f2049070441c241403503040015141501903d0800c40c00c2c0004900c03503650206060842d05001c0340044c2d005d0401c2c0b41 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 676699955 1250 676698705 676698707
    0x170108121303060203160f090540060509060604140d0305040812041703040f031202031e030703050703021806031b040303090e0903040f170a0503030702010b010915 72
    0x22420382000e10490407501d4034941e00d540c1c1d00384059a03001610300c0380004100522014003001c401d0f50084191104d0f043c501a820080710310900c02d01507183c016481c0420302e40081c48140d114601c1d40301d80d032094500c42d038690510b81042411501011446503c4500034050f5103020b0004590100c42901ca0b181007900e0100c802014281c51030a103400b07903801c400c00c0428180305000f01d0700a0009001290301c0c1300c6004e80c3c03c2207039910034866012084503001002000150110403501100c11403051006124156203c400c040c004a00c0760701c080d071004000c03034000044030b081d0042c5106121180c5540300d1905000280a0340c40040186003010b10411940030b10f07030801170444000000548240b40c03a1780d03840da81420a4080c8214100422401140c004100361703111900d8019103c800e50011500e8880b01c9100395203004600426003c1172001c0300c2484000c540d02c8034031b003140c6101400c40f451118183c55440c11988140c48007070050f5100c1c02003601a5800c140d00d000100051412080c1c13081003400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 676701205 1250 676699955 676699963
    0x18350a1409061c090c0b070b01050301020f030720060705190c05031602010c06060306060f0b0a0215060d0c0605131703090108071115041a06030a080d0603170a170108 73
    0x1206102c2d03003003c42e8041510091075200c150034640c0a8030072008a501e90801010380e40202ca41215418080c0001041604040c02a204040708044e031050940e00e80302030030348440c034407485480402e0000d400caa140200b41041407a001b80d07150389600365100c1607903d0501c4c82c01074000c0d405083c00080303003105c0e0004000000329240f164a000d11843d4042203440101c1e0060056617000c1c00050422401205001003580042d0407146a0303000f04e001c0c25500c40c1000e90070301500312001e0241e040107180c0040b105040d025540d00a0008008504600d440e43d00c807010007246812080000f00c011030044480010a4043c00150103070110b01c2880344000c1074007958a201701c600704ca04011000e80407851440c0640c4500841a958100740c4040d541100d808204014040b6415a0f880007000c1e81c0f810b21152184490f070107000c000e0701502064074551182001a1300c05007042c9503140d940c00c4000b01240c0780b00c90442a103c0d8940196540702c60340300004081c803881c28a00d0050401c801c0040003003443c001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 676702455 1250 676701205 676701217
    0x60e0306011e081b120607170711030706240305100b031903051321120513060207030b090d051b0a06091a0a18350a140906 54
    0x1410116181c8010b200303045040c00da000c0e900d944240202c00300e16075003091100d094040c00351100b481c0342d100b880a0742d0365103109039030520100e03800880c2e00c901030031410316181d4400480d090100d00c00c3c072030000071440d40d80b00220590f9400c1e070752007002250134280c1550031460b02c0f04031030110002c1d0450311144d8071040700351030701140147c1e07074032500d000c43d10b061010803101440010944003241660801030290351140d006026030b880e41c0c0501141180c0c5501d24540342c0da90518001210385402d0340d40b100e054034070841d0300d4180042809402041a800c3c0c2d484405085198042d00d02caa21314075080d60103060180001d50795401a00404046d00c0d80942680d0803c0d4020b0060312103800803400f01d50030080400e0f006499142040581c4043c40f070700c480159080740800b980e09a4035602c40c1403040c100c600702c0e0b00d00c4801c461441c41500100310381c0080100200c8204a03c0d40c030611859600e0082e8000080308042d05540104030007501036000044028003454001c1c0306860031120b40700088a611900c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 676703705 1250 676702455 676702469
    0x7050a05130209121203010603150b0a0503070c0b13020a08031810050d060f180e1f020d051018090c1703270f1206040224160309060e030601 62
    0x12a181219031354001c1154030b1011000c05950301c2008a0295080d258070902403000800d05000450540c0b0280910380c0e81281d0f0140a110b0901100342002c0340c095201400d00c00400404440004c0442d0040c11041d01600703a0151290308601148188803429607158040f21081d00280007940d220f9100655800002108071001010b40030020720036105070184a00344905907251050100d58068800300c01400e070381d40d02100d881080c801e101e04005541c1003207821007950308942550100c83d01110036105c1c000e50030036805818520144160701c200c520484a840e0260004241000303030007100070200030132460795a03003800600204d03115100140d6040c8168401c00c0000000c01040400910a40300c01c44040007941010b003800f80c0e03100b1014907400b07490a108070a114070942e0030f440d00d0f1607804480108a400f400046c1e55540801c03500d001104a05905242000f28017100225100c00800c0b2480955401150703800550800800c440941d81000061185140c4c0c1103540740d50008a0f941181d41c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 676704955 1250 676703705 676703707
    0x1050405090a120903030305090f0a1b120b060f0d0f020f010309060f0b0907030c0e0f01050906040303031a0402040302030a14010209040c080f070206011a07061506080907050a051302 80
    0x42920307880c64200c03100c00c0540103044040c003103c64103a00c4071320300044134000c1c0d40a02181e00e50f10600b81e1200c0c68600b1581850307128409503800600d0b00038200caa00c07080440501c0d0b50716620380103940c0e1440006c20850f051101201044818686002e200d0f0f440e65050b82d4417564680d481d607402c00a2450644007078402c1241d1485280240e109411040345542d2241c03007032041c102c80c0d11f140030240040e051980c0c828100000081c1c60b0070710074840c85a032140e0b196510b1440740000d500b07204001c41e0002c0046c2c1000802c0020504945688005000541c402d623000148005202805d4050008101d01d0500c00d500411081000da580029101e5070780c0c2c3c100da80d4549504011003450700900c540001590031a092196059080d50040c0180e407162080880c2c201041e52490000c80e15040e0900841c0d0324225036404030601010308a02510306184111400166000704407101c121038002030b401040029080720421401c20f10074403000b4010101030700c0d00c0c0307003203801c080000d1880d00603ca44100080e0b8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 676706205 1250 676704955 676704961
    0xe16080637021308030903010c020f0d08041a0711010509010b06090108070315091e05100303080424020405040e0705030c0d05010b06070501022206050f0304051c050912070e01050405 80
    0x32040e070445828503407610320018091343e40c0212503201d4103c025564443e500c0c041c00c1030130340c1d030000c2004001d00d14100040c0c01107815000d0103454400c07020f801034820212000d27401c1c1800d1220300031240954803d4603030710124411801030900b5190014000c5036644d05009103c0c0003507e4140948082e4030003400c008513240d80c0c54100302e00070021200000c024145503100021134810a9221468040038401c000204066181c415415039200744c61445400b0301c003000400110740b1419070390350410f1107040c11400c03848140c041e100760501f03000c0380845119030000b82040503181c544100800c0c4100300002d400580e25000c0041d4031110044141d50150120349615000c0110a500800c02d411004048584594032030400038001d40220703040d04c00e04030b0516421240c06141d50031081c102c50041d0344881c6810448611482e440d08007074011035462182a407034181c0d64150101d0840840401eaa81c47d885602c05020400b40c2c8504401d907005640200005110070301303846225905440042c1c3d000300c0c15032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 676707455 1250 676706205 676706311
    0x220e01030b180a03080a0c0306080309151909170d0909020a0203090a03110f030a080304080a05040e0f0a0f0204060c023a060605010e090402040c030e160806 69
    0x202d0070200c910518000e08a4000c209a008008140520702150040040f030190307110036000c85000b4011815a81d0040c420030340700d49090703803800c1c120304440c0c09224200381c070309800845c603e094003100f4004541b440d24140304c0607801c030190040702605000100305003408444080d22242445c0908454940c00040c0c5551150007081140c40c0c0d01750103041c20903281d5a9003030045159003401c580364030509451419a42034580001d03a8110316420040f050305d551a0350b0384600d00c07940b00d41844810b00c00d05010001c0e0070011741040902c9a00c00036030340d50f254642816118100c1f1070a450241100344144020310000d43c2c08108a040181d060342ca1a0100442030003004009035811015a154007005111703100255021031500000c512652003480160384800055940c0100600310640101030300c00000c000d864203400442120b6028140002e0040e00c3c07440a5003883c0b0319203070814011001c080204203465041108a500040002c0065189417914403840000b80110b503549d0b100414022441c0255 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 676708705 1250 676707455 676707481
    0x112090209070f2c030601050301230613110705120307020d0e0a0b0301121103071406090d05060702030a021507050405060f0f030a0603060b04060f1203140c0102220e01030b 76
    0x100703048000303511504a80b80b0700044454034414178080c2c040c0400000c1c90781814043c150040c848040c00d1604050703013010b2600d00705001000107900c032500c08400c41e10f803181d0303215020b2918200f49034155a01003e080540c54140e00c680c40d011242e40420070007030780700da000c550b02502082c40c1c81d0501c1c480d00d80c0b40c00201031414a410095030600d00200008000c525100052202d41c450007a505285011004141c2c543c106446501c02e03003801c81c0012001441d280000b004c0c003040050140d9019211621900e1078150111100d4002d41d00000e111040c1a80402c8070f62204004200d0103442c82c43e000c400104a23008030b1007543e01078500403030017180e07143c2050b055425501c660030b00e03541c072450304142e00030107802d5a1106442c0c862422422000743e04090148800f1303600500c0d0210050707803809100e400b4490a4407016020031180940010340664410004d241b80003e01700050303160a8407003c840c050040d00c001040c0f41030600340f800c10031410b000c4201811203820103041156a1342d01c05411140c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 676709955 1250 676708705 676708727
    0x60118090f0f050a0915050424020c070f050a090203130f020a030b04050a02040f0b0a180b280501020316080a17090105010807050f0d140a1b050112090209070f 70
    0x200a0400d0f00b0809146a90780c804c01145020f901d0307014088002000180496000707a402400202080c100650700001c034034180c580c2054005001840c01e840f400030181440e8182e040b101c1840100301d01004145005189000a01400c610851450404440e06029410070800050094000c00c0f0391000f556280c0102100071900081880e07034504d42803805c81d4542640b801e0407440f440c50207006103509055485a00d80040c4080c0403001041d08000c810700305c82c251a004c11448585800030302c0681e40f200c1120150034080049031401c0d001d02c0003801000804141c00160455105001c03d051904a0040404000381c0200084e666515008011a09050202c2001c00c69641100a10040072015405141210b6448040d280301c962034038100321030f43c0240c0a40543c4445444c4044000c9051000c40c00d0500f01108110344050310295500510700503284070b08480e41e424003400704038030b503081101031030301c80342014ac10010391b00302e17500013250000f014291200b0849900d0800c48214003e07440c1c412 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 676711205 1250 676709955 676709981
    0x40b0f030a030503010905070c02010c0f020310060e0a0c08190207080d09080702030705040c0f030e101812050307050d0513020312070309120c0312020a061b08060118090f 75
    0x228907038041c14060f0481d8020300c0b0308106585820700044109106421640030594141d48800d952401e40d110344100101c0d5440c1a64540500711217202000d19a10481c1c00901c031000c994509860303c46050070846d02c0b0040380400384035580041080700700f018400515030113060900161903a82d0360400022600a42180d2060b00b1701d00b101c100140030300d81010301310f0140708404854403640c60783c090206540d81880c1040200b0015141d402500d40643c10140050360120211035115040c1000401503403c149024642105d1a80c4000180491440c00c58903401207410f12600c0c60424a4005203188074564081c0d02c5030741e413880403e0403060f100c183c103000907800400311011418404414412540310f024100d003ca00d1056000604041c192544264240c201c18520700062642d1104501c2d020342e40290000c50151409400008500340b0038038900303210703030b4070701010012406d840a070848601501c81c6040c072210301240030031140b403103d0703071003d4484006000c90301318450b90b1500c010b0114071000d40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 676712455 1250 676711205 676711213
    0x20d050a020d0e0d0e010f03091b0302011202030912090609090a020d14010815060324161b060b0a030803090f190302030306040b15120118020414040b0f03 68
    0x946900e80d81c014003a03014404a0412185208009041da2078280c0000d00d404603180c03822441c959800345402130000312143c20f000c90620b41ca80e6801d50f0a90108050700a240e0038800b0520a40d644145000302070b105842c821442c60820700100390307980304100c0340301d85460f400040411036a19514140c8001e0100907212200a0900b103111034040c0d000011820329062a0000d174407030402c0511880da04070342180e80038200141d48500301d0750982000038a000c7c1c05204060154104000c882c003803603641c40000992584608041d07845200d00c8502d5024035040107400d201c20658040d0411585280c01e5004c0b000143c0c1d0f0300c40c0f10100d04c200980d54000307003123080d000c4100302c480040403c242e00000b4588041e1030103e108000c42c9003a1988106010340107070b00900c0000d4aa040652180d001030300010805c46101117070110400c1d056004290401c44039150a0040044d02c0100945140c0c41030702900c294280350034030b0904010810381c5c1540620980d16400160165140d00d44280b64a00307000e0203035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 676713705 1250 676712455 676712461
    0x60e0d02040603080a0f02190c18090803070e0f010c02061c180f060f05190c0e130f140603030d18020a060c0b0f01030210030902150c1b06030108070501050d020d05 72
    0x80c191909540300440075000c1c074045680300c92448103c07108e00d00ea0110b0100030395130904407150105105c10300d40e42503981c4e40303c6040340402c0448028520450b2542d0b070700c03080c265440e001d1062001c0b88554450602c1204442c40d80183d5400d02a52250102218025040307002d0001c210007400c0401c0043e4803c583c0c1000e80f0041c441011401009103002e190140406000080076800701c80c0229401918206100d1030351102a000d9007100803c1007642ca00050920072a000150310b144804421032855a50b6492b01e02d0022002d0040030f180d102c020401803800d20b082000b0a440e481410030024038245d8940e40b2820290440d080c540d071068000d415440200d44510f0044c124072055101a110681c258002402e10034541c080503041c1c0790b02411b03514a17403070360440c20350191880b01001c0383e00c80c00414900070b00088082c00341200c6e103e05401403800c040e00c0c041051030980d1041c0c546016031400c00040c45085000038008040714000c1c82c009640d4500416032800a00034001d542400a05103018 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 676714955 1250 676713705 676713707
    0x6080a060302211b09180f0d030b03011a0f010507020a080f03070c120807061817030a0e0a0506281406120f0606060a09090608060a050603030301060e0d02040603080a 73
    0x30100030203240300c00311981c00c010115000c0d40d90714049425a0711060307030b41c001909440d603180c1c0b1b503044c070064500301d400c00480c45408504210004c408070000070b0750b038451080c082c502405440c0f038407003d1003502100c0030118008160303541842e0b0781c298180a8000b44040c115150890908010010881914410000d41c42d94680301c1d44065000c0e601c20f0300f104008030f5040203a5040101c0283d01a90551800341660789180c054042440030040076440c503112100803405075061500c1c40d0700d6241c1c0c1599a0b250014030042110140c2011700c2050744403402030303400100001542500074030100c004990b4007119880038042d005400c102c8000490a040d050301074003040b689505d014500c1100e1840c40c1100b0980e02c07680d41c01c07004d0040596540404082410ba082001c01403800d81e03054940100c4071512103060b41c00ba50156402002e01354802c000704400c0c000c451207110380065080300030b14619454081c0050249001d583d040344030310040143c40045546a6014900942d0722003499900e55410401c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 676716205 1250 676714955 676714999
    0x8060f0409050d17010e070305041104151707030c0b0304051207050304142707020c1008150a03020a090e010f0c020610080d091404110c06070e03070f06080a060302 72
    0x10030204c1c2044d00441c1e1104035500e050b100e2040714450517a4980c0000c8000d03040c0a0400c3c0e40340b400c0030380d000035075448600a0010151111710441341840c5020000d00b011159401d1b05c0d20030750001c600501c0000c1140c070b8002c0031100c00394220b685030348880c202036007850024402942219000503090301000804000b810403110b01003544279044003150203008106590360750b45010304804000042d1041d0194900e03e802003000d104030341440190070301049481d2078802d4002c3c0464901410000815502c3e00c21044105094405519a41c9903030f02240490045004030144243c40b50001480d44900354007240510100308000c1c000c140201030040c0d1100001d4881d000200212000800c802d0710010b05100c5542c80c680d24081000d03e031a80f006c00711125941c0d21540151030715040c00706a00c000b00546103144d40c403001390000c0c1c180004044c0c6010301c01c0c00700c203001e60001d071020003c0a1603006580200ca0142c20060129a030b4840c1e0400186800d41000398040500700c44204040c444030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 676717455 1250 676716205 676716223
    0xf0d0e06040e1905070804231c230412020d0302010b15030702011d10200301080313082a011e0806030c011704020d08190509040b0904050a020108060f040905 69
    0x2000070002c60300c40725406c40d40603104844c040c0000400c4101c103051030a80440c00c0000e8207c420541d141c140c0f110100325543d01e1120800e000145003410350311900c410201c200c041c40d002d0450910318240c40c0464889010a540300041d108482c442582c6c41498004e4004101c081c4e0f0081c2081c194503410501140c0b590001d171000c030700540c0307003102c44201002686035001b0b80d44503a4000307000c01e0100a030740d070010308481c1282d150340101e0751030340080f03000c4e80c04040c5001c3d040000256847e4841008400e07602c0002d680705101d46da010300500030030190102400c2c80003088660300742982807a00001682c101003104500c08011443c1613403a90490b81c0851024011032080301580c4c0112200401101c522614035211013089085501083c010301e0314034400e9003010300c54030b8820700b000d2012446004129000c1c0304240820000a404500c2c2d1500b17100d84500d600d0200c4400b026800d2684031a99035544803a07009040c40100008203c00d50b444000540c06084000e1092105403020304d0301d241c580c0140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 676718705 1250 676717455 676717501
    0x603050703031b0c0b0903120f040e2203080a180b0907090b0303030f060d020306090a0b0106030908121008190c0f0e0c03040c03020901170f0f0d0e06040e 68
    0xc0c0f41e400c3d00c0c0c00b444216000b2115084100042c0b01030a101803617040703620602003954140b04401860918903481c1c00035104040340d8148641d1202d01e4006282e03082c2a004041252680b43c0c1074039071040e12000a00b80404caa01450850031999502c0d000c8001004a6007034200c000d200381035201d080164240310244034284407030607110400e030b03108070a4042d252008409541508180000fa06000045a8455200701b000702940082d0b4015000319040484c01d840b2010b80d80c1000d000b10b014043d100742c0e042d005003803910301013051100030345918111f40248000c02c40390000d03100224100c841480d2181c1c002d80442403d1301c624119400701c50111141c01c0344110341c1041601c4c0006100380085503214201d4442024135009035450307869031081a03000800844008054000101c056194006850f02070800001c07080001d00a49011518106c03230b8016100c05540030444a054040d400f01e00055465030a08000d0940b90643c000034003c1d000300c0d0821001d40d6040300c1085030401c01100ea140c2d4131041c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 676719955 1250 676718705 676718717
    0xe030f160b04120e101d300f1501030b040201020a17040e1b030606070c080d090e0603301b0106180c0206012c0f06031603020d12050c01060305070303 66
    0x3c00070900c001d0005c05039960000c590b03000200c510720000c40500344541440180342504821204008003241206100040c05040c080041c1110310384041007240c03144c40481c0d0050511400400720350b103039070805000c020441902c02d400f0030704590003001002c00c0a540314200c0a502002c04484003604c1d002071148001ca1120800441c040200b02014001469008100300d4911f07604c880600000381c0c0100c40c22200002600c0000803000424040c8d41e91100090342d4078024140350100010002101800c914482d0700149412007030840e11400315020714540c070003030304441c592403803000000c0c3c01078002080384460301d5090b40307809003019442002030710080c4091a031407007440003854007110094560f000260303000a005000c5000c80302c011303020100815000030140d441d540312440031040250384640540e00310301c003885498035085c4034045130271288070000e41e5824070390780008004850107280502140c0300ea46400c10910300c81e90072145803080c048001e01c1403c1da00e01d451550303050584030640010307171 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 676721205 1250 676719955 676719977
    0xd110a0f0c050307080a051b011a01030203060d06180c092a02032b0e012007170703050405030a0c08010f2901111501050f01030e030f160b0412 63
    0x40100c00301d103a070581207001581044425554441d055100900750401d12109100c02d02d01e01541d0f24540d03464400200001c9a000300420b440100c40c0304242100b41814014010030a943e10b40c0c442000c100c9400c047c0c003080281c68580c40b68903808170820042e060101d0300201050001150300811117000080c500800a031000b10303000d4024400101007440183c20800c00c005141c05d100d98840207214030384986c00c206403440ca441c0c004954403083d0f0b4011903510307081407030307469000c0c0c0440320007580c88541d0081c948680741d65001c511030b82030300d1381d01c10f2040b0114000c0145407041060383e000d0600902203c84400f07150a0141c5050250300c00d2038010340c28410141d03108950341c068008895a1800031648541c80103102026922400d04120b0404c0220031880134405001c0109032409141000c00d865554180b009001d01c210207802250b061600f09150310281c81f2000049a000300071221000b500c0c0e21540501c41921030481d60050414070003041030106200080030344922404480d160026180 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 676722455 1250 676721205 676721207
    0x6030b0a151406120f0928150902042d090201080117010f051f1a03010501050c010b03010203041211010509101a0d050d0914091306020d110a0f 63
    0x200010600005240030031800c000707442c0740c01444034100000410850400c00c407010903c10050003200c849031300405503070500000740024082055030400030400d04030184016580664184001384d0b0003401c0104080042a00c482558400d01d0000c2d4020001d002c5244110703041c01180380e003130b51786604211090544146500d45031080d241c03d43e034103850303521a41c1e10700000030003403035910700c80c40c4099520f52141d048840907520929104000241078001c6958050391000028141d279000388414880e200c940000c40134015080d2411600309280042d07176034401c14055030151081a01854145d80040140b10800005c43d200803807a9005a848540b080e0038992502c0c03c0e0340083d03c00d480f1582250a6860145509401a8000d400101c3c0005130050042c3e000c9031203280d84000554082d00121440d11800341d0240c0b40a0040452504d0406039519200001d40c1201c2d0280403641d11241109802c010411503805981c8054440c10f01004010f0941038480c035141d2021640c04009007401541c81402c1d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 676723705 1250 676722455 676722461
    0xa02100315060c020f030607080910050108150402060c03070515150114033d1e060e0406030f030c05070803040e150d05160602120a020d1d1306030b0a 66
    0x1907018400038841880c00c0010f55240c40041d0040ea0007001400ca0b414142d1800c100c441e00800b030300e50303c1301e070145440041c0030b051900d13401400700042c5c140001080311102c0001c48241e9411041b12001240d02c541c400202d41d44100d1254103058040865417506021010030f40300d03a2044541c06022141d42d503016501e861405421819001c9450000b41c8060310141c40c011316803100e042555130b6402c1580d0030001c4400c1d58001c0c3c8605d9400c51385200c1c2201d41c0c0c0d03483c4c4804014a401d500070701c4005e10035000d21928450902690007007002208901846030340e01c2c1c0048006581140c4504000c03031303481c00e00070300b1050301da08240c4480c070400c1e0002403035240020490f0112400d0000100c01d68841d0400c40c2c3c90403d480600315441100b40110740c0118400380401000150400002ca00d223900e03001c3c1c040d0610710540001400d0541c02d2000e040c03002d030080341b1312149a10306e19102401e85200100c10b08460091210590031000c5c00000d01041d507155400001664082c4a800e200c40d9074101e604010f07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 676724955 1250 676723705 676723721
    0x405100b0a03051f0209120309040b180f060409140123010f05120705090c1c090f03030e01060810140c040f030b0408120709030b0f1006110a0c03050a021003 69
    0x200d0348030b10540800340421144c000f140d0281400003501d0480300e500042d480d0444003408520541000500da076203440c051003203440e140b1b02520340714030035826004104e81d00b200c01481820844049400110303256035551000d000c0640c00000c03000104a0f1170011030003082d400356031003421802ea2a2083c2041045080c050407a6540981002c0d09810103081c0048070042a80c20012031241c02400302d80750381d480c0e1025100d2454282c145880d01080e103c814070021030100d22079071652811030250003154446c080da003d10354150801152150b4050b4000780104401e41c0102c4160180c0d40e15054000041e03000081d0110b003d13000d40081c1d0f241e02c145203446206500c07850b840c0d0703400d0160400018a09458240c2c1c0300b40100c007101e0030800c0c40c0e030b860b082414045840d41d0016440840910402100b076441e50b40145c040c4401601074a04128040710200e40d0340941014400c102880301c0703170200c003040103020003940207a0400000f552031130155038404820504030310a400c258001c0e914640300c1d10402103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 676726205 1250 676724955 676724963
    0x7020609070e0a020c0709020408150a0213090b03030d05090d0207090b09040311030f04120b070507110402162a0611151306090b04020f0330120405100b0a03 69
    0x150750700e400c4600b800960140141c2009805140c20014201f80d191010304010301d00341000e4005003c019200c0031240c040104401c140e9841031001c0e158409507034502c101600d83e141000121011810000b910310300842040311811400e1030708208010a01040b40701102c2d031590211010f09807101101d01c00d9807041d69203035803c0441880081d001c640b00c3d01ca81c0b00e4452469003540e103026240c0c4800c0c1c00603402500b1a8111640b0380303080a0030040e189200395032000039450300300c0c1444002d90f94441054483c2e2110b0344901c1c0c01203890f4032282c00825281102e1642300703070080544400400280780d00500000c4d8104440314030745001a22034054400807200c3c89410001d003071083d014042d918040d40340504207028055150b8003580c00290144682c0e041c15006035440211031030240704001204408054040c000c0c0c010342d2960486a40c803c10402c004104075003404540d440b00c3d0810f111500458882c60719920b1990b0510003800f401090180103140507240c280840307058101444108025484024 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 676727455 1250 676726205 676726229
    0x30203011112040807020406030c06020c1c0b060d0c0b040e0609060109080a0314040e1503280605090309040213080c09010b2703030a1106010512070b03130c09050702060907 76
    0xd0004441034020200180300410001d1426281c1d21071101e401cad40d94010a015038400204007581745001d16800c0e100c0d00d02964820042012980c1d43d5900c01c10140a5600600710554050204046041c8480151a02e2000244c071030ba40c50001e002492019610940252941d40c0420520351040900b00181c90000000b4004610565403c4a030190b442810b50b0380300c501884049900010b010b2407034090f1100d2041d80c10608413070130801d410698240300b02e0224258030001801c001802ea0881c03000e190304980001801c3d0f5510004d41e003180304003d00c070740c0d0140c0b0008820445900c0c200c110810784019500f03c17071100c3c84c803001b0f120300c090003070041d5034010b01d05201c00740c4440042c2181d1020f41400c01c481d402103091040c007080c5036805c00c200090104180710809000c4810800029005080c2201c014007228540410280c40d060113014480007240000001540380064400f990202d85d400138802129580d207600b0b55006013000d60302e040040c040c21000c5035080b8000a151400e40303078449040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 676728705 1250 676727455 676727461
    0x203120907060219110a060c03030e16060c0303090b040f200102030f03060103150324050c0d022b0f051e01061d12010f200f0306011e0306030203011112 67
    0x4280018104d081c200c03014000c204881e812511000303071010042030740d0340302c03e601c3d0740c041d2a0150550b000300b80d165100b50f0115002003140c60255011f8401c680290030a41c0c40d0858504086024015165001d40200844000e100401902e130551710176032402400301047c0d0704203490803802400070390450640164014040720501500050085421807014180000d40f490069010350155a0560090b540b840c1c00300d40b4524040074402c0841400d1118503000c01172403a000c1d101c50300074041c1c02c801c551400d5001c60244034208c072610714403030710401c010015102c1320744801e0140c015062070203c520325941080c01158844003182034018002104111914550303081c0042101d0340701c0828a4102c0e0180c000c103000352252140c00140c2c4c00d030740d2004008a04030303512440d0942654280101f10704e0380030340004000a801c040c5d50581d41055100106a680c039119840100c80b80e41803c2007039920780e0f2045401d151515050b80c852000c41c2d2082d4000c1c840c2e8a8808038802640c0074020006040300410000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 676729955 1250 676728705 676728733
    0x90b0a0521040f0311070b1608090a170d0c1a0a020d0c031508071203030c140409200906120a020c030a1701120c060815040c02031209070602 62
    0x14244030541926804800c03900e5181e0081e4405081e1002c0d01c00070300035000e90091552122021010305c07a02001420407625246a440d054070940e809090345e8400708043d94100b00300741c0d04980d4030308001002c04030901d80f40d00000c1800b1411003120080f5104034030780f040c00c81d40960030741d203940c0c1c0e0411802202c40c114204401c074209001000702c0086603081088170b0012019101c1c085a001c020303500010420b0384036441e1300c01c11140381c0014603d0b03030252004004001340782d00850f0354a54036150104070741015807420303a1098082ca0b13070007011040108001c503c170501030740003500b42d4441c00304900c6400c854040c0c40a6602c00e0f900d1968101c0002c000150b90281e0383c80d102034102e083d11200600c0c3c2000d1070340042c2190884000c040c0095100d0044d04007032110100e050b40940070794505c100c0486903680c3c407240300c42d040d0700c6030406100ca504002090154103141002c3d05a10251040c483d071701c00c4c540002d440354421003007000402805404190001c1f0f00142c0c18050b240039030020042c1407002c1d03138 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 676731205 1250 676729955 676729957
    0x53f090607060f020d0e101b0c03020109020a030f0b070e0a060e031203040b04031413060e1807090504180218190908030403080c070b01030210020109080f0403050d090b0a05 76
    0x190903154291183c03054410650a44000c03c98440c50841c00161a0301c2042a0750801c403111041010890400d0711180c4110502c038070080029490f800d200c0c49101d0a464241d000d05104900650300032a145800400c0c001b03074201006005108411900e055612080246c8107c11031030859134008480110600c82c0601403205284900401012100368000c84070b81c0c200b00381c0c01150216140702c4994280400c147d0419810468003014041c16070030804100704940e02d0708118418401084000140106181c881501d4007020070703c410381168a52a0065004d41006454481e8a0050389004241651062100d070545c400725401400c80340712941e000040029800054500d01c1e00c04190300c05840704018a2286d819078078824030815403249014200544151300007042c0c100e00c40c00401003100047c4008104c181920b40c104c60300418180700803012401454010710040070110b00103000400c0c14084d0002e001220b1041044600c51039903004100c0c4d1110729031041912000d410701280f071015001d10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 676732455 1250 676731205 676731217
    0x705060a03180609020a0501021f020307120f0b010f020c060d0203090c0a062708030304020409060e030c0106150f050d0221341205040807053f0906 65
    0x440c01203030020007900d060300b6891034440c1c11900c5541d2107040001314103001945500400c0c090028142a201c2000700452040d080c0400024441e4008002081c1c54003a400000090500340010003079007803d805014010243c0c1d0795101e01003400e122030401200e20004451010000150405003028900c0300c43c0400ba42015190540354014410809404e459080249005051568035200640d43c80b0114028100c07141c1000c81801801e01400c0c400700c400003049a4000d40e066034000341145407410904000c01003202c2103241400300003908401c00c01e054200c0030903500c681156030a13000041c401594412040d41075840030032024042001c980c03903203601400085e400c0640700300c0c01d1400c4400700301060703d0850710100c0d003a504180d00c80c0c900348500c000c00c01070501d001100a0480c191500036000081c040050040d00e40c4420000381080194011350b010300c0d50050440358815030600210f0501241490190032601e4032001c401d4a05911860011907400c000c690142740507144030512400368844 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 676733705 1250 676732455 676732457
    0xd0f0204091a1e10060e280302041406030d08041703250c080429071a13020a03030f11150910050105090612160303120507020105090705060a 62
    0xa50707840c00800d0780c5240c289100884410160554645491180e401c0096802c10340402c2845074100502c0807241025102500d0680c00d10f0f01180100c00b00103083c010703052600b1a00a003030031070a2500706658034185004c0d24070031074080c40003280a0007100ca4038032007242e4456150307111400780c0030703000d02600c00070f6042130284a60705441c608150a000c8207900954070219000b40716182c044d88403d00900b112403a12091426020744100c645400546014034061074400c0d810034403440e0f040d49207030100348400c0c9440d0042c6c47d4541c909420015003160700c0b20b83c41484100d125000401c2c011000100d0f86180380d00604c580c11150564034100c0390006240c001d0340074402ca00580b0b0010000800c40c44441e500c00b89450005803400f030600c0d03802c01081481403500241001c1c014003441e52010301da140d10603010f03581c0725450351034003101030300d0510122100555201030001c080140750307000600900d101c02003070040c8195210749008a0880320700302c94030812a00120703070601c51403805200030301d80b600302 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 676734955 1250 676733705 676733711
    0x40f12020708010507080a05060102160603050c1b0703020f0613060c1a150109050d2d0f0b060103050f070c03140d06180501270b041407030917090d0f0204 68
    0xb81c0302d0503400c50740c003a140d2401080342d090400001b48001e02801c0d030702480c28409050b58240501c80c5920703502940c003da809240c0ca40e0002404000640107440800301c92081e01e00c40c01c9100b040702e41e03c80000c9c0c00240c1c000c15035013040085504121084984c01d040742624116000c0c604038045500441c00207045071f00200d458800c47c46560794011480c080c0100c070030032540d280c40d6000054104486036101500403620701210101248242090701c01d2192500c101040c60005900c0c140515a4500d034000c00050070040468140030090040510540003030700c0401854032040d0028011520440c0c040f8006149101c1040000340708581200c0102d11915025040000f80d24501c02a10450b07048240d488144031540c5104041c9801002c0c010700d1012107860310151820a4552030ba0090440100050740320391160780c681e00c4640c400382901241c89000c50580c02c0c040001006000d0998007501c1c20706e454031640c5080100c8000700d45560700014080c074040c1d9080e5840f82c3c07011600901c1039902c00d903 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 676736205 1250 676734955 676734959
    0x20304030803010e0906162f06090f010e0c150d110c0d1d0a05010c032703150b03100b15070f03230409020d15080313090203040f120207 60
    0x404400b442c081d1800100c804000d14140c1c84840c642040100b0541103c806d20084202c0c01d50001031030112100c1c0c02c40c0c03030302d0301116604402c410240c50152900d0720303100c0c45080095000c804100d000b52001c61400900940d00404611030f0348001d60240c040e80407a50385090010010302c000107001900c2201004030b406642c0b03060584042d008440080c01030741040440040c03107940080740c0308583e154240c44541c01c00c40c00e4003140c41c2d00c6040c000e184c188040a0885024180101440c81404d0100610200801d50521029101d60302c01d00c8125030201c100c2d074061007601102c0c011142055000b41c002c0c59403052001900d4041c104031401e0581155140c09442c04403810b0340002c104c02c038050800c501c8110554a0020015259032500d282002d890703a8103034441d12a0803048400700d8202c0b41026031280d0b01d00321420300401904500d000a01c00f940c000007443d6001101901c2d40d0300c1481c3c203181c44d05503250012350503440700f218000e012141c004000c0c800500c2018008026080758411030b00d03000c0d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 676737455 1250 676736205 676736213
    0x20a060e0f12160e0f01060c0311010606170f0f0601270305060f060909060109091a0916060e0f100c1506030510060308070f050111070f0605220605060102030403 71
    0xc03101404168894000c240c0e03441c20700e0f0016440c00c0091142d0034280b4118648070f543c0080d8030406010b00310400030b00940400c1818840c0900106070b07050b2000030441581c2d101405020402652003c00203d901040040d100c0514081030b01e101d5812043e000c1e03a5540c450004507803440c50f003802c4480040c41c81d01c50b4203030744990502c2d21010b10712401c000c0c8118146100011000c03d001803026105025010420217403c1c000704003e8110307a020080891305000c245084516200c1034844040d5018004041141a070000140f499020b41c1c6000c03489107458071130b0030480780e06078652006608100c0301d005039000350824030000400100f1b9842c24a006542070350356106004052600e61800740d03104c100c14000d004090180070b14030102c140080000b9491652640602c4c01486c002816003034403848906c0612100390084500031503600302c415034481d65850400c464800c412015244249084001028540c002030012614412068400501c500a075202c402400000380002d04600060000100103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 676738705 1250 676737455 676737469
    0x2205090a052a0d0212011a04060207030f1a070206270c0121020c030d0c05190302030a060e090a030207150e2e030911030c130e03091002010b120604020a060e0f 70
    0x5d0f01d104481d010b40c0d407400f05020b403084003d01c00b01520343d00c1007000300501900000c0d0141100c0d07000c038924680c44441d007071600628006980742508040c000080140d03042d4081201d6115007117003d07503000040c0d1800030049140c041e102603880154481c0100d20303000c0d8080c0c10000310150b01d440b00004140c070710000b80e80590300f021740096420303030010500504004040c012170904da28249405410205031400c2041e0444050529800f459800070118600320315a4201502030f10070b118680140b401e248016642e19981011300f64018007034010041000354020f500301e02584610340d125800c121040c1c081040c404c0e52006202e001e0302010a81e10012400b02030010310b03d0646031400601e40c10581040d88444001048441c0700e40c00401c6050f02e50f036100505401d24146000b4009200701920144524500c02c08101c141d004804c007086014159054112418070003040d0794200c415212100c0450f541d420580b03009500041c10401480134620500c41403802c401c00900c03110f248150080840c0e21 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 676739955 1250 676738705 676738717
    0x10902070206160b0405071502060109050403030b031c110303150f0319030203030406060b0c120a0507080714070b0f0910090b0c100b060c12070203032205090a052a0d02 74
    0x103030383e11842040f01b0b0080c148007000041641c0402080301c4500d54030f000b529504140901c4282070303903540c0450145072003a4482c041800e0042d01b1601500422007004200703192104503900080c00c402c0041041041c0030069074012a907603110440c640400204004070350106941d001d4152040103041041030500300c0c10700802c607010760051a03032402c05007800400d44019030000c0031090420445003480702800100308444445009206480d480343c120116075a2081d0080a402c460700852a1014407031403641c0e244d2800c0c82c460444040683c2e450070200d00d03029002240141001c10702c25a0920304014004010314070040c41d241a00302c3d12030112100d01d400c0302d12180d11381d51014108060031000c0b403040450b404812201c0c0b40c00c01c2030302244190764429000010b0b14203100400d10104646040040d2400f10800d04046031880030060b54100c5003030800d1081c03620910b12032b008518180020310552740070760a0048602e0407040c3d00502c030ba00c1d07a00890040e00b542202000003814809940c4040c3ca8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 676741205 1250 676739955 676739963
    0x11040b030303250c05061308190806040b090606040b030402032a040b0103050c0d11120103150b040c090506181315050f01051b0106080d081e060901090207020616 71
    0x9188100591000c40f6030480703015500030300500e624194040b1303200140c0e80703034005d2004030011241032452800314440c0c00790741d4440014024000b220f11540381c10003800e600c200000e0740c04000703440280d8204200450305441c91034006004000c240518200c0c8001590f0090001d0101c0b40c0d6803800d00c42c20141000a03074035029081000c0340c07034021145050700900c1048002403805002c07908094480f11008d00c960359003a40b101d5640d5405031039661140d000d80b070029004814a04d090742c0d40f4207086500c101c024031030410740d81c40c3c480d1001041c503107440303040c00c010070a6446014290904d02032114990040c0c40c440304442e450014600705680b46000100c01c42c001c80c40c041142410381d81000403056035908800d204044d00171441401e40d03401380c1035548883d800c0c0c4011b600c160300500c0040c010440f0380c0000d00c0a000310303a08007074165040440140074152110b07103e10020006480ca4051403000d48810b40d03c01d41d1040100070300c41b001c2d00906201c1c1d00091202e0314140760901502042500003030221 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 676742455 1250 676741205 676741231
    0x2030c06100914060108060d021206100e1f03060b1305270309060d0203041e03051207031b03020310050a09060e010b0307050426060a0608070f0b0711040b030303 71
    0x8400b4006500505051034801a00300c3c10078204500068101480245000c0c00ba000b051504800d550398010f0200036400d8240036240c3d103081a034402070b80203005001da040032010b90300c00700c0c800290000140c0300090300905034901103410b50341c0c0c11010304160a043daa003c01c0d24807036045446010b11035140186101190104100781c04030507481e2000668201010540080c01891000c0c0c0318002190412094800c005036a40d545250004407d40550b0042c0607000944001c0700800d83c0100040021000b20710f60120540d0300c11b0411030944000749038408000c11a141e4a01c542e030300a401070b607004014010319001d016111404682c520381590700c10100c3c0794840508001017201400220f024110040810b403442c03030100c401400501c541c0c455050320b0045030f61090b80c070a0b0038803c2c0c081c9a0460300191101803c0c182e13480800f9004d00e0207012210300038410001520041200f00500b03c440c0100d0490410b00152540e404449807004d41075000394072500c017205c26030780920041d0f214082140303e030317 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 676743705 1250 676742455 676742459
    0x304030305180606061b1b030c010228050712061a040c020307120302040911091c031403040203010902180709050901081510030c0303050301080d030b060301230a0609050108060a0b03061002030c0610 87
    0x585418008003000381550030500d04e054614003402a0368100d600d030444080e248517014644246410b80992290253f018081000010400140c0007c16008028403001d400c58440c00c04010840c0d141044800c0503074001c001e0140026034898808a01c11001d0a0040c2440da4403945081a00d4201c1024860b6880003d5400340c14500000340068a559051081340e480c0c00c1940e0140c0110034a48511401c010b01000280456401b500a05e004030b5002d40661200c0400d0190141904003d98080000c241881004901424465035244c102c0b03168030300400310200a01d00c1901250805080712100c03280050b00400403e454401c03031002903100741e55955880d072411003041c2c03d0620301b004a808046c00c000c03002c10680c2e44e1303000750b80c15500000303280303240038540c030404503220389404200d83e4000d036001e24001100c580000500048417001c0c1c0318a280b5a0360042044a1820b641c014039103600014800704501d42088039006110309031a0044038901400780305124a8410100e4040c2c2c407481d03140d082 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 676744955 1250 676743705 676743709
    0x1a030607052a0a2307094502010c0b182514310e0f0a030f090815071e0e090a11040b0304030305180606061b1b 49
    0x180441102c1e070048011444103181c030580c85450282c0c0103018252401e0341c107040d15203442c081c1d0510501d9030048a03440381d5984180702c05800703d469614081300c0e03409422180c1140b400600029024105080b1064520001d40b01c01000c04060042c1e0400c00c60030341150000f0750500314035018841c0c08400b58101440e01491514290440001b1845102d402d01c086588610a4100c0d0064075007002d1804090311090011452540503158200c00c0044070000340500c80c40d43c0310600c2e0039100d070306d0014402c840380c0702c038280d80d960700302216008a64000250b020120b84a0011681d2885691804403205503441101c54500000301d0300040440300150240f009058020443d01e042200c022020b80721076414101c0070f4075036400a4411405034011f40700190954040e50303c04400c640e14440c4240c4c41f41d807a07020444d215042110f04801203882c160220f0300e92006040f0b01c2e9411069080240742070ba8400d010300109030010380e51000c56907100c4d1b1181c00350402c2440046c5441c1605503d450340d04400900b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 676746205 1250 676744955 676744987
    0x240307080f0127030507110d1110030204030b06040209030f1e1b0105070b06031212040c170a0609050a02060a0e01080109052205121204030806040b0105030106031a03060705 76
    0x1402065900c1d0350602140000c03034003404444180e0182420341e00c03070613141021442d61801f0a41258030400c024503407001c004128641c54089601520406e0806a00c00c000350124415400003900d0348128800040c0389141c550010b0240e00c4001c0c05503484103010340d00c26172412484001d031801c004030b808041c8502a0080010032161280e06c900c42e031521206900181043c414694042e0151b00300c000001c410351410000c2c0d40418a4006900381e80e00d4203030454044641054504a0302c01045c04000201310035904054100140d03002c01410b0141d40680d034681c018020948200c03401e00600c2c4192003d41c0c2c0e00e5024020150444d1138a00ca81d1814074001800481c050300300c3e0403080d2901003440100c64103581c4801028428010b03005c03251000e810305e2480d0001340380c511211031000081d4000040d2502400238041d03803003074640964a455400c10801564180f40429000400910040144610a801600c1044034000e40c0041200444002c00d0904404039a2000801c600107107841c841c0b440c03d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 676747455 1250 676746205 676746221
    0x41508060c120712091b0806160203040b030415020d0b0315040b0a0b0d08031f060c020306070503060d0b0403030519021204080906040b0c07030201140909240307080f01 74
    0x90101d071030541400310070b05505402521010030001c10004058801c1482c0c0c1c00840802e40000b610340c140b680382c00441100303807441c0c016040240204000310b42594107048249030508c4a9801460405082000e24900c60b0002401510040c10443e40e080780c1420520007001203006014011848401c0681410b1070020503c9960480854803000c01010810300321906400103140400410300c500043c001510304640400080c00c500000000d122000000c1c400321280e010b403031028291401c3c1d4075401641d03a004da5003c0a500f6400c007100081e0703110300c82d900540d40210300501400c0c0c1c03c01d0544901c40031100403a0100d020135905d00c140450300041c1407410117004003900095151000010f43c03078900c000042d00040c8032090124422509985d02025980500344140e21682c484914074203503691038200d071009074046200950f0740380b00e88883d10225005804054a40a42030701c80d200804d50300300200025108038501c056440d0780d02d0ba411f0103200001c0c4106001820860143c4040c207007160515 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 676748705 1250 676747455 676747471
    0xf05010510080c1303080f0d060503030703021507030609090605040506011e030b060d0f061e0c0816030204120b011d10030609080d0c080702010e010216140a0204150806 74
    0xd0710002102a5100703000d203900c0310200041d152100c1c1a139030380b240076043e2600000c209801c0454216031a0500502404042e110701030207000065403041415200c1c8600d079405401604048851090300052005a0740c10400e6440c002070301903918100c00007250030180c000c03241c03651035005000070300c4001c00103135000d01006820101c2500c084d101c1301060350680e100042403c0c08280000d41c107a660b00000c20813554028030307140300c94405450701030020002200e0710603007012180516203441d9001e1140c000d86d5038180d19a114191201030040308688149202c1500b0141c0030000401c2c800d112031141800d0b1445082595141e5040445031031700e00c801da549000c01040480c3c100080300341a420f14000b02d07034200d10001041c00780c504002c0458400d47c6c0b900c641190605d0000610154824004c0d4414802540204030178a040345a8500340c1c03045004e50360345e03210380c40130303140c04118000010a031015040c000c82e8940142039010905540c005000c240801d90301750010040c100302400896400310f11 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 676749955 1250 676748705 676748719
    0x102031503030a050a03051f030b04030306060f0e040b0d080c03120a1104060516170d15061d0303271008010302060406030504230f0d140d05100f06030f050105 70
    0x300c0f00c0010480c1c050160f11600701038540021840441d500d011449922102d04c0643e07180f1900e0782440ba00741441680c08130f0019141c060006101d07846141c40c07030320012983e034035007045d4450f460401010b0300781d410345554814107031484e1000013105c83c001080b103000104080c5446503e00300b000c030001c1400400e021111030420590411000e800c90854090329103505180e40c035108071000e400f4501216200c018081c4003c0800380c03494014103005803146034600303141441208010403550360705403c2c500c02c01c400700705100100302180000303111161091b40c000e8102d0b806c000e140d2801d4080c1e91224004a84140d1542e05540c0150804a01e4502c448006040080c1254919800305441c0e20803446070104240c0e6400100c0c00f007024101041c2c11781019058404940c07291910040c1c0c4071707602401c10b5822440f0300103000140c01c0c042e22000d1444400c0007040d50038405c140300b0741c00142c500108008c0d00e0504440c0c000c100707403801c80d032004043c0c10700c2c0d500000c82c007621124030000c40700180c2120303205400c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 676751205 1250 676749955 676749967
    0x105090c012601090e031902010204051309020306040b09100f06150c0c0e06060f0705070f1d0c07020102010605030f1005070305090c0f041506080603070e0106050f0306010c14010203150303 83
    0xb21100645045920580c1c00266490044084071709600854102c92102c40d0502401c10030300303905402030405d490b0200e5030b84c007400011182107c2240c605800c0213401d90030000002e008500f01c00f920131b901c1407070038041c0c0e403d6040380304200085a00c80080340d0704903661030301c090001c40700c007861408044c1d119061840381086961983c10803e5a01d01c01c00a01401c6800000d10350780f01c1c60181c1d842010441c003481d45468403840e007152a0302e128001e5140076028104005400f0052040420105000311008640c0340c03112040e400b05c503030240100303a05640d01c41750b000900d514100f0144d5140c140314000703000c1e031103044040141500c6000d050f210400d420711092040000c8049044200e5800031100121103000000115014110f00208080c46010170780000035440d81003091940f264604600313803407a0b10b403590401c2217444c17021b0040e140000c0c01440103051405058000350313004101410f00e240b00e94040d664581980c6580585c290403039401105101c848640d42041c41e0035108110041d600f044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 676752455 1250 676751205 676751267
    0x60907080411010203130602060906160c060b06040e0403120b03030a09050d0615060c0c0e10050d110409060c030b1e040f0e0a050d0f05040b0301090c110105090c01 72
    0x41001e88090001030282498141c1d0744e000f003007118444107044000c08181c564a5030081d4540e00708407004035260251500040070010790300c0c0103011031106a1220500c0921a440700801002182d6500c0c4d08007804100110f4052041035105202da8442c0c1d0315580e10a6001080009580b1540045070184c2d1040c840c25450326000800340068480594554243c80c04a0400c0b1024009003c11001d10428035503000c11110341c4030700d003201c03018054808007582a5540c0b03c40d846010045404149840980e01305010902e030a854690a9500501c4c02c800e080c0e032004000b4080340c02c5500c00f140e103d41e0b180c003448280c94050281c002c40c61070807512004010b0383d040080ca40c03810740d00d01c4280f0440d500c15140c0c00003034250b8808600100d4550460341d22411038600550f58000d01e62255012441001102c13007020300c01c00448040d5100c43d5151030079640303003200c16009400c52009001c20320800307000041d10a1024032070030f480303440c5030001050f86098010004d0121154070340108403990317201781d50300e80107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 676753705 1250 676752455 676752467
    0x7090e070b04030c09022101080f0c03030c030d09081e04050913050d080601020f01050c04030c080d050d0c0c02190e070203070203060f0a060305060a0e070f120f060f061d060907 78
    0x445a180000d03035110303844524100d47c0d62162104c0d91010310504004030b48c0200001e210740c820500702d41240c0c0e420ad240010140c3e00d018031001614264000c001c54441000540c0001c982d0034403460159007010085881400702c5541a48048114040460204032904e0030007402c94220a900d40c070414210f86644a0a460300751140002040c001c038080031034000d03442048071140003140c080c02007206051200144031250700c91710007a11960951000480d00340e002184001846165450f12032030525104c2c098006410001d003410280203042902602503210326191300400184020540112814410802e024040c0a01144d003190f0040c00540c0c0103860018699400400300200040141d6500d902c60014200e44d400041243c01410280840b180e01c5070424141e0490b403100b6140c00345d85404021560100d54400c1641413042d006400d000b040400d01c181d2041030041d040070070f0081d030401214003030350641e600c01c0c0c20755404441d01e5807141a0040708245c018404035291000380c1000b802c02040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 676754955 1250 676753705 676753709
    0x30c200c04111306030203160207050928020c0a1401060609050112020c0a0b040c05090f04020120190c1509030b0910110405011b2001030e07090e070b04030c 69
    0xd07a50300c001d0322500b1145181900c462825a9450a200d5900c0f110020003035081500c6020254045a0340032090328004070342c3e90217441000c2c244400960340d101604801000b03400c1c129000704d0011a0300314081c400b030b000406040f034808000b0040c011051610150641303d51044404a0349010f6091011640c002c00d003004070341091918458a01c1050020002803060045000c07241c03043c0b11400302041810761641c1d02c0f4500400300d141d0129654414485814070441d9a03000c0350000b0000a4011340c00b0701102c20350707900307603962640c80319141c100e00c18a0300d01b0900050f880580001203030f001f000000c81c110700c0a820080001010340452400203064031119020043c440040d40c0000360f10140b0400c214041c58210010034020382d1407001e41c1d44100d500a00490340010380c1c200000c141c0a503580215984180c0c4460150800b250780b401d2200b01c0c0700c030802e2840c101a16007618880310581088000c000d40400900040d03c80c4000c40d40a140010952102507005000c1c4020408182550f441c102 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 676756205 1250 676754955 676754959
    0xb04140616050d1104090c0818030a12020c071e060e0a170a06020301120c0608160e45070e060304021c050f070504290f0d03030c200c 59
    0x2840c0c100e650b00f000c000c1c042070310380c010b0090008940040c078072107550001c100c01c0d00c8a45601c6d2a5440700d00c0242201c1d01400480c0505074800c000015006105980e00c080070403220a0040c1072082c0c05542c0380c10150103501048241c40940489403c180780281d10b08020025420500e50140060020441c14003252003000b00801c178243c010750000c50140200030006520884c06c5580350385a01c1c2c0006808400c0e032050b1458100343c440400c200d40180c40d000c1c003034846c000018031022031025086551800c5a1851a048142d01040d4401aa40741c800284000d114109000d5564244443c3c444c11540055502000f031580c042401110740d04011000c0314031106850544e41c0382c2c0e803400401e40090854070880320700c50140d100101880303404501c24914250590a0711144c80c2c0e140104016110100080c000415142e100c90950084206480e5481c1c01d01601007180c080b440c1d800030307011150010382500460349441d05869544d501070321003038101c0780010404019803000c4100559480078414118 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 676757455 1250 676756205 676756207
    0x306050f060c010e060a0e010c030b0105030a050c2718040317150603070c03020606010e0618031002121005150f0a0c020a090e0114010b0703120b030a0b0414061605 72
    0x55100c0d0b0a4000e00030709210501240d05e241044100170004102a03040c40125501c0c00c000c50140320312a020351800403805070740d59411601c40e038107524020314006d449820524006c201c02480411031179110380d5910364051084207640712900600140000207031100d107091a00030f0400000913000500310802050f80405076981b543d4043c00b05240380c41114000ea4003682c04010001040ea00c010b0700740e00309210b6826529541c4034413005468000c4811701450348040144011b144030440c5403400da00c139200c000c0440e1680290000601d00300d903c410700003202c000105042102041c010340d001001400255400a03800791201112101401840c04c90f5035415000284a00c4181c0700c0c0c0c0d100030340540c00502050720315039102c0035000102060700e034440e00d9500b000702d44060303c060000c1c0541214280c0300324501c1d004071998112000300c8181c501c508001c2c1d0700c07607001c03c29480410021070300610411910445051a00b440d5103e0201c1e80a810300540c8048100040b00801c0d024204981495040003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 676758705 1250 676757455 676757467
    0x902091503040f020409290c030a020c15040c0518040201020307030e0d150c021b030714131a120a02010e090702101e050c0f190c050609010b010f0306050f06 69
    0x43c03a0960010b110180d0700030b040000040170301000200450001000719854204420842c5001c10fa8040c00c444018180c00140001000010160001c03e2402032003829911f201d0101350101c0340103502520b05540c0c05484420074422401c0c80e0a00c1070301403c6d48540e0300c516142542c0005d650344a2040010204001120020f140c2d88a804d20b2081e8a81d1000c492828018181113800080521440312340c014402d103410100540d40b250708a00601a014015040013400e01d1056081000e840f82d059401481207150310480515130303c940d00381a0034200201014000410402103001d19101000d8469049411190010303138000c01c503018a90810348480855544412060382000c00703008010311190b0a00f0003011450445448034540b41c01e00c0c0c3c02c2007195445600303092159010740d100c003141071901000452204400e1030303540480d0030b0744c920f440300244240e82c0d11641030850580e12030090b69118402c018080d03030000040000c0e4580343c60204591843d141c0021000c0c0b0303081e0342c618001c0b0b00c00510 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 676759955 1250 676758705 676758713
    0x311040302120a110109030b060402071b1403011a1c03030605120a1205070b0708100b041217030903120408090d140f06070f030506010210110d06090209150304 70
    0x544006540062114214030701d4042c1d0981c9880050800301c030107010b901d501d15a60760203001141c3c15642c218000b44a00d65860040c80001e52002c9010340e1a000003803401c034101480c0003a1000681380c6502145901e4402074140760175a1300d050849404002d414502034101e4230f13100c81c00700d003020421001000e0104141010b42c0188080c1e00718540000710302c607507840719100000e0b141210300e01c184107544103602201e404898501414030004d007002c10000201e04094486c4040075003000a900c1c00c0001540e40c0c028102496025502003040311000d110420244040300c150000741050a588251942c60700c130034016168400c010b40c641c0c01c182c1a0f4045010311030000e09450007071a0150040c1a0403029040600004000c0105e240300c0740704009201044203004501540121143e80b19481098070180082d0041d001c020400c6045100300003240340300c50483d004500b200344840c10b06960b1020003820200c1030720225040388003140c2c010403210204d500c49070f8040c06040d03240c3c0710164a0b80c0311858 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 676761205 1250 676759955 676759957
    0xe0d03030b0a0b041703030601050912070b0706091401062913170d0c080307141303030504050a09060b0a080601090308300403091415041715040506070311 68
    0x40d0703504200900310103c0c40408400040003a5403c00c8682da060300040d444c4c0070355900c07045031036500148081c8110a01400c01103070000441c0c00c076500703030f448182d1904e041540c1c43d0050038099034030945502c0468180000c141800c2180582ca00080c8803890501ca240260440c0b90203106e44459421f1440107400c0b4885410b031a0038001c50051f89941540d500151540c680799400500003d0042c4090b21459501032a1805016a0b000202c1d070304543d9102c4050700c0c001d0340080214200c490400003c040e8100e00c0c0e108402940c070075150744c4d4956080006106080075942c001000c942d14011041c4040740f998400c0d22105022468100c000c0e40c1c9480c01212140c00b85d6200a00781d18001c16151200750b20b40300300d020b41e00011540c0480c24400c1090700400b49100b52000b0300401c44052090151f0030b5011030b42d400200c80a41041004120407124031040e900940c01204140c0c0f401d40981360140b0180140c01c01d0256443c0510060308058541c20f85844020b03010341c06140ea243c107000710190f9014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 676762455 1250 676761205 676761221
    0x1d06070f050f0c0a0f02030f0604171810020a030305010611030d240e09010f1a010c11270105010203131509030c03081206100c0f05010605120304240e0d0303 69
    0x602900c4c032160781c03445c3c800b1005501e84003ca1003401008082c141c0c9030300000d203c1d07205540005502102d86a101e01200c1c1a600c6492a0758010000401c2069581c03100c13010f4064442841d401004070503c1820024100d82040e0407690801281031011040c1d14030000503203031860070380b81000410b422900e510900b5a02071a02420940c10010b400190400c0304030741c09840b40410750002c0c07080e09840101030f0202d03a050585c0100301c00d420162680194841c6c00024001441031072544580c15044002501c0ca100616181c214800d41c4800c551319000c0700e82c3c4d0140100030a000841c04c001c00a40354507607401440c0030301281d83d481c0c0803401003010b100d013213500300550700502d80c0c5d001d003620380c10209103507403040c0c0181c840200c1c0304011500d00d05140303450201041450b5204840d8060a580f4448403621003081519299207414001c01e903552540b81241041081e5030042d139840d03140400200f512030b081d400d0300c15222050300407811080d4002d814040d81d1481241c15421049042c60103034020080c3c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 676763705 1250 676762455 676762477
    0x60f0d0216023001060f090c121b021209100c080409050411090711101107020a0906150e0306042306070f030b0906030a03050c150a1d06070f050f 64
    0x101d010020850808958080e803c401415184000c1c942881d010b00340c440310b1058600d0310301c2d00401000003244030360003060640750a280241c80072a242c210f1800b560003120070b1449200000440070403183d010031200365441440181c0b51700b8034075044000b45085100104200a0040c00914141080140000c4402500a142040001e070501e0b04211208442c0100000d00890403480420740c0342e40209a00306d442c906860090503020700d000d2070700014058020321b00e0b18805c006c1c04000300580e030795404007003c1d054016001509519003004558800d241450074014059408d1441241d514007180307150f1304c03d40048580c201c2c0d441e012303081040c000107540244824083d0303006004525034007145c030b21002081030b9014030614006a00308000c00400342d5540f54035500c55180000068056805015101d8a0b4000d0305d1041c5050902c10010420490f402c1c03134125036503401c0110401440440384031007020380005110b940fa2078400600400ca419400d0428030001154a010700c20310f01c0100d038a01850 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 676764955 1250 676763705 676763719
    0x11d180c16060501090c050715150305030409020a20060408030417070308070f0228060914010207020a0e0903090108180d020a0b0703020901020d0c020a0e040f060b060f0d021602 78
    0x90780c104580202404c2c040d0415a6081c030f261611301900c200f050320440fa800c8802d90f280b4515280891000304402460410010329090000021034010300c064001082000809030703903044004002010130400780403085607807940708881207145600080481d0710641c0700020030380c2d030340712400c24a050300041c0503403202e100e0001030b004003015448079415000380320f95103070b0780317016204079805988407070a80d0200da000980075007283d054120000903d00d5400c0c051040000d4101140d2900c400c240d080300e1500c94a80e40004441e001c42c249918020010304281d64524245c1c01c01d8000c2903201d10500c43c0150403c807a40002c1500940c011001d02100d06003101111400c0c03242d00c00181d203807290400282d5600030072070001010345009000b164074142059029001441c01240140c0700e810712414180e8108075206404100307803006280f1580110302507000d45082c10000e180500c1a42d07040015140105000c1c0a030841e895800f2040c0c92950448090240c2c0311b0015214544400103810b0b00a503107d04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 676766205 1250 676764955 676764997
    0x18020d0e01090203060121020103241d0603071836031b0c05060318070f081c2109060204060c0201020d0f0909050a0e0a11011d180c 58
    0x4150b00c82c00300e651081e0f00342c0e172003a1b9036014002c5075100b2040030106200700c2000e10b98010b601c603134004050840f0001c3c10056501d848080c803c2c507140503801064040e03030410201c4012060010f94035502c01000c6005041d500d042c0b14800403c02124102c02681c0c03512090315112218141c8165041208580182c1c42001c0344240614202c0c11111800d4000c60070895a020180e030030030366008449a040f0004428452500085c441d05520045c103c5642020240420200950500ca1400200000a50741c2c1c4441d08001003a420801c003a0f0852941428210a250b4010b40220201144012040442e91070300050708442c0082d241800000381003502c0081c0100d1015009620360019600030b908403051010045c80549004010400660205048840030030043c1555080700b07074040d01641021851300400c2946620340a6040c90488148038209100107070355030300c07100c40d1200c204a44d00b06501c1602940100d40040303201220744412003650400100000e1080c000c40d0074003203030305452204417a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 676767455 1250 676766205 676766231
    0x1805010e0d0905060301140d080d061203080a050906010509060d020310051533071b031728020703120c020a0b0901050a0f0320070c0b1318020d 63
    0x10300301c4096000400e01c1414040307040d09050007aa4141c80d082022998100d007408100201c607643c4582c110f5540b10b0400c80c4d410042014050b0000502040041502035042440c1c06020311000500c0a080340c0c0c03610042080040c80043c0d030504590041d280407050fa125140895880c0c0300184020b5010721071601a209e05201aa00c207030b104490000d129014a21400c08000c007040054078034140010079101c2380f06808140c0608810481c1e004090680740402c5541c443e403103c7c1d0b003c180082044c50942080051041c0c500103030074190030310b51a5a213403614411300c071012500b01c0581038281101c1880030600d264020400c0740099070704100c3c004d0700f80d034031294000c000a500c606c08902520440a0024141203001d0903100301600585580d0700b0f000003450700320344803a60001034800b09521010100c005030a0030140102a01000c80d100c0e940750787c1c604109005440e5a8040e50f9440010060444102184000721041e14042c4c0030b201070416032a14001c0183c0103806540c035400b8a0320200306050b07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 676768705 1250 676767455 676767463
    0x151c030e061b06190905030706020a05120405010e0c0418030c06060807081f06050105090f030a020406090b010314010503030306060a091827030918090b0403020d110c010f031805010e 80
    0x50070300c552032113954415104200d01503c1d1480e0009200707a10901040d8006030194010305216080c0749000c50800890240741843c880b0140c609440995540e031480b101500d003404150841141601d00b400600244a80030a0480802d14050100464950343c142080105d03004000103203800c03003c4800042d00c52090903185d014884103414410380d80004032111380424050780c0d04403078050712042d040031401018048031107a003403012541170060b0b0f40c8500c0169079034440c21000e800038080001d0046000d070005003c0b10889011180b091618400400c0703581c1c0c0c0081140c0c0d000700c060f40c82c19201c4480c0501500d030000660040040000440710310024103030780c0d5002074811007110803942601001042c03005200d4240c058082c0000e84180300a01000d4400015460030340c0042e00005800b10094554000340303c1d0668003180180c0013a613600c08040c1e40000c6a031070a0305c200001d03002c0907502a00290410310380c0510702040c980c82d5000740b45a449440c40c4404101e420400a0104a0140b4280b50311 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 676769955 1250 676768705 676768711
    0x1502032a070f080d03050901180809040b0307050a090e0f070303170a15261912050301141e0907031b0306050a031407031703151c030e061b06 62
    0x214418074000181c6414034196000481d0010b41c00b074000000304c14003c81c00f5010007880305a082d92100030148000a40359882d52119000c0d241c01a00c5e07901c1d407001c101c103648907180140d21a6220040610080d40c9819003001204c5140e80d0004240780c111050074104804144000c1d00d0303004101c000401d258214032904044c0748500314035602c950f00d400c0c1c8c40c4115125003075860351640c44142d003404001a003d400c3d10107803401446040c2a070002d1a9800d160000c003030090000b28150003e40d5080004805014a4502040c00c1690456040c5103009502c03602c04445548901e0a181d02d240c8800e011045851415030003428810307a81c60201c1002e805400c10715000b040300c0380751556458401307100b842040c0039510f004011741c429501e95202d41180c00d160640c1a0b0180c001c4140c0000041c00c000385103600758142810242e141e10749100740b072420a10158005004000c080495281d038004c82c10340480b0160315003081c201c911740c150081201070180320000c2e841406055905e40c04190002800d81c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 676771205 1250 676769955 676770037
    0x151205060705030106080f07033305040209030604030c0812010b13090e0d0305040c0e07110105150d02060a1101181106090108010b03070309050a060f0c1404150203 72
    0x30503446640c41164035100c24864a800a0814001318031b03a6003e044045404c03414900d00412a060000340710200300c0303048550041e820040c690058503402000c00c6240050608403403c60400c024140429102c03040103000400704141300810070108466001980c49034176102c003184030f40d50f844131101020f030352061403840d42020080a0004141e07615000c0c0b1451548043c0140c050390b0090031060b40a410b0181044400b1602e00c3c0020a0700042088a1031042146a8494803101c035901c01f00c6003112005000d10780c0b4140c0740c120a01d125114142e03071220041d410780b40e841c1e44103181a42220050044040b4424950802c9030001040b80001e00760320300ca5000302090001d0407400802c004581c401c07402e400740402e590344010054900381130003640e4410302074100407408241b1aa0b405042000e038807011a011641d60303060281d00c14083c0b094040322009410b2501030300c2e80071180641c0ca0b005900c50140c49a4817607074540f00749842401a54101c1c1c0c10305988400c0c07410000d03c0200240603000000d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 676772455 1250 676771205 676771213
    0xc1e040306060f060305090f1b0102010e0105270c0d0206180d11150313060b031c0206160c051203060109030602120a111204060506120d08010501020705060f04120303151205 76
    0xb407002040441c660256000023002001d00c155814005d12a45452401c0c8a041d950303501e105a264032400c5c000e0900c81c42f0106c400c401164a40c0e0302000c503801d403d00030500144d001840d03843d90790303c2e28480ca05c0c5003a011600789448400c4800842c0700c03141d8444009400032505643c0f44100a440c0982c064240c004495004200f1000b4071580e002d8002140e070405201103107800d2002090450340902010b403000380c2500e6100c443c84941d01c0304c600f80003800500580c000d80400c11040d441400b0554112840d1070404180c056580f60b80341e5418104000d01e0002d0800004075010368081c51842c001194021001c0d91220610040001103001c11150030901078281148550121020021118a1903100d1050305854545071180d05c000c041c000c210316000000514440281441004840c4134180180d888202560600300020700f03002ca030398000c0b4050f64060080390310060101c01502d00b07849804900404209080c207040f1301404c4c6002c901c481c5020045000b00c1c0140c2c68441041195024404407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 676773705 1250 676772455 676772461
    0xf0c030c0d030c020f0307120b061c11150408070305010f0e160315020f1603112e0b0a0605040f0501080c0406030b1807030b030f01050c1e040306060f060305 69
    0x3001089030352040c01000201450340400c010b14020000e00001760000c0c04940c90640c6806012031000020785065071030300e030a80104151460082000c20900c0c0c0c00409400011034290384402410340c1c1110414400c00d01c80e035200300510a5202030741d0041c14104112079402e9564140940244182d0390110203442c20081d8410b100440001c20711a40b8113642c5904040508d9501c030340c0f15040d83e030262040220b03000c010130b489045e0104090018039820700c40070602030b141850060318205040c84403018580215101d03610540502d201e03141002851101181c03080d5961030040000c0914010319139011a0704080460000d42c010081c0040d580000c44808100d0f444000549545004503000b2041580c2040144039140c8207800c114100c44001d070100e900110050344081d00e1031004c44154001070b54410740200c01d49020029202141242d0000300000d08200c2c2c2e4403015071080b40c0c1859030310108110b45040c3c0d41c1d150000c40c1c00031a008081000034a40319010070002021511403003001908003408 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 676774955 1250 676773705 676773709
    0x906030e011b110a050d08010806090c010f03091b080304030b0a11091002150906070f050f071e060e0606130209090105150d1104030b091614060c0f0c030c 68
    0x5140752050000e10200c041070032150300b00d410411583d0040700900800d802800041e80400542c401c10340c140c1c856500d95810301950313514081c4000c1018010f6404281c890000e660019291007951800d4603000c500d400b49420801c034000f00c0003105c045541c00e021000544c1c0d403000b1000c1c20983c1d11942480d00355031101032004081c3c40c0b04412070880340c1030401100b88685415080b140380800b41d8010745030b060300803154092031500100ca1f803420b1601300c0d00c1000911548501400c0e81155035040260824034100c000b100e19004180303000703281d280c01c9140c400f9141144031011008580c0706c0e40900501580181c00f945903601a50340c1801481ca40c2c1d50304500c6591707070081d60050507014107a0000e507883d11040002e00901c1200c12158090b04003c039624031404ad0080d282c0241164406a543c2e52551408007001c2600901d01d80b0545c02100d40300008540280c06401164500040e00341c189101c4c400003845c5124005500380b0741e12480303408a18664011840110000c012020303030b4404540704003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 676776205 1250 676774955 676774961
    0x27062a01052401051804051e0603031e160f2901030818040b040c02030304020f0a08030f0c12280306060e190305070308031f050a030209060415060906030e01 69
    0x305102403940b01d11250000d0303520590141500c40350ba580c0301000310f040040803400300c81055940b00b907041080d00c0b05031203801a0011882d0007403c182c008515001c40b0030300005c0c2c4580c41108042d030b013200000300d01000044480d0f107001741e01e400a056035005181c03407400c84200c580816225450700da2000d03851078040c4842411504880e0880d044d1442d0400802c503010048011403503240e4008e070303541e140303d2141c1c85910450040c1812900219075906007130040008050354444864820b0440c42c0c001d10560b500030054030b8030404064012030319614110005400d00e00420b4405040400200d02d401a1007400b409110800b100d0745004220980c00e00c404a040d00c03854015040410a490181c90071401e2510440d0803080c80000071400c000c1e00e80e0b503804e04040b003551050713030a020040184003110b1400f1001d40001100c2c0c04003a1046490300340890822021f034480a07114000d40c03000103106482c0c0c2e40000c0d51068a9088617021030742c81d050080c0a60111f40038030340000e440e002108041d298144 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 676777455 1250 676776205 676776241
    0x51206040209090c0313140d09080a0c03021c1b050f040b100f090f0803031008070f0e1302090106051b070e060d21020601090c0527062a0105 62
    0x30f01950540c0c0c0d20a80286401d620140444414a00e02c13480d48000c1141c130740840510082c03840141c40640e0300c450b0000c101d80855005101e094001203003420026480f00e25080450707030305981d202d90800400306000a0b14002c01c03c00340207440c81501d442c3d40e4080d0551804142e0f5402c45241402201e104280800c0b928a6581c003600310440c00540700f040ca00548074040c038410075207000740c0c00c1911075928040c03198269000e50300340e52000c0f09004a12581c1034440c00584810401001258549107550b1282089845280b09040520340842e80340c5030300107059081190023800c04081943d49e600c00800592084141e1030204e89d11061207a9003100120f00c03a0b048880382804548240c03140d00c1040070207899079208031034010340c10700315031900300c14550a00200c80c02900540341315131401044105a030f95061000d0104003040003401989103500c4000070200b220b0315622a44900d942c801700d08140300743c044100880e44070309040244903410420410351341c0c04900083c001034032100840c880d450a00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 676778705 1250 676777455 676777459
    0x1090312051305030c0c0301060821131706040b5506210b181212041e05030313020301020409140a050f0c04051509060a051206040209 59
    0x40d405241080302504490b41141e003000c0141c410003140c0c0e94403841c5501550007200d154211002e040c94602c0c0c20704c102002004140050222034140d400182185c02007012491080b2101094000e0100145550400504803840701e0000031a07000e030003d0741d281c1c400c84040f90007040749030000b80c00480d058055840c3c518418000c14007828074104000c50700c0c01060600c01500308060316422110b400c40310701e90341c040789040e00091850a0401020621350003111021030500c10080a030005414441281e501200c43c1207280340b00e66030810207500701140b040455040c4503021460741c11961480c141c95000703600c40e11420311500c001003c010140580740b0006001508280002110131000704030700c50b68284010001440d0076191003604044501c51200100030321100010042d041d001c600c41c80b0341000c0320302090034051800700a204283e02c504d0055900400f4443c8903820701114072420380d00b0401d001003039292142c00c4400c005001d9000200d68204e014a2072010500c281420700c21500c0302140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 676779955 1250 676778705 676778717
    0x6040b06060a1b1a0f04050c060306090f090a021002030c010f140403180308070f05060a050103051e0106170604170903062217090103060819240504030e01080702010903 74
    0x260074540c44604802c60000e4910070700e448070000d445107040c03e4640c170411000e0003810703850505040a41c5812a2220400c0c0a06010401d10240b6035460802c40d034011000c01c2c0c1c1280e6a581d910065080420210f03000f50012403244d107208040741c021024200c0c40403500c0c000c000c89034001d00c3c0901a185d54820120000c0c2100300401d010920419541009010012610300d08981d6990703404090340c840c0d4401d0341e000e44c50900c0b070810001c051007207a800c1054904140501e5065443e44c45e00c0d07030191080b0061108013840104a210020340058004285541020400d500142d1010f501c41001f280c0458282d80d1100c0b1445803a1500000e0360b01c4020060002e100781d81d207501da140285c801070b40fa200092540c4410180005d5550740d032013000c40203009441515480d10300c0c000350640b081e60f04000110741240707060403c0c0c3d48100206d04072054121400401c200700d07401080a00d2006803c0200d580c034100401c001c1410780181810a0600003070381e541205a8a140049003281d800460003400111 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 676781205 1250 676779955 676779977
    0xb0706050c1303030201091502030f0c180a1401020c0d050c0405070e030318040b0406120609062022150c11030706090e010b0a0f05030a0908070506040b06060a 70
    0x555403199a00c0303010441d016103840010031901036005103d91040703005039100c0500700c080180600241c0e010b40101c440a5066003401801d07918105002820011405808200050400c4c0c5c602c000d00b82840d0007600a1031495141c158083c0140804a02540903214180411906d03040c080c0d800c1703c0c05c03500040940001103107042000041e28000c2c03c6031040000700313190030f41c171030390288000c00380e015002c0e2540c5002d4102c2014001a20558407031507200e02e00d080000c21400422500034161150301c841b00190164152031f010004010b032001c0940e0309150361035003000c0c5820440041c100500c0d01d054500c0480c4000d40088010903550041e4100c200c2d40d0042500954010320f8032800d110703c104a459800320058001c40c4c030b4041c5550001c400104d4000d0304102c10205180203501400e03080038250f1400d06108005450b4400c917070003401c108140080040e07030850465100030000b42e4015100340d50b030601410030a5032114140c6040e10142d80342c3c0046040c51402d41c003190810300380c0d600d8500d4005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 676782455 1250 676781205 676781213
    0x3190b0a1a0604030f1a01060816030e0304030206070206120c071406160c050f061005190e060603040f0204050f040212010606120221090f0d030507080f420108010b07 73
    0x20503044215031a5090001d601d001040d1120760038064000c1e65075489c844c1c80c00701b40c80200e52201c01504d40901d1300d41000f00190280c044215416283c040d201113540d051180f020403054031501015504520301d29042c02400107502000744a886c0c01810154038081000310041d13120107040d10310143c082e26280c45409502d0150211428035030040c0c0996040400081c042820b06c60304070f80c0e40d00303c1d4401d44005e025a1403e0900020001c0b111104c2002c00c0d410032303901c0000c0c2c84c1c0142202d8410b40b03004c00080c0030850301410107c0c007180d0242060060f410b0581d40c0f602c3d840c8055801b2449238400c04600d83c1c0c40e01c0705101e03020031500c02ea44c40b241b03809a00741c0000001d600070580300c00011507603206203a041c98000f000e0b40c0181c99100c024941c00c081000e042d8180f503d036545a40815003004148a04158040c0c4134a4000c108000c0a2480740ca035200c500e0f140140b20b640400c000708940041c04035075240491141040c1c0f105a54042164400d800111000802409174000314101800306030082 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 676783705 1250 676782455 676782473
    0xf060309030e18010602070b040f060e031f0915020a0c02041e0e060117150a02131503060f08072d03020303070c090c050715050603190b0a1a060403 65
    0x814080d080200700c1146070742c0441c0514140c0c484034400703001c4920041140c241c1c1004440010052103e5060416082980304c00b400741103440790f032080140640014209560600129940300c020070482ca1030002c00c1902440581401142510440002240c040c803000f801e00840d0110300c3c003569620321114065003040700a104140c611007100e200605071001c1221544660000c00300000000d000c2980b400c09045000844801d0700243d90f00490502800e891198505580024400a0243e00d4803402c151300c0c44100100d40c00406215114018000030680650090701640c0c215031540c0134041d113b548070b070f54a07c082d2103a031103903031034460b0354174904107602c5090425145101400500c407940c07034000034615003042000b66004028030f4801c00500c0b004d1301c100040d00131a07080440c00e0114684807034000e04104000000203c0c1c941c00010029030b020b2080c10842d0703411040c14036681400f410044117182e0100d82c102440c51405107451014001d0389401d000c4184014040340c40c0c42c0c11a5650042 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 676784955 1250 676783705 676783721
    0x2310050f0703020106230918160b19020c03030d050406060b120a050a090b06060a020f1204050f0d0221070b0d0c03050f270a050a0b01030c0e010f0603 66
    0x1004000d0008510180d041401024014020380c0041405420100403203e01108101c030a41600c071b00450b105401e440c0d20000513031081c0007000d41070703442001844650401d207141010302c2c5c0d014080e4601003910300380e01026040b4482e1202c0f042520303110001c411b0340c2e540075503082940d2590091000182894080d00300540c49032040d030012508031707a180c49000741d0b5040071075000400080c91042003081c20040c4a00b41c0d2103140c080c81402010010340381c1030700d1002c002e4589401010006201d0a00500030024044541c5c030301000c461f902456014680c01035046800343e14405c0c0c80c400764841907840c1c845d03964510180c00500c0c1040b0894040020201d0701148210b162590140200000c0d42008a0024140750b0583c1c10022446808003000242114402040c56031111000c106000c8440340120381100320000c0c5141c0408559028580c0c2d070324029000700c0c01002445058601c00c02c00c0120f854031812a4490411b28401580742c0c4888456590240a5140422000e01d800c02035103120f40c1160107 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 676786205 1250 676784955 676784957
    0x607020d0204020a03140a14010b0a0c05120306100509090114130920041406091807030503040305071203020d120b0d050114060105161415100f2310 65
    0x30100310554089010f0b41c0001840d00007190356800c1081d00e00c40f03103400032a40643c600c4030401ca40c89510310700c2148294107000d180d840410200705c03121780354000c205104c00690800e00b1204461300d407040036000d551044501c28014450840304010301c0e4000c4060381c201c86801080541d45a007040c0c0e144098100105891b03600c141e0a054031217480f0428410356a42d0780c0680103052003075030806180142101030728100c40c001c0340750843d00b14000c0a09007040c0d0b040001140c8030852515134200350910443c480e4505035090003030344000020004000000c0c021a0700c5201a100c00654070015800324901944009c1e01507000031411101081c451078100e41509203005000480301d68030b9000c184481d250b01d4040b100d5a6580218508001e80300c00d010754014400d1034050310345010f05018102903c3c569400030203114400341c40b880205070600c0700c9104083d540d0070000941c03800340c0540c1c40b1340708113110f42e420104d201c0d030011800101142c0ca89a0820269401740311042c5608107001e542124200090 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 676787455 1250 676786205 676786219
    0x31e0804020d022701050f060f0d05040c090614030c03150a0c120e010c08060f0112201201140a030c0308090a03080f2106031207050f03070317130c05060702 69
    0x1110700000700c00803c000821804c407042c200c0d81458140405049203001c0319100d00401c0c026100c100c00c1d100d040314596152910042a20b45491800740c1036001c41d6008008a541031032000300303070300d10001007103c0400030403401c44800c0c40c650b509054442d41a80000c1d0403801c10600060301c1c1c406241c02c03000003020316141c952511a524055441200c018141d02c2d480c50351248aa1151154000640e42d00088112581104550120000780c00b051b140d2a030518602d44411021038488030454440000d100f10031186541e03403201004101884100b4003600280b80030b40c0104040604049140c030090340d6100d0085400d20307055481d6003010750012400103a0280190b200400001e90f108080c18203400300c1ea0001d52103040f40d09000100d003031001e0200c41141c0c510420001d907941c0001d80a8a00c0d04050000ca6940300281011402d11800400080145c400050b1542c01c15038030485007441001400c8245d0203e0701e4070a04000401200074010f0b11500310302105000c1d03442d003200103058285c0b00810503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 676788705 1250 676787455 676787479
    0xf0702060705030c011506020f0f1e0715082d0705160c06021b1207090509030f1206100c03080402010f0c02090f070305070519030506060405090f04031e0804020d02 72
    0x11303e00351340d500b0040342c0003061000000c2140c1c80c1c0402907248030301e0b0404090040e8a0b504005c880d9544000f1310101702250200c01541c2e08200b00f03100001c003510180c07041c2c0d18200000e1402421100b826220700b100b0461030701d103811041d6091041c0c50071042d039811075044243c440020171926600000100019000c0e0b8a042000084074036151340028441034010300b650000c4c0c02d103400c6c002000c1220f50350241d00b400d58654a9104045000c60a407444174100194944503082032500e14018235203a0a0b45880c0000e0727054000c004142c1251080504070b60035150907500d09001c442c0440100d0005010038206400b080c010340c02441c420300724000c1031600302d40d0bc4480d07030001284510140c2d85020004160414400001d5040c0211a401001c505146150516007400d05d9140600e41103084200b40c0d07940c0120314542c4d00d00c4112030080000400c00000ca042030316840c681c1c1034003079130304501040c012a1030b0100313107507403010704071071034500c0e4403038160702c1c1e44a400b80200742c8010b550490f440304540c055 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 676789955 1250 676788705 676788727
    0x6010b0306060904020c060a050105010c080d090c050a080c041a01200c03010903030207050706080606070b1f09021317070501270e0403080603060f1602070b030a1a060f070206070503 80
    0x1406c10390120500504075810001800c0c4120391040e0413150401858900303d9010542c1d500851707011400400000034507013004d003000403c0400035000a58840c5800310001007031900003401d14901081120200980e00c0000c403e003003c0c0c195440c006000c51a02412a90b80c3d00c02c02c0811182800500c0c141c0303040c50800c4d40001e0840340c07926405c4001c603178003040440501c0780c10811903010346000d0500b6140c1d8204032001641901803034100510151007130b000510708481000c041c8801c010001c42d031058440d00d0351080c0c0040d400c11010720744650180300340005c01440508045031500c000401502c0e04609000044070a0203950b44044401c4804444245032500d2100c24a0000c0901d00c00c46181420240b400810300b10014120380e1090b0300c9201400b06003108280c0325500f060340d1135003403a204010204142d04204044c0d100d0f00c000300b404410409a041c5030b030403c52003402100031980322040340c1002c00c80c441c000e043c415450103005201600041c01c3c1200284680c5024404480c10b0240d0155 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 676791205 1250 676789955 676789957
    0x40f060609170a03080414011509050906090a110d0305090604030f051c0512150901081e010e0606010c150e0106060807030b011d0a0308040905011d01030506010b030606090402 77
    0xc8854000348040c40300b00030880401c0c5010031a4600b480141a05290741d4400500c4410302030b102a2000c0c140f0118041543d0095000c422000d54000c3c51000d107981d1040c034100105400c4909102c280118000036011032400700352540c6241d0b1141d9440d172110741d8003081c0000720200510841c180101007020000300d607121070240005500c96001d07040d9003141460a182001c2d4405800c000f07820003000300b880000e4000c0166035007000d1030004034915640781c00d1814002180d00910507046844640085046800232456650304580414513015560400300c40900321840e03500e0340c26507500450007150540d0b01c5900c2c03001d140c60180c14009400248002090f08484448488400681d5590b504001d416004a80d0551145103405c080100d0680880041d081d141c410040820001140d010310340355a8458400710060354004503c0f43d150b68645903102c008140a00038000850000e2800d04c40502c003540005040c1c9600902501203a40303019642d100a40015050f580d0000003032205120795282d507c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 676792455 1250 676791205 676791209
    0x40312020f040906090b010903211e09090507050702011d0d0218090d0905031c030e01021b0601050907020d03090303090f0f0c05060a1418031501060f08011206020702040f06 76
    0xd0340010b40705c4c60322040c0800c03107800a000d5418081c0e84032080010070641448001480c812101003000d103034505801f1150b240c0c40e0303c00480710506003a4008110765021b6007070401c0e601810b0b010865902d403e001940c0601034100c000707000582524505485051244000004020107445032020f1841c03a17001803c1c64004a8003500d4400c1038a0400840400c200840c00c05416107052090042d0b04042c08640c0b10342c4c10100c80d000c0d010140c8910300030360780b2940c00f0005480782c520085480300d030702e0000c1c1c8031103150300ca200c46050301c0b5010022a40d444e001c40181c0c0100b1035030300107021800300380c9070940160646040680c14940e4585240000c11040c4c8613030303004284980d1840603071114500d000e695900b00c1d80c2246004040a0149160068214000e5529070401350700c0a0f440e40c14105400045035250400a0b405010b03540706940350a075803d010324180c4029465510b0f1130744035007904a61400b004d1285220b041404203125000c500e040d801440210300140c0041740024403e951102540d98139 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 676793705 1250 676792455 676792469
    0x18100b0f1b0712030f090614040b07030905060d020403020a05120c221b021614011b060f0b21070302062206080a200409020c0f060705070204060e04030206040312020f04 74
    0x211004020040e40038110341b014000c241420110f40c1c3d0280c0715020700b80510700890644c2d801c006550001c0c140551410b90040800400c180d5840100102c000048d404c10702c03080b4000d0050060100d442d1512005211000e900c0900414180b44200d0401040300304080e2949160511401043c80c19601400380b2200e0385801500426800c055050083c54611a651042c00001007210240554048420843c80700e58092811540d440040c072040b600d1000c400000520442c60f00b08000700c1c4c90a9034000240c64070b001c54034081032000c100250404004000c01c103101c0b83c0c010b110184010728095010340030030000e07107100803800f94072141e0540030036006402031408103081c4000c00004589a01600030019003042d80714407110409812240c1c0350046000d074201142d00400d000f031041070104030362510307043d00300211080c908154101614940c03010030146c0c01541829800710b00700300411b0100d030080e0741c55801080c0c0365681d80c400f04c0d0003980c802d801200e055000c000e003500410004010704040c11031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 676794955 1250 676793705 676793717
    0x522020d0f080a0e010e28120b04030201060e130303050403110609010501050a080a0305090f06160303051b030c121906030327080d050702030c18100b0f1b071203 71
    0x41c100010b002d8141308000c040c10004011314800d0107440d108120600c0c40b0f904040d940580d002d1070340c542e4000e01160001c12076501d00e14405024400e00c1c402a43c05503000750001c02810351541000440114102e4088180c000500d80480000380b2a50040e9070160103850300070b0801c100b00b100c0504110050314074410aa441e000180014584114144000c050400c010003442300030380d502503e50b02858185038443c40c0c081c07030028034a0b180d040445a2007120940d40310343c0800c00e841c000c0e0040c5800c3d00c03041d540c20082481d1440400c00001101d0040c80a50600341c10100954040400580c3c024944004001020380d01c0c5010701150142c8400380d8840d4850760301c65801207c0300d04070a04000c8186801d050b03814810055001c00ac5888200c01d15589086542d0310624000b19187c003038490b9400350007240034103d8000801c2d01a000300d0107442103070005500c0340d42d100c2e800e40042c080c0342054500c800081005821003c1c51500c0030111032603050030b984d841e0303907508509540c0c8903800605a0200346 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 676796205 1250 676794955 676794967
    0xf05191b080d0b100f08090c03060415050601090f0302041e06150809030a091a0c060c040303030e0111040b07020f0d12200a030302031f060908100522020d0f08 70
    0x11a41c00303043c60400c01994040503050b02c1c240300502445011050005101c060400f007400c03c030040c86460603218010b02200c1145c142850709420803c540d64515898901d480c0100d2010340c450340030f5104480302e42e401030002d10708607001c210041c031070040816103540b880003049031001c03554080d40d07008202c040321551080c00c2c100c0c0e001e09000380050002e01560010000b4000f116000203021080d0b964000c55544507000a00c1030307a065210300700b8100310034420102001070400f10b000c001c0c801c2d2842660700f0322091203560030203405c0e03584805855044080500050110203140c2c809044e6150000b004420399408400101da02214240300c01d032011180000c0f90400540c000c0e1100c100200c0030301e14002503441c035140c1d083c1c4404802c0b038000e08040c0c00101185101030490741c0c24140e000c0380c0691480c0c040c0d8902000e0801c1c0c1e20752041d0215030050702120807509800340b042c2d52050030303140660010540c1c0120f40c2c101c101c940c004121b900115000e5540045401105442e0b4182d11038513800e540c500c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 676797455 1250 676796205 676796227
    0x705031204030206031b0c01020705010b12150604050601031424100807050a0507051c020105010603060806012c011e0e07170622090606060f05191b08 66
    0x440c120320018410108020800044e00c40b60201ca40c408564218081b010441c461500302c0e80c402d005002c410303580080303448410b11106500618061404035803500009051000351a02c0e16140f0003072030301c000b581400150440c01c0c04c0c0c0140d070303010b0030500d0001000d08503600090710410341525801c07050a2103070206400c3e0000c01605890381201202c9400c89507200a10050500300024000410044e0200d01c2c6c054150198058984803036001c02604c04c050031001410a400807886d600750011f600b80000000c51600a10900c819075414501514840e802c0c4102020381084c0915049002060b1101084003403080c245603d000e48a00c0d84003051603540890a04d12120307440d000800202950300a10a40a0700110542105002940b580d00c5030358a50b4001126036914641408050215003150a59000300b070340000300e2203200b41801c0201548811040741c0707194065107c1d00100d01c042007c4402c1d01603410038111451340c13910b404828a4510319008150307641d20201150404800308400943c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 676798561 1106 676797455 676797463
    0x9240604030305070b062d130e030403030201110a0c060b0f1c02031506010c0803090309030a080403050d0f0509060a020a05060708160207060804110402091002070503 73
    0x40d5581c0c02e001d84144d00003203007120301346500c500248191409007007100d698810300900c00030300ca4201a26180d0060034000c520750140c201c81e1a41c2d40c40d002d03802458000d42440700603613140d07881c40c50080e0a5400d10303c0c113881c101c5e406010b980106940510a0030925801000219908014038040b514018a8001c00f980041a281c00c0c080401100078580c2e08851007a81203c08029050035010800201607030b000b4001284001d10501007501d00d0090b5030001c0001040e246446966000613262040784101102c5040000c80c1c01c0080c00000d001a40d070b1228681090002103034200b000415038415145024442c03140403989015141c070820a02c4140380e131103401c0b601ca80c02c1c81d6401414180f403c40d030003003248070780c42401c04005201041007011100700b41c541c2d25854a45664408550002c80308140d0040e0742401007002c1644d42003070200039a51650041e00171217007008141410 = true := by decide +kernel

theorem cover : BRFrame.Cov 676618705 676798561 := by
  have h0 := BRFrame.cov_init 676618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 676618705 ≤ n) (h2 : n < 676798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
