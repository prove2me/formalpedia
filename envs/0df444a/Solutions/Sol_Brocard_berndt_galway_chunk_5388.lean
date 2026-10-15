-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5388
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:42:25.705591+00:00
-- url     : https://prove2.me/submissions/1eb0c203-3bcd-4b95-b889-a4b54ff27761

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 968884892 ≤ n < 969064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 968886142 1250 968884892 968884907
    0xa0e01090201210f061206060b0304021f0e031f051b0406140405120f07090203160c0807140619050906060f060d020d0f0f020702130b0103022104060c0801060807 71
    0x4283c010020b11341004184510448481da0070004113071250b41000b030148a580c0c0107480c064624540d0952a6007401e500141803402840450080c41051250558906000302a0f07a003c0b5600902590380d0f000d071061295400440c0411244041440c18001c240d188e8040d0055101c68401451880e2810741000e10549441015035100300c0307001c0c010003010685488404134032260344808030091800b80c0790890b1090038204c0300c0d00312080081c4140b00308a41382000180e04840400340e070600200d002501e051068040c4191900034000203010322808143d900d0003c5c0ca02c2c07003040c8505400d900c000103603c240b4241c3e08203a07003945d00c40c0e0203040032a00701e24101c0310791038031a20001c101901d46883e203080f44050781c1244100d4000b15582d1414803543c401c00340207080075012940300840c130f8100c042d80060b142100024030035500300e86d100f05080b8181d020f0b90403290b0b4224024143d0040c2602a500445104012101250400c1c10300f2010400e60307000d210035034141c03007098a0304a041d9803699403c0b038405 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 968887392 1250 968886142 968886197
    0x40209030c15210424020f03100609080307110927010509010633090b040b18030606150a0c0c061d0618040915060e0a0e01090201 57
    0x5014801c42404150b44410204440300c20060400780c03505050b41070190741242440e004184525003a00b0480010b0001a0b040000780c00b1201441c60000c14507440c00080c0030b40c002a44000ea400070074081507000c110030132021248a5550010020740740d170300942c0c4038020240000d0020400f50340d0b183c0240f40036081a648a8412424001c0c81c80c82d030300020301004c0015448002995481050000c0841d0038090711016040300f1410442d18480609a00b03010056200c0c40e9002d11900c007801032983e44103600100042180403c25a244d83d154010504540d1024004080129903d45001500c7c01c02141c01031007220010440400300505485c1001c1da41e10003d2108200300b10407036084001480d1120000240c0038039503407003a80600300500404c1c07030804810010b11580d014046802d044102540c800d0701036034256808201d119041c9002c1500e030480a0110703141c0c03070030801c001c115600f08248842c401c500046084c88083d00340400e00b8200c582c1c040e0080d0000d040746405409150704000f11400302d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 968888642 1250 968887392 968887399
    0xe0d080903010209060f0703030c0219120c020406180f0603080405010503040f020a091406040504080912030d06030b04171611030c0d231606180e010b1b0d020c040209 73
    0x4180d10344c000280d03150b024507180102c0840124110302450351601ca081002c2d04640010034107150541102840c200320800000c0914a00c100c00c000b14500c1030741c544210590103401440708a880382048582c10500c0310405442e1450014481f000398141c0c090f69013141e40080d54036182504010044a056000800503030703800c00b522180b1780c0140c44014000c0001c228400340081c2055100b084d2540351100509014072580c14042403201003500b050440d0a640c030f04a602102540c501c44640b800c42c0616a20f00c4030705450414000280505c1d18a0203124030f10440c1c0121180f4408a1103100d2401800d000080000d90314001500080f048007448007652002811600301d03c140c000041d02c8216070b104216114140310304440c032600b60880c4039a00c0520350101400c42c113000a8892801c01640d44603202c100007801c02c0761a0b0005001400102500d0ba9a6000c01d4660b120902030b0116402030860707140011001d422a841c81c0d1000c226074424852503406040820103280402020350000c104050b031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 968889892 1250 968888642 968888647
    0xe0106140f0a0e0c07022814010c020301111e0a0804030e0105070b10181404080d0212011203090f05010c0f1707110907022409011e090c060e0d0809030102 68
    0x182c40007844030303461040e10100c50169aa170080d01c1409035050154941c0780c820803034200d100003040003045841040d42c8940c29500351004400c80100c40d014039805001c1c0d059464041c50514a8840200419030441007041711454540340d80c1c0140160300c81c1180480c0060b44210114000a1040d01d10b135080c070005241c001e04041c2c140d2075800e900d030400c1d514410b40c0f1030043c1040042c070120210b040d04034440e4117020414502002c090800a900003000202070600000704207441c1c0185606840ca101442220a800e40d0b846034041003842c0220b0405802044c51050b000a0600e2a00e400c1800d480060b0341c2c1c6000d03502e059503800c7c0510002c9608650110960149808940c6c241c400707088180e001c0c82c0030404c0c40d074282c4240046008060406402c5411400c0d140c1812901c2807a000141d000505880c042079850f10319403401880c01400c0140004008501c040c003095068212404035409186400c500c180e45001c10381301c86038017940d06a0403020340b14132000410304c0c0801402010101400140c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 968891142 1250 968889892 968889899
    0xa03020c030d060b030603280f17040806100509010f090906090203030307030b040609020f07081b070e06030f06070909020702060919150e032a1809010e0106140f0a 72
    0x35140c1c3ca41100d90b081c0320100c10041e151500b00a1030007421104410b150ba804018501c68035a01583c40000d004000e07078180e035404001c02c41004402040f08802c00c151950340718010b6640b83d0780c0540c0c150b2803800709060003080d01e1501c0042d0a040b81c0d155200310912914101141c40035004803081542d42c0717543c45c40c070340c805614144015482002d0f543e40000310303010520f0412080f81e00c16040045191703c1480044501c0704e164007107852140e0000c4007651110480c0200d036240490f9200c02d40e04c1d90081034400507040c144004820b000340340403425102202085800d8a65958045a43e000080c03203103042001101d01c0c9070b0040c2031043c00034001d0b51421100e04017084900d0302c2d0403074003410b0f07841e00c8004114480e402640c0da44840c003589846c42d41c0440c0100001e90380c103590040f01e02d003243c00b0b403031424450b030309408a42c0c0c02490203000c0c0541c1000c8145414450113040700d5105c115402e100300c2c600c01c80c41c18444c5e00d0503100c103a021010007d9030002071125600003d1072440e0014480724021 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 968892392 1250 968891142 968891167
    0x101704060e150a02130f0f060509060c0d09090b0f01140c12030f0105120a110405060d02041d0f2407050c0a0606090c050306010e040b0f13060806010510050a03020c03 73
    0x10b03100e5084075001590301e60000c018000c0c041055030180d810403121b55424801d615100403a00c0442d81185840f90f00c1b42215800104640300c0e4000410080c82030040010403690810301210840c0e051420800c282440e031000c0c4010114011019400103030461405c0c3c40301c145000c0685030310b450389400c039902120041c80c1001d55500a0380c86001b070310400300c010022403400450141003584402c0141900806607521024440c001e03244040c0700d65161400200b041d2150100e1180340e60300104144010445c85021040b0140d8448aa0000c0d000d0100b01512103940000d14440b105180c0950a512101d1880c0107162410064007400c1048400c1104851000c000c0102c10810f5028010002d9200d16025041d801c555003080300c0c2c01800800c0c010842c540ea04a41e9240015200782c5000c600d070103400e4009600801e20f00c0700158400c1c0040c0110121200c1c59001c03031b081c0d9001800300c503016600c5100700320030f0b801e2044660000031001c2002800f501d220760040c205518030041200d007032612211a2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 968893642 1250 968892392 968892433
    0x101b080c09040c0c020a091b030b0121020304030908011a0112020d0c170901141501120c0c060e0604020f060d090c0603020d0c0e030d030b0316080c101704060e 70
    0x103a000180c041013150040d4542400700380020000326608211006801c4503031040110000050b109169498010480d039034094000041500c0d4180c01038401241ea6040c071794000d4006681c142c0000b01c81c428085400d09051007001001030301d41e10030b451045c00202c0110740c1d00d91307a14090085160207004401c0d1003265801001ea41400544900280c43c10304200005d500b2001410b410b216814079140e00b440160765004107810008640182801c50340034001a244041a0051650007a00d03001c00c02c0b81566118080c10b15071441501c0c248108044030b100c032940c4200c151030207540003040c01050a0310b450f0850040000070808440403d031110240c594a0020b0903940c07042011a03000203002d4410383d52031041c590040d0140c1030000c1d41e001e02401181d45c03038004950020a259980c401c11205075400c015005002d02c000000181864440c4400da44540220b60024022182c1c54458640c581c00b600e480008080011362010380d90ba200d449070800340c40c241e0101b900c240510302d80032502e002098030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 968894892 1250 968893642 968893661
    0x25020306371d0d0c0b07020a0c17160503060a180503070305091c2f0d140105070f17040f0b09010506030601080c0102070e070912050a0302101b080c0904 67
    0x240e0030b518158820407010703100088034081c0d001041c1004005422810001c00981c100d1002032003aa20103805910380140d44801a0141201107400554034800b208400301400c008415282c141032401d800c030008100900410f41d06400110010f00ca201e0300354014071945a0310059030401c8040c039100c50342141c0c08080254005500000c012a141c01c00c0810240000a5141e011207036031030a03100c0307000c00c2900c85800c80d0304004400222816103802504608030320070041c401c103083d5241e4546182412400003181c061542014001500b050260203c1450207a05403035094440e42c3c440f1100001440040040f41d2194004541e00d01080161500c0e0780700381040f070000640703400e20000300340c036044050788081c3c2c40f9884011070015990f070201d200804c40b18410140420303034440790380507241d50b80542c00c07010604003e00500828024000740c602441402a000c1e81d04420b8a00040170513a502200b0080e99007005508001c00301d4441d4510725031080707510950504200940b00045c05461103281c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 968896142 1250 968894892 968895001
    0x2c030304030c14040501051e04240611060a1e150e0f10080309130b0312030906041704050627040216021318030f02030d090825020306 59
    0x2101088181400c0c0300c2d05024140899071541c000e02c020741100d0024501c0b241d03235405140c40b510383e0100843e00c028150304507000c2c40700381c01c41c280d140c005c01050300b0090b10200b0307440d2080030089000203229200e90000d114120518410514400c0c1810f000b515103014058155900f242002411f000c1c000031080c000ca162540203041418000202517000d00280c1002500f07810821000c0c405a41c5c00c02c035540d400802d07031008520340d8140400641400ac0d028840000750100000304003840b800402c04510440c420f0080200b60010f0004110160160740106900008208414002468401d0314949080115040d10540080e02008582a07802800440c07014075a01460442140b03008c1d03c481003072500307544d0104224110f55800da00700c80079056001d000e220903042d1542c07426100b031040312403040300c0d40d2060141d50890702e0040368a40c808090031030031600c00c1c0b0316800c1201c6680d41d82841242c004000f8909915203c40d40d00e2040914521101280901c200c1d0140c00803949811104561625 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 968897392 1250 968896142 968896169
    0xc0306181b191d01020c2202070809010206130209061e04151d040c0323120d0621030e01020304081c2d0305061503040f030f2c030304030c 61
    0x2c0401620f6454038943c1100c41d42c4445540324842d036400a940502c83c082191034030700d500e26040151400600146004013014000079200341030011503402480d80c00030a03070803501aa5900c0c01002c0c0903440d10701d4000e620000c44001f00f0498900610310803200381d03400d108440030360341180c00141103a1440304002107d82d00c4810800100509084164085001043c40110707482e10341e880603042503c500004010140351001c8a1216110714030240114004800301c51402c1c1f1071111110740c98005582c803111041c00c1000c049401050a080c08810b0900c081c000740c8140304659042e1800c0081c0440241184028000011705031030400c80511544111404070388014460b40c00100310000c12886002d09038041012840603d407200401c100000d030030700d00040d26885034000505a02000310340d12040c6403011080c04240026903500c1c52042d0320a48905590700724514082d100000048140d5294403552459411101040d60304c60b1076068009007070724507207516a99000e5002c400c0d9040380312451103d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 968898642 1250 968897392 968897437
    0x210311010507090e16050d020f04030c09060801051003030e040f0e0d11070801090818060706050421030b0a230603010f06021917090a0302091302090c0306181b 70
    0x1a8840c03a0070035401005610245d01a02c4003818920617518103844959001458084040009090310080c55001911036a150303036a0321024058003050140c1586540b0f0030021a17012007001c01000226036142e00c07000300c0d10846c03504010041800384c2000800e11b4840d014014200010300c4160a0060309859100c0d0103400030701c40500d003480d250480c4000781c0c945076480700850508004d8410000040b0794090015101802240d4030b0300490303038002c003014100300a0000300040006901103182000010003a0715011841c12001d07141d11440d046d800240d03c100074420b609100d81c0300140800a048010010444407012403940d6009901c0704101d8a5904800e00c091907040c0300d180310100b00d11001d1500f400403a02c4600c00b1000401401402c1d10000510429540b21442c114008607002084402c01e49004401c3c00349001e15410120b00c110407110008290008100c15031740209400b4000c3c00701d01e545540c1c2c40c1104103000d020b40307000800f90300d0024511011301005003030410540728900100c90340d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 968899892 1250 968898642 968898659
    0xe071502010b0906010212070c0b04091b18051201110a05040512030c0d2f030309010606210e0a0c03051605090f16030f020d05010608090721031101050709 68
    0x600b400041c441d02291090000300c0c0c0e4001600b0410714009402c66988545528000100c8421540101a400000f1900048207a040d030711164081040151241d00e4010301c64049030150024075452800f840290000d01581c20b22150090601300b00d078000055500350329000e5003ca80000e40c00000240b0002800c0c0b02d02d0410390620a0811000c00040d8204140c541140e5119400b210604040000000d18802112044010180c0200b02a1440b040007140400d00c0c6407283d0048403a40401e600b021400119684582000c66400724040710104850a282d202d80d405082d06504c02c10302032003214500d40100302c07a402c1301c0c402148600010420142e984001a142c280c490b0f00041c8074500440801001c2c014116178243c0c403181e131030403040d40c407814104150002c0440b444004090351011a1107249880d1035030105042e12980c1c0c0b501c090703640e030b03001e10b0568403c40b50151402e8005c070500415180034001c41c01ca100c2c1446400e0104c0c4600b28150100e0866030101c80318070010b558800104403001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 968901142 1250 968899892 968899901
    0x150b0406091d0a050a021c020627010509150f040302061903051302060306091b12061306380307031e06060207181b0207080c1c0602030a0e07150201 65
    0x80c8a8020380007601031a01c4d680e844589108020b40101c04070451a0740c03154042030070030720850740184540e03150a02c0da06929904900360f86560f100101c1160b841006600443c2501c030081c100030410140508103070709280d166080400c107009041003d00021005139183c40141070000c0030080c0b48000401c003030033300234240c0780040c00c601404084c00c1d012001586a4104490b8440b40c19903e8001d69201c1071240c1040b04902c0400084003030001c507041400394020440640510003c4503801c03804483c10854000f10380043c0703e01c0c449220814120000a6080391540e1485100c0500702c613081c001c01880d48540b42c0c41140d1080000f95200e14001e0500e146030002c011880d102481003040e241002c1c4080d59030300c00c82c0901c9000852032901c5102c031a0607074010410714072008814500039820f40b00040d5980303407103001d055600e000e040207030403a81c24481a00b180340c62102c04824007222580c2c903a68025030019051184860b110140200f40300304c200312860081040b184c4070301c1d41071020000282150f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 968902392 1250 968901142 968901191
    0x30311190215100f050f0f040c050406110607020d3005060102010539160c060818030f0a050d140a11031b0f120114012a150b040609 58
    0x41c801480502c020001241c510f401c1c0c4030183c0d01040480486e82c0014043c4100a001d250300504001c3c011100b02c0d13004014000302d49582d02e0340c0720404c04030050039469042c1119850010790000c00002c0210b0300c6501d00304003000050b00d51805040ea210551300320a1142d4811114554682044c0925543e09100c1c00d688442c950025100d0400810f4039030880c50a020a002d00c06200d07441e22400c914501401c603500280c00b0040500120b45a00e0840d100000910a08010564440018071038040c1c00040e0000511008055840c1808410400d2000d4004441c1001044000d0202240032000c40c803601d01812003401c00c072a4245840d01014069403030072415074a40001c184184a200382030200394281804403507091948803101a08455040d00403038012002c02c1c031048000090b207580c84000641c440d80e082c1e80d01200b00380c911080e0303a25042440d01e1030040502809074240800e907100103c840c5000300c0c00c804100d658105d00020103540c241d400013240707907030f0303c0e00c03036281c0c08002581c41e41d0f20 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 968903642 1250 968902392 968902411
    0x106030b0c09030a060209011701080a170f0706180f0c050a0b0a02030313020415060f030510030519061506030204090b010813111302030106050a0201141003030311190215 75
    0x1d0141100100c1e0b04d500118000070304440d0003003100d150b02e80c05500200318442120802080035031b50342c40c609a0381c450000c410ba660300341e450507012074100036a0441d94426441da02c05c2c1c1c07a10381281d0b0303480001c002c0e583e000d800c0002486030713600002e81064101c3d041907003c1c40216480a0900701004a0101242d0090806040c20800300d03004035000301c15250302042c4060300d01c11201c5580041000760441c540d01075130301004001c1c0881d0081d044a50782c45000110360b0104059641c990a014030604140006000380d400f1840740412200038460310b203d47d500c0341d08045070510840c1900311000c015504590080ba401180030301001040303109040703585009103031108841c10404082c810303081e00b880020385501100342d503100c0700b0b45440c1d000c5040c1422689045540c1d6958140041aa8020f0401e00c0015400c000036038424441c00d9551900400400442902c0d0394515641500104452074110014031b500340004103050180d003005c0100c40c030302600581001c03409054460042100100b40103038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 968904892 1250 968903642 968903647
    0x1b0f060e2d0a140a021807030b01030b180a090b0106030e2434090303080f0705090607020a0e130b090f03041403011b200c0d0f0201200106030b0c 64
    0x703000c800010b916900b0b50f0090307911081c981c07054020605100411002079005480c0061000c0100e56a10b84c00b44650700030747d401c11a03191003000440945d007904440690041e9503141813610740c1f5044541c3c6402820595000801000702c0c2d444a00a203001d81c0107001003070b0340b04080c02c62400c05002890b00b8802d0404d042000c00d10800d01110105009003410500d0840703c1201c0310013484d02d0102c45441c40501c0d6140b000c04800c0343e00204468441c1c04203c000800030400304031446000c03042c00b0300031110354440c141003603889814007005801182c4203903400111000d00003070540510402c20b0107205a000d104240c1086420718030450340b030140c0980c01551200303010035940440801600c0c03c1e60074014034094843c0f00103000074090312400071890511010094131480681e04a500c41000c500c1032054101c0082c00c0b0347c102d0b03403268a03088400d900000c0200e00b1310000340c0560443e2200702d205060203200380421503541d10000c807030b8503240b0880780e64034202030007408009020303141d0103000d0310683e92 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 968906142 1250 968904892 968904973
    0x130513510608060a0801020d0f291c060905010504060e07081504081b060402041a0604170a0b0c0309100501150c0c05040c05091f1b0f060e 61
    0xc04a031080c2420012114041802c6a80740d203110b5001380b41d440000e644800d00003003000018120724943ca68020b190142400000c1603a88800d40060009450302214910307080074444202c0304030302420403110024060400059003403140300d51081c00f800000030307140340501d00b00c001c0394000b0080040d1948022010403040200007410b50b600d03020070141c0c0042d40c0b16443c200d03410340500c51581c00880491441c4c0b0040c50300004000307200314003c80341031003869000041034200c4c500c1c013410190402c0c820401401400740300031007286100751085c2241c40070441600da0900c2000180e800f00c0540740000700340449404100640049100071603001c108652403c0e44075070b0544c40c0008803005010781c1c0c2c0c3d0507001f48030750401c1c600020328010f04240a08510100000c0c026486100343c10300c641c034509101440080844101d4803085d5140e2a80078402c2c0e14906441c40f510f10340c8904940b40403142c0101c0b80014064040c81c035110080d00f009080c00030141071084000d41d80c040f80d17980a20035030600b02 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 968907392 1250 968906142 968906291
    0x2010b030132220f0807030e030d030e0c040207170304050312060a0e0411030f071d013008040902040303080405060a0b030d260106080417130513 64
    0x421041c100e54a1007443c0c501d03141000e281425003c001e002c2d41c10200d1103c05058000034842a241012400d940148110220a41c11200010000e8400340d001d07081c040864107040d401040110300840d401580101c842c030038555681d004072030444050300086400d06a0070140038989411007400c07640a10380e203051004030483e0b10700080014003075103040d80c0794540c1511709200c2c9031a90025802920601d50301c5107602542e03014552054035100008000000e0821600c40b05070310030f503035032008980d404215841034a400c8000814140d8401004010006800000f8801000254826214103210313290a041942c20494020285604942000c0e41d009455a006c10368441860603420001e2040e41076541d205060045a0f102d89d003040c804c400080341854000305103a10a91042581865078844140c42d180d850244120400f03040b2030b8a5414009440c10030244800c005110b0740c0025044007580b010141060095100d16240c00203010a10410f882c4062001040c0c0d590038002d40407182c1104c0c413 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 968908642 1250 968907392 968907421
    0x1060c050a020907031e0c1101061d0403120e0c040b0d240e03040b09120f101d1b09070306060503180a08220f0302060304060c02010b030132 62
    0x80c864140b0343d00113940c85002c0c1c1d00030000403010007100c40d400f804141b4084002c0c510500f044001c52a0f889190034040414090750040d20011200e070101180c40e1001c610b01c0b080d020300708a0600c4118140010081d895120f2010051160801806a40e280d5000e01044403400c4092900410350303801041c0c0415a1007171031940c074058803040354125441c2c604100004014003800c69041c0e0000080002d40c007000e81000e40040c000485804840214100d04c0c541c1d9481c0c03009000312903401c0040c640e8a5000c080d4080807080c0804003802e0251400d43c104241401420703400d05904050176040100c15090001d0819400a5103013800c01c03030342d424000041c0046c00003e0421001c00500802151070b40000e016500790310b03a000030390640303072a042041b61001c018a58120b07a0201d00c48500020420000d031503050480350080d001d070f441c6450700d4a911001d03240d200558015592500c0c9080c4103510240b00e100c80394034940845c1c50764241d40c50051350842040342031050720100083e05114041c1040d110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 968909892 1250 968908642 968908663
    0x3020a121a04110a030f0b0c21060120030c010f0203151c020a17120f070b04050106030b01081e0a03020d1110020d0912110705041802060307020c0901060c05 69
    0x219401e03981d41c1e103842d03640e600700d440032103800ca20f0260000080040d2200e24241440c407804020b503041d5141c0302041554050640c0c920440070000030150907448044040d40d40110341890b0a81c1410784007a41001a03087d01c00c400b0495074400148503540440a118189088003441029860b40c1010000407010304000160b03103100d55401c1c0758400d103010905a6500c5210b85c082c10b60089103070703145151202d039805205075001c0d034020301030b42d020740300d04400c101c5648900c0c4a00d542c2c01c003001501d0344a00150300a008488640d6139500c0400400c0780082c6d69030003026050014000040d20581201e8030a0700354500754110390040c1302c01d10000c2d8011030b031005501100c0c0707441c11200c1801c03038400f03107810302c480000300280d44000f64500c04185213420110348580076035481c040d01007d03400700701d8040460f60408441504511024040c0b450103070410024046c0c0521b12140324040303070300003c0b51540251801c0c0056441074480d000ca500381101d10a00401c1c85091111140c6181d8490301c0d01e9502100d03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 968911142 1250 968909892 968909933
    0xe060c0c0f150405240a0504110301090b101212030903090b0f041502190b1005060c060403090b0316050d020c0d11060112020303090f010509030307030903020a12 71
    0x101502445400c10841c4403002201c002c481c00000c44024005800200340ca00791890700030501103000240d50b4203030b04a100020580d4400550b9a9412620010800034204403003801d031940240c0849c3c1e5013402100005030150f0101c1d42d0380c0c2000050360060380059480014104203803400d45000c0f030b0400d05c003044081c00c24180032032a080135241c01c40728107446400031400030b940030030400400341c5d110028105544140048080400001c40c0982c2e17104421358408544004000c8140000b45a114485802030340058034000b0481e2513a0000302c0c0c940084d41031105a5000500704070525034003401d103c0c02081c0300e88080d4610b003041035444803d00100c01e00b101c240f1000051a04661805a044802c95000d51007503840c480c441d2400101080700c1c4400d03811a600c0f40134004544048031082e80310245500600461a2180e074000380881e203901940e0f9135052003014011260b241d181400203283c0d485c03103683d40e00e0805055204000c03014041e508079490100c404004400040c4040001460110802c2d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 968912392 1250 968911142 968911147
    0x1050f0f0f09090120090306071b02010c05071a190309020618010207030c0801051501020607051c180b0106030e0a3203040609061d011b110910030201030f0e060c 71
    0x1070000f40c09060070107144005002d00e40001401150b41c0e801400f41d102048098610507241c036203080340c02202032221100066814948000158040d0649880651265060740d64040d80c0d200103003c5542c1c459401c100711003000800c200e2050f0480700c00002d15074603003401c2100b6007c40d000300750240075008103d861301401c3d070212122a802000104015030340074683e400c09503100c0820b0390182c0020f450f1200140d1807881c81c10340301d600204640344150b48580d542420404420384a1405a402d903403030800c2c13255106001d200c1c01d1030102d0b01030400c2c1d005e0000f6942d01c0d4544000103086618100c203080c045c2d0040000e5800040d8540b1a01602407500c6095104d501e18180d400007007016000c00d0340300035100c00a0b00140c159080001081101d0081c1c80d90360050034035450051510104800395800603408289240d0028511120303001c1a501420380d00c4c070480e2880000c140059000e9a5200341890321031010000c56905004a45143c2e00824040c040c0e4500c021030035a039240041c080b000085000f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 968913642 1250 968912392 968912401
    0x90506071103100b01030c020714012a0c080f01090c05060309011e0c0207080a0803040303181205031b090f061e0301030605070906020304140405070908100501050f0f0f09 75
    0x74459a500c60342001000c1d03404000c034070f88100006101c0480481d001c40d05050300310400300d0000c82d0390404c942c3d143d818400c07900982001101d04508030580041c03c40c0203041e039001c4010450219510341c40c801c1001125181c240019680740c001c400300c0300b015580c1000f8406000039445c41085045440503200c854583e00c40d0213205015080106004444840910104450280d65001808500d015800360b42c04280c03070f00b00c6207445405400e40a401030404001040000e8441e41c440c04d00715900130030000c00c5155035030f60f088017a0145201080006c6000c014490f08030980d110b0780a04541c008416440c007042440811b00341d4441d056030174400d41c0f001c5441540095101940056510801001c5583e90b0f164600080104800c0d1890f000084403000081481e1323000100711400d407010040f07a134901400e0340081202130b01c002045132b000c002403030400189500c0200100c1c0f103070548484000c1401e60610303051098080042c01d0039841000038481c0741ba50b40d12070710324080c1c0d807410645144c8481d0b540c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 968914892 1250 968913642 968913653
    0x8030d0908070206122202010c1e021309030906092405040513021b2803051b0d02060a110a0509040905070305150702010902013f020405010e1009050607 67
    0x2e040c038081c0d00b0110000748070704c02007140b92410384582c04030880c0354603070411508611860360701c211000f400f107100d0320780100101e800980c07044200030044402d500440b140f0b80c04200325110018040e40724a8a40c08420b0030150031110381e0014142514082405901d08014141d1210509102020380e400390171000380340510481c100c2e4041d10f0083c2850502d003c1044c000380080d03000c0b1000074200701c032404011203108000f240c504031920f1051030501d0030681c0c01542640504680c0750440c1070010812005036141c40e0b00845241d61030b0700c9000340c01d0f207038440301000e400c203071005015003030030f615000c10804880014019503001d844c01d0320b0603649412120011038001c1981c0003010380b4134130480d04001b0822400041d59440311420510701075080d00c54107026030982e0050040240800ea104d80305140070380800c001c081c60301c0900480300150000f1200000018112000c05521f080c0d00018144000d507000100b01c030250409498140300303010f2801000f0130b07654160241034402d66001403800140302d0b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 968916142 1250 968914892 968914897
    0x3020907091505040e090604030509091e100824011412010615021e06010308030402010201090c06081017100c09031a10050607030806040f02042304060f08030d0908 72
    0xd1007001200940c89a01d00501543c004d171107000c1075248454005103254a020800034000d55054490b2810107622400b086000840141094840d01c400f0421480070064a04601d02440012810f0384c2c245c0c1c10514420309008061006041c495898014142036622081c011411240c0001900507208080000903042e005a50551051903003448808101d404e1190306610031080c1c950211518000020b41e1800f0880d106010b000c2d042d00002c00400105114000031035029105100014407840b050b544c50014800c0e68009200180c0450f0030024010001ca0224001d0049501a0005600d110003020fa4032044080c03041c914079200c10408040a000d40800c074003569100d611119200700c207031805612a0001c41d400b10300260320840004040c1031850880f41019050f0307481d04096903664080c8809040100050912690708110006e00c0340481d00a070810750807178003091143c501ca035200300000e443d45504541406c0306c00410400c0011400000c6480c2c2e0040bd40f00440d59804609010301c0c10b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 968917392 1250 968916142 968916149
    0x9010822080304080a0e1009051311031510020c1f1103040312091d070c080f0a030911030105010f1403070e0f04051c0509060304020a150804050105010504150302090709 74
    0x7000c400c0c001000050f401804500401e542e411850325990380401034814100621900440e005500c00c1c0154181920048480d180e032031400b0401d04442411509583d00072507000d0000004002d0005035481c083c01f418181e00f0701c600c02428401000c000180c06c02c5000ca9950140428403000d40036003500800300901d0f01c410318400d4944581c0e803410300014410308400c5841c0003440941c40131540e0586610070000b00e501c9540074030b00075a13036104195035440140c0da0503a130100c01403000032071041c0c912000f0f014801855901040c012580d1803c40c49004001114500c41d0b410400140903250511801108840207030340494a1588c00001103800c00010f6003003040c911890104100112180d005010700840c4590b04440c82c41001102c8418110074030b096a50001c0c804000d800040d140c000080c64205000a1040346515915200c0e964520056541e64011a00d042c1c10481804028419030b0300410055505100c0c00c1e004130408000042075000c000d20641040000c129814412020000607 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 968918642 1250 968917392 968917403
    0x7091e0503060429070c0813030c080703110906060712122d05070e190506070f0201170108030901050c0a0212031903111e12041a06010509010822 64
    0x9a0402e420701c88a1440c2c02080100d0319054082c41c1c1d075206000c2124644180940c6d03941e03d00d142031656a014203503111400d90105280d00c02800b2001c03900c51809080240b0300d840c010180c1c2869441c098107580004c0b89414407805030072041001d6500e82208551803242d02c5070850a0321805500280c0d0f40340d110300d0f80e02050601c0c011903190858001c541310780204076001103405141550134009001d48500310790070070000d041c815950009003481c8030fa421755040c0445040610039241c001188064100450a40d000781c80ba0014000b5960041c3c1d141c8040c204111190810f98140038a99980b40714000c90340d410450001115804050705211506180e6402041500c004001c03100f00b6950381c0003038003005022040300080320202406842000d0300c2074100c01e4010b04108a28a40b81407645c0c05c1000041074160170081010820380d9a080e2503c80d0388548204400c81503004100c10600c0e200030a01030512004001341e09890382c206200c980d00044110010000b1000010800c0c95141c001500421 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 968919892 1250 968918642 968918653
    0x92403090a11030a02010207090b060d02210610210b040f0504060f0204080c100309050609070906120f020f13020a110607090b04030b0a0213080d031407091e0503 71
    0x90140c01050400d90340d405000708107a42001d80040544800c4000720090141e44030201c1000503400603001854041c0000f0045424a16611140d0003603901c0580d548203142c28058020742d40c0b04040c1082c0d41c1019058404a0b0020311004000d00b4030002c0e011441100c900384503c41c00d002c07506d900100d1450101134014015090f000025802800090314221442400c040c03084028200c40d1094808071001c0303a00130041681a03c0c140219287da10008134109502d072169034000c03417820000325010313140c004d0003001c45a291000d074030b04a9841c0d41089075032079002c003501d00c0130440c000d0040440c4c0750111200310b801d81c0c40300d00140c035011400384441c8805001040580340079400072070b107100c244a40d501342c0d83e131982c07402d20841d2150864041c00c14012414042880465071034404140d0000c5a02001480c1030114214445026412b90005034140d001c2c0070b101c0c4040754140214841e04c82d0047c17030b603400c80c24035850140039020b1901030900b00d1003a41421607100e105070701d10341c0024840035040d1079 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 968921142 1250 968919892 968919901
    0x506030118030c020325050d061b080106170408040e250207050a0b090901060f0c0204060e011e05150f091305100e0405030f07050c09180d14092403 65
    0x40030f0f1070340440180d110f800384228820144000d501d810b8620ba10100c4458000c0741040b003040288200c1c1c3c1d605845466490a00144103c207072000d890001059440c2c0c2d48080d0300d81807004000d420160a00001e00b20a20107110008040354181c030155428000d03400c80e1552180e1905810311103000800040100441c8400a80b6801260010035100c1c00e455000400d40c40e40c0c101d035400d118500e00309420201140042004611401d02c0816414480c504503941201da80c000801b41d951541200f4805a0000d0040003051000401004c19100b841c0030003480e1480c4c400040d98a0116401020b0b0040c80000c5200200a00004039890400020180c01038510202d60000007040d0440d00702420703d12049011541000c280ea201c5e208903440030085d03142c442c0b41c140f01c40310fa03004a14200c50070b12807040500100d80c0c968150b603104181440d00d05480003241c03001039280c46030a213003440910036003500c1a888440b603030040310700908050340c1707000c0410324803401ea0312400e13a06514410800000720600 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 968922392 1250 968921142 968921147
    0x1205010303030b010306050607080301062d0203040e070c0b160c06021321050d05092b0b130302070e040809130f0b150d2703031d060601080a050603011803 68
    0x3d0803400070a82c0d00b002496200d1042c0669031207404405820300c0010310040100a208500e03009800e104140e003105012441001001003070324903e03151001d41c102060134801c030001500002e901072034920f000d000e0080386481e170f0b851504010b048606550750720034040c19064029241d10410780d602c80b1007199144865000c5010107846030003030080c2d10441101210701401c100d02e03400d501d05d42004c06440d1884c109038040d904c0ba40007040850f00101000c10342e6901c40d140c004030224040b40407841c10400000d81c503100e00c5030f00c401400e80c1c9088404041c2c800100360b000501d03206642001c02d0984050301d031400c2c042064010410101c1d0f001081c0c10000410154981010514812400342804039007500002c0001c0c3c0c40f4070109440c00c1c8401445084a149000c1c1c0007421540900a074001d0401e60800e0407040c2840350003000c0c0e0100e40c484207554080c086888000c650a600100600880c1c00c110300020040c40010381801140798039400840e10310354083d4040040071540203c0900d220f04a813401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 968923642 1250 968922392 968922401
    0xa0e060f190e04110d03050f0304020406050a06080411031b0111010e0a2a210201030609061e090e06040f0c0b07060608010513020f12012c060a020702090f0601120501030303 76
    0x2241e408004030b0004015017020101e1214a6505031922401e100d00044184403075003006105a91190701c513800059252114121400940740c69941c40e5506c1ca02800c0c441c05a43c400c481c1c181c006da1100d40d00300c65644a10468100d03008091030402c0203c070340d180000d4058220451508024010a400d02082046200d22030120100260b141a540000001c007100c810b0304078420321800b202049609494009010008000c0d180305040028a680e11540402c048a00701e0704094440b000b099100300304c4801c0c94010000500308001d0502080628144039519080040c3c401001150b512805004015007441c1701409044a540c440351074002a003064400fa03e80e82c8680c6006520308800b00780001e21600303024800d00e40240400c119030860a06014003001c61044121841d50f8602002d010305150a00c040340403039079550ba4501c080900311046e810028042c3c50b40c151184100103050058840210070b41c1e1052a0311700186080d52403070010382d0021920445c0d00607051038800040300f00f5070150b00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 968924892 1250 968923642 968923651
    0x3020901170f0c0c150a061a09060d0504151109040606030e12030c090a12120203040317031302060304050105040c080724020307050316110a0e060f190e 67
    0xa4900c010307603100410000109042d118034801e000a040000e0003041890020211910ba40c01210765600c030544001201203010707101062102d480b0002041203000061140030910f01440348649004a6000015001c0c414400740281454441c800581031141d0072004022410101009204e2002141070094031a8822070885202c0c2e858907501041c2c20f4403e1050400310800c0d00b0007006070f00104120181c46800051482605030703400c10003481c2a89600c900b0740010004010002da40058030314004c0d90704000c0d456a14210344c4144410070103d80c20107848901070391000d40642e03a036140d8100303c003403501b2103c90107500320000005110402030705520940c030580c0034096110159881c1c2507855111030702441040c21083e6030f01e131700d07590b03541e414043c1124035051401100d10f000c07519910f00e8156000302441d189460090740b5401c061203913841d42d400c03080d00c0803039907214800d04040328030310780007800b070601070080302d50719840769442d2500f248080c0910181c00e965000c070b50303a900d81c80300804030496 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 968926142 1250 968924892 968924897
    0xb03030c030a1d01020c0904140a0503090a0e060303030a180f1406060102071d0a09380c0703261305070e040f0314091f1107140d03030f060603020901 66
    0x40500360007100038690711050f184164098a0714408480c10003151083c007a0054035211410027040d00b051000b00203070301e00203114401441c0c032200b4520400c60100019032260700e40d01c1c07001007049202e64004c412290720005800c80020001d11410f0046004500e240d0000c00c45440707000e60600b4894407004070310703000c01000211381140d0b440c0b1004a888107158820002036150b41d151010b1599400f2045030383c09a1007110010312100140c17605158414050078401071602e00301d0903400241c1807541c24580204800d0700f14401414031940c9039200d8810224041e08210125042030000b80f11680503040e54680070410020506040c601d013a071001041f0002c441d54881e959000580e01c129619031889107400ca03100c507150f0301c92624183d82030081c03041c2022040e01d0030007100c06280e544c4c003480c100c00a40b00d0a40c1081c0100d10901405020004008002e00c1c0e00400c410402c0c542e03001e0840e1440344056425010303c415600d0b0580c080e2240c007004407141c0e82800004514268107070301400c14210241d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 968927392 1250 968926142 968926157
    0x3071e0504031202070b0306210a4704231e0a020f0f010c050a03020c01091d04080c01090f15141306020f0f180109360b03030c030a 58
    0xf05a9a61265220b0720015a2041c0005403c034501844c079050308210b070707078a5088540c50701c1d00705504010100c40c0850312001d41010030310b0018202d10014a40d44901c3c4416180c12402d810360114009002081030040c00c0d20303800040800c400503c0f403049110881010f034a20042da0100300e0748075410413840038080c501502d07410600f058005464150b854020b000044010683d030140108510740a10030341c18044c418040e8000150100081412140254050030001d9500000100130704113030b074011440b000b40c161140158a56095803d90420740c06410181c3e5842d07804503890140c905048040c003081da5415160007030004404000803054030703580f400c008242a42d410600303105002d980c54607201a81100c0d40c0c2c009600e581c024000c10240303507401400d00805c0541c2080b181c2c841c88128204600040c4811040c2d60402c5a00b0041c280302d009240140c0120301042c101d08404071a40c90f00c0c11f1448a903821100c00d190300c0781280e5200942602d58840c1c10404690792a40040c5580c000684030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 968928642 1250 968927392 968927423
    0xa0309050108070207051e150a0302040519060f0c030e12150105030303041a0405010b0618040e0105060607030305060f030319021207030f0e12010c030606140403020109030803071e050403 82
    0x40b480a0903500700818079aa680d072000c0c04241845112a8248e070407201101502084900104c0a02922504e550380540e4443c1050103000100e000c1441c4800000d80c03a0310144105e941084590504110702c0c0b815050035012410308890402d40c01800c9038000100b852104055070300880c0011b00307240e9154901d101640d071034080c503540384000c45001e42182140001060b1200302c04082903005406a030000c07440141c804002a41c40d484244809041040583e42d440242130a0041000c20051b080c000c00840c40d1500c0812080e02c40c11710020101941c07500021310035642c43c0008040c00c0c4002d401c4036116400750380f02c4007000c20040608009445140414540010b4400031203c0042d490b40c1c80324001d410040040e203829503c00070096000070198460380d000b807024481d400d007202c0d0382d5032b0105005103040c6015104000210301d401105200308814400360760040d0110302140d84c0092103554960396a202114142400c610340a01200c51000d4405003d60007409401520f000c0c0b18400c6c0b15410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 968929892 1250 968928642 968928647
    0x100b03150117090303190e031603020d0e0913060e0a050604171903110d0e0c13181136010509070f0311091306030b06100905100507050a030905010807 66
    0x10443d0804060b900c1080040c0c1e489404d8011050302d6246030801040e000d0203082403500b135812460b020001009283c1d9000d0605604200c0c58003081d40d00d042c820341101910b0003107060220001d00152403500c468950340100401a4030a0074681c0d140403e0b200640660301d0900d0711280c05031025602c1c0d010800c031881500f45410b086440202c4444c10f400d0a0454542c1c0175000340000c404030700034040d82445140c080040600480154039010381c040c0c1440582001000b44040107805031420091a1429041c0400701042d8501055a002400d078014250308000050668010401c429540c05051b005c81184080c00300c81c01800660012039000b45a032900b05011341441c0459982c2c1c0002d100c5c3c000e5000c410b0107a4060381101c8508411545403400900c0400c88550a10b200f00802c903548e01c40400912030b00c110459081901100c0301101d00c07a008600038038012440c010544500440040d40102d1070080e070460748096840019601c00d00c803913045c050000c901e503108081c01324000d040007030817051 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 968931142 1250 968929892 968929937
    0x2d10050f100e2a07030f09080a050705041a18160804030c0b041e0305090a0f081b010c0c03141e1e010231090506010512100b031501 58
    0x1100882c51600c16955928529290101814260b2100a00f01015200703988000010881140284c541a541c652800001809240103920410407030304805141e000040380481c60340112035048030042405001c0404031000080c50311fa1003a031100007403400c3c812800c02254054441d5a44e084405105d051081d070075202c0e140100c4d801000100c8c0b030b034240e80008100d100b4413500316004100b5070f8924000e444180e00301401d01c0e0300c05d901103200450350444518203c20000d0150000c0750282810703a1400118540d903d002d0358013008000c60340d04031130219074450b0394054150f68025204000d800d070750f8100203034444480e0340340648078056180700d078051441110340111101004401408502d80c96002a000309640c11000340c0d00755002c10840d00b48140d1502021800415041c0000091040308440940a55154800700c0c0841c00c080030805180e070000c0a035010b10040703000005555031400b4400744900352a0704009100d134004400d20012111540c0007010740442031f01c0306090301c40003190019014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 968932392 1250 968931142 968931149
    0x105090f0a0c02010f020d020409060b0f0301060813020d080d3c14040501140906070206010b090f09010e0a0b0a0308040605220602160e092d10050f10 66
    0x100c100324049004428030341d1014104004520002860070301c05003120059a00c5040d80100064010800b440a010948604030003050110007051030b0007010070441e4890b00051041d20180030303d100009508076a40621038000c030358018034030b00c40f0701040d282c011700c1904001081020585000c119450942c59100400810800c1000281c4024103d40c03c01d8030381340758400b441c005c0c40c3d21204403008401032100c134079008a00c40e03000412140301c503503c44000c00d44010301043c1030f5070121045c40005234010501d241924420841b06a0b50a200c1c00425220410b10b1030083d08400c4401c00041c2c15501820150f004d420405c400703001190303508003000b80c40e03d102e00014101d400700b00b204010080c010001009561600443d02010307180012551080c1c03d40ca52041015800003813000398003078204178020016003040a240d44680c240342e42c0721503545090380181520b8010781c4401c4103504400780e00c444421580001200c21002444803100c001c2d107170590f0070602c00e0004c2c60201d017103c442072034240d094 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 968933642 1250 968932392 968932411
    0x4060c030e07090513020406090e1c09060806010e060c0f0c030114010504051005060309070303030c0504150c0512160c0501030c022503020d0f03180812071403041508010509 76
    0x850a240da00f100801c0041c0008100f0b0040039030302401a10b641c01424020700d1403c00025004803a907607403a0404082c8500910050040e450307444060b50014242800e5a40c1450411829590640103898002284100301e41c040360200b003407180414009002c00b010030041050b903070403280801c00d260988913603c0f00320071000ca0002c01400981882d5008903400310700c0c288036001c16a507840214507254800d44404103550444c102c28418103401d070090f844040100d180070b920f040c3c0f5107103c0306546021001b40108220030085443c0c28000c080080c070b00e01d00c1e04103520b103544d5040308a05c0541091003d904464083c55081d00140541c020f200702130385075252340c02400c210404000e94407600b9480f480b00040001c400b240210268613501c1e203200041e40300350a201a070315a6401c01404004041107a084506041801409610f078086800201002c5140290f51101c0d85850440400c8202000580d12071101040000d00112031410380c12003120075440303850b11130f40c0700e034107200e42c2e04c008a485489 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 968934892 1250 968933642 968933653
    0x60a15060c08160f051006050906130903030906020a03060f0b0f04210605070801051206040804050105090a05150304020114271f0305061206010509042307080604060c030e 75
    0x104840034010000d440046403c08080300559850340040703649a2030a031101d9106014420120905101c2c10001d030a084514100d40d1400400180310900110000c151854682c803a43d41014040e420504240d07501420554466100040082c020006407181d070112446018002880401c10011035420a101032030075868030b410040c0c0c00c10f40108140442c8000d40c0350701e002c00007042c0c0f14400c244c040c04484d5144045035160200b0054960304a010321700494000c0014400022003020456045680c00c2c2407482c0c5076848a070010300c6800c825030220b030b0054401710742e0f00c1a5510003001544902d01c00d8841c504040d0120301000128020f60411000041d100440b142034203000c5071511040c1000141040001c17040200c40ea20f40108001c030003004282c90323005002143c41d0400a014042c0301510007407081d503142c0000924561005000030740400d6000c000c2258110604d088006407031880c004131040f0f5640c031040350750313149412541078500364548801c42ca1207074803d0140c5c001c24080480100b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 968936142 1250 968934892 968934917
    0x6180c0403140708070b030f0105030118020415120b040b07090e150d05010f0e010608030a05030c25050a200d0b090721020405060103151202031e060a1506 68
    0x71900b580222025564824000c000942e01c04c100403160140031840c20300c2ea00c9050035036088034040e1041c0c01c141d220764100310800da42c00036124900204650107c42c04200c0b0711340b458401200d0000b6400800d0f20100680000c81030040900312180240d00c110720307241c001e0b501c2007011250221140112120714904001047c01694003400349c48100074020040b11400c80180c0d02c0703508462015102904241c0c0340e91003c50003000a203c5d5800406503030019602c3c3c0b0410b808000e06500c030090400d41c500c4400b08800442544518a00e40980f031a40d40408a0108a040980d5240d01089044581c4000c40303140031122541d1124020401401904886000c0d10b80d603140a00c0180040c91040c0a100e240e00000b204c2122421610b0740a40a26814810203041d0041c403054a43c000c1c00316061508100d85040181c4418490104541303000d800320343c2d01c60440c8002820000100c0c40002002520790391111020004240903008000a04041225a50000341e0312400b88e60340c8264000305082e4034140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 968937392 1250 968936142 968936153
    0xe2103010e09120309011a0604060203090103020309010b06030705041814060108040f0b012903090c060d060b040f140a0503060705180a0e010e0a09020607060f020714030306180c0403 80
    0xc580120062080d10f04a80b0035100b05045034204842021007a0345031105400c100c0b008204180d801c0d042540c0c5c45144c80d0501e80041c2d682c0c40342262050400d51b00000158206100790301010b1150300080c200c660307070b040c5130314000c0c0203400ca4010000110307100548882d000c0704030321620500c00d0000408034059907404006540c41c00e0002c10540700314a440e03010348001200d480d0002d01801480c05103c50310b890345809074104040042d091a240c5404006016100c0000908152407a8044038510b0380e40641c01d4203c4080d0115074010b10b04841d002c607000c5010125007680b081510b600807511000d68092004101452101c2c0c41407036096081340010a401520540082107404500b4041000c0c4064503c045540e840040e484440414440d1005000101c0c3c0d8036501601f150303a40300180509110351b00024030510418200400565407a003010341110b1146c0c0503281c0b4a038008502c1d540588410703002548a51045605034480c4640c40300b07540d40315442c8000140600c04404c40c2509007425079440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 968938642 1250 968937392 968937419
    0x20d0303020c060103030305070e0d0506010e04050a0c06030b0f18010302040b0411280c03020c04021308060a060e0702160e04170f09030607051216120f0e210301 71
    0x940805800304404100c4150401101d030007148139aa0000d2240b509000c02070402501511a40c8545001541ca1001c10b4002a90300d06440519600d49819201c5140151030705001640040104e0320244001034401d13015441f040790618159400d500610940d130420188080c0225204400c020020041c405410035920402d50002c01a0000407490f40146289010750005001c040402c5102000036158007170306584803580300c00c94101404800d5240d600030707490b4554804154000d650220b05828100501141c100080050200303440180c204650b22102403d4a80690071260710b41c40003046003980b0010704142d421245840040c1000d00f0b2421151b40c03400b0290060340c200c2c0440c0e03041c28a0407055401024201e0440007540d94800e10307401458141040180741c3e0f014814284001d030701c00d102c000c6011303034044600c0320703403080001401e202555000d1400b80020600e0746000001084035100c0d0340004820f0141104480f00580807600900d000d840342d80014124170301c103000422400c040e6455 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 968939892 1250 968938642 968938669
    0x10c050d0f022a130e0a031b0212030d060812070201030b12060c0c070806130209130512120c0408070e0901091e03030e0105040804050d0c0f1d130c0302 67
    0x595202034035031218481400f40741400c01c2d82030042d4101c1e4054500e032802c00c0e028000d00d00c840074403105000310070607500d42854800c0a42403080d8440054042501400902c070031507801000415203501c042400ca944e03400401d0001c481c03d00d4124007044200002070052128440c580103140b0f4106030340c0c0118085e0007000e01150308034900500d0281108030a00841c1d03c00e01e206a501c0f5140c0e281c1d11111450a20280d0107905a6001601031141007600306c0d00341c000311501a6102c0320350b515038041f207200c0807030149006010f0380241c9000080c010401c40c018440010070b4401010b403502c400c1c10480035440b0701d01c1803800320350007110200700650b070035070038aa40700600d01c000180c1102203403124000302028a00078002c00e001400380800705900b5225541c0d0144c00500200280e1400303580d0f5581038070690003204d00c42c10f01d000036442044254001d1802074020524030606a56075011010750350b82c11034154011010030707180000c0c1a5524001200700040c2c110015000c4039145409000d0440c0c804071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 968941142 1250 968939892 968939897
    0x160521070801020a020129010f03180203010e1015050603180f0703031707031503140f030c0a02100f081902042102130e1e03091008010e06010c050d0f 66
    0xe5001035415020302c00f0300784501c40c980011680d8800540c2440c41d5049440a110003180302244031b61490340e00c02c40180f85d1300c03040e007000a007408850302c81101043e031210009502d5130a10358480501400800c40c410ba440c009142401503001440c20f40000300c4203030094940014080c00026210004103200c1030740c414030003050320302d20303004c0c820424200201a0002c0d400314150368030101112529660907640500e651900f0440380322462407143c00240d480c480a0119080458101859003051110745c556282500499545101e02c0340000d4680e445040141c0c407560f81503003010f10640c066550a01c801c10f013603030340c0340140d03403509800c4030480440344a03105166400c0c08041000d142808074000000c0540c511100448410720400142c1c00340c04003107060f034a040c204c2c80310562100240055030902c000200c44050b00d60210460329602422801070750088000e6244483c0c02d4214a48034181c4400040001260f40c8100040d9070080c2c112400502d80e13400031452880e51849190040c08011192 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 968942392 1250 968941142 968941153
    0x60632071e1119051f02010b0604030c030209070e10080a0902060304051f0c0e04090206091801060e1005090d03090305010c031d151306060e0106050a02160521 70
    0x40c040c41442521000c011281c0c251031298042462078203050650b021480e010383c4010f02424800880c000000721036050740c07486191000c02d05d10500030f4018228400d400341c2001d84442c0e81c0d0500030818002440b040e4040e0718100041030f04507208170728050440001800c1c011034000d029000312000040145400a06655050410016a101c40c000e5004a0050008160098010088100c0295a03040e0310741d02c00d10780004403000e5034201a00884203c400c440000315903400b400414014030800032010707030010f2100440e100d9a0300e4038844a06858250340c4c0c05010340000b40521001c01400381148010501c00d004101003464030315140c031582c5200c1c2c43c00000d055601d60360b69003503594a81e41c502c00b094035400284804000e014070507030054031580c010700807504620070621882c800680040c1f1034004101408007403280c81d40040f0000e0081c200d428117150ba440c03c2c0144150007a20310032006004503616440c001351100c0100d41a110014695402c1680b0f01c1d00070142003da0000f9468240100f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 968943642 1250 968942392 968942423
    0xc150406020c030301120b061807110f01111b010c05030c0702010c021801210f030f020715092c180a050a05011d030301060f0c02060903030d06063207 66
    0x288080c600070b00b101b84000c000080036107065100d4620051280e40110040010710101692042c0343c00e070448200e08160309860841c9101c1c50400d491002401c2c8203609105611050100c0d0400a10b1110708980c0500010b080f800d80301030a80b01c2c49900307030f00092401d001041e0a1310124008066140c814100900f424486030f022880e1410304000208621210b040104034074404518054038403040041084140012650f030500d140c140013801904002c036031440803a59030b0003003100002410812aa043e2041882c020080030100d00d401140c03c14401c1c1350344031b88188003c0b800e41d2080c0300000036000c170503694044012008403030074821410034071805d1444404990141701c00901c45008000210300301910409000010b040303451041025030042004011440d8407a503800d000d0b03031442c54103412511640c00003c01034020b07444401d43c1030200090100c00310805621090840c5e40e01d132210001c10351035085401c040301030b0070104007103484900181503403100d00384010010030b40310b001601e4402e0075 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 968944892 1250 968943642 968943667
    0x40b0d020409061a12060a230406050907050409021804020105090621060f0904060534030f020f04030206160f0302150a18080d1e0618020c15040602 65
    0x1c4250503540160703220300b00081e5158104911044060a5070110840c2c0d0030741185d1a510100207111940d001d42c0c1e2900040c080200040c84004000d1045103540b050600f818000002c001c01d0ba02d01c412440f800c9000201801c050043c030104540042c848617940f10445c3d422034110800900403410880100400081666910f0103002c80d20541410380c000303008002e111040111010740b81d10308c188080010180c1603a104044554829804607000c00c00b51107070740c0101100400790080c0c0e0352246c81311a1241c001d810032045101020100c0d40d06201030605042810101d01c100d40d822002000c0412060015040170801460900218102e107c560030305903c6401d80c20322610000c030016007200340c45651a84595502c140c00c02000c40041103080f60783c190000d201300740e840e001000ea4202048484036100d865000721614440740d01a4070095406803a0720b4024240c500900808880a040054035903042e4400e580b9412454002488044055a1018241003005000311115602040f03090043c0c2e5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 968946142 1250 968944892 968944901
    0x24201806160204060e0c160f050a060207030305070807021b03100608010605031204080c01110c0901090b1201051006210c180b03090a030813020d081e041202040b0d0204 74
    0x3541184940001100c0c410041078800c43c1e030040e900d1040000c14811100e18000450301e031055802c0b02c20840d1f0104d464a503c0500e000360380a04503005443c482e8042c031115400400180340b01c2d40e010083c0340d582c01d80c25110780906850450050b4445040300e682e4626016030307100e10080090840740201680110305042d9110345d0080c0e985c2c0c0c1d450b9413080005040412006008071080451b4a080070f05003000e03296a00b0007030400c00d0421000e03c000e00340952061110514014014050080075a107a10f08800540800c400950160380340e0391818440070010701c2164018040301c42d4000d8507600d0900c00f00c5100f03800c80c440307140d031241281c502d60710b203c2c82e480381e4a144c0850f5250110111140c00107810b200c10140e00880c0007200400400402e00030104294040d1545428180d43c40d44905a580c0078905c40302c5802500103041e68018001c0c050814051300c00403101d000c0c0040c81d14210645e07100d007806a8412a20405664600c040052034150059802802e01525a409200c916000541031303d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 968947392 1250 968946142 968946157
    0x80304060b0904172d1e03070212030712051003171216021501030b0708060d052e151401030e0601030f02061c020702120c06040e040c0e010324201806 66
    0x210700081a4400c9088a4404204621b440c4030304c0342140b400d00387c007a40f02c10005442001c18000080000d100f10702500000540780d0340100c04000510b07165101c40c1c001c1589000c10b4030000465100310a40d0300344242101c891840001d44100729407941c1461551400c5c10b40306d000154003484908004007000c016000e0300950198151a685080444024044000103002240a040358100000c0450f2000a4006030302034448003811800c03071a08500d0100c8545108118072160501c41d45103002031038072910700c0941d02010344d945000d48550300194116078800148044c41e030483c000402c0440c52503011401c080c5d0002e4030151a0403c041d4500c00803440100388960902d60103e488000e40c2007502001d4408400c0d04020700308111441c00282043c0500c2c81034540040242002400f008682803074140205448c0401d02e080356101c3c40d08410b1440035174a40c0c03084002c000001c948003565400740d040a00c070306a046104041100d0380c2c09460768402d1004110080c10003103104e0858450400401e640c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 968948642 1250 968947392 968947477
    0x3090303150b070206131710050f100605031504020f0d1a0f0603070c081603080f0f0c0c10090305091906120f150806070210150519080604080304060b090417 69
    0x41c40250100703023003221005028142c07140c40000030892408030070b440d44c806545881c18101c0d1a40d450b9408450407440d400c4469402c00e001080d42150400c15002030840f010300110103105003140c0320000000c10b0310143c0180d6001c580322854030200d0030214019604414907280c0003481e40380e2610f8a20b0164064012194000c02001d080c40515610821841e00000e1410071841c03c1c0c2003285c80e809003224050102800c028000601c5508203404100082585181d07074010b01407443c0b2800c010f01903800140c5c690740680b28500070045000b001c081d00500356007075034850f50444c5180b01e0a11004100c078558a06045030350302404080c0240c903004a01c010100c44000701a1841c11f02d40080c244542e07903009190030342c1084101e0350350449c2d101c04081034503000d65601410748070130700c030948003520550b1007045240112810b010522000380d00031072003140641018000d0203010300c2030004550046901030040783c0b0310554072800f403030200002d200045249800c015100d030f181503001c1c80381c2e0f0300303070901e010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 968949892 1250 968948642 968948653
    0x21005070f08070215030906160e090f0106110d021203150d0f030e0402160213061a0705070b070b2e0b1b01050423120a03090303150b0702061317 64
    0xc61900c8810b00020100043e540790440c1010151f55035106030140c00803030f0800020b0344c4010070300e105078000c025040c8c000700440281d0500f00712081c4a00000c1c0a508c0004400150103034020784005032090012174640d0042602d00c90404030703240e003900040c00f01d0805001c5109450510740e2580c84191140c0e00800c050301050410b442c024101c862401840360190340144040401c1e08203218001d03844a40558400729a55103600c901001005640c00542d9442811202601c40106240c054811984203004981086850300100c02c0d140c055008010180154140018100088440f0201081c4211039401480c4c41c0100521411420140c10841c0c040ca00403c40e0f00f0f0a048040083e0f554494a100801c002e0074a5204c402c400c1000f24001c2051003104914800464001c002410f81040141540c98480e00b070391300000d0140c8404034090300081e00342072342c0c400c21a44c060a81400c98102c2d44545107862000d600f4440715070008140702903000c03152540041c14103010405110001c501e0000b03000e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 968951142 1250 968949892 968949907
    0x4081810020d2c2713030212120109020d0603060606021506181803040503070b0d0e06071e09030215040f0f05060d270b10091503021005070f08 63
    0x10b000a10000f24601c03160300c10200c0c1c0d0000c0c502c024041c00141001c3c2c400d50902c10362684030340ca011103c03e82105100700000d04110b2025040e81c26183c880d8800d5080c3c1c0c208056901b000310850060448007166543c80200400c59003165074000e240d2400b43c147c01150140d500d440e00b03401c8800d80d0780140d0150f041010990b448034460300e0800d074010320840368000d040c4200000e880d0750308002010510782101d001036203400c0100400558005040003001c4400742c2e5280d14002e0740580146200041e41c500304500240f880c6800304507188104910350354284100f0103003c2d0156400d00307840c0c000c401d0003100c403401310140e110196058191012178031050380c0c030343c505075102c502001158400505001e44032000c1c886951000c040b144281282c06000c100b0b00c02c0c06850304042c1243c1d008159030600c00b145100c08102c5102c42c5184140300000c1805038003a51040c414056a2101744011000c02501c4018001480d02100403003144246140103030030a2801c1d0381d1070880801c400b00a8909200200328030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 968952392 1250 968951142 968951147
    0x219090b030127060b18040809210d0e0d140604050705010c030f030f140906090609210c07050303070c0306060501091d0c09190504060f05010804081810020d 69
    0x40e00e6040c0310005103c0803000e00003010494500301c8600070446502c2d083c1710f41c83c540e68002182d0040d15608034800f42410285030014032a4460034680c2d01900304170fa8898003030000c20350119a003158082c007800d410001e010084030362142159030707654480d01c1e1610140100340108496510510702500519070384c2030a013485468121984c1c00503041100e00114500000d600840d10070303030307a075a6007008140729030b401400f24090040149000b0703d04108404004201d90300103100c502500f1040296a41030702d0320384015864036902010700c00d0103921062045c034440001d2005100d03000a4030107071290252580c00003410360b4802d150640e0300402c0c0140c18000c0c84100d1180500900307003402e0501b1403074580b01c68464281e0322111841c51400324840020029244441110f111031402021552818051914801440d1040c00754a02640c41c040020038045030310002c00050320740503120218550748079500d10071594420400115080c03258150b036a003a40340d00f61b4801342041650042d00914400d400300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 968953642 1250 968952392 968952401
    0xf021614010204210f0b0c21010506040e040804080d0f020f0c0a06230a030f0506040501030f020904110a0303120c09052407020a03050a0510050c0a08040219090b0301 73
    0xc04840341d104010400c050f0341d1882e000c503614080e1036a20034420b01d050501c0c0c004101c4282019002c135400c40200102c0600b440002c00c0000802a500014400b41c2ca00c0c41c01c010609028050700300340700f04414400030b1910722134282c0c02845605a60b1070300d5107800416003003d0000c5036810204040c044000c0c1c80c20b80603c04100801444402400719102c2c030000070740007607824860841442000440000c9224040664503004490341c4901c5690f401c0e1000010000e0a10000c2000301c5443c141c00310341146010301a4074105d07600121801003030885a004c0024080007d0030458983d0607400480344c1541b5540502802503011f0b8840c145080c403252413000030f46040e02d401030100b00202105000300d0741c500d40100300700c12442c0e81e901584a101c2090702000c4c0300f004406944521031000c00400c120000910101084c4a1350580d60048003c8491009580090314540d440c89070500011000c244109115540035000401c890350000610300b00d104400441d810264005491340ba1880803420240207 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 968954892 1250 968953642 968953673
    0x1a0d0e07080609010e070506070501090c080d020c01050403050a02190e010306021c15062f070501090b040e13020609061201030605010b0a02030f0a0e1009030c0605030c1902010f0216 80
    0x900021741401c0d10551109090700410f03100303410200300402480001d52044010395840320b110200161606d80c800d03a520b207012283d02c0180319548011640e9481001507808481d8404000e040956190382040046003407003c0c1000c80c100d0f081d100090000b450003819000714051400142e568010820112024200031a035030206401c090088811503d00711007041203e01600d80000c0c007051615400e4000800c40320300904100305511140000f032030110342c06040300d902342c0f2610400c940d02c000591644c0101e125840d06a200c2d040001c50f000d40035904040c0c481d100816142c0340c80c01c940f0024446801c581010341c22002d1050062080121a106890140004a06040c180007940304029564031a0000c401c0ca1604040740701e042040c01040c3c0b58070020402004039290700c124040c02410380314144030590b01c0400d1040000780940c0220b040764041c000c1105820300e08680c001420a80480568652007199a40c05400041c3c0045102030326003040c60044d440c0c007203180e80c01e14401c032140014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 968956142 1250 968954892 968954911
    0x152003040c180c050a120b0a0303020f0607090f090c0504030b15030f12180411040608070201060f032003101109030c1008010608040f02040f020d241a0d0e070806 71
    0x20426411036130480151101c4024528000009807003004403540035281d100308260300610788480c08000c0580219413120309001c8101240d0aa41d2020400c9031282600c7c4109a40000350610510411649402110040002e420803510f0290b40747e5800841640480e14152140203110030201e0602d8280401040b03407100d1801004400381c0071042c0d210600c5218006000f0100345003503130003282c90300d0f048804001214040203459a82e40c01d03003d480e92004543c098015440c010002c03c60030301d2965000309a81d003081c920301000512102c0c45401c14114510aa41407060002402e8010001d001d46030340207450004141d01c0c1c9120b102071510b8a82051001d500c1280760f80090504d59a01164150444045181c0f4560356203543c20304126030189850040e411505181410030300070317107a400909060702070300d104108070443d42c0c01040c82c12440540c541d2403070070090810014044040549164417522601051030611001c00300c40846141307601d00344c856040000b00b0407410100344a030f65440442403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 968957392 1250 968956142 968956151
    0xb0a140c0c1f0507390501090807030201090201020d020111040e190e01060f08070b0d051806150a0509130303021806120703050601230304030e04020d0509070f03152003040c18 77
    0x340340f1008882c1404400c05c0001820600c3c074001c1c00b01c04d4105800694210495958440e07242c10000c1c042e0421460a070701504c948802c42d18907910501c2249900f10062406c03505040c180030b4140342440c2d0240c1918003807203c07004680c80000491262007861001400001402840d00c1307141401580c2e158010002a0804082001902c0790b0381c00320b038024203503c01c00207401c3d564803010014401d48602c80381213502c1884100003a81c15515100c1400400840704003480d540c0e65010002d0300d80c421101c01c403c22902c00d0710007000900907009001c290851032030440301c1400503c08503005403c0200c40038010852a0300388007110f83c0501c5400d402034000e10f01f0f1911501f512100401c0e9016014071610030311000000a02414481d68059038910310013441955030364808039437070000e00425102d000e4039000c1d0003000207107110440007c4c4102c03540540d03142540807211840308010151017080c101055916240007100350540303002548203511501008480c02d0405020315850341c007110040c80365900d031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 968958642 1250 968957392 968957447
    0x10c090e07090522060b210a0203010605160302280b010b070807121b060f0b010f17130507181a0904020d11120102070b0a140c0c1f0507 60
    0x290310100b0722501e039044012513898845800740c00102000d500081008101107104400d407072100c44004404690300f01d54403101d807910010f41e006c921081c0320740e8020a200b04031076481e103910040c0f0305074002c2c0240152401b0011500303c402d441a1816480382c0c0b00b0034420351400802a03201d03601d03405055002c2034907007414056a02c0400764030032028040e140b402c002c80180e0b002441090040031803070300030080c151400040e1038880b016001740304480e01c44034148175081c06d075544039180c6e441c80300141e9603e00302c0e20410203616944030700c00507046211440074800c43c4c2001c83c804010700d00040c80402c03103825800000098036011154500344000980800e4240851b090f034034100001c2c2c02030380444405400460724504000c3c0440940034254021400c005038003005030701903018000036400b03140010746c244d68141d0aa411604450402c100e400c20313203408501030f8508840500440c3d400081110b080c4500e103030038110b0320000343c200545001c0c0c9076410010907903405410010741ca5909050444040c40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 968959892 1250 968958642 968958649
    0xf030f0a0b13030f120b1e0f0d170a050405031c0215070801090e0f010906240b0a1b0807110114122a0301080d081f030b06040e010c090e070905 63
    0x1512000710104801c204078501d12040c280d1024150300b000074002c0c1c002040e01820b100011f290089120300c141003c40c1610000d040c903130300281d6039951004c8841044c031010b10700104142c00052040007001001c0c000450262402c002c00c9808650846101c4110004064000d15007440400e00404103a59039050203101c5030000c1529064074100d5001207a122001d90780c0910b00403030a40c0c1200b16600b1b01d0600710901681354040c031070001e209006078062007a4015124400b4030a07100d07010030070404000d40c40c402071040c84c0300e00041112020b0038440080d82d403100000c44d040030f5029290741000c2d0340402c00b02e41c1c000e01003203400c990b80c0050a0070305140710701046041000510001480b0b0100c12050b0300c881d00204003000c00c0c003070040344da03880b0b50b142d00303102e0390341c500c919400700c04100d0b50000726440800240980d81c41c5a1002190307011181159103580400c90b0103080036400c542c07503a45e01c0d0442d83c001c0c009d241c90040c02c1e56500d00b545182298078015a40050840028091030005c2031100c0e44 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 968961142 1250 968959892 968959907
    0x312180105041a070f05061806150f100309020d0803010936050c060f131a040b070602070b0a051603051303081015091503060f140f030f0a0b1303 64
    0xa03802e101e000e85400103820305617031051812030f0083c6a4011502000200489804000e401e454402c0c116002580d0340022060301c90208800c0b240d018400e216150020b10702540d440c00135004c280f401081755441c1e035000c114110f4923103204850851000c0014401c0c52440c0c8603880c070840c0c0c08100d40c083ea242240c84910014104003162510803440a45071040c05000c100008000401070242075461003032803115240c64121294503403940000c03031000136001400e9041c800d042d03413080301c6d01454580303003400790422075002d490100c03078040d000d200602c017041d040f100443c4210314071b110100b030324600404c0c040e000c0c00090402506051800d010f0044000030f24844011050345401c0108030340e25105030f0f400c0c00359101c0d407118034000301c091014466250310050700d030102d84414498015203d00490705406413159400756411a4172481c400300002445031945040455000d04002801c00c003401c0400d0a01842c03035031050b402e600003074210082010f44040035600081c441107200006c0c2d041d560080820703 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 968962392 1250 968961142 968961179
    0x1b010c1d04050c0304142505090105060f03180118062f04061d060304110102100504050c0d02061b030a09050607020f010c0507080613150212070518031218010504 71
    0x1a0145546011940c0801072468281010b205041f01194400007000285405000d0b00e401500810000501c50520f5015a01c41003000d9a1041c2183c0e40e0814510040503c441c03809110340d22003691500c0e0420103170f40c4000160242d07a02107829004070b0520f0712030340b910b0481490151100c2c41060703200004c0106031030548420740b0308888079a0110b04c2e5400c20012128440d0b500c0f440000070b100c2004100300c0c010000003001e80030f49034030300c01c03840451044660407a80607000f034000c080c548020b481e05480c1c21904901c000e001a041860030802c4080d08660810002125400000d104130300702d4102da807040c0103100c125842480c04a10b640403500140e0340f03401c2c00f8140075900403070704100603091002c01c2c041c020010440d0060301d0f16808220f02044802c5080c0d80000c42911840300c900c05a00071506c01040212030814140c49101040300c0640c03002c3c0801d0134001e02c4209814bc581d80910504140c03081da828035644038100320566649211844a8280c140101084104600301c000c404c1075011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 968963642 1250 968962392 968962403
    0x601020d0f0e031f0203090606010f02191a07030b1906120216050f060412080112021005130b0d0f020c060a1e06030303050f0114030705061b010c1d04050c0304 70
    0xd601000740071a2a2400104000b091990300d407048a400c0d084903405180f00b00c07010f6040b603109498400042d034179411032f85034920041e0070612841e5606244e0341001c0d6005807082d558040f40040d43c0d5040d01000c203040d00c0c084001f03500c038000c0060920380700b0300b030306100c49680841d045164903084001e01700070403200d400c0b01101d80101e821580e104102c6007201d171464205d403d4a0100c101d02200c0c80e12414111811143d5280040c580b20760b05100d81c00c9030381170798406003900c3c50030b0002e80c003089000082c3c000340b54100402084490b4413160b84805150041203411559500d0710b0f035042229003a00d00c003000464005105120303034500301e0f00020302140c00201d00341c030001c3c04001e10b6144e40244488601c0d0000751030304015000040503410751002e489000391000c02c091a980b60b540704034400c85804486645036000a106000b1860035400810085c903030b40071105003600380d4000903400e440d04083c0300c00105409440001c00043c00112411160384200e40810040c981600700405c00e0102a101404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 968964892 1250 968963642 968963657
    0x12020115061706030a020a1203091208030a090611041d1e0f0901022503030f0e0606060c030d06031101090f0e0123130506030d080c30010e040b0601020d0f 68
    0x43e103007408003d60542c0c014003031504260f116055401444507845082700060494400058008003022480800507400941d1600d90380700c400d001c0c0301600e00c0f00c9083c1c601c1d50b5110b4104070107400c000010b000801080c080c0d403501c6038042d4011a82c007d00242034141c01500210104c42201c050001c40303500100704201d89015845507048503009000301d40480407204160300a040c84018081c28501c1818429601440520702d4200100140c174031b0341081079595803144000c00d915180002c00b800304a140203085138140f051508a21342520410350007914503241c681e11000c1c3e15680300c0c4865000d084101e05804a280c50075602c000d10715030500c940748125503049405a00c04600000e04042041c004154045ca0141240340e000103001c00e80f0340c20701c20300c01d000074190014000e141451040b0044c1d0101c40c10110302601114030141c1c503101010840741801191182030402c03145840c040c00c902d00c2e400d0010316183c81c1c161400c4d20043d0400303065520412085d404564410609250206540342c50b04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 968966142 1250 968964892 968964901
    0xd0608060117120901140c07080705131505042f030a0c050304050a03120237140f030603070f0806040b0a1e151206090c1406030a090503040909120201150617 69
    0x2e038500880035040c05c40d0288c100c0000d040c0c44005050b50682d2021280006040403141c0d080044801d11000d40320204466282004640390940c0f080501d06860542c00750b03d9000c00c640c001c2d440f8600300007452000b40100c20f0008920551050303040030007617410400e2031400c0c0340e151180c1c2d400d034240000b001c0241c0c103110304001041c0364054407080080d182e40c2c496500200c2e03500c0c01c0000d044402e2015070080f0300a41007080d03440380c40d0340e076002420300520a142156012021135107a1004140710381600c243d000008000d590840660000c042c041301400060502c0d00c0c21401640d00500124502c07401c240300a80092040d190414003c407100c10000ba0b501451041040415144d91101d00c6692501d0810018404180c120300381180c1308000d50742d1155200c440e50320798007420b40100c1e60400c405000084e4400c540350f12861a041c000d40899007019501d99250040e03820054080750724595181e05e00103a250240201d400005904030360708000707420210004d15128100000512802c411000705 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 968967392 1250 968966142 968966177
    0x20306010507080304030c051002040f090f11070b0403031103010513020a0c050f240c1c06030524070c05060c07020a0302030a06090b0705190809030d0608060117120901 74
    0x102c80d041e42c032588158aa00d841e00340039041c07004000c0151042d001d072600c4c0240710345c6940308540603a280300e025080c002c1c2c00c004a8000514180b081800047d6446c0002002d2042d01406020f200703100340f03a0203074a0f15092074010141d07034100c40058501e030410300040c41681e85508070a8080c2415100040c0c0307820201504a404800c000009043d9000c2d0308041c09240c135020404441d951820140340e0600b0440034400f80c030248007200c0074000840140b010b00b03021903250b4601d4a404510400200d00c40d40c60740c8929082800c1521000f40500b90595440cc0b00c92100c1040c951244450030225446051521059140c1000502010a054000a000046503249294030002d59006003c50303142c425940340540c02041c03030610607100103560b0070008050354820700440d4001080f1548409804131040810344000102500b5512540401d12503040b510100348185001042007000800c803951421004405d000d11102c10803031030b40c204281d039002c1c0c920b18004590f0600d00c02e2800548010081544 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 968968642 1250 968967392 968967397
    0x102030415051909061404140f0a030506090109112d040603140609151006080720010912022b090b0703030f0c0908100b03030f0706050411060f04090203060105 70
    0x80804820103c0f06007040c1988007030072100340c4820ba190703030b920b25010340d00781c0d94107000e28481c1c1d00041e11403040d140d10390f0804814a500d1114090090305050f80c0302e544050410008940b480c2c0a60366940c848020320070140d08550425505403800c80d420070111903005619040802d400031400541400c000e13581c7c44070b6008a00854000200c1e01c80668072104098a490b4181c407890203074401c2c00708590a0740c1c1c602d169036001c3c0c94021030004215280c00000d440c05800244898203100f4035801088200064419103c2c207903102500010300c0070b0323540c40c10440d100d101c00100c008542c080c14803508a2003449603840000d05e00385104042c03140700e0490848528805800500a010380414644d08254258004994034600e6031010300001c000c008080703858160078413851142ea403103a5502228a4815800241d03480c101500743d80c45c1100b50010440540e01000040311820780d50010032092250f412914011548201c4059103072140d003018a01d800d028500410364035943c0000440ca840e03015204 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 968969892 1250 968968642 968968657
    0xc0503090f06040504020f070606170307120504030c0b0702030f3d2301090207150c020c090c1b01060303020703080d090611070203150402010203031315151a09010203041505 76
    0x2907581f0200d02a1402640c1c0104404072105400c0c14004190a1451110103400c0c41800005505050302603c404001c0038019840d00140041044040040785410f034000001c0c007c5040c920f50389282d14410b00d03107021121280c0000d6904640d012022026040c1114039504441b00b09000030b450340344048e6060000120610180035280ca1100c1c100b044c5c42d04040890365800c01c041c1d0015a980c0c00004040c3e1184000082803000c120041c09560502c55204c403525503424812281c2c810821008141c6508090f140311301d07480000305c0c101d4501c1540703030000045040c40340000d100325440c541d00a940c89045010003406283c020500106140319a44042c039040c0c2c01820900c2100c40c0300108440a60226a0580c000c2c0101d044950a01c0200c03404107002e241d0686c001e600d5a542d00c00e0001040c0c844080403500900d41000b040c1a405690084020f40d401000e901c1d842e4900c4c042556841158160030b104403c1028800086a0780c1c011059504583c3c4403008820201000d500440f480e102c1c001c07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 968971142 1250 968969892 968969899
    0x10e0306191b08060a0b0304020102060414010e0604200d0f062f12070c030927020d0204090b0a0605040312121406030606061206040e0f060a05040506070c0503090f060405 75
    0x20300e41490b0760307804a03005019a606958803401140c0366184200188070456000c2c1c09a80607034045000500c0500070540c2e241683d0000064105403500e415040900540b401da03414501c52116a801d00c40c0c61405020780b80003100c1e00e480e0303000c0c0d0f503503040100c01c0701d018083c051998a11014017201d51003481d00031618442d0201c202d210b20300340d14540054000e50809a4281e110078006820740c0c2c0211a02d05516405032a0665440e242564031040c80d408503d0001c4108010003048000c036100f03001510109141c5000035844a0400054a0441c3d4510b8501c5226100b605020001d080c1c00000b1142501d420070174695050b50050320076079007031200c0e25024400c286406900d0540684401c4568091002101652003030344038502000a640140501d691a0100c0c039404504540380c90380c41400705410070403e82d40560301c94024281070900440d02014090f07120002c1004102003070058540c050510700700354511001076100c3d41d07506d005080302580540c6450050030b42030340e601c0381664020040217 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 968972392 1250 968971142 968971181
    0x13031509051501060207090614100302130b030604050603010203070f0e0a0b0f07140606010e060c0a0605100e070f05041202031e030a110f032706070f050c010e030619 73
    0x240a1101c103042c2440382c0b40040c010000003140c2801240140c0007150040d5250303094508680d001c20414a410340c0804003495420071203030312442c018414800003060100719003922480c004040c4030541340c0003080107200c0d074410401c001a0f241c0010b64040d184031545016010005020080b81540060380c110704001c60002c10710400701c11461008200303151050000306980350306c2c414560350f500401e40311507011503403040080c00242059000341803004284421210408084e403034500444d0380a503018034400c56154000d000884c2c2c3d16065079001001407411f41b18040032801d0007042c0d0b004502803840260044074000080d0340c0c04201840c210708842d905c1d00441c1d40f10308183c0c0e2ba20340c401e00c1440003081844001145465001c03a6030380c2c03400e544034041c0d03181c82e08841c20850706444003400030068182000016100d42c035408050210207218200f20000c00d8180e05045152650b00d940f035504112070140454003e0b00c01180041d0000580e40701919080703248840c110207041258060706c0100400b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 968973642 1250 968972392 968972413
    0x302090a0b011206050604050411090d03030b03071508040b072303011e0b07140a1226044215060206042f03240a021303150905 56
    0x1298001c0781034160076210300c4090402c1c1c020034419030300d140c03107555446141400308110500705600841101d00081c500c8034a1310107820000b86000c1040502540004e9599920700c090f405d04101b0580608900e140701042c500c0c254100428400000b0801810724842d880852104d500400480c2405810b07840c1000c0031018903140f203851070300b092094041040820079a00300c0c003145551810103541491217924030f41107440d112081c4141300c6107102d607658402c09a000020450000c0c5e40c0d585250f440da120f42c91104540d00301d003d00150980740e07504605145060000081c403034075000c0c48400755000080311310882c0c8138040ba04210000f802e43d05800c040c003420103000005030b000e8159000300415035000389840300b0040380d032901c04680c000e0100580800d80724001002e0b454040001c42c106d044220b080e00408003190a200104c00e1003c0c4448068001c46ea03900c00d80c5110756070245103d18118182020744011011001c4244005081144800003148c10082140c01c54014290020708507490307440d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 968974892 1250 968973642 968973661
    0x20408010518060601030b0916020c03030c06011409060315070201151d011707030308250216050f101413062001140c0913180606150225030209 63
    0xb0200d050750036020308030006996602a1148082141c1c002e07291400b16030300c18081102c40040c807102541035100e040207074059642c04000602d841059580a0725055140800341112510402507861258074a101040581e840010f000004182264030036400303521813610a900400c0100803001044148110105081403082003080c000700d84d4403283c040513039851031000a100b691702c6290007241c000d00002c201080c0704100d280d401c4008440711000c03001c244040d0b0600a8446502c000244c0c00c581c4429980049940c96040102001e4990000120500c030000780b001d9082c1a00307030244843d0114402c802d03010907081d40c52881c0303101c040e2000300d03880e03000180c44400c0b240e00d640f2403150f031045105560207043c02005140311103086036141e16104c0018600e1a600b01c5030360607030041c00c205c80c072a04c400201e00811841d48006040359800320700b0742c100441660f801e500f00301114114901000349140d80000d02d0311080200b25900e00d001103892401c3c1c484840c0c1c56101a500c4151102030042440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 968976142 1250 968974892 968974921
    0xe01060f02120a05070b0c0d09061d06010f0b0d0213060206040506070302210403020c0d200108090607200f01050a0f0507020a1209050d0f0302070b04080d0e040204080105 75
    0x900c160225481c1c00c2c2e02903410302d12841414021000980148030a600050000d402c598101010b600c00c181400c407402e12484c100c80100360250f84198a80003000c04002c4030306044c07556180c0d024041c019a40c14071a01055041d105c1c4680d0340d0b050390001d540c51402030141d0541b9a245106000ca0801d5507031000d000b960740c20142e82c16900350284c440072481c000d009108036003003140c408800d805514403810b804009035000400980a500034203100703e00035552281100307010343c41190041b035400ea41c2c05810324808100200603050088890600c290303100002200c503480b0302c440c68000600080b00c401e21402541490044d41d0340c3c4507038441c001e00d41c00c041d00854030500300c1c00400c01541c5816007143d426910103858010258101210200100d0154405034084810b103041804080ba5540c000c145005482c03c401d460580c1d940d00800d0406a05000c000024812414a82d05090418148176250300c05505c00e13030240706540d421030311f41d0b0f00c894040e10020070b1583c0c000c101c00d1501070421407411 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 968977392 1250 968976142 968976167
    0x7030807050601050607030e01050307120e0a030831051501080304060f2c0111030f0304140601060f05070c0b03130c0e011208030901020403050319031a0f10090e0106 73
    0x2070040b500040b8250034010180c0e10150340560300c1100c000291001903420b80e101038000070800044e50400910803084d40500f0068009000042040ba940342c14020308050019001d004040c089400718a071300070f8560845082c501c800380040201c80c3c050714040d403406801e02070441002d6040b800010307446a0102c050300c100c4100b9111700710104082107040b82c94040d6003070070741d0303101400c48101e0707079030402400f00442d485034103040c00300312010010b56030761454110406c0b458244038000100300c00c00a107900d24a8122510100401095050040241003070918204520811030040303070960034841c1c24000350005000703844080c2da4034281000900c4041e070402806490038048840005820070400f49110b04803142c4005050355050a40d03220740c495800038020049642d001d00c03022020400034001420762250907030749500c1c4220b400201400b61040020308003c3c0e00244010206282c176101c030040e002e440101c0b04c4400d070405140e01aa0f42041070340048403c80042400851410340064103154030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 968978642 1250 968977392 968977403
    0xa1805060a060e011a0306042007020103060b0301051008070507080d0b0f12070506130b03010b03100b0c100f0f14010815160c020105070f06090c14150a02010603020307030807 77
    0x709881c2c070191880f1090a209a8059002c40c1083d41e0420303a42c036000c0c40c0c02100c0100082407000e05010543c0f0004404009026412400101e601c21503800d407207014024807008040600b15031402d80081c125600c144521028058007900242034180321760b04544415900c210003d0316014410300701402000c030440d0190042c0210203102c0401e00e000b42c07903420012804401040d840c0d00340400c2c480c45800550800b0300c5500714040c00b02d040f00c1c0080141d4044c019041c0d05a450745443e0134411400007460384000984801001010040e00d00820b1050034a0003002020603104c0c1c40c998000000d240030700c40e41083d40c0c84d01510089461556010604840500e807c9440c8542d100c0e009882250091b5100070700500000e0b0800149400b421080207050700504000c0e0074103040c0c1e1a129844560304104a80e416503ca1148040001c0000108003910414888914100b0301101203480321100501d0702007400c5021591003c854401d4000c08041c55016054550207a80d81c40c012510303802c5220b08440 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 968979892 1250 968978642 968978651
    0x1306020d0b0411131401090e0f1b0f0403020405130812070e190e0421020a0516050d111c110906010804050a12050f0a11010501080c180a1805060a 64
    0x2100c6206000d641410580c00b2207800d0b04d0386412440764652041c0c142c11814488600c0380001c410781144041d6125070080b8071046464600606043e201131021310350505400030501030a91020290710541c0d0036654165030000311034450907003103401c548140c0401050135400042d100c200b00e28400045000d4040380d21076100f524418410002c400034000070584105803005400c014400b0249401d903046406045500c008004c0e0304140c003621008901e0304805640701008a00401008002801d01c10010b425101e000d1400c010010303a48040e0fa0301d01030648803401c03551107071a81c0d9056045290180070f801c55006000c1500c2c0c244081100c0610991040003020300064107940581101c611455005000d40f808525070350b1200d100440115515081240522502c4d070340c8042040204010000c84d10f500b000300c03c7d0f60b45940d09448050b004403401d608080021421500c0da45400c400748021484000c0040d40c0310041640145407018409005046a4000c50140b10000c10700a000e608035000070700 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 968981142 1250 968979892 968979911
    0x1e0c06020a03140910031e020c1506030d0801090c0e03063402030304030c050a0c1202030f0705060910050f040b0405091008100906150b0301090b15121306020d0b04 72
    0xc1d43e01030b0100c4c00340c006020764100d0a500e40310354081d001c10304180100850307030042ea00c0c4c814100d8008259003801c0398030105030014174084c104050307503110f40c0c1200106159005101d001b00300400600c10f4500e415101d59020b90024000c5c0d42c0903d00180207411180140740182028026640418004500003100425545284a030248507603410744640c004510315100c40d03400b251081e40c240d2040d00c1d64000c9840000000d072011000704024001c0c115015580b000c1d0b401018207080d05403096035072075030003140c04120603107820f0250741c4a084100c0300100705201000040d07501d8880d1901105482e9800607000c5401000e03100680306641c0c2c2034403456015036a03909242e20f4100c2901031022550301ca0524182c01c00e400d500104007aa10402002c15021002107000e0030044198101244000021006112040b010b20841400c1007040300d0b02d000400300e9500000c210701c1000c0c6022101c9078809c1c001a040241c0b071400c0850b20354080310071592600145440b41c000c003404103a0520490802d180305 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 968982392 1250 968981142 968981177
    0xd0906030e010902060301061b0602030c09090f1005010e04150801020705070b0f0d091109070201050402010f030903090b070303150b1201092705010605130b0406060f08041e0c06020a03 81
    0xc0f11056019103a1031541c1d003800c0c400c1d6088040d0329000300240682000c0080015041d0000c0e60080380c00800c17141c3c40f01407a40421a0b54007005101240f104110002c02c4944020340604808443d001e00b05007201c031740960080741c068030f18124110b000d010b2007040003403861015401040041c0c09113003521850f84e00d83c104130380c007489440c006101c5000300380b01e1054909020b61160405c0d62241d800719a64000001c08590f12042c1200c0d0040503075914400c1201350358000c1c946003000350030b0345002c1244005966015100c030190b8001d00541103000f24505042501a41c0300c1d040d41444402e90300322056685228044950240804082a03280d08000007500c0426024210700100003600c602016540e0ba00c201043c00818001900d066480b503e002410b510b80c1e07110300480307482028010402920030010300040c2e81d9540d21440401050010310403026a12007096030704564000881c01501c11601d460380317800f02c07101038080d01123180c0d4000010110f030000340d4240494403d8540c110400480c50f0306 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 968983642 1250 968982392 968982401
    0xc01050703080f0603011e0c090b0306220b0904080a030c05040e3403020702240f130b120a15032301150801021b03090a0312110d0906030e01 62
    0x1008240b035880450f08901210384240e503c200c000d4000a064507580c03002ea481540d018000000f03960307075210b05016065000c08130034042c2c0110701500d8a10b0901c0c4020900080d00a4010b0456200020462050b0901601301c5c540b0820010004101030400d418009920351200500c1404a454640306614007801031040e681142c00000c02002e035640c1d0039440341040c0c0300c1c41006841c1f1080f0140c2c0103010b00320f281d40710a6204490703580143c0f90380440c414011240e4040c0500c07403808180d034030100f006c450b0040481e050400c0814410342c842c200c2d0034040c00e50200542121203410305c0801c8081100c242d130b000f464403c800c0c0a00c140710500080349a00042c0000c1c0c000601201c0d140001c00301c4007003040802c0c0c40301054031000050362200c290010b0790b9031801500300707644a94002400452110000b60702c1c880c074103034400245d40b8014400c8001054510746100007810058101388082d5090f0081c2c0507054640c0102d02928501840000020300c800101c2c091180070920b800a1601d0503841440b4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 968984892 1250 968983642 968983657
    0x250905030604030c030c12021f1107061508030a030b0a090911040519060b0a08060102060f041106090405070306060f17040b090106120b09070501030b130f0b0406080f0c0105 76
    0x7620031a22103032400c45101020f401c064040c41903215080c00081c041c0d450f176a40c104910f90140511501d50881c400e01c220250054140f8141000072030f60124501c80d00b2144129848031001401800b8020b46411051099004040d1030101007100d90340240c25420080c201141240c03040c09464550610f482118601080588440e0640201415070f0034290b10260f000340001c6103800e44040d04003102c00a032442038001d080c03221000b140c2252002e81280c946c64001600340041c004500e00141400d08015000f0400340c6011042c0c42048981c3d1220001c0704c009182c090710602c80d42c03911000190107440305210300780005401c15840b0604512840104400d005a08202040d0342c031a51200c030290103014001041556803540000741c7e840d26119040301003886a03000c0d01d010b10b0011034590800f0343c40d03480b80d414581440d410005070f6070307041680d102846443d01c1c001008685561000b0041001c1c80400d90018170b0300c9000b01e0721120000318804910103240c1180d182002e2140115210f000d01c04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 968986142 1250 968984892 968984899
    0x90108180a0f02040617031309020c061902040312080f070201060b09011d19081605060f0c0114010801151a1b21040e13031d0a050306250905 62
    0x8072500c0010001c00c0c1075241d49000038004281603450f880030170f01c3d400240302101515800003841d24031141c140850200105040c000440c00e000c040400181c0781d01008001002c02c2e0039020494465055a80c1030700c001c0d54120072061485039104002920346002a01c15011503842a00000c203414414000c060070b40c2d0301d5113016410110284015a000d400d0a0740c0404c5500301c507452040141c07110b0160010b0340a05000310054180707015221800c02c407100a80c1c80c1240030000e4103000d1525244111039600028221169803142c41040320b03801042c0300000c1260038000c80300005004c2e031054100341000102404440e50b190359542651004007040b41030130b03550650500080b05508241c0d1101920b0845282c26105010b060014a040b48c0c1c100109108540e24049001e12240c480c01064036440050074465400821003610098a14014000440941007941409032040c1d00c0d000f400000415029088071454201450342c01d0048407034000d51510320304402c2482000341c1c803e017020005c6030000f4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 968987392 1250 968986142 968986153
    0xf040807060903142e09060e1f2c10110903011103010302090412120e030304060b0d150c0504030503040807060e090411060d020909041a0c0403170a090b030a0209010818 74
    0x1600c201020405440c09120650346c0c0e450400d02103009801050040b0300b9a10152603010f00501d2444a00459141107500c99458009440345082000080c000707041002d40c54884450544420145000c4083e020385490a0514603d507400303140120103002000c80c1140240851141007586140900091202039881141d02c3d001c5008150038035000d030b503503c41c80c0c0360082d0a119a003a400b42a220340cac0c5d09190160344000b041009200551040e0000740a0485880400d0030a80c1c9031044019a004050040d465071104141901d030300410442c2c0c002c5900806076a01d4560798082161103070011f01c90440400e6508908400c0351904400c1030b8452039002e80342d0300494010030144141a0401d0307900c1101540d003040f0351160f698034040c1081c8541d100f0b49480d00028150010b010135420302400d841c8440f04140401e000103000d1b58800c0b18080c242501c4c40392589003c801c1210311310255400410b20600c0002440b00304c5171580c00800204c442030300c51240c1074550038400f0500500d8415028144d0f00311 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 968988642 1250 968987392 968987443
    0x2707120c050f0d0b030d081b0c0d0e030f0f01020d0b090103210e060f0306150a0e010804050a06331203051c020301060905031b0a030201050f04080706090314 69
    0x5200a84010320040d00e00190074860350f4042803514046c8882800400c5190042280c448680d07000d0f02034059022104500b4070300e0000d41681d9170400701100009100405019059540f401c00c03e03a450303082c451003103a184c46801d10071a4000d501c203500c9074048605009501405017072450300e86040b00c0e801512030350105090040f00c00500d802d08400030400508841d124003c2d51002e0281c140c80d40304041080c0e99041407020071038081c80c00d403620004003505015029003e80c109499100b041e8003801d00c0580f0381c1c1c0320301d0028181256050002c24480c5086100070380e01880140105c0410100c2c01070b05402203500c400440d030042503224205941d0a080248000a80b203100601545401c00e130741c400100e125030f40601c059030004d8000100003901801c003001a450100100c0350b500c5211040c5600c4807503010045403421443d400041e0510000184920030541184c08450003880c2c403806442d01c240d01c604000f800302c040c910080d00d1401080c500c1038001c810100e030103901c58428442042030000c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 968989892 1250 968988642 968988667
    0xc091c0b0c0a050c010207060c080a0606090506090d02040e01091b15120b15031005090c1801110105090c0a05010f200309120703032a02010e2707120c05 67
    0x2c08545141006410702503800742e00b000340085c00700709100b540b000c90401380d0500020502407000745100401070a1507000c11440340c00c807060700300780c8100b41e1390b2696400b0344201040c0302e254007400094026142a606a65180301075111401c450700c0341c114000d400500040791540342441c1d004400d079140020788840c60860148848000e501198032022456000d0300c40002d5040c070080d00b90885071030002040080e102d9031400104060a011030724000729041c0040000900d0046ca00c405001b40707101300d03048025a0203500458070aa000c0f000920081c9445000b16449542c146005030080410400c0820340c0d40c02408201026811a945c4c02c174803a0444031041d20054207030900c20901c2c00100114041901d03201c40d000a33002e0303842e0040c10101d242d40340040034807900c003803a044204040c401d40100c000f0707480310451586809103842c2304d503503220000082000d10748120030080c01c4a0f00d20071391070444499070110300c203003103070b4642c6407058030000407080c1a43d181c03400000000d002006070301060b10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 968991142 1250 968989892 968989897
    0x80702151e0a031805070f061d040c021e0304180203090a020d0c180605120d1b0312050109050702012403081e0a050d0f06030b010b071104050c091c0b0c 67
    0x15852502060400c2c0907900f46480013200401507443c0c0d0080503044c4103481c40104d41000038015440e1284a022504d18024040d664000c400d92040f03403200600498180300304017034001908510504d08011481355a1550b03603900610403c101110340018600400e442c61003502e1003410001c02801003000a542000301d007228183c01181c040c03130b842034003044000c0c3c0c00c0c0e4414040300045070001001030410041149500e69070450707804035401048030003022980505a01c0e038101010103452640c1c0640d1070300f603407400042c0102007640c4e850040002141415600014080d1066400810407902103680c0702d0000006400400502c81030050308100003601e54008109801c06189840d100214030701c0b9002d43c0303502113801310340055804140e4180c3c2101d41c1c4650f11001100f000d00b040a41d00d0740d61521000001445008510b4202003a88400e00c0071900b0950142c54000388100581c0c60200b070340c414590440e540702c41c041c2c0b5a0038124030640b0309821840c030810307400006852155031204240c141c2e0380d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 968992392 1250 968991142 968991157
    0xb0a0203091005180f0a0317070207051806011b050c0d0212010606080105150319020a0c05011419060b07022e021507051204060e01020f030103080702151e 68
    0x7480b6660740303580c0d00e404a216843c055208011100c10039200071001070f280c460651000c89446d0403030b940403400a81c101ca00d4006003a0751148049240d6208101039081410583c8040c0e0400390600c04030310409000719615100b51003d8803091300c07412116082c0321540d11019002040760740f107850302e001c103483c1948110414034030050011000f04850f0040c5401e48426600c0880810f81d58001031205103400c0b80000e030007900c40d0310f14605500d0490309421212100521030030002d40d0003e4140c4506220f4190300104a8009000b030101d62050656404044822034503080c60740d43c00b01d500501c03101c040c040c5100310340200c0380c0f840c102010364080002c0c100c03000d10440c040000010101c042181190744148484507690007800d420f00140000b255a103600502035420031030b04202903d050500c200809400941140d000203011010814550081c42122a04080100044000001c00485000070100ca9109607070003010544014810038050166083d0390104072102c1c21816145405000904150b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 968993642 1250 968992392 968992411
    0x503090a06060f0302090c07080307030504020607050105090c130606210902120d021c020a0f0203030c100b0f090c03011406091f09060908030f03100f150305010506070b0a0203 77
    0x102111651104200c69042c3d1140d000082c404500f0000d529107605070a41c4840e5601c0c08901d44070702a6541401444014004801e15070790b0310101e002d54903418107850b44e01c0c1e0b000000308460b0a0403001c40d507aa440300c04070302e40300d820361008503408030307420713005900860f8202d840f4640700342450641c0c0304640e2104040801010307a10000100580c2e0307241d2084d5071240d840000f0b003e09501d0484000d04046000c5480000385204051482081d40e0000d5a90b40040c0c0000030440300c1599480040c1c218801d8400501c2c180c030640090940c10041580b140542034011144500c07911441400e0090780d96003214110010f00701440100300502c00d200042480000c018030507490842582c001074a60844404003011040b4019101609160003c907400042d0002c2d045c900c00d61440d00281664922541c603000c10b400b000800800d0401901030300480c060840108403201031070b1148101100020358a0101c00004d00f080000030b2242001c408440c0a50f8001030400f80c260b42c0c0d4600000a0361001d07100402 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 968994892 1250 968993642 968993653
    0xa0504091e0207030f08071701270606030b011707020d08040c030203070b04051e032104030b01081f02031003031d130e0d082202150d06090f020910050309 68
    0x110710303100409005200e5207840001400c000c0d00208803001c020005001d00c00542d000d04018200d17a8045c604407100d0741e220080703030240740b040b8490803a08894080c08182c213011000c6900e903099003054100180aa030340503044003a400c120021300f030381034075601d026822480341e0300a580c0c071860340280d02c60701514180446903501d60110780307802c54550001000d01c0e800700b82480b8506d00b152031444441c1440750703411110125200040e454070800600f1141c0c039032088200c01c48a8500380295030040d0f4204080b41c00942e0344240903a182d00040e951002d0280e040c100c1c8080c1c0340414400e13207005481d03120506000170300b555420346001201075503100410400c0d0f04400115a6001182448440c2e003100100b20301030407002007071401011400810601c400c0034204103124441110f208614680041014100742e00c50000c201280c00c028103825950100158454a082c42074114070100c4203003010400c42600c000888004a001d2000010341c00281100d032800c0349480f400103182c1000110081e82d1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 968996142 1250 968994892 968994941
    0x60d03030908070c0816090e060f1008061003140607020a0209250c030e0f090a0f021603020a030e0d030512070516110a06081306091a1801050c0a050409 67
    0x5408110641c07005e146035112000c0c80f2107201485098100900000805110400c0710400c0d503501c0702e000a00b1103070034000c1c541c0045e11900e40080d010008042000030394000b41000420b0030480080d500040e5250600c2ca206800d040b400014441c0c401ca1155024203001c1503190300f04000d41d5000f5020500e5a450a0050005010540c4644c0c1011003039880702c4580c0081341c9030282011501c0220a88142c0c5080407001c51030300d400c1d00e120343c09080d4a000140da0312131010210002d00038817946039403040484860508040d000180d0705000350091b140c200050f8a8541048406420588005c1c002402480a0100001031001c541d8010101c0d052050900aa0713140d50180c4100c000c0c0d0136149004009141036907030030020f4000c006400240381c500003616000450700701c00c140082004000e180c1d01d0384042c2c20f00c40f030001d000e018030800c0c448682041c10a07004038442c0310580c03030041c3d049500e002c0208031500460022202d540300e180d1079070303424549441c900200420211056001000030b0700380d5907 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 968997392 1250 968996142 968996153
    0x504060b1c051204150c060e0102160b01080601030201170907080616030e03030709030212010209090f04111e10031103090303010e0903070c12060207200f010206060d0303090807 78
    0xc8074003401e854140c0d503072074071420034902d4803901010004103031604200c00e01801d902c0302000e90095955090050a40340c0c2803810000404031941400c1140d440490541d400c0712040407ca00150f002d00700380490790743c032030144c6034a9540a12000b030104080c82d05144144400b400103503402000709041d43d291302c1c1d9409043e41040300441d002c866503040d804000a94541510078048400400e070000c0d0309601d42410042e10325038a80c0406845110051221600b5000940465001038006415090141403891420411110656080b11a550724805601007424110402c40c032800310300f401806540440414040c8010045042004140d190300007900f0390780e007010086001d1003c10000350b40d41d61600d40114022a00038250500070b4100b04003038400301d0795000030001600d0200003c105044440c1c07404400a114050f0014111106070420303820181d044561260020000c0d50030585402209004a888000490f040c644c03256847d1000c90100c0c0c0709921020b01544280007040c5032841d5620b80 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 968998642 1250 968997392 968997409
    0x703181e0c0b0d1802090637050a061707051b070b070506060a060507030f1707020a110d0c15110a06020a03110a05120a15081501140901090504060b 65
    0x40411640000d81040c0ba444522550031540d13074041c401c22030750483e82c0c0010120324014024520a040f082030041400d0200e40c0107000310391030392103802d981425421025401042500c15584036400c80c420010381d4900492506101982c06074101040741da5001e4240c941d038100644103510840c4c0e01d100080e000b40d04005400c09800e00301600c544800b0145001032400308020240c40c06541d03807900030002c90790440d0079112580c1d41428505010301c9601c20031103964000400c104002811031051080c000c1d0082a56211a80a044900c0010780f880c403d110a40350049002840810241810409130441d02910710b0201403605e411400c4801305013801e0300d004060402075031900d60001d1032810054140c070072095403006803401b0b60f052031041040605180207515400103000086400030740740303694640c13101c41400780403100b880c0000c1e110181d440c2d481c0c80c45480801c0c1d1049420002c1001c0e0360700b000d04200b0384401007a0316280d82c284504400070300405001110295100c844003c42c540c2d03031011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 968999892 1250 968998642 968998649
    0x305130b0403020415080706110a120c021318021507020a1d060a060c060509070b04090c030e030301080c220f0b010e220b03030d02070c0e0703181e0c 66
    0x480948503800c0d4010001194180c5d01010020b81c0962410044001c01180203400c0b0781107414500e6240d0303140400355050107104c0000078100c418180740a00002c0e00a17800e0b28001e8020340e484a03511a40c200100f048070384440c4034034040c000301045100146000d5561f400c2c5415446480b5080c1071040c0d0101d20303045c6840d0040801d10350718000004c1003108603810190b214200b03c40b98007019143c2500648542c001040103401079848400040c0403a00822096004180f00c24450b5a03030b17a43c9030035881c010000481c3c1d1900080c2030403203c0c06001c0001054905943c12031000d848990901c00c100000c8001020b5124512040510a4101c0d01e21034455045d8400c106540490041c0540c00010101c1c00388a0071307641720355104080742c8000c404000103a403d40b0520350340050309400840010380707180500e14816440ba800000ca000800c907090b17032000c08942080d442904d25844558080d000d40e2080d4402c1e1304850060750303803080031440c0795204040c0c0000942d1400203000e180c0d11020a070b801300342c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 969001142 1250 968999892 968999909
    0x10f0608010506132018030717010606080f161119020f10080a1a06030a0b0901050d210504031a04050c011103070b06061c050603060708041e030513 65
    0x42c00c0140781c1c01d03c8580e070190300910200400c00c1c074001c4000c003d005602c0284000c814100441d86040f00351080811181c83d41006003213440310b50703a40c605508820000e0700304c142d00d542800c4001444501070b40005004400540b90905960b54071000380c40c046010780d2000003001031f041206100c450302171280c101003000d012030020074460709005001d014034501403000d0052040170254101c1c141e0049000381c21983c0317200003181480c2d0001010054141c0c46074920360104001041c40314007042940281d0f4031103815254622160380c0e51080182c1030f0000792016002d1880e03511000704d0151208a042c1c07501259040460920f030b104d07103500654101144402c10340c80341000c1480b0920004000c0004501c0c000d18208200c80c0640490580328060700400030a80d94285010548960350303141580c41039042c01071801c6400a440c40c0b200042d20007510110301901840b00480c404a2003007203880d12881d044042000070050120b4031411103070612005404004080c800d003800d00d074101c24540001d0010a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 969002392 1250 969001142 969001151
    0xf030e0d0c030c0605270621011a03010e04032d180503010b010207060e040212090a12080705090f130f0204050406050a060e01211416171305010f060801 67
    0x515010100d40c050b6082241030260920201d0340d0300c02070700a01043d54041c070f200301000315649401b10781a80a003450841c1c200d03003e854604070040340000c20274102c2d400441203e0a2010301c460740021440f0070300488001a2f9560005800310340070701b100c400c4640301000c04040729001e1942f0103800481c01290b54000031101200c12072090602190b100203004218001c00c0303551070070b00020350348100718402d510a100b803122080c13060766119410f031880f0030b26000b010455480e004a6164940010080c1222070a1880c007035040c1451003558000d04c18680d9840361440c6c5200d6508200c0300f1203803260b002e50b1150140e9690301d9042494000c005107440308450260b00c0e241000d0801c0b0a40c0e560f60452030051401c124200111517001d92407005010003801c100800b100300c42011440000c01e407051b51122401c01d0940c068114074a0007291003015040c031417014428040d40202c50541e410380c0051a582c0710b410101300d00340c0d04038460110292140b0000a94050644541d40550b0040d074450340c5030342d669 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 969003642 1250 969002392 969002399
    0x1020703110f0609030a1202090904030c2109090b041812030e06060612090f1603151815022106090606041a030402010c020d0507061209020d0f030e0d0c 67
    0x10065810808503541c0580702c0f500d4010040780d668028220400704214401c0c0702c0c0805441d041e8100c6012030301c050140c41d1103140070308029000f100302400440e80d1002000c4001e40501e100240c015200810350381d42144a031420a0789000b809c03a10314640d074050b94900704180250219154030117040c0c4112220b04124109043c05000c030f5028421089894004c001000b605580300b50850300c04d0000c551000361642c41d13941310903291000007000101c0c0792060200000d44483d2111150048a100d035001c106500c00c51808001039607841140c8a40c507115145d2401d0001316138602550094050344001400d004020880d00c214034044902c642140310381c001440aa03080900c42c9643c00b0409880480c40c1510307140d2540e6140e4840044010702c7c0201002040440e0b20402c0d0010f802c80d001403410410102500b003040e00c0380502c3c030507071005c0764103101c6801004040340150180c0c581c00900c01c481664064440c68a44e05450340110204084202c03035108a5070703000c000d2140240290350ba540700c070b0706 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 969004892 1250 969003642 969003677
    0x11060a1d30040b07021c08030a0212070c05030d0903030b0a031b060e1f020a0c080c0102010f0b151305150706051014010e030a051e0c06162301020703 66
    0x10407400060304000d00700428010b181000003103030a0603030306031560080002e800104d002075102c90800140030510000600090079610b80140c6840c40010184260b2616032400684909200340001400d43d042440050600e030f42c80e5101c0440103000c0c1c20301041e0307615070000040b881100c4c0e8108460480f03641c200f03010b020301201c0303d11025110707508044800c011448001548148030301e8504d2101c50546480311110f81c4203003c0e080d0240c1d405140c1c140b203151641c20413030711550482c0e0458019860000b81112000190181b100195000f420010140008405161b003a61201c0c010000417100d48000140544808500c2c000b5000c4011403a9204c5005181642c2501c04c0a042214410f4400d2002d00080c1201a4040710015007424582042441d24000c00e080c04000000035140d4007801d1102a00e42814207040b050762400001514a080b040700108603250180c041b002d9080c1c05101800d100003800c1045d14050f00000c0c1280240f10750b81800741c1401da0707100d000c1c2100001c4007007180303d56880 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 969006142 1250 969004892 969004963
    0x5060606040f05060a050d020d090201020c01140d02160f0501090512030402060409051906030b0105190308030c0a050409091a060f0f1005090d2111060a1d 68
    0x450440e00e003840c0c6890020000d8081500340100381c81803000160040046004d60100c541c080c421803400d54981000703001c5c050042c251100d09034054080e000c0b000649612482003030f90080c495410f403906140340410100c1c000c0d0007800030340da0146406140800070070410944219814810f00010404107102e29116082c0b005001048070680d1091080c4001a5589000c1e101074405000c0c0001300d036610348c59031780d5489001f00301d01c22540340380c1200801031050804c14141a220250b17510084c0d1130003010624905000d521020f8000a814000f0400c194007007001440d940209d842c00740d0405441d00c00007012a0012030040f41c080119000c08984543c000020b59032265080352182d810700c80c4c4101003078001d64054101c80c4245024100c6081c00303030281c41540c810340070161210f40303c50402d1411250110007e0300780c100902c0e80c07600700814503100b01012040302c52a81c02800460305e480d2009805800f441c00c0c01c0842c8075000c480750454400400c0b0081200c0e15081c0c0405a09180760290032018 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 969007392 1250 969006142 969006151
    0x60b040b0c07060804110f0d080d060f141804050c090c04060f03022106060c032d0c1b031002120604060501020309030a0201230f0c07061e030c11030a05070506 70
    0x341c00740c200304c00301b5444070b03001c5500d4000356541c2d4100840c000000d61aa040c00c500109407076000b00d58815640000d034451410f82c0c0c250060700c0d6a00f92500f08086a500a50864550144124001e012400080703080030f90054031900c112038130303000b82400040e2640e07802c45006e00301140c082410082aa8041e003030300040720f10f60030304514161004006030081180c0400c0701c41103031614400b1401c1921503a08950a280070b12040e640c0303906601e0041601c00062424450f5400410b403060440425032108880f44203007000010009103219130200e240601c041c62002c0da00d406051040104410580010f00c802026604000b889140200030007003104d00541109045500600c0a10300c1c5480c0000d05515094090901d0b8a210103007200c00040ca109168454494810228540f1080d00a05001d02400e80101080d00c0d58a0385400c0c086481041c0500384005241c8000200b0720703ca4080d0784120403007400c62402e00c007094a01e004040c42d65100c0020703180003403c0080c0710400d0110600105401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 969008642 1250 969007392 969007397
    0x702150f0c040902180a0f1a090a03031b0204180201080a060b030c0d060b040306020a110f1f020d0c020705030f0f030a030e1926032701060b040b0c0706 67
    0x50520044a1a0601a078012102c0c519400030f84482e81003c81c1c0c0314000701c10170040503026904d40f604141c1a0506507440b8907010f42895a00300402580341d401070701c803a0310700945507440c42d61a5890071038215483c408130320182041022110301507256030288096041074070701004e4200106200042101500030403007a14145081c2003400591800c800316604031041c0d260480e1a054245210b07802001c10307030701c0010206000180001004400d40103001e48044a0712142034049029145a403207034003402c1d81283d0794018940d080e510707200500044a01540c1054010b0808210704034800c101c990b01d012840241e8400300003040503207070070410b82c0509034280700038110810040540c95a01e02849000c4024146c440302c0400a40e0750030080b607100b0080b070600226038040c040c00c03c1348409118103180112154100a00d45072106808c0440f4001c0b0080b003200c2440d6100030341d11142d074070304c8003442004554036464009041d00055000c0c1004d48001d0007078035960a0101c80140c40e101d07040c0d101009 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 969009892 1250 969008642 969008671
    0x181609050306070c06110d06140114041a0d060308120a0506030a031b03051903052a030a0e0712030305060907021203011a12010303030b3f0a0b070215 66
    0xf40158050b4040c404154054030208522a03603009850b040d000c0c5c6c01801000c3c900d0103034006204804558019040d51081e240c40d0850340250a00301000c1c8128081c0c030f46505d242100ca188040401c800620000851080014090340c50382e1b01c4502c5680700043c01d0440e42e004d403041c00418543c500c661030300700008400038060303100e140c3d5000e880b084030078205800308007803e030302142454011011203c4000701448554095851036102500404056070307030815000c0440d03483c1c50700f929034401001002011004e410f0540e900d044819001e005414507c12540c0920ba400282040711030309071a501d00e11a484c080380d207140400c00d202c2c4480c80107081a045510030103940e107641c41808200c80c103680e144150b01c00c102800e0302c0844030510401800b032440c42c40f440c000009150b410b601982c40381000300c0d148902129111481c403e030303502100541e69640728070306201d19a03085d0792500b442c802e0701c1d032800e03120440401e8581c542104400c890100140c0c1000c0f83d2030349541c4d40140c040b940a1b12040ca00300303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 969011142 1250 969009892 969009901
    0x20109091503060b03011b09080c1e0f010207150c020126060d03020102070c0f050111060601090b090f060403030314091516021c090815060d02010e181609050306 71
    0x507400e10016080555401541a041c0c40a410451103094603903088a81c2903101d45004010708039600c25614140622000a0984d09d80080142da500481920320307100101040300300000740b10201e104030f040d889a6000088c2013000c0504c00d0710f410085072104001e0062030f00015003082c22126031000303501c3d180c5100c0d414951800f01d925800003021b540919043c0b1280c0f134141d00a106101001d00442c08680f0005200b03c01c040512080c0ca07020b980d02d0710014100fa104036500d4400303550301c601290422200344403814401001d80302c11341004221004080b150f80204d1696407141e041600040d450b81c06560311494982121078000a1907401002d0300240c148401d2f4000c0000f034007028200f40d0500b01480114420000d940324980410105800d40380d92a2020b070070202207110b241c1690050a480d0141404c03220026842418090701d032010348003155004460404c40c80043c4d9900a04c0317251140c400d104032090803803017040086803003032821070400f8024042c0a15030340100d110780d02c21402c02 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 969012392 1250 969011142 969011171
    0xb010503070801200a090902040f03060c110c060a030f1104052b02061303021c110a0b09040c030608070807030201120c050d050a020f070c090507020303010605030c0a020c060d0902010909 82
    0x640c2d0740c2c030000e2480c5d250440b07288121001e08660b813214010600116000c1249107000c0700400c1141c0c0311303074020400000c0301202500d0407140c0302c5146d40c4075002500b1070031850030400c0003044010b8642c9400203042070f88140d40012504040540d40c0070200104e024031007400e016007003c81c0455913038540a08280e2515003c407401030b125200900900002c610b030341e8201c02c5d07100c260340519801040d58800030004140042001d00c040c4041da244107843c50b1214079802c1051016080e81c0c00d00102528000508040c840030301038642d880000c00d541c55500080f1802c09000071400380c408003004c0e0645d13034918000100040003000e0043c041500d0140055041ea030440c0c1241c8800035004004a0070380d0340c09070064001d008507102c1d1440b105000600c0c404000a041000043d554040000c01164079150012640c80c0001d009000110300c080010074007811140010706414410b0340304403401a88200e01052050f00540c420750394584d140c504100441da001156900038006545080101c0074114031340 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 969013642 1250 969012392 969012431
    0x4030c060c060b040203090312011e060507110901082406010815043c0e0a0206160c0303210506060d0b0d020a0311120f0a03030507110a0b010503070801 67
    0x20001404a0001d00c142041a55040040d103c1c01c014011501c929080300d015031240c3c003d9282c0c5100c2102d0314000b04071a40500b182020581c1d80070015841c160511805640f10b600019060341ca440020307440034015612010031074040d001d480c01410926071500004245035402410302c2280204600030040580d81c00000242c0c03015500400009a48503040410020044124110000e80541c42840d01d60040481510a090090320028455031a0400014210f40c961072407003001d078000e45080340261400710084c140c2e1a04040d18191301c48820350b243c070b009015541c000c80200741c5020000561101c0020180100350b5160028029841d008000500612414800510700d079034404850045454035840703442c0300ca5000d80b080035215280d060041034080b024446900c20343d0209a104611030001c9203142d6003440719002449a408a07035815000340a00170030000401c80311124074001210108103105402c2c4c003c207501a0594101824503017011a26081030816a040c1055041403c125414 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 969014892 1250 969013642 969013649
    0xc020c1905091306090606081608150c09130204090c0813030807031d01091104150b1e0906070f05010e120403172101052e0c0204020d02130f0b04030c 66
    0x3240c41c0440c43c1e52503d40014400188090800f515004000c903440c94001503404058103071000615005503100340880c1d036074008040103407044a400d00030844551104029000c401001081c90f0003009140011100300d07081540b20003042038076040c14140803600580c105401c1103945420705a084580d450150000c0d001800701000c15544580c812080d18514043c94a0000c01c400280300b4403200d810000c900342c0200c50300b244114580719034a55201c00028940048814050b11075050603400381039000e9100c2030008100042d40200000c1c10035595150085c2400c5116480045450845090150071036614440d0001c036a803200090410302071410054501700c0f644011291362422421800c4d4409000b80818140452022006801687e40042220b81070f2941941c00b070450412040e409030032184002307031b28190048528024403031588184541940030b40040c0001d80341104d200c21000480c1d111016400900102c52400e0003007440c0b1100490007080160510360800d81541c462201070b104512 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 969016142 1250 969014892 969014911
    0x3021206120c0909030d06060c05060901060e01170109080a0309060506040b0105071103120705060a2f090328060b030c0f091f0b0301181104090f09060c020c190509 72
    0x10001d011138408004030740000c2d11440041c040b25503140c5015003140001d07001111343d03008450009508002c14850102103c030705541c0d2103d264a804031809400c4a001d10302941952075150820100f401d11000f440e03000255900050415036038100b0314200c1d4409003026201d1801c02e0174000c0d06a03880001e5800c095046070400d8107198010f800285003a0311710020404a03071000c030f0010144a40414210310401034240b0a000407540103200c64020032003219290282014103c1050030440550094500100f003d03040722248401204004240c8440c00d11040481004064103000c1110724016201c1d6045c080d40100203410484000507054031000100768000c018040004141c0b07039014400300043c1a0081101384866210905100c240e4400d00a695041138080070300c1c400c0d91400d11901c0c02c003c20802c1618105400c141e10040941440000c44003000e0320342d521203010801e188141c82c14a00340750001e2a0242e040000e002c440f9403035441d405500000c105c8100800d4851f802001d40c801d2214 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 969017392 1250 969016142 969016159
    0xa09231c11010e0409050d030c1b03090605070302010e0105090c0a0e0f0c091810170a0b040308090c0307150f0504030c050103051806090a0203061014040e071503021206120c 76
    0x1a000c10300405c1c1040001c1c0403889583c44081030150168010000c060311a0b50301080017422105614034503419100c002c001070740c1920204030701c0d4441c0010f403071218403910020030035961090403242520310550300c00b2540e0300410003079100c903d003000302c01009113800c804c1c6a94030703d0302440403507499600902d1755079914800a01c41005507219204860030311000b40f25001b040c00d000c0c0c185c3c03525403614055140c400036000c00200074103500103006044240c1c85001071100703584694088827149005007602c3c1c03540c41445541d40b03a82d0313000c6c0400c0c4090302072403000500200354120700806144a404480041c45010402030020540c5000824191002820040303410340301c2d0070100303241c81680c1d0400000c5004401c00c1c0001a000400c0a1113510300880480b40503495416042c52034060310301c6000381c2c444103048003044070b007081d810001400c0806810344010b6035651024410b601c60403000700c3c0020380c0c005070703041c1020042c2c0c210f00d0b0085000d44182021446540a443e502e00081c00b00074441c0014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 969018642 1250 969017392 969017417
    0x1050409080c030f1e03160e0f03190b0a091707080702040f020d0b0f011209020303040509160f031e091b09020909090316080a09231c1101 61
    0x100445500c6040807040301c3d542d01d91241320b021541c2051400722201180d104845100c03051201c29a8050b8808005410140740307040301c140c0350385030a0408240c2040426203c980540c4e014040b4100d40e100c49103c018050380a0702d8940341c40b55004100301903043c601002107011030200c5007152003030f80705600250340d43c501c3340c100402c1381d01030620001e61017401c0203410000480f9580260290384448070041c00040d0078034007000000180b801040c1d00198064443c0c2940d21429006100403900140a81e0700e400e803500e0108412020480d1101e103900c03103000000d251550301039142c1e00070701558038040000e5a0701d408541348000d900c0d0500344003e0749924180081c00409010074101002231070800601d01e55507490200a0f4002001061280d0600d1000602002d0040121140c030700158009001d59900d55403a0303480b035085100100d0820440d02004200c2440d07040ea03000020320800703101107107415407800300150313282c0f00d046d40c401210042014900046591040340811842402d00b100c0780b080c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 969019892 1250 969018642 969018653
    0x5071b05120403080702030d020a031e03090605131b0e040b07110f2104050306060904030516030206010f080f07060f020f010f020d060e0903070b060d05010507120c0e010801050409 79
    0x520000781422180010b00100700f082c040010801148203a05a40348844041000c1e62140c1e071440010f80841d01e00002849000018801c074550780800c0e0400250000700d0784c035401e0071103008860b1010031520580441e41400161030308111150b03041310001510b203091036401e50003610058402010b4403000004203c45500968645528401c043c0885608001048170b096803015803040f110070704a45207640c0400c0c90103140071202601c0300074004000503180c140034071041c0303a0020800d0b000c01c242407000072912800c1c0240030b103440d40603a000300982e5042005e80743d10016140e11103105a84070300010910031101098600840d5406e0900d0b401300040c0308130a17401c00b00c11100b45030f102d5182c010081075000c060303409490b4000109508020494440020240e941d00968400c000c55000703029010014841402c031541c407880140420303440308120b980309420350b00305495001c0800c100078040c1004d5a40d82c0700b840c01002081c900340004402507170000c0d1020754180650340c001c3d0340b40c0401e42d09001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 969021142 1250 969019892 969019903
    0x726040f020a08060112080313080c0607080732041208041802280210060602100e0a032c0d080304020f0420070212070f0609050405041119050a140301050a05071b05 72
    0x2508004441d503102c59071002f440c0c484c101150100081134440002c41c0445204506481100151800007083c03003500a07640c0c11090314244104180c907800300408640c84130023100910800703200b650030317036221130074064486001d920843e0f40c20281032045c41100300202b11080c0001e00b80760320420901040c56401030032800c050080c016841202c3c00d24400042da00c0e40020030110035202213900300100390642e0300f0705494200c8408007500140901148843c01d82640c0d41038000d80782c0c0740401c2a01e00c50f1207030101d541440c40100c10344003210080104829824298601d4504020440342006000031650104c040d000e07c0491591a6000100e01c01c0c0071900d03416525982c10342100215040c5076621355214459004074080c040c00140f0395400012507041c103000e0940525486954054840f9003002840072010340825016042c040018000038182c41e50fa110703801a0041e06040c1c2d91040150303082c0f5003500c01c0a411854140d281c801049205580584415001c520b5000b50304d02c0c5213414100b292400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 969022392 1250 969021142 969021181
    0x40c09030605040f08180f0306010501090608070203090d1a0f09030d0c031e09172b090b271b01030e0304080111090a08150726040f020a080601120803 66
    0x48400240c42c480785613641b9410003440c00d044070301c0d0311180002d00515031142028460b007800700b09121406d028150280e2209035100d07655104807800c045492001803007013070400c2c40c10789545642c80d1403080100c01f80e0540d070742c1c001c52810300c00c00541004c5c081c45d642c84c412201c00040d110740d125481d17400148282c020064941a0460301d86c1c0000e180340220000300300c3c1c14001c03255400e11648590a00102c64282c0b01c03054072541d007991502c1910002400e480d01601c0d66401c003d580c40c0c56040c006240f0741c01050182c54109805c2e0004002c40c548100003d591750680f42455010020b15400801c4180d80c180c4040e0003884d02150610030408103030300d51300982c0c100f04240d5003480f0740c995075001110087c003100300e03086030300d203c15698503005180c40b20100012403404038000300000e007813a030003890380c000f0203644044e88603103041180c0c51440d10214107440403070329800d1885006065250404608000c0c01c5e10344003030a15945816642e07001c004824100921240c008400980c04001031502034160303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 969023642 1250 969022392 969022403
    0x1a1c0203070c060501090f0c020d08063721021f03060f03060b030c0108060d0f0507180605030c010e100c05153d05060714030f18040c09030605040f 65
    0x55846c0c048201c042c045c030603081c52810b03180c40051070b4160301c0010507400050203600c40f211292a0309090091070a822582c550700400c000e540c3d080121b00100c402d402801c02028000c6100341004080076094005424005150a8040ea10809070303455640d5100074030781d0702241c444410305000c1e060b8090111035010400000810302d001041c001d00c4c0e00710b21404501103007506c84d40c0c00800d0056a1241c0f00b03a8460341c011000690f00800074100300e101e10041e5018a0485144a556080552081440502036410741ea01e41e00c007003141d410104404442403409080c082c3d80640d50303c011070f40480c5852426000c2003101d54890307003403103000c2c0096414101702c00700700c0c401d078a4100961104018410a00100036602076100401b8008807601d9407640d03014a00c3c1001c6140c503000801000b9001000107072440100c50411881007a0100000c014406a2468164803140f98960510f10100441d0722280034609044c44030302c41070340c02907079041030301d52090300050580c0b56400c0001c008149403030300810 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 969024892 1250 969023642 969023651
    0xc07030204090f06050105180406090f150603020f090c03160c0b0c0301050f19170114011e0e010503060403032a05030105040605180c03131b1a1c0203070c06 69
    0x2d1103180703c0e2a10919018510920050340e0310820310000000158001e90021a40808100000c107142c1024510500550030b0040c03000355912002c010300800030401202907a030343e004200314100103042d0b0840b401d0898840035185402091344a0900c0014002100c0c0c2d2140002c00e958240503960208005400c405250800d16041d07080d6406540207010b442d104051403e400d2400c0c2ca001450101e0294550500400071484c10b141142c034101702d8403450006549503004161110403c01106008042d140e117480c103088000011540c1000c00c3d034114140d030a19540052025450019503075801940c5442c0000e111680c440703007407d0301d41406c000c0c502c0c0709907441c2080e650b90782c0c0400034506032541201d040140035600c100b0410a1848d00d40d05601419401000840d140201e13006154002c02d03d001c2104400881d44d5034503410302c840307845606c1d0f80b0000d00051213800048030110712404100718103d4a070006d01d00c40c0c7c4c000c00c0c8122404111650300000020040c612810700c090480d50700420601 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 969026142 1250 969024892 969024911
    0x15180403020105240d120e04050c03070e030d08070c060e06161407110d08120f040c14010203091216082104030206070b04032c09010509010503030a03020c07030204 72
    0x24082d010070f035090182002c03c0059a2080602c8104400765950000c005404001c059546d910b04150310044400510210500c10151a21107000ea0792290700e017019203699030700d090840a44042841c0f070b8a980242d100b1524204d60f0394000004d03580000117414601e844c6449482c0400c080d004010305159180540d40c02c0c81852802c1861820080203aa12010324074460880c1d2000180074800300a41021a01c00b8650380b2402d040c0300002c00303180280c2c0b009180c02d641348140300d4041019074550448043c0c4108104c00d01884800010141403045405441c0d41c000000003075603800707000f044510440103e58201c41e4104100400d050441e43d03040040c40c05583c884009807540d4011451a00c01d4040c2030045241d003014800b00c0701680d03070040c4594141030f90b9455a04c0100f40041040703061106500120132440c0d42c0c01d00340c00403800f8612040e40842c5500051005a100680c4914098114000140070f2365601100342d54000040d403a0050311020300c0350b0300504d0030782190b00c0650000d1900000c0f1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 969027392 1250 969026142 969026147
    0x8041b0315021806070b07141c0209180f011403012d09170405040501090b0904080a03090f0b04120201050103020906041503020a06170c03040213020715140910021215180403 76
    0x90b4410307030052321140f03c103098400c4801054401e4900005010a9035410705040382c0c1554060200000d0242144800254140050356103100680c0d210008018440040004a28013010301c201403170180d000b8080401c5509010452054100e20100d645050701854040070f405036210105440d003040078a02d401d40b5010b0042a039511500500340120704100c000b08806da668000d0810511000d048164203a032507480350f0000390480900c80040548505040c0b000c1200c6000324400316009980729411410309260030309844143c41013130400d69050a00410150b650810007940c401425600840e4901c0700d4420500b10040ca904001e6100f060100b0104015a000c0401040b450308901090025114100b6010045c0800c507002580041d0500310b1182105268021b03100c983d10036214500424040911038007521a4110345406043c000001c01c140d003039007000b800100c5141000c04500d00780320386040701c405c104020104890755416031703101541500c84e80c02c2c000801801d07000006840c141480c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 969028642 1250 969027392 969027413
    0x1140d0b040b3408340f08090a170f040e0a0509120706020f041809032a0f020a2105060c1c0c0e04020a08041b031502180607 55
    0x810741803111201842c14900d010310f51180c400d41a20088124418401c2021103103a40c00a080703868a605801240c0070540403407588081440d406a1604407036000d49800034004452041c00c0020028401c007402a40e034070200d41c1c112040c6e00a40050b80d81000419105070b03920410351088001040042c3c0014420050308445000b1440010140710316120080c0e469510314803611000988242085648009012980200114101d0003155424150b81d80d1030b0210304004550504000b81c2c903140c100c4209030740811070030740c504e0341f10100c04640d0f44440600311f201851000010502c002240d4520155561003288500a100c064080341e00e0f29216980300070400c5640714200d44a01c2514003049100a06900b0b803001102c1c44400d13810040d1850b8030b1200039008844005080c44010291010607490700c4c001065400c0b2142c4034080c2c181464030b840c0e5401d4442d030300490b0bc0e200b45440705200207100120700b051101e48090300075032900702040c130300405440c1d503101a940c000340c005014401c000c0303598807 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 969029892 1250 969028642 969028651
    0x417010f050901020903060f060d1703060a06080903070f1104110712050a0e13091e030e1005070f030210050a05070e04090503220305030d02190203040303050301140d0b040b 76
    0x1001e0090b40c5540076aa420b0740650849540d06404c40320016514420030010164449002003c01e01812415228034420728038140762400012000801c02a613804e000c0c100c04000d10840c60a000c00f803404d00343d450f0b141c2c02401e41c002c040385e030410000003d2108108151072803d070b00500c03c1002010030011850075500c52001218040d80107442d10038610300071002d40310303583c50541f6052101c0ca050702c108518821105c04ca005515500d05000c1c010a4440903600c02c08018010001c058450710308024104c03462010505c1d00c5401e250054422543d8008141c2d40000d90002d07422100c00e6041c40c00f40d050140011264855038682810008400700b1038001c0760040409803910344100e1041814802030b43c60b06c000107400c80c0c0c0108913030755203860024500000741d4030001c1e003208003035141c2d980d039819680144010581d06401040c02c0401c0d8050401c81007000101d8001585000e01d1658080c0103400144183c1403880d46190a050513a00d4805081c105d00e90300c030f500030110b4503042c03404109100301503a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 969031142 1250 969029892 969029921
    0x60c0f07080f061504020705100c030506030c0a080a030c08120405070918032a1406070f021f02030612101a040e07210b040507030b1311040b0402041701 67
    0x11545480c0c0c040707000c0b8044c0030485504000f990b641c40a00c00a0340c0800e0040324107104e00c0c0380c5034250030414840d40c0c4141c1c0040d035021801d810300718209850020109111842801404410009000c000030074003549941800c01e45031065190070140300500802a07000c10113940c0d1420002080b0002c1080e10a4a200351002c201071000205001007c0303202203401070115014088808017100400150080070210b0305603014001c0040d0b0305d001c0c00c05e54046240c140c3c0d82c846401d100c2c00a4104641390508403942c03000b0580c02400703010380c04651929815000c03200c3d80c00404100103448011100007542d41c444211640300404100d03000041c1030040010030300300b180d03202c0301180d46841e00519900e0b40b00980100303151424044880f8503408590740c0d50301c00c90f100c8140300c1c00003810f030005503200360b01031000f4000582c5181000300c0a400001e0013001c148032842c00490010b910520802d40456050703500050740d41e0540d010134002d224613000703507031694590280c1c0780d00303284150400e06074046101c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 969032392 1250 969031142 969031153
    0x60216021e0609041d0d1116151d03010c05070210110a0f1b0305240709060e0316030b10090b010926030d0605150f0403202d030601050102060c09060c0f0708 69
    0x100000301000c101d070b00a0710700c3c0a048560b41043d0500c2058480c815610744581c14ad61540000002400c44001800107004500007180090941c0f80c803045181c0d49220030301b0080080080e40e80070360344988011000529441c440d44004050101e00c0340404c042e00810024607002d580c80c1d0a010341e0b01c2000140319050400006641a80c1d8600460141d0080085480311800709040c040292820040052081e4040c0f240c0f0741181c4103001111503001c000d40c0210400c86545c1494041603550303e840d134011442d0b0b035040c090841d009036441b850110480303401700302a1400310300c548032415114105004030701c4103100c08600740645005542c4004100d840440700395150031442e5540c0000740c0102016401c5280c001d01081002c20203c45c0390a41201022007110f282007014000901c4218414000d0040810303802c85e0011304851401c01d000381200120700824180d031421300001d540e100010724000d001c18004c60310002e50b0720740b5000d5945031500102030f02c550901001599548054601c10f409592188 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 969033642 1250 969032392 969032413
    0x170d0f0911091803041703220f090204030309050f040905060a0b0a0501080c1206010c0503040b040f06030b0306060427050c01140c0c040c0c060216021e0609041d0d11 73
    0x60307003000b4500b851142c0c050f41c100f034a00600100498110750041289001c10480035000141230a99001c8460000c0111810740d810f080902da08041359412080600d4410002400400d401400c0075003158802c82e00300e48c1014002010401614103d18024010700c91a000d100300e41c48650400c03107450f41d0030b0302c60395003a6684800444101e082910403041030a41000060a050030786050141d0049045c100300d8890b1020355146c03491039010398032a440a000100d002e00104001c0c1c6103030401480b6518041c0481406500003a4030f070b101c06010030340710365136603400c1241d05400d503c04041c4e9244142d00801caa21302c0f1b818006c1d00d1f05201c210540c0004d00d09001d01c818000b041058510864014000782030710010ba000340b000900885005005110354a0302c844002401030008045040d549086101c030345805206100e42846802c05402a407480b409150359140c880906a803c0010202c9010a10981c099503041281d894160050114041e1003661300301c06030091141c081e04c01c5488200c41c2d00e4a0b6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 969034892 1250 969033642 969033661
    0xa090503151b090d0f03111c03110a05160c1716090e07030303050705071709100302040605070803061302070327060903080904110a09051c170d0f091109 67
    0x8401165a02031581408480407612402480038402d2190030310214807d10382c6c200e98074040b541d000c03e01d80803255400781a44c0310303858000e10081070b400f444074900380b807400304019200380104020050080441c01b90300781400b1245508100510f10f814a241580b490f4040090f100c1020302d000003e0940106d1001520300c40034481c01c1790313541d005006800000e08590b0110301500c4042c2018003003090901500010500c081600110381d004000405d40c0c809800e4180008801400002c03003d02d4070500081102603000802c03165003a91100c0400c0d074a41e01c090010380c0d6004039000148901c0c0c40030484c0c50825800582c80e40f2204070744100b07180d20341186030883e40110740501501002070f080c20010000240e54802801c14008007d0010819004214008085400008041d000031b0504201008581000d19900e86400c5039144c0c170502c01480ea4460300c40070403000b0000100340d50300040c0d050918007180d00011296403810300922218503541040c41198965100b0745202d0042c82020807140309 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 969036142 1250 969034892 969034897
    0x20703170c34080a0504210b060a080717071d1e100e070309060e011e11030c16080403050a06050105091014031005041b170a080a090503151b 62
    0x2080320810448815466543c4191030300402105014001c003484042244139040c9540711802c00b000505010b804504c1c2000d8030700ba01c014002038054010050184080d060204d4401c1c20f9030a030300040c2c0170100d4040d00c04c030307d4051545e2000c030006031709607000c00100c0030142340b19000e0084074904041c41ca520203456680703e14240c0f500c00d00c001c2001e034100038110f24014510ba1025181c1000180406a0b44513074081c1c521001d00300380c4a0750f44030003009406400c035000308144c0b143c42400300041d1101c2c0441c491380344405401956500004205181d00030642c0300240380c00f0794000c509030781b80c2e40d480c0340c07250380d440c42c240044a01c01c3c105400498582840004c0c103108040d80400c2c2c1c161039150810607120031400384040e0340c040c01401062140c41c400740c0038080c0154030900508181120010382c040c107204054100d070104104a01200d1b105a40002d0742c903456507004248642d680031001403d95800d400c070b078046901401002c070355a55265450301d89a12922400c001d0341d04072141b03c5101d40c00c51 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 969037392 1250 969036142 969036217
    0x408010203090f070602031606020904180c1a09040b0d020312040f061e081023030c0402040609030b07120e0303150406050105121e010b0733020703170c 67
    0x103038418400951402c81e014035000088d805038400510700901400450241d5034074815450f07003291001e00040c100310303141c545a03004241d00802c00840701000d6180800d07500c113900546200e41e0f1214070741c00c5141e980710712003a0300942c01011151403102c10305140036a03810501c10034420700b00480c00010001d0140c8500458110040320300410f119241700107440401000c0c081c500d0031065232801250861581180300a0074400d41401000c052403002014645290344e54203501039801030100304030684d0461071a070140e85e40613807a52210794540e40112043e901e444a07042d64682000941810303208003000035806000c0c2c07925091449000c0f80b00b44419129140715060002d001048954041d07240e09501c9034000300d00c4c2240480c01011450440749420303082c0c120040c4802c000030381d001080a2640005d6906050f5103039680ba214031060311304088024004640e1901d9000241e10080600c2411000c02000603c05001c00a0402e0070822031903401080e81e501442e06040c082c1e40a40c0044600794595 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 969038642 1250 969037392 969037397
    0x70c0506070807050f0c0f010c12061d07051e0a111c051602120f0309011e020303070c020f090106111216020105090a090204031104110705120307020f030408010203090f0706 76
    0x10140040e400c2100380c1e01c1b00d50000f07814081d00c0c1e6441f2102c0360030300031000014510343d103507590242a208800103e460329401042c1100c5001c115842040111240c1035100019041a40c0c9030070f441c1c0581d490b00c411001000383d00a000060b45402e181d0850030907803001c00302c0c004540007681c02c40c0541a002d8980c015240215a05110201409010718041c8111a102415071b05101c4003818a652810308040c0c141c0b0b88170307000031602203d1540c1c040c11031008080300e030329038042a00741003401a40380d01c0090034100410440c90405400c2d92948814881c01c40c0c0017600314405503035641d0300241411103c2c0107480d4180158040000c801c003a080c1920649010040e8442d00101c032580199402e520240e40d41c1e400c01c2c511100081c0c800d117948007810045000c0d910020252403218100021a41d01c120007034460070003402036602180001038102a060080002c2c0340c0d807901c600c038040c0d03c0d1012139007440045120000d00400c4a0350b040d0084c5d8081e5a401046500610190400c1600d031506400b8aa00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 969039892 1250 969038642 969038647
    0xd0302032a0a0314041109061504030b061903110f04021c0603030f0c0b0f100e0c0c0111040315110d0c0c11040c0807051305310b01091e08010203070c050607080705 72
    0x6c040c9001c16110340c11400082c4140302007071a403030710130100f50011342c0141c1d00d0f040b40e44200034860404540c0c050304040e0304800700405c1070841e61050307941d01220780c0050180f004600d1000603900d990341240c062928000529006a22621229014101e0350004800003014400e1554010b0701525031904115440030315a17910343e4038018a4184e20600034848042c841e40d2050015542480b6401c03239000e0b008042110b6640c1c141600385d02e007035035103441c0703a5040030604210800200d240524029a9030801542c0480c12165100503c18180100e90518070385c21f244c407259002007600030a41120b402c2c49041e11a41c000400b404010031103030340d03038000c40c080b40c0c41d400000d28092140c0000e000c5152a40460600c250301e90001c10304c0400c400c070f811004035404140c2d017400c4d02a22808828a41d071601e205100d030314500c1000070090f0380248039000e50100040403040b00350b202010310324041c20005000715200d21317150400911100b5041010f0b91540502808221000d2160030030702c1c4681107540742d080c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 969041142 1250 969039892 969039923
    0x606091401140d0c02070f0f06120207050717160b0406020303130311060c0921070501050a0c0b2a0301030506130221160e01080d0302032a0a031404 65
    0x1140070102c903008800e841c50801030341841401900c510200c500d000e0380100f03159401e124138180f00c0c080580105107403c01e586070400c88994003a11040315028102409a1581c4041c80c003240741c8079494000007030800351620b4140740c07120001078000c00c580c118036003950a43c2d0b45050303101141c4111f000c1c5c0030041e04204001038840c640001c68103144d5200340b620f000800c510401c0c0500b0720005984a90522000191813211890301081c0ca10341601d21200300c3d4400c1141034040c0f5540c84080c031900f414404c01140642580e4003e03c10300c0305880d0000069201c2d0314104c492010700b000c2e10b04420703105014003544944d92000b00c805980c1600e901400800c016103403880ba04003000c002404c00c070703400907140d4040b03907000d0708424075511001c098600800c18031100c4140310001e24401e400c550080c0c1040d0340108008400010701d213004044600340144d4940716003800c0d61408d40daa95880b1405094400d1792401144417000034003c040643d40d0400900c8108140420300c081c003a2030180900d206040d511 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 969042392 1250 969041142 969041147
    0x1090b130e0709030c091406101e11061f0e01080604030e1302070302060a18030e06032203050a2a0605061c0b011e05061206190801020c010606091401 66
    0x80e0b000141400c0908010b50781ea9151402c20b0f5840e08000c0301c45460b50300d24110109501c4020741c1001003114100d99881d0000d6009100c00b80840003d03c4c518400c409101103a8011508240c0c2d900700d05059405610b040700d4954102c403800756000c83c0b4454005400a01c000400c19024140d4416038050400e944980c1c90441d24800c0c96030707640f035016103d00b81034a060b568600c020100c03a84260080c107464505000c55100b21021040d584c14801003440c403600c0002d51010116440010849141e80c480d200c1407023101050010a107241440309418024005060300f0201400c42c00500b0394807400f01881240180c0314460040540e96000600c01442400241072900a2580100041e020062aa000c2d0b80388000103040b0741030564100e0704000060210300c41c68141c1c130a280e00d038000d00d1080345103004041030881c416004202e00680300d28001c115103569090398442c0031204148040c14203074441c1d080034001d42c0030401c80340440d0700e0702400195681c02810210700b01e950341c0540440c0090f141005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 969043642 1250 969042392 969042419
    0x6010305031e040506040608070e0306060f0105030405010204122f060405010e0103090204061e0f05010203120403090b03190c030501031104020904020d051305210313030c020d060b01090b13 83
    0x50150307402c002d00c00850300e901c130100900018203540e561941c4034207140d10003134500030301c6141960094203c041001300b01e0f10781d00400e050032a420b00c0c080f5643d5645003403142c024020f503046101000f8414480c102801070f0a040e01c910b0a25402c007843d80722005011400015107440c018580050303003484100070560082c00c0c04c1c008400c0604000c58401e805600060444140d600154403820245180c228a01e0030010003501a03c2000c40c140022824403001030761743c2c0904c101e0007000302240000201014810312048005050b100c40c0c3c2a00d034100f604030314004459415242034a0b1340350000c003800041c030a01405040f29041002d40760509904010300010b58083c42003942c10903000c001048170310f0031034414644100340c4101034402e01030742850050b04214000e94241c40c504500310380300e4a51162002101c1d000100581d9030700100903a807806498a140107440650301440d803162080500205400801802009989a058050311026051401c0c080c0318450035031641030034030030300000501503007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 969044892 1250 969043642 969043687
    0x3120c02060630030406090f03050304031712010603050f06031c202505010503040803061c05030a02010b1903050303150103110408010b0f010504120f14032a0601030503 74
    0x3520700301c2c100b86884005842081500700c1d2090b4000541080382e0b40c1d07c00040c901403c01c3d2241c802d221881d6403100b81d40c1c0e004c0c03404083c2c84d44160174000c01160000b8400c90328240d00c00c500c040500c0d0307900c150103002884100d4100c001c1b400580e001603c0340c41d0100d1038583c48904c10710301c0800d103030351060100c0f80344200c03200f000c00404803c552100a607004001c04a41180000301814800c6584000c29041c42ea460780003e05201c414010f100000c0c90305c00950f54443c2d010f558801c8207070034449042140c81111407001d807850100190300422140d06412070b004440040d82d421003200c2c211414503d4010f850300c400f070503075003007400401c1c00070914821078420908145400b01d0801010034450b0000e900542c000303d80caa641e80b84109103400c001841081c244024201a400c140c54101c0040914003010f20042a24888020800422224402401c4400c8401c002c0702d8031003031180000c4104601020500c60003801070000801c540381c0005003a8162903201c0301641c02e1008451032005038800c03040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 969046142 1250 969044892 969044929
    0xb0d05060a12050f0f0f070603020c1f05090c120c0108041722120c060e13061806080115060f09082b1e0c15050a050403120c020606 58
    0xc00002c0e10341a0810308040380c5000c1c1d405005000070082c05503141110303000190b08203402910300341c040c007200420782608035482e5040c0540d507110000c580c18140b80901c40c0e2304030345110840d81c54010580342c2c0e001911940c01982164a003c040d5010072021001180614686622610301d0100552080403282d402c41e2056501c9070302109402001703c1d442d048100c2a6002d101100700441c4100c510070107240003071011031500c090381c002d01d8881400e1841540036003024415483d0000085031101c84000c4040301190901700711590f00d0341e120380c4201c0e42c0700c500803610505000c000300300c0400c10300c5240f0b82c0c1910a0304041510703280003019034400070000c800b402030050b1240001031651061100ca210a0380e003205c0310504d8104048051402346071000c80c0c008028851071214010b41030b002e8407507191030f042c1c2045080f40d149880c0800c185c40d0f10311060b80074542440c052150380010b0750002401540700384ca4094035a100401494111064010314000503401800840e0781030400d1480d12045010a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 969047392 1250 969046142 969046159
    0x6010b09040212071107061e030911030a050d020c031b0d0f06110d060b071211070b0f03010603110c0c04050402060c1e060604021810030e16031a010b0d0506 69
    0x5458000c030b8070608a03101404151a00c4045c86040c200b4090280504010b0501104003079015044502008001c0b0f02d00381031641d958408030600191a1094180400040844040c140e80e45071450303c6490b0121900c2c0907203d808040581841c012403410102c100300502c0114440080080107502c3c0d40001d4140e800d040251112400304010f809220742104400b840c042c0e45080341d0711b1400c2114005d0344281d035000d07000e002c080005140c02120006030071152402543c2085805c0100741002140e1740100040000050b280c0c00001e51040614102c41035600e0400022014051030445031003800440d80d490340000401c02181c0c509640010741150000d0a0700d42009180f800d002e14010030b41410307409403800710165075110081000b20035070100d01628154101010019030480078001800b046200307540c2c400f00d202d0902e20951202500030801070440300c1003014a215207015030b84502080d07440034881e20b040061488411640c0c1e048580114600d0b2030b01404281502c002d1070040c003800c0c1c0c000c000707 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 969048642 1250 969047392 969047407
    0xd0c05090a0b0702100302070b04031227050d14040e0c0d1d0601080f0d031808070b01140d080f03061f05091201180b190614010e030f06010b090402 65
    0xc206407800030385411111150344039094010400c1c88003e071600417003014010026040020304861b4400e4002d40d160904c2081504407894034400382400510b261102c5031009592100c41400c180c00498690107030040d1880400e916808a402e02d000301c5c208540110200003c00c0030fa081580780503400400351101d00d007007800042121007500c0d000c080070401c29000d070500261000060045030f00602c0300307100401061000c900c501f525004901120818103684024414000e80c0c0f8003088045a907002030b2580c0c0e1549c0c1481d0054855000703000c0e075803051804080201c010b0a12181c4050101e401c0000d403400c2118800d40031240780e04c02403816030080043c0c1c0c0c2441c103503600c0556682d600c04040d11450b4507500741d40300b0f21505070010a0541040d03810840d0b1144409281041000c0654010240b20080d548080b01a1a040000c01c601440070f803401e0000920281e40140daa0800b450036139843d00341a00600426a441c5032045104155800000c0104901811140240b0366494003400c05400d0080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 969049892 1250 969048642 969048649
    0x1f020a11071406371101140c0703050405100921020a090b0301090203070f060216050609041d07031109090a12030f0b04061409091c030b0a05030d12200d0c0509 70
    0x13002c1040b06032105014020200d60081851204c402c1090000c010303a40b02c1d0504014110310141c40c1c00d106280014001c020b0610460844015000103890440c0070b400c1e9034001091020f0034401d1640c2140200500208100000100c0d42001c0c0c00034034440c0d1180c1407410000080c140c03454425030640d44c0f106d030381c001a1420712640c4020003850180744000c0d450200701030b080050f8a4000c5031401c1d04244103000340e6407100250f0308554815603001840014941055041c0d01208418071003d1003060000000c00c00240c0030610010307000d4a1005030307512003104041c3e0301d00104c080200800300b07000c440c00c4550701c25448000c0e410303a0184049882070101c0c010408513080354018001400464103030300303c18281030003e1a0400c07c0c203001011828070502d05c0781440074044030100d04054481c5843c0d08503586140c03440c0041c0200030182c0d01c0c035890001025084141a0303d0007465a410500300c0c03070756490f0841000f21580030340e0079140d107000102c5590348024200c401c880001d000301030200c50750686 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 969051142 1250 969049892 969049957
    0x606100905030f01050a0b2715060c07091404050d080403090f030503031f0b07081e040b0a1101020a21020c01050f070207090c050a0309051f020a11071406 68
    0x3c4429000041506055a0300c0d0b040d00c1d9020009801440d07000d051281680701110340042075090007586281035114280412600100e07214010380c0001d022840b0241d016010411000f01c40120341e080015040c00b0340d0391628820102d501518a0704450855101c1d60b005241e042d0b8058440d00d4144102919400b0f884485500d6802c11f950b1980007101300009118005d8201001214810807041c08625212a5500034402d5403001444640045a42c03070080342058095200d1350190313001c45403500d845860350413142c3c00c8041e0f0038000400c44100780000301c13418400c50300301c6d00e240c0c3d80340060300c888250f5540f20442201080703c803240d0f0811401324000b80a01c5564080d803843c401c054440c0c185840c00a14000640d00b01c4800030349020141c4003c19002001c40d03100d5800c9090118040d0b40c0b505080342413a40d20642c0940302e03100c0101600a545055006000031945510350003908124041429640e40380c900030790007803050400488580b45080c0010700444500d406201200030f1003c00e41c0315a12 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 969052392 1250 969051142 969051163
    0x18110a020109060501050901081e1c1d010c08161104020c0f1006080601060e0d0f060b12010501290c01140109050c122701050c03010e07020f060610090503 68
    0x5035034420b9800104252801a5401410111842d940c6541441c600989420f40388001c4500b9058a01200c10813007030034400c0c0e50f0a02e0981210240c800e0385040e028001e1107100c88000210010030303000c01a19800b0b02c6000000c0ca80110a0a041840300e1481c2c5140312444841500c2c1104441c41c0d082803170740c4a000400b14201900050114820102152407610902c2071001c15824202031040c003002600049150465805240c446103402e440404a40410708041d0080c2c4151020284041849034642040c1d01000702075900341a01248001e000e07007203c000303019000c921092034400c20398450410900000c2d410f001b030911407802c0000e000740b03401c651003000d854810010000042062403107a100e8030364042c2c0b842c581c0c3ca10b031141c4a005450008401080c09803a80700c100c5020412819000940c5000c640f880c000300858104a406401980c02c240700b4680203540e44000212880e00c085040710f03214051400808868842200300843c501703080b0b0783c8004004603080c0018081d9410001381109 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 969053642 1250 969052392 969052397
    0x140a02150a0b0402070c09060602030f03060d0305091f0905010e09010b1809091b010c11151e1309020a02030f0903010209090a090c05120703020111030c0a081b0a0b0118110a 76
    0x21f1a0083c150180c0c0d00782ea00503803d54200f84000c2403400074581c2140c0e800501150b690005000b145000d42e0f0740e010740382ca2240c00000d0007005145a611150780d00b60880c1f07094980a075280d40d01c00c01100c142d10501e007900d42000d50702d001084030003808070240200031100c0740083c105441d200301296440c04102c0305c844155201c05800160400c10000c0c030701246c00c082c64410f04407103040d11a90480d02c074210149009500d40107178041c94514441c05d0380d01140c42400301c4004c10100340310400007508002d940c00c02e200000c0c2800901c078215071007260304010f502e4002d5804c000c1c801d000c82041d500484031898165400b000102c0e016a103000303106203c0c01c0c101c1400564499203040070b403120343d041e8003c240207074010b1140c600401800203504003120b81c24601450702d2680c610b6844d055024007544000c4a00c5254241e40420440030f015001ea695a0858403020500340122107a80b24407518014019103521401400804041036009071800241040481c2c504a25070f1146075503400300140000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 969054892 1250 969053642 969053663
    0x1003170415090b0f0304022e0207050a0f05090406020d060303080a0f2013080d0c020102060c09060f1b0601290304122f030307140a02150a0b040207 65
    0x20900310a285814040800d02e40021020b0400240b428584074010a03c40b44c00400b10019045540b0034128420020030144170304500b0110310f038007049a0040c0d45400001d070240e54008115410020030390400c03500c0403003031102c1c2c0341e180409111407400041c1040e030301160204490f1412451078010704008501c01d0383d60190b01e1400505140c11104611034145527103092500d14a4090b0042a07000c000c43c01585031181c0c0d42e40001c1c00c508000c0d000d580a0281c9000c1d280d019006540c0280d40489400d000781c00b502c5003542c0355010102d030362046440055000c601440031460781507007a00036100044040c401504485e0a1500c01e034a80f413400d81c01030082c60480e002d4900700c4420303d00e04010058601c00c00d05d056040ca0750351401c0320401452036208000246502850454581c560728240c110050880001d00501b4240ad07512a80100c0300103011807030300a44074004144850848030111040d501821505610200042416502070070340180c040d1103561031801650341c1e200404040e4031a080d0f00e43c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 969056142 1250 969054892 969054899
    0x170c0105010815011d07030b060418020c0114040b010b0306062101030501110703092102120604020306070c11011107090c030911010c0b0c07020a0b031503011b0c0b10031704 76
    0x3d04040301600042440840c0d0050001000c03a00710165420550500700030500252603404542e05d0300481d8071003403115140c00003007007454490f507000780340803103c00c0000d001300707000d801580c0c003c500c0075140140f039500030b0b400420000210401a60b000140100701605c0d290000b0308008400f48070a10031840700c00c0103401002003000034801c40d10810040c99a0508102070f58401400d2902d02c5c2c0b1840b8500c0c080b0b0000300d1507014400001980c0c0d0b0798010451880425540c8059549410448080340203110f00f00100d940070b070050048000040d809000c6004101240300119552001110284618426040c01054050290190780c0d120a5503a500280d0a180b80c28500080c00f03040c0009030500c2010a83c10f40451880c1c001d442d44099a4254076559003110308c0840c2c8a0886a80719100c482c0c008000c1c0076095400000d9070004c050b00310001d101d440c3d880344006144034640700c4910081a070340b10300c1000244246186542c000000e00e852403030340e0758079190140c45040700040080803003000101030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 969057392 1250 969056142 969056173
    0x1804020d0e061f0909020402360d110103090c170c090c0a1b0c0506030124110d032a0507030912030c0201050d021e0301050f1c170c01050108 62
    0x790f40c400c200b4200d0b03e06100d00000403142c011094043ca144060b1520f400314290344858040311031011000c0c1e100c6000b02030041c8030030030107906041003411880145601d80d001d854240a50341209402c007800d0018000208019402868549011200d0b541e40c0800004c5840100f40d640d000151800c028040f0940c4a01c1048a81c100003404034442340e00a011442c02903900240a000994002c256560348030100d0420481d008a15130201c2e6114900000200e02c01855070b03561510314005212038401c02050013400d03240b130040403c250045520800071741c00c4291098009803184902c1c6450201059514141c5c240c50542c00800340d8003045001800604040d44840284010008004007400740116a9402082d000303005001078100840072500405100c600d50468684142c5400b1a0701442c1a03802c0d6650581c00901c545813044007404020039450030070056050310f0315206841c0d481c03580c036503988041c24050f06500f54101d0035802d11441e05201780903ca031601030121040202104c85800804 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 969058642 1250 969057392 969057403
    0x81f170c01030e0a0b10090c0e100e01080402091306020d1d0a03020a060203071209060933020f21040b162115120b010b0301030209010603021804020d0e 67
    0x2228109894460f00180d9064007080c642c007a158001031041090700e4151a85041403507a40160000314905560405001c4c3c01000c240c01007001a00c0d804101c0081410550756a000084010b020407810700000b0010300d04813000307a80c040100010b400d1640820380380c2c90103c0e004000c04030a1247c0e02c11800c0000316030080c0380415036103814020f01d038810150760025164045204018140c540110100d42d00f2402040c01c1d80c40720394403410402102d0b07998140103020741481c00041d01c094048641c0e50000c00f500362180c000303c50251007138100c00103c0318042d100a500024007400359070014040c204800c0a00102182203001509402105003042e04202141c40e40203415498115600680d102c16030b030700560020002144800311244a4002000001c00340502120310707042000382c2c060108058040003d9010324501419165045a8070303800c400c0c07098402030001030341c04180c040040008500c66002420868200807029030003141c0130000c9400d0341c006082c40c54805444001c00481682c08010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 969059892 1250 969058642 969058663
    0x7060510080a0309030b0c12071809050c070311010b04020a0908100212040210111c170105031f27030f0e0105090111120d050f01060e10081f17 63
    0x600030b11503490740d02a100f151144801054040d4600014842c0e101000c02d0b02c0b1035200032040e100d15442e001c00014100300c924040c00d03c01540744000890120424401d00d8442c0c009003500320b00c1d040041e2002d4842d250110301d551200d64030b50250441640b1240040d0031000000c2d10b84009541c100b044280c00d14101c14001000240f040c0010801d100496500f1900140c05440c9400003981c0074000300c0780000144041e020034030590003440b1408100e81582084d80500da5100c501444a003000e807044030000780f094030b038998810038021404102c040004c80e07000f283c407000003413603102d0b5031070b040c40301c40240702c4100010544940100905802c0075924096814902c5d02d00222040040060f026028007610300307040010012482d082c21200300012645002c4640c11079843d11030f0608403030044e0104079611620618000c1c0002100d60040480c802c400000070440382e49102015412595200300030030a854014070713940846c200e103140300c60180141603421000c110f00c00e09a051036241c200c140c103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 969061142 1250 969059892 969059909
    0x6090a18021b0105070f1d0907022503020609040e1504030201061401081306050a0216150b0907051c09020d1406130b010b0d0e030415080106210f060b07060510 70
    0x1001040341c0c6c07040d00c001320144141098106801c3d011707951074207140850901900101c0c0704050014568000580101c5524409003c007030f440741e0b1104442651080c0d100094221805009066661425810000d42e8400300b0303040b260480c444042c0541e087c1c00a031420b60150759140401d01081c0464408108072410a080c06071103401c01c0c0c000b106505840f0071002d44107075a83c1c004a040250740d6012511400c07816004207101c03000c90f08241030348a00c507002d010002d0740b80001504003410807a42c4907224000e60388865091a80318a1020f40f103000302008038403260703034400c00e40005039035910303d0000b82401100002000c0c20341e1024640b0b42030001c2c061000c150202d1385035070001941c15034400d0654a01c040f01ca40c5034262401d816001e040c0b00040c03282140400b04001c901d00001c0c102c1104100340554403442580da850302c0079600051042d210144d4055070401000d501109a0003000005184400c0080c925a44030044d141d69006036900f01d54168403081800160351321703180040d01030031801 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 969062392 1250 969061142 969061151
    0xe0106031128060801330e0102030c010906051609050612060a030c080f060f0603030f21010e04061a090f040f0c081f11030f100f0f0503191106090a18021b01 69
    0x46c4c02078243e240f2004064081090f00704c007aa038140d20900642350740b41d00e050000c1c0000d013401c0c0f07414409000d040b10700c01e440c0305004541c0c00f11248254002c5048440c0038182c03e141809501e00d1224611006010710f03002020000000001640d1000d0340004180700e40c0a01405504502c2d06810728001070322400204440c8414408299404422501c024450141e160350701e0055009240090b10b01d0400f03500c46500b5200002040b04050390014452442408100b0000c081524000c228603a4070b81003d2700245140d00281c0134030703138010200347c00c2801412142c090a01d5540d03aa408800181c0080403a600302c07a1ba401101c50380d14046020840041c503060043c10030100c255211808000c143c00803201208000c03070007054503840c1c810080c005001e503100d42c09440d0a082c411008035407050500078440d0305001d0000c1040c0c519058916544061780c0781072503118030b00300443c0343c1003503001a40c4640308450004410002c6040003500c91600c030009a211030400042c500404007048803180141d051 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 969063642 1250 969062392 969062459
    0x8010608040c0b0403151404240f0515091e0a020c03090d0503040f24080c0f07110f090f0403030c020c0904140d0f05030c0f04030818040e0106031128060801 69
    0x1041ca0202d101c015a0740c41c0600021204414002c1c00311440308078946850001807215040007242081030145c0161033700d020544600a0b202c22040392040c4548000c4a4400410100101070b0000e003000301e42d680480303050400c0d1200185100c1c0281004a07616840042d041080040c4042c407107004001c03480f030304c032109640400c600704440c100501600401404000245890289109a8240344c0c894004651112078500d441d806100b14140d00358030a0050380300c0c9074800d14201c0312036442030002c5204c5003042e84139690b09801806000034902d096019841c000c0c6040d455a41400d8451400b515011140f03940c4134240d01c0c00e0600c070004075010000c1c03243c01d030b0360300d550040103d0360026a018a5141c0c1c607000e8501c4903100780120742004004940001d00e0005203212462084003511084808000034840d080482e401c0320301c00c0c40010325400615152400300e1514503404442c00d945242031090790184004200010600d580001c400f060881b401071000d9503c0c41c3c50758100202d813880d041c050000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 969064748 1106 969063642 969063653
    0x302031228150b0f07060e01110d20030c1e040302090705030601021020070c08070b120601031808210a0911040c08010608040c0b0403151404 62
    0x112040118944400c1012124510a00000103141450f10b654146c0607007011207548409550303c0c0000402e2100c55002071140444c003520008001002c00080f4204854100208500d0641401000000d0710118110359144e500069500d014180342d00f40040c0510032030b00001e41020505050001a0781c20002a40c01034109800741c8480c80c18014080040f680540c5228601c03000f0350303542c0800340649500030031270f190081b01003030051500d076054945004050b40c800d105010300040d030308810117040011150040800d207014810140781403811032034a03008903805000745000003218924158814001c0440441d41c1c010540e4900d0f104403200010100403500b9689480302514045c064a82841450f80f92119900e680300b80382d08000d41110341100007801100c580c58219000701c0c400e0000000f030001107124556013580b1005520302e100645800c1d111100e5200e4810080c00001074 = true := by decide +kernel

theorem cover : BRFrame.Cov 968884892 969064748 := by
  have h0 := BRFrame.cov_init 968884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 968884892 ≤ n) (h2 : n < 969064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
