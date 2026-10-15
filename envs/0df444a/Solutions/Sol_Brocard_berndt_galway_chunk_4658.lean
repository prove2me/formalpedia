-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4658
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:19:18.340768+00:00
-- url     : https://prove2.me/submissions/5b306ef3-6b25-43ba-b037-44b24ff8c034

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 837589928 ≤ n < 837769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 837591178 1250 837589928 837589931
    0x403020d1a010b031b04080d1101241e0308030c07020a03020d06020c0f030f18210d020c030c06030601030b1306080106171b1315060c02090a06080d0f03 67
    0x1901088041c000c00e40c003d1100c64030b016a00d01e00445c8142000096507442500031a05020500800e0340c00304524281110740c2c46d00f88901070703102c003106001d0001082c00c041c1842c840800c014094284940b00e40646488c080d88030306006c1c220404840340e000e00d201c050000c10044c03020801c0603250500400d0070a00041c6805c02958503a00003e04905840004403902580000c1c601ca031540241300100071110640c0c055805e01c080c10000c00d205108002e5000b00100545030010b81c1035030b40786103a00c2200c5200085d0003110541c00c074815660005035a00c84058440d8915995113481d0001e103464442002505141c1192100390040d0041c0c02403100b8aa4440580800070709207403840c1c45007000400280001040e15881c02c0418070408542e90104c2100e40c00c528810028100c8076030a20002c84d41c2582d0200180d651011040000c01d08950800000142003100152056100c03155403000c5000710348090441c1c07aa2010a011101c1c04d104280d460307002580301e064034900444000c01010307040e080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 837592428 1250 837591178 837591203
    0x5010902150909150f01050a0207081e100207031b050109021305070306050108040b0117160f030201081e07030b1507060509150705190e030d0309260403020d 69
    0x40658100d0003140300c07600c0010036090010b107000420580c01141ca816080c0000444501065001e1442400715041c8200020b4914446108014400013018000c00303a41d50f1451034070306445a03c103404402c031001d1003031184119040c0117a100700c480f2a949a26600b60148007505107100700d11640c0c2c4103a600c2d542c0d880c80038016031036682c4803007000303003402200065910f0011070140c12901d06401480c10840c0d103100300400603080d10311042c1940c5c82d100315090682c00304442c0c14074210205400420410742e80308000380346401c911189007502c3c800d80b01d1215940e83c21010201c01c4004410f490000c05403e404612998040d40c801c600c040f8002d4076440c0c041c1c00300c0b1314841059101003011500c0da9507400410004510512500b0040d20b003040d202211400c113000010704030701500b10b00d10602208a851447d47e00d0041d60616501c0300050300f500e10791444150064014140400d0135a1040c41080060440030002c5041070303000c01480100504090440e000d000d05c6102030002191103951241 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 837593678 1250 837592428 837592433
    0x40c030e060a2412112107030b060d030c11060d1a1f051b16030302102022090207140c0303040e011205160b0a020f0c010219050109 58
    0xc15106250321940880c540064a2a5550b81c0058071910b0100c5660383e00280502014250b0200c40660401032501420140000150301d1b0301c1d92811503c0a1442c008138810440c40114000040703d000d0b081c040c01c25503548041c802c8407040214010700091940600b8070000388510321443c420303c030140440d402d0000141c0c50104851428030f045c40c00e564681401041d07071038000b075100d4000c61040252103150700105c002030207034002c11040c800c0910013400401e14000c020408000300f0903081f0340f401c0700c4c81c0d0342e401c020f0345800301b0300c1d8110090390420807c251184010003400f5105031240d1425440e000d122001401544050039070b2010807141e5000c0003c0c8004540003611000380076060f81015140c8010440c1c0c0741408445010340290000e1000b00040d42805101c00d046a10744982c50154a811340790803030500034011241c0d400d41480c8000410032140c1c04003d0000c0e24000d07002c40e1803480c200c0700710399500e81c0d0407446036006a0020401c0c6d0031051100144440c80c2d4801c0c000031800d0003459 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 837594928 1250 837593678 837593683
    0x201150906050307080a020a1719210207033207060e0a1d010b09030109120f0e0303040305030a270801200703020c0909190c030606080708030306040c030e 68
    0x2a801032240301d4450905000920b010301c080001004880d0080040c2c0140d5408900c41c03202d030344110810b00041505d180d08604080c8004c01114400410141c014035891808000c07084030030319200c96038484842d442e06420b00009001c815281c002503181d04004529200d41601d4800505d48021701c0a6602000d405980c208901009002c8035104e26640d102c0c14001d2045154069201100f5507000305440c2c18a203d41080450540c1d0030403038000d6540e0a0b9001107070241c581c1d2400201000b090750185104298424801040c503075031940c55034801d00b016810151b90b8000c501000e842c039042000f00040180c0500500f00340203444000700070501d01e1407510344540320a03592110200d6511103050110f848034400e140d140c20b8400340200750030500e49803402540d8200c0107448134040c2d401c0700003203000080100329480c4105a24846d10701c0d0030361940740c1483c2800051004071065405e180c80800d0800740800c00100395445440103500710b544810400c0701500175008100c0915075118980400d000c001d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 837596178 1250 837594928 837594971
    0x280c0803010b0d14150405040201140d0c08150a0510091a04090605150d1d01090807060f14041205040e090c10030b0a0612020c0604030816020109020901050603070201 73
    0x6a0225603121103020444600b03641c600001000b00c484d42a0030446100c0d40c424203940403100035240010b080d80d503480141c40064603113200080d00400400d0789220341000c0e41145260b4503e50780c502c5e07a6a01c6800b0b03007120160307510700d50300d44c8041444414800ca0400416007206000b440c42c1040d4101d42d941004000c0c840030800f4044d550200003420710034001c1a009010080006866400460200c0391030300070075001d81480420515250f100030f100300c08010380400f4802072903000030045c0030356038500002c50b079103c0c0b50111801810145c1c0501d8840c1c0030301c5807542e01e44120680da001b90703440d079450b01854403182d40003d0501c81c040c403020500301c0580020301d00c550b030003000510410354090200702981c05c0300303c0040304040c20614450955110a1020411210f5a00700301080301e4499400f40041d0040c0d814111071446518108000d05600c00c0b00e041c0140a50200d0308000c03107106000300c0c240e50300c050001c4d41249801d4010000c03402d0200045a00c01050b1000143c0300c00707204075407a9410742c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 837597428 1250 837596178 837596189
    0xc0409080703090b040e150103060801020d06031b0522141003020f04050907090207140a030201021b060708181507020309040c0813080702150a0305041205280c080301 73
    0x100400c0342810141c1124000b805884c0001c4078a080070b01d808414200362400a1004000301440c00307011103264003d8001c000504034410003503407605003074107008004164504c000d940011074120040300c1c3c95004407021050343c4010b420b00e40d6154050700440800e01440c106031054a5a480300d0340212440d584103d0301440000d0040d01069284d401040280d10070311080e184138900c0c260034030409040001c2c01e40125160084003607228030248c20306202d40c09402c01205050301508110320700f0036506500078a034040c0720901500007122005001d07503480d81c0850302400414803000104210080f044072003280d03020901704079110070514200c101307100c8800780ca000303026074070225012a00b4a0a40240c60140388d4501e0140214031301500340d07081285e41260003038800d100010784003055446140710400d03840b601c2d147d0283e45601d54000100200303000c680569201004510000500e441075046400803140d91901100c5040c000c0c24440c01d80b5215038940007030004480844000454203400f941c02400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 837598678 1250 837597428 837597443
    0x15120605030d350f010b0a230c011506080726040c051e031b1c05010207120815040507050d0f0605030708010506040b010305250e0406080a05010e01180b090c0409 71
    0x80c01300c00c11036240c4068000080b158420312003240840d901071001802e803012400d00130a00120b03a504404280308034050f007009942001e2001000d0581e054a0301d048406031b07524810b00341d44040c0200e928030103030184c5681d00c451410074061a13880030341030070340c009000d52100b48203142c1e40c00001d1031600000c1c442d030310340c02d55804c4c20100d00e103424481800b180d2003940a100005132000c1c0003503440802e00500c1141101c031070f03042c8001d015007541941c482c59032000c8103035000c00c07181c2800350200070102e0380c0b9003041d10080384d241d40301e00386070240c2030044409480d42c03030401c00b90070081406085400b4034001c0d43303a640e03e400034603075070b0800a10b40240007640002500b4101030701032100f40e5131030043c0d541c1418241024071401c55460000860019002c0744c1020b00e03540a1340381111f5031218208070561041c1000c0d404134580301c012403414001c03031066008224581081c40414243c50603941e610584142294140b00420491100d090340407461300d054415800a00f00050b013100c00400080d1034a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 837599928 1250 837598678 837598681
    0x902131d06042405061c062702040e07030203090a0204050c0403060e01020f0405060a0e0a0e090f060907060c1a04031806030b100c020d0b0115120605030d35 69
    0x505240c81580081409103d5010140c515128004180d080300d00c680742c010a80090820041100d880320071350070414031481030000c0c595803a040801203030225002c1d0112104002241c0080c031440c42201d0840f500c0030202003031aa1844000c0c0c2c02500020040001070040e941510010f07034a5200300c52080071207114040d00c8030b06600345103045070310490901c8011784c03040207007902012440081d64103d840840e8243c0c1e8030043c200c0121100b0500490706600081607600c041418a014444148280011800c807042c80d011450806e64580c010355046540703030008841404907078400c800c80840c0310700071840319045e0b00c441c1c13160300303154002120247c0024109004114213407040c9150b5800400540c03406014801c100f5000520300300042e644030090003c280041070454403614113043c0d00603001990418207607074441210210140c1041a4400180c0c021445112814648203007026500080c004100c90307118142d0903160b207000e070350311404036910030040011440745031110400c0c1c40100c1e480120b402d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 837601178 1250 837599928 837599941
    0x9090f01140a14090618070320130b09041d0a050f070b040504020304060b040903080a06060f02060a0507170c12070507020f09101703030907050d03090902131d 70
    0x840700003400755407165905490401215240c01020080343c08126400d0b1903540301d0030000b40d40c2000b003210003a07150860a00300030619030160b0251034154031501e00580410603034202000c052248071481c0111400110050100007804005000725690140c40014414040d400c880740900320f020744622150b000f0824241085401c1c0110760092845030020044030f414a40c013041180194010140125408000241840714136001401e0601e40580100314000280c2001001403400301c81c0b103c2240e040942c00640c0e00e100d44103141c156440c990282102d07803103011003800501340150490007000100d5054450380c556100141b80244c490840840c1e84100e0b0546004070804020129014028180030441c0907031135940e08040d10321003c45103100305a9403003041d82c40340d110365008802c01c900c000d015a4031102c0000020b500030759881048820880c2d03100c2c200151642030460040001c0c2c0007041c2000791041c00c0d006401140714070b01c0d0300605035481d01c130313400741030044000b4140c2180801c0c0140005c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 837602428 1250 837601178 837601199
    0x150e0f0c0a08120a0c0206070818090c0a0e040f090b0705070b0c1303062d090c08030403050a02011b05030d06140f060f0c010204030807060501050909030c060f04050309090f01 77
    0x8201c064054030011030854003d142500030042100188107035082d01c1e40841da9214100c0300c8050f44a400d55840e611116000f60140858200d19806080c440011420b211200810380d820407896650f4802414448404e000c05000804141048944c440c3d2001c4001071540d00280c0c400c05050359416180c0d421804c100300240b80241c01001c0142041004076007050300303101c07001c1c2520303004cc1010500b0b5484101030010b158284040c02c001c02c0f41400034143d80101c40d00301c0407055004950640314691203a07500c585a210714440104140e0006200c1300c0154080c034001c0303a050f2100c0444420030b09550329054110f03800024100845595107000340030360303541c09820500701101920700c01c144072184004109a07200d80c3c00401c42a0f003011441000d540c400350100ca000d10381c4a8141c50726808940303048030152000f8000c041c820410040041c190003000410340b09000302d050000c103c1900c03500002195290050426102c3d4042044281c10030340391240c18a009505284440640350316140c017008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 837603678 1250 837602428 837602449
    0x30c051519050f01030f1505070203030613020315150c06010e040201030c020f0c090a021b01020d05010b070b13030908010e070303020610060801090b0102070317120105090f04150e0f0c 81
    0x4035602d8601400340103030300c0ca035980d41134070381c45681d03400c031900c25003450600b14030f4010780c0c82c0b2068100360800c05481e90100142d80100307801e448484004800c045040141d0000b100d00c0101c1c80107044030010540340c0001c00b111007810400d0311600c2e242c4603001407820544241c0009804000507014002156498412a1400c0c03c1c68070151612050f0104226148c42900d844103205944c0d08001c16818070b81c0350304403620010410020407074242d0900c5290301035000440411109071601c000007422280c0322044500c0c0c0ca6120402703208564a1045004400300068015010010079900205555001b4401d10003001110802064070900d1442d000385000001041d203030002221403002c020300e03504200c0050650b00030301000b091041c90440100d150220692015281c1c408030b0b000c0e55408440344c401054a110044100301c1c81e1380c0c986050001c005000d03102c1c90b01d440a500001004980c4000c54041034030012400810713084c280c000102d140c09102100c010094000c12500701852402c01083c2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 837604928 1250 837603678 837603721
    0x2091c03181401080907560708040302090c070c06020c010e040b15030c190f0f0c0302160f08010612030903200a27060e13030c0515 58
    0x6808450030403520740b6090708100c4425060141c0d40021a41c4403400f800044007909840c0c9006250942040e00742c040d8891084112400c5010420003c0f281088001c14030040c0001c40d5054000d03000704c0b2000309035035216803000e5855403c2400f0102c0182d42e50003445015601c082e503a0380d00c0c3c10003814503030080e8015900160656202c0348200c0c4150340c000e03500c010808401c540000d8007100071800308000c00144a03d40b00007550000801c100c058081b4081c242e1042d1401d140c0c2450450342e141550140081da05100c0484c1890308a0341300d003813003001d0241100d0311a2040e2001070301422982d0300e4401c100e03000710390001d281da40b050000300004d01c01c0600034140d040c464440e220300e03524080c01520107800301401c4c8071070b84880351074549501100707041c0091000e480441d00c213903031303901e0000e00030382ca40c900c50031103440030301c44040000c0c4d40d01030700082d1985908411200e44482c41c0c0010710400c5408110180030004207000049135040c010380222490906a4003807500d0200c40c1c40c8508406500c96 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 837606178 1250 837604928 837604967
    0xa030c260a2d14010806060a09092f03012306060903030403150609050603061e090c1201020c160e0c031b1602092d0a02091c03 56
    0x5180d94005010440c1c004401800c0001c0040b120401d540a8202035040604060b02621040701e6002d610391014103569001c03410340c00b00f40d0f00d07400450303100e03001911031542c85400b00000b80402a40750740301401c6280324648038211461406006c664000001c103200e11030103090001104141801e024980c185015203642042c000c1070068160802030001c0c008a000e1030000c603a0841940781081101c0256070014403800b450005a0003000252015000b0903000d1030810011680609001403032a0054042e0f0141e10076042800b110450030243c010700e0301425201c1e55000301c440d51200100b0002c012049000966035600b00d40246144c80c19240856180303503031481f0104540d50346009035a401c09146211180e413521a084810441c00004018540c1c00d400000d000ea040103090318258980d0b482918011003035620b070404200294105102c25007107104040d07205411030700d1b55203007035440302000d02d0050500d0705840102c1c581001803405291800188401d034010f168000303079054540b07801c0099 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 837607428 1250 837606178 837606227
    0x5010b040e1303031806020d1103040206030415060f030c080111091005030c0702060c0a0506091b09091528020a0f0f232215180801020a030c 62
    0x8800c054080d0042007040303002c0c03400041e2820503100b50080c6100480201c00028140e03143c1c208140258003d2070302ca80c0c403030300d0003500705101010102a0b92140e5002060300c1e05650b600c2c2c88a1060203002c4514054859071a00302003800075100c0260000356028034041c004581c1080102800c440d0301f80c11610010106008161950745c1d08014640e620720b0034a001c0781c0340d46402882a80c0c0c0e004140000354401404101004103000000e018070b0024018012108181c0b00c1d0303113203591580450131441075083d004401d91542c40c00c0c082c9200d9044248401241c440403441042821a000c05490071240d1004c04010340b0780b1680d0286a1841d8a441c1203000c42c0351543c19000600031503110321200060000202840c0b01050040303280e04000518407002540100c0144050b500b0755028070301ea07011900c03010307001c0c000e00d00807030407920280d4000300851500321003409401c1d40c4140c1420b25450080d04100004122210f00b80050241d80c0c1841e1400714101001c0c100240940b103101003d001e41055401c2c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 837608678 1250 837607428 837607439
    0x2040f05090a110f1012060b1b100c1209050f010c02030702010f0e01120b040f060f061407080d020f07140d0909150902090103090204050f011a0301150e01050405041401050405010b04 80
    0x92911000751260400000001b0020b01d000c020784550f6002a40a040104844201c0e0349220900c1110148840030f503241a09401c070803000f281c0c1301c0000040002c0403000009100100c5034040c9081a02070400c440d0180110040542505c806803079130070041c0c0020a400e02196004502c00c00c4800c80ca00348002081001000202520b4611003020041520741104140c1034036540d0143d041c00d00d110b4428840b240e11040d146000940030f114000000e0503840400f0b02502c05038040d610840c0c0d000103014a0516003113148006900880b01c2c0c1c641581041140c04001183c2c805003101000300107000c2d0000000440c0d014086801e960312005126040c4440c842c028846e0041103000d9943d00000107844000b40001200182802400250000c0c941000d02c13891005001c0241d040b030f1824003940c0d444040443c20417405020030320a10500b400b00c02c1c041c1c40d00d180138040d100e10084041c5011402c1580c1c400002c2d0580700c0c0b50200e4159556014014021400c050150754050089a861246400c0c03809 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 837609928 1250 837608678 837608689
    0x30c1c032403112e0e0d050106180621081c090b06272e05150a051603050904020703110606090907050105030c040b0c07091503110103050402040f05090a110f 69
    0x100b1206100c0d20303c1c060f01643c09020702117810300c1c44005091592401a03520741036001b0074160040c0b510444955900500d07071032480c019034050f5204040842c83d0643d504000e00e8034103101c660704903061841400003e11100f58007506a07c885c01840c008a000141e90a001d1101100501118000d402c1174024101c0d05038022841035000c2c140841e503031800c0d074541ca8611240d640e03140c4901c8142c0e034801e6044182e0640b01d0070700c209913101120a0080721280c48900b01c003a1160000c608007260040c0702901386040b000c115401140d029081c090720b0015810009800c031391000380c046000c100400384114209c1d004000d0f45034040c00980d03103040d090600145261780c5a04910849042000c000000f0f05204ae806094030001c111080d0300d140c603261045001c58a8040368000d141c6c00074600346501150000151002c1e089907085102107811205030401100640001001030360810784880450408102034801c9900c82d806020160012441c5413a08101888104c848684a05544160f9009075601d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 837611178 1250 837609928 837609979
    0x5031f1512032a1a1302152106010f050a03060305011d0615030c220504060c12060311060a05070c0b130e01050312090a1205031b030c1c03240311 64
    0x100c964807615511210094040c0c804584000d4007d0a01c544298082c50290040c0c07284407043c00c4108085403090050b001c1d4030310111041800251502d04d685070950244004108201d03851501054013626500d44509440d12000904400d20545800d084031200500c012500140c8052014800c02c0a00c00003e64444118540358454001100300c032544000c40a00e40118141e809024001da00d010306110006041008110000c207402c60109000e082d128400e00b410b0782d601c0795030700c0c4010482009022240d0004c011000502c0300811114000c9804209110014a40500e005030b03128510f44411041039601c2d400141c81007240c00040c0300035500410300a01c56101c141c4083e440310a400d0000ba030031501a4499401d842c1640d07280014000040010708144e01c00d0801d200b000090040300300e5a0f4450030303036010800d4209901d0305c040307515540d50218a0007001d2a01040d0940da21a41c4001903407440380c034812600d102881003042082c5c01010111450048690b540003141c04044002c0070005e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 837612428 1250 837611178 837611213
    0xa090611070320130203060301050f1303080c0c0a120f02070803180a032003060c120f0406020d020d09050d03060303050a18090507020d0905031f1512032a 68
    0x101c1c03006860440c99200d4003c94208001400b81560340d840071060002544180c038050b010b0750a01c00050640c40e030050116000b40d074000d000c1e43d06819103440844240790054268412040101300f0000c0f2581308002101c081d50180501015200900c0009050100e030080f40c40c080d03402802003007003200c00200588a20030543e01603a50191b00440004100400759003004005c4407035080416031440840c150003002040c164112083c80c3c4540c0d21104c0d260141e5580c03520505c00407800600d400544031460341d00580b0500000d41019a500c61300c0c8180e8016440d400d43c100e541c1c59021060000c00c000c0c25654154a04040003080c0c1180c40051542c45a20401c10a000c004d40b2158004101011002e0040001c050204031609214800a488031540200480060b50200000c2898500800e220400701c3c9200d107405182da4444c48440c005e07022034801003c0044c5041d10000d051040300681c0d00405100e5514030200070300c80d1401c80070030b190644403680c2c04a500d0b9200000500ca080c041d6541e0038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 837613678 1250 837612428 837612443
    0x91303030b0f060c0303090d0804240f020d090c0509011a0a020f1b041b091518080706021e070b070503191e021c0e0a1a0a0906110703 59
    0x480c407002007189039400c1c05000b80c00000005111030a072001001450161121030143d498444032038008581940b003c0d50f01900030000b000c400701c10201c21000e000c6220115103c0400c10120341c0e6200002c98200c10001280b0350f4641d580d90003000390308500742010300000c40c2c1150455050034028101c0781d5803520001890017000070702c1032849000b000300b41007541a52040341c84002205020a40b40c210544080b4000c17070500c0030303415050380d070700c0c3c9150759030700041c0c2da4442e94a240c090340c0d210000c14010b92000b0302034401c00c400003281d00e618642e405065800300034594036180240083c68000007601605800c07228401e01c1044660104001c0121403903541c90344d48403400c500b0441d0640c448d84200620708850300485103051900321405511840e107103140c180c44e42d52003503c02e07600c41d40011441640280c401c040409120700440712880c0d010320103015003107216250241840b4071400084510340c41034011410b000620340c03111000002e0301c0189440c0424101104289070b0b1182d90380802030500c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 837614928 1250 837613678 837613691
    0x8070605091204080c0a0b090f0103020307031409010509150106090e062205041211120d0b060f1810120f29090c040302010804060203150d0b0f0609130303 68
    0x300704029218003501034a03041680c90344e07943d01c40350b80c4115000d40b0368065003601b80d0000e680345400381520034441014001c01205080e8000440003940000d10300001e02d5030300d00042484450b40200c4501c103081d54000003407a410022581d6240040308485141074a010800603c03455a11182c0b600498a4900040794291035071000500054581042c101a0b50780c0c0008815508441c0e40007030f40505d001d800b00654040c044e00c0c1c2100c6c1c0c24a0001340303005a92088040417a901d0b0044010100c41d43c1c00030001135181e12060009c6d1040d0700078004031a45500124421940c03034841072401d29103d070111250903c8210150002d045002c9104041d840390703944059009513003e0342c4c1c04c03040700c01201c0448002000d88000038443c0c14039101c00860702888107280002c5548130040101da080c0c035016112140c1661340c40e99400d01952004008040801e01021504c5243d101c040c04660524401c0400c0309403490140402420040014640d61107680d804040c480001c1d00c4120104820b03815140c08200e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 837616178 1250 837614928 837614941
    0x60b0304080f091516020f0603091e010f0e06010e0c04030c0e060111071203090902030c0304080f040e0c03010503060a0b090a0905190f0b012304052d06030f010908070605 75
    0xc1c41c620036500c1d11150002903184401d170000343c96010058401c450100e041e09055051058a0208807501c01c10396100d4950080b0420f4a8882165402c802c08000700300c00a44440020650f400310940c4845a40441c0c01401551030528420340c1c49014a942d160900b451500c2d000302c0043d41e03210b407212200300000400d03e50303486200800c2854090308101c1d0500b690b510380c0c1030f00d8200f00440590000304c1650010411981e5402220f0103106100e00e15401d50f2600e8403904801e501c1030300718110351241008006008400040f40900c1001c8150f00a5201d601d0f1200381030030800700816402015241c241072100355592070380d100342c12030b25075000007a2070803042c94107928001c8000e624200180010340307030000304441c81550745580751060001c08400d0760783e0041540d40608a5000f011526030455000344c090416601c00c42d8025244181d01c147e400c904d01010441e41e000181301402d200b80e00c8100455401c1c200302d41c081409080780204664411a00c800d5800d0147c403100414964803000400c15 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 837617428 1250 837616178 837616189
    0x111010b0d1509020a03050319021603030e0a0e24030a0201120b0a09020c010e2401030821041505100501140702030102090612160f020d0333030501060b0304080f09 72
    0xc00f0755010b81a00205c0782c0300d0520958942140d101a01c40561301060000700520201d0b407522054040b80d5004c0c01e45042d41e40542d500710f140c061043c0c01800141c80003800c900d10644050041e28141c0fa9078402508402c03880303004441442d042c034082c0e40b10f13003041d07070041c2d030b1106841c041d50200290006a4034020360010f00341103400c0d801410034600200c0c040d1180c00c01035005600e184001c40449a10a200c01c0c0c0d00e0715039540d00c0307001030f001044c4040108041018840109803840d24140403c040701000040e620300c20304240c4055841442206100044001912036542c00401d202d14504080d03203042e000900311032440f0848104800046481c804644094050b604ca0704002001d81e51039403260f0701d0003036a840003124541403030a18404800142400303a142100c40350b0859000c9c00c014900312009501405182e50902d41c45900c18102d1542c001c1142802e50001c00e42e4070150140b0b91031804c01c01e09440c440d4200410402040080c0070004000030200c5618160039000503498110380c100088 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 837618678 1250 837617428 837617441
    0x3200304080d05090a090902061813060602062e1e05030d17130812090a0c1805150a210f08040305010c1d04090503040801060f050111010b0d15 63
    0x8600c2c8254a4080e0042c0d4010000d0403209000380c4102c110507903501500f80c142e441d24080a9001a0200f00803448034952404803005010050010186207098000203000c8174070a6000c6001a040f170401e002c070240f800c4029151500c1c1042015940d1005003141c0074091040e44a0b03400d558614007920f0b80144000e8041d803000b8100102580c26000c611180034200109014441e11059040f0340040d0909130b0103200d6610407500075103034900b0440840c050202e0300c0406462030040c0d1244140d034000003000c4001240241086407181c00e1201850083c9000340c64028000642c05a070b90541c861880c1c545e452010121480e079030181c0b400300d4008a009120b80924200034021302c107006441c00070300c401040140100c0e840384008000044010b001140c82000d41e01494010075148440c691444c5406d400041d8140c0c01002039926090795028440c3c03c5a17003a9015108802e0b200074100480d68020b091140c12840040080c02102c41e00c10000d20806081480100408402401c46a1112080e072018 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 837619928 1250 837618678 837618689
    0x20c01170c0d11181503010617090f06070509011709060424050a1505030318120c06130515030705030f070c06140a1808070b0a021314010207050d03200304 68
    0xf990fa50014000070700301c038254590350714022400760382e13615081d136072240850f4102c0b41c49603038606030899141d40d02c0700c50020240c14810944541c10910340c0b048010b00c0000c2c0110615120540d03107220900014040f00f801c09840784004100d01d040004041003c2480360303206501c00da518103202e51700c0e4003000b00180c5100202c1d140603d44020020f00c030500b40d01102841103400b40098030076944600b01030f0369102d91440140041030103400030541781441071701150b4818200003a10503481100d4007044071034200120082c80120912410407107410103008080141035042d031014598030304000054001c6c031010700061a5591050009602244034141c043e030f131036510500038404603680b80b00c0d1603e141c3c000c0d141004e4051500c081d1aa481c1e040d200324207042a448031180e414114143c41389411340c1d400030402500181c00b040501c00180a9800d80c1015088110005281c1150807000a192034001c3e00a18021510b18841c440800e40040c0407034068151002004400c48641784154154000c1d503109 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 837621178 1250 837619928 837619961
    0x60a0605190e0a1b0513320a05031506040c02061b07050a1707170c0a021e1c030f080606070b1504021b010f021e03040f050d08010501020c01170c0d 65
    0x36182815403085c0142460030074441c4022626403250045100c1c00240c4100c049042d01402501500f02284401c3d550500802030140d0381c0c5541d2100401d09042d10901a514851f95050030407207245400d01c1500680d00c0c00e48010051403512040640d084200309407008079040c0041a0801042800c00c180c4000c0c9034840344a000e030700d4101c241c440c1e0580005074104d601c1c070301102d15490031030719410030f6501054400d030050252211980070f02c03555100505d4404807410301980783d58140e0300d40c420200c050100d00c64000c43d194005003401040c0b6144940c0d440f0400869038244807140c0c0d9141705a40f40f086d003180384102a9180c000345021b200722200783c00b542041c00414404211407103422004401c10510009010a0400210b198101e21070321940380c030039000d08800b070022000750300081c560191040b800561030704081d031200352500c1c10800e41c107400182140011310a40d40d0612016802843c28204060304c0441458a08030481d00240801c1c1300200c0030a266001d041e85812550540951085 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 837622428 1250 837621178 837621221
    0x30c030f0f12030207050c040b0a06030e01020f070c0320010e04050a022205040605060306090a2706050118050f01051e061206011707022a04050702060a0605190e0a 72
    0xb805006904614001c0d1040c1c003604119070301c4c50a00c0d000744540c1c0407000301041880c604000090307000f4000346140140340c1d98244076502000c800c0300000c2c00260700490a8401d5540782d0320701400c1d894810092005041c5041809103200d90f000743e1840d0960704116004070302c981c0c51540d064028050183c541e03201c04810b402012011000f400e00f902a580143c03070a00c071254440c01032055030b203c151089034002800000107142d03031865078000030b0140c910480030b8040c200c80031003441c01c10208140664425a440004102c0882c403036001041c01030030820103000c0303480d111090112046c014840c841c0518000d80103000703c000c02e0044a0f00355030313000f007006071160f05140c1c4004458030122581400715006001655204c11340116071445500c1560090991000c18803c0d010480c200740c0b812104100440004201c3d50b07558003640e4070507811a0300500b0103141034880001551120340c0018080d9001c190a20100c0d000c03800203105484582070b501d035290f12100080c0e002064100d902c4400c00c2440311 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 837623678 1250 837622428 837622463
    0x22030323040f05010605030c090a020703020c06040303090e13080a0e04110c01020409050106080921070609080307140a0509010c14030f0408061f050d0516290301030c030f0f 76
    0x6aa20b502c05010350000c0101c10345640c01c1c107544a000b110f8007540025458002410b09885070010601c5a100b8410303114082e0944002c80d02540050f0012004100c030b842c020310080d01c040c000789500c41c0000c8500c40a03040503490b140d180c1c1c41175040c0103080208d118500300b07142d00c072a001039004e0702c4070000b940d548001c40e90000e4002c0d0018080c8102d414204400003030340500c1070010340d02030b64040c3c007e41003200c1d125100d0429081c442c020b400f0501c000380440b001155a610806c0c488600400d0b00390380c1d80c60a0100189161010b09070010045803e100c1c61682e60b41c00426210b4010b803e0030400780e01112800c0c001d0301028514000708951000281c401d1803841c5034000b80040b0341c00e120440f0781903182c0b201310408006c80d21200c9240098040d000300114a007074820b028545000780309607892058800401c0d542c0058030303008050340700c03420130208070208464031625450006114405045504550b0b4440d1241014400940040103048800042c000003040c10303029194444031000c100310012 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 837624928 1250 837623678 837623693
    0x81b06100e0a060b0d0f0f0203040201171503010212070e0a0803180319050c1302040b07020103181506060207060311121b0703090614160b090106080f10052203032304 73
    0x6151040c60182003813242d480040701f50003628055035050b102c484c0300e1103000a035075144501c010208220b40340c1c140040c08058078213200a20120100c0384207025245132200d40909650440c01516008165089040000d99070220940340303a02242400e80c0298048000041e1030441150810b12100c1200c405540070840001221300403404142d0302c0c41400c0b800d42c02e00d60124011031190f40b403d250304010303400c010f61195101030382d100594003c61b2010704041c1c95524000c1c0010120810003540c8038400d000c003d4040000304000e000320b20b01800726801c070840c06100c50017000c0710b07540000003035004921192446c02100c0044c0c041e42d515a502c0d40c0040c04c0040148003944103c07000f044010401400c800c40b8a0f00b1100300400a0380200000419903648150350346006260071000d558a24000c105001c0922844640c0003070300004209000c12440c0b08001c07158080e1488649a0a0810001c0444003d035008202190181000a9805c0a500903081031490040d48074602000d544c00700410840c01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 837626178 1250 837624928 837624941
    0x20f1c1b0f180b0108010f1404090f06151401050403120903050a0606062019061b0504080d0809060403080606132903090a0209100302040504081b06100e0a060b0d 71
    0x803030b001400b54503002001914140c0e401c1c01602c0f00d01e0141e002c148003013030420100395507041c006040060210000d860b40c480c081a200800c84c0e495840b0410803844601408003200a03100081540c190507040b4000a00b50303200343e01c8010a554108104d42402600500c00036000f190000c0544aa500d580d1170030500600060250801083e501c40040c0030340c8525006041a0056103801004c04034016040d00759522000c840403101152200000401c100d454188000b1300c0444c0d0301c81c6601d440c1046070803400d000c809400c18080245400c204070207100009495030704113800d818841141d85a59010488605c900d41c011420703038030b24410010303040201c2a07021020200c2002000c107500204020030310188029541c1003103582c00429810b0140c42c0c510040c41d00f10301280e0914043d50703681e6001c201510340490741031300c0c1b00001042d22015030f01d4a410840711180c2c50000781c4501e00d1301d0b180616900510340141030540f800b80c000501044071683c0204040c117581070351280c484100c102603501a000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 837627428 1250 837626178 837626219
    0x703030201060b040e010902132417090316170301060c050f0d090b0901090519030b090307150908070507083901030207032a020f1c1b0f 60
    0x290500029003e1103581c140e80503519000054542c50b403034800868003139080030700101c04c100c050701c070001410950602580d0b000c00709040c410041c44140c1001400304a4924800e002c00160f00c004c01c03110010110454012060540704c03001806154144070300c1d94074011005510514000001180c8c098100069a0142e44035504680f0b0002c020034000d0344950100860002065119905016620881c1d020b403440c94418909018115a14000240c10400078100040d415584010034014054aa540c2c0c65220303102c10021440c060095681c90480403400004210030f80e40c03503040b4020094110f08440ba11500103007116903071625840d1a90301c50012800002e01200d985a1513034501e400c5400d046142c0e8001210082c0b151100c100650207540100070071410021204a4501703c6e251030044803540c2460761407071400d0b90010b072050000c2407480207401449030404100048405022178000000d00340d01c0211411660071444401c0007503c1c0e25040040d91000b8000082503002001030001d03138825 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 837628678 1250 837627428 837627431
    0x6080d0c03090e01240e0306010e0711030f0d060614040e0709030605070809190f02061e19230714070506040b0c100605010c0f05121c05011e270e0703030201 69
    0x40a4150640b220406e601600303400d80c014000401001c104a0702c441c0e8004002c1c00c00000d2805034030501070560b40205030010580702c011945158402d8588181400380105051101d14a110744c0c0300300711580503d2041c1c00c030707410119000482143c42100300700011a4000030900090810365009001d0100840f10780f1060300ca04009032400541a544101201e40c02c80e400e600d0380031194003072102d00d0340924501a144906052440c0e0603071400e800034060304003903840c800300715905640001d000e081000320840054607203540c040c031255441c104449005502a400c809000c141081003400c01855902032544090081400940b0011810080c0a8104c46000b603850008489101c507007216441d000380360001d10007011070740000e6515460201c000d80600c00712802001e5586180301c1c2c0350701c5005118142d80945054a2040d41b55008007405040c21482c111521200340e1921030382e00c44907109802d1100c0c0703041001c8030201b2594810b00c4046904d000c003408075060403201940d070f1740a240300840042d0f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 837629928 1250 837628678 837628739
    0x70302030307270512190308070e0d0804050d0f080a0e01030f09111909091a0a0507140d02040801020d0e0714031c02251806080d0c03090e01 62
    0x100c500254080341c5824005880180f54105014001c80c29020700d16801a4400c10031003103030034401c4d007200460b400d200c2d980300d080c1480c0480c4010311044109184501401c103886d294000039125209603010313180c040e2596603031550071b400e000c034180125801c050090b0034001703021030881d58082c0e088102c00743e003170300c0600101c5c94503210b04d800c9890b0301c1c00c0600b43c1d81c015103958003e85040800812604415250900e083d9102d00130502200c0c02101c048400c0c41c80000c0005219101d101d000d54010340360403041003a85000705024010700e21401c02c0d00d24031000010304001002c40f5a050300e01815000d0000c5444028104c480e0b00100385846003144103202e000c50009d0900e20342e00b01c038100720030098068001c08000055902450103005944800c0d401504203014901c0d91400740c045448a400d075148681504e040462100001c134000200b0105041c80400d22a5220000310900040501c2c40c20b03031a224518103044491a00c4c90708101c0c0d0303c40003c4000110b03001c0340743d8a1411480084120400f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 837631178 1250 837629928 837629957
    0x1052701020f030705121b03030a060e0a050708010308092706040e0a05101a09190c03180f1a011409060f01080402040506031c0302070c350c06070302030307 69
    0x40380295400104603a1007460910040519000580000030501c7c4140c20129180e21419065401c101c0d00940540d590340d208018082e08000c5141c0c004640c010100304030704254400510f103403814040a0000707000000ea0b01441e40f6a0b0b007280c895003200052000e00706200c1d0038181c500d001c0685250348100d0400a412201400108048000c254000010b2070424406200c20b400b44c020a65060b4840340c0c1c0c0038204205484005805108035005401d054140001c100e00004880c041c02440007014548940b820340340310748642d00c00b9003c0c1c02009202c0e1400a51030002e40c00c2c00b00f03074074614030f45125000001313503030031400c080718400f070801c49800d50b280d6140b03801c0c070140700e074a040b840380012121004170740541001da001e030703820041c0503040d0b500c943c0f08854011040c102078000500066030000340070050010b9440300c1ca001d400c620540340340130620b410844804103050f003071002c52001da507040c100d0a110100900100207001400300c0c2e03160030715410041e40340e070000c8070004040ba4155100d13051 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 837632428 1250 837631178 837631183
    0x32e020a021e12030f0403030f0e01150e0c040911071703040c0b09060d1805010606051209030705060c0c07031e030e0d030906030e160e18060402100e01052701020f 72
    0x1407540c2801070f9034150740d6400c1c01500c60001c003600580515603106180b415013060ba004961074600d9040010500740b002035810080e03d21154420f4500d4511541404801c1001da8100e90031030383c2201001c92564003a851003071a85c420041c1c001c11002d4940009640c15680002840c421070050394900c440650300d24007900544a4611030315032186040100341003443c446d80c0050300c6442000c4120b80c42c1d506d9596414215911030f082100404c9000c02c02c0f2a2800c00721340c401e40c1c48000d42029504224160342d034150b5914014142209074100820b5401001c4410051500110303040362640703c1082c80d581c2c03d045500690701064000402c000d01085030b5081160703551705070320341c144d58036142a841e2203811001081030011901d450300542c142188100b04030451380001e8503013502140520305040c00954441041c07103032140141c1e0030200400000d0b9880d42c2c4000894507140c01c080c40d020b01044012222446182150b03601240b07241c04c01c0c40c03202105000c406000c0f02c00c1c0c01b140e0455100c00c1d061507 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 837633678 1250 837632428 837632443
    0xf10030b010b0703030f14010504180809010e1c0605040b0603060f040b09010b0d0501060e100b0d15030b100e09150c09030309060d020c010515032e020a021e 69
    0x28104494000100714150b9181c0041072580c1c041c3c94001591000300b8490026102181c104042d014801001408140351600c600302146116080f1005014034035034441c001400f46004c142d0502c51014582c00440d00e0360740d0300c5021144002d101e080c082801d4a4140300522080d1401d80c0d00d2049840010300a0400080c2140244094501070722540c1e00d580e1407448404000b8280015952150000305240d181e40c140a030703c1c10321400010a5440c2032240b803801c0c6140040520240014940c410000d40002c101261039000102c1c81c0800c0440914a10504034600303984002d00000705e0000b0031004194400c400c0b8103440501142c810503440386c080b030344c0da5880031408031b018a200c01c1022800c036076140e90003020340030800b505580c24803000500107950740c1c00000003c014240c0018109900c00028400d15501846140c40c0307101c050402c001095543d01c603100b80a4110b0134086a0614580046142003054211298299655000c040d4004d45941c202e81500300b8030a01038141ca84903140c04200c64 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 837634928 1250 837633678 837633683
    0x2206030609110a0c02092d0a0507050405060a120213031b0501020606060d0b040b060307080906010e1506030405010b13020405180732190f1826150f1003 67
    0xc00c00c1ea8061702001035505028100c01c00e1042070f10343d1424030411140f00401c44110030080c141080c581031800c0b10030b42e20020401010404100410701c0350340d0b80e14055444d0042a8a0440340d4a032005200e04024403a000b19098005140200001000000c80400440f00658a03100c0241590390b80166138400c82512425440b1328284040880c0244a5210001c150300048c80841e64172000c6021035100da20607108100011005002c1201a40040100c1d50041444252114040c9442940d0074800c2814184180c480c2c0701c000081030500c6803d400484030030a009080901b254603150000c2c0003503120703204980c0500d00f4000200500104100250700c10b15031b0f42c840d01104560002c0a880314920401801103080040e01c4210000794054041c160702042c40d554210707020107601000d0400d15082c00180200324601800804100030320f04142c003111124842608c2e230813681058a605c031841041181001e110b02607144160341c500e00d0a840c0241c1c540005504a500c80e480200399400050001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 837636178 1250 837634928 837634937
    0xa1203170a0603051b01080106111e0f160807051e0a0b090414040c030204021e030f06040b091611030d14040308060a1401140f03100e0105030a15022206030609110a 72
    0x41007224044d518903900100c2507410b07a01d010b0b0200301655454be42d00d0000c0e409503800448031040600c010405032510001c0c401502960914000c411903171403079940506401000c54102c440410f2165400c1310181c84c2000b0043c4260688075103031201d140d00300500075803041d403c2042c410f0f000c2c07000507142c60003550408113959038107045400f4480658090400c40342c0c03001400e002110301d4424013001e0745c00742e01c0c52420400300d410000200030984544058851140d080341040c803641c504401581c80381c041460514001502c0300f0084142140034560a11121505200a49030702140340502148501d00c240c642d40ca4680344e0a040c8041c0892500400c41c0005c01d6551b107205542c002c0d2081082e0002c409410b03450009403100c03003c4503400558201c16440c202540510100721601102d07405801c040d4018000c1041d01d49840c5400194032669620b8140d0020300d030b05214001551803109207050907a020440c0d0303620b650060040c001e501c52a40d0341c52901c7d07010240a00d90000301c0b540680c4a566 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 837637428 1250 837636178 837636181
    0x80a031109490f050a150f06051804150e030a0305180102031303080603071d090c10020705090c040905070f0905060708091c060c111b0a1203170a0603051b0108 70
    0x241c4a4142c9440c03c402c2d1054412030041d00d0006941101151355003020a402050451600c1904400e690590700900c0c81000705125410f400d140c1c406480f035002e034010080e0040c2521310025080107184807034145226000c0000c2c441d1410b0b4050700914020200444060722a4500c030001500702d020507100c0d03200d01c0030380c0d07001000403078130440030b040c0c1004008050f00d04540e130700c0d440080011a982240c401c251040b02c00c00940b0f2805014030f4202a41c103582e6801c1c80e5808090003074844c0303440d00a0034030a10f10440860f4079134200b041903601500400c50200210f00740958040c0038621034040000014034010b2021440303060607019030b17040551080020b801e0408a000b04603460ba50711003170014070704cc02c80c5c8560100d8040c0c00317020380794a115102d0445490100344901e0510620705044c00c42e06000c0700e56400d45486014541d812205408224081c002c41e5103011180300031890400f004031a140f4003405a172032000d520043c02c49100340c00700e684101411110b6803010042d01c1049012500703140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 837638678 1250 837637428 837637433
    0x9030e0607030e0901091b030b090a09080403060c110d09050d080313050106060e13020c061b0c060924091c02211b0307080a03110949 59
    0x8000d40601ca2080c1000304400551801058410a09901c154078068589400b0f040f1444e11038820565006203203410701c54407003000b001ca1888103000c0e2014181c5956904034500f0b00101e40c007510051584030030140540075540070010400706071060803003041c0c00f42e03d50420302c441c040c600d0340c0c0031500043d080002d2502c007921000c450341c1004140c01d0801020500e200300180080c490300e03024052949a204080c0c0302c200600ca0b200c0c145075040c45005204005600819100040843c5d001c0c0007081b988903610002100703034809001c2c00046480d5441108244420310002156240048642500d05040c3c1303036070a0030f0000c0d107036820745040c8166044014270318400488074016001c0d0140900407900d11303030781012818215000c482c4030408424004900f00110034100b40c4c0f00c0e43c00311001c10083d820a51940c036454580d20807441000241a1742c4c03180140860808003e44d90f1080d0002c0030003246030101108549464662070483c1d4104220320744a943c0301c0c81c08295001040603c002c190104130869 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 837639928 1250 837638678 837638689
    0x6020a0e030f01050f070c0c090b0a0b030a02120c070305071b08030705060f06040b011d19080a020f031b1c0b070c06060b120411181e090109030e 64
    0x128120410032100408150468404019180d010407800e00006035514006040810108001d0b02c0c0300c00304005443c2110214440b852031030107903411104009602000d071000220708410591100250003c080100000d4007103c0d8040c04841000440c0400710380d8a07600c0c801420b10900100901003241404500f022070308600e4260b80d88001521170300b204030b0302d8005580c90740e0404441200c80d40d04c400c0812003904c19044019402c01000c1d20300f132104d10006c0c4000303020220310a10801c46001105240b0100303644006490003440d0070781c6102c400c0c950300e854821383c0f180741201099000b5140040d80720031904000030125403081d41030b02f004841c4041101003014a64405030200b034451007084056012440d6161014060300c1d064407004840d1903540343c6942a1031342c40c3d1010b0b1071801d050185000c0c1d6100e40c000c1c02e500c5035001c0c005038a0340410500107100c144031502d03403040c2080360200300710008090110030700503d42010440030190350b48110003400e03102d10450090000391044081c0207681020b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 837641178 1250 837639928 837639937
    0x7151d040f05180c30030706090326040c06030e010b031621050d0807020f060c040501112a0a150203030132130204090221070801120602 60
    0xc0022400685003028041607030000d4500c012000d02505140101d400204160740403800140c3d6480f43e0f10045480c501480341050303e090050414030a00e12039103000a1003151402d6620001c1045201700d5801d00520f2010044c5d403c0120103407080c00008401385600c641449240e0000c20342e44005e0501c00704a01a00200602880782d6490301e901c03200340d641c103001405e86042001c0c0700f070182514122080034000358100410407054422415180821004221000840340a0911280641714080201c0c901500304040b01182d000783c000344061095000c0c01003084520903a03482003400c0d082014581c5603400b5600610b00e400f48401c11107910b100c3c965801440d29001480e0705200303a41d5184d9864450120b07030103403005030000401400780d8a03030441c7c030000c000da505444c0010003820b01000c5418902015400d071082c002d180129034200c8080d01114090017141005545841e040d01a40141003482c140792081c3d2030080d8002840188110041d42c12a400d444000300c1c0700b03106841c0d1030700a520 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 837642428 1250 837641178 837641237
    0x18082b0516061517030910050a08130f140f0c120a020d02011106040b06040c030627061505040504061a0f0c07030b01061d12100f0f05180715 62
    0x280b01030014502019611307102070031000802440d07030b421144007004480012a00c4403800c0c4041817202480d002c0c3d000305840e5004401c1e03e100e40440a050038080a0050101002803103242d4444032580040004225481c4441400040300c1d5108a100200840103d4076180100b00d503201050034405807900200021a060040c1000d00c1d0814640e1291824400200c07419210360b40000c060010070f0405129900303c845003803908011190070b10502c240c05450700c0a196504d2091702c0580c1e82c00c0142d95000800030804599441d8000e80c8030f080280250300310f403013501c0c401c1d031401e00d0005c0c92076024a01c0c007010070380e5245000c1c5003005e0008000407581005012450318410460080000362060442a01900d0f180d260f203d0428004202d980c030f0001048501d50040c4080c510302c4040e05000204c1c0e180d0744d00143c17004550150f510058000400780d0300c46a0000c82d0501c8103000c2900844c08000030000c0342041600e10b0a61070740301b0602240e80c40e0106900103a00d2082c000640790400b81c12010010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 837643678 1250 837642428 837642461
    0x109080d0305190c11070501090510051c0c03150e101701021c020d0e0109021c03120504030c0209010f050904110f030709020d0b030708060718082b051606 68
    0x10b41c43d003003082c11204c008000b1004100701c4184000c0c011400c0011700c00070002480c094180904120114250003030321080e1200748080420f811080d0407500089030002c0424582c10404680c0040f001409030030381102444203036074601d03030110310701081c0c1c60704900c0b84c070440525801c2685800c0c1d01512010205a190704155424000341e00c24507940062405010701038440961a240051a402c2c00c40751100c52300c5030180e14002c91071005071284240541940c0000d0000c0c003292096050036142c581c05c241441c12614602001c01c0308050308014249078040c002d0720b20865981c1c0310f841c1220f400840707000c2d15901240040004002941c00f150b205010840075044e001020240c20100380352482c0758008800280d00421030486402c158402d46c40c0304441200102001840c114215485410103010318041280e50140044580700b21503042004051700e50490782280c0101c0d103400c0c50100040c40c1000850644840a03180901c00e00650351619050192040d010095544090003020319510950100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 837644928 1250 837643678 837643711
    0x19110a0806010f14030f0a030f051308030a1b030903020d021305070c03120b0643060605040504050618160807090c02120d0506030703170d0b0109080d0305 68
    0x10340c09101590091180718041c1e82c0c03050901540c24403244003041d0f254040d5010481000c03030032000091002446405041c03c00110f2626142190148140b0080c40081e03010b241c0006a034900000c01030502c041c0c10b82c0c071040c506155040820301114001c0d00980002c80c1d40e0010b00151900d0742d203a040c400d100806400c2c85c11105290b41c3c0545004880c001c010601c0c00c607241c814550800ca081160403040e00d010002d8802010001c3c85030300905040e081318036090f0361000340607410403411070600c070351444040059100c01e0b44031000065040074201c49a5050080000c0e503400e283c09660b002c0d0750311602501c465605d611000520148219220180d48a03001c0741c0030080202a404034050705405d0060700e0a1410599250181c80d039043c0c000e011903110240c01049030200c0401d54801204410000c0780e41d45130700c030000c0d01e0904aa0070103001c0801c002c801c03150ba10507500c01084600074142f000d0200d00510360054500c00c62a2080400d00c0e000002011101842a0b207e154080300101000305d80 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 837646178 1250 837644928 837644939
    0xa0905090102070605012403020307050a0c050a080c030318060408030703150e091e07050306010302010c03020a06110702040b0109050f13090c0b041707060f050304030215100f0819110a 81
    0x2611002ea202010903681110191f02d505100e0001c901d44280354201903265083c04039008110f4454206a0002c0200c11a01340307003045014024410080e8006003103680359030544540355200e500c1903802807218030001d0114450b054002c0745191141c0d0304401145e041d603035000c1c81940503081d03140040402010716003000c075410131003a205600541d100d50040c0002d481841d000d1445541402c04980300b948011420400c5940c00904681507e50a00e4401421081d40c54242c0c640003c0071030041a150034411108903103007600c0c01810104d13000300c030248866200640117640440060081135000603207100060138a05101c03691826901400100080c84c4035103450707555100001b901720340b11421340060104134020350161921011107414001e0004d02e0715002010b00b621140d02c41003001d100011000400381030090220701039490049191000920300420948090201c1d802003140116005001103a9000009407a2010b0305c802a82d01d04014929122041c81540b801c651039071107424440003048 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 837647428 1250 837646178 837646181
    0x9091b0801050105040b0613060e150c010207030e0d020904080f0c0303041a010e0f0609180303041a13031409300c09060607150e0115031704050a09050901020706 71
    0x500d1010300014165041c0b400300310a40390740d50049803240901748881000c507151580d18000b200c8040c00c10140580d0000007040b108802c82440341c51090001c131f00c0e0880f46a0640050109601c00e58036028050030400400980c1400381c00c029403c45c800c900010300250a8500400425981703050480c10300704d0075008070b442c59208450469a884200c039108031f00b4401d90000c18050034404044035003c0c82c0504140b00550b01c01032141c0e10940c00b440c0421490000195070340c4100c440501525901d28290801c8075040e1202c1740054508031184c1c00080c3d6150041d4100b030800e940c15582e9481800d0384401156041d044840c005d5070001e86460181000c00c0700d180300400082c3e000d5900010620510f10903800c0c00c05000c0d041d0b0007a101e0fa001c0000994508085034101c5134841d040401100711596906c00400340c10030039054662a1a82200c10f104074035440b0000c4070b00c500011144003045106800480c0200d11460341c1180b0283c0080c0b000303208036000f4962240c103d4000605003001616800b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 837648678 1250 837647428 837647483
    0x405060706090c050609031f090b0c1b060105010906030b03251a0901170702011b02030403050f070f0e0901150902041409070806010c020d0203120406080703090506010909 75
    0x407110790b522070303001c1e0800c141000d40303100800d400c5a440b41000e41c84000b0a84a000310081601c4103260b0f0041c13584111102c0c3c0c06648569007110090a43c0e142144a06840350300450b83c681d10b01d0302c2d81141c1c0024000000d420780c1a500103035210382c00307a4039000782680600400d0100680c103020f5104092a1025600380003c815071140c4a1210101d1074084850055002c0030340c10720300300004100c0003040c2e0b608604017400355040920540015034074030400b240104503090072611021701c0b541440109075400009032095901540582e16040c40341e2140940d150068451001c809072880400c200c0e01c01c050860b19807003100030b000800e8801500d141e003952211725030000c803810756022809001c0501c620190f0f8840f13603010b5030381c0c502504040d003000d0003525000f841c1d030741080a03840e4200301719119240c10035103d9078040d0880d002c0b41000c680010103074101d80202800141d08900003592a4424007800c51303525080307005000e0340d9003024980000703010520000e44c0c00114164071411003420805042c3e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 837649928 1250 837648678 837648683
    0xf060603300a0302092e080c09091918050a141203160912380906010303030b01050a051c180308090106170c0402090f03030d060302100305070813020604050607 70
    0x1a642c02045d01040b80c0d51a1130015031804a01c1610500c01d202000300207920201070a04181e0f82d81d41e103607120180c062048440540c0c000c1c080400b4404c0c0036514009446140b10040740900041c0c1d0609400801c10b040e4400c05482030307010340701c4280031846168010f07100e54100c006a54002c00d60070458000e036882030b101d89071290251140440c440e90b101d094400034060341246c0c0c1c59103100d1619000710001803428900e40d1014000d05848005062103401d41d20101e150b0a84003081c508100c042c3d443d140c0910049d804030f82011109483ca602c84c1c1c00305c440c0900c40e5281e150501c0c440f03100f8416000810b6500d2494940d441c050300204d08100103014034110f10940ea10869858072900312425510030b540214501c40702d81545021030303c40401d10003400c0c002580c0050300c40800301c00140c8000d920b07468494160000040c100b0341c180450b0000070aa0b4007d540390100385403010340850450380c08850320301c0041c4010300072907440391580145070102400200154200740c3c031070001920719800582d04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 837651178 1250 837649928 837649931
    0xa110405120c0411030c3106050c0d05040602030a11010914030a270905040816050a0b01060c02010c0303090311160501020f0c030a0b10030c15020f060603300a03 71
    0xa0300c8585070601513000c503404120050350079030800d0040304086004412000301c14010b8031503110b64202c0c403800901d8102c07508503004001d1030364a15000e03003a9841518040b80c82d000f550341400c10705000310b04030740031505183d00031480c080107080116004500e802c0884841d54131a401c88003c6000340c4600144d60b0344040156a603a08200e102900c03595210400d2010800803506c491034016046118108803401d00601107181d980b0340c980142c82e481024085089601465038990a00c50009401040b01b4403602104002c3c2e600c62900f91a100c0803504000e00042c040559070300001c0c440d801118106102c1d050181001900303d10450070044503220002c00c0b81070030030040005690410101010013600000303449841100b1001c26101e44c880c41e0003503d000000008601520180e0360118015a080b4030541100c2d0b4494100401d40d11448000000502c00d02d94440c10468010900a003c3c2c180107004018680c440703600e104c0e40c0c0c1c40288451048017951403640c044416060b004200c0c0c02e085950 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 837652428 1250 837651178 837651193
    0x200327030711040b010e0102030406030c0201140a141e0c0703110604080a0216031a07140d0605010305010b12060f0301020f190206010806101e09180c150203030a11040512 75
    0xf404200c5050000043c108040c090404649036008400c90302903030311514010640442441003039015000e1050b6059010028800300b00a4680303d9000111008a1041c031003d1074039268001000c03030140c281c0e01c48051000c02c0102d80c0040038000100808ca202e410404c1c0080350045c1c419047c0350040b02c0c203645513100042c0e0f4045443e810300041a041d02d1080d4804441d034210384803511b0740c1c030440781000d80e460082d002288a40f400b500070030b00310020303100803681e07075069815441001d042d541c42521b0200b8144070004c16140e0803d0269001d0f80c540c02c114155a1f9221420085254003c40c00c960305550b00704001010a044000204803518001130411f5266405003802031800f03a05038448010f0740c01480a2182840310300d014441106c840c001030407081c0790f00c060608842c81c06a40300d003503100d1070461914079040f0074400f0b05030260701403d01c0e40d00700c5a4130f4282d5110920013100c5140142c1003040001c1c0d001c00b00382d004d84c42c644011522103080139141c00100e01c2d032402280254166138003440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 837653678 1250 837652428 837652463
    0x9061d032a0a0b1812060711194803020f0103050906070c030210020726040602030403080d11120f09010c0e10022e2003270307 56
    0x300c00e104895082d5610b4a038a481c2000c4030b1014015640c0084544441c0000e0002594a5030300350400c00142c50140c0f056030074444400b400d01e5061101b014039600884198800c400040340322810600c3e04007046845c1540f1000c004901070b580e120000c0300d96440e4591000800d200321a180052041d0341d4002420341c0d0550041000000340c03041014100340c20441004101040410103940201160510a0360340e486d6150030390a00c414110303164900781c40820a40b0a00007528a600800750080504201034413140c800b01d6528425401101c0c00741e030003088100000340b5600018600c41c2012240016000781031524180707258030103001c5070401d280c3c02044c4819001c9217a206900f18041038000c000e0b421210030094072092800c2d0159200d548940b9070401d00e42d00a0202c42c00004e44c06407400464400c0c1c15100101e007820f03540c1d0310241da240001d0f0403010041241002c0003001101c1095095542d0540e078540d01c480c40902d00c442d840c0640000c034401030340410240c58524410300807107130b4100d10350 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 837654928 1250 837653678 837653743
    0x120f020c0a02130501030c15120504151d0303010b0903011806050906070e0d02120f06042904051009020612100e130f0209070302070b01150f02060709061d03 69
    0x19030040251804c030040000802100c052002c442d90200d071400d09040c0000c081e1015074030116664004c0e030402040104024441c031b0005861440c1031001c1024000341e180031002600c01a44502440d40200010322010510300050001804010004070301401244200032540780c80c510110751043c6c580041c41040304d01402581d074004403030301e0003140b00c01501e0000f41c42c07040c0b0035801a000300b500094820140300d0a0041c01020100c0e04210703016402c107894450440a9041600d40c10b5401c0219280001e19200c00482c0c000ca8009005020f9410038007011402045219001c03607201d2020040314844015942ca01441040500445101c4a00d400070000040800800c0d406512401500d841c001425442c41400b50540648402e2800e94580a0980c000d10a5400c0078080d0340c03414000064054800c008548956103d03910f1502414040c00c00703999904c001c0d550000851840d500038003c9a120300d05c20381000d0340405400c4404441140400d0034a9804018502c1c1117000b03000009450844 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 837656178 1250 837654928 837654949
    0x5030409110309070b0306040207200a0b0c03180118061107060e100e0f040906091101090f03031107090204080c01091e050607050c040501060f02060604180201120f020c0a02 76
    0x2800c1c10034618588880440e0b00c4000314000e222070700c039011011414640304c42d41034401556004464191401820f50302c0c2c0c49400c6440d0350148104154480401c2072030321001542d02c0c06000d0001542000001000d0a0b14034610100c001e0401501c40c502c05004249038a40c10f0061480d5100d120b0f444480031b180c06e0034070700e48d03402c40000d002c030030044801e042c2c40300100a07800785420b142950b403054500d000111100d40d5515480d071302500306829102801507039804900c040d8032a00c010502034124200540d40189240320700e0310362507425070040020070f00421541e0216040b80c001e07200c44946400825080307070440c0d082014141e001c9000d1500e1543c000c0c41c2c02000c0c0c4842a04d5a504600c00c144c03c1c07070089104e00541c0e006a170045140c5c0d040120804c0706c05020764004009201d2907031581c2d8000c000001903102c1400501c00c40b80854040d00b060f04c03400209030460f0b18004541040c1e9001501d1b5418005034407d0b5a030380e01e80880030984034038406440c0d020702070380c0901411080c6004020050300d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 837657428 1250 837656178 837656201
    0xf17030906100e150409120201020d050a0e0303130602070b0f1603050c0a0f02163807080715111b2b2102070c090e1e0f030705030409 59
    0x1910350342400311403100f0141d00d078800c1100000300042015180880d0142c44076610041003040d8a48920107080e4040d000f41c0309c0702c0c100d4801006140d890840380d00544d003402c5000003564100304081513081c032842c91046042d901906000d4074104050f5100540e0710011180161055600e2081c411245160030303680e101103407103240038007407401c10686d4070b2403e1143d814403c00713200020000505135070017405081130110f0700700043c1c0d0b403280c0c1d103001d12100034040c03468449008502c9800d498138807143c040c4200340c0c065100549420002d641e130710031049500420054071b40c1350814034103400040d0140645281d401060304c4c1603448880c20000301030383c4140e160004450741c01c11800b1a001d082814100c0c04032074180d1030060042e10807a14240c543c142d2a00100010788140c003104400501590000c002452003001c0402c60a60745000040c1114043d05441d00701d50130203101810700e22214071070b0f00309001040055072407515a00d02200d182d44d00007081182c8613000404c04104007074040c85005903044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 837658678 1250 837657428 837657451
    0x1003020306150f12060d150b0d05070b090306060a150305070504030f030207030203060606041d0a021e0a0909110703120f0212060f1909051f03060b0a0506130506070f17030906 77
    0x40141d0387c000c40b5005000ea010041e96540b13070070403640d079100d040b04801c00340c0100a4034120340e1a541c04011030790020044901a207d0003004c10150300b810a0980110307465174021518080590108401610000c0c0600040040502c800310100e80700e495066003403403088d001001c0f16880c502c14182842801008548a883d05210411044203a2406090301c4140800210038540d24110380b00001d0041701c21403803482c140e8080814202ca0810300078140d090040d00c1d25100c00755910596400c0e211076420f4807a401c5400c1c099100001d008118144101411510100d42500ca0154500882e0019144084114008020b00940781490599000f40c80400e54182c40e100ca8060b5016426070b0360382c4601c4150725581c0300010045e400c1c1908580702c504a14481d44011503590030310b180036101190302d00d842108400000102072901608450f0705010010130342143c0c0303240000300b00e5142c01050b400c0d507120240d22540000160300036180c1e644107042410090300c03814001c01040c0703170200040040c043d04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 837659928 1250 837658678 837658699
    0x1119081b1617071b0f090614040507020c060310030201091401050a050a0203040305070e0105040f0b01020c040f020405040203040b09070e0402030c060a3e0c1003020306150f1206 78
    0x2031118100d44400350800c420080d50301c0d401e4692502481880030143c604110841034244d035038a603881150071510002484d40140c3d4583e407909080b903000e845000501d07410310030440b100d07003030540006600801500598001d40240310116016030b00c2280c40d0f8803c1000d0400c140f0841d0b81081400d8082e2102040c400110320240340081d080344a13044040c0d0500a01151520449108004650195a20006450315240d4503425480c16030428082e0901c691304040c4003980c446610b2050f01042501680200b10048105040c0402040102c103444000303a001c11001c500381d2a1030000b9030055200fa00d06098a01d0704400c0c40381800141d80241218842003410b00c00541c2d4002030410b00250111034072681d80c9014102540c40c108428200100442c558188040f4485604038034000c40c2a61300c291120108800b02c6540c84485c1c4011403a0b11401c0310060a4503a032103980595030044001c0e00940309003400d44407100290700400030b2160900000503500d01e504108100071a04108240c4c0d681c140e0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 837661178 1250 837659928 837659947
    0xd14030903120c0606091306090614220318030816110306090c060f0c0109050d03201603021e070501030b04051905060f060c0606190f06031119081b 65
    0x4944005d0310051148130300c0d501142480c500050700c90f002d41d074080002c129166840c90030b40041d2600181c00c000e100090800581c400d007896110f811002d410031180c6e06400303c103942c15508000f0303407120800d040e4000c03c008000145128002c0c44440034081010038401103c1c604800890ba101c5a040e0094228001f40148600c00080390444407400700d4400c0e80b640e0183c0240c0c6130310b016103040401c0640c00c00420100b80880070905000c0791440ba0380900c0700040026603070811541c40d04091401c11010485182807401e041440071403a8440e106980008600043c40350150710302c0c10f5414010381140c0c07030401c042c2d1f8151141d0451118145c0f01801030717180c003000500b4070062150106c0202a02c2d8400280c2655aa1481d40115a0020b0906da02c400701e203c0030300c0c0c0d50541260301c40d01406003c03d580e00c201d8a40d04440c4101c8040d80580c507803c41c01c1034070480242150305800b904401b41030145800003070f02c2c00000000403a0329a83d03180940b030b103400d0f850304800b0b5a070303950800c26400f041042030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 837662428 1250 837661178 837661183
    0x80f061f031808211014150409090c0807090513030f17010f05150301030f1407030b01060f0815060f16060e0c0a08011107060b0d14030903120c 63
    0x6582806090001e416156400c210442c90721180d0000c0520400181803055060392640c00c00950450280440032580d5050003c040c081142c00350718a00600148840308514049074054031901d00740300c0190416a60311000c4064400c0750000310f80030244201c0501500e14104250710007000c0902050201e4208401e148031000d101117000f07400c201200c403542d4400e0b4083c103d000407000d21a42400744540e540c2c04110312500389030060314441d007070294150750b59140301400c2d02d0699400000b50540301400c0d50790207000300c80b09003034444e1a0080e2000040428000c079032a074003c00094507403441da503c05a40c028800000101040c80c0d0382c01c0041c3e20056515114243d4502d000038480c89541c4418042c10784a00a5017041b000b00440c0c102400031030362000c0400c19800c200c205079080c1a0035902c0b01082d909884204818032410103007030003100c0204440790042009900c024000981c2c40c5080e0f29450a545034809002c041c2e5400001c09030594201004402c031400c1c10500c040f4242100e0f00062034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 837663678 1250 837662428 837662479
    0x21308011d03030105150d0e120307030c0206060a121e050a060501050d0b011a04051507020102010606020d1d0f0904260a0503040b0a0e0a0605150a140409030302130303080f06 77
    0x9460744000c18001c02040607030344012300a00c00c99085400610510403841ca181c0d2086074075100283c24440d140d034441e400091502d010301c0c8020309802d03c1d40e0034a0011810b2904c20361054500860032054400b88490b0014580c5a96000302c01401303024882d070402e0020ba45041c1d112902039109400c8640106480e502c840341034400c0c1d16004103540604070307000012070141c0d411140e44800b410f030328219111403200081003054403e0b002030001507078030001640c5440d84015010041080f4480801150025010100d41c001e40104080c401804107004103800c86011501100e003c01800b01c2d130303030b9110a61004440040134402c1d4041c1340c50b104c1000202907000140009000842020200d0503e144503000710003108640c608481201d012402e201001d08000d60b5180000041007c100020303051045c004400e803010700d40a03035880d501d00300a01004145100c010b904143d8207004044550f01e115040c4402540280d03035010705410080d06802c0c40c4400074142d18407a4158280380300241d11519503a0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 837664928 1250 837663678 837663709
    0x1a0d050a060807080a1203050606161a070305100b2a0a02030d0c2616061d01020706110702091602070b03070512070f0e0f04021308011d03030105 64
    0x4159612030040d1000544182e8000801902807803802149650340003401e1800103000318080d229014020f6025011a0820340d034443d00407104004240c0303044103144881c00b100303200c0d03144184440c0131200c40356a00141981d0410000e0346239401c0c00400354900211074060805010603520f06184425526045031155411907038003a440384c159040d42c030040c071003000c45580203420381d00310081d41c00c0020040d02100c1802ca960600800380056410f0040004019102c6c0c01a5118540b00c1c0b00c1d2400c44280c40007807002c80303030300d6286e01c0b111000451000343e01420802040015841d030480d85080015244566101c101d201e00502031500540c1e240380d07106030000e500040159964080c01380407420160160400c10060000005105555034003400038580c840b084030420307aa5032240c810450b241c00e0320100d182c001031b50413a1105118038000500c0c0f0860b20f0f0040c00145031101c1c0ca0010a841d0040703510a0603a80d40d2008402d844180d14203c907159400c80501030b6180d507041400160410410bc40070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 837666178 1250 837664928 837664931
    0x5010807090e010213140108010608010503060f0a2004231503071e0e090c0c0a061107020301060b0a080f04120507020414040b01080d03020c25031505010f1a0d 70
    0x207080e030240c2c01e5048811318103e020b010911140c175110094600c0c10000c0526000440403000003a81078131506c20305069500040c080c204039141c03004d15908440001c3c0503900c0d0b0a954a102c0d0700014006002111101c0458842d140c03298602240507100000c20300180c086c1c040c0c039652050855480d840c001442c1950714500c0ca0322a1155801140c181401452501c5080c0b9501c0ca00a6495003040c0b0094800c02c0c100c07401d00300c40c0d41d0390350302c0c844038080c1080d180e103954030184e0102c00003a8a50801000c000400d20414100421500040d080d16001c0d40050f031401c030001500e104041c1c2c071400d030a51000500403c018282856510a08880007040d0700508100021565008541c0c49030055844048144248181303802d041c1005410a802803099680b988101d49140068601034001e9604840039440a8040d0000000c0401140d40c0c09514000e13004104450100001e086503841a4003074200030400600d0f5810038008200c2e424994020202c180b00100c1010b1000f41078070304540c5a9440e4120 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 837667428 1250 837666178 837666191
    0xd1434061218050604110a0b12040303200f1b01290a03020d12170c120402060f220b0906030c09040e06010909020102250b03180102030109050403120501080709 70
    0x149040001c1e26150020f205016000c01c0c4800e02221002040a840c1e00715200b841007665542c144681e40702e01e00038419411010800a400700f03009038450a049401ca42070380340420340410120440f0350100c82d08102442004c140140d04550100e0303c1e07161554004002c0090796500c11803920f015021800f0183c2c0480032142c0001240c50b80000c00004580c041c00d040542801c91801a0754411102251400280352520044110101496040c007409071000803070710384945e21800060840c4001c10903a0040b50410080560071403040c010030104030b00d000c00c5c40301e00300c161107111410400c0703a00140244400384480602595058212504100b1004c2c0460b5110210000301d0054503034400142814040d40c0c00004000319541c21100e00140300341e007a10070078468035800b00e00d085c020750480040c07400002d00c00d202c50700307014000f180c02c295100c010030000c0c9001003015007641d0090304a0075010b47c40d0011f00c401c140d040010410b0f1810001010b004030341c1415003140d5200c0241c400c03012951348402d03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 837668678 1250 837667428 837667451
    0x3040b0f220320060d0902012f070b030702060106080a0b0d030306080d050313031b050703120e0102030711060310031b0f05030303150d14340612 64
    0x40391195000d5608074088507020032454098284540b205a070804000b4650510310301002c1c003548000d0300300411031800d040d042c0051400138111b142c0205d050096542c0c2003900851400c52040624059034050b0f0400fa18000005081c003019a00c0314041c11410f2050040a54003c500207043d01d84500d8041a96510010307440094844e02c0403a542020070109100c06155064001a00b91107200c0119460480c10080c1100e5500c01290301c14101c2c1305914010380082c1c8505c10b0300903038511500441d00e491003da11040d09200b42540110381001c002460b44080c0c1d44c0140d41c5c03403031140c024000b46041402030744908e06540e030503ca075540321b0800080003451820350540c00700061504000c1c0340c00c8a000e41c000c108900c04450060301c0c074164071050001103601e40001202d21900e01c861030311385080d421909001c80e82c101a04200d4054003581221000c9031030401c41c0d64043d061070010315100100030160320382a0144455800c0d03032883e20381c5d8140a501d8001d1412401ca510701035000943c04140e9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 837669928 1250 837668678 837668707
    0xa050703081b0d15210602070c050a170d0e100c03050c010606021e0d120203070909020c0c0f03010e0c01260702030711010207060c081c0608010905100e03040b 70
    0x341c1d080c400b03001c1900c0c094080d46a02241d588800340251031036141e143d091a406420139641c03042d00100755014910300040543c0c01400b455481044c0340b2041c16203410000b01403155541040c070b1500e08000706840f20280c00c001403169803110b410958194458040420381f0380a030000030009001c40c40402d80304042c407035000c4a00d03255200c1c00800c00941c84000094442d0020060b1403182100150b10109400d400f245424074040562500c3c50724101180080001c0e42006040c50144102a04001204182400102503171011803010307041350340100003000b0b2a0b520b0320a585000303030b160041c031031040040042c60010095090034810b0030300450180c4028940340d010080f48100703001b9014051001c0d0004080c0036035034800d4071100c8880510000490362501d161003200006003c0b81d085001003000440101440c0300703034808411901118003015410b0322010362001d400c0d6956218260140a010720003807980e61021401400b54070000389a11f5a240030304d006254090000143c510600030b802d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 837671178 1250 837669928 837669961
    0x105190b0f0c070e090a0b1b040b040302041508030a0302090d05010f0507090816052106040503031e01030b06040c0203041e180c0f050f09090a0609110a05070308 71
    0x5900c003403941d80c400d8070451001c40e000340070b8102683c03003012404240f0018030042c0c1441411394800401c805032003521070000886002d00000c02105030769501140100c400c2d001000900ba10740d10440d40d80b450f40c4184011103010020b200070118036032800384103070070004c011620002054600035032039140c800006010b452070410020299841c00610180040060b00700c1c61040c07200340c58017030080e0794480c65152504c0484143e81032000da2075500344100d1a00000b46521010f150b0140c032407042e405410b60341780c60b800391003c0d02c03558404010407600071700030320601c40c09403c0140b0301881ca502d1035503140401e80001d085035200300c2d01c40d400040014401c0060301c0051606204802412002c0c00284d040903225000d02c00c0c04028601180024501c03a02844903902c0b015030350429050980303e412515504080c2c44081c80120400000c4030340c3d6a0441524081c0b00c41e08400035180e031400c0480d01c11552581c003402c4241d003041c808452460380000c103549a064050426100b507986100c3c008004101 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 837672428 1250 837671178 837671189
    0xe0a0b040204080f012306041805031201150e090c0d14010b0c1603240608030f030117060403081302030a06060e040b090c03331305070905040b010519 66
    0x20202e0001021540042d80d041030701e00702d100801500b42c06000e202e0302003803030102010f030f00e450b06404100c0600340390b030116030700101050400140e0b00c015507a55083d90301114450741d0044a03400107202e0000c11722442c01d10700d01c00d410035590410b1021302040950703e000b041e0704015440400d03035640022181d00f100b082c2d091031201e50708071503855149010003138114044407805485a40050300100c00f0001d412020759422034505150220540b42001032803d01030392040b00d55484001c002013068040010b002501072921036640c0760740c104241c160440340665060360b040d07031100c018800400d0300f001c4410b030081c244144000a00540340042031620b400580b00920440c540100041c01d4818803c0c400d020b28400d207900c0030240c446c5401590340303840316071b03555605403c070010244180121000d0751000314440035003a00f24056041d00010b87c01402c41c1d03540e4280700368595210421000340b1014001c1c1500031300800c01d50500b522003e40303480050040e03500400f04040042c0600f44204410340c001c00c1d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 837673678 1250 837672428 837672431
    0xa020c1501030312050c070b0402010210060627031e030519030902010806030604030f050a1106010609360b1309030e24030f040317090a0b09030c070e0a0b04 69
    0x19115920809940902c0180c00107000c5840411141c14540110341c0104440140c05040404a45070071100d2000980f0407030542c403c013200344150007581d000c0c080041ca6540c032549100d074500340b1300c10021142c80d41c1d40e210083d54040140700285800c40f82d1034074400b90149168110a0314601590248601c0100c14107042c1d0380070306907503640c0d490b40000c1011403003079070f0740d0000351101804d0503525001030b140280402d190300c500d00615031250b0301421031503440c1c0c030746a00140e040400c2a8141002a002100007031281c80c1c0c140018452000d2580e01e081445115140d441e04055043d112010080840c1265903140c99608000d60b9401e41e1400d15200b40c040c1c200311804041c513010f0001c810f03030040540256902c0341111380d58205035580036444183c22040610b5a6035003070420589130340003403080f810300002c01166500d50140303400d0280f050080c1d00003002544000e007414940300b00c0003025500030754410001140c2840c00403418400f29600c010840406403a013400c0407014203015400160404d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 837674928 1250 837673678 837673693
    0xf1a0108070501111606030f0612080702011803030f20010e01050a0b010c0201050412020d080c01020715091121010c0201060f050102150f060d0803040501090b060102030c0d03050a020c 81
    0x1000301198040858600340c0340c101c004910418040d444050340319586031006501c0740c01300040c50081c0c2100e6502062607200003115611032305820f48411101c4003d4405410100c0d80108550700201c8010340302d4510000d50f40d2132455641e00070944002501c1101c2000240310755106c030f40ca0340f441103242140d010070085c4110b444002a03240240340880d90005c8140c10b0200070240c1d54001c0102c41901c03501a0b40e601d15260400207a00050300c45a0700898214112030702d0b1402042d11600a01022000d00f0009640d0741018101301d2101900c022a817100300d4a04041000050400441c17400d0862066a07100d02ca50300c4008007080b1a0b603040303885485035007444080c03054558198049001e640758054201006a00d8200499460f1404880d5094540c6100089088210315001c2c142d030002e0010001031000300203544894281d041600c01f1142a9101d96002c820040a8602c40354091020303c019401d290349500300d0750350740d9148140d03807050659403030110f0700c0010303260111200c0307810b1107040301c001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 837676178 1250 837674928 837674939
    0x20c1005071d01030204060f0e0604030602040f090b040b010903020f010908070f06110609060105130b040c090312031b0302090d0203030a021e0111042c1f060804020604030f1a01 78
    0x142403140300ca09030324020040b00c04505602920941d410340d100b590341c5404411840b00295411030301d41e00700c55030040c82400b000000488600040016050940980700202d19240807141520f14400a1030301c46c03030034910010b103e44d0307004181d04101d9030119800315070079031400b0040c3c4410400ea0080c4103136000b503d0300070480482d20140501106d41c540d461100b40107841d41e00740e4840c6000e0b00c9064994219000400c003510b00316400405c0c050854000142c40003030f200000d4100ea03a4142ca16000c1021000100305105202100101001c694281030152550010100354854001c645280c14580d000c900c1c0092510f0f01c14004848950160440c1c0d51350900400103952194410480c0daa200140414510f404606005003c8201030f90442a81403506018106142c04415800d0403030310007040b0440d4000602001540780540c40341c0b8488039200c0507001000340d0558007500801c0c2031081e12030078080187c5450080341c00702d0741c000c0f80075080543c0c5490062080e1024050050b81594441b001141 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 837677428 1250 837676178 837676187
    0x1c120501140324040b04034413290103140601240815040510060e06040609030b0a0207020607060e191a06010908031204020310060b0706020c100507 65
    0x8189000301d0442e42850540d0744010305040200e055540c007408070b00f000c10002525000d00e15009842428881c00e02d1320b000c184000032000d01c0000c5008100c051881d4090405860010000011210b42c40105460101200d41484c1c504101c0201640c013050200040c40110303000318050840d440301700030344550390790420501081c644072060200d03014240000414088008008a10196010700c0f40a030075042d400070303241481c0081243c0d00e0200080709042e0700e81d03614410389102e01408400c0036a21800c0c0800106920341901825000e075400300300078000c8641210070002240c0d0b1107845000150344802410010380910300d0000d4204c0c4020031071804000446d0810706035100c2e0502100c4102c058000085031a508004000e81403034851078481c210114446221640a903060611b4510190356000721451a400204400002e204071400c0c001146020301a50145442745607041c0081d40c10002201c6041c841c1d204000d001550001f081d4900c40c07c2848074600b8214201000c04c5203107010390002c1c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 837678678 1250 837677428 837677459
    0x20c040f1a040905280212060a0c022d01060509010b04170a02130f060807180e070605090111010b13020a1b120c0302070e09160b07051c120501 63
    0x744a00410042040303400c15100c0c10125075009070041080e07103101d008542d4211030800d014141900e0a09089016841d100d05151031221440001d02c4a0700d050a420400c070b8030601800790071074002a9002c0815034140440454a5421022801c50701214100140c010450344c0d2026410a04003000082c0c405d1120380600101c8049000a101c0a2400d840f2541c42d0b60210038020741c0030034600c9000d150700b10b1a0b40300e40760f9580d082c080007908589030103005141601c1940f04e00c0400e640300c03e4484be81d4403580600101200800010480c00b41000b001900034003560321141e0400c010311402c9a94000300b5081042180c0e4058007a0005000f07041c03801010354440803003031010440500304884841303c41c0903c4042c00c0d41022400700d02c65461402240c050015032000e50451141002c0403070316041d20b05520b030042025000400750301201c9007074900c403040c13643d00000d15200c06122000200d030010031441440d6030034001c41118030640644c25140700300103a4004a01910700b000203d1480c50760520700f07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 837679928 1250 837678678 837678701
    0x140f0619031209170111120919110415030c030b100e07180803130e060303040306020c0a1e0b07140f1204051b03030403120c050a1a070801060e010f020c040f 69
    0x1d8140801d118003c0c281d45d00700c0e4801e00786c9001044400c801c1c01c24142242c3d0000d1911050b039500c2c4100c90710728210f62500410540d0020303190080c119161a02d81300302d8058182d4505100b2080e455505e6014641d1141d04c005132400101100090143d02d4000c3c20350003804412600c0f988a060003e001005110011004007001d044007070081161507001040d1664100c19404140c442c1e820441408461440903105036018403003800b0200004802e400609002c1c2c2840b001400c1c84041e070b04100b02002c101c104c1400040310069982c00102d03024002950b0b010302241821451502c0e1101c1004140c45418985c8130001c5001c55003504a4600d080b6850090380030b54201c403000c1c4000d86094040c00843d2010943c1640104410000950141d6420a0000403401c21407117210b5282c0b58107080c1166000700302c3e801c426030303187c03040224110400141c001c278441c0741c0001c9941c1442d001821080b59030076072a0602c1200240c8804441c0b003005040d042400181c014492540880b030600c000e4030003995803 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 837681178 1250 837679928 837679949
    0x402040920010306230f010e030709020903010614011e0c0804092c030d0b0315190507050f0a0810171e0c030604020112110a0c020103140f0619031209 66
    0x6041e0b0f1040716503c01d202e0a44481d03581c1100c81010403801b0f106040b281e5050200c00f0b04080030603074051080c8002405840310141e07888201c5000c043c2101d04642085110301301d0003001100070399100c4030505035a02000202c0031103804400c01a100b400d6030303602c0184500000200410410166007000c2c18203803184012500102e107942c600d0782000c0310b490201035154000d00142d80c070424650880c0c1204040a010381d10100185d601c655400401141d0101c045080301082512004551040542c815100d2800c58100350141c0c81040091003188100410007580001007410f075001108103000811020309402c10420001d04001c1d2207801072007c0e4406070f8024411450070201c0843c0c58440d500004010b400603580305d07801501c6042144170b0380c4d61020b42c7c070109100d206442c1001841c6088460719184403c0c2d02c541300040540351104403001a29902a060100764004d00384810741045048a103060002800310030a0000000c5074005002030111918a641c00c607086441081a1500f003420b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 837682428 1250 837681178 837681191
    0x7150f0e0c061909050306010314120405090f15040e071541040605191e26040606030b010806010f090b04020409051608061002031204020409200103 65
    0x501e84400756542190340000c020400781d010400c00101c1c0003410610740c02c0c00030403030b5296000309140000907041141c11449140c1d00142e40030701000494280b070328150f00380745441c0c10900450a49040582080c075010140c0c00456420150711101c107200f244050000c204421201d940702e81d887ca4940300310180300c24040d5112006610034500c503103122400f400300d0300c84800c8100c030b03408840c208441c800c55511081c0f0a908101d00307010006200030042079842686030000d04a0900d031446582d0404030500400503051402e410300c0c4913400340496080c2c100102442420031180c220303d402c0350f4012100d40c0d0045e00700010043c0d980d02c40d80c1035034000c1c00d6544060b80c89149545d69038800380248a40030b8640c0c8801c110880f80f640003400707550300c064000f600701655003c44105844054520803002c001d41ca0700c90011607403003c4415030000007210503d9210460b120060748078402c081e007400c442601c050000b400c0d501d69030041403a0710b50202025010091062282c94103481101360140024201030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 837683678 1250 837682428 837682451
    0x706150e0a0c0e090a06030507030b160507120e0a050a180e030c101104150509040b030c06090603220c060f03050402100809010e010e010b1f0e130207150f 68
    0x1042c146040c845032201c41c03200032541d040014880005256007011600c54202000080301480f83d000214850242c01040d800d122981040041c01e080b446010498244603102c00704070050750b44102000282000080547c4420200d41554025007000746c0000c0c0601c1300040780c4945502c10450302620010800041d2540c11426480e8400d2040c0d07002c49a00101444000d030a09a20503524203051504135440c0641c0e50306020004a41e141150011440c04900004c507070415001e0a8402903044000d03108020580c400120035014850400d0301600b00800000c0e180390744002186100c03000c4081d88140c1c40c200c0c0ca46082e04042c10301030340001801802c00341c05018028011030b0b000f01d030300a180c03101c044500d0b0400c50340000000c010240f21340d00c2c2d501501c2100428400c110401c0161400072607001c0401e028044100c4240000c6008524000c085090303003039020540c3d8082d00002c403007041d004864250b00401a000700c0c00c02428982c04c0c42c1d400700040754107600c0300c1b182141d002e009110030f01004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 837684928 1250 837683678 837683681
    0xf040306110313150b030a0b15032e1e06150905100c05031902060114030f0d0c170a080a05130510051905040b070801081b04110706150e0a 61
    0x1e840c4003d100030000800300c006001031100c24807006800800081e8119060002850040b0b511006d42d10840f02030103015520070011600011248141c000300030700051400c89a40c194401d40c1018074580210078050030400b6103821100480ca030384c4030040051601110b03c5002004030b4030540d00200343c5001034149240c01802c402c030865900a01d01e103112200b0400540360344400030700484a90000300302801107125031103841c0041000d40e6008081c2d075814806000c454440c0d443d10603200350704c440045121b004c000550800881054a80400d48080e10b19110b9031055079100702525418000c54082480c40c3e004002ca441464030900c00c1c44030362101c42d005010001c0104016101c0c0d00800d03850074400780ca80c5c215a41151941140d000d0507c0621660000c48000313076402c4404203980000e00c200c00e9803085046000d08892005090840b4002c04403d40407019a100036000750345645020b42c40742d1441094400c540c0d08040700b4400b482043c2c013031852041984c000d890f407003001c0b000401c9400780139 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 837686178 1250 837684928 837684931
    0x51005010c051b0d080d2c0613030e060403030206070e0109050310110903071410030e060112032006071205010503190f020402041806081204031b0b0f0403061103 71
    0x710203014901a40480301d040300d507064032120f0700039005080b00300c00605418020050b00d144079400061403200000070070741c030013000303040740b03000c1c40100d180c2000100011400c549c1001c00c8241442814095107020359440700102d81d500d50024020900000b03240e004200349104007219039610030302562031001581d1001d01c90040c0e42d003680c400725488402429a80c1320090b02031050803c54104801d2500191a044064026580d1700039000d4880d003103814004518403410046081c24003088404406196032094148240d03100034000034040014140102c0300001100745040c01c00c1400008241c20681c1d0740401c0e1805c10015032031030011a00035103a8880da40c16200000c01800010b02c502222410f50850110161390a4007550442001607885100a000030f011160f10304c4650b00d44130308102c00301c17600c41e40700901c650410380103501890982022141035960012000d01100740000c88525a44141d0700201406c0000140c0e4180119103a4040d10480e4032900e41800051000d220380031a5000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 837687428 1250 837686178 837686183
    0x807050303070b04031b0c06050d061a07020d032c030609010903081f080a0605040b09060c120c070b01032a0e071b06050c07020a0801091a090a021201051005010c 71
    0x2d29404607002034812100c440b82104034001a1b0406200354880210b00903c13648250003040c0001003404c1410014000c520081c032940d600142229280e03059111944aaa08001e00c646840c0c8044810140203440314484140e0b40604034001020107020400c1c548100b4211500c00e100b41c600260503814140070b503409040e4155242000ea484002c15482084425440b540100341035103004500e4080410001540381d000d280c0215607414581040d40508002411078449a0084801c02a84c041410700b1144150813001d01d14000d070707492032605a0a4082d4010040640c04828000002d104007030300d94401e800c881ca40000c07110312050140300c03141036561141b211042c000703000044800d80a21000c0060110f2140d86810b030f01002d949800c00c9400072610780710700010101d800410740c24010041406080c50700300800031400d091302c0c0e1001014010300e0b400000f0b14032031b0000701c60034018400740c1051079000d080e407200d050302d03c0303a414003801045580d030401300c4178028009020340c800c1e846600100d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 837688678 1250 837687428 837687443
    0x180108090a0309051504030b0f180f03040e2d010801240b090d1209080c0a0b070b0402040e1f0c020a030c15110f0c010b01031a0f13020310080705030307 67
    0x600d00001d0100e5107600700305c0801d590b40240800000701d15010302d2203100d0028050300203e245000c1e01585c11003c140003c158080c1d220240c80c035042c12001040b44c00b5691004007140150307440380321082885028400000e0b60188030045808244010480740b41615520802802582a4180c5800110815000c1442007a01c2e15100f0440b0f90503850040603180310207003108400f004c081d241c0040040c1424540c10000d5070110007006004800d0242c00c42c03102049660101540c500342800341c1c54054a90090010701c03c0201060071582d460744401c1892000109842d08450603002d83c8504880411402c5001400e014071401e40c0c40c0301040310072500d80c2c140c4410580c16010b0f140d080c00380950001003540300b9950081601aa002e9070702070001141040c062983c0d40441112007070079641505c9810b4141360610351401c031503000035048400c3c03150040e44c0201d420306220000502c46c80300c6040088006100205103c5100100c0d18814140c640000c121070f03034103540c1c0b401d056072446440c00240c54031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 837689928 1250 837688678 837688697
    0x91005040b13180b06010503071e0314010b040501080a06120f14010501260105091c0c0204140402120a03140307020c090c0301080106052707050d02180108090a03 71
    0x103140581c462003840101034401d00e4007a0400000d04100e881c2d40403020b000f6036404440c0010004e580120300d50004d800c1c41d01710700b181410680039116040d2440e034007034201c076000107551003148280c2c8060310400364090f0b850306c030f9650f4417014005d991090042500080900000490030502c0b40240780440d422804c4460381070002d5111240c4600c59840c04a4820001112512204200340220b074060300b0408515000d01c0c0395110846109140c181c4034a0050341480208005480081640034a9564105901821441c0c41c0d90840b5100058903009500c00d142c120000d064051500380144940c0c070954a1030918201114000c0c1e8850b08050b004000650b2101c012500c50b850ba8003540d040803080c0111441d81c48001c0016000d010119840302a074400031004000081c424090080181001d480109010781c01141e80381c0207518400c0c0c201000c00801020401091003041122076104900b80c0854846444010150388280720b404180d00148110340482e44504011038400311096058071240f914 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 837691178 1250 837689928 837689939
    0x3060b090f0d0804120501020d0b030c030a0b060d0c09020c12130b1602030109060507020d1409100207180f0b22361205070b0c0c030f0d02070506060910 67
    0x200b4551620450b5403000c248000900710a000703521070290f521610001d40c584031100012021182c0b0b1440283c400e6214649190542d2400714080c041d043c4c10100f2000c06584540220700e2034103c50070001c2c50315212600002d4254a2070f4003030105408108151521110710914008541c010169202103d500c091801c000101c484001841905020b500290b40c1002c070b6000242151680d00042d6240c035241c00421196507418450480c0a00203030504281d4910341c10103080b604c0c0102403080780120410101081c0b04ca00070851800101500b00c2c1140d08000903108243c003a00c440c1e185284d400342885890a4a450241840c0071b058204030305520561048030310b4140546003c03100c41d241c1c02014144200c42c0040d482c54120060440d44d1426024895454403404000c0c82d40041030410409114010008000441181d00020222640c0b80c0716020405c001c0e00b140b040042028000d00c0000300c451201229070041d10300b2a0280042e0b800603038610040c0071001c5421914212868500c1c4002d018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 837692428 1250 837691178 837691189
    0x50f0715050f09030a080706090c05060a0903020d051507090914060609011b0512040302181302210d030c0815030d030c02120301030b04150c08010303030c020c0d0c0603060b090f 78
    0x1031440f00202143c204d040c2c1903c40984030b03400302c40103540c059107030321281c0c0500c00e05500050003040c0a80b00ca034541205100c00030120b0015000c001d12451801c2070b0f200600004000c3d0408a040704120118242482400900146094070900c9601420405090425003000080510591020348407514012280c0011903010340d290a800501403076100c0210007143d002c02c14902400800b15085d9542c508500420880180c01501c017156800c44404111004222613a503e2640350306440c02010812104003620002c010300100c02c245200d068080c1c803171958150003140310254141c607007801c2d5480b50f00c01032840c10f4038100c505030950311040c4222909071207507001c2144400c1d1841502c0c2c20003100000003003130740d000381c2c41a41d0b407500d1f000900050040d100c405050b244810307a41040b50a0301c002c00a04074440520019060558501c0700700d001c14004d204014003807078010159000041c0c181b6000041d59000c0c01608002481c04401003520030301d01d01214500d0500400300007100306810708110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 837693678 1250 837692428 837692437
    0x4030215070c052806020601050f030106120f230a02130507170717090d020d0207270618200f0f030705130329040812150d050f0715050f 60
    0x84c3c180320302d0390700c9803a6038103003040f42c50292896070b0241246500d06810402c000c201c02c1c00d8503209034034010080203c182c2e0410a5000789901840b1440c9491003803c0441c01c40c2c0c1e0b8500380c005000d28913201c1c0c0b1a03101000c00c520540d58821180380b1400140303801e0100032280100c2c4c411002c200c0360106000300101102000d58082c800d450120b51110881014096404c6c0a80d881180b1343e00440300d110509805200d4480ca241e01c920040140c5c0d850300c030004c1080c2604e1001d2800403009445403002084080d0031020180041c41b0f003054018142900920040c03403001c60b90b4003007150801c84048504808000c840403040507405281c207142d4070902c5c5031400d5102800700400d000080106803000d41c40007850000444c0600ea450841603100718000b00c1140c0003070104054102c3c40401c00c000954810255142c401480103110030340d66a21864001e0410070b01805540300d40ca411059042040c001641d2030050310030703402d0300d0207140d0f0380907140c000001c141c440c00003080c001e10070214090719420251 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 837694928 1250 837693678 837693709
    0x406050604150e0f16140903010b0d14010e0304081f0e060702031e160f15020f28050702091009060b0901021c0807030b21010204030215070c05 63
    0x24a800082e60050900412580040112111581001241c0d8903a00d1500e52007003c14500c1041a013007800010180d10b0215161203240303030045440d000300d40342540a0780c0004000703440c80c0241e00e400d0500e814102402c4002058542c02c1180300c400d1813002009a40031a12040300a01002042110b044884091040306021080e40c1e002d0110710080d0400c00180509040d4000e0f41d0350302040800c44140782944a0910480034013000188031708607003070001c5400c0c00d030020000b01201d1038500e8100085400c01d444005864000b2030140c0e042c3ca00c0d8802041564020105035090b506040c100c180b59200b08100301011800038410740d00541028903e84c2e0303110011448075601e4644a2040c04116020f5403c00d0b1042034000c2040c00407075804100920042e800f200b0701440404140c00d0042c40b000000f443c40c0c04041d120825840143c03138040320f87c0e1814036021600d400000e41848028002d4025200592080d480014201402c502c107c04445005030440590040c050070042030068100c41c83c1402d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 837696178 1250 837694928 837694931
    0x6130c09091d0105042103090201080601030c1b05030d0c03140114030f1f060b070b070f030603230105010501080f0c0a0c0b0403021e2e140a050f1803030406050604 72
    0x80b0502c400288286481188a98040c010025440d5190a10722100b00e104409040c604981c0b2000360781c00c080c1c41984400d09207400b181203246084121104c96200b074001c0f000d9000b03040300341d00708580030000c0c200d2145003110400c5030402030103041b01030350303400c04002c4030042000c4014407111030041c00740c6901c0c02d8050300b00c41e0001a1404003c3c6010084041802d0705084410365601c0c9c40c28500840c80145550340304030b402c24240384c41d0f0740980c0d00050718020620440444681b903041c0240c0140e00210707048800b04012030b4800d1102c40e850f0500e0b0100c6e4189500e0000003080540c01580024000c3d5400d9034115100d6958170f401208a40c000d010000510194039510000540c0d9424824030a500c281c0c06803c0400e0300500300010f446801c801c0004c00c0d0403007040400384100422186050105880d10b81500c440260700c4000180004034090705508002d004012170b0112603008035010309020211400e140e0740d403001c41110070115400c20081a0810404200428255000650080c80c000d00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 837697428 1250 837696178 837696221
    0x50a020a0e0105040605040e030318010612050f0706020609280605150301050705160b150306090609060a0b330313031106070c020d150203010e06130c0909 68
    0x14840c1516a000c400303000c035650010302c15410702d070069100904083e50244408035003020186d0b100d0100130100218050403003410006248250040002003e21030800c00c98401c0760b05040d9200d581208080d200e074840d03120001220361002400a2056071020003402d1404c0034404028402c00f4014408150040b182254402144241c458180914100803040440c48019020705007503800080c82c82c800e001d014098014249001d41c1d14040841c1d00c0b040704161a2340d10303d00d080702d0700a90345100703801d48129810490601360000d110f40c0585610021101c0b00d40e101d81d1807000b0f07902c0343c040e03a03508506005400249180500320000b40e96024001e8135460240b000700701119a007017143c950004278403803181d010a054105400b61244800c900c0602000e290881002d021070007030800003401210140044418020401841c20140c0d00b011419556035035103840780b422160b02600c501e03100e0810783e10030040512452242d16540545610340c1840c0c1c0340f40034005001082d03141c81c4d031001d9007100031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 837698678 1250 837697428 837697433
    0xd0f050c061603030c03091e0201020f0a0b0708150a0e0703181b0f0e0711030c01020c070303090806100e070c050a050d08060a03031407030e0306041a0c130909050a 72
    0x740506000310301446404000d505070f040040544050b004c0d050281441e0051100110342400e08414080301008041e0184400a100407407400c07803851003241d014040c04048500f0010000340203030142440341c9e1402c0e0262102142c401c40040f400d0517060703020b00600001c101740011b0b44040c1780d0121403410000351408942c500382007105030115088510001e080a10f02c420001e20010f040a0841d03120400e14036418000580c0d00803a014096800740310443c440c502e020002001241c80d5900c05c40000d5444481030300680c0d50719603503800101d010a0004401107a0708000040c0a4172070180aa502050545046400b0707044d98400b0300300408010071481c54802060b0208141c1c198035100d6001001c418041d40e4005091a01c06481c9610a1003451000c00100380d20584a40400c0e4600031165600c4405140545070909024021038150046008000a00960301e06600a861440b00707580030320340e59004400d44512a060703040c80c0c0e101d040c41040c441e0301d1150f4084a045071003141261001100c54 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 837699928 1250 837698678 837698689
    0x20d0609140f10060f0902030a200306030c090610030b0127090606020706140a0e0418050f070f180f020c031c0b151614010c110c0d0f050c 61
    0x8007640c25081d401040500b50510007000107026050a0306000c03c20541400400b0340d80307800c00d00c04d08100303a402002044000c5c01650000030079845180402500040030003004c489504102c0300244030b8003640d503165450341040f0505602c1078100924070242881b00b10381c140e0060412148550400402e904c81c40303031144040b0104c01001040822a0705198506140241511421307008003046400c034000c100410354201c0d2124a5004403030b4240f603121080000b0444055910451540d84242040c0f540b0544016000c1d0084507680240d0a541c1848a4000c1c0c0744e50740e020920520000c0c0c1c8692a0811000703c002040540840b10180082070201203040703418280d030892403c43d101e94200081a103c0c006400c040c041110004010500225007000002008040d801740c080000000c000740450350200910203070055a0781c81001840c1194180a41c14020415242c0540200700c0380031420320340e5000013a101d48038000003000c29405142503074820b400d078406080c04941e14030074022061080d40c2c45 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 837701178 1250 837699928 837699953
    0x2100c02090c1b030c03070b1513093e0d2003060a06140d03020c0301060602010f14010b030406090510091113020933030c1e040b07020d0609 62
    0x40c40d0a5407108044442c0140714100e004803c0d00503807041054140c0d00b0f0001c01510541a0480c14094140ea204407040326038100c0042000d0b48050900602880c20b2516800884007502989600b4110703200c2d0050502e030500e240040c01803100107281691801c116681c000d1842c07510141005183c2525a6100c1100c40c80d80f1400180721016a81c42c40981c1c2401c10055612105500003071100c2071801c04125081074944030034600a00d50a460741c0185402045540360016010b002007106035520301c8000e00904981001d220350a090808101c02c00030401d401e54140d80b00d15a0302c525607181d903504c2078000c0200000445030350107418594425208948564078003c0e019050702544804140e00b002400618240d20081241c0b060100310001c1c0c488248960840c010048a45030081c0110603c4a0081d50b0402100d015807001040040003034002d03020340b905c00c040110724040903508100100b0b03280941d000c1e4065860b41849400003606e0a407105003142406250b0006000c04a611192045100c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 837702428 1250 837701178 837701191
    0xe01050f1e061209010e01050f0717060a1d190908030a02090a0f0b040e070f0c02010806060f13090b0d030219061407050703320c010605030304061805030a08030402100c0209 76
    0x1580c0c4000606d031002070044640c40f01200c040d01c0c0c038928002c18094003c988501607a000700c4c02080018040703494204800c40509842c0201a102036184504015007000894800d1442c0a00c0e8455035484502c0340039a040d80d5030f00070b106c1801e5075207050340300c4007e4200c250032981c418000400010b43d00050a202005070003400c404503070b518140081c0b2140c4080207044281000801000c1041c2141d00c582030110003030f8246000c501c0c40d05d944d00050750602030420f051880e0b00340010303900d100704020301c0d50340c084600424051000c1540e42c401c002902503002c40140268000c4209000f041603010311580042d44900c00014151030103100d9a00000380403900c403408030700e0004021040c5a0007a0480e500c521f550040032520005441c0150b038600d02c0c1c2d00d1084004c1c2c001042c4030740b1103030b820b410038005031901034201c0c1c1e1034599602d0010001c90380da42e4103c0b494020b60700c02041e2400d0125840c00910b4100210610310f44840d824801c04604a11101d002c10083c0684480165503050410340a02c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 837703678 1250 837702428 837702431
    0x204090b09070506040f090203041106040f03020315010b030112031b0308070e0f060a0c06020408010911120303060d030e0420031e010315050403090806040b010e01050f1e06120901 79
    0x28020303051a203001d00356000f1501c1180180000c00c4642c14009030071094400c0b000026880381ca862404a048a801114555000b040810085061000240e03070350b0440f4000c5040300d001030b4040c01010491079082c081c44010324020001405440184176a8440c4e0520a1409164840c42d881150401541e81030381180040c14100c10b10071a550f0002c1d02d610141c03801c440407903203041040d000420900c41d000c0307000c0c1848440d030702d240c1c18041c295040c0ca004140075402440940c04c1498030290313051034080203500c16a038000c1444180381000013501d2040c03902604002c0600c41c2520144d4040500715102540680c8034841601c040e0140a1488519010800c4107900c0c0e080620711072070302c1400246a0101d07560300c10f0041000c03c074080a4101c68020792980024903481e03030f0a00f01d42900d070641100e01c0742d20402c0180f00030030a9280b40c1c1070485a00d2051418903076202e5081024400c0d01c4008958400c0c003c09460884840c0a14000d001820050a252905050391070904210300c0482d50300075a83d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 837704928 1250 837703678 837703681
    0x30109050702010e0a02040b0f03060a050108120406170c220602010c0e03060408090619020a020a05401d010c0306050904080a0302040308120604060f050a210204090b 73
    0x295250050316001442030009001c0344c3e0991a40c682d030b6081c0024040c0c4141d80764000d020070307a11030014482401c48090141c803500e00e80150400c01412007881990310324844c4080990551000c10161025180180c0d01c246801d8410303c003a00500001030042025100308009210301000b6092041e84901e043c0f040324560141f6000d80a42110303030980021040c0003030030041603207a5401040c1d103584240e00040454490a00f040403c1c8940560741c0800750500d913100011120307680005a602c201e034400c80d9901c00c0c0c41e03180d9041c4018800351209500100c080c40c04c42e0f01041e02030040701d5014414032000002812001ca41041c1a60042c80480d259103241b4200141c16810078000c83c1c070b004903181420300001d840c001c04030703100d02e40013800909580004100d0900042c441c1e011200215000044191683c0442c80344003205102501e1180c03180349000d100044883d021400c10080310f900801d42004107151241d60f04039110740c022612400390360195200300590b220311440188600071007030001103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 837706178 1250 837704928 837704939
    0x2092a070f051203012702040306020a09090605030715030e011b0903030305010e0601020307081e0f0c010c020a170c010b0a0e04031b0f0201030b0f2d04051e04050f120301 75
    0x10301103c400740ca040e0300820030051001c0420401c9500d406200ca60b8280e00760406114207000902445e08018203030341c0005590115564001160010f482403003204100903642d440806075640c01e44d00c241510320072081940810240294000c41170b0003005800410380d0035901423003a00350b0307000021510215400040c28001c4c154588142c501410002680e90b90034240240040e5580c09191001000203000043d029030041d11600c401021031f03421f240c2c40d51680403020082086410611074803090350310380400d140b4214800036102c1007082e0007510b0f0090f050b004c1204072030301d42c3c410b000c2d1603580d46d02d03102485581d031590032006000385042c104840803400d0600e001130a100005039031b00700e0134910100d29004a841640c22841056090130005010708002012a400445036110130794800480712005014524005c0d100f0544101a00c8a640d004141020482110800d0701d2081c1c403040640d018084031183e161001c0c0e0040c1c05070381211141000030b00158079003013a28104000c683c4020004000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 837707428 1250 837706178 837706183
    0x10020a110109121101090f110a0b0412021315030215040b04120507050907090519080109110310180f020103020405091e010609051e06040929040902092a070f05 70
    0xc1180000207100c072080c0c5490b1081f08414101000d080407240b10f030148550741d12040e0b89401001900e14064450740c0e02c3e1618850300380c460320300342c0c011403207000c400c00c2104aa1081e0031701400e0810303d226030f050441c1c09100c9800000598070300b42440c20007000c030307044100c603000d04014a2040c00fa1050703103105243c12800c0044aa001a016000a105100316242c0018808050b510251031184004a20032592001034031240d00c9040a075282c07012000138001303c90891100c2034801d03411982c0b001440d0400348102d035068001c1888071000003441c5000690142901c160b0140145800b40c1420348030f400103207101006075024030b0303c2c0d40ea00d80a1703021071240101e40380c010a140c2c240413440c0784c5040042950020f407582080000c051100b07121400355102d400340c40240c0b070301030000c00140c14810f1003104885400d5016407000c22040000e842d46107002d0141b282001c3e40a400102e19407030302e5025900c205030b01a03011800c158951841c90401041e131028201a0b805840b08403440343c40380c20100e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 837708678 1250 837707428 837707447
    0x110c0f101b12020d0b150703020f30040302030105010f14030c010c14070e07050a080a020c0c01120603170703081501080112030905060d0e0d09030510020a11010912 72
    0x3000e1201580d40d41100c590444224070b03454418002c056919180410f8400c000d040358030031181e2226644061401a8244d039001e0b091584c1709400701c40700e042c540300c0a40e46d500251240c0007000303400038070384014800041d1030341c00c4106c0382071848034240340e200c1d8002400e641090b00034115a4440c11401c220281c94032840c1040040c081d00500220f0380b4844c0002c10100740c07980041c110454501d501034108400700107940041140360800303900c03030409040062041e40b24003404400a0781d190042524146c0c0c6100b11064100113030001d2141d02807480040d109101c614000d22503041c0c2e11310300000480c485400300e1082e1483c03c4c00349640c4802c1840c1c0540420000303003200038101c00518900000380d800607800c0d07064a0503c0012000e41d08240360403501003509402261b0010008181000c910085130802100100d020040c1d5402418402e01240d0301842440041c05036031100d2084908110540e00601d2840c55528098515044603070545094030704541040b039200070207480506841d5031201303996 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 837709928 1250 837708678 837708701
    0x90b1807033c120305060303070b33060a0338010f0201051003080d0e0312010603060e1e191a0405072303090c0a0806040b16020d03110c0f10 62
    0x9004200b507446194104404a401d1010f140e0b5800c041005681c040003070b21066640504641001c0c541226501d01c0750014111090b4412461070b070018401854084041981001030038090500b0720b116402c5010b40055050892420b070b01218040e180c2584e00a00307413860b5119007003180340000000006041c0c03401201301c0021a40b4020910201140f19105081269084410b85440d50f484034461002030000740d401002501c00001ca491120080140340c0d03040310020b8408000855540d13401c052031a5040b10101900e9a03882d50b07034620a9189015147c00449455111049200d5990120708540401c2da1100361880300351031169240c5401d018040d400046407421074040d442c500502151503481c0310112042c03c0c000300000301c003464200880242a00d006103041062684da01c038052b00d03140156810798041180b000012141009440706c3c403a45603c07540200041400c042d0214001c1200f0700ba45081140e0401542c0300c0500c00b0020303585240c013180041e202c540c0000000c8021500041c403030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 837711178 1250 837709928 837710033
    0xd0c110f030309071a0d0908041206060e0a0504020105034006060602010204140f060919030c05010f080105011805040c0215010503010605090c07030504090908030118090b180703 78
    0x5010305d04603101500d9613503200e80d40101d00030449141124080c0500c2c0c000714200c030031142d1241c1c00c0c0202034106034200c803988600340701c5a483e61159801a50390455020b030100d141080825000600d00d0210310300d65120000031505002003411002a000c40541c442c00c0b80c816852408041c41290300c00c5100a10342c2e40000c41ca054a0b14000304018540c00f404588203030b07a40761845685032290300c100c814280d4012301c885045810b90703d191200306890300050350034604410700030a00e54003485811807120b03890f480b0181d0716803800f401184c20300300450200750003060850b000070380c03900e80b40207607403c02400d0b030040c069064120010340c002c220140c0c0050304c00c0e8107000041006440303c0c100d0640000029002d26600c100d0307401e040c0d03628400c075445401c0180c604101c210034080503101075816502c00700c1070800300e0031644004000b901c0d15424044c02105840c40484d030084080d281d4200b086500c071040d2001c080c0c1d00c0c0c4400384000440d880b41107240c1303140000b0b402599401010702100c0d40b0140003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 837712428 1250 837711178 837711209
    0x40309060c030e0301020406090f1508010b090d0f050c030d0503011a0c1c020703060b060339041716030c0902090622031e0201050d0c110f03030907 65
    0x400420600162003090107010403290700e0001e01d44941600c01c2982005002503580b07544e80d80c1c006100482501c22181c009450072000700781042e6141e0103030655000c0d5551440683d0030b003094200150300030701d003c070340c04a840c0c0c448000052907001d40168a0b030041d00504a424080300606051060040c41c40c01009010001448a4072501205800101007600a2174413852561402d81c94000c09040c1d4800111140b00c0500c819940000e5810980303104400501500300c07080280001404240e40c00111b1080034020341000c083d10816148000011a082034035528500c1741000c22030b84150083c1d2803000c144003040004840400514261031031080d0600405440c0d51214201c4c440240141c5802c42d4001488051a503620300030381d00000e030810700f0044c00c04580039402c94003965501c0111502d000710a40418070160740c5036000d00315501a1186803420305810118401041d1405a100c1400084070040c20a1841004a0300310040c08400440d500d0034501c01d0545071110560000c0803200764100c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 837713678 1250 837712428 837712433
    0x60f040b06040b01140c01060b0f0c0d0309080904090201020304090f0608060601020606090a0c172503110a0804060e07180509010902011409010311161406060a061404050a0b0a080f04 80
    0x504100010301740b0117000c0d1100304d01c9422502618556025464420011445541b40304912008010f0b0030020012204080c00f00351045e0156a50a02301a000420522040d54241407642010480c24814410b40745030a0722240800103da07140442c40136202c0e9611801e2000000130040ba54101c0d2090006204605e0007c0c006060014004e00d0420640d031038040c0e0700ca440d4050b41c0c0f6800e4180407002c0c585010314220654610040d19045442650035203120450441c5000c0d104a90f00c0402891300c07545007200da19825a10303154042e00441e60705548169042c10140c1c01d01c07a40c4003420405070396181d044947d07003100c4141c0c0c0c4090f0941c10984d26114500c0010303a0032031007402c80c052100340442e855405040040c1e004107055070f507480020303400048404502e0703510704130409041c6c0f003041c1d00b000ca0030000c1d28540da00c260031916035810419505090002c940240c1e484107507141e0440d80c0a1a00d03817504081920741409900c020f91030300340420750207522a00b2640442d403194a0040c04281483c01c2d8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 837714928 1250 837713678 837713687
    0x60207050117130f14030307171006081807050d0606050a060e1804020f040504112418130c0203040501090e0415150e0405030702010314090c0f0f03060f040b06040b01 73
    0x40700010441d0080740024410005e1900b080302d4200d074100d003aa0344920340404043e00350300908030030781c240040e950002000548002a0041514400c3d690320445903a1190b00285402c0060071000d1140305049001403d9900c001c1c2030400148100c80209501e4a450284819034416030005d07814481c44944040003601c0300c9180c200700340350000203c0d0860300d6a00214202c603052480c2150420b060004100500420074805220f0b8001900d18050032800c45440500802d00c480c04186003a01c10030034244100f8100c280305070100c038010944022031070301480b460100c58100d040c4001503000801d08101d2903800010100c02814003a003425184d03d0707c0d640e8220841055022000e1700c81d500c0181c2d0303500030f449648001c0600302410242c031480c00cbc2410015620342003503800b00c1c0000c0c10004a5581d114009000d039000710b01f540010038000b2192010462001c1140c00c6054004074030360081540c83d50204078190040100c040d0110840c245410042c4091400401c80c0340290b05001d012807043e40d00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 837716178 1250 837714928 837714961
    0x19030212040b07030f0917060f06010e03070302040504021801080d0e04110d050712020406111c0801030f0827010f020d0207030f051c11010f090206090118080304060207050117 77
    0x510b4030036180c543c685c0d0180c0380c0f001250004445070f03106000d00c00c920f007800502d5034000c1c01e68461020003640ca29004644204e0030034030903030305078019581c10001030505400c641c1e040780c4010071962030381011084064034400264407000300c43d44041204000c41d80c02500120303035000280c2e4103001c0d40d000c40050300d140d0710501d6940c00042e956a000260410320500e2082002804085c1c295525541c40030010030100007908031074800c1c0142d41d4000496030780c4016581d5007410648488165a10f161211030403640342e80c0094503101010003042044000c40c07400e81410f12030440703202008005260005000034032110100095600c0030b000410180c6d00040c0d41011640e01044c0c81205404910b040740c100403c1010141d030809000450020f5141c00121175004109003000810180c0b028070086400c0e920f0001010790006001c1000940383d52040f919160700211614401c05840c2c0d032810014a1940103a1121006070016a03040c0010b43c7e00100003892034046c10050040d03420004071002007601d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 837717428 1250 837716178 837716183
    0x50105040518310b1e18010f0204060f180620010e0102070c03021203030105060d0b042a030e030903030f1e1201030b0c1204080c010b0319030212040b07 67
    0x6510001c2d00714203c9680c0d6803444001d004512805002c2c41e001c40d500d0070100c103801c0302c400ba00d91300024150032008143da003a0b55000c0c850038505445000d1041654404229561099503c4488009414109000801c0207214542c1d50600e0784641c0e88004040ca0003403200c00d4540c800300802008807039807101640e204c00720003410301d141449040c511140140719241e61000103500201e01c120a0040e41621304e0220b03402519015080000e034202c0d07940300d100900440d43d014a00784403181c401740302c5911400e445100a8000903201c141405010504100c09428400c816010a40130107415410b01a007102e20310190001c40c02d003a51034002944034010009008600301380030401d9088000b034501c075045044003140120ba5500d0451000c030039600310074007040d40c0004118001c030b0010082d190494001ca5011500c071040d076200da9a50b040681c2c080981c5c8a0b0039900c0301524021a03809002081c5503840f00031000e44c4021880c90040e051000c96042840d8100c0c09001c00c10003021002c0c01c0340c10f804e6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 837718678 1250 837717428 837717469
    0x30507080d02040f2d05011809090507060f110622050f0a060b060721093305072a08011a03154008130e07120203040f050f03030a060501050405 63
    0x110500750b412314209503442003224a040610302c400b03012010691500741c3c3e21070365428070080402c6105441d81100d840c4482c169920400005140310384800720181c9002501840c42d10302600e41c0c480518050200031116016000761034070000304001489620107518081d0b947ca428206143c543c4d880d00300b58000b445403c441e17419005200303188a0080c07240609810100c0c4183d00c0c015000200130b00000070b00c85603034892000380d44080c00b4010b10a072800d459101e042c050344211100d04644044d40d9210f5082540340c1114004120352030300b8010503003c119281d14042d208a5039100701071414820303046480754055030340c00f03102e001d100410b24030402050341010410030740c01c0110380c00442c0d0f80250405036503c00ca00340000420403010300405980510718a050290b40d107614040c8000c000c00c0d1000c01c0031031201011410031920540140da8400d00682c15080b81400320b40f02c06040c4003040301c142100c0e0700000b080210103a8248a040302a2400303203003c5050a051002041e054405041c1c94a46103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 837719928 1250 837718678 837718697
    0x504050406140426070c1404110f09041b08040b130c03030c05061501080a09030504080d05030921090f12100234030507080d02040f2d0501 61
    0x107064004104056030640c2c03441591900d810266240000552074800100004140c44c0c04013100c50155044903030000b41d0600c10b185840da0700c800c003407042ca000680107911004000c4850b41d07268040c02000c00d00856403583c4074030f520300304022641d0000c0d24644003440703643c01a10715940310b00f025a0250780b00c1d4000500b5100e10b18105031a0380c2e80040180b0940da1140c01004141d84814442c0323005100d00c080b1859901c0f0b5600c40c001c02072158480030f00060210000a01100b80c9401070031890b4003904144e4501600c07880040d060084550000011400010610541140401c002d460100041866800b0184180601c050510840404a100d05c0c00306a98148039991815059603043d583d200701d070307540819650f030786001e0740140c22200d410306d0705e030185458404688000d0394024034400240c424241c20a990a880682001ca805d442040082c0440504180300d44010070140400712503009145150a04020034030040440751850380054403803407603903240c0700d0002e841581c8090800d0542d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 837721178 1250 837719928 837719933
    0x1306080c01030216061505010e010c121b050f0a1101110c040209040605041404030e10080a0c0e031905060106051204020409060e01022d041a0903240603060f060a05040504 75
    0x181c15803400c4c041c22051800c240851610b01d030080c04421500203882e80070072122400015608442ea0110240c10300e000180310a2105104940401d0b424002291512905074641c46603458140d42500030b00c0568802d003511420300185032103030b15464100346016510000c403209150b032219083e50025020fa40c0114103c076040e03650307070415400340034003a0007040780f81605034030a072a640c1e054400b94041030078410f00c91414102044c0c1d82d0ba5642e50703505c80c034440f0740341c2284200c002d00001c69400b041050041100005030780510903250f81410102c040d0802d8078a50828030304161040e404542407204c208801000014400702080d800381c1c0446d000217102825050800182c0410361103491254800940c400030028504103103500c1d861481041000022244030007010361007680552050000041c072580c5000c1800c2d801000340020203425039140e40c40103081c4500c0281150350f48404940c000b010040030307003001c0000700e502881e10140d010840c10180b001c61400b14403030003003a00443c1ca0f200010203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 837722428 1250 837721178 837721207
    0xc040302040507020d0e0406050612130b040b070801091802010302070224040906090501030b06102607030c03050105150c0a0804090203060a060216050915120303061306080c010302 79
    0x2190040c005010520301030400940b521019504400860342601041d4001e0400b84200340c143d88000d00710500c1d02d2441038006d400920300804000d80804040c0c0710000040070b0751a09401640300300808502410710f9200581245e0f416040850542d2070a48613040e801c5141c80c0c0305690b50b8080c00c00517503600803400454810107602030085c2240041400c80350700c400b1000c0092040b201d4165080140135290900f210580740b0030321000d0104a8800d0118405180503540203510a1803820305280d1075040604e0260000c2c10b0b05840250004c207402044000e581502900b0103460b4203103030070089507050000241141410b140750951001c0702003000c0180010030405403144070b801895180c0c4465440e03002d0b5010b903004540036800307100b4100d0b0016410340009a146000111031311214803440c00d000600c810035000901c1013415503a1280c10030206d440320204900079808060155a80749082014070070f50f490000408514249032040802c1002d8010480090300c0074248bd01580e40d045c2c1410301c02 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 837723678 1250 837722428 837722437
    0x312050603120d151403010b0105131e09050c03060f030c030706080712060b0417060121110d0303050a06050d03080a050705130807050301050a06150807021612051e03040902030c 78
    0x1c82c03028001307002042d00c00344032007403045000f000c40087c0000d05069004540358002c1c2031000322030b494928000d00c00024250440d202d55252007100080442d52501c0c0a01540c4040e2a03070741c03080318000107001943c200191440b4a825041e402820107001880119540d10300034800c0d40108004000491103d5104015090510023090401e224040c2c440700c1c0a52160300500c0703152106d5241c000105107030800422107030304855034407032000c0c00c070780c4080040d0341c650152180441f2800d052285100710b546d611040301c85c0d494081d541c001514607044210708125080b54004620a40c600801d000010340c0c8002490f81c0703c40300400120b00fa440c2c0d000c003580c26010b002e0701c00416925003407000c038603090700086420840750100c00a101d03d8803076010001c1201c03210700030900e0340c00440d04545440d900442049070004500d1040b80d010f8220b0600382c840c840b40c1a0400003207440d0f80d42e515401d01c00200100d880428600c0c060160b106103400c440d075030760b1007284034084105401200003a4908500410780d0b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 837724928 1250 837723678 837723701
    0x10306170c090414010c08010510082e150c06140112020f04180b04030311030c0a050c0a2f0303190f0c150509060703113103030c0312050603120d 64
    0x34060041e511b0b501506050b024041c01e40245600c02d100507800e841414100d0049110f0102c0c002440720244400c18200c512100d10001c22034500320008010710042d0002c41600100c0d500c55509034642d01e000d0003912031050320204628a1031006100d9880d1000100400179412500003d194090314081406081c000f00034995442d4601903030230500c44080351082c4128405c0c0d50800061940000c4000d407400182c3d107030915860140070f204038841c0510018803201503001300702c41c4d2030031450380da810516003020081c140f03001d00c41081c40c03022120a03140602c8070702c08401550800c410701050300a80d480d5100032000700100030015043d240c0c02280c51907400c0ea00720024811010070344190501500003950500203c0c810440001c1e1030034801d204041c5089480544a0301d00320880c0b11641411a07050161014071071065501c40080b500c94544000942c825110704031101160f050260400314841842040c0c6400c010401026640c046041511180c103c0310380b0341c90390180c0300e60707800402880002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 837726178 1250 837724928 837724931
    0x307030c0b0304050d0f0c020409061404060f0f02041d0705070602070b0114010206070804200d0c03110a0308040501120b040c020c3309032109010306170c09041401 72
    0x1c109030958800070340c03103035000e5000c5480664600344c0840f940c0700128100800136403000c62540040c61306410421a040c002c0340040707036494400f10308140d802c10588080710f605030b603002d00002084040c0144149030803550350460034545030040d210070b00550380300031914030051180007807459401802514502504038404540718610b52a02200401c001e014214080d4074098100d8075561000822500c5860642d0b1011955210343e6145600014034180a0f01282d9004201c0d13a069210030b10410107083c091159561444d2540c280360040ea000002c14900800c09100d00348003091110044400b154421320f032290040c4003a000400040c03d00c41c2c9926805402c5c0190324004590001e800c90704a501243c0c1d441300100902e070500c10220083e0f01106828a9190400b40c11110315409410109000b0303064400c0385510103409110110a15005001c1d59004640c0c1074295170b05100e03100c0030300380003038a001c201c05007079400607613400902c2d002ca4403d041100008040060b5018031a4042094400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 837727428 1250 837726178 837726203
    0x80303010605040503010b0402251416140d030f050a0302090a140a0e1302012601060f030c05120c0702221d010b15071407090c03230106030209030703 66
    0x70080281d84507216882c82076090403e0010b0a1820744211001c00084802060b079505004440c403104542011040d00c0d80b01c0781428030100e800302440025049684422040c11090401c5149407008a0800340075000d001110310040c000f0340c0124400c2000182070400b40e4071202401e42c114040e104014209030000e288450020780b14880303c001c9a5400c0302222400d6a943d120507000e012030300212900c8440b107500c000c4140155008441202c8260b044c1010f12120801d00880a4040a42a440500010582803801005070341c0f40c46003c2e82e00300d5503c1d020740340441d00401400100c9014020280842c00003030540d0031960384841e40008202e60000d5100a4600f0f921100700030102407040e0b981041142001595040041c85002d8903140c00400300040395901c140d002e0302c0340c0c00488040340d49130344406403224030103c10444040201241400820900402403000301607600c820b10504580220100c8a8280740d420b40d041410343c2c28a1500603180c00c20403000034900525680042c1c0301612000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 837728678 1250 837727428 837727439
    0x5041712070f15151a040b0a0203040807170d050a0201020912030a020d11280614010303090929010210050f010f0503030c0601181b0e12030c07180608030301 69
    0x300540715207000f64050780400703640300b103000141d50325504080105046204144071020400c84040c80710440358014034100f94441d10101c0c62940401c0074100942d001080400140300c04000043c02390070f40c840c1b1038040c8011010704603506d41c01020410300313109002c5500d100c454400d50688403508801000c142100c241307e42923607260381c0003041c410f00500500d03650400c064000c4642c6171030b54100030700410b1001501d030021001a1040d042205c041c0c01e51000c0400443c55034010800307030075401c205500503549140703805004026a83c0c0a0200c0c00d04080780d5051640f02041448030340000740200381d842c041c228004030304005c400000390080e186010280090100b0b8485243d050b9132070040308a0410b91200c04040d540c0c0101d80c54480350b5401103005100e0105000c2c641c404c10a80c600d0040b400e2203180003001c6904021001d4040024490f44500440345401118030400c54a0400510319014290f21025210025070003082e80c10603196880c1c2036a0803056010800900010090ba51a0f50310b50 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 837729928 1250 837728678 837728693
    0xd0c030e0f130f0b030708030d090f241a1815060a08180a0203060703180b010b12070305070f230c0a0c05060a050403020d170406030f060f03030504171207 68
    0x20800312120b41d18284c0a84000c0c24001426410b440390080118104401d403880400600b1120508072490441c0f520514005000a40c9405000f107003086090308a90804035444125134001c0340c00c0c01c001410620041880e04c59851011a585046910754410f540d1a6603964011171442c007400e40192000510703884085c2d124a010b0b0140d0050380e80784014601d100c011540d81c811040020754150000300116039031030700a6005211b404074080075055660340d19181c01d240303980c00740e220380c01c45000068041c10300361550b1400b542c40151403d007000349051540c401048400e5040712002400740052402c00c0702d0380158040e00d50101c55200e403c0d40c810307003e103006032643c1c204801180c0c1c030004100c0200d01d0303240000940300b2841d040c0ea180c3e820285150200008100300c0c279401c2d10f1030484100c01c1413000c00c04000810280000f030b100456003070008102c0200f20780c03090b40310789041c101e01e4030180700003540901103800300c4821203607034800f00d130b40580c0ca0340c02c0c8238003088103c001c20b0f800182e603000c10074403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 837731178 1250 837729928 837729941
    0x5071e03090b1b060f010b0a050a020709020f0703020c1801090b041e06050a0b0307020c04050a091b21021305040515010305102f1c0f0b0906030d0c030e0f13 69
    0xe400c103844040d110703c5c40040d4503103002e00580035110030034412204018410000b8040095403441203844040d03031150100d04903800f5054000a40d0400136140080c50340404c522039402ca010780340404d082a043c8400b83d207140c8180112030441e0f844008965290340d481d08840d0482c00041c0400f400d076080c203d0510000c00d064410709025040600300011101090300c2620702c10312454015000f88000c420421008010040100030703e240e444542c0404980c2014110a81e8401d415607014242e040a882404d44204034140390510801000380303500507103a4080f0303192140d260500c081060380321440c109040c1f81c52480000010400c40d4000400d00000140e51035600804000070440c0c0000b4602140310410320709044c81524800c80010300c2c00c0800742000340440a02580790100c070708000d4101c4800c0d0b90084100036400382e1185085401c42c60800c0d801c80d00188110000c01c8076107036035400600460310b00140a070074405030955000c00b903201c00e41c5072003c1c500021300d204035003e1f06000282c001c105 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 837732428 1250 837731178 837731227
    0x91e020c030d0612050601420e0a0803090d0201030b03030a0309030e0a0302012f150118050105030a080f21070306090c0c14120a1d0105071e03090b 65
    0x2c0000000344900c210031340740d140c0d940100203406030740c1c00c0080701c40c41e20790344500065080203100c9810305a1619440840d100116100c0030007601483d0710401400d004003040100d2144007110170800c0140c90010840e514400c0c241c0b1396100c2020703a0300050b802800c1c4141c03980d8040c00006602d0090540c140e018a526620070b031500207520780c130b038070900c418646203000080c040307404813106020b142d0100d140300700d00c0c015071941e14030f1040001318203605241102403101c120340310a41c01400710b040c0e00040741d121001d8070b440400c404d41c90007001982d5481c0c2d988000d890000300180f00c1c1e981d0384441d42200c01503a14203050001c0001d03403900e40c008000e0100d810200107072401d5804507003000349000f0b400014140d03580310200c840c0302d92205e00044030003903e0194203210701070340242800c02e04400f80007090000e450300309134003504282d01c40c000c01030b000000741003144c2003008000240a69191480a6544078034468050000c4e140560314000d150304007940303041e4040b0340940c01e0808103a1b00d141e41a0f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 837733678 1250 837732428 837732431
    0x60c01020726040b120411060a021509010504080f071b1508060904080307050d091a1006090608010311060c060114130e0c04020a0918140f04020109091e020c030d 71
    0x2c064107030b01018081e9000300641c1200c03c12413108101141c00510750440c0c007902031042d14032590400160035600c80301c40800560080c16680d910000fa0398445a4070003030f5040288813600d01595200d526108001c0c441a461501003040000e2100c0c0c0307460304400b008040070b200901512100703070b100500710150940340090f8009000404034146890318500550340425024216220600250342642281d221031841c0e07a520304503030340841c4401d0040700000d281301c0100c40450400c100d2000ca01402d0b500040140008000f04101a82c0d00028490440381c000c2c0e0230030300c480409400100030303100d1800c1e00b452600c5114008074002442e000c00009060048800c110680c86078990350080d6426049002c031326800440c407481d000d00700f64006254410191401e420600d4958404154000550401244c8190307070715012a80e803542090320703a030041c0304886050301c3c0c1d1409a00082c4001e010b030295041040d12022541411020469034401d10499000159254107209c1003a0395250000c005900105 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 837734928 1250 837733678 837733733
    0x9040b0a0e1227010f0c032a080304020316030f0f0f050f070603060602071a03090a0b04030f0206011a09040c051314090609010b070b04150c0302120c0903100b060c010207 75
    0xc0d80102044d00311002d680d02c41c00c1c90643e0310b407003e860200c42c41400b20142009901c2307580ba143c00004000486502ca17584a40d00c900b01801418503141c2041001509012201000c1c404954100203040b209944503110b0042c1e0b01181c50803284903000741e03c1c000c1072840f440000c95485000414400300781c500540d002c0110f160341e0b8400b240e90f001c5510a8051640448200710f040c11050001558040c60300412143d851031309030b03941007500c0d00446050300002c1c29101040b480c10383c140007190051101a81207400c0c0403103030fa0316458520943c0d0b00070303128aa4514242055034011015520301c00c000103d00c95200e640c6e82541d4a00034907102840b07100d518008002042072170b20301038660680c0d40d100302003410865682d50f440062000588195582c80c02000c0c4d00950800302e00450903003120950700544c031208003001c400c806110182c100070b000d507414800e40985440005010602000380c007004900741ba0034501050043c8100800c0c03180950002917204148a807100307840385c0340d117030308200c04a00703 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 837736178 1250 837734928 837735007
    0xc0e041d0c011806080901111c050112020117040501150b0a0207080318060f0d06030326010315021303020a0617090d02100b03190c0f0509040b0a0e12 66
    0x1e10400310903c001c1d02502000510440b0f1094545a41c04902c5a000103507512107840000d8903034011103450700c0c100031f0742040a003540d29240221030041081c07080c8100c60f01ea1590004e000d00d1201c41d00310a4100100c1c0000e8240320094000c1c0c4989070748049264000d42d01d4040e00e815542c8001101009440b45060000d141c42c1d001086501c4103045c502e0000d8181400d108220b070307a43c0010746401d40c9180501c07a41d03403101c40b0740c458840214030030740b02d2851046030b102045042c0b0300b0007418800100656001003010501602c28041001100d42c40180da0300200f440d03060304851150000394000c194100080381e0240c00a420038030150300c0920102c160f599908005540b000700451000042c4c003e400c540c40340e54065001015a104024240c403141c0d00ba084444400c1c8103000819200e001800b130041208800b5080c03040d001e400103a4004c41c10b40f505844d00d07400518041c00b0034140580e18100e1024905042c0410160301d00440c00302c230f40e00e01c040311700400c02003070400b4600036511300c41009241c0b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 837737428 1250 837736178 837736187
    0x9010212041202100c0b0a05180c090406020c1002040909020109050d031e0509121c0516021c02100c02010201180b0403030506120f0304031101140d0c0e041d0c01 71
    0x4a07042c502000d0684200c0f942030020075240440c600c82400001404e40001402540190b03110b540030700e40014542c036100440410812400001c118146c014030b00e40f007125103a030800d80368003d402201c090b80e103524103c2460f141c042c0081c4c130800110300c04600800c9c1c2c220380380c10100006000740c0e00c201285898000b0843e90b018801001408203130111071034503416030b2448040c81c42085604005040c5080c0902062204a00e5102c0f07051681148480c024415540003084801a00d6440c0c042d003131100d100d0100143c044000d03806031140452124144a521402d607000141e55405014003140441100d03001d455080c2d5064100d016508080811043c100842519008540c00032610401510341d80c4081c0e000303010141c66141c0044840041091078801007226640010211004560b103501c3c50401940c203030000b1501c0d5040000b100030959404075904e0984800581c24000042c0b00c1c5084141030704e02e113040c00c4002e81c04c64241200b141407a00c01c5c03d10100548900c000340d400c26641c902c01100d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 837738678 1250 837737428 837737437
    0x10180e0a0f0b0a060c05010b0a0b1b010b0120010e2a010c0b0402090a060e1305060903040f170a0b040c030204180302060a0b01050c030d060f0f06050702011d0d030509010212 76
    0x2c3c0c1008101c03a00b003000031300c540480380c2c2082c0070303000000b0040c480c4008102c81c030040d40c00040d0803800008140c40d84800b50003005a5401d0660000c21481c0c9084000a1004201e00100c46450b0700640004102150a60002c06141d00760350032a1045104803000e441200b0140703942c0035040c620a8206025540100c0180e211581c0c0104403000c0782c2d4643c0c0c2040b28086001e400c0540342986c8110104a4440c0005282d0061400c240c41c00804c1031246006c2d07241a800818540c081d4009200c20040b850114842e5401d0310342c003100f10001d4000168801e45440480718000d0003210304174040c0f0003801060050101034038000d40d42400785c6096034000442660750a64028016801035002504003042540441404031051500380d2412040441c1036145030450050f183c0d0260b6240400c12040312105607950042100485c0003908500d00000a03249000d04134001c1d0500a0404014849500c2c00306480b42c1224010904030b901d00b581d0070010010f0304009a0710f030251007450a43d43d001da05940070344 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 837739928 1250 837738678 837738701
    0x809070e1003140f12130f211407091b0206100302060a02070e1e0711030d0b0d020607120e0f0f0402070515090a020901090c0e10180e0a0f 61
    0x111101442c41d9a55040f018820760314210600400041c0c000c840010f22142c04030900c03140d4416219030742c0e00504082c11050350301c4415010481032040210740c13040144458800b030300000c100b242480a0804031840200062400340728000c0800205241d906540048009102c4aa2880a807220f110f41643c0c2d6a00c141e8062944105000c410001807a051004050080040c8150341d0300c66030355043c03414402c000ba02c1041c002451150015429882c01c42ca0302e601412515051218009107103c0540307a104800c0b20b81000c076120459040d490701ca01040c0d0490a502a1225039205510706100d45185e4131080c0c0240054000c1c41202c01c10707d0101410060902d002b4002960700302d24000300402980805003c540a010b00c101001102e2849004039100701030000141454181c244104290104145c0012085510b041d6001c04031682c4602e04010554040c1c41c46a40b03198800015107074207000d41d400080c40c182c00b02c0042849841100c040340510000c0005001d604101c141d564141c8030885c029 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 837741178 1250 837739928 837739951
    0x90b070f020103060b0d0902092a0a020c06031f080102042706321c060e0a02040606020114090f12280305090d0e0906010e0117070809070e 61
    0x1500041009511000c10480c414100042d51a41d03616500e00b2682103c90507541c810380e180c03030020550401c164426800814108110846e071f006141c03078030101d040410002e80c3c0e042c010500d0b00b4280e00030040600700341c20081000d40c803441c008003031640c40b400c112803030075500b0030221000030340c2ca00c14000e03241940d94000c859003c2c0c090200c2d0040c980040509100c5072140c40301e0000035903c031402540360301c428140e2001e100080e00c41d054004103400f0780c00d015000310303510107445031404c51590509004a40c00000803a4a85c05c0300751040c54001c00c2d05020350b10034a440341c009810350701540800070784011108402c0450790307580d04194881c40764011a81040d00050012820568044001c01d020b00290303108183c80030584044500c0c07240303200da0f000e01080d030f11428096600e02c06c01520801c140d8074a00107828010050104d4038225000e802c81c4d0510540e8111404607a014140f210010710500d805071141d072401c1e5900030000314040c0c403101154091841c01040130b0324080c1d00c140c824104c2c1e000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 837742428 1250 837741178 837741187
    0x140d1103030c07030210061d01080a0305070807050f121801050c3a020a170c28020303030901060e0c040b160f0b1501030f140c0703030204080d0504060f090b 69
    0x20780580c242d103c000110210701901250f540c00ea04c0070f20a0300050200320035041250495040240140c0006070000044e0b544400b406000003036208045695055010039075640b1801700d2f00e0001d1a00c0022100c481e00f0b8050040881600050b02d4042c0c10200e40148001d40d0341e0701d503000152800d12403031407070000b1500310a00444802c030f110300c40214401e20260a03142c490078580d220303182040180c6854001070f00084500c00500444006115524065000c96031074040d5031024a5990040c00362503110400f07040324608101840b007800240741d15000f600362a5a49802000b4030b0091070319000e44205140d42c1740125042d80161000d46082d1342304900054507005c2000501541200481c404a48c410445155003000940000549014400405500303844105030400501590741d100a90750180780b0341140c54a0701803e803071426803c071203090022561491141401c4002c0e203e10380040f6030768410045120381095020000744116505690b071040d041c3c54079001201c952807207205030a0038000902 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 837743678 1250 837742428 837742441
    0xc0703120e0f030c0601140a14040e01060b0f07020301050a0504020a0e060a0f0801050601030f020903030f09040f0903050d0506010c0b1906030c0b0c1e07060804060204080703140d110303 82
    0x103109040080d192811194440c110b40d04541c69540030400d02c154980128004020095050041d000b520604584206003d41841000f25002e92003070f002900c03503510b401005010700c90070350100010700502c002d900d54421880b0780101d11075102e45070890203036203000006080017a540c03082500131a4001e003d20443e625100c4080250100600354513400402013030000352158a0071f040000030b1202400100b0a8079140001400300c6003600345136151140100b01d454615500401201c1c00800071542c51601c80084901041c010210a040c8404040c0703405003900504d1f0304500a000099900f10301400583c0d148001102c8221501d180100607080c4000402c078040403074003541d030003141c0e80080099010358035125803440342440d9004014480c00003d82900c5648240724807070a010030100120b601c0d01c414a8174660301c01d514071408040151070000318003000900d0701158000c1603440102e901143e12400c00807907280003c94038005600c200000382c13112500407100c1861154918015608655451707 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 837744928 1250 837743678 837743681
    0x92802180907050c0a060f05090f10020c0106330513050d02030c0307030308011406070809010f0c06020a0207091d0d0509030f011406010f171306061d0604050c070312 73
    0x203001101881824001240ba40300d0402207064801d00800700803800043c0c180c1c6980031204049d004120a030429801080b01d00000240d80c0c1c6803c80c40d5800507134480654409600502054118400640c3c10018050510a000d1080b85840c1c40786003c119524000b21016112441501254000901c006200300f206180c0802c00040d400d0014095650580d0f1890001c2e06020b001e4004a020803004801403041c208e00380001078125006844052400e0704948555507180103420180c0d04004060b441034500b0b40c400c584200c8419401102036483e140c80c2d10003e500c440c4035000d64490a481c0410101c1003010054000d0344844002c000b51180f400d40c103004841c44d0340700150f400e81501c100e00b9482a410424451510390126600e0715500d13a01f89030b0001401103814a440408101502140d502400d0161420a4110b100b8030f081224044043c549000605201e6211088001d25140d0b600c00c50b204454080b8811001110704110035952000c164040b402400800f07000100403090f0f03600c0800c1d40303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 837746178 1250 837744928 837744931
    0x6070324060c1106030f0702070603020a020a020d050a050307060609050703020901050702010e0402090a0e19020c0d18150201091a0c09130e0723090705030f10050928021809 76
    0x144084110158480c408140300d81e0054802c4420b401c1c4100803c0b07e141c1c1d05012080c00740c2864074055261030340351003000356107440389200a0f10465000000c40c081003010080c6595076544001565121030f0075003040c00080c240c1d4440c0c045010b04003000900d50034071920840351029016104e290522140703800464403544141141a08280e00308422010741c2d0741c005c4103100a1808094035010340c0380190184454031160042803a01c0c0d070051101300400707a0f000c90078119206551514020309894a01e4100c0021540d0344881030034020005140074060f03040d0080e500c428012801c031864007404452000c200b003030468556400c40010b0001c45444e19220207041d1b05001329a002065008100f40c2140c01c1c20306030341c001440c0030640c1c0aa0401c040c00240c086d001d01104a401c0300c07552420a03805031280c480145807005034450080011064010f040c09203001e0000544041c030646071a616050704548003403840e5508004540f0091141d8840e4001c640410141382c03a000c250302103810034000d41e07003030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 837747428 1250 837746178 837746183
    0x115030b0a0515090a05120303043903260306060901120e01150e04020f01050f07060e07050102101a0d0c0b030a14070c0302121b0f06070324060c 64
    0x1080001a1640e50521071040c0d84610058450741d8030509010440488001c6e809140203103409a0071003030f07250000c01078039401600043c0b280106a800c1401012321000e01c40c0d40a41906d90f0003981d5945c1e201503582106032803003003000d0074004007070cc40c0d0054040402c0d0a000c19002c0c003040010300718140740004d0042d16a041c1811078101c3c009058407820b40b40c0c15060008660364078441c820780060391950500041c5600e40801d016402c05401080040c3c028942c094180900040d0001d011415079017258801600b0030401c024440b040d180030b0b5252800c6104950042c8940100211540e5440c49492008050307154080000149138080c0180141030300c0098507600000c03000062850a034000440c4900d0b00f040d0700113004110000456420f45d0050f021760b040040c609003040c002a0001240f460400d0441c04070fa480c0c4c846151101c103059400340013900c1c1d034000c0320080c20806c82d00041d114010131003614240820701c2103075084800c9060461902e480e004400340108174050151010000150 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 837748678 1250 837747428 837747439
    0x1a1903140a05061e2203050313080d0c1107080a0b0402011806030c1409010f08091e012f030c0d02131401090b16060506240415080115030b 61
    0x4425141d40d41030503c121440b180514030843c005600100364210141d004140100320640c40d90f02c92a90984010600742c000d060100000c0841c1c0913020001c030228045032700c815055501d10007048500040c00c0d140c4080e50104110302691002c084000c40e00c101600e4041c40100542d0005407601e404685010384140c0c1881004001d070005c2041200380100070709881d40b004544144081402000500c1c0e2458145c1240400e01a180c607580c0d21400340031220f900392401040c0c40e100c1210075428415200c030148103c5032012505815800103412502d004030805104016001211440c00c80601070245582d04000c01007001940c00d030384a02c040d01c1152200d000c010f040200c54140d182c00040030780c000303182e001880050107800c0d6a0226500016040468400d820607103000312101207400c08440c010501e541301e03000180240c8a5001104942205c42202072940b124510f900c1055400b41c0a01ca918030b40440c1c0742e0030058007883d05141210424030840482d03604100f005c800800d600e00240d50f106 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 837749928 1250 837748678 837748693
    0x10f06240831020d03090330030906140106020a140705060a050a05070c0b04031401061a090609030d08010f080c0f01111908030a0c08010b0f0304021804061a190314 72
    0x40e1215410300040c18804e4441d4111036003141460030403001140d000b050f8a1000310140e4802880c205103000b48008c0314240807e08104628100c805400c05100c090103011810300002481a80041c0f001c103e00d004200d02da410a1421400a403a02d005014070f0750403103c2000032044c5039204400408403140649042e81c107040c500e03030b100140d00c1c6607507205100703001e07001c00d0900c1803018100c07022000c900351f0030007000117901e0808180044891021812a020404503c4964a480d18000ca0300d00d001d0007015646140000710740606004028020001c1c1011256404152400001490036030118010030301943d020042c0011207171252110342c0890345001c2c1111007030010540c00c0c0300840c0e46215440d0144c492804806050031141102580030410940c2c000402804610804a81c0605110004c15550399281e00205201d01418808410146c1ca07000400c803d00c4260790020324004603521000320312901800c10444025a202c00c40000820100070800001c0e8030b800c1050320881848003500c102 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 837751178 1250 837749928 837749933
    0xc031b090e0c010809030c0c280915080d08190e0102030702010b0306070201091104051026100605011e020f100203090106120308040b09010f06240831 66
    0xd07520108031890040e0301c94604440d0960b000b2020710f83c40309607a8011030030100521b505968071080d4108180c0110703000c1c0608001080c04029021840c10741d5499081c070107a0f00e062610041c28408084200b0108070500811100c0011603040e0710417185a882440c0c9403140f0f11030049080c00c4040e05000075903240105809000d0a00203948034240c1c54000284104841050604041c03000304000116450401038000041e1070146042c480e03001560001f402d40d90f00c90014a0794000750b00708030044030b8411420803421940c0c01090039500410826108407050304829001030f15030074019980818110307501280360340120502c4c5840d00d841d0344101c8001454410b4500c1c10119030084400e03840360000200b03d0102024060312000b01f4200c4004441c0410640f401888aa80540010f008042e00f00100b4030460094124215281718001c040140907542c203841c00180c211605202030590f000703503c0ea0015409541c110381318078443c44c004080702480003040420340d4100540144d5481907000118003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 837752428 1250 837751178 837751181
    0x17011e1203121406060f0c0703051504060c02010209060405040b040f05070e0307170d120e070b0301090507090602100f020d1508060f070c1106091503061005070c031b09 74
    0x312806a01d0781502085941ca01d9420703281146008548000340a0030b1082c0c5445100445407105030300d918068035a68000c00940c03c2050f0381c2d1001e0214412070503003a50800b2580782640c0075510403c0e0802c03502c180c240059090340035070310405600c90780600041145041039005064140001080010080038050940045890598400e00040d03075000c1c03a031050703050030000d05001d0503580303800143c21078918a482d42d031161290004820840c01320f00e4040c030031946820840d02c2ca0b030b80c07000b036403081078450300791034082d410074410070030844e04081c0442c0c0c200307011381c00b4a016180d2a07805441800002c134092400f80c8603211080c203c0690030805069154002c0c03082100c280c4103488d4540c4041e02c0c20a045180c000d01a0420141650300c01c01e002076150800036101c2d030180e00081c0515030000c0c00000031464080d1546403900104118044168210702800a520590044885440c658000b000c115a24007504500405518400d5414004582103445c0d00c42c1d8030703040fa208160211789a803000130 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 837753678 1250 837752428 837752459
    0x31e060f040204231b040f05042a0e040b240a0905031b0103150b070b060a0b03092d0703260409090611070807031409030109030804050c0117011e 64
    0x164003402000503c80c4104880341865100600c5c492030300d040600b415940c40100f40304c1d00ca0240f0565036242e082884014001d1604e404a865800124400c0303e0200301828020716444d0035403241703182982e855064030700a8130051940349154048440c00054220202e000e40c032001c8228140240c05100203240c2d681003103811200f40c0b02c801ea51900d00340070400542595009884946c040c8255642804840100d806480ca92a0807440f03820322074491502051180c2c8150300025841080041007040d02940010708582c00c81354038910101c83c0c654140e000c42c003101d81d01100300194021000810110f400b001e00c1c2c0e94075004000726900e2541d1890081c000f50791080d44001d40b50b45d11882c4030310a02c20181b20b42e11200407201c00080c078080e56655401014414540c0c01424001c44800b00000041000300352508420041d008000d021030b6401e018103410700884e001c0364144a40c028003010f45d40301c3c0501200110b507080250500b6400d1050852a400d030f10030424140b0700d503100740082c10985035111003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 837754928 1250 837753678 837753731
    0x40b0a0f0b1e040608030c0d0c1506060302340b100e090d02061303120203130b090c1f080f090a0611030609100501120b040b100509031e060f040204 65
    0x40c08002e160a003484155426548054074503042800380550140c1c01140c001041d1120b494050004000381c0317480c05e1400d50000440c0d01031450241c01180594141d8001c20251120310b29413071041c100c0c440040c8200303d10b0400412448180760a040004010300c0301c003508402911090f89070720381ca4211000010070211042020307070380702c100310420303a58050083c1c540240400005103140c0314a5180500110302d080d00145841e640000096035008942100008483d407005030104142400c50000743c4e500e8807903a08902c03580341d00100e003004450340b141c4480082d03040d407a06902d50341e84a20350680741100501c0420640296100d04d40020720611603191300c007034101512038a1382001001d00c0b80003c001068008000c54a19040c0050380c3c2058594000c118402000308801989138041000340070f9828903150805095855075810b942c10801170054a41e081c6c00b04d40f007a0207003001860500f403004242c254280c01ca00c01007041408244150703640a030001d040801c010748501d44200520f401124003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 837756178 1250 837754928 837754969
    0x81e1011030712060b030402010809011e020d0f021309111209070e070c020a0306020f0f12011a040f03020108071e030b01140a080a0c0c1509030e09040b0a0f0b 70
    0x410044541212210710f1500705040704000c0203043c03d400b402d440c40054406410310409400003040c08609402c4240c41d110310071610f05d80d0011102e070140280d009284c5c21368a01e4140b446011030701416100351000c100c5e0085420180030b03e0074030048003c204013002e4500c544000c02c2174000f0070001c0b4148070f0240d8410001044840d1400301d0190070290041e2008041100516400700965220400302d019070f50032800059803440f00b610320800c0741c8540d103041850400e000c9030a15940d6a01e5480d6030403106104204481410180c0740011148a0b60281e140d10704150303001440517511070072003103070303c000542450440380d082e000c0400c0300342000d03d09400020751594410b40e050350780170004000c00300503000324505103c403503030028000000040c14920103a43c2d404075903440920420301c0d00255a005030401c141c403450080003001070a107619056002c68210089030070701e0b041c841ca0241c461600201c1c820b040303403203c0241c2c001410202c5274646005445950605142d0b4a00181c0407059111003503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 837757428 1250 837756178 837756181
    0x80d020408160f0603090b19062c010f030302030d0b04110403050607110303102702040602030408010e030405180a0f1a01030506040204031e05011116050f07081e101103 74
    0x1452180001e00d9004401014240040000042c0d490b00207583c0007080d21000c5802c01c10319848c100c0007066076171b2114070010900028200340a450550000c103032184c0e03150b15102680c990301d2265a9402900c00240140c2c02002205440c255075444882c040b60001c0000c240c092408520349175607001500145c03442d0300100d06004c0e005400c080f1894420040340095030846c9803004c0300c01d0220302e103445000c1c02003118200710242d04501c0020b40c4030a01c84000110b465907181c410003540ea401c6400344030f80941c070f080c21401b002c7c00008250b4003210f900074540350144803840000d8a0340b09018110001e90341e04c80e64079021f040400c0c041c4c05901040d00d0380c9030440350200c1000400340d44003d00321a0080b0b20400c003d0021070b2400d0449018402e0038001c10a07000c11510300140101a0300c11012000e40e00410040c0d54180c0c40c3c5516140c980c0128211900468850141e03601c4140501c20441c00e64002001e0340c2c2c1c0c045459842818482c60386060310100c0c003640c80d098064031074121891944010000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 837758678 1250 837757428 837757439
    0xe0706031d0a03080606070f08120103020306071701060f051603110c1c02150d0c030b0907020d020d2001060b0403021c0f031202090d030806040501090c020604080d02040816 76
    0x401c1c9207400905000925418100ba14054069003000d00014000d480004400c014000e03101124102c42e640811080d55070140041081403041e401c1c04204d12a000d03080125040500c0f810920760340c5845900d6562080c1d02e001e00a8844042c80f41c0218103200060007030f440643ca0488061030a14040c0d00c60101e8901040c02c0203007040b02180c4850b100b025050300d4500709030b030b5200c0d0383d84905505a5640400b034210407060311882c06142883c65880e070401201d00d810683c1900404000d01d000e0b6a0028951207078103080c1c0c1ca4821802c1c1c4c030ba00507480760100e0340c1d94500c038030b1a49680041c1607a0405124143c0350650b420340f221031b0084608080006030070030860410720092803031645070070540c00c629607156030f03000210b41103e00007801700710310400142c0209a480d81180c400d584014201045090b00d460007901c040d82c120b40e4144500d28003000003c0e044243d00039070800d945290301424240c0e94603034484065400c5411140340896081c0f201148480041200400c2c030f144950f950070f107503403401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 837759928 1250 837758678 837758711
    0x10606080a0213030609020120030c01060902090f0f0f060d150f08060a0209060f070b060301050609070c0f0507150503090c0a0308040512100204060c021e0a060f030e070603 76
    0x1d4841c2103118030420110b0a07900b00c803400306042c3d9a00410100707540c1d00d0750004031075406040200c0742c0b01d90320503000072200340c1c00000100301144a840003031040d00d0751040684224000d500d0042c2e048214207503041050704e0500c24100c1002c00042400490036601404103003103404c8034940c800184d603aa020442e42208026000000340b0403140c0c000001801d103046035403111b90107004900f801d0b03000700d01036185a80345400e840c20811807101c800c0c0c4481c21341c20003100c4094143d030080e00035480c10021a0b018102041c245201d0f04064a54012944055407030808030150810700303641d14010040c0118000324115101c4da0740991301d641c0d00d903c9007800c00b40c05c3d050001514180f84190f15000c400c000184055040d9011a103084980505050074001001c0c00d01c0006219041442c0c80050003240c02138100480c4c600040c000c1d6021211144502400f41911a0800225610140720502002400e00c180c00c004c0c03c2d01845d283c04140c0c640802c0109190101641040000c00d407a014402520b4204 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 837761178 1250 837759928 837759931
    0x601140d06050a140d1b030807320c01050d0e010614030f0a030210020d0219020607170903091c05192108070e030a0b0a02070218240a1701060608 64
    0x31070340944c13024050000500c120000321402031a4481c4807140c0300c0f0703280300003001d2001503400440b0b0035070f03070010307413400580c0307107080b582402ca88088078207022010384151a00d40641035107420040140754881401074826400121154080c5a00e82070350003003d140a024400c028101c1002d449444150242014200b9942d680c103501030341d02c02a42c84020960010b01040e188120300c3c00160356031580080c81c0040e120742842d0280c03403200c04003114a01030340002d500784982c180e51759203018030070f2260850450305425603904c5403e910a103ca402d00d0f14001c0760142040d0000c140f0409055400d959140c146604110350f4040c2124481d00d82042c070469000e220003828001a080c100c10000e03200203000380d200070b007841c01080018241c900c0252010401e2004451b0446110714080c0307081c00c0200043e40c03180d48200d0250b01e12003000003103070102808850051180d020565404418051086400c1780718054460380049500e0300007880f11034140f0064800c03203c00001284413810708a0142c0340303000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 837762428 1250 837761178 837761189
    0x20c0d020d080a3b0708010204240c02150711011b110604170a15050103030801061b020603130212300f040f0f080105100e0601140d06050a 61
    0x10041d0061a5968407208240e80030041010005031180c42c0e071031000e2031070300c0b07a480322603442c092507001c62500069022002660709603108540b55180c03506807117400d0340218401c01103200f000c0c400c203c0d212241d5503080f00e407205041c580100d030480160000307807484120004904482c48001100c5d8188400c3d4103044503044800e08154601204003400c001910030180c1c0041c044210305900f11010303940b410211001004040169a151040c52581a48441d100082200c540c941c000713407124070780303c1c50103000d0484e601038030b4409140e882e00006580c40304010040d0b42c004882401c0900050780da0001550144040101c05c1038025443c0c81030009021070014801d501d84d01103080c1520b042001c43c8100c01c2c0001c80e041c1e0701c01b480320a8031800103a0013090100e001c14180841c010500a0791303030340924100c0d030031000e4070420340fa0790304415400c0725020f40701c3c4540e80c2810745040c0200d2210322042c5402801c1032401c503444128559408880382c00030000201650740b2801c0402c06031500c020008050308 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 837763678 1250 837762428 837762433
    0x1b2e030b01180510140a021e01060e0609090c150a11010501030c0b0c0c0d05031c0b01080a0b031501091a0f030d0f090b030112060609091223070501020c0d02 69
    0x750044542000b2011620440d440392005162120210f449524801c040e2a412108161948428440a91500580107070451240c000704540941403105015500444074071940003550b5131110400e210502a006004407070500c1103148942c060707111003210746d00e02c09880b61a1a2121103d10006000035034041c030038100e6030304000060000c582180c0040040301c2402c540d082d592103c480c00581003040c1850a281c0c0580b08421365410b0100100040803100c5076242008112042401910211100c543c985400640c01800180f19401a41d000702100c440080c00ca446d4201155a0020400b409803c8494032076214031284201b0700d2414500d4031419812180b0720b054551640c0441e80e900c05e15401001080f2540314940922405014800041d0151941c1541d030ba41c2c41d00c10b10100f002c00040101e03020b500d40640094080524450ba450f500e92241c2030000740780e51003004694075118408200e20082201103007500080201c1c000b0308000740b01e03800240c0ca130030b103c0500c1410b00110420160554 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 837764928 1250 837763678 837763697
    0x9161d07030c0f050306041103010b1e0430050f071802070f0b2802070c06090e04061d030703021606090b1209010f0c020a020907111b2e030b01 63
    0x40f6048021900080301500c0d01c185c4030359607580024054804042e2541e0030410000000c503540001c0710080036184110410508064840d80030054a88207d12845480d0440301e5140308940030f051020280c04604191084c80307150103038a41500307062140501e00385580c0301090407c548541ca003002a06074107095811400e002d8182c407455039000407401c0050034140d44100081c1c80b49607c855903000e070344c100180d400c0b40003011130081000b54000003003581d0700c250340315002034040c1c412411402528030000c4502d03196182c44e07603444058000d0864003400b000140029801e507001c1000074180c1c04e8041e900800c2c1d00350306402903240d0100c02e50813540402017090009d10148040c101154170041c0110703110900d41d40c50b0790529005182d45000c1000c11420038802150a580c001843d00e0400d00850324280c41d6200c1441c00d945003a0001c00303040490b042041c1c1d003000c0d07041440b510302080c5000382403903113001c0030110188110003048110303c408030403c41d01c03000c07034940c5403140d6001c10a0031b00b44110b25 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 837766178 1250 837764928 837764951
    0x301090210170603030a090e060a120b010f1509030602030a0b0405070f1706060a1b06090c140a060e010c050a0b070903050d080606071e0b0a060503010b0d0b040201030509161d0703 79
    0x100c80c401d000d425034008c00d00303021032030300c0d203e07050a40c004158020b0086c00007141840e1842c10903800388a03030b2504200e0750202203211070360752020070104031864a4a101c843d1641d070307a04002c0c0d04024021300245690b461588010f80b0f030307402900e1007120940c1e50740300c08005001001d00554855480796031101d11803803c03c0501e81760001216484141814104540f20b4506252166407000c03400042116042c071125408000c544000c4005a8084000412113540e040b414400c5a003054070640d8002803c4514050300b9500860440c4440b42c05001504c0c0002e50f00c3c0c890601c400d505803140720005000d4042001800b105025031f58407c41c180c80e14800d0750500305e001864074060b415003c1c190f05450ba070cd1b001171100115100d601c46034071054015061410001210003010381d8880c5500a508001000b071321494034982902da0b0300d40c03100c903d40c103544540d0011001407400500d442843e10503034030309100d1900714080c0c0c2c5c8020303c1c070803c00c11a4859068805850004007500b85024981000c1c00c1010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 837767428 1250 837766178 837766187
    0x120c020d030c030911060f1c0b040c0509030a03030b0a08011b2303060118090e0a17070c030b040201030209121c08070c2621011a0a0c020301090210170603030a 70
    0x1480170880d0595240da070101401e0713109100f6000b80c6d410011404203083c540d096170b60401c50b0303400c4084900700700e4812030400517146440340500302076054101e80042c00019002e9448003031040409130000145640340c2042a084039540d0328103440300501851051039455010310f40c150019030b011800c840050010491800c50f02002e0001414002440100c40a51041c000040300918070700c075041c00b0113035122600d162030f09803120068841080c120b84a6401031400303c02c442c2403a0b130001f000207800d461900c030900500030141c0220304064080000000d19a02c080200702d007500d03010090010302c0c94a900d40c1e0b01c004107035612a81401201c008000c0c0c45604080c0802c15103411140d40304003202c00105e10301640c00404205091410b01003840c08105881807003400300c1c081d51450140840c4d0300c441c92101c1c0c1100f072452490b1000000c1000074581c501c2170722058102840a000810507865a90028900702001440c503030004d40910003c44041840481039600040290003640c81c040300742c1e0f802007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 837768678 1250 837767428 837767453
    0x5100302150903030d320601020304090b030a020405010e0a140f0703020304031707201b10121b0e0414011214010509030c0f070509010e07120c020d030c0309 69
    0x104001d008074106280341c90500031158440d01452003001391044129412421141210184c901c18214920b0382e501d040e882c41e00c0f1401000141c00560501d8a0100e504c0060620031541c0c1e40c15000319119900180c0325401058003a0030f072030080a103e450407035094802c541d1805801001d0a100505000ba00598008600c1c0c00000c46d240250b582e540d00c0c1401d4030241041038a01403843c41c18010807501503404000d5103a4509a02c03110701c00007000c06031445e52044030400c402c0f000c6108907151180c2d4a0001401c0c9401c801718100707024081458200482207481d40c4840c500c0d0000801e40c19100154880d00103805007a0466003080b2650b22a95a00c003d6441402075000036999500507009003e1030150f8081c81030030850007881a40b03031078a8615113035004502a0b0002d0b2107181500561450082024820358001801314889a840c0906d030080e40c01d4043c1501041c0300c0500070427280d6200900038000360b049180c000b80f110b0314039010020708464100c0c0c503070410140303010340c0e00b00050320102003907 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 837769784 1106 837768678 837768709
    0x20c010c08150d1403070f0201090509040c051e12010905150f0c090409231e0307080c0316030c0201080f01060f0c110411070605100302 60
    0x1d54012500b07580804210042801c08545030401031100c035041800344410007040c149412515045d644010029140f0500c001e040c0415543c00040e41401054192105001c500d0720b0748901a000e02c0700d00455100c3c08010494220340340b51041e071100000c0008143c00105100800c0480c001c03c1c1c00340080f12a4082e5070244440413182028862040d001c07000f40c40c000ea42e90607006480d5911041a06605c0f80d40da40f04803000c51900c0341d080c4080c101000c11321a100d51801302092030482944524113030702030b0380000d012100e1408801d03070b400c296009034825110500400014114002c01124180c50340b21600054141584042000354680c000c0c0c8424400b9180c05482e40480e480034061390740800c404040a41314540300f100403108141c029001b6401001603807000909940c03184500e100040070100310003080c05551b11480380c1007180d83c6c0d207030145d035455640030490710828100032 = true := by decide +kernel

theorem cover : BRFrame.Cov 837589928 837769784 := by
  have h0 := BRFrame.cov_init 837589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 837589928 ≤ n) (h2 : n < 837769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
