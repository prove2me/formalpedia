-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4295
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:09:21.336873+00:00
-- url     : https://prove2.me/submissions/485793a8-7799-4009-8674-c8706026885d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 772302158 ≤ n < 772482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 772303408 1250 772302158 772302283
    0x20d03051f090515060a0f030e1006030f02042004030215090405070c06230604020901031b050406110d0509090903040302151b0f0c010c080c0607080612 67
    0x6400014030740f42d403041408070302c55502841c03400c1000221841441c101400340006e040c2e07288401c2a0f0103258444441d030038141c40600504007140701e840402c10060b40d0380d003045c040034000c0d140140c1c0660315060500aa03950b81c00300f907440c140d0031442030b06c0c5013501e10f07420310045145a032004801c0042c00e10418103035549900546018110301d0b078440340210b4103810700d403048036144040203481e00ca02c04041811542c1030100e25600440403500103840e0a00c681c0143d01400e11104e8011a0000c00d200b032214040d0000302030016508517688013000b4a1040010940e04d00c0c0c80c5416802060f03017480680024501603078441d911a521106503400c0c1903403640440d40c1303240d16142000e10b201c0081013007158000c20140d01002480040020006011031010b10381c2c82c0d0128094550400800c143c901d01882058012520145854404c4503401e1a24070380040c0035250a9810398850038101089106841c800101c80002c07891041400200d40110741054029114100100c2500712014480880b014000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 772304658 1250 772303408 772303471
    0x20714120601060f02121912140c180306011a03071218030e010e0f0f030a23070605040602030a2a11010305060a08060f1302030f160e07020d0305 64
    0x1207443d500d1300418112000782c1408882c1c44520b1031400d0611003018452030303554418444409905140d000e600d442080d410140052072501d0150203050824005034070b1400e8020012003040310a0329210000b02d20030503446030070a11602020060040911604414400042d50401c05034140540b41582e10418202038542d04d007406041d282c44440110305160700040c2c202d1060000b40380c103c1064060500040303000d450402594080c144210036540a92403c0240c00750458124410728200186851110011041c4641218560084442c0010068082d2080da001e86965401460401d2014201118103c1040103110030741000d50481f281d400c6002d2000d100310034043c0b001d100418440c0000981900c038040c0c481400303220500c07020031031000d000c2817070f170b030056019070041c406500c603480c0f6010400c944050187d490301810411109050000801d040302c44c020001100e20107540d100812245a4101d5480c1c001d48c0051134000c050f9032282c0c0c480c56000c1019000c00612001260485821900c1d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 772305908 1250 772304658 772304669
    0x4110c0d051207091824030609020f01110d03021e070506042d0312150816050906010e22061811040b0403120903020d06051503010c020714120601 64
    0x6001807506a0942e03280301d541c1d0310500c90705000c2540c0740303001494444106105428140e0030b55480d07450300400d03c3d181480c8081001e0301d801144403a10382c10481c0041030788000480c8102c1552800846030350049031069800c038044006080003214000080d00030b503200c0c0c0061100410700a01c803001d40f10400002d0640302e400380009040d9444d09280c00f40704803480700c1022000143c0c090b840d440081c1c0313180c2c090302015410300c1c04d0300c084002c020562028104400d000e840d100310281c2c011480110014135100c2d840c03030000d17080406e00c0c0d5540500c442c41005441550020341c6e010050512420302c4200c00c0d240c0d1000070001e03046c01c12420f4030130017100c809412000314041c913040080380d2402c040c02000c500017013408100745403600d0003604402911a03480010050b00c1d208008045442c001c91401000317580181c216444580280b400100801d000c450391141280c005195910901b0140b1030404030710b035685c0041840c00d040904602d400701d102d040155010340305070304031700d484217041c84038500904 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 772307158 1250 772305908 772305917
    0x10b1207061d061c05100806011a0408030301170d1d0402090d0f0b090114090a1106040b0706020a0807051e030a090609050a02270105040b040608030c0a0221030904110c0d 75
    0xc01d016019800c0d17030070142c800c409080c50201d0500c6503e40c04100d01f0f04452114145001c0c8190401c0e80060754040d0707601201090002000010303010301a040f0040380610004151403a41c44001c1040d180080040380e0381d480e4950881c03e07000d540c1070aa0003060908001803904042003505c0d0b0350030000005805045030203411a80610400788001d01524000e90303c604c03080840e61500d2041030703555020710040a44205007240807003c040d16907800300c0d0040c1c080d1700c0b140d940d1070096050050280d03025661a000054081e400074038554441c0007503070008881041048146c2d03040c1d000e0015540c20280c9082d903003d60300d0b4641c05c0010964450252300e036105801809030a207680c01001360322100c62200d0040039094811a21010401288086c155401160001004801080450002c0c40d50b500040000d210001c0d54550304000003904450075407003190703940604034490500303416140995030a42c50f45d920601030340d2080e180541010744803140050425042c0840032111a00d4540b02c00095800716 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 772308408 1250 772307158 772307197
    0x901120203180705011119110603070206041101080108032704091104050601030203040b0f090a06090503030f01090218150d02040b0a030507030203270703060c050c010b1207061d06 79
    0x70b08091103400010002400c0581510480d4012540c030703080b0001100b6685001e582d580c408020346551480c0c1042c5010382400c4c2c0b6850140c074045d5a4200c2900c00b5034001400452800c01584118812410b8a81d008080c5040c0007480070b00c404400416401c40c0314003421505a00e03400c0c1c486101d003101040c0240036410410308001c00341310440304090140340c1018010001c200200741d107018a079403c102c007008400d03007694030039400d9824800c0c605002400c00b800c0459a10034002c00001860003815450f0f04403816981e42c116003403c030704c611914150701c0fa03a482c601c3c0c1060300d4903032503150b0160056070085203000706050100c0c0480e44581c000b031480f0702000c601420000d0381071140e0f0342c0c0f1001c03038242117140d81011031a142580d07000c0041840c400507250082080503c007440540000c0d81e0041080c007085440c0c81029140e508640600341c200d43c0703401502442890040e401e080c04d14205000b401c04141414400c4450100c071158101256546032008405a2960001030202c034000704642803a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 772309658 1250 772308408 772308451
    0xb400b010905030d09170307020306040305070203160e150f0406060c150603051b131401061101060b0906030601090308070305041d091e0c1806032802060901120203 72
    0x10000c5420460003a0703c403244c4040c1d2550008040d0054404982200c06015040c203412840c0d0f00c100100250140249014041010380040150540a10840a070b40104803600480801c0342c10304c0c450040051700c41c1020480f20340c0b0010380488042809050071a0240d29800410f05aa29aa1148002940e4082410203125050101864400103801d0034407c59285494150b55210302080102002c903d60f200081b0582c3d401d214100c0038040e501e406d012404207a10106040703642440f5a0001ca0001c811101e1007001c1032040307130151084541c0d414180032691050040e070760002800d15040c0468088040702207034810028081d0140300f80d80b0b8950f601e0502c64205884056005600d07022000081801b001c00d40c04100d4491400c0343c040801500c240c0d242000385403009a5001341d8010106c03407205106251440b0b14248504000e400b02c642c421010004a4a401800141c034040304030301d83d026000500d0881d0083c05501014549034050030700d120002c804a03403059a01030034000724000344602 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 772310908 1250 772309658 772309667
    0x114190c0809030901083625030f020319140d0e0f0d02011e030905160312050903070e01090504020127030f0602070602160507090b400b01 61
    0x110080303490100c07410308103140d840d0394901031900400e040c80301790380002d2035030000e103110030b24a13031007007240408001c3c18407552184070304851022480d2800b81c8030810440c40c9076040101c9200c0540d0048208080c82c603200c0c6101e104055004a070325009010382811241c108083c922603040c040c0340c4c8a0140040c2003209031a14440344a901c05001c030041d0b141c10107640340701c0908101030050340e82318410764052004032140380c0d52500050f0348034401d0340c0412800f94507a00084c5818441d1046840d4900b843c000300803414898400100b01d1002c8000f0841138034030410103890203082c06000c4030031440d15400c1c4031103115401d070044d4420724ae0ba2000c200541d070b40140004a8840002c941810039051440410741042c050302018110680c0c030030303000d800c02030a9030458480a400800440d140d215a203200094107440a2094070207110b013102c0800c81504904c5403d142c4500204403d07180c0d001004902000d103240715210300240c140c221107800d60117074000c1040c081c02602c080010340082c064005007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 772312158 1250 772310908 772310921
    0x1106040932010e040809040609110c011103040b01031e0f031e090305100c0c0c0e0118060e060d0807021503061e210a1209090b0d111002011419 63
    0x141e0400226004100410501c1c03450340d0001c0c1c008010b545c1d180095408100601700c07030b41c0890001c0d49040b140b0b0a035803071940c1c064490035201400921500100d07001c005800d0000750790103000c00d104100100001012400350117004410662507480251003511110413600074094113401044000c6103202081c00300c180d202d410a00c00f418200c0d006421612030b01e42e5035100b403c0041100341c1c1c03204d1540d032040c007458480141603800700c594009c568407044c00410000e801e2040d5000c0011203030400403000028080c6405560349913480c404107540d40410040c0415182100380c80e501030820041c0c026840e560b0011030203814000610f60349040260500c031562510034001c484040c25a0b041c040e41d035554001141481c2c483d4596104c6c20b8516004603030a00c02100801010480c0c0300504820243d000382c4000308a5200c050104000c240050910051110207940100303c002c810760084094a850342e108a5002610b1000060704902c185004103550400d80e4030404400700c80500d1a0700140320301400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 772313408 1250 772312158 772312241
    0x12032e050a0b1315120615021c050901030c052502010f0f0e0906031e0f19080706110c07090b1002010b0a030b041104051e1006050711060409 62
    0xd82c03810701d4071000510002d10900405041540c0d80040302d000030300c42c00d40f074038000611780010010b040c0d407081c506200301c000f19054001760240b8003010390420303c811540340340c00f0380580b0f030185407070b030880011070091808414520070b03c2420301244480f8828040501d0b6030a480030090f681e01030341030002401c0004001d50030000c0007002d02c2007141c0365620024090a81005903074a101d503403203180c0028103100d420800c82c00002070b05103000c29000800280d140c850300b0b8942c1510900007401d0309000c03902d013900002608001c2c0c10001d6900040041e48111600144504c0450418031028401360400055038003110b0002d0719030540d50803d00d0182040240220180000c120711040c600c0860650100b9103c00342c17013030200340002001c0c0500310390440500c810050040003645400400842c1602103d4400c040003100d150000720520040628401614926103810b414a40300e0398400184540c100503003030b0016003d0000080307002940c0501010080000140c1c052243c550150055448078075400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 772314658 1250 772313408 772313429
    0x1207080a1b030506060c03070c0f0501031b260106020d030b090f0f0a0e0715110c09010506072105090907020a030c020f030f100f0b090912032e050a 65
    0xe007030000c050741c07280c01d158541d504010400f580e80400140050090700c0e0015014040040d08108110785800b54000791441c0c005410345280e05d1310011411200d040c2c9041020741201e001420207280101e40c5001c1403600200b890b5190182100100c4251600303034001000741e44070b4001c403000740b03425004022403003806982c404404d1611088100060b0300c05050a40980165404683c101c00d15410107208111000100c40705299620140e1400801070f00c0041d00007004603400c00e0303001c807006c18107002000c0003c0008405901b06010059641c0c0320b461700314ac60002d00c1d15811442910a461010001c149880c0d05896a0300718060024a1200805460464000342c1d2a0f500194100c4050303100903805490107110b545040012070b1030200d000d010301c61180706d040300e1200300d40196004000c44008040c4240181c001440520621410540b43c1d007010b80c1103480ca000c14140800059940071400c00d45510200c000c286010308800e440d80000714482c44071450038402400c00303020340c10081c041000b1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 772315908 1250 772314658 772314671
    0x30105042007030503070c080301080c130b01080412030608011a0a0503160b09130f0b040f060503030d090507050607080903160e04110a090e07030c17031c111207080a 73
    0x503810040c8194100101480780c04004500440d1082850076981c951200301c40f552541c503038224983ccc601106c60540e1143c4070014603920b044506020340d240c12001078544121a8072503070381d5070b00c5104000c5070860400d9034580c3c0006150100f401500b80300c40040040400750310001040c404510071982207a8043ea0007180d690041d451310700e0031002207070448910a521072040307400003101d2041c00c070410b80540e400c0031858445041d26900440c0d20620440c0c0030880b1904140520060383c0b1750744079065264205000803072001140d034100b06030032071092017565035042d1142d0029170700e03030030802d0b007524003250214086000d828104030b051400724120300d8512185182c000725105000008000030590344031015130484d180c8070211120082d28500c50280b202c101600c1c40b10740da6150701d2105581c1c400f003040002684028080f41c00f0308125011002d9460061180351141e0b1048945507214a00d560715501000c1180ea03150203810306280f0180302c1119400c10074002008910060400f1080d0307440d284 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 772317158 1250 772315908 772315961
    0x40909110a0315020c010f0504080a030501050907141b0d0503090f031606020a1106071713030804020603040507030218010311010e0604210f0b0402010f020c0d200d0803010504 77
    0x111a140100d0004030301503694402d400c5c090b800743c003240144218046c1031606000420032340e0310140031008403e580c1081030382c0e43c800800c01d82540c05e8456002190b01507180c4d50a1200c0d12004044200d91022114a003040344d444070b520745034201000c94001400802800614041800b110107069090300056040072202d004220005d00807900080920b0b500141018000c0e00400e1020110b140400503200c0c00c0c941200007074601020541c50b034031260a02d4000030080b03a5941c403007060868041d6600f6010b07517900e9080c080a980040c20a813990b12030b50b8400001a6102c0c003000c1400c103680301d05540b81d0351451a0100011481c12100c0781070114000d01c200403074072241c06071011a000072040e110380d09003018400d400c900003030401030700500d80c0030103820900600d070320020b01551003aa5490031454846030101c0c0c840c000346140c1c40d401003443d5048400300c2d007090807003c25a40041070705c80180041e41c2c00141030002d001401c440035640800108954a0300c0c4c4900f81404044442181c0c00d00e0014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 772318408 1250 772317158 772317173
    0x5101d01150611100e03181504120c0803210a0509060a1a0a0312020601050612040f060b09040501090204180804090c03093504080c040902040e03040909110a03 70
    0x5001d20b034100719504080c01c11200c0c04014400d40a1040070040010103036020342151207901c03c05000b080c1d80070a80c018481030411400788601c90b40c040e100c140c01c1604010301a1519000c50b50142c42a0052620105d06207000340300402001d01010b5010051036168425088160070090150510b2071400e0204544900301145041c2d00050a080008551450000d068068010304002641140300e00e03202004004920045090481040d0220344042e80d030f6608100803481184c2c80541c5080083c400720740050080c5400c50401c0784a10004a80c00070400c0100305000d500316000c4d03c050b0344809a00095041521a582c042c4240c414007004810440d2151180d0344a14840c2c42c2c0e08542e649a11104d0b14400e502070342940303600c80104410840c1ea010785400448030001a40043c1c1e901402d4085818108003c40c6e044036052406072030560124000c010040004140590b0440e072101c845400103081800103001514100b00c00040541040c10880490a04c0468040c020500d02c2400d00204412 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 772319658 1250 772318408 772318451
    0xf0913061d0901180311011a0d0807060216031806052703150106020a050105090304050114180603131103030322150203040c0602101a040902060705101d01 68
    0x1018180000c980b40c03000c4143c010004002c075030103c418030403600d40415901034514518155800000d00080012011403003090300030941040c0d00195209166001541d10005080524042c050040c1046050500c504521074200d004500142c03c030840c0e441e0594402d08510050440e61600c641007944803088500184902103441d43e15010903112083c1f0343e41c1c10031621021900d032688112255940c0d00020350340d44c1103240c0468046d400e150000700280400800d0360100d0340141c0d2140a059004400c1d40403031341c420020342c0d910141c0b1815911041c0c480c100214082d400c1c020182038610440d04040351084001001a440b0707410400074031400f2000d401c1e500a0f800d05003078000345100c049107400c20b102c07000b01440a141c0c2d40003100304810311a071480707040d0403210a40c083d24030a1031284403820440b90080040c007403285000300b60843c10700300766100440385031028211516104890321881c4c640210a075080301044e4075416800510381520201c1c4250001c0d1030001d00c03142c03078050440e2042419 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 772320908 1250 772319658 772319699
    0x31009140c2a07030b091903090303050d0e01050103030914030c0d080901110d090306050105061306080603030d1404030212120c09040f020a0e0a1a03160908030f091306 74
    0x9841c90b44142002e000c41d58610381401a800315030066980740381180500030112400b181900641010440000c201400050425850f80c1ca060b01da60940d90103842ca90800390040042d140e1720f11040c02c01c00824490a03010314007a80f01c1c01c103400d213401d0107070824840f950340c014086e4000041c40940f5481d06482040c00c0c541c4008a503460703c00590040b00d40d14504902c80c4030701d10424a00001641e00103800406482c05910140503981e01c0d034052104600c11122500e404c0503050304100030782ea200e810700e0707904150024240c03440c16a11940300c03000d80781144000000016001c00340820560104041d81c00094a11000d5080c001c0d043c1c03103c15030160080200141440011710030300c1d40c4d644c0d94062a0702070081102103481c0c0d0520f1400820204144840601031044e0401c0845e0b5004201c801600d80c1c00c00040c11032450303545c0c95000f034448046001c1d0b07406100c3c48002c04110908280003801a40a4965245e42c032500c00030104030442030084503d82c44146032407c103201c541c1046a50295190 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 772322158 1250 772320908 772320937
    0x4081e1209061e0f0f04030c050103060b160c05130f0609050106020a15110304080702010807021204120f020303072f06030123061305040f0c020a0224031009140c 71
    0x7010f0400e6000741c41444030f1908800030014801103c0000c039030103801541d004a0300c1070750603a1240c0041d012280c160103226030b042c405001c1080410195101d0034101403085280342000e42d41c54003c50540c0003201e4202c1c8202d03440384c80940a048280c42080c0091051090500140d490144080e4a490001801500303d49601000f00164125500300c80c010484000503240c0e02e18007803c20200c0c9400201049001810b028049155584001000c40c1c0444001d11454074007807070300a488414504007a02101c802140d04003680c0540c0c0c0a01c090040b50b0b00a802180c55550f00402408c4a03a84501d1403101c04d104040440324941c807580152415600308100c00d210400c40300c0c07090a5400036001c06d00b0361001c00055a404101400c0d1485003c0352800d0b90188a0904070700c41d8801034860200074800141d014148070303c054a020355080440800c40c001c200344984d802126441c4651040b03035480208469080108011400d40c41114030100c60711350500e00c01e0a10303a183c5400751103141044d11094 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 772323408 1250 772322158 772322197
    0x20c031902090a2c0d0c0c122306040b0c030403050304030311090301060f210203060c1b010c020616030507080a2d0b0a150e0d060204081e120906 64
    0x6030481e6000040001203494003149444c06003000c00c101030a84010b508060007000d49444045020b590030704081a0702100c0c8010f445c0c1001c00643d503500d1044000c0e030b1b900b100c4d02010b11000c039000d00400c1d51400f410f40030b403556141c6800d19003107020000d0040300008608000b0803021130790180551307420035030615000c54140e061031100a214020041c0040e03065281a00006a0311101e518907401c8a140c220202e01c25605a00201c0c4c4e5403040d0100039405420120014604048690003884070000c0d020402090021410140d4210366100724040050792008007408448001e801d01c5226914691500744140d01e81500020b006c00c1000d0716480c83c154442c2c55629250780410020700359603a4402c160703080101d181110001030907000241c10300408010201041c05201c1440001c8505481d89035908038862020510080141a010aa81240e401d220104034100203002451001070b1440035008004441500c203411312000100500d52800d0800c9003080c0d40e00c0c1c607016503100700b070f00c030740d910303050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 772324658 1250 772323408 772323421
    0x61b020105031b030a090303050a020708040e041b08010e0712030c0201080c0f0c030417010212130c05061602030606060a0905010810030b0112050c01031a040e1606030c020c03190209 80
    0x1091102d0b83c4102d0300a004010040c40f0701c19544a1244036000b507074144240d44a1b82c0d0020220300c503054020300580b800300000c2c061001101c5079290010b1140c0200f401d0b981d1041c42e89290070301c168000d140541d4682d1070601d100181080041c1c0070f4012031092505003a03c2c0e41d000b502000704800000c1c14003a61400040c0c0084103034007a2a030310f91070303403901a5403442d50420040c0c807513005000e4107103c18802d6402c4000c8404c144240d600c0d26205c1260120300381c85200030b02840c0c01d118401201c1f0f0042c200000306564980344050501d00c10b6034600b05650a6144c410123062800041030039000344014014000c45590108502c8220340c001c0c00e04821580314074428050305001a00040c03e1820500c2c000a0061850f076400240e0368040c000343d80545c0c2840c4011001d40c1c11503031250041001004c00f60060340b81c9903202001d203000050480300038066800000c02c00c0c5041d0b5111402090ba28082200440e40510000c103050204402806450100c40851000303150901c201900844a00c40003601 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 772325908 1250 772324658 772324681
    0x51009210210050406021204060215131703010312111e010225030f0c05030306090601020c190f120506041b170319360b12010f061b02010503 62
    0x940780c02074414007140340d80740400303045644644201170040c8038803100100700e90a090191819640300f03601a11100341140c0c0e40201c00c403405095501c280b494022481f000a0406c500d0788800c4082d090020b4507585942084034202000c0e55075030082c0510904038041d40000845d00c000c1000001011884491050f03913803a0080c0504400400e42952783c6510302e1802500c2500e02c0f641c5031081d0740b03819070b00507545021101800030381d10051543c1c0c07050010591034600040d008d81d0002c1e041c4116088851440006040256008403e41090301d114201348518540035550ba000360141d48181c940c450041d41d2055503e01004201030701001c1d20130566014003400314030307540017400186291000048041090390712940094000010b5000c00c607140031070039002e040a0300c4005004103c0d41c0004c451b012081c5002c2030380300a40b550000c2c0704400816500306090262108400d02c01141c4550740c141006600400d6280d0000c0080c06280d14030b002402400d030924201080c4c0c20f10300706d40c0b60340308c00a0106 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 772327158 1250 772325908 772325969
    0xf18030c081c05040c0e16090312050c0a0c08060604090206040909110603150405070801030209040f02011103040905010f08012d060e07050904050a05010b0409050c0f030403050a09051009 82
    0x40b10b800c0c5410b0100380308028480c0e1003907138580c03c8411265180c2940e581c00b082c9266207074001003041d11400300080389090190122241c90f500302030b85810701e10301c925400c0c42c0140c401118008490401804078140400c2580e41c410826a0b0070016800c65030006000d900407481140006601d661070002002104074110a00010142045449040c54000d030242028100003075400390b481d00c0002f840d26403041d010141200d8002e025040c251311561208100718040910070381c14040d14a01d4090f0b5014100b00400c0100702c82c0b04001a2035041a48100420317100e94011541c0da030503c65182440c80072642284007100c248140c10102c0720b90b040c008006002c0030b034490110b2150810800a0301900300d00140520803044030204496503030b035170b01c4604582d001e000b280166030041c0814882079020750301a035000a0501c4d8034074107240307041c09506080e60044404600080010030049481500001c0440291804039000c651055410400034061900d0384266081d008003c0d0140c0610080d501809 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 772328408 1250 772327158 772327207
    0x3140109050d080a1113150c021e0102120408070608090c1504140a03051009030c06090305090112060e150f0315060f0a1508040516090f18030c08 64
    0x842c0c1240144002400f03003c1c00320350000c026420a4a07070b1718407400f003030211055008030308112000d050800c03542c03004481501c400350040c00015510b99000d40e4401d109420701310351046107121030442d41000241040300c2c009a04030f03055828482808140d20208281c41603404502d007003144d0f551841551407510910072441c1e80c000161280c44c0c1d0541144200a1094034155009d180d903120080703050010b4580f079448040e1294001d41c201c4402010f080e0086014a0301915048841c90341e162a035200b00c1d14845403c80c01300e040094000c40c2541c00c0140c525540034000000c005c0e192801d005206000401000380c10254130900c0e1400984d0b55040a0b00300e441c0707015048910442180201188282e000d80b910f41c81020701341c410006515003041600241c54102e07410042d0704a49510649928501601c111174602610b1b880040c4010711040c0c0c2d200410356a200403600400a1400500311110128000707a03030706407440c064000c01d400c03125512043d41d00403805942e401040d44e000c0c07207015244084 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 772329658 1250 772328408 772328413
    0x110c0d1703090c0a120528050304080a0506371d06010302040b03010b0609040209060909131e03020a0b180a15060b04180b130e0f0f03090a0314010905 66
    0x50140850340003c035a00c90100075a100c07811291107407000d0440e0708a03e103008040c0da000e03060704400e8150301c40b000200350b50728008040410406503a51030941e04150484050740d4001c26030310050140811072250845d08501c0da01d0307c030b41c880c1160804054900c40010724002d952080f0702c00040c01c250312850603c07207404030011042c448014004c2c0c07500001c1c84282d10031401c00d041c221040c0380620903d900726a00901c480c2c90600c107641484065006556940d90001b018480300e6440e071500340c0074030300ca205c0044080b4690081d6140c1419441010366a8044641e1050040c1001035000209800c0c3c8642102c928031960742c0c3c05444540764290004000f850740580307500e4104010804520100b0307410450000d00a650301c8506104041c02503102d401c4800303004000c0e03250300c202c29500c100d00302080540701c0b01c0b41100d2007600344c09982050030b420741e02da402000184542e850070303c54084c0100c110b03400b07989001840d400150342d92646010140c412080882101d0046909501c100e0b12560702405 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 772330908 1250 772329658 772329661
    0x1020313030506040b060915150706020c071a070c05061c180506150a1a04050a031a0615030c0c0109020907030c0810051e130504150c110c0d1703 64
    0xc02d203880340001c0e03c00326120840e900205a083c5040c0a0107071041c4101c80302058881c1c000e0080102d10b120861a80c00344107820844040880c02900041c80000810301c028103800745802c281c0c010b610360141c02107401020920049000960003400700c0304031001103d20359266460f03800144030180c440a08045418900600f0011403142250102e0000c4e00540560303000d559408452390405500c0d011040d804803519205108000d14a00d03105488814850242e040588900c04102c11408540064980e24410b5038140f642840b103020242d846001070342c900d0030003a440b081c00d002901019282d10304c2d203000800e0080520f682503101000c5030390001d1094610703050805003d0003c11400c8a200001350703044000074100c80760304142d1422035902404403000210007146030041d003100d81c0c08e46607211004800000b80c0d460140282c9000301c1c00f1742942a800c038140c0301d1501c1210008503120091003072648850300c001c107010443c00000c017010ba800140d000e1070307440c01400440460182da20050400300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 772332158 1250 772330908 772330913
    0x5060f030d030608010e010506150a021513021e1e030a0519060501060c170a110a14011b092603071a0c090907180504020d05060306181b0102031303 65
    0x3080f1a08548151000704001d0b10301161003402d84104030341054101200c100080d85120b01030006005070030580c415500e0f04402c040d400c001100e402c2d1742c2001c40002c0300c40401f0651911aa005402c8002d0f034611421201c2c6030000f003004808040030524260b54583d164140c5920240318003403642e90302005a03440d61400e200c414134104c50007441907504614000012507a9800307083c0c0703911b007560044203000d440b05c808100c06005520004d00030040054038260403002d8035017040812039041c0b14881c012040b5440e600d07810308441984d4090500ca4545010121080fa00400448181c0d4a41c00015006001460343c102c4441082c440040c40d0348400a1a4002c0c002c4100e0901c000708114008071199032921800c454041c0189100039a02c5040702001c180340a000f00034840b110b90400c020840c2c0b0b02c1c0ea0340002000c83c1c00054400c141d103070b200c2080081c0342c54144031301d40e4400700302440f81e9400c4060501d200d0b6181ea040b1500400c080462900307000503030003042582c8000400c4481914815140e2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 772333408 1250 772332158 772332161
    0x90c0a0306140a11070b060402040905090f0d080c0d02212703041d0a1530081c02040e0a0f05160e1e04020d0204080706050903030405010305060f030d03 67
    0x910b031258038541c00b900442c0d40030110f40503c444003103e0700b42081c145601512140f81c415005042507600640c00c20001400411502442d8843c000310005842d03c01c0c1d01c510454102014101404200075a050400a015031804240c42011100e501c00507168101c800d00c02081c400402c21000100c2200010048100524170a0600b0040c12040c3d8103465200303821a0303a502c1c0030b1802010070000c015054009078100da620041d5222014060101d005966401503d08511450b0004040046003070789140098150808500c40700840302113001c542e619648851659014a44840b076650700c628868410001898041d20701400111144150701d04203000b88000905586072091002820040025841070b00414100e0100311903440700110300030242c040044d0320030301c0d5292080d030b0020700d25298250b40311440544150580c10000590322824902114a4031119511000030410204082c00103924040140c40c103d44003800c012a154550000013014800000c110341e405100c3c80107450030142e4107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 772334658 1250 772333408 772333421
    0x3060e010b010909050f06120c040501090b1e2425060e011a040f0f02031602070e040f0605060d080c16050409050601030f021f02012703080f090c0a0306 67
    0x243c8070610210380d56800d800c142c4408942c5242600040c0d00000d0080c203101751205800300760441070303817138540e607683c002011280203030810207150707070340b100b003c03d01d0708080c0310040a0720b142401e0115001d100c280010100c40c3c400b081c12005551101e21040d00400c40e0b0b05a60007503200b10340c0e500b100d842c0190108150010050150b84050402650307542c640c1040c414044903034110003401280700114014403000e0a1481002c13904a6030360341c241c282c500c5091020758090006140d410281c8454030200a10300241b9411204106420750309000026491701803402c070866000401056a50b2220005110100a010080d21aa00000e920790340c06802240c0e00c0c0c080302020000e40101d640f07480c20710040b43c0f1091401807540c0c0c0100014070111701c648514440961000340168490004152079011401030318034407502507910740c403160500c40305032103005e01c195507a040503210510094400809541010b455110a051400081011070000340424004801b001d040c5821040c0c1d42d25100c40100503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 772335908 1250 772334658 772334681
    0x8060f040606091b0c050325150605010c0605040f120f0f110a080906070c30081204170307020c040e0309152d0c0105090109260403060e01 61
    0x60030302e011036504003038483c030070b40340021446451408a15203825185010701d0002518948021f12459001d203041030188480c0c00f5268842c0d0105500b2450490b2024280c1c0e00010481d5043c5282440b01c1d90b40301c400702026a0b01302e0320104003510f6a05001418080e9a80d0240148421030307039102115810280040c00c40005aaa8400f000842401207c0c910008500d4a40980003c0400c030301180320500a00b0380d01d8030080a641c941005039444802d8003903282d000c1902144070544549041c01130344d00808031444806064040e04019070358648080c031035050110441c4085a02280a005140fa02d07180407440c404603a507130b00d060880e0003139034465040d41024419802c05480001840c0d002c0103880c103000c0d0282c0f8801c86000041480d40668200300d0955031b0412001170742d0321185d8400d00c100d00700d08240d800001da6455150715007038290703500100140510f82c1000910400242c5108180d81c12a81c0c0d212224484c4507244500f241c4d6100701e51000d005503080081d0084540d2065001d95020712 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 772337158 1250 772335908 772335911
    0xb13060b042d060303050a1101060e0106030b0a081209102102030a06120203032a240606030610080a1d0d0806031b130f140a0e07050a031b08060f0406 66
    0x140100b5041503030610300008000440070f20554590600500c00902082c107640d001145040d01c40b0340240500070241e10110010380c6915400d4407a0500f40e200c2006441c0748000740000c50004071400c0d4140c4201e06002d40101c41c81ea6062406a11507200b0242160b08403401c1d00051866641e690060741090b541000c10602c0d000d00001c90b070360b20b03680b417000f61741c2e0240103141403c18006a018465402d86410810380480314a4200e1400c401d00c8143c11000e0301b0b0302d08220b2110f070303480070540c602d0f4004c010701c0c080c00d020020701c00141d40c1c03003030362000c09105454000b400350307940840031000d0030b9403a4040c00f0044464002c1010305802103030441c1034042301d0f0782d00b0810355510f01c00c042d82c03420f000500c0c4046025441141250741080b01d40c1c9084196880c602083c000307803800c412401ca5111004c1a031403070a840c421300c041002030303004100c2d040b04c580000704072440c01d00d000101c000382e0510000f01ba044402c0c002c4000300341800c010314002c01d6060195913142c6030100e000f4003060f60480c0c044600d00d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 772338408 1250 772337158 772337231
    0x602070609111309031d040b030d0305040302010f0c120b06090d0506151008151f0f030b1e01210203040f0312061214011d01020c0709090b13060b04 65
    0x803a41480381c0e185185c0c00d56200403013629844900c10301c844e072008115810984800d140c03110b03a2001c0000c54064851a41d0000c3c43d441d184c140282100d00745c3d1009203503c2e041c105200703441c1d036114291600020000d100010b1003c9102c00041035032080d143c40741c2d003107850004890244100030489078410348100200600c86903014013007050034610802840085a20384001c0b80140958103200c0d14041c002611a4090754034544104081c2c5860501c01c500007650750140a40b82c41c0e043c080c0c0c07800320300140d42c034008038007011250b58007440c501c002041c10040d03001c00503007585c59010303012105460001001c55590600e401c0214a6100308401a40802e240300f017542c502058030300c1804200c4641c148540c00741c1682e03076a0781611000d000f0b81800035640304d164890105160740203004540d03096000060740d0f580074400c1c03e420f001301d0381e004036a00c5251140355000b1680070818035078000c030300c2c08000040f1801850020002d10100b14401c2c0c1051802560806c0d16441d803050200c00200c0c0280810702 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 772339658 1250 772338408 772338439
    0x631031403090918033915010b1c0c09050102070b1201060c020d0b280e07091d03040303030504021e0a0501050d060e0906010303200a020d060207060911 67
    0x2a4810403204540003240e08000440c2c4e80036440f41d8005510194061324a0824001e15070b0107880841e200402007a46c01c4205901e24490145800742c080d000b03140984203402c0d0514564801410520a103840404005030311543c41003c401c4401042c85907071003c20840f030409500400300c00b454082d1502611908102085010480007a108094002e07403000c0c10907800d000080318104407410040384c0101c44224080c0000700c1200f0050300c10210f00102c1158040e6400e00d050700080c400402c59105490803640c222002c901091030016142e8080c0042800c640030a07401000c2d05105001d10403a0002003030102c10940e0681115010714001c5600d200d00d01118440b116210401c05542d03540b00c07121074000c20255001704082c0046410303000b40010f0300c1e550389803040c3c000e00c0704581c285034a4000100500826400c110300c1103002c28940407400d03204105045140c0e07281c0c420a00039104108180c640e0042104940482d0115a03003c0c0040c0080701031490101c401c61007045801c0c1c840c24165000c40c80 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 772340908 1250 772339658 772339663
    0x150a0e010b180130021606151509030b06030705031e01050709141509040c02010203010816050a17070b28031a0d0c0b19080a09030e06310314 62
    0x2020b8200b05040b980c0e1460802d0100c0f1034940884d0000d00e03250302440240801011560341d548003a000f22004511140d0041d50756000781d00940040d203040842c240e48408040d80300702d0a1040d6507114841d91950b0b00c4420000b0300e000150380c80346a152040600610491111240d007a2070303100d10794006d02464444007420b40e80c2e007050b0f010341e46102080c00340c0c52000e03142a40400003d841c541c11802d00d40b002e490301080540f5185101000583c0d000801001800300401070b800c520081019141181800d102c0040e00409041c4500992202c5007641e041c400c40050004c070005000d880040355a600009a0b4006440b10000952100611000c00800303818001d004004030702d00c006261083d03000703140041180104240c1c5050310b103000160340104200d12100c0041c603003d1000e500d801003440210760000c0204000500cbe801051303080800200001c1d1b04180a10a0905d0454038944c841c0013540003040f40c00120481c00745840b031400406900c0b000c4481802e02500d009145211150342c0c080c1a255 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 772342158 1250 772340908 772340927
    0x2060702060118051306020f04030203070e0408030c07050c030d0e180c09040e1509010207150b0a0603050a15030803010f140f3c0f030105040209150a0e010b1801 71
    0x8440074016901180c0c0f1811513404580e20200e1355080c07059200c03080e00c4050072600810712074030744580001024015440d0030400300c00240b040e0301e40c4600724682940c40e001e540c08080c02d02d1045400126100080003000d01901340e0444003d401c8842c0951203d2008007844c5038040c00318002c1c0600e4040441214006803850311511418400d6854900c42d042808000d003080d00001c0b415000b403c19020700500c450084c02e002c0c0340000005130319034910303040c0300d00381094000d6040b529614204051007140c49440074402101c001e800c001a4603598091071101078002550b142c400c50540120102c10080c41e80040c5040c0e43e0b4041c0e52081c52a201e1039001c3c078460240c01d03010b80c000c5d034548003e0002c0c944900080d90703030360440d030340e090030092000c1c0c030030f00814406007201e8011080d02c00e100c0c071039080104088541c040110028012030070310703070081801040054010b00384102c1c0390354050041d49803601818003d00065000b5001d0750780d114141140c0ba0800a1071540c04500a0601d16096100300c00c0d10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 772343408 1250 772342158 772342169
    0x1207020a02033019080105030f060718030501020304140f0304120f02010302120112171606050402040e0703061413020901090903030b040f0b1f090e041109070c03020607020601 77
    0x10226551000d2a105038584038064480f4030300c00c0d1040c0260040c82607805850380d00c4c40c02c410340800100c094000780541d0340c1600003502a40c809064144074441c00107007150000301c10b042071048513855a40210900456800103042d644c00002407008101c006410320080e400d001050304c50562019240d151603110b1407040d0302c1130501000c08500800c941c002044000c80c414103005203840001180801054400d91149a001d80d02541407002c0c010382d40d400c0c0e1880d85070445004c0c9003084076480700300001005134000d0040340d03035480001e00319100d07540702e219401010000c46110941da480c00320050000021505443c103108404120720311030031031280b00030303590052401c01c3c5a800c00c2d403160001d16001209030100351b11245052100d8407035101d941b603042c0a03444081100540102800450400c1c9004210002c3c1411403070101d559010252106440d1001585004c079102c0b41045100d078031050904503485410740342403283d02d40d001046030101c144039400303564940d03680e458180e8071003d091054 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 772344658 1250 772343408 772343413
    0x180901051e01050c0c0a0e04050d08010f060302070c050a090c110a02010507140a020a0e06010f0e150901090302031b1503010501080c03040311120310170c040b01120e031207020a0203 80
    0x881c4150b00035000343c00c4054082c0c08491280c0c1070840007580403040c651024003049900b40902081c44403c0c09000010a05c1e4244045e0740d500d80154244140158440c13403040640c00300e14003042026032030a00c7e000b040000c041c41c40c40ba848440d660028034545e0000c101107204100c4410700c0480206520f203540307030140c44160030505181c0328191004111144c4000c240114a6801c0059644044c400c014091400e503451142c43c040c00090b1244180c02020800d0000300124042d5a079507800e400c03205041c100c84900e2310f4980311401602c1056950300b00a6050040c44010022805858070b141303041c50040f988584482d0b604901c01c18184402c0c0601030014005200058080044800851f00310f0311074900301c5412182400765608000c120300480003811000401e202080c0c814517800c0c0060038450030011242800c3d40c0150ba03a50f0b4a6014890042c0c1e00d408940c8400e0b03004080aa60784040d0716418882c0c0d08007908141d4903a8085403941030001d0103940401c25040c400152801203940c00b400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 772345908 1250 772344658 772344709
    0x6130e0d0e060408010501060f1d090103170d0609050a0b092a0c1009021918230703020703030c08130b041e060203060a170303070f09030818090105 65
    0x42124821800321075290801410080014014001d1050500a00341b0b551030000599201d40d00802c1145603560461307001c480c1c1c1c074045809a51302d214003070440394410389140e80f00e101c104081c60359000e0030030603800c0e0310310700b040000e100011134001510688107944208910b5000e1010440588029280e0300c06a0192001e03801d4030012040d103210400724a600d005080194104c1440d00d0900d1500415043c1500c0700011000c40c2040302507405030542040d0b0554400c1e060400000c460038800c1c02081d1041d07210b401606810350344c010b460642e18030648101c0050300d81420041c1c0658800314007200001c0c6013107035a0010f50302c03841282e8080c043d20520b0a04507819034541c40b400d00340140c02074805d00d0030707045e5941003c80c0c00011452090700c0703171001686034901181007010f4031003a9482f10400200c1c4ea24030b00c9800d0303404401c90f03502143c5810180301c2c040210004590241e000d0b0401412681c001034424850882c003030721102d0102045401d500c0301d0380c07aa0107005031000c5e0000b4800400c1da403203c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 772347158 1250 772345908 772345933
    0xc0e0f07050c03040b070822080a02010c060e0607091a030c040519080321100302060f0a02070b2802010b130c0c0c09090c0909030903030806062106130e 67
    0x9005111142d60401100e05241d1141d030b42c422a0341c80020201c40c03040b0002944a00c2044141803200d603030341c02080c1d1640c02450291000c1e1a80002e020080c10411070340a400708016650b4002c160300c196400459085207071088003c2d2040c00c144c000c0740203c2c9000403000c000005510101c03407081b010707100e40ca41828501410f010342c80c0c607140e4046411868100000c503a4030b034100050850310a004110310345115990301502c05111002d0601920380f0a0381e981800580c039030108584d0b64480741003255a45902840c0304038103000294000b6080ba020005401c40d100d90403c00b1003501e645400c0750f80f0504200281c0070f82c201c81da01c01c88107400c8002c0074107503a108d00b0315912506141d80e0724140590301e1881031355002031030602600881c24983d0346203406400e0002c07331000d078405050889020015100c850300d000d015150301d40301c02420008504002203450704c4403020740d010000b00841c2c80444054000c6901c200340e50444a9a02820038203139255000b0507503000384d540050160014003041c50425 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 772348408 1250 772347158 772347167
    0x327110306090d0c030806030a0b0a230906070c05100e0c040c080906010302010807030e0609010606080c0a051c18050c03120a09090b0109030f05011505120d2016030c0e0f07 76
    0x70001e80e818010a0027000214144800b99881070f054224009403240e400720f401c00c2070a4513406031920701540c0c40d042041f200f00002e5000d8009040c2c1c113200c0185506498000d140c0890800711120071070070300e000d64280f031000181050302e54208640c18000300b002c1e18030486100d80300b1a10300c0c0055012a00410155010360610794001c0110324001c035600031456026440d020f426264110320307039554042001a150311042c1c660304540742080c0c0034600100314000401500840c090040824407d5141b00100c5113280d1182d0950300039001c00c400c115034142051030b26076800c05011802402030310b00410801521030200c0c1d040c0d41441d00d500348070710304050314400100120b500103410b0160150012010414404440200c5031003000082040300341d0315040d00805000e0b07488140210324410004800318030200380403240c480389180840443c05101e014800da80300802c0d035014a8001c4c038906d410030031104005070003500d015000c489400c554603024030300e00750f004507030110040380c400300490400d6220303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 772349658 1250 772348408 772348411
    0x70305070219030909051005030307080d02130909120521060d0804120507150509040902010c14070e1f150905090c03010e0a0603030504060327110306090d0c0308 71
    0x1948100d807040c64120304200209000b0400650201c0da01440c100072840e0b2901500b83e03c080713000a040d500c41d1601c008680d9900030400c00408614000c1102c03205060542d0650340d42c6604003844080450b95014074070700038100001c1c1500c0c0c0a515401c2c200d8110300075021210505011140d9081c500c0f035024010b00b035120042c0c0450b0f407200b4040484004600760402070805800c0092405503c02a03510300745180c480503510800d4206210030041c0f0045805c80183d6851703071000c0d100403808101074401211081404000100300d911030a000d151001c50005000d8240e5150001940c2d00d511480c0c0045110030105c1c501c002d040c44845000d10100f100c9266000c5048043d04281003295100c50010b0f4554004a400080d040c41c0400100500b00303403616903a41002c000f00041000604607200142240300305d00844092645078070341c1c042d8184003600528a4206070514402031a070741ea20b00140000035220b0f0b03080c072034407c0c0c801048072441c002c9040d40c0c920300d0940766140a03c0311698143d1f480e500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 772350908 1250 772349658 772349671
    0x110d0806010518090103030f0f170f041b03050c0a2711040b0d050430030c090314030901030c170406051305010218090106091a0309070305030403062c06070305 70
    0x16855200c3d8425280c0c1d90f061340c0a0741c4292103c00c1c089294207401001502c3e1245884204244c0c141c0040c03000303c050000076004180030451800399611818201180e12210100c0b80a82c7c03c819400018410040703002030808074111040b510065480120003a4a00080c0d4140f070f1024103640c400080c21a6584540c809412104150742002c0d40d490f00021103810242005080544034800c0008001d80190390641814503605000b040c400c1d40080454840000030150040c184c1d034681c54419540101040f900031079000c102008654406008a070b100e420107840342d40800c0c108100c609103c1d014841203210000a00145091541c0e0354a6900c080c010180c00804000b818070f0055020640030f0005200c4540840c0444004001c05014131030a18030583c8000304110f0300003001c0c40000031241c1202108540208255280c0d10359101c040c0c01c0c0100340e44002c080e448005070020400881e80c20043c510b0f407401040c40100181200010805105400e181406420003000a11958000d61150790044e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 772352158 1250 772350908 772350937
    0x302060f36190809131e0c020f0a03020106030b07030b010c0b1f0b070c1a04091d0d08010e0703021204031b060515090a0c140a050717030403110d08060105 68
    0x980c00d401d540d0b1801c0c031003401d5880034000a10700c10b031405c1110303484a4645088908200142108620002c0f04081100020700a0340f503424992005208102100c4c0d041002c00641d9522032591802034000c200900c030440300500c0b5000001c0419001c2d20800c444864180c580000340301150342c030711281d00c00c01400380d003a25884852034028201d40300d50800182a000040130b58a036291304040044000c140d114001070788041440d901d80d503d441c020f45e0704a581e2030001082250245452081070303040720b0341c0107045210f24803403041002e622080d068101c800072081d0b030301d80b03423a4200200d0581c4940320740d640944070384d400410f0009104400c514110b10008030740111071703043e0350740f00420784d001030307520480280d0100c980000380d28004000c0e90704202000c01c02c1100d0f0255a2000c0e015100c0b0f0800c0091040d030105401d20590300407012540e2643e804542e4400307561855486602c55081036a090300015002d01244e41c0000001600c10b2184045c0d40340d05140d07644080046130982c0c0012689104103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 772353408 1250 772352158 772352173
    0x12051e1f060309020102010b0f1c03030f1401170706021e0c130e0705120721060203010303080f0a02340804030c090b0306040f021e09040302060f36 65
    0x81000c038010000c1c1000740e60214038455240002401d444108101500c2144070301009240741e030740e0010060705244282c807000b043c41801d09068004008a1442002181c10225158000d01c00e941400781a6404000396201e0703001150011a940d1446003e20005640851880f40440414011800c0c100c1002411a0f090800d04e10208000007078a03800d00e445c0c00d49416032501c210300180109400381000303a40005042c0e140d60324150baa24101d10426854020000c2e007200300d2040001d4014010b5041401599607594078907001306100e0341140d41249842c40c140200d04d00b010305008032486086000c020b8025505400942c212683c2c0780102d00c2d00c510182c406007000500f01e42c000d08015400b9403002d540d2641340000b0841038418005480388250452400c1000080d0510007080c590394041d62a20845400c045c1da50000d88032100c00c10b5440183d1f03108100c1050750010300e9031b108260100c1c0a140c00e0719030981c04c0311840c0d2040d446070034001d00c0b0201c03c41c10078010f100f680c0d40d9030203400449404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 772354658 1250 772353408 772353451
    0x6030f0501140c030a0515210d050a05040902030723030105011407120807020c0a0b18041407050a0e04110c0c1903031101020f0310140108190b03100e0a0312051e 71
    0x12656800b0209042030f15170100d4100c2d08d9010b100740b444898040c02e11a00d40f45542c80700501d148a10b002d5041e80c0356010001c2024180b02e4100242120621480e008003481a02400340140e0402d226a600044044842c1c00d0101114019285000d9000a4a00c8802081441601c0034800108401e08521070354586281da40d81d05020314004016803100c1640e6442d409109107044004408824011030170105145038000b40c25800c0356100d16589091522607034405001c070342e03201910b08893352082c01d160b02c2103040001c047c000d100310f010040884210b0340d20034082c404c5800745401c81e483e411a4001040010030300a6800c1c00c65a010180018030303220b442600180e103900151000059560003001c1800102150350007002d900c0030909241d0140d00e400c00290311050900504080700d291500380b20181510100704813110300b21064002e000c0300c8070b0031100a90310722a0420560005444014420301020244070f07003401102001a03a0f82c800b00c00f1005a050290f01400c0082c00c890f01d14140701c1e0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 772355908 1250 772354658 772354669
    0x5040612060c050f25060c05070605221704090c0e0108150f04020c031b0705130510090902010201090605070e0a090213030f03120509060703050123100e0406030f0501140c030a0515 79
    0x7c5c08000c0e619129219445c0c0d040400441c3c0d4014407a0113500d0f402c03035042d9900c00c1c1c4079031910000796000d048000460f40c2c0d840d2001841c004ea40c440c1105605044440490340c0d003007214481094800e07600c070350059450110088403c00c95074540b9130030500107803142e00d42d4202500101150010340701200e24041c0c08406504821250124511203900414418401407030070391101040940000c00600260400424071b10003802c2a10844080940d120010b008590003904500682500080e04228515103017601501e0100b041054030320460007641c0210701040b2601c252540d0700884002e20010b6401c607030b00d450354107850300740a41c1880105101c0041e89655800b800388a4800140507004c2414401e4028050700d1040c2c009001002c0a0344180c960022007403043e000e001002c640500181c0b2100100f50303000c03a9580084c0d030700b2606168010007806501500144e495105500801501e1a480c0d401c800c000d00580d803200d00a2000c1002c40c126011071340005410425400400c60001a8140042d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 772357158 1250 772355908 772355921
    0xf1c08030108010c030e1c031a0904230f0c0f040b100c1b0302030c090604020f0c06090d05071205071e05060403020f1617010605040612060c050f2506 66
    0x31210fa454050600d01268903005011996240000801851800a00300903801c00d00360769440070541c0d501c440e2224000d16001e40c9000384000381050242e403c150a000803072a00081034508100201000024032080c002031a04210030170b0009071440040c03030410403850b4a101050306610984071140100280c4d0359643d111304c0145103490700203032000c0c14540f5800300c4080f007422060032000d40c84108096180851003401104040300c4e102455234900d40000d0085c0901d43c15200708540209498400000010f00d1600688210040303c0c815001c040d400c564501c1559401054400254524200750b0700030406002100d214156880106141e82d0040c07914014200d019941035002d81c0a11051540612141520312010000703402401e1048040f40611170451051820b9107900a6100402a40030b5208a0140034020014424550b4a0314203c80d0340d05104800d03030300e19140c01d045031006801201160b5204008440380c070b05000010a0380300410030550450342d00a100e481e0904000f0300f03544200e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 772358408 1250 772357158 772357169
    0xf0d0e010204180b01170105040c121d100c05040e18011517060106080c0f0c01090c03120f410315010509061b070b03070f031404020f1c080301 63
    0x2d0000c2441d03e408256408008a141400212442600c5113a111112181941c0c1c4c2600d0101d000040643e045803071501c00d40038010903910300b8480019100031760100c1c0140c000750303c08440c00c00c880480c08000710348100100e8004a90100410040c0120095034554048000c070070b800320b6502c03102115802d680c0d1112040e206113008400c2800320003100301d103880312244240020095581020400782280c2000341001a20850204001016400e55000c880801c0c01e240e0091020b41124074100c09000e03028003040750b03d52a2b50000c0403800703110362602011640707250755081c2c403d0040c14490b18005080b08003000c0d182100051540898041c00940150340944408255a442c0403062081c900d8040c12072641041010484200b0f02d1340d40405503600342d02105004541040c110082510340040c584c0085078600e030220811030082d8200004180500c02503d05200100709880d01030a000c00c00c940c020340c001900300524130313982404403000e46030040f030716040b00c6090819110b04203e500240d024 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 772359658 1250 772358408 772358429
    0xf03050306010305011707030b1017030a030b1807050f07210f05090105040311030a140a1115031f080307051c0c1a0c04050d0501050603010e070b0f0d0e010204 70
    0x80c400c907543d141c42540e00600f440140768013807440c2182816120316043c40b02600342c06c54040070030301c00b20700b581e20304006200041c01c1115403041610b4007500c0b0b4000c44242d0010030701c0d041d400000c0341001c221040500400e20f42d2502d0960341c0312001d03959034205e00c4105490082c148000000910944840c01240d500030021105251060100900801646d10654100102445500c441d0303608081a101541c1e1300168039100c10040c103011a240c403081c144060813007882c4154084403a9808102d480c1da00e03000f030014021a414640521214801c80403400884030010000102036090b410b0300700100b00030940c0c1c0440c1241c1e44040140c45e50304003c0050381c460f00400d240100c40504501004810320301402c2c0030440056941320400000c14405603d22a50f8000303001500c40c800200884010b458024800f404800e00303414a10300800c0c08403841c40c081e600c0c041340d0b0100903100150301e030225158082554501140850900c00c0c5c1d400c1003404009140e1520111004400c085c00900054540c4024 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 772360908 1250 772359658 772359661
    0x72109150906051503011b0e06090a060917010c05071101030902030d09050315060105040501051315050414032a18090a0c06090612050402030a0f0804140f09070c0f0f030503 76
    0x1400040c041600104e031007685070510101d00b000f420000419440103e007001e843c01a45440400d9040c821129071036800010001e0128015070041c02590070ba824400c0e02c8220721044e03031409400c0b100240000000f04509101c070000042120f0411284148180350203c1c04144660100b45080402d24480c00030965150081c01a42010418030280d103510489240c030500301b00c40040c0c4079114030701849040041c0041c20204030754524552400030440f410614000107140c400c0140560071600850384884c90b00c0540700170341c2c500003803242030b190b00084100200b0a050400d400301042c407003419030780018154444d140707a1001c0603a0310780f09804c1c0201030103540300c5515180d40e41036003541080c018070014200c24890b00c1e50021480111031034140d80000c2d04d448070300010340307000140c800c000c0500240c1003100007000281e40c003500494144035002d4142030486803c011030f0000300d40e002900076104500141c01507118458601889010711420b0126515170f07121004403000f0070f48140c011941c00030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 772362158 1250 772360908 772360921
    0x31009150c05091005120106050a090b270301090b010e270318031b040515090411090105030a0206070b13051504122d0e030708070e07210915090605 65
    0x28149510440034540039207406d100039500007804406000700c104010000c2000b0660501509242010303126503011251203140501a818044e100c44200324082c104c18204200c050a050142d03e1000390b02400040b101d13802c2c80c0d1800e20828000b041001090110658a105a03079016002001400030341c001e560f80311001602100714124001d5864026441000d00e40c0f48821466003103561210102c0c0c001c0394680703c402d2030009403e00002c1040d40840c141043c4001c22824600341c0b04210011b030b4000c0c202d03a0b80c0d003080503121100d40001940200c070401c00c0c840010302c000c281f164481c12040e0f4031507100074241c42e06480c01c0c440c2040380140c00a90801e110501140d02540a414403061a0500e82000e11810100d0345a86140980c02c041042081007142203010b1402612000c0c000340c01c40706213076903a10060b5034bd4410b910131140c1e000c02c19004120710f944140050802c11209000340b54214012840100040007801c00594203094010100b014940c62801583c40050040c840071403507041c4074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 772363408 1250 772362158 772362169
    0x603060504050c040f0e063106080f1011120c0319060b09010e040b060c15130c0501080a060e0a0504051c0816020c13020c061005031009150c0509 64
    0x5852070f1078540041c04100200600070800c201600e01d5542c02e0300f06604c80c0030202d0b01c043d10801c0ca88620350600702c9804182c01110300c0c0721159260741502032013800d94a030000c90302e810040d0041c001c1c58000202d080088609a0803140e0a100c81ca0b11403417030164103844c02c0b000300c4401d880940c02030341c0c000180300e00d004a00b00c80f00b1814401e00400c100c410314080a109c0d1510500c5401c84c1400911882065255070f0356004641110002d0682d99923024158111515483e4032045070300f0390603a94002c500000000d003210480e055108031024030306810000192036011004100e100c075291101c00116004048002c0c2e540544107009010540341443d19005091806401d0110b01d46440c05c0d01c9130540741d921100c865000f8540100c407000181100e10100e042005840c0820340080702c80c4138110101e809030340104800b030407550032384401e07447c0e00501042000580c42030303d80c1a400544400e102c030341c40b94001e25070b9502c03900b00d0401c003803140c81c0da070000d03280f188203200f0100384082211740e07060804 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 772364658 1250 772363408 772363411
    0x8011b02030306030705040e010b040f1d01051303140f0712030b061e0f0412050a2303070b06130c08150d050304030f0512030103210503091504060213060306050405 72
    0x2580007841c21481e00001007990307500140304070340c4540c0e12800000b11503c3c081d40002828040076205000414502c2c40302800340c001006080a2440710440b0300280c5401886810b014080c8004140d5040c800750714112100014820806c5034201c0410080070a0098200200a1140309541c1049032100740d03980a41190581400107006072400c0004104061400e07800c21708000580e81c0107512003c0782010800e950045800c030410300000b0981140901c0f0001810701091407094031060000d1038408040340d400c07586018406c0e1554401d00c00c400000351132500031a4028005030982e094007d0000130102500d200c0c200803408180a00d0610280e6102d2043da40c0880405075005900442a03503141552446140300181c04021003500604c2080340500942680a01d4110226240d5071039041c2804a05400c00362408c0c0406400d00b1080151f00a4060340d10a5002e1809003101c2c260345034681b66201d00c0204101e41666013000b80141c4d42004289440240c51560382c0042e0303440c01c00d0180803c4690 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 772365908 1250 772364658 772364711
    0x80613020c0a0c0509070516060906020405151306020715081b030103061a030d021002071e12090e040c09091401020c0d090801271502030a0504062306010e190801 71
    0x1c08100038240e0114884030b010406909c50707030002d20034502d4144a0b0007805907420281d4001e4189032400c5909881c100075001076110301104d016000cad030b0f0346030070b9946040e0361085128125000002d28040d50188420307650046c408828900d458030303030745040b0000340c0c000d800440c0d0702c5903101034003429002a00c244480c200410740080c26074035061038003c0d54860400d59006c9910f40c000600408000a0714a11f04544a030307032801c02d45a80440c40c1401c884e03000710100c03400051101a000aa0500051155005941156503041100d003450a10409000c2c0c1132401e842400000200ca002c1c20400d1000b442001c180002400145858440081c6002071075404410315a041c049407013224003e61020194500041c4003034100b00c821480d040300310441450030b1445031803003c41049800c8200382c01003441184543d40400c64032010107280d610b03aa21020300c0c880d10628030300004000d54050108a81038402c000c1c01c109064030301d00440301407503c1507080b902d0302d40d4440c401d1600103444400350441d07410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 772367158 1250 772365908 772365917
    0xb060f2203170703120207050c15030103020a17031b0601050102070b0c03030a0c090f0602030307141c0f0b040518060c040602120a20060f090d080613020c0a0c050907 73
    0x10718549a10b48142800c89000d01c0034a40000c04904040c0503c5000440c1c40100c0015034407007896003004c1c1c0c1c40d201d1014015004030418850b1421132040340c411281030300d50090403c8151814140341210010501031004000d1108015035070003801c43c44010a0702c286810000c4c580366050000080c101682da40c03100c100c9032404d02818580c0ea0b4040160781d400800c81d9400210035105182c104c0b4034014a504c584130146840c5404520b00307a01000852282049071144840c19150742d40300c0640388240c02a0314103c5618a02e044411001600320700c030f6524a41d00049040032000d8001411900103884940d0280500b4030442c0d6088810300c20030b64000b104a614a080504c0d00c08040d40f6151542d150341c0c200800021300401442c000c4a03060064000ca00054100420004d080c0d903940743c0c1560004030840c0d000000418030240000d803481004010740da511101d488820a1103903584580c0308824000c0c2e0280400c0104000801000050600a04000840d00c3c549001d21201400107420b280412 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 772368408 1250 772367158 772367227
    0x20a0e040203190b0402090306040809010903020a060f02070e0c090108060a09020c0a050d020c03030d0b030a240f02040b0d020310080a0c0e060102060f01180905102003010f05130b060f 81
    0x523036020802d00e920a0b0002c020325961854480103c03284503880d08001e6103c01000030102d08581c0c86000400d80500315003c9805141d02c0b96004d5030310600407944030540c0d24082003a424994462030700d49802c46000b0309080c200d41d03190301c030f884143c1e08041c00a1070190301804a003130500c0402c01030003501c0f054034005031100403a0b003000310b42c59110b950394108116469100050058404103c8904c500350414030f402c110b0f00c40396000045000c011402686c44900304081c2c00500c05451089a0840d100110010310f021182c01c9118043c0d0002001000f03403100c409400100c400041c4103000340d051051111807a000d08201c0c10f080300302409001e01d41154488000c2241840c034a2003101d064a98003007641117034140c4100350602408a028000b8124043e81084460401003038002510f4200b08411003026012814600c0302d490000b44150040700031100c41c10010380c281000030080000713010303802180142180c808103132a54403c0e107180e48502400105507080c03801281500103518105610810030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 772369658 1250 772368408 772368427
    0x1302030c040b180712020d0605241c1b030c02060a05040203030403020909010e330f0c090d0b0906040309150e0105030a0b04052502030307020a06020a0e040203190b0402 74
    0x403881d460400010f00c80807008240a280103036080005203004c2c1c1010341d941d902400b0008041c080394400ca80c040e003031100600c00c3c006001040c292803d121000c5083c05c0c240700740d0006007030310500b000280c82c190340d03900ca26a0f0210020408184804d08d903c010034601600d400c000d2600320000c08d07510149181409220059901108460480c3d40488016090762100701c041401046c00c9090703044144030303291004c03030342c0603044610800c510030101c44888584100a15002c0e14842154014030700316104000402441440001e48900c000140c204a000310450350b5540007088242c541d103426522034010042003581c080b502602038000710048034502d2403580b4011b403404601f240c0c00c40c14864044002222486a035010544040c0d0040042c492420b04205a454007000842c03901c06c00d102200c05072440500010440e030042000398000c1c440d00d030b455141d001c02034000382c0b00482000346090880040e556180040c1d80035a8101c220482e41025140d441d070126044501da5600031801031001019 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 772370908 1250 772369658 772369669
    0x170d0507020f22060905010b07020f1005070503070606180b010c02091506391c02100e030a030b1e04090c1a0703020c0d0f061509051302030c040b 64
    0x54103605031107007a6454124000200300b05240035100b00300d41c2241c114000403018a41113401201c40100c4100102d903210710707a00c9003a215805010790032003142083d0910034105125010112202c6140603800c040e11543d039079003140c6c080d84040d1150350b1501000d01c81c003445c01c2200b84150812b09004c200c00f00c07201d030000e01020454500a4410801100040e48441810f0030079011088d000707192030f54943c2d251954004640d00688598810440c0e110b09400440307441404090102a100082800740100c5034031840310940d007401402140641040001c28100f01e0080381511600030018607100c100c0210020121380c03040705e440c0d1044032070040c200c403450720b040700d034031182070782560040340d40c0d01d80d0f0500e070101c040143e02442160064000190403200c0b20b2007c1c2592501c25820303180b0480070700c8200f0102600944014041001e450000d800046450f408140e880b010079a60034540c96440030b10030300305c42040302c0b14080320050840b000114034050181c00c00e11003044a08108142c1c00402040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 772372158 1250 772370908 772370917
    0x2060a06080304051e040f020d09150204080303010b070f02090f0411150405010c060914060f0a090519031b050f01060b12010b0a11030d0605100c0308041b030206040f170d05 76
    0x4002c5da840314029902130301c0d80d800c140c03c1c501e403910040d503482c002c0b40618002000f64440c00d0758a0200a0300f030148a030002d0084a007100c0a5000540c210b9007456002c001c980d005040c11116400c2c41641c0c60010381b250301400388100e402010000040c5001d050135440c41c000c0c00c3d25684600d403000068000a10307058165020754a00b880c00303038991a02d6103052002801a5000900340c100f09030400c0d0101c260000c0c6081c1308406407600c0c0d003116201c1845500541d00d44110040041d0008051704102c11850050340100c0c45c000d140c407004c1c490170320307015a1246448074015122600000081c00c401c40c0709000e1000102051082686000c0129091520b61801800740029821000582070743d03e034401c1e02011000c1901c5416660707901803001c042d000400252251a00604000b200c0d03428035802000411601d03601a11000307842d07520356558407000c607007040c3c1071041c0c80c0c41850088050788510002e0f1010b44040c4880d40c074030a0804a0711007480503003180c0341c20181d0114200300c0070356074003009a8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 772373408 1250 772372158 772372189
    0xa05040903080a180b09010213120c030204020f09130504020f101706150a02030c010c03050405030a2a05060a0b030609120d020f0a1d092a07050d02060a0608030405 72
    0xc0c4000208641c01204d421001d80036200d448807205005000c201076000b030610050300107080c1d01150f42d0340c0d000e81c3c0048040b0406414a400da003400c0001d4281500100203201c0080c0c4420f14102c241c40000300d0000038915005d451503580c80401c000c40c18544100300681c202103070105440200c42c48010060240d20149100c5060501c0c08118144c4884074140a4118103804c5561206010390000b5900e411a882d1008150b0800040c5001035010f803062501030f82d0030601071460409022410f485840038452140e942903402c3c0403200403a4907181e9841c031042c3c820303000b404840c1440446102500c3c0107081083c440d805c540140607602d40c0c0054050807400d194664251103107101c0d0141c000a000f910712000200500142401c1500e03805038034248903031b20003440e0014034090b40041c0a00d0040407070f01e200c400040c181c0305540c1d0b050710382c141d00955003044941914007106661041c0c1414002c207058005a403245060080301d074802c0c020b84000d03094200086061a141c900051701c0d1030001d00b000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 772374658 1250 772373408 772373411
    0x30b04060609050c042705070c050706180e09070e09030d1b0806130b09040317100b030105010e04090206040605041d09060402010c0203190302031b0a02060a111006080c0a05040903080a 81
    0x11109000e201400c0f42503c0c614900d04121f94908450042c0501d42071440490752030140c0100030a09501030154040703c42e8040d26040c620380d0501c20303d0100e144c0084e02401251003140b40c000f56000100e80018800d185600156842d102c0070a80c441c180ca0381ca203460b201c154038040020701d4841d4050010307079000c48102c845000c41403200b402c0000400e400649180c005075480b00700014103800c01d6030b00800c419280000042542c6420b101d0507000054060603d0401042004100ba50f00c070708100c01291b04010304c0015114129070004030644c1c002d500103c04a0000300e1b003008180744242413401d1043c01c141c00c1104070700d4100c1c070039520f0b0300c0c00400090501007005070181c00d40d1020040003083c0350710030440044c40c11030b90401940c4d07a0009020428444100300d803e0118a001203141ca203030b40e40c0940342c00e050503081ca4060303888500c50b4103101e0f014031440c1e12030312400322140150390080010354080c1106048500900460280c035400c080e000d1828400c003540041c0c1c0c002071035980318450220 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 772375908 1250 772374658 772374689
    0xa0203071116182c01020f2a030307020a0f081b060a060503070e16020111072406120b06030f030a0e03060f09030a0f1404030b04060609050c04 63
    0x5803403080d80481c1c402800d20402212a035081d1030300e00301c841656003060b0480c0f00e000400480c141038031509001c09007900c00e150072031820302d2080600715500340c0826001500744200c5a0070641140c205103000f1504440c0d503034032400c47c1c01c0741803400d019007802d51015618601c2d1415021f5983e603200b1800510442c00c070314007035080c0b01c448016117245404081c3c44900d0280d80c001a10f40d1407400750388011900b8640b00d0005180d00d00014031008a49440c0000300c2255104103041c01c200c0c4441d0201e01c11b554035091003c1c07483d000c150080c1200752043c00030340d2040b1b814842141207802c0c3d440c0d41002151806105014030340203540d0740c010156024007615116076030b00000c6402d042d91488010325521000c5400c100c2d941e0403882c240b100b9481601200e03402ea4a8641c0c01010b00350945048426030410040c00c0d54241c82000e1029401c401824411020700d14800c02444941c89603005464204940c024482080f400d40a203400800743c4850922041c00c20380d290b41c1c02c3d481240b00d01d50103e42c0312107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 772377158 1250 772375908 772375921
    0x1104060516080a08070e040b030a02010e0604030b040b071101050c07082101090218060405010e060c0703020604062705150c0c0d0506070906050c03040302040b0d0c06050417150a0203 80
    0x10041e024680c0e118500507258110000007400544096880d1004910865401900350070300303100f00c2041c01c50090007001160340540041d24200c010007a0309410030300402001c070101d40800d00c910b000d2889003241c10054070709600002d1584807100400380c40f590400e014440c81413080c000795281103800504080c6c0e500c500b0385201c880c0074035046001d15941303424400015407030215406002100417130350058039540c041d88104a298401c5001d039a012607092903810540d070170b012000d49804208001100d0b0070640700e4000400c0303a04154010400100b4114801136100028441e031003440c1b480406081032a400d0000003107441c3c8001010394004000414500d8860004020020383c01d54043c2c00409101d110307003450f64460b442126004080f8420550004000f44140c0894004580d4140514205401d40c0c0c00c20000d4891200066400840210b01c1400318402e40b407100c0c01059213444882d40c1ea4644840101d002a00d00c03410a0680c0041000c10518080100d584c4d5100e5035603c070043e40ea98805 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 772378408 1250 772377158 772377187
    0xd03200f07140f120c060703051305060c07031704020d140c04050c0405090105060403030e0f0607050d020705150a050301031101021f0204060327140c0d0b061311040605 74
    0xd0291010700c5020000d0904030300440c2e4900c0203c004025900c01070381e030800c00d5020340300d00c2d440901c140d8000c038009001203100c1c0d840a074000d01072803101000300e00c00d920340f03a140940965a80203140c0c07000951000305500080250030001c46001c8003007540c54603800050301d4281c8407101801f0702c0c2c005000c20b04da021040c0b02104800b10018010092410700c21030241483d00640100c600521940d000030910780780c914140c0b000c5980c10b0780c074080110700390424004107641400005030415402d015002c00108140540c00010ba5076900a04200340b501c0c00b0400b24010421441074941030030008010180d03072003400c0b24103580d04a8145c0b1019802d180040785401081d25102c0c500103100c030101c10409189800034001c0300c2c56603030103100b4000380132050066010a803440980b0f8035151003075040060800d0b41c42805140144c0e090b44c0f20148040f001c40c41c108a1000102c416400c45030402205185c0081d21740000490b404081280030303042d81202c0c4441c0b02d2800f601060040c0882c683c024950342 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 772379658 1250 772378408 772378417
    0x70e0a14011a370801050a0605040b0412050309180f16020a0f02151207030e0c010912030207090f2f3a1a01020f1209010504080a030903050d03200f 65
    0x3e4409044001c1d81071600910140c003c3c01030504c00c000c16400010030038071a1041d50107540e0b8003202d02d0b140c627181507400c136103144402c070088489000c180904940c540d10104010f4441c085024011120302d40750b580042c0c1034400900429090b4450480c022206070b000403000009035100144e0b0b51802c659000049001e2044200758440c01c41c001103009264500300b248500448441d00c0500c010703640c6d25500c51300d071201c51075036a002402810f005c1005035400440d07100014028019a00026298a000c01c241e818100503803600c60b0f15003480c0381c100380300429501d20b020b41e040c040644c0c01078464480107540c451044003604607a00021110140200030b424003980b07880341e4040010342c0d40d40b1103270071024042c0d1020410900025070a1241d140d4001b241d54030fa00c0b0060b10240c07805140e1121201040e801c5030401e14104a4140800300f50740700100241e096072802900e0b01c041c8a860340c40e1191601200d8030395202014148042c84e8a031444070000308130a1042a0f64203a21190340209040d250b004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 772380908 1250 772379658 772379737
    0xd02090d060501090c110a030813060f2904150b0f190c03080f0421140f0415140405090a0915050613020f03130203070e0a14011a 57
    0xd0309000056995580d8011103040c11140c0706d0507081d0b21a10030554807100219806008100d2440010b10703440040403029021134841c10000880e01003440c014401c450b081e106680d41c07040c81c103e844100c0a070703d204000301c00800b1641408484100b508205041c0110702c103c9440400102c0c241199071180c50a0381c0d40161001030800900044000c02094440d01c40c0c815008900c00002007a071140c408040281324940180340c0c0c1e081c0450b007000e080f556420b10790540c420803000540c21034076054904020928144501c4642d501c1d5820010300780c00d41040c0c014043d0034800280540303011000b600056a046170421071345001e660f91101c0399100589942c0c0001011030384408001403400816600142c0030300700030f03100701c44550544440746040b88540c2c200780030118000e2002501ca8070740501c17048911403014050b503c81c02d580306600c1000007000d6035600c10850705d54110102c44412560000d004100120700f00030b0b10f842072204c501c00c03449086d9200300c0d09200702c42a0840c22420995182c070003107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 772382158 1250 772380908 772380911
    0x70b0f09010905031b04050105060405010c0b06041b021f0b0d170405091314010b060711120d0503220f0807140607030606080f10050613030501020d05010302030c0a0305030d02090d06 80
    0x10101c00014545580e00485d51149141800121f440c2c04d0003c15a025a007040e107543d07118404030b45406880c0c0c280144521340c89a2202402000c1030200d079282c1c00700b481960000e2907408101c0503a42030010f0701c0e40c100f22010303280202101c03060740e0341c4181c030f400b40b0740007019200031030150721424a06101d80d400c000d4001140b141480880802c0009521140f8000c1d2001d9280c0034800308141c1c05c1e9200032000c00d90101081c40074201003030068001001c100d1000f030044050034248454141032003080d0001001041c408010070031148541e001050184802c0840d801c2c1c071090981d909841d5400090025282801c0411003600300f05885484200450300001240c8031450b1110300280a0102401090b0004655102081d4802c0c0810b52142c010011100b00c0410141041c1c18407900f50440c5c3c40c0450001070b00c2c100000400c0f02880201884212400081015070440c01810301c1c02d900000720501403490340d40200042940401a01d0740328108180140e40e5a000070005100e9048080700940801d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 772383408 1250 772382158 772382173
    0x918030a0f0e090601230d090c061b020603010b0c160312031503211b0b01050907020a030f1d030f03070c0b04140d081209070e09070b0f0901090503 65
    0x590040e09462090aaa5070342c58404024030003400805041a02c045002c20b8444280100445407400e4451202c181311020301c3c181003a482c44201600c509007070607180707502001e030207002e801d0380b12050702c440e9404c0c05a8400e40e009280d02080e00382c481442203621425004c180440c0c1334034144400c141e0704140042142c1201e840f070500034100321240800402003440d0001001440000c03011000807a60071040d003002c1e040c8485039482c551000c180a071801c10044c4416005180e500005107201c5174010501404c841d81003405000780201c0141500d070555000b1200c0400196000203055003810840c41e0400700400300d000101c0041c1103a42d03125030305010300b0f8103841c1303000350000240c29540e00424103800c810759110105e0b901d5102c0d0f40580302c180c1c25031801c4401c1a0504014002ca024030901c1c10700c0c03900011001c090703000c0078191103d0645400c80c0d40304101007d404480242c0150904e4042d012040c50400d022999101c0e00c1d0f00c601c00e0700408500c503c04d80c2c2c00782d60321500801e8041c00342c8408 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 772384658 1250 772383408 772383427
    0x6110a110607030606050403021203090a090f050f040b06010e03031905121005010c0b06060d05040605061305061e04140f0a0f020406140d20210603070302091803 71
    0x29540c10041040862048400184407140720340074400450707415841d00f0340380900b5030b024010140501302016407540b10420070380709503403a0644460020101044005451105201c404054131f40103800300024429080500020603983d40034682c00200c01d0810402606240004c24114090b01700c107004200c150b83c10141c9166008002440103400038981200b06a407500c0c1c4461000b00d0901901c1d0010f03c0412650000403080003182d50003a00c010603240c1000c01b440c0c0307403800b07035070040350101c1c2d81070380354814401c280c1414004820a200c110006000614180300400d540c51a00c2070030400b00070200308800e54689407640b0414100142090f1452240740c2680b120000000503a0103c042c41e180c2040f20038050030620954041d50045d9891560340070303861315041c015402122031040a141d4908544100c3c01e0201c0782c1044500c008220716850740c0b4601c160b05100340408280c42c6040102e0f404000859030082081030540f0b5040b1200401c581b10800360210710105c04042914034480000d841a5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 772385908 1250 772384658 772384667
    0x605160f02030d0c0c05090f270703060b2403070c061107051609020703020303060d1e0b0a0b04090203030f03040311070e0a0e0c1318020a03110f0a12020d06110a 71
    0x2e514000d040121700c059a0300b0902080c00011503500480341c1e041d0300400c1c101c005a5119101440040c000588400d840d00ca51504041c4944d0048811075603450030496a03080a808625210300c03240a0100c2d003d00203000030340c00d480010102d100300400460480c0822940351f0000140340e12a400311505d60701a845c0041c0d940300c100c189104000e0385148001071540c50341c0211800705606d5409141107031038100c103012103040c842d5800c82d0a42c040241005d41102c05080780c4a5440c0180d03800340c002c0c14041210b9040318010841345006a040042c5400962000021100d07499a58000a5a250b41d1400c00300e078191800090407a06000e406000600240000030050040800d800c040050140c1c9000f100e94074100d00020b40e81044041058042000e42a40455a040d0307403c01071000701c41340b07a0300050700075449401c1209c0d1416204a8a901d90400f904030b80c004100130b0b1250780e062414486042009100c4400c003e04c143e070140c034150108a130640210911388407030440c103510317111490360240 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 772387158 1250 772385908 772385927
    0x319050a020301082b0806150a020d08090a020a12030504050d050d020c01032a110d0504030c060906080a0e01140c0d0f060b09040f1d0d03050609010605160f02030d 72
    0x44c2d039110781d04500e84640070f180c0c0e144900c10038a4204404c40f00d840c1c0e4003602c900c1c1300140740f00d61000000e5010400c0300700180c01400501426405041d00b1a14000050000b03000545161215030050f000300d001038a034181910140c0e0302c0c070100c05016605031720701214503100302c2e000242c12204a40d030010412500103102c0da08540c0c0d0382c00380da4807820524011001c0350740d41090b070001c0c02240020f20b10410303501c000c10341c3c9444203484c0001c81014969143d900d00280d022211300003850011701001406070001d0500c006d8010380c501002124602500108001009480a14201d540740a1400b0003c42584440700d0064080170321030580c03408801001c09600502c0032510000c0c00c1035144c0040f424136114107001c0d100d80100c443c1c00c000130b003070501000305003440e10001d201d0b9880580d440413443e800c65045010340320344001d28024080440c02000c1e520043c0c0180e010b00007140040c0400c40d00001950315030071115580d00c0d070804c214100000c11541704900650180240944030040c03651040b00714 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 772388408 1250 772387158 772387169
    0x50a090618032a02100c0804120302160f211709041b09090e010b0904050c030d030c0e10170106110705010815061e0c0303150d020f04020319050a020301 67
    0x60304000c081050408031141400410781e07000448414200103150600f010900e05c081440c042c1700c01030180d41c800140d0380c0070b60040e55152031045421000c155041204050307060740d103850381c044145051001d50001c50140a114005031a41010340608481050340104203604400b8083c0100302107207908280d980320581d1580568102401030110a05402415002d000b07039646a40b0080c2c5000d01120040402c0103246c0100e54a41442070709035070b1452051401180201c000d003403802c4d00c1d10101860131841e41c43d1081031506200c00407480d144c0140d0310002d010700a903110000c044503800111800900c00a418a038218540c0000c500543c2c05049040919044811505840e803600b0041d00c0548040f04c5019803405480e10003050342c10440c002d00401c803003078000c07028580c6200f0b03000c103140d41001207030441540c408020082215100c0d03124161006054a021411070b031543c002c0f40314920324100d11030090741c0000108107035441343d19280b40e480b01030640c03c1117682842c03c1580081d6000b840781 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 772389658 1250 772388408 772388417
    0x61e050a0c0801060203070f0605060d1b090e0f06040803070c0813090c170117031902010507030b010c02060306040c020313061e2604020103060506030a0b1005130603050a09061803 79
    0x40780341400081240c7d1a543c004026008805090b0b840d04040e042c000c16294000c104441c40c04000745500740f824444841c00404040319909281e607407421038074092802c420952040390380b0440c020000c81c00c03e42080d0060403d80e520340d610300041c0c0d910907500b8002800e00c07000203080e04048a032942101c01340d401501050150340a4003a0844072808010791880501c420b64004200645100c2c982446005502c0d09803404e00c00519940c40040e0001e400c0480540d460f081041001a0306120304100a44242003426880342c55030040740320b030300000f8005802280d0b20908112601c1c005c0050b969134404400d80700d00b20790b88410000740f400b00748600305c81e000c407084500d9805c024041d4840400c1151300e2055002a10f12039001c0d0f50440c50b024100ba414150741d040c001c40d09465a000030b42c4103203001c15001c285000b45205210001c60100f000000b00320081c0154500e8201d0b04c0010009c6500d00d2401083c240c880c500008010450620700604580c81d0512000c140f0141070341605040d802500e5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 772390908 1250 772389658 772389661
    0xa02030c10200c06070c0905090d0c120c02121501090e1f020c16150905032d15070807080112020d080d06081e0f0a061e050a0c08 57
    0x600c101d104001000e0303008500310140c0312000091034840301e0b140c02d44030400c8600b00100310300442c0c90340c3e20100d000d48031820000014040c181e0180219504458894020302c7c2c43d0006403402000031001540040990603008030780442a07101c1ca00c203881998004107200c40c8a0710741c444880e03480c40c0d49070351100110f40250000810003041d100702c0300f14a452401030003081c9500420490907401c1a44c0c4501102d41c01c2c403103000d09000802a100320001d030048807065041c00d01c00c641d14048000400b4404104283d0011700107520701003010b03440342c0b0440070941c8074486401359441c501c0c0880b40b9644a5486031920800b110310081c140b0300d0240e00a61036100031600c680b001181c6c103000c03d005622060710f1b448401c04c014280f681d6046100360040250905208819015000b030b540190702410b1164800c100c00201d1408400708a4044201c0c80c00178000100c081d004c0035103d000304140508260303070360340b0031032010641d6008101032a1028002007201d031812811040082144041c41c4000070100350 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 772392158 1250 772390908 772390933
    0x6020d0804020f0f010210020f0717181207091109011e05071b1211031204030b0103060b060f0c060108010b0d050615030115090203010302030c151b0c060c0a0203 71
    0x1026502440d0050520410043c1440c18000c80d0843c11110f00d046200e01080707100003061610280424050040e0040e980742080c0c100314560740d1400e584d00d0003c2204000081307131115182440c1c0f5150400f5103d03c0300a181c04d001003410702005034000d4060b1814620704854080d01e44004004246090300c0c2c5022480c400e01a050a000f5128500004600d0401001010612200882400029174031031803070038648a4803482402c502d008012200441000041036182c501841403941d42181c1800300d50600c0e10707549980101d00c01c1031001178102a40d400c0150815140c241c115407810103848461503680102c602950350b0786000f44076010b003e501c0e1000044440c40e001011f01240f42e042801840991518450101c4007010818602c0e495941c41030003118031108481000028281903c0041e240d40c0f44d4014941071540c0f540005200b1036400c40e1a16104440c90203441d16070301041ca004854180741000c1c540f0f4220824180c0e9401503000c220304503003034400921103105500c00e03000d0718104013564 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 772393408 1250 772392158 772392167
    0x606051c0b0a020c07030c1502060109020f1c0f230a0b0d020112090212030403030206090f0d08070e21010b1905040b1305040c1a0a0e090c0c011506020d 67
    0x808001c01101001c0045080101e071038000d8800c0500d0f020590300016620350b00c412003049568005150013924405464803181c06002050044c803642600350703d000150750340803065114011400e180030700710a10351020b1030034540c40007074055440d44040021040165007629103006402525104108810000d00406080d02030002c21020140003000c44045650065070050002c0d07140082c82c0e60b641ca0101c0150f541c0c2003181030b0038106c50004c1d550b101c0c21030078001d007040e034010021185036100c0b8142808a1000060522912000c0d1601d8032180c1c9441c04203d502e84444040c2540c800a6010208840d08540d10104c040c20402002000300b402c00c00b0030b01501c40d0024600c030070b4401001c1820071080c1000c0d040446209002480382e007065050b400d1a80482c1c806a40541c0c08540c086811b125070301e045444020b0032001c0c00105401c00700b43c248010301407442108086c0c025900703100031480700340c90081074034000c070901c4000340200d00d041012104c81179400d20482c0700600c0f40c8540302280034000d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 772394658 1250 772393408 772393459
    0x2030708190602030a0f05010b03100e0115030504080c070308041502150c0a0c0605090309010f170406020d09080c0604050d05091516120f021c0807121503060605 71
    0x190441e000348103040d80c6641c0700a4100074144044143c03a10388442241070329210b5940a01030148a660316420a82215602e40c403482d080120003140b51130040c01001c1034180b0149413171009140102c1c4a0351945003031545806000c1554200d886180301c0031041010300d2010380103544070400010101c08105d14104d076590040c001c90466a101d40340480ca80030000c400134078105030b503400c00b050200b8582d9908002c541003100c4001e0300b034001144c0041151392102080a03c8207480c642011010303003040b8a40761104020b48000c00107640020304030f0354445540c200c4a901c68002c00c01c592201103c0280645845048404550500454204480d0031303005005698001801411401f0084d54864002c41c055015088540c0307900d070040d082c50001420341244401211a81c5d46d4401c0b141003401000c3e107807990704040088244140c1c1c0b520701741d156000900503805902481c0640d80000307100c812900400e8504028001008840300110034803016401c0401203039400d90f101c5030150002110040a00030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 772395908 1250 772394658 772394683
    0x2708150112060902040e0307141b1f14161502181e041d0c06070b062e05090909070803120c12130501050a061412160803030402030708 59
    0x20315500d0004540b05030300c502c010610161000400300c0329a02d2107455900080741c02c4403801e802c0d0940d0a01844184450314401e80c0d00c10a0f040f003200302c5000101c041d103840300c6291001c080c0680303540e9000c3c0300b6410350489803041200659246508003074048203c18a0340203490400c42620405040f5140303200321003011418214150302401e10404208002140e01c522840d503002012841e41740d0395461003540901c5442e0400d411099203038018090030602d450300a91710641091284002040304100e08680c0000708440e803000418501401d0030720508000315a58480d001c91541c0c4190030382140c010036041c0411183c0e00c0d0310340c1e9180000e9a40d19014002c01e900c0380c01c00d02118160b858190312044e0080d5800c0f0459040503600c0c1001036110008940c031540d10740d90998203000b400002e11030240c100440d000706110190401020020000320780448500401505440710660001030114281d40d1b45003200c0303030000070765800001c0c1d501c0d00300b5501a4440d001d8840d000541610002c0d0315500250b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 772397158 1250 772395908 772395929
    0x6040b1303030e0105010f150e090414011d01150b070507140310110306100810030b06061210050f030d0206071206080604151109060906090127081501 66
    0x985080140d803003901840310860525448101c0640404400e01035107000c0c02e107840410010a01c0c00503d0b09003007003002c203901c0921844410a020b203440c0c00e405203500a40103142c031451907a50080d918010b0943c015200309080459001ea01100819000104a0110550b000102c5602e403004800c3c1d40c801c4407001000e80e4801542041010720310340e41a0104407006059407481d4950707000351810754086401c96000f0140c00001c0006030b141c8034074180340c2c0c8035040c5000c1e140e070300e41603451000b6804140006081420f00f0740000c1c507141c0e51301e400c5518041d0f0006040d6124149035524115144d05401120710864800c0006045410005000c0e01d00400d10703402040705486184041d46e40f1603046001001c0c1e45d031228400300b40070750b041040c08e004070300c1211000c400601a040000172165003500385a889402007003031511a60718003040d942019011103002d039850395400010b0300d900301c048001600c044404162404c03520359201081c0c080722060400d555010844080200b25030200f40a91001039 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 772398408 1250 772397158 772397161
    0xf08160f0b18150907030506091c030b0102190c120b09060a020304120e0d1205031f050117060f03060115030e06241206090c13090b0601080a020708040303081806040b 73
    0x5610003c4220b03000301c0640300340c8500d25280d407900c50525500f00c0e04580b0301d91000c0f000f01c82d803040411900381e040006250402c220048840001d49603440300803d0300f0b403181d41d120b00c5024005c12008500c020207003039403a403509090302d2400e9005141c2c00c89554013540200c2000855800300d900071248100d074410700792350f080340704060141e5084045000c21a00304004180250001d03202054030701c10140070340c803950f0701c4c1d00e400814022501010141a21041ca02c22030030005660040c840c003e004c0000c441d11021582d804c1d01040c0f82ea182e0401156041c03113400000a240341000c62100604006a501404041c8022035100d50705c5d80296000c00c42d40340d2045840380c000c860705885464450307000703141204500141440502e81036082d6501100f0340c00c0404d25200915003a07c19195604003032006101200d4292500d080e41c10000704203e0502889000180d0942d65541c1126100713544140f410b521230340c80341401400710b003003140d20190740301e0707255071046440074000345807131180d41d00c2075100c0460b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 772399658 1250 772398408 772398433
    0x3121404080a020a0516170d050414041e020909070806090703020705010212010906061b170906070501020d02070308061e15040f0b0a020114130f08160f0b18 69
    0x5078800c10300b110450042079400000600244055004010785080d030301510f030b0400c00100c041c00c03810b00040c0b116520039400c0d040090f8000c402e50f02150948040c4054254034000442c01601210b8050500183c502c042c8d1103a10056038090705040400341d65808169072140320a031450003007a62020b03030017001d620000f1809846a0014281244613000143c14500c07420354041300d52038280c0048200d19103408050010720f6228100ba801403915a24149000b801c0e515129090780c1c42e050b1064840500003040e0b20032343c60320011105002c0e80803001715a1001c00c2c03c4411700079002100d00f2000140c414022620a02d0640007100c40c2014402524180c3c00d000760801c1080705030340c5104008000d00380400208605000f01d0480200101c0314050381d5503800c0038000382142d0032144503184401070001804183e01c0e00740201c018080d441026034113030b09424200500b0600640c07141d800180b80035980081001105000784000b58030611201070b2584805400c034050380b2100703040140301e500c2140103500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 772400908 1250 772399658 772399673
    0xd050d0c030216140c01030212060f0109050613090506041118010e04141905010303170c07060507020d030b061e03040f02060403030f120c09060c0512130303121404 72
    0x101842070400524007400e400702e0194003010080d060b200120502c80140840405100481c0522001d01c0e0441c64080001c03440b904465010341054060b0700140c0341100d80d41d0080704450060140105216140e551000035816503d10301c1c0104a00b03542004089042c42c04c05000b401000ea01c040e0f1000d041c0031099440ca192141d40c43d4070a41007246045282d404d0381c4880c4a40c1d80c0304107003002e00b00f100f440c086450300d0300580307450300461226142c1001000800d501200d02045c9201000003005140c41e504011112030180c202c0c0070b4040ca180c807040c0b008458000402e9400b906003500c3c03e200310300b82842004203600840024008414824018030f0481c071000f002143d10902c69044141c29803041d80214180e5046600110b001c04c49003071000d920300c0d8004140400705901c115040c000548200c400070300001c000c0c8100400d00c50310b050f00c01c0400c4010300c00242e0720318900ba070064483d40d20705008d01c4079040c0ca10054001c92020500e03020350040714050520b580070f07521144100b580ba5603a9852 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 772402158 1250 772400908 772400921
    0x611091302180a120b1b041701111b0f060108030306010e15030c04031e020d0f050a02100207180e030a0f09030c1d0106020c09040803130506010801050411030d050d 72
    0x2850101403102c0c1d40d98582d56070007624040d041135040016102000e20703080c022407001034032510242c90400541030090403442c046400743c900b4104c0700854031107c655403d0242c050700a0008082c5404901500d080400620025044c3c49042c110381c1000c01000701607484030001c1c040c803080c0382c008000050b515401107018408004016000c110a44500601c1940581061f503140001c1d4500040c00c0083c412020300c0080c010605101071800e2092a43c00516126031482008201ba20b1583c152406e21005000010030b558000e0400064022503100081d200c1989019640c54045000c8035600c1075000352040b1000e0100ca00300940c903060804505981041c3c41414501c100000528040001240710308510000e0501900c02107a003002d0415881c00000143c10001c00c5510807841284035540d8001c6280d001074100000c40d54a0300c03510510074040e40410400b5040340b06180000509c5001544641e1060380608440342218001008142d00c9061304840703030b80024020721235810356101652010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 772403408 1250 772402158 772402177
    0x5070504051207080706021b010c02131401080616090b0304051f02032710110c010e0303040203010f09030804030302250f021005041a07022b0611091302 67
    0x541030030790390000100c5910441004540c20f0f044010200020b003070403c501d40c0902018005400100c01d0100c601c019100300f4094141040300070280750782591596840600300c40d550000a10140a0303082030303004155403c2c401c4000620843d000181c04501d01d180d01d5041030744603591480501d16040b2004215007028000f921540a0620b450329090820f44500e80c11940c40ba60141e180d10348001040796903c02d14400d180c2440030405d0740d00b400c0001042c00010802917840025106000c000c2c507807020700030182503a03095032030400c00300089040000a58440c42c804c4000344501c242040c0458251303400c511004010443e690f001c41c00003400394000c1c00180c400c0c04202c41000c0440c04100084001e031807801e59007118a0301039034041d420001c0560b050700080707060603803a2520703100101c074281c5010034050014000200e40b400840d62034490040940101800c01144490540000701030444a50405c45101e0b1a08000009404264095508070b480040030359180d80755040e010400ba5008841e007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 772404658 1250 772403408 772403417
    0x2100204140d141509070902030c0f0a0306030b090c0f0a030201082e0b030a0c0206090d0c080f030c0c281104090b0a050106170603100b0102030d0203012301030e100507 74
    0x604a4000c810011302c00b03166680291180b803401c020182a041a02d55089600c085004108001014094504540170031200c108103554130810f03400210010155604010480c440f16810312002800020741940804021640040308010710030420101c1151071200074013088083d00050001c007001d0213002650080c507040c0c02044c0c0017800e1030341c1d1100c1c1180c11070200c44038040180200101c040c8140300022880c1e000920340d904120740d406a0741d91002d00c601c8208405201c00b6402c2112450980b02d40b004d490514035101c0c2058204d8500c69004103035880e115100c0d03a5190b003450070781040100040491100386141080715a103e48000c41c80c28540b03940c01c00d41350000703040050b501d5448603202d0702d0320150000c0d440d4140400101543e02c9001c04005070300000e0140500380d600030030300040c090080000040c9001c1100d0050b400c0d030141e40f0304040c0309803000c8000101040801c00307810068103201303101c15500c1c00c20001581220b20156005000b5444000900300c450319a503c442d8210105042 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 772405908 1250 772404658 772404683
    0x102010603201807030911040c02061f1a0a0e0d15110c0318010f0e090c0a1403040302100c0302180409020406080f0c100e0114031906060c020102100204140d 69
    0x100b1103c2c0005132003243c0007030354521882062180d03a044140c00c0c480229014000d9005c003000c000e503a200701611500d49483c000c402c0120003030b00300360364100900002c240c04655442403a8000300716080b800841b000720350121032450176440c00d1156440855440b03200300741d40c0517070b001c82e890080c00a203075031fa600f0013000c0050b000410403c00c06420f01040740c950401c0301010b4800010101d40c0e03454110014000b003400300601e0365940200310f540c8031103e03c0c3c01c252112409101140c9800c0320898004180d18004103103c141940450040c0e12001b282c00305015850049008074100c0c41810707441c0786284155841da42c2c0d1403605401650145000600119146da00e0b4032405080000c0d90840007000e0348803040d03009203400d160703030504013040032414140031920078800042c00c09100000a072984000000001c0c102d290051039a52a1541d801010480f03551550b1014080100380380059000d0311454a40100348005da000302d9086c1c1d0558030480d00215200310038011802c01040084444070004078 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 772407158 1250 772405908 772405939
    0x50108070803072a0909080d06080606030709020903280c080c151c0501060504030627020108041406010902270f0423090a030809030a0509010e12100209010e010201060320 75
    0x25083c046d600901d019075a9030309040856049811036172003000150050f41c20006569408105481156104600982d9810a02d00000e003801c400201c0a02a28665206240800104400f1081072446080450b80b0643c03520f581799038030401d022100c0d078410390410318130b403991110502800d0b01450702e1341104000f4540800780c4081e40d01c00d8111400044010404000f8410140941da001d014403014040300e98441009031901d80d100707c0b0000e03062000e40e002040402c1740c02c00080c20002c150000b9240c070f40d612854004040d602c00528644070203103103501c0d207694008060b90508c420f030000340203090800c00f600a11001e8110102e24026036001d2a5003e1804443c6801c0f6500ca041c24201070a1801894a0090444000581813a0080c3d005015079403c3e1900700c03084a009003803d0810404c1000305400080c408803070500202c2c0300340034920300c03c1900301d40c9030041c00a00c0c07000d8860030007001c085001282211328910000e448880341c9586003102e000421031907199400c0c080e004c07104c0b401292 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 772408408 1250 772407158 772407161
    0x1401050903101b02160b0d020304080408010f05040c0806060a1502070905041407080d0806040f0f020d0506270103170f1606050f06062b0f050108070803072a09 70
    0x64400b0740c0140a4a01801e451607414404a80e805015010940030981041d640c200e240c0950b80c7d900e480103500001160a001030502942d0080440d00000d1101856408241340034220990707045805032010203001c11440700c049510ba10078000a0410350000386089182801c00340f00710314107021341c0944100442e400c5070a0103640d01ca035008040012141480c8980245084216071103201650410003041444caa44015106d8200c80100d40108060340f14100707140060411901410345584002504054102c15820180c4a1003040350294202c4808981410402d500042c803e5124289800140001050540b14803003091400e2406801c00558100100182d402140444c800851070400c0c01c0400c40c4034010386502600c6103603038482e141000c4001c078144d4002c207d00e4502c80c1c0d009803205004200a000c18982806041401b031101c000610306071402400b0a001c1e21500e4080d4450101c1c0c802c800008032403055074806038803096010004001c2404100c100e41034034040c40040780008509519 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 772409658 1250 772408408 772408421
    0x10e010c02060c0d020309090a11040909110a090506040f02040b090904050a021809160b0703030507032414100807180306020a0e131512031e030b03060c0301140105090310 75
    0x1300e400541d41c40840740100018208000d02641840e0305000c82010308072203980a8804580f8511004144000790389003480000c079a4000990700030300d4040002810401607000300c1c0c0100c03c02e94080000044040100e0241d100e43d00484090300c00030080c00d15542080c01400341e02c00e004400b40c429a940f0b40d400200070780e0b441c10b2582e055480c464180002800c090144400080c12080c503411494500400c002d01ca00503200d020f018569581d0000c0c06543c001c3c2c120500b000d80700101000c0c00d1502504440381000d550050b040280c0c0e00e020800d4141c2820300c1108401e2902e0b8079402843d0383c0e1100c049031103400c810012550003452260000c00078580c1e00203444c0c45106511414007078880c410a05c010082500c90600c80d10b8140a0001c4540e02256042815211080c06060014040b0304080e00c0c0d182111508014092507020140405941503100c0168100304400345d0300c0b10f0300c2d40701a04030300b80020301440351083c58880f001ca4556025000031302ca50701002c2c040e07840c200803414141c07003269039 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 772410908 1250 772409658 772409683
    0x705030c06100f0509012c01060201020d20042907120f0516120203070f080c191a04031209031d01171b090a030c061d010e010c02060c 59
    0x444428042c0918400c0d601c100a0311000c10360100f004c0c07421001400b0042c040c0700c0c501c00140417040e90303c802d8402610542e94150070b200b2442c0603580d5042c000f4001d5001c02e051005a81c980303c040c8040b201d0940c0c00c641c80581400c0100c0c2464101003401d49842d4400e00281d0b007500e005190444240f0000c0301803c0e0342401040301c440c0407c039006c405004e04e48140146d00400900b0000144000340e00c504a50406802c4240c0c82030443c1301e40c0f4140c1c80e5100d0b1540181070f044911074078204201741030008018000385003050360580017035080c18a04150002c41c0041c104120b28000c94a000d64082c072090303101d4042c2c9400703488220611511004c42d040c7c00400e400058000032b4a4181040308428440704000078a00480c0c60007542140c4541880007030700d0a10790100540c0000c04610120382950035001004048181440d88d83c03601d400b80c1d4215200c2c51001c1181640d03d41d0700c4800c10340200c100c0c074006031118295a03a00200443e801581c44000f264080424001000c100340c00b040f07005110503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 772412158 1250 772410908 772410913
    0x70303031b0807020307031101331a0403110a0506190314090c012618010e030901050f0702010306031b061403070f120f02031914010302030d0c080705030c 68
    0x100c20707946020303090140d030350050103121011060049065000084500e0141c0516000c200411900361040c09040a0040307400c60388020b24038614040302513a850300c8218402617801501d107030381d5142825500540b201011404d40f0900080002c54030318000b00031000d2000f021114019154030000e8000c1c2c02c0307503024400c18140c2c8008455000c2d0584901d040d41c50001c41c0c48daa6610700491415035481c2c4028915040104044080742c1100102503021201c500c80100c080c024944036408040696540d903c03920150300705040403d40e8030300801100c945400603946d052400b0345c50001c0d21200d41c88454103c3c101565420000080f03000a8480424282c030a4580d40045160002c0180401e00f003001c01500d9090800074042040d0708990180b0204c440341c1000c244140c10480c9000040401c0c2807564401390001042004176042e100d00c6451042003420200310605580703642d92500344090000a4041d030240d140c0c021030b0382c01503025a50071441906001c1c0380c0300b41540d45500f542c109030519045503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 772413408 1250 772412158 772412171
    0x5031201060c15200a020c0d05030306011412010b0a0c060f051504060e0a050402190305061605070b06011b17030f09060c180d0f0506010320030a081b07030303 70
    0x400110303005a44145402004c2c407215141c0c1c0c48107401c400c00040d142c010448002620111540244007a10400100030909000180941401c41d01d95004591041c00203043c101d904a6031110041541d11000c0c0243390f001c80340e824200080389942c0400013020500624079045000103445005108520817003010124480c14419500500c0799105400e05100d1030a0074001c1c045032030b00803800c650124080310049540c3c0c403917002040444040e070700354560040e800c403004030520400150b05400348428000712030003001000c0080710f042c000c80500078000b20703030b20021840640c8a07010001114800301e202c040a81040c1c0d403195142200320041c3c008009001c0300b000204529400c1480e40b204040b03001c3c204501c4e21964070b81962003114568100018440090001d540764658600441a480070004086031194201141d03600c000344421609151a150078501e4015507000e62841d0780c60242c000d1610100d0ba81e5030740083d403c03d1603024664a1001d001000b40d51080201c0030040d4066100041d01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 772414658 1250 772413408 772413413
    0x1e0603130b060111030d0b0402070b090303010e181914030c0c150406080f1e0f0609060f0a03080309030706020307080711030a0c030507020a080105160201152105031201060c 76
    0x641e50050040b410710220301840b5240072000300c11120700034035045000980c0041c11001038002c0c012268090b008a400000b0005d034804000011410b07a022034080071a81d568a540d01c016004003940400b80d590424000c5a400004841c4a040c440e40304038040440d034261094824a5a0040e40c0801d12503800411b244169080214100c2c2d540c0380d992008600d40303030500c1000740429001a12109800c03c074400094409540c200d213101540180042c2941181031580aa40814600340c0300c2620502c0140e010550618010780d01441890029210400c0c0c64a15110748260b50402080c49401d40003c101600c0085c22031f20041d4070403822a141c5101e40d09000400074010f1505100c41c0400740d0003008130b49440c9030003407600d09aa99040c903007241d85240038400314000300c3c2680d21411a660078141400000340450034a070403240b5043c1d0003040300b07088201c0d0022440540b403040070000400c40c1d043d81d884c41100700c2c20b40001c030700409c104d82c50314441c1c041188240209911a10021300ca10600808 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 772415908 1250 772414658 772414673
    0x2d070209150909240106020a080a0207050402190201240b0c0f0706020f0609030c07090c0315030305042c0a052a0405040f020309061519090212100e061e060313 70
    0x4101000d000b83e2006907040034406542c8d400e080102400410b400b0480142d154800c0203400007070300c4041e005648031b84940c600c4440540b2511100320255080485003d02480c07094052540340f41c5589040320142d280c0310810403158070400f0f1003040741c001c484c480045c5010411000c0000d000560060000b0b51820980c11309042000e8120600e03078000300650b100803880090303003109a448410f40000c003240c0000040d0002c00710140170803002e020613030002043c1904403010b8421601100f200e00040c040310b1034085c800118080444c01c111012034041409585503a005c039501810041c410034903203002051881010741044010300941e24001030912003401c01b0f000b0f112040328914415402c5092030031000e500c900c0000c221149024020800d411a41d0314088950354900ba44e06103a05510b4a07501205d010394406800caa4444c800500132034042103d8081200071240509000d42c5071303403110020440074124a440041144055001440055440300c000754068101410302980d1094145001c05 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 772417158 1250 772415908 772415953
    0x10503010c020f1c0e03060f010e0618040b070905060f04060201110304030e0906030327120303041502030903090a090f05060109051305180307082d070209150909 71
    0x400b150058003c1e00040200000c0001d00c002c02e280007504080d140800c1296051074074982c4a60502c241c1080c8501c5004012082d030507140b5002c008a21503640078240501103030142d0019003900c1d803090018020400300c0003402e03007001c043e1905030b91a56980c03002407540c0d008980380140d0284009010044550248100c60002c00464001404e5160949000c0c0c044001030380614001c601c568001241e60b0740500450f030401d204020308414014041e2010390281d074981ca41580952040840800c2c1031b07100000b941d124951006541d44ca101c0032651840203508040e11040d120300c801d0100381003035681e54000d1405072200400001c0c00c0f501072120003081c0c4102a0145040c48040328040c091a21000c10101c07541240708400701d11500d41c80c038200c880d446802d0403100380e0f0001055503010010301c24002c029200c09040011008011101d102408000300c8092120a401c100501c04c014108400540d500040491110321940303242d80106558032011507084030030742c010b82600d6480c24071401400c0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 772418408 1250 772417158 772417181
    0xc06200715200306010c050c03061003050c032b030e0607050715090b240307030f15020309030a030f0905060711120c03030604051b071a0a050403020c1905061201050301 74
    0x10b4035035580ca8150400521010740240d0401800350086030030320a00f00006041c1c280c01a0440e82c0c0e07403809a15240fa4110540811152401034507101e401e103160005c4d010440c610110044448404c0380811041040048065002810b07210ba40c54032005105100591040c00e554941d02d603145894644100083c0442010703c10b803a1811241101041056030b0580d40804130120904002c40300d01d8400002c1c2c46051261a45440741140200030402c0390041c0400c6140300e9113a80d150030450300c00c0304099000464184006038010301c50030400c20b209801076400750748500c8000075103d5180c1c07581c50030720800703d0341d45000c500483d0715030080220401c06101c0c0202c8454440c1e0034412801c0d500d035100d10028241c140301d10384a04c0425040d41d00c0001260f1241254404556503000740c0c070703000210303050347c8044070001d1112500080815407503000b680d2240b94075a01803e15105698104140700c80403840c00418810a5480811145c851400074545030181000d004207079858107041509685d0880b40a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 772419658 1250 772418408 772418441
    0x82410230a061701151b08120c070f0206030a0204031209060f020703020d080306040b030607030b010f140d0c0e060d06140a051c03020c04090809030114070c06200715 73
    0x1403d0b901545841214191208110303140c4403501540802c03201c1c01469000b44c82d001000131070110400c03010b400103120700140c011480e00d050b62141102a4a401446005080f03d07103511440001881d16000455000e06907000050510b82c0b01d484a84641841d0500c140126100715403e21809800144c11140c1d46064030052000f541182e0111f5402c281403000117105000c04030105180d6a1544c001d0741ea4110080c04480180c40c02c3e45005003d81070440c00207001c00c02104c4114140361049048400b078494035110300b49420b00140c0380e00020103202005000704142203510720029035070b40b0f0042034846c0003514007181150034187e1078081d05568100c007501c20209800c0410443c0c840031426130342c0100400c030a502c0802c04d410142e08200451200303940c40341c541411a0100281d0402030f107035281701900200080d9000c1c00741004001c50a44031080444c0e0b812940d100011017a4001d07100c410700d00f403115441403140c01544201a00071303e004503012030201e003102c03010103641d100d16007886000a10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 772420908 1250 772419658 772419677
    0x12011403060a0c050a14090603090a0605060603040b01060507021914040f05060a061b0c12060f1e0b0315010906080f07050604090911090a060906082410230a06 70
    0x82c180303100d203050603403d2046082024401b00b40c440203540d001c0d28060b109568032301d008040d094030340c61465000c540341c2c0d1400c00810881e0811900362407146600c80d0511445900f030074415644c1d60030814040740c0c028050403417800402c52003a900340c01020542150304814603004100030950b4028440c03540410318000400040c1d40d035080b80c0c582110101e007003544071080d0000707100025203845400900056400320000504141c2500d000c075615003d28400c11001c00c0103854001541c81d9152045500307400c15134200c0c120350084d40135014108008045464803000214000980c0303509a01000032a50358510800606c1c01c24400c0c50710541080015060072400e00740040c415000300e0240e45041907894200c00204141068055501c07a0002c0c184403407454a0b00524010300094020989041c0c240320b00041c108100041d0307182000c024410f0b00c01c0da11050340b102984200e000f441c1c0011200b40e80c0000848002c40b0006d10311000c0c03540c445a403c2c41403401841034401c1d80b640120104040304030f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 772422158 1250 772420908 772420931
    0x2130f150e011a07020f01080408131418060a14030c031e0c011107060c241d070b0409051e04080403171c1121010305070e0c0d09060212011403060a 65
    0x4006c410607039090810f840c00c2d03221ba0820340800d0062016a0f1010046d9900c049a005c01c14403141030742d814202d0f40202c0e030380600c5190b04005802039070b13060b4010b08024030130300c840c1c01c006500d09002a0f000e4115441d00c0b50540020346400086c0c0e802a504a81071910a98810001c3c0b00001400c802820704145415071101859611401c905c5600108140c803283c0c141007140701d02050504114a0110311152012508030400134812608405420441c20758025009040420050b0445003e03105403401c2c103123820f0035070001e40310040c01e10507860841100e211040c008606901e00440c010000070fa12241149010807071078000d501e00c140000d41c28441c07045a41e10200d01d00040050f0410041003403600d051124072203000d10419688591f2500454003010000f00e05014106c1c0d004000711101140e81d481603001c0c1e007038282c501860b00e440c104031a001d42030707150708810030451054100500c0c0001940d040c8c3c069040070b03003220204050402d10040c00c1c0c5010060300ea0445552103007044001000c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 772423408 1250 772422158 772422169
    0x212010b091f03140d0f0306080c060c010f06061e0302030c0a0c050a02130c1d0a0b0c0718021b0606090a11070204050108030405030f010902130f150e011a0702 70
    0x2056142c605402c06103456000d02020141c00040d07038060303822040c2c54851a19680c8032481c0c009a0b2001880014011240c18400d01488003140c17030301000340085644401c20301800d1703804140d20803410740d00c400360911041458462140104983d81c2c4a01e80310504c0402c0d004420b09071060002014014024014644202000c4a20000080c01c2040406180d4641141000e0404001a60265240681c04440b51464008a004981d50baaa65a9881074040e840d04a5015604e0a9030070101e80384081c0040309051008014080101c0b0442d00c2c100e50302d41001c4a101000c1c5114040e05401207540784601404000b40c4166615610290420b481e0100c08180c028400a005e0410680c6901c81c501c1c15031003000440f840306030040c00600881d070312030700407694980c480d1140301e00a20030300032001c1040406100f4614020f5009141e900d5030404d411101d006020b40707140700e0a030300d86c2d61070a041011012040c00070041406a041c120950702d403c2078050015030010601490100400a000050b85c48 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 772424658 1250 772423408 772423411
    0x16120f09120b061318110429011809021801110d0c2402030f0906090d14030601050c0316021302040b07140a0b04031d12030a03090219120212010b09 65
    0x40d10320303038182000394814501500344179240c1c64a61001c81003450a122900004240d41031080ea001d104405a1003030482e0030b54010030010082c1d80c05003803011401d6200d41c2003034014101000580c68001d49460b02c91080740c0c0a0940c10140c40e800300b20f2100a560011189203210081c50003902c3c140761899400380100e07500c2c000041455072030b0340000d0200300c02c480c203490708140c04903c00c6490f46091040a50101026101140303d132040c0300001c2c140410001d16540031072019a1507003402000c0c54440c400741e80015015606000080c4458203000c0010005098004a100d51052a8045a005104100c0c0700d03503010607421801044107000c4c480e4031078100c1c3c040b10b500c174004084075181e00092904042502c0c0c0000c0c0728800310000e020502da404070651111614842600741420488010030121320599580c1110607042031010158284c000d03070000c04e5070303400030300034001d2041b81e003512031904121a0071000104d81081e40c0d007030560903c6641600c030491040000c00c01ca500400004440100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 772425908 1250 772424658 772424671
    0xf0d020408060f0441121602030724050d06180903091406040303230f030f01050108100302010c03020f0d0f02060105030a0803060d1109130b0f011a16120f09120b 71
    0x24119800710600d08200f04501074002d82001b003a07100c0030b1803400345a00d00038080c4241d10a10840d1008207400f5030b00100703c4010b1070103d80854051050482c183d605810980003501450782e80c034000201c1113058400c010500c82c81c2000042d075000e242c07801424074800c581100c15a074211080710036090326614100c6065036054182081d8914885c1c0850301d08910102e100c49840b800810070032001081c1c58007a50045c115480c803059560b88800046443c0c40702211000d41507002d02d18200059402008441c0310300c1e00038418ae41c01000b0b0b40d10141d00e04a41e14a2200024a440410203e4158140700150260104070b02620041d00301341c40e03c80d03182c00041c0106210741082d0300c2c49001c00c444a0300c60024206c020300011190f24142d03850b01845400303035405466612000c00020024a42d510b49c4606139218004100c0c42e15519208110b0150041da0388044004040b800b03000101c1c2940c0300c42691500c84d542d0f41040c09400f04002000d21686500002010300504130440c0001d004c4d981d015480003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 772427158 1250 772425908 772426013
    0x121210030f140d0c0b2e0605120106181703270a0503070302060415120c0210051326070503071b0e04031b0213021801090f05060f0d020408060f04 64
    0x20301c51b492140940b40d898404072101d42801c0030008689800c200035084110400c140702403e680d035010b041d500c4400d0408807181030407801c0d0007440960700e645400b04241001400312420000d418100c0d980200240446070108100704515070002e01e031840b1920f015000c103a0180820b2499540842e203507000d140524a840d150180032114034510910020b200c0c0b1403141400d01c2030714003a560207912503441824a0900e80d0400d000106140001c0780e9180301c4660280e2140c0049194810f1140c25a00340b080c1c13041407101c00c000702c03400716800300098403a080c014042005414584560341d810301c0c040c2c1c0d000407103040f41c2d5400c200100e42c004a903a00213141c450740a241604d590310020306041c00d25002d80c0c2e91f2510125950101034a244070343e1038030b20130a807101c4200d10780f1820902c1c0b030b07004148070b820b038003000c01c000740d400300ca0010018100700c000e40310001d82041e4403007039000d0034403200704c442a4801124400300b10500c500c907008041e400d0003e07500142e8000306502d941c0c0101069403000320081 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 772428408 1250 772427158 772427191
    0x503010e100f27050c0f06180103022101090c0804031211040513020a090512100b0d050a03080702011401050901033905040e121210030f140d0c0b 64
    0x210075030081c1109680312403c1c407520803180c0301c44002140d80000d050701c41c3d200d100082c1d1000e0a010443d6040c00c08001d00507403c200c40c44050095150740c0c80718150405800b40f0441c200c681320301048414400c2c0346610710041d036050401030b208440b0581a00003c0184500030300c400301c0e400812001c0000e280c7c03140844d612107010042d00040c07050758403458000c8148100c00e2012086a409040320785103650f0340f100740664a100f000b04003482d100021016170800e44880300e001c0990340c004a1202c4025000d140d4a0182c0e0b2906400c003852400d0580100c0c220404200d07800c5d50a10498441c081d0003203c001503941080046110030005000040c02c1703032543c26111000a036982c06207038200059103980050710200c0340540c01c10982d0362258030b0049091503001c200b1214041824400511112001800c03d001d01d0521010904003900b2500800344442c00031010803105403503000118015a1400319010401911500d058604050041004646a0701100040603686242c2d04401c0414598802 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 772429658 1250 772428408 772428431
    0x5060a06062a050d0306060e3f0304080c130203011203030c0c0c030521040315090305040905010b1b0a03020d120f090c0509010605040806070f360503010e10 69
    0xc0d1030650b54050040c0c42804040300c000c0c1d40c180c00107401c0d10701d07955400d84020300b008c0a001525103841c0003907690904050000455003149400e4101071006c0d0f4900404101d080c070021821a0b1085d005280030b070300702c1d45660001c0c3c1060700d290304a10782030080c11499985440c081c1c1503280c0003510020100340d29940c800c0e0a4504c2219682d41603a00b00e074404032210341d00e103450781d5940240d10f009907600d0442c060701892040c0d00c0701620112600845640030070150901d501c001000f1804c011028040184000320ba00e1000e0321465001e0290400b107141c0d00c1d5501c7c0c00140620308142900c0e1800c0d0f00c0307181120002640805d80320600041400c02405403041c600510000d40100000c1a006924140a00080c4031742c00109000300e640503036421041d41d0f00c4075000c03189403040340a0100e4562000300841c01503881010345070512282c519000401850100990814401e140110120060030440540e00300b19901c071030000510003140200079213400144980e0300c4500e00074280c0f50040c0e444166541 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 772430908 1250 772429658 772429727
    0xc1a060d0227090c06030a09080f0406031a040b010203120a0e240703060302010f0f03060b0c0303060a05010e010f1409090103051006060305062d060a020a05060a0606 73
    0x40c5594024000482c00540d090740100b149980c80e00c01d1044191180411402200400c0405500303802030071451860713170b8040e070b0080a0b02d081402211551802c10809441140e80c5000e4005009503560100301c8034034500c494556030a010b07006a00c601c0c03800d0201c0132503a80000441d5882c1e480c0b800c00903416620f10100a004083c255004562030040460070883c03105155205152a100800d040c940c0761201e030f030700314111a014000280419228500001081c1c01400c80308140c2c1054a4080f40c8543c1f6046036244680100ca1344100c81d81c004401d015080c5414034484c005401c0030300c0c2c988101c0c0c151100081526000b024801c040c420480c0032010010001e504032059104003401170859541e42c1e240c44d554841021030f4010712240740080104043c1c6c404e004242c050040188075541d00c0800d42903098a280c8445400105110314124a44180d241c100141c1150790003600603012480d40e5050503424410004c0000c04494603010082c05010b400c01c0d4000000c1408a0304170005800a48801c00f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 772432158 1250 772430908 772430929
    0x8060c0f070b07020a05160812030603030301060536030c01140a05070507210c09111b031603260112081c0212060a0b0a0f030c0c0816120c1a06 63
    0x1440c50140d19481f026403880102e5110846e200c000031540c03c00d07010703150684103000c15076020340e05408c100700402200f4843c00c0079003500900e03098440c0c0c5c028081c1da801c515518091708414a01008900030002c00d240500c80014805001e0810460381c12024484e15036034483c02c0071103020b01101240700000e0050800040d00a80401d10149028081200d031181c0301c0c031078100c0103c51400072440302240e4000700d802411801d088003030415003880407068a484444410b01482919840144002c4900c41207120582c0009802502c0300350030f102030900c440039200045c00d0300da05d8411080f40100408009080145050744d085072401e40c035414140100c460384403c2880e407440050022581c0340d00ca0703004118480c012101182c41c41003840e070312002903205000c1c000c102404154070085e40c00d101c0303010780c01000d945221441c003001481140c0c0d9410341590025080c04101118044802c410050351b45400100d461982c01d0440011609643e9403c0d4003400351000159042850086440390b02c6503036100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 772433408 1250 772432158 772432163
    0x330b121504030809190b0a06120b01030215120a06051003091a04050a240b090108030a0c02040f0e10060e22150f0f0b100903060b03070e0f0108060c0f070b07020a 71
    0x1100041880e0030405034544080d102407c0d030b54a0140002500c00b19038105045032079000c120580141e1840e000c00c9086034040e108104a0901002140d4450f144800040c2c840c40075000c1c0011868140f01c02d10190720490348071780052619095208000c98a42c0220b01030a04039842140065916840c00e030b81000c0c0040700040c50044030400e1540ca040c29040c0001d2420108441003003030321003100401035048428400d00006810410000b0b18440c8508140061180040c0000c1203140002034202d0403035155003003800460b08101280480e044030340c01750400604e181003804989003404654460480700c1303e002c64110060346c136683c104005c400b074640d4190303140c980c80403c5440565010140503040203403181c151140b405010203a60315202040e415039030510b9950005150440c2c0da107200420a9a804c0e9a05104500c8001628100d905d4554410f0405461070516549400d8419203040e0000d080901080001c3c4080443c104000082c0d07680590400b141034402e45031444141d00700854a50301 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 772434658 1250 772433408 772433443
    0xf020414040e1c0f0e04140609180601080d11060c0919031a0601180b04180e2512030c0b040f02030a03030516030612330b121504030809 60
    0x400c211508032500c4150910700fa02c0d00105c000c40e0408210480303000444002400802c103000c0345590400014860340000c040403500e0345405504030103898848268885903459101011000c07101d41c0c8412400059600c407001000e042c00c0030b401c801d01c540956401603014081410b1018401010307154288c0003160082201e142c00304401040115560040319024081948074240348101600310100d0411601d031141c120b81000d00301490420228038000442d00740ca5120b0311903d1280b50700b4030042030034010542c8a60001e01240200010741c401c15400542c0806000300d000700820b804c540c45104095000f8940c1d03903941d456191114140044c40301c040d415114a43c200d0040640582c0411300503c07150201100080001800310b0036140c15024245005800f04600c20000304035240c580c41140c2244510944000024010001c5c5848184498205a143c56034540b440c2005c1d40c0c034102a900c0c050283c80300c400094416100b040d8041e000508004810b4006003a2242c10b000c40c8443e01d1a4019 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 772435908 1250 772434658 772434703
    0x608070e1506041206050a0e0321060102010608010f063618050303070f1b03090e0703020f1305130203130209220309030618330204060203030a0f020414040e 69
    0x10b0050013403801f140d400d407046160550808411400205550100c0c1d41d0340f10300041c000c805450f10380442d00c05881c041c199900c42c580400d02c2c0c10280a10920449a41400900a0f1901010440c8203080d0511070314403000a0f10300c0c104410b0349900061b078079406088082001003c1038180044400511000741c45404040240f203183e9074030a0400c0c856040702d5480301c0312a880c4009045040b180620000c0c0030564042d001c00080d5010310380070b540b04c02c440c140103040c886000c203468065403168050541d800180b44050201b0724101078407170021100c0010441c103528200b030003070a200003000360203803050010400156444e5044400d5400813a00d2040c145145105454050101055800101d50003070400c0c0199013004088554245825004a41e42e0101c8060a01c0e1010000040c0e0301440380d101054150501e0074600d0006000501c8aa401165249081c22001d401c41380a541d544540500410040061902404000c00d81c5001150f0010b03202a00400c042d19002038041c7ea040401503141 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 772437158 1250 772435908 772435913
    0xb0106030f06080622021201060e04151103130f060c090302030f03031501050304061112091005070e011206050901030605044b020909060a0608070e15060412 69
    0x1007140c0d41030074000c1c1c0240401c1d07840b48a010b44802085940b100e4011140d030b00b0103204010b15880d24440d60003e4039801c1101c3c80c1e85903031400d5600c2c0d90088840c2110100c10300041001c03250842c0103000c40c45030100f01d9100d0504c41c1962610018042d50440e4009031510b2090200314404100e00300e0703000600b04180385031024050071340e009501c001d83c4030340151590000e42500100483c0d1203510b60780f0030034100103d480010f66850304090429280c5c0380e950340407588a0328100c1c000342183e10182640100c0340c64010ba43d2490080100001708069080906000390a90440011050741c5d6003401c0c001600d405202c1028020007aa0b4451540040b01e14000024041b00794802400f41707000310700c042a607072180d10b0110191180c00d26081d240351504164880281030084a121410300100b1500d90903a0858000848144096564982d83e03040300f820f1000c00312241c841c1c03000520068029040d03081c40c140a802d03001400401e50714001d0b5036501805607654584044802504ad12071101c1403048460 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 772438408 1250 772437158 772437161
    0x3230312042306090601080f010203011206050c04090f1506020d020c210a1101080f0f010b030613020d14070c05100510030f03020a030206010909080702040c140403061e092307030b010603 82
    0x28411f01032070340140300b0642d2820b641030007101d042e910140711441e00e903515641c2d14401848000c0240341d00c108281b1022a14041b5806401c20f140c02100000c07891113140c0080c101c072002d455104070b06641c030601c811240c0940121b490061100b003200d000d20010b0b90550108603c00c1503d0882c1e4150040d2075140007003000c2e103020701e0140c540a0342c2d5400c841e9034030710154200003400e0f105414804100070041002d50038440040da07109a011385108141041da03000c11080e40c110024003039805484496001c1e10041c40d10302c5940c0b0075030b103284c08801010952200358580340e000e0340724000c07907440d0307400107176a2030800e90310078000d5500c02500d407500c110908000352540440c1100b00e0050065800004a0040c24042d0315107240d000a8602c0c0f401e1002d9007004004d04481e003105d002d00c100c8100e55810320306424041e20065008110100d254001c80c0080400100d11130a0b4501d40c0b803400c1c6140c8040b500c1c0c04168a0441d140e140102e081000c0030b0105032404129030300080503100310030008a50290b06 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 772439658 1250 772438408 772438411
    0x320030c01050709060206190603080a120b0307120605100510120b040516050c011e0e0106080d02031b0304090c03020c0c040b060a0c0201030e0106032303120423060906 74
    0x2403034000c2007181c60740c1800f01c510b130110b0300c580c3c8010790141011440740c02c040c140000418051650000c1c200e5982c3e940c10646070049000308000c11a030b0f0000d403d40701e1190040d190120b801318050130080b0304100c413803039034070031540f07800b030031003a96580000c1078000400403101c00780070000c0a90041c100301c18001444000c21284290060707050000601550506026440c09454801d21020b200f5148080450b45600203400c841c031690748401d4140703132828403984810891501e5020118480e1003034a2901e0954203180d0203500e40380c0c0000030070840f49038044251180e0380d04241c00300381e031240d0070404185940500d4201380800d178500800c0740e0791103825500425810b480381c0242c4100091910400044450a50030250004c00401020781c2c1a84a0852080720a105044c00108102455107060840b00c3c2d0341c01c1158500000c110242d100c0725040c0700c03000111200340046241100c1c1703400e501420003018000401e0302200300300c00040c2d144108a075542c4280c6107411207039685000310406035510f00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 772440908 1250 772439658 772439677
    0xa0302060d0e0d08010b1b03090405100609061b0f0f051504110303070c1809050a1514010f0e0a0b040c020607110304081c180b0304020a0b18010309032003 68
    0x1610440851850040d904103040b10240b507215802d11400d00740621f80c1e40800d0800ca1640e010400600d03c05541d070307124183c0940c03103ca0b004401a81009005080100150402c038140240141d4499000c001030641060640c0d000340660201d035201d151034800a654080024914091031079060744948500c00c0c083e200341c0c0103801c51450400d10005140d00c034412050041e252110301c407014081800b5400940042032034909000441c0510340e1100382c1404680c410890355590001e01c000d080c51024000e40b401100700e848414529494010112070281e06032040d0001921040d0020f032a00500703600c600c110b5000034006102120b0003442c003e4961408840c0400498200d41c6001c01d000b4000007030b10306641c1200010000b41c0759081e007091a840d4008408820400c0c40304941d400c0901d802c074540014902e5444a80d01c81c24188100600d03c41e05810003170560744140044503000c200d801d002c00e0032040c00c0c28002040102c07410105e804401c01581e03929850034607400010b203500000b008020210 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 772442158 1250 772440908 772440913
    0x1030e1002190e01022d0f0313050405220305040504060905060310020c0703020d0c030f03051819030308130215040501030506060702090106050c0708070e09100603051b0a0302060d0e 80
    0x1402c4072400d40d0000d0ba42c041c16030060b400030849160048202d0f01c0c03815100c0042400000700c06044050900e403405402c2c41681076040840d68001c416035041c0044080d07e4211414401c6e4a005450040c003118811038215000303240990a40505000e08101c4014140251051040c13944070855400507040607a100d03802031040002030544c1030320904c2612402405440904240c44c41c60f000c001941500074400d46042448074000000124111500340709248241c4490342c94118031f080c040d5041d00c54010042c01842c0384c00c0038100c60304004211409072649414011100d403203082d61a00d0342c11900c14000c0d00b111154010185941c442e4024004a4100366001c0c4842e03507a420900c58580a20f8400940100244006108560080c00908000217050b800c840c0700e01d80da1403480e071604505500c100c110306c0200b020b00c00441c02c20b12164480e451510b10038040c40e8516903074680d481c403115480490040c1c13049c04001e05a038841140030011500209000c0e15039140d40840e20003498424500481c51 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 772443408 1250 772442158 772442197
    0x709090515100f05090409030509030d03050702120301030f031121090406120213020a020a05060a200309120a02010e0604120e030a050d0804020402091801050a17100b01030e1002 78
    0x2c6201c1c8200c0f2010100b00d80e1644c0c01c043c0c034981400040c185501044040c03010900c9035035280d4408104a0900a041d91b5001c00d550424001c060f041c01c80810b51503045100030001880030603102042e49100d00d03858502510810030840b04107003044605600c6a010400f910107840d02000b00c00e0240280000c00c890030070800d55120300090744032030f00c0d010007900324200c02c0c0303070700060b001e50303400b401c5000700d00e0041c0d947e822075039913030942841400c03140c0060329941c804039640702510489000340070403c480d80b224554145030900342c0d5501c1c9904d41c0018131600000e6100c2500303200307412000c8080d02500440e0f11074181881d14000c0744081007103200028142c4122401c0300e25002948408460f00403020b4802442d03404002c5841d014001c0c03090b03800c243c00300440841520f0704c1b2a44c40c1258210b00c0340c0306080d410002004010980d0b42e000321113804007032010502802300403480c0d00d044128401c001641d80e030617500690180440b010001d006005402c07003065030000310b400510b401c7d411014480c100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 772444658 1250 772443408 772443439
    0xe0705150940110a0206042d0b1005060d02120708070203090906010509030114160302090a0308180901061706030c0f09040c030b1f06030618090f05061306060e06030a0b0709090515 79
    0x102150307590081e45506851000b0274000454141c10040144503551215291008907096500054071722000d55030014118030502c2007030f02583d0300410075142862040c246800000d5076801585203844c031840600c0f000c44c01c0d0f42e0268085030114a000b03002844182c0c04a110441d8651084034100034120f417003440540303510300c01d1007122401880207007009041c5045407076191082d04001ca44840c14090f104500225030365030740b0b209009050a607112008458000c90590102201400003802a84441c041d200d03941e43c1c0860014400c3c43c04e139010022991a03050420207840d5590025240c001e8410500c01c00c5440744541400a002d004268103071a540da07202201110580d104880b0f0303035000c410510820b81c025820503903d080c0a1082810210210780720a414540d040d43c00c40500d1880017422010850b03a07009542c02000b04816585040c40c0c041c0200341c841301d101400501461148000400307082c0601c09031005044011400c12283c60b0050301001c821860350040da1003590380c110103040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 772445908 1250 772444658 772444703
    0xf020918070c2a090b0324061c0210090e1e0a0c02030910180807150c1b03030203070212010b03070302040e0705150940110a020604 58
    0x2074000d40d55a64002e041501c0d80743e144949031078001d141014003d188200d010301c0c0c214190240c401c05000103000f05000c810103141420030001c2003d084202c01500d20f850303d90018059000320203440c01041111200400642c0180e000720003544440c01c84412420940d1005448080d41c80b50300b2028502c0e12070030405881603051801040b106509480020005039854220684003a8540110ba08003000b03007002074081360b50040c00000185044803121780c3e818002d000040200f600070060880b00f418030150364070404034004880c2c01c0c01401c414a90030400781c41d60080104691581c0d031524141c40f881e00035140da10480c000c0e8814031701058801010340d010722401139002c0d8020020300e9050310719030038440a0184a20390998901901e0800609902c1d0060101003241c4400c064541c0c46044204010004041444544105401600483d2450072080f0380b810514203c464085258000f140f050005d06282c2c14522424900483c00301050360300041c000340241d100b180841c0501b000d850464a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 772447158 1250 772445908 772445911
    0x30605120c10090806150a090209030a170909070210050c0c0d0e01020106150513120c03030e0d02060c0a03030f180b150a030f2901090203070e040f020918 68
    0x14403980040c80400c1e05403400b0349201c40c000c950303810000c0401d0b540b4044213003001001c899800c403420312108426042c0c58031184690160031100302c01c604085025000c680e592250481c000e11201180207a003011158041c00e84003035000040c880c2da020728002c07000079100c40b40703c03040a0405082c1004145c5590520069030f00d0304034100c000701209541d21004a9641009150342410355684104c040341d0400d0441c90f64115202ca0703141c0503503a0404170341118a0150580c010144004104448400698010a0042241e4042c0380143e505004140050ba18120701d01000b54003440025151603540000302c1d0042d2058000d840c20044100580b0983c0c09550402d031500c401100f000084000080c4010400c40d0089500f844c54100488240040703411485640c1007601d2101c0c1045a804c100001c12914440c46106042d005660030161004001501010b024450321950044000307060f00f445119481035240c030082041c4000401c4180c00e0380203500c14100f46010b204203003240b00b046881c00d11841e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 772448408 1250 772447158 772447189
    0x40e0105150702060d1104120201200304050603041e060515103006060e10020309030303010506160f1b0501080f060402220b2106220f0615030605 64
    0x40e0b280c10129400c000700da41c0024961110303c0c2d40c800c42880c5200c401405007003e85800c00403465a040c580c0000340075540002c500c4403a000c4403107003200e41148040280c03000c50700141d69841c0c594a840c43d18103d80e00d100541703952507107840c40124041c4030454001901490307411010700c550408003024020f100842c1000030001c10f00183d040c414400103140110a0044020320301c07001f00e515828a1019500c00744e2020000445500b9400d90b9450111142c80480359103000540c0740941c1c44000c01d84074041440303114400c0c20301140001c50104d91400c880e40c0c1c59404454404034052610b803c0107024030840c00d80700401500074000c11a54000c8050038001e03010703000b5644056039804100400b079400071210100001c64205290422800f0b40074000181c104048043d03200c164802042c1141c150f42089c44a250091381d003402400e8a038507240c928404c41603403607410154440c1c500c2902815409003911030f11850548009404818080c05a62820040ea401c0c0305480d44c4004100140e5844e0500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 772449658 1250 772448408 772448449
    0x3020a090605030c091c02090c070c0303080c0c0312011517040f050a1502070209061c060507110f010b0f0a180c0207030218090d08070f050c030706020f040e0105 71
    0x600555018901a644c0200c40f1440e9904d03122100b00460741c40080e218001d50340c080701e03403c01c40461078003100940d40504c100d41514141422034440d290121064440902400034071743c04200d4140c0c0860840b04d0f09918030084075524561840a004c0707101091060040510258948800c002e100f0140c41c070710080c1480c1c4003442c5032101e80301c2d400300a44028085600d0311900c00c0140c001006040d003008285074640006850f41d900340188500340074000d0045114400010fa001003100210b1104145507070494000142036488020503211040c3d5000003090304d10030000c0c86140d000341508140303c4004180c80b41d441100c22801444000d085902582407a441e0305020358007089980e610100304c032011032045806c0e45507031fa00801d10101d01d1f041c03089039058a4004004550804000550100000e80781855051500d444014018800c41c40c000d000c00100050b00803200398104181c1d100b95410610442d85d82c2c0160700303580344641c40391241001d54403c020000600d850003c03103070811000307150207 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 772450908 1250 772449658 772449677
    0x20706090b22090501061d0d120315091a12060c03060105070609020402030a1d06070509041d0609010917090616080d06170709151e080a0b011503020a 66
    0x2c14400500305424510b0910107002e200140030310075801202c0c0201055241d0603000030440e90036510001088030740b03601490304a07001c0070000743c1041501e100c42a040c0380c00502035008654984450249031b22001c12141458580074901031510340c034410381f074421958072071800c0343d00b01d190b51503007400c580805940005000056095020300002e005543c40303142c0c000361804a0b81d0000b001c0360001da480041a40da2034120382880e4160b12101c0403c030b907034400104a20f240c02d00c0c000b8144e02c91912290301403629402082d07040e182515110b882e000410098030880d140000800c0e00801c4d10b0700040d681318007025401c1403030241d44022900303840c90140c0160720704910070703d0f000300b0602c1c2450219044901000b030f081c0344032458842c0101510000c0d848250160300e07103200500e0009180c0220101520b440c160305510700808100d00d0450740081e281c00792880e868a2041e40d424002e0340407000794000c2d000040d040040c4140318905903941d007c000c01503040442001c500702d00034002e100c00032509004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 772452158 1250 772450908 772450927
    0x201270b06030703060c02280203060402040f090606030501150e0114040515030307030c0507060311030402040c020a080c0309010201060e0915091e010b132906131203020706090b 78
    0x240203980c000c1002e02260300d91036507030b681d03401243c10040364880181c00018002c0c0800c6118590361a0550b400521501081e480341c002a48849015100078030540c0e50b9400e020901e202038000fa00001c0d00305100f0404e41c0d98a003416806003034008040e0f0502044040e020071000d500e8403085040e0761418100d0820301e4052401e000c0241401360900d00341200241c04001540e07020801000b00511035030380c0490b9074480346001d615250701ca4028500f0306080248610a0321000d0064a50081d01210007103403401000200340d06105980001400c1103500203000904200d000000780f400150a9000300034942d03580700c000b1020a0240c64027003180d00000d50440307480d000c0d021001d13080710342d25040e99a801d00d030000e200003100020010900903512015001000c1c0f610440320310706200b10700400d10120b4200351200030143d607079038ad00002030b074a41000c0e005c43d51204010b40341502c894803e0301c4503940d25031020000740d45601c401180103124852022980f00e00c80e100e482d045a203024200d0382001d8800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 772453408 1250 772452158 772452173
    0xb0a11070311011503030c0605010b1c150b03010f0311030105010308180102120c0109060605031b0d050a020d060501080c0d210216030804080d03020708120c09100f020127 75
    0x42c14040c0c06592500c40d41070411034007000c802c0003036101c2c1d100c00d140c480d0340f490641d080e118141c0c480c407801d5800340700180d0044902c40c10481070104010001a01004ca0500181407081c5030700a0700038910040004210710036068003440c00d49020b28110080c40401c10101341c00d03500240401010f144041c022003450070284907428018110500558541540b151504a06a000b0754601b40081c0c0d128a4484240702851080802078a4181c010f050382865400145409607070f02c0f024103000b80c44008400081c0582401400b50480d80100030304019059400c001010740000c0c091005a4018040e100110b031602010070401e03e07a1000580100200e05801c0284c003441014111041d8080c41e410380700e860501d941da4002441c460f010050301c5900b003485407031030300c03114443d0101803600c104096008100b41c0800c0c1c92845400781140b5803207548004c40181d4901403000100d41110780c2d406c00726001c0d80c209800d0007250b14198020440000d02c141c400042c4c0300c005103100700080001080c013002c40d000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 772454658 1250 772453408 772453427
    0x80d140f070818101206090b0f010503100e0403180b09090a0510080111040e06030a051b060417010f20030a3303020a0e041a040203160f030b0a110703 66
    0x1514610fa0101c0c10a000c2503103500f440c2e91030000910041d2090866203828451000600380001c07003040505c1304a0b011902c102d030b44610700c0303041c00400310015164118243c551070140c2030035006103125041070324019008801c0440740d000000f000d181c1c00b14241c0440001ea40b9079020080640c0e4803a19032041c0d210003400040c0036241c125000500214810400b40200029440d20070306d00c0ba940c901c1c00140c1014648054202442500081750000103c2c10005d440c120180310300b0324000000c0150300004600344243d904c840100c46405101c10180d00c011743c403003606882070001c01d200000400380764032080045030050b007521183c24030118403002c065500000500711000ca188644a40c1180b606010111340b050610f00c240b58640140114100a000700d801445c1803105100542003d0355100a10590854010700030106a4001402c2d5a0b0030022040700d83c030a20f2509888945540d030112a0f0302c124001a80c1100000000c241c5095030b07840b03034501040f412404103040c03050035a4100c0d0040074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 772455908 1250 772454658 772454677
    0xb0f0c0a1d03070f080114061e0f120303070306090c0f0810031406070207060314040b1306020f0c1c021c0302040b040f08010509010b0306070f020a0b01080d140f0708 73
    0x405100d0340020340c40400c03e01014104522440b10018503040115003512100c40480c0000d4185c401803100948a0324002084002019514101e0022802c0407400c030030038420300c00340e00010b5003103504410030001c0b0085010f11000d036014041683c41e04940004e0310888406080002c06600180917400d20032031300b80380c001c203030b0b00c804c1d0000590360340751012108846103000c07515410160a000c0826010010980101100d0501b44001c40d44030b081610100ca00600c0548400401c9000070480e0b499042d10f480100d80c447c1c404c6440e43e0b40404000070a4001d800b1401d007034072440001645440480405c1703c411446c80c0e006010740074540200070b98100e84a4480814503400b88800701c1d820796880c0c00380010300034051080d00c1d00d070722302400d007420744001916820003640b401d408031700907850124026600241606100003144088a01286001c0b04094080c00d0400e00701d0010400c041d0118501c006c08066a80b6104140386107910100a03201d802200741603080100b01d00000138401d80c000d00580361 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 772457158 1250 772455908 772455947
    0x503030106030f0b09040c0e07170a0207030507150614180a0e070f091e021603050a05090909070f060203180f010c020402070609150b060403110409170301030b0f0c0a 73
    0xf104c0d000c1401c03210103460460703402c1c1c2a000280000980403d90340da0060640c601141c1d90035030a19188828100030f026414900e8002880900381406401101c200661150b4035030304400110326141700409441c01a030362058156036072402d0f580b5002a07200e5401c1c26065040410b5120f440900d4010507641d400130445000346000080d015031040c460750001c154110002c07605203580c1c0080c400480504507010149807041c400c02c014031840d010200c0c0080e605050607030b0703100c0d0000e400351198015030300b01e254030208800c00c1280004010840c3c01c1141c8a0808512021351107400c02d076140d010b5030652035682115610403040c07501d00118000101c11060401c0c100c007540d903070003007000e03680301c48420b17101303c1e44881c41e43e41040a107003100100788121040820000e01040006400341c4030314071010300682881c0c450029940d465a0001d11256072040b02178000200c130b0411202250400d10003a1030b105518400161999844403000b0700c00c4440d2036085280904a13042680d940d290100144c2080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 772458408 1250 772457158 772457171
    0x9230601090e01080313060c1a04030315090e07060c1e0f061b080108031e09041103010e010315090b01181e02040315020705030702010809010209030303070c021c0503030106030f 78
    0x81d4035900c1d10b103020f481080c014541e200e03068103409032840c80a60000c81040203111206020032410391402140301d20340d1070b050345142c84504085014000d03002502d03000c18401d2034002a00c0d400b940c0903103010003030002540e01c059a6810141d410100009020b070807070b9074a0402010445c5540b46103941d040c483c60150600900b41d4807214201e51800340c104a040e02e8201c0a030039690342129a00b801070032304034011842c00744140c0d90603099203800c0b00070088410011498400b581c0c0c440d04130140142191202e140ca0790ba544544c00e080d4882031005031094410100c541c40303012030303601500340320a0304650740d5003490b440c013100ea550400c4103141402d071050342d5110107480040d80303c0d0500703010101003002503162402c5080c81e0004070205040101428410000c99000070b801106840c501c540908025003113a0711080c030b842c00385c46108003c07036041c0000410010181d40207040110094000c3e505059004512400c010b042c0b0040440949a5401440100030852098115110000c0c0e00000130840c1d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 772459658 1250 772458408 772458419
    0x1050613150804020108060a0303090902090307150221070f0209250f020d09030b060f0604080d3f0b030a05070e041703012304020c100509070923060109 67
    0x60100d0700c4901800141d60718180000e56038048030064104000711041106185540c0d0041c1004000e803203031908035500421090710369681408460010001040c062207c6e40800000039119003d4000c09014404019800000a46580203907003900d54000d00307424060703d56400300403811030700401001c580c0081019070700020102d80c0900503984041e4540903040543c0d00806410902d4413040f800812124260401c041260b541031070703421080c01c4e41c0c0c00a039a030b0b041000c43c459118540000341c00380f0806510746041c950000c001c1600c6c4e00f00201d0501c100c0b10301c01003a4030020040c00758001c05440202408001e0741d942c7d01c0004910002000c44100a02690301c05060019942c002d00d842e14001082005100b400003c10791903101c0b20040c00d10b1503040280d002207802e100ca885000d04901e00d88208141d4640d80d045540610090040300d07125202c110300c40f000b0301012a20001a809004000580b0140600941c600080079030595410040062550607886500620b880c0c1040408840003c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 772460908 1250 772459658 772459679
    0x50c15190e07170c130c0513330518062104060509210c0102280f1d01180f08030a030506010e0a03060e010e07171605010801050613 58
    0x89840a5400b0b00030551900003080c0c8400c51500c918070041d0440800b0001681e5000010308460a41c1030303000803424002501200c190042c0900070009000310030011803968205140d8018000f1503030f01c2c02030460003030414400303550054102c0001240040c0f04961214540d1005021a0440074201c42d060628803a1405490b44040c0480b4070303010100824042402003034041c080d4045400002494000003000c140503050740803c1c0c054410794004500f00d002ca036020340494884080e4888214a00040c8480e060000e0803151080300114415600c0c08942c60301808004804600d41d1440350801c41044005461900b10403100c0e41480703075020004038050700950f046c1781c003800400c001941c03654030041c1c02404039100548211305100060040c404940d580c0c11040040e01d500103c0829082da40404507409051030126440c2c46000d002c10200700200b5840c4080050310b202811228400101840701d11102910301980303001400090060040342000c0d0000e00301c409100d040620038659440a400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 772462158 1250 772460908 772460921
    0x61e0320060d021e0906030c0304050f0703030e09060109060e0f150c0604021311031b070501050103140d08010510110a0602070602071a07020c040f0905030408030d0606050c1519 78
    0xb03190b804070344d15000305041840030211403002c103141480c004c0c0c10b1001a0550000409128500400100090401030184941c07030040e0284d1040702c444549a05e005460743c0700c800c58031409070031104001840d40d03102e6580e0408648a68030342e4a82140e01e10103010407011140700540d0009000c001c901c45516070f101c01050040e450901810207410039104102490000805400e0340c1030134045411013115280044907041181c1c003004001115142c150a204c03801025006040d95280c10000014000183d0028106e51f0800050b224402404542998019028000c4ca5046840c0c5d500d1508880d018039000700c9001c0701c0c1011240f0a41d16a038425050f03030b00c07522081b680c444d00442d5500401a003040001000b5071004401741441c0b40041000750b580d401499010f20403625000102d0121029070700000b20650800c05580d0744a4603801000d6a9a20521070784560a26080f070003e00a03104c0c205a58000ca50b01d00039200a5425140c0320041d0b0030301500e0300b0300c0880005803080c0b46060a104a1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 772463408 1250 772462158 772462177
    0x2010827030405030609070303050d0c09030f030e09090a0512130e070906020c060903060f0613060603020c07050301060b040603110d09120906030b0a0e100e0415061e032006 76
    0x66580d10f080c4024182441401b17030039081658850841840000d80090a45400010748400052030040c02003040300d0160701d5504c098070010300c0828035400c0c036501500e06a030700c841c240c0b9a0406ca846401a056807045a40340141907904120f81c140c8e599904440185403a1941b0131003800d444d501c0c0c06d0101040c03082554001c02203009004c040001c180c0600c0280d4040400712a480c1c240080180840e8031921b004000050039030035500001e400d41e13503041d40300c03050100c681010010740c2c3d110700010b4020b42c8141c0c3e1040d2248200100012107140500030001aa40000f8403070f8145454000d00f5000f82c41008540d02c6071103010b00098011000a100d80148a401100c0307049211400e00307005407902100c0d0b04504100350815900c209140c0b5240070365170840b030550080c4069580c461043c11000900340e0081c01401c0720110a0100384500e07204901405c4d500f084007005515940c807900c115205045007070762a42032001108001003443c0c1c681c0015000900c0c05004112403100c80080c0240e840090701 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 772464658 1250 772463408 772463413
    0x1030b032803170f01060e030f030307030902090606040b04032d1101030e01111b0718050f130f031d030703080c070905010f050d15020d020a031a010c02010827 70
    0x42032592100100c0004a5050f071484040d01386000e046420f19014003a102c1880752102c96100240c07020095082c0f18030103070302034a4507410300d070b1002000340040110591243c1d4822012610b145404400c590803101c078942694600303440d60341c550f80c600d003903965102d039110b243d40d13940076117420a1035036a030300a0b104400043c50000e00e20009011030b0794000440406030714008010b0030304448281120f80718652420104605a0601d540b48d00e0507901c1c0c1c00006c210a03444022103a141c0c580d40141e030149078814142784003542c032083c6880c00c1210010026003030445004204c0e02080c00781e00f2440c0700507414a42c001000030321501007880d2202940c030072588002e00003811075210b42c0c00d10000380904000b000078409545400750301c0e001c01c209030041034424150100010304101c40310fa40b081c407e0b04032041c19501e88055800380002504401901800b0a0820701101010415290110500f400503122903454061680045800060007407903030250308104e815800c11103903601003600140c140c4500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 772465908 1250 772464658 772464733
    0x4b033a02031b160305130b04080c101e120b040203040311011505010c020907050c0d0e150901200c031905013c230f071d01030b03 57
    0x450300d49180b6064040018020302000b01d022401c14034a0078619010700d031054940c40012402c1c4400f1a0b603074810500001d000900065014010800414030a000c8404039514404000180e07008102d03054407040b00510f4a802112040c080c0e1405111120655400101c50700c071003010030300700d0740181d800b9000f00d014030f074032640f00f20000d006003000c00782c94000b080c030850300c3e10300043d040360703803c210091207240aa4000f5034440e2041040c0c540e49103000080350b00034540e801014000c203000d841d910340070709000e0510781c1840203280200c880c10340c0c06035184000707960242d00003c000300c2d08090124a82c00b5540d910310041e98104034000b1400b2a400d03004000034079610b48142102d0503100200040c00300d1403510300c0340010000142c140c409007441413031040540c855a580c001c081c8101088141c20746a007034074814000c0c0c400f00318422005407903040390310b0700d80311f1040e110700c81d80d20705140120410a0787c494075035210f908500d540c11070140407900070302c0d401e82c4656600480b080ca0070005508100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 772467158 1250 772465908 772465921
    0x8160303051b04180209060c010915051f03060903021606030e0c0306070827070605040303200c040207080405150a081503030a0e034b033a0203 63
    0x200c250464003002d00003207291901d0090b8807002071000002003154103030301298810968580f201115200d40d050802000b103503003246400040000c52203881603000c0c0c40c250000b03009500b07600c0c0320300c1c075445c04200094009240d07664005c0580440c140850071030040d075030703819100c0b5655a10b07032010b00341c1c58401150b0000c503010301a20381800d10810324030940c0401c0600442c1fa8000c096903400c0030f0082d60301074201d01e03e080c24014468047d6a481e40910864a001075600d91003406082502d1081d078880c48110f25000866103001c1d8440612111070300610004000c0707141542c0280700c4988918003840c01c250351040051901c08011110781001351000508440c2e08d9403111015074800c42401d44620304e9404040404c1e500d01903007596030b040c00317150320585049075410004401460860034048440c0c103100030303c41e0941c1386800800e5144482440700703001201c0d441c00d00c0d4090003010303400950a00e0b03114503001c0d10001c1201c0c01c001c01d61101298164001d100f00501c24161400a9005640c0b802d102 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 772468408 1250 772467158 772467181
    0x306032505040f020708040303110703080c06070e010e130c0905030a051c17130c0305100b03071502120306041b02061b0304150519021b060c04031e0816030305 70
    0x182c010843e143c0c0304024050018000f403041d03034280e079090701d499400440c403140181c0c9407401a4201902012000c1507400200a0004601340704a00903a2004054441c00006486005906a01580c001c01c42d03088003682d00c0c1182d2100304516094507001c2c90030b03a624800b0038101056080d00b5200d54010300369604d40d8040c201304c001010308107441c068403440442c28003041405c9000d4502105101003141250074040c81c460840091a0484c0a0b100034204060340c9000520001042c28002d02489400040a00100e440048425050f80203031480202c0088444c001d940020300c40c130b501c103a50707107130707030311603540c9513001102902029002441c0a00b030186401030b403900030b00f01c1a004040d0030020000050498400c0d8421800241004916501c0e50000f92190030310071150040c0a61010a200c80903903070103d211824032903450150341050702d030b8800d03900d0f003449a0701000d8841034200c19031551500030b8182e94940c8500904016050400d106803855502e40b8040e02130b400240c030b841c14000340e525807 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 772469658 1250 772468408 772468421
    0x9031905041e060807140f03010b0721050904050405011805150109020403021503072327030703170409050106050c0d0e010806061c2a0305011406030603250504 70
    0x100b0404150051501d100103014013001043d18040104400034015400141b106450f021041c1c0c03151940c40c1c2d078552981401d90f8001090585005925000c00207480501140c4501b241c42140e032000e1514840800380005441c002d0400c90b800e640c0d0343d824202d52038034409a66200362240c0d002d400a1011800b2080341e405060b0000300a542c4100800c00050b03444005140031004180c40c00c030b032643d41d100c5d400c4d112802919680d01c09060307511501170741016840b000305180d00110384034000380201101c1c1042805450030702190542d015400500c04980310b41f0fa840c0400f8480d4800070300d010f8481060b001074610aa10080116902281c1c0b50100c007030600032141c00b2425450800408800e140000701002e4000d020343e80180c0001031003449000070700c4108554410180018060388180e03220f041c20001d82001644c958156000d00d4201d840d1081c007600e41220340c44488145450800020012190700c0030300515810b100303201a80d4480d11002e042201151070f00f020800081303141000303000a4805 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 772470908 1250 772469658 772469699
    0x20102060702010c09150e0a030c06020f03040e0402040e0f0307062003040f11040f1107020102150411040b0d0605130209070f02060a0e011401030b04060f02160b0903190504 76
    0x103004c503490300594441c19200441e07030401e903000303010304800a050718100a02d4100c580c00c0140900702006008006111004450a0f43d08079413040810301c001503180d008a004140c1d000004102040152410345c02c5200b5010b415000c0c0c03589007940b4941680b455120303500440b065174071042e0901c140101d00554100a00f180e44400b071840c40c0079510f241c454a41c4c414002c1040c0340e190b1070301003d51210350040310428102e00013004029410264600b0315000303047c080b801440703400074040c0740640c03405100f40943d920a4040c552080ca5130308010240c181c0540f504d4019864952403000309504d8041d0a01070310759082040007000e1035006101030b5501c010705180c103100d1100303503401c00300ea03000a00e141e1012492000250300c100392039019016003040355680000c82c071a00004418040c0e142c4070305000c0c0d480381c9000c004184855140c801030340548002d031103007003070800340c0380c070110700801c08403035005012009581c9802c16400b0b02e0900c51004203050340001e01c01080500c03012042c0700350201001e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 772472158 1250 772470908 772470911
    0x120b010c02060a030e12131403030403120e0f280b030709051c0609050304080606041404020405100306020307090302090f060306130623160f020d110a080a0c02010206070201 76
    0x1031640c0206145204544400080541e01d10360301307114550074000301d402400c40c203a5141e505d54901311444c07030031000d42c0155401c0c814840f4011084d440c0000c00c807400c484c2d01007003c020041c17040304255090318080b2051508601d1400782a6103d075254881e08101466140c074601c0a22441340b140e0510411f0303038000b030a02075400c0042c0841c49412604c40000c460b0201d5119a1800d18002c10415052000070014020f9003018685030800101001a1050b101510110b50f9240e80e00c40800042c3c42c51041c0c4855100c0550002c2005400c1640299900002c04003251401c10741d2a61108103da03c2119031030005409450144214540030004540040c90081001e00c0b90a00c0c1000944664015100444c102c90741c1d200141084882d80140d50761550410040208a0155446111960040f6030801400b86805000f407085405161010149803d0741d008000c24504808191440300b07070104080c840b4405c040606001801717400c020203003d4050751303680f1f1091280c1d02c006480c0c080d01814900559 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 772473408 1250 772472158 772472177
    0x160609060e0a0b01050f01110604030507030f14030c0d0b0a0e060f0402040f150c080301140108180d110c090a1406030a03051c27120201020406231207120b01 69
    0x10441850f82d0f055036011100340200ca9401e400688078000c6102600c01540500000c000c00d00d60054042e2030068080d440d5007010078900342084506042e0000140759130207082c0080f45000001c14043e005002c1401e400080d86880880058180c00082e4003000200d4a550108811810300c0d00001688540a0f00d00b0340c10141041300307032080035103140210b52031070101d40c03500c2c6690707403003002e6160b00b04e5001180c090742c03541c4860a610b40d100c01d420080d40403034500004603a0b0844c2144050510b0110798018100142c0c02d501c00b1100c000d0301e102d58109a03c900f1400a02994174451003a0261907440c80c00a090340011404003824880101080d100e508503850103408250080c080341c00c1c1c003070410112100e4481449194008000d000741030f09200b8040a0301d20340c4a0348840020540e6030050090b4880d001100304200d0907032140d0301564001500703000401801141d000e455134090071010b0042400c0c8060151361405c803050442d000b03000030700580710100e000203051040c00e40e41c44c2c00b0318185922 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 772474658 1250 772473408 772473413
    0x1b17070306110c1908041206050702060106050703050a1805060c010204051219031202120103060906050a0b0a05090a06080f0a060b030a11010507020f03011b0e1e15160609060e0a 78
    0x1300d2182403582d02d0003e00d29482d2100b003140540464000d09802c5103e0441030100381080001441c080355060058070402d400400d66501410076124410750540d03c40b4070344410b03c80120b400c03d5500c0305a4180d1840b0020205899503190080e103400e00000c070005840d64540742c2086210741c44000f80d030351150440c0c8400164034076101c151030b501c0ca815042482c0060107103503401001740301c0c516036502c401050000200c2040b009402c1014a540103600510080d240c0f260341004440d50314440303940c0b200303500c20204203605041142a6210402c80310000d90a59188162420000004144141ca81201c1c2100b070400c54240719003010484250014004949030b55910440c89500a001c54148070001c10750a045507250416101070710030190082c00420a070342e00c0300400d110700c50300c4500410341008102825090281e100c2d070103074910107043c00340e501c0400c0034412014402d0714035210401c4c04000350b400020804d07030b4003541c8a1140d0400902ea10103804c080d81100c440011011b80c0b5088400304501 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 772475908 1250 772474658 772474663
    0x60f030302061602030c0102040609150306080d0f02010e0f07060f03060f090209030a050d0f090902070203060f071b0b100815010b0a0c020301060906080c01090803071b17070306110c 80
    0x41c031414250003a08843e00752041a85180121500700440b503000040c0407449236840755201c8121064040c0004241840c58001e03070030303030f0100d000e01d2403540d100b206c9824406101c0e60718007500380d5040c000000c00c000329190681c00c00024041c1c00b515984140b0040241c6940518108040c05051404001d1a07082910f4a108442c6900c40d8600164011562800956050180710819030b032010440382204000e00340030388400035201221000c100383c2c0c6000198034a00d8000c452066500070b02602541d90b598481c40320281c0702902c10001c011250601d81c9640700000e08802d400c07406103074403a050780340803002c5405035100c640001c050341c5c118646003102c60308201001819070b51141103440d1115600c24049800e000045406581036090080015025426500030400c0c2c03034500b015144181e42c403c0040d52600c42c0792103000b02c40d500802070310300410160001c00308085144550501d2044c0d56280d00d03020028408140c54042e000a0005c104000c42482850305da86104006c031801e12083c00750464 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 772477158 1250 772475908 772475911
    0x301031101110c0d08041d09071a0403080a0c0c0e0405101407360f0e0f01030b0405030706110c010e011503141204061101050601090302060d0911030d12060f03030206 73
    0x107005108290b4840100016501601d000e01104400c00d087e1442d00940030f8801c12090b501130aa6014101002c12101348041c4800f21400d0900b00c1249020300d90b503202229584400105401c015840f0240000148c401c0e42d003200502c4050741040707490070241006420414042c401c071140c14a059403506140040c20390311a403004481c2824500351442040c804c0342040c60755445c56400ea41c45154400c880000c28202040e152640c594809881c4c6a04041d20460b000740c62104010081c0801000004e050b00b4140d5409481807041d2820042a0755070041940c030512821b40760640080b0310501c54441c04d2003025203421040009014161b60380860401c100400d00002d01040e8030b6403410030010070100152020041a12140c81e9070b6603584600030250800090022059401c00b400306100390710070800b0340f0a4075001001d013840c00c490880450020a8540c00844180200c885d4001c41c99805110310403007801d040c0c4600040d518003442000071120b558020118401c12134070140f003c690300240ca507 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 772478408 1250 772477158 772477183
    0x7030e041e090611190221220902030a0207110409020f100302040f031b0f05010806060c0a1703180a0b04081b030a0306060e220b0112050903030103110111 68
    0x14040b4058184600a0503800144180e803000002e5252a4680007983e03404101c4020784c02d9400003011402ca592540d03801000404070104240065038080400701003510f00c801e103d03283e4011481da00c84550007079803c22075444103c9580498400140048143e5003443e112007204c04105500c41580012000c0e1144410a030048139003806002000e40698111406840b004508211066807440d007481103206801000d0103440d0740003400035052540410710015144143c48226080d6200c600703118807a04807040046c0b01d8490031301c0e03040100d61007481c0244070a41e256604c035a689441b05c5404202c0d443c00404d852298811000c0c5804603c80340241d41d045a40320003c16075030800c8080e01180002c3d6110050030358000003411192058041e403004c000c5031041d4a1707508080794514104040b1180004842c0300848451108a0010520768030504880c081410507000740c80b40d42c2c0d1903400301c600443d200d0a03158000001402031211010801c12104000d10b80914615410822542c5030a10800c0d0b1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 772479658 1250 772478408 772478411
    0x60c070902181509030c09010602190309170a0c0609060e04050c091201020d0510051c05120409020d0b04090812060d080304050102070201110c0307230604060507030e041e 75
    0xb1189801c0049000034101500a0480c96a00d200c801d500e4400d900c0040325510900c21042c3e201d100303040c0744110904a440076009081e1301141c0704146000412082c40480400607c0310300451a401842c0300c500c01500c110006012203000351603c01d044103005d40001d02440f220203001c00c051a40101d0b40c004190090303e0205036a2a0344010300490701405031110b0784110340303e501c000721000540c003901900c61106414005c0e0307259a28807090310b4010303001e2183c008240c4132030425004807860958084a100e14211011130821005102c4160865044508000d80009640c0e00c2d10043c1c6c05400c0d400d0b03d04950400003d0b08554031480248a02c000b007440d6200b400b030001d0403035a10722044980c415000f1201e107036249890700d0254001e500070322040303020450400303500100300000541c8400f40071001e4002c0c080c80b8280b42c4000b89080304025265128001110b07281096211040030700024400b40d214075440c1e165624002e4a070002d84948a40214580350860150700300e6080c4040e80c10000440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 772480908 1250 772479658 772479667
    0x40b1b0309031203151005071103070e01140103291201060e070c0b090a15150803070c030b07050a021506040f0e100e03070b060907020a1a060f060c070902 68
    0x44060640c0510341c0c0c0164035026801d104010580f2900095120320184907160b4041c1e26200100404404a90199400904140810300000b00e0f60740300001074040081c1220b0904d6514100d1544488090f0084e00303820b440007944200d29600f60281c0940c42072256200c0341407034102072915958140b26014240b0841d440000451503480a500076801b03054504500c103040e241444010b8904031513250200d808828400c00100e1070312000c10181c0c9003aa01000704d84d040c10700d04902e14003900c0da2020841003401d644800051030360b000c0000300f02442c400c01700780110600d18203101c0c8003020700030145000c1c030408211041c041540410036040c507213071703100c043c5e59240c440e40c011400a00128408660082c40d1008034040100f0002d170038401525410024040284841c04841d180d0180400041030940c035680841c1c614a02000b12580c000ea00d44100c07044485203845001410f8007806140111450120074440103062040c6400e034540d10640c0c00318075003d518180d00b80c1e00c500a104418040382d000c40c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 772482014 1106 772480908 772480957
    0x90c0102010c410310170d351e1f0348080304050f04050421180501090602060a050a0b0310050604200d1a0a06020f0601050402040b 58
    0xe4070745805014114069000307000d284103155980702c1045200c601c48400101861144070844407419040750a24013000c422724001d810405860241102080308601c0c4109600441e17038806045100c940101c9403081d20105900701c43c42d08040b800020300d014007034520400700c0941d907502082514940d6031030065928811485083c0e0045401d82e000c24582c40d090b0700103503000780a109051500c442c8030110005003555100c0300c00c0400c0d0521005c503081c1078003000701400b500b82800c09582c2c85007031000203950382400501007000d25880c0d00c00103107114010707001210f800802908a640c5050360307100355805002c1c1190141e000700d103046901c20440d905003460401c101c11710240580740010f204840409080e4420981041025000c4001ea06880b803140348802810703594080d02c52400416481400c0140680c41140f1880c014001400201c040504991505020146d195214200032 = true := by decide +kernel

theorem cover : BRFrame.Cov 772302158 772482014 := by
  have h0 := BRFrame.cov_init 772302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 772302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 772302158 ≤ n) (h2 : n < 772482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
