-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1051
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:01:01.765519+00:00
-- url     : https://prove2.me/submissions/8acab61b-2996-4ba4-8837-2bd4d1b77ecf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 188848920 ≤ n < 189028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 188850170 1250 188848920 188848927
    0x130809030f0d12110322020301090804090e100b0d0803100b031611010b0603180a0510051902180d0809040507030c203406050703170402010c0206 64
    0x116102403045100030001078003190000701c00c00d040245030700c0301440121105072a102c00441a441135500712401142c1c049001907010760007140b0300000f009012005c0f41d0540d40d5503200d0700040d614901420040c0500c40000404a00c2000a01e040488000300c1c03e8040f441c0103481c0c951036551112a5903481d1f00500410307141d503103003100500401a16007010703461550100070484000441103401803181c15517650304140040905000c0c0c20381c0ca00300c540c00e40c070510520000701d82400350345001090650000844003038a43e161039181c24404072240700051581c4a0341000000c42081c040e00351081049241185021426aaa50255610144003511810003110a0b00034032050009840154600800c1040542400c180c0900101212060040031861041c1c1038140d80302ca01369484000c1c505017000d031141b81d040000c480d03a4901c240d2040c200160040031154040380b05c01b05a00b0161405403120742d520701950602030403141d044207920541c0000e140030440140d0303010400c1030304194140d8a5a84 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 188851420 1250 188850170 188850187
    0xa080c030f0403110a050402033102060d090215030709150908030d140c090f0d05030c06070305010e060915010f02030f12010302041a010c11030a060905160b031308 72
    0x540c81840c4094004007000704000c01031028914000118000484d00003c5940e9202c0c20b01050340000c03140243d61406651002d4501d420f4540240b5070a0703800c5030b10745200d0005a0010328076401003243c8030161075880c0950011414915942c9a201c8036031090a400c6142156000701002075501a0b0340c0c4000c0e410900c030441c0f501840105000c1c25031401501d03228000c0f484400c000380b200b80138004040c1039010201d034200c0054030417511a00d401034540e46280031a001030144011390360034100d680d44420040e41c40b05003024040d1a0117070b840d59801040c00c0d40b4000c00300580c104058a040d2088401b9001d0064070075040060644045080c01c0001c00c0341302d0594242d065003d90072040711055030004400381450524208103050761b20840703080120101d409001c100d00c5120180c3d1601094103032800c1c401045101010032814080282203818584090b542d0704c00b61a000c5508880d10781c46107410070380321442c1d200908054000d07501e200d41545880d0000243d14038003400c01170051100010b5401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 188852670 1250 188851420 188851423
    0xc010c030621061404080a02010609020a1704020604170f12180405100302040501080d080903040e1b0c01022b0b030616050c030f03010312020604240902040c020f0c030f0a080c 77
    0x481458901490162071409041081c1240d2010070700c21f006500e40303080410304246901c00e5a501d0360440c1d64006605240301010a07045c90007501c26a40300d0024840050120342c0800141000c10454020705160004604610715004000b40e41420a503c288070070014500c403006840188a41140e01240c6a01c8102c2408000d40254201071f40050a00d0000b1410303000014006920f0031316965134800c03a5440d0180c0d19101c0c0518011003416010034004503124490038003001c0d2114030301c00645881e107039066450707a0883c0e004080e81e10341c45581602e10103100030114a02419028055010310825038850002a2201c80c010443d02d00855500d0087d503140c2e220b407050b14201651070341240d64840d03401c00c071410260002d01c021140d601d04256458001403020600c0ba00683e40041e002040080d408007260130b40b035968410f010010794481005016030760f103000d0010b54401c59006403410030318120f0b00505042100c1c1d4201c8c0654000000c070b1904a1000070022203660300300301025114004106400d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 188853920 1250 188852670 188852681
    0x507051c02040f060809071e08070303030f0b010302091021140907080708030316031e062102031507090509010f080601090c1b260c010c03062106 64
    0x359889a100c110510128490740104255000d081882460701d640701e50403111301700210760000302030704594030400179a5078000c0026040c86003d4205580c5a8640025925104003036006800080d21a03107502c0c00c0c401d0038452111691002c2c6415071600410001007071800c640000c41d1020026011b0028a10003041d92881c0510700920384c0c10b0205100c0001814461502911314845500503030000040380d610024035007046803007c10180d400e41e51914070f0000c201008210000605444054000c1403090181410034405100c400001c0c070b4070300345100c50015413400b000d42208002c0350301c2060b003d40c1d00012030164100c9000030242032659000000c945010180d449260402841e000218003054045041c20030f55000360112900d80c1e07031740c8401ea4207070356030b060030b190100c2c034010034882c110381000c000962124060a1118200904090013000c1c4180c080e43c290300000c00402c01d07403092282030150041c60354030707458244181c500f4011904110401501d8041c842e10b10100c00074104074894016 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 188855170 1250 188853920 188853937
    0x302070519022d0a0504360606080d020d05040b070803100b0412060e03090907080615031008011a0616060609050c0307020118050d03111905040501020610030201050706050705 77
    0x4024105400000b810f04901c403c08800c0c818502443c01280c1d0b410300d407142858078903000302515401103141c5a906407100c010b410050f5803c603100000400714032607004003801031180d24000c0a138840e40f940002e080c0381d458144007040280400080001410308402d440300c45411114081e52902d0b41d1212041400300c55102c3c081d4041d01280009a007403484407500f0b02107018180c18488c401c03541c40c441c0d0b168803036403a1450303111071548040707a240e62050700400d501001c0a400c1d00210f2542c500700c0f50013600308035070b0840c000c01058014001b0007800e00481201e02d040c079503204d00e51603103600040c6d9a409840040b46d10f18010821711000d00c0110f40100700100050301c4208243d044c0102071031250f91007147c00c0000740d800c00d000d60482c0314640006810b1103400c030016040142c90345104a0107401103044141444005116240003e0311024601d6005502d503203078965200d00c1d01c00007900700314000b8034029904841c0c41c810400750760410102e40542c0d51060300083c0303603a600302054603280102c244 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 188856420 1250 188855170 188855209
    0x150906030602040e010902090307060c1a15010f020a211e02030d0b030604030e01050a0201020408070b0a11300c150a20090d050a0b0a02070b010501030207051902 71
    0x10a01c8860b0340180161039241002400d10f07130301c034104d02d0240e104e10211503800d54420381d82082614426156405854427440c0c1161560782c0540c3c9948e4008026540b9000e03001c02c0d00e030885200d41e0031014440c441c1c0c1c1d03c0d0010b03114603d46921a4540500c10340152407900b011103805002041c03180d0020340d01c4158507a03008061940b680d000941ea50002c484038078949140250300300d03403850000b8110b0301c40c95042c0d0700d60901c6c03001c00300110b805400104440c0709664013880301041c3d010b401c0c0603560103800314203001c075195000904020710954007001c48c0c4209030421030108070700100c074804154810b1215802c40900403241c000180140c46460700103405401601c00e861000441d00300c009005600406007481842100c0b400f102810070008058a500030040200e907020f42001140381c40700d10b0142c0190b818110b9184c0310484620022aa011601a40050724004129001001318090202881c0440c203284007a034441e5913a000d8440c0b000b0a40d50204002011981e07030a100351600285402d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 188857670 1250 188856420 188856431
    0x210509030c030307030e060a06150f0e06040e0912031017150108010903030c1103071704050406170f0a02090a0203190608070302130b0603060603040f0501050c030603060f01030b0a1509 81
    0x100101050a9100c15134000c7c1c20119182c40401d0207800f040d94414801104107015800090302d40a6680412105220302691141141c0c3d86400240c00200742d503075440d107114982554998200302414450b02481c0d401030003030002e0300c59003508040c00c1d28005c585d06110507800100c1c1ea80b801040000c02c0c14000810310010607800c4c019001020000d109032014402d550807500181d400700308864a071800ca520a100c1000400e100f2600844841380c0480020301c0c0030703110800709007074610301c2c0c108520000109a00d0176403803008100c048084038023003025017035010715076000960000700a460b0030341d000d401001080b41c051841d0864a07601041c46002c202c8140c0e55200c0c0b0392202c00620083c0e104040300ca0711100040980d004444048c40010042d510356541d4a040081c1a000680250341410008140b0000180c0074480c42d801112860750310340e140d00d0823104151600d4070051540d89021204401080003510402c5c1e00b5422002081740031855000c2121200036140c816030041c0390742c2d41000d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 188858920 1250 188857670 188857681
    0x70606090e1c050a1b020d080a081302060301090905010e06091e01060e01030326040605040b1305060c032a030a05060306010803070602070305040506070b0a060501210509030c0303 79
    0xd6000040040d104020b0351940884901c0d500c0301c07800207468a1001c501c04100e460718403841390ba0317410545a99180007100010440c0c011407940c850340402101c18000000c0d16041154028a1086d40a0200030340c403070141201d540418000c0c00188078800d483d94645260204001080d0000c28600d000d050403100c5170714022280a41e50303085e10b99105003040d05089031065040040c00750300700360740902c0c0b1044400e918580c1d08894000c1001e946600518401715078026599655090901440c0204001314140c1468204950500d101030803540c412400039a611000420100e40168002e40c0c03684070944a55500c02ea910401c036a05e0501e0103070095030000c0c4400f18610f80d01440c010303400d04004101a075505400c0c141d94070028001c01e48658001d000030000204107130002c06080b071191030160709040d071b07640200e101500829401c40d0740d168000c1c100310f43d000c07007803040c0001880d09203094461110003909000c0c3c2d00c02e4480550040e1501d400026a0320039042044901000e0148101c0b5178a1628 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 188860170 1250 188858920 188858939
    0x21519020a11010f080417070803010806160302070b0609090708070306020705010b010207030c0b030c0f0c010209010f02060601140c0106050d050615090c0315040617070504050c161205070606 84
    0x107a8100c2c2e48881c001004445035114140301c0720f814441d034440c0200c5496a80324580d10a200246010558000b0080d07440000c2251002c0c0d8000d1520500810700750030100311154804440c25581c0f02010310520104010401b40f90b845074100c907041c0d0300b28040782c9030860707103c1c240750b015000300f542071051500000410500c0c0d401000c003079010300002c0080b07420340d1004a840301171a00c406801480300352801c1c001d5508081c0250740003403032860307030620749640c1962507082c640141040789840d940c00b0545c50010b50300800032090140052014003441d181040010b01070030a08480070011540125a40d81c04800c00d41c881000b0b44001401204040c1803845c3c41e036555101110041e8901008070090203060400d941018000c5913000c21085c2980d40ba240392107c00c2081e070002c00e0348640c0f01c07040000e07806010f0460072036283c55840074020141c01c04007440150b80d405040342010480412500c1944240c43c10503188568cc0f0a48619500500c2c00381200c1c2402200e1014002c140b6225002588a00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 188861420 1250 188860170 188860183
    0x15080d02100b0603060306072001060b030a0e01050f1f21020a060302041409061c0804170f1b03030d050903030402090601030b01080402010e12010501080304060206011208040302151902 81
    0x1039408103001d0303a0340b14000c0c00b10500083d1a21a010b074050300100300c4050040c03800f00c3c084426a0002183d04014031400d40c255080c0f90311040c03207114004103012080089008100412561000074052410803202c480482340d0000d1004040c481e2032603081c5200c210b8040a03800516a43e00395820381c11041c1903d802c0240a43c1c4220f00c0381901140000da014007078001d03030f000c96100740c0100d10388401d12402d00520b030344002e003a2523100180c08a52505010319401c003400b0744c0c0c041c03494592158100502c1c40e00002c150804842d0f2075100c0f1190a1006100103035810a2400e0007030004078039000350700030a10354021000d45841240c02c00c41000b071060070000203103128074000c40f0034440c076403512070040d8201c8a0390407a00d80003400b503200180c0594003c0c00030440b101e41c003801001e0240174000aa03801c4a40030f80004200c4c0d0030004041006540c1044083d02420782510a131404007540c0d5182d01151040b40300090091a001080505c524280e0007a21046450130824420000d02c81c00700a46580307 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 188862670 1250 188861420 188861443
    0x1c05031c0c02060708130f0b241801050d0c080a030c0302010c0c0807140f0d1206060801052119121713020111010902031c0207062115080d02 62
    0x14a007084902441d84009a000d004910507140c5070b0098403805c403c1d690324000c2e042c05171780d0a4401d645413000103065603450b9204101860080d0b590142d807090303051403055002e000c14480c058144035080101d030080c054a044840403a0003241510503840d20a130304a50a81c0042154042c0702c60400505410955002a03075100341c0c004c00030700b80118410b481008144001415850083c4054000500740076110001020b55100f20b640b80e5040d4401c0c40c1c039007410981040000b40a2464040550f802801030324041c00003400c2017021513041401080c054000c2c034408444119201219501c005c200344030408010280a0f1600036400007803c2c1200e04c625040d42080001e200024880300a40c248400d00d4082d4100007421644000590011100070140400c451025588c540b8504016a82003080705407208400070300c007048502e10b2034040d03f0300c44140d104d032041c410410324000c007002500c8948401100070807000116404441031322403005856400c460314900c22900742d0100e09030001211b040743c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 188863920 1250 188862670 188862727
    0x260708010303090e0c0307030207170318010f0509030702060711090a06060f080402061605070914090607020f0601150e030d03050a1a03123f06030303090a021c0503 72
    0x4e983d22202c082c800012142e04028100500100b49582e2103900208201130144060313450108054040040c03590050f6803450100c0b203800d0304802410000c0c0118038030b048144400700040e14107203100e981c9910034044000d11070f0600145500802602d4060615418001380c5903840500e40000960300903ca94029400419100e404448080d407113200c4403833180c0d50291001c0e0a00300e402c1480c40541c00bc0e188226814040c4aa01081e005071302d00c5080c085414000e0303210010b040541000d420b040c005012501117420950710320781401d00001d80d29044400c440c07950307050100350050480c1d214880302010740e403600400c0c2c4008523040e803582100e0b015036941141046810300508541c0f0088103c942d405806401050b20b211416040c2c901402000f230131500c4400e202c10040c0b400174960500140030200210a1002130622049100111075204409800a41c50f45c00c045800c3e030350758060494003d11440d07064095002070a110b00740340014951000c116510781a5107540c151201072141841c000c1c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 188865170 1250 188863920 188863937
    0x50709060b07020a0e0702070513020c12130602071a16020303031003030e0f0117070e0d1203050f130b06060d06030609110306040804060509040b1201020901080a020406020d260708010303 82
    0x401982d0580c5c0c4c00703000c054004003101c070300d4502402032140402042d2051030b5800d00010301e0b041c0741440000c8542005842c019903691160102480740465031b0031400465106034820f10400034a52500400700102e804403907150701d03401e251411a615036060082d00343c00080b09101a99800c402034a055034072036103c0308102c08030402070040303104000c41141c0c001402c1803074850181202c00d00707454001c2014500303507000f600076002107112074105a8044a00405000000c0c00f0a5414807802c1d4012402d00850040b2b400c01c410080d41480301890060411070a68000c1021035503100116100c02900135401c0c000182c0e40c1c240a0010801c585042d11a4085456030010300d14022a40c240310b10f40c401c98450515050400484050700300d20200c41e0010781d00c0d40400810380d12a04903e07081100340b0009030751418190001400d500002e064a00c2c0940144420704c80c003600803403240b4204440386050300c1600f00c0b0007404014503a0681851800101c864180035900303520100741c80c107a070f0103510351804 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 188866420 1250 188865170 188865179
    0x15081501080903090409050109170304030f0306140f041d030c011103040203060f07090803072003011a0616120c02120c0a030b130507080705041109060f07050709060b07020a 76
    0x80464084801d03030240d4004126684c1d1600c2d09070312685903140140000100d50003280c0c1c94a00740c88215a1040040001000f04400c050340602c66841a4a00345000d0000300c0c0391201804401030600c030312511500c0c0b000c0040015440325804002500101c21480800510008405450303a1110761202c01550810041c84445a1501c04483c06150701034010007496441031a40010300c0400742c00a0f040041039070002851402c10405801010700a4404800340c10650303c494011903012105140244d041a42c90084140c140c9000019030030180c414a50307403140c6150f2250584002c03140200f01c0c50a0484250103903601400c9484c03103d100717840402060800c5404c15a441c0501c0f031110307070710580c402010f1002a124804d1690000c1c0c945c4511420400c4503aa8941440499088030b0415031003410200700781e1a00340210b4030700960f154006807500c105500823955911904a40000c06100011480e0420038200321550080c01d440000300903086e2965052102680004001e07445000b1014001c00e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 188867670 1250 188866420 188866427
    0x5031e1c0b13021b030c1507020a120315030206040b07020907050313030e0d0204090b060a0b0426070506160b0c0306010e10031803080103060c050a12021315081501 72
    0x8000c075004001c400c0080c040440394019602070040645003a200c607001a40301c410402c0030b08000802d0340d0181101e6058107030f014214140090038602103601c04240f18012400c0485001e201ca1382c14603001c211040a030200b01d41e0001da503800290403420028001070100f03505809000501c0c4202c42040c42034982c0c007012102400305886021254119100ca000000e004240b811580b29014040d07000c0c0c0b0003a60002804c44495100a5500c408044104030091a150903450301911440941c0d6003003509004007040b810012280c8400705244030300c1401c0c4284001c0280e8801440c000f0300d1155505d000c4178010564501440d800c03241c2d0320828010807402c10484041c0ea10862040c0d41e03205100c80384004100c07201c2065140308040c560350b84200d40c030310100c0d60585403403180207440ba84100e502d9407411004484604614404100e02402400d1192f544141c5504031000c6c54000943c80e5100d0307051034041000d040c3c1c0101c900030501800034004640003010349200710601865001411603220055 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 188868920 1250 188867670 188867681
    0xb1002070e1f060302181302030901050711100b03330c0a0f0c1505090a031206031106030a020f04060c050f010e0309041a0d051e1203010504050405031e1c 68
    0xb68903084400018000e85229902a05a1190b076900c3e17000303501c045e100410012a072150030009503580000401100d01024080d0542164891814643c581c1c0745c40f080303503100c2c080315070b182c85500d440d02d4150a0560f01000244003d04003180c50419842c104018503c4003001c4039000101030a04400240241304c00c08182d503085000d50319a940419246c41048941c65862102114000c42c21050840c40021a10590b0707c91030350507000b080d41443c5414098400d50b02503d41034a09800c1080c00d20010ba00281c0345c2103201e41c147c9243e40c4039100c2d841041c000c2d00410528500b5610045000100e2071fa000b10303011a00e034058015560f81000c3d00031a00d0030f07280f55600100090303004102107040e50415501200c0000442c10405844007410740002e98104543c1400340da85d9031268400d5811041401c85c0128450300180c01480540c404070040d0300a0b0105210380341c802d0740c0c1c400000e410700105004641500900c4402d110607c440300075201c0c01500841c201c050b000314145a5900030b81810f1140307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 188870170 1250 188868920 188868961
    0x31e07080a0c0203070609030e012019020d2f01020d2001090b0f010f0f03050706211b110102131e051329100f030b1002070e 55
    0x401006640380464940a0042801070b0b40c01c510003088000d011520510401d0f400c1c82c804da8a802d80b00c01d0100004200b11010001d0101441d41d83d0131301d90110354006000766180c00200c280380e584986030700003e0200d00122801621120030343c5210050100903e1078010740301d1900e00b1b1050b0740b848041c012603880c045082000702140110424008015464481c1680416500008651100c040d82c40980040c130071368441c152032901000511410921850707940c064a03100b416006051300e1034565560301c4546110740020302c5908e1070321510500c02c0e526040c2c01049488414029a03070900520a2801d0050500d040025806a2405034030801030003210308000b902078445e2145e50030030600410905400072100e10b4a80c40e04800281500c03804117910708a0035035880040da0440740352843d0200050706445101c1882c64840c0c0e401c1c1a075945c4c0c040040f400c0320b442c20401200ca6903a090300100500324100c0e034045c081c40c4143d00c1039035000030340303d066403000450400c281d21030303030040968142d12202 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 188871420 1250 188870170 188870177
    0x506270f0708330402040303050c0105010501050a020303150a030b07020c030d030b0102070302012d021b0609010f03021b01061502160339090903030e070b0d0b1201020a020102031e07 80
    0x200b4a90049441501c3c824011811104406030000140000d080b0381c00b55001703c010070380106440000210070300c102030050800b800d05615020480c40025142c1c40001c21280c28001d0030450443c03252114008070000d59030007001c414044c10042e00c00b071b65441604450758071910650302280f07091071082c0510f01040006800030a8998219801540c3d542000c4404510a86948882000b000c0b031b010281100010baa1f00600a002c4948000141c0401c44048060040108120209140c4da001d5400e00b01d0300007501d40161600c112a200304035035100c0072140c1c030741c0c0d608198012503400343c0c034022100c507011150200d80c4100c000604404010f500c0b440050155420b510341004003007027031803a0340c05000e6414900f01c201064851111402c40d500d4000c100120354584060781050741501c103858a0b185400010082d02d0716052188d0001d109600d21400e2094481c0452a090344035041206203e0340d544002b0764a4000040009000b0340007210515422501402d1540c7e1108040d0a10b0f809581c99a5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 188872670 1250 188871420 188871451
    0x219090b0f15090301090507030b071b0b19020d0f0203010f09050c07020111031210030b011d0106030e0c04060b031b0f03040305031302060d060e06060f04090506270f0708 75
    0x31640c4560860315003d5015500c8202142c0050020301c40340c0080c40c440c8045020904140380010085107031015038181e171440007001c0b04041040d1131501540004001c0440541305003401009002c0e006001035000654145200c6140d4220140c015506071140c9041c002d00349036031060490240d60f016100c941407460100010009540714044a00c881003010088924190140001844612003159041d1420700d140304240100407145007454014444000034a441c2c0c0340421001e50380002c184614020b055440101401800052180000c14000108100000d542e201d500004a620440315404041d102161040c00301c0d030340710143c80011142d33401c96425503866650a4546500140075442c400031902000001a83d41600a00440d40c51722000318009240c407001030024000030700b01714480c030400d206810101c0c000f001510200c8503141e40205503925031a000c11354901840010032600c900794418041c205040880550044c4940042428540c0d100c15044410000c1510000304904200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 188873920 1250 188872670 188872699
    0x405010e0f0a1203030e010b0f010f0c14070608060f1203030c130e040f060e0d020c13060b03070207060806060a05071506050301050a0c03060b0301030c0e130219090b0f 74
    0x20042884030000c0e1612880c0e6880f201240c1c1100060710b0114000fa494000c0c0b4142c100f0280150440d81a041d5103080100f4601d200103090008198000000c000c81c1c0003003c8103020307040051032040501d86041c0e6001944602005002034001c0343d00f80e00413030000341760901508003200882148400c040280d421500c0e9a440051107510844051028109000001c5021001c008280780103511400d0311940a18075071400405440b58001300041b690000a80987c10a4004c5500c1d4500041100c031030300d2020441036484000c00198109034804d80c0080700708049540c0000d15481554915151481140d541c1e2080060301e01c25505824005007040c4040400503029401002034045450b0700414a6034071600400e003101c808407144245282c80e102e80c1e1001c00d4140c0308d04c101901115000350f01d1581036448a546409061249000d072003101d9001403480704008008801d00c40d802058400040b0701d0a61948008030303580105a04540360601d032402d14a085840ea10410002426019104510 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 188875170 1250 188873920 188873929
    0x606041409130b0f0411040509030a05280906140a050409020a020a051213080c0f060c0a080c073002010e0301060b0d050906011a03010312091d1b0405010e 68
    0x50b10b0261002d0300d040ca4000040c0c0340e0381c0200d200c0c00c0007888011440c6440d00b001c1c40c40c48001b40d4864010b038540710620209900110403244580494100300360303290554452540441c0e030000685620011802c640592a54819400ca0442d441940c900e40d04141d0003481e4003940c4910400701e8040703a4100010401e440e420707009406400c42500640c0e4007480c094070303468100840d0544102c2100800190101e112140c104d034080500001401803c1900720440420780a001e0001031611030340011900112001c8208008481305500241d200c0d1a280040d134241d0303880b0487c0c05442075004001c20402482e4202011003045400401d031007264101c07854005441c00d404130208150155203075100412400740500080103103002c0302c6400901d51818000484c107141c0180c0288504084c3e440300c01c1903071001c0c0c90030360b419a40c000c2c074071803030041c21441c040e1042d010b95400460800b241085040c401d032044404140706403000595130300182804041c5107540d10550144902003117031020240154100b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 188876420 1250 188875170 188875189
    0x9010e071b0b0a0b01120e0303041709031f061202010806010305150406060c1b0f1e050d03110f16061110020c0604031803020d080a030b1c020906060414 67
    0x2030310458440c201078807045602c1c00d080b2000b007141501c480440703a180d40e201c50611140b07140b031502000141c450b10b0f030240d203c3c84041d0001c1c01c8003620f88502c6408070010001c41c0e1055031300404840d60300c400780b000c40004070214031841500394541300d40041c600003510b00144089605030350b0007016a44030310042d0000d00c0f01514007034004a1503546082c01d070f210303446050050311060b100c2104000251508840762100004203084100d00c00b40200070f4640e0340c00240c01a5003440d034100c000384c1d002c400e08840d014915400790b030740000740c406e0303903010705400404030403e41e5598000d461810680d080b0082d0744158103c00c1c00b1141d0b010301000c101080c0300d0502040c0c107005030001d17100c291001d00e000c1d0080c4d0700240b9040701d40b50401828403040580050112841d6608c6154a075113051446c2c0002c0d0302e0300000c1001070004e140000e078200016209900000000d20b00505020280c140c41c00c2c4089803c00c1144220b000789100d0021501601e800d20698045540440c210b8110404410a1142c03565 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 188877670 1250 188876420 188876447
    0x81f0f050909100c11060108030c06270d200a080d1d06070801080d020105090a030e01120603060219030b060a0e21150a1509180501050405010b010e09010e07 69
    0xe4100d000c20750483c24025616903019036a01d1408410300e00c01240c2c1000d2041c0d100c0002540204403205140c440814200d50000342c2d100d1080000880340310b0b0b031403014040122035003a40140c07192075007070039006018020280075501e0144003086061807059a202d081c000003408001080c80b09034464050384c0c116854020303058295224401b4100d144030b140036000e031503020208100100600c4441803c02c0380c400c1c41c003d00d2000f40000c3c10301c0002c0702e840c0c0003100c0c1c0103010094400441540759010380d64041501c202c40004002040d80c900301035009421004203100d20076001107005010380c0c82030082c43d810780c2c8014130b87c03840c0c5400c1000580d1844a0700d100e840d04010821401e1040100122418010000c484081c0422030402c80c0404cd45640041000c075200e0300d000554142c103180614402c060720344030880010741104000f5982500300429100514942c00c00b000c0204101064101403001c40082c0c0710070806161050070402080c0c8240620800841088002803031355110300c1c0c00f0319140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 188878920 1250 188877670 188877673
    0x9030d1107020a0905090a0c1502160b070611091207060e01050403031b020a1d060a062607120e010e1905150703021b0a05060703050912070c090606081f0f050909 71
    0x1c150f03072440d420400c5270b03200384002c90035803c0340040e154043c041e440341c0d1208403102c140f5403410802d0403807050141d1a400303809141e54070300c0c216006c40e20a00b1295101001840d019044140069040e034800c1507002d00c03400a800e00d08464110750192042d070303007600d6050700c0e8480c0c00e540010b6071004540c181c034026680710500c0d82c1d00007009460818020b61a00601700340c11041e280141c284003620215500a404114500c2c0d0100750b640c104658854190f4003103009025141c8514008440340025055000c80c29460221404c0c00e0140550018200e008103500b40d4480606194800400e8030740c1103c0a00740342c02004420b80382050700c181c1e16038013080c182001818044580800c5500480c1c0501c07440e01e40c0d100d4800c402c00c4c4402084116484100c170325081c0302600d81a0b00c0305444011010043c4000000402c0340e50402c42100c0b42e11000e010501301c00c100b03183c6da80800502500741a9001410b410034035101401d00d042d100140c0d001c5c0c072103045078500358911f080144640180000d201284a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 188880170 1250 188878920 188878933
    0x702151b070b0d090203030f0a1211070b071d03030a020102040f2c0a1107060f14060a17030f0a030b011b1a06041503050303010501030b120a081b0609030d1107020a090509 75
    0x160b403000e08528110f591782d004e003035084940c0c102b080314400180d48050100c2030110800044c0070301e62403a4040500c0c900a4034200000c140e1134034107501104c2656250001007059002c0c941e0540c068804c441131034000c41601c5070b6503065181030000c44118001031808481c1010216440060350580200c428a00050301a00012060045030410340045420503140c9040050300c81060040102140d5142d5900056040c948006000d05400d40b00b2441540000700f01000c0800013482564468200c400c2d00c613595a03d1103c0060042451ba9102c82c0420203d8a581800324000810703000c006a200d5245020003040010345409440014202c2c0d0380241c0300d401d407454072521008968001c0d84a44002c41e26941440b0000d402d5900c50301903103008651105480c3c14411001a40722050382d040781010355036005182c3e504c8030f840100310303489441e4881c4000740200d00c013000004040c10071554204001840715203942801521800001940c40741183c80d082c0030f113a540703a0040b07401c20f482804507240d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 188881420 1250 188880170 188880187
    0x50f0c071b080c090a14152b02010f0804030c06021608130f1d010909050f06011d0703020414040f06051c02040e0309060d0c03020702151b070b0d09020303 68
    0x201d4144980044107941c020040101d442d0070555015508100801002e0010310843c11104888040080c148840106c004070310075844d4941c01c07001c05459400312403030180d42d42c80000111060f6001002240010104182c8036a031504c5400b41a0240c1d030b01d55910100d01e101610388134069080041c14078900311500d403481000a610070020103861601c1069903400518104400c01114500d0b403151400b00380381c6001e014400071003041541542e200c05000203411440703040203460300c0d1416420200b06c0c803840e0001701e5001ca80c000603201c40451646a04020341d58810200e09030300440c0b2461034481035040c1081c00c0c51420b60801300c1c40c440800c60000361140d4030310020b011500a40049d040311000083c3c4902581081c0c000c040708201404011840e20030000082441845405056100302d5a038182c031170499403003501102c6640c0d400801c0320810031110244e0380201ea01c8010842184200700505519054020030301c80200c070000200d0600b005c100700c00481c003030082c6900490740b41c0003c2040d40e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 188882670 1250 188881420 188881463
    0x9020f0607060c021204050d0314090a030803190c08010302041d01110a03110708030408072a06020f071406130b04080705030708011802060c1504031d04050f0c07 71
    0xd2207900a40021420200d00f510103414070007581485440c0c0c1000300428001911920345400b0030f0f60381450168070f990071091882d02c09016580f41c1991000010a00105020608014500503107100c40703c0e4100580c41a0110f0899880c203c0356400b00b50042c0c0100050301d884e0b441650041c030560300031100348201c1013280b401c5520301800e03890b01c1c080c04910b401e00070b039044c0320b0b020b0840c03070001e8401d01e41030694036840c01500004200602d5040d00040c0034040106002c00600c1201d1220040501003500c24003080403003041d4000c940051248444409000000040560849840e1103038100800310a005106155214140090711140d1a003400030b08200c07c0c00c024002442002d0182c02c030036041030205420001140d0140c40140c0c10640f14030f860341290107250a0080c0d0468a280c1d44800400001d07045c400f04001802e04003c103241007205168001003c200f040411101140c00410454208811070308244c0c5c041c00c4c2503002c0400203500254403001050001d01480300411103400505140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 188883920 1250 188882670 188882677
    0x608160507061b0905010c050703120c050f030304170712050922060806060a0b0a03091109160809010c0c02100e091003021305070c200d030e0f01050c0604030309020f06 74
    0x1040f800a075079000d0140503502011110151500740b818601440e0681c643d240d9494150002410407002c0311850040c2c41d01030640702800c0c96004d0309503070103081d40048942c0c0302e07002200d0564160303c151071402c000024150446450302d900c00f20114120116070340c101d580303402940300036402c08030300400541e24009031100c40c010740c0b840840218030141031011060610001503d2035001d02e07030002047c00481600000e03a6581d030810310740000d030740d4500c1c142007544849078040190007405134424001e0418440001080c121100c7c1ca0360015a11a504120300306c414810100d00013070b80c020341c01c000500d00300c4050a1600b00340e140c031003d4a17000308001416618240c0e40d5805071140f421080085060a0a40c0026120317a504100483e1034100f1b8064074113008035000520407614106103412080c1b000340d03102204e1402524001400e001d070314000c0c0011a901007042c0c80744070700300401c07002507109100300c070000c040c2e01d00034010341d48459400303138058020ba0004982c049401c0d0409041500c854015 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 188885170 1250 188883920 188883941
    0x409031b0503130b030103061a090f0714030a020a02010c0f050f03041a0108030a0206060406030c180e19030e030102030c0a1101090506040b04020118050907140409150509070504060816050706 84
    0x2131a94035455807610600721101c00c03001090383e4460f21040b41c502c0c0c1e10700c07143d00e03441380da0550a4050390f924040b048a000c1d013200d1040449107404001d0090b011003a9014100b02c001c550002c000c145003109040d500c0d02444c601030000034400700500715802c4940000b40d5046031060b01c6107103600c001000e41900903075090b00080c04540c000f00b483e000507641040042d801400c00d540c100015410350f00c0c1e80300d5680440c0030f003e0784008a035002404014031580005440c40300f0200361070b82c94801200304404e000e42005c0c182c0010340c3c1c7c030518511628043c401c981c02141001800c610b00f400350344040d14072949400003c14195641c80c0c4082c0444c40c188800d81c03040d8482e0b03244099034a401d20014021074540d5000d0409803e03040d00034081034072032412036608030000d4244003030b0004100308011524411074001c81e4245082c0510071f80199040d8101c00180d0b038040b00e091900f990707101c508903264000c0e40301c2e0100080003400418550309540051600c1c620341071402902d0000c094403403d066550280d030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 188886420 1250 188885170 188885189
    0x5040606020a02270406020304022e0e180106030b0d0c080d110a030801050405090a0615090c080f0703020d060e0f010e01060309052503051c020c0409031b050313 71
    0x1c0d104520b0820491420383c10015113044c4809520308803007981c400003c1c0300818081d8000042030965643c0141954a120040010102c4104410540310304140100c5a413010866550100307100e07292102142e4412b4500d0005900300717030305c2d042044001d00a081ca00503004041c0d44d24041c0803400044c450000340c104500240507906041000a000c542207108182c0300d0340000803450001781d40071640d04d045135411a40420f141e111b00d1000e50034540052401005a0318080c2c002070102d10803111b010407505501420403c1c480d203680c09883c02c1d01c080705e204180144401c000b8403158001e501400321045a4000010a141c807600c0807541c031081680e4400201606400401c0f400045811483c0900103d14091008911340e40d14242c3d2669120140a140c4503004192034007200041101802160084104c6802c0c00108030b6818602000424400040c003944c0c0c8802d459060a00800092a5050f5956610a840d42c00d0f001d001840f440003c80c4c0310700081140191001c900410f8201500c04c441 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 188887670 1250 188886420 188886433
    0x304050706090504090b06041509020c0604050c0d050a03080c040905070c02040606031505090402060904090821130605100e15030c0306060d080309011e0204030302010e060402061b070504060602 85
    0x14000e0124210755003d14821402c0c41d50803c00203c05444c81608050180d8000c036078a15802c4800100a6007600031015445c404500c640000c0e4000426a0255000d5801e4503622140d8505101c0c5400a400d4054080c1d84a404088002031150004561115800c45c40300d007020345038240101503880540d00780740001c490120350820b40c5068443e1000608441c1801c120070a0071b9075100154070b0041c4a683d00c1500c012000030f0954840754121000200c000307008014006580c9080e90094000180002c482000c100a82c815003c203242928059100040107441d410641d039105405020000d21a21803c480d0301310000303854000c07502d450b0141840d002c04450103c883e00a140ca81110001c510b4031035440380c0140b00f45a11904045000305400105042c1d40303a0700c10440c0c50241020b11010200861066200c210036445c030f50240c8282da21940c002d22900303209221075596100c0603075000c4d6004070300300300700c02d41418a04d054680000034001510002c0d555031000408070b0707c1a5108202580040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 188888920 1250 188887670 188887679
    0x6090203150702060a090c080601030b012306040b0a0201020c0109050c1206010b0702060c150705090a090227120a060e0d0810052205150a08010b0d02101403040507 72
    0x81c42114485250341c03606000600e441a00203583c2d030f00240000000d00c0d60307034024409010240644c0030242200c5002c4450952b542d22704484034110034402e000c01044107001c07500d00b92400da40002213030f55004001034106420074907551070540c4184681c3e410b565080200b895094800c0c0142e540c400e0080019101440b41d075428000f030400385241400d426004040144200030781d001c2524041601920716503110544011018900142222010010300c02c54040020855008008002c2c41c4820350701821a01c1d41d400d261000d03070040d01c0d00c2c506411605a10258605131044988940c079034024003e000d2a42e409082c0790130310300c000c00b00b43c40c5503440d0100791040c0d01c000c118040f840e100ea407a142c5c4a51910608210900030745000b00d600c0340e03080c1a0341000341000340c00c0c50440340c403c14004001c01c2c28410f2520b03c603803c1d081511030098900940021790755006200d08070744682d01801031007100904c2d07801c1000406001c0d0184c414402c03400352003100019010003079480f40d48a400107049003402c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 188890170 1250 188888920 188888923
    0x2101101151404020c0703080d021b160e060f09220501050a051f090e031309150b0f0d020304080d0c120b0603010b0403030e04110c03070c12050705131806090203 71
    0x80340c461400f590040060b004600000940901180c1d04020440d4031405400c0078400a44615004d00b00001c60700107007410200c00c0443c4407503500801c544880c54882d41c0700100320740390108842c0725a20641940c4d8111140c1080c0c4603d41c2d004011184c80c0c10358854114150340c00d011400425100c9070b40d518100003510f2010301c285504804080c484802d5802c508903c0c400548403030140007080c036143d0200d101900070801c1920800f4003240b4414036400c0e101d0040710f0080c0742c940c2ca4601c52103034000c130020344038040d08200d820030320019035082e00d0208118016400381d400600b0803500e069040020060400891103403520179190b580d110300401484010030410f49040d0f42c0c2c5584686001c1004001003695501142d00301d03549800c0a0f010083c0d585d0000d002410100c00200707407140b0018106804050100c01445000d100c2c9039030300f05544c0c0351a660094111a920010400d500002d8240b20620304180520010320b4082c101003005800e0a08140840c50410310440e405901c41c0d01c0ca4085140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 188891420 1250 188890170 188890199
    0xd0909060308070318050a0b07031205070207050f030a02130203190506030d11011b090914090a060504020a031403040311010e10030e07080f060a06060f09030210110115 74
    0x100010502480e07003507440b800350500c51040020140b01d1561501300c0c081d0b0301c81d0384410080c0030041105900c16903403240701140741d0204100314002035010900c655294018450540942400e40c010480e2904120500100106a159007681407280801210040e42c4290720010024a00d00340076841e0b0401d03a0b0002488041c4120480c6600c3c140f4041000359200000c125006516500d00fa0002e40d20000850b40102203100c1150301c014105a00d002c902c0b0b4115a1140460308510b108119414100f2050351210f0010380717201030182c11907003100c80890301d180c1042d50001e0008000c800825500d945803d00001620440e000c41e070030100302041804501130001a01180031300740a02c1c8501b0501c0000c07000e58454902000303266461510743c440c500c041101d08098081c80c0c0880340c0c130f45000a84543d454204540c2d01004ca800c2c5000401d0103803042c090085800f01c41d0325041c084a0443c0c2c20002c1d496a01c840c2c03941007002c1004900d00048090080d0b0f01e81c06e170345000800e007140c103090b5400001003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 188892670 1250 188891420 188891429
    0x60306020315010f020d27080105130203100b060405100504050a060c1104090b060411090301020705032502010512072309100305060d02061e040806010602070e1506130801050106020d09 81
    0x100000c248401481c4c120710961082e00c031440c80021a444400583c0d99055007032341000b0b80d80d6180c00c0c10012104d04440c0da440c04076000314101d9449900e141903890684000314038031500080203020800450509641082c510f48143c1800d80c10240c4400105483e0400c685c41000014140500d4405020352801e07142c0000000b80c0b014060b030aa80d407280340188101815079405603030707920155032504403203201351020076000400075960b401060800c07070340c2e81c0c010703102c4030410310201c40c40105043c08240988024950684803141004090660035002001c0100008140b016044200034034040c00c0ca285101e07900d40c1c80c2e42540317a6000310180240d501d0400411420f2514000a120349a0307a400401b0840c07642c101c0340e00e40d550b01443c1c180c54040b5082c002110208001060109140c0c401180c21030585940313500702d8100e030342d890b5481030004900340c86501c052002c143c83c000082c00d28400419420300e000b17041488040d50340f48014216078090b4005e0700140c000c8039a0340328007070307200504500a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 188893920 1250 188892670 188892673
    0x31415010905060906310218040204080a020910050303041d1503191a040503040e251409030a080406140c030d0513060609050403030e0d080c0d060306020315010f02 72
    0x83c501200418500d000290140344500002d2020f01030080022003020340f001030056071520304246a20724030003c2d402c60401c10ba900941600c0d00121400c1c2031080e50119940440189010716043d02402840a000341004220646210000c100c54800300300800c0100101680005c104150080050758003e000d0030a94100d5103248804440344e41c001084425411541101e840f50a014540356805a40c400a2203002c0700303000d401c1005208010000e8000c842c0b076100307451840c0d42c1c0ea15003640340c0b00c1d083c0102c52071100709200d00030606211744811407980d041181c140f46880c821000082c83d042d80e403801210400c900242c1449001c0d88601204080701200e092a41031842440100f6140e001b190303040c0721000e60702c00000d003052806180d01403006030000c8007004415216400b40000c4e140071070741900403d041041155407420300080c610614022903994400d070b916540c14902d410f0740503806106000313440d0580440480c038030380300850051000d1400c15910486400c000b51501c98620076140a5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 188895170 1250 188893920 188893931
    0x50c01030f0e06070f02070503010504080409141306020a030e06040b15031603110301110a031b0e0904140c04020a020c030d020115061206170c01030b0910140a0314150109 75
    0x2664001840d0b604112141844599017003e000c040349007003000d601c26a03040d801d003014030045c404c5020052007038429680050250700d2617080b050b0080401500c503c01250700716010381012442c42d901411010020780703404903443d00c030420b29920700360301038505803500c42d80e50090040c00114050000800c110680c0030304a0485401d132030200c40800c910000e441026100420b0010341d40c00e6001e21074101c0300480046e15801c4440004006050301c2c001e20b07100c0703c02000c103429414082e8a0114880d540240904004d40d55039980501c40800040340c1e5009214100c00d14a040e900d074005082e1550060313000f8401411400205441c02c071402410000f5039160001c101c0c2a50311505055050700c01b203041c00b400925030020703504010583e680c41140e1000f030b0045141040700c004107506141420903a400e01103451a54200174403024244d4100207070007024001001055441c00c0c0c0c0c1410f4540050041c90625a82d45880040c0003550007100547d4210001e0020030142803900765014000b41c82d000c100c0e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 188896420 1250 188895170 188895191
    0x1503150705070308220507030c060c171c11094b0301020703030b0f01090e06040906020c030c010212130f08220e07090501080408030406180807050c01030f 68
    0xd502c20360344060b08202c10000028501c44512600e040c64000101c1081c07a0415103042039911504a800304450040d250600003440314840c101026400741c20426109580f084a401c282c41948007a0f600014020f07942c22411006c40c0502c80c01104a50a036480d60382ca00c01d041c1081701c440c81000402800325048180d00588240780c0c0842a000c00346101c1002450003106003080d200300d48040000c0e455800058103074205035041c5c020450603030b015549441940540740040d1340c00d00c01801924258241880000c0303042c5002e401c0000d099025800c01031030481074482540c116840b04050705520f80d00002d54200174503040d502550700c0040202c02e04c0501201c0d6a8031300040804031001381000601103801c42034818407003028451f003d41c112901c0481a912258000c02500c21225000032030618440095594001d9801c40d101e1a441142c44c0e00d5030b640e617a00e41c002000c072031501e500c41d41c031b604140d800011070500040c24054040c500500c01074842d070740010190b41c641c59248818034140b840b90303070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 188897670 1250 188896420 188896427
    0x103020418090203072c010b03390708030103230c040f0b090708010e0c0a080a021e07050a021903150c03150e01030510020415030e031215031507 64
    0x68404030402408584444940002407410145810020b0300d032054032440402441c00d41ba0040d111b5091032041410381eaa100e4000c07603140000c07120390101c3c108206040071002c8840c070045400c0b8401d441e4030981110b40c220b441c01160048403086504400000052051000780710404403a440080021581034401c0d0004540ba100b030110844e008544819028031a882d05404c0300b85d0290018040c110346140208000f0b004410a100795a0201800d40110740030344200011140d10320311300d03207484e4020703141d4035413180c001c0d804103001c44045201d030034068410302911001002d50034021001843c80d048036004000030010310460402018501490400c00280c6251810301240701e0703007100080c03008501d0401d4010780f050425540000e590740d035000c6140c00c400d545c0380d030581c0d000743d044801000714944803400724452030280740c4031042c98651803028903101e500421007034503d12003030324141200410f094018260a652114601041900c0040d1030f0504100b0011089100c09200c8058244100d026 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 188898920 1250 188897670 188897699
    0x110d0e0708191104090206160201140901170411030a1218120602030703090b0c180901050a031506080d050a1b02010905010e03010207200306130203031b0c041509060501030204 77
    0x148040e91100040f4420b40d03950b40b1500304e25030064003440da11000d1000780c05110072444012404103504c1c040200542008030140d840418060b110354400c042901c00784034560740000c004865100003000070381c4685e1820304c1110200d03403080c0b20444402c4000d580c00380c404080c051003d581a4400c010030081d032202208034007a0290401030046c0e503900c800404901505441d0b0028000c20082403d008404003180001c100342c1140403446102410120104505c902c0c080c82a41da020800c2a000c1c030101d103c244540d00410044400042c985a83d03504403410094030a440b4804200040b44280318640c014036120551001c0015400309451550300191480d0352a000d842d04018640c44c0c2c2c0301164400b50f044442650308449400a11110890640d01c2110301d1600c10707009004032000320b01c01480c001d803c41d28003035004000c1c50034525503081d0f0740710010a060711040c89100d800d07048140c036112441600a441c4120108103c014140a910001d0310095404141054810041008481c0403070425 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 188900170 1250 188898920 188898923
    0x702030c0304060e0f04110a02010b04020f0901210501140a0909030f110307050304080d0e0d0f0206090a051002060604050711060c07050a12090e10080604110301110d0e070819 77
    0x103489146285011440c041c15441803141c000349050801607d10b500034020b001004001e82c000d201140e07902c0144400e0f80606020000c900206021a40f03156004902c0103000340d91a9031580074840c4004811f1003514400c1e03021030300a0080794002c0c200c034204000c0e00e501071300207550300344948051980c005000c1c0d441d0003000810014100e00028160f1028030480d000e00d82c00c43c1c200c9803550f4580c80c0003a12009500c02c0c10001c01c5811544501c2404e040e041d4003120381e005610255507003015002d1002c29071203410516800414148003081ca1799072401c100f00010b035168024545440d01e401400100c0701d01034503420038000e180400c0d287c800000180241e100d51032408040d150380181c5440380c94116002d400601c00d10200b400460300ca80e001d426141203450034804000c003922203001b00410b41100303014582d190782000001402096039001148a155000740000a0b0602c2c041744545642d0003140e801c9000c9602d5407240c080d030800410518001d4440c00c000362440d4007140080c001e850080140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 188901420 1250 188900170 188900177
    0x30a020921100b0f040204030c08010605041107060b04021908090d030b0a05010c080d110d06140105040e04110405190b0f0102070512030d050a3c020706060b0c01140702030c030406 79
    0xc100d00b907255501494041342d4050000e6480325203c1ca0682040d02c1107005403c00386d031038084001118503140c01848981522005d1040ca003000948a00001d003608001298005408000c181c49402803003061351036401c401e5a0300e01c43d50408010060a000d900803280b8101404c0c4842100d682e5944800181100d609092100c01e40c4141e24010070140510b4009034401d61a04106211526001009001a50800004100e000d44802e801143c00a5195800e0f0009900780028485165070100150300a8098844070400c0c918400016059600c101c640380180081d0b05101490203155000360041c1c2c1d031003144e601c0031070f601001c0001e64a0120344103c07841000980c1e880344101006008a401c0681244010b01c11032409042d940003074502e00305081181c140503100340841d00407400c2120000e8840303080d445220030340c041d80c0c400650800401511090359030b400020710401520010202807003410008550030300550104d02c19041d004041406541080140b00ba403024044112002d130781c0c0d1801c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 188902670 1250 188901420 188901431
    0xb0c0702030c0604030b040339060b03070311040b060f0a0302070f1a01050924040e070b0301230307060c150603080a092d030224030a02092110 63
    0x40c0c9482640200c2c140c0200e000140801441182d00c901c0d4499800b0b603e4201b40c2038882149000d003602c0c09001c0188500b030010240405ea54050005000c0a0203500c0100b2900c02c030b04002420483c0c2580210b402c000c9420750400242010b01800c68110340841e003e908001c0003403e003284c980700c2d891020b005c041d070010750b010410030045114001542c00c0b0b45440718561040868a68a072400c0c05418802c0e0890800107a415242489451070b141b84240c20410001000c0203101c09000c010705140003034055070201007800c0407003001841c020481443c001062031100034200d441d00310f882d0701140c080e0300139200611001740c2005d01d01540e40d501000700c0186240d40c40348080241401d8100400001000645125955000c80901c0070350384904424849200d00e6600c031041c1002108048c00c5402e0004c1c41000903207030421403400220130311340c491804812507002e0204283c0c021960f044549602050509060801c1a4040e444264400c45481d11a00b43e9150507540c08004020020a0751502c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 188903920 1250 188902670 188902673
    0xd18120206090f06160609030305060d1a10170304090c081308071a0108030705010608071505030a0609050106020f0d02060705030c0a030902030303090114060603040c0611070302031005011e030b0c07 87
    0x4007159840b4001c0c0b101d05e0380d0b070003042c503084014040a4074283c00082c01c2030085925850210341304061598001841100c42d000e0581d12200351704c000f40049a0894507000000e40c011070075015001d5405001d018556960030030101c03400315140520340ba4100001003007004201e0351280b607004c2403035801c205250b07210156490103a60311498074036858040302301d5800001e101c3c02c002001e061614411002400324a0311078810641e100c0b81449654901c245c044c040b600c1c601e020300c2c02141c015010180125040b6107401000d01944c00030782c400001640100c0820751400b00c10310240034100410b1025001d58200100e0080c1075000c003030903800481500040d0140050701980c440c1080b26806029242c5914020604500a0920214030341c0e0305515000060402c0c50901c084134070995001d440c41d940142084811610541a000f980600b4811050080003580e001c0103007116005000601191a60410113002a000d5100761444d107000702238881400090050000598000d10400d44641c403020315 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 188905170 1250 188903920 188903929
    0xa0e07051302040b0703030203010501260109020d09060509070e0901020405060706020d091b140429030f10020a0e0d0f020105030c040504020d06030201080906090606210d18120206090f 81
    0xd1394041e030f610080001e403950070950907030051070489000340c0b190f41d10800e030b9801c01d41440003034010034445031003404014480b198443d03000d81150210b0000010703001120ba0b0ba600100e800541d2286103d5000c2003081090300400d42d0a194452a210020350401d4030f086c0102e4000d000e0050010421900401c494400710f005a12585180d5040000e403040543c00c20089682030034a40101c0407400040f41060b5190b082902511944084102c202407040b840a003802c400f00c181485525894010302102c4141800d04000c0d80240d000319400c016034441c441040a00305c821410403050143d425500360402045407140d04407006902800d00380d5680d03880f0348040110384155003010303602c24070104510310081400d038042d1090300d100b0781f20102692500c2201560350740040f20303e00b0555009000144407410b04c62040d4580046088414100c650340c82c0c826070504203102c60001c001408051040c5030743e206c414141e001045541e2401c11824030315000315080c0c0c40340d45d1959006260110004a25480303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 188906420 1250 188905170 188905177
    0x5120c210c010c0905010909060605040509040f0b090313050406081507030f09050a05070f030c09110d020f03060405180d03180f0c030c090b130914030a03060e0a0e07051302 76
    0x620700e00820030b800300d01001822240850080340c0c005042c500c00445d40221034070400064400540307440e41400c3c40c0c02c2c20060310040c01442118480d40e40460400058a11070040d4040c0c500394000d1903c440081d0b204000232034441e4017480c42681131050803c088040414016464490510010060b5540480650280401c080d02e14529440c00c01d03a507090001c00301c0c90341c007014403c10546480c01c0e40d035000000d6054075800058101c0c08181410062070310310b9404049028110300e012414943d4071460302d400c0b070300101e917401003003030002040040510381032051603441034041003191f080111b82c0c1c90b115900ca445060910074141d4603072890100e2000494405d4405a0041107281582003a14204c1ca0038400d601c01150381041002000c00c0100c1d480c09124441c1d10050403a040c240d1300f500b43c8101070100c50301c0c00d4940300d140e82c0340800507190603c0246208251760700c002c940e107440e111040f408075000920101d00f603072801ca0a02c0741d01c130b4040f48920445200302c032104c00014016803250024070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 188907670 1250 188906420 188906437
    0x303050d0b09070e0415150f1101060b0702040b0306010828140f060708041e1b08060603120c030a080c0f0a080609060103180b150d0b0405120c21 64
    0xc8220401010a40c052154003d0706002d4030180109440c0a83c0302203400340a0091224910402c0407c0c07000304d100e11440000b50129250040044507240390184c01c6990302d40140c2c4051000141850035820300d40500c2410302400d400400c0290701d00024180c4a40f6800c409070b0741c1c00d2413500e652000049050301c0780702c40c1d500440790a4540c1c0c135100c0b415542c0c0d8040c103400385890040c880011040c2c1e01a1503a248103603080211038280003144001c010b6000b10b44c900484c0c40c2d0300984100c8000703d030740b0b0991402421003c001004541052000c051600140c065000d100140030800344000170004003e03208141078a04140d09540c680ca4495001380c01003811f5100105800324080d0500d503030240303400c1c0c01010300350307401507168a07000011015103144a61000c00300080340843d40020b1400c010b178030740c0599a07072402d0b00800e52010000f0b000d47c070450b0041e1401a80c050511040c05402c0c410004000a10000c480c51700c1c2e50030140715200c490010503a04d05200301d070074040a0401e50740c200d45d100d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 188908920 1250 188907670 188907679
    0xb0f06090f040f23040506091605010c030306080f070501090801020702130c020c27010e070518270103050607080f130204090b0a090b010e0907050d02030c030d0207032a0303050d0b 79
    0x482a10203240c0c0c4201302141c0c140c2e040c1c0314031004207400f0302000c00c040710300107070206ca00c6502604140064401d04180c24088040550780d848c001041d802c203000070188003541b0700280c404549400700041c4009070300d82104403141d20402c050030060b6280c0c654030195042c0c00b0ba01060f034004841040c1d0600011401c0282c111840c01c804090005030081560100020854088000c0c0d072504415100b2010403503612002ca14204196000c4602d070712000400f4050040c006c0340020302d64402c003460101004815070320782200c0b800500c00c0180500034250b20203131903d03104800c0e2901010340b40711580c000c1d01051003c3d18006280b42036403540d4000201c180d030481507102580c01c0000f030610007002c0504050340c40130000070001c25003254500000e8094060071004004007420241004161015058220f0b030600c1002840d240079101800300703003800c144da90064401d0a04c0d42c00c2c4800341401c0210602e04001280b000c02546800407103c0030103a90301840d1083e03e42001a0003038005160b40f845649d0311 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 188910170 1250 188908920 188908961
    0x1d061c0e06040c09050f0705160507030507060f1e09030209092b0206150307150e0405010b0309070f0608010e070e0d05060601020c0906090c07020a090f0b0f06090f040f 74
    0x50007030102e000f004440150310108825690300c520084444402c0d2410400a50200f014032030544240200550007030080c0705481446580e50703102c502d40780300c59001c2c0000c0b4009246003003203140c01c12410390200885000c4440c0351122528001d103a2007103400001d1084e00d41e2004a004018100039013003100b1102000401041c40040440010104403c1c0d004010f1040da4000384d9060f9801c034080f04000405401007a60381d041071003060018843d5140035040001c07400302c02c07070140c0c1c40b4010035001b40312b04c03450140e980c14070100950900e02150070400717010041d460100a00c40c3d01248481c11103003014804071058036144800c48040341070100f0541d000480506a20501c1800304905015240907000c036601308002205010340d1507412920322758000b00c4000020b018002e00802800e156200078901081d540e2070b01c03c00011280107c6622220325600c40b401c58607800c212a0b00d21031607004803aa40e0411507080d0009903001e0b000c8903c64000d5841d544000b0382c0c5a80341d0814408580041c030740940 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 188911420 1250 188910170 188910173
    0x301090b0a0501020c090f07051606050915010e010b0f1603120b011b02040c0c020901030501050f0703090b0a150b0705060a0b06040302060d02030603190807031d061c0e0604 76
    0x540142500c95104199104000600750300000701c003e107440014020307900765138030120607128241c4001c288409028041183e00e10441d804903802070b050b07102e4600002e01c2e042c0b1101191421185460141d00e800d07400f001800b524400c61752080c1120500e00c10344ea520320740d02e801940c050152070303035a13010b406003419690308040e0050030100200182d40801c0249213130403801107404003088500c840304420600222005810580c01003808444030717080400c0e5150b0300ba40440d090b0300b4246d02c2075801c1e0f55103030240300c07000303058206040d0424803034030342840040341c0c98031112061100502100c04207a5528440c6c05101d420004a8004211079848141c9a03075940c00c0c01900c8020031034008030481c1c50241d80703050924121040d141502d8003c0e040c0c5040c04850b1504400a500117042d8682c1031080e48003040d645c0c101c1000103501c00e40302c1e0031401c6d00c500043c44c01418040c0c2c51814003550400d4a032250b02ca03512000c00707403110101040303040c14500c40c0e074000400c0100034009113200305003c0c003c01c100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 188912670 1250 188911420 188911439
    0x3071709103b03040f1d0c0a1b051e01020405090612060f04080c0105040c0608060a06021b0d050304080a0213020f040308031e0403030b01030606020604020303090d03020f030301 78
    0x10111103041402d00144600c41c81c404284001c0d00d05840425249000441c0107040c0384400030840c070301e01011a442d05449003485480240e0725400000128105e12442c8128803503840c032642c00680f180380003810070f502981e010301030072440c03d0924000e07040c2c2001239041c06020085003494202404160585440d200002c41c040d41c010b0290078042c082d040040ba1945c1050f064103015010710101801580c2c4803208409441d1038041c0060b50480e100f031024107020314003880345a0007144960304c0148094134090019000340d000500785442894075010402500d500460030910070b420150000c040c0c00c00c58000a0a15004041701808600c00070034081081c02d000140740c00c00034021200c40b0030134100c1c004480c00742e100321707198001c1e083e01c10700c41000003411001c05950486031100d40a0826001002c0040d03c914085405a0010b9140d040034101b550f0103103c1c0c43c001d440c151014156600d81900825030760310030a900b050080482001400030f1502c240145141e80741c10000b41c0c0d40ea56035946400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 188913920 1250 188912670 188912683
    0x90b04050c0307060206010b19050f0d06090b0603040c0512010906050a0b010206010e010b0a0c03110a030201090b1b070807030306120804091407020d030c1824020303040201120203071709 82
    0x24068441e062004c150716000081940c100d6624a0038a40340c400710a01208151000c0541c04e800d11005001c44002500d9542c0a4084020a00400940701745040c00110640742c200b15182c0c02000204140f00110f4012424501911803d544014514911941141c01021800c0c40507142c1860b240074808200c6d40e81e082a10070110980c201eaa50745d80b224078030240131500f8401e50440340380400c4101045030056841800b2103001e070818410b800c00038000c4d02c0c10403900c2c0302c0440044c0d5403400b5034403c01c404405125040300f28051004101c01514868000c144200c0740081c000000105040c0105482a0850005020103054819842c006807030207c0b000d820900950303060908241840d2803440096003181d1140302503500504c5e00c840125019001898098800c00170001c130f02140e49040d100342c0021800405640081101304440d0f1030b4400b0780c1c48a2030300741d1000c541081003448003507a88402c9020800c4041000140d80340c80b2108191160903400c400e2944201e080700400c4071400d400b0460 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 188915170 1250 188913920 188913943
    0xf1507020a09111207020309060318060c04060f080613090b090118021e03070801020a0c03020f0d090b0c070f0909110a0e130510020c0705031b0f06030a090b0405 71
    0x58880658984840800f43d603546000d0740c41d1a4002e201542d00e01e03c0d400c00e8260040303032900640e07190011090106038240d0003102c0304503074003e000d5512402100b01b001150f40c05041030f54007a08260034110300404c410000c024001c104848a8041551680c84280a0019440840f0200480740061501042d030303203000c03141700d6419442c000b0105c050032041c040c00000300340e00409038002580a903003030000134042200b8864151052400c041000d034002d100600c030b41d074450784500131200c0d880d203402464020120b40300c102682200c030313150541907007004285050b03c400000447d103c81d9001c7d03825240ca209a403003c0b0780380c0245000000c4e411a5a800b0710752150040d2550f0720117030900824045500b00354850402e5101209000400710380340c080000e8810391080d0107031107000d61810030010680e00044902003903a00224002c000718a000c111a0252803c0000024a90649200026100021000343d1801100000b001a0030765540c2d5000582140d4000c500d84128201810000d07980e5080b02038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 188916420 1250 188915170 188915179
    0x6040915230a09050105090c0f0c070e010f0602160603090512030703020423010818030903011b0807170106050d1e09110102010209150a030b03071206060e09100b0f150702 75
    0xb000c94107288070300505040c0d60700502a40d466403030740080e102e26580409440c0090b00700c18004c0c02c005405c01e0103c0350003815202d0311001c03d0350400710f030344003074440c07a500c000259880080d0700519600b221654030121421b44c200050392085c1420310743e0404c040302039080384501000041000c8550140e0180055852040304a54440c2d0001c0e8008880c0f001c2102050109441c000004c400400080c0b20003145000c1809480c18407480e440428255203800d14000200f02030700c4100880f081e40012100d510041c2841d000c400051119090408400c0600806d410000001200e440284250304000d14840c030042c403924540068541501c01028004412241076004a20800c1c5541c414025244227500007821aa100d10041d0310f40c00310b9610984462050540f281000c40a5540612a10b0028100314003203003031481c160318020040350419001400d0540b4030a00b031002d904400113011000100c0020000f8100145000084500750341da131186900c011103050803030880641001410040344240d5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 188917670 1250 188916420 188916439
    0x306060c0201020606090601050408070905160309020904120c0b0708040204060b030105150d06081c0807020105151314011403150105010e0607030c150b0118050604091523 75
    0x10044845200000c4040d0040e407156010500601e044050720307801c46414141180350690700c040003400d08085911823045540e0302c008004001e41c3c1e841d1103041e01c6032686400c1202c0c884960000340020740181c03024052001c2c0040307640301e0174003694840945541000c1600500c1c9000813008188500841d0201d000358101712000500010301000d50741620002448502c900b0094049100d064002582000d00c0f240c13100d400158044051000c032200c21400c001d21410740f000445c001c0c1549030f014080d0801c580c901070810021709000b5104880300342c0100c07258070800c607060300c2c098081c25018003000c2071200b400000150f070700103041c240f00b48107600354140d5032858045002c41d020847c0910949000c80ca0720201d0a0a900e091802012818820b0814516401f840c0d02c4038052a11240d01041a03603985007072050896130494040c3d50745440a1404001107402d00012610501440c81800007141d2148d8180402060242941e0041e0400314010107404a80c1018010020803440b50760b40218440d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 188918920 1250 188917670 188917679
    0x506030f06250c020415170606030706080a02090a0e01062703080a1b0804050f030309130218060708030703050105060301060203040605070c1706040b0c09030618030708070303020a0306 81
    0x10030340502c6010009400c0310724a150600315541103a100150904028a48040c4001690780f80310b000300079242c40c0c1105009605106a8040042401c80100c0c02c5038003000c10818140e9000a036041940c0c003515103844079407942c1074504060b00034003002c181d0010020078007050300140721845504a86a55684a0700e18006192081000341d035190588c0e000000346d5003d0004c10ba22400070070150500740b0301400070118000c01602e03040440c0704c04850503440050100558940070f111209256011400385141203c40d20015256440018518400a8010607010284400390a01440004014100603030700c000515007090303541d008880d9040820720f0f2030004105030074900142c9060356200e07001140384c05c0c1001015500c5401000303088503040108880802c0c1b541404504900c9804410000d000908152038000d801204c01070906085102c240301e41003059400064046d0090f5800c600a412a190101207600310705c9001409010801d0009a64041650550040c41d00b110165010001503850703 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 188920170 1250 188918920 188918923
    0x30c010b1e03070b0c0a050303010f050316080d11100e0a0c06030c050f0d0219050a020d021204030b0405070806090a1406010302130218040e161a0f0d0b0604090506030f 74
    0x111900d07942540c00a00180083c401c902c00500751011355000f1100050000c2c0e440c1440c6600981211101c410800c0e4101321030f0400708072252040d000c0e94a0b421285041c90300103952060310540c1e2004105144e121681401c40a001d070018604842c02c090140c503400c1000142e41c0e01030910200c03180c1104071000104036101e4490031070008259650b4920f031904840c103400154005100706960581d081108400d070ba9a2001002a20002da840b81c54994140381c5c000b0381060710540100d010b5400c000083c41d104002c0a0440c0c00f929489007100b4180d07187c43c2441032605103550810301c500d00c1413500b440480400014484052442141720607400700c4c01801d02e42c0c03121401e10000b50060000d1000c12300003001900070f0314055044030701ea02250f807030b89000541030b02c005020380312503501314410a030703002e070400a9110080d0090f40b18820150b10b00f4001c0030958071800c2c0c00c6200412001c41d80d0104950543c000466000b001004030f43c4660b201c20baa840142429181c052103489200c03c074640b80d000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 188921420 1250 188920170 188920219
    0x71103031603051309090b060937020c0a0f140a030e01030506010e0d0813060c170c100e0c0a0617060108070c0f11090c07080327030c010b 61
    0x410012003104821542d0b01500c0e20341044144044416000a002c03541c030440c3d02c198880103008501d10f03400e50808100380110502c01828055501084d4450f020b8601e0b607080b0b40b103010440c1911038a02ca1041c0079519070080c05020100582c502486407040103001000451048841c02600421005054445500e50301c154198008021440c1000740401540c041e500c11948401c06051410f40b4001c0b0000182400032465012100c0714004100b01c1e804039488403004028207114288851003062503160714591f400d80d0b1407a1141d02c000000ca5944021090184c80e40742d50340800300b03001c40a40d5000329070b114060301c0c041c1405494922000500c007880303003500904030511081402030545400c00111071100c03004111405000411094400003550482804903480c002c0c90518525400c4608000704540064201d40408100744941008552000226900000645000511071950040000a14451038035840381800041400c00d0160350640203540e05203400c0300c44152a818840c1008150003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 188922670 1250 188921420 188921437
    0xe01050a120209040608030a111908030606070507080a0c141e0d140a0602031501051c020a031107120206060a1809020319050f06010b030420010903061107110303 71
    0x28403019803085481100d030b0080a00e0306001d00040350b03058075080c02a21b550301a07000400019071082d51031650502c14401208280c0c0400340c40750486406454104080c00080c050ba8824500041e080040027070800c0341c20010010700341500c0401d0814100803020440510544415560400742c5500c10f2038280140005002e11640d812030048100d82809201c01810100300c80c1c2c03510341c1d03000f1189034004002010300300384103000c056134034505807502d90f0120001d20300c40381c140310003400025123440180400c0a1400c50009005807600b1000c5400c401400314003420251180b80001c205080c45084511800c40a0a80e003c6440c40d8554000388600c039101032064105205a180d1241d0740480283c0102084a00041c1200ca180714400602d07500980005800c840582c000d401174000041c041c0003050050100100381ca0940c074054507030048844441005201c030f43e10002d2010040ea01440041003e10340000c000c000400802e08440c07050f0b8080c060030307200000340c0e6011125a20340002106c2107a03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 188923920 1250 188922670 188922677
    0xa021011010c18090f0b060310050a05040c0f0f0c080307090806181207020303390d08181c030e19080915040801050a050402180615031018060302010e01050a 69
    0x3ca141c82002401071003a00741184200b91108046102659510040c602a222040005146514000c00c0040a0711980d20080c0654205240a09040c0e00302002c030181186030b00745490702e87c00110301101c1c1c0440303041004007928008400c0c01602a0310210b0039080c1c1e00110219a402c0e1100403115402c280384c01594a10b682c403c90804464000d244058125903102404890821018205c501010612240d40c6000c0d01c099003001c4424119240f034080b013401808010300840489110014201c0784e0040941c41005180d0360340c0b86841c48104424481c00903080c00074008105c25000003406041003100030151f40c4103020044580c89509a0403200032540a000c492401240314117000d2001d40d0000d0b00c10a1450030711002441410078000c2c94810940c14400140926040c810481081c0b00e520b171110407444418204405130701c40c084010760a600c80b114443c1c0300e985d101c4000c0041d0910781c00c001002e515050021050426070380000007a28400d803246901c40c802c0d03800444140c0139424540c1c001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 188925170 1250 188923920 188923967
    0x140303060a081603060c0504051e04050f04081611040c030e12040506070b060301110c010e100603020306131b091b050708040b07050304030b2707060207050108090a021011010c 77
    0x1105d640c42892078000c0340c00c1650400d9a0340d400180d21481e0302e010581c010683c9a0b51801c0f52078607200300e5901c403680502100c85070034161038009240c05002400e4449600b841d0742003003444034400840c0b42c050b6000703006011440c1090002406015520001c0c0c80034495130805860120b0480261340c1601c2c00a00740d07504040068542003c00c4101a01568055503a40d080440c502c07425070040c511030301d403a0008241c070b42105185601c0d0030302e80349001d02c003589012020310041e0b8010070701c550041d2618940c04424001c3d402d1030000d55207030480e8071040c83c1d13031250000b5003540740f5080312103ca010242003010350342410505aa02d03106e46d0400070b12000080106002e00c01200001c0c0141da40140b0880c1e0a00340c0b01e5a0f622036504041d5101d60034a1502c2007291925020002884c04050b601c40141080515204003c0d5a4810f580103507030622511200007042d4038003c101c425980c030340080401c0500020030f00050048415508907105650800b04984000382c001d1042c82400754590015182 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 188926420 1250 188925170 188925173
    0x20a0c1b0b09011808030f0c070b04051c03140c070504050a0c0804020d29060f0a05130b06090310020a02060906042001050c07060f020f010902060412020d140303060a081603 76
    0x2250124407000c0d0500c10104280401d40085c200050300760b880c280021507645550b0035103683d2800003194410488440100b005101c2500c40d00e41e1f58460b400e131200d600040c40c0461406a0b2400300c0c00c4c410740d9415101060790000325100181e800100c0704183d07030400c0ba9454901442040c0d8007581503c00c04502c07400007060050802104d41c9a24601a0104031044504081400e492400041034603040b941d0310710a010140ca060900050400002c45004007694540000b00300100d00c0350720085800c1d507a4103445203854513008110b5100050040654003455142240b08009402c100d803050014030610300000c5001c1d03400a80d02e07006641040050303501d03604400b01045082d40030300c0d4540c10030209001c2c440054601304110303000b5106a48440089140c2203400920b00740d1070406960b1039a0501da099805a250b800455042d107081d000802103ea0f840d0010400c2c1c0c40d07038608020030062a6010f018510100032000c0c5008243c100c84408666070b0310981c0c00d964100c0e0101407100782510f00d80400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 188927670 1250 188926420 188926427
    0x8070b03040227040302060604050702030c0a0b1506040b0c0d1103030a09110607120806010c031403090a080c03090a0902030903091e040608150a1803030c030609020a0c1b0b0901 78
    0x548030519502c0608001c05040f000d982410020384003100540d0180d0180581483e190166540c4241c09100031030500300107403041659043e01c2a400751107040000e01190004100d0610845901d1020f0441a6543c0c3e0314008030031b5990040b160301415004400f031074600144121502d84a005151000318110b84070101c9480007410f020b8803c03070b00c031440030980503180e403140c8010b004818040c6a20f0302c83c1801086014013407650051685040105005240c00000c0e08040142e030f20002d2500425180d42c2d07074a00035446c2154003400a0b00304c10000c600342051040000c001c0150607015650445120740d541d01000990000b6100401c8681040c03000303000700e040c4411300030b580d0030030b0042d10b4060a54200c003180440b08260007411a94011150021101106c04001c0b030300b0548080c000c1011011000c503000c0039505503040101015190344545158603c0307600310002802c0103000c210b503109030411018002c00c24501d400c45080720320591042900404406c400c0485100c9417426180914820045 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 188928920 1250 188927670 188927689
    0x9091208070e0a090b1305092806060b18010903021003090f060c0203180609010f120f060605030915010501021902150714150705040512010b03010f0c0908070b030402 73
    0x401111284640c10b81d81c0d2111918020074210000141e00120301041c810741000e0069409100d50819040c407030403400024070096060008030442c0c6050b550060440380e03801c0228409807105007030143c0401c40c4172140c0c005108602c001a042401c0e042020019100b542c22403001944c8000c2840700041c0d028020b4125441c5184900e404444600c2159030720f4044500724015032006900c085a081c0c1c0d5119041403940d4002401c80c2c2c410300340301c1000c000a00700b1840c0240c1c60208450300e00e034030384a4491a0000c0354ad80c03000c00400d0200c5503ea4000030f00f07a8000315107410480c440c603030b5041885800296001d05845040e40600f02541400140d0413540b0051101207800c00036030700c0482c1c100c071412009001c05030b1080004c085007505520b030151401c0c20084000c2d4a041440007403160b1349401200b15412103030162401034245005016440c010807104e80115055400c200b124040d200d6664010300d5070200c0307a110655800c6d12034603103d41d81c0c804c6024820700c0700c0082000c180540340c0300030003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 188930170 1250 188928920 188928931
    0x118090c0306081e160510120f09151104080c010c03020307061a09070f021c0225091b0c060906181103010e010204050102100902060c12071109070c030e01031d150109091208 76
    0x880c1e007270440410a4215120313044299400c0d281842d10300300507c624000c141070200f909008a00b09070419200a403200c1420800f207051210441148003014000d1007500c0c002c0c9d800020820103802610340c09885041c0302c5190f41e104502030b85c001031400d80030304103140c0124602d90050541c1b84031300c000c2900ca180c060314803406604c1082c40b10503920032a0810030072001e04405410502a2810001b0f20a0725a0301041050140c003000c03520400c954001020010b00c0e03005900419003a0701340c100000102111030001d0b03072804e002c2e4090400d0121500a003190301c05c0c254005c00003640009003440c00c13405540207441c016046082c01503031004194005a0b121030008105030300c6d00074040000c5103031400d26240d01c41d8082020035440c0c00d011544929003e46201510b95254500c0d040900506182095400400340506100f00780f2107648a50710480b451005004081d2071501a0110301d955111280cac99851022011800442c80c91024010410060740c00309001c000c1000548090322141c600404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 188931420 1250 188930170 188930207
    0xf0204090809100905040e011103071b020406090507020f01020c1f061e030c0b040b0a032430030e090901020f0304080a08060118090c0306081e160510 66
    0x1800c001907540e08800d21088040da1513800595141030240406d4a20308204502c450349000c9403054408104011243e020181d440c1c0302d1640103120100c0c0c042862484000b94001d03280040108d4060300d04e134405401190340c0c3d000c8419003c80c04000d40d0030b07482240d0350b082e41038000b84540240b02c01000c3d5006034140040902050b07080e190300194510400612418030324180d079080800a1108501c40c0384007070100300c20071030702c0c103811f00907021b0b01403103004018020550ba404031504a403102d02211074000c0c0340340311841e410350742c3c031001e26201007035440c1012000d400c01c522031060303403509107842a05580e058403420320080c1c1107000c20003400402404501c0075502005aa541c0c5890700c3e0066114502c0765980303540700c020807800240880c000034802410b1118801070340403005003800040d030448911000104c0d010941c4d200c03c6019112561001845214090184200346600c0d80020105902c200c101e03096408410010b0740c04103102d106040d04001c0c3c0007403484e01030b40300d000601040104800c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 188932670 1250 188931420 188931427
    0xc081902031914010216020a1a0a0806040902040c0216050306040f08070503070b010e0f18061801060e15040507090605090906150a09031e030909020c0c0a12020901050402070f02040908 81
    0x100c601d1309a9105854007001803050a004104601d4841c5400d00507240101d001c8081d40c4010742da491880c440c2c0c03081401404002c1d000123600d0360391500041803a0b0713030150041c4285004414081e5660840e004844142049001d020802c0e0500207501842650051038841030a03526440e840c072240e101942c103541a000030440480894500286c041c02021007131808400c40c50500340341d41c1c036000c0103008040056610b14544d0205840010a1600040043c251092100360000000d00402c1c4940c0089140903040d070070404500705201c0c10080890060340c0620980d50b5000007159002d0f01401600d011030720031303c034034109818800801580054007508103200a0b22017040c401080d000030710040e0006480b40b60500810203084150f5110009045807820354038000d680241446200707000d9401000d03404a40741030740700c900308108558a400500003503405034550000d04010740c40b24400703038010662880000b4440c181442180d82c0c0641003480e046900601d6800c21028050030300301030724000003d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 188933920 1250 188932670 188932703
    0x801150c2a0803030106030b010813020909030c0d030501050f0a050d0f020d080403060b010e1504092a0207030b0f060607060b0111061305070e0403021c03020c0102070c0819020319 79
    0x1c500440180c01000020b5441e0740c540344005041c0c0d00030702283c40c1009510004c0c00500800001041c1760700b6811174040740c0b030340d03100004103255004d10000e00c0100c1c85002c00c441d880a0b011303031115068070401da88446260301e50030244085411684601900012410854404500d60203200404503100a103030001400c1c0306c1e10386c909150400d030015a200c83c2c3d15104003000390382154029940900580300204c0f034000040c0c0300d0311240107a00c03c810219446410b010f0300c06184040c0403108840107662100c04a01200d130007541c0e102580803c6806510100c0402d0b001c0c00090b071500c2c490301c0001c002c0c52405000b44e40d248041c010701c84605041c040a0600160f500c90107126040c0b09020848992162800600342107103080c04940c080c02c0710705408030500010075030105014216103c0441040d10004807080101d00901c20003030000b616500c0481c40c0c108000f5454002003c030b03055101101d009541c0c0507000c4055414500c4001d40c9a48100f110819a0007a0204d03040d9650203907403001181401e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 188935170 1250 188933920 188933993
    0x3030f0c030204090f0504031409030f070303080f090714060d0b0406060806030114010b0313170309010204031202030c0705040c02070f030c0f060f08061e06070b01060801150c 77
    0x4160000d01090300400e041c080c2c0710091050700608251040140000c0c1000d40f00648074000030b4001e80504a0000341d881500d031010000c101c07442191030304079072165540b400c00605015050b60703140000d58010000c2003500c00000703400e00541d01a0f002103280c00040350100700030f0f540122940700c0500e850b4034107545150f613944110070041ca00740c0ca0b09a21880c14104150860304050f40ca04d54041c2194018403a104000d41a40d60024038036401c203600ca58a400c104405440c101c1c0c00c00100345000041004108064029000301e910400030f400d8400c09696041c1d840e4065503070b054181d640115810421807034250044a211011790058540c00d9458403501040b142007500107031142e80c0100c0c8100140442c0e002c1000041c0014a807401d1007159007c1e00401e588006403215104a6586a01d4120700d200350204400d0010010300040e5240c4481c50207000001c008d01c6800042280c1c540001358040803448005100c1030300d42c0c1ea541003d903e50740c84402950a48441d5042c0025040698103040e08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 188936420 1250 188935170 188935181
    0xc060318010c0e0a12030813060902030d11100b090718050a0303021e030a051b0c181b0301050d080309010213060203040305010c170103030e030a0507060f08060a1505030403030f 78
    0x11030350720f400340b040030141401011031442d0b010f811240722143d61400421380c000300c03451300886140742c084002e852600b1f10700043e01800c1c4020758103005041a8414107a0804c12447c4d0303103101e04003561210707203260f201101100c40c2030b084550003803a88000201600d10445400b0300080000384440c240b9615280800c13012040d030f0300300701d016034010822400c5140400d00500000303000c00c0e0046180c0108080010040d00450445e11201d411030040080020414400401400000351014400382d815080e00b402402094807081454501000345a0010a03884e045038165000a03040820f20031003a0303100c540c9a0f00041c03011005560a000b902d0341d0220728842132000b810150300844e00c0714210f0034101d003120500d1200c030b001e20500c640700c0c480008035020524116034050400000d01c82140300800c0c00c04c0f154120040490003103407000b20f0642d400980c00058540c0d00c1d61080c07407550b5420b041c4200042c40b40619803210040c10301c5010214400e030001c6600030310034a4041b4028900c541c1c650207079030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 188937670 1250 188936420 188936441
    0xd0603050f0c040e0c0312071106030c0d0b040c02191e14060906090705040207060b12011d2808130906060f02030702010e060d0b0631080c06031801 65
    0xc00c1421003080c14500f50140110000300d00001d40424140500000c3d1380300b046810010141c000800c0c1075045c02032542407034001940241080c2c5e940d140076411001d04e9400300e00f442285520f000d04a4046003481d1003481c0c01c04520380c0040c014400e03001d503040d5400e9600201100e03212500c1943d204c48084400c145401c02d8864400403000003082c9210b24142400104043e1840c0d1002c0c2c1007110b0aa000a5a20120f850540d0b0059640d5194106000034204c91054150004080300900b4034000055205414407503a403102a4019407003042e6980c0c81c1d19080030060124074500205203500804c41042c20002031241440b41d25100c4081d05040c1444990b83c4110280c50f61550700300500c1d41c10400fa059448190720107036150219950019200b0704460004500601c00414000c1e1039100d1548550290600240080e03110500503c0382d40c40604045551440001c613038400001003030140c10440142c7c0c01023400b50001c1104a001d124050700300800301d0075604030741202c040e62a1003c2c0304401c0302c0d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 188938920 1250 188937670 188937673
    0x1020c010e0102070506130305070308071b0f020913020f10030612080309060c040b1b070503010204080a0227010306180b0a0507020d090602030a080a0f0204180e01061404020d0603050f 81
    0x41c5407a0402038103085000380030890b8030008147c80b0300040c1d40305045030302c91645401c0c210450740350210200d801c8096580c85e0b610782c140f03422141040c8022114810302c5c181c0300b160350a44980d07800d0008103070b50b030507564025080a4042c81700221b07881c00d40580f1041840d02d04d030010b075040d076035015000503c8020b00265540780d000030520450040074030110394020764a0159524180c50040383c0752091181128040d00d0401c004014588080d05001040041c20010300940d10f494a80c0030580d2106048003040303110b00300c00c010342a51000d0b0a401c624030070350410310082d500e03882c5443e6070019161210117403d0f0308194900000004600a00190040300050000521807400290180c540b6030840031600c1071102e010002c000c000d07800022a0381c1d4114515143c82191103000c810381c00340018454020310b50b400481e0100b5440071541a040290302080d0051149808440f502e9007220ba003406000320385440c1080c01101c3e41000d4000f00703d5103a210000192540d66601ca05051540314001e00015 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 188940170 1250 188938920 188938927
    0x1060303050403050709020a0e012616080f01050a05011101020702190504050a090809210d02030a0f091206180b010b041706060d020d080d1814030c071701020c010e0102 74
    0x44c01030810025001c1d040440c0304501d80f5000b0000a0614a02c0c000c0d01810800c14840c440b0032050b880420407403c000030200c903c40c80c100030849154039000310501800050b903501c0022072500b000e920b914100c0d1000740942d5400f60503c00111464011545614480d40d0200700c1240140c03500d24601d03402030b5001c3d505103d02c0341404100f005885014002d000d031039003881c00c0040072890100890741c070440100c80e920f03c030980716244e8040e0f4892140c9000340c14001c1c11034604403e90040700408801c00705070342e0b1401c4010462000d0b2250f1019008410341c0c00d00881514000411a074010785902c030501d1401d0140c00a2603440e60700000003600700c0c004044000c2002c10401a6000c0003100d448440c002070103882c90700c00003095034110100d03c043d11510b5081c00e15000c1c426404100c43c81c5008481041c0056001404c644140360107000040b20030801964030b2101480004c410303211980b0105000c1d090b810310f4503105600300300c070401c205141950b01304102146c1050074410304041c0300b042c4001585 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 188941420 1250 188940170 188940173
    0x909030c0307150c0e01140c070b030a140115120f1d010606080109020c0303041118090f060703090b1302040605040e0c0a080c0901061404050909161509090e0c0301060303050403 78
    0x50f500c0309942d04c42401104c2500c04502ea801c103400410454072090215141d098102d076083c6800025444408240000403d00044554a401034008801d00c0c01c2c8000043c2d80e241c5114107403a0015902c80001000b003201019040c0b969081128020b01a020219a030300030380c64201481e1400c60741105250f9520300e400c015803908403552900500e58110110701b041400b8003055140e01c4020070007000c213561803003400400d40d50f03a919488003d01c03541500c4140d203030001a003640c0d0740500309002244c2c403c500005402c58403d004a402d410342c04250601b040d1182108580040c55100c01264802d031110000b00f01f64580e8410100452a4180188a8610400c0512182c503495411515464000c407814551603110901c000e411210140351140141024542a50b820b018a8100c554042e04803424400d20903800503524072410000c1e00403e014079540c4000022500783d8013000004181005401c1100c00306036030107003e0b144010390603074048034501b1000074212860b41c1c000f00e01284c4045020b00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 188942670 1250 188941420 188941463
    0x60305061224250f0e0103020c030a050c4e09040e0a02040e0309042427020a09060206070804030f0f090e010b1b0a0302061519030506060102010c02010501140909030c0307 75
    0x28417080203003021441d0141c50148251680f141c03031340c11402d000300010410320f041e80400c2114810150304103d04958008aaa94100e086010b51451042840040202d0f0361413660540a802c00b071420024505d0030031034006020150104074008092406001d9950b80544c42e14068013812500300300107540d84648a000f084215048000300071001e048030000ca540d0745a14524640c1600e5160401e405880080b1000940b078036441005009031500100d000b0a8807504240c0c0c80081d80d92a800f0b40d1003035030310710804030703401d98044130043c0000d00c0204c50358980714003c100140320a1017a1422510706034503040d1940f0801002c0e4000906081d0004101140f001c9460f20300100e000c000028048400e0580c40c000e569040c05040d8030300d00340c2a800203d5040c0d4420403654440383c125000c036400181e40b401c00545a400481d4154059424620030307002042c41031154038107840750383c24000743c101c514205000003044010104e0380d6900c4100402c020380d01041014000b80342c4904550391102c00d050300c202 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 188943920 1250 188942670 188942687
    0x3060405010e1209030303070e03030717070b0a0218040f0e030c06150a1508070302070203010c0206060f040b1309060216050a0c0b0f0313050c0406060305061224250f 73
    0xa000d0f60b54240304500e076507076012048a40000f803c0c03400064100c225400241180301c0d000e4020446402d20307130004030f504002c102a2221034017800c107401044c1c0e41e9484000a03840b030303001c242c01d10603510380d1500d290b86410317407008a02d844094000908803403078200103803840d800007800c60071300d034491800c001c2d21010391f07000340c1500700d0150f8641112504d48003000d482c2c804020a0071041c1700c07402000603e203900c40e506450100350010001c1c800301e00d510030044d403035600c182d500900a00d1042128195418540650210504003801540b00300713845401e00001444110000c440842c3c00300108440329003036209c05203400e805080948035401007440c0c80110004503500011810b20141f00056031010510152507110a481810308054030252400c2410480b00e0b10f04142c0c400d01d400c401142a65142d440281f080c8402e883c0800c202840b039142c590f540c0c00780090b412000800c0c40c07503800d4212a030700d0301c1c9400c103500011000ca1309003aa54544c00b102d4656001c0b4000078409002e0100c81540003918 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 188945170 1250 188943920 188943943
    0x509330f040302030f010b130c050f1c050c0a0c0609020f030a050303070809010614010c020301090b100311030c09070c0804050301090303020904050618011203140a091a030708040f08070203060405010e 88
    0x803c000c47c1d4020210b20034038a0341546001981c2e50f180c404492602a030101d800540050119503616502c200340c0d44484043d400800341030030300c0c0c02d000610000c4160100c3d00711501b42e85030480c00307000320341c1d0300e0300a0504500d04070707044401154400500e4504001c04010380d4400e86c040c5449140444004100400080c442c1413160b0501d6803c0001a00c400c081c201004000e20308407041910500100340034000b0843d004205560f01c1007080210070003403010005403071080c40700c0b040b2200240c04142c0e03180007441d09954007100c510007152a07640031b82d500071300307041c4a40c1d030f064101540c5400103800c4030b103500429000310b038000491503014034040c4103484d40524221034080c200d40d00400c501c00340e4001401580141b0540f454101c060600485907017420200190400399074513188070009190280da44103007142d0030b1402e0300d11541c2020940035030b071107019140d0304c041040d62261a00c080c0c5110f601c0c03003901c00060820099000d61414071010303102e18040c00010030030100546040c0d103418600450b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 188946420 1250 188945170 188945173
    0x5190503271507031b0b0a050c0702100e0f01051201260105070201020301060e120d030c09170708070b0f09060d0204031208011806080604020f0411030a15060509330f040302030f 78
    0x25990001b4140c0030b2064101e107072094001525a60085e00c0d0071a445900c4020358002216a01c0507072481d403200d4000c004410035204141c04080c10001545c1e2409a0f00d41400a405428014000c803650021001c1d8a070300b5004051007200c5a1041c45070841c6c03800d88080780180d400000501850346c101d4140348d01c040d41a00d1110304c030481c0c01407040e1142c1c11641c80c10101a140c0000b940f00c10710401c86500a803203402204035800b034158203000d40d00d2046100e40c5803d03001c2c8180018403250300005880c1214282c100c4145002012400c0040540c801c1e003504011507420b00c00440440c0c0a0205400075140641b01c1907165410004d200781c0217135200c1c1c075140045007065001e010072440420083c0d001507058840d01040c5015500050141c801108a071444001c04010083c540c0701035044550280048460400c002d81c44440854251162540f105e821200301000c18030708a0840340030f400c9190b001c030803581100543c00c0c00000217034041c0c5004001c0441c0810300b441903140c18072002810060140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 188947670 1250 188946420 188946467
    0x14010c0806060c030307080703061d09060c071a070315090203180d02030906181c1a0f04030815061803010509061b0f091c0519050327150703 62
    0x80003e9038a1000400072410003000c1c20104103a5802174000c4005080070b10421005807040c02c40700201c0c02e40c112030049940c4181e801003030b00a4805000c440c4141e4103c1c0c000d01c1600d6401c0ca08008148001e44024101651160355030203070042103034580e01510070410050794a0070302c00ca40300c0c42500031a29407407003038102800c500c02440e000403c2b03880c5071809440350354481c49150b154808136080d00800541040000c49816001e9a81c1104403c40178454010596034103003a80540880790b8003198100078500584002c10007281c02100c1c00c1da48900408442040482c0850104107150010382089240461180e2100c8003072034213004041d807018500e801001c051608410720100d540c842840995812000a407464a20035408102c400d01503001d0407900d44210403410780e02803007121207002d40d400c1c0034082100270300e8015141c004814a070401c0c0150304051000181881c3c0749a10070f5659410b08001c0b281032019100c29060100e8000c40801c4943c03282901d0601034003010203400c03191500307034120 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 188948920 1250 188947670 188947687
    0xa0507080f0709121502040b0304020a08010501030206030a09050102131701061d0a020c03072010020a02010c02040b01030b0315070f02060115030b0a092406031e050402010c14010c080606 82
    0x142440e011140b1a8141041309455418400050005030318901e1444e40001004105040030310000c6000b14801c4e035254201d00c0e07032a0365480c200c071000e0200951021081020407a0f114140d003212115502031400140361491100c000010701e61345a022409003525111b204120500c00e104500060003100500d9944a01d616500114014010034a048082d404036070265414030070019200784942c807551154030913400405070304249210b058250310841d17007560200d596610110b030002d4a43c2d8182c440e080744030b069a08000141183c2c5e11403e040642d152041c0703496a501b04016444518103c1c00c0c3d00982c1060040102540d020482040a40d4483d4004006012400d0b1210254440514001075076842c004005880e5440940c424107400741080750000000c1503d503100100784040b003201d10100d503a524820340507030b00281d408004841c440910024600e1030754000d140d129105240c0581e0951466035812400264804221110b039541d003003e180300741c0c10503902a0000c5085900d40e0425889 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 188950170 1250 188948920 188948927
    0x10050402030d1803024c140706050919080904050105010906171f09020a0e0a050d0602130317182d0d14030c15041110020c06030a0507080f07 62
    0x203602c0000c0c000c95034100f001144c400403400340343c8904040300c0701640da614000b811106c004018404d04103200119001186414002d80c80c2c405001c46943d621802d000c0783e07840b000f0060900812941d881e0264155000300035180d5110085c90510070302c401a00d5006400503c400c55005030020b074103000002005010054101c0f03642c102900b00d1800c12000c03555519070301e1441583c42144030b4035000c5028000304200700560050010040c1581d02d03003101840c0c00c000c00040354564824581c001e80c0c8503100c10f012071036680080200c3c00c02c0c2969000425aa40d45094dc4222800c101c0c080076140841d0741c180c40c0b21011082c1548003c210b07000c2003100300d18445442e03e40c0302d07100d490f0500c62084a0350400358a40400740084d054201410142800c14240e485403240d000100940103806051050701c000c00c0c24030552405250030180e50a1441044014046c40e503103c40115415403060400501080d541c3e58000c61082030686c801007440c0c10003001c050558070020707001c2100a8240410042c0c003960 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 188951420 1250 188950170 188950217
    0x915010302120a0501060f05011706010f0f050f04030605060901230f01020c030d0801090c020f100b030709020c100b0108130b070c0b0903040f0f030308040f060b0310050402030d 78
    0x804075440c0d0201095180c1c010f142241e4050028819400c0c4600010030700c085ca06a2000c0710801e0b285c101a003c443c1d2503008a00300e084400a01181c8255841030103540306080e286000c11407400d2131071504042e01d6003440144c20030f0b40100d0b01d564980c0e00304056802c2601025005140146908050011007041c806280040c0000c02c2d0040380e441184100c107070310070000c114511038081e040d05e00c80f14a0000050840c03000f40914580c0c01e00b042e041c070110510006141030704c00b00c02d10140460108090403d0042c1c001c50300115030511510001043c01c411510003894064047c4005140044261800105840703d0902c018140700b020002c0003480132042400118003648469244815600e500c0c0c2a10b10581844002c2c020040e904200700312048000001e0045c0d81006c194050182d80d9000b000c0019586130000400150000300401c1c0000c0400c02c040130080c2c400c1802058603d201400300345001c5d04c2142031902030352184c050109504060011420130091031601304140128141010340d803a9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 188952670 1250 188951420 188951423
    0x3030c0904180519240c020106080708101104170c04110301031109100b22050a0303120f06051302090a0608060618040902040221010608040b01170703020603070201090b09150103 78
    0x1300200f8001c1043c2c02150f84070b88480841c9044055170080007001c000d040d4502008007661809402088602d4000f078000102d40100f4002c05642d0b000500d890081c0030000a0600c4683c4140000301d00805480c040780c50f00319901c0c0c028688550b0807010402500c1d4a61141400390004000520100f0a02e0116a2503600156203021450b22059008181390f0300c2c0754403400c044800030907602e5607250905051580c0541001c5c460b41e42685610800200003450710000f40410310400920b01108400d4100300992218039100051040d50748002c502800c010f43d1116001e1980043c07500041d00e46105004068103541c0742403903980c50050040b0f082441340d040d14010541c1c0482381440e080d03803550404080c083d4098800d546505d1504040e28440186111031402c01254500102c1d40798402c400c820701c0350350030501c0c118480c1d1030101440036583c02030a6420081c042c03040d0210143c0c81d40300045001e08060b81c000101c0822500381044451005000045030b604417000f0424060302c242c3c581810340303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 188953920 1250 188952670 188952703
    0x501050d080a090b0a05040302040f020a05160507050312030f10050a12150f051911070b0619060810090b1018090c0306091a0a0b030a060803030c09041805 68
    0xe100890b020385840c2d60a50201c2d5207284d0008a55149981c007401800480784290307010700c2568980c410508c00e81c0140c520180001c3c0091120700002c0c0340c01d000d9194102c6c010f6080d90380d07043e180c0700824100341500c0301c8400c1d2030f903002003030100da001030100e0740740c0c01200e0762107111585090a0004102002d241308455140ca6940c4440050004010420b140c05030081c408200084410500101810048030101c1e00c4109010b0321400b90421802000800841c20301041d10306451640c034410700e9040900341c56045a42070b0004030041c80100444805070109032980612854a8400201040d4564010103403050034903c1c81e00268a9440c889040c10100d410315005600c010003240d6402d1615074000b81609042c044440303c059050340c03020041d00c43e00041400208202c5e9045402e04041c1940707a07070400c40249080080010940c081e5030000340406003c19040c3d950b0012030302c1c680056400d03035441000010b8900301c030303d4a4482d09034403420107588101b90503c141c07202070702c0c0c03400b0b4001e1000c0d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 188955170 1250 188953920 188953927
    0xa050d110102090d050c10020604080f0307050f0a030905072108030a020f07030905041416300516020f030a050f091201020304140c1c0f060c050705100501050d08 71
    0x14100079015541c803804007406184504600c0d060a0380d6801104030514021f200d442201c4914501c003140301880303241c000340304514103064036030341d21640d50008100e20100301040c40130b10b08009840008100150781070790082060900c5003803440c14040c5136880301e03e000b00d124010f400c5900b01e40c07203160aa00d42060380301da100d903144110b100203845608004068400001541801c01d43c2013419030b0283c0c1c0c000e413810016217616480c0c0049041040c1c1e03407a41a00000d004c86c2e03a1040c0720341e20b800d010744440040c0701608440e4640400b0225802d101c2c0005181c0c6903001c00554034000307a401780c40b541c9940b0090058007800c030042c903140d1190342c1e0104108a80003544a144881c02d84c100d841c54400584106c0b00141c180103003c0c000d40068508650b81864102c48000200d00000c10880d070701401080b640d034000a0304540f03811110304540c200c0b104c402071050000410502c0c0302d0509083ca55854040c2c1c2d8148070316009041c0001e210606207024070b048018080d580340e02540c114410b900c00381e00c41d40d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 188956420 1250 188955170 188955197
    0xa1805040212240702030901090e06031023090303060901030b0c120106030b0418050c040c030f0e060118060614030a0212090c01090608090a02060906120f10080a050d 73
    0x1c441503028001c00e030310807100c00c07900b5030a50f9244080c2d04405516220110703140c902e0b040361079102d00e001a0740051a10708050109006c0958401d030000c4005040300e906244074130840c401d994204030401c0058110207400200007182805840e0b000109001562461600b0b000003100d04d0018000581038000074000503504076088021194030000e071224216036581c1d600300c004e01030410042554000e6003080400c00300c80c00c14691400045900c030001e000700110303582c1031000030f020302080c0004154481c1e244008907030051017000b05400c903000c00f9040c2581000c0704102945070310009000001d01d4150100030880e886018010780409002041d40c3e07a03254010300c440a07001e800590742080d0341c01810701030b4440001412101c101820303214000f403566122401d03113616104542104854200b00444001498000002c040d4600c0040c0050b00380405000c203000d064200b15910f04201c9801c9060214804607114100b00908121000b4505429560350b401d8030361118003041d00c01d20400c1000c1c5e15 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 188957670 1250 188956420 188956429
    0x709060f050a090b2706121603080f090406090506041503080d020f0904050708090c030106030803062b0b0103020a0b070203030a2d020601150e01080705070203190602030a0b0a18050402 81
    0x25003540200b0741204d45c401004051107640d034055809a03c078a1050381161454480031600e99072201e80c1c0310320182c1051860b1504501c55001c13020880c2d07900000c21540f00e4035070705c0e03114034002750032241400070303d40c909042030200b242d00c005903410710280e00382070400c0050605e00c101c030102d01a105000d612080b54012916881c0030718041554082d061408001080f503110580340c1c0701c4c100e40011200f65201280a1600b02c40781c50102410780801040000c07200e040c03c08124001c20160381c40a60414000c1c02002901d800d1001c1c03c9411400d5000104107615010203008050004001072520b0400ca603170000303a507807140c08410014850f08056a05507000390760141846880d201a40c02c0390342000d000000d480395024000c001c0800007074444c6a90061140212080258043e141e030030880d1aa9001620703550003080080782c1c980300d001e200e0380c051035070281c103084036a11030364016860381001a02001940c0b44000001d00498044004102081a4009100c000265540c00013881c2d1194004103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 188958920 1250 188957670 188957689
    0x20105040e0c030406050115021b12061608091903030c032c1b0d1e0c060f030f0c020c0402090307030203030a180f050d120201020d0606020709060f050a090b 69
    0x40d940e103060008112400d40008000d40c455171156a0070000350783c0743c2050100c0d00d1714250601c00113a0000c6101b80c0144c41000100d102c240380105000e4850a4540b80e0501d0100102d490708010b0400000418001d5000760b2442c0c3c100c2c4043d40a8802e4019050000103800f4000f1006010161506014490709011703174030602c083c170440c0440806250303a0881c1d2005005400032241041d208200b0703140703480b07000e080d0b01052048000b480042132a805484100064002e14010406c5010340d0120400094003c00c681d0000e01880c1c89008019910160140489440d081a5241d15051203e070003c55a804240c6500d1030300100c4005854044900c0402e14010a940000350140710004034140788680161203010a4890001807092103519141d4903800480c1500c40c03190486040c0b510200040e003105100034400c0040d2000509052120118005490080c0d0000c40035811a007010f004420340d5000300d0024188030714107454070a1400303020070191070701c0f40b00720403c2565034205030303d082e59405203c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 188960170 1250 188958920 188958929
    0x11190207051e060715020903070504020304050309090405030c0319090b0a0e011b140606041104030305040506033102030f07050619030902101205060f03030d050405120c0102040906080a120c02010504 87
    0xf000405c0c0c00303490381000942c81301c01d02c50f10a1181002c00251898103000f220710899200d0003131070404041d2401d004500c0f8003d0b100b04d40a01043c0000c487c1001c00700054641215414850b20f10110040c0001d40305008c5030b00004040320042010b00e000c00e070001c2040380780c19401e10345500104180c081d440041102e4600003015803d05050080b100c140c0043c22500030741c4211820040414547d810b6541071286100c000c010800c184010481ea1030660b000e90707444000107540c41d10100780074036880c140842140303c800f42c01014806407800c0d4201040400c1c1c01201a03402000c2503030034040010124021000c80481000203480c821031614480c1d00481c0c04554041e068020030b211401b40506000040442c02c420f01d45828009081c600c1c02c040c213040c200d00c0c094091860800000c40c000c024100051090f0b950384603c540d0a4900c0040740000d12842420100040e203903400d1641000a4850650240381280d01111515003c101d40a498109150031810455290405c501c0141c4050140340c2c071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 188961420 1250 188960170 188960183
    0x105071e03020f0a1506050f0307031e080408010c030f1a060706150b0d0c1b020103091b080f0f01060608010e1506190f0c030e1306030611190207051e0607 68
    0x405000c100405d4520743c460050310206204068032081445186448c200c00c681d415403210500b04049000000c001c4090100f4100640840189844114440c0e0059109581503035507240c1145a59a25114404002d02d41000600c02c056405107540710085602000511801000400ca070400c04c607640700c0b40e440036a801584055558601c0104a0f076000708035000d115500302180c0088492040c100031002c60441061042c0d94845500110001c00d00320a040795001050001c02d10701e242d111074800d00802c182e1000303000d5011250030442c101140414107001580c105402030001c25000001d090550310140f4011016603203001410301450800b640e1560080000108808401c03c0601b04c407481e0400340d03c402c08117000ca42030840c0d0060420f0406800225580c07e121594644070070001000c2c410030030042881e03074072911201c04451140d00400241000007400e0205491940c00310084214280003400b00d061605010a1b640401d1a440e46403071380c480b21003072030300ba5207050680b0030140c1c00c101c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 188962670 1250 188961420 188961433
    0x4050406091e05060a1a0310021b06060a38071202060609040303021b100f0516050315150a0f03050105030f031c240906050105071e03020f 61
    0x10103100820396558103541c0020828902640c0d0120303010b880314925840401040f640e030351308148000401c10300d00700c1c4400101304003048000795010095200c0054003484010394a40c09688454003010b2440c0c007075440c070380014040002035594008102c0440d0000c19207a0301340e03102021085c8425000e540c9550240310703003550019000350a1805070107001d20401c40040700c000609801d982c2c03580111044c0d40c0c0010024002400244290003800c002081160030b00349035204001c01c113040842588203c1c00196890901d03601c20002401800d40080c0c0c1441504404a5585c100404512000301000c412140c9900c4409113910b66a103a4014030110b501640d40f02c0c3c0d1403103802000038244001d03040000e424240003141034034001c01c640c20050103031001140761400d46500c000885080000c540c0140f5900c00e2000004065045105c9607001c08401c403030340c69410088a03800b2074015801460400506000d01e10016180c421464800585281c240500c0449860200d140c0800884221550300848 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 188963920 1250 188962670 188962673
    0x4020c07060509030d080114010f050d06060513060507170708040512010b120105060303040611010e07080a0501050a0b01170411040c020703022412070c060c090320060a0302090609040504 82
    0x90041c00403104200c058401704480c0c20000c0702c00400070b01440c00400241c0302c90b21015806039a0004015001e4184079040c1104004032208491081c3c1c000e0020400000e81d0004112410944c034003d446182049410501d00380c8455400d825010405070fa41000007400009208201082e54010b01c002020580b200905595a60103019180c0c0168059039114480c00b48a24043c041c0c00c0c0b00d040c1c042c0c02142040e203400e0040766481403000c040d01c069540e620b21984030314070031302041028052410041000712040e24000382100c4000380030511441c54884680580da80c0a05100c01c1420641c5603240540c40350b05190444a04561180c1c1c2d01c1868a020f0750802600400e410003240e000301c8252a035200072040c4956950a03031a070702c401d0f080080002e00440f4012a1001c0e4200d2030307905d0140f83e8141240c0c0c501040794880f030707802e4000c598888030030001c1007046051805113007541d403044010140c1c1c16011840c0f0340500300d00c4505054000c507105030580c86d103100b9034102120045c02030000d41000d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 188965170 1250 188963920 188963927
    0x32205010213170f100c09090e0f0616090b090414190e010902281a03010f06030e1005060d0c180b03030a080609060f09100e09010b0607020f04020c0706 67
    0x107101e0301003003101101d44414050303030100f04940704a41003030141181c07100b0010f0706802006c2402a007011b0040008010505013120300c125152002da0b00300034440001400ea90130705d0040b0003080342070300d070032030700148011640d111003160200c44851400c0e41d120f000d404005805404103c402107200003050702000320500c4150349804e02000044010050508001c00c0c644c2610400d0a000e5003003455080441d8400300019142581c1484080a1990329030326282d00c1130348294001070a00030b107140840140012000040c0980081015080802201d004450629100ca160859000b0321a40c2d603c001103c0d0784502803c1c1d10501d5000e140d807030441780c8620403246000c0d51068401109850005240040c1c00c0000c100d4500c030301a82c0303442c40386a61b0042041a2070b2401000c60340c0000c18002c07a940300c1d4807450502401840b8044505001d6824140600c03c01d140c01030030522144c2c10310310741e8003039900c0d50030484503419010f60f0340082c401079000110b0301034851958041524461881c000031525030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 188966420 1250 188965170 188965207
    0x30403030204171015120803040c05060403060c172e171506040b06030a050601020703060e030d0b060f07110a030203030417010609060e011206111321080322050102 72
    0x104d00300c00c01c24140038600000016010f40541809002da000c81e40b0302059079003002d158001e20400b4070101c000d448501040454200768400c85405803980d8840341c04503007022503410945460242c0310014900340c03207983d8a900342c0714001740e03851000c1c0e000020044054440c200c051300c003001302d0306050301a0030301c1d40e0f0360b5101e0950403540d48096000440c01d0b51030300c2e004003041100018545415510340303010000c0100000303000360707040d4400c0100004c0081c81d60702400308403591a074044c6072a01000e0443c142520070610b070701c82c070584003084550003940c40a0b080e16500c64101131260124001c03480800d41100113504065814400400e0004000740004140500300b0b007048002d0100c150b64581c0801079a806000f0745100b0061301c001880800c0402500c1003070f21340035a0000c11704481092100403598494920801c5890300c58500303010383da40d02c519145882160f111481550709991f1119400d501002e043d56848050500503600b21803000d0980c0c854198000c0000c568504d14014014403004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 188967670 1250 188966420 188966443
    0x9060c1a0c091906020a03050d090f0b0115080c1b071d100e07020a0b0915040c0501021212010608040f1415010b09010e15071406040303110a0207050603040303020417 73
    0xf8420410000b401a40c1c14201003260300503001841c1c12002036800755407603086a00e90703a0001713035070b4007110010400740440b00c0c2041c1d000d0500b40209504041480050a0380031041d641809000400d00c0706a4201c40c00f02d40da041d451051180305200042841804c1c07913001e030300c21135260102d414072540754606860070501400000070740741150390b900c1c001e0412504044030720a02503001407862001041601303146660003c030302c0c42591081203401c50f001500c000e0903607003030360b455600d9035052040b5601003040210b440300e01c0321002c0c208402c41c110074a2a80d014042c100c10098104080f5040203103c0079001141d43d0b2104400c88102840d0b520280e0f80c005400a410521040c0030001820180810440e5414003041c0d543c4005035100e407043c0003800d4001c000c48130b0060b40810507100859818940100c042c0c0e45940a45080d05090400409031070102c00c000c1e038048000c0050b24040d40e0001051000c41707030180c590710b0b00c075a5181800d800074045c5902500303d2640e01b41d880504400b01050081044 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 188968920 1250 188967670 188967679
    0x7110f030712080718090c050c060403030906060b2b0209060c01020702040b06120a0507050c0d1701050a051806131803080f19020708160507090f050709060c1a0c09 72
    0x4d6036810012143d01d10f82800034580d540481d501030000c1e11840e00031000c0d504550030140c1c60020841c070f2240c94806c04413030507400a40e03111540c004001c80350281000800684840760700300440700c0c854034514030301c501303640d10340240c07a80092000d910a50141c03400410002c0070503032240a074100b00c034003039031003010102c0c4560310b0300714209802e140403004d40e1240c0c40c101554080300da891503983c07801400c01402902c02c0c08401d0119102d002c0c1c041281c6e602110440d503400c4a464000b0030101c0c82110107801051180c401c1400a110b0f54446590640540000109014107901c0b5540840c0c0c0c0841402404030955044c00c0b1044000d00ad004400f6030316a00c00c1e40c03080c016940e200c20102e0b81820641d54000081c01004801d084804142c01134150380e07026204c641e10b007201103400900c1921203810110b45640150300d04110000300340c4103c82959406540a11141c50b0044004021008900a60044c0200c2140e414148041c0a070071038403c3c074030200d941580782003585514242e40c000402247c1b19 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 188970170 1250 188968920 188968937
    0x41506050301021c0c02070302030313140405040201020a030f090b040e041109061c0503090307080d0801060c0c0e0c19030203090c04020403051b03030d0615140c0607110f030712 78
    0x9081c14404c8039044104503080a2038869044031000181c002d80d0540011031090540120160360f050008003070140303403054a51540c0785428842c2c3e141c0144464014411450101004003503600031411a48450f03151822480c2051700800980d0b00c4001504860b007a1200440c2c00304d0702585c528450b900950040e600c08007030030021010421104821038005801c40010740c0e1080d80d0414a01840120030720030410b603400c104440c404246400c485900190065201942d6550450f406c9010203001d840350b45800b410a00f45501d45404210061080c803034038081c00d00025400d61448415685081ea031154000b042c1558110000c020303400c01d694500c0da50180720384016039403909108a400b100c0e40900541000482c102808001202c500e00454150204210464001c03c8030b101c0d41018000e43c80301201c10080c956001060151290000e6580000800814913403050010300a03501c51010300d004039019401c442c0c0c0605005180d008900d903403101080b2001045010300d40085c02148503a82c5034038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 188971420 1250 188970170 188970179
    0x120501020904050f040f1401020714010504060b01090305120307030204030f050705031009111309121d01031e050712060e0f0c070218150d03080412020c03070923041506 74
    0x131018058a00814201922000f4400a40c1100f05400300c0201440014200340c0c2a0301d8809144d0300c07145c03580001e80d54550401080120f14400e112403a0310a20300310b083c040c116900d00e60f036000010103d00d000c3d000400080e00d001c2c03003030301164081e50f80080144c03e8015246001a40c030104c9009451090045ca102c0b004510158802c030a9143e80201e01c40100b000c40d5001e0104000700c5800303460882e0303214040480070520041406410000582d02c61861245c0c3e604600e506030041641c0c181054245820120403006a00000070380c02c254640c00641e90300c0300ca5043d00c02986d1409809601070612100054204000c5441d0344280e0000713940700340e10303560400300c180d03248100070000303501003410006c41e54140c101020b641c0d0b120420300821003c544032480003039250744002c50101c00042907881000100104c0044244d03500c540f0740020300703110712000d000a44421031805080b920f00d0b5034581c1404440c0000041c410318030040181000c0c28241420400b0303000701c1900c20300c0e1090341081da0016 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 188972670 1250 188971420 188971441
    0xa03120201020d20070b04170c0601030c1a0405040c090503010515030f010c0c15020d0203010f0519140f0303130f08120f09040b0f0406060807090807030803061912050102090405 78
    0x41450080040d841c0517450b03034441c1315134480640182c40d850702c00c07090710b0100d40b04600103000a40d0404003e100e550300d1464103504504198001c40380d0f1300f0004814082c920724040c203460036139900b124082400460f0210441f18440154013241d8150700704404d02c40c1401030200071031243c00c0b0903000e80d03141400080415090303505c0599841d000078040c6903048045a213102440008031481003015180ca11100060000d0342c00030703004543d40c100704550800c040d1901c440d40319115a0384107501130917140b070000160703c08102031580c10b009250400d80d00300d2703996080c000c807141000c0450340003880548400c1501401d442a0069051901c51075101c070040902c80401d44912024608444d85001400c2d414000500151440c00e03400c45800754005074666075502800700030b001c07540d0700ca0940c0c1c030341410010140d2001d64080181900708190070300201d0450022254000d1059864440000c02510950303c601040d81c804010700d5a42460b8030100725040d0010028600d0403035080c0b0890304c8546886 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 188973920 1250 188972670 188972711
    0x201110a11010212030c0304120c0501020f03061e030c09070c08180a080304030506130204090b040b0a050a0c0503010b070305040312020607120e03070210030f0c080109050c030c03150a03120201020d 87
    0x80c1b10f500000d000040c002038080500b40c460081d1490415004100d0b6510f00c2e007a07820403955a59181800310800180d0300b840c108101c0c100d5100300041410003d000b01103a00c031b03a115203038503020301035800000700e0381400b03450b940c800c050740032041c16030b1500d07110118480e00791500080e40c41100b4500d07002544020010a440070b0b40d4000c4041e20380c1782c03a000003901192241c0d2074200c0e005a00d0360124008190304076a22841140108007003a694a0310402c01c40403500000d219a601342d01d80301e14030008590181c1520306459500082c19039400e4182026180d40c000c0398802030041e0701c00e20210340c150b41c1c0070603014003900307441c6ca81070010f024002c00c2d2002d0b624a20030f510140c0c0e00c14070510001d0300c1c20805203000130429050020b48a0758180e40681510700c42d203926008a06003c1c01004031003800d206090b80000e81e89141429400c2524012103c0d10001e442c2010382094124602555a52280c0a00c01190300100d4040b0300c4003580c01c064080c0d000610182e62091401c50030324441110510007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 188975170 1250 188973920 188973931
    0x10e0106141603121d0c010504121113020307020307050c01020d170712020d1e0903091208090901060c060c08060a1509050306010303230909130201110a1101021203 72
    0x8a401d2400441e1000e0000b010840c094003042034680b410380b40c501241c0f1441c1c0704c1500001d48201c1c01000c5680799442e01c1d131044041810048104020003040843c0b540030440240d00030440c2c4503d811401c0020036825103080e072500914070000900c01080d40000060659034030030002c6d5010102041e005980354a1b102c070b070700c50210300e0700007030318464851955032203030720170176604040368450381d40c903e032004a07041150544600356441d41e802d0070b1030441d9941d041e00b001c60810240070f04c18040e54000d215018074428206460301d0b250802c0c3c104030013403003a603001002c0039000c5042981e6420000300310840c0485c0507103c0b24907227040d40500520860406104507000b03000c901559151820080320328040b9003084040001c9180c001c00d090f0340030b108881c0218000d503140301e500141446130028254200c421000441c10030402d0b520203072901c0d00040d6000602c1061441015070720300041c0d800c9545004440954042c4503000410051482c801c81100382080c2e0231074554080b1004174141d2440290350 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 188976420 1250 188975170 188975207
    0x6010f050307090506040e0d030b0f0a180903050c1c08010801090b060f0301020403300513050112020c0303040b0a06080a051507110d0c0b06090115030c02010b0a090203010e0106 78
    0x101800801c143d90083e40d0007900144c000140e4000141986050510804110001984844d15004185070030b540007911000101c0d40e25404a2425a02c1010b0f5011624503103070310f1791110040c500f4540500162004010074400f036800c0f204511706903100003503414141c030010664a2001107001d00c4140b0521003296405a000354258a4810422050012141031142d240d0f40801000c00024686005080320000c1004101c036041055540749580010901d000020002d05200700e02d4034060501481040b80d100382040200c6c2c031521000b21010f0302c1134500041c52440000140003c212884d60390034800c103034450f01005015104c01e80b190b21141c1040000d0116806400400020007031000034070340001080c00c01283c012080f004503418508595103081c0403491085176501480308020045510250407500c40f03045606204184a80921140080b02015600d01d2001c0f80e0500035400600c01c010010100454143d03600a2800070790310034016240c880342d20900000d0a540a2548625024807050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 188977670 1250 188976420 188976433
    0xa020115080606190b07030e100201020c071406040902030c0306010f0806060a0819060305060405010b1c06020c010b220e0c010e0d0f30110718020c100e06010f0503 72
    0x70300300296900c18213158008002540030020703c1020110050050754400d88541201d03a04200800c94141a490090815640104080034100401040f040181c4034078450b161040c1d80070101003107050007942c1000e10b03085c1c40001071041c8164000003a511400c4c090b642c0042c00360980000311101c01e016201c090304248180820030620b07020381c000c542d01c24103400c200071100c0700050703400c01a2101e6505c280e074141c0080c01071100f400400c2c001d40a0004040d905050440507003011065961550340002d402c090f070100d26040205000e41200f0303a400d800400902840456005400310580200c1c08418468645402c05110b801c0215241e40ca811058507805040c100641c2408a8880c203180c04480b0110112070003c0000c103c0614004003004034128140741200404402c002104015000000c0c03003080102000d04030710018500d001e0f10084881c0300c40600c81046048042c0c00b0703140f0410064082c0d0240e5071620308060f03010b180100402130454200b660394285950600301a07001d0300350560001c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 188978920 1250 188977670 188977681
    0x16050f0301020c010204060c0b0a0207030507020609211c0e030303010306020705100203010909060e0c090a020a0c052b08090c041505041806052412030c0a05030a0201150806 76
    0x609050411180680003500c1d02c0303511000542280e100740c2128006c1841103940100740100301f9100c552104400301d0451800e0715a403409822070040c420000d00c00d4200042c03064142e140e03819404c0c20888007070700c0c1c0159116500c0c00580c46122303249104440340e0301c07800c180e1302d01d0b44100046802c581c0081c020318950390030741e210704003c0d51002409690920030101c20b402c0403011f80c4004c5000b400491000a0f000c0a14600542960b202000103401a4802034400400f40d03126000c141d0819070b50000103a441c014000280c54003406140701411300c0c010100c507035200d404007404280c84003080c00c00903041441c000600381e0b600031003550180107a0384080e011a2a41c00e080c2e110013520012818840b580503503174800201a6006041800c0b090700542d0301c44010481c80c2d014480d004032140b2010000322214040080912a05040280c483c15203071209120b010024021200c40090a601303443c0e00803602e0400d982e82e6880a2442001503181424070000007400c400c1328825900201c0103407c098554 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 188980170 1250 188978920 188978929
    0xb0406051c03140a0207080724110f030406030213082b020309120a20060f030406060e04122d05090a050a080c03010b0a05030a03080a090c261605 64
    0x1c05108070700b8003c40b00301c03648103e44102d0160210260b80e90081148034107041e40d4900303102c030740d0b400f0000381144481e03040c91744444210100c80c1c3d82050324021010321011450185880d01190302c51495010004d0003050f04d684c590010020001c80d041d03081a5180c1c4c9940c01c80e96070ba040e44411482c01c503c05981b13000a44a42c0d801a80b114607881242d003481000d0001500100e00a0101005030f44180f000320104905c100c071400f105490704d68810716140800380414698464a01c0003000c220000002400700710140d44800d002d007454007541140303852b0a140504030b001061030600701103a6506030155018850700c000420b0202d442050b084002100f50050f6100d400030000c06620076075000d004a2607484482c2c403803005150701c400407d0000c40f180306141c215182c040405024002010092059407000201d420703480d0780c540752140d400d6a031501d1040041071000002080803201c0340d0009280300314502d50807007809014251648040143c203165035a0084145100a0710b900300c00e042104d85007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 188981420 1250 188980170 188980219
    0xf060b0415050a0c06061413060e0112020d120302091525110d080301090f1a010f0507060203010f0603060e04050c0103050c120405031e0f19030b0301050f09010b040605 74
    0x180c1e403c0c01301c1c1041e07256070b8090a90b2030340e410605080c241a040b486a9140071f50300c1a038294822041000003900b45035059150070780c1405001c0380703040000030903800c6448403011014070640265502180388035000000b40a580f08000d464480e145202c0c0d0309402d00c440c801120004402a0f038501402d105072854030783d0204801030f080c0d1302250702c000110401d0300d408000300f811520413500a40d6a40c1043c04c40130858070940c01d400d0242d407600159207140001d03d188201800000d003062450040c0d2900c2c21141841341503c0180001e00110000401070050400c0d04265000c60b2014041d0350780b0341e24031041000045601603c1d030307408010310034501e500940c006904204580c24007494030008442c4130824180c02c0d24203c2e0306901c001111141c4400c0354541d401185100d442041c80c10640030507502441c0a03650008520103030360aa0211805d00a03031210855000141c000e100310b01e40810460741105007210351300031355400c191050300380d480c11b48100400d441004001307164460702c1c100301c002d4200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 188982670 1250 188981420 188981437
    0x504060c03140d0504060f0e01090201090302131e1a0607030503060904030e04090302030408120903060406052203030c0f090b0a05030a020c01050112030f0206070509040504240f060b041505 83
    0x5004003c50080743d4918040c06120f44c1c020364003c108000750103280021103c01e019503001e0380c0d2500300c1c1440141e034854245000c60340c04946010301a8102d59a401c018429040c80c5094118803509a03021a1444d411140d080c032035079042c00b502c0c1030b654000d1140074402c40d00001d001910400008a091410001c1e080e0014000d1608901c0b441c0e0032400f0504035250200c095026034030101d01007012510410083c4101d0b050301031420b090010170000300c1d41e1940050700003045143c403003000070359200c3c8410180d00750b4a810500c40500c041e003400d002c3d000b866951030071400504542013040800b03002d8061340d801c66210a52040ca4100a85000c403010381000d020311a849400b0408118041024003034540a840b60510300841c10b00603180260007501a01e00542c00d42d0010f40401190640100999400c50002d85022610b981d0b1403400f44400d06481d00c5540d0100d8101303500801300d6039907030301c02150310346c0300e0504018650710340141c4d2483d8000d91240308003411f4180d032004903051107400074040c0b41 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 188983920 1250 188982670 188982707
    0x1305040917030705040e1506030f1503030d0f050702010603080a030207060b190e07020c030d08090c03060108070f0501020a02030309062209020a0f030504050c01050a11031611010504060c03 83
    0x200905070304428140d00550320440003640104040c003080c105000070a0b00200040581d40540c41a000440c00c0e80c0002000842506480c2001500003400f841340c54034407000040c1600c2d07940c03801119210044c062100e1280c000c0e0300e8600001c000030b005100c0c820550303403c884241d09245c10104220301952146004507003582d04c90300d03080d034282c503502025404c3c04c068602c940280c0317090503c0782c102c0010040104003113622901000303010f900c000c02c0300380348900c8901d03021500d82c0c0d50008552a01000c40180e540512600000062054000c100c00c401e458a146040000f02e649400490307950b000108040c1d41600b007003020b04261307e03200b001401c1001d001c90316a0106c7c80426034071001805135510241006800203030904110398060045050300e45981010840c0342003070b0301c40550300d02c40c0002850511000044081c401c9024800c10307090903020b0388c201c030350395034000c0f030101224001401c040b914461403101c0221998000c00584050b0713003250303490007488403490700d00300c0e5450b0881c00e000b00c54 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 188985170 1250 188983920 188983943
    0x309050709022109030414060a09030206070303020408030706050a05010b120c090111030a0f0f0306080c150c0106140a060906051905160b1e07200114040b1b13050409 73
    0xfa5000780002803080415201564031545003880e0184050035030703104544188000c011854560780c204020406403501901c0c0c450703c9100c2d40c40d09038001e111b00e0300902c0c00c0340700101c1c2e00c034108060b03a0080d602c00d00042c00140300a980c0d42c0141c0342a8010310070603004010320301c000120a01e00400240c44070800c1450320850101c803d07040e081c00c550060700564001416a000032441940218180700a400c61780740801c1014508090103490314011042c0620600e0305405031000c5c03904000a9640d082c1904008108140e80c5e40040e0300190300d00d101c164010720189a0028025008404500854000b80c03140d62030700a44030109141c10044201440c1400300c10300001c03c00e1101141080700a41c495090404a42048000d400c04640c144441c4541242c0580400c80c0c415031018519a80021680c84040c000d0740d40c2c01d0300383c00350007030030385403c02400c8100401043c810035040913802840c1e500407010b0451009400345115200d42c6c0490300c8840110581005607003055030001001c0b80c001c10b50000e5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 188986420 1250 188985170 188985217
    0x3030203040c051005040303020705060315060d24080c0603060d12090902071208160e0f0a171f09020a030209090109060e1605060408060c0f16030507030e01030905070902 75
    0x281c0740801320004005400460103004142e0100001d00150a0032101e99045181848044102640c0070300b102740283c40104049113284095085603240c5c03840009041038555090406141e40b451510404a45128041c1e1010650030001c2c2201e0285a0181c4038043c0c21840f9112075010302c018a4141c1c04000810500007010641440a403049501c601c022a412140c5c0d500024140c1c5409891096030091500d0002061a0880342480c0c10740310a5489018003001c0200194140d0143e40c0160408100505c0c1c0d550601c20220f5400001b14461444050000900c40c9003401c480350744d00020740000280c0402d0000d460000b0659510010340b000104072410a5035920003a81e0000c100802140d02c6982502408c3d030001e084407000c0d1400b5560b090a1a180000301983e940c0d026003d810341ea00300042d445015220030040710010f4a203d003614010002e2407800403d035074052503040c0c0008201c0f50361a80250b2182c01032001c100d0b0490010f209280c100310248009501c8684a8444500310203021070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 188987670 1250 188986420 188986429
    0x903020d061e020c0a20010801091d031b06130b150f060a020f0d020a0b130309030f150b1008150301150f0302090f06130c020a08041410020304080a03030203040c05 72
    0xc513201c040d10440855203040c0040544034101203d44078800c0b4034010850343c4c003042c500d044884600002c540520043c12207201071500e41c010004c2400001040392009001802e00d0440c0d40c11113003105c0081d900c01c052000090b03058240140f0541d82040850702031101c14015956126000f4600c0c50400740c400001220380e03100d10311034000750f00403042071a2200e800748004c01c05007110340007820195119030345104009000a1030401c800c010051900141441105180044c5900c010f14002804203403c01d0300d00810400b500e0a121030600141c0c00e090708092044001c8608291a40c0007142c48000c1e0b100a103c440e504800e8066603035020002c442d50004154500605203004040440c1e800c600500c2600c610090098016079424400d0141507190520038040e450300580002035031640e0000b00724184100c07180040c08550010401280082134441c015036085821214524a54042c400a81c0c80707006a1007591480d8100b503c1510100e4026002103a1181c031a080030409030b41c5807800035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 188988920 1250 188987670 188987677
    0x1b0906141903060e07121a180312040804080d020312010911040e060f03060a0c021b09070507050a0c060f02010c090e0109090f0602191b02060406030207050102090406081c0903020d061e02 82
    0x984800c0411280d07100d82008408110303410516034440b282c691023071030402c00c1d541e102e0421501640554040040c06202c20305042e140a090628140c858205150000035500e0f00305415440c05940030300000600c1c2400c51260740c004803440c0503824106841c011049104c69402000c02d41c002100c010b16050382d56003070100920540762050002803070f00d030110000f841e002e49580410300c2c1815055440c1441c0d030b0f5088001da40b00101d4036103a03079140c2c00f9151035428403408440003001c0701034201d8003041d919000301c010038002034298000c200d82c4000c200100d858002910030040c0c050707001c9005201415107a0041e01c0050300826014445e448240d4604040780d100c601d035151340c2c800d15004e81c10b609600469900d080c11902074107407120840b03a000500710b803260348a900281580000c0304002c2200039019a6a418401001084142e81e02c015007915a1480007502030307076400201030a80d003140240b400c201901e80240c1844904801a943d990090070000710726911700710080400e050119050005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 188990170 1250 188988920 188988923
    0x2070c0e010627090c021009050a120f1e0c0803160e19120f060911091e010b090609031209100804020102060703091b0906141903060e0712 61
    0x140012585019001081107400d03480d403d83c0740d206844091540c8182c03072602410b982c900e00300000d420084910992825000e07021115115040000c0d0a00b8080c01041e4001d040340607010740c02060a509504803401d961400700c9001003840c1c40f400e405564041c0b4161507401000f82407401d00214035448208203600102d500c3c4030252144201000350075441a990451298243c804110b81c1960200b01040151180600300c4140740f12260501444003107455002d489230410000c10005030315003000d0f441c103003580d0112806a1101000725034500e818005a01d000ea1270140c001555908042d68000140d110500f001d40c010030038040300031603a805005035100811680b040940d070300154018005114000c10088c42403180d940d00700300150341c002c901c1950207d010310740001c04661030303e49060180d1420008088040d926603010680320f180394008000c0d07130166100410000c0c604001c020011104004001000307196510400010b4010b4002152044e1190156810280c0ba141c01c0f08001804850 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 188991420 1250 188990170 188990189
    0xb01170705030f221110021f0c030b060f0918091e01060306020c100c020d2a05030c031308060c120903040902210702010605060f210a090b15010815010302070c 70
    0x24081a14140b00e5448151b10540054001e10402d242c5445039100503c080203070f515125040340140398401d074014903440c0360091955032140a003070b00c4082150400aa4640900102076881c205003d1100076540b1030310005005000ca44080d0000411090240c04607845940d00d801340840000d1141c0050704039205150700601c2e07580c4855a01c2000e840741c17003c014056401c140322017204254400c416500c800754215201000c1030415404a40c0b803503060030040c01a00020402e41d9000d07002000400b9540182c801624589d610303000d8242d259003081d44c20a00c4131000300502e155121380040d90b6640414007505807030600e0781e03400c09501640d028403030b43d110640b000140da00400341d170300c1201d54200d20f1520003001154100b2000c503c40f4491a14000140e50340401ca500c0da04074203490000e10a07413100d40700c20183c1042d4112401a20412404490154280f00041d4423071040644803c0384120581d100304c401c0d00c0d60740b850380701c12115a41c0380f8100768080180130049101040640010f202c41c0300e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 188992670 1250 188991420 188991443
    0xf02030a0e070b0a021209130e06180708070509041406191b0822050307060605030706020a03021510081c02010c0c05030d0c0e130b01170705030f22 65
    0x1c4400d040c4005a001200e86100034010303601580d90014035102d10a00184146d6940c11000000a170900f0300f0301030030441c41c0d003402540701c0450400328491340035030701218415006101c0d050202c1d895400d2402911b1155000c80ca0822442c580344c5100c680083c0a484003400c40500c0c2d400c070307034248901107a54070418010414001200100c52081e000c079000d220401c02e2095180c2c400003014200003802e0001284018400c9c000591408080300903050340c054205e9940c0c64043ca03089001d80400d1044920900170311a002810748d00100c0d03440d507255450b9024242d48541001c0300c0b0000d50740034101c0d141d442100b0700041841c0c00100300180d841100c22120110400e0b0085000b070941e144e2440800c200000030a5034400520000151802000302e92000300d001d4034010300464015031240342107039000071240310700fa02d6988282c0c4040d1068100b1f91b2441084400007000707007280c03c010381e48500004d00410000c2d103c00f200044468220803401c3c0c0030713030300141406d10800001001c00c0d0252481440e05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 188993920 1250 188992670 188992691
    0x11106040506091902030a0209070203040f060e040b040b0105070b04060f0911040501080f0c040509150c0408070b0703080c0c07170f1c05030c0a0e0406090c020d080906190f02030a 79
    0x400040b450018064019403c1c0c4c0c0741c9601203502c42c808004d0003070042d02e0782c2010800e0140284192409880320318010f1104958802d80181549203c1c04040d001e6440e001d00d5400505203409402c010020603107580346030920f503688000c13040e0030080050724a2079680b00c503004501003d00500c11028001c11444203400000001c1204607001a4031000199002a621001962002c1810305c4406411a00001c0a540b41c00d201c0d0300700f03902050000b40400c000d6041080d0031255a000c2e002340c40d5100308481c000c94540400c0c0c64907208404000d4040b0b02d2000000380743c040340000410710041903500b500c00d40c507590040d008075a16a50001003c9811004207003c0ca0317401040180da100c20002c00ca0212000340800181052201501c820a0b001c800071340a0034090242581241c1c24201510030018240c4e118203120007400503440f418018014402c040039090300c2490034030301401c0700c90040c2c041620b43e02c03000314035000c0e5000d11090b401d480715881c0c88001150b01c0607500c103000d00d050115110080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 188995170 1250 188993920 188993923
    0x10c080415090512160f0c0303090e0112020f010c0b01091e0209060901200f060a0c0e010f1b1401020403030f08040803040308060a0e04110f22020901110604050609 72
    0x50034922181c0340c9000080b2011400c0010020408076a000030356560b1072079100355540c0d01c0d072242405004440d600b1408020000b0f40d40c0c0800071a8040c0d921170950a8030b901204003107610038403271030302036070688800c0001618162114042e0b1050505110118903134680c0c9401505500360301007214180d540080707101583c1001c0b0440308007814007404500c0c000400001410a0040440030390400c03207a40b440c10404ae520003031008440c15604c0403581c40b0000300000541e501c40454040031114140309c0202c0f8454000c41002140d240140c6585144c000b0303e5408071950114000482000c074503900f201004a030b40c0e20300c4000031003000000903a0310703819400d0107066074000d4400041085001000c01c0089840390099a8110350f01d4500b40300c1390345407400002e464800c03e402c81c0b00c07244840d00602041140e400b114211911050303c81c00d0400309104100864101c0342c0845000390b4152922540001c40309500070004420141071010b102c0d0012110315140030340486040b81d039940040c0501800c3c000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 188996420 1250 188995170 188995193
    0x303090b0a050c010e07140111030301170a0c08030a02010b041b030e121602030c0108060603040609061d0c09010608010609030314131e0b0421050a022805040207111302040503010c0804 81
    0x1f03082c01d00b00029011100ca1660b20b10051181c2900300c2140103428514013800c1c0b0079010003540102800d0012610b83c150203440c0d503c04141003026628100442890341824040c0d6044240140c000074040c0f140d003a0164003602e100c801d4034130103000e04001e0b41034005a0384064404184000189610b0b1030180c814185090302e20745c0303c3c81c14031400038100b041c03540e070310740889600c02d90091001c104c0101c5860309501510503c1240c11112404807085076482d080043c2ca208a024101d03507242031643c1ea40c400b039844070001e010344400a44074150a0010900a5002000000c405500580380401111070f941c0907844581144014a86100505004a5910400c00c0282074510703c410718052071b000600030310303102c003011014141542100032410b201c414409140c810b80c02a0050820019110044440900a09504440d4070700841e003c034982c1000d10079101099407000d07603030190840044c00c00000d071496541d8401401e07002c00001c81d56031000e010711041c000003a00c81c4c1c0085d0400340b40c0780c0c92846 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 188997670 1250 188996420 188996459
    0x90f080d1202030603030712020c0604090e010b0405151c0203120a02060708010510030e03210711030702131d07030303050117010207030c08160f0c1703040303090b0a050c010e07 78
    0x2c1c014020b0100790780e404011150040d5005245040d1500055016401c040580300caa03540000086000200e03483c05030080b540d101b4661000300684410f000800044607800d845194600042807010083c41c2420400e04901d24844106032a00544035400603181410780c400002c82a8004509442d100c2d4041185c1c5070405950b040c40c0e520b0358100008240c03101c2c04034540c0400c168a035480b540b08801c0520440303d090400c030313403142d034090341240340005010000d07109140010000c10000c0300540001c0103858800d0780c028681104454040d002401411032a10310005800041403205a180c2e03003040305100461090b1400b2409600d405a0310050b02440181d8445a9004000200c0002d40c002c2401030204d0b40706909546038817001c0d546143c8540006d500802100003587c0315818405000d0002044070211840301c00400f2009102d540c6a008500c002030200b10a070600303102a02055000d00b003038517054a031030390505a4400c805400c2d03d084820788662904503240611030b45a12842d00700340391 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 188998920 1250 188997670 188997707
    0x10b0301060608070203090904060e0d09030510110910091e090b0111150711010f06030c050607020a060e06070b1612020a09090b030a051222051f090f080d 68
    0x13480c2045000e5141e10440e00918800c691080000c1c0c208a103a90055545060090440c0c44000302120040e00c0d106660009840501c119410220144201c0c0580d89420641c039140d00c0c2040c11038030600101c1c08611034610103003c40e468010800021191481d480d800c200016403a256240001280c21160b40c21f80030350401032400c41070b800a15000500d040d8400340422444422394030b06d40d0444400020381803442807542001ca0801400345203411102c00d8a010300d49102c8a5a922004c1056a2244140094018140440401950b40191402c160406014261030300c2c095247e81c0350300c50600c04541078917000c0d11070b20310140b003243e006809074244130001d0f504600c2d095030711402624a43c4144100242203031141c5424000303840500c40c1001140c1e0003011107204814404400300030760810840d10550300f6041c05d03420449200c0d40c02000480e50301411010030701c0381e8440309904c003440c0c1c40c16240510802001c00190301d607890907180000c0241d080030f0f00080c408440014006d0a0f404140c00342c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 189000170 1250 188998920 188998937
    0x904090b160f200f0601080109031403100308030a0605040501150e031b040c02120c01020316030902130f180308011a040503060723030901020d060819030e13050108010b03010606 78
    0x1ea42000300c000707a01040412500043d10004100c51624404d08040500380c05640000200f400c03054001076036070391081d10f45e40c00e03800f140385542e201800111181c20780410705070010000319641d10002e5410604100b008240706440e030004c50300340c4400f07a00c0003a00e544440b0207142880c0d404039904007075201c110301030720204c0103482c9808002200d450105214560f035040072244103008004511148940711445038403030700075030640e500030340003103886646551175011894040d9210313106500344a03034000c140e1034801c080343e03401d1b40c001c03c0c4600050b800b017699003082521909080d019001598403e0ba40d040142d81002049001d21410141c05074150038180402e00c070540d40072503800e074441c80038500b040005d060b14050482c103070f000003080002c02c00300005201c0189810b400801c07486c040c03804240720243d610030a9550b5401c4890000709a0308010741c05000081c89856850440c03a401000c02200142102500044403005c2c0d1010780960f56680c51004241402c1c003442c1c0007402070b420301c801c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 189001420 1250 189000170 189000197
    0x40509060105070b04060209061c0b100504080d0e010905030f0d0306090b03060114060906030106081b0f18010302040b16021509010c030c08070b09030903101a0d05030904090b16 78
    0x801884c083e00007400150040342351a685e4031488140c0e440900d60b0100700518125410180004042101c8944e00600006442d40d054600500444044903008002400b9090f82c2c02070441320303603500d00c0b591410840c90100010b205e40d010040072220460002c040d2190115180010b41101c4041d40044002403c0004961040e50042190f0f07044a004088806036601c2540c0061103d10480650f141e1291011001040c0594005030b69441000d20010b11180d440255480340918012800603941150040007510480e0001c0090b107070010006040140c100b64480784584c1c3c09800c181841b00305040700001c0042985012035016100e52440040302d0300c4c0c40a00c10000307003200c0010501800b8046075104101c1089251000c986800d900480e0102503414150503054481d07000e24400d510070b20904090002e03083d9640300b403088002009801c1c980300d084003400d00855100810058030640001d03c818007094035280204c031901c0e4400d54590036546000c0451086899006640700c0811070560202d80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 189002670 1250 189001420 189001433
    0xa060e0c0906160f14060708130609022202180d03141e04030308010501021b0f010c061409010203011a0a020303070c05342c07091a04050906010507 65
    0x38540381c015141c0c0766645032015501c001c1614088002040c62070110150001d0042c15160100d8140c17070038003a108030b91140d4004592804050f42e4807030039041002000d100043c5030303034015500548041e040c00b900c559660b03440000d140203415a241c0b0141c00045000d8450303174042c0900300c81c00d42240d0280310420745d510002e00c40705041c201c01302c02002c006036030842d40b01c2440c00000c1421149021684d42c5445c3e1400400400d0301b0f1250038054820f412000311100c041e00408000204050002111034000b6001120403c0384200c0a5034241d0761006491019050324403040d2042401200150fa603502d007031001105807110100079041c420003030044a144603400300880b031f00310f2510300e041026030000741006400c0036508240501006980280442d0f01868500505c28010080d1252004190340e1103000130050801c51030403000b4902c0600a241d01d00d40901c1c410707045601842d00340061621510460a85c19a08102c2030b521107020504010901d4000d8200d90700130020303c4c1081c10f014481d038546 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 189003920 1250 189002670 189002677
    0xd05190e09180c19081504080f1e04080d0e0105070f031b02090a0603021008010b04050d08091c0309081207060c020a0b01140a0f060c020d0215040f030203010f0603050d05220e0a060e0c 81
    0x44a1b80c246c0040c80e110203018070f02b801021180130070740c45a0750720f40e1490402c0d903600d55a001c000201d00c610f90484255030045c0252040ea58005829100043c0b244d9021170b4806d881180449030020084c4000000d17880f5940d10320f214840701240000c0c418190f004100703890707200c400c808003000300c1400140283c84034101503404840059805c0c2d6074290103440c241d00b8034010115069085504201440944c564000c1407140e840d0007511540b0b2696118004180c89007101400300c1a010700800c091030000300d56600500240c65107205a03000c2c070b481aa01c101c0484402c0e404012800c56548092000b490000d200500034420030001d84e11140c036005000d4003440101402921800207400c3d54800c0d5110008854220524207059a6980d034a4240c0c2c000c0c80c00842c00164029807030800395900500c080d2040f58103a035000350050590400b0701100300d606501c84000f6102580c16514070b03007110000207801d8130144c803140544150610b0805940d000301c94145d4410811008090184800011158200c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 189005170 1250 189003920 189003937
    0x190c0512040309030206121506040506091302120103030504140612040b060a030b01060903031101110906071502040b03040b1501120213080d05190e09180c1908150408 73
    0x15846640c4504050320b0043c0d013070340069005800000e120f80103d860f070340142c0c41800700b9907040d020319180c041841182d0040c1c1c01099000307407080040035444d140c07401188138100c4840401610f846a80030161014440030b0340704501141d004502400f025030300240c65070f040030040e0ba0301800d0165140790050000c80141000d4040d507100d4010a00c1510f4050f445009160030000e114010b5a69000007408100f09110070380020f8403600c4041c03034608060040607500320b0821210307810442920104102d42e400b150040b91540c000f9020066064458005400200800e400c031507228542410300d254684401049003008009807100c841081ea0031090082005050000040c1c0350700220648090916403078200507010320400c02e0003502254084014410401d20000c2d01005003025003054607aa20380484142c0d00c2001c0000062240051048503603010f215202180e95490298020601c40901d00040040c0f40d0b2210105000c000c2003003010307807264100f800c9039414514243d29602164040d0401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 189006420 1250 189005170 189005197
    0xd020904050c03070620031305090919061e020903070905070e04090503030103050d090e01120c150806040501080d05090d021203211008100e030d0f05190c05 69
    0x8a02030101c20000801d52100140c21242c40e141c480001419130b2a0310114003d400403e4a501b551840b40842510304901c0089502603600c0d0034001000704da440700a192443c940b0038108000c44104000f00405a50f1b4000c40c0c0004003202881080010480500400c0c0c15140c0100401e40181e240000d003102104c084e02000212074481c03010440e4990281380c0301651140c14181c0c0e0200388000817005604a9124034222680c84044890036941e07420b10b88540b03040102808010410700f20480c00f49542d240c460003082e00442d4880c3d040c903464054011181000803400130400c400d80c1818030403107000d0540c0c82d0040004030000702004001c1d118010300399005601e50b03500c03001150bc0354035000d2080300145082d2030b114040c0101040341c1424400740c8014000c0c82c1c001058144e107181010b5419500d134a0701602400d59505041c0003d808113040e42e0900344801c210101035003040d4410b590400c100020041150b0400c64041070b00650845100342d2840e1804001c20321494000b421524000c81c11038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 189007670 1250 189006420 189006439
    0xf0d12141323040902090c0a02031b010f0c03020313031803050d1205100302060304060917030a060305071d040210020106030506100302030f060108030a030e01090203010c0e030d08060d02 82
    0x210301640c0c502440441450580c40741002150b98191040e02c1c03440101041200c11140c0240c00c200020795954850194100c20100c010803d005039440061842c0c90b80c0340120303450685061f6080340701e813076419800c41569650703070807054a1059601610300d50144074541035045060004040541c41074501c402000d201401c03015402c4c18002c1c0c0c140382c2c010350b0800d00380c0d180841c06c030001900c0704001211400d8814900760001d140580c0591205040d00e07000340c46103040d030b607940c0d5440c0020440c0031310030751b0140b5403003c0380340040002c07000652040f48855404151a45580b0704540f806a42d034000c07100c911481b0b41c041c0e02800d941c8040c00d9015170100c40c91014400d82d00d01c180d005003035541019007280564001c10038411507641c0d2000880e44280c0840d407100c07030510300c00e940b250001c1c040d046517504104801c04206100e60018086440c00300c00024a0008940c00a0700f1600522203500c0811507550408145107014800c40846c45140e040240c15468a00700181c07003000e100034028072540464 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 189008920 1250 189007670 189007697
    0x10c0203070f0f0f0803030415050402130c0f030c0e090703150f140f0102010c0f080601021501030605090105010e04150203071403040f140c030a0609210504050f0d12 73
    0x81000d00001c140250b038414695481e41c00c1c070300d000541d034001c88081a2002000081034603001044070322030f94021100c00042e0041c0c1e10b605002d0200600142c1c0d0110b6500c02d88182980079119076201c1d40c0e4175498044000c024078a02609580103440307003000f0b11081d8402c400c1076491f0480d413240c0c071051515002458040c41c04a007141c1080725001800452041540882d1071030050b0910400c65404554074031060f0000401203098942d102203860001c0d004502070600300340103881d8244c1003601401030781c040600c6444e80d442a074002760300c01d450705503c0c0c2e4244151104217104090240401904040e00341c58281c032000c00391111460070500c803075070000c000381441340302d8076114803d582220b6032140d42e4101030429181d00e8070a00310589240751601c0414a14000008100d40b400f500980907258443c3d81c0e803034041c010003040600f5660b400800d502c071041813400071803500d0310181d00d465198403a401e01d014400404807003034038a4010000c808030000071400c9000d00f95503540d05480d080f444bc04e003d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 189010170 1250 189008920 189008923
    0x6091b01080613020c0d0306030501061418190e01051609080307080706060f060e0306060121021602040c02031801020c01121503080a170c0915030903070534030c05010c0203 76
    0x50100100281c0035040d5000c04041c1c0c50b07040326027164000c1c070081c0006601c0b84244510b0840a410090340318008030320000500c100401d08a600c110700b150002582d408000c145010f8130400d85100300243d540d1010000d400c403451102e0a014001441c0c00d040c0c0724184049103903a44140f581c054496000800c060301000b80d00d40150020700f00304c04a00d856140d4403880a05011807500d6050320a000380303400030351513520400080c00007062410303555001340c00c0040c00034001d41c014056040301c0e400c44000b140160b12103000380203420081c0d034011542c0f141c4022118042c0340030404028115008030600910f03d030391020020140305240e5400180c03000030788150720042c4003958001040003c0c00302d0704244c065048005603226540c64a6480795640d1f500e0260200d5125440e013071680f00d9010352038030800c802c4000165900820f25012030389002e1b2140c6545140c8810380034403000307414958061428241d01448210002090803441c03540c4a13013503555140a4408074050107042100b440405801d5560 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 189011420 1250 189010170 189010177
    0x20105070803150a12061d120a020c090c070203190f080c011503051b0301050c071b0e01080303060f0f0a03020f06040506120a0509120a0305071101050906091b0108061302 75
    0x2880152103640d030b02803a03182c20245190586e111031030840a2a1030500701106d890221030b414010705140203007450320301c11035044921a5001c5124400404030b15880d003200d41d5024240d0b4400342500c0c6c1d0014810140b03099164280b4021071161040e4040004040016a101c0694404122a101c46c202801503004041000707011400c500d4110f000010b0001c007190179008001a80011603142c0c0b501420b00d420703503009aa0401861100b007011801261013103130741e600300c8880c03400000c00c107a6541041507034a81c13007a08546882e41002003407003d58a07103400580d00700f81c02a518003103061540d00024401c202184806800f0f401810100d61103991404211000782c400100002c0c0c41d0020001c045a507007404a941e915410305d800e011951310100041c21103c50f0104200c0f003803802a695008070080d000c05490001481068003c80481c50710030702407144103082000c0100043c0c039040c400e0130f00e40440c009401c46244403080c900203240e41c0c0021a103602c88010303529441c24041d01050702e0020711 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 189012670 1250 189011420 189011461
    0x2040f0b130902240304021207081c0e0406030221030c120309010507090f090b01050f0a0c0b0a2f07080c0f0601050105030c0301050f01020c1509040e060103020105070803 75
    0x420720640c844030003107540c091401103000f5100751035004e24013034070f000c030400c46081400504002480014014602410f16a02c0c240303480c4c065071945551a10418641244d42251211101d21248a0203071140c0c400e840c0742301c805c4215070500c03032545590041f801c140f054086c51846880c00403c41c2081500400c00c0354545100300c02160f40c2ca03400c800303441c3c5541c4c005039451942942840041070450303203e00111007d8810811480170094035048100000380360810712f00b4148001070150348291450540035054030507090311442e4100101d4a007914440308014505500c0b1882c100d081c0a81c113107041351001c00002a900e01103c40d10381000b4680039801210701c0100b40000004000c02c210501190029414071400d04444150340c0324070040d01d01d40011500383c041c6031400e000400661034205010741c00700c401030050310510340603000401c100d001080d4407000e481c80005201c032010300b070a12501210200030f2019203000d504683c00201700c1d01c00e0b6030b0f014080f4500480801c50141200000f00fa541 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 189013920 1250 189012670 189012679
    0x9030703080f0c06060d12050d1b090806070c030516050309041a27150d060c0e03070b090d060b13020a020a060f0c020601060f0207080111070519080702040f0b 70
    0x100c100e800344031010f40c45508824400e0080d64003042e1613040c4030b08a1302e0726a911a100012200c20424200e4498001c054141152512241e0589030f1403e4821300d1003c0b0445a540c4124aa0400030758502d001d002a20840410240c480c51a000c03960200680303a041c4c1c076141c0c8003074048509040036403a40c003170103181c1c0f6805841c1282c0e95118240075000c0c3c411880007640c515010500480c0420307806034404040903030111020b00080c5114010182561250a00614252034044191600c000b1107140c0010200414031500e48802285030802c0f90000401c800c5610301d28210046022444d6a07800e22001001d075512010854000e0745c0e4661450030fa005405400c540f40c0b204135070000d5a82078121403d540d000c0c40d101c0010280c0d8828003a40010748800d80041885903e0315000300d40740c0c3c0c0b031908070f4070450080080c046040c0d042809008558400c1c2c101264484d102c90400a041003041c0b010400000585940f14001480c0380017580e083d550121000244403441000340000b50160541c5294007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 189015170 1250 189013920 189013927
    0x1c030f0204050306180f0703080d020a0519080901180302120a02120a0305041b0b0910030b060414030d02030705100e0a020d080d1a031f0912022a150903070308 70
    0x718035450515040c080a100c220b56810350301840181e210b031008d000142c5440d1013004124841040780d0000c0441901601d001807826018103001e034016200001c00381d00080160040c0405800e0900a0780d001224002c403139100c06400790740103513541c0e40c0017195080400c0085104402039000348250440c211010050660b136041c0c008000340104801c84048600268000810100ba80c40090620a42d256004003619152900c2c04000700f035403012b1102070400d500c1c1c400e40c9142d92210400b8200a100700b101081ca40380340901018101000c207040310045610034090100854000600381e55038200d0220002004903803200d0f600d0400710745010107904502091a008200443c1d00c000704940101d0050410902c2c2c41410700104120f100071180340c1c194006a140081d1005001c1d00c24060424a00700280c549403d40e505410284402d089002580090340345a15180c12480c1510380c61401200c2c48800d030351340748000348007a228400e52311039502012035580340507103007040440d000e103400501d110349 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 189016420 1250 189015170 189015181
    0x421110306090723010f0305042409020a0e04030c140304050301060e010618140f0d020d120f030212010303120e01050a0b0a09021603110a0f0b06010f021c030f0204050306 75
    0xf034842c0544200080044000c4400c85000d0f461441c50005040595a0b940e200d01c8280c821800707400054030540320207402c05121f281e085c03c0507042602d428181d0710046030880e00303070040103c212002d40c48926100e00c6201000000b80c0d1080100c640380740e01c22030886190390401c9801d4954007480d081190598680403000c6008a04802003078101d81d4140c3d292001000d8186a158030140c8902c1190f02d402c001004c1001c203460400c84280380c1c0f040280c0140482442ca40009011850f0b40703000780d4804110812038201603510608403c18010f8909007545000011044901843d10520000e010081d40d440603211080d0207070001040728118500030301060a042c10401c0050030400c480520450031036000141c9074156000303a880c0c01501120005402045450580d001c900e10010710002d4058540e0600004066004007940180158075410041c904540007410040c1001d402005542c02400e060144004084031030324803600381c0ca400304800f03030816103140182c029500300c581d160150340e04100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 189017670 1250 189016420 189016423
    0x7051504050312010b0c0604110103020d090b0108061806010605090d0209070914120601091d060103081c020705031b0f0f10051e01030602091903081e042111030609 72
    0x945501c40041d8043e003641e84010221740e52240c00c0039149a81c100390000f038042080d4182c05e005204041c14050304c1d09903000c10742402c40c0c010180803141d40c02014010301c450701e010800c4590149880c42c07000140720720004050707540c1e00144200320070004c001a610249031207041054a00301c1e03002e01034000724241010050032201060254200060340041c000f1118507054184034071010120b00036100b2039091480c81006000c8400e415007082d2404210302c0b070903002c10000301d4021030013240683c0d2101445608660300b40c07031000c9a1040c00340144001c101041d8044200d624a50040b2002c546c00745107004030a040810105010045004400e8204403c0030041256070600d07a44078802c002940d10340340c4078100000155818048800030314014400258070340e0040100b050010400c41030f2412170a051081d40283d6042201d01d00d4021440b41001d0b9056040d920070340b0020184d8904150070240048403890114800400b1001650942e200380800722510074055107016040c0c40e20f60cc0c0413600309 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 189018920 1250 189017670 189017677
    0xb0f03060328030f02030322050304050d0c081209061c0b03010609092901030201050313081b1b1c11041404021201060602070e22060e01140408090402070515040503 72
    0x1035004c1000f403100404940d20200880340704544849207081501105420829a0014084122780c2444100008241507640c850f50152040c42107665145150810904a003070402644048884070024010183e4542d626015200c915403840005824110119a03900103000890f64a80e0503510740781d008599a803140d0011000316004007142082d400c4044055010416110b40105802540000520040d0706c00c034010354001041c5801899906025110768043e03901a411009004814a8852030302207028071003d00d241c0c0301c0c0180b10400a812801044020440e01034451040350318419000801101c041b0000401c0c1c0094420820f081d54249090203142098034141d1054822900300c20b500300050060344207032900344e07018140d03152500c0c40036075031200013400c1e6040301c070340d07038110110481540d0303000b103000e140143d0020403c82c1e034028038035084075604207024005114070403c12000c2041c0740225800c007902a1001641c1c0d440c50700300036003001c3c00c40d9000104028074106010a1001c000040c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 189020170 1250 189018920 189018923
    0x10203070e060f040506030405120a080610081501031512060c0306080616030b0103090615170705012007050303030708010914150103050a151212020105010b0f03060328 74
    0x7500c14062480d410001540226044030055160802c802d000c5400c100000d1500940f04000700d59114003c1d00f0218881d810451007103002400050400c007044c5080d00c5000c540303401d00e0a02d8151814200c01700648039021103070f05814144c079000748011000001c3c01080040c00301360308480a003c1070346844d00152000c500180e00137810110003040070030300842da01b4000c620a04240c000840d203801c1c2a0080c0a041d481ca0b4103055481d100400440c03a40d002e0b19039190104150b51043c941020686518100500e8030700005521085003404240d03000008105007021504a8240f41303581c03919518a071000642000d50903000101c14004030540050985050380d174100703020b0204814034080202c0c4050b088030948584c1444480058243d40603500094214110381c80101d0801003050300691001c0c6180d1180c2410002c1e0501201400b0341260010040383c41803009100c103524012940c40c150050300050511202d0000101c2c0103650104007503005072011509218028907520b001c52014880f5400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 189021420 1250 189020170 189020177
    0xc1205030c0f0309180c09100c0b22110303070804060c0c081609090615080a0605150a03031d09070f1107051e0102010b1c2001051e1b01020307 63
    0x1a0507903030740800f00c15a10140d50140c075016803205a07914107100010040d1101201d602c00700b000c11255101e41940340d920070000e454001141200740340081001c14003d01c0764240c10000704046401021188250940c2e580100341034020300a001c001a0540c820f4441c0106190f030000380004980750402d5a100c42c0a00805c00307403da07550350b242041d803104001140758402031803d000c01d00c501c08042d4400b0842a000e500002862000a522815984002e401ca000d0540c130021848003001140d0140c0c5030300928507081206085c1055000c00d4240380c480c00f004090045009400030101e580c24940f50101400405550329810200e10241c981500426030301d001807220b000148070f00d580040c0000840c1d102801d561540598100000d41001e1141245030465480d009490003e13130360306d0031600600d1074030200320800e0511843c190020109812609802c0c801c2042c3c0c0841580c0c11009840480500880040b010070310000d40a43c40d11840e05c030018072400e0500c0c0c0c41c02c1413105501440c42842c0c60746 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 189022670 1250 189021420 189021433
    0x9030203070b040605040b0c0a02030a05101a060901050c030c2b020607090302010f090b1308010c020601060804020603040f020603070201050106080105061303020415120b041104140604090c1205030c 87
    0x42c030050280b0507401002e01046017003104202000f821001000401100c2c400d03503c649401d580064104800070b441602c040d07005440105143c4198413840f00182803843c480380352003603000d020031014056400c0980c1403100115201101d0a028001c66200c2040792065032500c90014031070304a8014510b28903c140591020340400e80780c00020403a0041840d41c582109507850741d8011100449840c0580080001c51030000404225001c00742c40c006d00d42c50700d0154041c0c00d0920395802c4522107044c180c01c652007100100441500442480c1d00180c059900641d01d680311f0406c9042051a102c000303410080000801100550640c0042d05903501076a484200780d83e00e0003040305030b005540080c00a807000100800041c50282d00c0202ca031002e1000c004d21880d901c005400328102d640006845000c41042048100003454140d1a04988216004c02c02601d040d4181610440000d01442c0115075880811042c0694510403800a02c40c40110418050103454115205e0300320b0319088949101d2403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 189023920 1250 189022670 189022679
    0x6010306030506040b100f0807050f0907050d09080f040b0706051b0909040512130303030b04060e240411120108060603060f280b0112090b13060b100903020307 70
    0xa02411040700e400c10000c3c061921603485900848101800d03a0812283d081c0002403e1140451103000401d082c50240103c01c1c40c1c241441040c3c948030503031501ca180804100308400e504407054648500c3d009a00083c0e0300d05030726005545100c3e2101941158002042c005a0100000d0060050b24840c000c20301942d01d44155000b208003242000c55840d100501102d200350500101c150360243c0aa81281c0700b00c0c07800c2c0302c410341550040300e9400321001207890610505130035000d0804900002c0c0d0b010029945041e41416408002501c41c40c8500820800c0c3c03d002d80c01c515080c0b210b100020001c00c1040c0d00e004d030704840c6034401d144080990f81e00ca03000042c10000403407840c1c8200d101801038030703582e55603031075402d40480001c0c60900002901040d0300c1c410400310307641e03403405009000f00284600d0584009000d071400b5000400c1d0490a040c101c90015484205a5402c42030398050420303070094601e4071501414411340c00b290006402c888141e480c0703500003a8181121300175030680e800c0603101c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 189025170 1250 189023920 189023927
    0x15060315060b04090b010203040906030305030103030809060c0706091a01141005090d02010f0c170406090905040c03020906030309060c10060b0703020d260702100f0b0109050d140a0503070b0601 85
    0x40d403060b0b1050050030b0000b00907100542d089064014030520603a8509078651128104440c001d41050380065004401032082607004a0240c2e000368034403000b02010325200000390349511400324010040e90716401d0880070002410141402120045c882e6001e661b103881d1504a10074240407018030079009000e8050901d4003c1c2c0c21078164001c0035041401d5074020703400560700d12140c0d02e4050300b00030103500c0e0345000c40c1c80c024420350480780500e6003a03561882d2020090030840581c0000b40e1441c42c0c8400c0c0300018400e0740c4e03003600b180e5040d06d10b600da641d50350b00024118058614043c0c0c0004000800d9428103c020442660a100419003082125110240d4007003a004540000b000741e8020740c0c2c0034070fa45000c0c03211102031050380d207651018050141c1e9520244401905c1e14005607000000d203e28184480c065003250308110603003040314800c1800020841030303581c40340c50b002c0c1012403000c0090000c10070300403030440008011190a03081603d007035a85c1c3c0d402800107450303e05000002c500150310 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 189026420 1250 189025170 189025181
    0x61503080301030b1e1603140708070c061b0e150901050f090d060207300f05130b0406090f290a020f0715080c030106090b130315060315 60
    0x410440c040d0641c1e08507aa0801200c0c3e0141c003003420642c1d0b44081040704176100040b94452804000e4404603100785840150903182e2804215000182003010000c040d5400100c09900210341d1a00c591a0041800c105001b040a00c4030030505025500b182c450860f00100080c1c400c0006455522104600507542c0360310740038003a08980090001c1005142c1900c1680c098002d1000c004c0000e40d860740710340c0d50f0303108903400341408540303411006400340c01196401861400c1d100c3c030245460280c0307140d082c004000e0391080034039405108010441c03000300721003d008c10000c2e040c0071707001c0d40d82d0325140d0780302502008076440307803d21002010002182500c0d4029084612030400d4443d0054581880300c00351107034000140c8101103200350711341e140c80b200040010350001c02c103844c004200a1602031004103000002021036550324020001002120341c01915402103848001d1640d85865054801c00c01402e4550710261050070215202003120240354011400c49105080c441140301c1e4112040301640d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 189027670 1250 189026420 189026423
    0x17010b0c07060c1518120e060f1303021809070603020702030c04020c0a0b0c090f0d0218042307090b030d140f0d050c0705011413170c010c0804061503 66
    0x4001c04420810075003e00e40150032180b113103d0460b010010071640104980d0918420b88510407a2400760040c8841c25441881b0503416281410481500c100414254812400045560180012006c03260180002e140001e16801001d421910703414941c00a001e210680710200c50303008815000030700e5406442101d00056001c5c006c0c1c600b1000ea0410040250810003001b203450203000e40300da0014070006002c0e4802c0c1e0360380361607644411044050003410050a0401c600940004e442040035980300d080345120440140d80096041d9200e280042501380009144c01c1c10b5164406c010101c1503000c24081c0070b454a404041142502d00404c25550344200304014000ca45105014001c2155036401000346d81d87c0c405a1070300c3c2200451088040b528103d400e81000785000c0740360400c000e400c0c01005030400d84102e806105007482c514061000d072040a0080c00e510840f1070201c0d4807003010065492140e456030003040b011074001300280240404840442d0505c0c078040c078198a800c8000b0007142580d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 189028776 1106 189027670 189027673
    0x20712090503030f03010e040c0e09070e0f13031d060c07090b01090e010e070c060c031401080d0f1407020a12110f0f09100806010617010b0c 62
    0x404582041d8401e40041102209041c41c140960303055403205200302001741c0700c42ca0840c62445c00380c1e104051000b003020801a80400200d040c00495400d500011000c0d980c11603603520081c0101c4001c00c40c41861400b50000c00e00c1150380c4800311211440ca000d140e003481002600d55001003140451980c466913090080b01d080c0d0054181140c808c0c2026071820b410401082a00d610500501d41c1c03031007884d00000c41851040500300101c0b60014030802c000c0401d140700502400c01d0132010074440d11044000200703440005000d013043c8010741c1d280340c41d16030522030454000c1281c05171880c6011080c0032800150ba200c408030001821710903207280d20380c4924900f001c4000c42941e4035500c01c8851703c1529440703844a003c0c3c091401c2c3c00310b60b100072a64079685111111501c035000555640b00c1d490010079010303008a08020100743c0d500c0058150783e80e83c1e400e0303041d6128480031003649 = true := by decide +kernel

theorem cover : BRFrame.Cov 188848920 189028776 := by
  have h0 := BRFrame.cov_init 188848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 188848920 ≤ n) (h2 : n < 189028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
