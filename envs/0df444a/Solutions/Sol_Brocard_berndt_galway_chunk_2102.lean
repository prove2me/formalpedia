-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2102
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:39:24.377659+00:00
-- url     : https://prove2.me/submissions/87739643-99b4-4d71-92ac-9474eaab4935

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 377877697 ≤ n < 378057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 377878947 1250 377877697 377877733
    0x40c08191a0619170709020f04030201140f03010e0103020f0105070302070504050a380a0b03010608070e040e0a03090b0c07030611120a020702090f0906060d2306010312030e 76
    0xb0703001007504203040300c00d07001946010303200d40c007050200034442004611450305205280040417802025481d12a03001070121441c0b0490000034148039a500503100d02c9440b1409130b920022180b0641c0381d032035840708511344000d5400d200c01c91086014500d16811948030340d065640b601d5258000708a40f03400c0800700800703031000500403219165601001d203584603d4920204414480b035142e08041d8490001f40201681041460350090035945001c01503001583d00b00e03411114289045096616440c4c0304403881c45407140180e51050400c1e01138034600303502041e41e404891280c0c46005005a58200c210102e000d2a811a00d054110300002c0011421a41104074401f03e18402a0b2510841a2659108003015200c00b4443c543c0420700c1d904502704600c0f640d4000c1c0026502c07600d40d1070700d8021580c0e01d10006151500502c80c40340b040c42004404003da4240781c1420318412603209116001c503640d03140903c41940c4c061985c110102c0358600a101c1c0c00524242c040241002600304d0301000d02c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 377880197 1250 377878947 377878951
    0xb0412260c0c2d10050d02070309090f0608060a020d02040e150103050601110a17070b1f05040501050d03030e0c1002030c010b120d050726071202010b0913020315040c08191a 76
    0x814040300308004800141b682c0300420903184252940e500340c078113060030307102121400070010300720924050040c4520400002c80583c00f40810700056503856140c06083c0c0640100c3e4040c0156a00140074032603644400402c4000e800401c0c0e0f010031240c0d942000460b0034021402c8540d00b40c1c0c000343e07000400301b11201c90004034140c24008241c40c0810550710788060f00b0044402080340f240e8030214031000070081c1c2c80c00b401010121000c1c059541000c000400780b0305078a03802400c0c5650b550304089404401d003c4030a80e040020141640c40d415030390041d4803584a180b5074000e5503e421801e2000346092081040384211401c01800a030480b41c00c10707940740e0f103d000192840c1503034480381044005000c500c03203001c0140d0381145454002e149084020100031503501002e42e41030040100440d04c070b8445080d400541e0420403000da400714000300307043c4040030301c86580075180c1ca01000240120b203d902021141e101049418010400140070603c2d6050280100034220001d031900b107107a0300c408155 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 377881447 1250 377880197 377880229
    0xc140303090d0501051006110c04020c100501030303050117070f03060b0a030501090f0b0124030209040603060908280c02010507030e060d050f010b0412260c0c2d 71
    0x41d1030507840700300042e40c1c44030000080390349179100c50400014000c85100b65008000a06000f24040750355408282c880da00000e05070f01440d0301150100c26810b042050319a12a8210810495542c69003402000740000b409130624203002c84a0311003502a00040c628211205090a10340090540d0341e528003070503900080c1c4c0e6200c000040c011001c81c2082c41214042c52081d403018801d00542e1800c0c002243e8141d00c165401450381c882c1600d00044481c1a80282505260041c0d42c1c01c101400100140281e41001e0141494540703140e04001804d8010140903100c84030002c1c444141d104860344031044586c03040000340c005030344000154010405000c1641c440d0074280c614142d5503002c00c0c0550020030361900e0050300c51091140000c42c1c1e180c81c5000d0803e4160b000d28190900f1450060052001c03070083c400a004031040360041d80243c03001540c7c0458175100c41d85c40d8650440b540d03660460006c400d1055029109402c1e440000205115084030423001080d250702d5003108200751409050504 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 377882697 1250 377881447 377881453
    0x1050403081206031c0f080406020c1b0f0405190b060d29030705030c130b0603010b0c12120c0703020a1202010c03050f040b0f191503120c0c1403 64
    0x1000041001e4090201a040c40621401d0340c03420f42e0416103059054140c21040700002c0e001c8220450340b00d0140c0900504a04009147d91982d2904000a03c00c003903c140407400707508444c000341700360112214031220088840d01c8040045500304821904256090b03602c0c0e88110b1005802194141c04c107040002c0c1c002d19541c06d02800202900c2500ca41ca10200a000c4280300041e00442e00704114a034984001d400600082e4103004c0461b07a604d203200340880c4988031945c0314600c1001c09400180450201400140e203030b503990760083c0b08540040100d2482c5001322854042001c000209491a00c0c000c1c0c1840c0035240c50310503101c02c03103071302000c0103504502440352840c01050010100081c100c01550000407540c146400040841c3c0f070181c04511342030b07000c5080c400400c50f280381e05034100fa4581540c030603d4850464405126401e484030b0f440d1241411a20355540d04815030711011030340554a507802c1d8198401080b070704070181034002801c0803007200092240e1b4800140c101d402400140131 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 377883947 1250 377882697 377882699
    0x20307020c22050c09040e010e2503020319020310020f0d020714071e05030f0a08130e07030f05010803090a061107180501050102070b0f03011e12150b01050f031302010504 75
    0x4010180d420440d844c285003040040c0c80101382c04c09101d404940c80f0208000c1140c005600a8651210102980006000c402010400300388075503120b004003c56005089802040600c0301d0000c9990807208181d203e8011039602080002c0c1c0345c000c8a000c0780c0030980f894901013501c520760b4020740107400f0a84040003042100c0c8800442000410041e2003401e80307400303840c0c20a1400d464013011a4000601036003102e4440048900d000544c8280698000c103015100c80c240d0400700804201c80c0c0c081312824a680303007030203407a507016408001070044030001801036030b17204c0e01110f54034440d025100350001c1080c00308010a910401e94a07000700500d006555080da80d80c0c8176105510301c00c40045460a036500700412007582c0407c40d1800411301054120306100100e1382003481030105100d851160141000103000080c05c20341d00501500c01c81031100031407141401c0108030140501245078a42d80ba18507031502c10f42c010015100d429440858180c80c581d150321007030f02400a04070040381071000c01d001c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 377885197 1250 377883947 377884009
    0x50d091d27010e010b01020f0a02060c0102070b0a02070b01050a030b2701090c1d0105060304080304030309080304031205070905131805030403030f090906031707030c0503042601020307020c 83
    0x46a9903070440c4980040350f03660005050600f1a6002c01200b41507600641c0c0c2450406c9001c54189000e94049a2032030b00e902078816550701a200307442c40101040f003000204840f00c0200d5000d801000e003e510020310f00d1b03896034280401c0c40b4031808040c1a445038580061422a454980d01c21403001c0c2c0110044240d0a2074003150a40b0400c000450f48009100b10506c17400c026451114424079007129290b60b0b42d45807002203000c0f480042c0010300280c800000003002c2c540031380c1003801e400e944140c2041d40c91900d810b004004230351068040220703504100100e107500e48104e0311001902c500800300e00708084110f10060040c14500b0f89884814030072400b01000c99401d10107400114040d84607102030b0580c0ca103000b40020071a800031400e2600c2c00105001141190804400114445941703680d5890181070548681c500c1060043c00e900c00090081811742c2866200000c002181c188110030200ca402e0070350907408102d91900041c0c1c45141c0e101200c0c6400b0072031003400b4078011031104075409408 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 377886447 1250 377885197 377885251
    0x130e090610231f081006050307120b0307060c060c030b060313030905031e0d030516030b24090f0f0d0609150204141c0b0103080319021303050d091d 65
    0x5484095198051400f000030b140c01010644c0e01c0626141d0b44030b0f405007092000740071804050400c80400420002e5404100100d6115254041d00182150400c5981d1000107001c41c16492080b155141040700d51008603019009421944400400c10ba080d039480d10340401028014000c107408100c80124006031640b4180a0800c0441e0b00f0300500c801c1c420ba210006143c110300001c101c1c1054544000c01c1150004403603212080a010b140100c0c400000c40009002001000d6000095400703003a0340d40490220b4030001c100e018015a42e10402899100411003130100390030845800c2002c203882140005c4039a401680e5051003a50095100c14104180c24102e81007904001000119a81c07681e401d407a1802c00e003a1102040482c81c000c1422590341c885151006200040c8039000120201d441000420110400304003001d0085495144142c807e4022507050b10041d1464080d00c400e140000e03208920003020b8414000004080d480701200305817481600520004c0300401d41c0f103809003104204 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 377887697 1250 377886447 377886469
    0x120203040b220b0c07020306010812041503022206110c06030a050406230121150e0f03070602040302090c040807061b21020609061009091106130e09061023 68
    0x250340190313245c030903a2040c185450410f0304282d0782907018005440e044081c81d01114284c80e000900c02d9404841101306a0280c050311250706030b403604d0700c10a007150342042d0b4011011511643e540b44004d0110202c0d082e11424402200343d004035081000409880d00c9401c900d400600c00c0500140e15a8005500d0001d5002c0d80c0003648400c403010300400c60120303c03c01410344080e12201a0700c0031819552402c2c18908a64840d0b101140c030b0721204410749509001c1c40324079401c0241982c2e955640c03464004000c2d40140030481c4214424004100103d0040042d2002d944140006283da42c0c180b4206441410190391907003004d100340400b01000403840e09110341e035034580c4032484401072045940039051040041401d001a405207080001c1d0b40580030711102103400d60702c030002d02801107060484410f4102c0510035002080000c01808102503c1500411610513101141054a072658616107403002590110340c44c2840d01c03414843c10070720000d940c172207001030540c0120700700000001c1822240e030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 377888947 1250 377887697 377887711
    0xd080409090b1812031302031c0201020c01140108070506070501090611120a0903020d0f1103040b03071d0a090209220e190209040b0702070e0a0507120203040b220b 72
    0x1c0418068045145402d40c0d4503401c0f0900900450700b2003e10781100c82c00002c1c00e91035108031031886001991401d2080701309103032802e107401c0402244440064042d42c000801c0f10000d6191000c003003804944c22030f01c141030790544009400b29528190402466400101c07040c1c9255580703d01c5040002c40a200b01c00b4820055016545c481d00c400501c0328110100500300520b49050210304000294080b03400c1e504164282880540a13002c840210b401c8014821448541d03c80002c0100703498038904c1c00707548180074540d80c00c40d002400e175601200840d00b036110150884240c141c10705c214081c03070300904078036040600344484808004026024244001d280e4521940d61a502c0c440041c0701840b50b0038846071581b29a1781000c00783d03804680c80342d400070405069020400302052041c6c1c8203200010041c50141045501f03800c00710084001444291940300110b10321042c03840343c1c0c81c043e000381c0e0302c21034100e200003045070340b0164007040d5910003d0b1006180d04030149074200080b005a1034030700600e4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 377890197 1250 377888947 377888963
    0x80a0c050f0318150702090a1104120501020d0501050a08070605090105071a0403081308091512011e0603060b0a0c080c0a05060109050105060301030c0b09131b0212030c090d08040909 80
    0x40c40f1018858803a0b104600000301a03010015440540c032510852500912942c8c8c0c00030381d40f91000a00c580e03074040c0342c01c00003402030300000321800c0c02015009071041c1749e024030b0100281e0b40c0e102c0802060104034400c0c0a040c2d0080d0008001040c0544080c021010060500e1450100f159503014400c6400d500c0f0840d0580042d4144820300d80d000a909503c41001c0316000c20f1a1101e494000e0a4050088164411482d43c1d520b00701c09240c0304180d070400d50101d034241e03190703584412103c81d0070601210b01000d500c01d41e00d0005001c900c00e01480c000c0710403200d030312454010f4540046542c502c1004003500d007510100715401c04600f00f00310400c3c0c803a004a000e130405505100c0c002c400d072181a44000e10a0500344014008125510074200455541a511556611684010811a489081588490f9032500c21141c1c0919440d08000c04d9008603075003900e491200d032044510103400161295603103076605120082e96401d14000c003445450040142508181c1e036484240161a110b171400c4030610 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 377891447 1250 377890197 377890237
    0xd1b08090d020115030b0a0b04091a0f1e04170418110c0322031a04020f04060e0606160c0803091002120d0b0d0b07021c0903080a0c050f03 61
    0x5105010040400d0842c0c0700911510040c0c0b40308184403050f40c00040c2c5a201c3d4000880c1a0400c04d9101c1c4190300307009841842420401c0c01d19220102c0145408400b00c40c0e44800102e4036a02c504455108650084081100741c0c4812850214550000c10131a402010202c00d03221030440d00001e80020803080c2d40005010190b5035240301a200c03c0c40b40d0014030b07c1c00f44201d0038401c2010045e10004130707030404034140c04540e5095011085a00364000340140d071000c068461803080b05041107100707500a41d00c0e074880d40039040034041102c60f035104c4c441e102070300b01c80030410919064000b001e010840714010b0803181c4080c0c0700c21101c916640e0044080b03620014055102e403e001004222941450002e8941e0040d8a660030450340b2840e00194420355464042c8245981ca140c0b064403001c2d04003e07010018035221310081d580c1e40050054540d11704a080200b121144502c020900f82c0c4e03842203800e81442c1158a09503090f032410360045640d0b01801c0582900220300b00060010079030b0802d410100b207 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 377892697 1250 377891447 377891461
    0xa0203010f1d0303010b0a050a02100c030606090501080f04060b030a1e0519082203140106090b03160b090406080a030906090914160e0303040608010504050c1903020d1b08 75
    0x20005010a98954009000400c82516414187c44600000703003445035544403000700880c10940c3c5103c69107003607132070046442c501c0c0e40e02d540703c0c0741503580300e840d2490780d1619100150b402c064214bd04949107440b400005e0005581600400e10740c8c0c00180c11607425804030754034203107100941c008200c4888805041c070000d001d030030401c80348500c12a0410442c41d4901d92520b410503c510410115010746406088240210030394962000310b8001010760030362400d05102c00e020740864030580b1406070901c0840d800c2850302040c071043e02d40440c0940044580b40c40c5a182c822340041c2501c55216940703d800180118051060b01803407842070b5201000d06041007000f501546440e00302120f214540304901002180300c0c0782e01900030108100c408080e04240004846e00103905207802d80500001c60b00141d0140c01400481c143c134411a02400a9515100782208601403526840728500b0150764021009000342c4c000c26101c885a00040f81ca584086100441d1a1000000b00c0000c0c140104200c1c030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 377893947 1250 377892697 377892731
    0x1090b0a02030603060103030c020604150201020909060102070b0711040b1203070b0915071107080f0a260720030109030809010c0315180b030604080a02070e130b090a0203010f 77
    0x8031080d403040c11411803c1580100e0364a0005000007000c1c4102144002d0541d50303a6005d40b0300821141140000d078a6000000034082e4200401c81e501906103c00803504644c0041140001d03190480d42580c100306143d29a5070902118013100d90300541e541c03041d9001900c1d1900c1d4025902c41100003035030348050030700d4550f064620007400c1e01201e4100c2d101110550b1404000f06070000510b142c0036103407d51610480d0708040482c0e004424a100e00d0042520400340890b03510b507894061403d10b03513044003000340c41c0198420800c1e111009207040200700300085d01e2807110000780d140c01e001003001c6507403030303000c03a00312001c90005802054107402004524007013400390361200304c8030707117400c0c4000c03a00c1001e1030381800c0c0580500741510842c88142c130306940345940600d04816008040324000c2c2800d0030540040c0e4454038000006000b14000411641416030241c3d01489030b540d0018035801258961003001c8a001c1c007414954001c1d2008240907a500340188a00c40500b03250000d00d5040044141e84 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 377895197 1250 377893947 377893951
    0x18090b06030f0d031d0118152901030b041505010f0309080a05071a13021f090510050d05012c010f0b0706020f1b0c0a03080304020405090a0b0a060e0a0b1f090506040801090b 76
    0x19113217003003035001c94200e043c181541c180641c003127800d004881c0e074000050f8041c2000e0700b0440e070050b141078422070030316002d041d9800845000303888050102454600c2241520000c1c080504a8001000b401403202d01c55002010b40340c0c0a0703403c00308041c03c40340307800d02e400e8010390b034080901000114503415850041520400c0100640b954002030a42400280080c1450720442d8860701650034004a094000c1044400090b07211200300f11a6031540160184042981d40541c02003081041c001d0ba011190f22645050368108d0040040d0986400c10703c54169004d400100c400300c6d02444144c060024840c0030304580b041516240000c01c0701540e18500d403410406800d44200c09040f000c0010840c1202100d030410f0b01601e012543d6a0307404143c510b0440e8115008104254440802181e500b055100e0420790f0740d0038501103c161210100141925207040b9019407214040400c1e47c003030156121892004e0b246401c0c00c00e07216a481c0001400358215074021001d0303946800040c41000b1b01411125 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 377896447 1250 377895197 377895233
    0x30b09061f0f14040f080f0c01090b0307210507030b0a060f0302160203070b0c0c03070302060d020705070510050c0c030a030e10050418090b06030f0d031d0118 70
    0x1002040301c150341200c22a1800304440d060203002074060307807428820350300c03074200003480404503a44599408920f0080d01551082d00d4242c052038020983c0d00f007002c1103142c0350000c16541d079013070f00d402c0c0407541803254009030440c070510000c0d903810f01c183c011088170b40e5050890113a002400340f0f04000080d064800104059101e0203a003402484425040b0340d0311000003495140068071a11071014403081d80d08070aa000c0d40c0340c41a4140040c11094602c000d0407e400b0303180640c4c8110324454180340e40d81620f0b00009500c03420602600380f1541640d4080d0901c640540103c0b01120303621b002040307514419008140004200140f803188400c4104408244903400350014105070400da2001040c510342128064440c40414406612071440340d030994010340030030080c072041e2400b400d00440045c0f11101e02150a03550703200003e60b16280201e201114aaa4000603000c00c1414410407401080e4a01d241d16080e00d40b000400003040003441070f08615103031b902840b076540c025811720030201c0f40502c002d2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 377897697 1250 377896447 377896459
    0xd080d240501080f010e13151107140307030509011b0b10093803071512140615030711100f0615020c0904150504110a060e030a02120708030307030b0906 67
    0x4028001c041401d066000111f4100207a082c00c4a2810008845958042039070035824040702e0281e900c2c4401c01041442d100e4507411400c51200d403102c64030380c01054030280114409010301e0392954000d00c400f090b4019041600b000b45030301c03030b603400c01d8025040e5269008043c0354841448421041d03c201e0805a2210440401c6003a5034103049403000c0c0d01c3d11503820103941034804042607031820070081000c1c00015040f45440001c0341801010445054280004ca03410041c4101504c844004400d0007541c02801e0856030b080228440f07440703544082e000310200305400031043c480780d20034018442c00c00030701c1c0303004699000084031000c00d60305150401c95101d0152403c2d282029000200801c94980550b00002695120b061000424040003c42c6200300c0c1030104000810101c281907142d1008202e80104170641c0b40c10040360070302c1003109082d0b0140d10540780000540740582c0300080d412a608126408a9100c004c003e0543c0c0055071480c000c2501c80400640600c0d140c15841d50020301601e003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 377898947 1250 377897697 377897699
    0x304060e0c01020f0c0f06040806010b07050c01030903050d091407060203030f01062a061407020c03010e0613020d060b030a050607030c0c080d0228050706050105060304020d080d240501080f01 84
    0x141545809004c17408903c10400c4400001032030301c92500b5078000b41170b583d054806a41c5e40b5645824035501030a000c0798103008001801403076600030f00c940141e490b00743e5600e40c1460b0b56800c00300024200300704240d80744005001000000b08040000401801c51035014541768201714079848405001a042101840302070018943c60784500c1002e05c1c40c55180e054040d01240d040c1c10304400820381c0071400340381c1e070a038072040007440b070340000d00c8600002d415402044044041c180d01a11030006680e040250085151440003515020110b403600501507040080e01ca01542c00107442d25600310021100c5812103020081d41035010b01c5181300102890622048820441d07954210900c02c16201f06d41c600e90100d0b040c4e68200f010400c0401401e070640710704000620115000d042c80d00300d03c204030307441424180081118106030040d03d0240e54041e228003019611556804641e81113902070b9052140d4520324074250000038104901510150744900122900340000100284001007100c1e10300540200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 377900197 1250 377898947 377898973
    0x30c1e0906050d0209071209030806030d0810090f020d0c0c02090c0304080d0509210c0f2a2b030f0f0e09100b0c0c0901080a0510020307140304060e0c0102 68
    0x1000c0b03e41540e0444130484030b0382c1d40d514284c407100303003000301448114500400e00c0d00300f42c3c0101a40d8094407044044450342c0c04c1650040380e80e45000ca4807d0350071051410200291501504110150751030003a0150426840c803820404413450070340c41000252442e05c01905504040000d1500b10480300c2e5443d186240903203e0010620450340301049003a40c036800a08101d9042c0008904400007407601034007003c14400c400314070f401030580c09866010b08241703030300f04450000304600c599440a078941403d0b034000bc91040c00e010090380c2281c00504411a0903400903050310b045402d50483d1554030840041801d000742204103141000041c0905403202c1c40e0100c0e0051034010401004540e0301446541c0c83e40707103040003400f80d400900b500724041100d40d01800041401d640001041d1032a07d410382c3d841403c16600d110f00c010250403038006010100b03081441d0b400540c2e0160250510482d05042a503020015500840307050318541c1e91405100c1505005100070707548210244010060600004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 377901447 1250 377900197 377900209
    0x4050307030c020609090a0f05070905010e190503060106032304020607060f0608010f051b04030210080a0902061602100908030d02030a110a020f191502090109030c1e090605 76
    0xc5018050102d5501d0050440d40e03a00200c946100300501100168100090a400600101040d403001c4905020015855034070aa0803001210340c140e440300c1408c4d100d8414403248411000800d15000342144010800352400c100c1c1900030b0603141c0e000a103001404154050040c00e00c1018003084164130184000359990784180ca031116080b0310001048440a01d042e402441d450740700b1000c81d403c1c00c498000185c1c09502c443d1007502404084d43c0394800c5d40302000190310480c000294000440c4a031318403c984100407060344807002e10700c005200300382500002c1c06a04411840c501039500d40b1000011400c04001c60030003a2041e0400200617400e20108a40703c1c0580c180e0303038005907408000503802c8005c60300000b4400380ea08803410394403401d2440007074443c0342005840e4030318407400b0f85405104402142d0900001d030080404011800d4100442000e136000c4114103040100078080880403406d4a0b060308001c000da0300b01c2d08034501a03c0d10a00c212107883d444076280381e2816100300003680f502 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 377902697 1250 377901447 377901457
    0x1508030c072103050903070e1807050307032a0f0b04030516031509030c0606030c061e050301030b130b07050c0d030204050f06070201050712022b1707031d07031a040503 74
    0x150503c13a4850030500c0220307142c000c4560041c0101c45c4071205110325000c0c05540c0c0706006207100181d410307103521507041c142e83c0c060030301c402404103507200c59601c400c1e044495501e01c034208400781c0c08100303076503003881e4410200980c1112205100000b0704004106003007060318080c400c41d03d1202c00e4149540c4480d0403603c0500003d00c02c5640311090314003014030030b00049204c2075204804000c00f40e02c80c2040204d402d00b9003d8240807600c04c20290000c4800400c803c0644161aa0b840d850750307013035654802c40301a01600400c00014050b601000099080908510410700780e44c4a81c1c40e102c030a07420134541000903803c64140743c4104402e100d03980340c3e07803032140503118250ba4040e50381855100403152482a05800742004250380700844510764007048084800d44500015000c804610245100c1c0a959040d420003052103004080d07501c924032103484d03920038514100024a6802101c9240d040d076440705000526030000d08e003e10030081090040d01c182030b0341820040c5107203010350394640e80c0e00c21 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 377903947 1250 377902697 377902703
    0x150a0303050d0e060a06051207180b2d010e0a050d14031902010c0201050606030c19030b06181008091005100f030b1b0901090611011508030c0721 64
    0x8001800c40b02501140c1250340c0c1c8010f01000c94038181381288103100102024051a40b003048405030f402060038002407c001628140c1001c0090304103030412540c0148601c00c1040e0300074505101e850101d54000c2c4003804841428140c184010424800041c0803041d91120940700717021303402c0305110907262180030700c03001c50b030000300495000f01d0000b0382442c602820303000341450045403000700340003075041d0017454480d04980c000384016150801000042c1c041125581280e01c014002501d80815602c1d040c0d0018880d8240024000da404000c45d40341d034000b660364819540711040024460801035501345010340c0902d08084142000c01d41246c0341c00850501201d06034680303000c48c55030008040b00000800fa10b411409106540b890301c40c00c0710608482c46141d0000800d64030420410850440d101540140c0d41c000c4c4650504005480d07406c82c00b46181150744d070b9003000a00400700c00d803070701015143c028011034a400c260364030306241c40c080341c00084a1071000143c100b01c041c2007118080846034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 377905197 1250 377903947 377903957
    0xf0d0b120309121612060e0c150a0e0a1d01051818030c0706030501290412060e010e0109050615090c030a090b0c1b19061107080a02010c08150a0303 65
    0x949182c0e1a450001c01e44d60001c02040000f00008114244401070100c0700e100b00021320410080d03000c000d4031400d55502c07890300b1902d48280191801c5000008081600c6e003410000140441a008208500c6c1d40d60480114500103022408014680401c1e00707004010440d111542080020004801450080c0c500c8062010004004e1201c4500348240c40c0c0d0123500b07804440d100741c2d5902c001409040700384123080716113480110038000104030008001c02e407200025880e02c0e00d840d01c440b010b49100555015030714280c0c0d0f084124003602081c02003103003085c1c0d8030300041007c07107490a10f14206000604098102c225030400b04405440c0c014034182d0004080e80f0042d240c0e070b40c4810b800003500340c08400078003003c2c040d020400790b80c12400c00750032146058682d070061203101e80855039480d0751200180d28510410051100041d81d103421504680e9401040c0c50300b0141d50781e1354114503802190400c000360351100c9150104990280c4d00c660301580e0506100f0b29001c003840031030390050b018000902000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 377906447 1250 377905197 377905219
    0x10308041a03061e0a0e10061d030d140c012406210f0902060a0305090c1801050f01032004060813031d0301061a0904060803030c032a0f0d0b120309 65
    0xf0755882541d0300181b241d1300e0310a00a1a10000c0c059810701e15000300008251011030b02c145031094105103a11180c00a002031010241c0c0e210103994100e031203401c032400c1c000208a120720310301c420301a541c0d0090b1010000465040480701c0f6440005540e0410800c1000340d040c4030400400b5202c0c0c807c841003c80200003003903182070050300c01401c460f07100a5049400010030003410307035056110781c1c130030350300c031003d031441c030700c803950800101e42c0c12200000d40da0440300006201c00c2c545806401c1d18103205060004008540d21400442260007004859000802082c00c000940c0c000020a0b404070940c4410701c0c845034a41ea02429016501c0c3c4102e19038580766500d259951004d5000301c0160891035402e1611448080988405600c4540114081e90421000140b134483c0003050300d02800d54510000e04540d01d4a01c0000e0b0322541e01d0468104000083c814111110808000d0511500064082d9030f203d1074140740400341d8408408081c019240387c03901040d40d01c00071080e600c15607000c4600040103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 377907697 1250 377906447 377906449
    0xd03050702010513080604140f0706140c01050c0a090605071a04060b03060a0f1d0d0f0215010f030519151a04061409010e1509070215010308041a03061e 67
    0x1070080890078801203113100004104603e00082140c415445001d4552072004030b03d14203525074540e402c0340d0081c0e03070240d1014001540142000c100c501611502282000e981e80522400d456041d20015024032000070072807185c40c4d204007800c2c054182e034280349117032400d203030788a10072120b600b0100200150709002113001c0244a410a41c00c002000b0115081c40c20702020348001000d40c1080c0c2205c00d0328204c40c407c4100420007a50000036222001f405c0348038258001600c01d2080350705500110300602e16005540301c503030040c0501030610b99100d0800700d8190320340b6910b804c02001140e00d011028074625000601c50103030a03892403070b0f00100402c28601d08140707100c6204000010981c880d040c2800031642252131107045034850b004407031101c29644c2c1d0b0018181040e6094508a001e01c01b42051140301d0f050042c032041d046283c80c41100e5008011102c1e29903111400e03042160415400503042100416500300c00740e072202c20300c861900c0c5080c2040015008098907104806130b001c00c640005207 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 377908947 1250 377907697 377907707
    0x8100302032a1027030506180a1b031205031504020901020a02030a0f061503030507021009030501050f0a050a0e21040302060a080109110301050d0609110a03031106010905060d0305070201 82
    0xb440006010031201d98680c410191200190640c400003009280f0a048600c80000a134001100c0d00180070b000d007900c2c4d008088a081000c0c4050f40c02600c140c0c6115000650007041d50905ea0106011f0700c001b8a04601c0c05d8150380441a0710981001014801e11040312904100d8560100080f6401681d51020b880140d0400000d90390182d41401895106000c0c44000c1c3c0a500c4c01900c506401c02500314031700980340000a082c00003a002807020721460703005040c02c00f01d252444070182000500c6070f03501d590f07083c00e4078400c490310003c07181c0c800c1c140040c0704140d014442d04003030640b2080c007081c1c44c807882083d030310820f0008074100075521682002c05851080704031806160040c040c142d6030805501c01401c450028843c030b80c91180b03403050390080307980c00c0c10582e4181e5034000d200600e0f108081d113401016041109003a100c081e6203519058445d605e00300a00001d40c440d441d040c8000e462510b0160800005a01590419041004106090341d5003611402e50651500708141c07183c01074001256 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 377910197 1250 377908947 377909023
    0x306040911040603150e03040e0417090a0914060f241e0301150e0612041109090a02030105010504061401110c04020403061b0306260a02040c0f0810030203 68
    0xb030801d240000110510541805007004466a0300d800c0c40000580304002c0d0703a0344610301c10840c0010741c0602007000161031200880e0040c0e40f282c82e640c1441e5018000845070600d9034050a1000c0c1d0f199414921140715800a40e88405c0032591042c1809600700410400d808108034121b000c0300c000c10080c11400450305880321000a0300003203841705403102ca0601540d000b805004070906422180341a15846401c52259032140603111900700300a80c039100406100c0988211119074094442000949440841911403661b000040603191014010f0500715641a0022070003142018020300100d0311000c5403a0080b002807900701550310780316030110b09203130021144e40d80c010f000040000521580c0d4110000f45580d40d0a0010380403006082501121700c54403c0300b032001c40070683d03009c00ba650b41c19204c407440c00f4041591461071103075002904440c3c04040ca1400309a41121741a122580003602076030000011241103441421500007a175254079201c401d0501c8034410074810032012000c040c0346 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 377911447 1250 377910197 377910199
    0x110103090212250b0309030a030f0e1f060806060a0b070213060e0a0e012f1e0c01110301140405130803040302011a15070206030a1d0f06010e04080306040911 69
    0x104660303d0a01107800303421043c00500002244404040b40c0d030700e442d8044178010280b84c070040d4039103c014442500a880035a0b5030450583e07960340c0c2c2140841040c41481820a0703440e04500e1504140303003081040320b01d2904869010b510180c20807005455404000d020348441d050f80c10380b03a9201e480006c0201020100c000d440608100b400113a40f03100703280710380c0200450281400002d0011842034200da4006002048104015203103030300c0789150f0202c4c0300c40524061145450421120b038844010f004c4120142e4148800080c01c2170b0955082c0300382c48000040110440c0366502d002c12113403803c1c070746134071480c403841d500e40c04030305030600400c0e40a560a9000030800e44030303d0581070181c000e00040c2d9413001448034212203015a403030648001803941038403000540c101322072078088c0501c2c2d420040c003402d620345e96103080440080c0040c3da045481058000204106060002c82e10b0610340c0691100101c209142c050200041c05101640d5100c80142e4000401e5001410301246802c0500348036 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 377912697 1250 377911447 377911453
    0x1c021203040e040302120a020a1520030402031006060807050c03040e040f0201090503070501021e01020c0129010302030403080c0d0b0916090f051021020f2203110103090212 76
    0x1450300d00900c000f40310f02d000f90281c0b60001c1288030050100d106070440d10300107801942420001980c0074810110503590000c00040074060025411140c241074215810030400110400c011843c04000d010030994880e1810300040c0d240c8000074021081c007911000c00c0c0f200101d0124840c072020002d40d4010a002c01500c180c600f0a410031140c050549503081c2e0000d01c8145011400b8200001e4903411500181d004010f016903a8121140641c292044c2d80c44a5408001d1104140400d02030400c1c2100c1a42c20091280d0039400b5180900c180c164190341403600520420020a0700149155406110750600320760f1200011040780040c00d43c0c20369250310140d4141440854040d000880c0b0030f401d026200c409a2a03201d250014116900307214131640540c0d40518201104e01c50014040c40101120030440040840000801a40c016055803503074240d02003a14426000300803284404051a006400851070858032407610b20a01c85941506050f00c41c04500d0031501c2c2d200e1a44001c81000080d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 377913947 1250 377912697 377912699
    0x9020d03030519060e1f0807080c18190e010b0a0320030a0b222906010804210207030602030f090d050a120b120303041b060e1c02120304 60
    0x74000b071600340d8608503000b5101080c460400da2510640007030380c2491001d02d2040e620f80104580c00100f4441c6c07580a41c5080c003000560603c1004444050403000c0007622400e12001e050000d0040c1221000000000c44018041040c841803601a5032080018010449141043e100c03405081041811600b0001c03602c000028000803d0301000032a48480d100f212900004003011769a0030f40c044060014248100030920f000808202c06c45081414880611402c01c030352144507000300d803c402d140310404549804c845040340c1e042c0c5d01c0e0703005030242445103503070a00351181c3e031621244004c0a130004840e251340b0002c071402004103030000c60b80410309540e649480c21010001c0d41d01a0342d1000d051217422249010303c0d0050003514400320f00341d07590104030144118450003400c08401c160703411110f42c0d10220740f01c0005100940c400c0c0e000c0c0407010b00c01c400b80d0404200b0041168441d100300140f00174401803d6850170040000301107500c3c035044000b5401d000040e44440701c401145214030001030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 377915197 1250 377913947 377913953
    0x3050403080a0c050f15241302070b0106090803120702010b0a080c0a060302030708040807170f030610020601050312030603010204090618050c03100302010309031110060302090604270609020d 84
    0x10aa0554600c5101501d1581142d4241c0c170784d8400500c05210f0700d80b450000000c0da8081c1d03144051b0ba4500e0401510b00001075400c0101e51000160300980c13800a400241d50740038041080361550050180e072900d031034054900132100d6224018941d03000502c150b4000818222413007500038801e0000014a40c1038101e546150090b0340f0040c02d103586006069242002850901074030079a80304e50307a03946078940984c2c0ea5944032001d903030101d0803c0b943d10654880c1440c2d0314400c0009040120802c0440701d40d00d090110412100400c84c2d00c1420455101e0b60040c400c54a001c507244004400c2c626645840391180c0f40007a01a0041d6048013000038540341c0001240c80a0450041d0300d011501b000704155195a04d00035001d120803170300c242103245150030420041d4426845a41d00501a01d001d9040b02103c000060400201403c04d030001c13901c624050042d440c02080341500000c1c101c1e4100404400181c410b03060104150707000c0107a0100805080074440303190444064607a000300541500038043c0707 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 377916447 1250 377915197 377915207
    0x70201090210110105010e070806061e04030b04060b03070522060315060f06110705010c03022d0708010b102f0105071b050c0f01030f0501080304080607080f1303050403080a 76
    0x40c015443e01d6092000005400c0180c290203401b074045940c0340461582c40d503040c04804d60200182c0f40401c3d41600c81d481a441065020380065407048000100e1400c003410450240c58000080502c00d030440c0345c01b00225550500091001301b07807403024469030351149082d17000500c541d03400584481070746480700009030311070f510a000f51101c4031400b0315280d80320340f0202da03c00300d40c182400c401d502146050113075602074800b00701c0c0ca40c460b10450b108039013004114120758460701e945003203200d0180300d03140b00944284800380c00350010400800000c000700340003421384d5001205040c1440541c183c0348403c042696000c40209403001c0010140200c4c44c8201c2e4020641200c0300400070f00081c9101ca0000382d501c1c0c06d14001500325005082024400e82081607004003002c00605155072030503c00c203c602d003800350034001d0407100055a00e039440d000042d820014020612810803008404004080c8103051200e50000740c100406e5800f44000e1400783c4a5100e540c0014089000100701000803540c05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 377917697 1250 377916447 377916467
    0x10221060901080715030f020f070507050102190309152a0b15011731110109080307150908030a09030f020d0f0302030402030102130803210c030f070201090210 70
    0x40d28401c031140e83c1d400f40c403500c94403140034044442100d02c00c02103205220b0741042c0d20504280d04010300d448000410258640c0c8a000110351a800c424020400c56806100c0c4240d0800c0c020080019030000307070740051802e2a80c0c05100c0c0e0707001c000380e10b000703140e44910f42d44418251904e000c03a4400e00501c1ea881c2640d40c01c614125140c9118a000aa018200c035006004010f8117031180003003416103030400308170900b000f40b50400c6c1d44801011440540303555049203a541d1440c0da1000c1006c0858244040a81c0d8440c481d2414403903e807070f0400c1401c6000040b1122180c1140380107014980071000e074006007180b40c40141c0800c202100b40b01501203d40d200030030b81071180e05c0b822107071040314906a88a002514005000c210702d080c40b00d0f0000d00940056a2051004000600c1d141031f50060680f4400d0a400200030340e8804100448404500003885440100d40400004581b60850400d4890310004000400201952011032480c500035002084a42d0b8018840702540c0303508040180034500d9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 377918947 1250 377917697 377917699
    0x10c05030d050c0c010f060e1302030c27061c0813030b040c05030c01030b1003230a150b07050d0e040f0c030218040b10050f0f1603270306050901022106 67
    0xe0b06100c0c0b0340b42c07840d502c1f4180c11101c0022440950399110200000d02c0580010300780d03014000c40d0440c00c031075695a281102490395503000e06070611f05081e031003035081034001c22041c0140070003440f944014030380c0d01024a0450380703e41d11555812129040c0700d0204816400205001a640c1c01d000400c1444500703d003e0710310681c1260402808540110103443c0e9480c03985410201d400c2111141038442d8011030780244034440c40c55500300411200e102e0041d81103030840030f9141d843e00f8904008540409680040c0a0180560300701100c50b00d07103a48072000092b01300b060085540d0542c0150315903400000c02440181400c2004084000003d4040d511a20171510300e126070740d06201c0c0300d2525200d10607070040301800068404007121000e49182c1d000d8075014110800c28400c4001d0014994002d01118003803911a04005215213005480d03008031883d01e098540501400400c400c21000031282100d40140b004519074403009034003402881000c035070b2a5060554440152204117141080f401024 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 377920197 1250 377918947 377918951
    0x6131106091807020703050a05030c07120309061b021c0b060a0308040306020711060d0603020f09090c0d15090f02130b010804060f0b0a15030c09080a02010c05030d050c0c01 76
    0x4000410080340305010700303140d0240b4101080842d1440c001e015070350042440c011102d8182e00c9031146454080d00500c111560b43c400503070f82074540400d00080c4020039248450f0130b2040b0160354060b2602e140d82c080e40d01007091441441240749810b03c003c0c44a10b0300900740d0401e08280000006a1550080c010381d02e003800000411032509020000d10b0803240c00c0250039007060b04540d42c00740a544150800d46a00584040102142da107002c01060b600010010002d0594030318818080042941d10410f44158904410014080c40118850150290031a80c085010001c0d1a00088100c014030050040340d15052629081050303000765003000c980203c42c03c586180e00c1c0b030301c040c0c1a01c5e5450521800030752084046400640f01d50001c42c1c1c2003040381d50101d90341e288900401d031a03819a62104940104810020b100310340c0510541040c1350103403410402d12070070005400e6940c80c403840024100401081d0040c20301c801072066400480040b10f0620413414a04c0c06c40590303401448406280d94 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 377921447 1250 377920197 377920223
    0x80a0b0105030622080702090c0705010b03060601090519080d02010e0115030507030b0421050307030510060e010c150c0f09080f10020309011b03020a0e0a0e13080c0613 74
    0xc034000500d1403003090401416007040c04e00501800301c4400345401140d0148081c8200d800603540e02c41001c1c4210300c00703804291924450309045003542d090742c120a0103500a40140b00b0700da43d12141040c00c1d01c00c10b5a00c08210f550850a02d4032410040d03000b00a540104180d5940b5580e040d0011078030010020000d10507800c0b019108040c036482440000c225034412002040041c1002162030781c030502820742504401040326440c0e01210700c4c1c0350500c002130400810401c4854040c89455040f040d69482440d8144c103246003d4041c464010009060043e030310380d40010020305114031203401100c0b990034003001140c064040c0003c0380103480c04e001300305610307004140072034001445802000c4130b000800c4940041d070b50460080d480580100368035521264201010359950704d00100080701039500594807910603200600009565038160b10801c001c0d14104011401c035074030f458000c0c4810f110081404800e1400c8901442040c03511601c0303014450400c8556405c03902007264907405001000490 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 377922697 1250 377921447 377921449
    0x213150f0b0403030e0102071a030714070b040201140c03180a050d150906090b15040608010c05040e0903160b0106021011030a110426010e0c03151f080a0b0105 70
    0x240c205402030005440050000f000400d104042203a4800c41c1801507480050b01d9070180e2400c55021034003100b000070000280301c086030b81710601000e000c1c1400030041c10070685664842ca1403101910280c10802080d03c0d4044003a4000120b40c00c0f008403104403566001d8010b61644601c0449080343e01c82c1241d140001094201a05844c0300345600c90038240486c007540304100c00074550303d80c0584083ea5030309140d600203110018503a00a41c85483c165524050311030070072007510744030381000e611079042c4080d500490b6044000c0e82c09841d106084640c5070340e00e41c3c2c000c520707601035401212020300081140009004407841c0d9241624016825901404071001003902564030400700b4001c0c180e4100002442a1055480f071040420100000e502e00707503440c14400046202c10300703044074a048840c010102d44009124800c4485041c2d0040e04c2007094060000c1e0b1540d1b0704184084104c007848000554041b444503545503c401c407031100320019511041d000365501c8285200700c5042d10302200202c2d807 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 377923947 1250 377922697 377922719
    0x70e0a0506180702070f09020c16050102030f0304110301020418050c03040c050d051507020c0f030a02010504031e02060d091a01080d0507060b03060903120114012a021315 75
    0x410318014200107001e5820102c00c10405030000e100c4021801a05404180a00040c108030000c010407130f40540c83d440300c206100c2c1000004c01450f01c001d1100c5204003d1a600802a00d190a800d80003440c0c40e0343d62400e0280f09010003112903030303055100050104d80c0c5a61450685144d1181c0e09003001603940c1d00314000316610055038050b0144a41c1074080186107012405200c003284540190789074070b200d52281c03102c40103040e0303000740141e08819050715050030310041d0345885580031130050500294980020b401407003140009001c5001c000780000c1c0310280101d100380c0c0f907176029100315036074440c50407120b00511400c8012605070455104040300d140d51000060705071000c0302d0203014501c2c0c007040c0c1560036070300a6108886880c1c6600004131507039414000b05100385540b0001d1507540b50f89a00000101c40c05800524283e0301c07443c00403d8130b0b41d022100a1b641404080c0300d450742c0060307644510520b017028000a5011602d214150781c101c900b5042080c0c104000c01ca650078840c1c84200341e1130 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 377925197 1250 377923947 377923951
    0xe0a020301051f030b03010603260324061b0607140702090a05070306171011030c0d1e18021c03020a0f1b0305060708070f1d060d0e070e0a05 62
    0x80e01800070350048401c0004055102150f101600740010009542008a0700f175070352300da00554070b141060114005d5030000800b40071202407030113080b61862800da01d0200740c0c03e03843c50f011050b1301c0c0039030f0003003039251074100490303080014204000b41d0390711000e1030903a07070780030121360003c0056480d4144129020a04080d121415402806401c840c1d8420f824003000b4134000780304500305911458001500085410003208000400001d8052180120380c0c1c0c0064525515a00750700c10700400070400141044c40945805490090020078031106003884010403a0015125040702d40c6000d04031004801c941420b0901584282d03140200800c03283e0007121260007045024002da0040c1d01c40341d0000c2d01e01040d00e40498402e21325090f800c0404000034490f0140303500101d030903602030014410001c0d000700a080d40141c0502d080d101d0380c52071810080c500302e62a1800d00c42850b014075514a04d42c0c0d00340c240d600140c0e034101d04202414118071441e03035480c590b02c00c003141010303d50040b440044060142c40c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 377926447 1250 377925197 377925199
    0x81b0c06180d0804050a0b090f0f1c03181e060201110a0309050f0a030203070311190303020c070b0307020c0405100b1c022109060f1611030910090e0a02030105 70
    0x444848200360a0040707500084400300c0d061841000041080e41e1001c08030006087c007010307991b4036440610240305c00b80e0442c040d03180c8541c1070307035180e0030565072405903070304d1240b0049010f085030320203519050703500d08110010b1400b05002210f0104580e94040c40d0030031644510038100c0c030034075540c1c901a401ca5540c1c40e00c0d030034040070402c9041151802500a000d1b00d91040c03080300c00d40d001d0481c1e543c0c1400703643ca03021001600002111800e0551040c41442481071103400b801c4103142c0c40d201d00101c0000b00ea4001c09243d0042a05503080d1000d0100b0f800401c147c0084640e40c1c03901c11002034a5180c603071590362040d40b4140220368181941030b0144140c2c0d06040c580d614010301806801c1c086405910310407032868082028507410700d000c000d2201001103448030340300c95040098000c0e0801070010300c46a41c401d5038008001188101c6120b40001c0c01860800c03004407211090510700b58801c100034540c0006000514014556001801c1d1003242c000c945070205135143c0c000d451060741310a100b15 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 377927697 1250 377926447 377926477
    0xa06080615030a0c06050a1725170405060613051009150807061e0201090b070809010b031c020d0c080f03060a030b19061401200307081b0c06 62
    0xa07600849400c081060203800a00703e80f8200020f07a1124040c101c56004100050404a000c000064019500359024440b42c1c0e1850300070f00c2d0000d030401e5036000300c0315a4020172904106071208180501d445001000c46002c0c001e0152509061242e44c980003601c42c00e000309198001c0c000c034142184601c0e03005031b001c240c0c01c0080c24508003020780680302c030320b4030a03070800d41c01031300060802d1040201000030100f6894a03502882040302c0f90300381c0650716030701c1c0043d64181920305000504d0040c0c010b900c0141400c00050a803192241c00d40148410855180c151081626508000304580c02205189405a0803120000680c0000b1950089508030051042d481800544a140640005194420000742c103861001e956900c0300e1094140c1541c140003909480c64180358240301174056000a4504050303203650381030302c08000a182c003010080d00010b4260f581c80c047d00c41e03a01802100c00058020094646030309848203d0150710028405242a500c00c03080c0400c0603052050036288108494068 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 377928947 1250 377927697 377927701
    0xb0a02040e1014030102210417030109150b0403080d0504061b1d030c0108010909030e040c0c05010b2704290702011b05191211041a03090d050f0f03070f02060a060806 73
    0x5254040e80c4023400860b0340384c032102400d60b140f800c0c101c00b5600030701000030003088a00040c03081401e0482c43c2d420100795008104001d0010a030018216115260440c2000800e5a60303400c0080c000c0c480003103c0f0803c90411a510601282d00410302000108580458045029908d0805941d40c1801c071041d400304a2400041020600c0c0d0740c000fa003024001d0900d209000e904070005030845d080303216a81c0100c3c440700d4036031042c00400d00c243d1040c0360707056032070000301c680c4905000e0400380c03103208a203210410100003400700901d03030020100002c00036105c1580c80400a40c146042d440403100030005605e031076080c040300f03034000b007074210b25a00c541c80742e501e0014082c0ea81f030398600f07050759140f081c092030446001c43d5540c01c1c418902c400a424004c140c0f503e003004900c0e800461072138122a8102000e10900800d4100403510405510090402c80d41c1c45041105260f0f19004c3d075040b003510800088100406590000d41c04034407561940c1c00d46880e80e4510b6a004c1c2140c00d64002d00340180d2040c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 377930197 1250 377928947 377928997
    0xf0f050906090a0e06010e040614071b05030405030307061b0203090906010f11101a010305040218070207031506051203120402100c02060409060f050a120b0a02040e1014030102 77
    0x181c8550041807081012618006959135030b49070800030707403105420807d4081008103000c1c003446074111039410036030000c015051050008210043c03146210091440030b81c0080c040110400c21140180800b4064940302d5000e0309002c4000c040300b450f1602034018139480d40d0308061021040381d2001c1401010a00c1c1c1703031142001150402071420328942889500501d030544220100b00c1c0d04543c841e0141c0100321030f4038401300900a890030720401410725051034240401070342c400302d0f44160500d11030a00882c039a102c0c98100d16220003544041c00c440321940140446480d150009030640e0402e503501000315440d18442070f0380e48103030005101c024180c013000c10010301d002c281d441e1020141d441c0030210800e458001a202d9481a4842140540d5500081201c1408811144002e01045503886801407a050458261030b145441c02003004002400182c1d000e880c0340c0c1034a0103440c4200700e8002c1307132520700c004120791a00d501460700c0c4001361000c0b9003030900d07050003160101d00556101c83c445102d080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 377931447 1250 377930197 377930209
    0x616030507080f0c0606012601151812120806060d0c030e0f0f0d0e090f0604021315080a1814010f05090d1407030e240406090f0f050906 60
    0x1c02212101402c20030301c88a0b00a08003e42a15003404010380b40c1414540d0015003005d0007002038840084c00c0000503519070503d2100581100d40380c0e0840c0c2d0300c2c0030004100305c4000d032040e01b4003605500c08110204000842c003038041e825500c100f2143c540700010007006c2d80c03842400c451180d4400301c2002000d80d040e0864100000140b0a0700740441e44501f010749950910640d921800020b50009801900b4410f0400012a991103d4244140603100d04000f048050000410460034081c046010035595101c81e41265048280c1081a850b182d07150026003d04100c00320078040002e503024041034140c0081d21880c84401c80e14680d0418548460761080c20344804000c10052656840c1070110b6449801c0c080c880c0316402501c00342030306290f42c44014207224148000036090f0b410500509000035040302c003901c0008402c0740c00c0b42c00e04a090380d525910400c607612008584002080002d10341e40c1145980303081d58082c0408500a2792580300d080c403106214440e140c4d001c80c111000c180e09003010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 377932697 1250 377931447 377931457
    0x602060c160f0614010909020a050609030c01051303020d03050301030b060108070e15040b03040506010815040c05040b0303090a030c06090b09090609040c1203050301050f01020a032f010e03041406160305 89
    0x41c180492240c0000d0a4146042400d90000241b140c0b40d00c101400c40c0380c907010310703000b525080310406d09000002e004240d40c0e2001da00c0140c11301c03000080880241d11450710440c010341d8010000d82404919140003001508207202c12100e0044c40070200b6841d6003c2e00c0c071a4031810f4140c2c0e440c5a0394064800300715285006d0984103038205002c101c045801c1101e000110b205072b0080f00105507a514003d916840d0440200c800251b003812181840006542e0703503105001c4031021900030880c48542e40c00030b800c0d48a608072040d440803684d80000100914450044201c51694460080407a640c9801c5407852003520712641d40000b11200182241c45e10107001030b081405108902c804c00e44450300d003104418402c1068001c142c022004000034074080c0c08411301e9900a101810300d0503040d9070041c003040002c14007030403e2500400a51102c102c8130004840c0840c0000c000d10032a220344070041e440c0c1c0c1c003d000d8110005032103900c6030010b0400340308564030a83c0703421402c2840060740c3c80445a50f048 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 377933947 1250 377932697 377932703
    0x20d030c0f02060a0c140d0b030708030f03011203090b0a020d0206090a151521121407030c0302030f21060a06051c020403120e042d090819090602060c160f 68
    0x40001104405030b1881b0107010224245d000000b0491b02180805d440c041c0780d540050f060f50300030444000c07501c503500e003030303e044901d4981c00c09124000d914095170a207095400c110050760010030140011a80000d00d6501c500301d5800707403070b05900c035041459150648094042e00407140203001404491446e40702e81d003540c407000c0f184040d050700c0c0d42515442d0140d000d00c6d0780c0380454050100d000d004000200304100101410318049101d250702d0344002c1c42c010840003506000a0b000151f09160003481150a5905c00140013a5103407440c5486440220074155a500264490f40004400e4140805068141e444548505003090300c5490903103202c230101250b5600c080e07024800000003d03103114050b80303038400c2511100c40f044024001e01c401c40d040000c44443c10100305c004402c0008014407050741c039000c048008603190001e410b00710654403c0c03140716030b82c00f8200544084141d90084560042d1000e03642602c841d030b240c4003090b1a40780514081141c600502d1104a000a00b440e40070305400e0344 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 377935197 1250 377933947 377933957
    0x20d05030619060203040e0702010501050f0607050c0910030b011403071a1201030b061009030804051009050904080309060a060608131b0b0901030c0201060b030105010c050a05010507020d030c0f02060a0c 89
    0xd0010b1008000741d07209501680c8082014444030701c802d01c001e644080a40300030029076260000040c4501d01340701526002e00d400241d284140700d0184001303070304d02902510245040c01e290701a1070611103144401c1e0b4042407241e001169841c1401d8801d122004020010034035981440b840c4a00b582c4114452700c02c882d0304019020740c41000142460003180034560780000e0b481e02a00b030214104000d101e00c4100402418188005104081034505488050798980140c1003080c0040d14400c03c60307003203183c0c00034030f00c0308110420048400a41c0300305600d4007904d13019143c9010a5040ea18035018600203c0c6e4100c0004584c0c00d44032141881039401061000c10b1440e000300ca0805505560b00241446100090542860351305802000c07001c001c3e600c020000285041c400003141e02040c0129810070a070361900205000342003081c45d1503507402100804c514108034001950320440740a810000c0f038140080c5070950383c0544480100188290081d03c0507541d0f060400c8000d0607900002801c4c40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 377936447 1250 377935197 377935219
    0x11d1908060a14011508010306020309070b1309200d020d11070b01080715020715050f040b0d15060206070e1c0507090e1c032a03020306040b01020d020d050306 70
    0x50010001c0e02e01509802c140041d07505280c0821501d01c0005820240050005501c60002a584800001d04403900040b00507101d13210106550305005465100c0c0c0400e81c80843e4000500b06203810190890310854020408581c1c0d01001c1d03485003448100041c0c6004081c0144c3c000188250000d0245141c244400a40c8901d148941003842c0c01c0510165104410480140015581042800c0c0a401d0751400041d02c0d0001c5078000f035951299018000c1561521048000020b00036019039101da0a5001c0007600c69858540244241d00011003580c900c07814140ca040550295149081c10354420754060310303040d642c2c09070550b141c01c1c0d400000798105005400e000443c0e00d40d10310a01c400c5204201800869107032540e03000503142c54565038400398202e0b100b0064044072604600180040c06d050219083ca100305803608054014003848402c078078a220408034183e8186d0095104200c12a000c114480031030004a80d160403910764000540d000c2c00c403030146903000d003001d980e100600400745402c0d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 377937697 1250 377936447 377936459
    0x2070b1b120c010203090c04110702041e1d01110403030801050d210c17190f020a060527150703150317070507061b1202150702030d0605011d19 63
    0x1d0b520990707422540342d6003c03040c000c4203070307003480b50307194008084405000603012141440007038820510024410740d52555407a4640c6002d100704134a40100c41020060724460070740f44c0012000146e070070740b41946461000c0aa0215410645081d66015601c0d1001c0341c0c2058244442c0c0919a0400e6070481461450403c1e00813807030110011022995640c20301030362451614881500360244020b15940f024040c0010050000c8101c03032a400707492030f000401c5084000c06908140940c1c0d0041c18180c20001000704004107941d0750300d1f240c4901c01d802280c0704115145140c8451851140801c00c40010340841ca03e030340b00382c01c004800c0c400084251142907881d66810010304501203401d000c000f0200350101842001e00041c8004c1c005800e100780c0c041614119558000d00c600001441048808400c2da18039100700241501502c4400407040a800c00c0d00c4080c2d56a0481c886d09d1003182d0501c40301096951049007103030070022a0401082c420b565120070410803410380c010300f0800e070742d07107800000b0340d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 377938947 1250 377937697 377937733
    0x1f050d020c031e09040b01031a0402030402061902061e1b0c01060e0f010509060a0308040501080a0905060717090c010903060b030129100311070b04060e032802070b1b 73
    0x5640c00103c085540780c60000c02e001c140c5142d03448060505140801e1340705880d004140001c1c05000886005030f030390f43c0b1840014018050f0200c0324107490b500f0042404016000200300c1e000740510410121400c0305076815101c2950b007241c680016010345a2100d130540071000141a0010300c079000030480d40d49500314035041c400115140307451506010010841414044186500040f050750030300340030b034110384a01e10ba40c8a070303210f2903040200010000311014010b52001406075808030035a4001d0400280c020500420400c02c00b107403091490100e0040c600004944e6050780041c0c407a059035a10f151030300802414945145500740d501e402d806803c1c2006280440d6100c030400030001c088070b0840080c01a002901c80c540c2c41818a428024084403140070256078280d41d01c491081240d9489191000103481500d107201344c00c0c4004a00c00b004000303180941c4a546000050803141004c0729181260b64458610500111000802100b10400e18000f150100070030f41400701c90007407101000c0045 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 377940197 1250 377938947 377938987
    0x10c0f0201090b1c0606022a0103020f0705010b0310061d040c03121e0806090c0c07080d050c0c040501060504031407050603070f0806030c1309020112020a030b1f050d020c03 76
    0x315440d0704010490391448074401c19006d441184001e02c0c3c0826081d00c28201514513010361000b4010031140c00000360b103c0c0e0100e4144001400e20980c4a0b80c49150080c042d01e0a60802403190151281340c0c0714a44080c443c0c07008951800c00d501c44440c40600c07009501c0385014000380c4084404441c00f00c0411000460a50600c805981d001551201d00182525000007001c5000c10018a0000d00c11160307244512140c00c49511a40387e56218008c096107468059a5444000b280c0030b0030510140c2076801c00090540303107811409840502c0340c660304200840d02d09001d1704002c2902800f0920201d288041040400f44e0400120b6550170745a00019040b900120740301d400207a075040c913610101d0360040d02503030402c0c41540180400001c180002c1c12000b0b54103084203445603039401240641e803284004084482e8098000c5640e0b01c02041700038090070200c020103008101c900c4014140c801c800d00c88112601c12661400d0811a0440141c006503106400941c158403042c8040a10700c14103075050b107 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 377941447 1250 377940197 377940217
    0x61311100314010611060c040e0c0c0c0411030a0b0f0d0602090118151202191b0c170105090604030e090406240303030605030d050f0706061d0f060906010c0f0201090b 73
    0x8600c0850b6017203803600e0001c0040203908243c205000402c5640d01c0284100e42240340191074030385624800d122185414100d5941590040c241070280d004015100002c42c050b01d8071081c1403103251007410074404240500800517401c242140c4441d8003207003941d409410000700514002803162005840d4106a00c110381024203801411003041d074255400400c456400c40e0fa00d10300b035082402902c004044003034001030002c1030028410840404030a285041d200c00ca07030104003060000e0311444420800c1040301c0c0c1021856182c400450403000300011007501c1240e0660b41e40d0360704003c0109010100601410403540079850755000c2d503005044081c000c0e44100c404070030b110302c3c2c0e2460400800391812030b03005c14000e80014220100042c0d01c10200c440a0300804c03006940d40c0780c1860254000c241503444900303542d08464038100300142c002d41881c0520709840307110784552905020841c16072020b980c042d0104040503080c000040011b9080c2800d40c1c014100040e542d60360755180165540442015 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 377942697 1250 377941447 377941457
    0x4030318060b0906180402010c060e030a02060603070522090507170c0102010c0306060c031409061c06050a050108190608100e0615060a0503190609020c0613111003140106 75
    0xb1241e50a011122980c007a80445080c41040c078090071081038004007400103030401c20024540010310069400c82d11200120004482c0ea40b2070b48400251160790030703510b183c840d02650380005010300d050251901c0400380760795500c0940104040d0074006000e00748046449000780c03100010340818003201400d4200d0b50002801034001880002400c5802c2922410305141c50000c1c1030140d19485002c5140b1180e050406040e50100e01542c401c0c94010200056409040010072100a54000c098bc2c0c1401c202510300b1b000c1c09454904014000c082d40c003401c0d00080d03d600001c0d001c190341e18401171003001900000108103440b0b140301800c1040e001c02c0f959501c0c0d125a5442c00c859010042250b00070010010042c148071814001a1107101e001407160800401201060300c1010068000e1100416400100030082d900c0078440b020b9004008045581d00960000521216036a192101d80c0341c0d010b0f2248048036151300c10407051008500c1002e08051350785000380d0030101502021f0b4083c24550300d031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 377943947 1250 377942697 377942711
    0x304081c064b060f05040302040c0c15020309340f1e0806520309020d02130603020603011e1a04050121050a0b0103181a0403031806 58
    0x251030980c5035920001c0c100c0d20400700303900ca0b0209010740c000041da40030780351180c0807444214040b6914020741d040a9031091407d0f05002505800182006440c0e10030103203a1581550340d0400c408034041112040f80304e40016541d0352898407a0002c42407229805014442c6421005a010610080541088031502c00c2c0c0d50301440b8410b54902c04a80c4501c4107508011024245000342c4e4880d00040c0016084000c9248081c49103803210a080255559071184104a82404c094445a810901e04194904980c81c101440c1080c07007401050903a9401074411a0111019802d100200200352501c2c840140d4034440480140e86d0000150300034421042e40108021481408080246807603100b841038103406010103081303a0348030301942c0c1211000d00307048104403480c21200b032090400c21511b0559615203406c00001e030b181c9901001c90348500303036020061080751019010140f400c2c140c01800703200c0382041590854001101255025220345004a107145190060544101c80031408a0707405448050b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 377945197 1250 377943947 377944019
    0x6020c060f15060406090b03060a0302031f0c1716120c03020d0c080f01150e0405040f060b030d12150902130602190803040206030a150f030c05060304081c06 69
    0x1642d054561044524034601031030620054090030442c072481c1c0d11124084001190b82d81c425004000654001d0b040d00d00900f400e181107884030ba1503142d440406450404440700d038a10031042c468095a00790100f043c0c9486052040961081c00d1940108001d01d00013000200030503409810203014490b100581c98260403200d0506980c0a95040420042c80740e08101e4403510344018641100c0c0e150100c041143d110b6601140c1da4144405032541041c101014002080080e0708284005d130300804080010350320704000c240d01d0f000d031a030039117000031000403540300000c0c1964009400c0c00c80c403500c02401c00e41c1d00d03008481a81c102d80d1181c190254800010420359405024161081d107000b804041911201e42d10b1000e50301019001900614003c000035512507d25031103024603103888036040e009180e850700210803281301800120340c8000c18400c00140360425009a03802237901c0b4003544d0400c40d101c0c41c80d00001c400840b001e0340316501c5200010300001c240d4080d20004880e440391102e01c2003040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 377946447 1250 377945197 377945221
    0xf010e1e150403050d0b03010c090914010e060f0103090c0906030c080d02030406050a0215090c030f030c070905040c0b0415030612170f040314010207050c01090303081306020c060f 79
    0x26400000c560020310900004540001072198030070ba0608003585ca41000240c1040200013015083e5015881c1054030114541c01015010031504070250602c2071605040c031003000c1e02800e00c240048840b514012403580c1c80d010010f40c288c0d070070624000038103480e140c84007007a850303090b031080d4001589c13441c0900c00c0c04181c1c1440406482c00030001d142507903e284c0001c0d5288280c0c480c0904002c404601501d2043c424403840e01d20b40c41441d0142510f08040c0003060f2075110001c2c28600c240328140202d00711718004800c0d508820805805002842d103403030214805400014011106940002408208841c0c040c014001501000100c03840c61040e0010150444085070081c080a5a40c00359400003d11920201c8052144069965444004007132601035140502d820052041c800740481c0ca00c111015030140880600400c212200a100000191201c412600000c1c1c009554440004c82842041c00514020342c030592005140c14480082d10303003806400d0f10054a0200103405000340700d001c0d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 377947697 1250 377946447 377946493
    0x70c05030604050303010b0a120507021e12090d11130510050f060a200d02010905071410050c150f040201080610050a1d04110307030f0506010507060e0f010e 69
    0x640c01040c1d02c1c1840e032105a0b0741d000501c29482c500798005a8490168852880c1402ca804400c900344003904082c0310103504c0d05a09509482c241c00c1416080b00c00080001d006885d80c19030744601490710001c45e040c040c0c0302c40c02101c20758150103c03d02100c49900c5100c0c0d112032200e590b0800150a0070007020040800015520980c442c0c4d540407002d80a6550714800c4030380d41c1140f13082c45400b6900d5482c0740c0d00001d0014201009038020b01e401b090300d858040d041403000b24410301c103a801040d200e510302100e054040010341c0d00186070394002c0c441103020350010001b142d548002c48040034201400790200440071074081a0031a0f030f00340de000465030080846900300600321010152000c412100038401d0241007948010400b2030001d01400710f81c82c00c034006240350040c105210001d0703500882405a8803e84480300000c0c034140146440e0303403c071303c41c0034014a0305030348a501d07144d031540701c001c0038204440420a05020344116100032034424840c0d00b003a070640f80c0241040008841c03501e40d0f00400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 377948947 1250 377947697 377947699
    0x25080610030201050313060603080c0f011104150c0318030c330e0d0203010e01140a0e030f09060c07080f12180d0f0c0e15011b080913020f070c05 64
    0xc031000a00050ba006010303280c0c05000340c0e507080c041d41002e0421801500322a072000d0811000043d10319210a000b058449075841108001e200b400200c1841e450300b44610700c0b441189419007007080c0d82c118403403036043c1801c80c0a8501046446a4550a2069003525038401c07500302c010410104007100c904c0d0510741c881c00d41a0850748801c1081c0f005031410940400e0207804005a800f8881120354401d48840d0300c80b900a0001c01801d0788440e4114001c3c41040c180d0300307e0054000008020012900500940382c40d198051424075122601c100310036002408041da0010302442031391000c00702000308a0050200c0f00c0217020b2030406195590070480140c00c0107224040811400f01400d031002e40c4090076506c1a01e02c4030380701c1c0d603a04003911060a035100c02403403040400000168018001201c44c0a451122078000f4402100740040d00d100314030440f01c40010b02e031103800c600880d000002401910101609140703080ca4020345103c200da110040314852482e000c0380700301c20700044503004006860 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 377950197 1250 377948947 377948971
    0x305010b030601091403030c0f01090303050105030303073207061521080a020a0c060306030209060901080c1210060305061e0403020601030b040516061707021603060e250806 76
    0x70948002011201030b8000e0102d40416035140174004e480410889034841e40c0c3c0404d550704c0e4035545034900c6c068100c00700c041d0006402c180000c5043d103008000c4900580107034440030b544551001c0c0080c2084138100e0500705d40c03804148800c080d540c100005040b180d1147e03100003552032039120640d400c000b1079004028201010b010281c51a80030304d58602286d43c12901050315400103600880c5030000100740105034140d0106e00148407500b5800810507284201d0b01c0c600f4039030f40c00c000d10402070000d1103806120b50141e403180f0f0707541c14406840443d1981040540310003403412440c081c290350300d42d4001c5445600c401d08111880d6800380300c07441101007040000d0240e0501d524000c0d52703000c1c18000a001c11030602c021074100001000306101c050083d52640010715030b03c100240c503003021000314640544554001034880da10105010705006c5640010030300403401c5491b0300000341414080c20810f4030a5041c0303c2002c0d03201c0310644803426a0144d00e4001d160500203a1418100041c142880ca40c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 377951447 1250 377950197 377950201
    0x40605180307020114041a04060e0103020901120b0a030503040b0d0f09020307180e15010302091e010b0705030c100e1005011208031e01030b100e04080301090504170301150305010b03 80
    0x326000c8110390388182c0910b449104085c940305545000c3c8521362242580064040450f01e4070030044000d0400c588a17030315103400c0581c464005509030300c00d220010340000c0c8118007e840c5000241d000924103003010b0700013600140c4075a103140c6140e1041e0400d40284c00003003a024961401e5014114030400750103018444a0f85036404241d40e003c1d28041ca8903d617420398981c450940c02c0781e22818140d10b0440c100c1c1c01045440601a003e0413080c0401d86c0150000000200030084042285410311541081e941040c0e103000250700f82d580026000315141e010410660543c0d000c2080f035003201c0f2449100004006104041081c500121340d900c4040b040d0401004001400400343c650203c0740d04440c515949a58030280103440f00c2d1040c0c0e0400c81d003511100080140851400207034132904408034000c0010340c4a40482070916411907005055800810041c004010301ea000345401c58480c076061502c0ba41c02070343c04401c503007090704204107003a0680b8008959a0341030080c81c0c0108070082102d840c41c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 377952697 1250 377951447 377951491
    0x30114120a0b06010c05011b09170c010806041112060f09090607200102030405070504050901020f19020c12030d29040915060303050414010201051905040c1d040605 72
    0x281ca041e01d01400c2c0c0960340700050080e03402016112843d55001300200010b621440110b04800b004d8040b850000e8200319000c07405e400c216200c1c420a40512380289020503480d80111042240100003541154880c11000001c9082d03001030011091000b404e410030b40361140c148812040211491481001000103104140078080707802a04050725141100310604046007005250741e40080ca41010344c4004108814032402040c1c43e8180d55045800740200d0300c41c082503d0a0340110a041c0f03013681800c1001d60610b20415039624101103113801a03401003803000340012100306c842c00b0710b00590340001400d035028410b5403207414003560003904003148207202c0750102c01c4010a000b5401d800f0b1503540d90000c050100c09200301e150a44509000d0000300e07224a00240140c01501c680008880045280c4007a580103008080c03203407004200c01c0814404404100c4050301c0040c006551607101c803507000ca03e00c05003041d00e400c44100e544800d540d6050910b054404c0f124000c2c0200c4810281182e00928 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 377953947 1250 377952697 377952703
    0xf0b060f01050a08070e090f0a050709080304091a03030f18010c0f0807020d14030903070b041203050313050307080c0d0f09090e0304170703020112021606111b0303011412 75
    0x1004141c0c900035039145d4643d901500c80c0800038036600c0d40092204204610543d084040c6442110208020f0003903894407041954981700c18080c03014250000e010600007100c2c540e2100c0c1c030003e00903001212007607401010900715400500340f03c510840000b4220429082556481c801d04002e103030101a010107030321403685003842500000c1440c0d00002d09501992340d81800c0c14152500003400902c0303005021074041daaa4400c004175400ba025640000034580c0b1910142c8089500c00701c02071403d07001540d41107e0355030008140785951070f00d005000700400c4003040075155181c03080b81200d6551030900706081c580154171010070104000307500040340701c2d5070141d4444122150214041021580080590300318043ca4100d60b403c0455615801d040c20000600c4008a078000c2c2c840d2210f8845903001d4505a1040c0d448c40e800c6052090300380030020309513038072000750b029034a0512400c02c4900e00c40b02c0d2240447c04181d961030fa001000501051440003403000c0031180407222a00d548004803d1070b52 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 377955197 1250 377953947 377953957
    0x4120c0c050618031621050607030b0105130306020a030e010b011d010210050c03040c060203030c0301050f0f0303030f041209030f0602070507050604090911010801051f030b0d0f0b060f0105 83
    0x1c05400b010510342c001580e1600c9034402920000c00342c500b501080d00300b05034192194400e01d08119215070049020085d0108001191604000980380303503a40d640d42a005044450601410000100301114244640d0101e51010351303c01c91016949540d2948003d05549510072401e00d641d145c5460f100503a81c10854158515000300001744403880c1c2140141e00b00801c0308a03071540f06003400100302c640d0b4100001144110303c507140000d812030300d4a800300c1c2d0b84e010440e94000f00f28400c20060010b8500031002410700c060007000003945600701c1010a0031034000361021880c03070220070240802c11070507003d0020000b0701407504802540c95520b882c1451590110050025030b4001000c07018818140203075800350001920407031f503841d5076840c201c0082040c07000036a540c0702c1141a80400d98402d281d014121040100b50700003642602c10b1151401c48810194828144d460307450308442e0b11200c0c40d03900310328040e00c03049080081b2400d140a0621000f4142441100c050800c55a141c0e04032094817 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 377956447 1250 377955197 377955199
    0x3192f030604320303040b0c04121b03080a020604020a05010e1c0501020705010e0f100506010f0f0e031f050f011a160803040803151008011a1605010504120c0c05 71
    0x180040d004008107014840c0c01d28503503561408010080c4450f10000019800b0f01d2280f009441280e50302c000c05040e6002d107000710302070a150000f0440200b40024600810b042c0c81c040e132060032036982ea4500c0c0c0035a000303c6088016801c0350082109500d03008801c0342c014107081c20b1a6a81c444c4820000d62240444c5000c031241d04104104101400401d5042e41c0d24260300000030406502120012995031484201c0c43c0c01500c69111490300c04145401007034045e00c01a104c2e00c00415101c501035071580c986540d00800c200380e11540c0d03845a602000004d10490180581c400d44602002960041d10401880746911082c07480040160001e035041100c444051920385549400c6040340740030503038000314005001d0703400100500c010f0140800003180a034058000c1c0c07060b941c44010900c000c41280c4011440400c0306100104880b00485449209111074891191b01c0d00c00901d0624159015180007698640e540e10204410000d20800403020a060b5080c41e900b1070290382e5810a070650750380106 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 377957697 1250 377956447 377956463
    0x108070809100e150a090b15030307060c0314070504060906080112081e040311180603100f0e0a050d02060f0c0d0908041701050403081305030706050603192f030604 72
    0x100d81900360903c04220440e15082c0c1c41c440c5401e04c0328001700a040c1d01002501c04145d100081042da280ca078004180505024000d14240003040d1240e00060608851b4141410386804958111040150170b0900c94044c03615403e84881c188207004009503403a070000c03c00d0010b14001405685c1ca200761380350322264807418059892050340340462054800c0c006c2d55081c5000401c010013003004103c140540e0150a680c2e51540c02810001e58545030360a881594051b08100000194a142504500760350010b89001044010a1900ca20720303160f01c01e00306540c2c0c1c1d000001d038080c00c0359041c0000d9030841c2c8035000a500c81c0c14150032211f42c030720400010140440d941e221240802c00b819003514000c2207030381e02c04403440c08100c400c68041c14003150120001400b840008881100d0891802c0c15a50000000c0d8282150b65031023000038000501410781c5841000102c0e010350008054030503805104603070042070250f420410000d4601c0750f0890503800c0884180341403e9440001e40c46510030b41055003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 377958947 1250 377957697 377957711
    0x2040e0402090c1209030a120b0913111513290a02010f09110a06030612080913051003061b080403080604091b1805060904030804030e030a11010807080910 68
    0x1c1a21541304800d001c064060580041014084004c009482c3d103041c0d0351543c09000c0c0c2c0301003101c0d00300c3c0c003000c0c52580e000e48410080b84584a142820f205258425000c10002051183c000b0340e1103c40340350086c01600d80081c2c0c2410a2400c00300b010010301c0840c81000c0b41d000c415000960020b004006103c003200d001c85e540e044103200b5000908a019440d4080000c00d0359401c08020000d0080a0705000d14000000003a8552080c030404003100c03c40203001120181654449509a0118414584c0954008001416141139100e064000d0b140d00980070040782c17561400300240c0300180c88100d0254554418800696000041300750f002e40d051620341d082d039580c0c0300010005d005280e03010786413194020028070104281303078001e0240d40c86880303402006083c80301c14005807942100c5c5a5049120310010500090050400603089403180c1008000c444d0303502e01281c500102503030b00342c803040d5102d6403403446940c0000360070790480640c1c648544103181c08801103554801f005d03890410140d580312 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 377960197 1250 377958947 377958961
    0xa0f06050f0f21091c051605070306110408070807050f1017010605030907120f0602130306020d0605040b040e06071d062206110604020105030403030b100309060f02040e040209 77
    0x704a4844220034030112440c9800070082c80f82c0460111091400ea108415000300c40b107940c082030794404a2165209880e20207050522102c500310f262080741d20b80305e5030700d02000041c6103001b45c95203090002026510703070746422480c03840c000c0d00d9882074466400c40c800a020702e0b1603440c50b06a141c0c8081d83c4031903d032a00e540c03040380c441c150540305030480da25080000c5041e580c40002103008850700742c100c9500e44e072900c040812000098a00070f001448403410100001c501d50003502c5807030103510102c041c55030340791121402c3c4d80c080003009000b240d03125803d20203032800340b09000002c20160350400c002e0755030b15a4550344040250152080c42043c1030200144052201c56805c101d2004e00010748511034104640c040044070000500345000c1d010000c180c05220380d004420342c143c1e002c010035603511190010360382680050b105808041c3c45d5040c030003054689a0700202458121f58001601c0505410000b0031034496001c81d00003280104001c00c00303000030700d00482d0042c0e0100d03010000c81d195a1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 377961447 1250 377960197 377960227
    0x5040b031f380f03040510050a151814011d010e04020f1504050402070c0305010b09090d210606180b090f0108060301090f1202070f15030e0c1e0a0f06050f 68
    0x43c01e80d00040001044204500400c6044a070018980d041c8520b4580900440a840401001070305210f0740080412002c0d1003d03000309030441d041c03600050b01e014240007500001310309800050406008a26624500d603440ca525801031200c8800e516003420650700290501040c613804c103100b030400b84c1132a0b400741d03900d0080360003c01c0300600456072008207241840b9290102e01c003d80b000e52078510f40c846282031401c2460720481146015141c00744c000e0409403103800202008046894007844c40c0c9180d02c8052007400050f125503201c0c101c0c1b81c0031046c8040c1a80440350040a9140701c280704404254030f5002c643c0c01d0360b03a001d0030904000d94507000820300511161501420048018003070b6020300502e4000012104120307400e031184161a41d1312000a0f5141d0b00c100440c1c10351f9852180741041c4654419240709202d0800d41d942031510000151001d0500140e502d48110041f03441d2200c0d1524010041c020504800305d03608203890418040c0041c01038149000104000090303e8a03146180 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 377962697 1250 377961447 377961457
    0x809120f1803011802090603060112301e020c0a05011d1c140609030a03050c070b190c030e07090c05130e010e072d05040b031f38 57
    0x500200921044a001c1c4641080d404105074003486e0058041890380c100031a80307a0603034003503004040d00d040066640040c01c41d41d151048400311910031208081c048001410310000d941980d9526050056580e282e444484001070702c400d55011141112407911984a0041182d4090918401050007100c42c000840c000303004603907104c03007041f2546d501a000ea50f44865454000c1c0c0c400c002280488c035100f6039600d0107660300c01c0640d000b03202c9980558841e800066004480c0e001c260b091107038030782d19905e502d01c1c1a1810112041240b140050070441d82c402c040c4a0609890203000b214401c0400c152070b031030507000d0f806c0c61903104d900e640c0d6054062011a90382c50b0001c20b00c1d2650560f030b60b010046141b07080c000d15068101c09004680c6207840b882c000c814a0240c80302039100e8100c0c0813541c1c00341c00200c5c42c1c080c0601606000001c0c11110120141d0b02c1452000d09902541c40100c1a0310380b0104030760841101e0360301a5020b03015104541c10030413006c1c2c4074443c458003040c10110302d43c01c0034020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 377963947 1250 377962697 377962699
    0x90e12040f06020607020d080609040218070c11060405090a2f0901030b0429121624020714040f060816090203070f050d091704060809120f18 62
    0x10010300065038014070400c1c40116010381c1d083d5100394480c50030880c3c41c0d082400c002c1e0b00240e0f010f0046005460511000e60b001440101400380c50003001070721840c0401c003264860040381c4e40d070302c00ea418400390b011000c00700070040743d0282c6003d040c280091f009010203451720110594501c3e4101040d400b05100e4819410b09400d445181d030103035030380c0000550043e04e0050001c0c1c02c00d08103400d44c2c2071038090380e01e0b047d2000030b48502c0e203d28130680d5243c9011508000b9407048209241c02d4041da420302c8000c5d14801a60744107100b071420003d10240b10124000c43c4c0c03a5000c0124403011380c00354049411000d8820380c2046885800b01c050000f806040d5801c0421703030507450301c080001c40f03100004071881e4208810181e1079885654201e141c0803400121641c901040489070791454035803050009010701c040350440045d29040c551611143c0e9020b414844c50700e100d000400307000580d0000d00683c1d101581100406924001c902400b40c10300403805100c00c040341c081a40c0403103082c1d00e9202140120 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 377965197 1250 377963947 377963983
    0x90a1b030b0408130909020d020f040906020c010c080603060709030f110612010806090a080301050d02040642020d0806030f0d082d0403080c0d110d050603010510090e 73
    0x1440c3c201856240d202c03e0420031240c40c2d10100050366241030180c8110150001d000d0402c0c00810b40034006040b030508401a0302950f00c503800400211a4405840d40c02c1104000055558008102401f1600050703d654403c2c0e005004004100c1c1e4401101019240d111208520400032032034505d03514860340c3c41003030b40075002140303848080b503a03003510a048418900c116042074450840198a0b801c20314405017075a04204014052814039442c400e042074405440007546940e40c2448080c6c0902c0c0300c40c00c109154411f02c2c0c20340004c01004c84921500341c21108030440d03c146d1000030f0750b946410b00103041030100e00c00024a99a1b4180690300c000c1b002901620401407889800910705082100e8070060310400a500e04c1d200c0040d10704654034151280c2403035102c1d40b80e689040c1c6640a00a2410704501c40802940c045200540a894465040401c0154489080c1c0b417291050703510050240340a60301d00001c00040d2166540d40408861b0a00c60008030801050823560524140034a0842e03003032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 377966447 1250 377965197 377965201
    0xe061602120a0521033105011a01020706110c0904021c060501290906031302190302090a18030c03030b0315040b0907060f051606180b01050108090a1b030b 68
    0xc0ba0210f403001311000c56400c1038040740789000503503806000640708030546108104d1084042404961400b009500800d20740c010340180355103a5082d1500340c004000010302d55a060f00707643d6010031420340540b0303041c200811311280c021440c0303689080d2981040c0c41000c0c18804540ad5482c0c184001c21094018041040650f000741000c4000c1c000a110782ca0042c51001426000c110400d049110801c010003004c0d881c05000c4410007405410161407e8982d00451101c0300040e0380e2a00f1058491880d00d559040142c0f03140100450f000d001050104041e051200c41c010403480344440000a40d4181014800785489040071401001180b4190303806101d40f412502c50410741d410503500c614450a4004801d0b540d40020a803600c42c20300c221000710780046c10f15440a80210301a005c01d010000d0000303524045900c4240c1031341c0c8411626541c1010102601c1c0c2401a101c080da0f024000a00781070029080040019035900050300005c0c0070414114222042c50300980d20040c025038020701590218 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 377967697 1250 377966447 377966453
    0xf0c0206070f0302150c0412170705060f010504021c0c11010f0e010b060a082e0605041502011b0e030f0307050d09091a13020c1e07060e061602120a 65
    0x901d0702c410075400b5114484620b242810441c0d1014810300c044a0110b081a24103400407402002c0810f04a40006985500030007021442000d00030a074010b200030001c078141411215080401a08510b000300d0041103d68071008407034140400a003481100003800f007407208821180403d510840d04665401c000c00d603101d4451580080380c440c3c605000070041441ea42041180c82e01c40c08241c400820902c0e80000c2410ba800807003030646c0c060000440030b4820340003072440120b40e0960408800b06201040500020000c59802550094107000822600b900440400e8010b192410040e04100d0400f00511041d102030229005a9040e03104176074507090365181c80745d210700742854044d0014840754000990302c40c0c5405508980c01e00d110050a02001500901c942010184e0707140c80100e80811038440d00b500200045600100e6515107901c1c0f00d4021500c00d414601d0681c0002c0400120f10055641c0382d4680342100d4035001c2008138090304088034800702d810004000200c15140c051640a82c1c14 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 377968947 1250 377967697 377967713
    0x30a150b040e06090d0302090d0b040201020a060207030314060904051005070203040e0114010e150307260405100c0509010210090203070e040305030108011103070c02280617060607120f0c020607 85
    0x340c0d101d402643e0307004170741c100101e00b240a001e81940e480480317104400017181d40c091420f9040360043c41a500444040d460b80c0341a0b90280c0d0049001964810010742006001c6405541020b41221700f00c116083c01e49410350340f11007031984c07080642c0d91140403d000a000b001102d0041a40484a41496175200c400550942e031f00010103002c00d118181394811071400308001807140303800042081c00c607110b544080324a00b0348081d401d1052a202054400c0ca00c0d881c0d140301d48254424001804c0104030108160f041e10200da603000207121090291004580c2c0201d031615583e4494072000564119a000080c503004140d030000000004d030006010030f0680c0030000b035050b2180c0c10001d0250401c401800034092108030340d41000210510400c400514080e40034542190800032110307158141400c40d51303d00790081d03000320f02145120b8008000d1a0012608a6110004030b84035406d0907043e841c0e00b2032050580001100b00b01c84ea00c420000385000d030040f01c901da50050103c03900c136080391504c694 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 377970197 1250 377968947 377968951
    0x5040911150d0905011b09030c18020d0516120b01020c010c050a0c0803030a060501051c050a0e010e010b01020708010b01020d180e07050403050118081602060c0312060907020c030a150b040e06 84
    0x1221000060b185003494005c070034003402c4a5004500840c01441c00c142c1600c0042b803825003200301070b000c0040c5142c1440c6402111b0240546504002c82481000d0f00540941030411031161101c3c1020280401603802040c2d0407038164080c204006012441c1c6482814020300c1100100508030803100818a00340000207180300c1c244501e4108076907500c60005507058025805140003040b0301d011408618046a086603410084c407101c00710b02d01d0100d02c891425504020001c5040f0b17955944c7c19511582d0411040c4000d18441008000d0240d000000079102c180e501c100506101149511901403003a02089000412880420340c015081c400e800616503441844161000d40c241031050021451800039544444e5210380011301e8200441d0301c10b00c1900c0200416070707108030f013031086003d000303014401007045c192200c18180c0140b5003c0f007040075144c0c0107400d680c00c40d8013011034020307184c80014610764055000024400204c06400361034014260703580c84107030414246403c104000e0390000d1018 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 377971447 1250 377970197 377970221
    0x304060c02190c0620010504030810090203040b0c090a1a04090609050709031b05030601031505090d08060f0f130903030b0103090305120601090f080c01020705040911150d090501 78
    0x106500011803984000402ca14405410214000c00800c1418040c0340b000da035078440c03000c00801c9401801440da003107500880341074001c1000e020401c03a00e441071040c854043c0003a881d0840c03c60600da104e0b035464602c000c0990010790b800260110240e83c55011800081224100440c40c40030700410176501c94000b48186a5480c0c2002000710703a13000680030310752051070340d9900d41c490b480c9580c84501041801d0003e94500003a5000040307800c3d103003400320901031400743c0310340525010b00c00c040b01c0c00c44100800c04891034100d00e20801011b0b5015824030340184044400705423a10035000010501e82004080d16800400001400088440303a040382e00003e019840030405000d0220056090300c0c03084100400003801048503503040381c2c03035140080d000107041c540a04500c5c0c030340000c0a05000e00c1d400c0002542d00050441f062584e04102c0030000d0a001d5400b44950502e0f07644010341c50340203d4144d07119018406800c0006001c0c4410344090b10b082d5030051100900b6402c0840c001e20351740742d9003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 377972697 1250 377971447 377971453
    0x8040906150905010e0f1302040f081e0a15060909030305060102060708010807060302030a06080106120507050a050d080306010201091b08070e09120a03090204060f050108070e1f020f030304060c02 86
    0x4501c11401001c4442c200d940c107071a42800b05030810108040f0607180012540c3c4105904100c14403043e5a03c003410192222501c07d140450a02c402ea901e02900540c40002203e41006490610720300818000b85140d80416003004034580c00d071848021300455003015020900c0c11416000b4164942c000c41d000741020307000d45440c3e4598404c12190b8010034003540c1e075607510200040213850b101c2d07401940d00200d0040000b41c8152968162425a00c00b039100c400000a0001c400c418800280003c8005010031581c1d40c5030146010045001085100806426502c0c0800000c4043c1d000390007011645600044845820020580d414001e208074003410301e10348034007000802c0c2000c00d9407030070380101d043e100140132140f0940311000481c2e12603542a0100b41d02d40c40c0d0407006845a000302c1000e004001525044141400b00040080320020040c0c420070004280c40401c0c3c3e161b460b004500c040c1c140d0074520180c0e0300c0e200260f183c100d05105000d510302c000401c11080c40060341c0250401c000741c1d400d07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 377973947 1250 377972697 377972729
    0xf0c170a1205251b080304020a1e170a0b180d08090c0613031509030e01051813110c06011706070909051305030703080702060c0f07120c08040906 64
    0x103071003201d404840c01440c8100403000e08051460040501500b2182c91030200201001812004210b400300c00d400c0b203103201c0210a02c411490499070540152241c101e90000c00d0f19114a0740e0865003c1c0d218154401002d0a511481c0e4041804600d151580116510000b030908402040e0303c2055030545812601600d140c0c0740b05a40301d42112401048250b0041800d902c540d010080b041d80300c03580c4a112052810b000100181d03841c000316000d51284100010308540c581405840b07543da40201c00d04002c4100301458940540001907444c1c40020f5403100a5103491000c15402850700b4201c1c1e0b00c4c101d002056607003a2444c0000d406040c1c0f020100f42d1201031a081207a950341d000180c031103c01041201205102455660b03001c0f692181c13038540c4018605041c2d490b45c0e4190791100314141e00145901c400c000245404203d0a0b801903040e0900e1480d00310481d4007a6440d00521400a000540404280113080d1140d102103420b40c0d0000030340c65807155200c2c000801003540380b2860340c0322140150 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 377975197 1250 377973947 377973977
    0xb040c02030f130f0803030604180203190302100e01021c090308010e13120503060f01050a090911070215121b040605092101061a0a0f0f0c170a 63
    0x508010924903400071410145040780d10640c0350098071101030800680341c400a4120007845010b001403400802460b0307242071001c10b11090303c0007031409010320343c04090490700603100001d180c0903604180303012041c41040c07480c08034204141c408240c25001e080111401120078103500903c2180a1400c0c28911400529990b1003510300c55940540406ca626004120140b00f2000180d8050f0312800e000c3e25202241d87d42d03080b045600d4000038002440030040003828105600311000c05042424403e05104400d84003e260704018042e0514142d11804141c4024141a05444a05d90300421145001300356180108880e04480741e2500138409032004103001c032808072002200b411f152417602c0c3c41c0a013003103c180d0f035542c000d030411600600300c0c44194031300c0d03100c0e022400540260301c1f001045003850702d10761503001010301071a004442010080d81c40f000b0340009050b50019914104804000720102c1c3c1640e150704621400f8110520704001c00714644100c400500c1d41302c01c10b455107007036408600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 377976447 1250 377975197 377975201
    0x101701060803160606030618060b0906030c0d060e06011203090e1005040b01020c12030a031d0705100c0501020a0909110c0a2003031602040b18011401092105010b04 72
    0x201c108842a00100011040712060090b0561607078090900860701664030350301c1c2e204403a00c0070a9211031541502c81c9000300440e50045480002003100d0601e11403c0c0403000070b4a802140034060f01c1a00340d49008000c000304e90304170300c0580d501081035411541c0e60b001240700ca03c02610088000409180b000b140b4182d00c200d00c1d5014502078545100e00c9030038071040c07000401466a0650543c03083c0c200788541c658419101c1a40880c3c4d271000b039900c40301d06480c080c0c01d0382c46541e440341440c4480180c15000c11000a01842210800c560740e04c46404042c9055406500d458000303003c03540000790202e40713103421041c1d0104541102c00c080186100d0201015047d01465030100d20980010a0110204034407825080340d000d02c81c005203121440c0c0000003451075201e003802e140000e1400410101394541481034a01d030440569100f0110303850318522103041c07203050286403030040e04e81d01c0c0068242d218000200143c401d0b10041d40c4006d404030303001002c001d1066011100d82d802c001d040d44642c00d00e4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 377977697 1250 377976447 377976449
    0x108070807090f021207090e01090b0913030504120501020903060c12040b0604020405060d0608060f0907030b07020a060603030e090901020c030d0506040e0d050d0e03070b0112030903020910170106 86
    0x600207000d880d4205000000030342604070240801907001c0c0810003102505042c882e00868082c0c40da041e5080c0f0305595240b492105a026107500c601e4544480c0d69a103520801940c000c0020111f60b88058070b91a05565074000c94102a002e48802034403a4208101580180507008045080f504a41e403000b09001c014400c0d050013170400860100030400082518442503041640103001604040d10703080403d40070380107028044d002e030351108010020781c1802d22030190091070b00c1d0010051072418240c025a1442c20b440f0007400c107000800010019442400450034a03940f0400c144051581d03810010980010788078018840c2440300c0102e0b96218052084504507401c40c40a58200410081c2d1800244001000b0603081a1144120509000709120302207481005032a41c1e61200b040c280504103c2d4400d90301d80f07441d80d00c100110310126400f003c105045071288920341d4142d008628085a0b5100f580e400290084140c000303001e0003440000c0c80e40103507405207040c08401e82a1140310790070380b080307 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 377978947 1250 377977697 377977709
    0x30c140316060203040f0b0a090c0803210403030f141e0f0a0c0e040e030c16050105030109020912070602010b01031503230f0d0203040302040b0117061224040308010807 74
    0x70026407000001c1c190f0700a154441e0040f69000c10903042a2180b003a4007104507082c200c450ba172581c041d01040030784c1d03100384054019400214100022141c810303001c01d0302d000f400c0c00240b5060307002904240c801d800005100010085c00e0042c80c160364410122040300391210725200c540c4840b2101c070f18448a11072403140e103600d2801505621420481001015010105c07820000c407504e9801c126266030041c0d2440c14410b02c01160b90f15060400107013401c0d82807504920220105400300003607a80302056906603a05200c0040e910320f607900c0001d185000302c0040303262500070424005407460b010342c0301c07000051080c0c809001414150201c602d18200d140030040045403402e41e10407003a84040d00f080400c102c0801120410544030352258601030412018038016400090203104500300303070046102e020020700303102a031004448092448010001c003103c0c018540743c501d00115080c00c01a89115640e94000c034040f40c104083c10081e01d2804031b9043c2e000c40c8142000152001000591000303c0e40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 377980197 1250 377978947 377978977
    0x1e0504021e07032309220603140303060f0108040b04080906270108010b04052d3f060a200a03060f0e0c0a050a0207150513150914040612030c1403 64
    0x1c100560001000c6c4c40c040850a001d545010200010301c40501c03040803020090025600c07440d150042105410b440c000c1281081803050a210000d60f1025900e60000e502c9603003075803181611008600d45010782039000600245407640c1640c410f009000d2480c10b200213076a448110f80e00d0707008018051140744111900031444484c0721801409401024050070406c02d00701d40f924410200003001c02030304002c070a00303042044049007521045549071403c540300d08610840d00e01c000388103258482a000784a91a26515811a0720300140d4140f400016459402c0300c060b25412a5040140200030364000c121014440c0f03640130030085494004079204a001c01c0400b843e2100d000d00440303154103d4401c0d10b06500c00c09401041e04000440c0000060410f55030720364490040041034030180640390300081c0038002c12200f0741640744d44a07000c501560701c940e00440c00000c41c0400305c0c0c001c00450b13105143c4021383ca6040c1d0105940700c040b10860501565101021a0000684988034880e155922000c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 377981447 1250 377980197 377980219
    0xf0e01050d0f060308070b070201050915360114130203070b0a120906090605070309020102121317070609080c0117090f0106090c091e0504021e07032309 67
    0x8050b03004406140a0030b840881c100d40e507a6218030464200c040101d40c004000300030080525030921485a000d440305004050400b8803c681040c2c0d6030028005020701281030b800403050800c00085541d61405014945c20b480c00d4002c4058020021114043e6108a00f070340410407400201702000e81080d0024081c107100b52900c1e80111582c2e000d05689403c3c003040c0c3c0030440f14255a8840c1d98106800707150003191490661510307000f181c40040a15042c11b140c0850000581d03030000b018950041c0a000d21079540c90809004840a4100e62001d281d0101128a00f0200d52001c161803040b55840e80303d1004403903c03a60071946810040d0341060008500c001446100007044407215080001113082e10640940e0810660958032075403c01541191126800301d1500c0c0c0c8601c01030018600d000206c8050848160401a80b100520a0ba48600c0e00400c118100c0055402001d668204c00e14804d031b607e04184c0b034080c0a20000b04800340f540c1e04240251603407840c003502200c41050004106000030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 377982697 1250 377981447 377981467
    0x10c02030f04060f023405010c0f110303090406120c06081b07140303070201060e010510020714030c0a1508010906060e120111070b0f0901020c100911150a0f0e0105 72
    0xc21611312103c01148100001c50410f5000070902c98000841407031120704298a812a04440b074800741d01039410000c0d000c0e00000443d000c903460401d07080e030003d1102c50701c1004000007032031401109802581f151510000140000240c0b03400705500740701e110003152259455a080d507942808a031180118002e035039941400c2c40c1c4100080001c607105003102e000d00105800711602d1030b04104e8100025070354808003840454100e0140a00404088071170303004200800780000d456600500c1454000400801c5060f8071f55014444d440740c0401c0500759031604c40da110241c0c0e40740d00e280900407010907008400492101600d02501382544c04917100c55880794160000c0c00030800801c800c10980307540c2d9245d01c141880c003c20003400682d00644050416040c070340240c641041c4090098002a0300c104004001c4040100e641862009580c00c00600c402c41da042041410070300390021030b440701c111070055055922580103410141c190340c2e220002c055a0403000e588281119041c1408558140042c9400d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 377983947 1250 377982697 377982707
    0x50d050615061b010c030b0604050f09150301020a0c140a0f030f0903200111010c02120706020c01050c180301110412030311070302031c02040506090f01030212090304050102010c02030f0406 83
    0x3100c503000d8020b0b8600a0351080396a0682d5201020411594607480c00303494166242c010740300c1c4010111507c6240501e4a00000c41180081501501904c00340c00010803042031800115075004014000b590b545d100c1c040300074500d04041c0012070303132011060060000c0800014070346450b01c4d8454210b02c158031854a040c3c1d80c16440c088a2801c10144640c04000100d41481d1080c0000484491515260a407000900380d407002015148480e071402e18503480b155400510b44040718481c0340c82e550707160f0660500001911810f2681404c1c0d60074403060002001110000340b10b0400c40c01301c0d02c00c00181080406090780c409007559286400300340024048460380c2e00c10010100d1207403e00140314021240b160600303800041c415005070f0408903040d803007107158609856440c079098004600d094140300c0011028001ca00c0080d000b000600b0a240b4240d003c0d9044074950085031100da0003d15044c0301c019547d42c0140a1180154205404850b4103070001040c0da2218030f0010490b4282420036800303d078 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 377985197 1250 377983947 377983981
    0x10f080304061d040e010e0f030304150e070e010f05011b0302060106030203091e0609240406200d0e010c0e0915040b10180f03080702010c06270507050d0506 69
    0xc00c0c070010110310b014a684170301c582415011040004202a802800c0250600c5110704644d101ca400805c00c10001412150410301321070410176000504a03080c4888a01d00586500034401014001c00041180b000c070505460485000345d1701c1040008108495450085402d00000e0142e40440010701049010343c01841e400070f0260b04803903000b1111080d44030450b03201042c40c05680c1201c000d000800105100150845105000e208401c030b200ca44ca201c2c0c510700050000c4c120582ea0580f9401c440a61800e282d1280d40c640110b9071185400d81819004200b0b1103c804525883e1440d20011300740203401c0c100900c4001012001c19239200034a0044090703c0c24242035101e90b03075040c052070720756034034488142c901c40070b64411201d000004c4514050b01d50540000303d41c4e83c06801d003000080e0022003105c01d01c95082ca0410201802e51a01002800c1c2480c404c602c80c3d100f483d01000c10140740040d0405070341c010000c8a040d9035954040c48404955082c0c05005904104005a0010705082c4660 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 377986447 1250 377985197 377985227
    0x316030e0d0c0209090c0306040f060212010602010b030c01080735010e070810030f0201030903020705062110050d080a05070b0a02210c1e041205060708010f08030406 73
    0x3082803540e4000150500004880080100c0c66424000b000d40c00d04141556126903460020000c04400f140060307500c180051000b841000b220302080c0421580340c054030f0003046240003000c070650310307005d000e030182151203c40b9010344650b142801096101c0c0021501400d00c0d9162034140c0c240c00414503401d005400d1550f40d121412500d40f40186890030005402400300d020b41103664104107100904112020f0910080c8064006061010035880c07100c00c441c00da4242000102c6000030b1070181d0502029a02040c0c1c000000300b5204488042500304001421605000b4013850751140d010480031001c0c1d00580307402546820701000001c001c28000c0421407064186282486010f9480c0d20400e50100c4030201c1d503940106a22407009031010f2090a0303488890f005407581e14040f400f1920600070115603c40d0382c1c404009106401c090070b812035000d42010030080b84281c840341440e6546980544001000510781c0d03000164010102e2180c0090b5881c2c0005186024904a421280500d5940540d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 377987697 1250 377986447 377986451
    0x1140105090307080d0807090806071b020d0c1403010f110d0c1119022112090103060b07080a0f090311130b13050a05060f0303030a05091507080603070b070206031603 73
    0x10401c61805c20030f61200c01d9070341e40c81c9081443c000034010200c602c55440071403280d211200780f20000f07400a21906070554031400642002d02c050001440200ca1460041d084e911460404200e00b00300c505504140c01064000384003008400c01b00070104e40400341c0d503403000802030100c070080d01c900381c00005541545160900d2201c1c050300000d41002000000c24000145c4c41c41000c046081c140600480d030201109330005c0140001388880c1c89005481000c5842a00003d101c0c01681c000d0780820040c2450180140c2c480e145480c04202c9030344104d00c0400451804441100301d68880e0301d260050b0703035204480d42c2014103140f044c403c450101c02c4241d104903440b8101ca500d80c1c1c66407211720040c0702d0901e60210f09800e04c0b01c100c400700ca502422282c042c150500d0b015515440c00411a81c2002000390001016540c3c0e103d414281a02402065140030184007881240390340043d07040c2c0140c804400780c81d1525918a4000d28a00c078028000750010000d2000840213144c0c10a049403102840c100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 377988947 1250 377987697 377987699
    0x2180a020c0d0206220308040f0c09061214061e0406060e090c0f01020705150d06150206090c010e01080f060103060b040617010902040803030112051212060102100501140105090307 79
    0x1078141030561a61a0b4001039001004103c9042528003038100c207402c0d544406035221060761401422008014005451a802445e0002c10403c107440d02c24001c00200600300700c010b0700c2e0501070f000d55400040c103540107900d1124180c1c1040011955601071501002003405000d542003036409144c10041c0241c074000d03511304001503200b114900b00340c41042984043d00c1d003041e1030000c00c912817605424075411988001e500f0b1207240c4400e04170b0304048a2801d05191600c83d4a0040c41c042c00881d004003190703000c1c085c09802d170b03e80c000070032a0064030407a081c0d81026040c0001151451024041c180c005800e80d00412014504184150340200c818900402c0340ca48a85240a03103501550180740091260a4480f2541300d800090314054005c8940c19494246403050050b940d02042c0150510520007002410400ca400c01914511582580c1d04036286d144100441e09000710480e41203016000b44269074070701d000b03030b841030505803000c0300c0701240325250040c01156650080543c3c1ea80511038040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 377990197 1250 377988947 377988967
    0x3060d06141003020301140f060d06090507090b10030c050307030f090f200607081e070b010e060901060f020d030b0a09050a050a0b0604030c060c110d060b030c030a02180a02 76
    0x14214451140040344510b014598814182101e0300d80310360390f40c1480c180050148819020b00000e420040403034080c1000301441c00d18030010f00d00740340002c080e80f08616000440101c5900005202441203c6090700c128840a059098903005010440055402c1000403885402a44510a8580c04841c001408102075495104c110b10000040d9490940c03118240d81e192082d1003c1068894103a4059080401c2591800158082c480074050920581103440003005a40781c00c0e203020b1034100410b4801e44d41d5809807003000040507981c040c010310040e000803500343d0090048600c459440e074003e00780c1c8640703e10704070001c1c0004440c03190320200715500001c000405000b154040c9119040c000303250b05060030380400300e80601d640075000d1003091104001050000002d04120340300d505000303a85081500d0030b0a240c0c1e0381207032403550085641880318117010960348502520380e015011141e040c17904004055940070065402507000484102400d841e0008003045500920a08009410901d00c44 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 377991447 1250 377990197 377990231
    0x30309081c0e0f0705060304350c1002070b061e0301020706290a06050f1303080a020610180207020f0406080a031b0b0105060c070504060f030b15030303060d06 70
    0x1102606280d41c40700d00390b900e418401e0040c00c002c0ca0b2408024a02d40e450840480c40b14080180302074800114040049c1400c18407401415440702031151081c0d01d400e03041810301d40c5420032101d20b20306101d0380442d169460900c3c402c032408950403018212042d62144100f16210000031403400e20480c145c01c2160745510709001030060544565004241425110304120900c2c2e49100f4410740c0d0501c810800110343c035000c075048181c821502e041076035505600d10116140c0b040e1114505081340d0301d02300009000c0030601414400b2031507400d403040b9072201b00d400c0308002c00602850040c98024146146500d41c3c960040c050f141c030291426496030040b10000301203540b00c0c1d02424040c0c010000d000c04040d4001d400f000b0380d804141c6100c5520301c65880c0c000004d681409424001d89000811041c1c400c1c04001060040c04014001d1060035103071b464889848600744030403160204071001080d070400c0880d44460280720007500442c2165106020428180d60410083e103580350f4454139081518900 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 377992697 1250 377991447 377991487
    0x14180418051009050609070b0a050705070f12060b03010c09051903170721020a060504210504090b0d082b09120e01031808030603030c061f0e0f0403030908 68
    0x900d03000603003030240b8140282482c90050211b4101e0700141c0091182040350400da903840c0d11180341c034988429903403800a14001e20358001c216281c0403102c00244070305200d02c45c0644188100b5007401002e000c0020f1500b615040800e08000c9040c51000b4001820652403504254100b020006040c5540e5142e44001d9454030300840c00210000030031070f0600c0100c00009131a078000c640c00c0022100c8410002391690760310b51004100b241c0b990080340520074500300d807030b49651202c0d050070b51031852203401410f036500074030074054600d00702205040c480c9030104c1004c403d0380d00504500d1030324141c1003540c81c0c0c03901e000541c0c00392001c00b00320403d44408580b0030f000700740744101c94101c26000d0035140039050000166400c1d04040c2046482c04025680c0520549426803000c0b07038030303203e444032400281940190490022244a19810062040a480d06290701031f11150421312165454061207444404102d880f86030380031040700801c0001c1d100ba8800c0c01c0305805110103600f40200c100900e5034070008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 377993947 1250 377992697 377992723
    0x21003020d0e15010501020d090e18030a030606110c060f161704060e090606071101031806140705070320010906090803060f031906020c010204170604031418041805 72
    0x10b151008002d45003c90400d0140100740000d058002148000030710070300c00ca010390240e00c00001c0119203180011211045414250025292140c00d81003009004000c1d900c241c5c0c0000c0c044040303580b503291000c2402000c903e4050090b5291000c0c900c07100c940e40c1d109021740c03000100003100f0800403d40344c01fa0365407008000914903030340e58034040006000aa80002e45032041d00d5440600c092075131344030205c0d88031a51202c030702d103040c4101400580041801044c00c0072030803480c224000801240340e00070314404200211203085500c40042c00c80c1c00340150031000300440c0f0400e001d9015000100b09043c0708100e16400810001d10342d54628095507803014003256900c10100c2030204902d0884000c000e420000e4008101d40110002c842100e641c0a050207403c0d507034002048070803242b0030340448020b0040441c86514018203644440e60700c2c0d0040b18107600264601403d1070040001307a08507200001c0d15100071000140c11000c0200400303059606800502c42c200010340040c80a020080789454 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 377995197 1250 377993947 377993953
    0x12020c16061e080c04090903140c01062402060105190b1903050a200d060905010303020c10020102041410020a0605010e0105010f0e060723030d0b100e0d021003020d0e 73
    0x600c0340c00c2d04403402c081a4010040c060440d0400640746001016142103c0310b652011414500a00b010340700a00034020780e03c80034000040300808414150013150440f15150050003050709140795400d1a8200e02001c48016007003580100814a8540d03e80b0607402030310002c46105030b640b106060800d511036014095142c1d00507601d040d1050b018403032954050300f4a4411b0002c5650304203400000740ca40700e082d12440202158103070220440d0f80c003d8020b0404407000b04143d584a00380030f541d50354200202c5104090204c800d035503503171040c001c0d6811a14038a04e012880b0900c481040360a00b58981d03688218420407e0007408114180500c82c02091100e21040c019410800010076202d070848508052011001c07041c6011340b01d810450f0807141d08a02110a4542204408000905440c109041031b10010900342c011445a074001c8900c903100703c59001c511b00b01c0e1f880655101c0c19414000340e10100961000000d8244020034000e6510513180040c90140e1020000c1300f102d03840c11401219034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 377996447 1250 377995197 377995217
    0x1d0c04050d05102a0503060a030803071211041a18010c0f061401080c0a0305060f070203090d0305040e0a0e0c040b0f04090c030b0a060803030a020913020403060509060109050712020c1606 82
    0xc1c3c04084d4050513081c10f440c4c10703880c52604101003040d010251000400b422000030004040c40c4c8aa0016003400501072400c0c00740138032400722a045500b240c0102440b00031001540306010a9010441e0b02ea1000b00781c605000c80100801501c8280c02c00405903501030890301c5040002c0e919110364043d4a13901c0ca80c180751541449070491030003030b20740c2c030843c01275200c0c030418030125000081b1558030184050700c0b01c0265131000c7c001c03805c50150004581d004048071100004140d0000090000c0d41d204094001503655883c000905070740300b0001e90b01d1550411307070340c44410f8100394003c081e502c0005482c80d100d02e01110003243c2140c403111015502e0b910081c00500402c542e014119801194603081030100f241000d0020783c8910001e03041900c01a80010040510b0310b4441d140d0b0300b405503028046481e00d903030381020f0b00900b604030b0320a4131601450001184002661003510b004103650394030b030450008500342100080d4801004250705100d24089800b444c0d41000f040400745c45140d99050381c1c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 377997697 1250 377996447 377996501
    0x80c0106181401081902041d0d02030a08060301090f03030b0103110d02040303020606030a0b06011206090501090915200c0102090306070c14060403080703020a050d11041d0c04050d0510 81
    0x441e410b070081d40054120790301c1d040341c0050742400b105d0666012140014104010440b140410703980c001558400d010341d9001c0b04501c0d401202a20040041da07c0d03a05082c1d071284101422203012032070040482c00c09540c010b022030f1207176000801000c011705000521120908801080350003001d19002010b0700020203004241d8180301075900140d00b80c1c01080141503585d0740b050104001010141000f04e140c0501d0f281ca91143c12401c02402908010000c07561100c1074407010b81481d4809032a152482081d004083c0740910806403003410000f0341080c1404542050f20841e804501801d035159028480c0d004640d40610046020340115119070903c8065860300e850025141e20988003160021000c12001c80d80020380d4940c4400b9919005a440c645040d060b69107000d019038403480c40e49400b080010800c86030340140240c80001060104000f03d0013410070b0096012182c16681000900c0100311078280000301c0102d081c0704000340d803050108024988210b42c03c0c2c40d5001c402000f00d1050300c02d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 377998947 1250 377997697 377997731
    0xa0b100e0408040501030e0a08032401180e0c07061e060803030c16021c110a0b1309090f02030303131a06090f070e060a0206100e13080c010618 63
    0x14200c1088551041c036081d00c5a503014000c521070340f414503880e244036810302241071050a5617140c7c4402c0c10b07501c0c3e0070002128102c20300c90350701c2100015100008042258054018940800f03030100404105074180180440d0943c005842041c0c4d00c082403004000042e41030240104030340302c1610b02c0614445c1504040c050f15126401075031290010400d000700505400c0c1112078281581e05528444a56440030070310104008100c800310664200c42c034410842d08010954020b42c0880d0404c1c8059241e10040d109440380180c00702e14400203180400102d5101c0d0003812142d4002d01211b01c8040680e00424115401280c51070323001c011020500e0200610301c149144010b424428200c0c50781381441c042496480003800310582c60b0b19800004071340b01c0c403039002011120300144c8200d4840102c2c045c042c1d5100816601c040340410f8240020460800c3c4414886c4a6200382c51110384038030140e121740c5155804205e40300301d99505c502000c903070743c5076900340c0c1c00907216401da000800c0f824154002131 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 378000197 1250 377998947 377998949
    0xc08090105180316020a0905090a052a0f031c0513080705090a0504060e190b0105032805030c060705070302012004050f040f0c08070f110a06020307110a0b10 69
    0x20768a10b852196a4441000825580c00d02d03107000490900010303a00000300d58003400d41c00910300d14280010403038580404108502d02c9071040c0d08981801c28022000030059002e0100d50005081e40811482c0c0ca15000f10a810300c203401401303652041c120786140e0080704009468540200b0400500e2070f02e00070680e021800100b00c080050440d5900741760008815080180007034008079210000304041c460150f005041e040b00c40e108a505104c8160700034070301a00b10003000e607a070758070040c00010b03030381808a011490814000000501030111110320695034040620540d024441400002c078103003070400140d40281f4040d1585525132110b032400030700b901c943c1009152805400809038071b00b8000c49060b14261001115200d45a800c020f022500424041600207446400c110309200440e4103c0311660044c040e941e1140031009000b003043d107005580c11013020469008031248808500b09502640e0412500e140520074151300c1803005103004090b00054441078500c209114000d00ca03003e000b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 378001447 1250 378000197 378000211
    0x40302270c0a200706110601150503090313030501050106030b04180807050a05060903130603022b020c100501030611190503060f0916090602070f03120c140606010906211508010c08090105 82
    0x1f03080d40c14140720030300c4200201000d41c00e01c1000b0010400d9002c0a0060301c6e8a02c503402003000b0f01c903541c2c0c10032601801003840b88001182c607014017060300d8200b9010741001204440c8000c421105e0960b100089940000401d441501582201c00c001070028004203009440b4100210f480e1030444004544107106940900241881000213070030002c5107010110040421402c0110340d04807078805080a4814841c02e0310640c010076000290301c41c3c00d5801981a80d01403181003118203102e10743d802c07240c8500091240007403426000c0d103080c00d00c203000842d40400b020304000c001c0c03c85107000ca60109030a90b400101001e92000124019500c40e03403150081c040c51004054640c9000c0028928030203500003c3c220014a0121201e00f42c001d12003569081ea11803980c42400301c00111481e202c060540704980010028500000d11074811000003044c0381030b04110966003402e0504950040600003c91484001c14880001d01c04000380700c0c8101c0702c41c541d1a460810314003080304508552001f4844 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 378002697 1250 378001447 378001453
    0x50615040806150406171c140409110d090501022d07030309080f0c0706030c080705030f060d020411070c0b0301081c03091502040302270c0a20070611 66
    0x100119040010b0268108141800103042c0d0030090380410003400d144d402825810041c01c0507500d101c88001040360540b5440d964031500c24080351801c41e605483d82a0340c000c494000d00080c061040594000125084074a00003490014820a003005541c0015010790312079501107020303801c0b0400e5800c01d03002d41c0f10212100c4440d28020b82a01c8050145000103400c041d40c0c0e40c620420084400d003168199a69a1421500e0b594440901e039503034035aa0082d040028109540300103400c0c0990141d50282c003031611078605642d52421003220300c0c00c00a0010380d201d61a103404401603222031107903031200e903180001240e031020503003001c062824549e40b1031840b28204000400c4502c50101d07811015068162203410100403622084000d031541c0c02d0007609400806140c511148a158001e00460344203480c04000e0161010665601c0c1400c0040340307500c4c0041c44002005046100c0003001c0045a50506440c01961a405c480c1ca03e11000310009107a407040c80280078407600000c00781107001c40e203001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 378003947 1250 378002697 378002699
    0x909064a0f1b030c1312110307062c06090a0f1508010321140a0305070e0f0d020f01050f04090605090f0702072303010509060a050a1103060d020402040b04030605061504 74
    0x44031002c2d00c001070041c022a44041403625004501a480c207004044403a1001d051460500307081902400030044940300b48136130780c4000ba8a60188040100b20016442e02c0200f01c1c0950030550512540c02c0310b01d682c0a502000540041d81d00c0147d90409004450300f0081042d0030700000030003080d140d0301004107101c1080d0040001402c1c010b4424540004412900c091109800b4140d030151044440e1048200011a401c4403c940c1940110b1240c41c0680c0c40742c100e00c81c0002030182c1021611802c1d50000c0c548407002015080c0103070100900e0350189840e910b4004080040d4140e5040307500441b07001502d402c000c000a18024400503006805048050068240740038081c0d51507802d07202d26030042d8010310003185049031148244100f81c801400a10407440c01041c0151168411180044480e25110110701045010321030122244240743c5943e10710b4a64108014840c3c0c519a0101d034082c0d020807000c91049515400b60000b144500340108030303414194100325040d8052101c0030010001400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 378005197 1250 378003947 378003991
    0x2010e030301170106030203070305060610030c0e0910050d11040509011401120309051c03020106080c010203040611010605060705030c0c01050310060309030c02030318010909064a0f 80
    0x2040724112060408080c0054192180003409040710743d101940c14010954000144103012401c94420002100c810300b0f0f00e041c5010560032504c0c04844000041e5014001410908014126603004118030395107680da260b4400c0090403800d41548100c80c030082c03100340e80700d075400c01e4001c0c0c1350808403e00003801206440d5100a01c500014441c0c584166000002c0b0030a05010351540c402034180500380c0000440d00154800503030241d10001c070015032804100051141b0f0106100e0320f080016170185103007900e050003c030342441e03c507007401c1c0c20340d50b981200003010341e83c000080a400344600003650700c0d40d0005c828281055a0600e83c0d030706100041040010600506a000c42520000d09000401d20100d0a044400d02130320b00c4000d425110000c0d6003105011002d4000c50445030076603800b641c0680301c2002d103050b1904c030320a075100444a54038554042c45600400901e1a410b03203011000420881240041008001100b260940b201004d000d1444030050f40c8582c002e010024100003819246 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 378006447 1250 378005197 378005203
    0x1050c07170d03202b0501030f0b1303020607030b031501030f0c170330190b060f3106030209010f031b0807090e150f0126130602031501090602010e 65
    0x11040440400f0380f4500c04400c21740c00c0110a680072000348003000070f50f07120f241014100d000b690301500c014000d0400100d00310055403001040e0359041d4090115a1205401903028001303604045505003e0020b28100e24801403900300c0c005c6018075032819409200781018030300c941c06500504148054140c011612103000001c40340c010084505000c3e07030280300c00036131b000207000d40e2400c0e81c0c062501041c0110b080400301141004840c14408200ba00c401e0010001940718041e50380c10300e26400e000800d620385401c24084003e07107a03605030ba020200107040c00030a08981e0b41100b07001ca0303404100301400d0b592000d002559101c890400700110070400107680c80a400401a13503042100c20305c0003504c030b18858100c2000038268034032050300c3d0381441c1001c2c1017070841c48007615000720030200b161803056204000c81180d969003407100e8803c00b05070f07604841d000710004080391141080000c4200026880c6e01c002d511905441d800303030411880103400180b03200101d82c0500116814185807014080d804 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 378007697 1250 378006447 378006457
    0x1404090204112a0a03080c0405030a1a01090c1707090e040624180e01021909031118040b0402010315060206040b0108070f0b0309010b0d0b010e06030a080901050c07170d0320 76
    0x17500709140b080c0d44000d2858424450b0380c02450309070040344105020440c01800d1030648030740d804400d0005e0f82c0c0f1024ac0f4001c5410011114000650000c0104160380440c41c49a400010b2032400202d00ba4131244001c81d1040107441c1141c4641d0385104550010200d80b0f24080c00742802c90415800510302900c044840b0001c60215601d160f44540c1c2c3d0302003500940c100c0302d912a070b41f202c18601e10001c04010700072109501c0140d407482d12005400c0c0061404aa0000c44088070b08900300e4251a03e445001d400c9100a1003207041c10390b5014107916040289161030018141c55000b4040c5107400d2500c0c4d600c40d0f006900c0201503070302c034a00c20b0100e0911450a00151001104601e403a03585d8119510702500401c141141c12204500d41c0d00140210315410b03906880e100742d03000800f5201c0805066a480d0001e40141400078244082c2e05030b5031080f002001401101d40807030b00e220361035480300c40c0f10183c00020104a94440c0792002c51403505409200c02010fa20078404181581c41650b945a603c10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 378008947 1250 378007697 378007703
    0x5030c0117072007090e010506060a080403020c040207080307021509030316120203040b1b18100e0907031b09030203150403050d0e0c01031103101404090204112a0a 72
    0x4800005410b061040c8608203e0101c039040c641e40b0310740740350903240d101c034094013414a0041c2050f8a496040f20140240c50041c0c40140556113045100c6c0c1c421a51488080d204a003180030740c480030340c4280e98500150048900550300d240d6641045c0c00c0107481c0c00120010448031213283d41c204552100e000c400e89a01c0740380c2e1170b02c40c401020020030842d03c481c41081800e0b1010b102006000500c40751070b0f900391065403e0362000070550b000010134145805800e50031021025001c0040080d810030084a0034422603504020740800f00c02030002e0180b400449041002a03500e0001c0056528649c6140741010982c1c2070503030450b4107680210792a030b2040d00701001841e48810106041603c00d0088950500e002c200c00c00c20030b0707a803041403a01d0b80f904541580c0003905250703947c25942e8840c0d04a034054490484102041480c24024481c6003140e24691036000303665070304100c05626140a20300c50b0010650034980d039000070ba06800c1024001030351200b06c20b41040c811007854000010300b1060f940d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 378010197 1250 378008947 378008987
    0x60309030c0204022b0c0305060d080a0e15070b060f0a0b09090c0c190c091a010804050c0312030609010f03260d140f07080c04140a09060b030f0105030c01 68
    0xa40ca00c5010317401041e40f003040118240d041000c0e030703a4042561148600031410b0760306000545400040201001c50003030b01034420402086000c15041c0102c88840e0b64103409441c170121030205080f401c580350040030050710140c5514007001000e150000c41d0700790402c0c0032103410f00114201800c0741c82900401400724090740d40d25001c104410740d2a0103485a1150800850342100d00358102903440c400320650848039152850400b15244600307004403d80c010f072256041b109000c3c1300d00119007805c0040c005450a0041d15000010340e142404105008600e410072244d680c00c040091000590059110f5100e003c2d40c60424400200406240000183d8202d40d1211b07007412480050058400c11803c031180034580442e0b5031482400056551082e1040d1055817a560358181080d520104119888000800100410700001d11009c805018154015151125403502e42d0101800c0702c109400129412001000f0025807070480a451401340c101a0050034a1603c5100080d00d402d401d0100380340e010f2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 378011447 1250 378010197 378010207
    0x20d0e010204080d0324080d12050f041b0b0309071a09010509090429040506090a021005070c170c03120a0f030b04023604050609010306020f0f0f0a09060309030c020402 74
    0x8200c0074000a08a45140b1081c01065910801f140e82d6001440c4000b01081800400e42e48103692886540c0c46031003c200ba062443c1d03100d85c1c0b07132000700070741050700c00e90044030310300210305002900c000c2d5119014000c0100380150405442201c01e901244403019111420401d08001c0d9a2101c00c0d00d208460660b0403408948440c038002c0c96248030701d05503100b1180414175526070000d9082c140c60003103021720165820743d2128180d85403900c0d6689000794010380c41d000d154896134840c0700105036080c0580c0500350340f240c07200344441812118072104400c55003d0074801c281841d040c05040c40702a2001e00c0c0798903190040304094480c04511035601c0a00da680c1041e1302c105e8a0350340403540ba0100c90300c41d000d60b044110380b00e0403200c4007060703405810000240505240b07040520405005580c01400300905038650307554400650301003602103031207a000380300f215004044a0041e103208585202c045032a08242000201000d030300398000d10400d4244038281c4003090304041c21000706a0107807030241c2e4030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 378012697 1250 378011447 378011471
    0x6130c090603150f1509090f09030305150d020f0d0503032e0609050103051503030c16090603030503040609020d051b011e1e050f0406030f1a01020616020c06030a020d0e010204080d03 80
    0x10006d29485a250113080a28000d48950154401050a4820340f42005562140084420a400d882c070447e5080321080040c1405031804043c1101005001007006140d40e040f950b51070305540050743c01401c03406204100c04840040811a44055200c02c0d19072403d01e4644523000b0048e10700c0b413107a14141955007021440840b1200c0c1100c0d80c410005d01201e07520f04401707a1141e0380d682022082042080303019004030344882c0317900410045030b403d540d540741181c0b526200c080052030040b600300d9202c076003440c3c42000039409000c220003008200101402c401c5425001500c0d4040b400000d40c518071110030390460380c6030000c0c00e42900c40300400d1100100031225409480c41c0c4950341c105c0000d0b88000c900046e036141d254100034101840340800b8040315005d107203082002d0040302d000c180940c00100000713105981c10088007100c40180d1044449204d1a4004103a0580c02542c5032030a040d000100085240c0341409810699600c1500840c80c080ca00400b00e5120000744840404064607071010b8504 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 378013947 1250 378012697 378012707
    0xc1303080c07050f0117090c04110d150b0a05030c0403140304030501050a02040e0408070611031504060906030b07141c020307020d230c0102090316080d0c170306130c090603150f15 79
    0x4050030240c02000700181d6106001c0c215008030880c0d61b441424551044cd2018900c8404001c644000070781c1810601420025566034100030034144c80140d083c800000807403107444e5400003107000d840146941d1400c50508500f56400101300140b140e00401c020420307003130304034101e0368000d4229242d9078075690b184c581407019009071090f88101280c00b00500401e814040380d0308080e104119010800b895442c441d0320266943d03803002400b40001e500004569038003401c04007841c3c01d0039014091615030540391946064000100598010740d0110402903c0c40c0c0400500400c942241017410480030400b2044480c0300c103101d070541800300041580b2511040940646610359401401d4030360b2001c48081490040c46144250240e611401c994800c0d254041c1c0789040d1010740205c1452201001200002c0300350b80050300c1c140d000f000c0194400347e82c1c540742c030a20025018a548068840d86090f0001b415580c207210405000d10fa254008c0144502d41420802202d500300c403602c58007100d03441c054072 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 378015197 1250 378013947 378013963
    0x10909080a03091a09071701050907050f0109091b0809010209090a020c01060e0412480f03080a0c0318060507030605060406050a2c01080c1303080c07050f011709 71
    0x4000750784c0c9418042c2c19100800c8110554082517003002000c0310155400e402d88100740c4a61301150082a0b050005043c04510012000b6060409200e5103544070381c00000c580f50003840c92001140d54518070b0a07964080701081d080500000250f040c0901c1da000106421070103030140d5403041c0d0014103201200001e40060000308004000c1450034a094246000400801045040095100002071001c40020311040044545a0255030300c0301140d9140030340c4000e600381d82219001184200d22000500d1450b9148886210b65500c2820782041449101510f100183c604141820301c00c00486030a94030043c400031940040011405071540e12040d401040240c0106030400000100417482ca50060014543c0b00300350303681e82c01c1c2036030f4510400d043d50202c04003050b800d030b0020600d203c00e980320b052056041090b18149524080b441c1c04081081403456000329100103011690b5000d2840900008004041c2a50000011500f02d0700017030a07003c00400c4041c003a004800450081300f01081410 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 378016447 1250 378015197 378015233
    0x20c10140c070801150f06050c01060e090f010c030e0307020411071a04031e0e1207090e07080106050904030c120302090d0807140a0803150f13060806010909080a0309 73
    0x1640c1e5425000c030054507003445000d101c0b840d40c2440b450050390504803910100300c0b00d062140c845100d0402e04100c0303040d400540a450103648034100480d00044480f250f90041803104010240c141440d0211403d4442145400041c0b500c3e094a00200c0100031085071901541200c00040e51810035550586501800f02d0180030104e1003903403c0803100001e00e070f540c0035601980301c0300c140c2074110210b00903948900e4110f20000e012026025010708180c00021070501280f01507815041e11440c8242c1119104001d051169010110402217240c0a00c01c00e00540015039406680e86020744003c0c128282411004002c0c503801000070455a02c0799054440c400e13401041c03240715200508049103103400c142810303140c44202071a4000440400610100340c0c0b0780c09a9040d05650ba02d00c0290448448150101e81004070740490320390642c1c0741022914403082030b0400107001c0c1d042035441498900d058108401143c40c1c1041c2a01003982841950070b144180c0c0f402184070741191501c102c501c0b850740818 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 378017697 1250 378016447 378016487
    0x2210610080702120703020102073801030f1101030f0e030318060906070c1b030308040623041e170d05010614040e330f0301090f11030c06040803031f0501020c10 71
    0x4011201d80301e18404600307122a2f00c96200f807001d00000124440c100788002001c4403203905030040000d0b900c0f10720018201050400082c04040c100d0703d0720076035404d038002e518541c00c00010085010108000c0318182d03211500148000d107002c81030f0540e0341170041c10207014401c44002800410000b01482c880001c2d0f400c0d008001d1569070718001c1c20030041501c0c00c84d05941008031001010006030b60030800c4112401449890391646d44070880d55044000032800e03106c006a1890020401d14400d0072503440400041c2c40c1d0f0780d0711b000d40303c4003110340680140d810042c49001c414050406102680c09841013484403103110f0300c0d0480d4440c1040303040184001e0030280c0001300b801c00c0f0340700c180c41c1e41c400e00c040d2103222600304050100f50882c2c800c14002002d030901c003c641800700700108001542d140c80a8100d54000300000001842070300254030a2030158000002c01c40600300c3c0c02c1e1044502221030040c2c030ba83c1800c1c0780c0041c1d11140d144a00310700a60380c400b145180b00b840f402c0030546540d004101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 378018947 1250 378017697 378017723
    0xa1a040314010f0c0509100c0c0801111c0e10020a050412050a0201020c01260903040b1209070501020c060f16020402130302010905120a02090a0221061008070212070302010207 77
    0x441c074007905070f1000300c0809500d49208100310501400403501d10b5000100b4052000304800e100747e410141f245001d807941c95040001141d2141d091040b40442e00c0b82c1c3c1031440e10740d080c1c1482081141852940b0080300381c10480043d03000c0300300003010004410000e03405030b11900c003824201c95030700403a4810b030310101c8099503801c140318005c6100c40d0198001c0e03098407040d2950b0401941e550202002030071803400c4400c031204403040703a03000154002030050305a07031910b41d0b125100192900f0080020000c03c143d40305000d0034007800c00254008080a0000c0d000c209001800a4450b00443c001c0800700e160000742c44100160000d07802034610340c010400c6445000e207076a1355400c19500e010490104481d06004120340c07420021081c038520040e801020981c1e00341d401e100759400302802501d000c640034040b510342c4a004030300422804400c0a01320f0340f240b90200420a00e010b0304040207052203104d1050040f819800305140d04041400070203075949944c145003c900900c51440c020b0000e15900d0030b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 378020197 1250 378018947 378018983
    0xc0609021c06050a0506090106050702030703050d0e10020a0f020f04090c0b0c0f0304030c27020d0c1d03100509070306020f030105030c060a020a030f0905090f16020c0a1a0403 77
    0x80e40d041c0300c6010705003c00459031002d001ca400c80f01c081e0f407140d50000b032043c010032087c0d1040008001003807001d42541d03c0559246e840c103280c40740d22107040d00495403a0280180c2814800400500b0500e580300800c14061180c882d1031054102c0c0502a0048161800c09e01d169142c681001180707940c840103030700c510742e0b80c1d00f08010b00c5e0f0810700d044c403040d0241e0b410000c0a43c400000b914180c0741c00c000c80807411440d00341d0303250201115021441c04025a03000c02c041900340da201074a80012000d00108501f000e07100c00404044103140341d50082008000c1aa240780c0b130001c3c000070200e59030075000540e51101d512292034002950310050501c0d0001494941811055000d14103c5400303804071a0151402d070104aa00d0003948120b40c010b904c10440756012a1048801c0c3d4031082250800441c0251540d022400102049510030b41c0d4000c500c00f4031800d11460368182c0c0c0b12682c05d1000d000d00003241c200003040c3e035000307104001240708010207031504c1e2140002110021a8009202181584042 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 378021447 1250 378020197 378020239
    0x41104020310230901060905092406040603020403060506040603030c02090c0d090c0504050106050a050706020310211221050a020910020f07060f0801090e010e01020d1a040e06070c060902 82
    0x2461490107403200b0000040c6d054003800b4a981070350001400c445a5990b20328104510340c8544810981040300c01000c0156078881030b00602c00b5040e03d0b42c3c0903a5690031400c1000541d50041c282c44e0280f4949a0204003096000c60044951541219010415151828500728034040ca4055130402403400f00f0002c1002082c04012003220006c0c2c07402d0001d03a0386d61005460500464403400d000c02d404116400c00545581e000f1079120960001e0701804036103542443e080d181c0740310060851101c4860f49941031088840d95262842044e2070103000303a012011411002c5400c29060000260302d0b0f901013500514036406172112140c0182c0003240d06440058029505d803040c2003a05614003504601081c032070f200d8030909114102b50b80f00c4240a1346041b14203002400610310308072a656942114000c0c0b242c0c01e0004180e00c0c01c0d01800403411001c040c001d03080411410390f0451155240c181409100b4401185060380a60941040c401c1070b0550300b41100580400c0074001c1d845007030f5041409a5080c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 378022697 1250 378021447 378021509
    0x1503060f0f110a140a1e1205060d11101403040803180f070e130606030804050109081515060c030408070603050601020a030c021002010e100603020f0603041104020310 73
    0x11040c8107102e24500ea2549034814880039100107020354128200c2e201406009103112211807404c6030442c115104000d203220484825000060307402058005032615900400350000012280c01620385601d60318a2610320784e6586441c001c0400112101c0c4035800744210b2a0305041b0308081c19036a00d401d15001d44d2641c030071a04141c40c050641c1d41c038501c2950001e50007145024071401003070f101c0d003003c51468540d600100038180c2c8101340c84124001030030030f01942008501c25a1416212410700e00054841d10342e5400c08040350340304503001c415002c1c03603e0722a42c1040e07440e418801a4491040401d5041c80703a17805940b05407000090014a503c40040c81500711030255904021a480c0ca80049844400118016002031318099050300540303042c24850064025500002503070201c03d54540c3d0914110b403541c103400a030398650800c00d40c18100003a95030f0046c12030342c80d45946020f41e80d0f161000070122006029581c04400100ca00c008071551502410411840382c0e007207484100510280390a07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 378023947 1250 378022697 378022721
    0x210020301030c060810120f150c08160c230f0a0b012306030f1f0e06090108010c02030409200705061b0309030a05160c060807020601060e0d061503060f 67
    0x440c00004046e2030b42e82d5200c0c016039020010303c142c1002152902ca0560309440300684032020528066a800e400500c16074042c0301103a22620540e14010b00d120070350720380500e09841808400388603040000e20045010400e583d0031400f14003403005102019242c40000c00540e10140300c3c100c003c10502c405902420304803000c0c191502a0012450380360410002045072082d0840d8043c004501b580e032002a8882d480640c8100041d1440e000d000d80f0300840f00305034484035210764420280a003078103060103c240500b075203200034066441d101c1d00080d900e00c00e510a40040a5603016448001d030030000c00402d2a10018403d6515041942070661721007000340c5003889104041d00000d51410312807015a440303030002401440c02d00400010503550780d0321880b0400c480120703440303800001861108a44001e003600c2c1c0c1d02d00c0030f5032801c1e8002a16011068020b00b0a20291606c1e01c1290340c0c50442100e140f0340c1c4280003042941000741a00441d40341908000d200e2410001d007207507225426441a500400307 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 378025197 1250 378023947 378023957
    0x40501231605070c0308030910050a0911030a020a1512020d060e060a03030e04150503030c01020304140a11150c070b0306040b040506060405010302030907180902040b0f03060103060c0210020301030c06 88
    0x3240140c0345885100300052074850f0084c0100041952034000d958400340c00d0b0191042340700300c1c1181c0001c6450403203010881076655600d80d07081c0000b09107503500108080d401400300c0300640e0005510440d09101e48070043c100d50142d40b8015104440100c48200103250654a4505100602001d04041d00948c3e002801220016040740384c90303113984040f40d41540361101e00302c82e014107000141020307659290341d40340010310008403514200010110390115000058480c20140b0300b03182004c031070858200365684684001400308080300b16400b4403000032102d8941c030501d580c928a100d40548114443e050045d9240021040c03000002188100411182040f03500c1c00c43c810001141c00c1516050303004602800107000c554020b40c001e42d013225444045850343d0b961012010030703103900e80c0c840002142c0c07038813404021410240100e8401510460700c150303149190001190b0781c1c820503c0054541c2d91507546086841e80240003003980780c80404800e40d900d43e182c0c240202c100701144550b00000b8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 378026447 1250 378025197 378025231
    0xa0501140f090d0f08060102120c010c080c040b04180e010e0f161d070c02030d0309020118180c030e0d0203040f080f0607030209010e060d0e010b01030513020904050123 74
    0x2610100340c02c0ca501d41251658901c40704628403c55217800000c10160541c4a0400c5400604503c440945108480d040002ca61000202c00007000c1c00c4001c0d01400340c40c44180300501007003006e00191804d5038210000c91550045041d204805086680e141022552034166034902022001c02c050650104202c1282e062112007100610084440c1c410151410142c00702c040207048503801141c1c2100c42803400310050111600041c1c14050542c500c81d022903a200084000c41d60850006043c5030104804460030070302d020f44101c141c0a00004980380280e60341801c08400c1d00039071140741c0440610007150051a03803458003951b02d5000d40250242440c10040000c6c40080009041050707040702c401a101d603880d6810140e000c1c1d0800c0340b040d4140000320403160080d40303030000039100c10090180007003014080c00c0006403c441c907280c81c1c82d0405042c078040144030803c09090180b420f5056031a40280c2d6298144507004000400b400f074103080b05204500c02d00d210384034102d40103d0b13200b1001c5d0246 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 378027697 1250 378026447 378026461
    0x3120d0b010f02030a0906140409051f060207030c291b060a1b110106150302091c02010504180e030f030907060207060c020411090a0305100e03041a0703020a0501140f 73
    0x71302405141c040007654021b010b00c4a544036001440a02c83c10400d40760a09031600f044005554040f00ca0203030009131070062214400c0e00382c1e01c5e50000d003101d0000d441c4550664441c1d044481250283d2800901380764500c0c00314400d0a604001748a40310005191030f50031083c00100c00000038507400515200324804240008030910a8626520300034405030090740c9041ca080d0340c100030703008d017042e201e5580d210000b0701108285070b0800c03440c2c4281d03001a0385522100c200107610102000408900761405050b90050760024101e030107450380b944028080c02c0d2400700f1707080a05158001c0c405503000204880703110080ca50043c60141191505440300315444a1040340e03580031791b00c1450002602c801404001d801d0070390042039001e2110f1426807610811038042000a04541d2085400364002541d0030502402e6100d02c41c2c001000001452a1500d0000741c0c1880500c2c126074002c041e5000141c1c1c108040c02080010000d50340b11009004110070303600d0566406030300300c40c00c00d10b8510001c002844 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 378028947 1250 378027697 378027703
    0x608180d020705041a030c040c020f0601030b041203020a020d05091201020f0403060b1909050c07050118050f0106050a0311030f0d0504090605060708030f0907211a070c0f0203120d0b010f02 83
    0x5490107001030200d07c081a081101400102d8094015070007028920b510308401400b110b40a1402813185441c181054500701112040d200c0c880006c02d4418800c0030802540454040e4002c100752500a444580c1c4a001800a02090351a20180c2d84001511801501c400e03001c0c0080382c0c06201e0030441002101c00780100c10610940030400408a84014000d0088a50084c0c3c1c0195070141624105401c030344e01d80342101c2d0132030244040c440e6110070a004103e0104602d4020141580090040900e41808154a01c606e808003d0076026040428401078600704810840009180200c41d405c0410b41c0380504941c0c030500440d01040d00305900441c10b82010b0048440165100380340038616519030220841c240c0300500455524012000002660f00d01ca62502c0c1003002e61800700d0200190501c2c01549180c0354460040f6035450801c10041c4191300041c0070110303281c024075820000c124030710020381415120340035603100041c00b0504d04224a907950244089000c2a00d40c0e1841d00380550060703075 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 378030197 1250 378028947 378028991
    0x13060314210301180f0207080c0c04020c0c240f0d24090221070201020c010f0b10080901021c0903031406130f0204050607030c030212030c040608180d02070504 70
    0x200e1007001c00040003007480c000f070000303c180e454110005032400d024402100380d81c08901c059800440200320181c180009001c001442e07e070854003145040c000e000b00940b94455074a030326200312a02d41400d030085840c1c1c0540e052480080410580c2c454075410703401000d0304082c8807101d25614110301501410600302041e4014001070203c8042a49170aa19030041c1d0301c1511566186180d89003900000700a1018043c003231480354002580fa851982440c81c2103d117240e00c400780481c1042c94108050302c5007030040040d03103010302c0e04c03c0880e912070000038064824214000700d04c203444800055249615030007540c21038440e503800e01003080312800c1e021450174160b500070707801400074142c0ca000603450340c050312003604200c0c8090f0070165680001035660300330380c038147e000c40e00381400c101c01c0590521041820103542c4201c03d085090a408e01040c50045001d00828420075401041161007002d10b006440c0c100b2030119401c0e1044114000e4448155110b00e034040e50419031810190702d1100d00d580 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 378031447 1250 378030197 378030253
    0x2001050a0603031b0b13021f0e13060f0b0f190e12010b09061c06020f040801060f230a030f1515030812070c0209090c0a150e090613060314 61
    0x285d82d48039002200c0c48000506000c99202444a0f010500800801c1058800030b0041d00e1b1180c48001110a110b0758240506400391107900c0c001040c01401203e4102000f40ca00c0d00d2140f540307404403050b40030114400ca0704c400e40d06c25a101040405103a006030282e580384800e4403c01d110060030525103003687c1c11003004a0b0300452120016a59003403400c4940d201d086d505c3c40b11146411542c071504c0c05c9038040300ca0b804601900280074003284a090040800404501078501002440c0126022400e80c0d01c2040300031003825a040b645059480040003170113036400c090208422222840d00510754a0002c1150b1041030030302d1510307044030150b41031541c2142c1d0860f043c0391801505007910601440000d09031420b008003513190b44056150f42901c00e20510042000784122040b010821448a819500803140ac00700005814412075100800f110407a1054401505ea916100c0000c0c0030a400c4011540a4600c0c0240003c140400345030151b00101e95201500c40321480300300c19110002c0411400c1c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 378032697 1250 378031447 378031463
    0x909100b100816022d010e06090304030803310c140d0303050a20130f060c02040209180c130b090619020304030503040609080c04060f062001050a0603031b 68
    0x210042d907002a07514030f0381c42510546a104148861581440b06010503610080000710f2582c03a42001c240328418818a0443c018030441c41c0c012039860f600c0c407603070000825920740031011032507088000030400c41080c4005588800040d481c0141e6101080c105410384020079010383c0080c51141c61110950440c00182950302c0c548680d440641c0a4400a005804180c1c0c1c0c8500e1584d405c1404410000c2d0401d01040841d0b880c10302031740b418801500c50b00000000300c8020820495039401c1000200c03c0b5a05540160b281c0301408001900d0002e21a080b800c0c480c2e91404000da150180700003042076030300c0d07105010065038450780b4080f02802059010341d00034400b003210b4000c500008480d48042d49003441141c0c0341035101e5543c0d81c00d503013180e40300c00040f5101802c14880d0313000912006041c2c002c01d0382c00700411031600e4420400c16103188107250603c1480708c140c40c4c08091503038582c2c40307602e600e100a0003e400c114001e44000e000e0b52005800141c407400074060b1112402d4100300304550840a6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 378033947 1250 378032697 378032701
    0x1060c1e030206011202060c070602071a03011404110c160915030807020402220803040906091a041517030c15070e100e1012150b07110d020909100b1008 67
    0x17100c1d410304c00c0755002c5e0390042c400d1064400c00c080c20040071006e40540e50241c20400d15240e0008405c804588a40b58480d80910041c0004690120000c1c4a00012074011941300b05001c5004560b128901440700e490084200150012001e00c10000841d1001e640401c031150400300c0d41403010140d8003004085582c100200340240c64503401411031076848a01088914034844110010f00c91180e0107a2131540002c18104a80f812030321407680100107070041804085010040304040700d01414441e80700f9030780c0302a02c8840e031a00da00d40b00c0142c0812107140a6003100e07101c240755a80c001c40c1c082d044610800c1a070b45403c0d60b480b1a0103000d1425910f41902c0c0d401310004000c1182c407445804c004114001080c40c1c20350f590301d2420b04050400b500d4038100400c3c40c80d03a0000359102501c1540840860600070840301101c4001c503503002e604508074140c0c649200d000182620441e40d0060b500c490701d46c0034442203040c0440c84004070101d401c4200111003200c400d0102c1001e88503c1100490b001c100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 378035197 1250 378033947 378033959
    0x150f06020c19050d1a130b0403031505100512092b050d141f0810020904020702120609011a060d0b0301110406021f0905060606070c0503010501060c1e03020601 70
    0x401c48007071024207216082516200c00128142c080309501c00e8404054840300e510905058140081e0131004c0d40c1e01000b1b10907071940300c0d400b0036a40948010109030752031303490454000c006041c2d88083e01e001403000d40356228000c1d009216401503880b07442510000c03c007003035800f0400500301004901e10806440484002041e8107090140c03031210300c05000301000010455007581c807942d4815092004904111b080029800e656200d50b1038034009200c0303040006201011000562001640d800d00e00940e0356140000440e010f4011100001d401444410342c16503454400700304140b29444a400070407001c07504070710314110154a409070a0308004c08214071410030305203030080c0f82880000b400204100318186040398080d030060740400010303000031044010010380c01c030301c561803011114410300000034980c40e2b41c0e480d0031015041134802d5600240c5c5504101214020704000c02d0024020040f07580e403100e000e06181800f0004444c40c4100544442041d1442c00030f8075912500366004101e942c0c2040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 378036447 1250 378035197 378035209
    0x510032a12080c0601030311150f0c090319030801031203020a0e0d0501230105030d0201020f09040903090b0d15120309031e02030604060207021f0c030c02060f0d150f06020c 76
    0x7990544241c24100600001c01904100942c0210301c2586d0701e20402c22401001410110b2503210205c00e4500c00080c8062000c1c2c008000d50004842e0941d680e5030217a49000a203418203905024103604801103690062507004800507048a010b030001c003c0216001c2c0041f0100e00c02d40e00061b01003036020140310840e0400900284085218600004140c40902c2240700d071000c000d0fa02c00c041115071401031005080921849030040c034640005c0d030410040170540201801200b40c0c040c044d641e6000c41406243c070542000008120300114166a001401600d6010382800303001a8414030400600180e5000d0b46100c2c1800550035540c1c41040c9420340c1d9584000d16010b100810030a417290081d2030250360f09006581c0201e20450006a4405840c418041d00359407000f4250b150040030f010991035581c00240c000c444682c1442d0020143c02d8a00c00946a40034156200030752500100700f02010420aa0140c446540c0c00201810400c0c0d50302d600110500440c060b02006070841000d103216420b0003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 378037697 1250 378036447 378036479
    0xa0309180b120a11010e0d02040b01031d25051f021002040803120c04030b1810050a05150303041a0c0a05010507020d03050c0a0c020d0c090510032a 65
    0x4140c0400c48054210016409020742c0c4841c0b40141c0149409000b08401841002c04804080c00e14080010040000686058030500064011521120a400c00e1f81c420350140880fa030401c55002484403004410340ea49903500340310132034003030390070004201c500d079010342c903941140c1d00100001050480101040c91074403a2112600941c03044240d10b00e11600d550001e4000303054628000e5840d18000e00141540807405484405100c004010034004901210380040d07204124039a5643c946011840151420703001d00c040d0030440f0b103441c05100d1035440301c0e00654010104e100206e100e2080203070406440703100e07d11441d1004182404200c2d0081c1846024218420407001650801c0c06162149400d444086554030010703046092103129564040c4941c0c0c0d040010202030508201d103098000d0b03c0506400c1002e8070601c100c55041041040c144004009440024018000c600749185805000c100d24081180d00541d08010007028050910b20f02c441910100041c0440d9882c1c84002444d404003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 378038947 1250 378037697 378037739
    0x60c0906090409080a0c1a07092705010f03060b010e0303090d150f2004030305030a050c0714030a0e010c02150708040b030705040923010314191b06020a0309 69
    0x1a95680d401240d00c11001c0d040961aa407070b100041046d514101501c50320354603e80706160610820300c07454a41c40000c0c10141e40390101e0070b401950b0300e01c0c01c160fa1642c3c0c034000394444508203800130030659101131401300ac0300c0c4a0078080c41900f60000041d590650b40100c01e5070141d1081c071006a16140c400c64440165024a8034030041d010414000310a0b00c0c00c01d030040e4030039910b940328058284203003000350031600760003200b8600b0141180d800800c503100160900e6030403a01c070000319140450840807074060700d0348410380c003100310700100340b80d41c80360040301c010004262424000343c0c165009651580c090b40e8000d102d0340c0d107928501d4500c42c094000700d50175101280c0a00c0041000046080110f020b0b9070070f0b84620740c0745d600e000e100b00162103408003a03804840c0814240324014900c1d0384c50a040d20f5110007260001100400101c4c604040541e00400003a0410b0504061107210340e0217100b801d00d00008140001d0711a1800e03aa52000c03132000400041d000c0d9030401881086003c0c0c40d070260341e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 378040197 1250 378038947 378038951
    0x4021e06030903031501090b0316032909060f0a0306050702010e24011203021504140a060506090a0204180b060d0e15010e070e0d0614010b030a060503060c09060904 72
    0x440104105800c00c480b6500c1507407002061044e00364000101e00d00e406401d20b820082c560402c54404060300025250070601c404072401d01064070301941088900441491002403400681d0350503c04500c41c0846a40c0250440004a5414200040d03c00118000500b8405d03c2c5480d55440c04c0007440014160002c5550b03a880c1030200038400e110b82620b480e040c003c0e02d518070171710b1881c8c0029010103a20020010715107001500000e500404c04004900701c24010725030950303239030904404540f100100d0080300e0155820300c400300090762340030074005d11080d00c00c1101c075920f07590188124412801442c140707180540041d80c4000c0c56402034071041d42c4c054051400c0440122281c000d4660004429880350043d444803803200700000d171810f00618069002e4a92420001ea01504c07001c0c81c441114050400c040030801031001c1a0801c503542d05103100c2500c000d43e55600c0d002c1a0740c00a642141850f4101703031000515203000200203000d200b0740c40c0d04a2038010807030100b001d40c0e4001144550095 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 378041447 1250 378040197 378040249
    0x204080a0f060b090108060a0501080a02010f1b02090a0c090902070506041203020405030303010b0306030d020105062206030b010f290906071407090507091e03061515050a14030601080402 82
    0x10704d9080c5a01d0003403c585004240c1070a2170700d94441074400503004001c1d141c0c0282c00d1000540c1c1d012085846c0100c060825404410300ca90700341e007210300a068040e41200c03408042c00704491095110004403103155840c20b81c2c2985482c0000c06078491070708090310741c0e4017240c04640800c400c207038010a203040c18280185000c0c0d8600209045401c240c0c070044a610000c010885c081c00d09003c86000c05280d4030080019240030700c000703041500480c021610383c4501103981c510034492640000081c42c3c000c18810020742e544c1851113980a0b4034000c01a000015086050681440c5015800840c0c0038080050810240c074040c49540c1c0c100b14010313141a6049a0029504c010601140010381400c000200b40b51174012000742c4001180e60011402c0201e550030921405201e0035500c090303c2e400386002c11611001c0d0b03055800150303280c010065551034569880d034416000401854070841c0d94032151060502d010307488000b40000c90300c6074049020070000078018074140010000310190b0001403e904 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 378042697 1250 378041447 378041449
    0x111201030320070e06040f15170a0204090f0c06020d08010b09011e0c0314090105250215070b0a0c02030a030b01050c010f1a09040201020d1b0b0708190204080a0f060b 73
    0x2210f41d5500949941c000007042c80200d0030103001d10000340345095018041000e4200703042007100e026200300e141c11462030700340402580c000e1140b0b000054000b00240441495401c1040c2080400030341100c03203040b07030000021034600116032101c0607c8552611505a80390a50402c0190b00c0100600c0c1009400c110011419940d11038020040005545041c8005194940a0604190040348060b810004d024001940e81d0150844003400c2c4140741074051202040c2d07142100041ca41070095000c0032410352010003181c100302818000d809082e0900140e00c8892a40c011240740100d81d00040e0410810258040c1c0240c0042c0d2840c50180f4041d0306e440540390155003140c024001820015444020079101c030326290074038500c00c034812a801c00c400d084c030b580080c1d924014030503540180041443d4401c101035100b486001100c0d007001d087d020514042800400300842201d2030045c4c5007150808401002c258401d580070780c3c034410000d208262a64551a6a160700c00d281196000d072100552405 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 378043947 1250 378042697 378042703
    0xa05640e091506040213091104051503070219020a030f0309030b180c0303030105010207030b0907030209070f08090c031905071e0f0803030402180703020d0509060604111201030320 79
    0x10070350724000540006144241006040007014110034401c50040c00452855403101c0080c00858409600010b101034100034418014010340d0300ca41d501210200f404450456044015445420540c0c00c1e036081c0d445078001a007a6000209010390808044281800041d200c0c082c10964907000e1b00300756140035900d58822402c40c40031210301c11090302d1210a25242a02040719201c3d0a00480c05182550b041c100000d40e035110764800034021240c80800305502841c240140406940c02138107100b06842c2c00140500301c0d10000241c0e60002c1c80400009804100109020688402c010041c00310800e07160403003900d10381c00305400e40b01070141c0000092210310700b140d19001540300c41c400790701035440c0c01002d1441c0d1102e0381c0320f420203400c20020000140c2d152414804007206203401d802981c0c4982c81d0031002801804001c1c031716985000140320b01c62500107403035031040c08226002d0040f80e40318020240c15008107018502925119001800000d00900f062801140c141c802c2040c58030200c100245 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 378045197 1250 378043947 378043951
    0xa0609030201060f0611030a050703120e28050c0135060301051e0103120309080706060305010c09031109040326010618081b0a05640e 59
    0x3000d42c1d51210100030404241c284000208a6401d020030b0a41200446588074491019403204200000540c101010b0040c2035002d541c001544007040500f0b810024103a603403901040890484110b17540d8a208002d42030780c007203102507105001d40000c00301603005440c04442c45160b500b03005064108251000540c080790b500c1d420000c9211100c904021082c1400c50b100501030308a400a080301300e16420740c006c8a20381c1102e9000c5000035064400c0361080f0001c2001c110300a02000b00001c00c9020f003c00e0780c11210075207000320300800120320002000d070750540c454400144403404031513840d074a51500014a07603000d402030a06500c40a40010702890102c0240e000c6801201c2800c01408019405148403036031580c0c07094011440d50074005403075034a0500c9040c070312500e852907000d060b4a42759410904000c00014004950a0603003030011a0425030101c21180415400c2d4200d0a0f901d0801c00c0c1c026807540e03c1050a900112800340024000c611070343e14031142030072200d00003180e01107025694 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 378046447 1250 378045197 378045203
    0x507091809120206040209040803090a08030a0e0f03040f0501080a090204091406010812270909010207032601180b0d0305071e080307030c0c08040b07030f0816050702030a0609 77
    0x15004510701d0442e6081004500724011940054100001a12000395854009820a4580b03441e50344e480003046c5062030424009107842e6003c02880903441c07950b0041c1b40c1400c072100680d100004012583c5a80b80518480d0360a03050703080408000700d5018051a503008100300a002c43e14103825000724007540c2c1000070446890884031044201e4050512981c0d016244840240000ba508100800018007400103407001303402403825499101d0312845419204020094525003052800c945c1e020f00035001100c00341c002c00e09031003450013498500c1d007030501c8200741c40c10100d4160b400c0c200b16803002d03107110001004680e903c00c4000c440ea60703080c0c00a1a03d034800c1c1d4076107548585600c1e120074000319804a030b070110100196910001034412040d03c0e8401d44919000030349010400045071a03c100071400740102034005030200b0702030950070050030118069100c25410b8002c102c4126499079007143c1e10210030b10161502d142992150009207000c0d800203080358403078891070300e811085400700d074011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 378047697 1250 378046447 378046451
    0x509060403110109090204050d0204021821010c05030903041707030f0602090a0902090306241306080c03190303021321030206070e0102031207050f03040b070801090b01050a0305070918 81
    0x81c140c2d03134410000700240017980f80542c04e0510301000b14409082078507000b0721840d00880c0c4811683c540c03070410540094014031040c02d5640140014031040c1e80c0d8543c44940e5420145116407890088003101d00860f10342c401986400c4c90460404603041d06420b40550b9802413060000104088c08030003c80e4600a002c0140c1d00e010728401c11010310300d1540030001c0e640c01441400c1455501050581c2e0005414042c59800751a103070b088040606100100b40d4007549003804100480981d40c012010f0303840e2001101c58481050080503550320310314072030260f142001c03c0702800103480f03034020340303011244942d10b50013583d15102000c03002c240c52411a4047c5141125a0041c10b0703040004540151140c00c0c180c40301145000000c2d200d04c500718004007015104804100400e00c60b17011124203442c010b42c5603807203080038a888015103c0c1542c52000003200e0400200740d81c651032080c4200d2400585a0b2441d0a052380c20a0b009004014502002c0c040001c0d4001582c01c01e1101a00b1080006140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 378048947 1250 378047697 378047723
    0xa0c0603020310050d02030307060f060b0408010b040c030513080c190303020d0c0503060105090f12030f18010212030a05061201020a02341703130e04021002061b09010509060403 78
    0x440c83c0c0007041d54800d6110705000301004001d030b00c0110468100f20b0300000b012821040c8a200c00740507046aa001d40344056001400290380c03001903000b140c403c441105c0030701c040029142e04505480d41a00c58a000f8118041060300040c1c2003401411030003001c1b001e0303818031403d01d0454080c03a10144020b50200b41c00261156600050f0300c03c51450030400d00b04035040d07040403c00200280514229203010ba01d035100d0780043c1c1d9580c150425030551008080380d81d502d0090043c00c0c85074010342c000060010542d1110105503001180100c800b240c0c00d0249821943c0b00c0501001070040a0001e540080c00f0f40d0014819400c20f00041c421400750750002c000382403110307140004081c8454451003645000284110300e0200302422001100d20030490f007807440c8081c041035400c5100306500108020740813200050b64003000e00c0d00340d104038003c507014481c04400d5282aa12280304680d410940c81c030800da504a00503040300601b81004061414509103548070010500a0740550400c0d1156030308414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 378050197 1250 378048947 378048961
    0x8060103030c030215100618050d06140c1602090a0902030d0906090503060103020d03050703050f1201140303130608070215190b0109080a0201030f0f05041a0604020a0c080306030a0c06030203 84
    0x1c188200c100b01d05174054220328006a034142e5141d25805894104600300c0e0540421420008841002d800e004280c20b041001a150000081c010700c00c040814018800010300c003404020107275100e07003035210400e94913403116500b088000b0000a00c3c19406c03e42d22910384004d601c0810018220340c5c3c031034171248042d9061481c0a058090310342d10540c131a070311000c0181700585880042804050707240c01c00c1c80c0c581001c0d00d0283e629000c0d0b0040409101c01c0030850407003004c0c0c10b0300028120740c140700c15007842c40c5010b01419268030680710180702d114801c120401100e84990300050b407040b03043c4199040961080300300b401180c0250b0301e841d06900c03104a016080c1c8910320503079000c00800d090440983e031501c2d400070b458550007080a814195503942e00c0380d1895140d00112201c0503030420030415841c0034980300160910071000f484c01c040094001503814180740c4200d489503102c0e61641ca0b0380c600c9a0740c4401d0343d680010241c50f014080c22540c0301c0050702041c0c8a00c090f090b55203002d40c40b850203034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 378051447 1250 378050197 378050203
    0x409080d020a0807230f07171804060e01210312140109060b070b370f0515060706091502130305300304020301090507081506031b0d03030608060103030c0302 69
    0x10100d4421101ca40c0c01040444170280c00f26202c2c0c11145d039401d41c03900002d040410350520000146611010001104402d00da020013001840c00003c54040142c0c83c1c46018500c2500024099100307010448044c01c0e0050407001620f49095119140c0060540380180e02030f01942c0e80c0c0c00c50600e4588005005010410641c0600805056009003003401c0610135110401070907409000da40040020300d4204289041c030604540583d0300348540509840c40416103940200040da4861340c40d2031800c4c0c0400c0c1280c4101c6034074180b0100003490681488121345400005003500038003124641201c4003c480540081c2c00580004a010401c00000d40d1a50070604e040000c9500c01340f06180701c80103046144007036180007a08000c540c000b45612030755a0310100e801020240c901501601c1450350004205c1400569204054600381d011482901c070038051580d07035840001032103003c0d459810b80b070f001810560381454803140a4517000c20360599410707005090442c01e81060b0001048960341c801416010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 378052697 1250 378051447 378051467
    0x9012d110c030a0203060610030e16030b070207032a120b100614031810052e05060703051c02070b071403150907050d06090204080d08090601050409080d020a0807 71
    0x364060020f8299640c0041e44440300100460b00c40d010350007090300754500c6a03101540e02148842210f62100c4600303c8000d140301c2503c003c0759814600000540b90074070218180d02140d90004414401135160040150401c48450071040401c5400c0c0b0005503003400789201c40500e600400f41f0021508000740c0c10661606550801c00c2444802000d0013542c000322030480e6442401d038559560905920b6490130308110a8a040741c0c4120b0a20080c00502e91130800d1641e001074028551006691f195a443e0003d0f01c03051180c681e00400501c07042000c00d004000605c649880a95035001214211410400f240c01c04002626000303c0c140400c2200c07600308000c003550078000d041d1107083d850302c0c08804145c4241c032411640038041880c0802d03404e07402002603401c602150b800c103001094489400b80020740051041c20000d00c00c81840b484c00c46c6c05a1042c40c0031300c0d141405842c6507800d0505003c054144030004882c40b070310802600340c3e142035510190110b03241640e02c480a0741807072100180f60b0090 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 378053947 1250 378052697 378052699
    0xb01090303030e190f031e0903020904020607291503101104080a0f050d050301030203060621010c030509060a09080d02070201020307020607060f110c070314070807080304090f020301060509012d110c 87
    0x284030314429500108400e08403981100d101071250344a07c00319500d07000b5004018117595107001d960010c0300a05c910743c0c00410440c985030096641d2104640028120741e0500354068004494030002400c8a411010b280f801604090340780070380d41d0000d1807a0046002d019140f0078500d000c450104a818001d5070050803407407410314195411900041c0e16810701400c82c074801d003410541001e800541d00d01c0c810308225040004c1141d00744a000c00f034040e103c00c40b240c01c040d00560f000211a20003611403180c0c2d1942144c180f60511041302c0c1c08000039800710405038158441441108016903c000003000403911a03040450801c608070544001da07030129005030794107141807010700b07011000040c000048a4000c03440b0301c9071a0f0f01900c0c042c20320034503403c820b0f080c0c041ca05010407080c100000400403540d01c24020072101032011041800c9000a00a02d40010340801000e807041d031240d030b0440a9503020a601c407200750444030b400c40014180100100104170f01001e5500051000e101811030180 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 378055197 1250 378053947 378053987
    0xc080307020105160606050913020102010b1008040b040c0315020d0c1d0f0a03020a0e090f0706081b0c1e07080303060604090509030d0c0203070b0601030b01090303030e190f03 77
    0xe0560000c2d045010b004104440c0c01a00c545100600c212500541c00400c8082c002c48400d050404841c40201c2c51868168050340c2000300754842d07030400c40206045a0a60341c0d62a465440d603507a81000000041e20070b4030301030084d140120200b4415031680788185c0d103d210041c1d036000640c2070441911407503d065420f006400e05080c1c0f44051074008940440e400306c41c5013440c102050009000d150b9107410183d044a003500b800300b9103200100d0070500802280c1c04131390900700b007187d2180d501c0f003960003a00000340d01035000c0360780d0940300c4481c00120340c01e08007614104244441010300d415510a8590a018050070841e91601c0049c0425806040c1001c0510301d1840c1c50710102e03c80d4440c40c0704040801e40d0b076400180489500f8415186100c9000720240300203c0d45c140d00030350b03a0300030f44001c0d12000f081c0c1c00410603a6019214a9030702c1e42044c1c59140701e480c6140c5041c0d008240d078000c00c281d28050740740b084c000d409178140114500382c81204040204150380c1030050290080b403514540c0c40e2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 378056447 1250 378055197 378055207
    0x13120807080c0915070501050604060b0408030406030c120e07060e010309050c0906041b05090a0f03030e091801090507150306120f150212090d090b22120c030c0803 72
    0x307a07004007019440b84076903807003a565144200119080309031441140b00c0d5030301c002c150f0200f08501900010b002c1d00d17003280c05010aa4543c11580c0c45807007640306490075980100400c1000c00d000303401c00f1550b100350381007000c28859100c840d43c00350b440303420b0300d000c040c0c11100c401d0209907003281d61644480b80030b1804111070b00c11741c2e45456440072005c42041c0f14924000000e9015520f0740c10800040c001010361050b00340c070a01011f023958019034400c501c107031103c0d880854521041c0c44c0c1c4800b00c0e609542e0303980e805031039034040c0214004060701040b0920410b01580c850018240a000c1d00d10b882038009010103843e051403600c55010080c041020581420420400d01105006400c6c8903504020048546410791400210104504204070005400882d05042c04038084040070f116580200507503150b1340000000b1141078010f8020401d14940501040090400491402d41c00008003c8407100d4603840d80f00040b0003001e1075204a51210b2150014000c02100f4004c0400400030200258105 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 378057553 1106 378056447 378056461
    0x110d0b09100209090705031b0f0a0e0d02011e03021207080105030f060f1b0705070909150b010905040e16150e030a0b06040c17131208 59
    0x1d0041d0070340c0090300c03070035030080350780300000240112500d903a901c3e0107481c0c40d0800b4110030504041d84507480b408442610040050354042503603140c66100c1c5800043c41008015100350041140380c0401c80141d8000ca1040b441d1240c2080303041c3c100385050741c02c4009008030304040c200f00350002d041c004041e8210900605807401901903035504000c200150390342d042c0c00c0d244038045020000010350720860b000841c000d00204660382525180041e25507515120407504421004d40e51800b001007007000180b10703482041240c60b0b00303108006200300064540c00c4144100d90041ea11108292403506060200c524854a8080c05000f026155404981e202c1c0c01d141c0700c0340c00b18801014840461500182003035000f58011161b110300c0d5184000d0102424804800c00e040c071181d0f42100d0328500840c50910312a22907110307100240c0190341008800821400d82d50000d0000310320a020341 = true := by decide +kernel

theorem cover : BRFrame.Cov 377877697 378057553 := by
  have h0 := BRFrame.cov_init 377877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 377877697 ≤ n) (h2 : n < 378057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
