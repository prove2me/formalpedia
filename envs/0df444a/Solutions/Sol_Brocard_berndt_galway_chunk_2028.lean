-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2028
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:29:02.362028+00:00
-- url     : https://prove2.me/submissions/17e31958-18c4-4ea1-a426-8328c890f361

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 364568345 ≤ n < 364748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 364569595 1250 364568345 364568353
    0xa0c030306170c1c020a0305030d0e0601060e010f0306080304060e09130f08030403020c09070c030305060a03030504230d05010203061203090d0b0601170114120f07062102040807150f02 81
    0x1110f007004030031140b480c02609114940e14041000d41e407580280c6008602c110011903454103043c1d40301090710240c440b15010b5420400c010404150402000d9121280901e04142c004104040550040c03034142c00c0810540300100707012607980e80100c1003000f80c2c00112075820070b50340c44220728901c100150b00018001003200c440003001071b076000003540d0861302c01c0c0151020038095401041c40103504940000003c0c0300c4140440c181501403150765009041a90240040e42c01c540b4080c1c014801c920650381c3d07a004450b4900c0302110410b0f26401c0a0b200101341103627000490030101e01030f4206032096407240c58041a0325940003030000480b10001006041c1403030016554031010518180201964140014000340c01e080d003103100b2505028086000710618811040418000b00d0210f00c1c051202139030140255040d01031001070440704407030891500d101c8041248150b094060144c1c6104042c0e00d00118000c0303400b80d404200c0000380c6680f04042c1c4040130084c4000c6440c254040c840301c0150f00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 364570845 1250 364569595 364569613
    0x3010f140618150d14010f1a031c08070509270c03040b010504020f070519060c0203040621060b0a0305010603290103091415040b0f04050d050a02010609020a0c03030617 74
    0x600e5091340e503006000d100704040341d4000102c814251414500740a800980e00c800a0740c0c1c06011052044c0c807080f043c1c000b00b80305040c850504041c41c10103d450000e00200702e0005690603c15400c403072004d880505004092124411141081040f0454601c40154a000092140e1700481e065034400d9821a52129090746480e0500009501488004441400802690021803002c02551602c09441820300c481862203085c100200c07420003d0107070071900100401c01820f07030310a07000f03610303029442c1c6c00030345444908035103038010f114641c4514040500030506400d030f26015840309048030001c0e1001c0c001c44517601d405011081d40c0c1c0d05400c2c0071981c10682d038074055129070700c114900762045402c1302190f21a0591285803e8040415100e002260b204210801603100c180d5030f003000003018625807a0405070b42c3c041d00c50380e501c204c16080080210300f445030079100350080702c014030031000215550900e09000400c03c0420180581c042070070144c0000e01c0c015a0b0b4060350302d0405039000f50a80720 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 364572095 1250 364570845 364570849
    0x19031107060c0e06040314060109110a030209030c0d12030c181203030902130b011b030e100507020d060609150b0409020a09091506081602190203010f14061815 70
    0x20b40035038140d041100e102e10840c440c2d200c1000800c041d500075103003810003003041e2800d146041016000401082d0130031007001c4078010407005480d401000342c02d0158035814524042072900f8a981c07500d5500104c1804400f0a11016400b503418484442d41d05008419a11405940041d030b9102904801d808a032001c0166500f050361005440e44240b0f4045020400c940014040344400c2e440e0300442c0b9030300c001ca10780b25a00140e080a002c00c0480b50103994546548000d0704e4401c10145842c010148003c10180c000e10880c1141c0303800e41d00030100b80c1e09908070705088005001074010740700550314100c45070300000c0e00300074850100c542c000805440e06d801e0078200d401075000b20a0060070b0107034041d0041820720060091207c1c00c0364481450f44a186082001030500e007000c1c02001e2031034802c51600c00c0c42c03a80410011040000507160316641101480402d0051240ba000f010700c0d1072a100c0c44440710b54020040601500040307411034001050f07240c51100e04030040d50032010500c038101c0d4200d428 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 364573345 1250 364572095 364572101
    0x204110d020a120b102610090c081902090612161b0b190204080a0503030703141b0a1101150821030a050402060708070b0406060b0702010815241903110706 68
    0x1b01c8240d880c3c0c25800c0c614503035403824040e070980301020035120802e4148151107027446650380c0d800f8107181007115420804502c0d14491041c244040040d60002a041a01d448000450f800040c0601000c009450208241205000a990000c1c005181c2440c2040c44642c0144402d098a4006000704002d480e043d44915111150b1101070364140c0e0203100c0012100703c14452042c1c01c3e40100d000e0350b0380c1c8c5800c00004044546c940c0003203c1d031050110610514801c5d0300310560702800b10309840c60fa41c501100c0309540d103005025110020350b0800c04c1d620050f40c2e44641401c100d40000d03045480180d1002c0d500305940611010790034440400740700041c0d12402c00c0d00055009400a007800c1d00d04000b540740d88800f0b0340034100540d102d09070030090100b004900d10900f001003081801141c28000ca9074002844254041d04105520b20750038003480c00c0740d4841441043c03001c880030b420302c519010200c500101c0c0d00040c100c411340d05401c0c0c1d404403465000b401060000d44c0858282440c10001d5a682002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 364574595 1250 364573345 364573367
    0x50a0806030c060c060411090106020a03030e1f1b0e030a031d03010c050406090503120a030b01030e0f0f010f0e120a0923120f03090d0204110d020a120b10 68
    0x2240c410700d02c2030701490b260350b40188501c1e24090040c0ca02c0d45000c0c180103d00507884e64181c0d004000040041280c41c3d0301080c82c80240d0790503d00030480d02035030640103150074460b00c1a60740b082a40700d0080c6815805911101801c00d2520040c1e22075100c03a24107403000c0420b0311440f90103400009801c0000f0744503032403560a0351030b02d001a5004040312400f282c2102c661102c080045200050140071035604191004003c2004500422041810304410010f90140c010400300713054451480d185168020342105690b1f0f00c4182c01c0303401e0ba009920003150b0701ca21400321800c40b9446c2c072620300c0c05507145020b006c080c502e00c00002c048000b450100d0200350342c031801c007200401c00c1451000c9891141100c050900c0c040540d078500700c0072841d1007003040322030b180c651507143d6511121001e529144044241c6031100c80803204002203140500109001e4101082d000c038910b0340000d0400c0c0c0300903a030340c003030319465880d9a9101040b403079400d004012200003042495000300355030f0040d02c81031300c0f51480080d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 364575845 1250 364574595 364574599
    0xb0109050f031009050d1b05210c0d02011b0503100e0903070803070e010801080102070b0705090a0b0c06040c05030703211713050d051e1305031204050a09020406050a0806 75
    0xa142450315407040354104a4115402e03004100071900f6942d0064507100119003c80d035403803540c903142d9501e6130f271080100741005410341d4221703030030f09462414019200102a0b00c0c082d11320301052072030002e000341908540d5104102c260f240f0044501d01c01c40a0328400c024002510300c0f1942080500c0c070034403200030032541262000704501b00020710044055405914103485418040d90a000050000081600300104580c81441414040380c40181d09503007150700d40c101780340c0e103100040100b00c61310225045002c00310b000033003d2403807200014013144039a02030303000d030090241c685e030406480d80151302c0050462400220030039225900c241e03580a00304041e00702100301e000404500598603c04070b844500004072140e1071024480140101140c60040b031400c6031078071b90344841c20f001c0c966580010304194503021510441e20000401003034081d020040c100e03400300c001b00d200349900398000d005e070601800c529800050900307118000d81d400e69805460ba04d0a140c0461001c440300c0c00018482a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 364577095 1250 364575845 364575853
    0x100e120310180504020102060f060d111c080d0e1606050d1e0b01030e16120602070c08031806040b160f020a0603090302011b05030103021512070914040b0109050f03 72
    0x2c0b5049100003079032031010b640740081842c1c03a160001a0420000500342e02d601c281c22410409030740e46284072940c171258070011040360751514001181820355100621103d07140300700b2855040c824090003420f00ba142030349081c41980d202512103501c1d0b64100c4844000700da80c504040c42440c0c0910042c001030000c1d0240040c028140110425582c000a00079170030041da2500d6104a959044c00b60703003070800300d05c4020507414040b4800e03000d541e036442c450092212240391082d4200f0150303030126009244c03c400070b11003040e280c030744241e08d80c0c0c080c00410800d541818240310650030810107403000c64010080050034207030341e14100b9106140f495002c40b00c01e800c4411550050f603d442040707028004a0340c0c0003922484610340030b42100d4031100400da018108509030b04500303502500f2281034941c1034034540503800c104a4000444d000c1c952000c42620488810803040e03035072203c4036004171100c0b610010100030082c3c0602049178400e18101d800141d0000d400c0c07007507040c5540d04200b00c1030042d00312 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 364578345 1250 364577095 364577099
    0x6070807050f04030c09050f0105150c1e1f05190207140d020105150d080a031104091b03140f04080a051c0212010f061b060905061602100e120310 64
    0x2c400350b40075030801c0780c003a8405d8a00740008603041c4104c6500c0440c1029905e4103505103400a14801107441123000113000001c0c40100360701083c0310039543c0c1d0302ca03a0040756840c240300d210745031580c0c0d1400c1960b5a03400f03075100448001c2c0030390080300d0080321008950035000c0e070309510420280d840140b050301d22484800301c00402102c01c00003001c04402300d07400054541044c0c00c251010655000b0032600c214080310445011585100468102c5951401c0c0003401d828a00d82c62030007400f559104890003440c1c510380c40c41841460b00801f11140705694104481da0701030b400344184403420340c1e00049100c101000a0005007040000b0f0040484a0030101d0038684440c100442800c13884e1146170a145d00400d008840390306070081d10780901810701d031100d2603038101440100390189001c120300c01445642c40358414450a980108901c80c2c11100741c4045280c040c400c0f8140070581000760b001407060404060f000c3c0980d1040c80212a41a8003901c0703140c0c074100042d04280c2001e404640858201640 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 364579595 1250 364578345 364578367
    0xf070b040f02060a030609050108030a050d050717010e0f0f01031e03030204080f010b041d0d030f0b04020a050310060f0c020d1703090f070b03070905100e040c0e0f120607080705 78
    0x4d001c0301c0700c4503500410082d04061a030000e586069012407815481480603044140c3c0002c00c4d11032141c00e202000038680e44201085803410140080500142c02480010070740004547c0050711800c0e001c0d06441c0c40781c0b2b62016074600e0420921014144550011040c04805881c0e0724007244d0701d00078580541400d803101d0340f850520542c0f500681070744e95281c008903003070b041c18090a2080c414041c030300c4155507020800341e40c0f1140201c1e04142010758800f00071803020030507408010401d501070310440d04c0b1202524007a200341d0003a2480c1000b0840b08800141441c440d44084d03042d038016507140d40100702e036542400701c0d645607042c08543d1201c0c80907101d0b40d050306003400303948242000d000a0901e10166000503091140d150480103100200b08101300e00190458190306c22504250b0b51349800480b6003d08560000700e82c3ea0031759100d4140008071000e0365000b001c000440b00b00316006515481c085040186126246844c1401030b08800006040c40b4020b20205900c2002d41c10403529010341c00321 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 364580845 1250 364579595 364579597
    0x80919090e0f01020703020d050a030e071202090907030c060c0203010b1e120c15250303020309011404110d0203120409060315021314061b01020d0b060f070b040f0206 73
    0xd010101e58a00c000c0303056240401800b00100201c1000314034045503a1030003034540d4046850301c01802000910310300c06a100f0340c4100d1010140509035591151100d800740c0b084501a031050b0700c1203031550b01080080f80081a003d003100c1c1c0c05213081411034038280b81519241050481070b0307419503941004210320744800800608580184a640848078039400030042c2c41d04005108034925408486a01401e0321501403a00c0d01c409194140c07a01c440c03d03004841e0729000e580a01109607650720a0007001c158140d000741d40940d0060f4000e02c2a100f507800041d4540c00215405058082d00304100e0000742405e00e0006d070000c1c0080c06590388807040150f880b07840e51103a4480c469480d5110000c00611006103280c2800d0f581600c0154580100070040450044450080b44c4040021016089455448004545035550100314001180e503065210900035004004440240c604140307815200f4900754085030303054040a80c003030b8101010f5803074103902a003009108590744904103802c1005a0b48902c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 364582095 1250 364580845 364580849
    0x2070b011203110601060906050d091a010305122d04030b090a060c0801050f330c010b010215040605060a0b0d0b0411040807091503080c03072904080919 67
    0x79101c2089030020b180040c11101d41c094200e00c2508070f40014800564054011011241d50b4584a03440c0c0742c00c7c80c490f400038402c0f85401400900d880c03000d50318040300c0b90300c1141240d000b0000c1e9800664150b1003101076101d04090b080d000c00f107010f0040c090303100b941c0e20501d9054450780785600b895100d50300c00e00c1220003503c0d07440155001c1c2c0c1c0c0003420000e06014200d20a000351409031501d501d0300c0040f84640c0f4901c80b80b24461440e03410304030014a985d084008100c840380711400807038540c0c00e15150f910791141c03400c1d00c00da50038040c0403002d950000410480341c1c190202c4204442d51191101c0009000c064071855100340700a00000750a11030001030001c01c030100301d0005141d52444104002c40d0038001e00e5201d0050103100030011031901090520031184155400303d4100325040c0d040c050040c40350001004c04c500481e04010248000000c0c0801e00e1041c02c0c0c40c9501d064002c240301ca601100c840140c8081c601500050014031402d0252880c644085d0485042c117007041d2001224000d19 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 364583345 1250 364582095 364582109
    0xf022410080a150b040b06120603010f060b040e0a0b1f020102070c03060e0c041a13090206030403052223030c09041103010c0302070209061c05060c1305060a0e100302070b01 76
    0x101030685010001407051300c144200884d4204968120400800d2043c0207c64407114803145050000e2090b403000c2d08640400d042002003001403544881028007190094062a82c1d5010041c0000c1d008959503c1042c0d03920000812144100d4903603d036640c10b640786842100110354090001c000010000b200042c059840341c100800c040f03003200000f41c50000b1000030644a06d04080e00c0980c49086078052456002c401e440301b00301d200b5000c4450300500352810000b50019400020801070562001c003a1400c1c800d54101c54013000728613421001c0d45445401010b216581c20301e502d84030240403840f05849018040e043c1c510102c4010001801120225000e81d07840000000c00c07501440c0a1003025101c450a040440c241800e580108510b90f80047c042401144901d408003c00c1d4640448013103400d9210084980a2400c1d44a030082c40c0c002d030140d00050705c00210041050f10b01038055960b9000207644105070300130308804012016011001420615600f00103050209441c00d074500d029040c1e03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 364584595 1250 364583345 364583363
    0x6060d0e0106050432060303040b04030b0403030e0a05030406033902010513080f0d1805011406010e090a050a0e1009020f04050103020603040f021516030f022410080a 73
    0x240c04144130035200b4540355170292402072000074a0420350300080c4003d02d842038003418420f640ea0f00200c1d00d140724681001c0c110302d03400310b0000100010340f100345201d03a22955003882480300440c5026954020010001c0c6036030400e00041c000c0714401e030312120340d4107090300514580d4042034800700f8124107030080b40303a80300c6a1010603809840e02400784541214100003120300c100c1254895030480d00a0044104001e030300003030703482c0f150340d80d9401454119102103a840750111188c54194000e01501c02c0380c2070014007610004406600410694407010000361034621b403a0340390b03804c8500034a40101f00200d80b03640c911807041341d50401c101505e801905400d000170b40b0a041c0c0100941c644060011b51710032400c0c00e00510050300c4500c00d5a81250703200301c400c410b01190340b00082c2c10280602004105c0794021130441c05c2804942200d120345402902c1d03099158040c1b42c002c80c4c480000082c02c200072517598030403502d0344032840c0c0c0081c0d10842002814410b0743c0c0381c400e0a400c0a212507070075141d03500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 364585845 1250 364584595 364584599
    0x7020d080c030615090d0503160c050103140a020d0e0f030a0905030316031202070f0606090f0510060c03021005010602030417070501022d06090304080d05070c030b06060d0e0106 78
    0x500315100315044034a041d40c207410751400c20005502c4040b42e803801481858049845400d13519009940305003c1d0344a03040c0c130345032201c181c001400fa2110040507650200000300024142d4041d105100c1807491411118030140d40d00707014240a0760081c070300c0f079140030381e101c43d04228084140400c4d1922016070380070b15030314642c09000400400040d0000d0744240c0040008510b0104009083c242c0540e05040c40410140700c1d103c410024000c121015104c0052280d000003044015072154055a619101c200002e4400d480100308070b030803c407084c2c01c0d4003c81420902c1003130f00643d00c00340000d109204450344006d181e102c120036604203900c40e0004d0b80c8046414864480d01e1918192403505c1c1d42c00034035580740b030100001d6941036411012407144007201d44101004100c0c000903001411208101d0b4500d04024060075a01e038024030892070140140c0b8035030014503204070100c17442a40c0040c0c0c010321160660311140c403400b60103000280e02060400c0140f2092605010308001802448000100c0c94 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 364587095 1250 364585845 364585847
    0x3090f05012d05130f150516030f02120f2e090c11030d020d09050a050721051209010c050a14072c06010e0d110a0819030c0201021507020d 61
    0x801d0b80075070581c15824403040007411132851000e40301268101c46451490b01003803c4c5070810b88034410b41d9010440c1024200b02d24014017540145405406981c200240c1c0014480d41c400c900600707040da01402c0e44480070680102a4080c1c1d0f98000446400000700343e00800b01d5010800c1c40c0c601c600c40c05d00d804030380800c6011024800c0d044000914104100301e28914480c003900ca204880b20038020b0755020031441c6e41c040301035000804441d0300a0460f01c1e0714441d0700386540d0321049885944455240144511440c152600d1440300c8994401c2c02814207840c0455001540d41080f140541004030306950207022560810000304001e0081d45120100c031190348030b2a00300760f03040d00011104480c90509081802180c00490b15a03281c0c40142001c0d600c4440048807400c400000e50b9900c040105a8201032003c0b5822545800604607602c060300340d9138400d655204c120815400100c41045000038010902581c0d0421800744144180d038510600c1c0c55103800050740554410b40140c0c4011419400d107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 364588345 1250 364587095 364587161
    0x5030a060b120a0206031f1203030911010221090f0a0f0f0b090f01030e070506030117071707060f12020a1d0915060a1701060c05150c030703090f0501 66
    0x102d80d8960180c0801d01150700810303c0392001038040b11032a40d030b0342c8805000c59680056a0040c1c0990300c0007210b040c46500b0024041c06034501d0a80b48503c20308291003a40d030000407404401001d03040520b0081035002003409083e00004291908005100300668580e519050000301404c180c080881899082440d2044d0401b115005140c140d6020490a580390f551404004d030502d60900c0d0210b4001145202c503400c01507158001034000340080000708500d20f0300107a642050014000b290001e90b078403003854000300d1840e854004e10f50080306c41030241d00c0c460340403d002c2c0640c5040c0404410842074685003240d00402070070700055194410582d11581407000401c050700b0850b04000c0d06d003040303000b071145008000059841520002241d1040f2070141c403030781d8405e81c08502095420b41e5202d81c050310064108404403101d011381032008481071091003865001c0c58807602c20030f0443c0d46a500640c024100b050003901d48140d01038441000407424060000280d1080d5451448075a6168005000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 364589595 1250 364588345 364588369
    0x60c080f072303030f060d15141803160b0c0c03040b0a17060a06031a0405011403070e0c0d0902310e0a030203031b040f0b03040506150102030313020a05030a060b 71
    0x483e081002480312030020100c40e690450002c440c5400203171160703d840740a4090151100d2141070401a41e011a50030701081e083c07203192a01e5800b40c6008000c0ca9103500ca100f01c2c0c6c8070042c3e13409001c4600c00072a61003203509900c1520188a1480c04104907519899a005644844105040050613049255124007130f40003050300484c2414050800400040f007441250084000701a501d203009001c02c0540705116407030200240042000b035071108007600201050007181d0b0301910946070000303442201c01c03603181d104505080ca000c0c2040122040080501100d070b00c1030b80c0c0328840729026000c01c0c03802d2404801c011003c51040280700c000c8138840c01950502003504405401690b243c102081d00031003120744c016120703c20500d071100020314030341e05402590050b0b4154403003008041541a10f120045000c0c40c004d000312803880d0784400d503800200001454803801170f00184081801d06030031007001280b981c801020481c2454036400401d140c030a0342c2100703076480c5488030102012414010302d0790714 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 364590845 1250 364589595 364589663
    0x307030b16020a02190614071a06040f06030f0b0601020f03040e090a06050106020609101505060304080f0c0a052b05030901110309011e23360124060c080f07 69
    0x104200740c689540100c10011a070705940c104c403110002c4c52a036070740ccc1c0c44818500902c441c20054113440e03051034001c2d8002c1c1072046034501e803020301050066000040e9110020700c0032001714681800e1011861800e90054032181d1584030382d0105000007002da0280f14081d0541e41d00078a440c1c40c0205066103840c0d00403415000003440c01d03403003100a5560203010380a9440030340b40c0c01d65070b4a0310700e40103203036114981c001d4541c1c1b8404a00840c03241c0c4040380c26000f4600032801c03181c41180403840c07021030700d2000d64030302e80001030301e4040d080480c054400366a00095003000081d9a044165110b8680d600441b8005602d07507488444103010b1007040074042603002a50790070012180c0c58066800303445134001c50240000d18400000e242e06407c0c055000c0c03003e41d40303111141c0c1c0003501c2c00302d510380c04903424040c110b82d401c2041017034074078126150070000b4540c0002190199464084142c4000803106825246030300d0800c01043d00f6902e041c0240040c03403140400501007000102100880040040940 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 364592095 1250 364590845 364590847
    0x109061a1f02010f3e190e03030c0703020a0b030606070201031d01061707090608030406030b060c0a05010605040516080708150901030f020928020d0b0405240307030b16020a02190614 80
    0x3045c85220741c401ea038000c5480f5403444c2e181c210341c80700a840401c0b4040d0201c1e450b01c00060310340b454031004500907007124401c0e01c207000a151964001042030208881c801e80103e42030110501640c070a8010105100810900c906010009086142510215000341103802c003090031602d0824000c2152100410083c5002c000c03d6043c4032400352203200b144128403c140e04c44445140540c1e40700215510900f00c2002c40350259000c2c40d141d4060b2038140320b1184201e151400080801a8503001c55080340c4056540b02203650b01d81d132064400c1040070303210415802201c4800c40c03030782e190054180d018601541035001c80d00150320400c1800c0400408040200480c40300c0e20000c18803580100202001c200c0016803284010141c0c10020007400341c0c0c00b0b034800c1c1003c0601151203543d4448c1031042d0500d80e400710490f0840000d02d6990112448010010520311b0000b4101d101c100c03070070403c1c11401e40b040d10f84440142d000201c2c0d140c000044130800c42840e90702009819080040c0b0300c0801c002078891 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 364593345 1250 364592095 364592201
    0x10302040302040e0610061107090905030c0a0b061003090812040c051203070512090d080a1806051e0a020706120f0204031211010506010e0423090109061a1f02010f 72
    0x150f09e40c146403190140041e103d18144041280034019142c0043c4900221409503a40d81401c0030140ca060f03a0050049010319080058a84a4040c0d80712494000c09024580401d002445001c03001c000d00594292141000c0810669500b08500005003003500003140c4074090350074458102210010b000f20045410494145140c0b600203a075442a0341122070141c0341d03d00340406403085001540e01d0031640c00700c02c10126406400c0350181a0246032010082d000c5510803442023020301c00c0820354800350780030340340c2003040a01c40c404100009100f603c012408040740104502645c120350421149840309500d141070440e40309050f1540415002c000307000c01d00b05035001900380b4a8000307002e801981c1341c040304e0403040f846000700702d04c280d4200301000451504c45821030013005040b00c11504a401d0210105094000d070040354000b0328028103c0101d503440581402088255100b568195500c07100349410750700440c40b607441180300721480e1040248142ca203503440800041c010802c6a00c04a140d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 364594595 1250 364593345 364593377
    0x3090406050f031e0a060504030305011403010c140708070c090606082203030e03130b090103150e060f1f08010f05120a140a17070b010e070c11010302040302040e061006 74
    0x2502d04821055200031340c1340c020042c500d03803c1c40325042d40074003018141010302040580c55840300303049444040c04140b15a10b00c800b01800d1b156841550400a6203100e29035030403181007001010a02e109101451810500e0b9a4038070600c0c80961041d17001c80c1d9144020001c05270040d410641c04840a1074040e903520000001120444000e5030180c101075460f03c0d1303080c050130108121000152840d40c011101a950500380801b40e10040d81240040e060490b000102d026903c0b00a0a44a41081e101e80540e034200c18050440421251183d101ca0b1107070b0701520940301b840515107800100d5485042d59030400b61085031500d1180e00ca5401900f8454550208840c04074200014541c00610328005001c3d4440007403408001c04e0000d003881d40c28070304144107400c1740701c01008070521643d00840c407607985502d82c501181c030031102c0c00049007c400c0711000085045d208404000c0e0141801030610792203802040030bd03480000800e03002d6000d04c080c440e0b0140f101e0300341001095945050855201d04c00342c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 364595845 1250 364594595 364594603
    0x150f010602300f030a06030302010b181302061e040302040c050301080a02010c061506050c06060109050d06020d02040b0315241602030a080703080109050f072f0f03090406050f03 78
    0x1805824400c1116800c0c0349814a40b080700c000c15640c1001030340703a0519055400c02000c041c40110090740c40c2c40300d038a5890404494410704151106401c41240d41c4600649048400e5003404a070701c20820080c10503080c030148400e00c0c004c140c1d00c10098441e0308500c1880101c60681004405010781840100804640051040b150750f03030a10f01040c204c170f007a01c3d106010741a50109131802051a100104d012036000016000c2080144102e80c11a141c903030066800c810b041c043c46800004c1c0444280c0800c1803a002050300d94007810300186460381d10040d403640d41d00300b03660a81c500d0a8100c40c043c01860240c81040e0710f244801454490300c0101403a10321148200a00c1c48028080c0445404c10f6540c00d000c040180e40c1c009080740e0b50f0f259a40350003001e1560034010f66441c5440c01c0049140c1d0542083d940f1304c9404117407203180c02286200c500120780c5501091038052203408030740030003101c6414000841507584d140001c544641600041000b039607010f0700054091000c1c96803090380e981d0009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 364597095 1250 364595845 364595893
    0x40f2a03112709090313050d02090402060f0c06011805070e0901140d122006010509040f23030322050c04020a09030c0e070809011e110c150f010602 65
    0x4241e6030700203031502e07011030b42181d0512a00794000c443d04200b1100e00f50200c000c0000740c4c080400702800070385400800010003121f22003e034115103034100050041c20b1850040000301c00410011381081c258001451825500740c000c042d8200300308035407101200c0f49010b05034100051f802c001d02e11710070038030100d03105020500c2034407100c0d843c0c2081503c3d1601c0c0c010304280c11a41122130322090800ca1900a81802030a28414010804075080d0a0114802040c0c45041e100003c1010009880d191034038007081103c0203003504e00c2031107050141c0c18030603c10340114003500c060000d51344034505510069041c0003021543c05a041906241c02e00081000c2404080004100e03001a101d100c2c01c0411200300031140c000130709088001e11f0100d144d076000000b85200d180030780e5032141d160b500d055900f400d036000c01800780040540c46088440320346140e003100480c40340c0010000d003840700302e100903441c050800c9170ba60301d100f0942d414005090901200c85000d001280001e0070000700381109103080310804 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 364598345 1250 364597095 364597117
    0x14040c08071d040608010f06030507060504080a0602071104180c140105030a0f0b370311040504021c0c0306050615040b030c07081b010b0406050a0e06040f2a0311 71
    0x20400c00001d968071540240050041c0c1d400030000e08004d4141d89000704023034001901c0900c1b6443c400604c0500c110200d4094271641030181c40c000086070303256006500402403c603102c0c1405840380d00316840d14030803003480f0a0b040b0b03210110702180341001c0c5c4800b22039400035a04070900c1d40c800c1280c0d0760404101da40081264000140e000754490980d002030850000213a070280403105030226040341d062083c1102120907825525100c00036051905201036444001c2056450a0202406d850160302580d0f000d8006094000b620031460702c159040000e4020490b40d20001c13850a00c00d005141c45402c0e07001d44203440d2203a0308035003007042411704c0c01a0710408403980b0000000400c214180800d440c00030358030108103030322108038981d0038421248403041d810341c541ca00741d110300107480e16001d00421110050583c41e6460b05105040c143c48100803c1e2980058031084598151580d6121725044d860841700c83c2001164000c02d0740c09240011941c1004050030802c100030203003980000c8804200e06 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 364599595 1250 364598345 364598387
    0x60608011a0f030a02030a1208251b120c1109010302090402130605090c04060318200102010b0904050304030212121206030a1a16020109200a0305060114040c0807 71
    0x4840300182c80d0200313044000b9014014010030800b0403c11501180c4000c507251500b42c00c541e0349401c10713a5003030f245451f110700305010340600d08020703805142c2d4a50021140f1400110360200354a520b20b03442c1040c2150f070001447d20782c0304014000094170180101c0401c0b1034100c0f10394915000556860750140020340f10b247c02034503010b60748c072381d96114000500026107612001c1c44c2401400c201038016204901c04281024a5a40444005100d02c03200c141d02040b1a4900d02c00c00007017111081d21300d007034141999a213142c80b11590b680d80821500c107910643c011079482e0704600c180a030680d551070810038290320035011240031944800030b9503040c001040c403030100c40d03959030000b92410204120187c4004120851040501032541174148105052129100c56050403e030403422518070020180c9100006007120b012000d00782000303490310100511b000565030f200c1e01c81e2403d2400a074850b02070003c41c02d4807941c040c00d082c0600513201c1c51506107107880b4038000380007400c5460700100224280407 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 364600845 1250 364599595 364599619
    0xf03040320070803180f010918060503030f0c1507121e0207060506100c0201021209011e02030901140405090412120c020106080c030d02031e04090507020a060608011a 73
    0x2860080400c107110301c0011224800e980c1da150036200e45c000c403072805c00d919000d158280c1e0f44c10100082c0c40007a00c180d44a0384034524100000042614070702c03040d4003654072a4000030341a50200050302c0b07560039412810342c0c2d42561482080ca408130f6403a40c8094540d04200b04003200380c2086650f01c00340d0f6039442c040384150100d4081c40c03030710000d003980050051000c52a1014000541d0165204250540701076401c00d04488044e00c04006d0503000a006070700441c00003170303500c5e551806002007600c181081400f074400c03120f80c2e510305248010319000503440841d040a8035a44826400014510f04485618003400d01010402c420001407010301440d02581d43c03e00070521610032100d201c051503000300510480a44000e010303142c6c0e440707039011a22440040d00308500c1c0120328006910303010b800541c50080844030b00c078440c211b01d5113402e904030014000011480114043d040c441c5c101903020300002c032914601042214042d411040180e03150100f803030250604400801c1e01710700125446000f1030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 364602095 1250 364600845 364600877
    0xa03150302090a09110411070201030213050612041205090109030227100303020106050f0a1205030c030703050406030f0603030e0402092403010303020f0609060c1633020f030403 78
    0x185803544001c2d0419a030200b007164911031a03006441c1d0301d104400300c00f03400c1040c0d4200000e50b00c041300901c8140d18108440740c01903011340e000740424451000e0b01454981d0303840009106411604800e007403242c442040004101030b449200c1100b030000d0030600c1c10a419440020045d1086000007070140113448203203802180852101008401048036410f0310f0f02d80802e102c030b00800f0500c0201e0140d820f0580c082240c0c602560342c0c841204000e04000320851406ca10080103410040094505d40008c10144914074000d0000f8106180a41c451a640310725094000b021101c0c070044103025240390200610000303600500c0e0f400c010b441260b0141c0c86200307202c0020882e20000146000c14400b1100168240441710003540c102c030f0081d000c1d1035861451241441e12a8000c580101c82908600d0010703009640481c05060044504004030400301c04075a25004094544039030301070848100110304050480b104554228260050b00942c10000c01021207103e900028000406200709030401d04d0b104 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 364603345 1250 364602095 364602131
    0x304030e15040f0b09060f16140610080a020d060e010f0f0c0813110919021605060901151809020a06090303120203130f021f1e0f050a03 60
    0x8090300400c81d032070300020405240741c00d40c00380c0710341c26850031a4000050000c801505130368101d04045c0c0134901e4820b20300d8101c0b0040d401813a0580f4080b100c10400004201e000c20301d01021401d00004001c941414800140b800c2e800d40d0048410394041c00710400161150700900d0045588040045104101c0d00c440034090010003070a81c041e2803070250300c00c0801c9001d40003000c0c6406140c591048507150074401e06020031000c00040d000078047c81036450030b4189101150f80c04603190482c94000814645a8400e0342e014428450008801482940602c24180900c542150702c8034020000408080101c144d08850351003007110303a41100c41c145100801c1d540042e040194000e00b0040e070b06884500c040e101501d81d0000ba000119022414210900300d48200c07801851241607a4001c40b034256a0b4401e07011050750200d0700100b014010a03201911000b4281002956841d0004c2098144642100c2c070358040d0040000c201500f01d15001142e004022542003104a140200317582190160b84000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 364604595 1250 364603345 364603367
    0x90c0c0a151e0f0606050901090326041d1815060307031a0a0f0902010e0d0f02090a0b031501050f0d06090c180b0108282310120512030403 61
    0x15840081140b540402c5582d00500301d411140c01c040007030340c0d00c459045450740554101c160100303a84440c2480462070240c1c00244420060840018030702000403c8001900140e0102600c4011300e50031001441164007002d030b005600c1ca22500c821003400b9000c1c0d54510400d5640c002845264000c6001c5803414084480599040030344180f0581103100140b40b0040119004582c1c2460b000d000b01d5001800d00074688400e40580d0b0f03240c50720940100f0805450244c42003140c1e0b404000600700300603191038144505c203500ca01d0002911010150904d414a002c00c031840f001142c505005000c80d0342c601091928091081c5e03035000540300c81c5e14010004106207940600520058440014040704986d2922000c2410500510800b041800151040142514281a020000765041248250000240c4032078004180c01241d41208800f402ea005600d000901010351140c00c20840000c0398124001c00601c0e542c9034940d0302d485941c940d40d840b0308200b02c0800513414000007040074140b00d4a03801003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 364605845 1250 364604595 364604621
    0xb011e0912050c0328030305090102130b0408100b0307030b0405100603060b0a05030a031220070b0f011a030f0601050408010e060103030206100b1608040f0b0306090c0c0a15 76
    0x154882070415a50f03c00b0904900d5100f44121401c04404d824600040d001d0710442161646402045a5068014110040040c23896650a129440d42021148034482c01402c007c151141e4071404c5c0364250f420940c1c020f0703410104038101484075124ae100000c2c8082181c0c0c0041c3c07001465262460018200555001440d0802d82005000720511100b0b074846100000120f440c100b90f079030b513402419291840301f04050040380700500d1200d03007605140c000080c514103802c0079204025035440b1141c8541c00800d400d0718038541440412400003484d001c0c0602500c501340100b1400880103154459901c0f0080560030703200562380100b0800e9010b0310544010b024042c000340203414000c5040790760380c802403000342d00611070000030801c0e88030100d6810303042e44c80e21b9131118a00400b6400000382001c6420040ba40114204030001c1c125005c040c2c0100070306042e41082d40e03a418503904000c4000000b0340030b2030414500f044000c4081074002802503249920107035596003a0b1817060304000070101c1c0c0000748 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 364607095 1250 364605845 364605869
    0x41806050a200d0b09040201170c0f13050a08030c0d120609050f150402090a03020f12061008010c030b01090302120f1c17010e071206050307030f03020c040b011e09 72
    0x10200000365000b07010204102c1d50204000b0444c041004130345641610042d000c42d44901c400102000c501a200340c1c00b41d801110b0510700380301003030b1540340d55100c00f10849075000300c40c0d0300303014030b14110b81104000e040110041d41081c1c030500d1403d44400c0414101e40c24819005a2a04800703040c0c0c001d10001c040030041003085141c001d8001403d010119000c2e452285503101806070391803d40b00382c48040c44041c2034480c0306401d550900c8a0b00c0d180100c000e6000c08072141a8500d00d10812000d4452414405440c0d1401d01c2c0c54a03107030941d15018581018103040c0080c402a5903031010300001201c0e0121084d2000301c0290194900b0416410403480d00f0340a46104000e410007046000f40007000e0340c0e554a8070300c0e003282d0080d903082c2c6800e005685280900402180107d803082034000c480e40d50818000034640d56400010b4079000d07155004440d00000c03141ca0006261f0103228402d200c4005403000d1003040d41060008001c0803c4856224001d0846d403400c0100d280705101d010050f1140700018 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 364608345 1250 364607095 364607141
    0x1003150209040c0c0b06010e031501090c02070b041d1915140d020a0911042304051e0601030c020309030105040804170304080a03200a06050f0105041806050a 69
    0x60003a500034005580181d0400c010b10b8201c51080c080348820680043c1c1030a100d494440046400000d0260782e1580340c440c0000b00c600240008903014003e143c2d0b80c400141c584581c0340042c0c02c28115900031036017100140001c01105810b80440040048a180d81703020b00d03940c910b42415a01420440f04480a280110000b6001031061000090326a68020035001000000c204184140c1c44c1c0c0c0001d40023000759204110300f052076003080c1080b14450580b00c0c1005e8844030f01440c030103d00e04001c011611083c0c600c4806040038450310703412484480455501c0703088082003482115018110504060340d030800c205410b0b10a10036201c460b00020020320641c2030605120190740c220b405000e25050740162480501b40c8000101c0e4220344581c4081e100030400d6403025183e605825081c1c400e81c03808890b41c50607003041400700004151040c10001170070309040c0049880794105030402070003542f400c6102c44009249c140c0b440900f55109601103010380e0b810104002500c0c80174514045a03041d6105 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 364609595 1250 364608345 364608383
    0xf0702100c0f11130b0a12060209060c0601091109010f0e2403061509011202090f04090b0403020606030601080703080c031e0703080606030c031303030b030f010c02010e030703050a081003 82
    0x783d010b55a01c126007030016000c9034850002104ca810018a0740401040400c215060400000c1c0001c50b001d240d0043c20005001d02003003242e0b0001d08413a174140c12440040c800690316100e035001e12100c1e100c100381482d28030070019140e80840007030309050001c8041004081c2d65812641e0102004110454200000b607040791840c0341c200303440c4d0501c01d065003002d407480000741d102a1588040140d580c441d00015000c1c1e003030000e6014180c0b2075007040810f00c80030015241d6001d04180103114100041d158a0141802810702e080640464481d4010318010031203c0750008048080c1d94000b441d82c1d5496076046181891840717840c50034401d0a00c0e000700038541400000151a51501036114803c2a070344e5103081106900c402c4440c2c18407a14240086600800c10840d4005058441c1c100020341c1b84040740001d103000014490703050301341c0d111400c811895070b0a000d56890030300d81344025420140d181d1b40140a90060545e6030042040304400111003c40640f2100019500191341000440c0d202003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 364610845 1250 364609595 364609613
    0x509040f0e0a15110418090203070e01031407030c0b0c100c080402031204080a120c06060e1b070b070f02150106030f0605030c0a091806050f0a060501050f0702100c0f 73
    0x2109581d820745880c5001e4090015015803440038101c80c41d420714203400c20b0300c01034086c400220900320807075413050600300681b0704100d080050207415843c80b855625628100d0821148090651100e42200d107080000a0504480c070003502c05015165486080030b969952402075940045500203090148041c825030f04013944a008a00075000e07200d80102881841d4141e2069109002603036020311031510109003c00300150aa40c0301e45050030401416460341c400380c6a554001010680c000300c00e210291449008045841ca0500c84150904050343c5442c04d0b107640081c0540c09128141144c1c480c020f100f44642032103094000c0c0420807079610741c81c000300105600e43e08081c1c401c1c5050008981d600d030001e21640c07030301d46c010958901e8a09103c00721000c1c180410a000c08403030343d201d5010000d9010f024051003800c20501c212052329200007404103a4034664800740c107002c000c01148050b1100d02e070450701001d40640d0156007145019804980546141790090950000750100c0b02c10404980 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 364612095 1250 364610845 364610863
    0x90d080706230f10030510051906051c050102070b01080a0501051b1911030a0513050a03080316090e1f061103071112030406050a031413030509040f0e 66
    0x2104001500c054689961032407841520200c01200042c00a01c283c0d03010001d030790340001c58440000c41070f81d4a50b035440c504960100d9891100303844004005039549801c00c1d080c405001c81809005891418010a03c440d03488652508203003099071000f020311109404070b41e4810383c4502104e4056030b4480d940c54546180c0402240e0719400c10307002c68442e200d449030010029889000d101d10b40b0210051120390030700548002001d00184a00c510907007a401d0015081d4403895840392540c1c0c00d24190b05004403905a041281302d4800d8401c14004240240252940668440c0c1040a9414803203c1615000c14035804040c1420040c010040800b144456903140c4aa880c9054403500c0d0b00c0341000c0d20202c0041c807130760507141d0091008401085c51f03c440d040910300c0141c0316000c0144002069400d6074495084400841d0300060060f00c000e6044c0300c1c2c42001c14200200c4001030401d10094404591031a00c003604008004c42e40f10380b107030350ba82c1c06a50101000d4100b0810902280c04543d01d0311014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 364613345 1250 364612095 364612103
    0xa1b0f020622080105060f0f01030605090c0d1407050406050f070206070309141e0409020f031203040510110a050d02090a0e01050a06080405150403110f0c150702090c030705090d0807 80
    0x203000c0040c2d0800f05029150181c04c004098011030042c0704140120410103030700d450304040d11a070001500307403034020502c1e00414001e0f15035680c8000d003007000c805565100350a951b80a03581e40030020400d9000b0141d800350740080c03070401d83d26a540c10003900d1030300031207001940c403100001300001003640000540040340c5030702d003c2c801000041000c00c0320320300301a81d040c1906400c0118940f101d01e800d0344041d504a100401c085034151b21078000c245004400c2d01d020191040000903c428010104881c41e5542c207003030b50510000c00081c00c0620300c1d00403c144202800404192941074008580540b078140901800c03024031a076581b50f809006030000c2c42190301900003114007180c030b28484c82c42544581e4100000f02112045869007000c0b41c00020400e40030440003420b0310040f441c05100c061800340c03861000301400b0040b8010000030303140750101d5803d555410071001d001600c8440180754400c44600b003c40c0c90f95074105040d10540b080302100395118001c10b20040c104009140504012409 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 364614595 1250 364613345 364613407
    0x106020321040201021e100501090c18060e0402071103060415060f0521071e06031b120b0a0812030f0708010810180602041502060c0a1b0f0206 63
    0x142050807007411030944020340141c1015091301046800c0003c45446e00b003d040440c0c0d03080c20780480420842d0400c1e00400500d0b602d0b0369403900c1069203d00d0120107840381e0000410300a09d0018040d2150b90b140c1ca045004507000324130501441045541003000c031002400f81c80d0300f40741038540203007110401c00c03a0709641c1d468044003060f00d251200000f03040d14806803003c0c00703482d0711004918200103100128522845190004144184602c0e2170140d12525011600c080381c3c240b080140941e00d281204a211940c071000303004c802030780000010b6040c100c07003400059500181d400704080b20b80341c1e04900c0b030382d20440c8103000558480000a41c81219084246185900c54000481303940c0070a1058920990243c01c84000c401070701e902003840b4109420303446110346240d50b182d0341aa00309038400140005994414017803142c05201e1107520100303040d10b29140600ba210f0180202800541c004c448104980210b010425200c1042c0491a0003c19180c0c8501071081e040342c89002410044840440c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 364615845 1250 364614595 364614637
    0x402160f020307081b010e040906020a0504080c060307081302011112041409060a0302060f091f031d03030106110f060a0b1002010b060a050703120606050d0b0108040f0b04030203040306020301060203 87
    0x1005c200ca00380b503010148640502c54550004454011507443e00b5030340195034101100005920744000c01b0061465111140c81d185480345882c18200b00201c41e9005145c20000c001c165640440151b0b4000d110312a0450b40110714001256128469030f0940e001348100342440300d0355952034015000701c416400d203200c40c580c251418041100400c0d6151a0029000e031414001840d01e000034061007405145018248200c940c00075018143e10b44010a0740c2c59101005584142e00d40107800c6a0700c0404050010401207511080c1c0d030307200503c51141004000c402494110704c0900080920854200031508a41000f10302c4000400140e040184034545207091800200d0060144410090008010600b40702984005903401ea00c10304c4210308104001c842008100c0b154031030320000c1c0c0307403560328103482d0052802d5100403104605502418403402c40308000004800c1403425990315480092105540c40f245410b924500035a00010041030000c4004203002c0e0b40000030b008840c10380813002c21109 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 364617095 1250 364615845 364615859
    0x718060815070305180a0c030b0916180605040921080702060103080a03020403080c0c03070603020c0a060c030e0714010806011d040518070303050d0b0a120f020402160f020307 77
    0xa0214a10301404401070002205103002e03500c07a55004920b403000d0110940001401c5042024510003202c0113141c4c254240140000b81d40e51a03401181c40c001025180c48201c561340d803401c00d52050381d0705180c40e601088070000594105000808028209006000940c64002301c8a0072040c1c4840180000c10a04e45046116401c00b81c081c1d040740e0040c000d10317400e54135084010780c4882c1075401031503001c100000000b0000c20091241612403000303860740300d000c00200b5080650650141082600600c003d40d0127050100c0e4000100b64001400215003180c004140d0151144004040d428010088000760008031401101000315090f039680300c00384d41d00401520501c103604040c00c25002d54188000c0d46081660106400002e58606401110988104c00d450020703180c00c00c8000550120b108076001725580140120071104032032082c5900d00f005100000d066800d0b03c05028030308448440019500c0741da040b0b0302c1182c29224800c0e200034242c02e00c200c600c4c1403014100d0280c4552000014a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 364618345 1250 364617095 364617103
    0x90204120203060609070f0806011412250f081e01080d0212031905041103010f02040603060f030203190807060501120209060102070e0c0d06080304090605180601090911090307180608 80
    0x240350661035801c221074207e4022a00032800074001814040c041803525007110400015144a6813091a0b0000d1480c10049840c2c5109859841003141c401060652034050f03001204400114050302e0f10a0b400e0384c4100c0080d20b00c00d590f420303009442c03142c000042174000d00412000001036494086402415080130542c0f098481250a0006a1803012250b000380000343c10464020b4040c1040c1319808007a400000d003103e050421a60310141d00282c204030154040c02100020030903d00c84c0e6090903d1138000c0b98a94000c80c03012004d00c0803d07100c0100b04001d20043d1040707690031840801056860348101001c1001c4e00790f0a13449400b4500014007950700c006010703000e86044041c00802d544404c0b0b058406034000c80c1903211280d0b281c66010502c0765082014200400a450010414500c1c110520040740c3c61801c1c0b0321a111044010021240d8014550100b111115a00014500381000e01700c051070103894145c1b80e01d0300940d01d00040400d106030010310300d1401070600300040c603a602c001c10781e1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 364619595 1250 364618345 364618351
    0x9070216050d06020c01050709050a050a0b040b0a02120d0c0801051e010e0607020910050f12030306090a141603240b0c0708240a0b011e030204090204120203060609 72
    0x240560304041845541400c00e103a01c40284a66805820415100304841c251481201c00400241108504102c9442e1104000009100545d52030f00118140290a44180716074021a041148002420810140301b0080140e22a096540482e00e54a1f0420008007520610741841d000813800c000110303061602c444000105d010719503030149291503142c019501780100a0460780e00401c148400c8001d03032112920710744980d0316000b800f203d5905281c01c110301203400e4400c0c20702409020001d0005000000100d907000541100d010341d036079585410f500003404244004828155603481031111400076001480110200c0d61009d0080c00101004030b0105100c8802041200c0c01c408400c00c9580003020082a4032182c00c400d990180f9200e11215280008003103031596050410102207114200c04520701e5001180f400041c00781c0e600600c0000c044403206007500b0100484007620700d0f6517600030390490b00240801d860654540e0b998280b415112100502d00303a020380911030000352140342082c83e90344 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 364620845 1250 364619595 364619623
    0x1140f060a0c260c19030807080411100503070f021209040b0a03050105010f090e03040e01060f0c0b070c1103121b0316080702130e0c011809020a090302090702 70
    0x708240e04808111400341d0080300a45140f41c00540101200d0850701c81030a100080d81c2d1040c2d9940d03441d50105241803100000000d1300382c458100500042e40c400181a040002440c01c00c00603202ca05000740700c600c05404695002c14007125900309540c010028610480c220f4841c41c2d840302c0d0b02802a81c81e0070842007140d42c02141046001d02e40d203040c0e8000c003441503010b440815496200e03500c00d401c4900c2038001c80d40d60f14151908000d0405940180c41c0300c4d00201020790700703141ca05400014040410301801041c444203a4101d00040c3c450b04040001c0b582049000304142440341c1d0142c0304090040c801d5600e2010780002503484d00f40001c0d18003e4a403400c856510385940c8805040b04070000130402c0981d8002008a0665081401880c02d2614024003615544518520402040c154100380000900e8282008000c00d01008140110354280a007420032604480e115042c1c0c01268a03008246514070128211546070b0b8080b400300d050ba4401c2d101003049454038641660303920b40b03400d42c00e5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 364622095 1250 364620845 364620847
    0x9010303080c0a09050a06021c030e060115030e0a0c081e120c0a1703060406091806020f040302040e0d020729070809090f06090a02090d0b040c0308030f01140f06 71
    0x590b00400c004002c0078080402d01c1c05002e8507403a0b0300040c4080b003541d80020016403102c0c5010764001e12040398003054a440c2c2c1010410400800000ca884650512804d046580b42004c25003099000b41c01560f41c200e4140166a4402c41e10300c0d0000340b892880c00750340c40522400c070803d5203d0310b0352003170700446041c039100801c10b031509620a8405584218080e80341c50081c0303255000065500c1c42c40001844500401e1910303494a0401d11085442540c0468406410240701c0d001040700e20032104400c1d5049070003d40e58021407410840c06118680c002074000780b4058868580300070200791014544010360a0391340311131340d1b540320038030f00b04103810b61315054207003c034589806854030001402d00d240300340e80040c00d0216400004440000888141903c02018010042c49141c00c214465111921040450800c00707040085040601071103402403150f00c403080420240031502e0034400086501a03202a903031701d4003480d4000030b640c2c280302c0d4282d88000c45114020b14901400380051980c0054201 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 364623345 1250 364622095 364622101
    0x90305070f030509030f0c2d01031d07080303060906300a080408010903091505040b0702120a1a070318061509052403030702060318010e0307060e0c0901030308 70
    0x4149620751451086081c03080c04c200c1e2102d95101405043c42c400c2e01c0c1d1006d000b15282241c20310000344102d8003c00580d122854200083e40050506864100020300c2e00041d80d0051030768003660400310300f4007210b2070b02c5034210001d03889400100442c801c000984030000580c5a41c41800300fa80c1d00401c208024021119011400c15507101c241c9803103100c804100c0700401d065072515642030340301c0d40044800741d4442070b11905154100c0a48002488d0340345020213202d10441004040c5d0080c0d01030940907800000b826829940c40b030140141d06540b030416a2003413513880ca4414595191018414140c0001600007513006002e80316002103039103640f0074540a06030a0350390070700428a4144001d182c000a074400701d80a801481843d21a40d00d2828040c00c2c640a1b6071011001c3c80303c00c41b018400e134420800580140c80b10f000342d81c2c000140700120741107032408240c040d001d401c003048016082e1201041e10011b02c0310176003104880c06508419510010391490a00952540900019021808030008 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 364624595 1250 364623345 364623353
    0xf060108040602090915100f020c0112060302030f060414030a02073011040e010203310501020d0b0909010b09220b090703140316020d020d02060d06031509030507 71
    0x14640c414482e550040c0f40100c0d10780081c002c06402d960002c02c2c0361221280005034101030803a0f510841d06810042c0d03d664090340c009548002500c0e915040200d05500c0c0301c03098805403c1000655402000c1d100d030440d407088041da8403002110142c803c01c402000414110102008442c28640c40368045d00405042840c1c55038004441c012103001e0044485800c02c0722043c4000c0e1164881c0b066001ca0300c0300b0910ba08000a4070040300c1960310503403041003403107282480c0d58a580c15880e08d040c0e240880301c41440e4003a00a0f0310120f00074150b5400000c141352180740b264000d10710a8400c941e00c240d5600c821943c182280c1c040e12500e500b2039491400310f0f0a0005811138042410583e007031110741903003183d5a1902007007055424034620741c4052b4003802000300000390310220301c1c91400117509160700e41e00748a00c0d80c4045c0f400039000e0305990300040d00759128002e80034800c1da005012280d44185401c1d0080041c00d281c070007030f24580362000c01c005845100f40130341c1d40c3e82901955214201122a15 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 364625845 1250 364624595 364624607
    0x314030307140a09050f01210501150f1b0503070506010e01050a090c02060613110f0d06170d081b03070e0901080105101a0c06040f17030c04092f04030204140f0601 72
    0x200c07450610048030071191040800d0b08c07003201480184000400c1d20b500d0103090000b44400085100305001d200490415020741c020901801103400072541c0c60013420605103503045100b401c2018001e4018480081419060482d65034103e500c29206013400b10395800000b001c449420380c140006801039004184a13140403084124105c2e0500750000f10a00030540071009544200c200c00c0e0045400b01c1d03003202c101040d11480006100c0f00c1d154140300d1511508840d100c801c0d42c0c0001d070130720903000c2c045020304411142c0130308901100450690f0384e04048501400b00300664460a2040f205100040b40c010707010f0140900843d10040e65002580c101604174000c807004c0d108423140c1502c240004903481300f0420a05010380d025058001c2c0c130f012107040541e840c94000c004818604004c20500c0300c844010f03401c9508440003103000080d42510000851046544880b150091215292440240707034a801e0040c8101c138401c54040000810788401007806031012140c0090030b8120800099081d40604 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 364627095 1250 364625845 364625869
    0x1706090702010f060f03020f0d080a0f0306090903110d2a02040b04091b091b0e010e1207080c031603060902010c15020301030b0f0405060a150314030307140a0905 71
    0x7000200d00c0e0b50054980700d048500c543d01501550b03050400800a500300010100c0b00210f0a550702c0b92000542d450388480b500c40c0350303100c1040121682c0080711043c401d44c84207001c0c005010302031044074503034200205112a128000400e07401003406094100b0f00440b6405901810114088200c5601c21b0107140c4043d030500081e41c0040e11f03012111000c3d51144248415188106c24600b01d029080714109000f055540001458070310b0402c88441c404401c400c0480c800283d450200040c8809100485050600c000c40079040301040e0183c03041010046410029202d071700f01112015000300040660790210f40b550100b40740000c407414000f2a0270b81d000006024010704101b0a4102942c0d01c1e54103814000d0305004159a02000500800401107810342e00158003950341c0e15641419110640c40720f401a02d821101035895291480c000c141c160380500031074000b202610380c48508094191a0ba008580e4840001c1c04040000d003403204070025107400d18196a40c818283e410002407051070700f500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 364628345 1250 364627095 364627097
    0xa0b061309060510030c0f08191401091104050601090b030c390c04060501080f100b0a02010b040501061e08070302160501020a030606080606070b0c0c06070c1217060907 74
    0x1441e4250224086010742030040b1110060210420700e5070602428000d0142c002e0303980c1031208803040112a00000d8080f4484a240c1c50030b0f1811201c0c5e00c0c00d440c41c24464401c18943d5400c00b1090404d021030600c0c803020000003610284802e1f5110b10044900500a006150521000727001081c03400c880c800180651080b000c285c4140381208821365940000c3c0d55015a5800ca070400909800e02414000400d81d10015107003404485d00701000a040038000070f1404450241d02000141c240c144a03000300024038800b48402c2c6d5541005100034043d10311601d100340224140000095018803030310b40482c0705013050f200a00a1500e2020844038103401910b01c80400d6020f000d41245074560b5250581c00070300c40c000041e074030b52984001409968955004105020880d0304100840c0c5403102100c001c50344c0074000700352075520380f284010a4020811032900e540b0030482042083d41d084561401501e00940342ca04480000303d1048800030164050318800e1068a008102d4608080950340c0d00308180f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 364629595 1250 364628345 364628351
    0x1050a0311040906081006060e0906060a03110d061403061e15060a110d0306030312020901140417190302031602180702030306040c1412070c050d0504170a0b0613 71
    0x280b10f00c0e01c0292040f540048060707801c0340541205c0042c49126010041c42d4031304240064107210301c0002c4010000030012402000d0024031503009600c80d60201100c01036401c103040c0c561400ca07200c20020106030282c80d5495031090100d8800f8980000e00c01d02c0303088007044000507400350030f00e00040c011029100810900d51104a01c4c002d540306005400c0a00d25980d4940309410950760041c41c010002d820001410b1030183e0600200e6481a01c003407c8070303059100541d8a0301e90000494242c5450040c1844240d0b000c40c1c04100745004030344250841444104903200e00d002d40e00402020140c641c8000e02590041005c1d003902c10308050600ca945000a121080c4414807154002405800311603c1c00160070010810002c0d01d841c0c882c01030260050310f00b01e816000e10343c00710a05880358a03080e0b55800c6240001030320580c803d007041c102290f402410b490611140e680081c040740c1003400303403030400856403002e15910000096100c1c02c86070444010106509c9400512011031004004414a161 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 364630845 1250 364629595 364629599
    0x50d09261b030a14010504020a1e0510050c0a110301270b070306051306030b090703020d060b030307021003090303061208070f03020313060e0a05042306031c02010b01080c030601050a031104 83
    0x540c0c042101140c1c04000406c04d40740034410815070340c8803600003000440c5c449400c4038046900d8141b2500762081074036104010000703184240c81d0f034010b43c07290202d14440c5202c10000c0102c25070001e09008001c0d0002c1c0000560031901c0d51591400c1500c1c0c0c1c04828120000c030003c1040714640c2c6400008074100061003d440b000441c4c0d0b699004081e0842c05031721400d00708104121282400c0e84480c000025002c51403d503800685103149401018051544602e081506590280100e40c0c609138000d01c04400480804c0c030150142c4a80c079000c2d800700e8644480018105440d0020413103455000005034070b00a0300341d403074403204920600b0a504601c420312000d208015040540405800319032140c80309035001404000c010b2800e034205600440c00c010370780c500c420300303007000e034205440003c15050340b40d8410000c24901f52044060990000d5002e042000080d01948092500741e400e03a1040310603550011014008d10007690014001902007007054201842684075800360b007412140c00d4076250f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 364632095 1250 364630845 364630853
    0x150a110d0f0203090c040c0f08150603070207080c010c0201051b0a0c1e05040c0c021017070305011e0509190204030818030f01060f050603040807050d09261b030a 71
    0x6403064a50351250b90700000380700100d2001c200100c820f98003140e0038444400d020000038019140910920280600080410b61100b88111450040c803000740c109a20703880d155030029540c010900c154440d03405031000c20341c0c80d03510031001c5803003032038042c0c4445d850507250314946101141c2c00f40310100c01c3d00035600c1d208006000d00d0310303040090030440241000b00c180120721031140e11166010307510485c640500000301c10303085060245400e030100c0b00c07001c083c80000c1090783c0010b400c2030080100b0134403070100028240c05600403410b8500b0034100b10203141039480320030a812806d020309544003507038074001a059000500612421400000054202a9039a40b0043c80c2d030020814544205040f00350420581010011891a8020400248001450102c031074200c01c03211f00806025010010000d0706000d03451040700c071034680c41002c582141d19040d400074006104c030f010703160070600f84602d41044144400c0c40e081e2403640c4440038210550481020301880084000340607098099460010045 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 364633345 1250 364632095 364632101
    0x80316150c0207060f022409070902340c3b0f06090f0c250605060307050d0305030105270403080a112110080a1103070602150a110d 58
    0x1840c01c50300104409400c250700540302c132100980c0482154050103500d13a8031004107151480281481c1d040743ea198944103042e50a000305500000d181ca400081d019001139001420800c8641d0080b8203a1070300c0c5209040041c40c01150540900715022580081c04910340c84002400440205005c0e100300e82c0f02d2250210740081c0104002e00326074825000c011962280001035540702c0001c072a04c1d4014078010030007040d00080035041100c211000300c0ca403400d00c1c0103040103007000d211004046030b00011034900240a0602240c0160090080d12030008441c24800c8801c15410f902d5103480e421a820401071002c0d0031103981040c44541c0d40052201c0301a0820a2514011806a42d0384006458000c2102e000d0b2204000588200402002100c8800300c01c85801c510384040301452409648400d489500e25004942080310f85006102c2108200700c000784c1c210281110540a80745d02c5039948805a071a18034900100290720481000500d00d40c4165000080c0c11114a8499050480b010542e07812 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 364634595 1250 364633345 364633361
    0x70c320709020c0601090e0307080d0209060309010903030c020f03070b0402180f01060207050a060906081005040e030d0b101403040f120801050418111201061203020a031808031615 79
    0x9442c0d00140404414074140102070240100380000c7c4035486101c100c040e0750f03104000c0c5c042d08041020810040468241d011200c400c18003c020540764200044d00b04d00900400c03104402091a2031000c0c4011070010402c4a51851444040c50a18000b5101c00080c40030003071040380d00c203811051b84a40b480d14010b40130300905070f28124868560421101900d000b2403038000c00e09c80e500c100000c01c046030b031000c41402603e4452420001070344445c1510003103030110b07401441e805800c0060740458648000003a00142c5141070044c40100c2d02c1d24184402c41888410050008030fa800f0300d00c04000d10100115080380c03107910755540f04601500c0c1d030281c04803207465050014440100411403071401d40a4501c00c60483c1268030f800c1022542c0340a44c0c0255215501c0c0900c050740e5070481c038905c081d80a8401400340c0250200d007000c00340b5000351112042c08084010408000442c0215051964050103848000c402140781c200c0d40a6018010049010221140f0059402072804082180a5802 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 364635845 1250 364634595 364634609
    0x340801140708010f0308030a1a120c0a0b040f060f020f06010e040b061f03051018090204110304050304050d020a051207060f11060402120307020d030e09070c3207 71
    0xd018180300c1c100070b00b00c080680c004000f0144c40c3d81c003400070407202c00860350000440c04000178060126034580700083c0c400c801c590f900452145400c43d40c241c010035100c5140c00f0031101301c0180c0f0344590038008540940c2c000c54003a114900800e000541c02800001c100c41ca45004070380c03902146510701031421030b090304104981d0180d001840100442e040388583c0203c2c044800103000848030110380c82c0e41019003010340030035442d540454915400907001c0700107006101a041c508941c0310710342078007800303400c0744c200e014520b0407003000c44580c1c5d1002030b20f0190f83c0c8100034625091400080050b41075a00d82c0c2668007800382d078000a101c0c1e8401c0d0f48644070a407084080c1070140d00e0298090260b100203001c1005020048841c84508180400d031544d10950448038134403042d90490301c0c14558060b4520080d0800c210041d010241a00320780ba03010040e5084034040132540e40d0106c101c81c1c7c0207648400404111122003a208460844e4001c040680c61480d51103684c690407001542c03900d181075010038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 364637095 1250 364635845 364635881
    0x1106090303070c0b09010201051b0706150909230304050108010b0d020d1b120c14030c0f160c06030b010c0b060409020303181309050d180801050a020c0609340801 71
    0x49171542c080c0121940500d04008002d000c0c03082d40c1045610b0b1040e900020669079444010303680b01045815100d001d80440f40042003103502a28108009c115900c2480201c00c10302840f04140d008000115810390b507042c1d4402c11b01e41d18020300486e01b50002400002c041b0340a20801c0d210400600c070328000800207030390310443c81050010140040401c0005003d582e810f040c87d004036a9000a00d0300c000203000c0786119540c4d9074100e4540058002d40e40c407141d54120004400f030940d80f1000107184118007418601481c195110401e80c204c2d40c04203541408241a40610307804034080b6062190700c0100508003041000e0309500090650f40450181c504840180c031710070401e400c4c9001d00c000914002c10042012240340d46425941e14160402c240420440f10844081059a94103d00040903090000c0c0078a08041c1c0001010790040288520544105400140c1d500000074100a002c011118078007007100c0e84d100e0005140f0724180c45881c1d01003410200180c030107001d102d01d0014640403a614 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 364638345 1250 364637095 364637107
    0x30706090308060406050a050d081b07170d0909050403020118030207091a181008060c0301051815060a05120f010e09032104060902030a05160504091106090303070c0b 73
    0xb600b0480042d09450203540703464800d0004d0303180d1706045000e170f5804a41544510645141174446807059024807154414194148514500005180001d035440f400450880352040300196645840e07030a5030500042c02050104030ba90440c1d80800d0b0458041d20010401c1c1400d03824040710b60500e0781d41140140d104a0017040004000c0c03182003a00d040c907000500480a0140004520720900404514840790b5400890900b0140360110030042003464280c403150325241600d49900c0e00240b04207801140c281c1d0001e40e490210400b40362082c4034090400e05d440600d841071051903002101c3d07442c244001084030341d0710828143c103064030035071301800c041c1007a40c140900d807054108040c001e18100d9109029502e905500201481d02e50301f0940c18100440c0d4950a0003000761001103006901401209000404d0010105010302860702040072000455600c005200403904400009000d6582445180c0c02c0c40c54044001d02e0517203c001c00303c034148030450311a84650542d96000041d035003000286 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 364639595 1250 364638345 364638347
    0x6090d02010e01060b091c0212010b09070801031e0303110d1b05040e1306110a05070302060610120f0b060415080105030102070b01050d021219061103010308070b090f0307060903 78
    0x603281050b518400284249450184d8545003401540c60452050303200101075518484002c441e039115a07001403c90201e1015882280d00924510041314082c001184c00201003500a01d21203040b00c0e480062030b070f26491003d1001011103d010401c900700340d1150208030f608031900300a44020042d9220009012800042114000000359000e4003406814841007102c02240c0f4104c80e0300452451000c0c01141707081c41e10340020109443c10ba070003e20040340e141e1a043d40007010b411118441d400300c40e81c2e40c8408041002005100701500001a03007011180b0b07000c0c1a44d009513500c00e85866011650100a0000501940094100140c54250000a081e400d40d100c2700b40341c01400280d0003185004181e88469011100c14001e4501544000002c8011910b40b0580491034038190700035500000c811104881c480c03811100207482c0d80c2c0c00c0500c0c0c0406e100c65007048904030781d48a1032241c900b6119030740f64518000010b1201d50b5501500385c2d0020340041c00e0000340b81d214414000014500281e03d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 364640845 1250 364639595 364639601
    0x7020d0b0a14090a03050306010c060605030d05041403060f07030b0f0d0809010f0513092f090a0f050916090e161106040215090a0b040e010f060f23090306090d0201 72
    0x12000d07580004e00c07036004641c104044a0f00b0280c02e18056013001e050341000340c054003103540095010b2207090300d180042640540600103407403022244d1005000301108240c1c0e22101a140101e0010740c034004902a02d00950102d209040040c3c18102081034070000503c116052480035101d200e8000340d40051582d000084519086240c1032a5040444402c090800d554440c002c01489984d6040b107400c405110010300100c0f5030041444140c4010b120708410b09540040144900401543d00c1c08600e40001d030030076005036000034048181d1a41e9a441c0104400f104490007000d10407410381c0071a001000008441c031861005842103e024a0104010145c2c1c0101c0488034040e000300d414000140e441c200048030840320101c005d500d40d01c184000441400040e0700000382c80034000f070001250303003615010754102c4aa408424035026a41e120990b01240041c1482002070400140c3d011000102003000c00c0303458001c01080d042068504c00320b0b1420300196841416a840804503041840e4240 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 364642095 1250 364640845 364640851
    0x303020c120703020f060c10090c060320090a03081801091a1614031606050703020f030c0c011107080d2f0c1c05030108010c09031707020d0b0a14 64
    0x5030361558501e010121840d210915400700074841c2d50114441013495407003030f0540f810200c000d000d030b6000c1c0d1040841d4100500741150b0840e4000000d40002403a14000e200d030310400b100013424070021403003100180709164081d540c0554070371240b0758040049018a0058074040608541140031420b440c0b0000d0500511503200e413007115640b01284a150b4141800d0b941490710819094648114900e00603001c0b509221150b4082e12022881a1035a9005007035040028090001013000c1d40382c0a20460603489441d0551038a01404c2002c02d4010840200400810f00c06200008481c0da4510010165034400c0c041540c0401012608000c4200680304425040307031201401d60030541c00c004820320b43d0344481b41490220340003040c120f140c00320078005440020408040a06075a1010f040075045810a0040c2c02e00e562a040d54183c50b54001c000000c103480c0c0269060381b42032141c3e52502c160ba4801c0700201e0b04950200050b000017412028114012176803500d01154904007a404c1100241c002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 364643345 1250 364642095 364642099
    0xf031d011404150c170901090b100e0c0306060702010c2409110109180b0a0510091a0a02070b0a12060f090c14070311070e1504050a0903081914100303020c 68
    0x81912558013541240703000182140d01c0d20003003401d50b55109814010100b40c00e01615990030481007000301c0c001c2010f480b0603600c65a054074130b07a44841c501c0344a580021160280c00010810268002d9030286403020030707581c4500402103000440d6150010f5044041b05420456a1501288010000300d0f030780e12007d0107000c0c43e240c0585880c08604001468113600300c4101d130750340c64040b01503545881004201a00000d0601702000011840090404200744034142c103941501c25940314880da84411030303009200c550300821605040000080d00c90307115000401c14840c80c00030a20301000e043c01100000c15183e01d144003100d15200128090b59080c0c0d148030b081140c040c1c141000c4102c04410785005541501d04410302036100040c0a00d4071b09543c1244816a0144081280780f0741c608195013024542940d0034441d58888100c40c500f80c0d02e007200000c010454800006200d8035004100d0561740c0461403000c100903103600305422100030261f50b01107081217406020320900d5010403552303c6181c41 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 364644595 1250 364643345 364643351
    0x2d07080c1221180307030f05070f120b0a0f090f050105010501030c05030c07020a12051b010903030f080901060f06030e071403070306020c1e0a0b070f0f031d01140415 73
    0xc9042c00441400c06070202441c01c1030106640581d07203852425007465840c050101c80d03241c0d8a9080110300f044103d902119144502d02d000b141c4c0d040038070322180c1110340303519181c0204401d5a4070304558007402044060260f503280407503040e01c00140945280640180314119040c1d02a040403400d407201600000e0516040006003072030150301c5400c40e075115088640441e258501c9100046010b001c55101e4040181000c81030b400b84500866104c0411048480680141c520314006650030220751201401250300e800b0701a00007401140429800100140006002600e0311000d0000c0c0102d0380115000070343e1400d078000e4086080046001900020071400101741606000070b903102d101c0d01000b021140c0110f05801207110401c104810f80c20f4000084030400010500c0558544c410101951400340780710106600f64007840b40308560805a036964170b001d031450101980a0404500d50303000e0070351508a02e480b541001c1c4541d010001801645201504050900e0b208080c2c17000110941c10345 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 364645845 1250 364644595 364644613
    0x9010c0b16090b0c032a12040f0603050112030c02010c050d090807081902100e130e150f070c0c0305070f050901060e060315010507050709050a1a032d07080c12 70
    0x4000003030b2103184e9450001d40c0b44107404408941401b051504415200344540c002240010310158040e1041d181740011207942c2c10341d05d00c0103c050710004e2003915803d101c49070100c00440d1286580c454058011304000c0c55034078060f81c4051038845082c4081c1c0016035a9078092007801d906011100062031010000c046803001c4c0340b0311445c60101494003d12803454088180d4006002d5030850360b030144000c0070820f00200f00d01c15440a4100d4600720300d41400740d0030a02200e19618100035000d914007802965041d50f0302003040c3c400c00d20314801500c10075848040040092000c109040c0544103004901038030034a0035052041d8070750103130403074400d01040380c01c040803584409041da64002e0004621403800c0720303c0030060f1094032900d01302801c2c5004100e00424604010380004d4051134221804015150150000152a9480f03c403800d5054020030a145032078504042e400232104501da0b032200d03202450b51030062030040705901c101002e4222410100c41c1d85080300c41fa031201c61500c0084c060040c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 364647095 1250 364645845 364645867
    0x40201030f14010b0a1d21070801050c13050103050411040e03090402030a06261f18200409080d051e07020601060f0305010612110c0102070c03062304030509010c0b16090b 75
    0x44051f000c1070f020403089110503046400c201c800014030010008100604280c03440e240c26600444100c00c200302e01550010700341d44a442118411030b0040122492106124200005488021081c00349444184030100c090ba032144021070003a0404030000400070710340b400d540441402d00c403000c02c0080b02030a240c1800003000c505c0281107400f004803070304040d0f80c1d1401d09004198041400c10019011a208010402d486025940c104180d5412403603c64510040105a480b00c103001031400000340030444000d20680c00c080e400800341e02100c01041d20503a01c800055100300c68060060703100f140100714050304190b1803c0a54503a181c14805907040c000040d042c1c60503160340420b80740e5103d0094082c0303c1c0c88819900c400f01c000c1c0c005d550700d209904005c062111240025074a01d480d00d414091640308000a81542400951191030595240d4409075100d400c603004050511000f106d00200027a00401d000d480742c00f20104600b01a5002d0400501c92403035038100784032610003001071140030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 364648345 1250 364647095 364647109
    0x90108010207050a03050a0212070614010b090a05090903211005093303030d240f030f140a0c0e1608190906020406020303042603040201030f14010b0a1d 67
    0x44d406091060b030722151f041d0102d00d0718004c0840d03416444000310b00c202c100704050300050414081e0302440d821a980f80e62944105200700310509501c181d03901020451420402c804a9109c03034010160f90810103241c8045072080c0800481d100c41c4000300041004010341c1003261400f40c0340076511102c06203448000c40c5501407201c50700000884041000d24130015a600050501183c09425a51507000a81080c0c0180c054087d01025400c0c1d0508008901031604903200102e400201c0900c103142c0c60351700c44803407040550b003040d644040a400c01074441c00c4100405240140328060034610b84d440c1c45d00c61054400085c0901444031170068249054941c400129500b020344251410003109020301100c000b40b4900200624250001c00c000070030ba9000b0003e0751046020f01c03642d2046c1181e4400e0940f10030307204030800074685401d001060247d446980030360f1440842840019000706080b40c0c83d03c418409034080c07204494000342e1140320607072200b504040d06d6624018100622822800a40c070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 364649595 1250 364648345 364648363
    0xc0f020609060c1609060b07082d0c060a27031209150507020c0105070b070815060c10110a05040b2101080706020601230f010e0310020909010801020705 67
    0x104034808140340800d40d56100c1103494810014046500c800596482040d03440c1c00351040714500b034130b401da0008002034508201c9100f250310090103468007807100e902404800120b040441e14089280e00c1c0f4462010740d40003001003e01040042c00246800349000c000d031102c9900400110034459018107180f414071601c540030541c18100079004404103610180180184180984450307400114105034041c0d03035000c5e0f4000c0d1020342c2901c012641d0784c0010f40349403194803030041ca51810f10001408040c03146c006a0340110080c6542030920300c0400001d40541c2005401030b500e40c2010100c07100010180c03040045030300418031380c2c40c01c2c4444194003512500641c4a40f5601c40ca0000306012040841e194090500d0000f0314194419615100002d640300018050724000d885804008505207a0402c881110188801c201c2a402c40982042c041480b10541909062105900221000742d03003d20525a0505240000580b118000000c00c081504181c0c000e40a0380d20400001010810110320000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 364650845 1250 364649595 364649599
    0x40b0a0603050c040c02011104031a0a0c0203040e0709050d11030616121e0c08070f0e0a060509030a12050c010b060309030f031008010f020d0c021b0d05011407020313060c0f02 77
    0x40e810450300307016805408d01413011282c40e000003034007104000b480c1c4604407140d98080500f551030341d03c8c11103104c100d441c042000009644140020452090034201a0f540086149040c50034a6a40d034003150008100110859010314030f40803245107804e04100742544415003020700154503040fa18080d01c80c03004c0001d5281d4a0b5120183e031203030940c59081440341e08640440402000100f40002800c200c0c0030b0340c021000076541010140007611034040101141e400070000b6007510728200003581e15601000740550140501100e280110b0800e00e0b9961031004941c5805030f0b250b50110800f400c40b0150a078592140314140188a400c43c0004140d03022a0001e282060f5651101c401d104404400351380300717003007075820014030032a080e91640180c502a94821000d000308424010240c2c0c480da5800c2544500c43c40c2c0b40485a928541984100d020394051800010700c04181888a02c000d0012240c90000d1b910005180e1510815001a40002d2003545480148081c0700c1d603c1c100341240c444d4010b8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 364652095 1250 364650845 364650851
    0xe0a020a1404230609070e130506040f0903090501021515011b061506090b07030c030e04180c03121b03050a2f010b0612040818090106020303040b0a0603050c04 70
    0x301d0a0380380c070f50110070b6600c3e0034452031040301003400a001080d0800c641503402840080f020818040c0500150141060010302141c40c2201100c140da001f000010401130740561107041b11140c4901600c545003400380240d0b1407007002030514001910f8200c45c080b1218510318241e08000000f4002896084400802d1030001c0300307000301600c1c00c400400140c20191a10380380c42019080041b80303210b403000b04d034199160121001e5803103040349144e01a081000e00072a156000100000f0310902d070f81c018a0400401c002245001841000e100003c1800b044802000000061007400f9035210303000c041ea605440c0c12000b9400d02c1000003240340d0511001030601502240034080503000d801c4040403506d4280a003510422401000a4001032689030710105501c0c0c0a60740381c413030404004681003060040100c00c603540f142d07581d020302d03688030450301226070504045da0141541c0d01c85c005402041503500654403400c4c2400c00c50b01d0300d00040c1400d898145481020000280085240c05404004031800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 364653345 1250 364652095 364652129
    0x11161101141b0f1203070207051e040c030e0307300c030e03100203130c0905070918020f0307021005010e06100f0e0406090608070f050109030b070e090a05010503010e0a020a 76
    0x30715002a1803102d2038203008050f0030000c103c00760720281d803207070140747e00311290ba43e40c030000e210035007080381e03103000c418110f6000341010b034182a0013440c00d107440ca14000840007895003001d82503401a1100f243c0928010000c9000368510300720f00d805549680c007200d502c1c801c40c2c11000d860311280c7e400003818032907408107441d9540c2d014023841440780c0021000390368074601010750000303a80456204690f500a0b9800200b800c010600c9414402e801300d8581c0094141002480600c44c18040038401754181c00b00910300c600c0611001444c01079000f0780007400c011340b100d420b21042d200160010150740d20400204000e9580726601c0100d29042d03410a022a8081040c003220191040440707107030011704218000411440c96841a4201d40b0481c003a102104c0d00c50a0003400c1c01030070300c03440d40010b42c44082071012660b030710f04958020040c2d0801002c900c0c01900852160349040351160b8406546000421640c102800b5074030741c400c0100d001d840626050f50014040043c580280d0094071420660 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 364654595 1250 364653345 364653397
    0x4060f05091b0406110607020109081c0f06030308041a04020303040509040302031306050316050405060706240306050a0c020303090d0f0e130507020d05040b07060903031116110114 79
    0x3649040b81c0c0c0600070940c2d6661107010240c101c2403c0d80c80c4401a00c01c10000a1038944184181a48694081c21a03403400c031840050381852140c502c150b0b40100d41d6515a00c3d164030240c810103004502c261a110010716007410100c1c40c154001111010080031402004016503002c4101e405a441c01c450a40b925121400c049140d03000c1c0002501c514180c00c0f50210703550f600100034602c5000b01180a05241c800c891080b18240910721981c5c9d0459003e0002c00c0000d82035410484040f41400083d640301445103c04064400aa034810b0310f00d565a0000d0000141060003092414603040c0000c503d1421702498107590b0301954840c0104000309121481c19051007a1a003840740c03440105040313400402120b00c00020001916804003500c1542e0040c48035500640981d0301712050304000500b08000383c0c840001400060300c0842c10142d0751894000c01c50049030107000b040d59001c1240e001e8003030500d090f18280d031503203420710305000c070748441c00c0724010035041210820a0074074900c003116070704614 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 364655845 1250 364654595 364654621
    0x170c030a060b0c0a120f080f092109010e010509010f0c1104090b1e16050711150711031908090a0911130522050601120608030c0c04060f0509 62
    0x2c0b11060700003d2069209000150070503d850056000103c0017a5100c1e060b0342c61000401d1312000315110308001051a010b00880c103074000158810b0341c0c0008203006001c1980410030403d600740c80c40108660784607580c090b01070b460000d07080c00e01500d040c50580004c2e00301d288148401d41045500201d003001c00c00d40c18a1202c040c1c0c0003030000d01030381441e0b2800c200b0440f01140d40c1b60181d86440510501400c4204510340140d0701d20110116540309228100d52950041c1b0040d609581e0355003440c1810348460351000c48030101480110b4403000c0500d00380c506a001059542e1280c2c0c80403001291829001c2d868401d030035800907440c1e60302c40e006004521510016441162110324001d885140700308001c00a2200742c4800c00141e00ba281c5440802411012010940111880140595007106c505a02160b005041418402e000c41d1450742c0300350a0360b44940010201f0f40021a1100c0b26800030004100c540004030307018015a070800d4031500818400e441043e00c2480081c01041294500003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 364657095 1250 364655845 364655849
    0xf14040f110901030f0b210a02090106050705011b0e040c020f1209100c0803270709022a1903090b0c0309120c031e0f0105180d170c030a06 61
    0x1640920400c400c07041c00c040c0315000a0003882c0031070b0400001003e0b0346802c0c8504290340c9801001610044c10347e2041c1444116821094a040d208034071406c4056a141c40d9414003c000030f64400d907840180d490704500792011a81d4140b180d12042042c104240c7e000403840040038010341d0002000c82c0c5c082c070300300e190008445910740f150041214600f00442c8400051a4040003940d82081900924400301c81c01c03c401e06001d04980824008a1000006e22809002c0072001e00002c2004000c404009030900003d5031024600580c001001c44102d010310300d0f9803004000c00100040d4132a004c0800b591200ca92001c00710404e0388003099001054080d41000c0050b200040c441034a844c0c0c0900c400e0703581c2d03101d15050ba104450905103400d0041c0005108440c101c00980982030740200680c440406280b04400950719004074800d241c1720700003d1040318840c4000380d1002000c40058a2100d041401c40071000301000600a000c00d00c07a112070f5505038002d030b410042c0541d00c0d0342c0d00100e0001440380f5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 364658345 1250 364657095 364657121
    0xf030a172a0a050c06030106090b0d060522150503060402060d060806150a09110d1e020a0306090b0603060306070e04060306021207020d09050307032301060303021b09010f1404 77
    0x901081e918000070300035034414418822100c1825222042102600003441404000382c40c201c42130041040302005000800d07003d043c081400c17610b07100000d140030410001140b0324115402000e8090074103000700610013100e850044003441c00c10b4086901c07a0350040010340591400074443c01d520500d540030344010b000c482c05440312410184041801e140f80420070f20b01c684000900405c04070020f110342d40c40c09405404a1780f070b00302a403801001800103409220800703200c4130120601e0b0708041c00240000307205580c00280060034020340b0012074444170f001c240140300c18800c10429407170028000d0382044075030600e0799510500300c4c0050043c00243e0001041c0500214903082e07000c550104030790050a050b000e0750b0044541e40022541004540700710790b81540401810801314140070181d00101074282c0d00c50b03550503203620301079007507032541da00440059000741100c401400d1103608050a2b600116239010181d450106543e5100c051070241410a1000e01b00c800304e569a241e202560312049 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 364659595 1250 364658345 364658407
    0x2090303091c06110412060b152109120306010503040507030507060504141f120f020301080d110f0c2205040c08010f02070b0c0f0d1a0f030a17 63
    0x100d442c100340e00081d0002c080b00c07038608202d0050000b4180300143d42c1504d0700015903a078044070300e4854501418008002039040782d01681d01806c40c0d00d0f048000d0800980c0f00b140350168190300c80314203000131001060380c01d10340c00400410004240500403240c01c1442460019140c0d191307420302504100300359100a04912458a00040c1ca58010001d0800c607002e04682c2800072400c14140007800545005400350100340142d015050f50250702040c201d15001c010000315034041c1e903151004c03a4800c0e0800002980010710009940340d002c85100d000b0011900540381507200309194030764914081d48010b00c10340700807800807140481001072040051a6580034400380c100f506164010825500072500a0350800b06803100d852240e00072580c5640e0f0142c1d10b07645599403c6520380080e084042207402c188070421500e40c02595a0254000d41c803c0c00b180308214082c1e41041101507003821a02e240260003400b080741c0850603845915540081a501c2c40d03680b200c450b0800022001050003050720104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 364660845 1250 364659595 364659619
    0x6080f28090f0c080a02090a0f0f110403021c0b0c180916020105071704110a0b04153009050f101e020733051303120e0d030209030309 59
    0x8903011030b000d803a805030841031242500d600045803510000d4401a40040b103c10105480c0c05555004858507070b00d041000480c03100c4c1a06c00000e40f01c108054500d140f001160920a528041c101444001401003001185000c142d40b01500c1a2000b40955600170021404414410f8013403e8602c0580300104031414a10304120301c0701800c14849042401076107024000703180709001c0c1c68401200e990081178048184d42e60364682180074240125690040d02d00d0f00c001482040002c09070010340b0300c0c0f481001c0000d44a5100a0425200c101d005c045c00b45090390204000142c01c82605441115250200303001107581009490000000e8080c4070520035148005040040d81d4400b040a80f04c5100464010060f814250103a01811001030300310135007041064004c1a08400600358440303489c40c8184025110300400f401c582003250209142c611040c035101c20964098106450415843c03002c025034001c0c40200f40e074404440000c0010b16500050402141d94200151412480010268800c1030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 364662095 1250 364660845 364660853
    0x91903020306092b3e0d020a0615030203070f031103030910080405012706050109020a0f18090203180d032007020402041211090a0b010215060127080706080f2809 71
    0x7440f079070f000190b24081c0c02c5906003803c0041031b80c0019904c150700400c10344c50652070ba0310090a0385840040340841c80b01d00040162014441203009000d100861000c10b880d60034420114520702e040903220342c10810128800c1d80c2d40c1e1305941214251031905000559851401b035006042d068200c0035903211141c0ca02000c1c0081c0140c062016110382020703c81e990f681e02012090340641c0b07502001140341e50390a0701c0d6062180710002d6121030301001d400c080c0795540610000f26401a5030009807807101c5254a14604402c02c0180c20210f124a001c1244061105e0149078400c0100412101e10000048910a568864041d600600510900c0c082803c01c0d030710f482d0382035640c8221817038020b004003000100b0018151003401d22074041070f000b030a90468403800410a0005c0101800d050240e000f0f0315a040001c1100120235102c2c1e440010780d036032802c0c24a0b091810f0381c96440b000c10055008100100800d440c0202500b25040c107408404c5c043c3d01d0401c2400c1e400048911107882464015100140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 364663345 1250 364662095 364662167
    0xd03080406020903011e1116021005070f05031806090a0b0c0123012612160b0a061e0311060d110304050601030b0c091008070203091903020306092b 65
    0x1115046c10800016103c0d5600c02e0590207501295121403031803001034405820020010800e003c0145007881c43c007442a0b440851050400a0940e40c590011a140510030782c00c841094550104a440078100305085000440c641210700900245800c00704140c0c0f80700d60250803112103001c1c905403158039081c18014518645600348101c48240c4180c03c622041c140080c0c0c411944200030700081c145a00d403944180546071b0142c0100c1184803510b8940c00c004c43d0310905040e0040d00198400b0401d540b60004080a12091640e0014210340f400070410000d030110882c4519002c05642443e03d130f01c8a02074080003080201680321600100004110070000c021a03020f051b00d01c0b8000e114002d4682d5403040c1388138021070064a401c0307070034031526002c070a00406d41c81c1e520400510440b45490b0321803001c039800302200b80410b07102204641c014821468140040e50788490200000d0011a1501c0d45a109038031003000059921150920081c1200b40308482101c0c030f403680c1d403038290003c0c0100030000c207030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 364664595 1250 364663345 364663391
    0x180a080d030212010b03040c03030e0a090905030901021b03150c040305070b0c0106060201110301060503040f0204110a030f0b010806010804030207080303240103060608011a040e01080d08070e0d0308040602090301 93
    0x4220010020900c89017280c00d0340d01603030304000f1804822781503590540b6030341c03002003c03d40d20183c0d6180001c1c044960f805650741d4103101d1000785481e41c84c40000a85072100341480c0351031008003410924060344001030700144480c460700680305280c03100d542807282803140f604090180d00a88402091407510500106109401d08008100640ea6150101e00300e4800140d00031340d46170204010000f141c420740295030880e008051561050380c1c2980010300303da401c3c00a00c90f08000c017007007503c900798041c032403d01604408042480341c02c0760040000c0c401d000c014101d605204400d8045014035108012500240007020110303980d03414410380401c00c101610907640b15141149150081c20b5201c0d005510444a00c0e44812005900b024280c02542041050710407402c0350912000991004c0c44041500a1031820080c00050021100c020603000d001043d440c10f0101030001c81840741c5a540c02c528a080d090319101c050303a2a14900741c40644550781140350706600b0821114200c11070790182601c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 364665845 1250 364664595 364664617
    0x40302010b011d0d062712020c041b05071505040515130b0609060f0a031a060607200604080d0e0310060608011208120c070501110f180a080d0302 64
    0x1901c21a00b12120f003c000c030095400c00c0514010700300240d245e0700f01c442c1d0705090f0601070000d0311109a40c0102c0042030394040d2051100d0605030103ca54040c01054008103007910705000084000132413114100001d06150b0030060001008424403080c40100d0f801a400c00200380a20b00f0306040aaa99031008801e1b90031f12003000021a0071074842d803c2600b0300703981c03100140c2c22655130401001051040208000e03003210301ea400080e02c88da00c2c0b110f0074014622800300c150490201c41c0b07508200b03501c0104442d000315010030465010501d60000c207000c528030380e007250300ca803080c1001003070031801a80e104e01c4243c0308200b90b107201c464014825601c503c10550032540035a844c0c4200c6800d80790544940004910004010700400720004c22995289018500030340c60310b040307803d40c0020040c04803000b442c024070100d41d440070040280900030b0804281101c090410100c0702161886100740440d90b114011030000a02e02500d400c0c0e4800010420b09040d608481d41400340940a5400480703d26 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 364667095 1250 364665845 364665857
    0x21f0c140d020714030606010e06360d1a0a0212010b0c0d0207061704170406020604050709051504051305060703090311060421050c011803020d0806011b03050c0105040302010b01 78
    0x8a134119071030800d488040b600400918036a101c000c010354001120b0310364150800c804103c4a200b54124100881c900c0b98031151982940da02c6011010131980c800c0310b606d20903506081420b011803441c10340c59848040c00c00a042c0c0d9911100095002445240c070303c080141e91180000070300f590b54101030010318404400761144107401000481e242c0055008c0c0c40041103104591502d01c0b8072040859501900c20044c948442c024079070003010540151f44a2801a802a410030081140c02d01c4100001d01c4107013418881410070b068440702600840c08028006e0b03607070388009040000c00e40700c6203050310740010580d440b904101c14010050100010190040340e000c07060410140030005043e442103410074044080d01e11010003488240c08114004010403006000c2100711500c280300725a014002440460a5003c0c1d0749006801c3c060080440002c7c44028030170440300783d8010b004442102d9004001c021a1070f000d127801e07a040e000d41da049080f25841c0c0000c00c404c1540540c449d6200c001e00340c0b158 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 364668345 1250 364667095 364667099
    0x601050a0813050a060b18040224090a0807080d021c081302100e01141c0902060c06090303040213020a021e15010b0706061a0a03090311060a0c0806060403021f0c140d0207 75
    0x8403d1000305a500a4010410612b104010700d900030040d010050031503d0140b45c0704082000880c0c4174510782046a032600058000c00034181d00700010301104442c0e0005e032a150b4000c00c0a14100c0740c04900c2c02081c000f07407000051144500c41541100301d54010030001e503a908940000305220784c4409100d0100700e100900b43d101102000c161201e003212640d095070b0125035150301c0c034040c120388403040b031308a541444a00071290040c41f2591080802900031603c03841c050041251452260510707000f8a441004003880d00b540c00308610b004020740c00b01d00c2c9224407040320250b01d00b00d5502545590751110030b00200340008414020100f142c017441042c0100ca031900d800e84001103d1810079507424208100f4a50b5031402a0010350510380217081c0010942c4200703107020708160302120184041340c2c1d200349900782d20b070f00640d2061700201d041e00d1150801d0305641c00b245165540c042103425200001d000c51045512944100030340c954000c0103081c01032180d543c095914a800301202c80036000340340340 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 364669595 1250 364668345 364668379
    0x11e0537030e1207170f0705060f070323060909100e010b0f120a031103040e0f0435030c040519090e031204080a1e17010e0601050a0813050a060b 64
    0x1a44d64054000325601d241c2d0643c00c07007030344c681c0c3d000091400e01e002c1c06000c0500450390900c00c4501c1143d0b454001c8a441c07800075030007011104003011103c500200b800314001ca000d40c9a82c501d504c00300544506d450b640700c0b42c812625240342c034000c0110a60a010380b00706a11019045a5100f140a680800403ea2203071b04100400e81e0307130324404980754822100341d800b0034440d07032028000000c0130041d86e15280e10b404960a0b0060102c0300401951082c800b48002c000a1442400d1064107554244809901203001c034042c4010181c0c8007101e01da400720110b099044010b0494ac001d010007030050104918000e10100c480c031442c443c0800c15460b006449809480200807196024003240414003260b68036603e00c510340d00482840410402004203400c0c3c0a182d8a1107250008070b280c698800c815503841040601d004160482045841084103000259800005581c2102107034104042c06a95461036034075111807000000d005841600c0d6082c3c1404003690241c080c500046d5000d0410100c1202 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 364670845 1250 364669595 364669597
    0x7060e040608030a0c060204030c09020417150601120b09041a10051f0315240215070c02010c0b2d0907050405060102030708070b06011e0537030e12 65
    0x840d21142e034004201d5000e040303104014041a507480741c0001800c041d2170b0b03140d564001c0314941040700f910740e00140038041c464041d100e0542001048004088854040c11a81d680c550003030b054074140b0450545481d070842450f0420264200301411990281c03a160a2250202d11030040d4503110203860740108078010310000092082d40c2000c0c1034008202c1e0f1208809141e091059001b90805a0b503c40c007203800120020410000c21103280d0440e84000c000b07020020f4012310384610025540304200c9901c3d01c0030f03801c00050b4010840d040001600c5610b00058810700d0544000800a442c21002c200040300040520b4000740c428920b01284032600ca43c1c0032000001c1900c2d008510307803207024200701c241b0f0039800ca00c0d844001881031700d040c481a07554400440c0c110720000c96101500720708004034bd503400b90300c0c0130480050b42000541c4200700d10f4003034080c1c0700307202158070a00030104040070011b40702d00c2c4084d0f0ba501c00099005500400d041e00400404044a21042d5800b59216449903549240 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 364672095 1250 364670845 364670849
    0x6020426070b070204021903150906180b030a050a06020340060f0218040b0d020913170d15050a06050d0e0a1202030705060a02030c09060a11030c07060e0406 69
    0x101051810030100442c90b4020141c103d82c4140c081001e0b101da55104201d1000c01c8209840128460100c1c03621010740c48500d070801e00d40c0d60314101e010444445440203540d4106a00f900c0020102c0340381c1e012a007030160381c040140c9507108503040081006426801588034000c8008120954000080c540424031810039000941000d40b40600031079602c40700004262500c14140040c4003003424a00900703903000301c002645441c011810128041c1440d014140c010281100c40c0c3c1c0846030168001a81044c02402880c14026000c04050030070900c0510685c0d500c0c0c40c4003082e5214241d8869850190248800f000403203074000d200003800d41800402c1005490032500c07054100302d15000900c00410307618401a10074420400094042401c222041d100242e0700d6001e95520101400c0052420038051b040e081c02510400410485005181c00e861030800200d031442e903904030070313107044503d61801000c03011203000001d5240005c0e203000908404954007626641c41009442081000301c49084c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 364673345 1250 364672095 364672169
    0x203060d1506050a0f0602120c070314010f11030a0e0a03141e0c060403081b0a26010803030a0c050304050a1e0f030f080a0c140a030612060204 63
    0x2104010006102003034200d000e240c0d00030700281c0da50340c41c0d0000d103034002c1d29800a10b110070360362803c0c04120380c1400200e40c1e841c9451003e61600d406604860740c5ca900c0b9103c0540381100001100782d10450a4001941c034044440c4140200400c0f02c501803240e03802600c40843d6180b611b4400d9411040c08101c1c162072a805d0344581c1c1410404500d00d01090b400002c5510b080c1c450810705400700c0c10000f018100504000c0014000307803030303e854050181a0b0242c000ba520019410f0079450380022041140c1c01c1000a20301031648a241c0e60aa005914003580240e118684140c002300d0368800010103144201c080c0002403043c41e03441d0b40196880d01c03054802a010743c0043c0150408240344080303d00c8056004800c58001168607202d400b5070111101044000880c0001c5000b0300c00d52000300241c11025150f4108004a24000064205440c05104102c3d000022500c100054060b82c01440205000d401c0001107500300e00c0e00ca13000754403e00468002001d0460f9480310884100c0000200c2030b00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 364674595 1250 364673345 364673359
    0x10b0306010f080f0417130e040b06010c050c130605060c0f0120030a05091f0f0b061215131113171209040b120c0117070e2404030b0709050301020306 66
    0x1d0384c582c0d017882d0811b51004450034038200410b21542c280150104000d000102d40b01c2000c2c201480c00c01c400c00c0f0043d1000c0d04100441c0f80e2840401c2001c01c000400f02d508445003803011075000c5010740a022280d1040390f00c41c3d0b020550b40c981c5400802c0300919000c541000308005401c158024011003001640c5105c200c40500c0050170000180d8041178000c03045800b2200080100d03c1c110403003035007811192483d1512a4030009401406016072000440101e480c2401c0c52002d044100307405600a11600140080310400b5006413585800d3300303240044a80107000d01242041002c503243d001e103104244504140c0701c005070301140b588010340d400020750080d140320000c400b01c8600341d4110100312580a96140058800f560303032803003400b1150140f0400381002418100015104040f904070101242c8825010014142d40c4110691009502110911901c1107404500002850b5800c1b0807040c0140c001004418064105103091080d11195513805440c1c0e00d40045c18240d0200b510f03041c0d04216 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 364675845 1250 364674595 364674601
    0x20114040627031b0f08150402091302130618060510080a021303120305130320240f240d0f02040f020306191d04030215010b0306010f080f 61
    0x1d01c00030404000c500800c0002c6940742c4035241da0011050381400003420100340b40301009001c0b066610503004080c450007130080300c046002e8400342030b003008100a204500c0200040c1244243c4540d412585402800440111000403d01002010140a5030f84a844444000003500d0f0041c020701043d540c000e030101e032000e040c00a096503145406000b8008182d02440341d03031907820a1981e40c1008502601e184a01a01c0d6804e01900300c036405000c0c0d8480d8080c00311000c1c0400e403c00c0d2080400700703040c011881000c0c402208542070000d20141d45071810003503892821128183d0b85001d00944401ca008800c41d1101003a41c1540a8001c84078982039a0141a001c69031501e000290242d600407c418070583c1180d6000a085810340504c046159501005000081c20205d0201041c0382840c500003d2440c100340555035003400c80039a103408001e40500080c00c0510170720094695001c44041c10300d8035610380c1c5000c0341c5038000705c5916001440500e4035041b054403032542c45001d4051032220580e039132 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 364677095 1250 364675845 364675877
    0x120f030e0c100302030c1e090a0603021314030f060408040f05031f02090f1009140415180b0303040305010519051510020c1203030a0e010b0a0b090d0c060c0201140406 73
    0x50401841c0300540d0303006010308550024426003190100103084511f40d62485402c081004007011600b1039001c2620520020b813449070b00040c05e45c1500c00c1d29000b10300044041000a2902c249010440780f1030240100740300c2000300510291041d601b240c034a540c3e0250304c440070300d545d0705050380000b6801c2d071a41a102801e46032076801040710b41070140040c06035001da80041380070300420045080c00a2800003040201e40e0032065482400c507003c42d4103003ca070008804903200c44009009015542030f02da0090500c01c00203030312840c0d01020103010340b525680c4d41e081203402420111507103c0c94003071602038140a49403c1c454988655150801e078003440390403c2c140001013000d02c10007000d51149284c0410240c3d40c00b8504001e140900d802950f80341381c900070120580e810808022401c0e810000908800d80d9001d40782801e0f24144110980c5481000000802505401c0c00140000905180104030706610589040d0018002e895480c00003400071000c028a00c22481aa8002840100701100c80 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 364678345 1250 364677095 364677097
    0x4050d020a2f0d05060912030c180406090e061503120301120201020705040219020c0402040f030f0c05040c09050108130b060d03030f020f0c0d02070602060a020313120f030e0c100302 80
    0x40d68082c98426031141075000402d002156a040550b2107500102c10041c1040082001405030b03100d000311a400c50402c96500080382c05010300120b1040c151160381a8151501d80c0258021b2a90072014450020a0f036107180d124001940c01c1c00109044444002840c1800138044103c8003071050410b01d0360b86804054884038500700c0b03040341103014041c0005455551400540350400b400e00d40300401c0c540415000c0d20b040700c1c1e40d1041d401640140020060300301a40d07404421283c00c0300784051600d0b40361602c04150717085900140d9004c5d161a400300c1c0c06940c03084039101924001e80b15120507449000805800c00c4c1c120200424000000c000200e0500b40a0b0a0004241c03003800c01242c40840044000700340d070452017601800000200d03000c01201010041500c2101c02400600005418500029240c08004180041c41900003011481503002c40c05c402c28030b5500003824409401d1000c4000b0b00324410601042c000a0804d03078286070300c0301c0c08500d070080520002c02800a0742040142038020b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 364679595 1250 364678345 364678403
    0x8040f060209130c0915020a020d0321020c03090a05040b03060406020d090b0f04260a03150506030708010501081605160302072403050c03090303190612030804050d020a 74
    0xd81903040c007400070303441030280b04442c501e070340c86005d031103401c15101e4600910f02e01c038480308540c401034407080540c413024203082c952601443d20341e0007001c074101c0c598400803190a4004100c2d10020304500c4074840480501452401141e0b41407800790754100300320940300c0c0d102031241c0c96080b800c0801d0008040390700400541800c2c0c0f01c0401c88640688408410000440b040c1c500d0300340250420042252820b13040c0c0780030311440c1c4c402c4442000380304041d0b5075000703040411050665030301c58001d0b50b0355107203060402010024215642c07443c05060042003107e080c4502d502140c2ca142c0810b000110b50145c0c0511910700d071b65800c0c1002c0e420b52000199040108042e4207600640c080400d42100740384140d400c82c0e00744001c0c0c00c0c00b07500410000301225001003040500171414814080c0c940c001004070b030b811401c1c180a00002102e0789217184020000da50003600100042c032404020950803011040c8520301640c1580c12014001d18281e885c0c0104210080288a61544d1619100320401d00208 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 364680845 1250 364679595 364679599
    0x15060102071d09010f0c09090903021002030703021209031801080a06050d0b01060f02070f0b03060315010f1e0303210b0a0617070309030504090218030d0e030d08040f060209 76
    0x10341d403050018040c1e010b241c0460640522039080000f009024080d01c01080503540c005c01034800d1850005060000c1d0380901140c0d1502e0382c1036241451b200f044401051281d4220031540ca050844002d4004c2d400a0100d5050100304800200d01d2030300481500c00013401d01e0414510f590610b001196039020041074800103a680b0354001c252510b07800c0200b001c26104201032543c0d0750501401811800401000004660041409201c00365800c8080c03c211a84040e003181c494543d000002e045c506083d030282d04402a000001403140d003002c80100444d0359200d5a1081080c510608140c80682ca02000c0c02042021418205641005e0407401611454910000c0c0c603088520004480d020f1a900c20310001b01d9000400c503410101022a5410400e00e0600b0800c440039554081d20a0085200307080100e5404685441c03200c1072210502c2040100806941e940d04200030050031807030601c1096406441080880035030b050061984a020343c4d0000e07039440190310240c1e2004041e41c40780845507 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 364682095 1250 364680845 364680853
    0xd080a0c090b040e091605100507061803020c1203040b2217070e011401020618030d0608061f0e04120c050a0c050f060909060402090a050306070903030806040e15060102 74
    0x15000740b1510103000035052112901c00390782441c4d0001031401c001c18a0014010104100c2085507588a00b10209032000504003240c0b22013080c2000360082400c12526080204000441070405a01242080724441c0440d01410040401001c00340e4034080c9004888590000308021880e0302c1c0c545103000070501c10b521a20b4070071600c90561041420907940c06503180c0c0d10a003c10310034207040c2222a80034190410514180807100c2c80000e584107000f91000f004105650301d06840c0800a004071900790710302d11410300c081640c4101c400d6035048204d0344101e0800070302c0950401a010782c4030020031100c80b604468130311388840e16000c0406811543d00c900f402161800400040d406028101001d4000d0807508041403510b01880b0300076402e196224412102004107058a541e00044181c2040040c1c0d4016100c01c164800309001300281c0d0002c50b031500ca46000c000110341d025001c0c10940348039581e0810b05455500920059503104052410350b80c00a039032640900b85140c00103607100030144116 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 364683345 1250 364682095 364682099
    0x50904020d1202070504110a0c060f020f070807020f0604050901180239071d060f04021605010609060b0406050c0c0402040605120f060a1e03081611030d080a0c09 71
    0x390405640308440b01680128000b00032a06e8035100c0c45065514100c0f08518040d602d00000740410f10b0303104000d011540d80c0c20000303000d25242e81034546480310400c0d040d944108a04100d2890741090a08a1190790b411f01c21900d941041c80984e07007100e01c0a44400031a074201103800003096002011504590350038081c40100e881901420340584480000302d5442090410010360304006441d1114891390014a0030842800c01441c5090702c1a03440d200c1600f04d03243c4000003280741e010846140e034020300200c4d200984030700221101004512480082200603928154501034071224400c1c1030840c1018807040081c580618001c0000314070043c03e842c04c031403c1d400054220f8015802101c00a01c0110301207100c4121968941e8100d000c400f0740e148103241202c00144100d401b8001c0c0c0076840d200d48445000500012200c402071035000c2055034550310203649480260b1014001920201180b82c0e15880604000c542d034410820241c0d03420340c01c0d07902c221f1003801824a0407030034000c214100b140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 364684595 1250 364683345 364683353
    0xc030a0c06180609021003110f0703110a050606010915050702040504110d140d0e03030a0f110709091a060d060506012d02070b19030504080708130305190c050904020d 73
    0x1001d98030070f1040d0320004080e48503005000b840d0a524216405152400024001c1800350000f0307551000c000444103642c1d5001450100d8000481e103004921903c2500e201c00100305021640c03602c140f0003a03a600d00081d0b995110340c0c50140c40320038580c000c60010419000541413075000940e0041c000e02030360a02c0c42d440c40c00b00b0f00300001e0314400c0d142c111412041150035202400000d04180b0b0b0380c078000071903c90800000351288601c0003d80c0c14070507079188000c440d5005410380c442c400d24007070548080b580d5804c1c2c0300e006008400030071500f40300c10480c41051980c54a000c0c0b4000c1802070070700c2d08000c52640c3c40c6401000003401c0e09042c051411a030f01c0c01d00921a4000701c0c41d2941a920019840122034040d1500e03409810485040c00300b4040003018885c02c51501c2c540b84c4407803030b0125081d211030600000c94494401d014110340f07000109410124107c0e00c40d070040300d00ca4030844a1070f024070010502c0c00350020100421411060408002d5860050300c800c3e0000d000410408001a45580d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 364685845 1250 364684595 364684631
    0x1005030d0c0302100c020c0f0d080f0a031d0618160303020f1b010804080319020c03120105040c1d03010b1903050708030306010c060507090320090109020c030a0c06 72
    0x544000034540441001c109035040c4284501c19030164020701110034401006516100301c5610f1501980c3c50106461407981c2c1c002040c11000e4006920b45d90300c503004032a12543e5801794907060042400c0000c0580d1548904070a90b004101e240050a01c980340c101c0d43c004009048601e04161381708441000d61a80c404401c0c5000a40c82a00246455104440000e0410210481001c410009400d40086990708040c0855110381c2c050340c2d09507070365110b00884550081900c0d0131000c0500c01720700c08102d010000000c008016054044440e02ea0fa02c1c410042540c0b55048580006000d480b140300c60045162101c1998601c000c0021070340c04100004500c910340d401900040c80741c1f20b01800c0062103420301810f0050302a160285246140400001c0c2010660304001800035903254002030740305108060700d1001c1d542c00b02007080c0c0d0152104a40750460200e0400520842c849000000e44902c3d610888200f242070070065800d00c0c540c400c00340c8801034030303040981d141a02d50a5500501c601c1c51 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 364687095 1250 364685845 364685863
    0x905060c2503030806030106080a08030405210307181419090f05040b07051608090102011d01050907050102010504020a0b130b0310150f08151201050108060109050903120f100503 78
    0x60911010915500780104142e201805c098082d03458a84244540000031031020409904044141d5494407249007852070019200b1030190b1410441400301001d1040d00003d50081510350740e95000060312106c54111004c544c442c415075056051492515401c0c011180d00383c66111815429140c5d40e90906030040d54000c444140c1cbd020f50380c05c05c110401051414403500003441e441d11a01300760b030b0343c03081c4074100894420161042001149101e100c1c0e20035041090129003541009031010394458072a4041c01d4180d8411001d8081c80d8000700e004e51052059034030864008044412452924074804c400f544260502c0b44201c200d0b0030085154080b040c0110700410081d2020700001c0d2920010130200d0b078102c1041004c000c903103641030002903840b040c0301d50021003100f00c513502ca4080c01c00260355440b5411903170303a9550804c0c0000881580c041441da040b03c0360001c0034010f0b650340c2914591030b4420290b40354940002c0e5408200400060780e4055480100700c2c007400d410680f21700000c0d02c1e0030036007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 364688345 1250 364687095 364687153
    0x60121020901030c0203040e01090506061b0c03010b040b0102150c1b0f060c03063d0908070f030f080c01150902070c0501051309050a020d090c03030e100905060c 71
    0x24003600c5540c0c1842500c04144e510b10245086c98180108004092018440c01c0103450311140410410340e90001141c05c14040314080ac0c2d4011440e260f05515034a0140300310748a0752806c010301e201400e240c040d04038a080160b000d000c4d07550682c0c0e0b401d065042c000d40b000b81095024000f002c03120803843d5070310544494940c0105403d4070500081d910301034006041c020811014014040380f6110b2009031140302c50034002498203107591095400d05010b10040b0704490722214600014401c0c0c00102d00000c0e6114030341070b160500d403039a410070745800c1c03144401800a145528140c01003840200030304080b4850800205d603200b0ba0300310f500d05c00034081c2c004c1c0c1901940020206d0030001369088a0004000038284203091800425106868841c5846103550854407079001403810320030f0b64111207080c88003c1c410026000e2900300300810b0301c118001100030400d1303014001900d1402002c0d01024803010340c4c031802424100b0301840559000103144004a1146140c4551100301c8010003003902a41 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 364689595 1250 364688345 364688347
    0x507080a05101421011109031005072a08070c06030b0a05030c01050a0315030f0507080102091f051201080309040f06050d080a090801060e0f090606030703020906012102 74
    0x44654640c0c00c41e000902a034100015901041040c1c03002c1c3c8660924020046510b940010b9940001c60040703485404d1100d2035500e071400441c02c0c4070044010300341145042d070031204007045103040901110810b80da00ca0104104038280009071107048603c0c4000206066007480c440744598a600302604003090403031b025130660106009480e85442168440501111030400d00d0b860032002c00d8a5180440faa41c2c1000000240700070028040c1d040fa0004246c101c409101481d680d0a0420030040315160844031030160443c005580e001c14002d8407250040103092001c2a8a900300b44070452080300e040100788038043c05100000326030102014002c0881001070b513610141101000225006807429030308480c6814028801d613114640141021039000a2455039014110801c0e41c0070710207684210017940c00d010707011546a42a0703001e20b010350b089203076080700c83c1c0b0340d50021a01c41e00111442074059002c06000c0015140c004101c43e007000d0181080c5c40030342c405080b000d46160020348035596050f0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 364690845 1250 364689595 364689601
    0x1a090109110405040b04060e19060603020306010b040b0910090302040525090305030d0b0a0f17060705070203060708180d08160906020706050306010201060f122102101806050708 78
    0x5801405406003071000c03a0200058902a5100301c0290340c05000a4000f59843c1c078000c401000800140310103a00b142c80a85420801c0d190100181c540790000701e002c2e02400d03000183c0070005c4001e907401e80e080e0740d0f44c3c2380c00c0035441d6042c00104840307540d50008000c00e02000101507160b511a59004612940202203071101051790342c0080301404001ca020400d011900b000401c0d004001d41d80d4440079400086150008280080e0640078150445001890710510000b03256210080030b1404080640540d4885d603141718068072180107001e0003075050b8026000040d0014400d56045078444a454522685222501c0005251141a403642c5010070641d00c01c0c44900b54010740706542c10f000616006c0318442c2080c800035100d556500c980c03400d0141c00300200b44140c0c002e4010341c003e010402400110541d94108030024000b1a41d8140d400510380e1031100750742d640100c3c40d842d4041d4250000d183d9850303803c0c920002401d0642c0815200303a02c1780300001c0000d9072400782c03034007512041e907036403165003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 364692095 1250 364690845 364690853
    0x3020a0e0a1d0312090106151121070609031202030c0a02070e09070e1308210a090803070c02130501030b0103030f02010506150d200301060e0a0812071a090109 70
    0x11a40350441c185065541000703a50248000304035480403040301345040c151344450b0103d50241806800c19800c10840c8054810700a51114080c04014a00401c60707112200184011014010702c5c1034242419000700441d0010070565000f01d03030071a1080c07610403840c01c42e507104e1008a81066840d4450402d00013040d00001e035040044101604060740442494103111080555035980d61003540e81e005901e2001944411032200101d0445400c0707001c0d140c0d20882022903424040c50943d00f03501000546000c60a000b245200e00f040a662200e442403954840070006e0301c1940c0083c00880e031014100403189040020b50003054021442003060102c0d6505614015000e45000c01151086a260804002c1255a074829051540780d503000025603c03100740510780041c042c41d2a03480282c585039019459520140d100560484030a03030b03108030b460400a400c001400030740340301d0078840d80c0c46407030089403540100d401000c070180324140e03056010b882c114450601c003100b1940041c1913550b61038040140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 364693345 1250 364692095 364692101
    0xc080a030504081306050d2007020f0109080d0512010b030f010e060d080d0e06010b0c06040f0807020316050316080304092304050a151b081005030a210206010506030415020403020a0e0a 81
    0x1007048042354040342600d202d00084501804402900c40c840e00788280c0d456074010b1001c3c401825040c804d59101d4116020090076580c842d910740c01900d03080c200002080c801a50549018802d100d0204030540d1804c003160b50103503c0034122903032000800c201180040c1d104801083d4040c00c0b1040441c0708142c03029800d041c054141c2c400c00c61070307004214012503440e010600315030003641b00d81c00e408880140d0501c031a440c041c1903002034051060254010314002e6844045040329821000c0350943c00d01c0120107942e071a0280b00b21075160784203120601c044401500007851070b440040101407010007141c54158a10b17016201554507400c0104040f0a0100c00c00140e103a81007085401c1c05410424030038003420802a104402c20410a100031a1038500c0e8040204001d0400404a801d841130600b00300d02112000c924005854074940d4480ca80e660000c40d205040341d0004040a0969803142c44107000c5110540d010700405508110100050b6642c0001ca00a440c4540c024407041c40c1c026000c1c411 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 364694595 1250 364693345 364693361
    0x6180b1f03360b0702101a0f04020a200316210302040e010302010f09050907051b0a0506060910031b090b03070b03060f130c17070c080a030504081306050d 68
    0x1502e018010044510b14482001032070300e690019501c0c03010396540300200e041c03400031405e00511508000e0303072142d4484441c24501c10303014111886c0301c10180c0709041004030301c20328840300003150055000b1030031014042542028070b4640d4041d68600800f1076803411511216030310458410400341c965035491822220400112041420118a0300c0d0030100400c80300c07541440005d0400280d6601403645511504044001f070501400c0203809040001c0d0181990700328030b000101e0489090b110305001c1d41c0008500c800c1c1500000500420340322501030002c9000002c00c1c010301c014900c2c07000000504a40007081c1c0c40080c0401c0032a005092030807120030343c2c0c8141050361096000d09810701c40e06041100f140d402000884640a000d02c0d00d002168900717400c00c07a6031405910b04222034100981180714039041c51410013040d030059135681c0c010703660950300940241c1000f50074000c0c0081039001c0d030300c03458215018200042c03c1203080e0380c80c50b19a0049411543c00114040b035841d4994505010b1054 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 364695845 1250 364694595 364694651
    0x132f0a08010e040f12050903012d05010e07031d060709171b1e120c04050c0a090b0d020702091e0106110604080a2102040509060406180b1f03 62
    0x1030541059112814070742e420f0311000c0c0c1003040041705510720705d0140044403041940500288225816140d8115103c90031800c0e001d07204080c21065262202d10340b10b024141d405210703555400b9181c03054124000cac010110044000701343c034031240180740c00c208410f91150340540d40b00840035040c1205c0c003401d11044c01c039088482e80301c14092161081c0c017441955090400381c906400b0a04547c40c030301c0c868411350107025080941e12450b0502d0400c0030441c0d00c4102004d840c140300c01c0d215804400040e102d440e00d4440000e290720700512203954a00300400c90a101c1c0c0801604019030340d00003841c60300e0282d5601d000c9a0481c0a02c0303080c042c0720b800f031070f004004900f002080b402c40d88900d5610b542004000800700203000584040c064000e000140e1407071440604517400d4031089a0080003580725000c0e82c0d1003081c0c4100028950700d0031340500415a0344000c5017100c08919414428040c1c001110707483d912240aa4a0004c3c030340030b56540d9809140203640c04604244002400c210781c03080440409 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 364697095 1250 364695845 364695869
    0x409022b0203160c020f092d06030c01050c0304060c0c0504020406050a12020a1d0a080105091e0a0f0602070c0905192003060d030e0402040314010b01090302132f0a0801 74
    0x20005d13a490b84841c1d038003210700b5a460314a540d10f400c101e06411038a441001c1d120f03021000b00126250750120b20912448040e002c4511050100006451a01859020142580c0308010500025210b071108103e550712031303804081980e44840026080c3d0304140c02040c000b4002090503402664131401d481d14041121208610301100060024020f054842b80080034042241d00d00c66282c850700c0841c00200070140081001d4107005190315110754160189a095003010000c034560302a0100e901205158805145071600e0a1541e0300360183d0486441034480c1d035020300000074141c50078040e00340300e0040c85601781529910340c3d401d07004850929180406014141448481040d00c04d81101d4000748100c0340108416005e01c1d044684504400345217812500101d00042003044200e11620000c81480080c400c5090000c01158402c810b8032000e988138032400960704901c2c003150b01c980a04584040c0340302c18814a002a244011441c541c0011044400964a0416070740504801d01519180c0c2c0d5038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 364698345 1250 364697095 364697117
    0x1804050f0c04060e061207170f0108070e0603011b201204121e0305030403030f020c060a0b030712081905030412032a0804030306060903080409022b020316 68
    0x394031540164081c03072050084084240d11180d40300015a6688512046c82c01458984240000e20481180030449809803c041c042918a140d0700ca40074142c1d03105400400c0d1a514004e10b81032002c1e03000c5d1020b5019561401040344020555020030008111342d110008050503542c540740810000784102d482c1600450303c1c0d503da00c0241811542220040d0b071400007115001d041150a6045081101045901c0454035008050f0814040d520079402038401b0016a41c1000040c0141e100e0a1a1503140d07401070070010b00141016440650480400703012210811349a0b0000c8590301016281500c07000c02c04142d0000d4560708a11008002d1407a180003801c50030556240003c076001e80421105142d140c02d29a82c0c140040b040d0320004a14401405d070041000d1400680032101c2039600380c0000e41032040c0850903034011071621302240c0d0f001040c54070b01846d104840009402900c19486030b45014412103006070303109600e0074800c0c031011600603900d0070411310114051178a00c54400600a1601b44 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 364699595 1250 364698345 364698361
    0x60e19230f0708130510020f0c060a0f15141002030d0f0f0e070521030f0f07050d0e0a060c0512040b0a030c030b01140a03060302060c0d0306170a030f0309081804050f 73
    0x8481d00c46401b2081c0540c492088004088170350080c56000c6c401071240408100d05006c080e081601d075005d44140801503050104180842d940541c0034080c3d54041180f190030745800e06012580003004184140c0b42050b0000c5001000d460260144286031522100b100200010901c1075010f911800401043c080d482d107404501c8018044822030075407540300c0c4295041200a0048900c015440049a60b84078103289950342a50440807065406100c4e480c01049800d001e40710b10f281c0340c0c4004080c100740d01d00d030100464041c4a5148112081e00a0400101d03210801c1000382000c0d003000300030309448805c0d900c4024100d40301030504404060501d0403021869801c0315403c5c2207180300d0400f19036283c00d415025006405598002500580c1c00106107511150116080e212140035070703818000b00b035681c0c28031203116078055200c16903174000d94440d0303000a0003180f20480109060a010404001c16100c000d0035801156040301070741d038010419501461705215440e400000310741112590304082d11 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 364700845 1250 364699595 364699603
    0x70308010608101d071707080a09111009051509011b24050a0e06010b0906130b030f040309060507170f130306090501060e19230f07081305 61
    0x1061406000c1c49038003280100c408801440090090461350010400628824130300042003141d0840010318070a004202650800d014280180c0c400e0351081e0254031007038402e100402d01000c0c00c8801e01e160152481454a440c414003080c0c07060780d00c81c01d1718180b9200c00d0001610041c2c84014154504008a1410f40e8008142d80000050340380310b0010014aca103003045551480d1146403100070320109000302c06138000c0d005184a8031010600348004983c03d481c3e030381d40d031100b07014503411034806020701c1d41d20342410006007441d80d180d15000306c0c0040c2d880d5011402c030762058800c05001119202003105154105440038001d00452070094501007030780e01c901d00d006000b15004640014002503c021085030541624002c209404c124030042d0350324274042d001404120802c030360a50800d200040e000445812080c4560100d00100340c02c02d009a125900801c28483c020110300316241e100e00c4042d02c440003180c0f0400100d000c2c0701090a0588003e401000000c083c1000c00c540c19920400140000c6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 364702095 1250 364700845 364700849
    0x15060307090612090510050412020c0604120c3210120509010e2e020406050d0207020301110a020c0306060a060203041a1e0a08070305040f0816020a090b03060c07030801 74
    0x32070f00b1041c10300f6006064019140460002e84188035601c3c1000024480790b200900980c49640440c1d00b00c11120000e980781c5540303100c1154080c1d030078001005810392100074074000c0c0348900c0c0c144070000d45604000c0b10040000d0360020512403082c0c0c1d0b04034002d400c0d480c19000244121764803800b404e403005005010250000400c6100c2c3d481d000441d45081c800d402500313181200340c080d11316007202c40702c8104032000b25400010b05038a0b911250320048c5000d00c21034041e6400c60b55624980040601ca80020354050901244c140d96107004030b2501c1d01404001c0c00d0901400da02920303202c0c00ca442003604d0940058030301ea12411202c4400c10640da0000b044604490040344850380d650a9009101014060742c1401002c640c27042880b0a00c0303000003001040310140584818140f174031121000c90484a00301c0d4000c10303641c43c50700c1180209400c28054400c4689041c217180c403550b0103902040718003900786d0012092a403990822038841c5024080d11743d00000c140061401d21101d81c500400310300c018 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 364703345 1250 364702095 364702097
    0xa0e060f0405040f0e01050106050702012012180d0b0f06092502150915070306030f02090411150901020d0302030405030405010e12030304030504090b0111100f02071505150603070906 80
    0x185003060013050070b90300b000741c0d4400d0070f2000308025a56080098141e9010300400c0b40094101148203600f41140c907240346000d4107200041101018000403080c56078085502c075401840a510b190140307070f581c00b101e05c2c4640d101d05540750140c1000100244407180160006104907600410040380104201d4003080075546c07500741b01034000c00349409908045440450700fa00e4142c1c5d204210381c10400040707440320600c142055182c10703a07440c00c0480c1210420700004202110120b488405440c1c41c2c0d41140d00240105030803101c130020301000852494140764200c0e0095404580461203607014007580305481d0f014103096286240c29911217442c0e101c0d80c0100c6051040c2c7c1d84400c4d4242e211031010710001c60100040b00d07942d0405003006081900203103c0d0612550500f1100440d551080d0740051038090010011306090040d03842034000783c0742b100c10024105a00b484000003045c9028440c170400c60149100250350705158560364601f41e003805035139010340410400c4c00766203540f1120510443c2c0503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 364704595 1250 364703345 364703351
    0xe0a02030c01031a09010e10081b040203180109050a0b1b0d091a0a05150607121202090d0b100905011d1e150109050a1d040f020402030106050a0e060f040504 69
    0x244441c1810081c00c0105500605c052001141ea0360080305114010455003244440322560f50145c01e0303480c000c0c21030b088240d480188051650341010b402540d04811a18108103091420413401402c46062140940703190b40440343c1c0009201c1c0d60b440980c0c0112200b000661002e0b1815000505840b400c40614032455030b9214000c1486440c50b140003001f808000806000c0c1080b00d518406048182d81c0d0200c4c1e0304140107800014503200003202c9000c0c1d0b110303e20000b489488001615140c81c05a10408c82079001c020400450342d070300300c08860840c4902161207150401c400c3c014983d0303500381c0102c500c040ca0480103001040c04e0700612001030301040030020b499a20382c0611041807200082d07000428070b02c08188080914041e1042000c0780b001c0e607449440b5a51002040000740840c880d041000088555168021962199850707000303000c4e84014108442c1030b03000c1000ca920907801440021404507011040d80c0c0e01900e01150260300311001414002c0d101d00384049445944600c0e0700c180c1e5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 364705845 1250 364704595 364704611
    0x6050c09150d0924060504020a0c11010c1e05060a05040c03080c03130e090c031b100c0507091509020405010e010503060d061401141f05030702070305010510090e0a02030c0103 77
    0x18803a0410307800e03513510401d4911401c00d06030121119818018840d40f05031704060000c80c05041c00d10035510b503880d00d962680308504c80c9486081c414840324602504100d01d00c0541c501280c1c5c84c0780d004c2005e00003e1102c448a8080f401d1860a0030030203450890a142400c2c14000400e05a40d0403606498100d00c04039626064404294510b1003981c2c681440805072810001e8403000803a041d40c0714001c1c0d1003d0390301c0300c94403804142d114560799500c0460b00703003c0407504c0f40d81d0801700302c07189050035981801c044014082d144e051404845500110708140c4030402403003011004015000204410207080d400c01d402c1c4000649001138212685040140c00300c00980e450f0764030b1a160101c40d4010100300041b030b602e80d0000b0f107101002d000300b200501134641c007281c4034141001c40c401760490f50620550501c11040b02210b07503a202600c00400c511a503034021010607403c0c41024042c05119804c02c208510b80070b05401610385030000851607412007501c00307000d44c40220b4030110131070003407a000031070203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 364707095 1250 364705845 364705867
    0x9040507090c09080d0306060e0d150e0a08030f0108010c1e050d0b06130f0b0705070302060c010e061e060603241c030e090a02210403020a1e06050c0915 67
    0x601d144e84228007920448040c52451a09a40108103a801c85d656503418605200e01740000064909401000300e45854080e81c5a521503a101070880102c000c01c0d074031450103d132a20303211600160780740030010f4000d8004020300c040911a400f0344480745c1c10002c3d0011204000f4024411103010032900780b000000d21804000c04940c02031030070310001440e040d100d04c15440001503140e81c9000b54031501c00c3c500e101040c14285042507a00e4254004014606581194240402c503041701f1103403101903407141d07041c11100c50180282480307501103600903000c02040246030000c0301b5020b42100d006400400901c00c0c1107914a04403c0b0001c4a000401c078010126004141040504214454189a943d41e00010198041400030100c0c0d012641c40d0510f84071015498102c0c411090f500c0800f51720701e007907591500d0041400592080c0240190f07038040055031180010001d09141c065283e420702442d240400055114a54010103d181e810703060031121710104646424034224a81603a1001c01c0c031171170706 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 364708345 1250 364707095 364707107
    0x703030e0f011409010e0d080c070309211a01080a0305160609050d020c0f0109050103180606060512090d0f0c06060302060310051305090619092001090902030405031602030f0601180b09040507090c 86
    0x1c144aa450dc000c050806841007075400390804d0443c2e40036118502d00e006982a02004c038142e0b03031000085c01c5001304550703068030240c2c80440741460212448080758042181032080c43c24641c0201e003e40038034804c03214002c1c2010740500c007580c417032050602c0424407640d00c240d01c00c064400c282000902100c96010f01c040c28116000000e02a9083c20070108075a0b41c0003014104041146a18415030380b91510b00c0d40e21901550444400201d0001c5002ca030144501c0504c40c849018081c0020840d4407500802c80703a510407900003070291009941085141400382c100e1000086e81d090400180c200000c08546a00014244441d4905c1c41c1c28440081212a40404020780c3d0244012525049050300b204c550050200284e0100c1d40c030000018600200d40221b902c40d80d03001d07020f1403400d072000d0494203010700c1003102030307070144140003500c036030307907c0402105010704040320307581e003413140e083c0081801e072031070a00058060366110052000007000024110260b540c090004944c1c030b00359071002c4441c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 364709595 1250 364708345 364708349
    0x70209090c090403020106140609060304060b1f091a090906040b13021206010f021f05070504180501053303090a0215030403090f06050703030e0f011409010e0d080c070309 75
    0x2021402e04107020405805510890845000c40c181c2c2009441c142d041080310301070805085d1b0000010400200020900d901201c00488024002e44e222206403030503902741826201071801181c144102845510302003d50a00c95504241c0c41c61305e000703090301c042010000c01412090007180c80d446440e04031b640d1100070a00c0c0100002c0304540390007551103422070300c52090307039001e002c00c0590802c0003105201095200383d0105180c481c001c140c545c659404010300b001400c01040000a00010a90307a140202461039900f0401300840c4c0d0794180400c1099011341c1444900140d2203500e0a1400750502c9040c0c41d50020b075101c0703d582c0725502e030f0300810b040185801009500001002811803c90300b06030185000e00d000b591009011500ca070300d04c9094103524010000860001e01c6042c000a10a4000708502d40200050300c4110140c12070003820355140c4a109003011100f08204050050300b44940c1107080b02510003451908040c04018100b0720000e4018040000001032003000c0c540941040740c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 364710845 1250 364709595 364709599
    0x100e100b072015190206091b0d0807060c030605100906080a0b0301020a120b01022e1e0b0411130605070602070b13050606010908100f0e0f07031a0c070209090c 70
    0x20994640700f42444203035004608050b60b03640c1c24040352020620008400303210385010070081828020400340f0b454000b541c83c034020792080a04861100041000c406411621321504010800041e680e8028064445c190080303030048100c1a082d611066100380594121130f0306090070b00c440e4882028403405440d001c1055a010b40c000214221660382c05001d501d460310303a0403410404404001d004a0f11003683e154400e20080d806238030920080340f8004660075103d05000e0000340c1310b142e94042002c1c2c0c0884205120482d6407a410004242454001c0c284074021404610b40b910903841d5451081c403407540149400c002d008140c1360b08122159040b2094250400d5181c5203900d0590394205480c1300280d001c4840d4042c1d01d003c207009500613035007501a904d40c40058040801403548080040860022214a03d40c84210300301180c1418480030441d0a45100034140d034600b14140800c101041e00c441d4900116030a081213820241c42007031300c0002e54100c031029060f0701c0e1051070038549040c00c2d500035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 364712095 1250 364710845 364710859
    0x303260703020f0c1b2e050307050d09200d0b070c080d0e01020301050f0609132f0702090f1003020d03051c090b060f030c040c0314100e100b0720 64
    0x390790780c2c0000940e11585000301c0b28420005030070b0704045118100300081071b49503000c00c40c3d0094a640100c016640c840c94600d000360400b032000300d608040c1c6080c070381d040d00c92141144502c07100748101800c1d00d600240544076a6403a002c1ca603107200340c40c0c0000342102c0c01c10561f5003e02081010381d42c00c032885210300001c240106004442c1c100d000b54400c1c42024490041060b002d0f4050400c00705990410328024290041d20254002e414080c16180e417000e00700c654004103d0406920780c1d00044c0d03400d200000c4d00c0d81ca49441d84188803c0100c0544540e01040100c820010107141c0120300c4000d80e681078600d65007044143c5016100c5001e0344415010084588200801c2c1103419807040d5110b81c00350300b030000151103078070500c21022040800641c054004150031540346c201900000c840510310700c3c000807219250980b2034107a640564070404062103820003003200c0701210381415044110b0300101800d0624201101030240b00ea40e000820001e40c1908954106014180b5800140e001601c40d1b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 364713345 1250 364712095 364712113
    0x50a0609031b1110140d0506041e0204090e0303060a030f0302150f100b030c12041104050f070908070b0415030b0307080c0406140108041e1505010303260703020f0c 72
    0x25039003603801e4500c042d000e1943e0403400c0030b40c82d105007036860421000385e030f000b8500030b40c0c444035401400e8003c0659420980300c440780085602c00c3c1411020b0210798400040c1c0b03403418445c0d0708040daa117070034190710240e00030700c01c1c40807a644900952049030703072104d52113020020074501a41001202003101d0017541409042040001c105040203201d00d1002051322100ca407607003080003a5000950f403c0072041814007542505408502c103450b00309004030340c015590303052500010151074044403809031700d202031390901a0041e004803031200030f00002e101800c916824401e9520050040e485a500301e140300c04903d144d207500940c00001020f03805170694108a0302c503002a40e684040821480c0101d240c0f40000510345c2a0b1545400900c105a588840c2a01d5580b00c11010368180584000501904082200010400c4030800c0c03c4c0c80310140041001e41c03440c20041d0a64002c090001c0720072080c0443e0b0072903510124502d650144c424140143c455401300c02c00c240d10b000d01c2080b094144940400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 364714595 1250 364713345 364713353
    0x5090f190c09052d06070512072907140a031b0e10020c03060a020a02100203100e0c070b0601080703090206040b22061d0f06130f12050a0609031b 64
    0xd11000e80d541520825440b04080c00f80c901a02c2d5045a030604c11a04402d0507510b61410b10004c1050074000c2c4c1c01c07651030703016403c0c02802951000d042200e028807030000b80c0c3c03894883c02400c064601d8140c2e03101e18840c40c0500c40a003042640480c1c100d4072203170000751640402d010740d004219410791101824030504c0c80383c0000d015800d104e000e041c49400454200720b0309910004088900e07020103000380841c0c0d100d2600940281d004140c050042d0702443e03801c07060300741885c4050b5204107a0741901c04d46140c03400e9072400010b5009860704040d00400c01021002c1f40e0000c1484d078101d082842d00348403c1e40da14004800400a80c00000c0d8071000000340000c1541c00b07078004d00762084004405001144248448032100445841400041190095100481a450450909682006040359009030030003000648c0507800404000c1050220002c2402150000c44001000d84410360650804980380e031241d90340c075a81c5280080010b62107001c050209881480008504200c44001401c0d8403c5032034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 364715845 1250 364714595 364714607
    0xf0601052106150a090e060a0b0c03251218080d02030c010b030d0c0609080f0c010f0501060e0604170a0f05030406020f0a150506120709091b05090f190c 67
    0x12003a1103400301c00058101210303c1c0c8215070040006032200e0700040c0c580340d8503440029008100c503501142034140083d00c2c0500c0d100901102e034081002d183c1d0381079a00e0050841001160090740300c400480d4181c0d0008403a0104454281c100c0d08145072a040f41540c40c1d02880c1342c50700440c2e5a8000c43c900300014036000009850350740312200090242c0103041051681d24610078810a000801c840c10341800315440c1c3e070084904034000c02c03a4910b010b10520503005a64005000c00701107a54501a10119441c0b500c075183c090070744da00d001e04400300a00c0002d401c0307000e1805850440c50900c00c880302004020014998010b43c48130400720742d05100c2c10040d450350811710031540940aa8102d0702480d00000c500d00c0381996104050390b082956030b101c1d10b001044003c0c07800d904040122803848040740c1c100420f0008001000000c0f5406e052803400d0300c0c48241118460480625000082c0702c107035604d00c40385911010300d42e1400010707901c1d42d1210055000b410814031080e880c14448a0080340c0c000c1c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 364717095 1250 364715845 364715851
    0x120d02120901020c07151e05040618081b1c2402032403010b0307030506090c0f060919090f06090c0e0f150912070f060203040602060f06010521 63
    0x301510301141d407185519400d0344a103050500042d08042c40501c8402d0140714502a03d044510b8030b100050019410070140a026005910118001203000c0050300d81c000c11504a82025081880381c1529040d07a0756903e50031148224a00806034010010544490340d10350540c01d42109880140c90050600048d00da041d804082a000c2041c502180810b0040c02140d0240720143c45c42045c105d03511070000030318284150030550554071207150700707450794040001002460090000c0c01c118105000024035004032084001d01484005100407459542c640275146140000d40d95004900705a02c0b035042407800d00c2e00032110480ca02120342089020650004043e03a15110040000c180c80002c2034031581000d480103540080b14104441c00350603c0f0400d909000311105030a0f0505c521480000c410108117078041d0b643c1da00100c008c01000424a01d05d200500c2203002541c43c290402070029103e0b9402030004100f0075003130b000316460744d10034812030b5000c100882101488581159990514103415 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 364718345 1250 364717095 364717117
    0x50c0a0b0c0403020a0f1a0f0c0109240b01080606030a140403030903020c0105040e190209060c0a021801050102030307030c09030218040308010b03010506090405090a06060f0f060918020c120d02 85
    0x2100f0080f0743c1950a89401c01540d05807c0c0380810a504800ca0b10340b5503100c51120b0390414003d200700040d800e02405618103140c4a1911400c15103002003600030380c0e2240d10034079482c6600f480d6201c405a6002803206401002c20723640035940780d8810007280701400340308043d0010320b01410100024554142d0010040078460b40c246c82d0301c0404a401160140a94020042c1d0320366000c01140302e903038036080d240f03417080c1c0511400350a1820b0000050f9258110320107002194202c100018118604904407101d5100290319025131941032800007543c80c04003c100c602810317a1070b501200c8290240c64040000d6900806081c5028002180860b00c00380c00c1d07a003100400c0113800082a281d071018203803810b80c4c201500d01800c02d0114002c020107054040d02038142400344809002c0800c07414002c98024045c40800d28100034540f40c9120340b45001903200400b04519070800313011706001d10300c0340925201e00b640e000d61250115500707507007020200c44c08201551b03c00034180300c0100c9650054078800e001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 364719595 1250 364718345 364718359
    0x303020d0206010f09020705010902131d0a11010c03030902030706050d0f051b1303020901091b050306030705040504050c041401090605040608060a02031b040807170a0b0403050c0a0b0c040302 84
    0x8035100036a607035070003806030b112520a8a0014400d01c1c4030303a809045014010030000c115200c041d004034540000180d89890f800e0340310503503646c0ea111040d40d00c01c40a06440000d040100c4aa00d40003445106000160f04000401d014002410301c2904604a019001410381b09201e50b140c401a0240e481003601c0304c10725003807440da01c10040d003503c00c05119890240103600004142104c08415078840c2418a80e00c414000c2c001c400b40e00ea411059010701002000050700c2c489110380100c04440080300e61080020400070003c20f42c90100b0404100c03181070b2804121a1071310300c0d02d181031284442c05181c11034540012100520301007003101d4100c401c020010454942c4541c18001a180b21f40034500d1b1950010f00420008001d940c02158044080309078501c0c0352500100200c22540f00d9848805075a0100300244000d2002401403841c14168000400811405582d101c408410040001d0305121020070000c84814040c0075115910742c1c0f02039a40341520f030501021a00c0d4205020903801a04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 364720845 1250 364719595 364719613
    0xc0318101b03030c020304080f150606040609050d0303060915050a05012c0409050a050319050c0604110402090d0c0e0912040e040302010213180b0405010b09040207050f0d0504030302 80
    0xc02052100c0981081e408284880501c680307080c1c0c0035110780c400103403c5110400000032800024070001c0c03032010710840640b032841d041040303c0c0700e00c1c5000b60000d84981000c0004100c45a004440403003116803d40d00407040c4850303400c007500108015804240c0060030f202d02d0500812100e038101040d0f480842e444500340e902c44004440781c60101c44151204585460103802100c0000c0031700403428001070001c200c0c611541e888500745480240304580540c00410700346903040d1002003128100000e4500b0b81d04150b486c500e41b43e592200680f0203040b03c43c0b01e008050300741c1c03a0ba804032181c0382c201038041e04582c00d1525181d0300c0640c80c0d108400440300d018000ca15400130118488a4071010900b40341e06180c1440304100307922402510450035507600f040308900710061010450300070b01207988130100c541200b910035016500304145491003a80740c41c0041c00a0b090150660b041301c44245c40041c0c50720318074035029241c101c001d250040c1d28801c40340c40c030903c1079001000b00103880c030a600b901c0d80346d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 364722095 1250 364720845 364720847
    0x1060c050d0e28031a01090b010804020604090b0d170a02010621120e040f0b10090803030a02070201120203040c21021f051b0c0111030304020d0303050c0c031810 71
    0x42e0140030194030141281c015550425880700004482a0004520183d1680e0307540d41204209170f140b260794110f0050004000300001807203071000500c0282841d02d05480c00c1e5001400921850041d039040554030010201b880d04c40414440c4125403020180c5e41c100c28144540c61700307030460a48800150b0810b0004241c1305c0940c4103142c420751400c1020200f005036903655501024160100c0020032000320003240390f0395a54080d0940b00c0d0480d03c0c00203803040d100400d020415143c24410402c0c42080030040140c0da0001044a520a003c00780042e25203a0510049409084561010000900100600007403204541402c400c9900001c000680203070b40385464410248850400f035030244e0121403c00c0d01c003030050081c1200500c5071401614100300000c00310b1200014074010001c0b68061004544903581000b018007000d01d00200070b6086242c5903002901402d2440d80c002c003019203c0010488007020702042d100080e802409480d1240c1d98052901d0510102c0d009540c45101d40d000445645 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 364723345 1250 364722095 364722107
    0x1050f01030633090c0201110d0b06190309031b0201021507020c15131d06131d070e01062111041505030609100303020303060111030409060602100e03090d030f120501060c050d 77
    0x123800001e0450b0b007000569403803140201580c140240d007000c41041613075a031001501c00c4402c100d9040c0c40001c0e007001c4c9820003c00780c0341c1c200003944031070b0b04005810000d43c0e0001107820020000b030085070450340d01d03a0300c100d041162007490310760410b45c4860100c1010b4481405040640c0b240c0554030009507981c81e02040e507900f1203410401c0282d082020880904059004202d004030455001c200a94502c49230890000c80100c6061582c020a400341700d10102c000c4424014034451408500c04044c0032141d0f072402d6030300703070a07151602e6658070100d8044080d18261402002961400003104402c0000a0710030b41c0100d59161240d07039110005049002d40454000c03c2c0d070b402d035001b5410750b41c2c2c890043d40d24004084802c11184000d010002c2d0b200c0030760045501400f11603010781b544403008c1c08000d0a41d100c075000842280c005101030a4152a1142402000b80d0540303000700b000d0400c40d50685d040d6006c3c81034412054140400850310b07642204c2d842c03051900c00d6044452050103000e0491719 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 364724595 1250 364723345 364723361
    0x50103021507020301060b0c060a0b01030e0709090f05030f030f010b0a0509010807090b03090f06090c0f0d0c030b071d090105010f0e1804030c031101050f01030633090c0201 76
    0x440034072403400c012800e000c007001e8001244040d0000074802e868a1000d406600500141401ca600c03110030004035101e54040c4c0400e1040c00e0030203120303610180d40c01503100c40c1d50780100740b0190b80d03500c0140d06102c18440c3c00c4080e190442c082c1c035911000822103c2042d4021510701030f60700450000080c85210001c12141160b88a03500c1904010913000111503e2002400c0081040489a008034005400c40700950150300400b00030401c441d4005505400d0940080c9042451b4202d4010850340b030f2601d40303031540d07601c4040380c0c0b51048544500d09101607688542006e4058070007401081241c41d08201074003d034061061100516040c85400c010ba400700034080e060009092000501c1040e016070540d05107490018400c0840c01e40010840010741d408480690000d4418900c0c1c0080c140c10141181d00000700b88001c4c003041c81e1104821030004418170004103256a5160800628a03003d1048000c442284a084002c84000c00c41681510010700a1002491500c148080094014070400031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 364725845 1250 364724595 364724599
    0x907171012080a1107060201061503050f0601050c0a052416090b09120318040e070806040b070903050a050f0607020313050607110907090f120203100e07050315011805010302 76
    0x20700d40c8107a5030700032280d000a0180c0307050281d5881c0181042c2028002880034284540c00002c0607860480500031440b084005102450325085c03c0c0036558039045500c6078802802c1c281580c1d50300785c00803821b183c07541150001e07241c2d00071041041c1e00121024004505220307401d441d100300c0d44419600003903031481d46c0147c01c082031058804100210701c40000d4040042c001702100449285044424250f50180b203910741a00881580500715180505c107120021070003100030100319050404081c1e9130240544060564a80440003403c1140300380c02c0400070b15070240540f07500c020f851800c03590360b041000b078140290041a000505051001040d12045100c9514110345246000706200d40d550001405486800520041c070360281c507801507070f901450095403000001c034605084108200c0580e000461780440d0490008050313940090b1b8845000944480001c0005a4400461611080d903001e1078041c091440703071300001e404d0308059030b04a40c000c0c1c410800000d00807880804681003400025 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 364727095 1250 364725845 364725869
    0x20306060910050408070f0e0106020304030c03030c0c1a070614060f060d150602030a0e061206130e1209030606100f11070905012c0417090a0509071710 67
    0x20055250206415400901d14101071345001d13154000d16040882d5500080310b00c1704041020800e0340d841000b4280100003a01c0610b00b042d05559403481801aa480017504202003200c03000d040c401d010070000014001a8004811001ea011082000f500280e200f40c40c50392034007000154902e512140e141c07040400401412210402c0802c002458200d030742440d8242e40e540c000039000021000509001c3c04941c0c0003141c80d030320007400003000203460055190040100f48512202400ea40e48400d400a404490701f180e0340d01d81104640082c02455405041c0c6d1103130819a54824407030000504150000b03a080d5041d5036181018030502101078084280011200b040ba803500c188a0b0007020302c0d540e900416160b100da40c070142003040d61000e8024051050101c00000100c03d90781c02607036070f8245800c6074541d45240c0341c5c94080d1300c08824068404484400200490607a651201003005007030000d01e034000508010318010030103408103240009483c22000407070485c43c15000c07003c00b20340c0a48046 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 364728345 1250 364727095 364727107
    0x21e120a05090301092d0b1803070f0b06011409090109020a050408011b080702010b011d0102011404110a0e0108031c06170109030305100503030417030f0301090c1202030606 76
    0x1261660209001608008040c00259103d41d000c2c0a2090081d000700c40014800b000350805100c4203c134221b5002400c10400203410000307000c122040d90080300703680c601003a100c005104500714403c2c48002071000f81c1c20200c9404101c00c440f0010f000325402c0c1e8801c03087c1c1d1440d6070b080300980705508a0507031000c5c010004000c002c15603001416007140c20f00e011070400b55100d142900799029500040c0d030300078402d4881c070600390380440b0b4580e210034503100901c904032100c6d0010b8a03004411364000a00d0700ca0706910790180c0d00035000300d44805200200990a840c080c141a410018001602440b03440b00102c000741161564031040d040e1001c8a01852074030100c106189c005003100002900c0300e6854010014400755031440d050000c81801001080c0688580707001811118010400000d046090b90180040c5c0c0b000001d403000d0301c1c03051101505804007017141c00e203180545205030714210800000880c041c842c50300500c980c000355440d01a0302c4002020080705900040f01c82d80d4011000b4414 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 364729595 1250 364728345 364728373
    0x130e0c2403040c0b0708071101030b1f02011514030d0c0203100203130206040b090901150c02190e01031505010e04201212090a142404080d0f021e 64
    0x85802c03c2c071a10071a80c846030750702d020382c015800076a010360304c069000c110b010900401841c50b101803002480d0030400c41030070380001049130b8039540c080548400312400130901203000f5441540c0c0e260300704002c802a103548401c80b0a143d2286d2207414041c0c0a0361801903196402582c0c4800c25a60040242c0014400500444000c0d000140483c40f541700c110b00000250300d440c00200050315100840783d030389600100c01e01c84e01d1141a03104840042400d08005251607006045c00000c56048845068168085003890040c0c65180c122010001040380000200030259240c02143c2031301c40810b000c9683c0c0d81003d54607404007100e024220180b09012013440386400d48696031491001801400c21035107907400683b521000c1801000d8640000960380c13150316203c00f5140060041c0f0444400c0704101c200031885004961f0034003044000c89842c0c030f0004150000648000d042000100d85c00d1041c00d0308018503071140000c920700075002d1402152140c48a54210181821008009000200ba0444 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 364730845 1250 364729595 364729597
    0xc0402030c030f04060207080a0305010e092d0309090f060306180307121b0303020309010b06070f03030216080a02060f13020109030212100912140703090501030506060702130e0c24 79
    0xc80c5c2c0c440e0708001101c00900b1320030140202041c1c0343d400140642c10320912150290b401b42200100c1e40c40b03c0303441c0a609280258046110400f0010003000d1107140a17070038030307601595035038562000054040155806100384850321400049089072059182c6403c2040908489401c803c0a5003082100c6070106a8880360814010621b20700450701d03804030700c0e81812001810108400080e00002400b111a209001d80c442181040320b4051a00c00e140c1c1e503001c1c10003a20b43c0010103164020035103980c5003551068801620741c1091039681e482d40b041d00000d41366241101d044200348500780c0800c03400202d442d4208038241e41030b160701040c43d080d9020001d40780e4005000340d444c0c0c450080c214104a1103402038200844c0308400d41228800000c001a000d0799182e000074608000c1880402c001c203905c506070700205c40080c2400606034585c0c5000c200540309100019400080b0b00640410b0f909450348610750340c100c91070a03141001044020400d5100d00031042002c050311208081c0c21202c0c143c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 364732095 1250 364730845 364730851
    0x50f160e01030f0f140c01020f070f0905090319050705010f111b010204080714100206070503150f040e0d0201051b3903030a0f180308042f030c0402030c030f 69
    0x4001021501982d580e03101071150705c1c0b05d90003507078100c504030b50440e58040100f51164122040900261030801c81c40711404031035441022942c43d1550040b60b5601400d008031501e160608840c20031100604401800a80c00b03140f048550350b203844461050309146100e0343c44e0500c407038a481c03854202d01c1c24201c00b0002c603440c00c00107195800c02002030802d00802805000b80500c01001c42a40d501c841048108000c440c02d034000e5401c882c040140c060351010443c0d44c459107202d405403100b409040840c4018112550054125181c18078501e00345000107095104010198001d0015685a10a00c11104640344c2e01c4846107a090102c881c135440c06025080c590340303280b940c00b0384549080c0c181290034080100a0007058000000740540c91495005030101300c0744138001400403880c1641d030403040d003442c4400901003003202c42c045800c1102400200150903c00c4482a03401d9598286104c8000720b008001c82c030030700c51951002d0381d50801e800be40303104a0b0304043c1d40d0700759942c0803084951a4002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 364733345 1250 364732095 364732103
    0x30f0201031d0607090314160b07050106090204270e060c0a1107030b011805160c052508190803011401110a060204050909030c07031b030f050f160e01030f 68
    0xd48030064103031100f040300a01c0307016251340b5600164918100141c840a281881e41e0558004a121b210f1040e20000050201c034042c9101c50760722401c5050560052103150010807445000280000301500d0b1794000c18113580545034a014035042e1545817070101c56010310a0040364000380001041c14101d00007030955207105083c4001c14507008410103060a0080e0800c96116550f00014009441105d5044c0354a5031049420011030411420745801c4500f50b8203650108000d040300d8000700f001c14802980c2203004089403071030383d4034165a1070944413007e014200041c450701d40c83e44005800302d008441030981160380f8918513400e029240070502c110f000e030b0b02c0c10702100c240190702c1d9a600f040340c0c0b008039001d030348016201e50038007003004414500a0038100384e40d4270a02c41040986004900c6c1411a50712040145840c0d071009a1703449004040c0d803019000468858580c020f0000102e00c80c00362003011001d48045000280548070111964090b0550a403030b50801070cc00698004100e900e20350003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 364734595 1250 364733345 364733381
    0x40506061507150f05070807081303050c100911100c150209060a0905010305100803120703150b0706110705060408090f040504030f1e050d0f0b032a0604030f020103 72
    0x490740b2054003d00f221624030000c00c1c0d80c0c01e9007914981c0c0900c20030781c00010a203042c151a0070200c10040c00c00501074880c2c81e03c1d000905003e02010b0280045070390030080c1d8810f0b983c0940010784200018107040d0400c1e80e0440e400c46001c0403514001404603400c050545034990b4040341910b17401010480c42c82a0680300360300f04518281551201e003e8200b000403a964129003d04040c001030075500050807002c42003055860611400c6008015605c2c0c2c9103840c0d00200303042c0d5500e50203c002e01280c0c6031075441c461046102041011a207401031201c00d0160070140012414001c45d03400d24410607101900507005032010900107014030300100f04e010070041c629047d0505500018080f5001a00d0450100b004400c4a146003031b0069644450510484031020040c180d400001d817162041e43d80c0c41400650780c0c101000400020740c00355100010280c111505010560741040d40032101c041c100028140306a910b0700185481d008031800c0da9844501c80c81c00300e40e00d50045d0080c1c50b80003a03000030066 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 364735845 1250 364734595 364734607
    0xe06220819050708030f070b0406110a050c2104050114071e060e0604120e01110f03040e1303120f09050f0d27140d08030c030403090503060405060615 66
    0x10308000e24080c010321034a00d529074210030300d0214036000d0f07181d000c1c035107a070400c0c4079001e0100d100c0ca003500e04c99608002403101503640c9181007401481180c415200c4041302140410b0519400400b1700803c80c8030703004030342c10441c2140808047c06040c04030707408a40c4042105201d95485110101c0c800c2c440d0b25586400c00c03480b965910148920351600902c5440d04000e04818042d2a0040c0101e4490f440e002d01050308254440000c0c03458003840c0402480421208003c3e140d229901c1542903068440544540507110a00143c59a100b88a824080f03e1468041005c0100c0504d00c140d046603d41c4450800101c0869858003030154181e00742a095940c00180b004a0706c1400384500c0a500c0d840509820350307207041c025107200d0f888800c1d4220341505000014000c60004000415910948050f0b0701c859070000000f21401003205008200c2e88000c018804505080805140618420740380c1c0c4841c161504145a0340300012500079055511680104006041804c49503951441e5a9111440c043d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 364737095 1250 364735845 364735859
    0x4060e0709020a020318060a0905060307020f16030b0c03011224090327030b0c1e04030b010e070305160c0611070b04061808040e130c0e09010c0e0622 66
    0x3e00a24072101c00358000240e0794610070224180251400800c507442410100b041000400103145401a14014040000490401402000b080400d000d841d8102c5081d038a00c941d0900700c400491208a41000b891804110025040b400740c074180d403030608004203070010903140c4c0202d04410303c601380705c0b5003009180300c10192050700130030396503034080c0e02c9640328054801095160301c4048030960004c42100d1500f88001005000c0403a0000386803a2110340795400000030741240801c100300d030600c1d00381c001400801c10541c650154101c40b220200f0080c2d40da41d400d02501a18821241000380501e030403850360955000b62132512610380203500028080741802c1c00440f480c0c1c0149010b8074820041c6080104020041c0030342c0009420745c26800c054408240c0c3c0e070030094001d900070880c41e1168140003030500c000c09500042110741024807001d00507901c0c15030070342d90784007510b0001d8654240032103078650502070031030004550005000103240c051010300c5086421000075002042c110b01c1d6000254030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 364738345 1250 364737095 364737097
    0x307031b1716050d02060c0403030503152e0201050f070813050f1b0f1503070516080304050c010e031b0a090c02010608070e0610030f020705070303050c160302060304060e070902 78
    0x4242c0c00000840701406401d245241003032030382c045000c551080d810004000b03011301c00c1c0e608072a4181002c5031241c8401094100301c60880040540040c21007448a02071a05190a40741c2400890072402400f000e18800700d080e03c800f150709400d6580c0c0c4001040c8242e10460f94103030b2012103035003051941c8005e40d941506001411a40c4001076200442640c580450029005c0203a20116249800c0c4403140021514000103402900005c840c0070002425007030054040320150040c420f0761403200081803402d00055001964140c80034490f0561140880d4040c18103400d8440740180248032903500000c1c401801a500295560004450840000c0c1e103d030303601035402d000c0400d80020449a08049000e80340010782e078030001002420205201c62900c55220405c065802c0b0701d000708010744001811400303845408001002d41c401c19100000740355110000d060040001c00540d4140d00515241400e0415a4007020f0341c085003c0020034002442503000d4040040581d0640e001d05a0f240162812 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 364739595 1250 364738345 364738357
    0x60103140f0105031e0a0308060d0804060c120e0a090f020c340e0615040e0411120f12090126070f030e19110604060c060c020307031b17 60
    0x4248072107005011600c0d0600c00519a00140080d141d9140440340d949941e4000380003025003030005280c00b1030a181c07520300d030f003d42072900f180a00d03542c3ea5943c580101130005a0f401590790f06001d683c0d0400740e5208040d0030004000003451960f506d03090910180040c0b54020350300200c0d035800c02162041503001d0082115401814502e071540365080d03141044590f407105458212111f072008180243e040c0705541c2c0e50000c0040e6201c0c20700b007404202c011807900c40ca8107c65180c0d8014810082000819031001000b501e090310740c00d0746d1100522402e6500d041110601403160846442c14402c0400d5002402e5400014505000384104030301189000300d0754105108401d110176810854000d030411148030419601e448c00704800c42c420745000c0d850382030007042000c0301c58003013035130905101b131040d618040020b008000d0f542d55966060060211084d40008846103410150001b0b0400e0020007522509905a180c0d40180d400e0190020045810807804650f032a00c1c442d140215480d0100c09408 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 364740845 1250 364739595 364739611
    0x10f060e0114060a1209030c0609050c04060512340e0a0b06121911040605090118050105030601120f0204030803090f0703020a1806150c021e09060906010314 69
    0x44954104042d60340340c510300c860b01c94000c0000f0010b8600082d400074003a0f0244004540c0050302810503d8111511420b01c503014059600f440c140d41d06000010894000c0480111000c12945640c0c0e028408030704003421150300344d900142103800c0304a0f02010b00103803142911000d100c3c2d0302201125100e0030760982d04a00c0902000d60100200d00c4060710030320846080c22a02c1c030f410f21824004131a480305c0000c0a00d2200f8400d03450701d09140d0340e00e410000d16460b040d402c5a480d640c80f00e50003480d13600500340580c001610078a04076040281c03405d040007504c030184e4480e0303d140d0b0380e1401950440a8010f4161909981d51003031400d0300d03441d20241c80075501c120320860b901d0602c1c180440c40d00034030204420385a00185020001640d8400110084900100e001c814550400040d00700801c0c40c4e03031041054071118043e41d07a413036901c09a492005d510032960007260202104e4418048485801c3e0300d0340250100e40482e42910342981306540c844414980415180450031801d80d264600381d413621 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 364742095 1250 364740845 364740869
    0x10c03050103120c050705041107050a26071106091c08040906081603120e1f0f08070c02060d1b08150102010b010c15200a1b0201120b03010f06 63
    0x1200b00001c0719652000143c1c03a02d003000c404502074580070b40b1040588580740c4100c0d07031107080b40c48815020042c1c444158225066440e54082030402c103000d802003a0307103042e01001c0991190720b41c000c0f0324140d0340b40d2a00103440034202070100040c0b0802e43d00c0303d003d4035030082100c0700154103121941420360300c3c54030030904e00d61034514040002040e900c0b01c1d00240b2042d0403040062001e404000700d90022250055011244e03030381205815a41071800540f2150000c21302030362030740c100c0e02d140e0100d01200350a43d101c0d8515003205c3e104071180441a145480055010054940589800005001005001d030070005a100311080b001d41d480080c4c0c944040400c0076a02000000d1030355840f0202c0300c410a000074051100010002013545200440043c07640c00d0404e0052031015669001462095040c811044488401105242950400284000080c106440490100220100d24070102d03a041c1c4418003010145107594010b0b04011825540641d41c8010318407016010340a0030f00107100001d485 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 364743345 1250 364742095 364742099
    0x2030a0f061413020303071101030e030a0306150503090706080405150f041403130519090501060809070501030603020f0603091c050c0105010f030b1b09030102030411040c1e050906040503010c030501 87
    0x902d5141d0091080f561520107400080141e1000700464903441d5112005403005070007080103074000d0030044a200c1c45c610010441e6020340e0b4050b03000344152410081c800341c200041039011149403000719107010f519000014100145401442c0b1140c00501c900c0070703191010341100701e003090a502142c80c181c41803c1322080c0410302c010210241c10000341e441c01b0711310300b0103008040400c41800f4850386008136048000326010040c0500d04034094006010144640e5941e40c3c00140310755000d659400d40381c0108400040c1c82e60007445a036080303d501034250200f10603a101041034a81008141c0407250060b00181c00c0e030b401c107600d0000024881034644680303800c42464028211041604040350403039503030006201051001010350351002d0b900c604007404104c0641d9000c400d004040115406600201c144020004c0c5040c241d108007000791000c016080d0020030803120008042900c1d00c3c203030468484081001d01c500004d104c000c001074403242ca05503030b4001090840c0d410307074070620010340d81d0401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 364744595 1250 364743345 364743371
    0x13020a0e070210020a2615150c070306092a0905180f03130f0b090d0f050a080d05090c0f04020c0717030c01051609060e0112050a0903110f061302030a0f06 68
    0x20741e81000d601e421800780c15250040685071f42d100280e140034803415016044850000b0000211902254208103585a0555a141c29400790515020448409011107003501c0b0380080c030b05075503203418050f510f004203052070000c1e1180203080140900541c0d40101c1e104c1c182c5420204a01c50700c2045200085507654044180300e40301800540100d5407141e10028200190b0300035034142c41e401441200c508582c601e0500c2c05654000300c55500410704d000382d60512041c80083c002602c01760311075840070304c242c0e59030410203511400c54110465021000031420100340c10706501401c82446910121401070782c07500781d02140e510003801d20312241d60002520f8003809400780291500510342806154254030040300150000c2154000d41d410003804214801d1710343c1c4250301d0801f104403a1501041a82402c1c40608043d05a22000f034020a6958001460007040010b54104484052000e0300460700c410401c121b48550000050b68148074416014000c1284030340c25000003840342d1000039250103100d01d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 364745845 1250 364744595 364744637
    0x18040507030b060607170a0c120203030103050706031e0506030c0303220e1308030a151e080309061b010209031c090b0a0801031e06110d0513020a0e070210020a 70
    0xa4038010701c014400704000644140101c0b0884241319420391f11781000d1300301280c5201c0302c032002600c40e80c1c42650180c11244c01100550503203000e0b80036145000c1e280c0c5000c1e41500c44a24000c3d49210481460b8070314600300350300258108800405455503220301034002032843c4c000309001c5036908220340f41072860006015040009103c1e40117010002d00e0301c902c102c040c60100c60790142142000100141104205134417030052810710ba011106072988031910b02126801920300b010010404100c00f14a0680c0081652046500108024944024409184100800c41c040020559002e1124010b035540030320000c200f002d50600b06500400740724a000708142c483d5070062002e02c1c020044012855803191010741503d8000148a00c11812200300d07291400d0b00c81e10242100303251120141d10041581e00800440c5141d1006109036160390300b0016000010500080d4084100c080421441d01c180c1400380c3c0c0030086005542c1414022407840080c1d0781f000f243c07100080c0744060810070a4090308 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 364747095 1250 364745845 364745851
    0x1060906090f060c0f060204030203071202130b060301050607080f030109051e0c030c1602090a021b03040807050f010c1a04020a0b09010e0909030702040e07090b100c020f18040507030b 81
    0x142c071502882c0390000c0a0a031115208002d8401808007902405218540c0c04440c0110750190465040c1652800c05440c0040c40d40002c074491695622031807031189040c00342c0c0c44002402422149181d281004000090f4000c2c0011a0b0340c3c803091000c210903202c1c01010f14001d05e00803401103014a02407003240a1101420000c9030324421007800d1000300c3c6210b0003680c3e40b0030b8980e00c1c09942e804408000340c1202a600d03400071b41c0104101d00700446222150013030f000980400f104008100c441e0754026849000b54095500c4680c00140108003d240c05c1c1100c56007540103052060328138400d80c4851112142101032100414503490502046060600f0075000800207605000c4c10000d4640c0003d20100b03641c6680c42c81907420f80e000c10320600c1e082c4100c49005500420800c8a40d01e2980640d0300d980711842980c0c841c43c980069901743d4144882c0414a24100b5a552039490140d0303070800040c111f181101e290080003825001020340303030f90900c06006034018401400100c1c03651030101007903c802 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 364748201 1106 364747095 364747109
    0xc0c1a0a060e04380a0504081204060209091605092209060b0f09010b07120504120b0624040b0c0a0c060c0b010f030b07260106090609 59
    0xc0c243c050030142000d02c43c1081030a16562000c1454609558000795000e60300141c107003c0180d06c6030350302030310900c00541040e0000f29043e558140444080700c180d40d0010b2a0405440c1055840e41e114007041e2021100450044008005010750078443e070040d01c0044425000031a41c850030140e1041c100300c00c009102d91380c202500038000008c1c50ba4082e08240c101d030202c604040e401c1d203041e588103401e00d0b4600403c1e83d0303c03a50740c000701600d402d080080501011500000f61780460808902a091041171410650704014044036105009a602403940a0a07111008054207903400c80b0813400d446515013000f50061800c0945004004040c80300c84440420410341280000f03100e5030144008148a03031f03d6030501c3d88000ca460202900358100301b0700084410348240d00074049a241d6610000f10718403a500b100e4011031080e0000740c041323019003a00f03001d0f42c0e60200d03030b0b08000d181c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 364568345 364748201 := by
  have h0 := BRFrame.cov_init 364568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 364568345 ≤ n) (h2 : n < 364748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
