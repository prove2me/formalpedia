-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1391
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:44:42.962499+00:00
-- url     : https://prove2.me/submissions/3e4cfd7e-6371-4253-b492-58a3f4988300

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 250000000 ≤ n < 250179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 250001250 1250 250000000 250000013
    0xf1e0d05040210050a020619090b0a02030403090509011d1801020c0c040506012607050405121c0207050f1903020d14010506010e0d080310081009021801050303070f1b03 74
    0x70345040c0d20661005000e881054020130484586030916000f9003840e56450590240450100d200030042545403900c410010f290060320601c04d030003080300142ca906060600610041c0c00d9000103024488404c01031000340d241951500d0217045010b800221a91925041010102480b0410a2070360022910945000c0b001c15881c0c012202643c042001baa80d1000440300408101040f00300303c00596860070b881c0c2150081540d00c522103040461800d6510400b0881c0507240307080c0148103401c03080c1d4101040d070301c640440100c40c40520041148500700000283c5a10070041e03124400c03040c4400b1100d68800347c055020013181c00900000f2542064107101c0c8144051402d00991946003d00140d40d0f503029850040c0f5510700501280c101008580c1c50740b100da40302610074030f03c4402010340015400802c10040c5503004048001180076411841031040314010140303240e40d03101401c001401291400000d0303c040310b8100c080842d010404ec180b441004010041814400000c003030040180580c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 250002500 1250 250001250 250001261
    0x3030e0304080c01030b030313061d030607090602010c0801080606040f061a0306090f01030f0f020f03060a060906090b0d08030601050f07061b03020a0816020f300406050f1e0d 77
    0x8280c85c02d10070010340104054076071050404000104103048424040184150264410200b003030405200c1c3c5039450000a24201080b00da00c00042c0c40b0020a11840d039080c0240100a80b103400d1402081d41045080b5848000c014842c134021641d400c407030054503001ea008100202600b489947c45100703807030103d125640c0102c8502c0d00424101d03002c070704285d0080260504a98000c0902c070311030100b0350307a50307036001882450a80e4400301c5c55901e08840c1e681481907034002d0300071f4040000c0300c07417808841c401510aa41e000e01e11042ca0800303030301c2d1a61240c0340c5201006920943d400e613a95a10700040e1541d0107442e8000d9001071340840c44d00d04024545c0d01c8065800080507240034803699814003141680f2581c5c940e42d0010325103001280300850454020030303010a41c1c1c01911011100384a00c140f400d4a503035001c01e48080d1814604200e003813140c00c09119220594802494141400e2000e4424480c6980031802c43c8800130320541e000050028074401003194560495540d03040083c032601804 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 250003750 1250 250002500 250002523
    0x82a03091c0906030902040207060f0b030d1701150302041203050a1701060509090402150a02150603070308032a0f07023f03070204020a1d061e0703030e030408 70
    0xc10320180d91039000c580307400c024003081c19030340d084151801c0400071030117050491412600143c003480101c002030058051043d030001c1c0342c1c60000b41501d094003058501601c502901003030107180811500c10003c14075000381502c0e0049525040d011003c8401c8000788100da001a180e48500b034410400c1541c401e00415a140880d615492a50004010320300801c0c1d0138490034001c20703401c221b09511401c00c130558692290008060008a0310300d0a442d480940c0205804001a00140350342481400100101c07904004241e00a0408605543d1072162911000e0440c28006118a100382402109207131090508150f201080d07071542072203100203040c3e0f004980c04900c100d000b24201c0c0500200c0d4014907940e00c00448940f06800e110004600340401d02e44200019404104042e8000d6100d034001411070354010b03a2228005920380340055200c034aa91019031060804001c402d0341c007500f1104204440703181032a13840e035904007450164000c3c0044281d43c00f09000105001600490100360025643c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 250005000 1250 250003750 250003753
    0x3010801050a0203070c112d09010e0f13050a080f03150f150c07120f03080a180b0c090d0602030612010204150e190f0303031a09040201082a0309 64
    0x152240b00b814030590008507840800282e1200e0f2900105030381000601d9402c002a0803200c401664149007091152540070054403045000d1803480c10741400c113201401884070041c031051600300503d6096203070300043c00d80e5460b40a070032000d0041c08000c0c0421241140e105895560300d090780c040c6201940c204a0700305ea05084041a45a8242401804040306480c014a038030524100d841200380b03190001e18090f4034600c600340e0041401c00007403184c0b00c80c99000d04030a17840402d5510307008108150041191a0803402d181c89225410380b122118002e00c1d90201111a05554004071440d041c0101034007540d01402c0484100c0500401e68015030280c402550b10000c41c5001d80c8556080c0e01c618802c80f0300f40354140c5c60b190226403065040000c5e00d5401420b8030301186c0f801d50307018400607842d0007198100000a80070001c00d50184103203001d0000c01d480725a920021000014039004000300040d0502c030b402e00000307071076003021000124810442d0100001e41c04602804010382e41007200e400055 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 250006250 1250 250005000 250005011
    0x80106060f03050a1404080c12041805010605120c090f040f0906051501050706050603030403050d08060f0901151d10091d090d0c0c050a090f0f110a03020310031703010801 75
    0x103001c65008141c1e89191445c00240d4580359551100b68607486803461150a00901c06021081c0700070030020300040850422030710969030791251010807150180e005100340001001400d10742c1b0852044145d10181c0300c0c880d20340b501b42603000301e410740782003082e12584946031208007002c000481d848003440f140540d200304607641e12040405c0d120316a6011240c003080301848021300084e100c0d001507600210241c15681415a26982e03030b031501a0030012400030400c104100f24560601c81081c40c031459080343c4503091941b505003840908030110180d1810840e07420070340030700500c114840f99021940580207010b900308411000700504204c1c05248800c1360841c1412030501c01038044140a4250a406401c803040c80510644490140031421142d480704407400241650b66041050001c010b80040401d101c00108a14011a031855185c090701900d0100340700316080c12401a40c040e2451030400594070b44442c540c1c070380744200c0e0340e00050802034401e0051040162240c00366048507074400c0203000c1c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 250007500 1250 250006250 250006261
    0xd18060f0c02070501021203060406030f140613020607030e150c0703020a050d08091909090c26060118140a09021504061403070c1202160602011e05090304080106060f0305 75
    0x85643c01442620700507407001d8201c50b884100d4100540d0881001000020f08a950ba03950441d4900300b10001e840007410003040c080211014001e0715800040c2ea1540140002c41c0d50008009000d03018001d010810070001440450b1600110000d074200c05580441d1180d81900c210b56681c144c0d4001240034102d08100020f2a042c40030421964030b506c8000030f810f0440c08001c4c04900e001824031a85045850340e80010307998641d200340b00e00c0a01542d00031850b5400d000b580400c4003400c2d00000d030001c0c0700044103100c2c3d0a010034001d05444081140074414071018080e20041d0048400740010480004148000c0241075400001440c0c0b00b51100100c41011980c401ca1501a0b88660030104d41c4482000a42405a0006541c00000c2c1d0030081043c804548800d440b0556503105680940c0c00844000d505188800043c07005114a00c02449566108800f10381d0b0b01c0380d01a404d8403401d44039008504032071424001c0da006800004002c11483e581c802c40104820303c600d4240b03000c00e1404010a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 250008750 1250 250007500 250007503
    0x303011503290a1e270c050406030b03061312031104090e060601050705102d0903080a110904091103030a21050906130c050312091f020607050d18060f0c02 68
    0x7000701d450001c0401c0844d103002c810400000c00303c1c030844401c8029005d101003524180c4034030190070520755035054031380d800e00e40050b0440e000016064420b601000820084140d0b000200c4000c560015900410194091081d00030f0a6003401c042641d80c0041008030300c4400da42c0c0404412540c100850f04135485207001541d8030300c5200400b400541080124504040454000c1510140c1c043c03c5416803060302c2122a180e2180e0403c8440ec45450304010414540e200e0070a90308210252010800c4403000c40d0009120f02c06c145003d40a0354076600b520060011050b0100c2402d800a410780380e07a0710b82124010304e00a6440d5908640c40b118105401848841d88035091045200e0303030051807243c4848a00680d080011141190041c4d030003240824241c50038007240c51560751f00420661203114510070401c100301071489103804920122446100141c0c00240c02e60000c600381495566512600c0d1610040c000e000d042000c4806015500c03407c0295540c0201412009510700b040b040300038240c01ca = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 250010000 1250 250008750 250008779
    0x51b0603091c0e0d08090307050306061305090312091509010603030503040f06060b0c030c0105060603071b03030207061b020c0a0f05012f0d0f0e030303011503290a 72
    0x1040c140d001200041a06150904560ba070b400c1906050760089049400102c0080d01450100c4070741c0741c08034540f511810100131400180c601100035041034600a030200c0c21720001c07150102c07006501c1d0320100d0100392042c403c80d010401c0c401451141071030041d000942e2000030141c401c1302c4612010000e039a280781803003504140c0b86e0650341d662942e201e58483c60904100004142d0343c0a075601e100043c00f6098400030b07d044d07003a00000e152101c0c0e802e40a03a0071104010085805110b00301300300640f06912001d94002a002f09980340e00046003402c2c1107000380a0954000c1004d490100d4500482c0000b481140801c0202d0303007190612500c0c21306100c04003140e0700c0303018120750b46110b0500c10f80d170140c0c9031100020086944c443d4403040300c24120003010040c41c1211303065084034040d5841140e21040f071000c003400c0f6082000c4204105401309940c1d12052180700c101a98107500031305400c1c4680c012403491503003200441f031850041c0d0a600320410261840d24451450100001407002214424 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 250011250 1250 250010000 250010011
    0x6190c0b07170721060f140607020f060c031c060509060301090c0e190203190b0901030b040305031510090f211b05030607110c0a08030304060f06050607051b0603 71
    0x75070416460340c5000707070344000802d00340740314503d9602058544c0d45003d201d0240100301c101356052840746419200e0f90400700480c0810302464003004103002584420746260081041034461581e10100141d106007107014204a0886030b143c140d811b152154140c0d040b180a840701280c510002d5100c0d0400c150895010b000c009201c2c580c1100108440714031209200e90080c041e900d02c044104502d07a01c0000ca07841240c0e4409000495240d14031500b040d03124541c440ba2041d0b500034600e504540b118025140300410040c2040700c000005035036611900c1d04200c50f030201820b41c100700294a0301c0681000128002d44c01040d82003440010103101501904d2407540c06070001181d2509503440720084148022203400600074131b4400000c103610100b007120310403441075450403440081d160315941400c0490541501c038440e1228181700c2c1402c0481100e402c903034441c9000034020b460100400162146600c11031f031082c03010600c0b0051281c0450401d0182800010f0354403454803a404001d800d000130307100c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 250012500 1250 250011250 250011287
    0xf050a0506100c0c05100305011404090803040b04030512010603020901110105150d0501150f0305150402010f08041518021206150105031b041202130908030a020906190c0b07 76
    0x500b00d00c694010211000501e0054141c040115115004039500c0d150040c1620002035450300100030741c00e40740346030b2910707000102c2d0244051809600c448440d408041c0c005000420750b800030a080500580c01c94181e0291980040950f40e0b413444050020340080922502040c82e07c800101d00f4101889218480e0200040e0303041941000c60500018410b010002c40b0f0540d6900059003225240c0f000541c02400f0004501610600b1803410904040c00321002054650050080c080184e0304030840c1c2c488212030740740c00380e6180d446040444241e402c05c030842c1c4e0814a01100d030841014818041d0385403d00950380c0080303865002d2050340d521081156011000805a96036182e076600c9200155008100e0801418070071229a4004425038481d42c00084406d200044040860610f090f1450000c4680c04007080341d10825128546903200082035407984a80c00604101203543c0c4006036101d07103c0003404101d06000000d03000d0075500381218166540b00b61540000e00710b44c81001c0709860180c8244 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 250013750 1250 250012500 250012519
    0x120303240f0911070615080f060c12130c030c090605060c0607050c0a0b010b0301150503090a140a0b0a02030405010b0a0303020c09182505030106030206070b0703060b04090f050a0506 80
    0x8009000b400c982c1d180300c0c10010b0804c41180401c03405d000d000032400303d501e1040221450003290b9490010004003809040c0c006108105851550309e0641340903035406000d1034455a01d0080000c12103040900051054190700400700078403c2e1224003d040d6034141d4010881d0b280c445040103c0c074010414a020355130301c010300107080c16215a014080c000d0019086a83c5032105958480c0c0e2140240c101c050b40800101c010040c1c48907200440214a160b400d000c0d03d1400d11641441d202c141161000e041b6044006ca030611407002004890501d44e0800603410007802c0030314080c0041d6006803820b41c3c0303941c02d08001074075528001c41d0800c2241d40c15001044074071108024421003a00041041100155003803034001d481c48280720383c800f14540d403201c021002d4540c021100f25000c1e107070401400b81c0c1c9025400c0c80181c490f0720482d8800743e041110b4407031030354900b0800c502500d1150410f0800c10404140003e038108650000046000725080600440d5981801242200d0701212130316800503604 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 250015000 1250 250013750 250013759
    0x20304140d0c030b04050a15020406020a0b27010501090b06090918030f0304031e03060f050103110c2505010c0b0a0506040605060c070f080304030308041407120303240f 74
    0x4005071541c4503005074421295a0380301c51050745402c0380d055a041d007141c1c18040c1000030844101501030402c540450400c0e00742100259030718032951008003100b03010307000700d040b00c1ca02817038480c0d0f401304500c41143c040b4201d040d000e001e04000c7c4200c0f0407040c18803c041d1050300e81501502d101900c0544000d4481c0d0f90318201c161000d00b81c100054a070b020400606296000d6103004600c01c500030340310307600110384160300c54481c030007540015010140340050078084008064072600c00c4880919000c1460000c40a8400041c400c01c10000060b11503006100740300a842044802914200d5540f200300c0b40d90381c8010f450090748400010010034005001440c50405a4425504404081c00000d901130320340d00410a10703400319a200b8110340c04007504102d550250004407000c2d00ca01c01c040c50031f045ca1a5006080701c24041c20080a24846a02c00c0303040304420400d00008010121321401030841c07d04025005012400b2504c42d4502d0b880d1030b400440e0743d04418981200d8038200c2c00109281342 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 250016250 1250 250015000 250015009
    0xf1b0528050318090901052e120b040201020f01020a080103020103091412030108010e0109020d020d051504060204060e03031804050705090a030b0703061509050d0c15080f0702030414 80
    0x90419003488098421202001c10030800c00340000c1c1c00c4a1001c480050404010060403075001003982101c1d80c181410003d0011b0206075002503100c4c40700d461aa0000c0c0c608002001c8541034200c0112488180c80036014004541c91aa0145000ba0240c0c0c001042041030b480c240d120f680800800300c0d1440e401040154400e0303200480712802800502c0c04c4200c0700480c2424142070901c0d45034504800f00044c00030210a201d2401c043c208070380200549070340756000c580201003080d806403184007040d03400700c14418140b0008042145000b9900500d261034a4090020b4009014141c0040c510410002c3d86080000c2143c0340b84070084032110706940d2000800c4040d1000074400310800105001400c81c1e074550094013401345108400c070383c0317041c0307045107008048404079131111007011081807260505a42120403401600d10a403001003100307009092200d4000b4040d4401040007840c210b071030503007540c011807160050550040a0343c1075240e68500326924001d41c010320004401d00c68111250749070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 250017500 1250 250016250 250016293
    0xf0513030312060905090a1e0203070915080307030f0e010f2118050c0301050f0f0408070302010908070b040209070e011418061b06010929010e060a0f1b05 68
    0x164040040741090b10303070440c5405c0e0707030b0140c0744002c02d54441c0104d0401c1103120042030303c038410084a2251407524030f40000366994503070b100b1112910750324050100382d14001c0400d1720192030410200d0b0303681c10041c580100001811100800066101605901103621420300700058034141d998410030f0a81d49030304400200068500006185d42d618000342e24902c800049000c5140100b000d01441d240032002e0500f5640002c0c8000c25068013813040080d0741e9001c2c211141c2180d00900016282c12852070203030b0041410f000040d00030b99000c00c071b2404100502080d54441ca1003540c4500309912203141c00d40c0c124000c080581e000c507000c4520380c03521060300740203040c650031501600c0728164410000708029074003100d020070180e040110030700c410395420007010b8014050fa0604100503100882d45404000406517500c0e500e039900700c260040b0f0717840391250004012006001a0361120040d9001c0c20b440c450b0080100491140500d036188100014032041156030400081c06030101f811856250956 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 250018750 1250 250017500 250017527
    0x2041812111f1d012c060906160504030203060f04150905061f1701020403050601140f06030a0f0608012708090904050703060e0303010f17070605030604061e060f05130303 75
    0x426412112038904024000d90000c0207070004009840380c0b9651611703085000d13002c40401590702c013100b4441d02c500c00180c2258000300f0900c0c41003007200d8081c411100d600c0359038006075140c4101e1062080340a100c0328041e01913403040224110748509100741c0400e1325480715020300a81c100c100014030702e42c250f40018481b0002c0303402881c07443d616103408071000210090006441c0e9400710307060082103020860780b4050045640840c0820818200041442042a03c014011800031010a45070b9180d0b13000814000c1d00d40e4000e221041c1c4a00c5054001e010100103440e15800100b00c210351000d08030220010107422800a501d003410004c00c0c00300c4840e024104884034482c1e444000003150061061021303107640702c40910b540c0d51504040c05010102034001010900441a000e080c06030001105012103006040460700da50300d00b070015004064039800303290328150103407140005050200542c001e0328125260002410383c03034a0111818054407000d0480903144180520100b03005544054090 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 250020000 1250 250018750 250018781
    0x307090f020c030c062205070b0a030204090c030e0106060e0612090c12010b01080730020d0903030b04050a020322050115170c0105032202041812111f 66
    0x240c0c1481c40303e01d564428071604c003603904a0401d11001025035404080a0b40e00907030250b4410025031150b94540da81481303904006d0200040b0704c42075038040d80585006040f203120801c64844580380c040c000c0e040e80e1004403200d5103000f9000c1545805107640c202ca0340f4005c0c1980303050580c141841d00256034054942111440b0301e442d9030989655401c2200c141d04802c0d400482c102d01ca1400141540c0009020f403000c5c061b00b01200c180f2580c0c04190311280503021840210102c00e041e1042c0c00034440c21014421144c1070030003003003d042d0160814054410280d07001c004070340e12400540100e00050714840141181e400c0300450b0449210342804560f401413000182c010080b841008214020b640700103200700103441c20401c280000c6c011030390b4403202820140c0ca1071600541d18043d10b120010010b030b000200c26101029512140e20069a0310583e19001c9800b01c543c3c03c2100103030340200304500c0000c001018500c1c14034404140c01c0360711040400a9500c290081c0d12040207814100c2690042 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 250021250 1250 250020000 250020007
    0x60f05180a0915081b0d030e04140901140a0507020a15150f1701090b01050409050a0c0f050307090606120f0e060a020d0c090302030703031b05070807180b0307090f02 73
    0x51003103100f080c8220400c030441c9042075140003440d034144040e40665140380442da904000b0251190041d00010300d0f4146003050425088200250090000c40300c0040e40d4024802001400d810540c00040d000e030443da00c410700c03a80c13510700c482d0175a102100c0905c0181c00186901740000d00b0201c00003104402c000d0702045801ca49085100d038003065921101c2d20000441003044161000d51a44082c05081d100070b01c01d20086072107500348444107100c0d40340100e596242640c14898180a144038007588407026030800e540d079556691240070b10f401843e00ca80281940002d5581030b40c0705100864250b40c90b40681060f02400c1d0030000d26001824980c447d403500c030200303000641400034034812441e1035801a110600c800c91070040315840c07c0c03070000340408118248050382d000588401143da140c07601c0d07441a42c404c5002c60304e0b4040702070010014420b0710740c08510306801050800070340d005115540c640401c044001e00543c1c7c0500c03003090b01904003803014000030145d42c200781030603007154202614 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 250022500 1250 250021250 250021259
    0x2040c112e02030402090f09210403020111070303021b1c0f0b220b090111120f070504060512061f0305040b0a0b010503070e0d0f1506060f05180a 64
    0x400403200c00d603039928203200e241601c0e0295481c40090002140c90070850840c036241d804140000f0000d0406018920741e44002200180d040101c03410031883e402440c59614894141180036410501040303003c916801c005403202c250006107030003142c0e0140c0c01080e10513103d466a140c09400421216044000640d20703047e0716030707410184410540f050101d9149021a41400d0700141c07405090300c4d1040c049100e500d0790300840c02d851080000c2c0c0100320f0341b00c962103040e40240100f01e015201c081c05440821201840c03880a08414410140070304521140c0e070f5410001c4410b441580242c2c008070303c1c140942c0b01011010b400c0d01ea40f000c0040c080b6041c941008030000d214030014030f807200020380c4842c20071080008a0b410740342c001100c2c030000c0c0308509001e800a00700c1d00000b41140300300203440e10b0031901599810110006590041502c060361600c13401e061008080704034214001a041c0000010a60b00c00c00c0c2d06200c4500c1559180d00380171101c1c814132481c4146c0c050040c2d2100e4680790129 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 250023750 1250 250022500 250022503
    0x12060f080d0311030903071704170601060801050d02060307081503100c0e030d05040605070f020910060f080907050d05010e07060c030f0302030412030b03100507030f06170a02040c11 80
    0x400303011540000c010340380403080000c06441080180e8624520184203121501c00b00100784c0780301c1d0b03070b00c654190251013030764000102c0e034040c0341d1200100d0355403083c00652000700481c0c544d040c0ca100f40d03039400440c1e0702c80301880402c1c140084000c2d0811030400010f407034544540300d51500440c16424000e0b540c42004c1c0024604510903540e040303107070740e47c0022850b4250031041410700c050b400d40c042c1510038250b07a00580705018030301c101d900340000001d90004001d00041c000842582c009c0006216003041c2184820300c0c84075010351804110011070b0198410b0250301205c0c41480f80100601040d41000700740840401010000c56003507485590b0f1000808041c40140d000e0315003030baa0039955504a0078010207d0a002d04200281881041031001141301c1c01c0e206c0030060399505000c181299a6004a40b0308101c0c1e4080d5400b01e49443c4c04d110019034103400056561200714003e2003100e84426000030758690034549185c03154810044540141000c1d00312078500015030606141c0501081c007541d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 250025000 1250 250023750 250023779
    0xd090e0703090f150b0117041b0305120405011710140d020310050601090b0301140411190807090f050109120507050306040b0601031508030702040902030304050d0b1504050c03071206 80
    0x46030010500c81040300440032600c985d0103200030902e00540d20003660410120100b0000c0d0000d0942e215403050035804e400d00980b01001585e128084030140c240640c00c0501c650414081c03240020704c40f86440400d1581e48040d58000c2c40b403880c0076000302c1d00d040e03070301070100d0403d140313a50700164070010420140c0d07020301440e00d4000320780368049402c1c500302000501c42c40441d000115030317000910042c46002d86040c14410010400e0704d0002c2d034100442820402030191900441c04404013407514900c1c241e2000d8514024541603d48054807500c80c41000440c010900031640051a01c880401400310680140000240181c050750f280b0f64858004c079041c51703c01c48040d560448203c09020595070b040c45030000c0042099240d000300d5040400040d02d900c00c4c0d42d8003074440ca482d1070410302959001d0040b1070003881c0060102030290f04510302503001c40412141d5040bc403900000c1d449070b40c20140a403e10032070514031074910b5a6154001074030881c0c1603d00f403e42e16661614003140c0341c1031010f0f12 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 250026250 1250 250025000 250025003
    0x3060b1308060f070f0c02031606111006060c081303120503041202030a0f18150f030b0a08030708030c07020604030305030f06030a02150a1e0903140d090e0703090f 72
    0x200c00409052004a51070302d60b020300040a12050351080000503035004a0064500c50940b625a0042c015400000c0c58541c80811020581100990008007240c001175007048a845207416181c14140114180048a09034030550003c80c980c0c08610300040e68001c0140026803980c0082d20b4100d849840d00c0c1d0550000981c6a0003098002041c8014030800c0013000071071300b000d4401580381058990340202a2440e266035081440466a0781d01140f00c1d5044a800c0640901c442c06000e03440d00240c01800095413002c01c002181c13400445040780d04108840105a4080c00b008503e040d00d582d48400710399000038841070014106001100043c5c1e580801080214043d55560381c4904002008004034200030f00001d1190780420407490058444100c420b101c0201f00c003040e0b407901c00001003500c0c290304811011082c4e14151680ea070001d5040b0b074404050300d005658505800101c00d900607030b0f8460440800c00468100c14080291000d109840c2e41e1040d0107241c00300c0c28020640d520781c0d01403540d050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 250027500 1250 250026250 250026277
    0x10608010911013009050c04050a1a03030315090403020a050d05040e0a090c06050309070305010509070f0602030f0d0c050906030703140c071a100f12030210050c120703060b 76
    0x480c0c0c01c1c59a4032a031014000c804e819601100d080b0520180c14036440c000f842d207010280c44412210034000e0500040d004020040c00602c02e51500c01209401440e540710400c60480d8070400c000420706001050301d01c01c1d0326410080c195000307500c1c1002044c03500104102c003103100d02e002c4040041d40500c410651040640c613516201c50801c5c0b0060003d890061050503542d19041012010030b00500c80300c0c007247e40c1414440d50326200d10103224104031164001403c40e43c00c03c5d0078400300f00e900007400f508840705552021700682d181d10701240c0b07a12401c03400088030001841205081c491952100b410002c05040c05407809961070089005608103c1c0c0c001d02182d550318521205a01004d02e05a2080b80807554500c0c00d0b44540e584506984080703105080001c2240000703402d0754412141d074024081c40044001e1203a512049500e0704880c10800b00e0042c050401d145100e4401c3d070140d20301581508a0080c00e004010030110145100140110105a19000002060f152400c02044581c4c8440b1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 250028750 1250 250027500 250027523
    0x1090603090f231e0712030c061a03010e06010503060606030912090a0306111b07120b04110301020403121d0604030204090312150306060b1e1308150108011b02030a0f020106080109 79
    0x4c807800d04054055106900d01000580e8010002c1d51040e444041c00ea48071000245e1144200361440061130031152240d055132a00c40e15901003070707001410750304a960840c01c40d62603a96460910883d80000c4d220b1001356880a1442c0c041d4540200c0a0140070f00003a1601d00486e650751280420344544001041501d6030020f0039514012351400005011500c480c014103503945008214110b81e401705002070441c02000c00420200022071a40180d1303520020001e64445450f401c0210519060000c9030010071282d41c2c1228004510051440399007a00601650030300389160248005000501c1c0c04400300450b141c41d05810208502c0380761101c8100b078810a1815007107140103021120b441d080003500c0d003802c2c4031360407464068107405128640761b15803003a20b4014803080403e40008640060b0240d0268034074801407250604402d6040314640b40c020322040b8442d0b189010b0505000318980e0058004001c03200159000c0d5802d400b00299074800025615550b552036400c40c1e01000003101c0810b19030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 250030000 1250 250028750 250028803
    0x2719020409050601182102030c060f031e04020d02270411031b1003020a05070c061d100e010e0102150c03090c010801060c030305041104020c070501090603090f23 71
    0xc100048444840c940b0145c259041034145105e0208910100099806003039204003103481c10f01101d09510406401c40e925000b203400344540b150000c8a050180014003e2510b6201c2c0324001010300564001d84258000345441e001d0100b5505024800c605119042000ca165400401400c1e44158050075070514000601c40405061603411300540880c4180c2d0390805956a03a04901c0031540d04550a0050781c0d220001420342c1c140c0154003014000e00d4030725200043c0290041034112241d50704254400203032424104000030300c509180007000044101500c44500e50065140d485d5195050049505169400100484e250012603c4410244010040c4040e444c1c0c00c000c0402c02000c2400c02c07050075810044d00502621a419000e0f08064032100464288001c0c4814500c28620207003066540b03d5840790b046544850b64410140012512200068414824422080e0081c0e210a6003004928a034a13003080b21402c121030707040140480e26003003040c80000c2000c0e081c408150000401418100b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 250031250 1250 250030000 250030007
    0xc01030506031b0d020301140c030403140f09041e0e010e07050103060e04120e1513081f0e0f030c0a0b0108060105130f1116060b2719020409050601 65
    0x141c20903000354840d0701a1005001e20b10340041491009883c4403190300f405000080c090148940030104602101c0d043c403604a503c0c02c001c1d48280d00a40311000882e8420001c2d240038856529024841d035002c2c0310031156850250840c0054000c000d030710700480c50380d039002c00d012100c40d10074000144e035440c611001c007a1401c1c401e0713000404090804105103850300d40c3ca0621060b00070802090184011101180d150154120b4164400003a15179041c00200c0c1041c0c207a1075119030310403d0125620070000582010005080c04903800300801504188a1000303030001504581400624500858240c00e004000c10805010518031031001001001510b0070306d02d241f1001a000900c031900900c00600c200c0c1c460300c010107156a103440c0000760003103100b0114001850b940701c0303c100b01c000004c2d140d00c08040c410405a4014080e540402503042450204003090a0003003996544501c114007184240c8180c4140603400602e007041c80e1526801403a40c142240d2103a0440304a05a41d8418015517591 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 250032500 1250 250031250 250031261
    0x40509010510142508031f080319020307060c0503010e0a0908070f230d09060305061f0c0804091b030902030615010903020901030b07020f0304031110050405030a03020c0103 76
    0x1415103041407490002c0030010326a5010411504400c1e20025450002035000303070b1840140300c41001c02c04851401490483c000354025100e100d00300e0030a0900c000c00a00b58415082100c02c580021442c00140d505191032003041c444400040d40000e01000c00405d280c5d01501d145030a06958055507581040c070703031100b0303040d02400403d07804e40340400b0480000c00d8401112201500003520304810405d900c0d02c02200540e4074501c10050204826580c060074001410600c1d42805445582c480c80d00c404089040301e60031246140c1c80746416082200380301d5104184410980c16292403c4502c0b003580314100070f680568000084c40e40d03150f6410072921141c94001d0b0303020a03d85028000c60569400195071024060248a0549210760341400355a018200070302c01568050000d4171990b035a41411003049004940701d01c058060080781049807800442210b06617035010b41036526441c40e03c028844403480c222180c0080c400c04100100c0c00390b504011081195201e03074020070450005000041c183c40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 250033750 1250 250032500 250032509
    0x60e010905041208070203180406030210080411011b1401060b0a18060c152706060504140f070503060102430f0506030603150117060705040b090d05011d0304050901 72
    0x54132a090055440e4040700300c46841c4950710b00c0100d82c2c0c41d1100007500410007540001d501c4180d5801c0f09403600d4011348501d03c00e41c000e5480819681c40340c0010b41d004080400c600d40c210120300c83c404001340d01060404182e59403a8000104940c507083c40c1c010035800300a0b4080410403903042202a0541d820034103000c1c061a00c0e29040a000d50b03130b07444c0d582245920000129035100c5407000600c82500d070384c1d08600b15404c204171071544503904104004011501035240500e0400400304042300c900400b00340540e141c913001150355980d0000455a40c5c1000e40010304600400000c94085042000f4402c11034407518000c6041c28414407500031a5480c2040300e12080c0c460920030400c042d419003140003103e0040d11496038903902c0340c00082c140b280c00702e220240006140000709a420100000c607072200e90769070450306c007074031062400d41d9240100e204502401904003c5100c04d4100424003c2c2030f01d21400010464510b80004080385503000302c0500982d0348003080401141c03504545503801070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 250035000 1250 250033750 250033757
    0x50c091002061f0b0a050c0c060f0706060801020906071412031905060102060103081b12040e040c0b0f030420040e03190e060d020f1201090c031d061801060e0109050412 74
    0x41d440c194500803540170380a25041480381c0071514545400040c050740703040a1000788155a58482018441d4058002c0300090300e0003840e01d400808c09200510803110360b07810082195081c00150741c0d9408084c0d46260016029000d80795070700080910a81c051405141c5903c8134100400b100b600c44022030b0740080c02d0300e0440d0700103001080410304040888202c07440c0b0309001d042d03410002c2005031910001c00c007420030404001400040010403c480c003402188a01440c00a460f0756860103c414040c00000d070204401c03c002142c0003480c040c03901d1b64031891002025003155507040001c3c0854440c1c610b440615040000c4012001e1030114001c00400e40604100070031130030b10800300e2203a001e62401004650b500003503c5c2c40c0e00d901042912208000782d42c1c070052941e100d03400100541078401204000c2400c1c2401602e1100001180e02070b08408040100030583d1032401e09105168156207003501c0395615100480c4102c0e001c1201400303000c001d4000301d000d060031b1800d8000105104548001c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 250036250 1250 250035000 250035061
    0x3060f090209091f022a070305010608150a0213170d08090d1202160807030203070203060a0504080307031e1a10030e340e040b1513050c09100206 64
    0x4070761350381d41c100a820140d0840141c9800c118a0303c3c6508503202940019070380002c074151154110001001d0301a00d00c02c4009110b0550785030191562070900200e403107221103110000500300c0b2129401703410700d032140345406d02c03500e03960703400030428155050751800103038114400034011150400d10541d0041c224034020030f40c52038501801004801d01d0707145101c9264000840030070b140d4142180041d0b09822601c035a42e01d01075484c000c2c2d6039504c001000c9020b40106000030300b000086110b142d01c525001940e40e4555520f95004078000e00010381c801003010501807061411103241c1c1b04030701d40c0240130f0319400e05000c1d010081009240039800050b040508107006020350103400b203140e8010002d04c030243c8084007000b500790074480c80300b030000e000c03103040080e40090304034501c07a9100d008a010b210080450b403204e042c060300074030b4000c3c60079800c01c030011711040007044540d11071030780603000c1070180741400364540015034903004c0d1580e20401a4016002d00108004d0021030101400307104130980d07c07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 250037500 1250 250036250 250036273
    0x9020918030d0f060b0a0801140f010f1b2307050301020f070f050c09040b0609100302010e061b070b04170105070c1502070c2403060e01120203030403060f09020909 72
    0x16244216404560b00c9501d0707106180c2c9098464029002070800500f8403510344416600060503040d00348100040c004120079151111b0810313514503407103198182d4480c15020007080040d1240241030301100f00300300502003400c0200d80c803001e00d6012030b054208800062030f03507071544514102498109a1081c0d1041010701042c00c405021903140540c84038103003143caa4581070184c02c15035224500c640081420040008201e00d80350b050344604012243e000440c4c03200300344d01e43c20b5011404000d01240e070411004041e490204080c020100ea1414403045980d55180301d0307400c01c29145d020000381c110120701070104522100c031500145014000800c1180b0b0b10300d60040c103044050b1030141008001c4514814205034940480c1d01e6650041401d110305a560060301426415075140d004200003508030030007040d80301c1d0040901700d070002c1a1441c2540d092200603004841010401ca1b03052000700000030002d01d00c2e00404001000034880001d038402c19005103c40e40740001d0000010390000c404010303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 250038750 1250 250037500 250037503
    0x302030c0708120315180906010501030e0f1f0207051c08010b0316030203181b0109050a0e0604021612030606090b0a170403020f0a1b170d1b06060909020918 69
    0x5c0c0c1c00365100f03521a03140e400d00e01c0400c10712076045078640114000c0341d04000074441d00080e014100d031421b0340e00b0044940c20540301500d40441e075803101e80340e8200d001910b182156412803a007544107243d200514008255076072500e444184182c189020100407855a94540c114042500420784e0511305451441c204036802800740c4058551814143e0220104466000300c092000d24000000c0880e10341803424120600402032040040e400101c8100c0b000c1810f0500d814203808a5291940c084500d071115401c100107500710400003102c280041c00f80002103100ca100e10000c0c8400380e1000140c482c20b03c007008100400b0340c0c2114400800c20031607045000e0380034a8901024606540c805203075120707840c0490504111243c4120f02d4841c2c02803241c1440f218980312494080007141c1c10901c181c0e0341f049003845060000380840280c1001c8100300c2218000d110001000c00b50301c0500c101013989540383e0b01180d100f41c00c449001076580750060304504080300a960416103e18580741e80e072400700c9026 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 250040000 1250 250038750 250038757
    0x40302070b0711120102032a090d150603080307080a020909271002040608130c1802130605030a0b01090f1403010902030f060f15060301061d0d0302030c070812 70
    0x102201e000018040c81803060740340744001902d000804000c0c031207041080700c1d03010f90010340b8448a0741c40c1400100a140400d4488805d094066592190900c2c858008000c60131803144001c2c1e9034a190750940078a01802c43c49481c2c061072198064a0701c9081c002001071068900403da1000c10384100301c07032180c95a850008950100c00401000141500090200e00c01d41c41460b1000d11440b46c84058821011242c003d00242d0343c0c0c1b40c0e0b07500a50b44d43c05c203000f18407000c3c50714050a000821101032140d6032540c3d044054104420102504d0105024600c0d0b80b1000e4940c000000540301109108841106003d158880b40d0246014106036080c03502080284980344a8404041c242c8641e103080b9440a400c02640f00d034004050311640410031030501d84407142140c070114034840d03c400142c02031a03564030032000b2500192100313085a00f480e00c25034001d01007004045e00d00c07550704100c0075196600300451616a2080e0301540c0c640f031120141c00d1410b4420f8004079210740001016050405454054 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 250041250 1250 250040000 250040009
    0xc0702091503030d06080318190308070201141204030e060a0e040b120a0b0103170301210201050c0a0c06030e0f19060209090406020403020a09090f111918060e04030207 74
    0x9607021031038110000703440c40c0f0074040121140760038210005038550010000e010800c5442002c5400000d0800800001d240d442d1802c105d03405494000303002040c10440540b420780d2040c141004103408101e5004403a802c00c1030012a2a440d58081100700755100188001d0900c043c1c40340c6003071050044000e40100142c444c0940900e548058190090740d51821030700c01c0c1c12024040e070304000210b00340044045403d0000340c038541510721244840000fa00f048a048030309070381144110b00700b86001c0399031040126001341c0c10803600703226003004c0032030501490821a1140301d840f44050b01d007040103420b8505103100c240c0366400c0490000f543c60030100b11040d5881e45180c0a50695040386010302c02070190120031900040844204020098181d00a0091b0b90088443c4205650f44484903402c2d126046002480b004548515000007a40c050f901d800010000700400391408800360001c075041815408050300c22103001101036940428402c140c050403a40d14107034524902a02c0c060750380c030038510a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 250042500 1250 250041250 250041271
    0xb0714011404081306141b1908120912160201031104092301061b0611040b030a0e0318010e2d13050103080a0f0509030105010906031e021f0203040302060a03140c070209 74
    0x1040342141c40103102054240b48c0200117504c01e46071a04000c0300c590840b0580035400104140031907080303c8001071007204400303440c03c954500002512001041404a442203040c5a161155180000150005000509400d0b8000908000c04802180391503983e94801c00f200c1e41c17042d00510040740d001e000a48842030070207242610b00e1a92034074400908120440c07642c5e011000c2000f082c1141080c0086000e8080120180110a00248460b84030701ca04c00218520341d680c0c030302c615440c2d4099040700a9611006010222012072004019024a044a0b030074000ca8614594401185085414030251228185041100c0d40c1140c2d1a00f80d540304100c0500b090228100240150a22075411100c0c40d54015000740440d580d05c2041a0140109000481e0a8056002c0050a201e07007110120003041d00240b51b0003410609118604803004034244075001c6000401c000b00258550b00300a024600069400285500c5d0300c40600c2090f9501421280c00c2030303420041034015941d20070055803c190a5036 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 250043750 1250 250042500 250042537
    0xf040809010e0d021002010507080901020f0a1d090a0b041109030705040506131e0609181103010212040b0405240c090a080d09080105060a0b071401140408130614 71
    0x4001054500000f000075407141d05402c10b2108281d06421a81c050210b0f511440c03e641c443d800e109003030303020311304404012900034084424128821212003000031022800e1341d03801801000801d0345030400b20b800b95051503e038281c082c018201072103100500f025801100b0b060600e0900080d440d61480c0c03241e9807043d91070300302040190f66081d074804612410000f040244038500300303003014a11214002c1c1215546052000540d4400c5c81c0034407407423822200160029090941d4413092000e1035171080c290190750a10440d00d85d02c105082035801107003c0d054003411494640b50203403400080700c00402400b11100e007003180c3c280ca04610f00f0303007103c0001d030003944808515020030140e04050788a0b51980c450700044081c9103410440004c181c940e1a00280b006079151018824540700f00d224081f103901d401c01040700841c00b0b2000b07900705840078400100302000b03200100e0869010540d41500c0c16074001074060065900002460010700060400d5046281d075081c80c40c409020b40c2006501041048 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 250045000 1250 250043750 250043777
    0x3190314120f24090f071704030309020316050d03140d06080705030c01090810091e0b091c0230190e0906061602120105131a09062a041401080f04080901 67
    0x391507409108031007c4000140d4545420020054103240380c040c0e019020308482d0b480b50b2105001524107480c40a4904d807141101c641d01261181c1a201060514510901501d4551221405003400030000301000b04035150a000401d0704051262903024140b0850440070010170760007042d227181601d860756001500741214200400c0401c031003005810400d8a004c048420090360550035401f032403204007215140c01d6529444000b0004c1c0c00b1001300580c2c414072a0203070350040e00555007032200700712420300210725030600360350995001501c001021400019400d1000f581c040711f0010300190442c1c0d908018106840824000e202e00c19503070484420f0050301c4010764955003d11400360034110020021803924400d80390040780240d80440386c1501c04203488490000c0c034010356004004040c040c041a0b202c50071038820b450349292015621441a411110070084000c2c00b4200601d0460b03280c0100082c0800014250140181801074800120040c040800c1065003980d0540c0300a003481d0180000d207 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 250046250 1250 250045000 250045007
    0x50a0e13140303010b030a0f05010e0613201b12090d03030b03070f09140108100203090a1e030816021f0212010b130503190314120f24090f07 62
    0x480c4415441e5220000001a544040400a520420040e5003c0100415103a4101c040c1c600038800c0034294900740020071701a02d09903146200150b907001000030003080c0001c4200a03540c040011010604003c241070fa24108100d44242e019003143c001380c40c0214007400054114060f03910514080d1851030240410980280d00a03101c040b0010125401181e42c0c100402c081000c0d0f0140e044882e05000180042c04500a6480e040e9940c3c480034110100440003144001d4000602c0110346200700480803012071000c0b8051400c1100340035403000d142c083c500f0046c0401c0000741151130880a003504018940d40c0c0800c41080920607031a28401c01401125840b0190007500c00843d200440d800000034116400350040c1807481004c2c40d0042419035980402d40c40d070b0f0030048402d841000303400020740028815407500284842c1d01c88000d040c0f40c09100c00380340380700c42103034448120103500041c402009501144090040d903100300c1c0c02c0801c40d00d00c02180d617407207024050b6860788001e58040341c5580d00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 250047500 1250 250046250 250046273
    0x80c0c0a11040e010f0b01020106050a0e01090908070210020303070216030809011107090c0302041e05010903080309030f0d090203010e0c030a1e0503190905010e0a061b020303030a060807050a0e13 86
    0x80f100c024032800620414a10090003040c0440c0e0166183c480001980e09000710511304070f4007684c0203000107030700c0c00b165200030306900d1070201c071000c2c400c022032001a03031400a680704042d001d50041d52a46001302d8007074030300f03044564044403a071346a040400006002d03104564030800e081c03812846070f0308591101c620b81030864008411440c1000440080c207541070303015108031680040034818403858110300e03904d100540d01500d80050300d54403041c004989880000c0d60040c0103907048910b40406602c0307500300741e004060b00c0040640c0382c44154065280900500214207200b20203070a842c1c07080c000081e940c4070020741c01800c0c0e8a4484801e172840721a12042e200c42ca0f0000c003076a41d1940f038201c45034104800f0b48021004100d40e160702003a030354400d00c21041c94640107401a44150b0a00c0d20950302140d402008480031004c2a003440c0c0180c409001860060f5655103010a0460400c00e07000e06010300307500100d00900c46583c0800005241d4ac1c041c0e5001104091000c10109180c00c00007450328 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 250048750 1250 250047500 250047521
    0x4090b19181b180b0306030a0f0816031e02010506130b010309080a0c0308070305010810050628050a0b031003110a08060115030e1b040c031503050a03080c0c0a1104 72
    0xb00c42e9000030703150300281000405558401141030141c0c641e0159103040c00306480d0300380c1540c001200781c000601d00c642d0b040c10040c06640442d003410500203808c1240029880124005a480c40b00da500390064203030f40c490004c080740000c2c0310f0fa2510b88045140240300700c41c554000b0380c071a485801264001d5100c107203082c2c3c02407074580c2e5511005201400d290304040044000440c2800000c1c0064403c4c81154140c4098030050540d081c060404a0068071024001c0c0d13034042c03a03410012002040012008100c030148404c18003500d8642000c11201c91000e91001544a0b000c0ac200f1600200405440d03065030fa00c5246454100103210125043d0007594200180c0c1d84510f10011402e00364907400c02042d01d03010307075007444400c0314030b1a425100c40420212503405e2942010444451038990030070300d04284103160005081c9250548400074071016130041e50aa0020030ba50003e15520441c0d00384d1251858600c40d1400701d05420580e503a0041c0035010389000d044400300c3c0703d03d6649801107403242 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 250050000 1250 250048750 250048781
    0x601140f070b0f06100903020d030915030605030f071d1509040b0f10030203030724021209160509070507030e0607050d02070501140a0810030503030c04090b1918 71
    0x1c030458542a0700300601a1008031600002d000054214902484410380b120600e540f4a141135245500344103c642c4408800c805010802d04085891604490320074498043d56501140c1181b07080c0501d400c01001003400f400c640c100714000c2c403100010b481c0500012400c03007221402541d0303000ca10740350014114805a4000c00074002c2c80300340b01e4190300f42401400c0c580803280300b5443c0c040d20201e0000c042e1100a41603002404400081822400403c030b46200003a541000740105150303203000c9a010403102c2104018500a01c10707109410050355080041c0120304104182c24000092040c0400030200c10800200044030420544600107500c100d10014040e103231115094034140e502c8801c040421303801842481070000740d541c171420082101001da5a400e030700e41211032104a4200400400d0420204011030700000010000c00056105e000302c2c24010361654140609001502c0103103e01503c55000c52047d65400702001103481c3c215480080d40b072902120090a60f400307009450100040f1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 250051250 1250 250050000 250050007
    0x20a0819050706020a030804030c05010908030a06031b141201150f05010206161218120201050f1602030301210c0e01061202070c060503180607030204060f0806090601140f 75
    0x61104100540d000361140042e03610700c43c0c40c1d50b0120307500c09070102c02800203001c0b80081004207001d180b98058060044001042e0200581c80d0031040354010780740706c54030a0b0707213203820001d100c03c0013000c2d001305800070b564040c4140340000c16400a00d020030814072404031440c8003640c5a8095000745074002c00041d4155800d59a030b141410100c00074812580907010300e0000400500d801d800501c21622552118800010303901c415200400360285912030100003464518081441143c4a050820341640085136528003203e011140e14400350000010040e0507803000742d010f40101c140d0b07040d01c06040411110b000c9840007848001c1c060140900090080003003c0f600004403e03105058491549500d005070131102503850407071065480c0584814100007040c0882d0348521300450308010304181207a007810035840390500702042658010f01281d4005404c00400b600007801d40505009820161000d10300720300420b811030001004035042080d0b801e24410f0701c20743d01003500e003515620107442e038a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 250052500 1250 250051250 250051273
    0x1409180f010618021c0f020904050c0d060b030c12190c0905040b0f06040504110f04080f0d030507271e0317030c070803152e020318010c020a08 63
    0xb00318501621601d84121468141201c020b4000c80d4813007100300e4003140c80c590004500c900104012014014102d80030040d40c142669980201c0340280790304814247c1d5852150341040845106602c680403030b010070300410035043c12007001c0e69014107440800301d41c103690308905441e01c0071a4a140c03101441c07800c2455954564000508410b0362403d540030449004000c042000061320403850703541c0400c0030401880582026046004160703c81801c2c0e600b00f0125082c5050b964006420112103036006120220800c40c0030031000d0b43e050701e5418100800d0800038030051a160900300007a85500c0c98001c0305980c1c410030390888000300b00818084005035030100b00070040625a20058610449500100c040385145004803400382803004070301ca1416840350380380f01c080c5e0801001c0721641d80211820a080e07403107a5071440d8841100e502c0c07040c41c83d0b0131040c0b07055038850480b17840c0c000c5505c10701c2104e030400380340c04018005143c00d003860340d4080d40610000344240d6283d0005074160244250b07049 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 250053750 1250 250052500 250052503
    0x50105010f02030f0a0903141c14071502070206072009040b01030609050c060309030a1e02060103150902060712170601081909050115030c17062205010507050d0b0a1409180f 76
    0x307449c0704901c8662001c1e102149411222002d18409203603000381d042082da0000b41040c1c010240ca081d18080141c00d0043c180c001070310316040b80c2010740313900040401012040c2d4038900403410ae403000301d4200c2410704054494404600d4140402095141da07000201c040c02010443c000c0c844c0d500a08107580c910307001c0340007620380e0002d854000109500d41251000d003070b1600d0303560b0030381c0e90294014040ca03072075034640d1500c51100903a11420300d59241c00f18005610ad050007044c8060246802c40490401d0740c4005140c41d030200d8400f1850780511003400f0640c0c0c3d0080c03c80750031031032010303012964540d6060403000401142d0f10082c990341c0303402052080003c600c841c2c5402c49010b40009941c46a0f680349004590000c1c0c070031070748150080b100003007440c000c0301a00f208061000031041e030901301d540c1e900c030308480c1c06640d060b012900115400344d03403d2030f0740244040524140c4990340200d2820440641c1a031a144805d441618a000003c0046007015160344c60147e00700201c4425095078540c05 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 250055000 1250 250053750 250053763
    0x11060f07020301110a0e09010b07170f0711090601050c0703020f03030903032106030304182a080a15140f0d0c18051b2704021804050105010f02030f0a090314 69
    0x400714006e81d0705809145040020641200d499020b0103140083daa901c103214448084035480d841c07007080c040c424000e07041c0800342101c648242e007030741251f0000f2000c1016040008003038a041220410003111031a030f01040300011240e0603107440b92104105400a82580201d21919406107c0820705c0b0142d6100c8100f011260030a000024100d44c40380e40031726032648076a009403200504484012020101345074049083c86007070b904030104031940746032010020b80580140304c4c00104180180704509045200d0300c02206081e001800e1105c1c506200d86030310808207403500e4481c24113084102c49644075103a2405003981c2c070004030240d55440750382c18582c0038400f1400010f01480c000001d04d5503a98002c602c00480e842e4180ca40c1055540c0e2440888411011040340845403072601c1b0400ea61035a00242203c024641201d08680d07840400b03000071074205034020350410080a580c00d42141c3c0110441c0c0c809483e03a000c0503950301c0d212800342c1d54684540d10050000301d204150030150307100031811 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 250056250 1250 250055000 250055017
    0x20c1503060a06050a02030a0e0a030f050105060406150e011419080a0b01030203042d0b1314160b03100f0323010c02060c0c011404060b12010911060f0702030111 71
    0xc0342c07646482d458202d900b030094070060000b40e4010410b211415000f0041401c03161401011a0030540d26940d40d128030f40840700d41210641c1d1544188500391505001d500701500d1801c01040f010742c50701c2c03001030410700c0b101081410300c855040384803003001a9030119108019109001c240c010251140117005e094202d448030051882c203000d0810f40c0d07110307001b107a015541144040c00915020403911298030700c00034203144002410700c2080001011442e2051044601c1403085201c1451400c280604c900007091051040d0407006d1074035481c1100c40003a806481000d16515200e40d42c01c401804a1012900000d8009000d484004100889241d40408a07c9c4030301305441303100b5004421600781c41c141202003026800c0800003981c4544550041c05048180304004652a401103074031041d4010243e4041d108681c075021110303c142060f8813803a003c0c2440c0c0000b0464280240c40e000a00801080914400c0340d0000700210050800b00580d181e254008000f0001c000792241c0b8040d055110301c14 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 250057500 1250 250056250 250056259
    0x402040303020c1c0b060402030c130e07022b08060102030c07120204060509060a09180f08040509010b0c1207021305070e0406050402070506040f02150705100b04020a1707020c150306 80
    0x9690501812808248095079100d17004003440d03142d440030400a034000038242d406015040c0260304002c40704c000014014064090b00c015503052900c0000d040a5180da140d00348005040320030415070340000078088a2038043e28000e509521403a0040303003141305203803101407548118240130800c142c0340c24006504034801c88081008965800620005603011603034a540003000000c10000007420707800c514035500f030810a48800c1003d40e03403480c80c0c1c0b01d850441a13030140d00107e070500440c10030400e170070b0140240102581c24100305251555440d012000080c0b001000850040110748554003080c0e54202850380078080b900e412400201342003600c00f891403003107040c0500050300781071910854803200d0b0810082d00303842c0d549498020090040340001c17030304a014080a420300101c0400074142040c45030015010f4010022a100255940414060722481c0304201c0c0d188102d40011a024001401c410795414030355079500168241201042059080580e80c100d00000c8090400110b20518046070f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 250058750 1250 250057500 250057519
    0x3060c02010c0c020904060c030213030609140a020d030f03020f030f071d0a050d02032e0501050301141906090c030f11040308070813050414010305060610200703020402040303020c 79
    0x4004540f880007600020f50044603c90100e0007107a4030f0341000580d59180c0c140940b810540e00301c01c4101c907100c0d9005884407079490086000f0451040c2e00350720107a00800060031281540c2c0c0000e081301c51285401001d0020130ac1c6440385460091b01555118006400300680342d00e05420500c07000711085454400160002d0305130ba00d154541140c20244403405401d18003054204410320040d006502800e0b60b040c0f180591440e61032001d00c000c040d411905070a18000e6001c0031201200b0781e04180c005512036410607001e000181912202240e00c00481c840d4100011000311ba80b100401c1c454020b911007504200b0b4506810750160418002c0c00c0141c00c08110b101c8204141031041d00440c00020300d0603d04110342d0340841c45110203004040103c400201c1c0380fa40e00e1002908560440101412010a80c0c0040051000034040d41d6400342c070a80d0401091500000c0040c926010030341c003050000c4000f42d808200350380400420019540c003500c11507880380c0f2800d019541e4450280420700c140c8100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 250060000 1250 250058750 250058771
    0x203070801050126010b0f041707030c08060408030a0903030e0708030a110f0601170f150f0c121f030218100b040b04050609010e0918071a030a0e030c060103060c0201 73
    0x70013540812145070601400d1603424400f078040c9581c80b00c02c04554080c0d06010216240c3c61141e40e010540b03621000400d019495441c1080014001c0c0c1d01240d0a50440d80402c0007242103d0b0403250710080f840f10024002185141c00d900412160b89052140d1185c840041240f0f00e0000081404010035101c194504030344401c040e84c4c031107034006485e2154001c60010008141089000c2c407408040300c0544540c01c4900300f40700d1501ea88840107500380b81002081c0084403524a14a81e00304a629044501d885200d1802c4030351158041d1650b00503401e2015141c0c5208100c00081029640c0209040d04603034210130a11561201699003c0d501c040340400010704e880d1420481c0c040350100350069003442c1ca44010455513400000116050140c0d140c40350b901641d849000c2c0d031290000040c6502c0c020107003d540340c80d05955421030709481c02236500c180c1c900c3d135120007925400954554003145922891060768154010760341c00c42114071600e0004020840c090b00184460691a0b000b0001e00307000703 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 250061250 1250 250060000 250060037
    0x41e031d0a0305150c0f030c0418020a0c0b0603100e0606030d080f1b0409020f0d0b0108070e121c090e0702071a0d0b0616031206030515040f020402030708010501 71
    0x4510004042da4498481c00d200142c1000704950700007025820301e030405006c8106081541e200301c4012075070384030008052106807000920a1501502100c046050511802c40a0050884108007400c0c940e400000209156030410050701c202c4840101070000c10b8003618001d075242e20540ba070600c00e025806e100603d480c0700780c8140344164900014070f02d013512500c00e001c2510f41d1400248074076000801020500e41c1d290300050a5408880d5945540c034030701100301404689039800018100301c640310034014070030750282c80c26801d10b0302100c04c1030446440034611442e2008103000d0b414040b0505207030340401604082c1003070840b0484400c07070140d581e8040080341c49070300e0346c046c0c5034001344911170002000d40004003038004900f08003400100301851800160300da801020740d500c00441811400820103138480305004c04001401002d00c42642103030343c0c807038880d42c1c030000c3d004110544400007002d010080703d000b098a038000e801190b070f80c2000b01c4000c011801c03d00607075008c24070000103a00b0b055030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 250062500 1250 250061250 250061269
    0x8030d11030c030c03070327031101050603060610020703020310060e16020a20090901050a060803190807021e01050f010806040f02010e0f1206070f0c0305070b041e031d 74
    0x2e0910105140d5510715609030b01640014100c034007015070314418000c903080c41c10710110740400d5200321140440c8039840c00070b02e040031503070001d903091b410f00041c007034542c0380090080d4200500700c0c1ea6541080c10746c4402ca207000c030303a9440a5494030a141b005c6c484407610394446425a41c060081986a55400c3c0160309102c15440620300142d1103441840041044888121081c544140c02220300303003035120019010b000c0075100320140341d5442050002c41006c0c0e00c030b4080241040e102550405445016603001420318482401c00d02840d40001151148203118450880c13000c4500e425050f0189043e0600a1070211a0140700510344400480c640d0b000145d201c0c40345521480301450240035500454130380c4100d06450b9042400c044003030502c0e030b0310058070601c0424101c00038409480c0100000301030307698166045c814840140010004240e12000300c4601641004411503e6169858802221102103005010300380c003803078001342010741c4110044860780145220104903229041080311480 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 250063750 1250 250062500 250062511
    0xa0203040302041e020304030806030f150109020711090108070821030a0f0f18110a0320010909141603110d2a020a0b010e010315051f08030d1103 64
    0x2801444104014907041d0400e054540030740301d100c040e400001c5012826600107490072000b15035010208906400c00b00000710000c070141e0004c040000141c804016002010702840c0ad10303e800086050501025071070201306410b0250090301c03d50307942c160483d168000c07806500d0450080b12590640e4a1140d0403800d070500001c5c2140b031641c0c84837030440b00102038420341c0540b0301c0d03102c0051404c0012148a000380740341c00a010700c1418082c5203007c42c3c1d541942081503100c1e5080480c10320104a0301402c500d02c8041401c0000c1800e003941c40140c0303854815a014a0003e4201811748030f60300641c082060040844101da04202810040c05074203450001e600b401a00109011a81c0c00c60384035003028a2003004890f40c122094025407240c3c0f814807030003030400b0140e444515802d04003d11170111500420002c01c08200740d5040d55500903000c0c1c1c0300041220b400e500d80000c19650a031840d03008000c520560a604040e617515000300b926900301c0719078105884c0c40c01401e044003076510b070102d91050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 250065000 1250 250063750 250063753
    0x801060e06010c020a151d041a1903080f071401060302130f06030f11030d020613020d050f010510080c1206040b1008010204060201020319141816090203100602030a02 73
    0x96484000450319560000d0f03060768003030500f403000140c00840c1d0189450078181c2d50368003200c060180c16899000400382d45000d00491412855054600b0301c642d213030943c280c007120b01344460020001c2102800065410290000c0400100e10540003080e200400025215001e07c0e1960306002121038220740041c84040d420031b20070b07039410100011941c45802005407800f80003510503103d0322030000b001c00c900e5080310300d000049402e0702246010005400c01c52900e10040c5014071340400349056031441154003d008152000450301000000c1c0701030082039207200020003141c03402000308001e080d0240720703445450241e141850681d0030b10a10448000002900501268845581d12051040d004007281c0500c03001d42004030300d8007400c2c00200010f200a5001680301d050160843d1340e20b21043c02d0440caa54902000d00000078a040c10141d4000043c0b40044801c9074096016400c08208203a107882c00440c030b0801140c0c07002c103039001d540214409098072102c0d43c1c54900c00d030303520304c110440400235 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 250066250 1250 250065000 250065029
    0xc060c15050a021b07030302390607021e01030606050a020a080c0a08040303170a09022202090a030f05120301030b0a05060103090f03030f14060604180219080907080106 74
    0x10000c80d40c004a41040e04800014908614410440400310400640342c00e642c10850040043c140c0c108904c0f81440c1403411710700382c015010000c889030303a480d01c840703103a950f0101026501d0556640d015202e00700d801a2062114810142030100d07070f00c400545e032174007192030103d0102d1018411403e60302d805240c2d030020407000c01a0707140ca5070340da0070031190007105100d20070400d40082c0e248005040114400d4071000710b814034005002d283c844004100c88401854a07020101681c2c0d0345250301401202c0171958110f0001034000342002c1c4c41000740c4507401c148044c000208002440f54081d2203039008800744c490081e06800504400c1c842072102400e0400700341c000c05d04d2120a98050754100d0414140050b000a20b070740c03908045201150241c000c0b81d66281c024202116030f01681d162203010b4a840c8116180500015045015601452000d0034410180d241c100f480c0d070b030403940c0c13400380400040c489010b040c01c010280102118010b0860081e24000165548140211401e455000c0e122030714 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 250067500 1250 250066250 250066283
    0x1170610051806121906050106020102090a12330b0402070809101e0f0206090c0105030a0216050a06020417030313020f011e02030a0e0102070302090a0e070e0a05040c060c 75
    0x200001410b09a4801c60351803c0030f1800300c1c100f11728152400314500c21070314298281007040807110140d02650542e40100300042590303949810000c10360f00d80c610586034200d158280180e034141200311201880c0b54405078644010180700e03203003035001c035800070620607194104203000a80c000c580b402400c41d01c09020040c590b240103c09500c01c4402441c1242600850840b583c42c23408424442e540841c00314030f2240b2101d5418001e096000581070024002c1030034140001f801031000510380030100d9400f160030709403c820030840c80110340c1c10000310b81040b02d550030610000d500500c502d4800102c2c0300c20521f550b1001000f0341c3c0c804c1418111003190038065800b40543d846a52021b01c0c10032610484420301072042c04414141c2e14402d40c000c4da00ca82c02c00d0000350001c0601c40c119419940b08000c204016500c01003010b5019020b18030120780c02c068150a0307440c150f00c4da0441c5604000e684d082288040d05680002d00c030300d014489a5400700e0380d448082d20800002c02025015441480c03d4a8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 250068750 1250 250067500 250067539
    0x150e030c161d06130c09060809060405060c1303050a0c06020d08040c03030c15150311010c0c140d120206040b060a29040801060608040506011e0303030c030b06030117061005 76
    0x41e0303c0407001c3e1207003c0310f0307001e00c00407400c0740c070b030800058040f03555090305208669104000c168170a071940c0080a050909465280e500c01000703081c040c08240000b101d01403201b10200304c00055a01000b1200441c00703500d06080607501c0c3c0e0151200600c0313118043c150003481610b0880c0240c1d003200384200c0250a6460031961950350b22401c0e1548107440016140c0015180b01d00070031626903115800c8640c1c11803904000c0c1e0103881400c1c0c1c0c104a41e0210300c0021440c581100070881d114074078440200100100800c040c2d5040000c050030ba00c010700e020720b4010b50080b8415115030700c1118007030b115030740c0c038820001d080300107024a0301080c4e1400d222402099884404040c20750b0350780f4102e07007402d1f543c0d0307440c0b420345620f90001740c009a100e20070700007005402c0000720b014003550380030881200e002a901000780d185501c409410141c56420b9203000c6806503210185c80030340548041d69a40c1c549280071101030507064400790510688001940c2400d41d244003100340c81000b003032244284280d00300708 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 250070000 1250 250068750 250068809
    0x17121602040603080313020924090411030f0714010915030b0a150309110301090201141b03030c07030f02061506070618060c1713020d150e030c16 64
    0x890300642e81e0b51021001c40e12110155200c1d40c00b480c480c11120300b0504c18020a00c4010b0154009010401c4c4401c0c900701511900d8003840b2030644000f00c49568608240440c4c0c2186426103805002d0620b2003016424082050400d850314251684296200740700115801c0000744207082c2c4038041c500c0c0103c502d504c2a00140c01680340182500091134441c0840c00c00341c075100940e01e001c640c0e24400c06c0100700b010b0300703005200764040300208055040b64001824074501800680c1441000207445246038089200840003008440e0480c1c0d12441c12040300003207a400f2000035030100d18501c100811700d41c400a00c4e24420101181d480316610b01080502c601c03a00309007412903070305031220409a103541805c0c5023100c041340120404a08034141040182c600e400c6003400890b40400c0008010030f40e0000c440700449640d05881c58600220503042c1000c502010000403041a41030484a112050300000940f1088200100742c41e100380009000c00a440d049200d10f41c90000805200503010700c580004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 250071250 1250 250070000 250070003
    0x209091e0714190c1a100603020306060a0807120c020604021f12150b0339040e040326010302130c080a020708090d060f0c0302030906160207050a090204171216 70
    0x40790004c18944c2d64a141800010f0451002c0592004108404440c43c0c4210001c1086040440c03440c00d240010500502c1009200014001c48001050116105080003d01c50591003410804081d040300c000307440b402d0560f4164466580c602c2d1100d008030700b91711401c45060b05502c03803649414a510400f800b900c4075001c071481071410400009408248480158401c85c982c0d4000c49410341c4041d034a020b40e11452191556002502180007850012002200c007a80d022221400d4141d4070703454100d401064003100d4000070206440e8080c01440003044041c1a40c4c0300701c88108100362091640022a02001414000207042d003011410868240c2d0082140307500642d15689410003400214000c4c82c0600c40890b0810360f562042d840306c5503e4070500320401c085107401d51840c185100c145076a403038007406450445592034403848050380204a0080100000b80501c04038030307616030901000350001c0c85132580000c02000d8102d0768150109112400410b0016240d0401d400c0d81d64160007804400340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 250072500 1250 250071250 250071257
    0x806040c110703050102030a050907050a0303030203060d02150a030507020115060507081306111015031103010f060603020901030b180103030513080a080702030d09140f0102010209091e071419 84
    0x1110041d16040c00a0406140510000340c0e82e070501100c00d4044a10050488035943c10490052009a40300079080c0e045035003500c0d0160b100d07150800082c60000b11740100a40c01300c0b41c8074505d502c1c402c020029000c040001c0d10100110365a004082e0300362840e00340031506c075585841e0140300880c007403009419014000c001e8142040085051114510401d80010300400c084400344038034040204080d4030715468000c4144004580078414041c0c5500c01d00000f485c041343e402d0001110b03202540103181031000b0050a010040c1d5541010380291301c25004c01c1d00082c1441400c02d518100056804c880f030310f00100100a0382c4c6192001c075100d81041c0d1000d41000f04418000032403003000c10100350760700c1c0a0402c41e039a5491610405240c1a80c039a4180103019150301c0820844840c0980034848480031750302c1c2d00c031700005100103c0c0244598401280d00542a0040c04640301c0c0030095104454500c010021564440d5142502d8998103440f020106c0003003000441103d40384614010010b821904 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 250073750 1250 250072500 250072517
    0x3020a0501050106082502030414030a0f0606090e010b0d0201051606093903060b03030c0615040b032107060605030a1a1003020d080a050f03090309100f0806040c 71
    0x649a81c02d441e800c2e44071100081e540d20602c21658003070b4540c1d0060810301b011500c846070450340041d45900841c800c4100d4041400110482c40e14140141005250f100e40c3c5250f629a0170f01c1c048000b090680949481146444a0640c0e0301c00140700e40714a422008045040800c61135004440d1540403014268244c18640c084000094060040c1c1200b2440365254002e44480340768480c01c07200341c06414500b1049510044062100110b01d09401d86c0d030006400710340158982c000c240745120384085243d062281c80d0402c0740452200400e0038071104119400c0c4820f1800303004250792004841d69211200e43c00e1050003084613546002000294810f50700031501c1644c03900000d00b40442100305132050116030340c0c1c142882c503108070303c01c2d4081d90140702d82d012a03042d41c0100340c0805000c84014540e120008141e81d6960090702900c40255500d444c00f5a00d250005802d40c9981103512000d008240d50001009481d001c0c2c8000c01c2d01e42103a54800035159280c804110140c145a880e5005001528 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 250075000 1250 250073750 250073753
    0x31b030203030a05030415091a0c040f0b13060302030402090f0a090816020f040509100f1820010e1c0f0b0c07020913050604030f05090409061b08010b03010b0703020a 73
    0x2e102426003004a0345800d0385a00d81800d060061003040360400e02021324001e280f0b0b0000f10329890b06540e600054036030844607500c41888510600c965001900b003900c40f0400000c600102e840140900100ca100340341200303a0b101e005034141e0006481c020350100d8034400061124112000d0103501c1007482c1300100d90010f60f5144c00040f40d01810848602c106c40800c00429401d00320f100c42039001064400300f002e8030b441a1145c2d02c42942e07a03090b026094a4581c0703062111b41e43e4022516540c484c0148000300c031143d28042201c03488a1800b040d00880300c42c00900c10390b0003288d1110507010013528052480b240e900e0f900510415540d012114002c002c54a0030200d0707503210007070b48500d4103580c2096030b40b4401d0040105004006117810b044c0314203035401c40d001a40200d900d03604603174141025866406c400e00b090b50b190080c21400e075001841d040d801003c0c0851a0020480d5503000210480740c05920074040750a14001d0003525005201000100034800c203600051a001d4002d00c10741b0180c0007107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 250076250 1250 250075000 250075003
    0x41b08091212010509160807051b120301050102070e0c0301030201050702190603381c1a0403170601141804090c0311030d02061521010e0c0102120301031b030203 71
    0x214030301100010b41c020040c40749041c0a1266504601404c50403254080c1d40c00b801080010300518001c200100810b80404088a148400390285c01c00f505580404c0c0319007030b00c540c15400900c00c0b2801032150312800500c1c0d99200b09101c0c001c0c2201d004840c41c40e030840c1c0056175140c3c010b800407600800c9032480900148480b40500c00901529038011401c464040040e1011075000040794070400348040c641005092415001c001403003080d140d1108100119010210400516401a184120541d07104408400c1044040d00ca98806c2d205c40c10b4005240e01e030012504000c507009400720301090120001c0b404200040c00620003541c58103403035407000f44040fa0590741c98010458213041c07846804d0040000075142da070017040c0c00350010a00c1c03422982d40250380302000707020741c01d0ba004816100103403034503005118004603080d192500b08000d40d0200441c003c0800c0d1031500303064011401c3c0c403502c561000ca0b6016640d070113401703942e040d6401e64a0305920311034060180109000b1000c070000068a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 250077500 1250 250076250 250076257
    0x8070c080c060a0b0103060b03240925080402030307170d0c05040311010302161124180f21160e07030609020f03010306020306031006150905041b080912 67
    0x4040300940040c0c1400450f010540d0040307058681810b00703003501888280f8800b825680e02c0041112025500700210039583c2d50045086000c0750081404c03804c111010309400803049241090a41d02e05041c41c03030030000c4510400640e8000e601d904200810004a110b02c9440030050b484400343c00d05d094000140023003154003800c040404100e001c20108140081c0c2d29074400720740e00a007001e5280041190f0f0307240340c90544039401403c110246200b204035444605407040741d42c103406108080d400c0002c14628098001d414032040748020a4590003c03818550310302c2c05a0b0b00003502505464240201042d4903849940002c00d45100320000d00c0600044403200c80020701d155240c008035800c0000005040d41c005812000b003190040204956120014003100e0440b42c02c000c00507140e4a403c0000b90420910705074404000b820030801040c0541c0c1c8011017900c00f51036403500c19603a80d8030f00500c401c0e22071103030804444040302c1c643d0018003802200082d0344040b201e03082d0f403039885606125070349580 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 250078750 1250 250077500 250077517
    0x201050c100e160906080601121a01031a06010e09061e0603070305090601060203090319020f1806040b030109080d0c0504091b030617060c0a09170f010506100f08070c08 74
    0x2e01c0302c0105079800030040c0004000d030482d4078041c801c00d400c01b0501940d0b07140c18070424030080c8645d030044041c030000140300314024006c180d210b815561b413400d1408103859103a8000d040e400344940825480c1d030040c000400f694401038828074113907946030108103080040729240030b490140c000c030303140d600da44e1700c3c00440c8900150f40340001e00f0304200080703929007003058000748103650041042c800c2c40d50340007075190703200141580b5107888074149101241041703400b0400b072900b011a08001c0703000300c0c40b803412061180748250307401c220011010f02050300341d6030035520180c040001003041a000030300903007040702c00611071300307007180b502d5910103800d4112004c140b806900b62102030501100142c0c14040c000c01080340480c404143c102d8260302e240c8910300642240c803640c2d400959081a035005004403070080dc10340c0300c00b180a4482c00c12030798503650001403500e03055103004002900c81c42c08a04102c0d00c080681d071513213440c569085003940c8100014101c07a0a01054450302c4001580c041d00030701c00603 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 250080000 1250 250078750 250078753
    0xc0c02030d051806041203080f04031e03060b0c0a11030c0109030b061807030c02060115120507090b040e04050105061210020307020312090d0f051c110d090b071103090109030201050c100e 82
    0x3001b203040040c41132402a0845141044035001d000200e41d024070600113101c020301a25451266903141036004200551056520300d1340070131341106d28a00420b0107290756000b1101c9031000c4504034200f649804101110b107010485440040c4081205801819400a0701038131000198000b036001c40c1ca42c03031046503924000380c0c950812002c0345030b043c80000d00401224007202d80c00c907800c00001c0d04102920402040081c0d440d000281020301c21fa60800c000d10f6108a100d03540c1d80c54182c1030850020440d0300356025030070076002c100e6030300300100029400315401c0d020b8680755082452080c043d41c409400041141300a1050b406541c5048102600844c01000207103c0000d03265000350100b1943c42c1042c0900c203061082c0550b84101da01e08003140d00f020280060580c00b050081d4007240201034800910b18a0002590300b040b40c03103000300d40100100c0d16035040041101b0000342d940e02c180d4000c94006401d4000810055002e20040c0c45445400c00545913094540501c250071500150143c402a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 250081250 1250 250080000 250080029
    0x29060303040b0f1e1b1b0f0109410a170a0213020a020606010e0f01030c0c0602030903250f020f040902030d031b0302040e15031c03060302040c0c02030d05180604 71
    0x1092034031044005d12020220103031400c0141d1a80000c54951105020781c00b50040e1003112400740e10030f081800144c0503c662180202c1d201c0340404140300e120741c11a5003070b000d0301030030503040304000d0700c101c00709000c02442601d599090110290003000b0058030030006104001500f00181d403802c030341c510072400c41c6400588401c00039400174a13218010381642d06000c00e54000c080c980d110740804510a407004c0c24049042c807020501110940001c0d400542080d1022003030113580d080100003080c5505c04e0119082019088200e0001212041c1100a12000000b080c40d001030805074800c028060340280002356104854010906000a600041000030743d14000c011519a4000f13441025011034030b001c60130141032040d0611407510140454485586c1c01d050482d60f84c0d400c008d0000300d220390b685c403a11039074031240c0090007a141c9400102c1c4924144102e4180b0345104013860322545030000c005020358220f0010944e400e5200708a140c40e50001c2607014025500c40d0401040141844040c0d600c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 250082500 1250 250081250 250081267
    0x70204050a0213030206130816050f030f0a03030f0f020a02061f1a031512060118050c030708150a061808060705070b061c29060303040b0f1e 62
    0xc6400041484036079520601580c4242c0310515011425268152001c2c1d683d100e402010010040099005007040c5c442e80400034103145240940c102183d0041e6581ca100000300d104050b220700403040f400c0d000d60f0001e007081c0c9c086482500240b50000505800040d4540c3c8030318100280c0e40b02c400c4000c0564005c000b0f11511054840c000c0c0110502130420a40c03080c2030011404070b000352040d658134419404400301c0c608001d4202d41070020b05000b042e040c100010200295180c0c0000d1280c601a0348a6264011040295004043c4540416018585155101d14040d15000000741c035410b05000c111120403030175155000b50300042e04007078840141e80c0000d081420400000d0360800d116a800030000c0c0440240c01c081616556580700c02c02d5241a501c181c08207100524204600030407100c6401e01c001400082542d0f140c0449406541201d060940e01e00042c1c40c000559a2a80640c401c11003044904511405800203001d01840c161500e508548010f156005401d6200310707000c40060a4070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 250083750 1250 250082500 250082509
    0x91a010e07020d2120072105031603051e0118110c06071202090409030503040203010b101b02030304031226010308030103022b140f0609101e0504080702 67
    0xc0701100a10b403880c004c202da60400701c8903140c06802120102e485030a0860040490902180b030103840c4010143c441c1c0d844e0810001c510f515641d0001d9031703804c441d020030b000c610031001c81e4031a1b41c01840c07100c040c1d51070013822030041c00000e10480302c0c0489106424200644403050354000c0c40c1c5a40c5060710181040e0010045900c206800c01071700c1c4042081206400000c1080c96200321319080c0148002060f520304000791040301c610381c1d8441d02d81118041055003280c09180a9030081e0f00030400c803104101032201110000d102c890219031f804100d45090504081c407206418406400c0e282420307070743e03a10710420251104143c400b0554044030300c21400ca00030303441d0521520305504443c007075140d51290751207440180000380c000e00340c50340f820258410400c3c0c1803041507003003950651511446d003490407902d078000c5a000030501034080d02c041541800644980150b0441c80035001403100080386100404198102c602c02e101122907001c03c0748031612502d07200c0d500a50702140c0d640640e20420 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 250085000 1250 250083750 250083763
    0x3080108011a0a090c09031a04030912051b0d0b040c03110a0e0105041a030312073b0301090506130c17030d0b0a080d12110418091a010e0702 62
    0x201400e0a20101d04441030360348440040c102c80d208100040c21452203e0106c0301d03903c10780c00107001c1e904150201044111140c007201c2c440c84c020b5441c01c42d1070b0703110400103015019030309019109034058501c0f1403241d081c80c2200700c5882c8004011401394105a50b0340c41c00d00c501101d0540d069a804c100420901c294666400120f020484003d1800f5041100c1c400f400751041c01482e00940c3d540a8201ca000c8054413264035000004081700d44800c00350349144481802180d021f40001c80007141240c0540c01030300c240a841001542c1e24000607089030b0b0714442801c003000100c0d4150748500c244030101d0340c00d10845020324140400403a0804650400c0207050141c2c0c1c6c03101400c12402c0700001016140442035402c20b94500c50003256070348601000030000021070708000c100d40107004005207400d402c8a4040d1100d00203401c140035800c0800352020640c00740f8480c0c45039121640030744915403111640540c00e014800c188812041c0c040e45290349103030001340c011000f15501070081c440c540741c042019 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 250086250 1250 250085000 250085021
    0x50a0807090e0c240409050c0a110d0c02060d02070f2018010e0402030f03040609080c0f0d1b0e0a0c030e0106060207120c080f0a03080702070e0c07080d090308010801 73
    0x101482080f1074046804011000d801911124018100074000e032440001c643c001c200c003550602090400600c5404160721209001c1c3c08650006000c401107030000c512440c0340c0100741c450000d1301103103030203001d4558054400c42661076404c1040300000f07400d40e40b0382520b0385c0c00748101074201740490f8030314102032021400382d500c030b1514040511094038440d12a2819a10006403581040d00d03280b01291030000c40e0158503105000104002c1404c0e540001c85400f01c0b2801411a05c04e1380900045c00748400d52a1203040e0850007a01218010031000303000ca5000d4041c0b9210140080c0c0d031202c000306440d4094540110040d111461494284d40c10300442c5006400600200304562820001a5643d43d040c41081c80c08010390980304140507031501c1d030800809030707201a0745d0114921602c1035151084007408a000c240c20201140c1401c1c8001114015030300c1d0407417440d04640320190076280315006940100c4200e030f410405510780c40c2c031900540034001d00c44d8807514029410074204030f00751001c0400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 250087500 1250 250086250 250086253
    0x120a02060c040f0303030903030e100e0d0c080a05071a0c070b0105040209010c06050a0e060c03060907020316112d120c01080402120a0f03090303080105091303080907050a0807090e 79
    0x410f00503400c0c803030008421280e040c240054841010720341a005000c00031070381c08030b134010441c050b030a01e04250000050750040509075007010782201c41c02e60300201080c4c0c0c094100790f0144991a006401640100510782c01580500146480080501c0e005141100c44142c11800890418204081c0c00c003064050401143c0640c100013440c00020155034990350003038125612480401c511200701d500c001005041e00096500c07601d0080c0d69960725502c151011801054010005400c051021054442e61a50420134000c0e4040c03c0c0c980444008441d109168010000d410310907100c5028003050002c07560020355044128881d40c2001202c0000c040d20014507000713261740310841c2c8e9100344010b6100760b04440101840c1302030700891389001c840010003001d00a00900d40c5c01450b80101c0203800b207034401e95405510b6038950092041d400415a020044480383d103410300d002a001c0e900c4141d00003143c0085511a82e5510000303103e05c080b070b81c0014501d07045a14180080c7e2528000c030030340d00d0b20200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 250088750 1250 250087500 250087507
    0x501060906020307020d06020d09081801050703170c190216080316020111101e06060c0b040f050c032d0106270204080d110d0215070e12120a02060c 65
    0xb07910792003900d500a01c40e8214070064420041658150b50780e84502c040c0401c03804e07100e4a40084503921030300c10420700b11250454028039610900072119030551595482c158542c12030b4204d040c011015055000d44e0209202d202c1e0359020300302c0d0324a41c821003a40105581c50a03c807000f501458240c100740c5068000b040410510547c5000b845e102a074286803030150090700d080c00d103003400340c02012840d171f640c00c2591443c0f40d4802c40b213078001c1ba544007070010081e0b550b4440c0144c44a9852400041080d2101ca0002d4081004086800b142c28003860590f00c0c41950040064100141040c9002e900c01403040100c103200c5c0304030501035054900381c00800c007480c1406080d0040b80741c8100c50191013156090740011911064050310018403e100481705800c1100030003500c01d82072981000060301c04d14542d24103003072000402007641709408400c1c0325030f81c462460131a4004022040c86400000200b016024544200188401c000807065550745441036001c0c0281009405000b154001d141031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 250090000 1250 250088750 250088759
    0x203030a09031506030b070c0201021e071806080c06071e0b010f23041104030f0b010e06030a021503070315090e060c030907091a130c1101140411010e130e0105010609 73
    0x480b42c60f87c1040503400d10b4140c10f011440103c1ca0482204840c243e290106990141c40b4040042d010041d20940203903140903500c034008800446110f0300c41c84019910440040e4410300b00503000381507140c0128081d090a20421070f00c0c5400030000031088031240e201034010404c00002e60b144002610103181d20309200c032803004482011401082e80c0c0ca12607944c80c0d42c40904541580100c2c2c0085078880342d51152410070b0b0030260300d007480034400c0c0d41400080400140c1e07a80303004146500080d5005204039100c2007441c10580311604020240000d240d5100582d00d0466842c2d04810000c1583c59004105c401002c480b1034200031000d003030010700801c280144806107901264181c11741e6400080000d01c01c80100d112501121080d07001c42d00240d601c01030310038001e07654009444501484c1c88404141c4880e00c0b4050803100001003500110440401140002d002100f400c8540101450140010710044000426a40b40944219030f9144d031090751400000080c001c4500506090600c3c0d152180740 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 250091250 1250 250090000 250090013
    0x2070c140105041409090304080f010f0f020306010f0c0204150305010e0705010305060a06120b0604060302120c0306240c060f070e010c0201092123010b0d02150a03090203030a0903150603 82
    0x449068814410380700081e25103002001a00c1c001e11182088ac2c0c0804895186c80f0b00a205042400c130805003069411412001c0a0007200c0c0034800c180e5580c001c240321400300b2211a079410404a0f03102c0e480e402d02400c2c0311610b1050002840c052000003a1005a02d070003640380803602e84c0328505143c20141040610780c0e4000100d022200c40d03003826582d40072000d0703449008241d00c4854580c041804100814402d6040c0e002d400c00c4804084001d582e610341e1501c1129500040701c04c20340c0510b00341c1d0b10b81c000303c0c4c0c0c16a0000c98000480705146c2445c02000c501c60130300100721403110045c4442d1041014240d8040d00915a140081c241050300c0c450540008040380102c1c022030140503030510140e01460410640c03900d5590704144102089991600351030750450107804005541d40c20101000c071145005540b55100380e500900c1c1800d140c40596030710005030454106003051580c0c0e900c092015031002d0005003174a003400d50390808000d00b1864840000801101d04040040c034107041400010030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 250092500 1250 250091250 250091279
    0x60108071e03031407030e1f030c031505150418020c1506101b050d050307120e100b1809031309050402010905011407020a180c050f1801030f02070c14010504 69
    0x90b10811161703589080d0806555104035511800e8000c809070942c600c6a0310300c1690205100000e03034050204900d1440124151014400055408000c03036404001d60301e400254611010251880300f410310782d0720211548100e0410f0f275060700007a00040c0500354004113124820024060030f2500805041410129200002d03d162400c03c2c007002d03603a0a011050a1404401001d512004941c02c04982080041c03943d00240c0d540c0b030200305000400c1180c4642d6000351944c0e44610401016020384203462040644120070b20f69400040349401410300390000b01d9080d01c14405a03000b16038412114545080044d80c0d031384422400d61904003400010f0ba0700080da0001c0740d00034640b80a0700019407100b101184550b500096014201190010300c00c0070400345180880ca90040030050b041001000b511035108440030944440c1c8100710f00481d904851002802504040c500000d8122990304850200da0107050160752004000328201302182e05480c15090030354003868258100f501c1d00c12600134905 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 250093750 1250 250092500 250092527
    0xa08030f04030b060d080d09060e01090f08030709080703030c052e0b150a0201050a0e03091011070f060e130608150613090f1101080c03010b0c0708060108071e0303 72
    0x24560f5001c01d0309560b8002582d20401d82000441e40e881c80030690810045c808018111a41070501640444510040c45200016071700060b82015449580d07968070030b03942c801000c0e03a051100021012910007020460080550321039182c2d2440c0c1140c500303000d031030300d807407010221507070701201005a5165192a12505000079080008100424400001070341d00c0c0e1181e9804807107060105100000740d905400283c0100f03910f6038100102210340f100c5030b40f00e100381c0c07a406411520302030207140e0701c500c078114850389003800d00b050300c0109803141c9011051500035840080000e141030342410359071600c100c2c1110454581c032400c00032103103414400307a101d00716040c80c8080c0d1252000002c549450381484905244004d50301080303e10300324606a078407900d29030350589840f00000030000e175650250305190b00a00d02ca001d038a00356880e002d20510664450407030f2030010b0080450000b01c4560801406001c0e01408010f000c0c1c1744d040020511311030095900171603825100300810808a034200b0014281035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 250095000 1250 250093750 250093763
    0x209010903150902031002070c0b07020d080c0c03031c0c020607120f11040801140a0203090a0209092a03010b010c020f060a110304060509040b01080f060f01031e02090a08030f0403 79
    0x101d14070040c00c0042039a00d038042c5d0140200d01d0520348007130345603009084141c850344c0842c40498980d0041402801803080080d00185400c08100104031800c020303102801c48003040303400441da0b042c042401c68000c64101500100d1100319030f030103030347ca600440809070380a20051103503141203035000740400d11944a941c215aa1200c3c4c4465098560300243c070130300b00e61105581d07555901d81e201c50081005525010f0f00140b2440441c1c48405c0700e008582c003880341040103000d04403454003045240c40d00a805001d2034490921514400e0f654105903101030502e225404e860200f0a0041c5425a4840800300e410070100700401c10060307075280d0121440300c4049e80d40c1c0e5184c03088000140d442d88840d92110349070348008140011103d61100062829020a94080c02000c4c0702200640c1c0d82d0b40151000c07072800c00c801e0f00085440c240488500c40e01d580c14035001c100c0700000c11501901745003602c69070210a070001443c1040e07090080d06070005142c1a00118500309032040040d1080c0140c0c0001001f5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 250096250 1250 250095000 250095023
    0x30503161809020f04090518120301060c081309051806010b0a0507120e03030c0109050106060e030327061810080106021507021e010c110d02070512030c0607170a0209010903 76
    0x44c0c003403c2c4140d50180030302d40c00800c00b60030606c000800b800c0503242c00402a1040d103c660418484460a81c0d0484c0c0349a203540c410302036560380e0035a60790090000c1242907aa4000e0004c0c211100c0e008032400752641134003000001d9160048141001c405802013001d00d00c1c10001e00c0b0719250700078210780c070cc150062848807000800721800c98180300c11684941e4180300c0030a03103104042066000340c008500c143d00800a0315503821090740c6c000ca103583c905500d0f80051000b13810044070001d0b1038203100f01c1c60032040a6241c9040c001001900305001d0750000300c00e9201400a6400d00064044140056040c0406190301d0008000e64403a551000ea0000c0c10400e40072840e258000c1040f0303440001242c1d03514403403d02d0b00c08090b0082140300b0038100010784042e20040d030500f02140a4440083c03642c050015036003450b05000142a07000202001d81c0300820018013401030500c6000c0c0290f0055440340d41c0391944611f030308000000900001035044c8100400c9080daa08529880116640000d04c0443c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 250097500 1250 250096250 250096267
    0x1021b04240e0a0e01050601050711010309060609020a0e060313030c080408070306020c0c010f1d0f10020309270106080c1b060117071404021e040303050316180902 72
    0x50008401840841501800007046640e0700414451103403c60f01010002c11500b078908609859051720b0050205000f0050b18010604c3d50710085403140040c103010801100c9559030308111440d55100a4070300d9404188052420750201d1550300c41071040340c10304c1c1103080451586514040400000f4107100440c510041084194010f0700c0c01001102c041e280295541e09010000c3c0d84034083c0e5240c80d014106000349198040d6400f50180d20540d0703286112a94a0780001c00412100c50700945d10500104045403550b858070b4281003400c10940c0503546030a4542c080c80495400b100700d03d041c8141c0075451542081c2085c1d5035170b0455a82e0700d070441d0152208004000707135100703c04414090460301d4221030329001d0000354250403a1451b040d14807560441d003440580f544428003909520720682d00c0700f0011440d26802070a40701c1d210200044506020340c50221281d0720591046020480c04010480c40040410701c8110420702c500304200d2a0754003c034566864085805440b03001507011a1100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 250098750 1250 250097500 250097531
    0x130b0c070b0d0917030f0106110a06020d0f05060a03050d050d09050318030c060408060a0906020c060a1e0b03030922061205070f0605040308070312140f010501021b04 73
    0x24020300252000302e40d18003004038803401400b031480003903c100702890107136040b50210808580c4648000c17000d0600ca0390a003001155038400c44d500303e0482d0310174119a0710109040d8801030610030552400010b41c0c41840c0d06070b80076981c0050019114a510035020004140f0100c1d49149030f110b589400e645e03c2080030903440091480340300140040c0700108504486541c60440106507040403002c0703910600d801810040280700d00e00920032260059008240301000c03542006015911804025080c080707145403c5142080403110100041c0c1c450441c4055014890003108540f1714082c8140000160900440e0b0f4a2061004450080014044802035107058000044902b01e904c174044c40f009946181360842c2c403007804010349540c0a80f08000404a410420245c01c0315201d84849003080e10315200c80300e0035000480240c05100c9000700e440948042071250351004004040d03652018142454040c00300320050300800c1c1035502103a940d008462070382c004181003034800c03030300441c580c0314141800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 250100000 1250 250098750 250098763
    0x30507060b030717300d09050c030619050702010921090302041b02010e03070c050d0c080312010618050604090f02070203011b0206160e100201020c060c0405120102130b0c 75
    0xa44c82e00c495001c10a900c1404190000183d08110382c3d40120780c50f03c00351402c4100c000210780790040e070420103684075821981199800d40d0007034054034444d11504c03000c40d0902204641e021152402280503c2c80e42c0700c40d00c90f450308164148001c11a190360350340e5003100c0f020746696902d410414900780300001384c4586090307005540c0c064801d0288807440152450720b10070b070883c0362003d5405e000c1070801c07040c0000700740c8011a8005a01d600e0452500c824492940c260000c161495203a0800100d1400d0040008144030036071401d450b44958545040108116070103000031521115031481080666107910648096906600001620a0308d401d0800020b105a0500940650904171000c0314891410310052a086a0350241e84a550310701005410074240c0002c00b10100e2504080e0402c1070404400e4940d00050a0000514185c210302d40c2c2842c00304110b130700c0702c006c1000040c24012402c1c17014046d16000304280013541040708100e550010702040303001e1102e81c40000b00d500c0c0130181c000c0001e07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 250101250 1250 250100000 250100009
    0x806060d0609060609210b06011b050601050a08011a0118090f05041a0705041401200a0615080a02040e07050d0303200408100506040e030a05030405100504030507060b0307 75
    0xc004465507982c00c54081d088510561000c1803580c00c0c0010b40740c1817102103c146500e841407620380300140d0754a03c5c070380200180c0032504010000c81c024416012000701d005040d03014200034543c9614150410803075503610b0700000b403240d040c90540d8400300f064031a00d0450820900b441c2c42030001031010b8580d1181998810100c1d541446010481c480c081d82c004d9004900444258841c80501c00e81d00c0900207066529000040080108005012071168102a14881454810540c45c40003403003001552051000340240e400c604d0b4403808005d0756101c0c044580050000031b0701d40511f070003061901c03210600c0019004a0325407004100068050009401824000b0100120340c00c140c1070080041642101e2401e0340095409108030900c008410380b801c5403408402007400c07490b840440e03000f811014107010340141e15501c9450300b000c3c4c24405041d03140001d030b640d56141d01d4542082443c02a001c01c2059207540340c8002d01004c29400022103030f2894110201150314461000802e191445c240e00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 250102500 1250 250101250 250101277
    0x91116050309040218090703020a0f0c0f080301090c1d0a120812070903060c0314040809040f0509010c090e0c041a090303071a060108150f01030209040c17070504080d080606 76
    0x40c1c0039101c418018140b5005d041c00d544441c3e0990307848a09504038460031880001181d08032469400d014440c441c1c101c0810700c40c806148042c64107a4030158241c01c281c2268402c00c1d140c011905110383d00030082c020919200b841c3c1d490001c03001012499005050066010014029110100b800f2a079400c4860704904507094060a24081100074440c0d4014042140d0540c244a81946051f120317024010105004040c00e600c5a115079076003400c247e03c688841030b0480d44400080c01454018030860344a017803054000b05082500000c020030b0300186070440140c04113410107111420700381000b640c05441003180800e0301a0300d03900fa03442c8503020b5146005e9042c480003e0503010007000b05800311201901c5c280d440025100e000041d1626074040390300403501d9807080a40e8085181000c04044000d0041c103005180030111400b140640d00008480d00c003080204e90b102c3e5941c1c001070786d81c81e40980740c0d242443c2441d045c0001c590300c40c0d904422031801c00c8403507400b140d0195541011115240f00545 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 250103750 1250 250102500 250102507
    0x1e0a0501052b060303020706030c080115120501030606181808160c03050d3f0b0429010207030b150a0b070501090c08030913020c0a17070204060911160503090402 71
    0x19202c202a18150208070018090424000344160180c0a9102d4200d0281c4a2060a03820290017105410915208038200034440c040c012421580c0d1103031078060b6000e903601054141c18010308804d5400b02c802c0c1092094908001e044940364180002d68120750f01401041d0303140600da8903a40039031102c80015080c100703500c0c0000104400010013000121454850302c0400200c0c200c103480c00744000a0540382c075811005800d0710b64501e0002580594800b0200103031500180001c03604441d41c0c140c40e0000b402d103d884070b250042d01c0c40b12400300c0b50300900c0240782c420b007075680300c032440400a40342003c6001500e8445489070b0f601c08680024041183c4400d40319a51424803034081c0c9030040c01516004074181c8082400d4002000300c600c8075402804040e19074560906840095002480d1201503015140d400342c001040c09072500d583c1e420004038540c4500260042008590701e0742d0140d00030300d252241d41c0d03200520308030544001c4d203503100f4886c6040710a400c1541c1148950401c459001d403002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 250105000 1250 250103750 250103827
    0x20a0510090b16170c1b0102120d0510141503040f0803070c03080f1012060b220b010c0c050603070c02030d0f020c10140c0709090305091e0a050105 65
    0x103840c0000c80e18003d03001d012408a1850304d03128248038082541a8030b070032100c144204a1145c0070341c1c2c0c01c00001032046501e000301c502240c8480d900701907100b802c0180c680c02446100203204600c14003030208403421040c140310b072400090840441039804403040c0c0d00803000409105180c4014242c0a03080f090055030b078a41a0801408410303c01c000b203002c611143c01180581441804a41c0b00382e03900c48169001ca814801046e24860321640116410741c1c450341018901e072540c104003c290085109102019203452a140082d54030000c103441c1000502c4007524049107543c0c02c44030440f181a5152941c030740f0b41000c2110881c4409002940500c03822840c12085d83e800b642001e420f450700c3e03094403170f0f0a050394104015400c9441000000541c80c054607a13102259400a0424000400c1162811565950150f0544200d00c100b038000c148041a240c0b081d0512103468217030b291080c143c8014078540100004c030b541c5680d000d240d04006010034401000035000340c042031071001c0354112440c6200c3c1e1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 250106250 1250 250105000 250105027
    0x10b0a06050d0509010e030a050705010b04060e040209150d030e0103090204060b1b151617070302030a0c3006090203040c03050c0306090a11010e0d030201051005030307020a0510090b 80
    0x19081000361a10f050005410414184610b404002100018501d08000701000300c17416000100e0607a01035503075003441d1402e5540c0b403040c0c6005000e0b008205181307160500402c501000018140981c1c08803d0010103200c0d44c0340e00702e03003000c1035050a04c1c07401d80000000407001000d51400084d045443c0034000310320400950050140c4042910031807402c0105400c4c51a2520f040b801b40400c070044100c0403c40300c11141100d025084203520b882852a040707401d180040450641340200426400810701a0b8000c4034050401c00902d10700b00090398050302c0c1c060041d0302e940494020001510340e60050640c00103500014014000000107649a0800d824810025001031100f11110b2250a110303003040d06010039001c2c42151200060144200e00717440388100c02e01c41c100071078104100c4119011865403840d0710020b8442c0070341e0001615140c01129075189400d1904001e1080d4030900000006031750705060f180030b0355820354844418204204040d2060b02aa8114418034180030900400300b00c0c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 250107500 1250 250106250 250106257
    0xa020d170a0207080d02190209180601270908160305090a03081210050108041202100c030b0312040803070305090420070314041d070c02090703200a08130302010b0a0605 74
    0x10800d0a5503900000501c0980e5940b034000440342c0c84614402c47d0070098500b13007610f03503403000c2007407005229080000e1045045c02804d800007090090042034000c1484088410314455142c1c403c010010000d80351a899405d0050007104400c02002000d1802010300c100700b56040c803000902141c40b00d41c5c13246004910fa1308680140c001d1809088005148540f25034501c0d81280d106844d00c840503110b0f0388030300740c01c401612020003e500c2081c8400c94000010b10400c0e40c021501d54001071005600c1c0b04144c01c115009200c50341901051200380031240300841122861340d030500f4415520500f00c0d002c00c0203443d12102584100c02200c1900e00c2240b20a4010008544296103503022195041340742c802c140124003907244203030070701e000c001e4043c000a1201030300901d55041c2649241d540b68002040c03000100c0d5482d0000c0d071a608840004540344000d02c00706000a0072850a0040c02a001440701e40c008042c42c090034040040141410300030743c030003071b1842030203420186500e8681d60050200d51 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 250108750 1250 250107500 250107509
    0x70c0204050a05070806150705060708040b0f090c0402090109080d030c09080a0c06050f0702040603110109050d0807031404030c0602011d010207030c0219080a0501060905070807020a020d170a0207 86
    0x2400d000010b0301030280d07071180342d2203100326880c0c1d803006840d10810300401ea102d00c8400c003c488401c20034000030a00c10088240b18018543c0c52603c58600751030300c135852071800707400c040c0d21082d500c0612808440108040d00d560800f079030010f071601c0c0e03400012106800c20717610060850042070b060000040d4982c00041c40c8642c15218056925903500c90f19a075000301e090003070618143e1840501100b0f200b40d00a148400032a40c0c02d0342098400d400140c1100c170a60300841e940070011018100c60750308003002c8070041c04200c6283e00d20840c01e40784d0700c0c030510400038010b0411402c09000ca541a40130f2081c0c602641c0c002c2018100b00703407113001c041d00a00d1103000036680c10241d01c1d245070000105000f1a0741c85c03a850382c1c40f4626020395a00b8403154000040020042c0c50690300d0125000f0410841c0110890041c030000c990140703886482c600f10f80c1c02920000c00c00501e50100108a600054a01041c85e03050b540c0055011090800804c19154038200038003c820000d1350001c04c035800190b110685 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 250110000 1250 250108750 250108759
    0x140d060e100b0a060e010302070317070f0e010201060b0f0901030e12090406050906060a03111902010519020f0406110316050d1710060c06021e071407061709070806070c02 75
    0x2c810400720110b0b40c824480091854070b0004c0d10341d40700e50060003615103e41480302098040c42100308201702e003200d0410000d100c6580c00c03e602544074581e065007080030700080006e94200b4030015014420041d075a0b041e41c000040c02400e0364072030784c0b00501c1005004155000e0403045000450a94010625148128141200442c0e2803404030b0980780903d0000f40801e2400b0100c1da4207501405100c4202c0910500c03e002c00342100c15062148160503280e540009040d1424001c40c0c000003100010940d0500d105015100c42c4a02c21000c55040e5102e500340002040c8000907400e240d0310680c0200400700400200000030007100162035800d82c0b80d6502e0350301e04034106000d6102c0041e000c030b0b9061090022910100300c8503008503130b188901e0340102005442e1406230400c1101281e09108140d0120000050101c24428060040100140010058141070b49042001400e820900d0309180b0128400c00c0803480300101040190700070814001990014038103140c000c5e00161110f60241d008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 250111250 1250 250110000 250110011
    0x20d0c0e07021b040e0c150c12040308040501050c01021c0902090f04111203090904320d08071709010b130504020d03081003051b010e030a020a140d060e10 68
    0xc9001107140c40f0042160440e0302c2c0320303240b100d0401000d0b14001c0005401c0c5d002c4e0018039400340c3c8420700c0700ba08982030344101c02d540b4002e100840d031030403106403222800003005120510008440328103c0d412204c2c24a849511074020614050080c4036010071030b081c01c03000564044880d041a081181c4289c000c660f0b000c1255180c029040c510942140d005141c40b0309070b000a00b803407034001c01c004000d5580a040f00d0408242030302003407840c8000d4030309030360041c1a140b0f15100d1503141c040006000a03614280504010010055a03503040d40380d46d074200784002040001c2680380f20701d0182c0359642c1143c290a10030b00b0014041c034000c14004034468040c03030b5445440c4004074041d016171030080354040d003210458907098800300c980e0300020f482c01e4204440a4000000306004012485002c80080307004101e0015880016101c4040c008546029401c80c0a60b480580e442c50031100032100d80101c0c0550490440c00002d05103c0c441e0001031406103003c281e0b2001a038001034502c00b40c0c501c404104103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 250112500 1250 250111250 250111261
    0xd090c0e07092301211107061b020f070303030203180102120901050705070c151815080105120c010e0319050a060e0a0b0c091c0302030c1c020a0f0f020d0c0e 69
    0x100500520f0070f40412102c1070020408242510418284c920403100051418540c1e0300459040d840084d080d141e058980381c0c20481d03410b4000c0000b003c00c95034001003080046810f1841e840303070214030020301450b80c00300c0052000010400b0002085010754001c55950b4001c581415840c0015282004150310f01800544044d01a50484540b83d4101c01410400ba203480589070b040b01ea42c1d1010b004104000c070101200050764100d2038040c1c0035000c800409292401001804000c05a1081340703d2050719041d40004500070800c060101c00c01c2c0b90510f002d04141020034940b407030143c3e010404030481170405051000c0400c4140000340301d44400c0c0405854414015691442900060a4a0f280c00c002c5000c03030f8001c5004000c0701030050300d030403408008008100308034620b2210540c003507040007484c10303c00c12040c00402c00f004810340910545542141000317598a6841d4401821003066403040000d12500c032401044840e4014403004c1e540c4454a415004000103200d089440d0020700301240 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 250113750 1250 250112500 250112549
    0xf0606090106020c0d02060409020f07110301020304021f0c08031005120106051005220b0a0f0206091e010e10060305070b0405030316060914011506080103080d090c0e0709 75
    0x2812035010f0342c01001c8680d8a40100500044480000c81e401030040000003040480e03400a004080c00510b081c54407403c07141084640c0c0900315003828802c0c1d10410070000160380d0395400d018004d5091403d0050100441003d4824002101003c3c1404101004100ad008108039801e819101c1c03e54543c201c04008085040c280c800307600520703500201014500c0c40241c410070182100d903030484a00944603080c406080340e00583c1da0000202c5040008000071400d8100c1804264014140f00600c07487c540304c02d0003526800d00644161001c100040465007040c42508028040f15405059604005840c004800280081c1c842240c060040c050000381d1030072034200f030368100c40d00900a5842c146040082091800300f050f0304580c00c42d80d07540360701d0200310a615411039404010b400003640d0043e03080d00c078041c00c00650001c010808000018000140c0c510203480611044110100f8110f21070311341100d03000f42c1074001c08081d003443c03c10485003644c000420401c5503200700c401d0421034003010144 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 250115000 1250 250113750 250113769
    0x10c0e060f030f09070f08030405010f051201060323010807030b1803180111060406090209011403100509190c0e15030606010f020c04020a050c100504020d1b03140f0606 74
    0x2038480725810300c00106041c5811800783c1d8001840c40c26900020b4940901c0c0c914050660440b0b0310f2580b0110f4140901e5801c01000800c070802e03814a10708003140300060804042c01402000304040d12108645080c1e8189002951507809a80000400d90b8550212030b55900c01844160751500a180221b0301c030190a46d2261600486800030750710707240601652007080076800694a0400c1104050300c6451207090181c43d0103141b0910f40890300f4041070040294510068000e600f5050200c141c00b52165000541c102c2921a41c036070214541d0b42c1e0714641d40c14408000180a2500d0071400d101d01000702c98a040800c0c1e5540305d49200301d07601c600d0044640d140603032036200e0701940300c18041141903002c0c3e01e04c01d0a55030700740f0440700d2401d0190701082c02e0740c01005000e0003061010404651034202880810ba55419000b82085580b6003900007800300f03020110b000d0522540c0350780b45110004003180e404007a603040302a85030316a100c2010640e640c0240e00d500a0b41e401400e010030041e141a8100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 250116250 1250 250115000 250115017
    0xd1d011a030613020112020304030f09090b010c1b0807030c030311031e0702030106081605040e0c06040e1f06052101050310020d0e0a1a01080a03080c0a050714010c0e06 74
    0x1d00c0c89036520220f9020790031000e00140e0600010490700c400100c0c45000130762246100c1e07640c9032030420110501612032141c541020202c00d045c030118095076640541c080b002507401400414440140640d60414103585400c050000d000c1d9010200c18015102880e1003200d103e0382c1c440d981c0340e030420511520fa000b200031b01e1464009a0440c0e101040d0517401901c5083d0000700001801580c40e03140c54a0510a66000c11218111105c200910300d03003846042503000780d2201a006500413030000980503c035900800684c0c26402d000300d0403101e6031091300254010480a4103254640762540a005c68018003626010341d9400c0034242c40003a000f0315158121100a002800c6c41c10442c6e1013880a5041946100380d89907440004541c80300c820040e003020345c1d0085030104002c8107415081c154407a0160020042c80e8040389040e0b001a901080c1c8980c0614040c0901d92a40c3c12a08100c030706118840b0041c01c1c0c200341407d2650344c1001980091414003c640f1209010001c0780e00740903040c00344056 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 250117500 1250 250116250 250116253
    0x8060f0c16111816140c0705060a0c0f030903110f030d03020d0207021f02160b0f13032a0504060302090a1d1203070e0d0f170d1d011a03 60
    0x769800046403400d044040c140003c18402d10b810040c0b00d020000001190070f034001c0c0380d801c103002c00101d400010180c08806138519032441c1240034440740e44d581d0030398818140110000600c40c2180740c4602c4e0741107641a405040c0610408040c140206080e0090000740c82c41c2c42e01d080110000e01c0d1030014400e0900024018001502e001b0300240c009411001840c1ca000740c080085e00c005a0310710302103007101210f4601c0303004072648829009141076014258400b042846080500080d01990309880d4002c10082445540311621600c01d44c4c0072055070f000400a03085038a140c442d4a000c4000c108a41800c14814440d0303950358810842526050310001e0341000425003c60b81c1c405007a004110a0300449000c9074400640b40195840e04018511482c2e05840c080b00348641168007140c103e100300012140c0d0300da00e160f50717200c42c1c1c2a080080c4000b8085100f01450600c0d1080346420344008044800b1308100901d551206040c00c0070348103c030014554a800140038208825080325809581c0240 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 250118750 1250 250117500 250117537
    0x60402040e0f060f030a050724091a120a200307090306021e0408030d0501060c02090a201615060e060d0804050d151805061b07060608060f0c 62
    0x80340c01028801504603030b0020b000842e114131a031010010f103040c0c00d01c1034006000c014903010310103040e0300c110818640c206002029403600c155102c03046105031a0071740301040001006030000c84070751082c200b10000c076002c414104200111140d12941242c6a05002c0114a071001c2c0e0b59039a8510044031405c1c041004100c0030301c0424880d03805000401c000c020041d0851201d80c0c2030301aa41c00c540d028000300c0e40000b54010b0354031024003030b17a030040c10141000c0c003000f1050340c0080c041d0417008000000d403d5480c0760502460340b090000346041c4c4400b1b0b8045603175413941280c10004074500102980c00320180003480c408a96035100d0340d81101d03041c0701d40e000d99807203090030404240c800310300030b540083c000c1c480400c480d500e202c01400c203180b1130b40094000e0100480c1180030744510305d10200c100d44021800030301107a03000c515140c5c8180681114a002d01d900e10b200d500500034120050407551074540041b8107142c00040076401020b400100315038550b1110800201e0344640306d28031444400b4103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 250120000 1250 250118750 250118761
    0x6010f0315120b1b180109080307080307090902070203031c0b04090c0503070614031b040b0a0e100309110603090a08120406180503090904110904060504110d02010e28030501050f060402040e 83
    0x9844185c1105240030503140c5e6503502074030b1031074100d40d5054032704040c000244111280c001c1c20440003030000510640c10100b4540010746c4034003400c40d00242407003100700040b045030016445201c2c1024020000c000702c04141c200710b4045413442c001c503406840780060200d1900d008000d2440c040c401c100c4290724550303e201d040665400e0b101c40c022200d020511001c2258200c00020745440b00c810340e18504017280a108020320700000030000014540342001000115080d2610b40c92114029190a5640d4a1302e510540c030300b56000902610499021809100c0304014100d0306000d40d0207502e0601124942e921644c603a00460b40000b482c0d64410016111a81012030900380e2141c05a044110515100000b0502041048030200c5025540741c081200b0030038441c00151f4050340039290459805581e03030019040c2a85108074500c07038240510101c655614840300800300c001d1410010007120395071718244d4080d090907144451140c00400008049080c0f520a40c0e0072a0107019464010340c171803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 250121250 1250 250120000 250120027
    0xb040f060204080d0305100b04080d08100b0a030e0706021f0f0f0c020a06060603050705040512030408030a0507030807022d0a170409060b0702030606010f0315120b1b 73
    0x5840480305141c091100103201007040c00070742401e110980300412140b400f00304141c6001056000750039419002d12040c000c0c00400141060414940d00700350610340c90b949a20208048030f64046038825a0010b800044107900d504008484100503045034081a100c21050740c0381d44c0140020888a145802c0c9211246000d0300074108070038920400040c0c1040c4d0f00c41e050140c500302520b01001d60300c41c008503001c1203500c1c82110001c214038501000542018a8002c010313110394481c80e80718a0707509504808450042c01154020040c0740101c036615000b03100c014140360030481c001d601003407140d00010300c241d00202c1c6103c50440c80840a124090041d4012301c1e113050f140a25604603c41d55001800041548460000d841c1445190a44441c500f802e03141c280c4d8143c0d04481c1d042c100a000756401078500043c400c1d000003090805061604a1000c101c008203548012021812102c0600148044408074a01000c82c0a1112a03040c2c1d40d606084407100155041d0713008070140c04100c83c0002c00b41 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 250122500 1250 250121250 250121273
    0x503070608160507050d210b0f040f060b04060918051b0705150f090c0a0803070f1b0b0315010315060f1101020304141c020c01030f022106030105060d0b04 68
    0x501c2c2001814442c080c5c8906191403111001040420407400d060b0540407241c1c0510149445059000e20012001e90007261030341208903c054080c6440380e501c000700da14a608a04041d089441451380c44d15503800c03008003050101e1180c0c010811401c038902c2000d6140d800b8951040c0040c040084690049080c107100551003030070180c640b400b503888130007903120444078840e00a1811034040c041c1da00700800401c0c06c0c80440c428852280424140801c0054004820703070700403a40003444010720031a00c0c00d00b15505000817055499001c1c2540b00400d02c5104c503009180501a00791f548070101d10410019000c4602500042800d40c2d00c3d440100550303449581c0ca2143c80c0b1280c40d040700319001d0144aa404c2e40c0096030111200e03640340681c90fa9044d001c0005014604290020044221704004017035201c441c00c200a504160312007036035100b0030200c0d404445038190340000518542c448100b0048004006982ca41d100354209000f0401515019503005846600400410410388599485211552 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 250123750 1250 250122500 250122541
    0x70807291306050105040b030a1211030307030c12020909180c062d040b04060305090102090a060c1a060f01080915040f0b070206010308041e090219090503070608 71
    0x250400042068109040c4036034001c1d0911100100040d00034580354040d80d105801050285140c003001c45150344e000a42c1da40c9854211030342c2c41c00040100c0c4212990341480d02d00440c00d01c4000140004540d00d5071207038200300c202e507880c00203092203400d01e0350580c4204079503c0e41c08210803000c164a0302c1010060030300e82e074410007100c003503108440210300e082d00810951891100140c0b0f02d0a00c00440c208000714400c50001c54030720f818280740c169056030045015400800d65074600081c0406001d40c1101c81a000042c01606619039880f0010a540550b48088483d45520303940200c01c2c000300e600450003043c1c020403042d41a000880111b810359001082c4201c1032107a002d42140c0110a80510350055004840c0c406907421542090f03403602001410380d504544c00380b070042002c10703008070903a026602c14200310404031402d44008880401c440c1c0204010300c0c0b0004582c0c1d0009a090100180840700d07454180185513502c04158450320184a442e0205101c4000940b03441c96040c10f10f203a02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 250125000 1250 250123750 250123793
    0xc03010603020d0b13150e070c0b100b120a0c0804171c1103040507150e041e0c02060907051206010b0714030301031a0c0c0d1b0b0a02030103060b0303070807 69
    0x813006100010303c8000f01404050340541e9a0540365100b041c41c5150b0009405110b554401c142040440145141c02c0120041c0c100e0601e02c1c00700700f29102c404901002449094103150b11000021140300882d402541c040348190700e4441c004224501922646200703580007003510902159024130b1030081e03444414082c04000d100522410a40f059203d0806d80280302a10f05880e49054035100785040350356000155924011080c6444a690110b21010032110507200460000500095a8101e04034220300414050a00012141302a070000f5460703c1a0040b10860783c004d51342e00180200301765a0484850309421020051000723040302c00040108500c82c10400c02c16021290000342550421b800c04c83d2015221446040610803100c84c07280c1000e1414a018548050101d1a5a460428440000500009524060586c00d0098603003010300c1d000740900485103086100c8070000e50007404110348041c640741008100e410000f06489100382d01c80d00041c58124191900c50740c03008440d5580006 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 250126250 1250 250125000 250125011
    0x507200313080f010506011b02040b01110d02060906150607060b060f0d020409050a020c06072a050601080d05071208090a02040e01090201030e010c02030417070e0c030f0f0c03010603020d 82
    0x204206100140200a060060b183d0740720303c401c1040c25135001800c51810008480d40600d256001d20081c80320a5a0480300003a904c5106801600e80300000701d1209800d024281c00a044d19070040b0b001d44c841c4c44c211094408039990f452003901c20268200d89a604100e0610401c00099241d82c001070041100034a85800c10001c81d41d510001e601c8400300ba020340740c010600300512040c83c0142c64000c260b20070251706011180760101e03a6104010300000800001d540100c01044030407008130003020106031811010742071400c045179180403c0c812102c01d0303ca0410704406003807162090780d407041c0d03000182c0800480c141c0c0c4c04450505c00a00107100700d00942c08000016038840c0701c3e40e00210071b09400404e80b00064000034040304d954600c907403c580d0414580c0111942c1c00300454054843c028941000c00000400580c40c0c614181c120008160001040c440c0301d010701e2002d144219003000520529540d1024038908210b41510304e25800c20044c00103011960080c0c01424000c003141d40700086 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 250127500 1250 250126250 250126267
    0xf27020d050f1e1c0c0303110f18030c0906190801090b06090615040b0a05040902030705120705090307030305071a07090f060216030204051803120f01060305072003 72
    0x410508902039000d660203820510030700740507148603070301034420720340680461441c840301106a130201c04d6550301040b401c2c141070003c05019510108126250061103511140c5405100c0d4540d4444c08481100c01700c82a6803681030f00e00054001040c0700c1c0900701100649a03007050141069510325010100c0003280320220380c00c4424480d600125001da507030f0551500301101448000403002d441c2a0003240d134201c017142400d100c00c1c1210203c40c0c81001e0650f513000300031401c5403580580c0e08647c014600000c1031100c10b07607014001c2c2c140150381032590b4101d51500708050354144105024550190070444080010034007500103405403c0c0110000725000c03042c101c5404100c0c800f140c141c0301262480d41c3c1400321504156018003c0d1115000610285c40302008811800e04148030003882a80c84600181041389103d08200c02010725504490320395500031448041c0c11402c5401c9100525030b1000040c0351031080c01014011a03540c0c4441e001c407502c400180c140c0003000ca00c6c0007040d2204111005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 250128750 1250 250127500 250127503
    0x1c0b0f240a050406081305120904090c08060405060711060a090212011b0810030c140d050d050717090105030f180a05161a0a030e010b060a0809010f27020d05 69
    0x49012000e5030b8590740c450900c40090b02004001d4100d02c22410803002d8100042c10008043c8000404c0f0001e03184c454220800060140540910007800c4846118000030514400a8800e0003644110700f07554043e0358a54003151400340d050f01e600e007240d00c0703540428400c45181d8021070b01d031070000e449400c0c00c002d10741e02c1c00d007507032560000341d8403041020380440c83c650b6000e241d103a089042e0100801c9000c0c0745443e1058540000e000c0c80d84ea40402c680802d10a40c1c800107002419a40034040d18082e640321500a0080c0d084a041aa030046113026045907980e2503904880c02c42c801611498155141c0a50400e41920300500f0030003201d440410084034180100090320200d840340e40100b000306185e2505c0800007580394085105041241c0d41d841003800f048099460704042481e00040381640075600b240036001e5000c1e400d400440016007000c002c0c0d072040c4428031510181c8001e10641d0451f1985004440d20b030502484040c40400d004000108190603030494140010700d4194000c4140d1a00b5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 250130000 1250 250128750 250128757
    0x403030f110703020f0606030a061a100909050c04030c0e1b0c01020903010b0a03030e061e0a09060e0a03030921140622030203090d06021c021c0b0f24 66
    0x907a1002400314088041581c10401c2811190310750020705807900f00301d030109550b04409100209a183c9a0340c0b1075050440040510820800040141d01c0750340d9240c001912400e41409181c803500d00346800140041000421034003201c0e4000b500891103171800c40146100071024002c00241181c02c44120380b40400e0a0151140e4a00780d400142d580e07203802d081500b1a0b00109120340940c0d20f030759041004c41e4001c2c4510f200c6910513100b460391100a108000c1c45072a070440403400340080490308060880e484418031094401a4a5002c1400075010400026000e2803000400080c1a48000c0c13140c804541a2640d000080c07802944204002d0741c3d4811500c0c01c500e680071180d0b0b1001c4100811541c034100000241030044030800d42501003030314001d44920900b01254015211050800208605075041702c0b00401d11035245030229880c42002c40195111190003600ca0041ca800d04580040910417022039080007004044002031010a0190220400000d104003002c100044000404000b005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 250131250 1250 250130000 250130021
    0x403110304030218072705030706030e060c0702011812030801080102070c051306181a09010f0504051801090507030605010b040e16020309090705090915010c0b04050c0310060801060506030c120403030f 88
    0x1121b40d4106000e0510f00b882d10750089040505041240d5201100400c80d170b03420640080a06a0380c041a0005035442c0c0c580448072400c501c0c03400c10000d181c218083c04000c0480c4650380e803010300e907079420f081400d03401411400b070301c000345c681c004001514001580d5000c000440c00040307101651a45606280b0b01c59014117084c007602c458a4030611000010064480c8204403110849941010400a403c145600a02e4015076030b50007c207000045103540c800d0604c0c254002070120185c2c910b4415220006c07840100c070030034140700001c41c400f0340c0d00d0280c0d41a6440c43c05002c205a40380c44640440e01c4d04100441d0550204110061964592411292040e00e003503c4d4180d0303441e1284180482d4040041c075046c105540502d200f41030760b0780b0404464170941c0242101d40162103505010f810050030400d003d48c58803800070240b030504081d801c400110359080c8002c0188a98a9060080902c02142c010035140002c0041100b6580743c0c030781440c1c000c0d001c0c1c5400a240241e0681c008111050803c0c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 250132500 1250 250131250 250131317
    0xe09190e071e0801051e04170d020403062412080912010213180204050d0809030f07060210050901060b0412030e04051806060f01052a060f040311030403021807 70
    0x10b051241c081e09000e100d401134a4038a21907403801000100c081310004c05800101904180c074849250f21036210b09407003e040b00300004550302d0f9030f02d1404c90003c120312900c505030364070a00c1480c030038000e801080104171002c0f00d0042c4544042ca54038003416512103620f09a20181301640c089804900740301034024480c1c0d0007014030354030b0b0070700f41c0c0070200c03a0550313100004580c0104400d0242ea1280d0b8a4120030640c015400358403002494002410043d40602148075031084100005084d5030028138911502d641e88010017071a01c0381c2c122103081c0c450324004c09601010400c010400c0d09440c80000340c10500900d448040064584001801d480f42035031040b6443d0510020303100528001e0041c1504588112841070603100094000380040c0100002c00a4801343d5001444a100c0510308900e20080400240c45a51900b44000b24a001e07080da419000541c840c00c4c0748264100c00812941901d4009120008168440b240280c0c00718008108404100725032072200707003007015200c882406480001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 250133750 1250 250132500 250132559
    0x1060303120203040302031e090d06060f080105090a02060a020f070f1d06030a2301060b130506070305090d14150a270f02240a0e09190e07 61
    0x8009181003034540e020700c0d156104105100000744c0002c00c448544c900b204a051041403840c840d40a180505001e0f541c02c080502c001c9400c10055030702c07640c00d8501c007c48617414151100041c5007200c100701c070000078682c4031100010151412a0292859101034411502c0383c03050070506500f4000c0039400205c403503400002c14410304003d010302405401b80c024070303d80c11b8500b81c00000d5840015400181c030a03a000b6a44190600c40d020324140390501d40c130001d0000c0ca617202404040d66016441809071305d04066800305881c5010304c101c440c00c0d50142d403903a00b42038520013001100580c880003280e000c090803039010310068060010b103140d50b600e0201c0806614103442c0702816181d1444d000da072241c0c1300410420110360480030701c180b40358004185561110341071001c2541044aa81e0060000040300403004d01c0100010041250200b6591014511010351040c04550a010f0b92040c036045040200c82c910b00400340c0c00300340041c00c0001103d44d41d5542d082c010240020b404040c80c05000d00c0d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 250135000 1250 250133750 250133753
    0xe12041e0f080a120323190e0303150906030604060e0304091107060b030705030d140904150612020711093409120209010e09010e01060f060807030509030d0209010201150305010603 79
    0x3801642d56285d050030f200951900c030b081c0c0d00380440600d40d03200a00d4480d0100721070001ca03080000c209040b0706003c220340e0020590303890b903d42003242c40c8501584561100344860070001c6e2901c5c0140da01030001e04158a581d582d003009010404101c100c203100a0100041c035210038098411681080610141ea0f1101070802c1020388880b8640365009903c03440701004940c038000384240c588442803030140c3d141e42c600c8005854500c034440c0040e90060408003614544110a03030a9421100241c892414003500480c10406034000c04170003418400c0c2007011200e00e400c081c5110342d800148614240d0b940c4c908800c0d0329050300344202410351100c030b008094502507500041070134090b1880d44983c041510380c60340081c038650414014000f61031a04800319140c07480c2500302c003411303500c800001d0148a484030415071100f6000e100308170015a105011400d5a4041c2c8150780c0590300d0000a9403402c108504590060361109440504541d0307900340f90038400200300320840255206800114246285 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 250136250 1250 250135000 250135013
    0x209040509010c09090b0604030606030305032e03060b121002130503060c0a0e1809011a060702030a0602130e04121707090510090308030405060a0e12041e0f080a 71
    0x70a00292a85030491185031160001030718011501150400b10340705103803101140c200d0069900c010485c0381040070220400d900032015500c33030b01140c0b00c80d40050350785942d035840403811841200c5400d4400001407000c00c5a50304941c55000010744020801c242150b00c6a01c5c4c050082c000036a080e40c0851000b000d00c2d80a60b8080c0101030407401051241424201b40c0864403800394043d0900c460700d1f0819103640c0b0707210741e914840d20021805850500d0910b1240740078203000c0d00b2114410003c400c0c00d15681c9098000d603540183c0140041503400a01d507204402544003182080d80d10104400004040e40c032000c0be144510f1080d01560300b0565083c001914100d40c07892405280000302c0100003c15071721444d10411118100e0300a0101d0074074020035910722800c0e81001c3e200360320010402080c0527000507c81d002e103040700c208000d0801c0300a401500e405107502992405402080100411014a8800d13000c0c41c0c194160301011035600d0001c8400081e1a07800804240c01082404041c490b1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 250137500 1250 250136250 250136261
    0x70c141009050d030c090e1b04081c0f02030a080919080c0601050306010b0d090c0b18030f0d2f0a0c03060b04140c0a020a12110f03040806010e0c0c10020904 69
    0x101381018450241141d6002e0b0224035035002c0c070400c1e2141000000c42e901024400145003204080306155102e072114101a200c042d030b4100c2040301000101c801941d00d01ca9440310240c420540d01450800901030403c581441000c0e0407030841e80310340810015541c07400741000c14007502c21400580c1d5001d44205650400ca0164002440f94200740d0040110300043c5086034803070700025100040c2928185024110200140c11500c010140803c03041d1094548001e10742440000314102e070400c0459068440d9204860020303400000e000e42280400c2d0400c910321506540c03605030f40025102d2840ba402131401000841c00d440c83c0324403500401c20303c4198401c9982c180d00070f507028484614406108081820060300220050400085441c01280709100901c80c1641c010030a40502414200051403150542088145400780120301480560000222001c0340e4004024180d1686007290310b5034000b07170081500720710380420400782c9440c4000380021040c56410f2003006072076003202c0080c00f00301c40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 250138750 1250 250137500 250137523
    0x50909150906011202060f0c0714042910020a120507150612021203090916030f0902130e1509030a0306050d020d0b0601031d07030b0601090e070c14100905 68
    0x10082c0c07005125502d00b0b410400c40c01038044e2562960341c0e000107080750642c4034018060309503024104c4041400582540c0b0349a141d20101d4092140756040d90012412001c920b603400301c0748200c0420102c540c18030074401d140822190040d0743c0b2007505500c80e500103030b10200075500018000a0040d041100c0d024851400d44100d80c03007042164148076001c0031151102c40064030840240d0070070452540304200301c40005038080e041c0e40503402c1069244500e00740c1c400c0107034082130030004c2d07a007000c40c03803032050400b6590010a03042d60300d4864200000181158064a03065005812003080f40850b011a154002c20340c0a0085030f603024030f0340005088a5113900054403030a150006100580c0e105002d840d403481e000000032031203490b01c03801070300100464640f403a0a1092000403100c508070109829040340e008840010203603440c140111141d9040340541e1404045080c04548200d00c140d0000461610544000404210344000e0300c1c0f400d008050810a91610703080400200002409001040c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 250140000 1250 250138750 250138753
    0xe190b0405010e06160315270e0a030504050f0f091e15130b49170f070b01030b1005060406122a20030304080412020a0509091509 57
    0x342400c885003604076903504188020162034500103440c0001d201500c60040102e2003086d003440a9510041002135642c441c0c003107440c0c9c0380002d035000e40f980c045014039aa0764107942d40c0e0300c2c0038100410020700d450300b8134040e40c008030800c3e035015064440c0c081e0b1900590b041d804400c06d40d440c401d812000104028560382840700205121209600c0300c1c141a01d0381c4400c010042003d5140101140308101c1c1250704011a6022520f0f020f421030003481581807081074090005603407103040c4101403c00090f014001c02907040030030340b84c0001c95054017501d03c4d40c1110728100d00e031003002e0315180680790007078205030380990000d4103000c01c4201105103071004120a0702c00c40d0070180341c02400307002c4005015903450350546400302d80402c0d512204450300c0920101030700d420548500c07100105043e03462a0411101c05103c0c60280130700e200001900d10903079100c00c0f01807415040007020302c0e20440c099401c98004c258441d011a081c1d907117030911441600214010042480742c01c0c0ea140c2040006411158103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 250141250 1250 250140000 250140013
    0x1201090e0a1e0f0206130e18030a0c06020f04030b0117120d0b0a0306020f031b090a0b0a031506020c10090815070c061104051f0e040e190b0405010e 65
    0x510500c00d41c0b0240d100c03400301e82c0c402200c0c0d040112035264080002544000c00062038550303403240c0c0500c071081e0341402944d03204031703921541071051065030760503030724802d500501c50300303102510410009240c035100f1034000d07040c6900941d4404054012b42c0086402d006c00800500a81510000307081d0050b9003d40140300c00301200320380b4002c80c466501100398050b15044081041c1d100e981d4100c0046900c410308540c0e8100c030b030341011400d82007a030380c007120603a000440e54000490781d000c0d0740c40004000c0c00038032420f20301080040b8581c0310b132510f50141a203e403074001c000302d15500c61000800c00d940261441600d40420000d40d1307518440302c0340a2100940e8180b01c840d0000a4000302c00f140c46014211981b540b0740f0a031165000c2d600300802640c10841e1208002d080f5401410843d03405070b5164000110064a0200180507090b10340005041003d07502198034154211041196170342c1c0950303810052180400c1c0c1c03890288600ce41d990602c0100740010003400340706680c964114040075059 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 250142500 1250 250141250 250141253
    0x305040b01030b071b050a0b130b190615020a0302010c0908030f03130b01080f060604062103051e03011d010312050d0b09070c1a0c0901030f0f021201090e0a 69
    0xc020060201508021121000401c158011701d05a11007480d032034030210841180c4c0c41d016a540700c024404441523084900071441c60962044455030f96540900c66042d076030b95a85a00804400700940d41d00b0b82516a800010140c203200345081c405c40450b8080d280c03410207818040e080d100da8400310810800c09200401002101001360f070102c04003a1506030b901c0c0c441104c900038a085503403001c0d013038028050000940030710004512045030300f00c0382661565900d140030001141c10700d101e504448030b03070204590442c603e03100b50b0141c101c0c03003410490b00f045441a88a681214000200e0381006400401840301d9100100110007641454105140c03039030560381c44141c0c0c8144516100144800810300c06080017050b0411141044060300416241c500410000d1600d07101b050240c4101d00446203455403815101002882100141403561401c040360004400822444000c06819584d440c9407080f08110380c0018412002440f100e4121941020203280c215040c04140c5031090b800f4902110 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 250143750 1250 250142500 250142513
    0xe040309151b02032d0114130b06120601180e07080a15021e0706050a1b0f0c0506010608100e060a1a130602061006030501030803040b0c0f0310050907030504 69
    0x40c90300c0d00340d00b003858980d039480403921781010480070010513014070340c840d4052009076036a17001d000b18005c000d1100169151245101c09800d6030407141d18060b864851001c40c50900b0301c1900200c4c0035103120b62242c3c02c02d106d00d080031401e07081030303903190006c00c02d030150380c600790003481000306002c2c002d01000c900d0b00000d00d590750305450004041242c0d040ca22640707540c06a050f0f600740ea0050313234002d164501e00105401c2ca540000d004564040c40d100c0425071290301403240081280c500100ba80c0d0000d6141020344000581d80c0d4580d0811031030859110024405010352802001182c0b5115240c3c02c1c010900eaa0346440350300a0b0600c211704e1010003996650705a1114126407000c10810461000e0822102592080c41400c3c0080460281d00003900e44e4006003552141800d2481204445e4640c4411400c4e901d080c031024080c49014070104e00441c0c10007214542110311001400d180c8044020803400640044075042d2102c060f0120401ca0f60a00040466008500e460100501d14080c0c0c1c948 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 250145000 1250 250143750 250143767
    0xe0f01090c020f12070201031433041d060612070e04060204030503160c08010c080c03061c0311060c090d06092405040212150f040512040e04030915 65
    0x35080107448880c075640c07050081c03001d83c1220403035400b542e0020b5854264541268484e110490000e481c25903d0441c1c520807880d441d01404140c070840da5082c40d000800d94502c0f0005442015001c9962446000f83e940c07482154100c5525040c5880c0c184c040a100720305021000388600d0003601c00241d807034110000032a20070b007a640d02c5811040e040c0c86d0790074148000d020304d8000070403a12002400c0d042440c00c44c1c0c580c015442c440d12410700e8041d124500c00e07003a07698025003400402d5212001c90060002c00b000703143e115401501d014056280c074001d040b40e04200742c1c0140e000c41c01700c40500415a0003882850344c0304004120840c5403070108000305109288080b8081e00d116540c010704020400440d61108001c078201056805d0b94003119098001800107580403031143c01e46440403003194101080b008001c83c4038100400007603480c62407810070900c00800072200c5018010803071500c1c54500e03020308090f004144000060389098035001c4c100500036005402d2502c500405003a031143e205150 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 250146250 1250 250145000 250145009
    0xe070206010306150b180301060801022514030415081302010c08030615030106030605030106080607200106030804060c02100804021315050901090903120207020a1214060a0608070e0f01 81
    0x143c0307044c1021990b10407110540060f208500c00040d80c0101d0344035405a5100c1c103c046000f0014aa0380d192460700300c2c402e003509441504413107406440440b4504007580007003030041025400800780c3d941080d003154041d03007104402403040d10305056149c1d4800a1903a000030110003184081d08160006480c0c00903803d002000d481e00000002d031962a8204030100e00030090003540d0300d070f50b1903000180140425019180c0290318240000565010004519001d01c0060b05d50b070402900e90001060255044408282c2664941c0800400605810001d00085c1000c1c3e98015605d50030380704021145504030007071010407840c40140000750341c03550032205035513084030f00016140c0901c412420702411694481c544c0070f0344440000a050b80c10f81c00624009101b070381c0d214289142a07a901b1b040380210000030750440a4034400740b241c008142162042507002d060a8034840584103004c9140c40d00483c2c0e507580300380e2141420007800c8020000c0c44060003429400550a240c542200002030205205 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 250147500 1250 250146250 250146263
    0xe071d0f07050d050906060310020f03070e060f0712080a02071101200a08032d04060b0f06160c090b010c02060904060e090703030906080601050703080925030605010e0702060103 78
    0x31409542c01071084880b030344640c0c1024400d500d4000c01e4183c80f4101120b040713019009292040d00904941d100f2a000e041d02c449132682944c50b044022140c20010340c2c98150007150400c842200c80300100080c03c0500d02c665014608001000c000400c002805040080400d0040c03004500044205d40b03042c021400030300e0000104010650200104025002d0300c4005010b203005038024801c20341d0045d88100b64400003095448122102d203140c184100400051480c500c501080001d0055040303980c10b881d0040140c40d103002140001501c3c1e41c401c48412407603000f403a480e035007003140c0901242e0040103011403c02001e100c81c000600798842c2c20350003e01c2441e00103904200c0e56a6035110340043c1c031384101041c41c14980002995a940d64500040d0049005140c0014140348a0314049202c1c0314103030f655074204405503a0584104602503d10030302e500850340504030040391030200a2a1407403403440c0422846c91030410b90110340042e005201880e0510f4200501c40d038000034203c0c1100d900c0b50703 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 250148750 1250 250147500 250147531
    0x30103050334030f140c030403050c0109060c0b04030c0b0c090f03010501050a0302122b02150106140d110a0e120d0503010b250803010e10050a170708010f0e071d 71
    0x10440343c4103003c5d00b40c080c58440205011240034400005001906c1c1301707904564800440700c0c01035802e44414450031000440004181001a01580480b40c00c41d209040c106205001d40c0e0310380c11108000c8071451851000410b0708507803803400030300d120240402030303000b00701650409010646003641408083e0055002c03c02c0c95a503507804002c0440040500c42c0c07130383d260800300041c445101c010451268010b20079000c4502031000c0e805071940c100d50f4aa11051150340c1211090303400390b0001c40303111030f619035a0101001c500b13030170348010301200400303a0300c802a5142190800c4200b611001d01e4003002d510009a8000c900d030004200d17410f448560105d1901e458840100b58440460200c0c171900b402d06110b80d91041025400145050320a00b026001007680c800c0320500089070544215030784500900c008121449110807201d10901b980c0d02505c1344a070300c0301261402e49228110400d2006e55980c52403114a005008a0010700000d10b50013000c0d090060b19400b0401c809081d0980c040e4220 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 250150000 1250 250148750 250148777
    0x1809050708030a0302040509160503040209040317010e060102010606031418120a0305040618030e0609010c08040f1a0f040603020d0b09040c080606221503020603010305033403 77
    0x1000300400404072101129a40c41e440c0f14024081d400038880c01d8011064070000ca1929048e0810f101c21241c05541d90328290b45d1240c08200b42e40c18060801c0d000d00042c41c9201004400980300c89000e8840001140300d135017801400282104c1c03143c2c0c82202094a00b074485d80705055031401070381e007100320b608401c8480c000324240c01c1d04000c201200090050030001e661014281c01d500f050740f040b0f024200801c84a501c1c0f0304999600350041d44020009006003494208600d4100068480524103141c51070340d00d070f4560780f070340342c2c507801900038070031032051540c00700b104620b000110201c0c0440d00d1140d0b41003181c41740c000351060040c2c1c050701c014550042410400d02500d54414800c25200414107602ca0070103081c141034804480c0038490290140c4400541070342400000040b611400c961403904039040d50b040400107141d035144648440520309800005a42c501c1c0c0518040d5010354003944c0d46401d41100321921790403900c44051068031444000e2003d10313482c81e00d004880c1d0141084030b03064219 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 250151250 1250 250150000 250150003
    0x1b03070b070813080708010c0c0209060127031a061c060e030f0f07020907080121080705011506020c0f061c0b060409090303061a1b0307050601090c1206180905 70
    0x30b0100c4540380350f012100008400308002441022101000000c228000c54005c0480b104803540c000a5001038035072012030f519510600507003040900400e060700707401144400440b0420100d030b00c180e8400a001442001d2540301070040c941050044a030000c04403a200c41140b40d000400310050080c9541d201c041610722014012590b180640a008075500e500460414005401c154800d034050720408000130440c078003444a50b0706a030100c07000301d0070010035000701000518100b901121801070500c00c00c000100300340a95800800140c000182490606030024036005500d420b95101e80b070515147d14940d00d074030048070310a0001a980c644000700020701e41001d081e6903c1101d422100c001000501782c5a06d901c40c40582e44a50f5082c481d8550340d00c610308101842c0340b0000d44860040140ca200c0c5d03481d00c045407161620000c1641d041400743d445803410900309920800312581c54010114841e80d01050545411442110030811f8500b49102c40790200504048640c0031544c0c0c20242060080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 250152500 1250 250151250 250151257
    0x1080403080c25060e160504020d090c09020c10060501120b12060705030a0f151202010c06060305010b131503031d03030309070e0612030304081602211b03070b0708 72
    0x201038a0b031003220003100c1d04220745245030743d00965500e440c05c3c0c1c0d420f0700102c022410f5805513003210000301e10031341000c042000031340c00385c82905190352399105410005045c00703c041e001005100001070f25070659890060030210b059040c1c6c00b03c2c81c0340010500c8240c1e000011060a50b103101c4001490610000200301c009050f100500711600c60740c401c109100740d1210046101f01d007800e400780708081c078004142c010354800c40000302807110040c0c0140300e51804d1031080211940145090345140d03035580c68240485c0d030160401c1c0c03003594480114548a040032044c0010181e0100340402030746202005400c01101c1038080202000a107260344000901d03c000c0212030303040d009040d2a52424030b4080266190340070311640d07000b1700785a40003540c580341681d0305103805200f0001031855561960ba03042039652022a080b200600700c101c0380009a00c460b030104d1169000484c03e69051807409070b5240c5498036043e11911640c81003100380d03280b5140401c040040b28240b080c140e48851451906154600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 250153750 1250 250152500 250152517
    0x3030a0b0d0f0f12140712020111070302070e0c1810050409020a0207090c020c0907080a0f0f020a03060b211801050f0411011805100e0603150f0f01080403080c 70
    0x14410702e4002c05121902c40c46401182c422420380d012404542410ba89160302446030342c024100600c20500481c07031400c100380c0141114800010720201022306000300d9041200140d00603481031390103014203075070b252426400c803030700007003490510310a0f80560b2688698610983e000c1d0b02c2c8100c50001050241d419140600341d080420b54407010000c9009507070760480e10a2000413420324184c0301d0104c0c00420785031b600c4d02c00600203c10654600384159400b1070041c4c4103110840e0359040d2030319a50010320034540d01031903280e00940e5076a4408002400e0f14060341040324144010010a4445924500309000610303054000c51803d80e1122010300e9246240c0b240060310b5403c020822894075481c900d020b100b507118110745200c1a1190b001181c122040040345900e4201424041c400c61410401707084860303d440c5803001440b0440ba006c10a0b54000741e41d034589032240007078200302c2841d014940c0f944503d07007a102010406080d0300000c12062002d04054180088040801c1d00c0e465182e08944900 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 250155000 1250 250153750 250153763
    0x10e010306030606060507052802060c0705030d0f0806090105010e01031a09040507030c090209060403021e030f070609062a030c0f030e090906100303050c030d0e01020307030c020a0503030a0b0d 85
    0x90355440094420340c072404042301d0a0081948010510381e048400c40c020643e0002c1c0820040000e60a2000580c000c40c643e486a00c81c03850700013069a000c1041010810495a44500c940d40780310003c2c0212802030318145c86070391550300500c46660300a1500403403450074a00441d41c03144504008020f105404a05508480c0410801007806000174060703080f203100d0304130420b40c540d44404610480c056800130035407100d0200002c10241c600600c03003660300c128070300c3c8078103610700006d000901e4014031501e40c403001e40081c90200134254100313985800504890a03d00c14a00c1c181d943e2141000c12001c00d0140311029500301c0007414810703514800001d1784200d0000600c80d05003006055004c0e840000c52291290314001007003070002003007050041755103109021a5505541d401c0d03d890b005411090034520042c40a0140050207010724203070244558001a60b07410b0440d00102940e41840f40d007415580510410701c005100001180e5000b01c0a40d0f000503c0303d14100056290046180e029184 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 250156250 1250 250155000 250155011
    0xc05060604050a18050c030c0306040b0417120a0902090606070b0406022209140c0c031b0f0a03180504050c03280204031209090e07090b0d0b0f01080d02030f09010e0103060306 77
    0x4205c40041c3e07803a0f03000c80850031141070044403420149c0d1080111001441000c0b00808140003410f8440c004075078a07000d880c202d0a0541c00810035450b002c0c125516404641c46041c1d04066052081744180c2180d41912034601d4442e15440350107540340302420081c081343d80023410007e44131050305050506040603a5500200c0e0b1b071885640040c0c9035525006c0c0302020650b000c10f007035142d502c1c101c500300e40e115400b03036042443c5100181009044411650714078082c1c0c0d14403010030241444180d1485200b9120b0748a0700200b00c2c040c90003e03545810040c0100e180c502409820303100c00041d0ba41c012400c0380c00e501d2405e4080302048131040301003040782d40e044c000b02b808800c00039034419481e0949a01c1d5594101a80e88aa078281500c803100001c04d81500301c0501404610060b80001154150140680c803240b80340c0d87da856070b0001c3c00c4030700d08a29039101c8014481010305015409603103d04c0d1004608058a5085850715131050b0f840c601e06200005450440f164040e820041c015508203504001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 250157500 1250 250156250 250156253
    0x507050106030b0c1e04050a05012f0f0c040b1c030c12111603030806010309020f030d0f140a021b030f0f0609010b040e06010902031e13030e010c05060604050a18 71
    0x420ba003103017101c503c4040701c00d030840b0341503c00c02064504450f00105002c551500d0322005541d20811002e050212180c0c045c10a01030031740c2d20903046010035081006022000302e500c00035003010414542c0c83d104c1c50920050403000c1c1e841000440340304e0305814540c41c1c40d0300c0a1038181c07a541c0c00d40344010301c516101078400720320307981114600e41240040e0058030340e40111a1072517076000c092408000e0100760342202085041d4800e40c42240d0f16480500050800008040003d1410110740c106100041005001d402110303403101c0480403540301c0920190415140d03aa0183d2100070200ca07082401c203640b60442110360702005030514101110098644010b406506039859800880f08400c007503084c500b02c0451800c1900c00c2d0312581c1c403204050f011a0b428515440e02135031000c0c101d0034505100e603461242a001001c221406055402440b1901600d103140180040408030019414031603071549007000b0030390108450b58000400c60300010560780e0030070210000c1810156000d49840103096210 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 250158750 1250 250157500 250157521
    0x130b1807020a1b060f0206040c06030e030403170703020d08011d0604110d06060f050408120d021c060612020412021201020c010c0c020405090106060f030207110d03030203060907020106060c030507050106030b 91
    0x2080e2046a6280c40381417083d0b010a0340c1e01c1c00240e400030074504c11001c081210601c2a407100c20320046520503a440c050703a9448165440b460307400c220310a07010000c0d91208254041042c1d05000c402c6081403c1700d58940b640e003503100000d520800341e01c0c02e010000140281d03a558400080503009140c2c40d900c695820761494001c02490048601003856041c5241c000340c010003c2e641101c9000006282050b054141d042054101d140d000120725000e101221416020700010400c54101040004445107444030003401c03550708004010307543d031040000744150301004403001c42d596016a407000010b40340800540c0217200e602d00450300765280c00d2004804a90001c400a00b183c0212810301441d00d4100405080326118429030340800c5409141c104028081c0e0090896140520b0090003400030f8940410000c0c100240d0440c00207500204000381403901b50b0415802503040c1c4000c0088504080e405004580b1511000e0140100412540b003004002d401000245a10950241d640c4c1000d002c0318 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 250160000 1250 250158750 250158803
    0x509190f15021c020309192102030d0623010f1205010801060501030b0414040215073e13090809031b100c05190303020904060311130b1807020a 63
    0x205618240302120101e4034000d4a000c0d040c080c000c0c00498030561411200d0001c400b070215a0340e920231110008500343c486820100c81280d4000c1c556940c01400c00d402210a140c1150714240040c0414601c01c841070a000d82c0c1d88182030901c940d00b50520710003500d00b005880c141d4000c1e01e042500201e070320315046d000300c0211003082c1c8060000b84805001c12081e0791001131410342c00c405642c0028058a0095010284202c60088052a01c000c40e15401e40b4010f45260081810700344040e0688681030075014428070906210000d006080715900140b0f00342110a54869845e17144c4600f2014880d0b204111020103000904a45c030b01200301c5c0251018100306810688601d2000c2503034440c180c00b441704165a0380c8e101c0068070682107038030701c800300c00c004800c400c0e410180c0c24006405141c03140e00c211000381d0b0107901ba40395041207a4082240003d8400c0e0501d84c000e0400402205a84030f00c00844003214612950381015a20000201d01d4441c008002910302c18492580d401105041010f0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 250161250 1250 250160000 250160017
    0x6090605010311030112060b060d050901060e060d050d050a0909050a05100e0108070501030c1205090a060c05090306060609060c0a08030f070c0305070f020a08120c100509190f1502 79
    0x103003d8081015141100da0109104002d038000d480c01420000a20f1175202c22020f141c000c4c245410014090408811540c040b10510082d81d512403003401120146e600b140d0340004102da020b252440036540b011b4a64403204000414000f000c2014201c1c035000324050720142050300710422880c82c001c4644d0307018007001e07903c1d200210301e000780100322200b03204084c5060f00d40c038030700820b00e60785400d00442c001c00c0343d0b00f254001c114142407214078032585402214003a00c400e000901c61142e2500b054000c5414043c07580e828440200040700c190307100071410592241c012928035881d01a0140440c94070700c5030b544a540f40d07004105e10001003100c1080030f0740c081d8000d2040074070380d03980d51181603030369610219024000c01d800b03000920018181d0020700b041c41d0f102a03c02c42816550314035440c47e0205080f8106a1800003041841d00c0310000c0020303441070044008140315a003031018205890705075001c42a2011141c004809050124481848000a03401500d94540500741d24126000750003c0b0070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 250162500 1250 250161250 250161257
    0x501060201380a060e010f0201020c070e1308040b070c081603020d0c05040203010b09011b0f020907020319210507051b0a05010e0609070e0c070605070c02040609060501 74
    0x898914414401e450388914041021140b07802040100c0c440000c002c411420a04042e500450741901c50600728001000d05860f181840d84885001510360f242a610b0b400c11a8810f006110f8181e0001481108031500b010240d0800e4541d214000d07107050001e10f004e0118500000c2c0061155041c0c5c0040590780e000d940b03c0460b050b241c509654480d18a00040100803000e40d4051015260044178100d50707510400d412884103a8640118050340c01c2648031030766007907000c143d40c262541c2214203c40d5041d500d00d080d03203983c200c0d40d442100c288401000a4003602c010b000207460503000308101c800b1001c0f00074402c19400d514840c024081c0800c0c4419900710300c03003807040711610002070040740e014191a07200c0300e08203860b05103031038210304128a035145903203c0c08001c580883c000303102740f21210104c038019183e14901014640d00d400e000b030b840035030034844990400402542c00810b544803240e1102c4041090384503220111140101c1c044046c0d88030b441c00100003400000b030b03400300f02103d00030789 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 250163750 1250 250162500 250162511
    0x1080a02150c06060402180a06090504110705060109020f071b090e010506130b0a050904080712113a0c06050601140d0c020304030f05060f0f0610030e0f0a060f 70
    0x1902250b01607080106025406007020540e51300d42034025107409100080d02111a520080c00621806100c0d88910b004c1401e09800b8480c9040c03501a0783c01e4281d144115524151250b0348503940c8650500c180304160342d0200342c10740d10845d14011a070030183c01c0301000e0040910f020303c26090300c0803840f8100d000c51416855884958040c010316100381401002d140d0079058407080d29014014401c9001d030b00c002e0160303020860391b80703da001500450244d070701c040d240d60f02850403550404062003d43c060041941c0d542d41c402000040f4842001384020f000c0e420160401c1181080311800780d104244070b140744098881050307202440b440003d000d001e00348450f444030300045d610291003c00b182459a4100400002d1040d650130044009000784100da160a582c0c0d1580c00c2c0440715254100e42c5500101d003800001404990302c0d03a040482c600d80030b40103042200010b0b01d50410741221030141a210b0460f44c084250522010b80180b289409607000415245400e1000300041c41c44e9a4081c0c1c0b402 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 250165000 1250 250163750 250163779
    0x6030b0c0d20280816021606091404020903030423100804020102100c0203091909020f04140102010b0108060907110d02031e0405210a06090623040506071d0901080a02 73
    0xb803400f0384003e105443d00d031100e803030380e84e0300440c254080101e04043d84200b9009000103413414a00750010702c4a56200c108641c100640407074140042c1411314801e90051141c0c040c01e07900442114200d40548150a0f0b414015a141c6010a0008076840350711200f0003003050021600010303541d00c918400d81c2940c40130030080551104a03680120481c006034024132450000d414050350f002e044000301c2e040d100f101c954801100381a81e0080204034100d00380854100005040307076500e4000001d0900003445226410b0000901e5a0b5000300414071a80d400408101c405005504040c600381d94141aa42c40d600b508002a64030343c000620f00c4504100741d418120b980c8101c00555041c0c500c0106a07200d4480030461100c8070803000452050b071405984402e00004a02e8850211210300c5040003241648100b5101101d034661a04500c0541e0100c804010002c0e6011030740c568010760340d04200ea40c460854201d81d003072124828080b500609850700100c2c0701040014400b60b440d1007281e07155642c2140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 250166250 1250 250165000 250165057
    0x1210c091403210a0201090f0c1703030105030a080d0e0607090f050108040f0605060126041707032015090a1403191409060a08150406030b0c0d20 64
    0x590f81c048501d00180002da00340700c21400103200c2c0400c40e2001007030140480d2101c0340c84208001040301c469000303440400c400b00b41c0200c2111003a0b90400507605540c54800880d460b00503180d002001e810340051010403840c40c0f94440303000606072030b04890b814a000e00d4081e10307025090241c0d40000b008010009001d46c4204400b41c406ca61140d0000b001c0c800c680d5440700030f000080c203424103101d0030301001c0207850740b20403800100c101c5881078522241460b00f4510031310345e017800280701c801c1420030803007000c241c0001d00d210514644200350072200302100c070420700304914030044201d031092403002c0c4003504c0340004004d6040c500980211a20010204460360f80b0f12032540709184010070f0b00c43e4500b07643e00031210100c4502a1104040c90b20690344001801907000c1442c3c1000308450900b40805a0620818001c0703002c025102041036900316261091480c5004011080b421800104002040345940110100300c100000d444c051010b140050b40c100d801c00703000804540c40d49005040366894 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 250167500 1250 250166250 250166263
    0x15031d0d051602040605030a0302010b09011409040221031308070602070e010b0304060b1011010506150d0b030f030c07030308060a05150903011b021506030102040602030901210c091403 81
    0xa4403540d20b8903404840c11100c190010b203060382c3c4030740c3c0c0300800a0251010320602002a100303034000103042407101c04114850406070049011121050411132490301d9030360125400c290101d0b099004410120390045810b04041d030092010700012035019058006101d01c00d05441088060b594403d41b14081240d41d40d00510401da090240ca1004110030040c4030011a04540505008504d44540030041000c4c00e0508110000184186013509900d240c28400e56400075022180b2076507001207070b003101c080790250a04100c80d2580c1c803100070b4100e40d020030a07001905c2c60001600d46891031880c0c0039481c2c9160348410b601003680800010154604022010f080c0d6070020048903000c00b101c8a151140d401100105416659854803100041c0001104410b4480705a0007010081202044038084090181446002ea8018081880099004002d8440702d00080c40c0410700c1e03141d0140c4c07c60003440b069414010032490500161452a8804070b5001070791688101e010000b1510005c6c19960b20 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 250168750 1250 250167500 250167523
    0x20f0303100605180301020f030103110108161b140d17060315060402090406030c061d0d020103050c0d0203040602030609150102070b0a09050402030c040e160c030f0915031d 76
    0x2001c1540c1485458041c0003d0034829000600300e140d42030320702c0d02003422230303110251100c04000b021004204000080704910f121240a20b4480700303034103002540d2101c90080c0380c0c140092000320325581c440007400185c4039410503000080c141061034030860442d01c0310490003020000400340054200c0030320399003110600810300075004100c000340c65100c504000c0c10140403154841d40070440f902540d0b070745000c1c0e003002d1030007150200200e41c40c20344060101050100207881000006015600c113940b0701e00703025911a02801c0124a640e140c24400140d80300e0810015a107510120900051191640c09980322b088250b0744a0140c0e11584011284085100c2031140180d000e0305d020b00c404000140a04000825420902c004c1516100014166042112015103000307002c00d04200c06080120000d030400c600d0040e500344c03030388003200c0104522014600035051101c001100310000c5d128030340103002081c0c00305461102ca180d800c0b0040181030111080403900608190117010300d880400d110f084031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 250170000 1250 250168750 250168771
    0xf030507050d06110a090608100308030a11120a02131d1b04180506030601060c08040b0c100c0c0302100501061b1412030f0112230c030706050a020f0303 67
    0x510300010000c103000c08040890f03a094446940281c10300b14580600000701454503001200380c2000d2009004c1e00300107003502d11500c02c00c007040000c2402c200859070800c0f5241d01c0070a60b44020f440b6000d04d4440e92200500c1c003144035041100c000c0c8594060141c1109450351441900e54424500c3d0900306910050300621085d480440e1950480e26100d19000785140b000314200307683da0809212510184504c040c000d6251400c000c07440c6010300c22070380034001500b44000b0020303c0b900d4101880c015401401a101c0780001c103240c040004010f000f030100c40007102441758050504000700b890300c440000302c01500c1040c1d40100c0c04003450040c4c030305071030300c950701c104095014041c1c100030800b41c1c450969120307400c402c60310748109080c040300161a003001c40b00b44d03a03802c2c40248016003100c141d00c0b000b07601101d0804240001d441d402c0a160940c249002810315190241d2520308200380400055498414418005001a00140608003141d020f40903181910350280a441d2a84402c0300e005005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 250171250 1250 250170000 250170013
    0xc05030601050313020a1d010b0a050a110a150b01021504080313020f03030409050603371a010314010f18030809121201030212030c0c040e1f050702070f0305 69
    0x1107501c01c0d00a540e0105a070324031800d800b080d43c2c02050b0171150340c0c3c000034902c20014000c03a00c462100c20206004240c200181481e2900f02e00c0d0060050065000f2442000301e04006c030000c0316801c00031080c00d9a08264441528559403100f40000d2400780e10346d9001d030107808511203074088100201232081c1d0700304441d20b156642d408200040ca103015002264003020812400c14152010405803000d0b021600000031641003640415240c0b000242c0c000034110200800e034005250504e0070000c10360022110248403d0840c07800340c4004485070350380c40c5030b100c500c0c1c000024400401c1c0b841c24074002d0f0303900801c0100d1701c904c1020240d40104000b00b14201d5001c05403000603204440056002c00c2041c01d450011321070003280710042e07021291801c0398808020040c001d614103000e41d81e008048001c000d503d400038a800042d00c800381d900481d88215694a0328072213842c0c2c00c0c0645204180343c4016003550b4909501e0386402400183c4a25005210f03580010401001c00e50f00141541d411000415a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 250172500 1250 250171250 250171261
    0x90504020918090c09091603060c0504050301150e0618060d03020307020d030f0f030203041a0405160303031a0f01050304110103060909050303090f0c060d0f180b0115030c0503 77
    0x80d50050750712035000a2044000c0c1c04003212401c01e28060b91020303003d89030201068081180112010348046006d800001400380101201d0050404036640301c180800c9010350450180c0c0d980c019a4000754155091040d18800401001c151405030382e02d1540c1083c0355100ea00c1480313000746204212904142403440424442e140040e81c0e550007d00c00d1044a160901640c0880c4115907058021008221000403c0c114203400244422050441d0300c1d04505502d480d07210071842503650307142001c00c4920b58011a081c000b042c800c111003001c5001c0107032545c5da900c2c80c0c01001806105c04141010130700984503041440c0001e043e055010b01603584e942140c944c0d8588488503420612450305065551400140300c044500450141e50301442c003540c0c4030720f0012a00d909001c2018003503c0c0c2030f000bc11890107942c1c0e0341010f680917134065000c001034011045549800400013840c240700c8080b08811400104030f01c0d0020320b8140e4a141e00822003110381004140d0644042428410200300c00740300285 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 250173750 1250 250172500 250172509
    0x614010509060903070b120106020111070f0212070e100f1a0703201f0f0c0207150306031505011a0c06040b060418110117160f090e070f0e060304030905 67
    0x180d03483c0c0003020381d9080ca41e500e00500c4c40354030800c0e100d900907540e0001088202e40a10900e10b4004050303002070710b803402c0780d41e80c14900411114000c0c0310701488207110030b10b24400c000c11005080401d0b00003005041646410340d00c40340d2441035001d0070900040106040807c0000030420490860707409003001071a99003900c140c0d00380d81862007030f40315001c0040d0703003204100010348601000032041c2001208003003070081510340c030900903c40a414030145480880d40040d0400403210664401c004a40900c001103029140f954801b8140301c00c018103c8071b103501107510842c100ca00401c1200925244022420703280d004070701c1407a50b150001000903012804c00351146600c42d000420004e03480c0c030004400c840715060384100381c505c0e1050743e890000a58014092142c10385030108014120710304414461032030031089040310208031a94142506403030203000c0d4180940070b0070b440340c0318600c0e00c048000c2000b00b2820040b000681d60071042d20f052304080007241d000f150166503102c4110304102c14071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 250175000 1250 250173750 250173757
    0x16090302091b071a1608060a0308030603030c100608070e0705030c160b24060f0d0f021905130e01060e010c053c1f0902041508030706061401050906 65
    0x103041c044002c03c01d140004204c5210000d00705401140d6408a05100300e0500403002007401c0f09003881010010300c00786545040e14a411658841450f95070313507603540046801c50140c5142400184030741c90b001510400d03e43c008a0544920f002103c41c156a9040320410300401614034901050041000c0b9600300c003114014420401e04900311911440d6603954548001011542229070b0138400d080c400c0180350785044100002002c880d0700d8140783d015111848184034002d003501c20a90f48001141c0c10844c1901501c0105140000d12100640203401c042c0140c0e10014456405a000e01c0c0042401c070000038607903051760720507a00c07140c081030b80c10b0040d607030000c0004042d580d030300c15003021598010800e4810b07454102d101b00040103141502e0f0100c03950120312040c4801940100d6141c02d05a213807a1b10484c400011500003007140c028500110f4004c0c1070486144550001e64100400c01c0f041c0000244034240c07003403500b040907655030303082d410342001083c420368006001081342001a00e00b8274040c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 250176250 1250 250175000 250175041
    0x9050606072001050f0a0807023706090b0c0a1e08040b0612010c03020901090503010e190c0e04060515010c03050a210204060207080d0207030201080c1617031609030209 74
    0x259142602824415240d60003040851000403487c0e400c0146070396040c031003201c000a01812403170b40c6103244000c010001d00d100584050040c414907102d070502600760010100e90350004684405401c003502010041c3c0c0c01400c12202181a1038200504611241c0201c601d204581d0b0b01c00b501a2100d1341d40300d0351031001820b669440b290800f5000d44840080c82107035071206841e2030042ea20004440003500003d80c030f83c020741c03103079140c90356841c1d0196020800448000c605418681c4500c840e06e0905034408146c0c000740095030446003013008011043e0701080c050341803001c2c0315000031540c500440b200000d2400040000c0d10074092581001c1c003501d0300004240b610301c50062a84c160841e5241284c11035400300380140d114010070080c50310305001412581900788050050070741541c001130540440035214000c0510002003001c01c0158406651070090741c0a02c2c400300c02c1e90305002058882e0011b03603007901d89072141c3c40c0e80400140200442d400702e076405000c0220903628641c064812100701d118 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 250177500 1250 250176250 250176257
    0x70b0f070314070c091d07031205130b030702060a05090307020117070c0611040f0608101208090d061e0b01020a060902030109050d0305010f140d06050c16080409050606072001 77
    0x1040c0000d00000300f00001e407824013000a00a200c01c0403002206d42c4480344415160090070003800801d40c3d124504902c509941032181d0b0f43c9580c0e84070240f1407a01c40d4810350f07800602109003e001c41d40402c0c814060711007864280b0164980744002034483c454454000d0100d1007440140d603050a5003440f107070340301038a0306160b0741c5140107880d001d00b030300d0008660700b0030300000040500455101e080004080c20152070801c2052910740c0f61208074000c00e02035039403110088901c69040110460845400c8540504042400100c91404402070705014044440c4201022447e00d00080303d4403c00c2412035050b0300a240e070507500d89a8000038400800c00340e802d5504d9850b0741021800030060f80090351040c0e80c00040542c500381c8211315405071600800c040109140d802c0c070040d0703101944055100d0304124001119220b901c00c0c01ca4601c68501d40101c0d035078040c4454000d001041001c0c0c03040340c0005106000c03580d610810043c0a11400400a219420340312071841900c1c034400400025290606 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 250178750 1250 250177500 250177507
    0xb010518060d06081f090308010e04020402040b0c010b0a090b0307030308180303091c090b070b101a0d230408030a020d050a48020304050d14070b0f070314 68
    0x400c0c201920240e400c9100343c2d0b400350003038010711000c5900141707064034004010010345441381d900900d062410320541380d009015602280070756a070383e4102c81c010001800307a00e540c3c41f210b0b00014080d100c801d440720b100e5000300c0f800080c0300700c2e01d026249490700d00034043c0940318119a02540c281c840070b8a1549540c6c0c0c0c20b656150072000400c0150f0040020000038a0401d450007038004080703400a40c10800c00400010402406c489541aa1321580d03001003082a2a41d80e503416403620a0151f01804001c4080000b24121130443c0c1d009080c4440441e405122518030410007501500c0b454076264598445031000a01159040d0069608040d1034000940780440300d205240607624240c0700b500030b19564100c000408140c480d011003c00c6802503244240b054034060040e600d01041d1800103a55640109201004d8401d0085802406000300a06aa410541040c1c2820940406200f03024414424045044440340095444011000c0515450502c032980c04994100a000c40c0100051007070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 250179856 1106 250178750 250178767
    0x1201060f0603021803070303050307141216020f030304060f06120f0206031003020a0b0c06070206041101053a050a020c1e031b030d050105040b01051806 67
    0x40c00d00503102c0099208000c101400180c0091749030040f000b0110030103410001071806001c0c55030b914001c9410030340c150020303481182c2903e1080c00c005400075944d55143d01c521440500140b05a940e01050180a28a1900156012603031583c03160390030101d6104034400c3c41300a000700d1400c1c0803003254a031112400360407400d50181c055040007000903020425044150f0085034050400003669940703803001d0a803900550003195040c09100b01150499200040300b0707000c0c0340c000c00140c9030010880015120360784420401121483c502409500160542e01840703c240140014800c000792620503c1049520080c28654880e00c1400b160b19a980000303503e02210407600081c0e900302c82c100000c90720718003032000d11110305482d019060100c6840800035001c40c2c04842000d11645e41c850041006469016800342c0c00208244506801c5000c03034822882c45950180c0003a00d0300908 = true := by decide +kernel

theorem cover : BRFrame.Cov 250000000 250179856 := by
  have h0 := BRFrame.cov_init 250000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 250000000 ≤ n) (h2 : n < 250179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
