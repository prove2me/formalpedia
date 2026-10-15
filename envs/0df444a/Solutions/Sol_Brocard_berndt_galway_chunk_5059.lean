-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5059
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:36:39.975025+00:00
-- url     : https://prove2.me/submissions/6385ba43-8d0f-4545-ba97-f17602da76eb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 909712230 ≤ n < 909892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 909713480 1250 909712230 909712253
    0x20406050a080c0112020c010e070f0902070b1305070b0d060602011109030a080c102d0b130b15031005181506090d020d0b18061006030e070906030c03 66
    0x14000d01c0024000d021103140019114521403003420407003010b0468002c000c006e4420180301c0301d515401c140c041d144000e00004e002c01618070510304158410707110307030038202280180c0402500008990010070410450015204800b50265051f14034103600ca142c0078040d60310240c501003035596119002c000841e82072107400396045000c142c00b031030710a10b140029626000300d5005008560002015140072004104200034401c1c680782c180032440d030420780c2401c100c0d842c03440715030b0900f4503040c0c104812035144502e060204000f020b102c0f01c244541d100034010010302c5840c40e008130f4100e040c1130702245080041c40c41142c1c880a4120301600340010702050251200c0742400004a200503c41c030400200070b5081803110555090391224142c0c2d001481c241600c890294211588224003020711103284501d500c076801411400300035400c0d000079180d07507081c00c0f546865848610703074007071002d24801c0d0050500c40300950304076641d80b1341760002d00d800c640f990381c41100e050b08113110030810040386c0d1404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 909714730 1250 909713480 909713489
    0x11030a051c090c1d04050c0f0121021806031b210103080301050406060c0804031121010b031608030d0209010e100c12050909070f110d091e44010207020406 68
    0x83c44490704141e9650751f0342d05070812201c0c0c0300310003092132405140d01c1204020000d4009155020b1407000300d460032002580020904080700c000c2000344880ea00b440e0044900070b03510700366080201e0205414201150308603e00c2408210403010001103103a8100860f0382c042c40c001c1542941d07a515240c00c000440d01c55510010910426103045008500c41906a8003200d03040a0640d03000480400024450720081c00c0c00344d00329081e00010810070605501c41310003400203404030703402c0c9141502d1803810b103030031171140010580c01040400c0007601240c01808a400041c103200d2886000400002c40000140d82c8100002c0c034000c1c03e4805204005c500c0c940000c200f400c00c1440c1116000104084940c003d10a00a00410f50741c0e0340b603010700c1800d0741710a091803d0240ca4011400c240300a00145031442513040b074904610551101e0405803400c030f01210f14144041c035a07070291000da44c40c83c16161028484400c0651034100b0204488190b084500904400041e62144184100002ca6195030130 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 909715980 1250 909714730 909714779
    0xf0d06050c040510111501050a03060b04140901090606270b1f05120a0b0d0201030b0d0501021909090204080303010509090a020d1a130b0c070507031b030b0711030a051c090c 76
    0x41041d43c60380101c132790541c1d802000c04552603003c40c02050280c4480d403100c142d40451901085155401036110980b960712443d810b20506540c0c415080d00021540200b6010f9800c40c40001c01c950131641c403541d9007600140c104040c2e0f4440d0815441200300a2450501040c80014040c09454690700726030f500188901d01040702d1119240031942c100c00d5030000071705040d61000000803a41e614a50402e0030fa901070002e40d0307682020301c040d0b94640110b421501c080344151002143c018118000e41d41a00e420074001c5040d6031900c01000a0320300b014201e0f503694044e030501000583c684529032906280a440044c85094940200040c0704400a10226120345501082d10010b2213a20080d5000726188400f1500c60b100c40c00c015080641e5035000601485001c0c1c0c100b9400c009412050044034010710065155940d1020191a2103e00001c40301540e00200000ea0325503000d000607103017041c0d40308a035005200c800818141210802c2005480400440c80100020b28404a405060700501030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 909717230 1250 909715980 909716023
    0x608090106153c0306050f030a060b061b06100510021f0f18030f050309060f040804030506070e0a06020c2b050604030807020c0f0d06050c04051011 65
    0x101c20b80360010052210800014500d11070f201a224801c48071400e00e1001c03840014070001d901681c282000d0380f0748001207410308a0000c2c1e10701d02160710b10003184000c1c004d030103030002660b603030b000074810881200d034050418030840955001204200072542e00d80701c010720b402c1c10030070100b506885556000c0391091410042840e850703035010a4244a00307402c0c40e4980d417401c09401500b40604800903440240318581042110ba8410b501e516038962402515207031a407022540d001c03119031200b190382e50403030790106000c20001e100340380c41c0c1c6a00500a00b509800e00c3d440760703140d5081c0b030f000ba0b804400092031505c0c0b0408516100c494080140032900040010b4102e00000c02c1034010040074410142c003804280798102018903299100f103a50000036118540307440d1a000c0c009100641703012005100319610740d0060b0901902c184c003841d0000740965551540c0d0382c1c4c0c20740588401081a07401d032031305000006080c0c654252012600403503131150030114000e041014580300340e024000c2a0501c8a1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 909718480 1250 909717230 909717239
    0xd18110102060c0732011a0a0611030703140d020301091a06040609060305040f0b1e010e061f020f0706050a020f010218131103010b09120625020c190608090106 70
    0x81105166030410105a0522005802c0004802c0d44109020546d5090158030000003400c1201c44588090464080f08410307242c00080740d02d4112001c01c541c1640c410001503000c00d00980b11103804540d00402103250a0000603050309a03082070780b00302c0c8040d4840080c01c8110003010203440d044503042d2480740c01d180c03800d2402400d40d50700d441802c09050f034610209051044140880c05456004500241c050811181014681b0040c40c0d428a4052036000042040780304c03d800d06009030001440e014404415a01d00702c3c1303001041c2041c034150320038401004140380c0b042c0300d5100100600d48509d0788a0b01c51030f102070308000d880b40d451240759204004002a9030706681180030645000c0e40c0200b5560344402a0a000702034580012819810220001444003445802000007607000d4415801302c000a0b07010950318001a0780500b02c80e1498400d803000e11003007040d110b0b031800240c8100d9641c000405e000c11850034140d20640b00440c480c90041c0010b85e0044c2034942c0110110f0000c11080380340 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 909719730 1250 909718480 909718493
    0x110c0108070e130908030609010b070807020609061201140f03071212050d14061807080604021e07080a030605010212070803040c05100f11160b0d18110102060c07 71
    0x3450301c0305009410b08145070035280d00b030860b044041d01c04010003030f0780d40e0390a2040e1240c1044541500c00c000240000c12801c4070f000585c1c0b4100d900424a504240c034540c00c01961390084402d880d004813080c421007040e0007103460628001c140035600018001203241c284541d8512071003141d4004e9006a404114940d00042c40650f550b401105108940f203d021086400e4850041c2d400c0d0141c1c20200f110016100d084001c0380a4036045644003106151460607401c2038034215030030804a511000050074a040c550010840800780d88402648600344c0007444041c0e8000765000d44140002280b850b00c07040e0944103600241c80240020011141183d01030b80c0c080c4074815004100c030f28040702080411400648000c00750900506d00b4031401554140106401a881c00010004114041c02020302d203011400c2044003a010180101c80b60401c808440c00d540498485211259907208c044004920403806130220b520a4040801015070440024a01100501b03088000c2e8000c1100340001140c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 909720980 1250 909719730 909719747
    0x6030124050411132d080c0d03020325060e030705060103080702030106030605511302070c0e0a060e07080403020111030106121508070b0d0207081603110c01 69
    0x28215004503541060709003440f0240200d454444a50304410f1020900d00a642c00e82021050b6a1050f10b00140c24082001c1d44143c8510802a990708560022003080c00c001258400040c0603004592a1982c00660302c644801e80c0261003a00c1d00381c06003410100001c50041946041d0800001c5040c5103140d12069164001880014100c2e580040c411045460a4010200950308400b0402040c034140980180e0382070034004444201c2584603a80000d8201c0303014880b141c01c1c001503038040d144420221407401d01c0240744040c0e40710540b0581c540390344015000070700e038551207803000600052504150900c0c100c00600014640d500785081880b030240a1500e00341c0c40140c5141001094646041c185e00400d04140e03280b24004000001143e01500400130140c54a65003600300b12440c2030000e02001c000c4140510310b00c6401c24401000141e481002610f144178401304014580b1050340d46800e02c541c01030b9101400701d9108400f1209040d048500f11680d090000f000c4d013110f9074000002028201f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 909722230 1250 909720980 909720989
    0x1b02010f1803020a030c03030e011106071103070b0721060b0304080d0f0e0115121208090f030a021c03090c0302210307060203060a050a06051207030b060d0506030124 73
    0x100858081581126140d20307070009640140c22500c0080c3c90342403281c1108821f020a5010400e400c07550342d000d5201d91060046211400041c00007511200c508a03400d82c40406090300c0d602c814019030000c695000075a82c040c1d2120346448071618420444100811b900301c188960041c43c018041083e403024200f1030f940a81d028003080e654005480d41c2600526032061842d180c41c1c5030814464600d081540300d24540b1403003041240045541d071800e9100801c150030024150310b81e26518070b107513a0098903601d40081c444c0d0113540043d04450026451608a803d504005034842c01c801160f1407032440c0000101000e40c5028801d90100b030b103400050fa449840000c0c041c41364809110308250340316961001c103984804c2520f640b4951401d000300a908142c030454410020400300240c6454080c0e801d4045800c9030705e0b4107041a12a100c403a4030348000509460a140d1501400c45840d40c0d044010708824540c0040044c4508240c1e06250844038180541c0c3c15003082d03601a5441d003146090f4003021107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 909723480 1250 909722230 909722237
    0x124050906060325110a0b0411040b0f0402030c1e0a0305010603052e1a1b0d0f23070303020a02060f01210503040504150311041122050909030a1b02010f 67
    0x14140001c0c11241540011070407000b1b4042c00c5203910400a0100c1c501d801203010b03015202c0c0ca007803020f080204496813040090307880f20120b51640014113068018651000c120003d050600d0a40c560301c1541c400e5016520440e110002080c4085070780500c01d86001d401da600d4200941c0c6058603109c1d80503851400c07490102c00c1341882550000e140010200064407800c6007a4003148000001d80da0070390440c0260742401c041584103a000103200080540d040400c03569002d00103200340c0415640d5a2840e0354094150001e60b80b10a03c0b81d041c1001404d109100e030303800580d641c0c1c0560b0004d0510f00050082c901500500d40100214000c04009100c0d03100ca440060300002124a030040c514445e69005541040c1001d4030a81c49584445040c02264001d49401e0301c079294100c100000c5800c2410f000820170005e0005a0b48082188004030283c44000c0e458008580c42e02c00007010716004603074855131540001003c9054a500071100210b40b01803075103095008007141d001030911141d01d082c0a041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 909724730 1250 909723480 909723541
    0x18050f0f04080304061d0c01110604121209080304210e010f03150e01081509010207080409020903030d050f100803030906010e060105160c09141005060c01240509060603 74
    0x21700c021944000e00c1d50b428100503c4005660001c110389949810710498007064801080c80b640b40310100c0c03058031840d031282105100d0b8601c0542035443e280c9a9000a600035a51700b2050005800034005600850140062002058080d0321074411443c154065808000300701c0603c0025903003140000c09680f505040100f045000b9003040c24031051554420b0020543c01c10000541031b50201320580c0d6800c030380c0440e1581e5070f94440700c68242e10a959000300203000400c803c0004440e5940901046903004065920f013501795890030098810640b071039013110a0440510036068040d0b00000d000701130b080059411460308940554944a0500c140000b94040a0000b401a84142d0444440500404018040e6513203410031a070f14000318000e905500d8604220050100f03d00040c203441840c600d030031b6500d42424a4240f0900f07411540740c001c0a90f40311986403c800c0905000784070300c18016030100c400c1515140070400070001c05480d00b80101001c20521030801101c603a150381c61400e0f640b00ca144d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 909725980 1250 909724730 909724733
    0x2030433021b063c04061e0c030b03101107111801080d090e010503031602010311070515010e0601200309060c010c270e190618050f0f04080304 63
    0x1480b1149010320701d0b980c024601041400050520181c590382110060a03850030820a241c2100744500c003408030329103482c3e100080010382290000802c810010702e641800c2c542c111401420740c1d640c120f811001c00d880d04005200c60400f0801c2074400a5541c1041c00313100c103094442d140c9031144200103041402106081c10054072079525080b2703c0d000074850f100c403a42c0d548001c10748909446824000143c5101c0d800200c03c1a8243c0e001e040e0341c8020301a40c500020f00c01000c5d0113039800300d012070506446007017681043e00004083c09c1902c0c0150040d05000a00407662144090140c1200e503030a10b1ba00144151a6440002120082c03480c040000c00444007a13030192450040040b0194400000184602040c1c019000b40f503191170302d81c4031400d07040610801c02807680400420f1000c1c0b522036210402014100c521321130b40050300d9884020078400307100f03102c00944034075400080258100079003844460030244605036000520b40041a0b6608203400e016800600245c03000d40703911000700c003050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 909727230 1250 909725980 909726007
    0x7021531020a03150e010507171b1b070801090314070305040503030f0909090a0312150b0a091d0f010506030411030a03020c0a0902040b03130f060f0203043302 70
    0x36036898000344101880c03940c910740f4842c0c1a12802c20301d18143d050022906442d901405080c2c05068561200c450070b9085150b074051520004103d13120380b4102c0f0503031274030b102d40d0003008107110851500403102c20340c021a0520b140207d0307540300342e807180c0c9420050808030f03511040341000c2204003500155105054103049803240a581c200315494080000d1a0445c15a40002032000383d4095501c401d00382d40307581c107860b1101c10064000c0c02240003282d0100c0b0301210b903800004640c84000b1a000c0c0c17507413507011549081c0c02000c1d114011400c000000c3c4035094201d5580410f0000c610540301091510a40f4014601010300c62540210b0000c00445c0030428000201c270018680a021914980c2d55818000e50300c01e404c1310041e0003081031120104041890340200d60540d508080461310b103444a600e9200d103401c405005550a01c4c0c0b0b0369418001840034022043d00104860f0007507144d06081c20040301055291a41581c0e4145040b4030705175860302101c1782444458034080040e01d03101c0080004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 909728480 1250 909727230 909727321
    0xa110613031b0b070503060922120c0b040507061701080304050402031314070e010506120414070302060f1c0b010c0f060e150a110301080718060e0f070215 68
    0x2400e0f8403911082114440c1e01c100914400c1d44203c9141d0001c0c1c8603c5618051580d001c80c0d41c5606015001e510b0000ca241c044000c0b41402c0740c3e02d0030a0003185203844580c0d0f0802c0a84d02211a600020410821503030b00c42d0a04646000b0031191035111351505110300c0c0e50b880760b48951802a0380100c0004da003442522821503c0580040c00052074000ea211500c0d190000c0d80503180b02c002c070000002c5410b083c4117059402c002208400c203005a125a03ea00c2045c4040c040f0301c611724401ea14000c00180c8980000c0c02c03102d2925041180c840b0060003911281826100340c0e0f502d507510f00940003c0384d0781c1c0301d200c00600356004a1040414800c500f0414060090fa030720104040c40780241c0c120180c0c040d880300c03a1061000640c20484081a590122098442071013920003981c00100d05001c8400c00c110109070f00b000700ea00014409aa5000000012104035610310445042c0005c0003003154043c460f110240380d18845100040c40d141421804582081c025134081d240c940714035200598880141 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 909729730 1250 909728480 909728483
    0x61005030103140111070302010b0a0602010c121812050703020f06040201090303111615030b04060312050a051201141908060c16061a1f0e040c02010906050108030a110613031b 77
    0x45681b00700e1410040e001e0180c4040c4540100c402c01030008401d0310610541e807203000c29a60340d00d02e19028440380c1c0d010707022050461442c0401401c6000009a800c0c00807000c800c0a600c072140c8414507401c010b4107100c000c3c0d00c0c0c0e84240d040078040100503a0701c0503c50069039454240080c402600810103131400303081940000600ca0300c0742c408203c012000c059207145401c9954140109160441030000b5901c0c0c610008100c0c4600d1803c1c0350100d030203940074101c0300d030b031500c0c0075420407804c46a24000e0032000c0e031140c0c1e004c0448070071240c0142041400140103255241260014924100e4101d80c4c8030001020001c3d08200403d003110005403000d4804026500040c0a0203803540e0141000c1038001c80004a80c03065003450254038a00044440c0c01c1c5a0303040948402c0c0403030b90040148000380141c0d00000c4119540c44c0c02d110000b138101c0c0326103406042408011501d0b24034200019080c00102841070080b41d00080800808882e040c4484207055814506084c0c0e08180300064003d0360f0708e6010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 909730980 1250 909729730 909729761
    0xd15120b0f071e110c0307030c120503070804031b08160915050603180d020d090e10030203031c180c050f01051201121106090906090411100509090610050301031401 72
    0x8003510f1258004441c1001c00794100554030503080c072008050381c481d42c52200900c0481203030f10820402180c880005e0b40b050060064a1070000b00b03039103485055005800844c0d13621301d2542e1001058204c2030841020704483d5008200705072542d21600b0108803d440742040c10ba840703014010040c01540118002490094000d64490808404100403c0102c254030101c1b88151440c03000014400038164403041001d441d265240d900302500400102d02c000c10220b40702e52040000070060f241080241003081400250307541022182e42d0395400d42d6016184141c02c0d078942030440c00071131410300942c0c0c1200c3c011210320103c802064016a418051400a610580802000000e10204001110304001e10410883c180703250f0035010004a402500005500308110800045144c24a14245908180200166203030000c5070000610f20b01e03880f4000d90b00103400403503240d949007800d02c502c0350420703400c4a1300c0e0b010f144203840051881c04144005412410010404200c048081d80701e000d4416a590 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 909732230 1250 909730980 909731027
    0xa051311060f0d050a1109210c0a03060207060501140f0d15090b0702070e07270812120606190503040807051c0f09180207050705060d15120b0f07 64
    0x9480f200401040340d5905505080000f00c0650300707583c8044600000006004082e10840450240f01002e0441c242103c80e00c51080c41040550b1401c03858030085100310005603a4800038a030050946006a011001466603a158183c00d95038142d5483c0c0e065005654401040700c0c9420600c0d12101031403e04225185804025002e016801c070049200717040a03022201341554402281d038000f05c08407040e00010f4485080314000340300c415220075808260041c0112130b00e03240c40f920303030034084c00d032020659030000050340741c81489041c0c2446a00c4001124041d060490344802d0480b40764446021034200308001001508011100701500c40171070300442220f021a400c2c0c1400b14800f42448281d0b40030421580c69109494403650f40103058a030340280b0300300804030300d40002020750480f0f10120391034040d29a02007040d0f110900074ac10740d80100c100100c0c0c644507a03001c030b40444956410801e25003c010b010480420520b5081c60b0700301501912494069079240c00844007030b415802500d4280c0f1011 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 909733480 1250 909732230 909732247
    0x206012102061e0909010b070b1303020a14030306011202070f0b0c13030309050405060609030d050306310c0c0b04021306091409060106020d0c0213020909090a06050a051311060f 78
    0x200260440c501c0c11713152801d1590703c2d00300401c2240035102c0002e114903150000241d40c0481500e10000c40e51190049461402c0107a80b00181080c090502000590010080024660b403290319903650f085409800c51a0400076210003941800200000e0011500701012407494800041110070100301c003800000d10688034078004051101501c5490701c0385003410085001c2d880c10b6001c980c8084001401089a404c0c054001c3d9026003004000b01d501c11030a414080c990200c10340c44100b501c65140c5084030882d40302210508030740d81030148000300003551072004002480d04030070580094044920541045003081d030381e00070301019009260741d00e09018030f41203074010803441c860007004048241d03040c585e02d40e03400701e0b513404c1c070801070000280b00b130007210000d03040511021b0b0050b003902502615000c50100429684941560300d000e0b40e9003c001d441c42480740d184101904100c80d01400d00c03090401c904c080600b01d81d4003001070b1607a0500c0036080043c2d84d401d402c0ba101c03031004040f241d850b01d602 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 909734730 1250 909733480 909733537
    0x51e030307081210050f09150f030102280203430302031c110f090406050d050a05060109110904020903010b1e1e0d2a150f020601210206 60
    0x144d403448495503040c1c3c03003c030341e0389420500304a03030980240002103581d481c10b001c10149185488129080080404002003e071421300060102010030508042100700301a00e010024a1400000e01190005d0060102c40d21119210303207c0801c0c00700518810700340380c10543c14200e19030039000641110403140c1904142d0088040e154164400045d1440e042010b1403400a950024029181282d410800c0d980300011500141c00e002c680500001113144d15240401c000000d2080252200d074030846a01e01082402c001150142c8000002440319059034141d422003402100801d610454011035400303000d8900b5407122802c2e200003405242200c00c3e41450080c010488441140101c0400310080c1e0403040d00b01031110440000781001c444584140c5171007207103402811202d4440501d41c09911620303503c80c8a080040c160078410001400c0c01c1800103091514000302c084190b4004c0f0004005038200d10300720305031206070b01102c0c010030035081c0b00207940341c81224680084480c824034220b400941 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 909735980 1250 909734730 909734767
    0x10181d090105070c03230c0604060b10030219050705100c0807021608030d020f041a0d0b1e09091911010906021b04270605070e0604051e03030708 64
    0x4000c001c01240d1a0341200301ca00913a60880a00480c111500c03050700c00010b2801100101c3c0c0c08180c560422410554450a00b442501c05072a116151000103205103030602503410b000c0c003c0d0600f1442d1504980f50300144078a00d5866200388a030109200041c01410f10070720f5402c8880e5102006103240300c00001d0007480c41a83c1c0640148a54030081d0b9150141040403002c1e501c841000390300b451155030031035000e54840d803045c2c0c4404c2c005000c00500e9402d420382d82d02c58040341403d61a22101080010421140320705035143c030400b21070310350041283e491112502d9030b60b010344031068143d40764203500f49003049016941c0d08140d122030040b028414928001c02e04c40000740d0303501c10f6190359490200e0303448105804044181e0070394800e5508619280d8000c80100440350744800061400902d0810308028a001c241d80c120b03261010400c40ea80c2c8006607a4480008641d8071703051078180808200e449441c011555410200d41180c12603075903082042e104d200c2c0e44400d2040e650b1490280c41e010288 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 909737230 1250 909735980 909735991
    0x1b0308182b020a1104020a020c060c011e0b06180f100203030108010501080616050c0a02130b091602120c070509180c0f0d020603100e010815090a0210181d 68
    0x58011007030101c541c400700f03c0003c0746400c9140380c00c40e040c604040000950041000106510810050040b162500f401502c2c1c2050010000108804806108900c2c4807100962155580c940b640c014002c5da11182501c6803002c1804280940d41100c501007401c40000c00c034800c1d032105100e84192a1141d0000045041c1c41401e0002c2c00300766a82e40600b07507241c0c001d0300c8808107062602c0d00c543d0304510a0018103031905600c0c0c2100c54441003a00400d00c0f5450304140e00c9802d903210016a1541e080c00401140c104000090030349076640b132020020b48418060481094025001652400d500401c100d504013a12005140002505119509020140c078515103d40c2c1405042c0807943d003460b10f08504219060302034850f4280000359401c1000c140c1c001072800f2030b4500d202c40701184000704201c856010b0401d01c00103080032500d0490400b4000c60080c2442400d51061607180c006845400940103540722a040100f290754203004a07500c0d107082a013050344244014074000d00b04209030f0030700b540141c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 909738480 1250 909737230 909737293
    0xf020d020d1103090c061303060f0905011401080c01210f0207031b02090105151207050901270b0f040e0a0603030816080705030a0e030708040e0105011b030818 70
    0x300c002c1101800540821540c0b69629008408149075906045005000400c1501020120b407230b280d40e5000200c0c1c0d0381240200f4115503a4416038100a82403080f00d110710940365201a9640c508039070241e07540c42c111340325070420250344010220300e901d80780c1000c4200701042060154000112840c0029001200b0950003d0407410108004554003c03d5114031500500240b81581c200b40c207000a0740640c41606600e5803007044441004c94041c417030540a42c189550f074580e04c2150f4400102190a5200380b500d01c081c507207140b003003101501c180b00001c50f5100c0310781903292140300211000030b015a60048907440b0325001042060030f200c0d072003403040ea803103a1180c0f8866103d0450b260580305c0c2c0c504004020820801c041250b03540146c0c00b869003c54060b0002c41e181180300f080364155084038100325400707040890103000124800c00594050702e0700f0b00e04080c0369540448880c040a41c1c05070007609120142e0003190410342c40c071420078821f200362400c942040d007416030120565103402c00090041c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 909739730 1250 909738480 909738491
    0xf110301090b0a050a0b090d141501051f080417041d0604060b04050d230a06020d05060906130203060609040204031b24321e0f18040f020d020d 63
    0x545c50240340103030945020346c09483c140707103070701c42403055100c10031300142e810080810482a00c1c1324200044202d40d01200196407417545014180440881040b014104184106011007140c41c2c0c04190103034803c0e001041c803041303035002d081d07420000d200d640c028803460078401036030b01070301d240910b00d940c0140c1d01950700f0010303680d507052903003d14040c501540c1c0c0d022041910641c00314040c0c00d5055010300940320200c040c58038103c2d00e00c2c03421660b058125482600400c03121044881c81c8101c079030108040d1807030382007131515600140f11102031071000310240c2d0b80800410269111242516800c40d4080d10440d13585d0b80b2070918514051080c03c1c012002c1070307031000c04110345041c000384100d079201411908404140407402540c04010700e00112010001c401c0c290350342e0001da1400c12308600014006507030780d101c816440c071404c0341500c0442001d0700002c0040b61089008a411212042844107922400340d8040300045c01031301545588003a02d50021a0740e403e078030381c981c1c0100b1010304064020041c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 909740980 1250 909739730 909739739
    0x8041208010b04050105090307270506030a02010f0c1511071506030b15030a0602120906010605131a1b0f0c010c08030a021e0c010912210f110301090b0a 67
    0x20030040074018031038010000d01013005194051000f410342c0140050913140215100c041e004410070b100c01e100c101941a0300182d10294040c0c0c80303403503003200d17080c0c01a220402d50741c1c001a00742d1300301c4248a0308004c0c40300a4202400919800e0105100402c4c00a220b0400c1070100f4007140d400011041c4c07405001720300c1407030500030b66119070300c11640d026200603804e40d01c250000402112007015560503008107010030f0000340451008260040217641180103500303000e190f86151404c141c01c10703003d2100401c506182800400d01c0041110001c80008407480c403a402c010403107010b8801e030900e1000c10702d840344007084000724410414440000032a000e10a0110045800140102e4054541502003022803141c48440d001040403a903c580c8000070a4182c141506031584000800825a555500d0280030012007880840301105185800903c0c0d03484901041000c010248040e1230003035445441d04202503840c2c016a11141c40005255229a0b5030f013070f031700b02a0005100c0b081c440c0040000109 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 909742230 1250 909740980 909740987
    0x1906210e06180d0804110111060109021b0d050d0f06082e06060c060507210b0f1f0e1201020f0d060914070309020f0a030f11010f0c03121407080412 65
    0x403410fa166039151071150b101e070703118040e4034017820081504205840c0d501c0c030000381e41001000c1c024850a0801070355034407019035076070660b0240701c41d18046802ca50110004a41d0082c2954902c3e0f142140005015881000c04002410303180c2c440720f101d0090300340712000c0019440c0711400c11205400c0381401c02907800040130441d9200c2c0104000308128028440204565500450780b0038223600b040c0320420360443c1e0f603403000c0525540070081e544d01da0903240894240024000c50181090760240e0505ca803201d0486039408640d88200d00300700c90440028460368840810302480300c0309000842d0f0310b0212a01e003c602e0342c04205400d6016040800c0040e0011180c440c034a0f881d440802c030760b030f2681ca6154040700030302581c00f01640c0c012007101e907103603040d600c0d200700100842c410307044603108100600d4207140c50790300b0281c001e0500c20b000c003c5041c02900404c03100d01c990703414a4024a07035050b0880d540000c09000950360000c80060041108461b04425500d006070702640440d11351140804084 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 909743480 1250 909742230 909742243
    0x9040b16181a0412140d0206010302060f030601090302060a0908060105060705060c030c0405130b031501030203070b1c1802030f01020a02030f07080d0c0503060f1906210e0618 77
    0x116001034100410001001141008041d5482d8901030320310306070765401301c800001015079080d18400d130751001031800c48008001c1c0c40508003180c0054180d135803440d00010140d0141030b04580800e8400000100e00d42e2140310801c000c2c503401419151144d11903030380101401000d02414400d4450b580001c0307040d1a01030240e41c03032607030b0107002484280c0d941040d484040d000513244410010041c40b000c907090b61014000005005c0140d8001110242c4404162500d40300486c1c4c0803120103154018405600d0224851081e04c00301c0c20f695540e42d1401c21a0550a4860030a140100e0315003c80c00e140c60803542c8020742c8660081b01140c01000c9101c00040c00c034819408004056401081141c0c0c00720f9a40300a00388060082d1142c508001c0c0503020b8400b61408802100009000081000080d242442c00300104060640e03001100d20a80501104c816015008030b8080c001c032144007800980c1644524000c925030300704107008a800100040340d48032015030318009038109048604d4149040001c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 909744730 1250 909743480 909743507
    0xe01140315040807031b0602120718031202031b01021b030a1e05121501030f0c08040605100f06020f06061c0209190606020303060f0307080d1d09040b16 67
    0x101e8610b511566151030496012440441c18040c1450000415400f0003a507205070900030344004d6035441124241d0351945500600301024451215480a010400e0140c80d1082c1d0b503100ca240d060305a6040c5050345035003c0c03003c000b08501c54035050f1b4140b088040d00909140d26071000007903203c040c0c41040d0398480c01256050700001c3d6002e2140c07403000c6920a01c0c2d00c8500820f0421919046081c0180001e80b9000c56811700f24a071511000070507075034148580b10a022400004112403e0449401041d91001401c00760140342c4071004240002030190341040200824401903404558a24019441d40703080321300040103004840004049040079140c40d0710000c111061225058226030800040306000b6100d1616400c00300902144024144120000b81c4074580045450349050340800030300c01c45980290303000307030080d03081009010300005099090700a10b0400d0900483c40728030700c41c0d10b14624a5030030b138800900da00b8007080c0030840305070501440c1005c0c0c007210047c4010405072456a2a03140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 909745980 1250 909744730 909744763
    0x5120a020112090c0e0f1006090b0a0e0604092a03050c0d090501092909030403260f030a0506120a08040b0a110706170702010e1b03160e011403 63
    0x41000c0300b080039403040322014420b51240251584402220000c000300312901200300040c80709000340a0403d0301d480e4001d110368500401ca41d42401507400d228042c025020050002d10600a1000da98201c2074038040e1903034040400509840c40180940c4000304051404034074060400440124400e015561003221803101481c60000020b007003100814440d1001c0d10b1655036080c1000000ea9820074090b29421808890201d0003201007040c144184081d0840d0183c0d482004108000b5441126028100000d2910100d40781c603440b060840314032562020420740790340001000702868441e071195004100503a01c480014400101c1142d440c04443c8014290701000c0c0420008544401c2c002c164200861030030421803141000c51304d1400401c0e40000300482c030b958036102d800810107080c0d5507203c0d510348000d11030360b170800402607121500a00c03100061342c44885803d5042d202000301e4a20080880100c02ca05961485100840a028095200d2051610300310a80c035142c001404030341c101403003a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 909747230 1250 909745980 909745997
    0x702070b0708220f08071d220f06050708070e0904120c0803041412160201051b0f0706020706170f150a06050304030219050604240207050705120a0201 66
    0x100c8407a119000031008040382c6480040c01e008000781c3d444038000401801d2040c00c2401c0c100090b0500300003554009601490100440308080c58007500d010381c201e9800340c5509004454038244038404440c08901518805160b941c0c0000c0000b5544401c0c4224582d80d544062501c4401046620818511040380e01401600200d030104000c0004511800746500300300051880d182d81b0800c15800480c2c0946291018011407680a4001d001c451401c00e0103d2240b442c4c0410510714003104d074603a6034007a04024000c240010300343e203e40050f412101606081700d0540f8050100569a66500e001c0d410050042c04030016600d4041c600341c5400c08007004c107141c1156500707540003450860082c00300b80c003681e09441041c0103854198600d4040d01c410313501e82d035a901c1c05080c040c0c03a10310079900344203000c0924061000030401c0401d000e50400d40c0502410707041c00b5003621100b25420034510801419200080600070440009692030031140107032030680c40300401401c000e03100c40340c1071000380c040340341003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 909748480 1250 909747230 909747233
    0x71706041202010b0a08010506040c031e05070e04021911071d060a0e040807140d120b0f04050c09031c0e100903060906060306050f070509060c210703080702070b07 72
    0x904101e400740e0303a4400000e419030403000140440c1c00b1a842090b050359100c050041034101030003034110074006401e042c04041c1032a5511070007100c4c48405d440191b0b0b911404544440d100300208443d01c48000e00c2591202441116440a134030314040c2c00c404180d172244003010390381003c20854100c40080c001c80500f24403044411000083c01000725610501c2c3e41000b042004103424003e001b18000c500082d00c40f8490303d032900d401c001c050001050359100c0d00ca81c030741640e4032050300b0038201150903001c1000c06121000c65424000c05c9401d1b0391103403c09041080c0303111910301400309200201c003107132008003145201345604000c01c100c0c0700018150030040b52550070180c030f00c0c141000075840c1801e0303100e6a90311510200c41c4031440445000392911000c00900040c5c0c090380b41c0204141215845d90308181801030700d144a1904880d00030301b008102480300707500c14800304600840180080c00790500441c000300300350303000a50807001314a800c00481c1510744001922070645980b0701000c2e1405009 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 909749730 1250 909748480 909748493
    0x40914251a040302030d050406110309060307120b030615040f0b0d110d050f060604110921120f0c0f0601030803040b04060e0f0106080c220902030a08190207170604 72
    0x400c6040341d403072003004000010789040108000c000303460ba81da070345c445081a5008048110501c151100d43e8020700c03441c040782d6183d5081321340000c0141801c104200110b4060805025880341da250b041c01018100814281c05459003861088101d8080201a000c21580790485110130410f0750468480c42e00940007900c04c022500c640c500041038101c070301c021a07507094540548107500c909640c00c40418800b2030705290040c0c84000408036152418010032030007040d0301910a01845d442120302800f081c01103041841b00751400038038000306541d40d05101d500b400340341e448042404007502c101850007664842c0442c90f54185c0e644030b0110b038655151611002e00d101c101070030036200c507513554006403010081080b120340b41e000001e0011810914020120781807407603155085000f9401c043c203855162443c4480c6180400404d000000c40d00307910700110345440000780005000d040c0c0061900c51710201c20500800c104244d80c02c0b10815900c0740300b9200c060011214100e82540b00801007000504c9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 909750980 1250 909749730 909749759
    0x2060c1204080702192c071b0809040204031a0c07030c03030c02010617160e0601090302130e01020a120f02040608060108041410140114060a0503041104091425 70
    0x401208030300150f07140d1500110708035800302c520b01400f00383c40c540307901b5040e240850400c400300d0304c18110700e00349202410f8007607502c401160403e1840406010480340005130b038682c4001070021500c0c1c43e142d141035100b0800d0149103045003019000002c980b0a6540225423145070301d07540da10ad0741072040d6410b070090310000324008155501c0d40c50104200000400f0003411007104002040e0050f0203880300d510344105604030340c000038680d070100841c81c0d070001030050889a040d9500d6040d521360010320b40003801c898040c0c0c440e5500001d1302d0344043d9400040d420034003103440300c10003090303106489410403841188110008281c0410020b49598080c1d41c00562007030160503030800d0082c80178505400d14100c5032400c0b07602541c6540144008442c024202e01520301002c194161800351000a40e141c09203c9e289000c200300040000c0811aa007650341300c490001420a01c200c02080c07a150310509520340030383e401445140760307145068034048401c600442407040a217003014107109015039a40b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 909752230 1250 909750980 909750983
    0x210f04051504090504030c20010212070503070b100617040201020d031a040903030524280803030c0d0c1716030e030c06040c050904200d060c0e0102060c12040807 71
    0x8006010008003c0d0320340c003529110b07611035500d20321140f005240030140c555005140860554030091011920f98002843d40c01c201d050f00495902c451551070300a1645c450658010403114480301842116140015980261841500c800760320140c2d100d49440c1e840030448010780180e00820848500a0180c0d2190b60891907442080c003180c0c1c010320120782036440c1d480088000a81e01c400700011410000c48280d051240050101d4031000c90380c00180c0100e040d84040c4042c54214600498408100307600034008200500c10799072039180260a01403590040b4889420300c81c00d01d426200a01d00c00e4990008040e0100400c4000e5200c8030901c0f501c0313140c0c00c00580705041e5541213402c20140f00300054602040020010040d51801d0301d010030b2505c1c8954081400b03028403500780302c00604418680924100c20b60300d0f0030250029207001900040c0960703000380116182560206001d9485800486134000a8003198110340718141198800e1150301810b070341d488503801c046000548250014181c3c40d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 909753480 1250 909752230 909752269
    0x10c0f020f03120a1d0c040b121513120905040606030c050d0e0309031603020310090503070f02030a02060f0d05181905030f030f10060503040f021c14210f0405 70
    0x1004420b00007800b800d4000c5c54164036409410241c41614050003000c0c40350030141c494005d0960380c40c2d1407999505041c01e60f610004181c10002d041c0e503070003840c24a202c1380c21050408070f01203c40c5002c1e01c181c54074000c0038062410140c021504ca406802004044081039807814503040c8a000c1c100014078800f100a04540000c120f041041e0b40c0c2040107200f00ba036614400d00c030740d0717281d40304040c0390a1021066038021828402d206012690200039240b6a540144042001504520019043c00003a58000b544034401042c820108403040e8082e000d003043c620403c014940f10702c0121310390806800c1d030b881501e80c8400b201c0014a071180701c1c240003880c0301d602224106589050000b0150304111021041880c14908210302c070b1044148000080c0550f042c50391940c10075449000c64050800000303400303020140d00800b150303841103490412042c0c0040d40c4890010071a00c10503168040303064030180d4101c04851030141000f1000072a6246c603411810300b07103803071302c0d2070140074040c003254540324150b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 909754730 1250 909753480 909753491
    0x50108070e0a0b0c030d06050a08030405012601140f04050402060427020316020712020607060b01230a0e012d0c12120525050c010e0a05010c0f020f03120a 68
    0x480b003d46000d0842081da02d0007035911342c00c640484400315020381e07100c40d201e0340c00313010100800c00c004011202039400071701c5d01a00c158200100d1100e00188408103050f44640d6000001d481000990301462080c401c0b0354601207482080c0c100802e98406407006907001c00100402c00003c034280e000e041c0b021207a10400c1d0403012284040100301e800486d00440b280c80100480d0031030304e9040c0201e42c00741c0055000b568004400341c001c611140a0300350010709403a5a80800541c0c1da00540041c0e61529000440c1d440420101c16484031a8001030b600a001c1000e41c1000b904075030040f01c200e41011649000b0014030751003800180406940704400c032003440355444490010492040710020850a0303a2283c207440310184207507401b1a1402400d00d411f00481040c3c0300d18640103c051200c62506500c3e0041d150843c1600143c0103020079a23035406644910060b040400c00190404000c101d0140c40d04c41290031400c50030398552031b001019002d142c0040045000da44040d00c00c3d103821120b60f9a00094 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 909755980 1250 909754730 909754739
    0x9060a090b0a030218100b12010b0a050d02072006041802030a0e0d0216140d0f05010f1503060e06040330020406021e07080a0602070609050607080405010f0501050108070e0a 76
    0x610080d882d08111545c2c00b86042080b0208140d050000800c00d40c40500c0c0780412800c00340321580010b014400c240c0200080340c99246128400383ca91020300711404640e11281880c040d01c2c81e1010700030350301940d212001c066406180c610305590440b100c900d403003000d000c0c41c10110340007503100514003015030342d840208a00100007003015822010040d001450003051013090ba444a05c2194001848440c450855030341075240c0c1c2c04171959040d40041c02502d25041c80c50510701508601c003101400600d850385103d054001b00103250210790244904001c2c0e184000074640d264042158040c0100d00303041580c403400e800c40062402c82403200c0d4940040e80c0042120703002660701c1603000e400140d11160301448641e807002d607500b41d07101c140b00c0204886480c105000380c07038045507000030784200e501040b404107010282d0800d90000781d1100a5840c0c901c0c02c04800382802c1c0082d10141e40039843c08080c2c000a03079440c03180906803030050b11280e00e01e50303031550206c82c0c003410b4050b010307004240840c000a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 909757230 1250 909755980 909755989
    0x11030c0406120914060703180f0b0a0b03100902040605030a020d170705030d0e2b12020d181502031e0702010b03060a0615180b0912240609060a090b0a0302 68
    0x4132812507803000341000d810301c200010b00b5542d001c150340f1459400841c404000a00704115400a0344d4495060710b042c2d0349545022009189410a0907014020340070704250300c010035481001e000e4400c550170403180f6111424180e6406c005a40250403000f500a0b0303101050303403002006001074441204510f0072071107541e02030841c0c100d401221000c0b9100c1c494060907a005110641e460301c116605100310050342c01141010720307a420000428051a075590444250840c0c0440b565421101c05c184403600800841400e905082d41e81680d0704d4003100749201c1c034000503000b22030040d03c000350b80100c40025940441400386010745054150341d641c4032192255181400964490040d201b40083d4640c507019504c60b031403410803400c00c00c22404070a080d290686242d41c220588070818006516180300c0000300c0d200c2c2001c4806050300340b1400b0043c0da51140c440b5120049681e4220180341d00b6100c0d001801158242942c0031a440a960f80303007404002880d6011000ca504014140000541ea81e00460f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 909758480 1250 909757230 909757253
    0x6150306210314220e06030303160e01030b030f2d03070227040c03020f06070209151c0b10091109090c16080301080f07060206010308210a0f11030c04061209 69
    0x70000d511084c0804c2000244e040c407000e0740008140c000c0e600e5840c0003400742850f43d024032400f00900c440002c0c01c0655034441c0e80110202c0102034100c0764030300c1c0400401641e500b50b6910701c0400f5030904000703000040c1000748509078084020011824901c0546c2042014051070004181c5100c01090f44495030032400c44450041d801081f51002c0b050031030040c04546d1441229141c060ba0003000800c005031100b0b4441c0b6030140c900c0b1410344584103584001900c00034501c0800010340001d441080610946000c4940925a6800300406541d0307074608420503030303003011220f100112092203042906d05202d19580e80c000301e036040c2646001010640a82403080709242070b644020701000600145408100c0f4104054410000b03002031440d104000350741e0903050000402290740454200401c1036802c0c02e000403840c1c20298041146402130500c3c000b40b0100f1401d00c920790a001c502c255202076001201d000303041604c900c85c41d0500708042500c6400d0f1030b4141102c0aa503d14044012542c90100c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 909759730 1250 909758480 909758527
    0x1802010903290c1801090b040e090f0f1c0e1005030604060306020a180b0306030619180b0f1e010506090127030312020309070e1906150306210314 64
    0x5258851041c008510021007552030f404e070511603400340a0104000b68000d0320300321041d16044c1e0402c3d82d0369100396420035200400450881c800d8410000d902040450500c9000841c407030721040031086000111000e5080042443c0c0000c2c0c40c041014400e4810402590300110103400460b0855807a901c0c00300300c1e800000308c4000191008001d10100300c101c00500300402238002c1c80c5085041000c006904c450380641050540c1007040b020b079220401d2ba4029110700402c202e284c02410900e800c00c43c6584c04100c0350b051000b0100b50014a00c10500c5141d441c540000294004d181c0e802c1138140071083e44080c0c0890305000000810000c1c03210360601240c2d050f043c070105854810301d1464050100f07007482481c201d40070300500401402c030600040440c11604055000001a00c03890405140c1054005030f003c1340c076044c00404103050745c13401100701440d1890f03a02000016500c11401401c08890900b11016044c0c2229450120748243c04600000300f400d4030f01c40c43e0680c07000d071a85210444021 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 909760980 1250 909759730 909759751
    0x30305030a0b120304090203100f150909140412020a02090405010209040e071a070c05030109030c02150c070e1e190b12100504080c100906180201090329 67
    0x200aa00701103405540b003041016a19403014407800180d40d500d81c007aa008001480781d02000003150481c882c2c00400041c403070501c140340c801d500d800591100320700c0001310f0408500307000300000c0d40000610038004095881d8603080e14903282d9a0703648640e043c0480c250811442152081d1003d40e41e10740083c0c1c00307030307105600060f599030014040c003058070800d8103065401d42200c807007001248100c0d844002e030142c09100c3e8035039540f42840e103894030f500f00740c00c200d42662074090a8010150820031814540e8001c580c400003850912004614520480307160001136000608104943c01c100084c19803c6800059200704c003410f010036060001c18122100035030440d00300650f10349036040c0d129004940350103440000b509800001d074155942d4242c4600d000c21a0703a10002010f00060005641c03e006a9005550070f54100700081c4001d840c46c502d05444441c6008030021300d8141a11103402059410707102d402000b80783d91503130301824200494008074001a640a1481182c000310110703c500600903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 909762230 1250 909760980 909760987
    0x2100905272212030f0f020901080a021905030603010f1b080604021305010806280302010e0a050f01080c0706060f080d0e01051c110406170a060b090111010e07030305 73
    0x103030340a4803510060020141108440b84240c0700314028854092580d80000d40509400303d080c8046004000031030102004c02d2401d403000c060044550014040c42c0000d0317130380ba059512044102c40881c0b00d88050345000703028140768482914019400f4641c415801800002c40307a01a444000544845109029211002c2c103d00003541c0d8000d1402c82d0400c505490848c00c0164411a110442d0441d01410741406008000030780c261b5101102820160a80c0715081c017641a407255240003920701e400b040780819a05145070b04541480c000c0d01f03040b6000104220f407003d084000640700d07140c003e00180811081008040040762a9000c1d00000300300041d4185152842c10007843d06140ba41d1400c2d50810281d0711480000d0703a44502036618156880e05042c01d0303401020f42c03810040141d641d0841c041c000114000508642140201c10100640d50402000750b0b240040c1c0401c50f209070240030503603041809516401d52140d2590b59040c5001d40c0006078988ac461006454150075034801c4002a4000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 909763480 1250 909762230 909762289
    0x61b24010f170601270c0f030e031305040504150218100816140c06130606060206010b04030602071410151202060d090602161103011802010c02100905 66
    0x94110801400440b4001126181d800c600c10703140c09040c466071500380903c0f03e0403840300f83c0d40800308640c007594007420421000400405400c1030451000400400d140545e00200b0a5000c41198283c0340c902a075039031441e0502d0100001020044c2040d6900300c0b603c00f49000d0300b2002d2000b490080240d40520826803008810042ca90400c244000c00304910603080c84245940090104e0001c030703103810014200e45591010301481c1c02503034000103043c45140188041c03030340d805c0310303c0749281d000340703000d1040b03640740d60382640c0d11070080c8510001c8a404120406c046446680507044a40c418000c840c940000e02e20000d19085000d143d69200350f17a80c034104413400d10085907450080401040b0034600c103c0c1500014000e00440d45040030540e26130b40c102d82003010641c125464014040145a030340d049074103110350700300500c0300064080d600c1c141c1d011040d80f5282e021144004e40c141d550309403060f2580c0c244140c0104d42c900e42d4041c02075500c000716042c2d8504900c40103400c103c0c08100096045c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 909764730 1250 909763480 909763499
    0xc0e04020a1202031b0316090501030b0a0501230102030f0301030b0f0f091209030f0a03020d0f03050105090112030309060c030e070b04030b070f0228050f0606061b2401 74
    0x41d4044045081c400c4200001604c01050030320080e01d00001d1500b8220902e00828100720f040d400165400fa035580c404600309441e50701c254103807030248124003d25070f510502101251404e000d5006c5500c030406041054226250120303481c80010f10540b4100790400c0311488180d002a0400c42e00c0600e41010040281c016180c0140d1105d002c04014020b410610302042c3c03107038800102003a85940018407420344c2c1e1030030401881e003815404212007100301a4280252503105581c40032001032038808036905e003140b00303004003410394000620b200e0040e441c000c00d800f08198002021410301d901e48110700f010a100c5d105650000700c194801040481640d141c8900f802c0440c0c000c01035044061105001060384240780c541e0201160405540c0000009000c0e8a042c102800103c0c032000b0034140c000030001550b6040b00c50b94403500468600c10141440d054030740c41d0880719a41c2000d014015103488180144244e91044031500c140c5420003941d80905284c0011035440c50f000d07520142c01004020791 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 909765980 1250 909764730 909764749
    0x5060d0f0506040c09050d0c0e0a050403170f070c020102150a1e0603110108040c0801090807061407080f0c0c1b0909030f040302040207110d030c0204050114031e03070c0e0402 77
    0x42c2120104020a98001d000e40358034958081e060040b00d03017012000400c41944450b10240c00460410050382c6418603450000d08411101240080c605003e00c0c5610350003030030158041c2d129007900140c1c0b5500c07140d00301e80140100f1400e904600c604140c800303002c069a43c895014849544000c110382d40c000c4c211f45031480c02c994562114515088081020502d5488000040c00c424030b40000e454a407070038503a01d424626000720080b5480c064480b001c0050001c0208506442040144080c0402d070204405920086036220086980c0c400000c981e8801c05041c1c50b4004c032101d80305400d040c1140710342ca03c1c106a00101104140303003a041e0740343c1403401c00710f43c9074410380c804001c0d480c20300990141602400b03203100c000e0140b50082480700411030610a808543c0b10b0252215914444906008001c1c040c03152041e4081c0303141400209282c07400421348018000050300600d02041d5541c8000c00c40c4107070740c44060302800140813444c0005d0441d070100b0014070413040340614900b401d004000e41d0b4078 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 909767230 1250 909765980 909765991
    0xb073509060c21040501201c05040b04020f03071d040b010f06050712051603083301180f060908120a1e200706021b09061905060d0f05 59
    0x244203000c1c0c0000d03080f5000003088601e80850003807546859601d8190302400c540842c620300c00030016800d041895480307001e802c0c0c8102008200d80c900c0380041c076000448400b6a800b409514410b00001c000d4148401c1e6140300703002c003604461000e03541705000280310064000380c190358214141803200b881000c20003140035001003921098131030f2030408090210b01c290480244a40100340c40054400d010340305070343d2440f946004000249a003480c0080c100c44046400042c21840000311f007144850b03000b480c043c100c00441e9100c141607503400066419102c0c0c3d08164118048070703076010a0074080180749a0040029840d01002d490400e078034142892410040009a02d0080c440c076001c59034084e0407101d840d84101d1103070101c0078042008071040184200e2403030307824022214a140c403c20001e0300c0d604444031542550061540303450710081104e5507203800c0b030703012070060082000c502d040c6c44403076000c01000a00784980c650701d00125545402c00c1ea1810241e0356100c04c10b15082400b03008056021 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 909768480 1250 909767230 909767251
    0xc190809091302040501080703170a0918061a1b010501031502090a05030708010921080c030a0b09010f0920090f011e0e010f020c0307090f0b03010f06050f0d0b07350906 74
    0x2f2062001080d20780c541c8150903030000916400e03030000c80789074080400707815000350709140110140044105903114003942040d119884948a0380884107128a5050720783c01201032a24400b5000d03200b000c2d401201c00c003640249500b80025103035804001d80d00041124400100b407640d0203090004d1002c1801d550a000c1450300710001d1041c40d8450031055010910f0701c0c48035100d403640082e0380d00611200c021641c0003001e81300042000001140c0c20000c544800c032044c46044096914004040780e0148030700380c007400601c4003030304030314008801e584400010700d040c180d5001440d00c02403948502d00000c90104003105112015941c0c40807030459400154001084d054003030402196841c100c5200d0400d03015910036184210745450b822200c0c04001c000c00900041064a0803072004142c1d9101e113900c02c0c111280f10441e80d08100315100000c50304003286a9850761107400c00e68400d050013202000c2211803011030481c2c0b41100401050000103002030300060718003840306902d425000740901852 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 909769730 1250 909768480 909768487
    0x12d03050a150914131203150905070c050715052703030a09141807080714270307061e020a1505040501060e0c041208090306010b0c19080909130204050108070317 71
    0x10035110071b06081540110302c0e00103031076800c480111011428540110318420f05000a11240c0c07640402c00501c02805070b400e0741c00c015682c0000010396040d4280c07217402310300b0520414900c01c00e24003500d1344419607008d03aa030f4185c8a10001a05552026010601013199010f040c814001c1807520045908805d88146444032807110740410170340350062071401080381317040000e00c5103441202180c40c419040359055484081c28266050340c110a24604000c090021004140c40d01c0c3c00602c0c10100e542c0c6444110410080d002d40503101c050f4140180d095110744903e681c00264046900307040590380f40300000301404c00345407480c251141d580c01114410160010310020003d680300325011204d0306501c0d004004503034503042d03c080c043d10a00c1c940c140205c000004144100c2e00003440840240c0040d181c08035200c3c072030301c101e801d5600c070064021765040c000c0800c00e042040c4495000706100b011000600d6440e8005010754000b600302c080c050f003002a007001002609400c18000c00c084034441c03401d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 909770980 1250 909769730 909769733
    0x8160e07090509150301320f0414070f2601060e062110022508031909021f02071a070609030507081602012d03050a15091413 55
    0x1c120201e024262203040b6180104200146001401000c904054001d0003104545411300c8003491843e45408400129005098181701d01800880e00c05e601c101203012a9840e0f648843c0b0110200d00944003c0348108503010500002c5482250b00403c10b91910030080c04a61000d19a40740c1d103049024403a07030611030140b04034101240d445e40d120300282c3d00190084a10044031001d81b43d1810308002d240140c80705121441d8080d00100001d0b103034202003041d840c0d00e0140c008000d861401e80640540030501c04200c002d40b1503808030555035640100892016090740014a030740111328411108034000a0003040d038140c0501c900c0004009071046001030381180100c1024900c00d03040d000707110684e545402001c15004100fa9040d1540025050fa2660041c00306900d050380b54881c00e0780455502d980480d100140849417002d5025503480982043c04a4802074000c0e00001d03000b402420b8681c54500f410810b601044401400400d8001c41e200b244855103c42c1003201808100b06a500c0c40040350 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 909772230 1250 909770980 909770987
    0xb09121204171606030e01020f03040609050d050427061e03120212220308070b0a0f0203060303070321020a05030a06060306050102030a05090d080a0807030509011503020d06020c0708160e07 83
    0x3c200d41c694100840c002d50b640500900a200c2c104c0392558400c000300c2440305122171030340000c03441c2e0310030030858480204413001520540141d00c921040c00640d00400060410b0028441071240c101460204240340c51b14814000c104011041445d4100402020001c2c0700ca032550101c0c040349280050202c2c541035030303000d0350b03d4480c0c001244d6202840c11100d240319502500004011500b000356075803141e6580c81c0003a40e144041c1c400d103004508000c6c400000d1507092003103900510000703008626002099030141e89030720222881c2031a401406001d40a42c0c1a2800104040d134903c0d03a40700c2c0e481c038042c54048112201d5402c02010140f500d5424061660000100c500c0003520b414219142d400c54000541140e0b41400c0051401c04041003070b14000da08418001d0184441d62407d201d03030350710411240e0032540d0741d801d1308400301c0b047c610400c05810642d1320241914003400e409854046218015441c05074164443d40580c4e0051700040c4d10b40112040c0000502200c0521a140d41401000203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 909773480 1250 909772230 909772273
    0x6020a021b09072304051012050601030513240c05220602030403150e1e0d23070302010e01020c060402181b0901050d0603060b040f020708040b0912120417 68
    0x80c5040e5101404180b12203403040252402000e0050901d090003102100082036890b82c1c2340d00502c12401c2002041c09980640030321307845003140042405100e161926840700840d0f80e0620b10807843d40a00000303654081c1c50041c400c801038640c68281e1b4034114030b815035000054107284402c442c2881c41042c070260f03030b01004550481c0d400c41d8203409006031070480c09009150380b80b95010070740700b1524222305410704c02010301a00300322442940c0780a407052800b941c101e00c001c444402901c1d450444600031200d12005012614000e01c00000c441e550707a042c81c0d003240c4c08101a0403d0394842003c000841ca04900c01060410488840ca45c49003070035500b00303010850804018502c00b00100f801543d0382d202b00207980c88407090701014030201355242082c40007005080314080c0140d04001024601c90302e140220f8111603408482079107882e14000e4a8001303900403101641e8445018030918842c1c1c0c2c01041503a11103030070030340302c190703154a098401200b12500300c1d0810b04580098110045070203101051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 909774730 1250 909773480 909773507
    0x81005030c060d021b101d010b0f1005040e010f0833060f0d0b06010801211106070b01080609010b0a03020117060a15020f24011206060306020a021b0907 67
    0x503856054040c4214606051440849000d100d1006c0305101200c80e03401c0b007206201258022501c0d19464152142a00d2a0100d07403a04403000e4001200141043c80801350810000c0c49c000f0705181e201c0d013220241040a9001200000d0521800c5c13041d504240010440d903100540c104101c018240361509500004100402d4066849400100c075502c1d01e03001301c00c15100040c9040400f00043c9000c80c0b04c51815506d0500040640c1c0021681119680e0200080c086035005d0082d100040c1c0d48200003c1503e29032140c1000c0c0a0107c1d1001401c9605030074040c0c00003c01401d024170780f078903606085030701c0e102c0154454212a0360420250740c00000c41368181450643c00c000b255103000100344800f010742d008010030b041d170859414280358041807146401d80303504185c82103030720080041d006610b00c0b00d00102d0300034080d000400c03500319413004405806204620204107955207403a00c1c01240c11800107880588c0100b0300c0c00d442d81d030184954230881f681c1140c507a00b00d420091380050241080d40032 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 909775980 1250 909774730 909774757
    0x30607080c09010e09090d02010c02030301050a230d030f0f05120403030c200c0f0d031b0609060504082a0613061b0905100203031b09130c081005030c06 67
    0x500b46850392040014000c000c0c4003801d9050f05041c48503040c0d0b07403190480c002600551800780d84422030b500c080300302d038122140100a0320340381e4100150030f0011300d2885051400050810300c00030440c0c0342c4c0c410500304c0c24000d0325082ca00528120340684445d106a22603c1000410840000a510b101f80029041754141c64000b070348000b002010369010710f00c801d40b040007039600800016100c1000480d1400000d00f80c0e803d003c9004041d052014244000710024007144501c0c04038030025001510b80b1a0860040002054035985071b02c03100100d840540302a600c01c040043e00c0c0031340c0d1090541100300c006550384401d9448a400c40b9030340d151000034110308919000042275400f44107041d0054002c1d4415aa0661505001c0380406842c21209110b400d01465410816000307850011080c0c0e449a60102c0312502da02d00d02d0381c41c10301030380d00c460f511a078801c14100004001c04030341c2c0314064880c0250b03180c21400b8100010481407a100700d610891096000b031008001644a00701030b40c050b41a032a9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 909777230 1250 909775980 909775987
    0x7060e04020706060b270a06030c05040b0301080d0f051207180305100f0b0a060f050901050f0a030e07230607080c1902040522020907020106050d03020f0606030607080c 74
    0x80000d001c0c1c8158000074044078280f060202e05e00c045003000700058144081e4101c411607a1150500e42c40d0000d00540780d100f03107903140802c8141c1c0240c01c5a40c056087e40341030761420b51101c0c08440d041e0800e0b0016040c561000714180c420340c2c4c220349004600c003881d0074407908280a00a503162040d00080c10101000b45d008228a041c0180c00c1c4c10001455010003502e40081d4187d9600c13008104850301d081100c0c0c2031244160341d5060400751542030301d43c40d036950032034829510000e0702c60342d00c85a402410000c04100325030112005002600342c001050b500070440b00030b0104010314200d80c40e0450f400700c0c0500082d100a541880100c110003060984a6030748174051401d048099008030342c0310702d141c0c0c01001c00c1d00c0c080728480c03200a2a014400c4901300b0030380d00e84021040580590207030916a18030382454110151800d170003019800840c81c030003c41c0d82c544807008110511a4100110056409a0b54841c41c95106001965001c1e40070b600502c1207103002803000317088510240ca004070090002 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 909778480 1250 909777230 909777257
    0x30c030919052d0304060e03120c06040f0f02041b020d020f0d0c050c0402030c0a031808030703020c0c0a180e06070504180605030d170601030b0609130b03060a09030f030209030706 79
    0x3082c0c6180c0451040013541c1d1110740d85d64015210740c400d420744038424042c01110712040020031066035415008032008080723030383d1a5550100b410010b800196000303080d001c01800180d9031030049040c0900e00359117600d0781c0c840c02d0742c0c0649041c84220300c42040d500710540c0144410400220300d0307210300c3c552404900314800e030b0629a00300019219a50303081800003040103000d0302c00c10010b00135055103650402404000e420072444a400d1000002c2c062841003010817265403003600a0b101902401c4180d03680c02100b00d0000c4c0341e201c0c003541b080503044900d02c42480d0519040c400d080108041d0000f61006160000004080d445030b801254a5615804040500081258030000140c600507040b01d03080c41c0829009040c0c0e0004103400c000c803334107800c001206540b113030040c0e05051102030405801c003140281003007410314540340400c030308654603148000c45a80030400c15000d0f400c121300000e0b41410780d040003000c1d200040017100905004100700304864400040600890369603213090009507034007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 909779730 1250 909778480 909778543
    0xc0f0a1509020111160626040f150c0207091a031504230a0204060503010c020a080906161b15020c0607060f0f0e0c1909020a14030c03091905 62
    0x98031184410310030040c85c8041050031310150f40130740e20251901c00075407042d4032114401060714086460b2000b640c00200e000110180001a02c040c46214468504c10210800c401115510641c510069020800811442c5070382c0c03160001c09030400070707040741c40c01244011907a5101d5400c54080301f0842e02d00090700303000351824000d468044542401007200c50700000c0a60b0340c21320713401c1039105928124001505190510030040107410640242809c444541c40314140c541202c500d451300400204000e8090060300500c0034900c81c070800b40300090243c101445502c900701074008240140e10180268451900007680c44040901182c46580c0d4200d83d140c0040645521828030780e0340380c104960400e100e40690407143d80d4030f1001c1c04480c00c2e241c1920800c15070309811000100901420300313052082c5903e640003409040e80e1401c1510610035282d0141c84d00358411582030030160404428007085940520000390f854424031120050450701c0e8232055207804101c0f60b502c15108410b000ba80080c800b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 909780980 1250 909779730 909779747
    0xc101401120f171207091d1e07180602070f0807080303130516030f02120616050d140103030503010e0f2e0b0a0906020f0d09030f0302010b040f020c0f0a15090201 71
    0x13090280c05450a1215010b400168580504080c040018030752007001200c61030440e100d005000f14481c191800020001d01d400c00161020040201e9051481304200300b0103140d4000301003d6004001c5585007a100e407400d6207036a002190359421129040040400c004141c1e034012a424042010014035858081e142101d03148480c034044158002c0001800001c140d02a2028000d8440502000300e400105485039000c0340c00070003421704041d4800e804c0d40700303002078444000c2d070380000152281c01e1505603079520006da03c00c0707001880020042c05804505a0010381003408660500c11a05107030b05214290f45120103541c0e8400c081030105007682d920140150010803c14500c2a62040c548c040100f036008103001701005403044030b40040032242c00140019158140359a0b20f6002402d517030b69114800005c010a8003103640301e0101c1c00b031907600c074840c074044451f00c50710040e076035006004882d0034a100c0d54042139854001c0b0900201103600d02030401d00c04a000400020150305510060312481d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 909782230 1250 909780980 909780997
    0x15040e0705120726040b16020f01060b0307091403031204021804050d020106060903080307031e061d01050906151b0604060f060506040f1401050c101401120f17 70
    0x500c1c00b010312a52a4200344c240106010050f4082d072441d41d074a104500c02c010035200285140c071010005500d200030101045802545c078030681d1076041040300000c1c203440c400c0e04071400c0c04800200f84040140c110107010010320003221103806a000030300000742c481c0202140845800680800501150b40c0c21a00e548082100c4400803520704113030901966030003801c41c00303a02541c079150000c01e00c580140000c40c02c8076400000107203980d0707030f04c0300850141869144e03020700c1d1024140940844070203030003040042c0000300b92108001101d05200008500181d04c40f030b0240460600313000700e6440700d1003151623501c0819141e643c1c1e80402e41a01c100c1c03c01c02e07150305034940503600a000401c502c0d90001e0811540350601400381c103890388204107040c443c900c80c020640c404c0714010040d0b941200c02d000f00c0500141419420300d600b8142c80e80c1001940b07841c00e0783d10340d034804240790f00b100c0146203640036200d41c400013480e41c0c125030b0300e205081e4007140001c0d04042542400c040046403e004a42903403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 909783480 1250 909782230 909782257
    0x50304020d0537080318030c121315020a020d05160e0109110a080f150604030b091606090621140f0f04020f0d03090801022715040e0705 60
    0x44003442d9580b10600d403800030322180035601c3d03650303c0a0b1222800010000c81e0008203161075034841164458100031401050680e0707001c06d1080c201400c03401e001d00c01804040c2c49445580d820101e8010f0031240250300442610700c001403279108000d5002811618541c0d040d00e0507a07003490641005840e241881816005081d205c00c004103078007802204150484025a00900070422007100c1200700d07002d10030150002a40800c0052a49042e060405400c40b072141205418440c4da80d001c1032031640641c0060356040d0200c0b00b800072108040040c102445201c0010b800b8460903c0c0380140b40090500c203440030400300000200d54400580420306010008610802600001c41d020320010441154203620210300680042c161120a017025403103503a008000aa91503100010099214800503056003040020b0f007000c90f14031030920050826000010030788010720f00c4c1802c1c0c00102000c11140901540302240c0d20701c04105842d06031425125140c04581050342d409070120703203500500811800c0c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 909784730 1250 909783480 909783493
    0x10503010e160c0503130f1203051c0219030506090a0e0d050a020106120c0e0c1303080d090b0708180a150209060f070609030906050306030d0e04110c0d020c03060f0106050304020d05 80
    0x10b00c42c98100701c0080383d6141000b4005569106290b4448c10507001d00a03001c110200a080c5203224010114000c022040d40014188602c0f4018801d000804161410109985a041c86040d28240340d00a5010400f0a4144071050301d02e8000c0e80c0b1484098104000d10401103216440a8000c0d007000000d0080e0042c01c42101030705007030040001c0404d21a28400690403404256401c90380e404503036421515072650301d1400e00e03566400020358000182d06445c1540c40f02c01400103002d80c04064040d41c032594030a401c604261004800b9001c00042c049450340c0558941d400180e20449080e5000100d11740042c0c40b1f10001021414920940c1c0030300241510000780314081020a61014003928001d540b451015512850309031468072040c3c44095040e4800c001408840d441119400d614040290010468680e401d4001d101d03500603030303031202d655001002d0030518aa070410070075521001c2140106014140001c80820703626060182c0010404000000740564864400c00000d681d445002c5484 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 909785980 1250 909784730 909784747
    0xc04090c18082427100c0f020309010c08070f0605060306150114090a0e2d06062205130b0f040504020a210804030305030f1503100203040f050604051b010503010e160c0503 75
    0x3190b42d1182c5d81e00f0070f40d1b46003400030128a40304140c841042d903403e030011840d0219001c015100801103403070464800008000500002e00c5280b81c0992080c400c100c04903242c180070007010700349440184820346154403001a12043d81e40160302402070b0382070507691550b46490401080c40203d42c0d0b0031004080100e84140410060390b4503103542c4196142c0442e13402c0c0902880c41c0318043c0400d07140e156110303105004161540392850045e0301c90500d80705140080d2036071640441c02202480d41416006595108852000d0520800880c0241d104441c20401880c142d400101000010701640420803802004e54840d040c07500310040c006a0040e0700c032621071396240340c004c0090340300b10341c3c1c01a0f940144010a0020f06844052501d1000c020003414038011246d88540094200800a450070050703080c00d080418014040740f07029501030030107404680400444071542c46e100302000350401600b080100442e602200b98150010b0403a002d0129210f0344900441d081c8545080151060000040030780 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 909787230 1250 909785980 909785983
    0xb0301020c061314150412030f060b041a0307200325031e0f0302130f0905041b05090403030b06121f0506130b030c04090c18082427 58
    0x910892184080e0b0013a201e00790051a122142080d5140b031605c0b910000c580058410351070074030080d40d41d1400040c4400c010000100b07507150350340010703403140700080c3c00e110258a000b90380240c0d05540601034036500b40a0002050506402040d07141c0498001d9609032a6000f40100c8601c8684020b40e04811a00540c00d0b0310081e041090840104021400410304003109216131041c4caa0b603078803040054440d80d00190080d5125101c28000e009a0003400700780c24202845503005082d04c1d020014540c5080e20700030307a40c0d004001000503200d0094004101907914860b42942c0240d0501c0c000c10103200d264003003205801007609034446d0b07070054020480e44140d01d1010340032144140c0500d490040c3c3c0ca00920806206021594803213114441c1c061021000b04002550844131080d00e071860107030341c1d59120b0b0456922100460001e002d40c1941c1d036459400d01e441001400c00800a4000c80c0781c0018076481c0500b80c5805030180d0030b0880f00140c407c031540c0d00b03001e5000c1014070041c00e005001502c000d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 909788480 1250 909787230 909787261
    0x9050604060e131104091401020c0c0a030f0201120605130b040f02070b0f0603070f0803342618030d080601140903010f0c0807021516030b0301020c06 66
    0x10300841c5031000001e0b29190031a403240c000c100c00c141c900316030f8a042e110704d410351000b0390142d60800e03220000c180000f140e00a150349280040e0000503100c01c540c06010f070038181e00000480c82080001c80c01e102041d81d40c0c443c00c811a80c2401d00741410381004810901420080c0d0120754000070f440d108024452642c4c000660100e01154100300341c1c409025490203c1c012040c01600c14258130300000c003254542c280641d003100000781242c8250b990f84e0350b803014184058202c0b04950f0000314078108040103448020601d100200c10b0300b80d41ca208030805440144000c031002d0880b22208003001c8145101500402880d03403078282041d40c50b242c016100e03c0300d0030350710300c007034024462607440114840c8210511402280140d442540e00542010181d500d030300200200343e410355958449000e017000034454162021016141d90485151151010382806407040701c0501e00e0401030304105045005000d031110751021030038001007021941e80400e00a014468000c002c0f445101c050019034000482503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 909789730 1250 909788480 909788491
    0x632030a0302120d1e02221802070804150c200d080d06080d02010c0810050904020909010b04021912151a13060c0c14060318030705060f01050a08190210050d05010905 73
    0x64001da980302030152080c1047c0784030b00d400c81d03424090101d003d10341540007024a10b004403000e074241510b920011242e07000e02d28400010410b030304054001c018036001e0218440800b014503040340d0b08904040340d00d58810842c0101361900c0050080300c00845a400540a05000401c4962036810301d10302030b008141821101d800700d1560b90004800c410190102d000781ca0001e050406d0302c1d241d560a1104840003d4400b401c3d65403240020207254549201800c5500c000300e5241078499602c490250503060700c40103012070a81420449170040120703e404c44200c2d580f03a02400c80130011211801030368007070030959920480c40c4510010396240c0c0700d1b0311004d0302c6015045425500e176480998050b02080303103000580000003480054221611014400f081020010079207140200640d40c150800004482c107000210300d00d0018411401c10301010009400310100408031030f40041e1408545064101c40203201e00011005440c102c1d01c26000c0d503404450251060195503150803482c0c0281c60308440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 909790980 1250 909789730 909789757
    0x424050117011802010e060f030a02030f01060c03092d0b220e01030318080d02010c02100e0a081308120913050708060409060632030a0302120d1e02 65
    0x71800c00d41031090f40c0328900c007441c0161608640d68019a044090004070b43e600250038400828600d010000440c802c030494200140d0b61701d00003407404643e01b0b068000c1020044145141c40009800c1141d02c411b50b214044604c03010b1101035a40d40d08210320b00ca541514040280000541c600d20300003074680342c40038503440302c24940d1840d01100c0d500c00910039130400140c2c204c010800300780607464104400d82c622040c010101c0d01c0e01882031410380701c00082001070f07542d125454141d944c1489900c0f00c40800a00034464030181e40c1ca540d55441f01000c01400c0510002401c01e90b4480405056001f082031005035003482d000718050398903d8000181150040b4042024001c01d00701034400c0310b04c1905280c581c080151503408c00c0c80010315101204a80700c03641c0e48000315010407800702902c00355040320784146080e1481c0c4031600e840517042c8140d0340070b54400c0010200007030300401c500c0c45126070003000b10745420003582c00501a002c00210560b108054407041c03c4450542e40090101c000d40e0700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 909792230 1250 909790980 909791009
    0x10b040903181a0a0f030b0616230709020c031b06040506090a120c02031510091a0d020922030509090f01060906030b062a0d050c1504240501 62
    0x400070040c3c84010390244511080412005001902038a464103600c2d0540ca000150340c1480004240c00343c1c8541e000b45102c860180c1c0038001c0141300038488190304054843c403403060f000328040d070365036000e43c3c000e0300c209640106640e004980300b041501c22541e4400c6070a0700401003001c01f6900d819043d1401c2c1d68500a490000701c40e40b030000781956003540d10140d004120b4000381c7d806c030380c0005d910100700c4c3e050055a40c1410040c0d0f4250180e40900540b00c248649207241941c0c0108403031600e5090010401c090401003126940e00320b1031050980c0580c0e07800180e40c0c80c1000c806000d5404444181100f10000004090641c05805000c0550702520600c10356250780d1844100b4200900c5040000341030205c050080d18465000450f0041340948024141000001e407501c054142c0740c41c803000910212034661a5030010041c00c40005c9050614600c1d002c201e04000c0c3e11140ea500d0303540340c000224000315041000c0309440b00c000d910004812150302034510503241c007400c001e214142c504030010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 909793480 1250 909792230 909792239
    0x230c030601021c0203250b07030204080706021501120f0b0702030904050f0405070302060d0207080309030c12130e061201050906040209091513060b06160203120a1b05010b04090318 79
    0x424070a0f000c0550011070514458001d002c41d041d6902c0f00f441c880200d0300305028001043c0151407030103250359072005615181400202d91a14071103500c02021540b01080c21600c20391407420307450640c4d01004c09107a10500a0405066001142c13030004c0c0b46010410030811510f07408400b6010114040724184000d48403d0103101c6600d038113940107091500a40780800061400f82e0042c000120310704405070608100780c6882c0403540040303c02c59002c8e0130008a000700c425040c8040e105050b0304c40d4440741091012081c9414134901c900406222018810100d544d40e0364201c10740401079401c00007444640741040c5541e403240c10585040303005681d00004543d04410126640b4400503900a500c10b25a03110040f94800e2400c42e4401d4030760300d50b184a4102545c4442000386940e1809125000304c507400703481814580307441d2038450b042c0702800707120034203076194446800e000312480101001d00f1404581400b030300404101d000503900c03520340482d0360304040c0c1000608901c0320701002c0d416881580d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 909794730 1250 909793480 909793513
    0xd0b040f0905100504170a08090708010c02190809040f0b2e1413030807200d0f02010207090227181f0f0e04062d230c03060102 56
    0x16003100810542103803c090070400c1c01d69110326409030107081c00d4503214100d100741c40041c0e0301a008010000ea40e0380200118060108042d07801040941c0c000c2186d8150003600035201c0ba9189014510703002d98603c25424021220240c0e5a140e6005000b044000c0500141100504178641140c0c080d104401d071250b4541c203d168450b00ca010404004091030b101400c3c100d5002d40e1045068051881c107000022000440840160107144a40c1401c1d50700e00c4c550034103948501c030030140c5c540d402d030707400151514903140e15401e54100c0c0c1d030101c921618801c8a20041c0c0c103101140d04030401c003510102e5041c3e001c164101080d0600b9894407581450729540005005c41410030040b840a00002280480d4441d50035050403000151800e5241c103c3c15121500d6070030390f214030351000c2e2802d800d840900c070511540780315076525513294046c5016050704018080f8170083c000301c0d114400e10303507034a808036040b603505544111183c25141d07400500d14080d4074a203216001991018018030500d00d074010350441c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 909795980 1250 909794730 909794741
    0x3180302071809170c1c1d12160f0e060f1c121e18032913030f180b0306040b0d060f0b0a0e0a0e030f0d0b040f 49
    0x4065001e488914201401c49402e5850341044040d001d6444110001180d0b90408082c070388001c0288643e911092204664500600203a5041c03612540f10700d0881d50582140c01008000b8030210b104581100c0c210005691104d041901d408501a02540781c00b407000d00d031030701c8044e60450031030111055104e841c290600107040b01c6444d00900c045080c1e03500d6140100d1900e02456501414500da034100303549800210421003c0c000202d4a9251201405624003040e4647c11f040351910f02c4412041c0003a01134520000e02c0054014684081858401c50300b03901c040b0321194201c40220000e003052002021600b0404405400245800007200b25031072042d14001c0c1d201c2c45801c0303038075a20b40c1086100b0445a102501081d801651410840b40d261590282c110b0158003031040002c401004040070400c0da82c5041101344200880d1605106182e0364506081e0400002c1c14002011219542c03003a28520961100c00d400d00004106030300d80f546d550704041c030044010750702845503c0400c2c803045c040d0388 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 909797230 1250 909795980 909795983
    0xd060e0f1915050a0b1e040b10050702090c13030c05030f011103010b0d0f0f020706200d02130b0301030b070f020111040312020c1507060515010e091302030d0f0318 72
    0x1c03410050100b20a15000107820445081c00010b0070040b510000c0e081765a10004000c00c91546c420401c001e160500c2100c0c480c00381512100c000c4401000000d004d840340042c02441001100c000c24070b40c3c034440054600c42180740409824264407828004251035a82c81522300c02c1c450a805000720f030406010341d141251441c500d45013980d081500541040c2c0211070824550390741c410140c502d90159016040ca94460301030010707502d0641f07040820603503c03400b19881250031004030f443d241212617021211009d181c8034006884041d130480344401e0320030b103902032042844080000b106001c0c02840680c00307411a40c540c00e40c900071901c0264242c031601c4204840b002824030080012820b1071131100e41031640d5105031907403182d100c00061420b0107488803c7c91140741c0880c01404021003440f5064012035048040d0080d134062800003065a0f4070758409900601e0220040303020309810002441c0c3c1c00b80c0c02030944852508240000340800c1c00c0c40b000b40002801d200f080c44181559035400041d40d03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 909798480 1250 909797230 909797243
    0x160206010b0a0201230a0b0301050601020601090915020706021909050a0b030a0e070f050102070602070302090610021e24100611030c030c03030105090f09030304060b0d060e0f19 78
    0xea10701038078501160401407808040d55200c004481440300404220342c81010000300b0038443d8200032007020100d600304080503000e44e00d81400c0c17054036a00018028111035051002290312640c900e0b104040b040102c0580c03052500200b2124204031964028114404529210111b90f0040c140e0440e14641584100f60f0403181e0a40203002400c0090019903004c0582c0d50003003100d15148841c607142c01035541c0007400d2201d2104c802d000c650303418801980100790b40c1c80185201c0b0f04540014a1082014120a114581c03900170340d502c0e14024040c0e00326211074009404242d060407203034540c4030300b06901c048200b0751342c3e007490082c02100010490700070313501c08500c451320f141072200555503007012204036031741448140030034040f0b09d40401c0101140020140a1a125450202840504070001d0140b4000810300000c100707801d00c002050b01d610640010021580000460110340f040055003006005c031820700341b0402000900041e0b2081880000b0b0449501c503ca20704e90400d1034035030040007000d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 909799730 1250 909798480 909798493
    0x902031b0a05090d14060f1f0e06060a030603020603070504030209060a0e1314070f1820160c08010c08012103261602060601051e070f060f020c01051602 67
    0x83c2c4c14800055055030f485117881800784640d03400e0700b900d000402c0b00c1061240c490041040122071402540700c00f401c88104405c0701d241e040444440030400b0017424103005040220700048107034401d40040e002560041c14030340d5242000013000b44284d01c40d00060340208100804207040d810700742442411199001c00c450002d482d13408030000c2e0102d822030191245080001d4021388805c040c418a0010450510020741d5549042c03069020020070308101100300d0f162440e14041240742c1c0062041c44600304610503035421080d48105042e004407000901003108000001c50300c802c0541c802c0b020341d01941c0303c032115a80da40349141c04004400c150311001485003118800024040d070003020125112048400182018082c000304211041754200d01c8410500c4003140960340500c4200e4114500786001c61600e01064207001400651040880740c0b200c00042c84000d0111407021071070a942d0118050000203117041c0c3c0c00020f9041f401a03008130b54a0400030a060255030b002c80c454a0300c254018240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 909800980 1250 909799730 909799747
    0x30503010308160b1501120603170705070f0f080105090111340303021b0a080f1b160513051303050307050f0a030c080a020307200c04060902031b0a05 66
    0x2120b8012020090030b000f143c890600006816030b030f5481c030900c681d00300c001003242e07400001000d0110980300b03003032610314280c800d201141003031800340d4409050840e00c03aa05c00252500130719103a042c1c0d101450742d08400d000032450540340081c42c0d0484508200a101c10303210006c80f5800c81e4804d507210102c4600400000318035484101c9041480032201c1d9165488100f41d1030508513410b07070400d003100000da0002d04140d001c100b40c1c00718412556801c00034801c4100030351b949200c0e88511400030306112030114a100740c41c1032101041000440701070680d0185000040340405100c000e00a280c450703048011111b200800b244616885a1100b4210900c1c80070b0344e0b00c0684d0711381d101900b0042004010440300041011080c02419480100e0343c0010f070030701072460002d008501c05404d180c101030040043c4440309030b1211081c080c03151506000301100c00c111202d2450f040460b25800d410508040d03002542041c2d5502440c403901034540d00b02e00724043c010882c1520b20615131a031000c940c06100a00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 909802230 1250 909800980 909800993
    0xe0604060c0e1c12050f030a0b040b06130e090c15030403052502010806010806010c030e011112091906021b2b05011109012a0615030611070305030103 66
    0x4001d1409041094005000001045107128800b95101c598085081002d0400041c0c800494510070585021401d040100d482c00680c0d11014100414040e155040b0000740d40d5140c0c485101803000924076640c5131543c0074074191080043c4a0003480303840381c0000510402000c21010080c00340144200c031254020481001141c1020f0419800c001e428005081e0391044018150103003803082c0011354444440c0c1c070004241c400c009000c0340c1040283c8081c0728181e6003284d50740d43d40c50f506041214004607003200485030f0110040054100d8850780c081146026040b1005004820080d908061180ca0b0300d030303034184007851b01d02c00c22006a0206c41d521207504255031030740700d00400046c62000144080071140e0080b80d014030b020102044545510810007209200b0108014a07052540b41440e00c0f03600043c01185040500c800608440c0210b9000c45201010003061264403c00400c20000081440c0303900f00e000740802c441da28036008840d01c3c01c90044040d203001075815942c1c0781c41c0d6805e555442 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 909803480 1250 909802230 909802241
    0x5090a080c100e100c180306020a030f0c0905040b0a081c09050a180b0405280213030605010e1b030a0b0607052a04060807050121050c040e0108010e060406 68
    0x314024064008200034801103030080d03c0360350040100801c02c000b40b83c55080d00b1100400101014803850740311013800c410004c141d6000720303a045800140c5071803610074141e02502a10f040b2403003061600c0c09080d1410b404c1022101550341c10741d0104464410380c000c1c0b0165992500490078151302c84401c0511611b5450704407980d0510515000b0a1580c1c1d4401141c00001c0035040110410f16940181410100d54030a070207400e1000c13541440523051141c408000350300203644c1084406c4141e0b84021082c6210b80407030b000400c2c0d01c075030740360308654a082203c000c0800380152050f804441000c0b8500344045007000e001807086904072840c5445510805004060001e40d06800c030070140a41804101d05101c0700d420008010700d0f04480401c00da011f005200c04101c0018803944c40e004080c003107801e001070000c0542d0400c1c01c081200c7d2034000030031440701c0340b8035200c0441c103420203040080010415001e8412903103450303c00035859803038807a96400c2e1002c3e00c00e45646540710100140100318590080b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 909804730 1250 909803480 909803497
    0xf0102090d020f22050a0b0405070f080606090a08060f060d050d1b02090f060a08120906030604091401061d09061b040f08010504051b0d14070b0304050d1205090a08 72
    0xc0c2c000c0750a82c2044000d40a50901c1c1304101c0c1e80d81c0d03081045001c10f038043e118000004079000c02c820f03c0c028801074580039003030540400f002004400186140c840310120340c0310b041d00901060314207646200c102d0342c80908650f0003503103061400c049410341c01c003030480303041e029401005443e840e40d101004a840c6800c0c180c60039040107c0718052341c00b680b03d04a038203001c0e8829079940c007031924003481031260b030a40b180e02000d1545e2140c0e1060322916260700c107035184c2040c00c5584c039640340c40302000a40540329104019201c0c3c070b500c008101501505600c00c0c412200344c0149400c08111882021154603412151060700b6044800091020500f0909009200c18059410390516454042c04040c5a1481e0032020b07035603541c0c0040c03009100c4100041c00003500351104150040c60345502142100340702c141c1c01004c012074200c005050050510401000d4200407a0b415100c0c541414a2a034900c0d400007404c02103004a0340c000345101c000d0144520442e1014001d02160301940e40328030050740001c05 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 909805980 1250 909804730 909804739
    0x25090e1c0e0a0915051e09070e0a23120d270b1608030703092a06050304060207020618010e0a060509010c05010e0f0705011106060d080721030e0f0102090d020f 70
    0x801117a10f680d64139400b4001c80d01518620381e140c1c010024840304450241101043c45011600c194040e510f0b1308900054904840741154070351607180ca038010034111181440e81c00791180c03c01d142100790018140420301c1080d5a01501e00c2007422034024490102050b41d142520b1008003803110010420040065005000c5c840011540300e489001e0150425101440003940720a0300e00107014180180e282200f40211503580b02170039481290081c4003031032184000f48580800054107005450381900c42c0b441e0080c1c00150b0343d108940813400031402c3c400c03205001c19407882419000303040ca64000000d83d000c0747c0f2250300c0c041d50140159020083e50000b200e4035900c488483d07200750401d03c0034040d105021001010395500b0000090501400b958014045501c1441000040ea9800d42c066407003680180450b651007a10342810303d00c1011050a5080ca031281103040c44043e58181c1c88003106090f140c050382c04d400c00d603644840c242c2c4181c0782107d5000790204810005403a0402c02e6a2a8640003403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 909807230 1250 909805980 909806021
    0x40c0b271c05100e160e180d08060a120528021507050d021501210519020f04060311120309090405012304030225090e1c0e0a09 56
    0x14010031840021641c1101d10390003034503000c1c441c0c0700d80340070303424072480038101422055101e00c10740e0440441c2c07442400e03d40d034542c4021074014640c070b03009107007241040403d50300c40220048003c0c00c0c144040e00c5903030040c80c04010024071003d160f038000580a41c80307400b4002002d0030114030072a411001e803007525104031040308140142e0b83d40d4000e801e0314240d000556210105401d02c03e0402500c2040403040d900055440c068103424800400d040d2401d0040498208691124003231103061200c4c4000d000d440388004280714201d203690080c24a5208aa0342d0401c6920701003400180c4400e840014503500c40e46990000d0ba2030080f100a2008400d002200d003082043c10000c5d504d0401075a05548907552080069030501001e40d800c0800160712400d01d0460402e560000d5139031180d106082140000400b0301991043c00307403d004021701e945942030140c0400f104096031078102c514028400d00c0010740b41d503080c0502814400444000043c4040c80032490f0032100800740003520103e00400c842c42 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 909808480 1250 909807230 909807259
    0xc1505090c210105061512070507020a030317100f06030b0d0c0e010e090d0503060d05100507020f011a031c05070503040611240a0e01090812040c0b27 66
    0x4585040b0410075003411040c03640d69003101034211500034140d580500c007030030b428501c0f084910040310070442143c10000b840380e85248040781c1d1030181200c020350024200c2000024035a03c9510302021916240c1c4000a41c1c0b55446450800c400d41d1240148003100390708108140c42c0290b00c010503049001c0c1c540345001d041b83e40e5803206049242c200f0001c01800c640107010224420345190350041e558030042001000110f00a0114040240031a10643e1050902d00400400744098024030580740c00c140280d0400c084041e440354036104100740198a00085da106002e4542c40c0901c041d500940a040d44c4506820243c4d1154030549041302132010030442e91340003500c200002d00003448282d880b14644a0039100090402885110151450886101d4034050080100305030380c0200d0036440c000340b10f0110420460241910031000340600700d010038480c00700b10552007424810361080510036101612200c0d50350450040d4004445486600b02500800c125461031942440b01d0003405c1c400e0755000c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 909809730 1250 909808480 909808489
    0xd05070317120a090f020f011b030806032a0105160c0b07140f10051b0412030e0306250504120629181513060608070c1505090c 56
    0x440005100100020b410400030081c20303007141c0c00080008003480348041c03a8075014900030704194060f1140040355540c8406a006426901a26031038a8031503000010f14140900308084c04c036811802030282c40e542e072030a80c4a8810480460a05001c01c1d401407110f140115041c3e04010030f507402d03607281907125101140d1801c034541c000744800c401c6199581b006103041d900e1180c0350071444400e98080280404545004100f04603268100180020696680803200c8111111151008000180041c020500041190003254224040d8445d0140f1160b40c905240d569202208c5100c0800e1041c61401c3d01844901610620901145405420191a0541c0c0c1203000603080c011100030b940c40110140c4210040012281040240c20958070480490082400941e0140b4500301c0880e5000001d103000e4410910600c5000020f4600b0b04c003803c03620913550003880107004200124006800148140d442400c44003040c0da44503a140c0c841c0282000302c5009440081c0818840e4000d010209805448 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 909810980 1250 909809730 909809753
    0x1c03110301121b0806061c050c0d021f0909060b090102120a0c0605010602100518030405040b0a09020f04080f0a030e0d0f05061611010e150c0403021804140109110d050703 75
    0x44c45005000d4504080c0100a00140300c4090301e10700d000c40c0e001c540e01143e00490300910a85d0706440c1c82c42002628070010700181c0c007001d4111032031080743c5540000b9179841101d007070a0382c000700b400b0042c030380d2514000c1d240760048100241c0142e000c0e40313140500288501c081c101c403141c5070425840c401a25911041600c509030841c0c00146e100840c0d0b6600e0ba062800b8441c0c11166403921101d1020091084903101d100317a01076180119120041c4241ea510303802c07400c6006116084046444030b4180003210050791003071082e03041c28469208491060340780481e4180d03030f00350301d5103079034034040312850500148284040041e14200c9040c410000814424010355220381115401108015203004001c1c224004c0a04400d0290b85007100200342c014000501c018000c51042d070480a65a0f04248080c007445650802904a030081ca0b050001506407690140244e200e12980e10900601d084654225440c0250240c400401c0810b1020349061a45001111a02520035511040d450751a08401d146 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 909812230 1250 909810980 909810989
    0x1a01060305160c120e06070c171501060e0f240a020d08010e06012703050703020f01020d0c0b06041d03030708010506040303050a0e120a051c03110301121b 68
    0x940700c0e800c12001c51000c10b000500c076079a5040120555010b42c80f440d060400401c00e120901003180d0080110341d5840c0d00381d81c2400c2e841802044683e03114144c1300d500a091000700d54403031140704c1220100c090303200303202c6060b01c0b6190b448000c000171400c100281c030441585120703006070500301840c404200c0303180c20300906101d000c8110780e1604180c03402441c003041310001c5000c1100781300c01402100d05d80f03000300b07810000034a0300780a4504000160508181d012441103280c1448050000c10000e011800d0012280203c0c2c0341c076101001c0000683e1a41100c1c1d081c80006081c140c100340008820031451034014030082c10000c1c039500d441d0592a5030b060f0081d50341101e40d101008002c64558050b000a001d401c00391140c90800e40f9694000e841400b401c1580c1043c044094883c200548500b214040c4450000c070485001c601036051031900d402003002c0240c0d0702607a40b1001d2038103501078050081c2c00c440191610389160718080c040301d50400369000440c1c0820800b000010894a0150004040c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 909813480 1250 909812230 909812237
    0xa0b1e10140f2d0a0504060302150f1b0d1e050316050c01020a080f0c07020310090303090b010303051207020c21011409060f1521070e150307080f0304050d1a0106 71
    0x450702e120400c05213a8081c0d110500c211306002c010300050315412420b0301070100c0800c10704d0707c900e07082039400d480303000b007191140c0c4403a0b1402c4e909109220015207022030048940701e1210707070229094070780404d080d0b046600011031420030105451069203010068581e030a0700d4410301301503480c80e10b5426a8480b003100400200b49405004101c02d505401d203400c2140d0441302454503240e039001c43d40b210b203841e08294009959008135420300d40203401440342c2c6540200b0341049980c603490043c0c00d40c0c02143c0002d0740080d441000a048131f000055045084000408400381850189a500d030500c4500295031025502ca6a00d41e007131501381d994550080d4100d40151400d4075050403662032581d0700904000c40c0150f080c5583d0321a0320b40b00b00100941c2400400024011a460f00c20742c0b400d41168003144205500380c082100d148401d03440c030080447d0403001c0d03440c00396a5040c1a03503140300041641440303400c02c0008100b94940034151b941c0c1c451190340070408175240f100a648071200c0036803005020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 909814730 1250 909813480 909813559
    0x31107080d0507031706030706081e0f040b1501020606060c0705151e13033f03060e06090a021b0a0501020403020a09090b0c0c0a0b1e10140f 62
    0x4041e04640c0d2801707613a075040383d00c58661400c2000070742c3d21141031092006203e004004205c00c210203014240d44004610480240345c07c00c20003401c070748030b0100d0781502c0300504800442c021769400200700c1a0701c00140e00030912900c541c0100704842e848403500f1145841b46400025580c0c9a600c0d08014240c40705005c2903c9a60440f000d00c0c84146c8012501103e0104202d99980a04044440b401342c3e40c01600c80722800c20360740b0032030308042c003a441100783c840020100d404c00c195209100f5044150585d806202c495130b03c180060741c9140c1039901d0b603803100300d03c400034003c49425400303040844030b51140c417580040f00041c03a604184c141c10054031540d400041c240254104003041400811141908200c1a2019200e5076a001d801805040d5802400148000d03204c01c10004c3c16000c94106400e6411800c0c04c4641c200018048081c800e451000400025120403080b0400ba084451021444a0555107802049003050f410600385038414185400e0500d815207031042054181d08034440010b1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 909815980 1250 909814730 909814733
    0x1204120f050f041a0904050f10050105091c0314030702010504200d0f0302011118100c0f030e031005010b0d0f1a061c0c080106110c0d031107080d0507 66
    0x10303042100e03080203021040000c44002c4038090300702c4085a08000d08804030b04000d41c0c1c00000c9104030740c000341c0c0c814241700604c94000c07844034080340520201680940980c0c0e0358001034500340035080600754001c190000440f40407124280551541d44a0720b469450340005a0910920350400d03079610380142e540740c007000100140300100c20301080140f4141c1124800d6400020241404104020400c5868400000400d0300035041131213003c4001c8003007521a40860b812034444194030511510074014000d1070554680110349600000c1d800454504d140100c1e42c6055a0560704410000c0d010700c40c236841c481c0340d900944110360107444003595107941c444803007928100390307403505c421191271a103000c0e40b10341e1440e00b40740d402190303001c195400d9071140c54103511100111315001c035000c40107080200c920506a03014400c0b5050703c09070b442d020b510f001d12030005a81c4400d85a034681e04190100340300008240500412400310112000b201d03661b0f900c03000c40c0d0307080a100040034000315078041360840 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 909817230 1250 909815980 909815987
    0x20307060e1902040e0c090903070317060603011e150809010e0601240903080f090a090506060702090408190315050909120c16030c090f020a0903030e06120412 70
    0x1900d001e40d100074190700400740d2040103481802103000b8403c0303581d00107058122a060101200c8280014500d410501d044c104a580300d44c00504218001a00300c44442c0001c08040082d601410000e482907045a003040c0e44c54824603c00c40181034010184880054000400c0341c0401c401d8043e540c031000e0f60f0801102c1c05003512880307005039445030007000c01030000d80805041221402c0d00f5401d004100011034805035000c0b60305401c090700000d00000e07220b0858401900a10343c80d402502d07034207510381d0f60b1603d900c129442542c0490348010100b05d80d0026103400400700360024081c10070311385080045040c1e801a01c0b54120076401107a110300b1481048020241401c005102c25203562110b03203403c68072070740c503803010400d07000c005000400c0c03d074820b400030000c640c80c80c1c140c001d2501c0d03090703168200b645082840703100c0d00003c00d042002c0b144015000b170080d14865401c9444030304040341540d80c01d40c1c5c1440d0903009203030031000900105c0c0221000e091694061130141c085104440403100c4000e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 909818480 1250 909817230 909817241
    0x70602070c030c170a290406230c0a0c0201141c0f14011e08070e010801061a030f0415180b0f010e0f0c0f0406081006020106060e010c0501021902030706 67
    0x30032400035092076060824042139610800d035104108502c0f0001c60352040314030110721b20410b5201d1801000700410030055900c0303d50410311001e5403104c2c1400c440320080c0c080c0c1086441420185050104609560280d002404440d1050421400c5c0080403504440c1c9a0400300c20403000d0b6840200032400c42540d03128610301c0510105080c040107039412584181c03071f00103104441d0f014400c202c5c0b1081c0c94800081600252103600240c41900750369000c0700c40411300c2801185801d500c0e10100107900010a880d02a880754907141c8281035541c1c602681e102508000c2c0700b9a1100a20302862205415501c1070380c2284001ea800241d000c44141400c0050013002003101d032001c0d66520060000340c680d450751503404462002500710b03998444000c03d10341c1c05202140410b0a00c00b08002c02d60b59000042d05114406c980c43c3c0b00007103660b4040c01c07400da036000d210700c070b001c00c80d00f20b50700d089540308101d81c05103103000340c0001d803800c4034058131101c12940300a81d0301e00681010601c2c40c10040c2d54000d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 909819730 1250 909818480 909818489
    0x120d030c05090d0f080d0c050a1403011212020106090c111504020f210304140108060a060e060c19030203040e16080a0504051014060102121914070602070c030c 70
    0x3141411200000f0500000b00c8000190072000403007105410002804110b8040e01e10250b828884620050800f0b003050300724a01d100040350388a00a1050900c00308140c07812905108003200307816480f40c40b4540c041e400d20300a0b10855495040100c0c10300c03810300036004940400d5445003d1a004031a0311800e00303482080100440d080f1405100c0540d8644036a00c0d0160021960b0100041c62402509040d018011b140280c5010116000034040e21302605400030701803c0c0c98a13030490343d5640412030506103070301907100030607010f010325206810108090401c0b200740c942106d2611140100000041580983c00c8006902c002410300011640c0580b20b03401a0004c9185404c00c1c8107024050f08134940100490000c9558500107010301c0010840b01d0b41c03140c0300e01c2d4208000800c120b1010203e03e07003142c04a016104110700c3c642244140400c44541000000c0d442d144015080022104a186000c07642070100d410301400c0040b40c024402800c1841c40341c4050b07182c20340347d45001c00605809510 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 909820980 1250 909819730 909819737
    0xb16050301150302032208030a114008061f062c060d0501060e030d09050f181311010e030c300a1a070527120d030c 51
    0x402c00400c4404141c40024114280540c076603882c900f444605c490b00f814510700341d003500c007602020b229120000790301540c416501031045108483c0703115814411030b04184441c0140030075944c140f1f20b07465200d0041840d000b00c1c01e07441e144030045010306448983c103d50510741010044c00603181e160f012030075501d0b07924060544414600800642050940c0200400c0c81148140401c0201030619001505040080106850341030040a40c0002d140034040c80000c1201d18002505601d000180c41303990043c00e03a2504c900714241418429a00031502000e40c0250720002c410045420f00641d05100740c424104d420100c402d43e00b0f01b07102041d0a419a10b05000c3c12a6400d00c01d503e0104050203208002e0310301e8010703c81c03c2041040c05030320080750308081821100003c4400c1c2404514502c81ca40951a0f808d8210b90104490008241c00d943e0f901c0417440801c0540340c2c03125020501242e54504454421820315070402282118554080f540c08942262204940594051241e416100030a28 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 909822230 1250 909820980 909820987
    0xb0d0c05041d010905130b041b1215050c041401050d090819180e010b0a0905100c06050c090a0e040501150308030f0f010e011e09020f0714030306030c09130b040b1605 73
    0x211f990607412005800070309015200f8420680c40807074100c2100c000c00c00d10394904a07014031401c010010581e55800c1050941c2030001240c08006140e040c2ca00f903440c0002c10184604000e8010f45865001181d90400360b0b031101007144c0410880000b4002d0b41c06801000c22410140c040020054030744100c0c1d04407917500c200d030184590449400301c50f040d81d0b0550000c907a94640404299106813982e8801139104e8507030b40e2281c0c4000d6100c81c404400c5c900c68681400561104144401e150013031a513116005030807000f0403c0380c02103803100107401030700817000062900d505c9a40030b494152684c0007580c1c8003030008107000c80441c120b080190320005124600c074641d414055030302c040341018410002d8505000300c1e0b4030341c04400d90003010014840d501c011075907030740c06151400c4a600b0554043c1c0c0e4603030110760307004140c00020003124070601c8001d0180c10b000d8035000c100000c4403070181c4000b000c03c3c84e4a61a5000841c0d0940e164050742c007600c814012881c00b08045001c10b80001000020000e050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 909823480 1250 909822230 909822233
    0x9020703090918290a0c031d0a110d1208150102010903170a020c15010609050d0c030f060902040f0f24090504081903020901020c0a0b0d0c05041d01090513 68
    0x203141c07450320194031011005425901c03540100022464044410131a1900740c10700c4240340d015807100100b680709840030b000703024081c0d00080403072501f41180304094000b510180300040709420401107245005261640c048841d413600041d01c00d10f0020400481d150400b0f02c001201d651075030708070442091000303000d861140c1c0d800405844203c4071070f01500b0308890100741c045001fa01900c90413001981203c51159104a01c031182c0302c0c0078400c075800304080300d00c040740d2802c3c040324a45480303410120010520349507540d40401402c422a0994049688403055001a03941c1c1c010308020050358171007c502001002c0009041310f08084d0f00d10b89010205800c0c0100c00d446800304411038204090014403030390740d400e240c152442416130b610516000001e5900145030945d002c0e04074800280d0803500e004001030148400c0007028018001c090a041c81000c0041d241a08062410421880c1403820300d13030b951402d80e025031b0494119500241c1e4030300060000070240e00c96035500018400e5280c03040f0b03456 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 909824730 1250 909823480 909823511
    0x110d0f020405060103020c16050a170607080a1103010b09130e0c06030402060408010e031201060813081e030112050f060402060702090a0608060709090c08040c060f020a02060301090207030909 84
    0x6a420003801142c03140e000808a81c002c0c0e05655800c15000155410365910707050144210041d40105441a03c20541c08181e047c6030f03007034985002d0b003c040145265200c0340001e440412000306060b02d0079480b88040802a0450400342d8000e00109905a4840c0181c078202b00c10080080301e000c00623460300449009e0303007400044411200406840c06644d9442d2070010510901c944d41201c0415804e15001c0fa08850f00000103008540d0102d0f4a01c00740d1341c0715001128004402e440c80c100b940c110840120102d41040000c08103070030f101803107011408010002340790fa0b0704240e0050344840c81013019801132240c240003960700d0b0300b0f0150190041f031410f680041d145000f0544064002c9e17400340c0000798100143e80c42440a010381404176001d51030300070341c000c4c1038450074041c24901c0c0b8104042c082400f4002c107509801658030000c41d12145081500450b01001326240c450210311550750301802503141c1d040154080d010350000540d5440c00d40c10060040c0d103169114002103490070102d1498002e8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 909825980 1250 909824730 909824753
    0x3060108130b06011b06052509031101051606060b0316090302100e0d0501051f05220510091119080f0402040f1d010b0415030b010e070903140307110d 66
    0x209080030810701146100c0700c1e00d0f0205e5560700504851418090000b85800d50759048440c3c1d0688000501c02342c032486e401c41c3c9600d6103110003010310985000714801e544c0140040c180410003881026801501d51f03e8030001d540e0f1a82c0601c0140000200b03114066951260741252002c00381407456500303195501107100781074101f50480c10014444034401080da02c07001c951503c1a080743c020700460904c0a8844211300120100c407018420042000030582822403012800341e280e14030440e01d11020b50060000b4020052000e000b51440180219964900b4030510748041003510410303480d5183d000401d41c50007140403241c414802e0705030402000c05100560160700c2a81a14003003602203005640201400540c00c0d030035007032902c10400c8034041005500290180c0e10031a02071001088147e44250441e0150002a1074402c500005020b280340280c0426003219440c43c0200c1c44582d00d4031000381c0400d0305201140541c10000d5a24180168141118a9030804654201c0030500300c0d5540e8541c801d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 909827230 1250 909825980 909825991
    0x18020114070507150c0b0c040e101d100f0305060604050c130b0c070302041802041505131d030c0304090605310b090c090301060e072a02060a030203060108130b 70
    0x10b0241e40403284c18481c00012800c10790002110005042900c0410003d400c180190010000c041c40050f402c2310303168013008219081607224003c850441056100d5104005020002d40e0002d03450000f1549102403d2030300560103071010b84a282032400030001922800307040550300030020311a2a4504d0441d14603807040703aa49000240c0d46100e50700304541407101940c0040d44c802e26289400d1080b82080099180b0300344203c07002c0200d409001801038614001d80540303a0040050490049151581d900c0300355420010f43c1071000301072030a500304c0e1648e403110f010601507800c040340c10440f0400d6030003503402a00381207079650200705c00c19480d201c601400240c03012000e40c00e00500907a090655105904e144e801809107855441d01200c0724000c0c3d84400c0d1581c0c0203610740000000c050804041d43c42c002c20f500e6a4100e012a24207281d08203540418004194440c030070704000c001030384d4801c000e10300c5484986002d0303128a8020f0014081c5880240094100c50000074484005005c150100b580078 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 909828480 1250 909827230 909827249
    0xf0309030f06040506130501060e0f06120f07050609210f16080c04021c06060914030309060904051e04061505060c120d0603020301060803191812031218020114070507 73
    0x211341e4201f59000d0071743c550210000740d02e0103040c01540d40e48004514030a0030151a4010700100104106589010401c008400c43e044050b0030b000c0e0b850480d0083c0020600207103c01b42e58140d00440821020410001c0744803070780540f00643c0541c90500485410402d0f41400309403203482c0008081d101c1000120f440d1190390700245005040a42120b01441d900180740c0801845881388805070081000340520998141401c8265a1030310340042240d0588a01602d12800c0003082d40902c400340002500c1507880030501107500172065054050075215501648011411800c3c00407207400511464118501a040402c82d100c03504400180030310003005603c03245640da000310207215000f0401500001d50550900d240042c98200000141000390035072085001e2001c01c100003a181c0c0b82c01c81e503505043e510322000812290300b4185000c040d25000703045c035042c0500782c031101c1c400f01c034000c0b000926041100310600d400d40d684219505044507280400d140303400065251903035140f4140c4106040c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 909829730 1250 909828480 909828511
    0x60f030309051c051c110316020402070305070f1a0a06060512061c0606090b01030207030c03030b01170405010227012016180506060415050703030b030f0309030f06040506 75
    0xd681d1500610482c940c0007003d450003403120500680c4109980c05d040c5000610003011550656408011100e00406900d2801c407030010716401e02029401c0404260306201c030a011300380105480000d040102c41c403441000c03118104440051508000c080d0250b481c1a280440511020745c1100c00c07070f1030602078113611140540d030f1040014010382065040114954a8034034180c20081c40b13070000c105484903007c003400000d0900004500b24052004e001d000504840c0300a00407d0180d40b0403090b156049c5040758903000000544504c801003036400312090ba50010f060500b004403112038800280703940028040f001c0c900380008001c41e070b00a1300071400c08102a541035107443c08120b4a101000e00b00558201d44d07a03135920040f0b0b210320b82d20b4199902410f100c0000d585141100c05c8506036014038041c45849085182c08884075040717a40200c0c1070590398080420300307940400511481041203001190b40340c040b03070700341402c100e0780d20075030400c0c1c1d8400707010311000406c04200b9580c48180034120144 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 909830980 1250 909829730 909829759
    0x120512030c0d050414030c1f09020a050603040501060906030f1b060824030f06090f1c030b22020901030c050c0d05030417040815010e1509090111030a0f060f03030905 73
    0x170160f03441103221214030000176213843c1541e010505400c0d802c4820180180090041512020b45a03484030003035105046900c14082880c3c400051a0480c2c041c0d03000144550f2204040011602503070000e0380c2e200740f024400300030450064840c0554104403002c3c0c840c0d46140400151803517070003a20001020003c80c00d121150740440801513034940004040b01c0c0b101a8990f0b68988404083d6406691400381100180c026080080e0030984030048010390007280440d01d0040300108031880c01a6803001d4410034141200e0300b0640c0040700706084500c0140c0e1020510005021104ca60961600f130003001e101c40340745038401140c4949045114103209a5a07900c51401c00b41000d40384507048506080441c0100381c04000141c0806606059000da8607980d0301c940120580f0702c021a1009098a202c144244160808440c100d070814400c40021950034001d032040700341c603001254552059940c540382803c5010150007110002c1c994003036507107855402c54400415800c441c0c02003a0245030000307030024 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 909832230 1250 909830980 909830993
    0x1170d0f0c0209040c0503010e0f120a0309050a031d04060f03020402030403140c030c071a16140d02030d06090b033304060b1905030d0e120106120512030c0d0504 71
    0x51080e540144140c80e84c0c5050300c0e1819a84255001c1d20b8080c0d0710340390445902c241c2c0001c0300300088049030004e01c4041300c004403a000301c1e88401928802c068452170340f400090420800301d68100e02ca07848020000806d00480342607030100d060f54130312582c18030f102040440641c05a4005894040d20050b83c0c0b80e646e130406807000c268003401c01d19081000100c01c0303090134000c405001c0d030010020580e8843c50703841107050b4111100c00e050100d0b503070040100b0325040d10045008003419100741035441d070340c0940000503400c002c0c915100f4005030300001003042008140d881740d03034041c0c60b46410801002c0a00000b1a03034942d031100a841c0c00148030084040300200c10081e01035075601350304c401c0c02c692401d4500800603008a4074914000c152980c1915011460000310000744c40005c0c0082991481e000412104012040e940360b41201d4180c11800020744280501c1001c0e05204410400c0c0d01018a001c91401c02d5135200c880d13269805109004440304200120398000031410340101e05902c407800c000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 909833480 1250 909832230 909832247
    0x30916050a06050f251505040201050405061614030702182a0702030730051002070f140a030908070e07030b0103140106031e06030b1b070c030c03020901170d0f 70
    0xc0d2080100e078889010b0702000c00d806401305c58400d02c1e15000f46c0010050441c00d440c820b9400a003c0303402840103001a01300701003d00210340d400e103c9001e0181440d2903040072150501c04100340da40001640100354240400c0e400b080035402d10b409001c4e4505078140c802900d0085544841d0303e9503901d40f0140a0107800180c030304d0f441d0028141c1c1d044aa80b694821058074441c1070000c00c1e20b00e288140307001003261851580d8034a4110003d40340c0b04862080880096100342000c88d041107400003100c020600a640900454110100030008541681409803490246503c014015409450f0900c0745201c40005160009410308020441d0100400186e014114800c2480c00c18079000c000010425410f4003e04140701c0909039100720b40c5082504081038030700b1400040e045640308400710b0412074800d01d41561240c5160340c0b160502180d6502c03180c0f038035487d0380152103850442d40c05006600c2d00701e040038010803010041c803400b10400c000b850303120055114200d0520149040360210103004d610070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 909834730 1250 909833480 909833497
    0x14040c020708030a03150806060a0611190501050114060f070f02151c0506060c19110a0e040209070836030f18010906020709050606040e0a02030916050a06050f 70
    0x140e82c0c8900c41404002c008140250242c1b040345656000014485000701784030f40a02e03805000c28407003d040c240c0c02e4640d0036040180039203d02c034800411007225000354401c94100d20480011925500d00f07140002d4034020b0b030350000e1161200300720f03c0983c0e12007141112070036544040410f0404545000154002c8076070406000e200e0000034490300d540f00c03011912190741c000100d0801603030710707402d05100403402002e41c4520395611003480d10b03280021007140c901c0c00e00c0c0b140d000060011100804500c03041c09035402041c2a08281d07003480304504e8805921540100e0a00c1d118110b460079204090106070b14114903a20344464440c0d42c040300005c6c103542014140414116551078120f006104207950141042d00d8a80c4060318800a141d846400c42e44112282c507030044c549141040c019170700401c005407090f540035104000002c3c140c24414101845050b400c54011f2b1280b90144c0120f080070004140302013441100c5400b03100503030302e0a0411054940354540715480313903485440840c0d1882a21407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 909835980 1250 909834730 909834733
    0x1902220509010b1b032109160b0f030c0d1b0201140609010302061809070216080d081906090908030a0b040e07090c051e03040302070b0901020a080d1e0501050a05010914040c020708 79
    0x50502a945125042d14040d01f179541c101c0304502241d0100da10b850b0b840740243e00e00310b40104120581c01c0480c0300610340040350702c0041c5c4d14000340e80c0766190488545160801013035031079246d80711f590364081c0305000e2a1400322440d41c2c2c00d0700e02000000e01142c01400b00900c0398001088051203c641030840201d40d00c000340006100d41040302c0080e503541a101c0d003000c0545071050700401d0403500404d118000d181c480d100c170161a2070342035588503500310406106030540d9541000180c11a224000c009502d8050080c4669a051202c00c0310291948000350360f001e20704060300f1100141d40040e5800c101d0f0440400080d5002e1b0200b070440e41ca01c10000100c50300e426051580d400103070000001c50007240719400b1141d00c2a034070180d00e441c9004400102e40541c004118440201c0c278048010810749407034140000f0ba40c4013103415070010310010402c111030140d5034801032010341003403000d01c00600741c00d090180d403085c03406204040c503c3c0388050700d5000d56140c000d070100c407034020040c04000c1c181303010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 909837230 1250 909835980 909836017
    0x70516051e01360b06280509010b0a09060f0e03030424081b21100302042f180a0803070201020709061d1902220509010b1b03 55
    0xc8000340a4858603401c0400c3c2030001c51000310030405204400981183c90310322040528464580544410000f00f89542102140300d103a000c060b010f858941d0440c0448508050311400d00d0244040b50700142c00c62402d41400b08020810036420800ca501240d900b49031802d148060070f0022116225094800ea40500c4080382c0802e498401c0c0c48a0b1012055014214005500c0c40401302d400320f20550701141c280711044c4502d000742c10201e0003000704030241c0c08090301082d848190495a0901201c8012040000d81030074400c51806018000d45041501611903583c80b18000b07500748103e506071915682c0d00006011441d000070a8484104404001d0011180580e600d07542c603140c0d070003282c04034014007900d0700100b2000064841d600681d20b03040c03002d16109401080c0d268640383c0162040c0861501d02001c2c000c2c0c2d2032035000030700086a4003201d400c4403490300102c24800c000306800c41da1040d481c01005100c24440b4005482411494544109008054856150a61152004c40030803080c0d0f16 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 909838480 1250 909837230 909837283
    0x63204080f010b0f06040b160321150602030a0207060c1a07050d050a150e040c05030708101b050a050d1b0309050f0105040b06040b040b030a14120307051605 69
    0x1984840400030082d0780d100b0810341013a04000740b41c840e6001310300c0204414000e03417402c07690540c00c0d90a901e00c28140280750a401c20f04d8186030b001d00c03204c6050410f0b1036649200c44030542e149039000030441760004504242080e42c001c0e49485181c000d1078104070312802800c0c02d0000360300b01400076400900c54440c1c2ca043c00b440041455203d5140700310302d54100404108981c40c075114031002c2d407003030f807110b40c10303007410480301440d118005082543d0a04032030401090725502404004010600440280184a03104910200390384c2c1c500307200f080c40c43d00b0303055108a0703a0300078080700c101140318580990b41d29400540756000303054090341c2070350701d1032090501d4000540650180c81e403607000e0021280e48103140d5280a00345c80049078000c1c00544800045a0241490382107848031460061001c87d200c01d6102c007103460000e00c032505840c14003c04400c2c3c1030034401804204c107080601c60b1030f2803452804400107410b80c45151800c0080b0180a80000c091280034002550907244441c50041282003070f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 909839730 1250 909838480 909838483
    0x4060e24040602060717010303050306011101111c02090f060306031507030501180b01021e0a0f0b040201080f01030809060d0605120d0909060f1809080307050310063204080f 76
    0xd0241c18094400d0f100401e803014000c01d01c0f041b40701c80310704118400c0da095580450380e60f00060710582c180300682803010600c000a0003840c03058a400c00405461340e010b940c0303c030b07070700d001002e8030203403052040003042620340380c1c15800c0700e62500c2541d40950381d07110300303021038074004869022140f04105030043c0060345a06400150403254ad007000c140c403142c40c407502c01040351603503010745000d41c0c010780503840c0d03851a461224510702810802d40b11007400f161141c2d000c4806003a01100c1d000d4003401000115a0000c4002d0b400036407500450b4000d41c150360713540c065407181c900d030107204800c003050500d000e048a0300312802500c1d01400d81889000009010342d900e2020103031440c0803482d4103a004c1003801c41c034800e80c0125074040300d00e58500d9142ca0650421030984060601c421922490311300c01080a207801540112210342c0c030b1554a10348500c0c8018442641e401003002c100101004251031500c40c1c61b503c4207140d128140b039004c1503511001680701d00c981da2145078507014140507021a19070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 909840980 1250 909839730 909839737
    0x1c050c061e0615090d05010e0d0503061c050607030504020316120c090c050a0c05100c1e020a0f021e090703020408010b0a0f0e1005300a030504060e24 66
    0x403404210401d0b07110101080710380004a036264021200501c80c091583c508450700503942c4e8080d400020f140801422101e081c5036140f00c514000c11741c000207201d45401c0044224641120500382401c0300034081c1d5030303152541c2c0040c1000d4205612240410155075040c0095001ca404c06880034040a5442c030440d9040b04141109880e40f44900c4e000241400c201d000b6848000f1141d07582c149401442c10050b2020522003506030340c184106064a00840c14138400c850300c2c24010748505203220ba451542c10142c941103003048003150080d500301b0000403d080d041802080d41115039140c0780c00c003072061807e1595011202540800900e06100c4181e41650051081d60341681c0240700020091081c03001a1406100302e64491100020800040e4002e01c20b158010056aa40c0b07503166a58000044220814100c10300d030f4460b050340301440380303603d9042d107034484030030803000e080000ca403524050540d004503c01e07101030000441c2c083c200742c2d540c414006c0c80d480700889111143c06403081d91925940 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 909842230 1250 909840980 909841021
    0xe0d120305070c02100c0807080d051911071e02130e07090b06030106080403021c050a110a020f041508011814121c060b16031407051c050c06 62
    0x1e140c100850342081c03081c01e9200307110742c001c3c0030100242036101c001c441150003002d040d11100801e0142d8000296603400030450888005004961030524580c41455641c448a84011040c904000c0101c0c94919805aa0080380c005162a0040e018200940b42c080d100c1140254002c9404108034042e0800791300c54501940c2c100209e910b61313a10342407200d044454201480360302641c02e100412400e0300c61041e490380b00b8400d106680b0241c00b0074540300081c00d8805d910501045011034069011540030094040e000300d270200410800c4a6a0081110501142c50050040e0303100c40041498a800c0241c00c002441c142d00204100101c200b800c241d01c00840b5022201011045100c040c03040000900030030f169819000d05107020800303c1c8202851199824000031036803240d500203a846104c201800f101188000c0600162429140080800038200750018114209010300d8000c10000550b200000405a9070b0005558843c4000d480900659030915100d00ca810100000c02c4000c00c4008c1356070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 909843480 1250 909842230 909842237
    0x4050f1906052101091e020118060e01030b0301110f0418060308030f070311040e091501081b032b0f02061e07211d0109030509060a0e0d12 61
    0x21216103410a080d500c852003080da12040a101e5050215201040c40c2910070045000291050159a48106a41ea103007886004103803451420025560405540e0703501d01e56880070144180e0400001030903001d04203000038101a65040000c0090b1425400001440d904d5100207803220341c8002941c03c264828001c800252042445a891070702c6540941410340760300001a604540e10100c0f9425048801840102015107402014074000b000c000100080e0070055803803003484c03030f180300100d18250320105030f10100280e500040041140c0402d0143d412800c10001e55403051886000030b180114440c5c000b41c1d1088804103c1c80c100d9600d4040411020380c0b616650340da104420002e0342c56510481d400344d14280111880003540e04040c1019522031403030300f40032201c10611281c1b54a00001d02080b0300c0c11701c1c0e139519511044000002881e40300805407000b44414402a5402441401010f910358080da40102e034501140c1c0c0250980821008040e01d000c5801000e402c002981c0790041e00180c020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 909844730 1250 909843480 909843511
    0xc150a0b0a091517030706050c070201020c121c090509250512061c1407081b0a03061805030703020705040c050310051c050123070207060e04180204050f 67
    0x2032483d00860040b81c0d1115201e4880a00d45030144070f0000d035664800046001c2040385100043d0584191030242540c3c10540752501405d10005e03241c0041092000e1162014004100c030191000a00701840ca4400324001c801301c5030740106940020310354000a520800c040c0c02c100e09002e2920703001c0c1000c4c40405182518001d44a030a981512500a01003090b800c07480c0059070f5401c10101d202d02c0094507105044201880c5e494030b600884000104800540011000b080808410810981c0602c0240503407040a01180f0024009001c1c038400144081c1c1c40300c141003006080e0019242510390000292683c902c107526000f92180018005d81d4811854001543e0b4014402c0007503030310407803040760f03120182d509000401c480504250042c0c44d40000d00b002e940c1c00034100313000c1c02e00c2c0f14400002d014045188590851401d01004000c0011540050802c000701a4070034410304402070140c500040001c0a24448440c02d80101d5020317402504003014030040300c10b0703910b04510501c0700d14840b051 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 909845980 1250 909844730 909844739
    0xe0f0417040602100c050904021204020a06030b1807090f090c0318030507110a090212090607050c06040f051005090c011202090d021309050f0706032f0c150a0b0a 71
    0x2800749000e03490041e4071881003103c40780036943c004180c16000d400c101d4103001c0c0d036100103026a40564003101c43e0490103000c5c0401c60402e9a039403400390050381000d019080c01000400d039510b07004211a5081d4510b02c2c080342045008110b4600503242c0140c04c4000c035a201c0055002a000302415540024a00000500c03d4095510b410300843d506544403860113505803250024a01d2107003a02d680a002c800002420080320303c010020700031907840d000220715140e4581410000300030201010701030b040010b103c030307171001140311a402030303002c00400c40310281030400d20300c0d21182840c003000c0d480c80e02084c400e184a000944d0725851800743d07241c22200e19400405000d070700620b030080381c20581c0d00700ba200043c581406882c80c8035021a00000380c00c4d1640c2c48040c60110860452800c0360042c071800d001b6a41e01d4090400345c1c85a81c2d100516442494250076907a02e03c002c10849151404581856400d0040c030130740c0c240020403a2034859900313080d00c3c0400102001e042d52449940d11030300018 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 909847230 1250 909845980 909846023
    0x1512060907091205010f0501150801080a0c05060c01021c020c1b0a150311120f010b040e15011209061d01110a2708280b1902040e0f04 59
    0x41c8229026a51064240c2c43c1c800c4201c2c950400c520304641e0340d500c40d203000b0400750399407140b14002e0000c2440c100314402d030210064591401a040700c046900b000402a01003040f500c02e0200b15201925010395814064000b035009000300c011786804000b5180d10005264455005488500410b170305440760400d407000c00c5d141c0400c44000c02600282d90003c1000508032001c0124002045070902180c3d840b050541c070002640030004031060784031102c0601c400c0600d0000d10a001d440e00c4940d40349428141400c0705c0c0c0322032000301202c0045e83c131254954602d174440d280480c080040c101d41071111483c1071504e0405001c8a40b1107080f0b59042e42d018520002050140c080c088500192051504507034900468080001c01074085025100744946c07c03035842038000150082603003901901c420840b44503802502c00c2050000090341038241440f2010850544e011500107403058054014100c0d0655800d02900036a88107140300e07000b400810441421240178980f2480c464a4240310414880001342c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 909848480 1250 909847230 909847249
    0x20d051b09090d140c01060f09090501050c0304211b1a0a02070c090b1203030703050a05070507030f030f0b030d03021e031b0706061503020c07090608030f030411151206 74
    0x900000da804c071044481c001c3d482d0010403020081c0d400109070740f612502d5020081140760320407001103640301410010300c582803090715006071015490510750704103501c0e13091100039401440c180700808510401103403070080e0745031514482a2242000540342d28281b90484d0101080d207078155240080c0060b044400c8c5208464885522030080f413101420200705c003005206e246000c40d005105c1d0444114845403c002451042c0003550340424180740c00402003050302e502070026414001e0602980740080d80160072441c0000541c6000a18191403124420141c0418604150503014403282500b00c940c1c540c000f4801e40002d42c1d689035607150725200340322710fa21084500c0954580e550400e400041c4080b030090807424000c80d80820040d031a52400e40120829080080100e58000780c4c40c6104041031280c88020010840c0402490707261600c1c00d0b40307074032584d440c0e203803001d0300000003c2c1080190001c0a40065001e00410103080d000910310f01140c1c810300c2003000400011000400078517001c82d11 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 909849730 1250 909848480 909848503
    0x1d04050103210e061e0c0f030c0f0d0f180504060b09090c030103081e090613031101090b16020312160c0f03050a03080403110f06070f050412030c020d051b0909 70
    0x441c03410705d42c022042d0f080501040050400311003007090b4074149108002c1034188001c1030010b9603461058084103480c0500501240030746070060204010002d0f0400ba44140e188030504002110101c4031142144010094001c513230b00a181c01e04c0410090580b4000d4030385007100f45cad07003920503484040c80c400040c0401d120040c1100000c12054040c03200000034194035450170942213041105040002e0f103260002c0c0c045030303031101000100304144070000484203081e10007820001582420316007000303200e2091020303d01c0c815400e90304c51403c40d1800c001440b180a604c000750761321510300b80d40da80e401d0180c070b43e8141c0b0703031016200000c10801148a041c0044950040042c80190090794080e1100c1d0f800410039003d10014200308415000c0074018a01d4140082c0050011841d20310000b074561100003441301c08111081c00284286480354502041311501414500d0480a151001482c1c0b10440d00b0010880e000d0ba0310050103e074040080e20540d900c040b90000e245503589600c46940b408100c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 909850980 1250 909849730 909849739
    0x6090609090501080a022b051b01030b0d061a040f020a02240a050c0412050c011d031f020408070603020306100e0d020103090c05030106030308091c09061d04050103210e 74
    0x64017005140071524802d10780c01d01d80c1c0807504190007424108141c42c22540560f8150041c105440d20191462506110b4100900b820401d01c2100c801156201c0784102c4020700b000d0ba5103e10051300600703c0400d2186002c010418042e13101001346140103034000205c61005031158500003000340c040007c0c00035a0343c124131441c0c100d03503440c400c90402410700a00303030a040200401c00400c0903640b40c03400d4130781d442c00b507001010180500f030f000424803090b516a440c101c2e1900440d1459680d4089446101241c00c49190000d6440800e441e100070320036a40300f10f2551080480000e0b225070507130051442080120f9100e0b102c410b040c04143c84c03032035501d0b505561001c10b103521240150b000382d001ca01c0c404e0180721740740d81c09616280840d084500300d800030b502164055040040e0010700304040c51421040382c1c03030045081c49402e03015020407480d001d00e20501c05000c414240c00c42044c0541314040200500600295960781040c005c00e00303854000882094810b0303900ca1640d8021000d00d9a01c403005070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 909852230 1250 909850980 909850993
    0x305220e1012030806040b120c091503150604020f0724050403080f090f0105130c050303090604050607140d0903060e070503060a0b1201020304060605031c0509010309050a0c0609060909050108 84
    0x2070f41141c0c09440184002d13070059884855140c5601d41c460343c2c02c450300c0c4040c003c18502d0f0041d420450200002000492524404a0300390b907142c4020034204181c1050f1086036920740c844800081c00b9004030b2940c0c02d12004c1c08a1520103001ca41403441c02c2d201607501c44046090841340c8203a003540c400312030103000b15649102203462030180e02c1c2d50310b6203c0802c0003520510000c0f0780c0c9a500b51481690b2044007071140c1401036040c048402d1840006040c200e00852401d6005804114a8022485042d200d41d50110744c00003407154800314210f810001e40705903001c108045c2c40280c501d0507540010b4480c54a00007d00e084060000b6105064902c01001465960b8500034400058200c03185400d8104c4800d00f003103045200240040c5003d0352203038070082140390900060601d442440141c07880340070b16001036a401c042c0c1210490b42d07200820f01e808a51500383d41005440c2024a40c4020300c00401c03850006246030b03000c102076055452075610024801e90b64800c40e42a100b0a0042600316042003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 909853480 1250 909852230 909852233
    0x309020d020f0d02030a060509100b09040602070c031205181008160c141c090605070303050408071a1005030115120507050901081f06030b130305220e1012 68
    0x80c03090115104001e003e100054001e902107030500c1184030b82240c5240d29134051006500040c44140000341c04004204214285000000e462040203440500700540c0000c5103814040c02c29801e401441d004003440c0c000c0d0b4401c440044c00e07a07004240314410699020410506854107074001c030707594609580d8501c0e0a032501541140d0503504450440148801c1412400024032089090002d04485802404044842001c200300148103140c0342d9007040b40c0f50078240b0007150040c00742e85d00241c15240014031941c03146010310543c0305e4030401901900e030311030041c07140c07401402e2164403c8603880a800c3c1e00036914001e240c2030707448007a01d041c0816030203070050040f10000d217020b080b01d50040c400c0350200c5a444001c00d401842c20b82080046402c90348001c8101c00d0900b00301c1940001b07107141004000e00d15140e03045260805000c04045040c1d006090050500c00d4007607801d0f01114400e400500f81040d1780d1030f11611200e114950f90b1030401c4c00042c214194100b04001100c0d01c030150540440c026 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 909854730 1250 909853480 909853489
    0x90b07110f1504020906031c0503040c0302120102091906140903010b09010f150f091418010b0403140601030b0423160806250f0302121f060309020d02 66
    0x2120400e0340c6100e42459035222110400c0028a00b800044000210341441e0060044a000080426000f6407158002200c001e000361401c0101d24207a2a2182d229229880c02c805800020f52000e5400002c015030040c81c00010350003440c0300082110302ca48103081da5074102c1440d000380d1048001060040100d094801c0743c0b00000c00082c00010000070340d00c00020001a25180c0c283c01c0003099401c810414003048081d204500d20104203400d242a602482000050101c2941c1c029814450254820a1026100c02000702a10105102d04402d40e6848422266503500148002d565003c00107050304d41c0850041030541c16641c00000c03400342d5903201e4580d0031480140c0304900d06030951440010518003014880190203544100c0c0d911003d9203885200f6142620103131103d0300c81440181031070b0411940551031500c1290780d00301051002c100400503402070003605014182b405c1030404100301d10301011209481e121040080d06081034849100b10f0882e42d00c07040007034019420101e640050700e00b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 909855980 1250 909854730 909854747
    0xf10030b04020c010c0804050d1b021c12180506190302220e040c05010e0d390608070504030f020411040b0c07090e0a05060115020309060c06070909090b07 68
    0xc001e0400361070b000342c144000f821100c00c01582c0c4001140360051000f00301052016006200040c41c0503001301c01c1e981e400402c20001640c009105950a8070044283c603030000d10380c0742c1560014441c5004000610740608040202040e07141c20f0f5448110102e500e00c1c140c0143d50111302506100d01d00000c007460280c0003540200eaa60b015103501c00c803101c00d2081e07107281e02c002600030040e2000d01400c0c00c0c60080d688140940006050140c2030303a1658143d182c00d0130326030b0119040040004000c20700903000c900b003501c519100c01c0c2c4140003d0a2600c0c010b80d01c510000321605903071104a1644c4100040724180a01d0000503e60303102ea044420142c80e25400c661924070342a8103c5d89081d50f038029000c11540724500c044015000048100583c60300d030b10134103941d03034241c8014100c001c03010f60350b003600d0f010305000e829584000a00c1082c049842001520080c440146c84a07983da40c444007402d542e501c0c203e607002d0000d00c0005010581612501846410951150114a0303680392038600351000b59 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 909857230 1250 909855980 909856001
    0x40b03060604150905090a11030f0a0b1c02090f0f0a0222060c06151409040c1a03100614090d02040f060b09120f0715020a0501021201140f1003 63
    0x14040c000410f556165181d0b040203c15140c4407035101600d031400707111414000500d900ea0aa01c0e064104680300c849104a070780c0110f006264981c56a94290050002c00600041e26044001a103107154101a4090b81c400d469000311203140715640c408848d5882c03c5011120000b1882441001c682c40102070380103081e210842134085803944441101c450500d40070750f40141c0008801c0360040c01880100e02c15403041e49409100c162400f0b05260a8100311001c0007000c80c06501c00c80e000800344840180b507500640080281000e11301c0080c01c41c203035a0340043d5040c00c1812520007001a5141c000c2210a01004031841128107010900b810031484004100003607070001e03107940e840484040303580300f000040e00500a006466001d990180010b034409031110100540c813466940c0d0b141580010b01d40d080350850813002441c092800402c0342000050b541c01400b642c0045400986505201c154505036240d104900a45450344010015844d0a0005194214001421201c00d05129400000f400c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 909858480 1250 909857230 909857239
    0x627020f060424271d010e01050112150303020f100e0606150d050711011a0a0b0705071841060303070f050c0306011e0509070309020d0c140d0503040b0306 68
    0x6410b0241342d582c16030440744451501407030b41d04060281041111030302004810003006a041036041c8080880600b13018040c4c02d0500080000d06100c9070f149800c411603000c18101081e50f8180c3c1d134030f07020f541e80342039002c0040e50f4015070001059040d074038800c2001c00481d2100400507529080c1c1400040841c16080e02040c440410160b81482028007589004180d01d03614400d58465481c01305007140d40c2d000d505040c5141c200c004038003070303036481c1c8143c010380c0c13043c0100c1c0780d07500501d1810529001d030359440b402c814001c00d0f60b54003e50456501200c2c103a260800b40d040c021078a550000300c89500c00d0031120b46d001480000341040c01a58a812380e11080c040c0440b0b2070300343d8030f4807031180b05e14141c0c00c22541580028003e4140d03090900c5141c2c018280c80b07000e0400c0c070900d440210703010011400b50b18003e00c001000209080c0c8280c004070000c640143c450090040e6504200314103022501880c682070b8080081002541400500e05000a401c0005141800d0400350103041c2030f80064040c580c072 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 909859730 1250 909858480 909858497
    0x1203130213140f18030409180203060f0405010b0f090f060111100f0f0516030f11030f09070515251a0a05060a05011b0627020f060424 59
    0x1541c46622034a40c911910580514603480e00301c000c60103451004050380f0040c03081c0c0d032203082d0a940000c107540603900f00c2c00c00420ba1000b03904002c034848111090196040c41100144400074200400752805280241d000303005c810340b50401c0c82004e5142c100013a0300120398030000340040e100ca008068104905144c2001c04500b03004409203005501e00800c2045640c5040013180c15030345109288114140a4003840b0a142c580c0700b882e000c0300c1d0380201c04180b5803a0441441015100d902000c424800040300544030b0034280c405c821244800c0324407600030701c42d03c60302146a00d0071541c22214a881c080c00185081a10790340c4a083c0c2244805000c009036584c00c828000580038143d040740401160341d1064140f401e10440029200c02400c41c60042d0f80d102d03804c0c0b03c00e0740d05c0038420a0b41e5900c10000b1110200f24030b080b07001400f00c1c0d041d40e280c044011a002040419580812039820700840c2c074292080c00c01d1003040394600c01c0c3c2c41002524480b8411202e210100344840700724030051810650742 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 909860980 1250 909859730 909859759
    0x4120302160f05130b04240504060501020703020d06020412060c020f0105040209061003110a020a030f0e03100b130c05041d150d0807060c02071d04050d030e0a060f0902040b0312031302 81
    0x41c1e5015030307c6030001c440c4190309000d0403c29403541000404088030144501d525000004c2e4a800450001074084c20415528200b44203180c0c0480700101858040d403a0f000c0080d050440c001c00781074000c2c8005000710301400d50b044105004041c0a10780050890200d0345514040000113034045014105041e01d80341c002c0900784845020f89a94481c58000e850056840d140041213207902c91303001000d0020144c6c9901c059180003618207481100c10030009030f80e161600000e00202c81e83c1f648c01c9400e038100000e002601e45d129020380202e512200401c090450f49401c03050a0302c9040b141003100c440c4881064a252420300c40e120000c0780175046a9141400c3c81d1036003010b4800c0d40b8081e0300507170f001e0762007001801c07a41c5401614170180d01e06003054a0400d56100d42c0c0352802400700342c08041d21164511032904090100e00c03c202c0e07003d01c04002501c400442c500180a1000c07040c0d1040340341c900202d00354103000c15100024400148100e00d1a0b891718a584040386110b0416600100c0100b0b0204 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 909862230 1250 909860980 909860989
    0x50f01022118010804170d110703091e06050f0f09060c07031112060f071b030806040b01090e1b040f080307020906060a0c0b180304120302160f05130b 66
    0x505049040d0005590b110214107800404210310001c604000c0c0c11800c000201d000362000c542c605104881880e5203040061080018101d0070300840720311480018a0020160445020800c460b000e042d04d580400c0d1001000011280c18818400030510410490b198000c03200d004050801c894600d131401c109406000c5a03464000b8110600590300041c014800d2280780040c10240e03020031039180d0201c2e00440c0703600d42c43c4c880c080c2c54407052500c031340007040e9610b00800c07001030b0114140c03110107444001410000c12400d8141c4926001d6031400c40780140d1540b04000c00e1003580c4440e1010a03a54403031495801410318000c40e80341081e0810300c0040342c800600c40b250001045000d00454441d00c0c1801046032808000e05001e02c6044100700410529400c10802148150008000ca8035070352400c030100d5045020048036440c0740000030b000705840500d903a4081d00c0078004d508071344840080303480000c211000b070b01840c0c595000302e80c030801c070500d004814030ba6070701c500b400027150380941c600104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 909863480 1250 909862230 909862273
    0x408030705030d0e03090d060c02010608012412050619090807031d0a210215071211070f09050403050702090403120b03060c19112514010207050f0102 66
    0x11182a000001c0b00060440f80380680e1218030018000b4515007220800003503069084504018007040c0ca558159803142d00030b51110b401014142d0080c00aa203441c5000c2480d20308018242088a110030804980070401c411506a2a60f00900401040d00c410540c1e4030340300744114696807400c0c0ca0b030880754000f513801c10143c1140352080d143c0004107038a0984541404c1c643d0120381e07004400c060710400c001c501e08080c0d4600c407405612011813403039940c004a4125114008085001e020014810080040c0c805141c0d0f8005c5a80d41ca10b0f5280101241c4243c48144a02c50446044140141449010510791055030001e1103428403503e025420b40c0400c6a082e412241940031072000000014408494020031940d40c0c0110080c10291034902c51010f4540200003644074160b00c804030f03080003131340180d000c02403d1291204a4030802100300000106924402e03540d02c03080c16911000800009032161451a41c205801501c2c1190400c0c0500182010701c0070b4940c118410300510a42c01e003c2807640 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 909864730 1250 909863480 909863483
    0x605182809090c05031605011206090e06060a0509040503071106040e040515010f0305150406090c08010207060b091509191a030f0a08030f1905011205061b07080c0304080307 76
    0x1280b10040d07030405903402c1c42240d0000c0d0003504a00031941007003500c41748013004d0715001d080a8084200d218a40401851103800501c0303050310f00070745160358080c0010101e20840086461441031a02c480c2848241c900a4400401581c0b040c8070303d0780010f8201d041c00882c10009030049040c81d0b03540381060301c2e0b030303170305480541e04c98102035440088002c0cbc0c0101980980241002c0c80301e41031a60303407559669290000e940c1108505840800c040000766080703030f0b92035500f012010301c1454561110500030b50050108960032480c14528001d030b800c00c90071403071046e0040e00c080030f0404103c1c8248040d0f8040281440000d0a0301c4650042401a903c50440c40e1261440d5199104140c00103040ca451a00c50a80c000c503400b00d5080b8001903047c0382200e41c083e2218008210640b1040b4410b114179803600c80340001d490800b000820440201410014640d01907401c03100c0c2d81c2c566108010410060341c0700c40b0003600701003007501c0110300303084001d1035800441c8045a1070907607980d0b21a4219009001d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 909865980 1250 909864730 909864749
    0x10e04110405190606090f06050c191419170a0c0c080d0e0303070803273a020c06070206070f240e060414030702090a1506051828 57
    0x301400c1c4079410320504d0060f01d0360303040c00221242801c500c8040c4030400e200e12001c0080000301e10020440502c0142e01011030100100e13001034441c0340c1881404041140c45003113100301902c14144001c20410b2040042d00044030094443c02c0014107081d0380e10520700348d801c0c41802200a4001400307844500010014000645070343c8400c0c140040c100c1c016200c40ca4403d41c070510642020486810860ba0050006848501d64185148a4001c0f00035000c1d40b86106008034501c074500f42c00314489080078240701544000407000210400700d800083d1040d002d0050f0b0007025108018200f20004010090005050b9070a02000d59603403038a1124244084a80d40420200041c9000b40b800040d50002003410050018040030441c06076038110080000e0850341a203510214400018000c41d48070540180c03040c0c9051411501d00009001d000c202006510342da040d002820500c507a00307a0b1044201400c00030868040c4504001401410340100d0f403010109000b00b694110040c980d07c0c000703024940 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 909867230 1250 909865980 909866011
    0x250f121e0b010f0614090103090c0b0c102706150503030409060602010c0f0c0209070c1a04020a050604030203032703100b040b0909061803040512010e01050109090b010e04110405 78
    0xc801007050003d9901c40000e11a444111000c01505039096a07030040c002c0c80c000070a1409410311240b11822039110306e4182e4400141c0c69401800800c0300d00c60380810036810300c628882c600980307103054000348116440080711030940001442c20340040044000844105401c6501c4100003030459116a201100c100d0b520001000300315028010300c1005409814841e00503040c0100280c0f5a00170908004d2080e81c2c18000174040d58010381600c280142c024490010101c0418018082030b0410740d0280c3c8111030005d0002170901e0104121030599034003401071820188003103100300c04d210103034418061500641c10a6a25910100101da02d040c2c1c814001259a0a040f0140000c40300d2400341035000d96504400c002d54441c0c00500142c01c503440e202c1d2980b8601c0315411076401c60003150042580031040300503101003240e0541041142958140007046031381d90354108002140c1c818000101142e442c0f03030042109a2071502c8480d4001d000d0203d41c002c0f00d001000240494004030707046084550480d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 909868480 1250 909867230 909867239
    0x150d0311101416170c16120206060315090309060711030a0c09110f04151817060c030f070c060902060703120506010c1e0320250f121e0b01 61
    0x80035000d540711501d00700001c02801d4001c03c0035240340010403032007014000290642e241a1046d5480c1c20a0740c0240c0d020074030004483d4025160042552030074400d2255410812031082e0b1940d14a00031003400c80150701c0d041045043c0080380d0010740301900e41480038800e20b0310030b8905211007401d0a03c80c0000c0406c0da410060f048084510400f072942114800380301d00345113608030200300c03020f480108000b541c403100c92640454000000250000b07144144000004134030b260340c01c02006071030b038541c2512015a184041405103003c02c85980c5048be6102000c10a0381d40200c140c120100c0c0500404901c2c030440e9008a40035902c0b012048000443c01000100185402e00c01c1e10f4010500f4644446083c065440f00840d0308120300601013000044280b00082500502c40a0751012902c0e0580c020140078124894446260440034100d5040118683d52000109880c0909035022502002401d5041101d4501c2c0d07281c4403501158200042c1149856440100c0c80d04a405441074004a0603036040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 909869730 1250 909868480 909868501
    0xc180801060e1806011202120703080a030c2c12070e100608060307030311011e0f14040308370605100504060e04270602090108150d03111014 62
    0xe246140d0000c0725018110f5a010202d080d5046525800318500301880c1400096021680c003207180c0c405100e003403000020807480c5d0000e01450300d0942c03030401100004d0703c41500e070400b40500e400402c0110111860742c02403541515071205034080c040c940540030b0790a0180ca848001d80008000500e40e00402c55050780810301c185c0909043e00e00006941003010100e03685000134040141032120142c041040088250b101c00d0070b45958450081c412840f0052440003480c9400214824505043e604001c0700310301e584550007940e169480e100540e80b020400391440c02c68003070f020290001360752082c0148500070b000700c03a1112000710008030713985404104a0000c0745581035200b804424007040080b55000700441400301816100428100342c0a10803201c40f80b00f40840804440084041c481402265030241c802d034642a2141100d07600c0d4130186248407043d82900d107621071442948100041d1080f400c10700c00351035980444145040500c01c07070041e1510160a440500301070f00421001521 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 909870980 1250 909869730 909869759
    0x3030e0a1412070308180c1021021615020d052e062c04020f0309060a02070b06010c0201200f0601090506031c0c0b0c09041b05030a0c18080106 63
    0x3024008640f0b080c541341d0b00540000c20044c01211413600c00076009902c0711090002d80e0018100034845e04c0c8400b201800540203070040c001c45505560184108813421001c3d100b03d03646065900d2503011601a1690382d5500f6140440303c10980076001d00c40c040c900c40613806254000c0344207101010002d5221039a203c0c54600310b071f0b03082d40b4000b01c00200308401ea810811880302c500248039541d0311940c0003070301c14244845044885402ca44000f520000044000300514050484202503840070b03218080c6550a034002d8800c090204001d5401090075580220220700f0b1503032041c100000e1221040000d55454100020f10325030035040078030300b00c650080500406001d051a10403c01c00c90030240b02081e07640d4144000c00d030808242c011a608503c0c01210191030060f0701142c0b0a07142d1900020700c032420380002c0c81c6c4900607810300180014102000080b80508003e954407181181e90f082d59050160400f4005001440995040c0700640019135404401034400c1c9000032424625203043c2c81ea4060 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 909872230 1250 909870980 909871003
    0x122d0402100c030819021903020c0f0c15030618180d031802060307050c0106121e021311120405030306030f0312070e0a05100809011805031603030e0a14 67
    0x11600d07800b000080d00850119040b402c1c40010102c0341c02a05510802445218008010300910a440312031040d0306130002c00e040082041502d01140212109550392001c02617070540c00040310403000301c0c4542c03140145074401d100810744200f10306000010100d180c4141e030b502203407480c02481c0c280d00042c2003010360400c1d0303442e1804121800d104541030010014800c0000d01c40c0350000003280a840c4100251038000e00c0c083c0081007115511380c10000900c00d202400c0780c02003238036041444440c000d0091408500d401822030200201484605801407502c0c8140340d413050f10074030068417080c8504603028840c6105000540d0380703061040406141c5050401c0100f00d0740e004002c0e0580300a0411650381c0c01880c0750501c0320342240e140d40000c0d803442d0720390041900a01c84004425101b640030015901550b0f21034000c00c0810304404505898522040000c0e156900c1080b10105001c1030b4803810750954001e01e00043c9000c00c07200f01506203003a811095418110141d1944408d03501401000903d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 909873480 1250 909872230 909872237
    0x12010c140f0304080a0207030c0e070f051c111306050c070504050103021c0302011b03050703060501052a0a0b01080a0309050d0b0f09070b0a02072405122d040210 71
    0x160703659800e070045210082004200500c0420010034480c001c1001d10b01444d48403050440203500d41c0301c11007408004441010001c4e01400e88864001c9c010021035040b92446031510034849500b44500028010400312540c0072541040700e15400311084d2440c3e406003620703958407940c40100120b880d18040803a0040c5200fa8584001040181e03140e000c582504102c603040881d8102050805900400070000e07000306644004006100751513040d4006481503215031003c1000541310700044886000720ac005040326002c0c001d180c00400c1c1c00621320b4042d4070416040f1208a000341da0b0744200e07001c0a900c0710718a40e100341291000c040c0c016140c40060030050b02d00a203145860344074a00782d808042c0040004001050101d144140c0600540c4050b000b017080482c0d4601c00b0b0750000391b8030078043c826030101d412041604d810034000c042004e40500b4180c3c0d01c1e982400c1b208100721401400c050110020505002d028140c20921900c02c16000b000e40a202200307441d041c014804490113103004d00040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 909874730 1250 909873480 909873487
    0x152d230315090726060103060f0c03060302030d0c080405030111090a0b03070e0d020303120f070306060c0f1209090e0607030606050c0a0b06010201090506390409110912010c14 77
    0x2c0e280001a40380440b19442e4100c00070450031007420001342c01c0c81c03801c3c40c541d01a110000c070a00403107070051003204011641c10049030b07041c04011007c4a0301400005e6060b00244109003025100310031140d0b019005104039841c1903564800642111000804260250301c0801e20686529044400c1c2001385a00c184052962503c000010000c040d4440350a01c100d4044100f907041d51401c0003502c0d441403464420090f14104088000b000e9501118a24006400e260010030900d1090b1301300c2c28056403203490138003850483c1c3d40c1c01c1061802700010b50300308020709400003800c0119008004041000340045c04403403c3c141d00050640301c0c50781000c0b0502c5020080003096110001d207501415400c407850402540390b2100407409000900c0b8003400c54810700081c040d40721251401f001320821040c6200a6607120900c1000300d505981c0404040c070f000034841000084805c1c0c0094481c440010726241ca01803100300000c000310309150704002160b40d51440141401c2e001303203040d5420440714804508 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 909875980 1250 909874730 909874741
    0x501060908250806040b010509060a18020d090218040528060b01090b0408010b030d0e01020a200d030315050406050d02040213080106030510152d230315 67
    0x56654885040c0c880815120000158412a090b07980019064403420f03100c0a041c41d05109030814428000c162266040310b012807000d1514090351412580c17981c40203031060607003681c204025004083d00ca1a003c1d110b560900040e615002c00031102d200560311408c0d01e007444c1c2007003403801c207880502c0c50307070350100b1002c812000702200c03140c4509550000004c1400071615004a810159030350124a440e1030104000c1040308041d04842c120360300540886030301031103620049540600075030106025800c121550030214400c00c8030809a80c08128034040030b0b5411102143d6111985102540000c1e601d10104d0103c0700d00750440b00041004541c280009070401002440509440d00d000788160ba0000d5059044890164410010003454008104070750340e0381881c0351114982d40d1000301c1140f5001d00303440b0346042d11700304002740e40080d2280411000c91a81441c1121041740500317004400d1464002030003440960b00c1d40c1051482c0c83c410828503500d0060501e03185513266582d4031410500e08100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 909877230 1250 909875980 909875983
    0x5040803011215020a03060305010506040b090103140c090406060306050f1b0d0603120e0a06140702060a020c030d110705010207080c06250506040b010e1005060f04051c02040501060908 81
    0x2410b4403201504040c80e50050324104079400038040c1d8550312140049040b901940d0143e06c5942200e010700001e0000790740b06000c004c00c0310600880c003030340501c41000603c0400c5141c1003281c03041e45460111000303201010001108428201c808407402c1c0d85481b000e004120132030042c56080030000b03201d95041d00700281c1040da50400440400c40c0e0002c007091a00180e041908007a00940c1c00910080a062074424001c0c510104070300d02d070740070b034400f290f0000e003c0d803280101c072264100000032581000419130070801c46501090f0000114401c0900ca045c083d5400e000d494001503003610b41c0b0200741e2011100c1d9040004a1b071180703055400185040040c1840801c91084400040311926aa80c4400141c10b1861905400e000842d40790000c0100410000003103c2d80100e01075462a5a03581ea154242040c05104407030b80c039140302405804009505100018002200c445423425040ca038641b0017003000d0304407541540d0354000c030209669066007820310541e40502506e1401101c174070b00307080303119 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 909878480 1250 909877230 909877237
    0x100206090d0503130c0801020310050a060927021606060b090603130c0e0411031b03030a0e2125032103090605090f0127140705060703081504050408 65
    0x1c80a0110001c00a2502d60f41c18101c00b00346039000260440d1592a403000d50b0007074204a410701688420200049001e00d0b0400926040701c1c100d40d20480001d0501c049000712449200d24600c1090318140b500d60444001e00107001126503500e4034410200d01401c2c81c0c01903c03242c0d4400004000d0411001c840c2c0d032600c03c100c1c0d82c08107541350700c52130040a91421400710549503018a0306500b4540511080004803040311080340c00486c1195000543c3e941204480c007040c00c0c0d580d501d41d20070015030701c940340110700e55090f1001c028035110b0303103841ea11040c002c500e190b1007240c009508a03121003212216024902219501307d58940c288460841d03903104203228407018842a07800303c01503146a6a8840c0c1c00480c102a80700b4018030142c10301c00808c80da20540512a031a8a50038101709900d0b10102e411182010b0307840380700c00c0c5403541c43c1e91102c0800c00007010b900c5490740200170010170b23282c07030321402005014403d80d210403131490800104042060b080c24424030032400c040038000030620010030b9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 909879730 1250 909878480 909878503
    0x607060f1b20190317070f20070317091302030603030324130525080106120f0e06010314061003060b13060303081e09060a09030903080301090b10020609 67
    0x1d4189002c2c07411021460f043c905903290000c10070346030304102015404030517141615285400030a0f43c0d140c00c1c60960301120440c1f04080024032010040b050282c031421107450081c5050150340e1208c1d12500ca49058000c24080071050000c0060300c9542360500f46400b0407011a5401c04605604124000a44911010b402070309030401504140c01d400c2084420010600001002c15080c0c003411401c0c03070040c1804490741c01c16604504140b1900c640300349ca41040300c7c01607070b40b007074660707070828005032004031615014444817692921440c481324900d1042e20070313070b000721300c02003440e90714610700910b600b6818100390100390030900a02c003000c100e807090f020135658003400200b900030107400841d0103201e200421608540c2000710000515800c89911400340c2f1380348440303407040d1120f041c0c0750041e4003007a2040030351a405040028802c50250340500604c0d440703854070314080342d601d0702c0d0506160401e0308010405595a4401811407405034643c2d44500141d0001e403032140307401d881e034a4540c50384000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 909880980 1250 909879730 909879767
    0x50f04060c03050d02070f0b07020a0f02011404080303091606170106080c070b0f070f110a020906030a0b010f080c01030501060203120a0b0d3c200607060f1b 69
    0x8079042050301540980b0883c80b8010002c41d1103040d9402c15a44900d041e0005862641104000c100503a1011400da00800d400001281c00920355500448444503d0710110451003414840403805503418002980900c43c00c03002001c0a41c807840c88005007401580c810000d010b207a8481d440101d0075602e11604440301400c00881c5a603039043c990409110b007a200500ca00040400c000114280a9203280180010741d600502c050403000c060310b020120060311046640811070880051500504003a40f1400150958030130170a26079540300521420b811548111040120900ca4a88200590301a1507401d01c0d050116501d854800394030381c851804812070303a44400001403222003554120000040019081e460103031030310b040804414119102d002900100000354452075100c10911100108505909540700300d500ea503941420652041c455900302070f100b4148645a54003800780c586180180c4010808054a045040c01c54101d030b1854810014414060455264806d10f001c072051243d09 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 909882230 1250 909880980 909880997
    0x3030d06090501050603073903080a060905130b180607020a03121a09060f0a08030702120c060a1b060614100929070203030f0910030501080606010302071b24050f0406 73
    0x500d0313234141c0ca078000c24000340100031880001c10540d108030098451280d0250070000a6100c104880076036006a8a44e10b5127840c1c007aa49001c5884032065640080c42805d42411240038281d0361820213008440e001c0146c0c01c942e6000c800d0540003a0038031048100810708014000182c500c07200020707503903c0114000c512840016038591140c0d90754414200c4002d00056829665880d0550390368130001e0104d024580d0481c503a80794241c0050f00c009881c038000d11755070030000700345000c40302d4840c4e000800a100d081d00001e440411454403908018061a0840c001d26218002c207000e5000320108000302007010082e01000700c1c6601c00801d024284000d202480a07215034894080c10b07003e4110065814000001c0701d568071000900182001c58003640c0c1c00154a4080d5019400c0783e001b442144881c2e0480000030302950704c00d030300038202c5030b20030780c0c81c1d4601c1c405803203861010001030341000041c01c0001000500c0d545055006c2806241d5903c6c0c900c2c81c1c0588540d0490f01c034080e40c405c0ca401d104041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 909883480 1250 909882230 909882287
    0x6050a0207030b270601050a081c0819022808070e10021e030904150b0909040c030807050115080f0a0b07090b180a14010516050c03030d0609050105060307 68
    0xc460041c0c4130b03001e00c2c0c1d1840700c0b040c00318481d807550b030284a40c600c10702e5010300010351140e000c60030381c1c1c214075020101d02401500c1e802c166900c010040440340014590b54846600c0c03c41c0d40b01401e4481000c5d401045807090702c00c11801d0003004a09900c003441800c504104071281d0096000c03600c820242c5010800d15403500003a45040d59664501d0048172140f5041612381c0d80000c0500408041100c1c00c0c480d081440012031080b8000707001d0726044032030420019000b1b01b000081250824440e44d03203464015502c2c0c981b0000c58011340070441d12a511100400004407403e080300000c0d1841d0400391085280c545461603841603100b0f40181b9041032030b800600c00034017501d41c03180100301040301c031580c850401c07100707044245000d140584648500c04011804290500340c0c00d48801d011385072286498050440c0640d125003008081f40c0510503086820340e261018405001d603a40310160110380d26040c11004020b44d04160400c2d4003c940a104100032a41d2100c660101880340303600305540792814 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 909884730 1250 909883480 909883501
    0x5061c09230a05060a021306030c02120d020901110718092d0b010602030415050702040b13060306110304050c0603070905090f01090b1906050c10090503040e0106050a0207030b 77
    0xc400800661a0000e4188600074402145050006108205030740080e82c0320a440400ca00881d101608212001003041c02105d00a600510329001640100d4582d124036014000c6075034082c815a0240b00d80204002c1c81a5804c440c0f410800c000142c040c0c80320b107080c158440005804200103500164a8240c0602402034401820702d040c15108216105502c2004500ca41c03040d1030030342210307118016000011083c1c408415141501c014180000e079168418004030307031640041006036803087d0f03500c002e807000740d90300c000e83c05400750031400100b8040c2c610705040b02100c05079008420a89010010000003030f4011801c0c1d138000404440d52603c03510b8198046440034141d81016402c4820001400f0324982d00045ca40d04031841038005004088485040c89401c03801b0100f01021a00c541205029890150000d00700c000000780c1100c0301d60768454520410746280c07010603205600000f0f000e2040000003c10203000d0011401c000749081c150075002580d0342501d00c0090842401a804181322103503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 909885980 1250 909884730 909884753
    0x6030204090305031902070507181401090506100e15071a01032f090103020405220c0312020a08040b130305031902070501020706080a0b0114040803070b0105061c09 72
    0x100a0810802801d09280140c6281d00070380758041d04081c03000030f80354042502c0c001c0b1200f407a400005000064030701310400d10000441c814480405850b04140140901040c06440c000c0c0080640410642081d60500000d0350400e4000d4003007101020b900701050710f900c01d0001c55031000e5a0a02c1c2c1e03901050a00710000c418a6950085031040c0200000c2445020000c8030b10031b83d0500380501d480003075101080d030002c0e0031074502c541288580c001040541380c0b0f9480305034400109800c0c80b61070085030801c0b6861003100c00d81205d05078180340301441800080305941502d900340d4001001628940d880b000140e00a0344906a8000c2c0002010003081c407140f61960011a4044120303600c03185840e4030a400b00c2420040100140302e00341000441d0743c4000b410304122030a07601c5912068903440c04840180c241034419605110182c100007e103440140c0040c80201252406583c5038174040c507000014540c10f038031292099005000d80100c2e180112041e230000c0b4220700f00041c40e030035145400f4540e02c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 909887230 1250 909885980 909885983
    0x50406141e03040f030912120f120c0917030f1b0a06020d02090f0307060f0305060a1a030f0622050402030a0c09020a020717030304030f12110a0e310603 67
    0x7101005100c10020b0011800003094841d40702d118005484c0d5100c00000007014401801c00010741d4035240d081070103043d150001d10001d26020000d0074003245844181c84079001300320001122102c04100003034030f49a034036203e142c028004c1e42c98154040e0300c0038080d0141c4404088082e000300740c0d090920800f08603004809510074410743d195648007142c00c1c000d400803c0c58a004860103908101c4501d00400d285c0d0071703504c10351920401d021100008030000d2000810070740e005881e2403804108400c090303844a0200c1d0a0841c019a285000842400c1c00e00e0042e2107980030350a403c1000b114000d441ea03010202c00d021301800170b490394403400000d24084040c140903010f60540d010208440c1b8080e0018015034010b50221910aa605e04041402241900d4040410340040c000301e400a48030701c03c0500d0403496442d14079220108028100c04603001490491454036000030801200d83d00401643c080075811103002d03a02c8515030201c1c4442d07406040d001114140268a20203100301154050405035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 909888480 1250 909887230 909887287
    0x50c090f091812040618052409042c07060918141906080619020c030d020a020a02010e010f0c0b0c0f19030b090c090904110303032505040614 62
    0x4041c401c0f000701843d401409081c00258000c03001c1c0c5074078101000c035082241c90203004810741d8151038000020000c45440300003000725040200d010199503a02510000c41419489008991640c0c3c0890501507443c0010000c26084800d08000c10307500812104125101a200b6240201e401c1160304024080a078440000000c41c4091000c9402c14581d00c0100c1c14841c6003c22805840e01c101c5a40c0d200100d400c140d83c42d4000d40400240300352600984442100c0c0d404481c24003454040b000b040e600640c1141006a1001e0740100666030b0080707221200050a091001c966107400d0300080c4180d10313405003e4070400800011841d111a40c10407150303407250001c0e0080d104d88045032110903c2007030b40d4459001a08144000100c5c0c41e1020700c0c1c500030341896071442e15000d4203105000c4c0f103540c002c00545007060030061400c2540c80500040d482400b5111800ca41d43c0c3c3c0350300d040014595107085003810850144001d00046d900004030071101a030703800002340c60308014446031560948040d40c41500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 909889730 1250 909888480 909888493
    0x304150906091101020f0c03070b07030203090d060504050724181d01150306060c150908030117010501060212391c0216061d09010810050c090f0918 65
    0x1840316034284a48400c00903406d80319800c1c1e211640030381d5002c00c44200d0343c0c543c016140030480030b40d01c03800418116101c0c4c0190303070a09034404001441c1d03940e5000203a87c400d0300d034000c0000b000800c1c0f04a5025040011009561507180c04913510302c11261381d4600f0600c40c41000590a03125019251401040110b8200c500e1042c8050724100c070030713828443c1890040f00f505281342c5260290068005680b2140d039004102c4401d03495210800d004049200481d40e5201d004202250001c00190f01900c495001045440c1240c4801401c441050b8041001c54100e07900390354032075040f0030845484000644181c0c2843c44032000274017a11030600d06842c001e420b00703401c08410007004644404070000c0340f13100d8603400d1003c001c166190f03d0010342c0e408849118507400d005850095a501a04001908042110b03240560100305406001c1c0c0181c0c0f859841840e2840c007449840c01040d80c0b098002002605040092000c59910007000ba8900d110745c80190018810000901c91400702138411720840380b1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 909890980 1250 909889730 909889733
    0x1218010f020f070212060601020a08031f0303090e09150606090f0910030201090b0a0503042a08070f050a08060a2310060f0f0206060126151c08030415090609 69
    0xb2640d015100c02c80c0184100700c4d0200b545000495668810f00040c1c01520040c10141d950f41c1203648001d00c4041c80240901c40180c19600a007040b4018500c2078507084040ea0410810707840b40da42c0240512a143e10a031004556403544c0b200c030b10341141c1c041d00c0158527000301800243c41d441e010310249401150314401c020b07688641018100850303000f81c0b02d15030504d80311400f600052052070003c80202c0d0042000c2000524002c44140d4078505942c000c02484c0c10018165640740042c0c0c0c8040c84641c000c3c801403112420300c210072801000121005c0e194540303084d11041d11841c000b0064903009d9516000d004c2c00d600098000800420a0901008103103001c807040e00c40281180540030009903030340b01e001c1c1101d014820310101518141c0007008103075100401107400c41420a40083c8041800e000001046a00c5181e2401940d0740704101c110360103400140042c001854020b4110090300c1c0d0080004a134100c800c40f900039402554107140468801e5584014210043c0011700007441e01e0507550 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 909892086 1106 909890980 909891007
    0x7050303070e12100501031509031d0f0909010c02100c0e040905030903011104092703050706200d0c052703070b0a0206040c0504021218010f02 63
    0xb0443c010f1003500c0e4208844c8203900700302e140e03ea8006108010491020003000b03100d09408107e024203945005210360311000c40607107a886040f800039815100e60200080103a005803108289040c4601d049008100c01c0c4c541c0300c018002c4d0040e0b01c0101d8200d029542414002d952951145030502040200170010305508076000e00c0100441e100c1603e0a00401c2002c02c0e40d060340720b480e0341c603105005e8181c1e516a01c96070760380050720f00751205001c07140d5940241c003030b0180b401980712030b80780c03a00310020100c8102d5000c2c034103e081299901c06845100505014195100c00c4c846811200030944560045896102115110211f07818110a410311313801d420200040807100c1e02a0340b10b5002110750300500c0300000680100c4100014407030089030000051200b901d00b1441e141002c004540f1161018140e0751080050004440400c1000d400031070001c00601001c650300c2200d01c2804 = true := by decide +kernel

theorem cover : BRFrame.Cov 909712230 909892086 := by
  have h0 := BRFrame.cov_init 909712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 909712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 909712230 ≤ n) (h2 : n < 909892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
