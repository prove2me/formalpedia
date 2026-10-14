-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3106
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:40:59.635377+00:00
-- url     : https://prove2.me/submissions/3b9d6db5-9808-4b3f-8121-f627c967c3cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 558453237 ≤ n < 558633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 558454487 1250 558453237 558453253
    0x3010510050102071a040e10030209010e0604050f04120e0a030f05031308010605030d030218090703021806070f12140c07090e0c0f011b0c0305011508370212 69
    0xd40d0402580028000345c401200304240c04e10348881e1240100d01c10440408040000642408101c42d04500159405030107000340756100c100c52200010111159406a45000000f030742c0c405e0611119030190f0b41101c1c0207618407210030b00456400c00300302529030b00322104c11300020000701c2d2041980d8485001d0000b560700c600030300101607901151607001e207032140e040100a003c02c1c0c3d000300d03164200321040d0400584da0400130b1207034800614130042140e400700844082041840d00b54000b402801d07292210101e8044440741003016034007881c1c0b4060312441d807680f041b0700015105c031018005d542c2d260803c613803c200c03505605c0e8000c0c2d200540011454222080401c000301140c01800038a502d000c004c0c013280c865542c0400c15100000c4245410851041285016442241403a40185420404100c2a59200c0c1407690203004d484440340d441006c00c24000406500120700540035000d107031848180b02002c08842d030018000c0442d80b0309865425a0207100503070321030540054070300c65900985548 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 558455737 1250 558454487 558454489
    0x240f050921071a0403421b0302160b06150a0f08060904030c1b0b0c0f12120103080702010e1305061005130b16020301020715050106030204120b04030e0301051005 71
    0x22030707190196030054610910040c00010000c06d48181881586030340b50b41c000c11410980300058540c0700e19420841c40b04091a1a40d07201074004001e00741d090804064402100d801c03c070704910413407040c540112600e80807107000407060903e0a0700940000c0031802080200040214150b0121b12030a010540740391030344224907040340c1070070391203031707044405450b1840d00341c4003c0e0120071040f400030a03a18240150807856050103615001400801d0300407a00c504604484642e0b501066146c00c0e12840f520900c2c0071000182d6084400b01d245007992656070783d103155100b420903044404224103022401d140700c4503a4807058031a0307000c1b81c880345000c1450f04042c014000c80344d0034644448100b1908200300008002e07408004030031a00c03030981140e83c0d400c00489180c000000c80034020b6241d400007940005028100c400921205401e000411450340c1c1c80d101035040344250710900c280740c04901505400f01d0301207089942d20034040e04014140042c981c0011382100d000b02e0360f20715040b201560030b00903 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 558456987 1250 558455737 558455759
    0x50f0639032a040e040b1003050d02070f080102030c1b0709020d0f050603070302150703030b060d05040c0e06182a0a140f0301030b220606240f05092107 67
    0x7281050b855400d29007030800c42001c0e608800240040c15090b8040d0100782c422140340f2962000395040740a40780c0c0c070806d20900a4443e80b140c465139821500030b600c04520101c041c8200d90091404c0b19000d880c3c40000074004004c550601803051042c0142140020400240e00042c0551401140700240b81000fa40402040307400240586009a0211400b4801600c4038202410700c00e402c1105d09413100740e42d1a01320003030051188030541004003c40c04031000300440d00300a01851207007151500444c0c80d9605242440e1084502c180d000b6034850403001d000c00361407001d0ba00080549484624800b402e440103404d81c0541c801d90385d40d03245c006403010241c0d500184400440303026030131440c50040300740170350b02d400c0c00180000390442c40c1c0c40010550f20380c1c180140c8116010104001e0074980d2190401e403000b0034952041040860705807a20184004e0300343d109142a10240e01da0003560280b0361002c460903000707148501d4000401c210100d00c03000307505520755800c2940303038020f042840c1440e442d040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 558458237 1250 558456987 558457051
    0x1050a02030601030c0c170d0902060c160e0f07140f032e06080a050a0e150a0b0a180f020405030f030301081b03030d0902031018050f063903 62
    0x2041088140c94000000d80301e01c07165a08428400d9401d844201c0c0c0c0c1d508d14010300283d4402507100308002109000751001003044800009d091000c0c0600340c0e51801180c210100480c0c0b0700310900314140008004900581c4a070044804102d986c6052240036280301c0e10503801921101210203020b106000b2040c1a029010300c24654058201420f0749021805003a100c4003400700d003549500e030000030714072503032320380c040100d680d1000202c2d52000400150118810f02c150340c1c002c0000c1c14000328400509100b40b10034211004812400299450b50845000900f8180d1800110300d07000c000010306960104292004103500801441d80da526200d411842c005000113004000081c6220b20306803994040107a4450240801000c5181602440040c2c100095508002c0c502c40c5014162f40d40d010700702005000d424465402c45191422080c122540c4200440d1440380380c0141030400c4045502c0707501c041302d2084171400c0c12615440101c603c010b264204030b5880300318190411085441031301c0d04550346 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 558459487 1250 558458237 558458261
    0x1c0203130b130603090516061d010207060f1107030b01082d0307080a0203040e0a051e1918020402030a0b03100e1b12010e0601050301111305012001050a0203060103 72
    0x3850110b40c84180052030186206240c141035031032480d0f0080c008203010322044e820f00b503a03265510355103c40000d410318014000c1a101c044081c010041294000201c00c400e5440940f01c12511003c1030b00d08450445084101d124240144140000044c0c4184031650203000c162000d400b4503100d00d40b00b914170101100d0302c0210100d450003c00901d80e404021501600c0d00604140c0c3d40c1e41c20248140c7ca107114940c0101144107840042050318100c5070b20490045814501403210080f01801c40010741c801990401114130606151100c5040c040e405880803d0b404c0181c0e004003c2e030303070300050100d8000b110040e4099451719003c0885d440d00340805841c03200704507000c025288032000515500c1c00500c140141107443d101d065011740d590f01e610f02500404c118024460500054000e030b03180d680130310a4501075828940e45040c0082c4110680d6406580076025240140ca03000c01140c003040c001400962000e01d07446e1030b082070b590030f02400d4414020460056502d0903c00c0005003206c2b04100d0380 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 558460737 1250 558459487 558459509
    0x61b19020c10261e070903060e030a1e110a0f0c0b03040f0b0705070203030a03060503010c030225031b05061005011d090604020c03040806060a09050c030f091c020313 73
    0x9203e1200020088980c40792410310b00701c9141d4500030103655540c0a04980e501070021a020070141590000800c07080e2032080c1030a115880c5100100da98034022551100b02203002605d5080c0c00750006101c03080da4040d0783c60304104400346007848a0602ca00140c0544003841c041e02c0c6103083c03080c20b5600305d00a100c9108407614610301034035a60029018400d00030072492030030b80070441081c03107401590440c070703001000c1daa07460100304030186c001c0010b0312403070b4065400e00c0028031543d4040e200766640b41c0c076501c01116901c078098450320b02036031000004605004c0c0704000d103c60a001c003c0c04805040c400d074001c00d481e0403c151200b0440065034030007410407003c82009524404140c1491068aa0540301241c2136103d80c400103010780144940792080e8400400e00085411001540714040c29007912038460f019201c020282c10f843e03044400c070420303074003c01c0401d0401314155070240e40000c0300d00c291001400b0290201580c400b00ca2100401a800462000300c100110100503008003408400c0d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 558461987 1250 558460737 558460757
    0x105030706020616050c120406020a0312051504090219030b0414010203041101030509070b0a020304060801051c23120712030912110304090219140309061b19020c10 72
    0x1513408a1103071810305030100040070691a003500020494403407010703182e1341143e03103d94907282e0081d0307650f641000560018803030003518104221302d0f2189034012040c031418055441001424040a40101d030400c0340c00402c0151810310070311042c40d1500196120701c07007200d41030400b0308007850360001103107584c0010b034810018440080c204100d1090f260700f00707003004a19680c2e04101542040d00316804a1f4a0402c00900c01141ca03070f0110090040d50551b40352081a070b600e800900c40ca1100303160400c9100e004100b6044042010b400f0065400c22902800c04003204a0340181e905107241c250b8402030010300402c40e4020003003008060020340c20310b4074040010710301035100e158441502416000c18021007024010f003075030044c8211800b40c1036515041d5921010031201d0158a5080d11141000441d124944207201c140001142c3c05500150010f0940d62260410084120480d44042c002c80340c08200b401c1c1046040411081c00d140d158004c3c2c8594190307001403209401d001e0f14414200a90244 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 558463237 1250 558461987 558462001
    0x20f0c011707050c0a030807091a0a03020f210a0506060705060106030216020d1a130809010e01051b0c1e010203030f070c170c0d0f0c020103090c050d080301050307060206 75
    0x1280c10100d2100d095481807a860b600025165841a1850003c0900074501040181034100c4500703070103a21503a60f044030035aaa003120b00e21201440401e4960b41104018800d400380c400d40142c0721713025020315450701e0180d503c107400c1001c41d03094046800400344030381000b51003881440340e02e030300100030740d9400c0c680b050b01d80e2a9500c0307800c140110300502d903020622041c8600c800001c50289a0701502d0384400e031040341400b8003403039032031220320000c42242d17000141c80001401508103020745c80203040303040c4040c000054580c0e0401180880c104441031005142c212400c442407410034000c0c9000d400920107490500c5994843c001d000540c001d03035521020702030b0340e0001c100c2c0d0b840214414000346a0b186c00300c048511014030803003c2d00004804003458102c4420b24010700080d80c400c0c0403148041e4641109075142c542060412006c182071960b4040907500903040b80d48a1481000312490b25505c1c2c0780000e4800e9040d00701079960910100050100e41000c00c104006041d440c0001c00c51854412 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 558464487 1250 558463237 558463247
    0x9040f24091506020a02010f140720061c050c07020405010306150602071518120b0708070e0a170f0106150e0609030c0607050c030a080c15040c0b0a05090d06020901020f0c01 76
    0x241780281000307010000404a9032207030440e40c81d90f8080e142d4061307403212581810465102c2c0049030361403110000902a80d0703460008103c64182803c840f507040800c1c641209a4000c110040c440e0701029400c00c00d01c0b0046e17644d0700c685406180308110000709a01140f2054005030303407540000080d5441100140321040309180300d949443d0041c58081503004e0540c2807500b2403c080c0d4005040ca801d04420401003100520903d8444d01c10341c0e8490b140c0756543c0000b1031b1031030140c0d11000c1d0040c994107014031401180b5501121070f50790607011585601c40781e104680c211400307036114662000f400580000d54507442400100c0717001e000c0314000d0400b000d100c0000c1e2266103e2019500c2524001171407800c00c002400150328207500101501e07500c0c0c44504104400d50301c00ba16510300c82c050940e8029508404000181c080d0350000301a00060b070401c0701c000d48551101d00c070901402010700026000b80d0319402a6421144955005a01c5d500f40030000381c94070450420a080c160000d802040d40c5903400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 558465737 1250 558464487 558464503
    0xa020402030a0f152304021303050309090705130e090f07060e240415140301060e0406080f0d1d04110405040509030a05032403030d1a0303070809040f2409150602 71
    0x2030003004245c0404080060000d00c2444481d17a11500407542c00014000040040c100c4008160340c5c0e04001e070342e01d0310308503001c3c820301c1080300c00301441c6a01481000d02d0501015402004070302140c048200d114005442c22209601c8807000504c4000e10103010300f0841c030345400d00b100c990107042c0800502c01c001120340c0220301a00d40303503800390b004400d1003601ca280c500c0c55a68480103559034031b5850b00c2d0b00401443c11800c0300c0340103034107040740081c2e08a00025109110b444500c007806003840300140c200c86803183c504854a55507410082d100441d929407080c040c0101003155099a640d00d00b01c103100a0710b20003058049160024801500b8041e005230449503c0084c1e10383e513400d109400c0c082485c0c010b4031040300030380510010454152104080d44100c44000400440720302e40020501019542d2040703520050040d203040c0302012482c10503400c04c51109031005004070310b60704c40b01514203002c2d0b49107080c42c080d080b0400082180d1425480303080c541440c0c8108840c5064103102000c0d59511039 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 558466987 1250 558465737 558465779
    0x6170a020d030e0d0c0806060f010c031d10030f0c020a03020712030c170d1a03070b073e150405010f121a03070509071407050a020402030a0f15 63
    0x401e203000c0101481141e40111560000302180c2d0341300510f08008814060714000c0e803206200f840e002c0360403860045001e103001e26050b03450803240c1a09a40440d0284005d01400528403c40002800648d030344000b1a0001d02a60b44c0c0001c1c072200c0d1007011004c1d10002480c0c0310554110380c41d1300c3e0200ea404a002d109480b24280310340101d00d42031a088a841601c00c2000e0702d0540020000b1041034510b50040c65660241c0c0b07018004158501d240e070703200350390440ca4540d0642c404001040242d03016005006041d008101942071706014181021510020900c00310700b80c034404a044c0d03001c400c40301070502c1c034550988100ca101030031141c94500601c103501405043c041039100d500c0c0d180e841a0380c44241d00201c40f00c01d205c0103c201c0c03000d0490314405407585100b8000da4101003042c0c01d20341e0030103200e80815600d41c150307603100400ca006030307900001080d5164042c403034a03100549c44038001980203980846d070000b245082c17208008102c0d1070105000381d1141c5111002c02015058011500211070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 558468237 1250 558466987 558466999
    0xb0c010c08060d08030c1c0f1b02010c05031317030a090b0c03061c06291809030403111203120a0b010c0f0201030203130b0a0207110a0b0f07080f13030606170a02 71
    0x4003107480744000b035141900c0743c2c2050704111201289020302c0c1c200004609a000c41404d0b0743c80728a800f6802d80700310cc1075440020304d080c00010100f103201745102110318000e1056040124801050600b00d6104130f4404070400d0b1034460792410040c2c1104050380c41100e003103a04d4107508181d000502440b01c48610a0441c2501650020030b124042d800015400008013040c205210120311200340712108151841c4a2070301e00704c040d00103841c0c0c500060706c5985403030040e618144c00d5a599008122810010540214404142c07202040040000704111111807411005c44e14102d503103101a03d444828003810011030711901d1000030701452001d003e40d54242805031b02ca50b03c54101c03000c4907101c2d103c09840c114070001402102a00742d80104200c40c0940d1a440302480b0348400d0005ca56894401d0145d508003c2250f1100741d030918010308181e81c400e440c11890b040c1048110310240d040010b540c0c0c400c41e182c00003007081080b144110001040e0031141d1000200703060390825169025035401a014030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 558469487 1250 558468237 558468247
    0x5030408070c0b13150504050a03080f0c03040b090a0906060e1212071505010602060103030804080a1403270615120307060504050715080105130e070b0c010c08060d08030c 75
    0x31900410007805000d4200c2c0c40303920380c90324401c4c0c03030b43d684410b104042c0400c056004030120306204008580a8640151055100d145541d8a00600e94010b0300c02c0f540c14002480307900035151080c40100010081c0c810901d0701c8a544204010709444981d01003028036140031000c11000303421142c101c0500d9400c03900a400d08241d604200d0404a20848901c4403010004404081103040401454002008082003100d42e807603410130b9075102030a0202401203269040042e00190040d001001848800c0ca8600c1005900c0c428003842c5800903514040b60b4051100d4950700130050034001980310168000034003607800c04803074007180311007e07a0410340a00a000042e40b09060200212407000c0e0f4401c10800ca00d1a041c00d10546030310b034901540140100051100c00e4a9206001d182d050b00c20080450560845000e0b4100052807541c0003010b8030f01400d540040c0803980304026041c01c0707282000100c0c18000741c2c04002d0410340e0080a5900c00d140c8038460b03401103070b042000d803540a16817a07050740e591 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 558470737 1250 558469487 558469493
    0xc0102011512061d010603060509030a09050909011811040e07061209260c0d0305041a070e090a0515030a0519021305011d070c050d030b01050d060905060913030503040807 75
    0xe8030209400f02e620350303031300c2ca00b145060205600c00e42c02c6030300138041000540c50f2551401d031a4410f0380320785c40004200300b20030720503071504081d001d4010180781d00000c0c12101c0d130303c45a1089007045009561010b85190030350341504041c0141c0c90703480e5110303011302030301c130f0401030040c214812400c0d0b05100c0f2030755000d02c90100500c8070306d0080d01c120f10781d401c1640c50094003840c400a0b8001d010101d1180500000b000c3e0440c00307070042d04d0260354000b0194007641149465800d000500520f40002c1002e44504841c06444d10007100e8020541c4d5440031030940341c404690300aa1501c00b1000b03020750f20092450b03010802c00710300f404000943c0d20718100700d07040354000914900000c50340081c0007032070b00c000000c08503070700d0501410300402568402c0244d80c40441c10b4500c0340c221140945242c01c210b10088040303100b0b6000707a980d0101410a07600785200412164102c6c1c0490f0880b0007419510300a00c1581d192001c000c0d5402a10f40c103403055207104c1950300802c2404041c0c03005014080202d001420 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 558471987 1250 558470737 558470741
    0x2031e06012703020a060f05091909050f0906060f1c0c170709051302180a021603110c12030d02030c04180506010306092009150a110c010201151206 65
    0x40144114401004014504030344407a10a544030485c03180c4e419082c0044c080740221007518544100c0d44500b400c0501e00c03414800e4480084084500340c82140c50040f4092441c1c4c45103070700410004e40e26800e01d203000c40406262900c0504841c0c070030750500681034440d40c2e984000d0440303078481d005841c0341f842252030800441456500a000f111610a600d0000c042002a1180460341c00d0b54081c0400c0e04c0d60503a100940001c1d0501a402220b004102c01c48107060303200c91034001130400001840c16080b8031900300700c1410500120300003503202d04c1045d1071750300421120950820445003184040040c0080e5070341d900c0b61a07060041b05801200049039000104183c40051101c203180b42155483c9955039001828101c4201e40400e140c0b100c041443c00c1540b18000c540d04580f014006140090708e81d140d40c9400c02d0300d045a02003445210484030210141c050542860307551511200c40c5500881d130790901002c1c2040c1c504581c50b003d1070545511901440808981c080719010780c17841410b043c4200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 558473237 1250 558471987 558472007
    0x3011811031e1501140f0616081804110309030901080a06120b240a1e0302041b020f16030623070807020106050f1f1e0207031502031e0601 61
    0x601c0284001e521440400c0824003000b80c0c040c0f5034070740e0f440e41c0e25540f008510800e829506900b00d4404100b06000e401e240e00144110ba84a50038000701400366035030f000c10381d8407156410700761051a1404002c0d81c1800d0280742c01c5915003140950452400802c030700c1c5d8a0080618240c10000700002044180c0d030b841e0302060142c011a400500031074054240010303401e9041d0ba002919411001c50048840d01065112510140003000d1500c480d2400d00c0c0c9101d82581d5401c0655054401040040166035a204007ca200c0f4148045400e48003091400303420308615051070552600242c00d2800d48205240c201000d90758080c070f0019450700a0000f40c800704e18048050f05110a2800a000c105d5400212071481101c0542c001d004642c0c032002404a014014101150811a000c48048208685510492075090645808031904482c144c89a450b60460840d24000d60419034052003407041c110910354a64800c14010f43c070b142013040da80c140418044206076094002403000c1001d030b078072500d1104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 558474487 1250 558473237 558473263
    0x20070501090b2110030b1e130c06030c030f1a0301050c04030c0b030c0c0d080105150a2a0206160309050103091109060111151510020d03020d14090a020f0301181103 72
    0x80e0003447d00e440e540c401d40644560708003034002c13001d00107918451350402e40002d681d440010342c1016440c2c45804e034050001c013406442490340303070802c3ea840c0181030f118901d50028100000136007058598285401c450f00944a41071045040100b440421070451044d802c44100c101081c0c4e981e81c45012407951406200b80b00305060240f400255a4281c1c400c401905a0b081110000f117500c0c0e0b8403e1040e114420071140f10082040240c4401400300110450419280c0790682030b02c0501d09980064140d501002d0100c2d00000b08040c8102895070021074030700645400e0034100801d403103a0310390b98640820340107503610507403003800051b134640d10907601c00c0c40400241c4200d5404001c12070781d503038070351200701c513242001040780c04424843e142056690380a154940c000d81020088100124082c0d4494014840d160361581c003105100c0640040c0240300d01c20842c054160303041207204000224a084007084e10030b07810016a0b002111400601100c01a404000c01215400d6440801d08044003101d0030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 558475737 1250 558474487 558474503
    0x307120509031906110f3606180d0b070e0108070903150b0924060313030809030c0d030203011712030a1a0306101d09150720070501090b211003 63
    0x540b030800341c001a0020015501e55070514040240814980e9100c0e200040d0302da047c2c6540c403c8007403c01c00010140205140034900ca600e0740c030800316100c2030104d03d040f83e0201010041140f01c9500046501c03501109103018482400d007500010124842c500002d40142001c55181100b005c40798446804088003034001c40c5140b07084015940c41494480f0103c0c0d62884c0c1d680030011601d884001c82e0310440000c545070b112546a924125136101004145014920041008101c030f40710410103a800e4191a40d40507990b50304180c1c610a000a424a104000c0d90000c03100300d41c00c0d030315401501d45c411690383c00050150320b4010b01c901c40001c989103498160203403a080c0304171500c41c42041c4040d1205860f0318030100b514904050180316007100c0c000c103190801213205005278009050143c22041c2454030102041000e20000c4000004c114040c200c0d5102c03400030003995800c8040c2000910040c08024101909407504008600c0790700d402200c4503208500040050051000480c040c58101d960 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 558476987 1250 558475737 558475747
    0xf030b0906092815050406030803010e061c0b0103200307030b0c3006010801081c050c010c09080d180b07020307080f010b0406090c022e0c02030712050903190611 71
    0x3c08004003140c2800e41e00d030f0500d0240108132800d250060074100c0e41d01c4140107155a11b0a0110703000c21001400c820750258010b6000108241d0040030165501d01464070b81708554551b2a020900c0c0b2044002c0c06075405103140070311526500402c4031011a07801080114055540d650a291144072f40c0030705175511050020302c0c0f8403200040c00e031346060140c440350080d0b2503140c0a00558000f1801d00c00d4148560213001c0b80800c0072421000d0008503046418000e04000b821901a42175030008400038002a202175010000140b0801c0031400000c550f050400d1103c005404c0d800e41c0e40d40502800588040002d64201103440c10000503000b003035601c2c182caa250340c0003003200d40a890b00c3c000b40c074410343c1030290100745031625202d146c01d401070341d030010f1000003803900b100310003a0388e8000b07a0340041c004200c180c0c95041082c050362902d12460707409155074600074541121000d480340e10001c01c10205120040e0381d43c800084405080b04030703c0c8000081007652403c48050504120580740303034807012503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 558478237 1250 558476987 558477061
    0xa09060b12070207080f1b03120d0b04090204022d090a0501080907050a08030c0d0504050a0e04030c1506170a020d020904050a0c06030504050d0309260d050c0a0f030b090609 76
    0x10b0101c035148003111190107c03e90660030140d80d100440262949400100107041c1185403d03800346010410142c0080341130842c5400080892b0800320746820321121800d80c01b40310034240d0900c130040b22101e54416040400303200c085002c5030b1090080740c0c1031000c51004176541e030700100400d0000300310003001c252056490f00d0500b526074121000c030040307610500ca25000d4150061041d04c081c0c8801030101083c0c40d00d42180c4c0b114013440644180c0c00d00c81e10b1020203004c00ca0b0018007001d503000da00e001040c40ea2601720f142034036140501d03444050707401c40982500140c0c1d81000021800750100c400051039142d5003807090400440b114004c0c44c1742c02c2a40c00065958044d017205120301d02030001c0d501e807800281d200380c043e51003940c0c0080030580e1449052100d41d00c11000302c0e00300c9841e2103e0f9403e108011000000303c800a44090035054400300704410306903800a08400188403c0c0fa040c840c030384141020600410300904104d2007805075800094800d21005649031741842840c804032440d100e415 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 558479487 1250 558478237 558478243
    0x50a03030b030715022122081b13200313020a120c15020309090c04090b1804150e150402040e0309030a08130506040f050a09060b12070207080f 63
    0xc0d1514000d020f090b070000343c2540844d4000410b01130540281c88860101e0290845d070742c602003441c880e09001071050350383d8000304410403c0070881803007488240c1401c05203e545096a800e05822082d1120148000342e6103681040349041c18280d0008515400b09407040c080d400340100986c000c1d05000f0040100c0c02c41c248072240c10a40c0203552400d011501c07481110780c500100b01c0b02419007101c11101b081091110001004850b080b481a030b410200008001103540c0015603418071100d2000ca014002c07400144030700300850308110345544d10720b00c105449401a0342c0003040580702a170f161000244101003a041000c00760001070507a01141c4420540c0090040d05460990003145807410051124070000101d600940004005010280050341c40c0d0380e259000f01980d9901581441001800340c8500001d000035240920000f510702d42000c050100c0c06029901c40700d4101c0c01c1280801010340c02908450040440c88070781040c40e0f0360044280c4c03401c070045d44802c00c944100000f00ca1012008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 558480737 1250 558479487 558479501
    0x60703261605070807030810051e0f03160e10030b0103081909120b062403041101140403060f0902100525020f01080a18110108060d080315010c050a0303 67
    0x40c5500750050781400300c00b29024001c5100060021384100b142002081c041d111280e80680d6403440d4201664890020484594014a200d074840002c02440103d500d400d00601991210a07001408034140c5084400034800d1641b240c0080e0301007031404110700c0900d1150210140d501720011003259650391a124905521400100140501c0c440d40d44540f503108100f0502201c3d021103d201d19901551252110890080d0849501c00c0840703520f1080102d001542001140510450545074909403d05844207001d045000c0d0402521260010340c43d1040019101680c1d0003860000d078004000d80e09100501e074540000c4d620a021038000d48041d54014010311349000d140380100841c1d407048500c1e84013501d124400940c4140c0020990300254410115154410741505010860035181100b50300050310141c03080e02d001171451512105d6581100c036490300040240c034120840d10312511818001c0c00041c00c450200c3c040302d0f008840d1680301d081507846403600401a030304610304901d0050018004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 558481987 1250 558480737 558480751
    0x200d0e03060a140c090609190f0614030a0911040f1d03030108100e07150203040e010b031501050d0906020f0c07050315040602090406180905070803071106070326 71
    0x2000300142e03404142d406142041c240c82d6801c03a10a445882548140703422030b0701d0355504a00c003800228a40e03a5007003003800031034009040c038240c800e0500c40b051100485030f4124100f405009000780c8407172801d40c0c048950081c40380d0400507212b0594600030b031804160519103903000742440010074040c00c082c2d00401038900c03203442c0c007400300000314442d9031640000d00c18030b00147c0064106421030301083d00404001c000f00c1c42030720725650f15990620101c0700001c1c00c2d8401079001150a10140140c250804c1c007602d00001014290f28220700c041030382c583da8207000c81c1040004071318090442e5664100a505640c0301805548904182c112221113030040e05084809100790380d0000b82c181804540c10150400540040c0480e503103d840d8034019511120307250b60404d80d50500042c00d94038840b1160074440380054045084c003000e00740f0f02e1410013a90450610380d0801c002c60400a02c084c0c0d0644039640060b076280342c9034449070605030703480c04603600c02882c5804c491510b0354010340c45901d801d1080316 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 558483237 1250 558481987 558481993
    0x1401050106031e020a0519030504020114030f061504080f03030a0c1e0e0d170d0507030c0c021201020904061502010608010632130c030b0f10200d0e03 66
    0x3903250011802c3d202402500841440300c6a000d000c0000690028400b01d44681441d510344510501c05014200342d0411041c0002e0b510024001150303030040007410250800c80d0340780d00714101042280442d04000c3c2c02c040c0b040d190171031042115241e11040c0d500600022050b109061100348250b503d0345d0084440100103860070484522907802202003070441c101c2094829512a0030700025035100c222414642d500c030845a401800094040f110689608030700f151054942d00d0340c901e04000d58a01820950a250802c02100c45c4154440c414000e0380d030701111040c82940b000800c003030092040e0b0380501d81141c1804c001203044500b04090440c1d189165000304805503450650500301c40c140c7c001e07180414010305149006030000075181d20001c102400d040c807410420400540a0400420311120054035001c2418bc4582c0501c90307007105e1403064525104000300000010a062045001c400c103001d50030144000f00201d0500412080390b01100302c035507010750701c100a008224421070300c2e8400e01c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 558484487 1250 558483237 558483239
    0xa12030c0e04110a0c1401050a23090d0302130e040b250c1104140708060a0608010518090a05030a09151803080c2b0207080a1e0201090506030414010501 67
    0xc1858441d50f070044140d040580d013000074484048591403400301c0c0a968041242c2c00e55224420284902c5009002c0311130002a40340b151003000740c0480c0340140743d107001e480c02000c02901c1c0102145c8540d9640b00c42c41c00503602c90880d03459000134041d0707030400315038512441c00700070801c0071951550780640300c202c1500b01e6405103c0e42d600300c03032030480d010440040e4030b20420f0000604001c0034140641e80c010004115101805000d1070301c00c0c0c0440b401c00000e02c1200501c1940e041440c4480040c000178544120f01c3d6040c107000c00c00c2c00e070800b074041c07400b51605030010b08280018085400e1150b402825681e0312240c41302c009242c0b0903140200b01c011242c903e1070103041405044c05a030801200902c64556134036548031008560400d142d41442400761107509100040190324482070f038078407091201c0f10303200c59a0000b8074001442d000010389900400c41c0d10701040e1514a908964800c5c2e1510143c1451240700486109902e43d0241c4e4215801009001c03c1000109603140c8003046040200220707 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 558485737 1250 558484487 558484489
    0x2001020f040302010201051f0e070311131a401701060509090616020f070f08070603061206050405150c09010e10090605031b040305101a0a0b0c0a12030c0e 68
    0x7429105402c4034231302002c8041011007040150158448050b0400003030340f50002d0040d940720390015a1107110a10031407401d10000a8849840f2504001201541d05118120f08000f202588410078004040c500c43c01455243c00f1103400c0c2d401c0d00003010741807100f00e039a034540403030480c02070700c40d611180d401c4c4640420030b070810075041031154956000411841d100c0102807845801ca01013090114047c00300711040182d4204150030040c1060040d00d50000c2c83d0031412424600030f07411800401d820700a04020001c10204038003001a080301d00025140c44529000345040311210000801c0780509042101400c80c0c3e80182c00b02c4082030703c0350310886041e0342c10008d403c41038007001d401007695000184801c910a0f005141c0c070240304034503142c4e039617000030110500ea04254407c5403958000100188040402c1c010101401700c04030b01250004c00000c009402c1c04403034028000c41c07080104070300c3c03200103041011400b8150000d0000c0d0106000e0070002303001e0101d950406000c140044066441d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 558486987 1250 558485737 558485761
    0x102040b0a110a0b150328150c02030301210506040b09191e0611041214010207030210020c1f0203150f0f0d0201090305030a0201140601030e0c012001020f04030201020105 75
    0x4407560140c9440a075903520000254602a000d42040e018854103140d0580f011a000d1801e407a00d0b1602d030447d00c144240e2a083d40c0c0328000030400b860080c1403038017403000383d6000400e49054440c4c07120081f94892011100001501003800b0140152007010184010311214950141c05030700760100355942c040300d1032002c001f003080c010001426010b000741c18800d800070301c002c11016a03100c2c0301c000c601e044050b030403039010380c00a800c022103c0d40701400840400c419411902010600341001394141061610003035241e07103007100b9400c1819000075681e868200c05000708902d8260810410030b442c40c5003c4030710001d4008568032038048003d07000c0702c00c2600d00035200c03112804000b0590900503003100244200310f9400303c1c0481c1440900440400000c0c02400134104505150780002079481084100080d8094041e203218103144c64400c2003038500c10013040103102c40b2428202040380da101c000c0e00001c0b24601e000030726140e501c00300d1000c43c1d9104103001001140e000341d001b400291580014001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 558488237 1250 558486987 558487003
    0x15120b04080f0f0f1306020f07060c03110105091f11091201060b07050a05060709030302060a150b040b190306050307060f051c0e060a0507090e10080102040b0a11 71
    0x64801000010006400080105481c29104004504000245000c8983e0f41c0046034224010720000c90310701040c180c0d110014000306098801044e5001c4807180c0d19840705031343d005000400119107182d405245c050810740c2c07460309456000700103a18100d481d40b5150a243c1c0c03404403401405040b80e81002815018140b42c4a544c1d007801703803502c4400010464194003413091004a035407100c8000640480da0400707404c400d40240c1c0503000e0100d9510f866410007900807d8070007480740800301480425800078401da406250382c14001030082664158480d4200035034006000d40c00000340215009402c8000341c900840c440401c091b91892030314098041d41e005000f0207405500803241003103920b2260000c0f176110146824842d2604603043d0b010b14035040c01801c1c1e14a01c81e26501c0c40b00280108000450380b094282208008504204400801c0d0f5004d5110f818039500e0003501188403d02c49150341d82c02042c03032400031941c0e035a84207006c8005410402020000c11000001280d8031413000c21004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 558489487 1250 558488237 558488243
    0xb1e090304141e030a08031509010b090103090c05060d0e160b16030302120f04030e041b0e0a38070819051201060815120c100c0b0a1512 60
    0x41441c2c0718100c24001c032820424100f1005907126200214252010321a05008500601c0c4540c1c0c1c91030030100c1c0190006100c80f48034000d9481400400c081000c180942d0b0005a09180c0810341450605041130104225001305511640000e4203040121030740d030280a0003d014801e91340d04090b008401304d52041944a25201031004204041509a4010306c10481c40d110341001424488045092a1140004c0f45c035050916000010b00080c140c000c0308003204c0c00811502440304201c003810511094081408000a004a04013524504c3c0c0e40e1042010203482d448000050400100c5081907940b10303a060388421010803050007158802c50300c0100d92051390004c0c0b02901c7e04400340144151b00c024143e44c0000c1040c01d01400c01004101a0130780d00811076030b503a8000d00d080450400e400d696003402540c0c4204e0704560400c49028011400c031101d4402294881107001903018156124503203054018000400601007100c180c106501505000c4c1616440000325501d0702400200c5c4404070341c0103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 558490737 1250 558489487 558489509
    0x10b040f0504021c0305040e0a060609093b0f0a170a140a030603050f01150506070209010e0c0702090106020a053c01020d0f020d05090a0b071202070b1e090304 70
    0x44c000381007201001100c441c03191400600c0c2079a0741c0c2e102e0800800035140400c0c4a51115001c11403241d10841030405401206003c100d12074078440042c0640c8080c44031201003104002100f01e036042424483c03254032081d001034503071001c0074004e070356141d20200c0740131144061101c45548105544009503110000e00741c94100a0204213040c0310181d40218020001305a240d0101100180c0c0c107108044007154860000b041c400c0c4500030348555440c4541006006d81c60a0007208096034503078480301e044030000c8030009002e840d003200c0030702c45100780400a504040450000228103a000840c250a00d00a40c141c941150500b80307134180e0407019441d46400041c003040d042150030700742c41d1110218100c0d28001494540c55080440c00e50304200040c0720078030750200780303191422450f01409902000b039030041c141100c200c2d99092008076010b0300e030300100188108144010f5020758126140c45401254800382c510302502c2c21a2806500d144c00440365402d000412440d02002040c1c40680c0c00d190b000b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 558491987 1250 558490737 558490759
    0x2030c0a11190510032a0f0e1009061b06020f03040c120f2003010606021b040204030215030a140a06031209051e130c0c140703020f010509040b1002010b040f050402 72
    0x10880160900800e40390344207040c41700c44040c0c0c21b0045101002d10700c1c1d6840d4400303815809a00642200c2801c0300003400f81040c01401026141e11a042c401a6a1241001c04031880c000608928040342054001c102510000c0c4400401c90b040001d148114445c00c1c02d000e503691201d18814840712071078801841c0b128070240d01d00000d0400680c098480c0f041d0007003c17402c40e0020740043c0c01d440f02c9034001001341c1c111b411740c5402c01e00394075103914034502c00307803800e500d4035246a020407130082e00300c1d03440b9840c10004004904400c13215041b5413007151700c8030f40744000c81c1400917085004244d0780c4800c541c03860900643c0c5440d50f001c0c0c0010707011540002c041d00f80c001132418120140286a0113401da01c8604074807105101700f81407042000d0282d0301c0e40c0b11030440318146400440c1c4d0340c004002c0309031a84200c0f000c20041e03681604c071070032200e020710f03225448000b038201040c05495405982ca6110901410310410303140c0c150b10400c0c05d018200c40c107128103095100b1003000c40b20113840180d003110380c004e4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 558493237 1250 558491987 558492019
    0xa052811060c0a170309070609080604062a0201020a091d0601080601020a0f050f0f03031006050d020403080c010b240d020307090812190f0f0f02030c0a111905 70
    0x2010701903038800c0c42d0503904018000d64034440708504c120001e400d594400b0050203a0014104903e0000d403140307040442c1031700e00304030f850341e078a98008000410541d121800040600144040f460325014203e80c205a01101008003a010350424100e202c002891540002003120301c1d214801d0848580d01e030a10900e0301c0e50360044640013070040a840c194070407044c2410010f02c0720151107162a0040c00035000c07668a1550040c02c0400c90344402050394030a2062015199255600b40c085a089040280e540c03000e000d8008064066a400503007100804100b6980e190810b412440246000715008107440344040c00b081605040b600c9200496482484181810080c070780c015608038450b4101100f003581d4600d1098a8121076401c100b1051f040425110201415a0034050041c1400d0800701c455420700200100345012407040c002c2085100107c1e0004a4000e00489030b11464100540d0000d4403a0706204241c0c048540007039029040c40308070300100035820340d200c071306a51005000201c0349071018 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 558494487 1250 558493237 558493249
    0x60207060f0828060f0b0304060b12100b030c09010602010b0a0f060504051309080f070b0601030c08130c08062701020307020607201912030c020c01120605030a052811 73
    0x18060f0640603a43e22404a07444502107417a20003001d02c4c8504a07540d207400d20f441070541701ea60402c00d00841c0e043d0341c283c500ca0f0000c5400019008040d03000180500303100006440c0a059480154210350f1507400031500315410342100d05a020b0a49111710343d19510b440c0380400303607904e00c101d50001d4002c0c80309024501d80040121071102105801080d5603d560301d80000b03541c800d618895001030001100340c10895401e2803594071100c2400d0403c0180444007014289850040c6400d4001030320300d0050082008046a560181170450201d8900e46001c4003001c0a810044e444840c88005c00c41817045134020500840740b144905038080c00058840010640e01c40e40d0140c44602450741c648820654400c04000c3c528070944007001c0b40400c0398543c24110054030140405c0c000305402c01c06111030980c0c0004e00c2c805003003000e06e462220049025000d6006003c190031442d818003414aa140030300c08002034000d0024503081e00141c040c0300c0d06441075a04030032000028480c5a40b10000c2640327143c24 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 558495737 1250 558494487 558494551
    0x3050f04080f1c0c020303070818060a020307031e230103120315090c12060914040813030c0807050315010e0103060209040b040f050a180f021c0507060207060f08 71
    0xa41c556902860f01814400071346144203036190041e03002000300100f2951100c60355422120341100d00401000294101b82c03289001011000c030903030000b010070b000034440d80c8480aa0001c7c1c110210581d0020954803028141c0c0c040e0841340c1c079002c001c070400442c030404260390403203030300400404a580030100180c0241c04440388040100100074030003d0100102e0003640e45440c16a503070990704160b48076410342100d0590708269036580c0307000c0580e010b21181425194001d504010b00d075442d64a030301107140480c0c10b00c0e00000c1450510740710005140400207454000d03144100d060321040446c0a56110151600b4419503450300c0781000100046030b1503500406181c4809000800c0420140001c2426581544d034050301965595040201c0e251540c800c440c505011003801164a1782c1c80c0e165045038148040707000c8d110f0a1080220300c6401d00004180000d141d010098401c00382d030328130303004c0e403500c0c600e10a000209048107207041d241442030003410300ca4120440303550400703003080910450305140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 558496987 1250 558495737 558495757
    0x50d2f0f01031e0b18010f05040f060e1504020408010c050408060a0b01091a040e1812040b090906060405030a05340312030b190504061d062b030f03050f04080f 70
    0x34005c0e00030740c4c81520060705018054910740c900b4818a0181400b08846060f100d118030036140c04000c1c4011381c0c4903072919820003603443d032003007801401000003002481154070a92656103030603421024150405c5c007400443c2c4510381910301550383c500402c401d03102c41034130560001d480c40314280644410314449402841290410074107190300c0745011001c5420586040d0300f810003500c88030382d403103604011250400300366500f031a040a142c00c4e840c1c1c48600400250511408400001840d42e40341c1e08156002060300404980e81142c103810111f0325900000c1078003621401c0d043c507803164058015079680c48000d036941505140c511315220659544140d0202004154440e2031800e0655124a07039100c1d142044171380a03020502d0301041201325070742d5a1161076a10700a000c60700c03910280c42c4680740d003c0400c0d1182c208a1500c40100007411903640100030383c00300c100030a242415400700303900100ea40d543d10100040c1d11104e000e120200c508460040610b001005600303555104080a8162400c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 558498237 1250 558496987 558496999
    0x60c070b010501050d1b1707140f180303030408090a1707140409020405010f0915080309010e0d0501020a0e120604151a21070519050d2f0f01031e0b 65
    0x40305460b40400c1160b007100200040304180501f0b6144010700b416a000700c1c1a080802082040f1114070070342c0c0c041e841d8030220a1902281c0d103c4089525071243c8000500101980d0717503450141b0700140d07140c101500c903a014025140d00410040b8446203401034031481c41c40100034084c07808280404810a0b010301715000b80d02e448030100140c07141e00030140a000c44148006007107040c24101c800700d48126010023603141c1303c143e082105420200881c0c000c11020310f00444d50b11100341c003041c601880410010604e603c009210442c5543c04000b01c86204401c43d01c0070002610070391050755a503c141c4014281103640918205202031307039800241e041001e000040000c0c10444001590b452038508140420a020354108142050912484010705130803a0340c001c00d500d038541c4d095030580180c09414042d421070142142070042c556074401481e513680719210007a07180400390818614000320064021400e4038040b6003150f0080c010900043c000d0f0380c000500c06103410b181000340040200d01c40e0410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 558499487 1250 558498237 558498251
    0xa0e060a1101150e0606070f020f01030e03040608060a050d03081513020a0309020306010f12170f0a020f062815050409210206060d0b06130204090b03060c070b010501050d 75
    0x54000e000c0c502083d4200326030a20f01034940007002c00c10784401002d461050754100122400185281158015181c0645d001e903000603100c0c00680080003840c00c8400a4440814001401e0385c1c004050b501c1000c00343c0300c002c2042d40c1c0e81f091002d00084c030b1200401103051100000d17114407082c9048030301c90350010465085130300ca4100510407680a2400309002a80b81c08240c810b5040800410740184048080e1a6900f40340844480d00744a101d60001c02110411803402c80c205074030010f94115000d41d500096950181240c0170350b840b101083c504846000b901d002610402100000310345030100040c1020302c10074800c0d400c0c0001c00360031045150f1806140d1010441d41ca40d4170072065240e206c0c05101c0207113000d0b9440c1d410120a88005117017158031580c00c1007042d40380c902c45181c496030301201c0701307040b0740303d100000d141c7c0750301c01c84501250361021400040400160304038002e0241d040e02070712402e40707138038071178071001d05ca0b41030080c0000304210010801035100304000d081c1840e01c075030006091 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 558500737 1250 558499487 558499517
    0x80c06150613151413240e01081e01140907031e11071a010821090405071e020601090e1c0e0d151e0e0a11060c07031a07050a0e060a 58
    0x203812145e529200a10030100c10311881c2003000380000003040c0740340f803610703842c0d298000240110403042d48241000346c0d0304003144401c003510510700f0031038109101c205115070312000b50400064443d10414403078603140c07001c00c10720750003441000381c00300d11062691030300e0221102040140441c40c050704c13481482040b1502c04280910044e1102c55512945000154503282100b49015000500c01032001700540c5004070840388e03581281c3e180642900d01080c80ea9400d0415600c9010600c03840600000e00000841415408903040d410385801810810050000c02030003a690504004072048900b0900c0100400c14080d25100714131410040c04d012a40b00b49580b580941454038218034445a11016114407010310768099149801ca00c80301000104040f03501c00e0b03920310034610301400e102240350f01e030542d94403900c08581011007841d044407901070766807420f5600d42c0382d45a0b40700f410100c450041807076144180100c03404d80c20580d542c10640b020805c02c20199a03c446140f40502c0b089a0340003401c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 558501987 1250 558500737 558500777
    0x9030f030a0b030705060a0801091104080607030b19030809041a060705010f050114060304060e03041d09010e0f03030c030712060603020d06140303070f020d080c0615061315 76
    0x441c59071800081030380e6104200389440c0403031a4019074460380c0c1c1400003010482d8451715507411140080c00200c0e111040c0f140d070200728800e0f40c0001c80103003d42c804024500790160040c20307101c102a1001d0443c2403039840d407640f9150031404000c08901c002c008112240c5011703003000e01030310402208072420046110015080760301c1110126956511400180b19012091140c0d50040100301c80c50103c4060348000a0001d10008200401c0c003a916520300c6070010303040041e80e028207018003e24041900c0b0300040b40120800719a030347c1996082c0752a5008011021900e1407a214501000314119141d800364283c2036040141510704205040c052203400e1201390080c44000e000729100141d480c00000f034108140c4500f504240201410341c442013482d43c030b000084a207030a820040f603280840e0035100040d4003001580e40641000804035480541c400082011070080c204c0c4180382856855160a20100d8021f485103c89200f130001c504101006400d090901344403c1c5160104c4500c0301c80007418a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 558503237 1250 558501987 558501991
    0x30903090d031106160527030105010b0904050a0c0f110f120a031a0a1404140f09071a16050f1c0e010201090b0c07030513080309090a05060a03030809030f03 69
    0x80051403200300c5201c1c2c20010304c61250030600101d0b1840c03801002c110003074001e21860300c003030f1118500e0308800c160b1000f420f580c11a1100c03006000344040d5a680a0203111900045074041c13080e0b1074100800c80c0c0700b82034807506c100407165445160b040e540030441a6040341c503140664516004100600803035100511011240030f0383c01c400a621f5072032000f001411568420304010001c40c2c3c0c0850307440360b580c40840080488684090340c0417000810008900501206520850501010014012890748002480e0b220b1042d8104994600b40e6032401010721001c0244011640b0604000a40514001d0303001c0b03a43c0c103030084040b81c09100d0071001b002e00e00400c42030107013051360050b1480010300b540150040703e9000700f48000d1117445403030380303610a003204007910f0001d900e2b0002a00e10101402103007928a4401344001034208507682e00c8003140c032648500306003489454480c0004135940610b200e007600909010304141c01040c21030b0303800d840500000e0440d426922043c1300104100e40548001d43c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 558504487 1250 558503237 558503243
    0x302011a0d0203060f07020c030a1a100b030f06010309020613030210210f110f0d06051c1401270c0e0103080f0a03090c060f1701050d0305030903090d 66
    0x20380d1411406155810000008458810560768502001503500082c1050b00810345000f40b6a40d07071076400040e490f0a810000035609405468282000d003d072030411134001804210b601410360360344004440343e0000501610341d0305002800851510303084207a070141c2c0140f060400003503100c0650000340c01c6411060307000e0300b800c080120502c11810500c0f2003400b030340aa03041c07040d00400e000100d040103009840607444510341c1d9540e01c181001050300807500d881d22a1010381c0d915041c0a000c510a0f0303115401000342c103030a05c1e20008044c2409600b2580d000081c507060700c1140420399410f00c220811031510035040d03495031070003051000c00e2000e5440004e0010307903c038520801898100e000e0710907036101c50b0510100328010400705070300804031611a081558556031b60070b21401c050713004040d4000d0140440e8040203000c542c064101c034203030f1180205911403041070182c83e1000401c01009000300f0f900600501c4000d030001e4040d40103036030059a008292420321007054041000d00202171415 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 558505737 1250 558504487 558504491
    0x20309101b0809060409090f060c08060d11032e15050f09100308030c07020f0409020f0114040308030106050301230f0d030302070b0c0a08070206040314160501050901051806010311090606040b0403030201 89
    0x4030821405102d07100d4100d6050a0031401c03450034030005034042039480800351030050a3b03443d1030b00a590a1000000b0701040300c503403401200d81c035220030f000640d10900c151152480c3c03c80c901035461100780c4460840700014864852100d2080c1403102141000d0704101d82040c0718200440060000400f5500c00d4800104d019141c400500421111458040f0b8440c080c6140108440158444950542c40c2400a080001c03070807540e440600f106101d682d002505e42a404000807070303010f5002c8000e50494204191540e41070b400c100004074600c105140385a0710032a144030511040c01d1820301d8680322070103820700509004640d00d0708655000101c840d0120f0b244d0015880003035540101c044e0740c200206100500c12494948d0300075000000b214031481c0e02d1074002ca094210350010050f5507848a91003030081c00541801035000d4041d100c1903c0b0301041d180c0e05c3c2c80480070182e000a4883c100c90b00715103410300c0c0f00d00d000103210701150094117058101404001c003280d420500300c000c0000718429400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 558506987 1250 558505737 558505763
    0xa0c0e0d11030c061e0903070e0a09020405010e0601020a15020913053106050c0d0e010507020618120a050c0604030f0801272406020309101b080906040909 68
    0x1050b05100802443c60702c0340304140500c140310b40c0740c81ca0f42d11789800864441c40da251010700c0003d10f031400079406014119200d404001c1d504906070814245d05100780ca0034403441e601c500a210310391100300c80c201d0041c0c3c0000381c0207010031051041c4850350207140c100185401c00c04400b0840c100c0300c8000c8402d80f95112020b100024200300e040400b05034884514501030b84603100b05082000443c6005480d0310303242c02c0440c5d106a41942140c2c40c04071906000c02c10104400d08290280504480400142c0034040c00514090307148040f4403610032040028080714803180741c4e05085600b100145004100c0c050040028829042000d140214000c3c6c94501c002418410010010326050300304c0403120089854903854040a00c042c6518075003142404201c240313400000d02c1c4c41c0084036040e001200c250007000515280c010004082002c4191581303041440f00f00d809840d40d07045890040d5801c1c03142c44000e000b1418450142420400080000d46016607e80140301940c0f200030040d82c2500d000751ba = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 558508237 1250 558506987 558506989
    0x5100e0f10050c061f27020c010509100506030309041805030a021f0b0108130201030e0601121406010609050d0c090f0204080f060403020601120614040b0f010603060b030a0c0e0d11 79
    0x10407140c0c01003229820b400314008022140002ca100313840b0703202128004061441c0d621009003e1400e010011403421908c0e1000300320701d13a0203004169000d1009020750782e410f0505c21868003071a4070409014000718038020300b28062000903c0004d8400c442e2002c8011810000b4809100418170000281e00500d000da00c010030b1040114103100d011444945843c040c0b101c00d0741c000c5040d50348440518030a64800341c41e400181c0207070800750407a01e094001d1000120b4801550807405040c0340c0034a601023a5482d025a8107a6158401c0c050381c40400c5503644100120324040c1000b00515115060280d02c1c25583c8071003400340d690483d911080d0b25004a403d00c1344280c10000c803045c5d2071904009014905250303d02a4640c001030041103c0c8080c000701c00700611140f50000d0010380e80c030f012000e909207013500704000c4240b0151107601590103c000005000c41c030a00601054030841020603141d074a81001d560b00070300d4040c2054003030000c0f6100070b07681070341c1d04805130308000d00503178480450a003e40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 558509487 1250 558508237 558508243
    0x30b0106050712030522060e0d030509030706020702190e01210312050702012909090f0303191409062a1b03070506100503100605100e0f10050c 63
    0x180004040010621003100071030803d42c0e010f00088824200000c154403607840200c5486c0c012222900c034104c1c1e003010a0300300300742c0341e00c240da41051850958082c0d410406003101614025181c1c140c0d140e03c14404030001c94000d500401c81c2c244020920a10325071191003441075540c141d4001e08072414803a0041001030700c4d18613504010403c85000004100c0c040e030f00504000300015543c001c1640e00d00011780d009000350f01c400c4c540c80240ba0220619600300c4100001c81c0030100380c1900070103042c400700740f00810020ba0402040f0090002d542941d0b10400307032201c0c0c0c1aa030318200074403984480c0965192080008000d00070b11042c00940b0862030255108013008042c807980d20000d140100b51a00f48402003010303144548c081d021080007a03000448414654020000c010740039005546c1809000206010a1411600250305950b800480140d04004641c0341d4400c40d0341001c0c0c0510103070b80c068801c110300424400e00824407814a24401c0114111010342c54854010510000f003a2404031020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 558510737 1250 558509487 558509489
    0x110a0b091002011d0604050d0c0b130c09020c101b020604031805061c1a0a18090b13030e06030c0a080a0608070b13050a08070b0f0c01050c04170d0504140102030c0a030207030b01 78
    0x9800e08112500141c0e0303408ac80c1d600014800d07064050182219010042c8240115004041d00c8400355140c030380c0d0035004c40c0c88489400740c0c02c031030520b841c2d0221000c4625028030681c212254010304544c1c0d440e40c800ba00c890740341141e00000e00100d0140802c5070340c0c03200050701c0c180c208449810341c0b0450030b003051000c690f80388100d51030f185460b48140410380c0e03e100041007039490498140200c00c0d98000d031340c8050082d044005144c900710808011086050b440740803d424040c0e5a01a40b001d0800281708483c4001da407603c8941a041115400c803038005e200080d04003c1d0f041c1c001a07520b540d24030050529440e600301c8038104000045005030040d400184801900046415550152804480c19540c2080b03100350100b001010a50014094165065a07200c124050081c0158940b510f4507003c01c0d403050090396541c5100c0203c8210814001800e40056030345034544508e0141815401d44042e904405107604600c0708120100101038240070744400c0c1482600142181030039071401444403901 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 558511987 1250 558510737 558510763
    0x20c07090e0d031506050d0f051e07050f041a0c010c080703060801050907210c0b130b18120309040204120b18030d0b0f090f0103110a0b091002011d060405 68
    0x2c044503840071213100c2ca9080c048075168200555104003642100000d07000700344004138042d182008010f401d00005d41000400074906507501c81c03582c2c45034000d950300e000f0441d081c9100d501c04d00060102d900302202040800c0111401d0f281059078007480f240c296064801004000303400c80083c0961a46c040c05020040c4c04400d000780000d2a14201043d40e072900c500c20b603080da5401c0c545088515000341e28040f456074000e5114000c00c1e4403402d01c1c1086031300a003085010350501080020781002403000359030380e0503100351108902810301e0b41082501c02000d00980d041e404200a8821965214802030000700303010300d81c078440007200303007440940c0034001031180603250144003054409450100460f2828900362000180800a07880801c003224000491281c1245450b414000b424950055650480f88654603c002034840c0205212000500b0b108921501c401030100007414581300312101c0040015100009100f1a20410609052910700e04410260420802c0c031080c03000900c090707000140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 558513237 1250 558511987 558511991
    0x3050c09060304060b0105041703070302060601030e0c0f1f0c02040c03060609060c060912020a0b070f050406120e1e0f0d0801120c08060c040e011203081603020c07090e0d03 76
    0x140c0d14000ca101440001c200400050b603442c0b071002c19a00a1341a00d015007104183d02070108414042e541d40da52200e0401d41c054842d500024070250303c240602041000e40801501c2c4603801e0006124203840310380046076110707000a102c2400307000551308109110409580389180762129005100031217842e003c00038201410f1001c01c4c09440d03080020031085895270301d04880704410a0814000500b005070000300400d84500f03002c45569400a10444201c0c0500a68001a107892000343d90104070551000041142444108219801a4a031048200160402040015403840b03c1030800a040385010340e43d603240c81c10284880810800c400300110004002c0050b410b034880007a00b101e030144104000c40c11100101020081040c0542e8010041c0000b110440d040803071211a9941140c02a00080c80181c0000248444203450110780250161107180090b161005240800707800b92040406040d005c020810000104002900080c46801340010f404001c1c1c5400c1130919020340c0210342094 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 558514487 1250 558513237 558513247
    0x14010e0426070609060603060b12062205011b080a1404060b0118141507020607020405130c0b0a0e0102061905220b010f060203030f130f0503070c050103050c 69
    0x40e0446005107400107407800c4884104507000e020201442140002031100e0f013080d94a1040000980007801070b41d1041200380701c1d02c40c0c80c109008809a9020349020345603c00404140c020014008400341c183c1d41445034045d0503c41c1d2100c0c0e0a44d09400c920040745601090313600d000c0c6500112441d0031401241c6c003808600c04030f039003141d14114042c4c80901401d588109030005070b03006080c000302004070802c0c002182545da182c041c00440041c1d1815000e80361b40e80c100055a05560201e0745c0e2241c1c01041c0030708081c129028007000b0700e8001c190080c6c8450720b08240307010404d522030b403100401201c80002d941d692005002070001c42c541c80d20342d0645d4007a0b401d020323402c1c010400c1c0451a9010603030004190762280424002e0400030303240524548070460700c071400d20403508641c505a40700841d0405020b40d44280899591008840e510010b459074804101e441d01d8607000710501900500d51451543d1181e214907003103612810f822107a07101c81110421407541c00d8014544d214415684190134a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 558515737 1250 558514487 558514493
    0xc0f01180506061309060510051e0306041e05150604060f1d0408041809140a0201050f0307050702060f03100509091e0f0102160c0e0606070807021f0314010e04 70
    0x9a40242030a031180040004e050320380401c5500440306940c121400744480d05095035200180c000a02a41d806031200715a010840120103d6041c0c4150004c0c0040c440c80d6290388407031144000049070003036005100003440c00819420002c403010344101c0341701e51285047c5101008111032499000050071840346408000284512080034810001c1c2d4803a240255158a82800144a95003000c86208450410911140126031102c0386441c410b459036030304408070310200c6d5650081c0940003400904100400c10700c5141400185801140505001c0e04110311940011240c0c2c100400300c80201d8404010022503c1d103880c1404002c2c03c05507161111402e00a0441d5120300c0100c00784544048400c1c00e5458040d000c21150043c040c013100219107501c41003001020395103009505503405210148046030400c1c4a0030201d01600700141b28516188007941c1b04c0a2680015800345d90001c100004920880c010f9802c61018002039035001440c40c4044480051a500c10782050740e054441c10104400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 558516987 1250 558515737 558515743
    0xa02010c03050a0c1b050310020f1b010b0402074d010905030d210e07060e030c0405040c080708030f040303031e06030b060f1806010516080c0f011805 66
    0x25254042c601140d036078001500a41302c140544500400505116511200600e002941ea2007520004c07010b842100541000142c141d010301c00c1c20030500a41002152040803c12828108400c0e0500003c507494452200050881e0010a01521401c0344e01070907054038200142c009050490000030700e640985003e14074171800ca103962540c01c040c2c0709100202441da001d244502d000b8000102100d0031980a030034000c25210020007424a0503000c0f60610449246070b005400b5048100341c01015180d140160407100310040710f05081c0c250060400c0300c100c9407102d0285a108500030700b0381c4084a40f41111702e0346815039a51114101d0340060040300e0681e40700c6022601120380510340801e450b0f6180c010030340d0314041c3c8140000940e00c1c2c580000100580b80e05018071600d01191354074510394080081c0710380051101581d10742c550213a0005800340d2300a84c0a01140341742c0994480108140e690740322210741c0100c5200e80260710451008140d4082400b0342c4e001200c40304a000500116562060342d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 558518237 1250 558516987 558517007
    0x60501050a0e0f06120a02070605060109031101080411040515101706090a0b0d14060f01180e01110a0801030b060d15020f07080406110c010201050121080f0c06180a0201 74
    0x3c403521915840860f55503848041d220342c118a010800420304081e03069100a5000081c01c41c1d00c1c0f0b0078000040c4d1651701424010007120380286503820030b80198001111089001081140c0a10451280d40f103079031101d00c103441c802d01c0c0112a10000008000412041204200703030442003100075614180508068000345411a0059544031207035196003c600c80600501c2c01c070310744c00c40780c400381180070300c841ca102020301d840d101429104540c44101000f000c3c4c0724240203007140101d0403080520216007940c8040c9130185014000a03aa082604030800c00383d114185610002d9452001481804044501c1540014041b1070a009200707540e80c0301012911203100b1000825404100300c502070b440c00c070407607400c150700c08001517441e80c544001401849120114034414403440c850400c0c40e500520990381a035030321248071280340d203024116054010340b198045501850074400c1900f00440580900210311440024158510b04500440c5803800314074090289079200303003408005030b40c0084200c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 558519487 1250 558518237 558518239
    0xf21020c040209030a24140f04020d1b06031d0304080715090f0b302a0304060507121407270611190218061314010306060501050a0e 58
    0x581c4031414500000e0608005e00005807a482c1c644001172256805105c448161746164541007094070a21140e01d202058103d60010215a004020801524201c00340c1c940251299907990030b0101c0c0000310300184460340d81b003e00440d854070184200b4a00d4000e038030124440100c011401d00385860710a960381c1c4800c0c800c1c140e200724410800031010384591140c80144c1203000030351080c40c1c0d40b1750f003003c001d6000e0032041d07588400c003040e08460448130089205081c2220640c1454030345036070402c08540003038401d54149402142c000f02c0784110101000c0e51040e4065403000a4502e4052000307010300300c01100e0004a940780c90484a5102194404950410018513000c1c100550b000343c0b0651380d1440b006c188586030700250000034619408800c901640340e404058828140a4080303111004035500c0000390321800d414001e582c0750100201444d40301000502503081209081c0b016001c4990280440d030240114000500030b204103402180004d01d02880c0880c5032418810008220010640d012 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 558520737 1250 558519487 558519491
    0x60c050c060705190c0e0c1305100329010212040b030f190e1b1504030803040318030b0916080316150c08190b01090b03090313030f21020c04 62
    0x1c1c42c00e100e02004007400c0038140d040014441000341c00c103030704202542d100300b01c440d0342d0f805c00140103141401c042c0c890916055114a03103240c00c0104200c10741075603074045010903170344450031401e075803011000310b041440250300780c1c5004402c000024141030803143d260181c014204000c100c0c0c0349007030085a03801903043e10115100d88950754900504003100511003030369400d01c1c102c009400004030b40f071901601420790703441520741e6a005104c0006000d803204c40e03441109001c20404100c84c24001d5034001d10903d807500041c3c10300180ca040080b0700ba0816541500c0c41810004404d030104089060a405003100b401c1c0c10385003101c403940d80c0c030441c484401b01c1041d070061f210400c54100d0340c8902e8011554820300041010450040c600d030012520305210541403800100400c2841c0702d565510801a96002e640d0b07400e190454032150f10240005138644020060075840e103404004610246100700509040d8210070b0030702c420705010841d6100304035000107030709111441e000550100703881026940 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 558521987 1250 558520737 558520747
    0x130b12010807240c0b1f05040b0102030702010c022b060b010206190b011709030a0e3304030219140f1e150a021f0c0e1509130e07060c050c06 62
    0x104070713a10303221404001c201850f1141070041452040000c1c100c09071002003c400702c10b503110204400c1d514103205031130158100300a143d000d940325229a25030b06001810f03052100d804d9508003240d81c4100300c0c28000c0f641d0060429001c00030b1501030080c540c4001d1008282130f0401d0002c081180d101000c1041800f170303448440040c00e03405409100b150300501e01050f1024508008195101d601a004030300c0014407410003c459481c00f4850400d629038844e8450002100c2c5d04c40311a80c148503804110815503007404004010380c0c44980004e481d828052002066901e8100644400300341400250701c51a000e039036400b00c64441c46101c814401c04101c070007a0103040c00d0041600030740368000c05102c0b4000010102c030020740004003500c4c01c9200e1041d41c4200710040a0341e1003110150390422001845804041d4524642000d20b000140309240c00103240c000b00c80001805038000090b181ca03420346a104000101506000328801424a810302c100b0b8a09140d88254a03019400010f5100b0ba0010076 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 558523237 1250 558521987 558522059
    0x90321110109060c0e2706150c1f020c060402060a030f060e01050901080d08190b03010905160801020901021903031401030c03060c05041811130b12010807 68
    0x8214880d10641000030005511a800c0c04005085514000e00104000c00400c07040750501403c0110b179000e0b50f1181d40100f40040e1640c091090018000340e80c011240300007102400d44810007400c0045c3c9540c01802514216581400ea1441c005940c1c1c10041c030612203050000340104909034480e80c12108656070b041d40c40000e500500c40f00319401c404c1454098045a4142030707202c000d05039a0201d8816007103a90701c00d20165038200a4401000280c080d10118101020342e02440c40d03101072010780801c4c5464001c006c2400c4403800c010946240e40305000d51070400f05003180c20005810b8100c002e515000c0c0500011795100c058402c0c294902940c07440c00030601d8442d5100d9072803a80484075400140d652410500c88a840da0702060318840d01d4410030400650185c000c41c0d0445081c1c0940c5085841075030001d034002d001240c0c1c4501400410851101c041c00c40342000c0002d004200f86003622900400241390340c00c60160404000365110b01c50502000045000c1d0001e4203030552440107640920340 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 558524487 1250 558523237 558523247
    0x5150601050d1e020414030c0301090f03030c140a0f0816021f0905030a020706120506100503091e01060612050705030f091603080d05100b1b0c0a0305010c0f090321 72
    0x2481e0743e00001d20100d800b00301600f0345c62000004601c110221025011800205400c981122500078000084008100d000074001e402051b000e031403e041824421881c003813019000d60003140740600003071139041d0400c0910b401003036094101d02c50700604003600950000182da290080400000200802c2030300406404140c5c110030300317030b50b441b40a07a6110b24032040e0195480c0224010302c00440e4001c0103044c00c0d41034912409100740030003442d20b112410740180a85440c0e201811001c800e01a80500c0c1c2c050848040d400c0708200340030b5000203025032034060014a042e03414840c0c24241781c18082842a030540c040b040d05d0300b16142400703403103541d03d078100603030b1600150812452900018610000901c00b80c1000b030924203640740c1c000c1c40300f941c81a07141c01495070079001d90148042c0500410b80b0f41c916910030b11103011542401c588071485204005002c44041c2d600131101ca0f9101c0000101e01a40606e18a2005400d81841c1803581d056680f0100c4034140e101c80001000c00781c40e21071051912074 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 558525737 1250 558524487 558524531
    0x50411072604171204060e03070608090a0209040609050105250203030f0703020f1c020d05091c030e07080f03030402030f0f0307020112020403021e1207080a1e0b011205150601050d 79
    0x21843c250f0b0f071300d5485d4400f611980200071f04070320034010800e0000e20302d40214580c500ca120400d004d850810070640c02c1000d50301d030103807094800690750100320000074001d10803030340942c2282d00e08d14140c04100721030403441c600440319001190000d0090080c9559428203040d0442c00038180580c0b5850740b160610082d020380c0003804450700c0154084010844554001c003034904100d103052215a607081259581c40700300d50100d46281715040f00c240c51070340c42548000040c00101080d01c0d500340d0746003174492500803010718009850300000240000c62400304460b06040748507101401020340754005254680c01020400b1341400401d080e145042411541140c000d0740d0300420001c0200a03540101588505c1c0c6a0000c0c090340140f400081c9820000074014101c500000081a80341c0195441c82103581c4451960b5110510000c02800064021100d10740a000510314603071b408442d03410021325180319103800a4035610490244415030343e1107401c807441441e504001084042045031504000140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 558526987 1250 558525737 558525763
    0x10e01093c060e04061202041512030314070201140412031116060614030705151e030702011a01050a0503041103010507021b1504030b1005041107260417 67
    0xd0032281c446401e07501001c0100342c0b40c05a40b00c4109649140500044980d0750194480c900c1100d51110018034241d0071130f0351060104000c8900700b0340e03034031a80c07403d8051240c401c901081d11841813800480d5042043c580c015400d01c002e12800c0c404106050a030a4090400b84c048000c0202c0300b00c0f44c42c06074200e068201e4022070510b941e80d580c02e210003501403a0100c11140c0d030f4201000013a92066030100d00840e0600103001e061107074608410400d011900c4041042002c2050041d902d01607118410344103000b1000722099a203281c890002400c60b00060103065140c0c0c030f51455040c459078440c0035150015140c0c2041541ca4445007000100c408070440710f40e030f0540c20141000f400c2c5501145150300b04010681880b2900201410081e02440c640a0903540042c140010000303e00600101034011742003280c00c0324403d840b00c01040075580c00c9001c401520704c2c0058500200681401500c24050920208091600c00c40864128034071462041241141540c2d01120b0410b0080c00800000e04c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 558528237 1250 558526987 558527069
    0x2190518070512010608040b06030d0f0509030a06144006290a0f050907200a080304150b010c02191e08010e030c1213180b03010b010e0109 61
    0x380d00c05d401008204100e17012078261240c4008240c2c241000182c9403100d5465448004190702265800c96050300b1180c19142e15208442d10400030658603c100c6601d900582c2c0445818900054151000062940001e0901c004801751485c1041d21402000100c0103140c11040500c00e1420000090400318016800051040e0300d07040c034152120821720800142070781d035018802ea48040e40440c10380c07544505500030b56080e0016002602c0b91030650860550400500031703c10451032001c1c83d00c09609401c80b000d1000000344802e002414103a04000100c0f0724003802917014980c0001c2070400d450100a005004912105041482030300c2604054002e8440c807055045220501103581e005c540320b400b81c103510b050782440c28680c001c811210000b014400520580702d031011944c0c1c0b00e81c045c405155010181c064040f0301c12100100552507030741c91b0304010a02050030404c1508681030030a1444c14002d14165084150340c200040c48221000b608010141101e180c0940b090b020ba49070052091071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 558529487 1250 558528237 558528239
    0x507080d0504141603030f0e1c030c05030307080105032109010e03120d0207060f05010b032a0a0512060a120b0408091008041a010528030606080a0219051807051201 72
    0x625424a031308216402a920800f240310100e50503208050070f000d442d0b0300b01c2c2100748503a40b18620b42e5038200c210f40c424030f07100703007a80c4803070b1921030568000f500c0c4040080c41100042100b0315041024541c104010054441da540600a4514592041e01d07095410f0103000341035003c241c5d8040c826803908205100340f942e40d818504071000004c0d03101c403804035505403420640140000da01c4c46150b0503104a0303003603186541c8a020700121840c081e0003401d00d01c0641c43c12108403c200c000040c0c042107105840700f54981105c4116080303078040c007d00d6980199204103040001812004a41140c1ca401c054404033075203072806c11850781e1040c0502990485171082c18980d2855100411510943c001c40030041c12004500e90105080b1082c420386074000c522070009501c5803d4003410809c1400300c40901044542d89a40e2002a07468580c040c481c1500001140030035410705400501381294042c0f4140102d40c100300c00580c2e43c0110007640d5500d40b0140e000504403600500482e691400f100501620707035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 558530737 1250 558529487 558529513
    0x10504241512020705060c0325121a061c0608070f150c020f0f030a05070303020321060a120f0c08010c1d210c04091109070507080d050414 61
    0x101c03040300204000211003082c101d581c2c244601c01c0d549141e034814050031090301c880f10901490342029001c1c9070300030700d200d0341c9410401001d280260594140e441c0d402400c031010000c203040f01e00842021312098008071504025940e8142200e6040b14049060708443c03600e0300000008109a8100b0302d00c40c446c0e24800f0a99640e0f00c0c0402045980400b031032151824070b5001210025554030009420078901e42020b2600d162070340e0044850580581107031100070036a00c80a241003596481900503070000130f0581d00758414410040c11141c0d25541020f464240791010408840b0305c2d2280c000d0799908402e01008102a9883c1614250340040000001c2034031010114020220f0380c900c5004620f0240c40100c40e80300312141c00b41c01680007440303810303240b46a01b03d40e40016a1420b18680314003039040001e450b907480303200c2d101700107020b104541a6041c2072030611440050240c1014244101484018006840359040714100c010125010903a920b803454081103d0748450b2500c00b03103000e40b07800c03c049 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 558531987 1250 558530737 558530759
    0x1024051201110c1e19030302180904030809060115090302040f15030804090c030b132703080a1d1011130b090405060405060a09020f0c2a040501060801050424 69
    0x4404c41406800124007508019555070301d40d081c0a43c043e910000803541c01190280d80902481030380800c240c00039450a800250020908907800c4002c102080140480c80381c0400505025280384a100c503401c0c0c0100c54060415103561000a20030b41c0c84050401c098235907034001c6591051250041402d035902d03846d05044942150045440303061405203916046840781c09240c09245021b4401604202c6590721b05010f0642000c0e0f00c03100903001100501c1d10b0b4080300c0540d503518001c0c1c2d200545801c000b500d56042d03600500d00d545d081c1c0c40006865040b440e01040d460059101000c000400e102e480500031620b01070050042c6982c140c980c0c0002d5807030790355001080201802c4904000a645900411045840136030f812a000715004c1001c0c07001c2e203015401041603e144106c0142012000e10040d07143c10a5846e050580b0720b05400b02110b00a40410080320500084038280002c0d81003100090454405101e00c901c2a6183d01c482451891403a6140c0d44910b60f51611108898a550300c00c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 558533237 1250 558531987 558532003
    0x9010b0a140915130510030e070812030c0c0106030206070f121103090609060d0203040c030b07020102031306110c07290906070f0309080f1024051201110c 68
    0x469080c0d00c0d8104046409801c0710030441d0028483d0200c0c20b04000d014800b0707007040b2419040c41c0e0707140f20007241036a101a6a002d103515581d4003c552440c40400c3e0b941411101d5112481c42c5c1e12100b5404410341a0100f03403079020424104e010348440c09025614090700c12a071010350004c0380003516200f4402c40641c041300c91806054a0000c1011480084401d09007000345a840d5401c24400c0f41c1142c80d00200908021400a02e0349041884800311582240d00507a030031074503503030300d12820030410020b8042e0951000f03490008600710b05e044400580304ea00c4903c40100b000d0b50b81c0748402100c109800941c0d407410302040072200c526807030380980c4100c0c1c20750340c499000716458913a00650030100c10003150b035054005894141400100d980d2100e624543c82001c8042c041c112b000428a0401004445d5200d00b2660088c108042c4061009040343c8250f008064102040c800c0c40c0c6145000d18203c01c02c9800075102100c1c0407240704000b6004040302c1e09148500d000029002092000001d040d20f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 558534487 1250 558533237 558533257
    0x190f0603020d050f0907030b091e0a0501360c090507030b0102010614012a0807060b01090f030b070c1506080f0d0302040e0703050a0209040203010e0f011a040b03090c09010b 76
    0x802d842e1090b065801e41c108a40174071542c1e00c091014000a80400000740c1c200c0c9000d81128403071000e80c0342003038444080d104102c603143d004001020a02c80309004001018281480101440d500410010b40fa590308640b02011190103801035010031506080340340040501041c1041907040c6003000402074201c540c0d03050b0040d801c005022500601d601e1008141c80b270161150b400c03980c0d006102c41c60704540d88103640100e0340c007030b1116030100e42c80c10024001c461180b81d000a0072940c06002402039046a00091014a04140d05200260b603418040d43c0025581c1404440440e0a01d4152800800503400c8250181480c00003e2240700c00624032000140307501c03e46e514901510b000310101d0040d8850040c1102c80c040124420302c3c020751055801c2645900c0c00343c035152850011806a030705c02c3e40a1140508100300304080d0709240032145002d02031a0250080261404c90030724414040c0c0d0041007001c030000804507860000401580c02c2d64074002d8a0f140c043e603074400e016000c82d0401c031030107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 558535737 1250 558534487 558534491
    0xd0b0a09060503031b0717030a03050f1e0604091407210b070f050408031201090c0c080a031a10050a0206130c030809120715020c1c02190f0603020d 65
    0x8100001030380200c0c0e09440014000b142003056176141c201c0c1d410080c1d421103030b1502071540c0100d074030400c402c1480e2864605100450790789190340c100504440300103003800804200c4c18240006005122804003100300440c1c64074800f0f803280c00c006802841e20300c4004109101200c401c2d241401c01042c060107c0d1204402514900400701403851041e03011100105100f2000e0000341d8180c0c0251080d42c01ea01ea41e00d48503041c5611400d40034519031001014031000303c444001000a802c09000d00d5401d02e00034981203464030519541c0412900401211405164032030b080044500308185100510b00300043c9001c820300c82400026003541d10184183d001400f9160005141c02100e4a24a00590b03000203c07540052843d05da60000e50041207945a010407040107074100c5943c20031004020b441001b403094554004104080d14001d88850214095640d88180d40d22002c0b07580d1111108540544070440c5564958081c1c50b8244200c0c0c110840d529941c920100310194142c2c06841f00c0d07100d804d82 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 558536987 1250 558535737 558535739
    0x10602011b030b060f21130b130308160c05030403060b030c090412031d0303090d08090d02190c050307181103010308090103090804051827060a0c0909020d0b0a 70
    0x10490940c3c2040c8406a0820010445115074684800080010001107910092030303107804d40031500504025520940003080c3c2c2003141d41840b012060707080d0811059900d84900204c10795018012200c028040d90000340c6c020f883d8400f0900510703900340c0c0306902109a0341d0740d070388074500100105680745c201c1d4043e2003181e505040c141490045580035030f400c18420325070401d4803801200a8a0240166020a01040b900840d070040c20005140900102da001d007000c2046908024040a002025221103a10900c01340e44026008902c2c0710582a6003c885440a1650709241c8001c013010341c40707180c2503c111480012044031240511444600320b04043c080c4103681c0101e03400b01c1c0028003014008480421561201e50301940c0010800b5118617001402c0ca583c503000200340030190800394003058030000802c10314800c0c454000e050f182c3c0002c80d85007601a402d59031a0b030340d5401440009040e03503030003c4800030340c01000000e00808000b4819540e410320000c604001c0c0400c00c801c1c501070084848 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 558538237 1250 558536987 558537041
    0x30c1c11060405011b03020118080306040f020a120506121c0f09030803060409170a0f18060903031101020c12071104110d15030b0405010e1b0a050d0302031201060201 73
    0x42200e04440c0c059485406003c84a02c444003085d1700850100c081d50350b02e0000c031140341410114018003902aa02040c0c0301d123409428030055600070b502c9444078a104003e10404137411540022810044500014056072030a005c03d00c540020724040141e03101e805403c00242e07040058008600182c0d69480c17042d6a2885410b0780c00c0c1180b804010054403042c0001522170030150710180700dc034020b08000134880311500144040380c5c0510045000035042d030b401c201d103a6400c00d00c4024201d01c0c41f00c1d0100a1480d21000609000b080d000023010052130310680e55801c6400d4040c6d403040b00b410004d80c1c81c00e0ba449082000c441e031004004480c03400c01103962010301d00c2d282c40b4081c0d01c0705180189610380000d038030309000145100702502015a803e05c1c40800801c507ca100395104500c241d000248640c0208101441e048201c520800d0b40100081c084415807120b400d14000c444060362420384010951505a086018445a002000c2480c4000144060b815048810741c1000c0c90703071001000318554 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 558539487 1250 558538237 558538249
    0xf030310080c0105030a0e01020919060e011d0103020307020f0102220504020a08010e090a0b040c03020109050d05030f07111801052404150926060c03090c0906030c1c11 74
    0x403440d40420000d01c001496246903401894442000b0000107192034180c0000485021380180208444552f042090000320f400100300e0100001c24280348050f4140c0d1814006000c6030300d10032504054001c00806e05a034000c101040b00090070400075515100359480900022042d299541b4241e0341c00d101c0000c09082074403c403680305801c0e0f6200d080c47c0c0e082c4002c4001088001c1d2940244c0d101c1d05904801041c6e0a400c030f140114410355440608034030754000184002c41680007544a01c1c980812040000c2000080b240c89200000c106611a2854104080280d5075a65030642003d040911001d48030803520700da50590720225403500c4002c010014500000501c004d45690244081106004250240ca601c428411007450309000c0385450b041420751800080c1002d2003c0080962a040c1d503000c240050355028040e400440d00310f00e40340c0e00c625a50032000e0b0b0114061203030040404e165480900140d5006040a032110103910f003104000ca008040d07006080d50303810200070000109181031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 558540737 1250 558539487 558539503
    0x50604060509070806090402031204030302010b100e060406081302060a0804120f020a080f0714030d060806160804060e010e0c010210060b0714010f050c04051804031b0609050f03031008 81
    0x184e51080c1c410380d00c080601410101c05003061345d25105511654030203800000080016510980c00400c0d494012000d010640f01a8a906028040703043e0311021f0b43e845410a903011110603240c51950790b102d99010100c028101c0c2000f81d0071002c0000c46545041c0c000942d54041d5100d0300468010b60071404080350481e07084108103006810541a0402040e520740140610a60341080c0c1c626056196131001c0f0701e141500300c003c62a030400700703280030b2001041c820b0310300030310551010f03044a15041051200b0340304240c4c0c48c0c0c014007a0140c046070500000fa0301900844540724020030142e820940410350b91041000300d2401480707440c00350a5903810700c0c02254115500c1c449411305065003070b0b07280b103800940300c0d14040c010f6584044030506000b0314020240580560303072950395590700701814002000c070812140d00301710111034180000240e0141e40301c00705c1820040380354072107200c86c90300030003500c10310501030a54404c0c9034002009141c040011030240204007001a517159841d500142c80307541d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 558541987 1250 558540737 558540751
    0x903020a090e0c0603040b01031b1413090c030c091d030d0c1209030c02090903160204150b0d142212090e070f0e030f1207030e13050604060509 63
    0x380c4010040c149168101e0321007070100c80251085106084049034482d0412a07040d00c400308424010000c0c001005281e00c445500401301c4009182020103031a105140078111600851607090441d200300020340c03000c4e52540e8441044402240d0340c0c00e215605107a0350240f406001e140c190070002028002e9559003490036080081c5041c400d540c54400000d100f0520100203000c101c0f0340d0035010390741d14820750100b18030903140d00e480310245005002d484040241501c2c0c46a108118208014000b2201e04500030342c104d03008104070044c0032035010380f02c50a6002000104010070b000701803000b103401100c000034030100032090550702c200c00742c00c10400c03806200d50700307410824440c1c000c101e0a46003184054018203148a05681c2c42e0040840c0700000c0f2800d00001d040c1485035910550300403503554000c0c408800400303c00e800d01d00a43d0311880700c0c0502c56220080090f00c00100750181288030901d00d03005051154030070003502400080c02080b641c03680f0440c030305800401d46d49000791082e4000d00c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 558543237 1250 558541987 558541999
    0x51b0c090123130e0709020d050f040b0f0c0f0d060503010b0307030209010915050616030201050f09030d1a09041b060810090c091e08060c0702011413050a1d0601090302 74
    0xc10188070688401c1441020f800d80c130b480070504c90308070820043c0018a0405001a551680740d4420f10450380054070701d09910700108207001c00700b6000510705800120140440d0aa80c0b07900c0304104807481070000c051040b202c0494481d2203000740713a00880480f10298000d2120401e00020103440300700754000258000c0342200107100308042c2ea8003422200f5180e110600c44e44d901e031400034100c0e03001002d4040524841480c0c05082640c21302542d07801c000529284040d50a0140603552139014240c01e460304a5650305000d03d82c3e402a040e204007031070018000201e203003001d040290040041810035084400343c00b01c0058424410b0421522403041a483e4007202401c112040000d041e0394048901000040d1102250034400c0030060940d410381d0749a07401810b0f141c4110305041820052800112040901922002d40d80012044e40b48101c40c061155564410055001403400c26420158024804c228007040e4200310749407401019808115100d00c2e03503101c1004442c450118003000790881 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 558544487 1250 558543237 558543299
    0x70504050c040b030a0b040203042d050304120305070b01060224010b0a0c1b0605090f030303150415170115090e0c060a0203070b091b0d08070b07051b0c0901 69
    0x140c030750800b131034101200c4000440c0b8088410000350581c1c0090360305444100c2d0940c400b190300059895500f0002c40001d46441441e800358550742c1d224015407242d9800704400031000010036104400700d0380802e9102c0d19404855031640710081d81c42941070b640e0780c18001c04030100303030008001c0c0900904854589071803900d13040f0415003c807101009a981107800740d090600c078030000050f8101c41c074080c1c0460f40d2460f840d24955000c0041802c96481980d0003078108105000308060844c030b051000c81c0083d9004910248180d60154900865a1213207003449142074440c0441201074001c21810345142d801142d18940750a007050417190200a4100e20303502081c0c10105505202000e400854018010349007003448a0300c80880b886011a20030320180c00c182e034032260755052b8020000500308150703210301ca11840c507a1001c29030b115450010700742c600d420700012113613846002241c0034052246800844040c40112091350780c3e2020340201d00c00d070a03500c00800c60a881580410311003440d10700103a00e074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 558545737 1250 558544487 558544499
    0x40e01050f0603190c050f0a090e0d03180c0e0414070b03190b0d0210030209060c01090515010f03240e0c010f020c010c0312020910020f062203122903070504050c04 72
    0x44142c44100c0c03504106460000034000400342b040310b40705120f50002c1c3c450441036120041c00c840c02d0b80303000030217614001280c4010401200c881c0050740d221804055494a85083c04070419840c0c2c900203c85100303046010401360f0400000d50301451290b92001c070020000b8103d0410344500400d0b441c0c00c40d150138610320152034148890300d9000e8040c14010b2901000001160231a03200802844180e9100c2e407034603042150402036010700c4000c184003076074103504000509a20050340e11016042c10050f0001e502c000342c01c118044c6d10030074000002c00003000c40c041069220710304100981d0118605c2c03101d0340030603400403c142d6448007050396618000c0c803850350152a02004003966406045d802d00001c074090301d4442e00344079024026001080321410003a1000e00d401c00c01003060811502c00e007401c455544000c011088110b5140c10420002082152200c0090007400044030031040c0c6001d00c070000f14041c502510791600e090301621422619007050005441d4107031948114803030100010070035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 558546987 1250 558545737 558545749
    0x16050705210403031b1205090f190f080c0d020123040608090d0f0206160c02030a0b19022805130f060f022406030a12200c100509040e01050f0603190c05 67
    0x401d83d0000c00561101c1c2e0700c100480c44902030004050b0ad603d010a200380148941c2c1c172816070003084904002c00300c80c00c402e000308a0140d80300300028144100c4044490100480700080b0951103084042245c8a580d540303c014402d100940342180e481c002c03003003000e03100361151030100c403940626001000e09440f03036158001c41940e06010340e020021391308040d00040e5804d1180c58031442c00313006801c026050036400c2c10142040c03011041e198510422501d40340401b903141550042c8a0a4621106207000207003c0e1460300c17078200d030000603440504010880703138404031180041e200c4035a00d02e25003205248041c0da0360380540305035000d080081a014680300f50100720080c1c0c0400042c080da100c14040e03648030344112034000341d00b00106000186402c003a02a81c4c615400030302010000305802e4155901140e002e025801c9100204200041c128145440c1d0b03420002241388003200030882c0307140c0300003c95600a400d40340c0910034001d0b030320344500e4200c800c0c03d22144a500207111b0603c0320f00d00380030044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 558548237 1250 558546987 558546997
    0x1b28050a1502041206020304050c0a060806011d0924011704080a110303150414060d0b10080304060e0a050105030408030c09040b0a08160e16050705210403031b1205 72
    0x51070756000c002c04200d0030089446030303002d103108050250700ca041130300e400380c14400e504c0049406107144140410541d41e00001c0784c5d030008404e090052150801701cad0381005401210007002d030048510f000f480882001c3d18150f01c00402c01d1800d90100d051510011618200d00e01e030b5880d640c0c00740c140440c0c00720704140004c2078440385900306840304140b03100d8028219041180d00e03201c0460400380203412418103014403100054002c0048200345001000560280362500014103405002c00000b4065001c034512903015009000c1102d403616640c000c000c060382e0603095803e014540030b010028155008105482c0944d0b4891f10b924155079070b14000321007030741018000315031040d200c0041802c240c9400000c50301604011000e8112070140b40d2111581ca1456407204080220f28010800c00e24143c0c2d26841c503150f03051a14a90f50901c50500902d01224001c2c1c0038140640d600c000a00c00000740010310469110b80ca41506543d480407500310344542000016108a44142040506a00c214002d103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 558549487 1250 558548237 558548273
    0x50a03140f0d092106241505190e0306013f0807080f03010b0d1415040903050d06060905010207090e0c010c0213110d0e010204051806061b28050a 64
    0x4c010909541c0710799007a80c0140360b0500112243c000c414410a07212039000000c0c000740203102451003885507009020340304d070744c0003540083c001c0c06841c00241e20a95102404403c01000c40c0c1d1156100c0294039078031004a40e07101c055910021610310f66542102c1d4880f1044c11503149200501100e40f00d03580c2c240d006901c1214001c608004c002b0803410325a002d07502038402c440030191240f100c1180c0600300c2d406c40200b440a00900e03400c01040c51464048074451200a540214140c8400d1501380c445000d04800705040900b0300f04042499580b1454071000c8640036402c54621903a02c5100c1307011900d00701c8001c0e10507048402e110b1a00e501071880d80398034500c080d100d0041030100b1a00d102c22101c00a06d518a01400040e1045805270140100380c01048040c1c0218540b502d070000261900f482080b0f4403a5210f510700015043c0e643d900e0655205820040c2041100c0340750b0703070009880702c400b08040c81a100a4103051082400b2681d168030b0f016078400f004000101c060340303605200d490098429 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 558550737 1250 558549487 558549539
    0x5091602030f07030c1703060d080a0507021302030601030612080703030c05040b0c070e0c0c0c09040f1a0415090b06041116030323060303030109090606050a03140f0d09 74
    0xe242220b0b6040010903005001c1d40d14001d40100a150880c0101c2d1030b40f5600b104070700180280f0990342d0315494072041c0194055411980c1d890402819107007030040303c4000e90311064000282100c045640c00441c82107a00742c2c0d08000c09a150329800c41026010140900710450030300c0414002030181d07108011040c45414590b09240e6612001402640420010042a004a4000c1140028260902d43c106050808440c18881c5084525949909092005d842902c03404085000d0044060819207816005824005400d1400c0d89010203100107440031200c0d80c580414006000f07600c0e104010243e41d20081040042d00c500c000c010280c02124200c0c0740c080c108004201c0b0f8041c82510704001f06100e600e000c03c18502400c1c100c00c0c2c50502c900c3d031002c0301c1d065104000540e074003c01240d040d584280e200080310403580c1020002012585c0060341c000030408804014800f000c1c0516201d2010349003103070601043c2c06086519040c450203c1d001107000590103202c88111600f20401d401e210b00d0301 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 558551987 1250 558550737 558550747
    0x31911010b12010c0201061a0a05031b0c07061e0807030b15040617390405030a060608010c030c02190212011a030d030b15090607020405010b0309070503070509160203 73
    0x141d2401d08045400e02c4507903607800c01d040140d8080c06180018990300101e140080d111032414019071003150021001c00c100000000c900040a0496041c0900d5031204580c44181541c075813030340c5075454051030010a00749004101d0b525400440c41200d0002640d0740c070503e4451a1040e8040c140c00c0036265441005c80c0340341c82da54264000900002c01080c1e0740c01c0d40102041c031003407410040160000c20083c01801405e0301212406070040d41907017540c0929120300302140003030300c2280215000540d240c010038100d0410301c1010380020040c0e0341c1c0c000080180040c2c800d01902121424000d50005d41c000440c0361a011039020745c1001410300141550b41d031300c0d10f500c41c1e0301d00f1034906090840b00f01c20030011000b2282800c00401000c407219050030480f45808100090b0071000d2842402d019040000d01000c0700c4c0c8510094814080d80074106100558403002030000d0741d00101d074040454400c9000c0017403280781c0041c10504032400608006055110611281170380c0c102c0c03a6100007544030400c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 558553237 1250 558551987 558551989
    0x102040b070836270106200d080601031d0d050328060e0601090303140901030e01020304061a040207080d0b030f0d020c030607031e0c350603031911010b 67
    0x142082511580e2801c02809404020411110300e00503084c1c0d00d03051045104004800b07030362036821415a1001d0404000d0f0020a0061461000705801110480c4c01045030307c080b00c0e80c00c00d90b034030301030301c000d032800c2c040e0f58152501c1d081c16500d921690360844d0b104660300b4240314091401940c20144550024556012144d03004d020010891610524030380d84090802c0b52000c598a815084032003444c0c10f00780e462030b503180127218140405221030700c203600040c00c590583c043d07031024096600304002507440c3d00d064140310000300882580b00741c404a8040b4a41e07420b180620845140d030354040011400c040640249070005d011818000b50544038140c5500d000d400c04004413450421141e000740a41016002850304203400588681d00313250805046442c0042e15811040c0d0712448084001512088404101d601000e0290000c00c84000d5410103481c540740403801205400e036000914400351684070600d03a070b03480b655591340c0941d0140075540d03144038410401200c107202d000e0001f140d640d002030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 558554487 1250 558553237 558553297
    0x1c0b0606040f0e0a0606050913180f1208060102030406020d05030c072f04090b1609030602030c0406170126070302040f02090f010309020f100315080a140102040b0708 73
    0x60400c00501020f0310800c601d904883c00303910007400040c07074551b04045228010888001000b8010000785480d0726520f0400f010b50844240002c0c1c000200c42c884035540d0803ca2034455180711000d0005850200017481c85d400003003164103c035802e90003000b100c0308140c011503558202500304182904100003507401300c0c40d84040000c0540c0c0303000e20210451841c00c48280d0401c0c04040503030181e030030680f044c0c010a0b1411160340c0d1000d40740541c00d0441158000403035140540c0c0d080205140e10103c144410280108060410b03503101e621141821102d007907041c0d903081c0e02442001100c405a000740b41032020f6200707030003011004420449061039203d034005401d660b40b46000c00440c2c1e5012940c40c80d540b40500da00c202e40802030a0070000ba6802d82c0200b6241e010a0010b28011502480382880c210710961041c031000300c00f0400700c0030481d103a150321511940d4502c1c050f10746d100702d440c00120392141032080310300f02c40d03031144141d280c4041991054030503084541d043c02074909104504401018130 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 558555737 1250 558554487 558554489
    0x70801091a030f030405091003050c1c0f0b150406080606040c020a0f2d03082403151f0b0409090f0807240e0606120106050d0305030f061c0b0606040f 66
    0x64405192900d0910090000c3c460008200780c54003540d541c809c01c08034201060b55042002c0542d405601085e00403500c000c0c4581011005104260722800601842001d100880c0140904440451411003030b40c100030680d0003c3c01a218150040c00101355540f0341341d806a1040c107414016510780d0451038442c104090149841910b01d0350400c030018052400d004081c03103140c1c03000b051600d070442080d20000c058041c000c00f550714654108603510390541180d1011020018000c0880301b100f8450354100076551410790b4080c140c200c0710206429811080b84190341610f030f44840150900385070040703040280001d01419200d21014113f4103022444407801082580d001c4c521703000000d407090b240700c90300103036035034448002614003e110718000ca00850221b40160702100d10441d01042841024014075680e40311590017401c40d2501010035805c0800756104880c2c3e04940b10442da03030702050141c41d0307404500d1102041e500c4040d450024403400c0e00182c000c01c001c0c00e00f03424035480e0b200c1c040c0c443c036203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 558556987 1250 558555737 558555763
    0x804141909020c241906120f051903020a2603010e04020f0102010c0c02040b03030c06070c03020f06150d140717120a050304020603130807031d0306070801091a03 71
    0x1c045642034020481c0c0c1c3c02001d1007104c00b020400d480ca0158507010005410801803a0b40c07884803c00134406504114003074429030000201c008a585401b407000d4401c010115076902810840100c651015218010341d240c041c2c014148124103503685104900c024200d2106001c0c0d9100300d034010030b401d000a18040c0c0302c2422540841e04183c01004156010100b441d411607040024082c82c884e803040d400340d002c0e43e0580b4041f8500303581da0700183c194020f0301104001449607400b0483c1c925444030b02c0a0060f4002d4003030318201c03c2d8100519464160485680c101c402413606003000a0800340410385403940aa5181038003018500021402c100c4550710020310905609040c20050000340403001c0444052002540f4201d5102805042804000c201a11841003c00001d242c02c81ca13101c114001c650010680d5030f600701318030f0003a000d003003460b038203e50505040d10160051b00b800a0454000c080ca82c076800526031a10010001030800000b031880b22112000c0521038684017044203a0803040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 558558237 1250 558556987 558556991
    0x3071701030f031229040b1309260a0c0609050d02030406200618030d020d060e06090601020c2419172505090909060a050109090804141909 61
    0x181d400c0c0202032190000039840d6aa25041c0d0705e2a5036400c0111044144a01c030030340ca85202c4190b0006402070060000f1590440f50401c0641840c900b10361094040310300c110396102407035218000071000e03101d6040910204601c01c1080c00780c0310740625110300d01640700d5140855000626034400f401c00c0341c56445100584d00114041c0a5150881c00740241d6800c01010300b0360380071401200550b1220050301201090b00081542c114030340302401111a1060010025951030400b80070910040401e4403072044182c4141000c500e9518280114500512050f4000c0003941e4000040103da44035038110003541c1c3c01010008200502d507240a005030f2032208507400a503c001d042c000e45440e981d035950f05c00c0740d01c0310010042040c40001c103084c2540c0700c40c0991030080c41c0c0c283d020340303480c4558002386038095014020449600000100e052144030301080038013a590381e6074140310540380f501100520200080c00148030070001c1141d40390340401c0050a80c2203c0e00c6000d80da100361201c680143c00015 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 558559487 1250 558558237 558558263
    0x50103050a02070c1a040f0e06100906020d0e2202070605010609060206070f0909022a06010b09061309090503040807060f1d04060f0f05090c04030203030f0307170103 73
    0x5a018800d40d40e000085030819031500d14503556190a6400c83d010705155580e070307080640c0d01e107508a400d58001e41942440c400701662501c0005991036070403148180300d00328140ca6881098800c139441022035245030000c02c0c40c0e4151003015252681029000c6420502211540e10030041c0d030403400c011503109031001a0b44441505103101901c405801070070500c41080020000b65500040f0240d1125841c80c1070f0250462038081106c0251255007c01d130310314004610b40d50035201080d201c1030501100042c5030303580440491216207440b8241310b408503e001c00c0c800380c401801e080004098801e1261044045a9181d8000004540081a0035103c9504c01f040038040c28030104030b0340002d00b60a00b44950368822001009005c400c0c0200703001e5803a403801d070b0003820f16100d07070b008500070300010724441074100e03126030b805001c0b080c1c5803098a20405844010031080d4010504a034180d980150240d45009441d958a50071680007030082820400406105034111a0b42c00b00c1d0740c041d40c0f007004909581 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 558560737 1250 558559487 558559489
    0xa1e030e040c021f022208190c0510170a050c180d05030a17090102030412030222060f020115030f14030f07060903030e0c131805150f010f1a0304060608150105 70
    0x920b076402d01400580c01096400d1190440014a080029100e042c03002c940e843c05140402015120354029038008400d1121841160333084032401c691a244d59480b0a003541c1c2e218101c40980f002a90620041203080007501c0003041d14001c05a03102c1405014412442803c0c1d4541c2d240d584400704440c0010b07400c0c10324104480c20241c00f90b0b005a5410029410b5013420303110b40d15480e1194440c0d1041c1070f0b00003041c06125902c000310141d05000f128410400e281d0342e075070140280034901101c2c0015482e01000c5030030918000e0070701043e41e030003e103440428000b075580d440c0860700c2003142d9249880107001080000030703210000e04a0500c02c0c840850709020341e207800b50958120f0419010f80ba04201ea0508179622103c07202d141040030b2500c04580c10b15400c2c3c0f012a44507130306070050854000c140320701815003608540c803409070340e007110b0740710203a83e940c42e4400c0161654040c004500f4078240742d40c0c0c00e101c40c00000d960403a00411000a81660343d074645443c03c0c60501f0800003a0b0020001000b031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 558561987 1250 558560737 558560767
    0x7140c0a06050a08062103070302010b1c0c0302090c040b16060b0109060509130b060720030f10020c01021606090201140408030d020d0212090a1e030e040c021f02 71
    0x105040e00b42642000403038203000e0704110000300100e000b04149401c0c294220304141c1da20303000d0300806007526036801c2da9090080c040e260004c219070285207426180c44d2111213444c0c40001b1703c1c0d044000840714504580c2004103940c405005441502e000740000718103410000010804100c0b10740120b440c13500075142c42d106403085982c406040c03054152080041c140c2100c12903a098400316040400c2d203d0880010300100341c40f04901da0400c0e00840c00c81c08202024075008107183c0b80e030001a0322024a08109550f8540c011700c1c030511a000700040c94441000740c1c000e00b19240c80c1c240050f0410502c1e841c564280d0344003002c284c807182d88605c250000d6503006089298070000c2103452901c3d281c10030848035034a04c1440c1940b5400f980c00200b01c0e11f4083c95905840c440f0046c80e20281c840e08081000581d52510000306948584842c81181036060b00c11480860300c0e85d02d07440d02c4481026280402c4014144032142030150f0080004580340134441c001b1540d010712050a0050312002d244411201c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 558563237 1250 558561987 558561989
    0x80709050a021813090804090f060803283f050103171e0c010207120c050c01030c050d0c020d12110301030204020f0c060f0a180308010b0c0307140c0a 66
    0x50356510410003150303c401035204200300d89000b9141c01c04041e0003c0c40f07032401040e00b07007005840d078000481e01043c1e030324007a00003d20160748400244015502da807200d41d124851140741c00034042400708840210301200d40002000380300ca051018600c030700c0200340c050308801022805440045c0d101004001004030800118174413524030104015815940c071040743d440000d403000d040013000300301c80a030b54418030b21010040044c480d84070707200d960703010b03202e4083e40082d00101c03107418200e00c640511074030030040c40035000c0c0c2000080c25413100000064000300221140340d01008070412914564141c5802031041100c004d03801090a182075820042c001341b041500c2c211940d06011984022018203001e0743e0660b1f4040382d0043e0348000c0801d079003880b8401d8694000050058104100b10302c0d01100d1090310407481d0250034000c0202d010002c00c0d00d201000d00040101e0090304c010300120070704d90b001d0074002402204032860501140c0705c05200720703450301d2000d041c2c0e4000f4103003c10600300079100b50 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 558564487 1250 558563237 558563251
    0x402210706031e1a04050a1e0603031103070f020405103203030a02060a0506010302040f080a05070b0c0604150b0409060501241b0203211e0412060f0f0608070905 71
    0x2000c1c4400c07100d910091509003050034031454464000c0f80c03030080c26601140203501110051220b104c501d44038a4050502782c80150089800c1c0100221840000300840351210f5020410524a80b203650801c001403202402600120703003c0b100204582c0f40c0ea0a0030001281026120f052407042c0740c543c030b41801142446507020303400500c840009035070002205a00054501d83c080780f59520700004034002e01455100901c1c8410b04480098a031710b022070821551405038060f65403050302e4170b2000030030348070302c0140e14640c0e48400c00044c0402c032128090700c46000000c81c00702e51403c0724400101900d1400d50250780243d5102c004001c240003020030802d4003010615506000b401030b10010300402c1c191052900d6610010050904554003031001c800340410f07201d00044030f80300d003d4104d941504a09001451074801940c02068204004103840c11a045d80c6088200d861141d501c46010f02240d9038105900750301e03115956144070300c9000307240c040c0c0128002001c003e46800000c00030349102810b00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 558565737 1250 558564487 558564491
    0x16060f0504060b030d032904180c0e0702030a0c032f030918100e10050612010819050601230306090a02010f090e0f04050a06111306030e060402210706031e 68
    0x111f80c0c0017241c0945002140d080c01454000b03028004049005061200f0030400b00d40210315203074080090356442102030f502c00403813a06c1c0e269140034084c2e03600d10440b41c8083c00300d02c1411038140028401c5400c180c0d0380c1c408014542880c1c41c1d00000903841001082c000e0183c1c1c0010545614030700704800c1134100c20703c001c0c2c00c00d1000e09240c8440314090314980115403441818100140340d0070405410f12009040c0500700d40d030744103c181c00c10901108280034004580c003850340701004082c0c4c13050140b40410f8000c0040c0034564640500c0142054070500b13400f200c4283d03c2d800e4000c540d170910000303200c1c1560300d01615104400e0302c0014202c80b812000c1800b800b1030104140b05903000381d5000795005048140004007500c840c20032a01d80700b089400105000c0c00c01094012400031500500540d0080801a000c107940310351080d4103480c01c130b00400604d9840070740014007528145014031100340e610303406001040100000c039400c020464101502003030300c401d5600300034044501e901e03e1030040e0403c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 558566987 1250 558565737 558565751
    0xb031b01030e1504060c050f0a120b09040b0a0b0307080f0601080d0c0c0902090607230d0908031c020708030405010203060939190804020901081216060f0504060b030d03 74
    0x36003424204081c0005e40125a0381e124020490701450845607511341104003180c4400780040700418141d1214142241c4c40d0400c48040d429042c600c410500541e40800c2130541ca83d9045213041c001c0c03001d0000300b036040c82101d000003101c1100303101005444041c44043c1c4040d60500303192510700039140c801c40c0200445d460360703100032580703100c00c910035200140005640d0340d842a000030458000d07064044c1c0794482c0300250460b98421403085840d41006441980c00e1070150b401c3c1039036507010a00c9425041d0f0000c2004419003c0941150145421a124018100903840d1103005031608115012102c82e94000140007071440e203c00025400101d4a4154401d070040542054500d00750f042c4c00d52034200301070240841202d01405680c29440c0014002d01d0301c84001800411004066500b80d0052103031100120390000e0214095105c0c07a0003010240c5000709051310780134608000c02c41516140e03035651200818115501505010320300136100450030300300e604205400d00c161b0070000c0b000d0501d003040c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 558568237 1250 558566987 558567013
    0x50109050c041208070615150815060421050105040309080c031207031b05120d23070c06060806131a040507050d050c1017010608040201140d0b031b01030e 68
    0x141c1220f100f64041d101e2601c0300d00d03a00c0e1038809040b2086132803030034101c41c05011a0f04100c000324038046525644e1542d9280d140c01e074a002281c018001519000740c0200011300101f43c24112022107032103004000c50b544109922210308485080c2c0341100062100c40d010005500200010440808100c020300345c01a817030360900c0964411042c004040c40b2061820f20242c4048201c901000c6800c44182c50050302c1d000841c02c520f901902c00301c66503d24201c621b8014020280340082c00700b4440f189019552282001541d656410000c1201c002d80c03500000700b9001400c1c230020f40905a4004c040a03070251501c2c2460101c003d01055603103410610081002058002451004a45090b01d01051901c02c0e0f0a003141000c1a042e503694208628001d00041941d1001101c049070924051a40c0036076200d00049841032400e96010b0b00003000720000003440301078100107110044c0d015000140303811041c000300e410507034002041c0e121020315440c00159035030103005151101c480c030006828102e003101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 558569487 1250 558568237 558568259
    0x6080709060e031609060f0e060607080c1f0b0112091a1812130806070203030604020a0507201002070b0301170309190503070e0403020a0303200706050109050c04 71
    0x44070740e1040215002e014071840d1014002201514401e00410303c0c180d0b101c003108406000360f803140501690b40350b400040c1030000803581600039030004202e07038030b0260706443d111070070781084c420b4640e98000d5011361440c05000c400042c003112000358010400901140025001840810311020928100820b00001601300c0c03000070181c80d007203008035a4035100c0c0105000a203c407005008514800c1501030604808450090300380b004505148815043d11280402d4840501741c46000142c1c0c02480855803034500750700030f00401c040900d041420204940c83e1340e803141d5181e0700b245121031102d0b9800e400605124a44103035441880c00288a41450500320280383c1c40148210606c640e4410038004414609004946d403a200c01440455080710f140c84031117403480c580c8a03941c030070722a070b404c0081d2529165010610640e01030b000303081182c903e928180c000d041c404000c00b500024031200080e041c591100035010850007208009155810001001d0072540d010b840783c0010101480100000c040d51 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 558570737 1250 558569487 558569489
    0x40f030c0309090e0c0a050102030703020703080f090402040b0c0f0c100e0a030c0b0409290904020f04050108010c0e03010b0a0b0f040f062c0609040e1207081306080709 74
    0x52400d901005803504040300c0d1038a190700aa0701080c200110b0104c0071100003070780c40110300100c440c0454181d88400580c0d0b40c1c0324440008000da00320302010000b20b1032240c040c4c1409280e00c3c208518203c1c2420004080b68015080010b4003030b40130500c941200c004010314807111202c00000c04c8a900703041e0002c0d496140c030300e441c0410840c10b0088015280c13541100b080c015684200ca03403c902c7d49840000c005034100303000701704072180345c803205d4a010404100c506280100307401c0305100b8000c1103000d02001980041090b60080d0540501c0c0500d030721144122802444071200005814900c400014140701c02800c0c2548680e040c144010000e40d18007031003004580d180d00c0c21035521b00300000c800206000d82d9000500c03901802e0782c0024550342007a802000788482c1c40305000e4181d0907800c0c02140080e540003907500414217120711015400c141c0d00c0038121380100310880d03609141007590240e0aa00021084890200c0820000e246400c400101c5024098508242c4014605180024890241 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 558571987 1250 558570737 558570743
    0x16050306060f01051c050403111c0e030f060f0a0f02040b090904021f020604621305060301080d0807030b1009060f05090102070312020712060e1203040f 67
    0x1e034100c409241d80c09081201c618801d440a042c2c610140c420f80d0f85c1c01820304a070243d0114a03051121324100740c022903503000c080c0c40c5a9101c00e001e8410481141c080e841a0449a014131a502d8400c82c1203074104a00392060390005403458191425080090907141410701007084030740180400e0110707504140079a1031501040d5214030031a41c50780009504c1ca2840c0500c0c3d540800e0801d00c07410203560102e000352142d03008503e00d1310101060644e1900d00e501641c000468015000c4441e0345c21190114107400020816544580300d80c450049100001e1501d410507a2242c40000d03c1140031513042101e500a080440e202e80c1158503200807241c4036800c0071326000c00c010700383c0c00040c1c0c8180282d0210850100151006400b0b080c901c4018292031198050500840c24201031071045c24032034011203221142c182e02400e107440c9941d5811800015032a8a042540240c01c80801c03060040c0030041e070700500450021401c080701035406c9040803100420010365800030000c000210fa01059034001a0f64 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 558573237 1250 558571987 558571999
    0x5060703450c030501091208060906010c02040f020c0304091a0d0305031f080d090923090106380711090a0b060c210a1710081e1605030606 61
    0x4240c00e424541e038090210018140310b00c80e480801400015440302c00007174031914040644261204080e1140c8004480096001c00d00200042855205001940d039003480500081450405a030082081c0d800c98051a1034960007c54200300590007405a9240802524200340e010b04050001c200c070800002030141c05c1c440c0c000049051244c10b010700c0210030050f11202030b0700c95250030b003c0b522007012a0280b8001403103800f01044021061081d4203e107180650070110510080c8030007880c6070b0b4014500440d45d544c0700c02c005800d07040d48440a6840f041d0306190054040b90304001d0902090518602c0c800503810b01ca00d40014030258166844014104c450301c006503201344904c2c01070840c0d21100b907008a000705036034568110001f034801103c2c06850b840c0051400d9100d8810b40e50191a0741400050803903200ea9546400d041403240c1c000c8032095950038465100e1401134170300003650540700700150307000070301082d00c507004e00101c8a843d00350701c8a05101464800001d076560f1000d003080384155 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 558574487 1250 558573237 558573341
    0x1803030336060f070c05060103030819110d0b010302041211030d0f140d09020a030303230c07030807180b130e040507030303020f040302090108010c140c03030a1a0d05060703 76
    0xa40940c02c0c005d45d00368003070701f124141d45c2c59140c0245132590640b001000800744000c4800382c0b03041c1d80500901100300b0301d03500d82060141000131019014560f40507050542c00c000208400c02c008006c1c4920f64095060081d140d42074030706052078411081c1e00e05c001c12840414424003140d116400741900030003d58000d840c0c1081081c600001d0040c060f000f54003600d01040001010b03056000094581031941c50300c034803488078070090000c0d1282202c0034414940d042010b100000c0c012502d0070f801080928200001d55081c03401e1403040307442a00010440040841d10100e0608003140310340141c0b002d03000c00d00c0c841c2402d40d01e00b5a6000540002414542c020a420724034440ea041504c0040d90011300760101365956921041c001c24448920b00002080841c4260350b0000304011140040001c40082d4603513a102e80c3d00b013009128505200607001c80c0300b040f80043d036031240c04038150180200d014150358280303030501500303d500442c06940082c038249400401c101c2c005105070242100744600301685 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 558575737 1250 558574487 558574501
    0x915100b13091416140d02070c0b03040516050a06050304021203090a090e06100e040b2211010806012c0d050a03020a0302100b090703021803030336060f 67
    0x21074160381003100c045160400003000c071030301206500c0c024a18482054889a0b0b01802129900e2081a6000e00b13018100b1140c4604911303036000b4540c0501a8603104107243e1600001c6910343d01c1524283c410303a0058005880300000c8070501801410f084440ca00c6081c46c101025204d80030041c0060311450358605491190351041c000c480da0384000034803070202140c950641c00e0007040c013800d82623920711812000614410b15811001c003515405004444c0e0b55446035210f0b4801e0074001e224000411003299040c400c21054440c00b6001d074445c4135942031030420a400148100d10080501e4100418101254500011460608002c58298010781c12001d00003000c00c403030020711040148030384201481c920a059021403054003072031203039003a180c07002000380740942a240b09042e00f030f038020000000b04041500035801407149200d1003ea001d401020800002c1c1903410441c0d440400d0801242900300d44d00c150342c10785640010050050641c001003444039551042d000f070482004480320000308000e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 558576987 1250 558575737 558575767
    0x6090f0a0f0b0a0b1b070e160201020403061406030d020d1e0201090507080a0c060306030305040b09010e0d122a020d030c0602030c0a110d0c060506060d0608060915100b 74
    0x60200140114a6265030340300c03d25020740c00342510700c000f0405d01110154040011842c0c0b0701f141c503030914041058a6043c1286403412001580109640d82000000009a081e0003071508522000c56409050319120f4145810b090025000d941150000f2001c41c0c032175030b0072a10708001810486c4c000a100084440140e005054040000d8100e125a6070f0000e9041d2001808485880c03040c43c0c12940301d075a175442a01074441d1400300801241050100b070010614000203800d80c610b051518040c4001d03c1ea0101c0c0500302c0c00007041e2a0005404140541a50008040d0303101d03090905084121000c282d01e00c40e0155a2484024450360b41040e035001403500c0b800c0e0405a082d0010821503503800d016480329900c1d40604028004980c00310401070030360001280750500c4982d191101a40d02c4441e65405008020040c156130317100b181400f0b214501505841000e01034411f00e0018525420042d032940d20b45540c5a2000d00341050200401019034050300ba440200c2d22444070040d200c1c4030640600c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 558578237 1250 558576987 558577001
    0x1020307141318050603010b010f020601120606150f090b04050f06090f0303031305070b030420190602070f0e06100c051207120f053f010b070b06090f0a0f 68
    0x1201c9000f40316002420381065010314082e210440080100c7c0c442040159040500340f030030303400560412401044547c010840c83d20086101c0e1600151803030b2108010180100c2c0050182d0000341e450034201d440c02d80140e240070217000b801d03905c3c50a141c900400146c202d0b261740e0110b805a9804a41221350b030722003407015118040018282c0f1340b02d1a04031038142c2850700c0001d0654041c4900000001c240e08400e0459020f07507000242c000b0703040758102050303104001086d080c2d40c0054071001c1048054800300700c910040d0a0329405408072600e0100594140406608001550703104c2c40d081c8035480d69040720318481e02d0800d0030000040101414038904102006406503010384000400c070080042841c0d90591002450311088110941c0d001d0468a03802110610462402c0c07501440340300c150303e034145070340014031403021207500c2c0a04c04da5482e54007400e900184a06401103070703034010041204805a0300290070740341c0c1e01c41d500d8511075030f5004100203000c80b0405580c9800d540c0f902969604680 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 558579487 1250 558578237 558578249
    0xb04050f18040b0a0615080a02070302250e0603010506030c1e0d24050f130813060f2604030c02040b09040507080c01020105040209010506130801180311010203071413 73
    0x400c203207440d003001c00c0c0e180f8046601e807007184e10700348012800800203214520b031880c60b42c0e11078009a540c0c088460080d0b00c030440940943c03286103560116881d80640030184a120405c01210780c51030200840240d00c0090410b80c40380c0d0500342001910b480004030022150300c219200f4048000d504001d0b44d21800d03588209411841d0020f041c0c080c0710700d10408802c032400140381d1200078041c10240d041241d0055a201d24000621030201d0f5000c002c40598680040c007500310149450341540030600303005c140360f003c00c0c0441e121400e0020130580026446e01c030f440081071160604100c4c2c1c0b00307800d64142c0080009043c84007100e0751209545550780100f0a070348018250703a0f16800c00c0c2c10300c0c1d60703515000c0c0301d42e06042c8180c031040302c40e0794810301415001d981e000e41a171000b0707402c1004203c01074000c01e03050f40351840031840000c0d92407400d015401980100c410440030f079420390300340200070b811014154141d90303004109102d216903201032043c1c0145210100b45e81c4455007080c4134085d15120303600c62 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 558580737 1250 558579487 558579529
    0x150302031009150611190b060303090910080d091a0a090308070b06090604060b07021c081b0c1f03151e1706100e04020a050d0506100e010b04050f 64
    0xa0b00c011042d1100e00c01c00d8130701503111011020810460306a9071b4036180d2002c820380043c02502c0c0002200c40b864503420000c02410780e03007030106000c0868000102201d041d82035044140c802c02c0410300c248500600d50700e061610050050802c11901d00030300050281d0300301d8940015218a480d0301c038028803005141e200b074070b240da5000d050a120a418100f540c1d6184502c1110000c182c83e4682481108115a4034462803030406155408001411050300b220000c0f10920948403400915030134000c008520b03500c2c1030074044c032550031034440c50004550340490041400b2110350851042356211440c03080c549142c04104842c00c0010110113105640c0700c041600d0702c41c28100a1007030f6106038081a038034807869500c80c070322290000765550700055440030013401c020b0000380a8104012040c560050010341011241641d070800714110b0030f580c590599541e04100700340326202032079843c503000800c00c14168150311f5041403e03108c254070480c81410321510585440e8030b410785809044260080144803c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 558581987 1250 558580737 558580751
    0x240d03051b0c0109060309050c19140d1a04020f270a1a010c0809060a0c11010c0203190501110406090314010908040603020d0e101d07150302031009 65
    0x58015000001d58080a80c001a0300710080800011200c010000c141e4414904a00d0440c0c2030b00144102c00c41503501e4000c03403000c40c40b0390315180841c0304035050f4003112075441c80c0303090280316202040c1c43c000c61003448181900408604100c2514580501d041c120564644562000810b524403940086400a80c1c1151282c14006c07001c00c414140c64806050001c1c954070b50b0082d00807168019200700301c01d1624040c1041079485005004a0603116000c500c0ca451103001c001000c5030068807032680001c00f68180070003040740080f41d0600c50b801c01c0c00c04c4090b0315190b1b0700083c1c8800c602000e0a00740c030040c440080500c81c00350418400001d01200351a501c58807428018034001c401d00050300c289000500e0807081103030503c104120640c100c0d14480c02e040c10594120040d50000c001c00428580720641c21019843c00c7c441381c01c1d041c44040c4009038052091200c2c00a02c0183c002d040142e4001c0741c800c00c11103a820300e240220131030b1454016902c0c0d0343c24100e0f409232452500f140c4070031458002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 558583237 1250 558581987 558581993
    0x11040b030d0302091503010302031b1201140406060e1e07020309190303080f011404020708091c0b090312060d03030207050607020f0601170c0f01030f0f0f0f06030506240d 75
    0xf0080c08001000d1710f024a40c9200000034409030311081c84025003680c0461540e002c00da4005d803448640181c01092007034181501011a82500c6d030801000405c10409420711080080794880d000c024008502109100e25000c0f030b41c1051400f400c10b01c00c81c510000e200040c1940c0c800d05c00c45049060050035440405003e083c1c41310400d4050008501051b000c01c00710302d01c069044007040c120743e5201e0a2800c3c0c100241c080c04080d40005604030f071540d4040c03040840c0340e5a00c3c075148405510a030b40c07100400050341082c8003860400b40c0f840d82c3c2600100700320402d024054060a41c00103094605200c4d880341c52404400a2181d081d014105000d11000d120740c8685c0850803c3d0311100c82800c407003150341c0f9002c00e00c408881190845916501a5004103018105034034511003441050400082c64454041e010040d030303006e42039040407959500d007100d2110f1040e2081800d038128408040021a08554815541d0b08028201c1e1940180d40d48580d09440025600b810f10080e015255003c0300c09145 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 558584487 1250 558583237 558583241
    0xc040b070c0503100908180d2003010f0606270f0b0a022a0108060102120f0903100c09050d1403120603150415150b040605120702070506040311040b030d03 68
    0x80240c43c8039000e00c441c22221900a405a042c01c140c00142c4180703004a140d00f080035809400c1a80d41d0403001101821012484104081c84548001070006c840000504101400c5980c070300005100b43d890038001380071342d40d8004007015000da9028a01e40e100c1485280741c244da00f100790300209031540502000304060101c80050020700d00303150225514003080401042c04e112520745501c10700b4403906010011903206160182c0c1120040c0140ea0203400e103c642d19003541c2c13210810384003035080003820110508003040b240240d003003407120400041d03c4a030320041c000b05141c80b40d0b0f0300c50090f441c1d2031402e20142040c1c0b4500e10030381004580c0d54065110000d81c90450460ba541d00c20302918040010380c160b0408054400d83d8030000945030b810343c07010300100611120b1822100d03c2da480002140007900e1a000740090452516100d03141c036a0b07aa002c08591703900070328910454210040c1040340351185003d8900382c03035000140780403008080f030100d002000d0381204c480e454491208410840b40c0c01d070b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 558585737 1250 558584487 558584489
    0xa030e0c0d081309020c030d0504080d0507030b011101020c0316021906020610080102090d0201050c01090506010b190504080c010309030e0301020a2c0913031b0605010906050a14090c040b070c 84
    0x44454a034183e44c0e0b4041c0340c040740540a030541c900e40040010442001140d844164014414007040307041c007d4050366a402c4800460303071480030036038820742c03145c1640c0c0000c041080891200300075031402c00504405a201d018070054202c0c4901d4804100303045554207001105030001c2c0301c04e0700038034a036520b0009585240c1074130900c00140a940d00480c09142c18001c403a090040500032228030000e9074011141d903400b02c0d101c0700b0255078072007580340083c2e014060103000341280700640c2c0d262220101c01c4904241c0980c02c41f014041d00300000c00c83e1500104140680303401c01d00740002d98130502e08082e00c00645088a0b56403651000800030000341e0880341210710210a00c241c901103102661502880300c06000307129074014802030004e003810700d900c0104d403050351084c5000402081400c0c4c2d4085c100210308400c40300251603100601800c0968440c0f4001805d048441d241c001d4600702c5051011261190140d01804542000901d102102004c503001000890b481a65589280c1442c042043e61 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 558586987 1250 558585737 558585757
    0x80d050307140f0304110109050607060e0f0f060c1309050f090705060f0409020714010203191401050f01050703231804092406180509010b0a03080a030e0c0d08 70
    0x450280081d01c60000001da6107652011100f83c3d2854589031560390801039070100f80e60400801c044085110f40b41c18003d80380d06407107910041808141041c205040881441c400c031403560000e400c02014003000100c05070804900d19030f1139540c4444071012002d0300c0254000b06001401e110034070042c1d54007102d015118220701003e840748a508e4000f00b00079485600c000c04a007141c14001030000b00100c3d801420064800e01d600c6d9481c00b10000214260b800803690300556071484816400c10303c2c0140a00d104c27004048403206900d42c1010005850110014074081c10000003203000c40030140600e01203030009060001e8107110600300b006402c1c0a0b88040d01d20114180000c02082041c146406a0f00209d43d00c26012000d100500941300c1007001c01d0f281102230702c0e1700e41d00300103030004510055102513030782c1072408a624907000c1201ba09440c131120219021313644810081004c5505c00c070540f03810081900d070100ea0b03401507201c213920b00081d01044503406000b190300001040500c400504007811 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 558588237 1250 558586987 558586997
    0x31412010e0f0a05070f0302090118030302010c2604030c020303090909060603101118150a031401060e180912031f06080c070b0403031113051c0c030f0507080d050307 73
    0x40c074540c0a800742c54040d5501c0022414802c0c3d40107026001c0d030089c015141d818540f10b0310003c03070124060705e4100d240d4002da0142c0d40d1000c440c90455402511412004507905400b82040b20312008070350342200040c070180030060308040e2141150b4081c03044803140741006041400b94104082203a449450969241b8401d04c0380d54400c0080c1c1c00c41d4099503001c030380108859410102d490407640361443d00408025400406c030780001d245001044042d00b00c40307045540c0003038810700440140341403201c113130446014440400d0301c02c00c0c260f90300903410740440f10300030240409490b0a0005413800710110f02c801d40d020008802c106041d001c00c01515102c0d00c1411040752404da8610342600c41020581b0300010000c000c2040b04041801c440640b038000d44a480d00281000344100c244801d600b00d02a01d0b005c02803420b404010b2860184100981d105031040b0f032510110060fa00c0305051b80781444010008040c000c4c003542480f0b01070101c0b1005051000c159048070071040c0d0000d001d54030131103029001c12 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 558589487 1250 558588237 558588241
    0x12090203011d010e07060e090622050624070f050309120c040b01030509030f0a020304051002010906050702010c051803030d1814030304031d1906031a06030402030703031412010e0f 79
    0x4e00c00103502c03402c0340c3d226101e03a00403408900a210700c65030002c2610307411020300440c05503582c100f507500314941708800b4000503060034aa820883c81e4851300705610003102c40d07040caa0724000f540104407030300d1a87c864820f058244991400a0030343c022030001c01c1d4050349000c50f1015426021070f40041180c0101c804010000d003401c019030468101f52008005640144640d042c1049150000c01c4461040c0c01120300307181e5244000b43c81030512900a00060351070740c0030801044120300903941c00c568a07000a01000c2046070f0000c100b8007641c02542d0752820150280d61154030240100e5540328486c00c41808a1031035210041066800914221043e1170b9201000b45048004019240900c2e0305903500804900c40400f900b500210182065903c0220380348021034040c840014078004021075100031034030075a1401800304108403a540c25028003001c104000c0144d81c0402c5840940b42d050612407a4940116450080c40c020107607000e84240d242c00010600902580c0190b00c0f0340c8100d00c0316202a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 558590737 1250 558589487 558589511
    0x30d020a110619050a02030c12040e150127030605040b040b0705040305062730040302151323040c020114070e01021501030b16050406050a12090203011d01 68
    0x2030f03c9000394001c401c00656008503181032045008003404912441140d0412003010b100906040302c01504410b134950000d410480741395481413844d80300c40360340b000100c507186940007e07089102c2e001c81c0086240c580c0034441e620404125101c4040d64101804000c3c84c0b03030502c0c0489414400f49c0d4103071064a0ac0c00002840300e0320410480d0107032903000002d0a01912400c402d201d90003072005200030180b2003031240701140c0c00c0420050024030440095885030b1402c016140c2c10090301080300c103800001c05c020600242c2c42d468042c5142e120f4002c101c0c1e98404e084421000410100d400140310050b2044207044003c0704150361168000c0c04440070804c0a0301e0b40000da00b200c841c5512020b280100b900010802401b038030712083d04400c1801a1016a59000100040360000360030485481c10102c0034007410a8200c21b05128003419407c00c01d251a0a0540203030550141c08607450802c030a4003006105c1c150a9004002017580c05070092001e415031030510003003d02d1087c4aa1400d6281c8101c9401d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 558591987 1250 558590737 558590749
    0x303020c0a060c20090906070e030705011710080a050d030b04050421110d0c0b09030a050d0b0a09061503050703022a01090506010e07021c0f0c050a02030d020a11 71
    0x2c0325165142d075804129590707612240d0340035000c19014100d0301c01d0101441d0307454030030700307503208211800c042d00c040c0c900600090300802842c91803034060392044006100990700480f82d11440d8082c0e006500b43c0d56185040810b01000c25000811f25008442e440c40420030b00160815580311103840505c4417164540610003180e104540141061003022522803110b03c1d049214501900c003407412440802c0c403624094580502c5841441c0094070102c000340502c03401c400010741019411000d14501030003600c1c010101d0258042c584a40d0b03580f03825210140c3d0b58140c9140081c00900401d0103419035400b400c4540740c0002c151071b07000ca07040400240c402c0c0d20034400c9528120011050350243c01848080c0c8003940700c0d003200c1c05d0943d90794400c0c041c081141040814001e1104109c0c1c0706091030b043c1402420804800c4443c502c4002c42c01c2c180507220341224203c1c075121068584615101102d06042d494007110300c1001e505801003a152507501940462607203d03642c01098001ca46680d44024080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 558593237 1250 558591987 558591989
    0x806154020040501050c1513050f01112710080403020d020601031509050c0a1202012a11011809060807061115060a08010f0606320306011412010303020c0a 68
    0xd07a01c00100814040c03507004034040d02d0390b03a15010883d00d0074561001d84111451040c0c0e24800b482c05010203210030050300f000700d905001202d6000740301c0c40010400c008214080d4480302e042e09211140010300e540c0305090175042c9850000c200d01001c040a00c4050940c0360140d40030b800501404c600d03142c149000207030440c102c90f0300a041c4001c43c03540900b40740c001d201e1168125a9409280d080e015240da8110314100902405a0750200c480d03298030014003e201c044028041c00c91551100600e20f0700b001c54800c10090f04440d4803103a40450b800101d403200360030316000308100155140480e40c891035500c4542503800e81400c0f01c1c801134494400b9108643d1003052502140c2c4104265900562424461604001e018149044654403444600d080d554016a030340e68040d9100000c1001a91050700581a403580019642c05041c000c407101c41c020220940f2502042c02c00000f00310680d00c10783e0a09a19140494821348502031a41140300d038a034217100950040c42214244502450403481c110 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 558594487 1250 558593237 558593291
    0x16080603010e0a06020f0927011d0109021b15071107270b10050a09051503042a090b030f03040608010e0408071205090a08061540 57
    0x6443c00c040d6507080195008844d0007048020500c04114507031540d00c40072283c41040c000680500881840b05a0300d081c0582c004991440d00490150565606094160542c5c00c1c0042c0980d441040c0c004000b045100308604500c40d2003050840340801c0a0310030450300070031059a99050342e08401d403d09503115a540555001c0070790100010b03950340c43c5101c1000c603504008201050111081c00003031150741a8400c02808100b00040411903641d0001c4a0720151500711012030200e02d2001c0c403401c02d4000140000d000088100313000d0014100c07210368410781c1c03a42000e040402625000600d01034003042c3c0985010b4880c0000483d5001c030040103440031340c1c189a4546e071841e8a0078a0b07680c0c80e008050030a49801204001800118a980100042c02c0460362281950751001d00c0a1140c10100c903480404103800a400b0300452590780e04a044400b41c0c111180700c0d0140390711503c0f03a214842010401000000c00c0d00a5071400541c0c1d00140d42e9100d00241046800420040c896a10038071034003803 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 558595737 1250 558594487 558594493
    0x61829030c09150d0503040e060a0f030b040f061a0301060806060904170f07030306210c050d08040503070603060602060a0204030302061b1e0d06140312091816080603010e 75
    0x1031445402d080000c10b92015101d05a000300028800c041095003485040076112900b0000341031140b5107103541c1407500500b081c1c0d05010703100e14190100741c441c1c1c06800010240b000380004581403001c3da1801910160300328004004000000019a152020044610b070182d4200b00c00052011008030b1700c10b1140c0300191200c0115912a9161070f1412076514013542c003554203010070096140c0d400060f055140c07098800188041c20450740c41005001e0b2880d100c18142c0142c0b103100050300040c06d81d070031140182c0d80440c100d0b540b403800c4000ca00803508807039003520814a000a02c1903154001508981c816001d43e4131039211650320400340d20441c04081c02503032141003c40c002925488003409403540240d007203808c1913440140c22040f80d00c0d541c08170b214110041440344c0044a544199401031400d9480301a04203a00307130100c1d40f900009004218150408282c13001c56454a80c00e40e0440a0560f0a2004510380410600c0f0204e4001c0752000005a0f11000a40710b07040520691002c10320060007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 558596987 1250 558595737 558595753
    0x60f0306040c0909050a06031a19020a020717030d060e2a0903031602090109090c1a070203030a0f0e0402030112140102160b090114060a031506182903 66
    0x1480042c10031842c0303141c100101a00002240e9100b881114020000319002040c003c0c51801c005401074003513005a10302c60440406d0200d00d08200541c00611446c000d0051f884c0c01c9000416402d0084c103030320401045020600610034640d000c00181001401c0740010001551104041c00501d00120350580e114501c00c1b040c11140740c50b01c1001583d03028041d0400745002c0d05940402e05603005140300710390075030032100202d045180500c0c110713015000c042401c2080855035103d045084aa91141802180160440c2c100c0c01e0040d00480c1c00240d001703000c032130351800881001000507054444100005000360702c030120b545024001c0b02c0c101d51102c0f0604045200035210341581c4d005104903400559820066002001c000c20603140b6910300071004010702e4944000703610b0a442d2105204413880d040394081061039950046140250b035040702850981c6002c46040b03900428042e00843d030701c01a0b0003c042c1524001d82c10864000311003c00000b004500100031491103907280a203290301d6004101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 558598237 1250 558596987 558596989
    0x40b0c1c0212090a0314010b011d1c0804030f03080a0b040603030801031b2c0a020316050304151a012601051c06020301060804020a0f030b06060c210414060f0306 71
    0x80c10781d00c2c1c3e0041031000c1440da41d076103010029281b810300b0b40d1142d4441d420815a9170b000815280c0b0810314503215a441e50380c51002504100c03100e0b840240040314140aa000d2101450940d009940e00c044180c6000f001800c010b00b6800b42100c51140140c140801500e050805018000490b0b0303051301d64030026425542d4808008006607600121f44c0d8981d20001100f2a8403480c0c0c2c9142d10210111760403941c164107050116240082899011500401c01c0c0310318203401030b1002d200596540b40c0349072607803624642903010716001c6c070328803480d942441031550602c0129044030800030000d80354001d207428032401003810b5003910342d02c55100788484d600401103420106d01007541d11001e2118110f030780303096585200807070b0400e030026000290b00400f000b04505028000001130101d901700005140d140da95090517007000240b4030740c0907100200780c6980c0c446042180648201c4513600500321031403a0983c002e4150003920035502070031803924400303806003005001c072011070080d04410391560359000c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 558599487 1250 558598237 558598273
    0x1120f030503090f0d0801050f040209060708070203030c010f05101512020318030f041a0304080307050f0705010c0f020601170a0221060a0204080606180f1b040b0c1c02 74
    0x4220f016240101c03654241c9104c000d01c0801c0c90800036840d181c909504180c113014016001620540c021171042002d95035a50364842070313076000c0b580b0800c02a900c48003131021a003140100c0e0310454040d8208440fa40d4120300d81c0c0c20180c03003032844c140385030580d90b81c98484070240e4403100782031404109a001c1c035400e0840c003070700155800014142d1034499171420022075417559007e0b403c44410b4000102e8184840b4030310354855a07020381c1806000e810750a03e510350410b503210180c0300c042402000a00c0d81e2000b900101500d001c5034000c402005a41c10200700900300c440900c0340310700107024440000c6098180d0f204031075030140c10400204950010340d82403240c0e81e6604d420486481d48041410742d50482d0800900344903040c8008003507150743c0390250071480c2c613102806403881380c0d0780c025441811807192203c00d640081500222041d6481e030301c8000ca40d61580074000c0888140006003c030b08004154001e103141288001192408030003104c140f540b48600048510040c0c0101e6002e0781b084900e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 558600737 1250 558599487 558599491
    0xf13061e2007050d03020303090607030c020d0c02010c15140603062e090615030c050405131503061b09080a0b0103030f030f0204090b040b040501050604150212130e01120f030503 78
    0x44101d40c000303910342000584d0042e141000f140181c3c000010490000320510010390801403034103062050503960305000e91140800c940c03c034202711081c1c08040c150382c4561a16010290450814000b8080b960b03640b00c0039151704510b500d00c1182c0c5c64041416814000f030a144030700000000c01c44a4250340c1214400c0422a034000c0c4403d0801c40404500000988103105c000d000c0c4117081d00441d540070030b0141c20740f54103400250510900703010400058550300c18841c21006000000180318050340d9401218040a0b04090840f0b860034500090f80d44060103499000000c0782c8a0b40c0f0055544c0c0c130740568542c00110010503100e01c840c01000040e00a1800e1a844101401c010819814040e000340803608140e1040090740e4840a4020041c03e1502c2081d01905041c0d030300313110560400022590a109a1140d2010901c92904c0715446a20901041e88030011110f09960748140301005840740306030901900031544080303400094030206241a111904c0d0f07001c215a040c024858030280d40503000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 558601987 1250 558600737 558600797
    0x4062304090f1b030519060320040f090506070e0a05030d050c0a0f05100c1b02130e0709020405040608030304050a0b1806130b0c04050a0504050c0f13061e 68
    0x203070782800300f040401ca40b08840602ea903903000611031034009040c2d08100194004010b1075480d04c2414030100d40e02d0400041d00c1c0004003e84030000c150a0042401008104101070380c0f1441c02400c2e104025002c118940511040da4400068400340f8080100085851040c02c2d41070344602130300c3d03007994040c0010f801d1122840c400d980c007600340c82e2900740e040c94402c4c008803000c3c0c1001c0d40c3c1c103c0c0c050b1548982040c0b1420392a001000e0241020360b26001d800c0c140c4007074071400e0f080412107234910994100d41c00c5010084291490f040e42c1c1c03800c95001c2e4110780180d030320a908050020615a0b4000140d9104580080090218001030b84885001c84030241581c00e44058480344004c06610801c19240100811101030f00020450705141800040180144e40103a030204000c12090740d0302490103050300d40c21035002a198030f400c0d4407000b407071098500c044d0890304041100c0707004e1032407210400c1c1107441a85902600490032808818074000f007000c1003010410b12080e400c4440c1c01c03000d5035078103400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 558603237 1250 558601987 558601991
    0xa020a06090618140607050702010f0806040f060b0403110904021014160b040201110c0f0111010b1903060b0f09150406031e0524040b130c0b04062304090f 68
    0x41000b0241501c034040c0d030816200e40c0c01d1120f122800134000c001d860f0b80001e05262050400047d6400200802c500380d141354200081ea07070120741e055031194450528218010420840300d550350001c2681c540062006031810241040001344a0504103a00f501c40c50f8010020803003102c1000c0b041e83c401c81583e2104a8502060101120014118080854040c0208400011440c05100040240c0915512041281c22100c20140c190312894011810002d0034244a810315441109107401080c1e0101d10b580e21404024100074089048481c07441940c1c002c00060101c41c5440041c0703711844c40f41d40c80d9803c00c107100300203040201031100070030320110001e0010030b03010380d00d4544829542d8222401303c003da0081080f9402c000c010000d42d05100340021240000c400d01029448020030000c0024105140050000d1400d40c407004018410b554800b00f10354140e03485080c5284150014040c12000c00c511520052070000403c914400c03040303035080040d141c1414803032060041c0105101c56031442d5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 558604487 1250 558603237 558603251
    0x806062202070c031b0501020d14160b01030b0906010605030a020d0e2a0f0d1e0510020a120b130e01060b0c0d030501051e0d02060705060712050105060a020a060906 72
    0x310550008044060040c0c103440389107400c504088405a150070084aa03805445030204850b9801181a41c011a668102428880051500210944a01003a80c0030b0025050b01410802206000343e42c1664041d0001500d19a03c40004581c1c80000380100c0b0003191b0244002104842590010680d25110b4070010529402081509182c026400442e21124415030b085a039826521070008040f102e007203500c90441038020340410b9044c0321401c0003619441c54160007080c9005254500301c00c0a03481422034600780042c00c60702000b90400484c2800260082101399803080a80c020030079408070041403d070450b450030b81d100005146c0e21031001c0c00c9540f21140000c02c00c42c030001a2410b220f051014110400c0f009200030202c1700140c0125106211310600b03d5413000c6403d070700c05a106401c0e43c8610410040d800003c201d030103030410040c007a100c0c403010416070f142d200204100f40094500140140e0740c07240108081d50081004400c0107a104003021008601203801118106005120000c0c10f1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 558605737 1250 558604487 558604549
    0x6070804170a1101020c0913081306020d1d03100c1e1709150f090312040302012c2a2e03200c1612030809010204080606 53
    0x1d000d00041c08070054100c85210b030107100002580d80700c40842407029001003c14000083c2c030320540036006a09036026500000200900f64007144c030b444034203035405c0d25543c0c0e441c140207688180014030076002900b82e02c0030b030488101c60940d604408000901810034080020210002413200b030341c501080002217010500c411081101c1c400c42903241c1d6645020000402c04c445140f250f014016541c20f9000105241c61065811482c0344c12000c0c1d200c100055868500c00a071540c06001d68052a5080300410b0004042d01548204240400b517190f00c1c0e6802d840e1100b640200c0302c40c510b004d003160040101c40d190200d1002c00040d045010361400c42c410491a000318a540d01c0070480c00844102c1c65880a20700c1003008803006807010240b40601022912042620035501076084031000010003080780b000145040c4074045001c131400c03044070000d1707907100410017202d0a1400d00380c022646600100303050a43c1802118165980c40713004000c03907120368080c44840e4080c000c1d50100380101701c0c0b401c640707 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 558606987 1250 558605737 558605759
    0xa020c0a0605040603050c0301050a0312021507030509062a0702010908120403031106060d12050d0e03030601111501170a06050c0a0905032e06050d12030b18040206070804 75
    0x905080d5442d9500c2d5418203030081d08484018041c070a03444024070040001d40c0d1814601d0058a46c4522405c940f01036180342640743c44a10022810402c0c422010003c14030f070b0680c4507600c40d0254400310f900c81c2d141d50b5005064100000c0d8801c0c8240c0d6800003a1a254001c40d00600440b8810b140024401d0703515000c1a003030410f404050f45c10030200240c01c2050545c02081a2552082030000e0100c50070000006000c0c042c1a6800500e14020112000c810380e000e6001d40d880c40d5000c070710612000031040980343e1031b580b08940f900c0c04100c10703148550301420b00240030105614404000a4240d081a030713152420711413072420740200d124440507000051818050540545164064613844141022016051607140e42240f0b020380d101000c005400704200220b2001d035000d03d9006000c00016050703a4029140c81c0e040705412580c41c0b202d0104000041c5407141c551082c40e0f80c00c0080d0280081003080c4080c400d8a0804159040804240075213004401041c40d0780c41011411b207002d03030b24444840 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 558608237 1250 558606987 558606989
    0x60d020a0e06041407020a020d06020d09060c1103090906120703050a0803062e08071b0506010f060c2006070614040c060302041805040206042414030f0a020a020c0a 72
    0x24041d4460003400000e04041c016298401e4140c0001d00f01031814110003550f914181001070b20448140004400344025541160710840e0320303000070b10441182e402d0160140c1401e403002c070001084450085d103d040042305468614200400700702d11500c41408000003540400a48002e900555800000040081001540240c4502c0000ea200d1070050b08014020300c05503080148481200c03007484c00203015107000d101d0b5071400d081100345500c51260850f02030669035450400b80207010015424402c001400d6812150482407441020784c584d00d0032120350002c000300521038980007046202c040d80820385060420405028103003410213948900b010b4031204070030303180544c0314001404140a1291550070140165044c1540703058a000c1a082040e00c90700e11108031207594030b011030b08640e641c2c012580140742000600c88040e01001c8810b580b035004580b0400441c0403513464140c45e003041c5003640d1207080da0382c450020956440e5281c0000c0d6214901030b10440c0602c00005a8135031741c6c5d81300c1c88 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 558609487 1250 558608237 558608249
    0x120f07020118210b01080601060f322701020706080a110d0f0506030109120e01051b030301150e09060f06070f150c03060807052103030109050610051e03060d020a 71
    0x10200341000d003804034044d44103030445c664039080300e0014424aa003010114092907114905240300a1541e140c401b010361480190a8420519441c403442d07101c40d51016042140b601c0d1a41468101200c1c080301c10054660105070150b0092802009414014160540d00c403d80c8030000c20700104195040d5182d510001080007281d50380c040852200c070b070300d101e0b055022606500821038a009601c030803480c50300d100548010841008203640d20780e48140700307442c000040c0e4101c8040030004401003a0316034009004800c488007003c805401c6a51241d12807400d034190203410001144c9a183c00e0004090382400c080740c0100c0b0800c00e01e00080c5041d4592405140205190708030420641c4000d401d403084142c0031401c0509146003403050355800300b01141205c40c00c448090342010100380e00315000140d0344030a0701e1400044000100c514940d0090751085800711440c4003d011980e0f0142c1c0e00d07001720319111a440902c0306421400600350b0005541102008092119400180d0700080c00c40b102c4e60040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 558610737 1250 558609487 558609539
    0x4140709052a13090e010b0306100501171b0a2723060301050d030c080328330f03050c1e3708030c120f07020118 50
    0x2a22101505810080182802c1e54075040714030250303c00524403801090380890f0b4490703220415410940c02603a0f60707080603003174803980c0c985080403010002c15845042c5c041100c8115070340004045110300e03880f5401101421301100300241340311100c0e41240500c5014807190030310400300600300800204150312120b8550111710300b090394401c860100800b0305118030031440654491a5a04801d89055a0041c0d80c550301040c25801d00f110f0703075031682401411081c800018000840403a41d0715500002200400000e1389620400081c121003860105081440174010000606444180801c2d0803002c50f01c060419541c41d05044610b0806561084800c1da22100100209080074414004089a1000c600c0c082c050901c0c0494000c1c00d4650030760210f0284040485410a0748460000390010300c071b40c0712511252034680040d130300e82c003071482c41e1100d1141512085122100d64122075440160210880c10890140d0041d901c404042c3c950300c00158040b14081010003201d0741d400c0310304514003d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 558611987 1250 558610737 558610771
    0xe0d052104060e0f211b0102160302100c050318040f02090901060c030309060c0806090a0902011b060e0111031803120601140705010c0302030a0b09040b0414070905 72
    0x1105103484180031610000300c034240010410150041c14000916105a50203841001c0d0500040ca0b404c910b40d1004210010316082c014010200050b5103010241c030007010500522014010783ea2440c201c8200042008000340520050074a8035014070340040e2428075030050f04403070b522039040d6041a26031060783e410300c0711080340c0d41c50540212036400500500440c0780c2900c2c0d4011900b4004d05028035400d00024920100400d03100380c7c45000c030f140c1c103ca010031032450605c600a0080c2e40a0f40c1d03c1d4840d20020001c1900400140f00b420f40050b416114845d180401001349000d070001004291212542d8109442d210402801110790030800c50b4039156892034074a0302c1150100e1126070603030f22035000303009140c1d41c0218200345a80014090901d042d6915440700a2030182c82042001810303035080c959400e07010b80c3c154010718080d40b409001800030b02419001e0050300c81084401a02d050902404070300455002c1040b04111004041070311521b6031945c00d01802c1d2001a9010343d951100103103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 558613237 1250 558611987 558612013
    0x91505150a030b0f0c1308070626010302040b010c020a12120206010305030a0302030c0904020a090501030b0415031101030204080a0c05030607030b060712022d0114040201170402010e0d05 82
    0x20111100101ca01d00c03962402c540707501c150541c0c003c05440c0041c034000041a41c07090f008042e140243c0007400703443c03a078949400c41991124404c0c4946070208504052a920710a080d1180740b2462180062403c6070303070310710340811014005005800d17052000c5030050401603215003060b50050a0701c400d8240c090103140c0b824103400c0400e6283d20b0b0840d0410001171000031404130488a66820301c0c47d01503102e44800540100c1031091409095015200040d035000b9507402c20200411500d09880400c03140151170240002d603240c034041d900388080c81c042d0078000945c0204003a20060410b1400508050701c3d4000c540c98041c0480054403121030f0350320100120b240400ca041d922980c145800d014100b13031280425918017804900074200342c004118580020320810200e056400c482c854186c00300c0c1c1030100a407a240d01d80c0c1c6403210650070220003d005040c6e0008440c02154180e4800b58180c189421042030404c024100f241000445454030490703903540c130081072505000d030010b050645101d10b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 558614487 1250 558613237 558613261
    0x1020316020c100f170f0f010f0f061202040806090a051002041d13050714030f1926070b0906070206010501050406030f0204081603050f07030b130501091505 69
    0x1000442103500c03040751002e55031150340d0700c100e060400e41080742614007903d2050741e6003030348044a42400d5125008004046120b000382600414901c000041d0f182d0b05c1c0e011403080c0e000c0500804814203c1c09a04000b180d20840c006805400c4a023001402d050f241c5000a05214090760f40c070301590700510100062003410301a000480d402400304514142c50003050000c460590548456100e0620001500c0b86803030410360b41115608c881940c3c8080e45a0741e0880403000440712490080c4201c1580754002200040c0c0d80d0164108200b02c5c40c4910415030b0340c00444806010700750b5201554520341c0f40c2d011200006405502d00c00c2c0d03c0b00d915480c28115151a1080040c018001c542c01600100310990b0004101c0302650042c1c5804100200001c0000b40640300310f03480b201c03e80c030600b02980540450b200d1900c080e40c2c45042130304c9001c0e50106107a0f035100d0441c0030190000a04502094002064101400400384510300204d038140d60f0b511115107000398504284c901c20703268030802030035501103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 558615737 1250 558614487 558614521
    0xb0a03080309101e020c011d071d010830030403020607080a090c05040b0a030f080307031407020601150e1c050c060a080406090f2910081009030509060c010203 70
    0x8904000569190880485411103d610026400c1d0300188141d07540b402900010420100500043c1c123030284000d4440e50f895040c8102c085204c110700100350b004030b0508d4810f040303c07182c1700106050302a024650007007034282c0494242c00d44104d55095042028030380a5849240240c003c1c203100d20700854068500b00c0010400703101c0c1c51070280d4080001e281c0c0b5078080e080d101d083d1400a51032101300082000d80074503402c00b401003640c240d000410407038014002d43c420100c59800f803002049401c00b0014030305082d54070351f01503040ba0f001800406140d85c01c600404490346400701d482c0c4602d1022511000b0021f51151070a0304820200042c0f203410460507401c0c04098406c44e15241c10010014294140500000c1c00151124030340010301c90000030b00110141c102d07000310920420035845110603c0c000007507120300480301000800b00220390f0b242d40200da2441c0098425030114000000007056400800c40078010140820007041d2a10000790640601c0f2000042e80c0b400d00e0901d60707101c4040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 558616987 1250 558615737 558615763
    0x3030b0301110705151906080618061b0a020304030804080c0f060a050412020a030209090604060b040c050904020d0615020a150902010e2b03080412141c0b0a03080309 73
    0x1c10800340c0300003000000c01500b003800d80400401c013603c6130b041b0f18440070640d0355000500c0c3d007820804550303a003000c075002c3c1c0201c80c0e564051340d02461440c245910f03450112201701d4013402e504075900901d50f400e0001c2011003503501c1624030b425141c0c1c0c2d4625203500950031068442c1d120f141420b8050400e601d0782540700b80c0031900903050104402004089219030b000303c4040d0501801c1c0c18086465a9000d60091940145107407214034001815139901d0101b15015140303070741040409c0400d814688901c151207485a51003a207884404002d00000e035000003980040305a03180000558644515410007401d1040c0d405880850a02e040c54414081d040d111212060702c0c0040980051b070704101c030121200c0b8182e81035020000301002400440712862443c080036401c80a00104140e072080c0c04600c0b991103031000785501c00b102e2804585a24507885140b810100801c02d00d100040c101007102c5601860786404100740d66941e0118041c03150551045030905c0c030100c10f0100a017003c0c4083e030a0460 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 558618237 1250 558616987 558617021
    0xe09040f03201c020102040315090c090204060207151209050303180105131209080106030807120203090904150e2b0c0317070e09100501080105010c080417150403030b0301 75
    0x40d501c075116143ca000004000350380340741a01c03a5002074000c1d01520021034000100c2c01c500d4204900101c050a040c5c401200c40d140c03000404501c10b0304034800d4400b0303a40141c5c02011940d04020320305500e2081561000c040c48001d60090030120b03818000d1011081c440c90181d600c03070800702031507441d01040041404281e4109400c2200c8190301e0101c484403a502712121601c5442c00702c0d0107840a00c4180c12400095003008404401e00c4103180041ca0b026104620b031500c0752042803000c07a100c0c000e041580350b100b224039020502264a11000503801540c03a1400201c400649614624004a03030040c40380c0d0307400c64200204100049882d840a4045d2820a05001d9219550090014520341c0c156816001c00e900414990340c850b0781c503104101000780060710300d410141e0700c0c948909414400c4c0b80c0024001000450203520512a903040c0c0c503800350307245040c1400c103102c40c902101182c2e49011144500000d00ca01e560403500302900840c02510700141c001102c1c002d150a56400e5650109064 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 558619487 1250 558618237 558618287
    0x2304030e032404020f0d0c080a02031c08040b25110715090308130504060902090f0402041a180603040b100e0402090c0a1107060f02190f080a0e09040f03 67
    0x1010682d91a584a5412a04003446103c020000350000011140180403d1300d808000b04d440c40300007590b80207203030080b81202c20341000e16034650020418202c1150000d2000c50119000a460703c40c01c0703400a45180c014004160a01200c6042c100c0e00541d01000a01003242c0181020050000902410115142c01c940e044070400141801d01d4a210040051030700180c001c2c07001008001847c00b40c18020b105020403130355110100c0194014201d21849040000702401051806108032022651605121202c0310100007880381e0a8112060044040548018007007007507441c00020b52255121700c03070741c0e456405c100c40b01007080d9510390011242c240c0010140405a5944650079a0150f02407600b13590b80c2c00000300884100d91341070b80c1030b20217101e6a00042112030b00701844c1030804d6129030032039011501100c51140c10b41c01000e0040d052a586200c00c01c0481e80b0702c0c0003800c0c0220f50341400d02101881402140390490100d030199042c85c8403110038810140d00a004184908880054102c20 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 558620737 1250 558619487 558619543
    0x513031803050c0111010b091509160e010509061c05010f09020a120522150c0302030c04051522060e06090307050919240605040b0406032304030e03 65
    0x4150300d407119414441c5140242d154803170250042c00c030100d0050408000c03428041c00c1080342d815184803851007940c141c400a081c648000f00c0c103245041803640d4002c02c012844005484550080c2c0b04070f07030891402c0010a1603828003034000030411684644c0041d00d03601d40200c0f00d10b00001d5401074207546004000700c0141c9a070200417460001005207001885840381c69510340300e05510705421085d1001241c4520620072010040b100f8510f07008000c1c020004001c0048040b880200d59240c01420140024846410040c42c02031005407084c142c1441c0c011071140c902c0c01d400040109562500c0b02032403e00c03181b030307100d0360310046490207075070044c200416980040d880b1001d47c06454083c107a600006281002603003001c121a1584444c00c1203000006c48001c10a490182501160010b02032000034180e4840e01c1214112840c14041605050034440c0031400707414074105520490b0041c10a003070410b20b0000301d42d0b00442c401c0c0ca400d1808003003442414100a9169044020300598a0318001c113 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 558621987 1250 558620737 558620743
    0xb0c1b0a0803061509040f05040b151f020f07080703110405010e0a0902060409020c0c0901061107031707060e03120f06030d1202070803070f020c2b060609051303180305 74
    0xf014003200c1c8640c01000d0461300350068090603007000c1d132041c20440c00d25181c0d1180d034400381c002c0d4082e00c850485c9546d20058011480c01444c010380e00041d10785004072608030341b4503072414035000c6441034401c01500c41e0720f01c6150111a810800303180c1c00200040042003044901495480d005480502c90b961501005802e08080100000c182640f03c420010441d61140c04a030094980b8090464a0b5441800210b03a10a0f840300e0b002c1c00b8619001c00421441e00801041c00600009001021020704517a6400019005038a0301a0388800912030721002070400c1c065031200c401944020350b260459100303c84401080940140d0314001034105000441e103000c03c4086e170304041d500b001c4050354000c900b00350080c8191240a4076107034003c428481050384c41254031700c1c4540e242d801c4400f040d01c442d04001080c0b110001c40c2e04441260b95040006c00d00b01803000b079685018050004480b0350b20074030402610310071070b89030310703a0114200090101a00000c0e83c520720010501d00b826124210303a24230b0380d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 558623237 1250 558621987 558621991
    0x30a06051603202a012d09050c060a020f0a060912080c22030803090102091516030e120601030305030709090b0307141210020a0f05030402010906050d090b0c1b0a0803 73
    0x1c844c00744070389007010700861040425104c3c0510b07002000260440700c214150100d2a0010303d03500700000a921580d0080c900440640640200240a21940540404c001076020200a0065000384250148000c1051242d0700c1c8140c019031003c2101141403410100030306200c103850041c84950010310141500c24400e0750030703059400c0800b40042403800400400c8000e581e000920b01a00001080603404064020704401700c0c0c19503000300306240c20385200116008241005110300c0d240122000400d12588a40c203400c200a00540021044044d4040c140700b0240c10541c013081c400400d11000941c008489030052401d4001005081c20341701c0080d880c0c0304a07102c1d0000c0600441c40c2c8034110b0362401d0440650b24503507012901140d807080406400f035004001e0000100300d01c1c0c030700e04102034000d0040382d100342d90581d128640c4d00d0404a064070280c000d100840110b40c0d540c92442d000035080c0340418040c607070222180ea1070300142d00c143ca680d0f84d4001c0d0b002c0115000007020f10b00113089041607030703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 558624487 1250 558623237 558623257
    0x22120b1e0405060103290a0608120a05220e0901090506090304121103030f120109050f1612020c0d03050103150c0503130f0f0602090103150503030f09030a0605160320 73
    0x30004600b4582108103218248110406c8840b03d404e000120350f5503403000e81120800816940113031464074000c0414014422044040f90040003004510041140b00f0000891400b0404220301e4031419007000c9208101c403402c68581d90b425400092120402c00d50390b0212081000310b281c503041111649644038496002001000e1400366a072450380c0910a40c3c6150341c0340c7c0b000d207440700d400f0101d8464140c401c0c03244064181c41c1001180c2c00031900f00c3e6203403180c001c031140e03a0000c1d10315110072a540d001e600fa01c0c540d420313424442344a42c0c50040c0b022114010555602181c154154204803a400c0c0d02200180074203480c0842c0042d9003174215007529808100f41178030305000c2c003090034080c0072000c080d080149000a0601860100111035020b4003041e0400c3c0d90030480a404000721820411503401042e5040d0700038490b00300091000d50007410714101c00341c1954a004901da42d1001034400c10f030350141c1800505500e412105905214000601440c50303120603417441c1b007402d415028424120701d8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 558625737 1250 558624487 558624503
    0x2a050129210609061504060b0f072d0204050609070c02010f1202041d18071505040e0406050615160b0618070504050301150b22120b1e0405060103 64
    0x800c0c0c00000c0a201c181c80812240141c4007103181011400e6101c841c204c6003248100c200400040050400303214800598441b4100c1c50320b0601040600d00050301704a83c02c40c0c000401100d071208850a08111014005410920a000051510402054581c020880b50040d00c0201c10400b0040d400820300e44c80d680c0a08286148c035640107001c8407004034103601a00d92034000030f00024111000851103080c40c0c580b0203c40b8194442c204080110105a2070903e05540203100602ca0000d90403402071041c441414590b2401d0713a284243c60400f6000c580c245d030020395030f604100d0a401d01884018044d80040e0f190703860700548001000c07001a040c4006800121743c02c001405c0c0d40c0b111401d005c400b10340b03c03034000030500c0c05d0b4200a000354000d00502d0300950803e00d11496941c0291200d84c2926549007034141018500600c4540748400c01400f1040c2e441d59280024142a4032071099285600500c1c003151580350060344803069095004100c208000c1ca00308102c0858400704550381920b9020900c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 558626987 1250 558625737 558625759
    0x6020c18060d0507030b160f0e0d0b1305010f050103020f0a0e1b0904153f020103060b0d0b0a14030316030e150306130c0203192a050129 60
    0x3c2c0380b5010958000418944e175481c148480c1d641c24002148072015941e1700c030310b01540e8108048606050340e00546070030404072050340c1e000844966200303501c4100101d400ba07280400d038856a0a44249610441c900c41d42e800c018030650802da0f0081003010b005035028500c8031300c1c0c03107074410345400020200070600c150b14840020320b46421084410610008000b03022120310218003100c42211481410000180c84c204080e000c45c45d8011004038584595142c0740021b88128090000c1d05500c90803810150b489102042c000400d0340039140110903010300190740740f238045c140124050b00380c11070002c0c0010100020a00ea40000484034002c1c981140c0300110142c605e0180c1d204c0103403401e0f50307a002d0045000109014001c2001c1c41c40b90000311011040b0701c650010034411100c48503941c03c01a0400c108200e804543d0306003621b100c030101c0c6001040007408003c1034000400c1c80100349900c018000042c002e00009000b100c0c15080200c0d04040c149d400d080402d0742101c0102c1145c5c7c020b0203c852 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 558628237 1250 558626987 558626993
    0x3d0b0906071106090603012301020c0a06140d02131401020a020d03030c0306051002101a01090e0702210306041506080604090c09180c060908060c180d060606020c18060d 74
    0x152400c0a0300500107503102c0d6188d0034550680440f00b001d02c41c5000b281a0340100940c80003428046110f03001d03201040240c100f401c05c503003601c0c0c2c000400004120800404040790054030061605282d080c14191580b8185480900c10fa6071210800c0c0c1150300074003011001d41d903203070484100c196050030b00107590315403036a00358040d040e1684115800211280c11450043e0041240021104401000c020144091400c01c400e0341d194485a03000170325036070080c00007501d0003040171340110307042c0116002d50940c101c8000d00203544500030840d0a2002c028402c0d036042500510807034a0840c1c506000060514500409030b40780105030504c19a217502301c0f502800307044038202d03026000003a000c0c040c0320020340525101400d41c9500310390025010070001422403040201d141508c01c4040504440d0320340300b0088030613401100030503030415102941003185540b03030f1604541841c45a40042501443d1941c064200102c400049005103032500910031344c00310804899601040403a1115103141481c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 558629487 1250 558628237 558628249
    0x601060509032e110c010b09090304061b06020403110a05040903020c151b03210f04020d03090915180c121812090305060a180b3d0b09060711 62
    0x4000140020710b42a044d161000a41c3c00511100c1d8088000b4400d0b445540c052240b030341000c540310780b00703600b080c4000d00c4924403070141c028022442540b40e440084407601c1e05070882c0d0042d4412507141e0741c42c180c154101d003030602e2420020001140c042214503619280652140c825403040c510507007440e040d00010400440540d0071103007100030300d9904840300c60215a0f0740d5009041c00c60701d01442c0203200715071502d2003800070f12403581244021565241c030b509000e00c00f980e1003000c40600100c508007184454203403003030503016035000c0920040240303010202c040300b00d103103841080f64501701504802015000f230b03482d00c15002c2d00400020b0140c0e1a9004004e40c10140c0802400c0301e1200a150040d40d6000c2018011f4a00803016a240c0380c0710507010a044460440c21404941c005c902400f0204000c10741d0039900892010080358004030341012080c0000c0300c5030309414100080440303241d2050704016048085c0c1300410b282c6c1d2510110b24000381d0140a00d4400a00b10b03944549485480c0e2900 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 558630737 1250 558629487 558629563
    0x20a14070906060e120a080d1e021614011b2105070807090602010501150c0203120c150109060503071215050c090306070306210302010b03030318060106050903 70
    0x8004200b04458480200a0085921418040c0f01c0d0003098141c00d00d1680106039035800300d600c910b02600d405e21030040d500141250071218003030000c0b03804800c02c2e05185400140030000b200c0b8001582c504ca0b03480c18507143c0c44881e208266a078503114441c01ca80040d26841c03150700d401350404420208682491501903074050041078251030a120603c2119a0850781319406500e454480d859020f440c3c4204900300c1d00300b407180000c081e802030507180034035020701c041400d12400036013680d15001d2036514000043e4070100744210690b02400404110303c2c0d0442150380540124030007480b2280ca41400a40e4440550043d01c00d5084609010000c000c918111180000c50b000410722107403130180120788550f0014481380b4068007840c0001465103220f8810324041d1420300c0100a01c1510801c401d030a02c65a203140ec40a41d07580b003480b500a0b95040016610501d541040d0281e0024030600c9075040c490181c2c042c034140241070140f40c6040c0d6000c00d4203410780e1a58820064080190741585070175a06c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 558631987 1250 558630737 558630749
    0xc030307030903032712030e0306010f0906090e06060609031005070507031d100e01020f16260604151805012702010909020a0c08040b0307120c020a1407 67
    0x40014110300301a0056078102c2182d0094840140041c030030b0180400d42c11102180740c44501410b2001c1c442a00c282c441c1d00719283c000d1030801e000601c0000400d140031030a8202d100310811240c030030084900d280c014000030300068201444590300361091540d40307120140c019445400046500d04080d1810016038455600901d01482281002c500181c0113901c4070400360000359060440070301c00384500c400c481075607402034138800c4240c807190001c85d07103c0d40141e5058110300404000903030300401000010584900000d80c020f02d0fa03d8022945256806004845c07071582c0180b0000c0c06031100802c0d03035139015410075110726005d01d940004800400580b100400c2a4020a5081c0f041c000154005038004ac510f0703001c4031016403282c040104000c20b540000f40000c49014050103007803490380147c590f10301a42040b21010250341c0c0d8020f0f00c0e800c190003440e8402c1d408020840800d0740b02c1c407200c00a9040102c02c000c90900214020344500e40300002800c10f200c1840e0b0803132010000c1104c28002d0030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 558633093 1106 558631987 558631993
    0xb04180302191407081b0301050c0a03090606030b1e01061d0402070507053102040b030c131701091a07050403031202071a04050d0921050c03 62
    0x1580940840da410601c0803c00010601040840040d2010f0710203083c25400b00300d4800d20b121804040301d0300c81c3e810002030184110135a070458040710080c0c50301140c02c51039414418042d060640c0020964902003040042c16514164803894024100c02d42c0c45481e40e841500b01c0c5e400f02d203020700001d81d01103815110f805241660041c51003d120f9001c2d0b400a40d5543c00143c8825803003001040420040c498183c40e8800c0e1a06001c02510605011418507052034608a600e010090074a6206080040c0d101c031076894408844004060110305440d1806003881100d000c0d040c21401160391400504040e00b5001607040428031824690b038a160416107191400c4503e81a02c0c180c4035402035081021001007920300790400850f0303000303a0104642d42410b1800c00d182c06400c140309401c1003100c0501f4000040701e0810200503001a0030310424865450038050700300b80c0c10450040d4984 = true := by decide +kernel

theorem cover : BRFrame.Cov 558453237 558633093 := by
  have h0 := BRFrame.cov_init 558453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 558453237 ≤ n) (h2 : n < 558633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
