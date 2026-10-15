-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4457
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:40:56.490738+00:00
-- url     : https://prove2.me/submissions/90d9adfe-af8f-40c4-9454-a9a1351ef21b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 801438848 ≤ n < 801618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 801440098 1250 801438848 801438853
    0xa03030e0c130905070f080d0e0103060324050a09031d01110a140c06180f01030e0a0f110f09010b030a0f05090303190c0f05030402040905060c0a0f030b09011205 71
    0x6034402a40c845103202100648080005602c003803030303e401c5203010752640103071b03007251004030b02041810700000340201120b0882c9040000c1500c02d0300145c008d0304281d000103004154000c0c00c941d0701c801132146542100b414900c14440c0ea11650129400c4810403d0b000e00054050064041900030400c4088012032044c0b5080300450b19000001d07040c402c0c0c101c0d00b103482c0150310500e04083c903010030148402820442e0795629001c10a20b42540c12490420f0240c051000d8208240d10360303001364807010540382003c058404603001490000c42ca13400c2c000d001c0f00c081406002150306401c040c10544149800940101585e90030420400d02c42c0e0002002000c4641d1244140176010085008042c05039501c600210b0716800c00301300c000d1034041c00c0701070305030310f1880c02c8501c0b40207540c0b02d0b5440449400b9801c0c403e40c1ca0b04c607400442c0142c17031480b0003e080c82c400c0c001800034018405c001888104210381d91410340c01702ca02e2007202503481c050400c5610000420042c800480300291100c1414407031000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 801441348 1250 801440098 801440113
    0xd0f1d1c080307080108070e0114132d0902061b010213090e0f1c030b01110715080c030606030406020f190509041a030d0e13060f1d090a03030e 63
    0x1104111045400c0201c0c0da052000c4284003800f07811218540c0541480f070003502402d814450501c421100501c02c040d030f801c4440c1c601205070740b11052212210100040244800780030500c15501010b10b2105019200d0404130800341c075005030344580110b0950003401c0d14500700e5604800c80080c40020007511065508000303020412070f13480f407680e000700014240400c1007004a1221810710003c4404000c1c55008090042001041d241045c1000c00c05418005044d01c0104012241c9481c06801030105124500000c5400000008400c406003c0d1382c1c0c91a40c141d4a07071400c41c619020a940550b0001802e001040010704143c000e44031000b18101e0280c100902c0c40e81200c9012074001d84003000c501d00246444060400d4040c0c1c5c84503103582c00b60003104c0b450b20408241d0b64403440c19124108030290303070041929900c582d0415050611214203118068136821441c03c2c0c411a0300c03910007218425805a8540b583c44a071b6503106200e0200549003032401c80d01c065015040e1011010840d0141d0344 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 801442598 1250 801441348 801441379
    0x2091306080105070801080604030915020f07090f18030912080c030a170603070509041403040b0f0408010b04050f040b151002100c18061206180b030d0f1d 68
    0x30400004003115400850b05080c02c0714080c06103141a0040c848a400660400020a40012180d070450380c9001e2041c61109040104908107400d03a00420b4250007149170005440c8010780144c60443d42c030f800304104404100521801814945100070b0100c3c1502c1820003170544205803125100d40a20210362401d4009a0740742d04561281d00f0840100c0c5a0219100d101c03900c0b010800d40c4200706400501d000c90502e8009034400d40001d20040ca1009000e003030441d460300c20320071350707004150781203401d6282c00f0745a03070401c081d4000b4000d110256281034081641c61515000c1e2502a165940c0640788944643d03d0b41008040020b000c1c10300704149413604101600c500c449400c0c442201da000d8000001c541e070b0000141c03010b5000c0a800c0018205400803100d5911038207200b142c2607402d008a1190303010003103902030511a444141c24a81c41200c00d20520101e802847c40c01c074044040e00c2c0c00d01c1810b0b4055520400384200301d80050500e511a0f00e86204001039451950340040006100c260180c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 801443848 1250 801442598 801442601
    0x30a06030812161107030b090a02030312040512070c0b1b160e150108062218050d031a06090a08010c030905101a04051f150f05040810020913 62
    0x2e210680d01a00e00420190a6841103404072407011403401c40c9040789003010f49a0b80300070070300001e004001c400d0003051007400b040161004140c0c2c0902585e1300c8141040002d603030f81d502100c0641e4280201c0700100c045030300304421036000f560f00200c002000c0c0d041010b00c40a90700101354036240050003400d6010703981c01c02c01c00c030b44103540700c100414202c904140c1d1801003a500580100c3c2c0d03c401001540d5110b07a04a215164819401c4e5840b407256402c98500e1184800e00d082c001040510307000c05040c200c060304a07641011400740b8119428500319800803401ca507900200041ca8280503102051240790140c0244041030380100140d0060384c54600352404c507014015901c010950300e00c0c15400f0800d0078009413801104051040082c0400c010021012001c140c515a1080e640c40000030700c40c4801280805450605d40a890b030714503182d981c0d030034044104003042d0000c1594929903400c2c480c80390084400799610000a8241d440c050703020394001c1d41018032000e5203d21100f41d00612211075 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 801445098 1250 801443848 801443857
    0xe0d0b01030c050f0a08070306112b2315010c0602040e1506040605040b161203140907180507020715021005130f0b04060f09081329030a060308 63
    0x2800c0d0354070707040c0d281504004911803105580e03170049581e20b1081001354800301c4e40c1011a5000307400401c50351840c0294400c50f108010510790030051700740503e0040b909846100103881d0303000c4810400c2124a40301014442c0c8021074078410740114400256410076110020010070754181414800c0b9040c580e161010fa80250b00b2400303000038070100304035100c0465090400e18a6003a2421450300b0704008009205110354060522102d00c005015a0354080350700741c85a41c160050f00d885250000454014013510b000e40d100343d0103000b0000421400003010444200321000c5445c06484041d41a103c200580401003c010079405420000914201030009070404c000321540a0410501c64001c25412128064003420190b104d5140750310020702e000d0030440399160402281c104d0340d9100d1800c0300c0079120190b42e518019041c0f0070180100407040e401b81c240055002ca001e408a52101204515030b0b0600c0101a2100c00850303d0480d192400002150400d000000101d04640ca940b1504d410f54003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 801446348 1250 801445098 801445103
    0x2307030e0a0605031b070f0204110904050604050c16060e06090610090506010c06180602160209010e0417031008060c0a11011e0c030603020d051f0c0f0e0d0b0103 71
    0x46520004485181c0902810060001070400d1411401c0c55070000c110007240c0d0758041c0d40003400040c45400d00400c2400a810990300500c1885103840759200013103030303130818501c8a000300d0034035001c15841d18060082510902001d2286410401c60114845070300004280507106150344080c011a0900c040c40502c0c402c40d2280020003c60606003007400480c41c1b254098800301c3d141105110b240c0e031340b20b0005410b05412000107d1660844000b0120041c418040200032900c000b07002c029440c0301303c2d44100070a000311140d154503a80c3e078010001d4400b0486000f88000711440021590084140145030003081140e00c8032403207034695010070314010080e03510500d414004a0100e0001d40e2014049445006040083c800306801c036013041e02c0b06d81441c00e15041c1903103500084c40464403d134408001160018040003c514103401c2c0152281c025901800c2410384034004880344a01383e000340308030310300313070756200c0b5144000000e0031542c1d20520607561b1350109585500344081540c03104041d01860 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 801447598 1250 801446348 801446357
    0x2a060406030506010210090b0601080606120f1005090c04050d1e0308061e012001200a030c0504060c0f021507030e0307050d030206010e25030507140c0c01230703 71
    0xa064002a103005038003103000c40064104516440010748c03050070690045806c1c01c0011040d1109400100b86020b55071850328061440c0d01000b03240000304440c203024004441c010b500d915201c40502c41c988000b2182802417400c10401001242021592410814003903031040440d40018840707c00c00a00b07140041c3d000840450600006141140118500d480d1a0715401c1c0655101070001c1c1c1074029000c00c801c44010101d036100c684040039040600085c07481c076000581c200130303810319421907000341241400203031a00b0710a4030b20170f0064080b01c05603195500c6404130300110b5034400404c00c101c1c00080343c0000120f4400c1c50042c20325406070110500ca901d42260540411092500d0304c10241c6c4141e20078048800070034003080d00407902c64150713031500e4011100ca50310520030080e01020006880820700d50070800f000032903816400940155180c0c1e03148440440ba410210720540612000c1c1030300c0750040b0746001c400d036000d9a01140300002c0740d400040304200c3c0d400c2c41c03030150304020000e4020a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 801448848 1250 801447598 801447601
    0xe07080c180601020a060e0102130e0414031c09030e060d0b0315150402070203120a050a0306050d1e0303150b070c0b03090a14031303230705032a0604060305 69
    0x14641184090032007100054040840e1412000003983d5031803114024080c6c40d41c803091000441d00c04c0d0104c1d041d28400f2805003141c1c0341d9540807805001c900b16015200d03036070f406940c001d0044010044400000c590407007200d400301c05220201c000c2040e40400c60512004400c0f40d45680ca8000203080c02402c00c440005900160a080c14204414000c0000300340c8201010444402c00d4050800600201528010307119031a51020925000c984d000c240c0741c894002c2041f54201d984003004051004c12940c1c01d00006565405019100e1b03041c0e10010311604891100c8111000f1607849841018041e00e00030407005014000b0015140d0740340c02544081e00001030010034006010b1550005010140403585185020034540389c85031240f030002000804842010003801c4000c005880c40000070781c128255041da0783ca00a151464040c3c007160221030780850302030301c1800109098040300c1001e0040c0028a0b4220030212580082030f1146c0e0300ba41e01d416841c0c400b41c49800160026045646000440307 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 801450098 1250 801448848 801448873
    0x5070e061c0c0603090501113603030306061804051906060228030c060e030d06270509030c1b090609012304020c0105070e10032304060e0708 62
    0x12501d035074050100c0324844064036000105420480802c031101440c0008407182c082c5030141c007420102e6000d03070103207030045220721180f00400907511000e060300c190500850311640c03040040c08020081d40d50700d82c01c180000758490410000525109156141800b181c542800018046540540d020f8141907042c0080c14070401040c4240c1d80030b80010300040c002458500c2c00d582000240500307142d80500344080b40340c10180191040100c569100f40706011001c041c41c4501e9494202009029055003130a0001440381414200345281e102c06460401c11002026200c40c0a001c0103051030a09100402030021860814803802d26580e082d10012141e41a4110400084000c090112845200343c5c5004228008205030150807001e03a80c18420408201135001400034041d0780703c803242e45c0d4201ba04100140b64080350302001d031017040710a240d4000801f1021400c8940541c2039490a1400035010801441c030700e000b071039210340b090078081002101c2c4d102260600d88107a0050419a1125100c03403003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 801451348 1250 801450098 801450109
    0x50f060912090901090f0605100810092a0219030206150108071b02010c1a0405100209010504051e150307080a020717070606050405010b0d050a0903140a090305070e06 73
    0x75440c1000c540a400e140018000644284061040014180c1c2c0c2c1c4200b0201e452090300030b07800400008022404c149008032001e03050000c121a80e0b1025400140701244400c801d102d10410720030145901d00d40c00c3c02120403000405403141c415400e61040d00d0902144036180c10700f4400c8640b00c0d034040c1116040101c44a100301540c100c0d4541801050400c10441551040c48c0c0c0e24103504c11a900b07440c0c0d1240b4001611041da0800d070140022110f41501ca01e010600741c02c0c1c0e80180c0c407540882d041000035140c40002c034002d1501c3c550024804100070400c40c83c2141da0b41c060b105c1c41c8090b04000700480c2002440000c034100c10b041d14540e0100800074055042030380d0b40e81c0401c410070154680041035031058112001401110300f146408500402402001e1b842407014001c0036108025a50312400b000141d41c00941300120218240000149801c01600419014550584810520283c03540710403040760800b400c0001008840040040842d1701000441e00401e0702d509445254240b0009110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 801452598 1250 801451348 801451363
    0x6060302070b011712071707290c1602030f06070c05161d0a0b10081605120721060f0e0108061b090111010603060606030e160311060403050f0609 64
    0xd40c940030108100780e480780170130080206100b000c600c5940710340c1d52a1101200300c221960801e24000410042c08106011300302c11340a901600f000c9040c0e081c00c0300407030445101258a000010020b0055540040d0301030802d212240c07000303042d14501c240c5085210314204041750b42c00000b84032602024240201805104800d920161141001c1814085209000d2820700d80040f04200307214001200060150f03c00041601c00030440c0d0384180e1004402419404262003003000410242c1840c20a140980b040740c4d0403000e40c10003940c00750355021040c1c031018241c041d5a600c08030801482007800d01c0a05c00d007005464022002c00340c150910101c200341400581051850b070317001005200110340400302281e801003100d603040755600d04140048508005095400302c8c15030a00b00c010040050580082c0146c070051f0381c00700b2060f010307030340020b0761035042c4030700e07509206a1804140041201814100880c0101502041c5420b940e941c6462524400811126494208905201d88200e013400b001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 801453848 1250 801452598 801452609
    0x1e050406140a0225330f0c110f030f16080a02031c0203090909060406050c0702010e12070f030b1803040f0317072102250509270a03020c1e0d05010e0106060302070b01 73
    0x501900715000c0180081035424805403400014907420007a942d180c0202c1409c4d5003020701950044c6960b08046a601d107800000d01805039903121010682c3c4100080803825140c000f00181f404002900308443e001892000b0790045001c1084055200c0d11010301040c014900c640c014581031810303040c20b00c122140540191b2480200f040090701507a07002c4103284011800320b80880d501506c82c0480c500e49034281d403000011a840b01c1001051101100d9000e101d2081c80420240c80c1d52100c2a40340c40348241d0040100c1c2800300070047c00841c00c0d41e0344086200a0645403549030450688030760b503a10702600f500066012041c1d4041200c2941841304400381c140010726115113240c841926881140c09003c0c07980181c41caa400142c503045000c0035204440811003040040401c0a0865501d03411a0302d403d5002d4402c0b4141300d00710f810030012400881c80742c0702d4402c22324a1031004015000c6100300098800b5901c0c0d50211500d00028403800c0028002a00c006a844c01c10389820051141c059115 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 801455098 1250 801453848 801453857
    0x918030e1804082b060329010e0903040911030403030f141911040e06100824010e03060a050a0b09060a0b09011e050406140a022533 58
    0x5140c00c881800c507031507001035015031442c1d01c4800e401450070f801c18100078002d01e000084020b20011801640c0481d00340e03030044c5540300c285003402007540000000c4103403640003411142c0041001c160312500842e0056190750070740e4074081e640d0f030b400c0e0280d41c074145280c00f016900109200401da050302c03405000d03640100090102948400c20185100c070010900010040c0038807030800800a81d510002100110100040e1030b01c2d01d980d40742a1005080342c0c081e028407980d00041c80d0881c010f0340b10910805032498101518a60701c07220f0480d0180f980011818060f0070505001265400d1000c40d00c00e20f008507000442e858414420020781d60720301081030003450304000b8802e0985444855005541a014009513921001c000485804440c0115100b20901050241100960020043c400c98a040c1d60b048210081406d0300d04c0c05102d040750300005648943c2c401c4d02c40000c3c0078004003000c0c088404a009065039108189003c40c0048050b0408801602c1400040b1102c00040380d20714295141 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 801456348 1250 801455098 801455119
    0x1801020a0f020f0f040f090302010b1503070c080702090718050111030403120504050a03320c150c1605030115050a0611011d0a03020c150405190918030e 67
    0x58440c1081072030003002c0d02892184803030450381d0f19403103544800004050070400c65048440c0895008044445044005500342030303550003075140241e1034010718180030018a181d915012403c2c2d501805d1480200c0d1140740512801c005039031244507152043e0000c0d11003c0c07041d8000a0070501020a6400a078144242081c0c104000708000050b81c1c00d5a5003d104400660300d4910140c59038040c507480194092203506000c020083c442e00c0301d46010243c450b030520390780305900500d03668100008100703040303030b001c40d5000456141c442038824449a4800000e850310720348043c85410001c0c1141d200d1460b22400340100f105040074070540740502600305541e00070174144400140c003800e079881440c04100240815a811070000c0d4407440c025039260b038000202d80005150586c4070500030a00350b003d401034008442c02c0f0b00301181c207036080103070803540c0500d0300b0b081c502005000f40600003643c0203600c54a1011401c0c204600c641d10f24401c81740c60f21260140301d494000c1c0b150040503c49070117580241c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 801457598 1250 801456348 801456353
    0x601110f03120a0b0301020c0d0306050a031a04023c10140307020304080303071d040603150e010603050a110a08010e0604021c17040f0b070b040b04030c0807081801020a 74
    0x1098407541018400c0308020b60725403c00c1d0303002520180340085d503d0352000443c5090f00c01c0001e1200401d52245d04c0c01c0c0400d564944c100950050740344800342c00243d07100108001b659034440c0702035025100618004819803020050901c1881101c0242d00700a140021a0300f40240e10b861036016210840c1c006245400c5000d004007081c081070302880020b400840403841046c02802914064440c0004498a03480d1010004086582c10301d0b005107000a4002101081c0c103082c09000d040ea5081000e01c911000e44080344401400303030040104c6103550303607140030000840c14414101c4050041580240040c00c43d000c012050301e9542c0b10a410340e140402c800b0680030049034050344580c0494103240c1e02c000c0040d2000340c54040182c01403910004140ca440e6201d4090302400c2511444207134541c1d203e44079802e001d0107110710a005000c2004000000d00011130190a090b0310900c07034507002010348499a82d1000c0c0c0d03080707540c040700c55500106100018542500e030080c01c6100c2440100f60201c1c20342c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 801458848 1250 801457598 801457603
    0x31d1006270e10090302060f090114151309140f0a1a19051009060605070309030809150a020309090a0603030507060c020102090310060504060605121504091203050601110f 75
    0x80182000c01c9498031500e2000503401d10110b002205981e0042c08405018035000f0748850040314407008915511001c074041503814803030000c02c1085800301e0f550b9501c0d900b6103202c0b01b20840d0542640165480c0e0705e10940d68040c018000c0c40c40c40340900360b040d0003035103040508003000300e03800c0840c503403000f8980000711300c24240d01c2e4202040707899126616207485d040f0909014029801d81c0d422401c0034213020120302e144815034100c42401c0010071481da07d41d20100ca19101300710019000500d60f00c03061011a010f0001000c2400d001403501d45241d03040186070110350031244003140546c00116940000381462080c1c954800c0a0740b40821080c1c0c110ba602030154043c0b8240508495034400300c1e4140d05000b581240d10070f40000f8111595403000c16042c001904040c05054009ea00304680015441e0084c07044d42d0010340c0000a04200703995030240c0041904000480310b41c4035072030340042c1001c07030b041401034a100d2203d65004559868141d00260104691100501050f07201043c50351400102 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 801460098 1250 801458848 801458909
    0x80a050d0e1309051518070801020c120d020c0609070f0503010507140c01090519021302030705090d0314040e011706070e040e0f100c090e060a050105030403031d1006 73
    0x1002e030015050ba042d04102d4600814001002403901c0c244c17042c0200d0011804074080b04100c218100c4800c281c446808500741d01443c1101e0590b50320541e4102111340d000b00203010240300990005080c000188656072402805803640041d68215000c1440001b4070300008070007a200a5000340701c41e0805c401c006003010b090001d499805440440c044411070307402e4002c0900c00340c1150403112000304410109040c001c1d41c80c8102d2044102d41440038119030b140c02034a208800070b032105410f00c1e400e00140160391509032400c0f8200040d0b214844003200030300024002034140c000c4184020742c1014860325440ca02c6041d601c0180d0300c04820000048d5020104042c010410384002c500300240c40202e03071610f2607506140c0d80034000c50a522601081079440172520051a5403019400c54bc3c501c03900e0708005c029154682c00c0300c18180f00b031100d54002c00c02103410501c207142c00100703030400440c01d1115a1031034402c18001e030071400419060f280980580c002415005000644c5190404600103c1c105d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 801461348 1250 801460098 801460129
    0x108060703020a142101151701030b06010f020a14060709050607020d110f12030a091a030601030c050919061e050d090c120503040f120b0411040e07080a050d0e 70
    0x10005055004990545c070111180013040041083d6541c603504140415040610148001904010660400d1001d0301d00d150481c3c2e0045035058280c1c65410044440007007e41e40a0150300c100e9091600150040031004d101c00480c00c0a81080d0400c520010040c0100d075000d5849000144048009a500c00b002d90040d580d014004400a00e00800030034585030900d00d00991002c0c20040b00c440c00d24010006002030900e550710b50489a440e40da1500c400c403041264131040c11030900c0000d001b94000c0d03100d40704201d070f9410058241440e07880000c180d0701d00180c00740014075590104002c1960041d030020030304c80c840404403000320320020b4010018080d5544052a041c0c0f1a8125824025203c100300d0140621028604181e07969027003542d0380394024414180c0051001c90000780e900700000c0d08040241d441007910216032140d07218608110f4080c041c640e4007569440714022481003c00c00c0741c0040a000c8050909940c140c00c000e410400328110213030038402820b0303002c0f1280d915a0380d880c00841 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 801462598 1250 801461348 801461387
    0x516110f1e130e0106060210050a02071205030c270406080d0c06020708040807030c17030702060f2226010c090e1e0a02040e09010b1c0510020706050108060703020a 72
    0xc2d0200b40b600003400b820511101c0b15460004049281d82e4080351490242c508140284401c0d12442d043c90100e01ca1000702a00201140c41217854441c0305600964000c0c0441e00c00a0522200c5d60819582048804507400a030b00c109191095504240c000e24004188041c0a45002c3e00b000601600000c12010018002c83d400240c030410040400c0c00d0b5000390070810101d0b6580d03601c901c0c143c08141c1103401a0000d14040d21480b00418400104817500240c0c090b12450400c0e00200c00440a034000f50720350740410b0b64441400b400340d0100c819090060003480320351082200000c0c940c0090608850039486141d0501515202041d04500700c28102c80400d102125550f9074540c186040d440100007034441c815440f0107100d001180d640150054400a190094507602d441c03403c90300701c03409501d03103507000102041403d00d10310503640600c46940c01002658020400002c0d0130049034495801102c84075601c00040c840d05e40104041e42d8014a03d007021440c1c00c00180005d045450200c07085c2c1650b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 801463848 1250 801462598 801462619
    0xc080702060105060d0914011d190201120b0306070f120615080705040906080304060e03150c0306010903050604060911010512010312030608010218010f03020918070516110f1e 77
    0x80c03005d0b500c4034507007a0300010452801d5111282040c040c042c400500c0f085065403454400741000040f41c3e010201a600070721003805034482e801911080031103281c800020303035140220256130b01d0501042d44940308540e04d0540310007054400be00703058115140001c60364a40103013442001d9912603d1002c06000e402c2c945c0d200e0352440c5088605100315044840342c9401c0000002c3c25020000180c000d64202da2a110740859100e0140341c0e40390000c60707010ba001006440454806540b040055401c0481858680c02e9240c8903214203142c440c050364200c0d0480da9400b29542885080d102c803814910702441e00b0b91404000003412100c514060001502c00c1c00c51000f0115864001e9001c80f000307101e440c009640b10351040400d000140000c5000c18045006009900300c2c2522902c2100d00303108004001c0d00390701a00410210705070000074105014480100001c2c11200564108510128890607584800c0300c2c40c0000d000c501a0040c0300c10307018080e03803007918004044c50b964030340344e044082c0d4500c03804 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 801465098 1250 801463848 801463867
    0x2070602090a030f05060a0b030c120708160504060b04231801060201050f10180f0209091305190b010905090c04050118050112050c0d0f06051501030c08070206010506 73
    0xd1041280450b406030700d0b460004104102c044120807600e01507400d0724030590340c1d07840d40c2e81502e0842c82a1540758001061111051920850080360500440105c0d0381454542c89168a40342c1c1c0384c01d14108481d44044108240d1802d401414003506400c0108da090601d03020356000d5848210102031540302c4c03060300750385681d02d401f121341c0009a02d0400d950680e580d14403010380280020303030317001c0550010b03003000540c0040301b401e1301421208845110642c000582d00c400005003039000600409d44d40820005000f550b4420030240616103e09401300788242c1880c18505e8207443d000305010121004064802140c18010701504645400001051a503034400c9083d04203080e198604e5072040c61310002250f081c3c1561600da004804184003080541d8a85c11040c20444000400800c0c55000100e00314407410315451150b451307442b03000318040240103a81c2d00002c0c0e90341142e9032070a400d040820880e166906010303400b405005030800f400f43c2d09043e0350094880405008280c01802e000449099 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 801466348 1250 801465098 801465101
    0x503010615050c0309060a08060f0d030801060c080c0601090606020709050408040b0c011803030f06050603040b070e0604031221090203060411060d0e0c01090f0e0f06010908061e01080d0503010504020706 89
    0x1784400020022075179401081d00c003802024040e01c115000e20b240500700e03030042c2001d520258403aa0542c1f125500c5178a03010302180e9400095400711400d82007030012429092042000c14043c1101e041d01140541c2004402890142c0e1a408480082d04180601002c501d03040116425220f1700c105a50342c406983d503025016201520420240382c99201c2030800345507141d40414051200300c001803208560340c40c10480d040c001581c2c05480707000c0e0380340801e030700c10b000c1d5070110540c880c013034411410a40d40b62110140c03660000c003440085040e00080384044c09030800d40d0801c1c0301c55010200058402a0003003940c55100400042c250404050603903c00c0d42e07003109031039105907150b02c18422854481c05490721a0700408a1501055003c1e02c0400e038001c00e103d032941036513040d400516030341d03980000c0c1269035180907025505000d82d09102185020050100512904a40d90301d0160a5845540303070188090507400500250800500302c2056544042140c1c11603000b01c0e80541c031901ca9083c0f000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 801467598 1250 801466348 801466357
    0x3050d090b091e06120402040e010603050c060a140409050a0c080106020a1203021e07020f220932100204050102030a2d0906020105070e0f060d0917040f0503010615050c03 75
    0x503442107021401142205c07020140611941c0301307940620003141441260b03800c4e2606800010000d41000307498118504100001c6c003180202031800303041040300040f918285a005800c0070000302d031140d0030000840c0b22801090000000341c5442c0307c05616041000b03455545440005202040207289820458481d0301520304001a00b241e45202459140d40c089141d8422007049010b04002001c01076645010f02d00708408141c04120714848046082c982402050305580031194940c20182000f00c2e4945084020961001c2140b4014401640c1d0011407400300401001a03900d801044140000c0c0d90200580320000031505180321200d00c611084602ca8400700031405003110064403a16410703a00168080407125150000c00c0075403a9607800315070350704651940541010081c03041d40201d0038002e005101306031030120001190420360360386114039007031142040c00d40d0078045014050365490003200e000505040f0002c0000e00c0c0340600901800310441c0c81c0f20140300010500f12410b0b00c1c10300488 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 801468848 1250 801467598 801467659
    0x10501050c070b0a110610030b060d030309050a0b01140907051b0120270303070f03031b030c090503010e060f0601050d0203100303090509101710060f03050d090b09 72
    0x3d40c44003580c84008058403d48009038071503114031400300e16601807403699801030380d401c05418042d55950809100d107000501108404050362480460007041041c03106007983c5c2c0c40754006480701d524142888504018060b030044c810210f20080c000b5803900203049400501081c150584451045030300d0f40d004100c01000180030604c0117000e01c041a031007900400c5501c41c1c0340128565864545602609200421620b5805900030008c5001203104003401e00321301c6100c1c1c030b4003081815545983d10411540c0d290140086501d80d03c6e40c001e225085100d0700003401003500204000644030307441c82d0781e4900c041e201101c0c0c00c001c0d502007603107030f40704e0b40444078007901c100d000755641d0800501815001c1c00900c400d80001d8840d04011607285082c000150060114040c00f4071010b091101110740000352029803002c61203030011403041c001c401d00030140144200c4400619003441d500305039003440306c03040c0401c0030498011400d00c100d144645c15034031601e905030f640798032a510b071070348008006900380b209 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 801470098 1250 801468848 801468869
    0x2030f180f160905011e060c0c1809120c050705040c0e0612010801050c041203031109130b0405060a030308130c18021b010203010506160c03060e0d0207050d0803010501050c07 77
    0x102804400090410407a00f00c4803040181e6a626aa83ca5416034040b4021400c0c080d218020172401d031085013154501c03406100c828802c40e82c1d5169071054554900000d0740e0181e292506542444072400700110011000d00f0a9864500740c0c0da91251184010300440340324a9032031401d01b5069214200c042c9840300e01908071683c5010590142c2d41382c0c08244100d003169070810f0700243c850800c00e0183e4045414400d1101003c501c0360b074041e00940b00c0300c40d10320030505050000d160365a40e41314a120a0710b481d404001050305590090005640f40101207a0240801290400c0007135800300ca581e17403001d445401c040c607040052030081c0c00a01c49510003401540a8810600f4854407a8005d0031004040f0502c5c480c100c0d0302050040c240c0c0024490b055000b4804d102888400706100360f0001001d114200f1a040c0c15225565034080392200d84007805181c0c04a11541445a010818403000d002c04940c00c0e02544002e40d210b8109100c14095103040000101d03141c6001c0200304801400740c080c0800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 801471348 1250 801470098 801470113
    0x13091415010806090a032001200d0b0405060a2102270709030507210812010f0b04030c090f1503050c2b0305160804090f0b0402030f180f 60
    0x600000c200707004041c05800782c80302082e400031000650500640d07168640034030301c1a1805030b01a000c0300788080c0c120319548075071288280c0010501ca9009607615003402640341c0303811000000480d4a2665840c1c0038a180105100055959200241c2221542c0b14210941114191030010340c1038a044020f400c0b10906004503000032200d148000b9480301c100e4900030f665207062084070788209512001d400c2c0c0e045103e00340007541c5400344844440c0480e042c0204810000d94a52030158401540c40c2c4003d400c4c08014803c3c80e01c1409100c00a000c0d00405a08050841c4c6842c0114405449941082940d4091110110060b50081c5c40d01c080c02f44200300c2d5103992401d155803903114030f40034140b15000c03c10101040e0801c0d114005040101c4282c014900151b694048c3c400303900c4005034040700c00d00383e401000054083c2004001a003071200c40072820b0140d40e860507041c0da5001705181e110300e006200b00400f90303103601c1c151544011504190340210740c0e003181d05800e1001d450100842c0f800b500c0d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 801472598 1250 801471348 801471373
    0x13141204030b0114010507030f140c0303010e01080706110d0804240615030e061504060e2e03030f2106030b04020306060102010509030d051e07020a020f0f130914 71
    0xc2d400d4120b035465071031100404902c5004480074410307200010045060080201d01c0315110b101c0075119103504e58101031030003011100707440c9183c00903800200328904030401400070f07040901c02600104202d0030311490340c5284007441030301c4071030300f04514003084807200000701840b030284690cc51803003008548840d001901801030307025001c1380c0209a954450301b401550701c43d02c00d21a03000040c41c1d9001a00181e1074a40c511003000c581030450540c0303c5e45444010408003d888100c90180510f4146038103a20240c1408500c84400c011590303000c420301034400c1012a03000441a91406501d00d050a0780036890581d1000d5051444a00c50b91030b0b240540100c1041a0881a10700850003281264120b6841c5001207099880840703411156800500c000e1900c0000e17038000719004603003e80d50700a8101030340c030112011070b01164107500503401554600c056080c4802e1030127034100d094845085003141080031440f120120b003100b542a6130340e60a61014081200d00f22850001c0d800c083e03812108421 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 801473848 1250 801472598 801472613
    0x11104060f08070e0f04050a021218120a140306030115080a020108012c0403020109120806041b0f05091216030b010e0121300f081314120403 62
    0x408040301240350ba01c041000940203515091030660018141c0e03034640503803004e2002400300600000c07001034091000e0121580e4050103d446180c024801c000031401d92659a407609600b02407200c0001010040b14942030707442a0409010315945000903525115100401d0041110640f01a00040403c5011601c0c80e4086401d41d0ae80d8000d0f0303200f4103541d03202d1100c0c1180100420103131030109070403900b9000c10040100c80e01e034000c0c0240000541003456071125041480141174400002e031400e410490a442c080c070841c01c190150419000100000307200281c0006000e246105c01e000020452400070760701c0e02c18100b419844c1000ba80e03400c8480380b6049940700c03010700003142d43c04004000400c2d40c104c0e2445da54101e41c001007404a0880ca2020701c03424802d4004019201600b54400740180790310340e881c0d1882003500795902d0350f440b0f030762180c0010204100c6c9502d000c1000102010301c2014507602500f5107441d900128150f022808040c21145042d4a2908072220020040340000034054075 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 801475098 1250 801473848 801473867
    0x20a060216050a36020711041d0c061c02190906110a080702040b060a17060a030c03020405070207081204030b06090c19022a0a05060301240201110406 66
    0x80c21101c401c064803001000000900b50003500d440d41c511000c04041c50b24015400c03000c0d01034801c240c046180380103c078502070340e00a10702607076510380052140100c1d0402c0c1c45001c4c21103441c40d502e190315a08204180342c80c0c01101e0005171241d140851107a407004680f038080e0b00140038847c411075440c514410000f00b4010f0800300100482e0742810001085402200341b1742000184001800403d07060340e4803441030350040f65059801560f80e6151081c141ca44900038284801203864443c80082000125000741400800590140464880820008056a2021081e40d904607408074403980d44030401c030720380219940461030511820506e80559a000d07002030081e00e0050820845c15076800d801c1c000c002e45c06a51880c0310f100100310505002006440340c00003509a8810350382000d0000801180c46007042030f558002c1d442d426020096803900345504001400103440d11421503150505c8d801c500d00c1821040072528541c0600380342035074400e40c0843c40030144d14901030b880c1c035181d4070010b140482 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 801476348 1250 801475098 801475123
    0x20c190503060c0c031b12181207081203130f0c081c0c0f0f15020408011409030a050a03060b0301180f05090c060a0e04020706090c060c0302060f070507020a0602 71
    0x2d401c000c02c1c04003030010200c941c811007241c021460041140c1344c41d83c4e4005040c5907101140540c00140d900140d01c8001802d4051504044090f0807500d18204080301104083e0b421095102030820815424045464510265140c9000b5100da45c0c80b0780c00c5c0c904094402c80146011521000c40c0208007402414105407070510044411441c1c03880e85d002005004901c64001140070168050005856024100041407181d48912061115650b03030f20700c144c0c80e4102c00703520303d90041418412200d0910070b0220440c511079403400360f8200405801d840303100340704000c03040110000300c1d2a0514013a42241c401000880400741d0b40c5d42c0d4810340c44004800740c1c0780d0002c801d03090041040c5200d4803030080714090445c6c0c0000d090442d54460400c4150b5100c4d040381030902c00e001c0c81000c041e03507841c07000d05039143c01440082490502c524080c94600c520303400031810b022412810502196001526551001621004040540b68224150741c01d000310075000b90b01851648020a1050b80812401d12110303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 801477598 1250 801476348 801476353
    0x2030c040312030203070c1103010e0708010524130e0f120304061a0a06031a0a0306270c0e0a090203011505010305100605071e0c0608100e010803030f0403020c190503 73
    0xd1002d02c0443c1603100c00c0e1450b00c002280a0445008262030040e90340d0317032907401000040d0f081c4000030742c0c604104c46030b48a03c038565520420004040b140450700007141c42a5038414003001502c0d0300141e201c0e10100c40c402002d607560200c448880408106011a1080e114100c2d4254400440c64200e00d07402228111503050521487c141c04c4000c0802070290141d00500080080d0b05140e0103e0040480b03200c3c2c441c00d021508241510784e200c1c050040d01450040401080c0903071310450903041c0848a00100320103c0801812070302042c440140b440584503850041d00b0f180d103441c20301402400c0404806545546031424400560f06040c0140044a034281c80c180050364900e180843e04c0780c00c9200b05c1d07010880c108003003000180a032070300c01c01410100d424a88010035940343c03818514246e40214010682c41d50601c1304504045030b802c0001d04207045209800d60402001399240d000240007102c00f045400042800c00d0300903c001e4000100140001c5103001e150b07501882c01c2c410510030ba031b0090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 801478848 1250 801477598 801477623
    0x70506040c120203030d0f020d0e030c07062d090302060423010f0228050a0812090a0206220b0309240423030412080d1a0f0f040f02030c0403 62
    0xb2400144241c1200d030014080c6090060389003100018208241e50039414130f40c02c100d03c2c03000c01340c41c1c032450504010400080d9196021408a68540707401034110f4024072000100652000c419071040c0c0d41c0301d40e020000c1134110f503880001604d0083d250780009510941c041000702c0c803124803100e5205245104102441603080890041d646842c021111034010b0300981c401e0441d4071000c0710706100c00440c1c03008801c92521581c5509060000c60141214200800541092250300b1561000d800c48a40005440d141074980d002030281e204a007010700d1041099016160f0146034441c802d4014041800c05650b01e14207603501c0c5444e5109aa4426904c44c1c0c07101e00b00c1140a240b4821034400d5a01481c40c0703007041c0580c858242280311b8000e0366846844100400b155114a010646015610030803000b40c803210220384040a44a0f0048042c48200b001000301e07029603038030240550816801d80d400c00c1080f61303070750101d405000c40440c40c440180c0000148000609400020011030b80114000c0220 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 801480098 1250 801478848 801478859
    0x408030a0f121e0b0a090e010504150c0c03120b0904030e04271113020d09110123090a12051b090103050607140d0507091802040b160c0b070506040c 65
    0xc640d0443e642003001503189000803900001948070019100d030080946a01c280c2d1940884151054400043c0690751103405000800000c1d01001080803260f0700180507180203840c0040c032404075600090104101c0303001501c802106c40d0711268110401804242e00c0749064140500000303030030345540340a58070340000c00300103000b20042c843d006461865000503244581d26138a10220004100d254402104040c400401d041c0380300412020b43c5046012480c100c0904040025103c0b21061605008074450001ca255003400b00080780f4192100116444510030f5010036030101042c0c204a600d100c0c0d4030041d00078000c0014070f20f403886410b009135144200c7d0780402d1004110080c40018525400b440208a0082c00740304001d182114400200341809400c03038480381902c41c04d441402c04982d04171002d0042103079490101c600c40c03841001c02e6190518200c440d0103075104207003040b18020311440b82036003002925070f6918014409030700c0e90781e199625820701a8070380300700f0780f0304696071446074000291 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 801481348 1250 801480098 801480101
    0xa11120106080318010e2107090b0907080403033201060c1214090604120309050f0d030806180903130510170403030b0907031a06030105091602030408030a0f12 70
    0x10b4840d60350145040260f42d030750200d00e8a107003041c4541804401c0596803c0744d22910404217000c0ca4a90104600b00c0d00c0b800c0307032810712842c0d40100180300d0900300302d0f8000ba1524602c40c2d400c14513130714120310a40d5903030901324014041c0440800081e4822483c071601c000e08810080d00300c0c4a586400d80c06a47d071403209840b8800c140c01c0040070000511b003000111400b13208c01070702c005141c41030540f40111040c00a0069030103600b02c0d1070980c002c1140701082c90340c0076000b4006444140e0707d11a18a60000000d40611058840101004030b58000580140c4440000c0c0c0c1410242000000e0241020002142c03a80c03c51040170002c40759041000440385030540c01b10f22105c05540710718240d500c4500c041c0c0003211008105409240c3c80e01c83c2e40e42c090b00d8540019125081c25a80091480c8500d5988001001916007940c41a041031006001558640d03054070b4000f0300810042e100030701c422100740d00714081d952003154a4000815a0622290050840028040380381e4440700341100b020362a00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 801482598 1250 801481348 801481361
    0x10615020c06030907050301060b0d050703090b0c090103020f0a030c1b030f08180d050a180e0c1c181a10060e040e10020a08010b191b050a111201 64
    0x180107034005500240d803400c16400842d0007010f90400d0340c81072902c88010034203640c0c04c0c1d400542c28800014143c1c1d0b070100c0390b204568000c80d0301c0c60240403a03482c0d911a4800b01070083d007071748841e910001c0c00c0075941c2e000354100c800340c046464595417682c1403210041d00810440207102e0125001701100c80c41e040c940c05a100800c2c1d8142c5460148110591742240c070000010714a0405145181e4405a03e090402c00498206d005a540039610420010001d103000d120681140036940f0070002031102143c2150b046138020103d0103025100e00c0440c04040c0004620804849414505190110351074400e81001110714052400140d505104642e44141c0035021104120414030300388080c0500c030300c103d00c4401031b400018404104012050300d840d061101603442d56100940c000355075262680c100514900404007400c031541000140101c120301c0b0a210034452003040003000c10b898029140b540180061900441261007610072894003003024451244031a200d00400d02840700d11503814018803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 801483848 1250 801482598 801482639
    0xf0c0606030b251707091707170d050702040b06160501090209070e090f2d0a0c02070501050d020a0c0f060c1107050a031b0801141005010504030201050f03060d050601060509030106 79
    0x31071080010814441c901c00907002c1c0c5c0030003811000c0007a0340300446001c2c00c04400d0301c10181c4445480c000c50180c11002403000c881340e035086141031081498201040e102c41c070b0b80599000c00d07000c0381400010454031554010070800c5035804100c8051110562040c01403500c00d50b500c030b01945492074107036070140a003d40698840c2c0e0760400104800207541c502c41e0459014145610068045119500440d04090720060070344004401c0041515880c090301a9800143c0098102e141c01c2c00002007492054003580840300390006643c09941c0d1155540a10640d041340424841c8080c6160000140ca0f0044090000441c04a07041130014404248041201c10040400103440d29558800b41e011155507441c0d00f90001c40000014441030a0056040c10491414405d0040c40c104c100d10b819000030303402060410500784400d00040c1d030070a048820110707803e00c09607142d40d18140082c01b02840c0074802030403805100c2c00000e5094000028003c0044118001d125442d00c034a030031040d5004600e00d5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 801485098 1250 801483848 801483857
    0xf011107110d020301140903070506150a032310020702041a0a120f02060a020a170a054614190509060c0706020607080f13030f0c0606030b25 62
    0x160000c1e4900380403502400c074409070000c1034040669860a418007021030b100c00042e04005141010400c049c08002d501c01c040c901d0071001c402ea104003091228809000c02070114841a0300e2000300104010700451103141d8108035644030064000f610041c2d001568200e00031401d0100c01c1100c0002c01c0301d4111081d201802000709940340401d04149654085001e643c82a03503405c40c0c2001d41c0b0340800520b103200558008051140f55490700310158040b00c145000d010354148030113a61254041c1c121202801007402daa4001000507110380c1d02600311090340d21518005d00207241c0560340c40c003c403d0020300681c135203100c480441c00900c440f52043d118420802c410040a00d02c406024001600050b100036110b941040e01c003c0003546004010341024016a000004200340140e2080036260720020050349000d0f2410b1815004a0350b024032a0000c0c14881d8401450305000d00c18140b58601940040007480100d40c0c038102200610400c1c0d55440010012407541440501074001c0814884443d03500e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 801486348 1250 801485098 801485123
    0x40f09020304030c021c020612100e040308130201140d0b01020606030312041506050604090f0b01050c0c21030a050c010609090b04080906040506030901050f010602010605010f051b0f0f011107 84
    0x2003102e205c00c03840071b00300344d01c614002c10b00140e2a0030340a4103288030907880c084098208214080114980740d449214030341802c0b0100800280d0141c0703555048104500c02d0382c046d41d214801664800c5445c54101e10300752010030101c03102c6025801161790250203800741d840315104c3c10f0034192207104207004c000c4140044c5002c0360000341d15100010b0301c4641208002400c9403180300190096011758403030000c0c0c0d0b1b190380701114503001a1052541120b03007428000d14050303a40300490780b6000c0721074a05210340305482080d0400004011058100c0d425507058aa55001e015000380054000f9260250598078010b404124620b262140d28442034010424510036559943c1e0f0703208079409902502d0700510117000010745c58030340c50080d501600c002800421f141ca4400501070400c50164003c104681c10700c0c01c1040244d81280d52222003c005142c8039607544019000020500c5125046214074881c00d4000c13100031002069044001306040d00078132098145410003020790141280103417044407400b8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 801487598 1250 801486348 801486353
    0x101701150207060e0d02030102120a14010e0601051602030115080c0306040803060603040f0b0a0902040e0606132a0203030f10060203040501051b0d052208060c0705070f03030302040f09020304030c 86
    0x5418030301100c1e00174080c040256007a8046401d9810815289a170361210300103100c104a060701440121640503203441d005589407203032080c4004405403902c2e05000001400580410740c403c4490388054000e0024041d035240d14005044140d02d038440c0480c640070340c80c806401c514020036054000e540000d90141507448510811440383d1002e44202c0318002c0b01000e031000255070b0b1001034030a14000100060100130b500501094074103038880e06035260800001c100b0140d54104500103c08200c0034001495460031400b00001729140702ea10f03200f5001c13803040d50303011039000004510034940ca00300e091064417800c074588000c1b80d00e8040d4801582007070100f44165440741f40a802142e06040120b03100c290034000c1541466410300001c2c0000f0030011700300d21480003005103c051262064401050715261604141e150070014204901c000c20008144c030070f01030208800c05c064985942000040c0d0340c1c9203030240c000c1d030040c800c40350011444007001030b001c40c0a1007500d01c00c40d05601c8200480310140e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 801488848 1250 801487598 801487607
    0x414010203090a140a030537030807140d050c0403061d0c131b0f0e03150a0f0605090109090c06080903030403030906110a0507050f030a090b130510170115020706 71
    0xb0004d9600900020000404100c01b00300045428015201c1e1000c0025502c2d16404403000d48074004c040450100e1500d00042d500600069114402d464003003070400300d10304140304501c0307030b00300d41e00d251802e14062082192904005200b2644984020813a101c044030f4691441005580c07200c1443d0841500144103050403801c8521007200d0f10000510710340600714070101c1c0d40f81c04400c80c000404160540720401d42140c00b0210070300c42200181110480852400201e201c01040c0e402090303158400940303416400c0d0010405414020200b0081c2e40c6c5a0f05404000e0100340700a850740390b019000001c8540c05407111a0141841101851841c0c0e141e0b1004c1d0081c0c520603108651103580d4174003481c2c00c007601d00040d00d0400000c1d6210f60383d826460901c40c1c40c00b03012030400c0300030340c00c10407240c160150010b020800300e40100d0410740d11030210300c5980d00c20040701d40c0030700d4000005031030720303440076503c600007036850307800d610421449036255103240e1001c5c05822413501c09640f02240510103940078 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 801490098 1250 801488848 801488879
    0x105061207050d020307110625120609020c150f04020114070f02090118060b030f0118140a0902041d0d030207110307030f1203021c020711150414010203090a 69
    0x16070070318034030300f0100103a01c1d0200da004a4401c000150001b68620b003000040c00459084404201c002011410b5184800e1030a01d072000d0900038403281c0780391800505155001b0b5401424079000440d01d039a2882c0701340d40c540240c0701219221481c00e90000305001800c2520034061501a0344039800b003565980c07201c81a038441c00c070540b071748000c804400d030040c0d40e5001c829000c3c200116010300110740145d040415516950070088031020180100074003181804895030448513400400c1100d5024103144200921366810090300344640141003002003881c0b50040080c0600c242c13020400402c02c0c01d8640e40504207048a2801600548140600c8510940207416500c1c026000300480100d05400245000819841250480310000040c028409004460010305c50107090a510f0903942c150340d410f0050b00d01c501c401d805580480d503030083c401c450100300388644000d81008111032004039030301d0964115101d2494801e0003c2c000d04e02ea03501c044155900c040024011001072810092040d0310200c0c1d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 801491348 1250 801490098 801490111
    0x905090402120a080c161a0f0d0c18050906010e0f0f0315060405010e100b211e070c0b04023303091605010c060b060c030f2101050612 59
    0x11900055000b89040c800c001640e403142c0000c42c1d48100300e843c86130400c02c0c405048604107540000410007210508610790100305441d680340d644150800301003800380a4500700c0300101c2d1400603d180402e400c44039161444500c00354000f152940c0300c04029400b201282d05500150490802085504084480340c8100318014130072407203c1c03c1d440120740340521034800c0019105034501070040e80e0419200360303400762034403013080c3c140c2d1300d8103420f2450003000350b110b107050740c150010740d603e10081c2c41c0703400c41707140400c20b510017035541040750b490b420301c405c1329800400c02c480e841d000c205a60700a900c1a42e2050303105030f403c0381a13370304c0e5020000140703003602e0003070001030481040c5016100016107034007240e001c2c40305440d26070500f410580d02d081401200c407111040750031018171490303820001c000e04143d480300c00401c039043c510010860038050304991403902e1002142c040717410f0b0318500282c210714129652201101c1c02c08900511615400c0c40740d1074012204002c079a0104e00d05e03881740c680c0700c03a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 801492598 1250 801491348 801491359
    0xf050705040c0e1002010e12070b0109060819031e0f09081b040902150f0d0f1103190b12071a030106090e0a020403080315032515020a120306180c0905090402 69
    0x100c10328003081c00c01000355262302d8040c4000402c0e0040060f0703a5002c83c05010081c404000850500700329179951942d10308942d420f0210b08404104043c8110701c0341c5080c01048940c04e000c0c0320481005410500400700482c00304201e03c8005c5022000000c003042d07404501200403c24039080f105210042849010590700808800d52480c81d45d19808000c3c046c1e4024400c401e80d442e0020f01c502c40480e01080034000e1400d007046e000e144044100c0f03007a2900301c1c2001880034034840c402590710005003600816560094042a880714122501141440866291010703024000b81c540070005498442409400081000c603001031140310000488291320100c0c40c400149002d4994540410310b13001140d4600c60748500b08800510703800d041c04003582c00c0e58520440c00b025400300300d600c48080d480c1d020350a5625150340341c85103800c0c400c01004807410f4205184840d08291040c00a020b44502c2c02031a003080c1d00030191101440403482a02c0c01810740340d480c407101a040400b00003c0b100090030699000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 801493848 1250 801492598 801492611
    0x605130801060f080d030b03030405010e121005100608090a0303020309070905091029060307020c120105040605130b1609051f090b040503280f0f050705040c0e100201 73
    0x1250910880000d032200c801140f49452078098028a0300d01c4010051003007600304400590b403500e002007075405440e802d0a001c0d186d610f00c1c00114107860b08007080c0881601c50250302c441c1d007585135070001d40a140000c908020190b2980070540e0031000c01e46601032580c0c000c0700d2413404a0310a601458005800310181c2e0400c030341e10310090041d00c90545440e802a006510340464450076440742001445a0006032424403880d88c5c03414481990920025000780f0340040040c220328424882c00d10b0300840200003103000014420302500070403007210121441c074909808126106049444001e03510750010410a1690354210001d01040c241c0c00841c09000c00c4500c04902c81c2d450140109030903054400c0c6403a6000714240080100c1030950001640074400c01051201d500d010601c1e006004494114100c18001d1010f11420540081005041d00284503450010004c07150b405480c07490103042180e03da180c03100c04100c00c407500c0d0789640002c50014990f5070f020341020008208081110700001070503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 801495098 1250 801493848 801493859
    0x619090f0605190603060e190905070b07080706061215180b090d08061c020d05030f040816270c231c0c0801030b0c0702041103010602010513020901060513 68
    0x40341c030504240306a088283d0002c1c8200c81d410702c5034000401c15200c2d4010181007541c4e00a0381e07070f4902c01c00d5001d100e84501014041c0070040103100024100300c20b20a56841c802c0c141101030780c0003088100e80c15400c0800004000801160304001260001c201a991041d000b0036136004001c2c08016150304035070000c00e0000320b10500d201c544200c0b0180701a0802c400d0165005000180081c80c15101c0c045840c46010003021203c4948802035064407800f1900d02103081551440c001c164081098000c0050003140d00e80001c074000051721030094080120a846500506400d80728009458200060504401c0e00c0d039881c2c0c0092030f485c003a07400e110001741c0c4007051303c1d491600c0c0300c58041440c62001580411908613410080c1510381c50210822208500c0308005158080600c005860040d80902040c8010000421182c0983d070082c03040100380704500380768a06030070900c59100594038020000300f544104441c00f00c00158014001121b0741c0c02d00b0380584007500a1201120171b107041a101080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 801496348 1250 801495098 801495109
    0xc0503030901092f012a0f1505090c0607080c12090109080c0607120507060f020318030f0304030809070b070f170319050a0e100617070608010b18060d050f0619090f0605 74
    0x191b143c001d81d0400606040b07414144201180f041c0c1070601c2510349400c000707112201003180007034011b0864a156841400c0c0c20000c2d00b50003155103290080c0100036814003041184001044480380c20380384c44d0318003641d441503030361034030440c900c5503402c18401c109620024818582c061460107a43c20800d080c9200790712204112103c4540070100705a00105010080c42c0c50785925203482041d000640c9090f0011650741341d1800060001014050f40c0004280318000500440340075090000c01d55898240c94204081840791200f004d5074410b03140c040c1c50001103911000c4078419481c4003c18000f0000342c00859000303000081c884c040d1030740c0d108d01315061307803130244121403410300031500100d9800d080000c0d401c0720070002100c481c103076401401c0070414280c000103081d044419616100d0389440e0701080090f030016180038881d0740a0070005034550131184550010307000b40d05403125582c840c2d403400c1c10b2091a880c0e941204200810251701040341d0011604110300c030000c02c0c4404100789964802040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 801497598 1250 801496348 801496427
    0xf010e091b15043602091e12060408030403120b0f010f12090f0b0f04031d010504050904080a080c0a090b09040b0d03020d0e040b0d020904030c0503030901092f01 71
    0x110100703007a103481400107916006000083c4d107405411881d02204000103040818420410940101c041c0903084203a540c40200c1c0c44000f4025090310554645850014032a030300448084010650f04c0346500c58480c0700f442442e140104c06861000341b00a42401500c10041d0485079070204a524078680c00a0382c1d0a00440c50b41c0307031280b06903c0e20000149010201000d006041ca804104680100000729502c1102e10b080c00000c8180341c1d8940d5101d000494036440350343c000715000b442c9001400200000300c4000e02c4603000c1030f501c0c40000c1e11000e05445052150300c0401d03002803060402403001589810080c0b0031888000e100042c005204004a640d084003684150056080940c52011058103c84590004042180d003089000c11704400248465021040a07007d1409200002d0401d8002c00313031070300070380e030042c00f00d903260701c3c10710f041e14080c00000804680e03840941070200354032800f241d0009500c0700c03102440c000040c100c2004440e01e02060707003942203d40c44001010442e101011100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 801498848 1250 801497598 801497639
    0x7090e040c051c03320f07050109030f02011404051b030c040603030302090108010f03170d0906091b050303030f010e04150606090501033801020f060f010e091b1504 72
    0x3d0780c2032012810094452600020541d024644002140c81c50b0340000c0710761502492090300d2142c031080d1050030410940200a8001c00a40c40d1602107814544c2210500c10021070390741c005e1080390340555006000d002d0030354004000b54858a8401c010030200408590340400183c12104021031100c0014140d0740189d10a8010030b50018400d515941d002500f81d0140111010380d40c1014507590705c3d50035400041c00c0c650b0700740d1000f0805041c8591690001c111a5400c0002400700a825003805015103207501032040386451400c0d0b00142508021059900c1000080c40b01c4ca0140c2ca0510b40d5801d1200080084840c91080d0050a42084991113148042c04050342c40362060b609000000d41160141ca0034650b00c184410040040412801000500080c80c2c1da0440d8210700306500507860310741403140740080340c0a8401042900607900412034100e6024500203100ba4985c2804c2c41c0d21030881101000523140d45098004e02410f2068a280710b5409180c00a0314066840e00120314481044000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 801500098 1250 801498848 801498889
    0xb060f0703030b0d05030d02030a060902120f0105040e2d03180a050d020609040f0b130e1c08070c15020c1e03190c0503040503030c030c100507090e040c05 68
    0x1140207140d814840d15484043c1510000d4000b46903485450396800742001c6205010340010005441002c542c01000007400401020354441390041901d00c04000210760380101e04420100004041c41e01d03011f40c0f0304001ea4400504000c0a51603004080c0002d0f050550b444031150400b000c02007142040241000105071003403101012403402000a00e140f9a0700c5036120b10a5580d2500160751345074110381400904440001e84074082c034500c0c00181000445403a80083c500219040070700d5640c01c43c0942034565000d688c547d4000e00e0910b03142e2041c1903d1503000403e20300009020764042c0c05c098014900940038100c45605d042c020200745c0c0e001c03042081254100740b03400c116a48401406000c041c102c079000c1c40c00e010340480506020f400040d0040c0400001c0340c40c9200307004050003210b01400d0050160781d901c10111044030b0f40c90788038001c0d40556103c1c100d1042c5002400d0300c9124043e03038a5a60301101d403441c100d540c42c8801000742c070a5651990003a030000742e554408010b960300c5040c0144 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 801501348 1250 801500098 801500107
    0x50d111c05060717072d0f0206010b132606040f02090708010303021f0e0d020309090a05131101050c06100504060602070b07030c0302150103060207151e0f0b060f 71
    0x14403900300038015100d0f200b84061809203010321051140c8599120065241646044111417000c0998816010040040d03041203900100003d50100310400405016000c5502c0340c1d83c2c40c400050700c1d120754480c81190401441701440620100043c40100d4180e940c40e41c0c0f490304144d5582d0b0f040032402c3e2011034202100100300c200318100006002d034400040d0614201c0703580345880c0a91510540000300e403200c1080700762032001c003c1c50b5010550421040c02184e0700325440d101d01075660f50003030941a210748200c1c4000380c00048e990240610520590802103c2403c89907100d4545295040172681403080900c1419884002005200d10840341e842903601031030718000902044075040c1d0000c0c2e0454000c001c00b40a81003800007184d08655242c60031310010001e40c14124103144c0440c18090400c5410400001401000e802810ba0300c0c1c011981c03016040ba102c130105040b100300c1d00f0131403500302c5c40e92003141111002d640801700c0c201c0c01351804100183c00d180060b01c10b031322404103160032000124 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 801502598 1250 801501348 801501353
    0x30611120105061c11072913030e0402030a0b03030706090b07260903121f0506090904030c0203241905040206030a1515030219021204050d111c 63
    0xd01401020300b40e50542c504203946190f84130fa0901942810012901c42124900403080c3d44211421250012090858030f4190002c00da50040d034002520015201c490101e240240d0b15142543c4d0b8903419183c000c015031146050201a4000174084c900e0196a1490881961014070051103605c0c414407001980d0101d620b80701250004c054403120412088a44070511000c010403440200075051081a10315170b1107010b50303482c5100c0d507055039413049902010300c14168852000c940000b60211400c2c0c0405407030f8824401c040c0540f40b40c0691100400000c2000329000d2600c1803a41400942981c40c210300d0380860f500e410200b6070403960820200c0042007107010310035404032407002d01d0081c140f1080c1000d070006030003400050002100306d81d03201c81c00b0185100402d804c1000f000d0324218000703040d00455000c1e0003508408481c0c01031464002d1905105440440c03a0040000d4440420f401c150408040c00003804480404a40c580c200480340c01c41c50741d59072001a040e01c4040390902080c0d8091 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 801503848 1250 801502598 801502627
    0x90f0d021506040f020a17070912020603040611040e011d04030e04020c12040f050405090c180c070219030605070e0a1a0919030c0f060f0305040201030b0d081806090a0311030304030611 81
    0x401000c00c01001d02c40c14000340c403251070980982c62f0100c07451034403501d40303041c00c000502600090076220380000900103a0700111400c905d040b60101c480078002c825401c40c0302d05010408480c0100029a40d18200d045450503a0140400c0d4000c1800c917401201d00e80c1404000744d1158000398251041034804004520b01400f4065011a8081c05001a2901400840c6070414440c48042107094102e00240002d03086c4402e403054150001c14801001c1611034100b800e40d4044e01003590014140400640d52a0049002068524003d840b022560380307840e0805040d0b6801903241c520b035110030400c154495469101c0030441c195402c19110f031035469464400c0301003699a000340064070582004004058001d07070741e160718404a040c08900da40d502d20048004140116103543c0c481850640c150030312089002130309600302d40e401103c00389040a0f0810885006020445612428082c2e007032001400c1c1910f0440240c04c00340440e400c094403542c2d103801340c8851120300340c424100440e110348003d03280e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 801505098 1250 801503848 801503851
    0x23a0503073309080403030e0d0609030f110109030c08090d060203090c01020f0a030f032d050601090801090f12030e0318030601050f1c0201121103090f0d021506040f020a17 76
    0x520700200203d01c280e5035000c10724000c03444050f0a0110751000003c1715110030001038411076200208101c141c240e450041e00c6c0400400a000c00a25001030000940f50144984080c090700340e1140340e00c0c24142e40e1079000c40c3d44513207081da82044040d00001d00084003400038501400c0500003030700b0104101b400092400d8018001040d8540c843c41030180402e4121101880b20031031880c2c0812101d5045ca05d07a05580006000001803c8400d050100721032555804540030f88404d82c5c51361841540c0e4140c5600382c40c81c81c0c5020381496041d016000024829141142a0030f503a0b080110702c070440d01c440c0d0740c1560001c02490000c8240110410030f00e18050007803602610b012107000c02e600107030201044002c56188458030106012556181c05d5a0080510040080b100e01e014891050070001000706a00b050310215076900c2000b07043c0c3c1d28400e0200300c010025a042d8002c4c8075416884020300c0300c8460250150340c0260343c1d801e0003800090240020041040d09480d060800b2041480c0c03580526030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 801506348 1250 801505098 801505193
    0x20c0f011a0315070c06090c060e01120204050112090c0e0f1b0f0403080a0e150c0714030309130e0a0c060807020a03020d0f120f09023a050307 63
    0x181500000f085000b0b00c2d034202c01c0da031074905000e10f410b00e4140b000300745c4200043d150300f400040000310140e0220300c04058000030307601c038178500549484540690040d03000e1940415402c1080d4603502c4040c1d886038002034002c07400200100e44d00c01c5030000350354081d00d1100c06103089000b0071800c200200000442d4885101c5014a0014010803031000c4e80682d000061080c1e01c00916541c0207442080c1101c50141c0c018009a070405c0070b540c0c600441e074450403078003046002d14030000a28034102c0901d80c40b01840907000d1854413000008001041074881d500c1e404c070542e601d4421050b242c04001524869116070a4500f000b1f0400070050400e00c401080c002c00c640c00802d03081d00090340800c0700d450341d04e058107098040d1041c1413405d5601c0b240462280c0201c1c0d01c0d0000e4090180850342146c19040c1c02541c20b6401540c80203915004404c01a840d504005a000b0882a46011020460b0b181c54000d00c1075a00f4185680d0301d40c231180ca81075801c08504040303001c124a1800c852141c0c09204203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 801507598 1250 801506348 801506353
    0x10e0d080103030e0f0415140f0603090a0615090c020604030e0d0302070b0c1e0c041112060f0a0b030a050403030501120201020604080c2b0f0306080a06090303020c0f011a03 76
    0x10b1440d50000e10007400703070800300e0180203008000165515560003450301c0d01c1c039885204171120f03200c540305400c1002c0c1b292454030440520900811b03505090046030b001c0c004000203005406c0090315110040c0c040018080c2c102c440301e2400184504c182d10a00b002d03040d19a0141011303080505008002d1022404950300c904204580701001a800044d00c00071600403043c143e48600059030498180005a55130354510304003642d40d0040041c010030381c60f901e02d500700c0781000803a5420241c000c490080f03000c01901c0900c0400403071000e25110b501c00003040c00c010002c1003050340310800c004554000303481a510325516103050004054060260320701400b40c1c0340c800080704170b007900000c1d034415002e440984000300009202204541c00e00100d101000ea0079520740031b07681600780003941d807e100030500c1c002400075013480c1c0d00341d0310074081e502c1260132800050960750341d41c2c2c0b90701f03008001103003040b03091686c00c2040c1280c2607814081e29502c00d8a5000020b0403280312054408a0041d0311105171098 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 801508848 1250 801507598 801507601
    0x30c140703020f09060f0d060b030f1e070807031103031303030e1509031f0b09070f020d02030f0d180b130b0a1407180f0924062c090405010e0d08 64
    0x142c5480814013031b200303400c9440a450210304d00340728008150b440c0740160140146c500b03141142e02c000a034107178107201d2940034510b2903482c0303604991102120300880c83c09400845003040480c25a568510110f08000c090724036055505401406590b0303da44224081a01c106a2444500d4050b40e941404481d544220b868a80c014000984072101e0701c004012a208000040d500b42da4154018004104058100a8107040c1044098100229000340100501c150244140744c02d10220540303403985189024642070041c40c00c100d101800c0882d09020341c07000700301050310100706e030b6100035405200360600f2a2b42c03030051130070400003a00d801403200e0340203030030442201300c0310b20700e80070b81540b00c003d0385490305080d000c0c145a4615400a540300d00010108034030049402c80b036540c01040c100207180091580d60500c0003852003501200e02c01c2c0e1001c180b80b045e001c5030b08002001d0b5481002d2181d202c2010002c100c80024904031030941c1c050710541c1d0358401c104818001082808110f107800c0c100901079 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 801510098 1250 801508848 801508861
    0xd061404060f06140d11031009060308040b0703021f06150806150702060705030a020d080f0601020601140109080114090606011404090207080909090c0114070c0b0304030c140703020f09 81
    0x2010345440fa041c20807842c4841d00015000640948031155800c0e801800040010311460700c00350000c0c0c0e04172410102c206400240040a441460200ca03403194000c3e040c640b030448071210ba5005001d040c1d065001d07070000d00d412a4200d2221007040100150009107260404040c0340d110300c2d40101c01410700c142e44040c80210340da0f0010101d00b00c84c0140502d5960070703d501c0440c1c40d6001c2c00d00300034071610001c1042c03104070b9000309130b050300c4c440c0a5503801550366603007030910742c46041a12803038050b030400001446149070b440c01c26a03030780c603041c18a0303181c01c1c1e901d4080a01b103e542d0350340c1c8a18800380d17109100300c0c60400d004907500301d03e0918006031180e03211244d052040c801d510860119960018840081007912001d554200c00c0082500c1c1e11850140c07840c5840e00c3d03c00c42d00e20b0000d80a01411800070410905450100340c0000070110800d0074080e200010b9413000d00b0035020311088458220005041350615800007000341c001e03001b031928620501ca04170f004003d20603c90303100203041089 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 801511348 1250 801510098 801510119
    0x90d050c0c0d060e030d0204090522020909070f0303111006060210090f08071104060b190309080c01060b0a1d01080a09060608030c031c0b100f0201110d06140406 71
    0x800020440d0001c04200a0f440c105000301080c4201ea4282e0101003690700d48441130741d01a104580c2c504c1000c0c040c0f980c0350002d06407411801c0b5400010520315408130005800c10355000c6512452200844050b140c41d101c5042c04005650700480001380f0603106050750000901c1000b040603110981403295508042000c1e446000e0302106100c00f43c1d5801c1450300380800c220403200c10581100d90f041d518a100d062100880500141e003501035802d10100050341c0c10b03007001b1376100ca0f019005101c1070403280e4104801606a0a0082d035002c04e051000703103c5008203201b000001c018104c00396950300641d603800f8100c8940300c03010094803601246000840d036044010180e112150b8803000a0b07110088c82d09100400b0580c1141301548004070303c40c000410001f00a04568211800c6a84000d0001912805682d040003813942c0003020b01042104881c003844252200100703034000132800703031030b4581c3c91302d400e40112070010076440e102c11081012050101841502c0c4070207035002c0c00034900b042c010700e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 801512598 1250 801511348 801511363
    0xc0316080a1410050406090b060a030c12060b030d090e0f0f044d0409080a0e060d020315120f0c091801091b0e0106020706050f040509040b090d050c 65
    0x40c01c42c10b009610070541007050148070b0010516540802003414035041c001c006103a4480d084400948a03000f1030414544081c04a085075032150b08a1080750400b000c000c118010007004692032521141818980d82d002d01001c8149030160f41c0351030600c0d03d0038001c5c1c4000309026121040c1ea001c1101072180231000d10b104640c0c0300e50003280602044411420400401074030f015410b242461400340d61501e2aa03334501559072107000380f22a04000c00c40c0c1c040004903620b203000200441010000a01964010100c1d26071103680103164500780039007064410180e0344203c1d0140210380310070502d0b080c05d02d0f042c180d81d100080710304e00900c411f18182000ca03a54061b020b030307990322a103841400942446610840a94032081050080c40407184c0c6203485040d41a188074001c080d140c900c0008103a14003001403590498400358001d240385498a441034450f51300024580000f2942000046407d40700c03c000c15018030311a046848883c07800f0342c0b0043c1013520019000e0204002000b880d1103501d000601076 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 801513848 1250 801512598 801512603
    0x90b0901151e09052e0f090e0403030605060c030901020d140a210f1401080c030303071202090a12060f0c0c0201081f121205040b1204021201020c0c0316080a 69
    0x982c4441403400040d40e424005600c6280e0000c02c142021079138201e000100d001d1005600310348903581604050076550a5907510030100000c8113010100007001a40c41c5140d0018080d050000b0000d450310082a2030b0350140c0c510b00c10542c40001c4014955a0400c0842c00a490764601040780300440c00349603050388140005102048800a201d001c0d0451a100c2a4840740d00d84500b08071080310a0704400c003a00008180156112507100001083c0d500480c1d14440010300402070340c611b130346800c002e4070b0b00c0081100c07000b00f070f560a01c589207141d1611020300010f000101d001c0d04481001e4608507054508010784011a02d0801d40724000300c035004144034215a030b0900b000082c0d681c4d50701c0d0451403081a1502400d15031012100000c0c0d0100410409004500442d05110035a01c0c10000b070f500c034495407088000740c200802400c84000c00d860a000c0d0001c0c0b00800703032500800340c2440d00703099801c000c0b02044150011954480c42d0f141c1041002d140304100d05d4608107007454942c005481da5a00c0001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 801515098 1250 801513848 801513887
    0x22a16120c030b060307170c150408060412020106030210090e0a0b0625060501030b07020601080111180f0a03060b0f0306060f090c040305010c0e151224040501090b090115 75
    0x704e403244c0d0f000c0c0300d110701034054104118000d0b0030541a995445c2444034203540941010000e48031a00d034980111400d4500ca00020a01038580d50b03078580c2c9200c6007501150071550f85120100c0165a8020a038007903103440c1d42d0310707200142428640c0355020005080009414035107001c0c01c03c00d03110801a1000d199007542c0c0b080f850156a400d032098a0341d43c1d80b0003000249482d002104022981c507146018116070340c21038000d6038860300c041d4221113240c8a0b002071510706011106108029001b1440b4181002d00305d506074041c0d01010944800f4503401c1143e0607629150390f080d46062401c005882800200c00408c4076041c20408206e01d80c41c51082e489c01070311520300043c19402c10008039001554020000c003c0d00c0000305006050340d01e0400d00c1441100c10410b50002007a6020542d40c4e409820a2101a5030310b649150036042d0007a001e10030034800400300c0c3c2c66400c0d91240b090364000d00101e240424022012010091040c1d4141c00a03c6101c11204141502c2d075440000080c004989100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 801516348 1250 801515098 801515101
    0x30a061e0510170901060e07020f0714130c0305060906030c01080412050702130516080114310b0f01050a020d1101090602030123030f030d022a16120c030b 68
    0x90860700d007400d0704014022083d040c81070007208001507014000301da84206000007207841d0050220f0300c07000006010b23012540b0540040c094020382000c809410b95008140c3c0d10603072005481c1d04140c07109540310001080d0b0310340c00c12031981070621880b5403222049004d024034544c01000030700b8000000d4030103040403142104100d01a401030b4200e4401e980c00800c0e084494485005241c00381008842e00324042d0ad9a414240b030761030240280034181c1c0c4a41e814100903902c100c0602c00310b51141641d020790105400003001764006260140b401080d460703407011031904002010b00100c5407104c1c418904011341000840041940424030488011084c5401e0602c2019484070341c1c094800e00401a000c0c2e07100100010310520b8606020072418184002e0304140c0d4400010180c8401460702c0c2d11046400411518103207008580c001c1074034074150440c0095030400c0b0000152449010328821040d030340b045101046086c0c42c0400d10005180c0c10340807548081442c2d43d00500444144001030509002d02c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 801517598 1250 801516348 801516379
    0x2060c0324040b04090506042907110a060612050c0a0821040806070e01111203070e0607050a08090102070b0418020c0319120605010206060306180f1002030a061e05 72
    0x8100901c000f01c000c0c0280034030718a50400c25291401918110b03180c41c045501070586070856103c0051035142c140b503e4019a4441005940e0b40000c14041003890240356403400000d0b020707104200141000205144a1501510b4242c6c80d003442d052400340308002c0814100f10b22100094040c2104c4c842940d03021155002c15901517503030286810502d0140901420000c0b40c5603c00500c44204109070f0311044640c01c0c422401d51030340c09903020b0213151003081000035280d40c00b03285481015000504818074202141d103600303040c40301c01070701140d01000c00108419951ba040024030701400c0c1c951b02c803610341841d01c10182d103010341d8000d41ca002290007050500c000d0100344191000080c04000c00c031011a00d60400a001c8800680f1410181c0d15050000c103095100003022442075401900412550310b4070010044a00155100340700305106108492003022414403581403450303602c9401603203904100c4001c0c026208a0f80005034100d9440750704c18014010801c208040390070030354100e0403007094070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 801518848 1250 801517598 801517601
    0x706031514031509011a041401050f060421061512020d0201210509070b070b190e0d0e091819210504080705040b01120f1404050d02060c032404 63
    0x40d000001c0f0038082d801000203d08041d0400c46c4000c03c481100d05500c024042008129044043d0814551030380a005006908148003044500000141118217059443c5c4d2805d141042141c0c0c1c483d80c0e40004c01d016030810100d40150003013584e002d1980509281450140c074038082c40d542d0b02900c5403104070a072400b964001c420500100141a00c8149001404285030001d45402d645209262141c1c10000507400310910a072080c0030741c0302c100401141c4540403d80440c1140d80300b82058140c0c2c850a65400f204100001c161041480c1c5800079400030907401c00c007035140018100410181c020801505007100490003030b10400b02d01b01d109401d04000c2c105201541278030410142f403a861114050707075644d0008050011140c110040f501a56241d2041c0410360b6040310301e0901280c8182d440d22a04034107500944c140070243c2c0d600040003030446c481c0000000064500380d50b141c000012040785140e0520442da40f000c1500400c42c554107180300e540b00608808408042d64040c00c81c060b007040d5855 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 801520098 1250 801518848 801518863
    0x11090402030117070e071d060904020406080a0b1c0f0f0c08160f06140d090213090b060a060f0c14070306050906090a0c03110310050906010602070603151403 69
    0x548215107030740c2c40c0c0d818410b1141c1101050421842a41e00c0002c55403811000107205103c29039601d0407090580c1c031a10000000040301950040c3c06210a40c61174580c0c0c80648001c050719900c41c4020700b40401c115046924502c001402175018603054511409a04041007109a01c4581400442c1c0b0300e04140030b207001d003040c0c01089001e2250b000108204009001152607041d8511a9a44c2d0340d500080b039910452072042001050303c0c0c0ea80e80465048050140c54200c1c1c4015001c1a84402c81c4c0c0050f46440138031028080b025500c07a140e40509c001c0c1c4c40155408202502c0e004c50050400c1009098111403403110010010b10210042c01c01691b140c814a42d14600c408a441c51901e0703180c000302a010407140d01c2d20310303ca00400a41c00303583c000303403142009400c5500021428110b03259595080342e1001b01035018130541e1010302c5a110f1501c5a5072080911101038141703541072800c000d0910303030302e0740c0300d81c0800d0304003410000c81d5109424080708490401002610760000d1401007404c0401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 801521348 1250 801520098 801520117
    0x2030304230301060e0603010e0106080d1817030d2906210a050915041109220f061109131a060309010c0f0503090d03050a0213060309020307140603070311 68
    0x302100041c01005d2091543d0080d54206d000744010724983c440103007225000c2c450100183d2000d40a0140240140343c5010040290384c0f8524085480b001543c001c2401c100500503503a00003d66020013600c2ca01c40e080074141042800c080120001c002039007541c48103040d0380d00c1200002490040b0011007829084096202a0079403160305e081d030881c2004040464084509000e80d41003196628240400c3c1441142e01000c90a03030380d40040140001010b0080000c01300201d800c1c0d003207564129401980e00802d1266400e0303d0000030301d01c1c10205643c65421801641d042c103000c08145656070394070041c1c0c405058600000c0d1441c8401c6070b001e1a42c010b8800b141c1207140001401003400040d0003440540d0030a4031200700e51000c20000b1509403200b1181c000b9107410168032030700068483e0b04015005004504058140318440e04c0031107860072642e020a012031303540e100120440c101031240c4001068100500e83c1002c804001049091000030110400c140c2d84a01c11681d0580103030a940b000103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 801522598 1250 801521348 801521351
    0x815030316031809020406140d0f060e160201050105010c060216080714160e0c03090a08030c0d06080102070302030901050c01180b040605060334050909030301060f03020702030304230301 82
    0x31280c1c00c01038021480b50400f0000120301034000700d8103d185000b01e500310381c1c59580c0d45c228807405907040500703908100c00300c80450707481c0c88080285804600030350011f00310042c404185400c101c025045503480340145c0000b503905000040041c0c1c1c0c0c1110380c610602d5000f04015036240583d19090500c04900076005003c49408682e071707803c3c0311001c80e130401101e110000315101ca9010800002e40780403148038000300f2a0b05000061940490344001c2c54010035244111110ba008941d1900403d400c105e23140c8400c44400326103000081014010175000303000c1d0310000c505d8420f00f41c60007912442247c4180d41400345c00038605071111000d40c41b51048641d506480b122604403440c02c0307215000180d605440003401c201c08a001e601c0c010a41035031f4204e00b1501188dc0050b2100c04420500140c0c206000b10701005a0003d030680f40c8035181c03845104028051a900c1d030400d04060203521420045200700340c0305020003c0181c400100302d0342594012040003402e60300c003c0070740e04410749141c40c480d00355 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 801523848 1250 801522598 801522637
    0x60307120f0b2103190305090d0309050c0d022d03010605090c040e180601060215091f0b010c050f0313120b0109020f0c03180307062a050c1c030e0406030308150303 72
    0x42e600d0b9001b2405460550141c0721020a801070482c1602e0460b04060a030b40c1000800302d403b071038060f10b001d442c1032000d0301c000005104000c8107207502003806010018a070b0001160481440d0a00c18400503200c211003034401c1c0d05020310721020354000c500030314400c0200080411032444c41840070b44d02c503008600c00c981e101c0d070b1142c42c02500c82c403421101611503560f250102d0a803400108401d42d01ea14111144a40d43c90f00f0b200c0c540207080c200c486117050296010103603010030410300c803040740c5100e450000c3d40c1e101606241c92644403980e5000c22041400c07020883c0c00168050724241c11101207440250310340000c1006030308030344903860004c00c1d0307880f00143c4d05030604030b40b03244020108001c0b01943c0b1050b540b40400c0d40c41752542c41e0420804143c800640141c4862040c6240115000b0030451b40f00320034500102d581c800c600024412081c04510b003d60401d94071002008040800f9076081c001c25142d56070103064060301402801c0744e0051005010140c3d1002c1040e54007171000c224141840707 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 801525098 1250 801523848 801523897
    0x607030309140a200616140115050f060a02030d02093c09101a07082106030115030323030a140615030c03040809060307120f0b2103 58
    0xc41442c00c07030464081010707807040c3c4458045005041503101003d40046d18040085000303003420f00c06198220780d0000c1000311205402c0007403007440241041ca640010100742000c2c100b10990320000001031290a0801600d816240d0100c02d17603086000fa580056290309501d03000400300c242010200003040081c11200400701c4407030500410646421250f200c62101071010f208000130100c0d19403102d40c924240400c050105901201015141400d0403400e00c510b580e90030704217030b11a00b490402c0d00000d080320759608080c50041030700300c5003c600810081100d0700f01c5a2440303100e880042c050040c0132000801c44070031001012412003203400029a82c1c90041d07240380c0207040d04000440501040800030b40c00f030801c2c5440e10328201e04080c0160840d40d980150507515440104200ca8100301440f407501152078200140d0702482c21500c4900480344002c02400c1210b002d000c030001c4c8039061502c4080c0ca516944004400d0010a81d1608412078008002070700d94820840245c45c04000c40c042c0c0c501c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 801526348 1250 801525098 801525103
    0x80913050610020a030e01050c0304050a0b04030510020702010c11031912021b0a1e080d080a0f05040c231305010521031602041d060a06080304060509060703030914 72
    0x704000455002c4201541000201c2c0d440d01202e00050100e580590000c40c198011009401e070103000d081101c0ca017a840320b01082c00315005500182c1c41c824041024410094107004403022844c1210b41181004020340000f81004404075004e000c520507906416801d072414022511100540e001860050340f42d494280510100d90320301d6070050040d51036449040c0404c0c40320030a5840018400081c41e1700b015104142d0b1040302036110031005c0445000104003a09000740c0120f603800d0b442d4484140340c40f11000301500c04411a504c81d4500d01400c00c400074044c5500e039820380f50903054074074500b00c2284110310001205c03039045502000100d240301f0600160740000303040c0c0300152030b203c45800803404070f0107600000340c50144654200f40f0001c00c0301607200d08000c81d8140018000f08251203580c0d0394030b54818100c0c9a4184640124040207100d10680c0a0103000f0800c1c5002107103042c0c40c050004200340110071038503100d446d0000b00c1805141c03103504480d01503508891158041040c1c03101099 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 801527598 1250 801526348 801526351
    0x4050709080c150714160e1b0c0a03081f0b25050a030c0201020705060a02060a06170709180b0906150906100c05010608190317012108091305 62
    0x801807007602c0071000d080c241142214844114500214100031865945800e507400700c1d0701d4203d05104418035030a10302490400d080040c0700700e1252080a05250030b0f101010400401e02c0d40300803008000c2c1080d0b598000607119803403601440e0104c41030715400031072440354803941440412800001d81c007141d62a0450010507003201481912031007610003201582c440c21121101070016008142c18601003801940520301d6a407052042c1d500954a450025541d81c110440c14070050344a00e08002e0842c542c0e1082d0009044800d0520b05510202000d42c3d66902040c010455140e4584a01940d5610350051103003440ea840340c10101f051512055080d6202c1080f50050a1002c010000c00c1050030005100c6d8002d45001e404001900c3c01001c041d41c05031101c03401100c0c2590384e00b40c002005801400a02a10b90204581a556003528200100419040314518000e980210010802c00798082c0c2601d82c0038000d111118122161810645881d019456510343c004214000c46103c05c1c1c22070f484a03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 801528848 1250 801527598 801527609
    0x110d03140a030b011106070504050613030501020d0204050f01020c0307300b1b090d06020c0a0c09051602070f05040c020f06010f0e0109090209041506031403031006021b010f0e04050709 81
    0xc0c902c800c0710039880e0343d540c0800d87e055804980c0411090006040404c02040c980c0c07510000708206030b42c2c036920705007203a02c040b0040c01d0701580420309006503d0700301318444460350244010f110004450300065190010b41c864090a000e94130250003c0071220f900c1d02c901400c8201c220611480710303041c00e0018200417984e24200b00d1444110381c801f01401016515501c8010b00040c0191103180c0e500402035100d20b003060728a101d590035800000351018040c0000c0c1508500101d4281410012603c01914200d054811740d00300390702c14005030040e071070b0701c1d01103410840340805c210841c56000c0e410400c51950b20115405a100081946080d00441c14101d410003580084560b03650710305078080b1114854002d5000b0042e402080110707004121090f4500f24a8000184440e90703075407403406512103210f07420742b5500048200010b10300801c2800005140364006003081186102d24140303c0c100c08103019052000c8030414507245031180c1e0034510300c964043c004001504020402403c19035851144 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 801530098 1250 801528848 801528857
    0x80a0b060f151b01150f1208070f060c0e06091c021f020606010e1206160912060501051003092607150b0f062b02130312020105070804110d03140a030b01 67
    0x1040031620070100329011540f48040340042541007221f6010620304045041e2030900302400420003080c2082100001244100e5002078035040400f0007520780c2c0a4044000c0c810070040c00300210710b03100c10a012004100f140210622840c01c0c1c170000c0e0b100c103d82e5110895103d00b0322408444207800141d03441c001c5409032106c03030340c11114008008bd00440810100c107030ba040a008100740503666410b00d20701400b10300b00540325545031f0940f840e601d02c08040581c0c10340c5e2503000401540c1401c0f08c40903031441280c6001c1c0304041c91034551140c804084210442c00c1410170440884803d0108255141b0907440429122401894100f01000c0d05000d60070b14803c1c5035030040d43c2035518016040300c00440a80e81d40502c0040d01c041d4023095103080c01346d07070705441f0340801401814042e4802c50f100614803a04031103814180e6481c000382181c42c004c044509000d6040b0500000c200e640b05040500c030001c07204001c4050710f52030308480d41d441300c0240d0030414030082405a003054054006030f00699007aa43e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 801531348 1250 801530098 801530111
    0x1050724090f0611070c2106020a0302040e01050604050604122a06110f0d0f03090b070f080a11040e04081b030405010315050a090e0321060901080a0b060f151b01 71
    0x25441e1311382c1304003003000744004c40003d0101300602548050701440510001d0181500302d0b55103454040c0e9024020342e40009500007003d0100c161030703200311400351000341c558904007414074001c00c0f00b6120781c0c01101034803070301e11001c00100b0802180255081ca014040124000324100d4045151101805100c000c80c0c00c00c0881140d090340001c071250100d40c100700500c13441011900c20341c0c0c610140e001c0d06c01019110700c400008907001a0b15180035100941c2c4a010415801070014001d08000c2e080340b41da41d0811038070f4000044482d06a8054950510051002c0e0300c0d10729001c0410b01c43e0880380340c510404c91171800c1007180044040e004803030b0284c07018012540c0744200c0b0644495075020b6954000c02307410091140c0001d5600c08001e800d044000c0b40e24040c002c01d1b1080503001800d44501c0700c44480170400065040c0060b2190050403442d0062240e000640c2e1001807042004054034003c1e8003074541790245544260600441020351241c255481ba42c91805821082400c1e8600ea0b1541c00c090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 801532598 1250 801531348 801531371
    0x206131511030702030a031d0306151203040608040204020f07020306191a090c0304081e0703020d080105010f180b04080102030a050601360e07020102070b01060503010501050724090f06 81
    0x2c1110140c55008018001d4490580d4080e2451494203402402018515122480c1502c0800c4a0b43c000e000300c141e82040b44800204101201c034080b00d541a454009000c100501900f102c4091b0300554112000768071001842c0704000310740107880d00030750f00d84100000d010131120791462050402e54101e005100c001d070300000344207030b054068120795040281440082e00e001c04120156400c1840fa5180301c0c9440b200c048002e00c5045e492001050803000082c0d00c10406404200d07500d2001d94508180c421981b6000000e0a045c001050440c1030100a00d440c60268220076407400c05400707541c20480e101da441d502c04078002d400c2150485a01d40c0381c07001050a40d80900c01041d01055248694085c4984000106003101458005134600321004203010a50110380f4841c40d1140c00315600041c3c6402c22401d1001350420184d2000040c82001c20050200e0b036408003c503003690740c001e0020034115645810aa050350898a5000325003072921645204000301602030100302405410b007440404082c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 801533848 1250 801532598 801532603
    0xc0c0204111c0e010f150f0501021209010e010c060f020d05090c09072105180d0e010909180b0403031b0206010e0f070c0b040b100621090206131511 65
    0x140d1151030b41000146082c900001d4000400c034545030800402c1e4440403840150603507089031810a0114242c600600ca01c0460039402c00040c8802d00c01000d4020800c0403002c0e06208101d941070400c1100a0501c10a034000c88001c8803c60b4030402c00c01004805040c004021340001862040d1a4202400304940c202c00040c0c14038a000000c02040f00360721070f143c05554803402c2c4641d014084949440145074200d10b48900c62080d10b943d0b40070f200c448107428949041603598070014051100724418455580da01264034020f41d540c00400144a200c408424959042208401010304610800700b00c201036254001d0700040c0d1501d81c001480f086ea10400760385624003405550003803900080001e02209242e0000c0c1d800445505003402e1409298503003031140041141d0561381d8402c0710062014407040710540000034a00d510b00000903644042c02503885031142049850035a440d240b0f60000d6544450449400c01020020a4441c5540f11002650350b400120ba04020030205040c002124401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 801535098 1250 801533848 801533857
    0xb0705130614030109201206100219020f03010e0615040b1c17041203110607020a0831030309090506090103030e0d0309050303070804090509031207080c09040c0c020411 74
    0x40e42e00d80d03411a030808090a000f440d84c0c0b00e801000200811180d188464030a00034030007a101071a000300c0d42d240c40d0080c04170104100340302d80d0465114403011940140d16098081e9210f604807008181154071600290140584140440041c0140d03000e200040c0d650741c40003461b1890a85050240b4060070f800c000c445e41a0a10102d021284031003060002056241444d0407584c0a41c070032400c003520348860510468140604401090000d155000840400c00000307900030802d00c01450b0000f100da5135003509000340c0080c032560304082450f800400d1101040c407245656400300d082c00851307503401c00428030542c91080c1085240f503c0f010441609010100c5416039030036495100c0c0c0030121506000c1c00d5840000309400b0080340c4d40d404141d40d030701400200b0f5128011141140c503142070441241c01c66802410405441d4010050000400c00d400b040c40e60000090800c14007568459580c84400d00c11180340340d038000e10707040388010016005403c03024024000c2d0350800035020f100003d800305109 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 801536348 1250 801535098 801535127
    0xa0b0301080d03050c1c02031009110f0c010f05070206070f020106051c1104020313140a05150a09230105060a0b090f030309060412260403030c020d0b07051306 70
    0x610400d030b1007507000c0c0c0c000a80064480388680e10b450054821610410080f0050304591074001081c88051b050100404024124400c0b080080c1020200044060300c40d2204408181c92b020915888141e401e510000300840013510511031841c020701c000351155022560b03540411000d9152f00d80c402e20500c10341050b500090404032520221115015090420600494042103210f0280f000303525203002441c040d003201040c51080d910a80740c2244503d0a500720f1a41316408107600d43d0200c1c100040c0c5004c1c1c550408001101a111440c440000d0038074924007901c1700408890741c80c0046000a102071410202c0402049a529141c0802980342c1c0b03d48503903d030301e290512070b0241c03614065103822451040182120f1410203160080344440d040740d80207060b10030361091540f08ac481800f00c41d03101c02e81c4078600810301201000752000a03001d0360201500300400c0ca0031441c1103441d154400c88445400100b0401d51749414035008009900148808880825807007001401ca0b005a46003455901e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 801537598 1250 801536348 801536353
    0x3060306040f02040906060b09130216020609031e1005281109030a0807110901060504090504080714210405150d0917130f0315050a0b0315060a0b030108 67
    0x200c942d2a209034500e040c402c2a40e000c1e0380c1c0c05a903400a011442900700412460124030b03118203600c0d04200f14600c0b29140c440c640d81c01040415010040200e4034080c1d207038129617254603001010f0101b4684500121001c0d0341c260615036a0300d4050001511034400d6402040910159847c46002e0050420f440ad10b0780001c117105079000e1460303509801480c106140303243d00509180c03200000900d440c1d107441058402c0d250001d070a500b0700424001480042d81d095916000651410600400034030840c840e002805a40310b001c01c00b040b00000071114070a40012001e02c17040c01300300e010f94a84880c0301e440c02c1906e10f41001040c9030108081510206e51b00241541d01c60149462031002d141c0c444546030901c3ca070764030b080e040004e41d041104c0c243c0e00166400d0b01d8640420714a00020720015070080a42038a0303050040000403003e52403011041032401d0b003c241c6850341c1041401034010100301c1075040c05044208641805000701701c904c50b8104840444031107a8444004d96984000e004508164 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 801538848 1250 801537598 801537601
    0xb070213110304020d15110d060e010b19021c110f0c0f060304020a03140d080906010f0b3714162003101e1a01120b040c0305010501080c03060306 64
    0x510303001085e8101640584031000c050b80c6415007003801c40d0903034060b0502501000c2503001e040c1115109e11005004000a05030465042c940302003080d00486443c124100c0c1094881d03040b661003481028090059030b00c00e0403080d41c04640c0504040100c0c80000040d10a9208900300c041c000100b0703690000e40038010922029012040c400d190340000c00c1640c0004003428000b0009000540a84043c0120405040d01000d46c500090020901400385841070b80454014491a0b180d01c1803107003151411240a0f0380c645989402d4540c2000000d041d8440c0d0400744480c0c60103080d0030304103c81101c030300d0340d035500000d4110883c03c26500036150b42c00c51351a401010740001841000c1001a00200d81544044042c04000000e142c0205040402c1029494820880b00078440d1416407003412031a000620510780710401100000351500b000302d04000d031104070b17549500d18661040080d4440076105005072201108090064070081c89a140003d03401c0d400600080400000c1e2030040c24010040c0405 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 801540098 1250 801538848 801538853
    0xb0a020904060503060108151e0703020a170709050102010608011103010b070c030b0a020d0b09040213020f09030114010501170408030a09031115090705061206100504030c0b070213110304 82
    0xa411411403a500a5611031011842d540c041084c1802045180014180c0030b40481d0048964034003d044094914201d42c00703006546030070b4a05e070394010107502c2c00680341c1880110890b005410800040c4d89a0900300900c0441d03a40711151409a0b5800c0c1c00030b00440c1d0ba9000482d08807280e400c101c034100c03413082c4014442c55010700010181503020b0891185c1040c1c494888130744d4014142d0744406802c3c2d000821404900030b60180200d1079504494140c01d80c0742079004200c0c0310762701c01503600100307500041000807180384034280c0d088036174054020401980440203103101c0c04001c0c060796001c64048540040c6200150082e5840b85500c21246401e40e1146440d500180926240031424400c041e80300045213003041008107192480100d48002c503040c80d00e149030038040e1a0300854050f1030104000d8005031100704c001a00507105881c5d122074542030039401c0f20b181c00b4541001302242590900050359249200142120b22700842c0c0c04c1c0392420760a41c91030101e44050305134240c41d05040c40000c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 801541348 1250 801540098 801540101
    0xb01060207080c12070f0f0f0501171501110a061a0303040b0f030703021e0304020a05040213140307080a052104181806020301121e0209400219030b0a 66
    0x100e103403002258103490715140741b070042d101c1e25001901c40390b09118003000b01d4a0015040380050000707013800c915189121820000800c8014145000840907900b80e54440c0d01c0f80709404407a40804090f680da610951802c4406401500311903141400c2400e452940c0340b0b001700c100d50888404074002d51038094400200025908001c102c8000e01d9400d0000b0084200c6100c0b103001a00d413a80131559681c60300c0d00c10881d158a5031380115010300e00c1400075021f86120500b01c0f8064034440c00250400501c9240020326040d281e410031070700760040c5910282007210004d600080341c280c0c101d40e808050241015008180240d01c1044050200328660500c407030340a038440d003520b40000b06a807241c0c801d40d4985034183d80c03084c5c0c000443c448000c141c01c0c090080305003134100000c0740c0b09500044010190006003412201610580160704406107000d00444082c5591849211601580c0c0840b80785508610305d581c5180c5e005d80c02400f06d00c1e80c40070003a80140c031440580340e00680540700c0b40c494556000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 801542598 1250 801541348 801541369
    0x605040c1e170423010506060405130e010240030b0601030902030a26030907140105160c2d06183503070b010b0313020405040f0b01060207080c 63
    0xd022034415180101802c0b24100c600c624060920348482c9100300403500b0704a140c0502d100304991500d0305001c456500d1504440445000321082242c17841422800ca0040160080780d10103584009811000c88094000305101120301141400300411210051803040f16050040002c1a24a103c14000141100c401e60b401c800b06141c00124109203a000c24944001c1e0882601c0e00c440f00c0ca00141c02c030440440c000b0b60030081018140c00e50908c42c90243e40d80007035000d600e80400722042c030b9021071f92141007503801d04500c41c90460061200c5c3d050120b15404a4018000d02c107201c9400c00b40c00310131203c0101d801e03440341071807082c0143c5480400c6503481440b4a48140510744004005204400940007140b8040e178071034810410a041c0d0411400004808100d031690f8009109840c04112004140c9045880c00200305a9990350b406c4014541641c1c03060080d41b084c0340400f800140200c40711860328003840f91031403e03401c1c1d0300c1d402c0c00c1e070f41c840030351107038641d00d83c419441007007581804c042c1d14 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 801543848 1250 801542598 801542657
    0x110103051e1f060f14030402010c02130609050f09100b0a18060e1003030203040e1306060b0a020c0303090f150408010c02030315010311090103051e1303030605040c 72
    0x1c0a60541e0103254040c0c0000c16102694401d866465800411000088020051215090010748407455080140c4040146808080159004070004040d64060a03080c0704650f4000d003001d040e055401002c5d0000c5c2450b000f501d81e06c6e0310f0f10000884000f0f0342c5a91501076103d1600601400c05401c06083c09803010b0fa1029410160800c40001c05d2004c0180e00d1081030840b40010a2050030810308a8190000500203847c40c0c440140410202e03801004a030184c0d001e00d08503100359518941300c51303107100c4500c800505982ca4004001190000c59019104c00f412550a941300d189801d010196a409055811030707000015929000051600141c5511005600c00016041a90300c089440c2107902c100d40840245e0000410005031081c0f203152440704150908080000c0440504c1e8055a8050307a41380714180b40d556000b24003a46403d0101b803805007103540401c00389141042030710413211900e42048000c613050001c042001d107014010f144000c001a603824213181020200c405d142c00c0c1903600d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 801545098 1250 801543848 801543871
    0x7090c121505091e06030705010c0311160905091510140d0f0f020321031602030d0e03300619120305120f0f012d090f0605030a11010305 60
    0x2d4a900d8414019114107100f405400c2030004610b1010030341140200020b200c2e0304200d20a00c5a60f8020074440040c82c1c152a00e0f00b148079403034101030310b032250401013200e40e10342ca8280010b20030344580000b841241080706846d0290703641c00e039600d10705405592514031710070491004d1000c08039051410b600da8900a10400004409442d460b080402c3e0702026903580041006000541c102000400400d005000604507902003c6061158130f00001d040b4580e0b50180c503001e052160b200300141c80080c5070900040080343c1283c820165254403680b050642d000c1d07001e400281d10100303000c48c1e02c035443ea000100c0e6641c0e5030384410081c0714034403c80c40c1d622400a04502040303281145038201c1c6060700c0b0343c5071142d450b411245444020b0754014030209042215070104202e03440780c0b0704900d04441c00c1d01d01c001d560343e003442941440d8458403d8028814060300400049a80f03198005100c1c101007514104a2607464038185900c1d00042280039002811005034070b101e0f54401da0100d035000d00b601d1344 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 801546348 1250 801545098 801545141
    0x507020612060907020303070f0e2701050108070e090a0c09080f01090b060d03020a11040e0d02030403060c02030304051218060a120515030706180e090d0207090c12 72
    0x140180d004010a0703a08060030300100112800c0c5040305a0304a4500d000031030551034001d000801d9100c00815400c108445c1201c0c6a6443e01c601014090441c1d282600d850701309019080e04030185801d10407140040d000c0c0b0040340d0014010b030b21212018101900810060340c45400d0031001c0c00c0d0000001e01004118100081c0f00402400315601308056200041803118085c20706441d22070010b44151300c02d030460380b10a07001039000544400c5084e4001450007520781c0c2400000d00600e000d81d80d07202d840c05000c3e01019040e03404070082060b07074442c5000700841c80000704200e03528001242e004090340d00c540a002c1e00035042c000545400d250080710060020700d0100030440301d030001d40b1060701245c181000ca09051b04507010f40c9500c00c584801601d00840c040c00001e5a034405841400c040c0101002c51080c1311082d1245100545240f03400c94409003410420325660345442046d80c1c0060203035400220f00045140581c180000d030035a1220804e00d060b1440c5c9008184509408460060501 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 801547598 1250 801546348 801546353
    0x2030c1c200709020a080405070b130e07140d0608150115080c1606141302060405040e0f0703121e0f0f0c02131e020403080d09030908070e1e04030e100507 68
    0x51180030611391b1080a5802d0925020345050305a81082032a01014031208821100249140049072086180e402468a60503c1601c4014840b0041c02a00d02d0020b91180c0b44212030300000c049900060803135998020361264810080001c5c015030700c4060180105003140d030300c501411394002c000d01600307a24209500704c0d01c81004040300b034200e5100383c581c440c40814400c403015031035100c50760203211001c164555001a07054400c0b4000d0034400c2d6070782c07404080b1070002000007024044103a0100c8984c6912810030f8800c0d90350490340c080020304051350381c1c3c40040603002d500c048011241c071403c004413400c040070385210748001001d070104105600d0800159031481d8120003116036591000134810300280300100c2c3c01036801070001d0741900400c402c00c00220540120f8201442c20341c0002070700c0000e89002c64404007150f2004200d44103889001c5086504502c4550203005668207020f4160b039007000b20003181101b154040e022540d407079580115410102c480303249500c2e4030701c2c1451403c4a03d6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 801548848 1250 801547598 801547601
    0x1b120106080f0112170f0c060a060e07020307051f020c0d03090615060813110a0303030b0307050a14120c06040b09030705030106120f031b0302030c1c200709 69
    0x99001400050461082c0420718504121043c05040054100c001c07401c03641d211400640684099500340c46000980c00d829502c8080540d1506040c20060300c840303007089905e03000500450300504951030f8500c0d0101c3c081a00000407103903da6030210150080003840ca00511600c2c1281d22074804854080100d512001024040d40c0d285150780e48000416650f1410444d0480305203031f40c1414440c4141c5801d0140340e400110320340d800108000c00c48081621841d141c00100c0c04007603855041138058902000b0960150003a141d0174500340d0454040340e0b9180100442c100711481521507008004540100d0350500c041441003d400c19011215040044008120164810f904c01a43d03501c010590399002c1c03a05004c65001010200c2c000e0202c2803c0580442c100303c550180200010800d110303000406000307e165a034822251801c02d82d480600742000780d1660b1119903d018613010382c0301c800f01030817204241e5640c407903080da4800f42100c0d402c21741071490b2401d0b2110100c2a101340b150020391010765 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 801550098 1250 801548848 801548851
    0x9091302010c2a09050c0f03040f050a050a060b06070f06020901091a130b0c1915020301240807051b010b1906120e120f090d1211060c031b12 62
    0x25840c2c1e103081440f03c003814a805419400010655040105008850b041c0e2000d0725000003541c905659251142d1405503515423603064000c0160181ca03e041050010204044180d140a4230042c805804a001080b00714410004010250720071100c0c40c0c00030611a034042c0101c03407c1070609007000c940b15250070080420072540d41681100c00501040b1106990400e40c0090403c030013101d060040202071152155000e2005171003050519042d1418402075004821540034000b400315540d50f11080b2428140d11016080c0104030f1504400c0d1448503c0381d0040d9200da54907954044c02c000062008049040000500000b1036407500004581c03075503404081000e40401030b041c2d1000070b180010203480a003907010303a4210356181c2007a820203081d0100c0c0030720f68015803480707403941d07150a800c5041d4540642590b440e00700c0c0d014038450041000d6111030059450a90301c0700c002034401e140f103083c2e441c181101c3d20100390f0b6060000c180041319421000d041110054051400c0005412002c0004c100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 801551348 1250 801550098 801550133
    0x26070c0f0b0106030e010204151b0b0c1e09030c150c0105090604050708070f0302040510090c230405060f030406020f0f03251e090803040602010f060b09091302010c 72
    0x74000410207140c15100309104200c00d034009505080c0f800d01000e1402c043c1c04000c1d0300744884100000308000c4170714501e1405d16404280d900a9041668001d1380725001031100310300c0d824444c0f44103a100d605030400d0340c55189001300109680101c06003480032041042846000740349017801000c030300800a000700ba1250440c000107042c1c5250a00b012840c181c5664040c516070b4004810034000c0d9003824610106482d01a9800310b1281c86408040c00c801e64594840c110310341c0b070704d4081c2d41c225601c003c2082d603085000030024645184c0720b925840034440c502c110b55100030f0400c102031101144001466101d80500302c0142408007808001d005070780b15080c061480500001080303594075815600d1291400309000f880c4202101d035402801a03180c01e24060012001622054007071031048417407502501c0c0c828196900c0d1a43c60802074040d000200d403446000b41003800220302c25001c0c0040da10f00203001007a084ea1a00e858092001003401294141d0401c04440d1040010030000f82850301c0018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 801552598 1250 801551348 801551363
    0x170919050c0418110906061602062808160f030f0207080a08010906060903081803011b0504030c052b0f0c03080c01180b15190303021c26070c0f 63
    0xc03c0c600d400c03d0150100c030585849190f4034014001320f503c40e80259000c2d10703240c1624050903100750002602c0c500401c40c2c201c2c107034958004c0048100b100d080d441c480744102e54032140f00d680c481105084060381900d015030002001100c00140040c860307049801c841100420041c905000340d101c080341580074900c08400b1800071030041000700c05078400c4e440200b68515100300c0007415503441c0d40c05403040c000300c101d01314641484500c203964203600c26220f44940c4988001d81c505003100c003902c07a402c5840255582059024002054104000048210070511480a03480f01c440850020440307124802540c0c075080310b14030300000a4101001034061405401c03800c0d2904a40d00840f0b0940717442d8948210154640072603507000404110443d500031402c20094030303031211b50717001240420004100840615415860010500d0307001304511903100d1300985003c144030780001017507800b49400503c2d40b0b440c4600450012410400030101504600b070f5140450b0605840e458060b040c41c1503074400c0c1c1b600c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 801553848 1250 801552598 801552641
    0x6101a0a09030606120515040b0604090206091f030617100518030a0509040e0307030e1002030903190b011e151214191817070209070206040201170919050c04 69
    0xf046c10481d90900c4008440f0700b604c0c910b0303d60388440070480080c016034015034907600e008045644078001d031541c140d0040d183d4040980130f010041c1510490315201d0307010030700d00741c1e01045111055020307504c05c043c058001c10742c00c0b000e001c209005000c02001d80d4100d050303c5824410240d42440101307036659495a9260310740c0c641c4030400c02101c03814180190b80b54420045000060b400000000800c40106d454030b24092580d10b0590840c4030b0400c005030300d4052a14680d2080d28070001c8958040c3c0200840d0307515a1b20f80380441055010010320445102103503034100410105c241103125840300030b2030301c02c24440d8900142d0007038420f0f201d40b02800710341250400c07501d2840c007641078003001a62a000c1c80703800c03007110b5072000f4441c1c2503501400d2112044030a03111440b21008940761158060242d003100e10f8480750094861006880403400181543d6111400058981405015000c2d00002c0c2604551052203400b101d40006005c407010f01a030510b10a0941d0b03075100b205c0d4041d50410042012 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 801555098 1250 801553848 801553853
    0xf150d0506040b16080411060c0d0306031b051318151e020406050702090a090b0f070e01080708010509040f0206130503010b100c0308070905040203041406101a0a0903060612 76
    0x2c01400901001264015007402101341c2e504c0699543c20541003102150003025800101e030091098032a40007a80c1b00d0706d480080e046606038442c5080307a01400141c00070952080321403201d0442c5205055025038150400075075070700168000d41621030504a2f407841004070381d5544c41e40700c418100214400d503640000744400c540312580f0380c14113071003020110f1402e81851000f40807400f550001a00551141e4001004403034942d0040110f1034208056086a01e4405400386103214200c0c0c5420011b07103042000b2816501840c1c0c0e140c0200c010f62507000840e8200741c280245150001c2c400d0300c650720b09451400c05602e42030010105c0e001d058901c510900e00304000d0600b9103048035041d6001d01034103420107880f40e5200b607805100550518020045031141481194818051b4002c154054400010f100c100700f9040f896007106a1410251010380d03903414a038111001c1640f180f440402850071080e00a035071042c00529600031242020341019489031102021100560011205180d40c480340805 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 801556348 1250 801555098 801555113
    0x515120717070201060f06051e0c0d0f05030c030a05070c02102a2d060f0504170c1506120106090b0a150e04020f09090723040e0f150d050604 62
    0x5002c1d40310300003800000e1030540c10000c8101e46100b88010050b001c141045036145820b070500400f99403041e0607490745e605081d01c3d901c0740030750620031020402d101122003420f40940240da10510141a900b400d60b950010000040c2c800245a1000c010300703980b1000059403040b00c405c0d51a03050382c2d02e001d016502e0302c0c825445035030364101482641b0000b80071280060300048901c15110a0608050b101c6d4181d819401800c940d8003078020280790820000c00002aa1070744804d203c1e501880c4001c802c4c54080c1e8010a8074400d0110040740c98000d60000401d03c2d00402aa0750442d1020300410084640c4805031800c580341504a4003140d0745402811495150100b907000c068010b848540c4184996002e0240030204c98013612070040390080344420309031b20208280e45104d00d014040b2211071a1000005042c42c80c404010f220741d109420005e101d00700c45405450988030b4003200c0c0421901c403082031061148008110000c042454408031640e40c032659201400544141d0040c001c600b440e181040c2d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 801557598 1250 801556348 801556351
    0x5041406130f1104060f080109050d0f051e2205040f23070509090705190212070f1106071a0a09020f01180801050903040317070b010515120717 63
    0x30740c403502a0280c00082068800064000c65110403049846030481c0c000c039020700316641c040c01100d9002d0800003141a010340281c2c0c901c0c4e00c030b0010f80d100ca00d8158819110590140300020000f42c0601940d0764004220341041c00100b441040316040442c6690000d009013011000c42d0090300e000802081181846c0c00703103440b81c280d0f0780c03c24443d080d05000c0800311400c65940b500940c844030808039000d140244121160300c480607200b03080518010b100544a0b40c4613903440b404519070005e01c0c0c0c441074804541c451142e61603c00e02850008a510391051400c0d6201064440034560780b5007144590300e81d402030524610801a840f40928200c3c20384542041c000c0107000154109075500005a403405c2c402800c20609003400f58681c6881107003801144120b41002c1c1ca19031819050011640d4000060022070b44140c4d030355075102004c031079562454064068001d2140c2c203002c0050000c2d2406c0311007207001019400b016070500c4180c1501810610058504e0b134041016121038684584d030900206 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 801558848 1250 801557598 801557611
    0x311010509071e1409071e0c030215010303140a18150807050f0301030609080d060603050621060604050903130b071109040f243b0607030b01090905041406 68
    0x40040c9410100545031080c00e613850710404403640042c1500f80502c41034a0f1002e20842e0b01480c3c103040300303809046418031080071707400361042c80311020f12041010070042c141c80d4566501d400030b002d03000d852100b135000044400117200032549015003e078000344005004202904101380501802ca0014000312401307444101008020004244030000d210126411660310000005049456040c0215a4021a869000841d080c004002040765050700210301071a0100c440540c001e00c03012245030001018a0310039044e07046240081c0342c40c0751036404540d05c034403410b09a0f0301e481d241d980d2401000b40e25402681030124082a12020720034646482410202c0545d00780c903060405444002c000850100024180c4206444030301d480000e424171480695a050300a2200c1d104850395043c070220085000e10843c007600c0c0d11000d0f0380b01440d007e40d1002460201403c0d19071600003080703015142c044101418070110030740004030000c1e05e05c1136520460041106029401d02405080d0600c440036141 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 801560098 1250 801558848 801558899
    0x303030c020727060b03130210020a1109062e0909061d15060a0804120516080a0203070b0f2509090f0e030406050a030b0a061704031101050907 63
    0x1032120446070b114440e49461129201c0615482442e2801c024141300e801585000034040b062107d1650700c00500e030741c41803080f2250000b0a03107400d022030742c0e2920380c0300181c00b0350040c00180d0b0f010704101c00000d4200d01e0241c181101c070110030b140c101c1030600402200501d8101c07000682d00c401d0380081c81c40d0181100d1b07075051006a28114030515045a981c00704080300d4030720000f049000c0d910020102508002038000c82e00c0c0e4250030400303070041100700d80036540480c0c02141414100e03c034104490840c86442c00054001d80aa155160141c008041d8641548401c000090124107245541da04c5148100c0450320140303025440c0c540009240b0b8206000d40c216944807a00d4250407220035010703030741640c20000344014401c40540203800a6494002a0f0000050204e141540000280010407960b00d00b03201440724502032180c21403052052a00054490240701407503c04402c1c3c441d0014020310309520140400001a42110700950301c0f03e00c41d502642d800c0016401000c840e03251007400010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 801561348 1250 801560098 801560113
    0xf0c060c0702131d0f03040e010b0f04180902030109121106070504090207020a1d07110f10051504151707050d030c0203030705030412140109051c140d060303030c02 72
    0x30a0180f2840c025101c21035413130740c440720708104050403400031842424084030710a6200034006500d0764001d019090160010000100b9500307050030443d6100e8030b140d554113203828031b0000b613811080040c2075039500c2c40303441c2c080d00070142c0d809020707056059005043c2c0f400c05036104100981500d04c2d101a80c2001d400c034404006a1030b40160a80c1c00320741c10004050390b905ca00d880041c0e04507640b5044400c465200c204201c10416491b0f800b90321808107500d842e0783e42000320013032076a60410f5054220b01d0781d0202d8142030ba5610715800454001100801407010340ea58800042c040e901e09100300c0716000210780040107040c001c4001042c110050401919502e410174000c01c03507069800744003806000403014240110b443c204222545544c01c0810380e0384950704d40c14038549845106500761025030101c86043d00915061295481540d405002401001400340440b13499014503601e80090080161010340c035600304170005d00c40d54a031500300054550640c50042e007110f030380070040c0c42103500c05403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 801562598 1250 801561348 801561353
    0x50a030f230303070306171b1801030507050406051c020607060b0303070302010507020c01181e08120a030c0906050d0e0c0d0b0f1008060106112a0f010221030a110f0c060c07 76
    0x84085941500b0341201642c88e058001103140c1d0030504100c200d4011211000005100000c40c1140039544201d600b2b010613681e078400c100e40c080d000000158084c030204190001841c10900604110f0f10504e4042802d04120000034150303085140d0950150351918104122998184a2070710605401d013020044c0104950142140380c03802c2c041c2c1c0d264541204140350b40040400220f00050110404071445003c0c1e01f4548141600182d240d0400310741803400303507810a4017641c119819202641c1d0f419042291341140000035182010307081d211802512078284c00d40d100c008003c41c45c2c0d030140038406100c1c01c08210001a00030003c1c054418880810028085c1c0301c00402d660741128180c2c038003e05000320015100d41003803c4144041d11103001a18031510500d0701c517400e02480755045400100c244140720040e41c440240141d18000341003181d24044655822102458204e0901440081c908154202c130301c81c640d000c00130f00e52240c00c01007051010780d20100100f41d4001052802c2ca070500f82c560707 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 801563848 1250 801562598 801562603
    0x170112030e060f0417060109060e06010c110907020a0b062709010f061212022107030207260d020d020c040b0d0b270106050a030f23030307030617 64
    0x121001800c019100600011559480007a6042440b003020b049036241d40d01c810f05210300d05c00903140c3c50b05004407400005d0f84452403146c0b0040398407409107500d06a07203007801100c445081c941d0032207045070388000f80d075882c1d2582c60441d8400d1802e80c0052030303d41c2c1c6c0c07410010140c4a004207224454800314440140140802a204480c080d4045855581d80c41e06081030780900b01d503213030950645280500002d2084c20944c00d06070028014040d041c10284101d2040b40c4651800c01c031402410b002108191203071600400400c0d459002e881601c4a03540c0b20844500b4541c44280e00c40c1c6c003c0c18110b101c0705c2c064403d0110326081407041c002041c5600382c1c5840030f9280c01203200214461541d852554010b51201d410300d003012130340004240b00c146171071406071144e4002254203001840c444032070712000074014403d030741c07c2e514000c1501c1c1c0a40c0c610b5503038040560180a0407180c40b1030050702c00c0440b110084800e03205440400103191245030058004040f500658090141605100c004d01c0015102 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 801565098 1250 801563848 801563879
    0x20c12190c120308040b0a0b010f05090301020d020c030912160b1e070609030e12031c0b03030a02011e050c030a0e010b030a03050301080106050d081c1d0d1701 70
    0x34800144640c40034203000109141aa2044200100c0703808160100343d8400022807095128001a010319100e4210074000c5503401074429004ca10034086580070503000344007501c004040100094074146e941050b140030381c1c0000081000c181d0000c10702454a15001c5485844845440010110116000c8031004090303000d1296400003200002c4403c0108036040004044462941c89282d0701c625601d401c00040c100c50038140c0000d8100d8203e4500762a240c00c5560030305807000700030740c20300303291500f611114801501024a81a41d4002c01400da131001e102800c5141d04a80000a10904c129941c0340c0c1100102c0e45450b8080c038083c20408902c86241c01d40c2e4022152120000d6003900c0241410b00500140b1022607140c0700d1201e601041652000046058601c1400280a02952075061000e85031101c0e100400d0f1500138424065966800349007030189405140d4082484552040c0c0c2c05600010072580e81c1c03050300100780b641c441517000070034181c04103144401149250300d0112510b00c01180b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 801566348 1250 801565098 801565123
    0xe0a0b04050f150906340203041203080a050c0309070605030c0702040603030804060e0601150e01212c03030727090c0206090c0f041505180103030801090b03060402043207020c12 78
    0x11071b0104044161080055070040c01d2801e41d00a1a04000d04020308051411284d951280e4101000100140300d008180d82c080d040d0a801070101600340300040d95243c0006150000d559418442400540d40c1d501443c4000c500035100c000e00ca0806052170826550052891480d07984603100400401d00034051440e00003c082c0340c04040e40c0000001295001254651500b51800540d4101d40710f5400e40e1000042d020f50b1010040030342c0b21a605908003803418403041200750010b000069280d805522911a5100e809146260324070700d001001c0c0407203800b81c2107072000550b1340c21520b403c683c0411007250000441001015099601000502080e040d104818011502e80c2c000381101c80c0c1030403205014042c01400a244000c1e2042202c0c0c08c51800d102c2900051500750000503445810311403000800e0024024001958446d02440081c1c40042c80340c0e8054000280170f400c0c41e1a00e0b0701d02590384601d840c0b140240f406c2c076510083c41d006003059030510039902c2c911020040c500000d240441240c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 801567598 1250 801566348 801566431
    0x622021216180c0306030206071704030c081e01090b0610050c010207050f062206090206120403020706020d0908100b01090512060a0f0e0a0b04050f150906 68
    0x50303811a0505040c400a14410a0201e91001003201014185400c03092804090700704202c2c000340c0021002d5030078501c000b03504210204191400301d00210840003000002d0003103549850713944c1c0d03a500e4070702d080c42d442800550800c203485260100000510402c0d81c0c40400240080003085d02c40440c8041c0143c0501c0c85100c80800c02c1300c103c0d020701c0907924803943c544000c43d2108803070301702a9200d1b40d02c000c0310f200354000c1c0800a10b40100403c6d035482d690910808000d000305003136a50000404000c401664851020b00034142d40d20090030070103105600c01d0f8041d054003450100007074030746600900f110b41401445003041c000d000300024100070034400c2090104a840031000180c3e4198615041250004101c0000344000030300010914082c1040c1c038010410380c86503000507400ca80d200180c24441c1c0d0404d03004ca5010070b5400d4502500140140192100101000308081c50207005621020100c10588208500c002080c425668480f00304030100d01404ac1420140f49031690300d10801c141c05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 801568848 1250 801567598 801567619
    0xc1e0406050d0e0f011d0d03060b041a12040615171b120a0812010608062112180a1403031e040305100204090c02070303020d230f030108062202 63
    0x240c00811030403460036071000c0200400d050749020180c480c5001c0410302c0d298841d108900ca0307c00d10034810b81c412605558407560802c0e0034400a50007094080c08117103030490f000d00c818140401e103048068080d41c8645800181c651034050403d0303000c04103078480d200100300003850031940c180105814440c000d1542040300c00841074000280340000020700c445403071007004201e07010821044020505180b00ca141c0c102c1c586e81e0707400100d4107180201c805c140c10842c0c0c400a00700b00c0040d5011800f00a4111f825a8004040c0c1c00b214403032030700401559128a022207001211a0511582d0b00000d08200300e0030082150344040401c6e42c3c0d1103112515030001f40b2503590f50040328540b00981e030155070710005a407101562038a041c4080d41050242031400c0740f801c1491540c0c0c90002034030a080302c1c0d154014080c20303021090160f0b44590b0319400c03112900c00810f11a0700956105000b0203c170b40100040b90f481c4e5040c02c1071640b800500609070740c01c4410f46901050400c42c5414080321036541115004080c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 801570098 1250 801568848 801568871
    0x20403210e0f011413030c1202030610032f0909100612020a1a1c0603110f09010605090a03080d05010812160204050720071701020f030a1109090c1e0406050d 69
    0x30171660340082c042d141443d0002c5052407680300c025142c98000c40499181745c482c080000600041c0d0701c4002d1084102d0480200c460440b0b5400041122a005100c680460200e010a400c1d80c0212030542268020590164400040d4890100035006030415162070708000c3e4007080c040c050340d01883c001c0080843c240f00e081d420300c0007242c40399580b240b070020f405010303201c840000d08890f0000326400c01c01440690b240342040050100c010a00810039543d69282c00020340345907026400712500302361039010102c08500e040008002203041c030240058950701d030042190400300344940303602030355404003e0705002c0400318a5000c11150102c40c001110b407918502a80c40c80d80c000f0104405d5032900c01c40b56140b84012881c50212a58440055011486d102509080f489681784119601c82c080c800300300140110740c0100200411407184030f15008007800081c011580c11140c0311030b0281c2c00a590740709003142d111280802c0c003404d41098203003410182c2c0600780d402007800c00760425070340c0d05400c0d00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 801571348 1250 801570098 801570127
    0x90112021b0a14010f11031305010612050303011410021e24040c090b1018030b0c03150a050d0303020d060e0c04030302010b12120d020403210e0f0114 66
    0x154800001e0441e25501d00c14a0202d01a041001da5618154a0800c120003140c40502500ca48014801c841c0303451541d4078000520151244102940e4543da14140450b50000800001c00340d10b004100540e00c030761404c0c0c2080c10030111040154001c0050b600005011600056440e18100d1300240144181c0001d40e4580d00d003810309140075100100b131400425840c40d800760014022030052400c01c460f2922654603405460701c900c4115000510140d403d9040382c400c0003500c07032744108204040551942c80d1940710399036506803880a5108400002d0001e011a54101c145c01120155003080040d0701e13010001f40f007011820405000e25400103541c007a0343d210f542c425000340c02c44401500030b41c244059400c002c0d82050100f10003641c43c0c40c0396031307465207003514004000084000040a4250309000c820390950000d100c0d405280d0f400380400300008100c081442e00c011110051a40075138503401c0004c1174940303600d540c00d0103a001030b0394529060b68007450f00e1020301010742006642e0106041c1da0754 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 801572598 1250 801571348 801571387
    0x1140f1506031302040f0b06041403120c030a0f080c0703050f0c1002040510080412031805010507020d0f0f021209010e040504050a110a060203030411060403060c11010c0509011202 79
    0x940c045000010030078050403c0c1d048040040c020340b4204202207031502d440c4201c5e10740c96170290f80098244002c101c00e0030309500111302207402030152154500003100d4241d041d0003001c00d484a54002040011506a01c00c0146041865a14003140b89040603080e0070514401c2010141c1002400100314042c28008400c441800030540104ca011080320312042c1d000307400a0156a10410480758000e42e00ea1080984034001c1e50020120b010b84441e00005400400c0c0030451640d500004d03541d4640031a1080c802d0a214000710340140582032031040c00104081b2071120040c06100180c00101d941503400251a607a81a102e600c007941c911203140180c2e0032030592010554028107102c01c100401c0008602103d42c58450348031401000e50160070021940c95a005640041e841400004c01240c01020b01c0a0982c00142216150640f42d445840c1910385207629400407450b0840c522070f20719424440c2c644202050f02d05035092104110001780712000c0f505440a4a0760040740c0020804000c0d00480f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 801573848 1250 801572598 801572641
    0x203030f280c0f110913110627010e090c12060411090d140f07050307080c0108070806180c030708090102042913060f030c0c0b060108040f05101d01140f 67
    0x15146ca00f408503084403901158041303411503041c4801030307901c0c1808000d560a0100a41100400c807030160548030022426000040c1000184584100d25445072003800340900740c490301e1b09030f940c0c50801c030170117066501810700d9004600d818040488d070f9541009407490014100d5640071a0800d41c00c0000340545490112291800344101401040700c3c0080c201c01100d0058059540c405c0d65001442c1d1910305900401e400300741c0000000d00d20320b00ca0074003070343d01031002440d203c0c1d1000400000b6109084c1100c009000b07001c0003040c0844140c2242c20107501100f6000294a05030030403541742081362041c0d40503410003100944c2c03101c5031002c49095485101d02051408800e40e0b460300010700003146404883c0200340703406203941e0340c50f01c40c41c01030749410f0f001500c89145465240046039100001002942c2c0c004080c0c0390800010780030310958a000c04024008a40000310f1a0800050b025411030318000741e150000100e03071041f9030721509500140311550080315a4503851a58503207072001404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 801575098 1250 801573848 801573859
    0x60c18100905062d130b0d020c0102040b03190b060a0309170d15060903120c050a05070f090e010204031a090a1b060f020613061104030203030f280c0f11 67
    0x105001c0281c0340110b90351100030485543c4541400605801035104103205c2c0c0d040c5118601083c80900145402840241170740d220040c40d11602c01c41190032031700302d900440400364000052000d8411103d1800c0101c010030b400400c9688081c41c0041d01601c43c103001402496294880b4405200c1c403502e411a02d00b1603144a642e940d10b0084260004003900103940808c00600e40d0049941445a8600001d0765848030b41e0220b0380c81c52007419518480c0b043c6049540e8032980300303104005001480700ca4010b101014a990904c0c0c103140d03081041e070b011042015290ba02c14802000450032440c902c4030710042074078550320242c85085000741480103640c8082c0c4513400d06030b1003443c40074101e05d422044072229500e00f11000401c4ca001c1b41c4591040c0d03006031040c541070002d00c0108070b150b031013000400c0c00710041600c0c041c0c0d80d42c0440d086422100e15004c5800000c40c0c0b80f00070021884003046074000c1e8078512100170780700c108003516001030300001400d880d0400c00c920f0200501c01c03034000043c0303200030300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 801576348 1250 801575098 801575107
    0x72c010306060504180c0303030911060a020c1203182701060504244e14010803030708100e0a0e1501050f0105031521060c1810090506 59
    0x6142020b00309a1140f41e015501c0d0001c4000040c0e503d15091051a80c02013000c1c51462958070218060400c80d102030f0b90b440c6003400c02004540d5203200034841a48a03802a0044c10030190401c80e40b808500102100c90300100010305400f110385080104505049070030905490700501500c200112800f107038003075202c80c1c200109540e0b0700071002c3d008490384001080c0025800320505048006006002c4d4003054240300005a01e03100c2100c40ca02042e8004030303070300c1e00c0041c1c800400a8016541d2103d02c4000355080304034050111402543ca143d40502003c00c100d52400841599901c0001c01b07000c01c003c002e42c049500d011401d11003000030141001d030381c0242c0c01c041d181c04004150202e402075440c070850002511121030296841d048400040c02020041d1207a001505c59a0000b01380d0f8100518420b1075000c141e80d10841c0d0040d042e400309103001c403590040300c41c0741307401c0e4058205090f46209100c1480440c0c2c050742150f01c0c9800a4407800e40d00c1500c584107840b01c00150f000140c0c005400f0030b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 801577598 1250 801576348 801576353
    0x18041b1503150b040320060f030f040303110301150908011104180f020f04140a0501020d120f0903171e0a0207020f03070b03190b06070f0c1203020a060501090c02072c0103 75
    0x801820300400d03217006c0711011541d0208000d014454030440c81d60050742400065440e421012a0b140c0c014001e007070201e440c401c200d441000e00d03482600310258000c005070411364156032010050b0b014001d094001c011000c0c811010342a240102e1003a94803501e05902036080c0103050790030098400100031410b540303c00c4046446501030b0024010080303414a00b240d0b100b254034101310000102d0320306030090a43c140321a2002c89006122071034405410303840303406a01e13079060a4824900414001e40e2070240c088800d0880352601607014014901581d42e81011280340b458200820303810042c00d140c0166a07010b00c0c80030625000f03400340c03603646c580141d030000100c400ca84d0008510440d5190584411040c0700c80c003001c120307080380349640c0d0012000e100040008040c00c4030b10486a003da41c0d441c8a0b1030342c89220700003107840c003c000c400503001070508604210711400b0360341c050301401d0402d0080305106000203582c0c032103a220350954840007a070403201252604400d010010284680c0c09030b10343e10b030f0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 801578848 1250 801577598 801577613
    0x9040201020a051515010f09031b05030f0714090103121815020a0c06030e03090402030405030f07060c0f03060501210e0106170d0504050a090e0c18041b1503150b0403 73
    0x48600309000010090b211115610641000d00045c006846070b5100c236055131900551202e00929118460305044000f00340c40e902001010b01c2c000a85004003032031414030942d90340c0342003450a858081d6500100510000e02d180c0320002005140d89060f1280021032505510758004c03582c46841c015201c0d80b00300c1c0d2480d82c0801d603046c1c25800744c001c0228440c1e503180704500b10740d41140380c0390300d41c1c00500920b1000c1c50190002c41d08540a141182c1c103049018000600540c840c60046a1040d51040400d08683c4c2000c8071020900340ca050800000d85000000b03021003000c1e00c0c24142e02001e00c400d90885544560000c030844034070390003c00255071946001c0608a01d14071340f4075031507c100c0d1003c0d01d10320321401c21174043c0e44011306040314040c03424040e08007500300b10803c84168021300c0c410b11001e4444901c611440300d40d01202c141d150070311f0f04043d17103041c1002c05480141da410040a01c0380f11410280c40030140f1041c60001404240c101e8503c40300c845c01e07007110408590004002047c0b1000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 801580098 1250 801578848 801578851
    0x3209030f040e161805010302030402030f0d080f09150f06190602030c061b190504030506042d023d03050f0a020403020310090609170a030c08100509040201020a0515 72
    0x7034200c100062107290805480c4c030f1415200c0e9078880206040c0522a030752298003d56042840030701120701c0d881e80840700c541040403828446000030740f04c1c001c0100300031403800c07001d4100d105100509080816034104d408a008010051507884c0a8031010071181d42301c8030090f00e44280aa41e94030324843e2154402034403a4003040e07280445100b0880480d0018664040300000b105a4880340c1e49881e080180d101c02e00c01d20415a0010301030f00740310000200380e051042d01c3c459480f076900071142c0c400003440b06481030300300601d01403600c0100c07070400010380f10885e04503000c032588040d58100350140c0300100c09009006d01f62001076114207445003a1180c054001902a107036008202c0696650501000128007403440081d52590140145e055100302580c07010380242d01031ba80106200c415512020a41200c16858a00600300004ca0a501540c1486038010b13081c994603112010303041c100940004030529000740b61189001401090844e8000c0001b5840d080d8814281c8000941000050310401c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 801581348 1250 801580098 801580111
    0x6040b06100509030a020d02120f072408070509030a020307030605040b071403040f141b19050d231902030c09090a060c030e0a050309043209030f040e 66
    0xa01c0109015003500078002e82d800c5030400b800420000020f9001c014495241c1e59050380c10110072030401d008010140070003181c51030440300404010340f51030000703607011103024000c40c900242024420941507000e601207400544900e0a65141c10042000038105010800000d6141c400c0030000020403880d138100b14400c034011544105a5501d6010a40e19503503404081c2c805030030204005800100c690514080850203082d0400003d80c40303040562808003080074102d907100f19541c10040d149001415100095040910114064074100111b111440e44200c000d001c40c0705045450440d80161416a06442c0701904459007814030003e6100d55040c400000e90103409030f000019500e040211105000d40384103802000c0d85001915580020030702524414100b646440300c03280403140c10056845100c1c041c0001e5541c8102910400c02120031040710440c8030903140c4a800440d41d42c020074038140400c6c4a07400d40b05a41e4401540d4114814107103400281c0f900498081440d0903021038107803185e031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 801582598 1250 801581348 801581359
    0x50d09051f0f1103090d1101090b01080618011e11070204020720040b18070207030b1602070e0403050a2304030c1d040b0703150801020409151d0f130506040b06 70
    0x20701c1543c0401c00342c4803c40c2c807921250300858003500543d10564103900111011000040c0c000002e40c0c8000c0a102e083c1e0003003030140e0280701070085408801034012000c0f001000204901071321507c6a4007076400ca171038881c4d4500d03a1130300612050100d560441d41c2d00c03940144110340c0d90700a490109204413042107245039400c8409000724044c106817140401c00c0d0303002022801d0740d1100e42c440c03565051000f041481140210000080090030301c0e1403590040d0b848150850004081000091400550f540680c01d51a2401c05000210740c005048400c81d00080c900b2140600303c0049402d075a10200003035102c0048000f45c00400d10030706004032410790b4108101030219900c81c20105100300d45c1980c2c041d10203a03e0b000030556a41c001d500c07107011150318003010a01a0754071f698a5007241c1165222020450311350a100c2c810018941013031000d001040c200074206061010403100c0c8820040051000015a4010075441d410001a41c0039641d4464111a844d24003031412004150060740d099000d00e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 801583848 1250 801582598 801582611
    0xa060f0914010515062d09270c030c0c0f01020409050703151e030b040507140a03080a0818010f060303021e060604020306010e0d03021615050d09051f0f 67
    0x90301c1c10b009090048a10382401e0900701d034418108403541d40810042180c2d0300101d0480f0201c46848142e490240c14510ba040782c4545884040c0f0840f40c140c40c40c0f600419044004100c081250040000d402c440000c030b4550703c03a911041d00404a11402509100c5445010036021480c0d00540003841a03444140040c040d035103d0342800c2e42911b44502c0044001d0340e0402082c0f00214407a440701d0740b204494403540d5011030342e0b500c03041540c210586041c0c80310782100d002803110400d5800c0d03560042c072060b01c240400714a9a150f40d401c501956030210104241000415281d903c3e19680c1550540e40704000c0014074650903000d0020541d511048001d40507101c0c45465528001142070711001c4460080e08081d0341d9403003000020b500003080241030242c1461044120b403200f00b10400305610a40007828203c09600e120100d034411503011181c00780700e03440110702d040d0f800010349c2d0040d8810800070640c42203a19025060074043c10b06158481c00796410708980c41042d8000307481e258031015040055 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 801585098 1250 801583848 801583883
    0xa0b2a04061b050705040906050411090c270a0816080d020a11031510030308010503010216031b020916120209010905060304080405100309050c011e110a060f09 70
    0x150240d485220003055548540035550480050004100d80c4250103445955441d02c00040c212595811700b030f10290f59507004c000030800a900440c0404202b181c0d8401c044c6420000085a4410250100c04450007980d000107000b214410400c00000d0040c40c1c3e0907140d45901c816555002c41184114900b00510f000140250b004601c5280c100021f0713001d031a000d031807621803024040309080c0154061048000a00e1000e9144000c035004040050344c1000c40b51550a000313101c1c11040c2c1096210382d00c10004080d501418241502c2070701d0749400d0501c00607208030710700b40d12846080da010350490749400030440d2541c2e4800d01054031081640b00c021304c18400d010301408a001d080e040300c1c04521194000d1180745841e0010b103030f1003031281203210715050b1943c005c02c405584109915001c00c3d1111100020008203001042d5210402e283c10b08005440c0c900310500c1c204c0c007604000034070160342c080014460007800754002050300041c05007c44424003a2507002400107150640f0f0020109465010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 801586348 1250 801585098 801585181
    0xb0309250b070813030318081504020d1410050603070e09062e090f06120533011202010e0904030f0806040f0509060106032d0903020a0b 60
    0x1169a0014aa00446810084125410782c03001400361402102807101c5111200120040303000356200740e55442e410900349204a40c00740468100c12041e40200f0b2038804119544070a5541c0250101ca501c0380404083c2000f001052141c6201a5603000d14040b4844c1d02e40c0503000680a00c8095048807003159440706003003400641592081110b4002001007200503503003a202d6100b04803041d545c110483c441c10003a01c0e1a030229840340310f40daa00c8030001401c60210303218400040034816900c04058106a951903103c921003400d12256401d041d1640d00712a0b804800329002141d00c0c0d109200e02c0d6100c6149400f403071a4203070304070b00040d000700e4103d100b41040d88150b40140d40c1340d2a62582100200b030251280c1c1d2000b02070780c0d0800c0d41c660400001d003415005142c0101528400b502d05941000030090035100800a10364074010381c0301e1040d80c18094445409440c2c0122000010a04001d280072030800300211070250060302d80c0d41c10b2000003145003009068400e581880b82c510f60356070400719079 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 801587598 1250 801586348 801586393
    0x210020a05120901111006030b0c0301060e091504421a130905071404080d030f06050607030206010602010e01060e041203090611041806050a05060705010e070b0309 72
    0x1005034011180002e45403050801900400c1c0050400742c03121185ca0005914010070008128075a1f07460320000c0080c4401030900c4d5800c1340c50390114038659070424801411811000402c4d501a8080703000103506084200500e00c150400100103001e04110b00c0200140c0807141c84101a4040c200d008410000d107522600f403409030307204c01040c010945066210210b044401107240d011b10420410301c3c450b842c0940049018000300c0b200000d241c10540e1004000c603c81d03054030710240804110900600000040c0030030400c95a1074081001940c7d581a0b00180040394801038010b400442c22808158020034440d05980259000b046042c140c0400b940c2611054406c060704207581002140c0400c0501c89007400c190035a00700443c0d20003403130b030380c1004884a191440c4160040482c00340041039903040d40620001600c5824019075007054000b540115051180606c500d90015219017044003e401400c410a84a819226025a41d00c10311403590301c111003041090240a514074203000a1300c4841c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 801588848 1250 801587598 801587603
    0x140a02090a05100801120804050301141503161703090409120212030c16110d06061a0c0715021912141201030b0a0b03071d0702190303021305040504030c0210020a 71
    0x141303c02e9280880001c120304030000241d841020800010074151000d01030030342e01105200c0c40c0760300351402ca184008060030a070803052080d0400c1c2003106070204948170b500706445601401c80c088a0282d03035843c0c03951045a040175001400e00640d04107110014110b103003400b02c0c039029100c400b504041c0304071440c40100e41c0301d07071070304000d0040303040504101120000b640c0c482ca4000700703d00326650000344031003014002121035685841c02401841c01e07008005001e089024069030611001c0040c0645460741030288003055040452060040d038420050201d00f4590300781018981070950a06484800036445410046200301001e0700004140c14201d1300c111200220481e540d03421682c84141c625000303000041180c2d11040f00e48842d0380c00f07005c120020400d1400805001c07100380c0014a9070321009000e0b106640015010000003aa2000140c2d040c90340f52400507902c100b403c0e00e291609049800003a00703e45808100404c1580002521410600880b90403009110b4088201e07a00d41c0f240000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 801590098 1250 801588848 801588857
    0x100c030e150906061914150d061809051b0f090109050601090f050607020d0201090f060c020f1009150507061b14031006030e030702060309030d0509120f0a03140a02090a0510 76
    0x20000c41c0d20382c0071101080d9500810700d50384070b06c0302e18440302203801c404030604008d80c1e03c000c1048002108101d02e0b2030540110700c280030722013054868541314802215014078125500a060006588036a6585001c0500034100481940c5420100b0001c103001c5800502003518008042080081d0804a10858400030019031400e14541d00780300002008200c02ca041c40604400807602d20992980c00001d804a0b9594485485442c01005102604011890301844c107810b40100c01030b500100362400c3c1d03080580381c0400c403412a4021030700d602c68104003a0102d45040111aa8042d02e01d90504c2c0039802503070b5889901c00030081c15620780c40107451210100801880400003540240c00c8125108060340079682040704607000b00d2070961013202c5400b015000010701d40c0042113248100e6070003180400c014103095000c41c80c908080e1051002043c040c010201c7c18142a41c401e400200c181c40c022221050720b03040407081480650086180b280c4616007590010600742080490130003c00740c0d503130311b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 801591348 1250 801590098 801590149
    0xa180e040c170106090204060e042703080405030d0203070f020f0d05030610020102040302031c0909020c03030403110a12020303190203060f2707050301090b03010e100c030e15090606 80
    0x341c50000700510a2035000319521203078002617401d628805840101400e40f5103601101c0c0c0c0354104401c84003440b82d801c00b01c0c0079020380e020082d10b00408260202d0f526041051154945040061840c05428000d0b08403034000800c214240d64419a10f02062046400700e0b00d0703044e80a024107445500c14111407001501c140006202890b241045840d80d158500005181945076004681452b520f20342c210716a00d031021000c1200ca50011070725000303100890b0110b080c40b101d0307125252071303110292000d800c00900c03443c2d4003200c1c5002d000c41a000b6a00120104c0002081350020f910390700100e42c0242c0c0c854070768880c02c0c3d05800900880b1300c50700c1c00412203076054001d581004414807120410401c66200400101c00e04152100ca0301d0044c1c0481d221030340c0380d40c035282e0124140e1302d2090b0700c030380a030341000b080741d441a4000030f841c001164620b101152502503404114000d100a03e1a030b100c5103c1c1640410040d8002c814060240f0000d00645000da5103500a0049143c2c041006171131600c100312 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 801592598 1250 801591348 801591359
    0x3450d030305060d0c030c0e010f0303050d0c120507022b09150c14011a04061d060619030b090f01051f0e0a090b010806030d1d0f03030a180e040c 64
    0x40c0078a030f110301c1c018042c2c004d8000c1c0340c82d52072403c001c5030411500440e00d040d06008450342c3e0120907004020b540010200c40b8195903004114ac001c0040940c0010b45800388408014081e0b44518018400810108028988607800a50b0394031240707000d40302048219100035001680250050072012161500748045207410341e11800c1c1c1240c4000b000c100241924628000341c016208461380131080c1c0008120f445801e030000c090144180e0410b03200d1840c240303080003103e041d049403c0380c05484000701ca00c0d56860f403020500710b1190314a0400f2802c40520381c10007194060348075125808040d9411400c42e55510034184249a080c06410ba1002000110340c403170300d408620100030303240c0a150400c206007010b4081542600c894000351102c40e151008003495591200080750302c40340c00c070300801104110324405002031040b64407143c8070100031559001030f61214004d2114010010303085a40d540c07029080101030507640c0700740c1444590742c2040055481205410b1034000d03500490b62032166481c01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 801593848 1250 801592598 801592601
    0x503030a0509030a080309070e010e220c0f080304240203070f0c0e07260115050d0605090a0e0714060904020a1709010510080a080a08070203450d0303 66
    0x7030001da903d445031441c0180001c4402000c4d5000f600007500924005041032181181144160440150000580b0410944988650f42d01100710302c40d501900d00f040c00b6080c44450702103079030045030715000d51000016007980000018012a00041082c2c0031410940180e25900c01d030085c124801a8424414080440c0c3e151080c1103103035124000302c044440c0d0340c0015a15080f4112228000f08540101c15204c1c02201c45001f2200380039282c110704d241d0b041505012417038440b00c5001042120118148415001c1e42c1d001d0000340100404e800014905906444003815840b2540a40e50042e2400040c2c1d22441e4880c910070300600800d00b9003003090083c10b1200940243c1c604208022101840b114514801d1180900070401c640003c50360b032038005803100340c4002030351168103a9030114000798082681c85051300c0c036146080c50b144903580c0310040700b2451406810300910740f01510318044901049030501d0403000080c080c0c6100c40b2410322595a88a03081c1090410b90010803a00310840000d20a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 801595098 1250 801593848 801593857
    0x90b0d050c2e030501030b181b1302030c0306010e030f1f1b020d03180c03060c02031e04060806040216121b0c090b060316080606040b0d0519060503030a05 68
    0x1a21840c2d202200000241c507020002c2c440da0000c01d03a10070050041c400c5100403107900052019118650445030801c007940c41490900c10064590740c5141c06116646214900c5280740f080c8000f59181e042c0030205004030b5005032440c03800704500e440701c0c02082c180410314405400c0f4080160030007503004c1c10600004595410441c0000b0f641d40064000103909840700d29070b2003103560007444a1500200c3c0941141c000360011414140200502e00000d041480701702d0030fa980c00030001c0f81180b1000c00070b0b071441c040c01c1c0c660006a8040004c000c040d12910015000701c2d0081c0e070b0382c6070a5071219400e1204074400d5070508410b4100400e003180218500c044c010340703c0615458480718612841c0d1020200e40c50302c08e41110015661782081080c54403034020b01c5a24001220703503c0c510706002c003480d00d03800071101c403240500000e0000a000c50395600103031401080020240303035a4119842d07080009200440d105802403002c00c0ca070170301042141c8540400d0382c10140c002c501c2d1044604099505410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 801596348 1250 801595098 801595129
    0x1a1f06030e0c01080f2a0c0604030810121407050a030b070305011a180f040507110717150406060312260c09010507050111070501020c06072c061909090b0d050c 70
    0x2505214916081d50a1b001b00071280c0104044c3c05903080c9858003c141d4078003d841522045100ca8040c040000c0e5102d281c1900e40c1d21215202003c2180300c80b00d8100b400e541c0c08564070400051001007802144207006104100c0360741c1c10407007aa2100c01400403814400d141600c900f9090160608141500800460010006103111020745401002600303440040303480c0000138200105000155808000c001b0140002c1002c41c0280e2440b1010203a48446240c40300e880c0f07519000101303043c42204d622040107142c1014014041c544803550103020f0b690b50300da10b0000d07515000010441e0708500580203010b1059240340030324060703444c00111b43c0d5400200b029101950b0b50950038400400150090000178458070001d600c0b220206103103418444000c0c54441481240d01051500040c581341e40d1034002c0040014005100345031020404038084d0810300f41c3e5451018440e0030107503800c51120401c60311012018802c801000d0107222042d071500c4802040d81e07000e01b100c2c0d1500e2900045450707420300e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 801597598 1250 801596348 801596401
    0x915070c0314190203041404020903101d01060308121501090e071b060e0d0906050f132606100303081801090f030c0209060a031a1f06030e0c01080f 65
    0x4540d400f85074000d400b030b0380000026920004007004281c0e455004000c0400c0100c42c1141003000d4980880d0f02d03140070b0103201e4903450381ca40000716250140d07190007014511a000030444103859191000044d880360307080d16030184001000500e104a10354141c040c460060350740000c82490040f10b070280c01c6000d0045028028a4494581512090142c01000031301516022400d00c80c0d42441d5410709445411100030000c0110007400429089400c94041907001c3c500c15595031900009445890031982101c801c01d65036410706503100703d0402c020701c5401071031030030b907091503c6000310b203034601040b440024042400300b0002404074003101d103d0700b1003110a80c00402c4244d0790395078030060341800c80000c40c00b00d00113031500400e50605200d001d6000c41c0c10380702c8104441c150342f2203040c07181d41001545a0303d00d010740041c40060220645580c0f0700305042d1a0706600b41c0300c54018000d04108041c1140354131030600914030540c814000e0302d000302a8081c1c05d03401903c03003503c12030011a4221007041c405 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 801598848 1250 801597598 801597607
    0xf03050405030c0a030207030c0e060303030c0c01090807060f0c0801180504140609030304060e1906020c160b250c0e0c0c0304090209011806050a20060405060915070c0314 75
    0x3d1605000c0b0391100d83c031a0380506541410343c903040741c004080b904000d84030030003801081503e807400070469811181020710071f07456400541166001d0141158010301d5440081800e0b0100b04090708018494591040244100c0d600c015086602d40400d00c201e0711002c1c1030641035001c03121140d00c956042070080802005c600c400070141d52a26000341d4203c0d01c40c1c0d000000b000305000ea981f1a19801420030405000000c281044d41110013140c0d00e07028080c0d5500041e8020801020403804050107092003400c1c200f59a41c4805401c13a421400541000803061aa002c07043c5406080c440c44840e80500e1301080036080100003400004010401900301c8000c10041c4200310342040641300409024202682e9030818a000408002c803090000c01c0304079500d074007400002d4101c0300396810442c141c90f00c8032345098911101400840101d08490860151600388010b0020228103144a00c601c2c10484201c41c0104040410402c3c049407554005101c80c04100000b034400d061082101468803044d60a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 801600098 1250 801598848 801598867
    0x5070203040b0d0908160516081507020f0607020c181b07080d020309070501030b18010621060b03040c0506030c180112020c060103031b0b010909170a030623010f0305040503 76
    0x2d41d44006c0c00508200021580c44042000030481a80b494104e42c0c81203824034038042c101607450714542001401036910100055406100300310350090b2070301c484100c480e14101520040e4407072035480364090040102c0d1130322082c48070f0010711b114050408038640c12410702001c5005403198006980440342c805080224040ea04014006540294a1000606221460000050215180344280600420607c40c008404048002c0000d04445060400034800350b501d4040100d823241c03499000304403c2c500a400f080509008015503c643e10a0403d00c00c100d480d44200029408111508848c2c82000c128616082038128851000e480d010704040040a417503245807010380c2c1003c040c2c429598071120040061550103980b8080e183e2034000c254600d000e10340c8802a02e030340140202c808450311440d0b41400c0190b881c018410306800090413075202e980308100100038140300d214a1196002c0107041800360141c0c0c0307a28039988813050312103040ca003070008030517409400f00604c03c0e5110301092000240 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 801601348 1250 801600098 801600113
    0x20a082b020c0d09080a031218081306050702150903010623010f0e1305040804050409032c010906030b19080c1201020306030a020d061b0503070e0405070203040b0d09 73
    0x1940005100e0250b2520910321405203090580143c91040140a0a0030014204045950201150103280c8488000d281170a100c001e01309054074141d241c0007106035071040c000c0ca14003403c00c40c10040110f40c030300c56561108403030b1070040c0c0c50069801401c802d07007075007210005401024092070141c00451140e65500d07100c291410300f82030130402103240f911480119a0300c440301543d444021301740880003606410105a40c040744250104000b075403140402e0612482906603402001d0080040c04140d02d0340c60000e001110003881803030b8008071030356600c40481001e01c10341e4512906950fa0600f031480c03e0350440140a43c0e0b4126034006c5480c0c10500414410300d9074110140c00800e0050000100a40c24804141e0880c0c10b004c030345900c14000d10009503000b20340c201141d50102c0d041800354426040890042c04510310300304100700003140ca4014242c02030055071060b0042d4607202c0321001c8050502007135030381c200e6610005800400c01804141e104001505024145900025041010780d64110 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 801602598 1250 801601348 801601417
    0x9010e2802030c04030b100e150d050604110a0b0708070803060f15190507020d0b0711030711090906070915140423190302040911180105100201020a020a08 68
    0x1060060001030520510180c11a411b0b008500c1f901080c6080f031500d0300010724408050300c0e0400c0f4020f096501c10481e5201c402c00c1d0003d03a0030805440b0307182010314081207014000b80040e40603007c2c40400040c07130100300c800d4403069500801160324018807a661103580e58401400ca55020034141303600c0c0810b881d61344d103214542a07052152a41c41d8000c02d03d405105a44214403020048100020390043e102c880b5640c0a803540505a403080da11120000d4410811848450460b840049040002e010444840700383d281c500742c824510541b0b402d8012900c456040f1000000700300104405c000c400f540c50b40e5000c40e0780c1549070011319030f44070070086205079015901a00d80c440c9130001d104a010103500011b0065a8204c400ca0640c0400020701c803004541d510002e44519600d80d0503c007440604d507030542c42d8141c02020884d0f880750700321400c03080c540d007805110b000f14a4058040101401442200c110780c1d0607400800b858001640e80c0b1200b81d018a24494100048414010700c1030313894811070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 801603848 1250 801602598 801602611
    0x50901030626010605030f0a020d06060302060c0705010e1f0c0c0b040b030f101503020a12050f04120305010503210408031b010c020a03050315210109020102070509010e280203 77
    0x9448510480000ca0039104c0b50741101e8840c0d008089a03000c0d410001442d0300d4659411707034201b42c0d01c0707031182800401080c0c564000394221100185030011940046041d0b0f0684201743c84070070740150280309105203005d48074003542000621519a944a82c000e40e81403000a1055450381c104603103032600c0301010341150b84810305144000c0180003291070789601199101800201880c1c52510f0200b0300d1034140324900c022401d0690010b0304454451150301e25100010558200b4021403c141c5080303007000c0411241913680117105003d021101c1e200340216412208002c0040c440c1000d00b4a0a0003030701807512200404d40c4040000080014062000e0101c2d103203813040c0d005588091491890a642180b085401150403201c00103000070780007000c2c4d036000450019101d01c100c1ba50b002290441d041000c074110a620b003c5807100c1c070500150070940c0107503c00c0e4241c5d21031303558490900c84004030a005840351624244001001d01c211b032481c0071000050300400d800c0038603501100e0001c0343d0054408 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 801605098 1250 801603848 801603899
    0xf080c012903010506030d2c1c0b0a0b2b020a090501080607090e0f091009061505190501030b01120e0a061103151c05062502060f0402010509010306 65
    0x1a11a280b90a11949034480d909801030000b847e0004401444c0c40403260034103039161103d5000308022450003515a0107540064142c001903580d10310680d5240e00c280c6411a44000c181d07001441148280c001c0003c01c0740050b00c0101d04240c1413241c2d000d0101510b400007500c09140d900744002d44e0350351303a00c20700826091a0024955040c070700c0850510b20014505024403a0b00417003005001c07040c5003500d910466640c00d4810a4841d49421410998440c080003102820803c2840134060140d01c1803810041400080c0044c42d9100b0501c0360311081903030030320495001c001d0b0403c200d50090300040d214013414503205590074201c010100481d000204660f1155001485420801250f44030710b40c2048442c42c41c660a44c680102c803ca4640d216400d1280200c604160301c01290820b03501186c03106510105075041840c004007000800120404401c65507107644406141040c000300d0410701030002160703440220740e6a0f40040d02e00b540300826031410580d44d85d400103200d01c09144006207440c034500c0d1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 801606348 1250 801605098 801605171
    0xc020c09060103092004050612070306050c0d090c09050106090f090507030b0916021506100c0201020304090204230402250c090216030206011e0e0c1201080a06050f040f080c01 77
    0x6e0008444000340300178081c45100181e140510400558481200d43c02400880c103070b6a00703207440d02e881c00744201e070340100c90420001e101002400103484050b120b0104041202e80c0e0313102d0007100d40c2901da108611900300d030070310280026403030741e000f69a02901900300031800842c403c02048400b442220801c3d910410640c009151076814802042c0c1e00c180101020041e00700100085d01850501c4410014005045004401c59000f8010743d030003008130030403c549032a5540e2101aa640010418629100c0d030180509110716140c800d031017645c125201410700d5500075100001e007003008004155115200700c0310006d8003c01e036000820b00408030041c08110b202d42e40c5800791074a50187c10080409102004000d017403c00c003061030040703d101050705000d5032910b4650307600320b109400b010a0b90010803400810000b200041000120303220f6201004140d40c0c650100c6400c0300c0c00d40300240510718900d0b104002c030b2000c01c0500a08240d0500002d81400f1214168025004031445400c40c0100d01c80c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 801607598 1250 801606348 801606413
    0x180f1509150715321906060c110a03030e061819031a04051f150b0a171b180a140a060e090402040905120f040e0a0c020c0906010309 58
    0x1414000da058000c8283da440203022030804e8410b0301c052002040c1c0d0340507000840d00003514410750080790300c00404004aa44a1740c00810301d032241c070800d0f00e90218421400f0800d080c003450680440c0c2e016514008180d0755130080103101e40c012000c1c0780c40d400c4039001d1074a99982e2a8903120355000c1c141211148203240d4540b030300d0304042d40d4004d9040a80c040f0f003044007040c804142d004080307900344590501240385015150080c5800442c0c2402000001e0003c10701d08a0b04000f0300500b94203132103045650825503030030450f1070300c01c403040650000303883c0424480804034005003140412415200744150100b10118240300c072261700c4400c1c080c8c0220040801814541c11550240c142032030010300c0343c500d2202240c10b03c9006000280243c0c4c1e01c00c10003003408000c1c8100e0f94403844012006507541100e205c008005e801c94020b007454031103110040b4081114034400e00510306a10b03005024168805810014023500080a0078145901c400d905000519032194101041c0300e0b41420000c0d03810081c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 801608848 1250 801607598 801607601
    0x211b0d030e150705030a090503040906081203070c08030402180703200403030503130f12020c100f0c020103050718031a0105093108030903180f1509150715 68
    0x50184003125080b2804904200c0c100030229039000e202400d04a0350383c4c4501c001ea0004220340030018120307000211300452408216008001100d401e90212040c0010401c0c071000b0720701c4141c1c0ca0700c002c9030400009a000030f08a070003860f40a40010620b0310782e00c00c9840f042202d18801c5882e900080d07959280d0400b904001100750b01001000440b0a040504681e006401440090701011804c2c0d40211003004104098001c07485683d40724503201c42c500b8942401070341d0f032030340e840c86503125a071062011100d00744501d49081900030b0655551594450b50340055005000140151040040016080b0140c0032102d09a000641c800c013400004c02c05035034811000150183c0110780308540600a114401c00f41c02c40107a2000490706071014590b801105800d40500e040d000186280c00100030004100d8010010f08003c4014850b414541d509010810062a0b203c00b07006a00210490045c0700c4000c841016001e842006050003104120000e1100c40c10380000b40101d0303400300c1340c6600f0449030816 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 801610098 1250 801608848 801608861
    0x411030a0b0609041d370507150c060e031303111206090d030f0509060c0a0e10031d1f0b040b030307141c09060e040212010f08010617211b0d03 63
    0x340c0d810b00c0741107828030401c2c2c4801a40c0c1040f130346c041d072802103080c0074400d0510981d0028004274900000a0f0300940c00500000b044140a950040c6011405034071040d0102c1200c000c11805410080110304580d562034000240714443c94001581e03400e954030880c4100211400b1301c28020084c1810070380c0a8004059030082c140d04c0c14814100814400c0d80800000c007282c000444140c120384444003d50102c99030080461071039406092602c0c40d49416806610a02d0108401d200044490701100483e5503183c00180c085c2c1c540407084074800740b02050a0703000341c191a10045c1301054204122000074515007051109032480d08114102c0324407040100881548420010301c0700b01c1a03082620b01a0a1b42c41d548120f4060203c00c401180090303460b64100d8041c20741c008004012941c440aa210002c0d416000307240096282c40c81c04140118082e0320030103034a8080d03008151982825003200320042c0700300203514040b402400845480d0340e03551202960904130500414400c015000001d0a6909 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 801611348 1250 801610098 801610123
    0x60807090c030902031c02030d0c0818010209091512010603081201050306070206010509040c050d0507090b061e0705010b031506100807080f09070b1206040b0411030a0b0609041d 78
    0x50712109100503200411107440e680702c507a06d1410803a00e1000245e00394031620320305054007031800c0f0440341c041e0b4018090707900410410100030700d90300c2590100da00300d114403880e1551011801c8002150903009814050000304050410042d0042c0382da0501c1c20b58046800450b034061000c00c01e2844d03180064031090044c10200e0051442e800d003040040d40f14141801a940541c000324000780c184150190b001005240c01783c07075605503001c0ea051140d115441c2d4002c00540905182880300030313180401c20356555800c098941d144040c941e00c1c10b41c0040d03000c448101c40d02d54035101c141c06c15540903c0540d0703200103e03540714645460810200b0454403141006807042c00384190521000c6036108400940c45030140d003c07550203803540c4034060714000c0c099101e42621178001940150f4801c0502c3c0050142c042036a080c000c10120030100001d840054030311484512017400050144880c03030b0017003419501e000d45035034903091002c1301003401e580341d148078004080035882c20120600c000300b00042d001344 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 801612598 1250 801611348 801611351
    0x40e010f090b1e070305040516031401060e060105160501112109070b030610110601180b0307050f0d0813090203071b0b0a110f030a1407030c0806100e0301060807090c03 74
    0x40400b043d000f880042d00300303030815a54500150811004010a0450307a500b54034007112140d803894030311107170501d031220030005508001d00090507405501c042801a181615030340d08144507054445c0d0240c0413070300203440c1c0399241e0070342c81c035120000300c001e046000101c1c1e481049180368184040007010003408410182d40400e408000603106981960340201080303a0301350204001c1d0000300c40d80110995004a540140c40000484240d5942e0019190b05c4510b414410010807100301030b1504224410381e5080300750341918100514203c5480b0240c188a08071981c1070008810240707410340f005070401d0fa41542d0000900011a41102d028404241500c0b2481c580b0b1181c2d503110441488090312080c2c44c16225040e03a85000c03010802c2c3c0300c03200c0801d441c0c1a200c3c90080001001751100000c07000c1913a50550100b901c55104c3e028202502896480d0305a280d244c1405100d402401c3c050b000c400c1000c520b500c46099942070141800606080000707010300f0703080c82c9005084640d418038070014503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 801613848 1250 801612598 801612631
    0x3040501081302060c07180e0c030c041104080f030901030e190605060a0506070501020406030e06012702091f0e010507050c090a151d07080411040902040e010f090b 72
    0x160307032246a55500601800341c602c20910749102041d201c0c0a9024100380a0003804c0003c07500c400d142c81d20240180c1212814070066a800c5105070700c40c000320a590f078142e0800e03564890f103030401e60401ca002000541c1c800b86019940d00c401c07818240208480e102036000010440f10542e8140100d1958000034005070150b000d404c0c0c600001003101034402000711340c5400020300c8594800700503000900780503082c59541da0851500c903000354494007070304010a19090fa0510201e100088076410f031000b0283c49101e540c1e00c0d121400c5c5070084010400b074640d03020040c143e0292034407405a1084541c0c5006004403a4220754007a250b040780280490403c50144000c0700032075400a89a080040259a81c0d009925481c00a402502000d100d500c0701082c0c103440016880036003140d480341d4a030b5859450205840320141100e000e40d040d613010380040c0b0110b10802d014901540240c4010f44014070004000c08084000c5003550300300c076a54034025a03182050010320010788101580411003191140d5070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 801615098 1250 801613848 801613859
    0x1080a0605060a0f051c020d0c0503090a0b1003020607081c0c0203040e040c121a13021806010c0605010f0810060303051911070b0306010f030507021207031224080304 73
    0x16800f0b00210301081109610070b03224998010022110141d0390400e40030003203c49801c2c2c90000e94070460000641d41c1c600051905c2c00c03031148003603d00440884015124816850b141c0001c014000360810628400d120000001a500e1000420750f4511582c540742d01c5440e05940e0815203501d4500d42e01e00d190600c20b5409003c4d41c0881154140c03611040303212580e866174241015541001c0c1c0101c0c00c84030300b48081c28140140422a1078402c0c2165541d954039540d920b0011264038841e950081d00b0918501e201600aa03a044640d039200704103141c4a031340101140c5510381950b03408c4c0e00062030b42c04001c44c03d00181c0e009200144041d072280c0d405022042ca03640d0000e005201d0340343c0100fa003002c00d55920031828401c407080c01c07220b03180e8000c841d90152a8880da010036481614810301061081a04c10003060080c014144100e940c0e402070180b01904802c4881c1d1544281011005c00c25200c14800c525403040c8203201e401e82100303030030800c041c4200392108401c03940c5800c5082950300501c401c009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 801616348 1250 801615098 801615109
    0x306070f0f0e03010525020304030201170a200901031503150b1201060603051e0f07050a0c020a0312020d0804111309020d0609061116060b0316080a0201080a0605 71
    0x16001030318000c0056460340c1001c60302c00540c2450030b50301d5420001030200c1b400107407100301d14800c440d94140d0041401420b00340c1c0e4038807a51000a010075185417000071240e0384d10304035560000814a000c034900504c4007548803010040c0c508100b0071900415042ca00b56454032485900300d11626125104a045485202c0e8101c0d5160b20403005a13140c40c0700c00904d446541444540880e1079009101c483e0716000302401400d000c403841050b840e511030208440c0d2182c94030907409040c445502c07198940f80c0c640119010340c031400f2800280050303080a40c0068584642d02c00066014502d840349811400200074140301034031842d0341c1001844020f000101e0401a60944040403c0303e203582020020001180500700c01c0703201030b60000d0340074040c1043c0011038110b040c1c1d5522480301088804a811060406401222041c0c07404080c0400e208000501ca94440001c030800102180e580201d2505000b41082461300103c1494200ca28214210350300480c015400400101040c4122070800300400c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 801617598 1250 801616348 801616367
    0x20405090a151d0f07030902060a030b0609130905120304080a0309030e0409260c0705040209042d050f0f04120c140109020a0e0c16060b061b0c030607 66
    0xa1440b82e49542ca002034142801c0b09000038184188040404a0107a41e03000269104981c400fa003034101c000001d044c10320030712842000796402090b1504203da40c20044000303050002078603400040802c40410280c0c0d030712001c212035030100c1c500418100c0c20352800c0d40c00c00340c00c0c80d030000d0360307500c1402403000058200301994075500a500e0005041c05c460306045819211078080308e60403503e00000b520902c421503041214400c155032100801901211080c030f0148554600ca007002e8010907004c0c841898150000e01c080040200302003221038004001840e690b04a0208125142001c0700d1400407a02038004c144d44040090101d4815240a80d40d100304003070b000b4001026050b0f15616411482e019081d02a5000d4224414150035180f120500780240400352059201d10710503000010700c00e0002c4180c500c640104801c0904201250020b4094845184400c0f1b8007152105804641903c0f07250141900c89001d4a0401c0401d80028605041c00d6240d91030350f029070030000c100311600d43c02c8098203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 801618705 1107 801617598 801617611
    0x90307110d0c05060c1f0614180c0d0f0c0507051204082806141b1315090b0d022a1b0409020a0b130b0c0d031d0604030801030b060402040509 62
    0x42144c0d842081e6800691400d27070b00041081400a000e00407040003040301107210a4114160030a55900c000007000203a00401d0304401d0220800c524104004544400d515050511000c5521002c54404051018a0004203480d0030540081d120103001d8110340100b2841c116203040c0d00d131003201980d00a00c07106400d545540081e0f41082100c1c1803044004200301420b192508010150100c0e00707951080c00312010001903214848001017604a2840034010785c0c410600d01030358094003042221b58452450580400b902160008094050751a000008001568540d000401a102a00c0c000390170102d007200c002111013240010780710525400d40c000c1c00c45901c0b01001055402808900300d1540e11808010a6007070081d800800020308041602801003d004a510304c0c1003026141180043e0f660401003090118008034540c001c841101d085d0703e09443c15000034540d85000d03286 = true := by decide +kernel

theorem cover : BRFrame.Cov 801438848 801618705 := by
  have h0 := BRFrame.cov_init 801438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 801438848 ≤ n) (h2 : n < 801618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
