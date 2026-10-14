-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1926
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:10:53.505093+00:00
-- url     : https://prove2.me/submissions/c30b71e1-556b-4e9b-9601-79d7b9411314

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 346223021 ≤ n < 346402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 346224271 1250 346223021 346223027
    0x5010c111212130305090907020d1805100c060b030d0c0c210618061d01050a0515040902120a150b0a050a06080915151309020108130c030602040b0a 65
    0x40c1801d9200705416280500030002010140301c002c0005201003a45074501042600c1030040e40c001410144c4441c299040042d80079488640312415440000c03070044c4403242075015010314204583d009013103c90740d6400c2803402c40f8a91444001680d50307549800b20200252010041d1400c031101964640401810f40c0ca060708a0604580c000e409150100b13444c1d80c00400b606000c50703403007030b803040c400503805070042c40c0004072644c1c40c10040c0ca12403901c420585c51488559501d54003e03a071200820241c0c0d15200d80781e040340d10503500040d10904680c50103000307080641c00328035a41d000074001450b0b880441c2945203025003804048684080f1415880501943d0340101d1007020021112400000c1c2014080381e541c43d428800c2e4810003e900b00403c811500030700c6000701c540380340c07121031819180404416034103010b0b580507030b402100400c000022200e410320a07000f40c180e0507940c840a64443d42010070140c284014165626001d8400000c0003c001384024401012a1600c044e1140b555400c05 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 346225521 1250 346224271 346224283
    0x11404050c040303020d0c0302120a0804020103150f0b0d0902060c010e1b030d260903090a06231b030304210804120f090f0e090d1d04090f05010c11 65
    0x3400107044140024030000381c010580300180c1d201441c21208103640c07814100c0c80d06285003160045060001031228903103170b024902034030440c001e0702c0600c00d4108054042c441c40a03103101d000d02040400300103000303650140006144500a643c0003040214154000500f01e81c00450070020685d500e03e2480e0a007042403010708901c900da9907800004243d044007107074460492710090070030085140034184400c82c0f481c00101a4440d200039100d814988100720660302d9200fa54134610030704500754002400c40c0b00310310108a000810074943e070000080c040c10600364000344040c40800000ca0780c44605000c041020310b01c00c500070f54200d02e880b801520720014a101807641001000380c2c0c2420440440c030005002c0010900350f1070300c4146403644100490300e48049400c11000c0c0045560001156201070007010b01030b0941e0000c0d0381e454100c0c6038003076440381c01702d0100000c0302d0520052051701d032a0a60000d005940151000004101103a0f40c040c00c50782262030000104513280500b9001501c20881d0f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 346226771 1250 346225521 346225531
    0x13110409090308060315070302030c0c0d02070602100e0307171e18010302040303020d080a1d010509010501050406120b060307090e0109030e10050d0b06070204020304081e040e0103030c1a01140405 86
    0x1e00382801c028161b9141d5141b00070301c140185500080403a003040d44042c12902d05128440c103444404415010094450540d4403da40052040c0000b820300c8101070b00c5a4180400d6207402540380561588c0e5041084542d19140c005c000740902103000d0764460580800c1140004030120717542d847c075a08207031041d03101c40e82c0d03c00d040610621050002a400213480500b5080b9414200820768a41044002808c4001b1000c0d000000150380c1080c544c03015040180501900d000034400380c1c0e26101800200c44027481140100c000d0a40c9410221fa03d441c400c58000c0006410740e480b03582c85600c60401c5c1c03201c0210482440e0b6483e65003800341940301303105150011044440841c1202c46040c010541d0083d080b00c100c0c2c96644004103203895a030442110461540980195203d240234140b501d072a41100342c280311010000711426400303101030403c907019181d8880290b55180d08546080b100698058000c0b036040d440802c810058009041103580280040c640c00e03200c0c0742c0354200340000e450001d00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 346228021 1250 346226771 346226773
    0x5070803160f0c030203101a1c08030c040f03030507030f0807080a0e1c08010e07020c01080a0b0f0a1707060819050603030d0203040c061b050705131104090903080603 73
    0x803400621207800805101916048100803250461a050000c5100200d0340025450310038a928249415500d80000c81c1e098100081c2400c0c4000803000c1c0030401001c01c60707121320004801c2c1c44100241048015540119071080002e00309610741403001490f007c20740098000c80d1001c26148100740d03000d01c0b200312903d00d510f841403d904040c40050140640074288a03041900d8400d0f50b01c0765002048550a0756031a032a50f007250400c01d16000d01070030780c00e000e00600c943d58100004c03145400020000c08004043e03480c82029903c0c0344a00e030061012616203039001364203480d908003982c5e90b0640d01007d409003805114034101d40c80e580f03500d02200781d0320890900c024982040410075001c098062a420341400108a50355480002429846040c0113850500e20101c1031005000f01d5460308020390f100c585076581c2007806280b042d40c030f4215400005015501102c0184401d0400e6404c44032146c0b0140c0e400308048141026503480d5810a0b000a54015900c04070039091680c0407040e00c0c5c026605074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 346229271 1250 346228021 346228027
    0x607020a061d120a0507060204260a0503190c0b1608010609060207031b03020612060a0515091e04020c06090c01030603030804030c020f06030109141005030c15070b100305070803 78
    0x2500b081e1030f207000d1140c20032212008038094040d40c0c000c1048942259000030b0456031a911210b00311840f50000a50100c00410000290204140010601d28161300080158104103400703060340160f20080c110b0340100725042041c100080c1740c001000f802014580f082c483c0c3d018031000c0051440c0c205038807034420400c000d1420403800340c0110310304040d280c100454a91a01010840145041861b40000c1d0003450000e88280038140054105004010444181c0c15050ba144100900901c040c0d0310945d0f989001c21007083c0b103151000c0001c2e000b880c41445013164100c240c000500300c1e005003080d001150030140401c444014280b141c0b41054009003820002141942c40040c064000108000c050043c09504003066503030728003c4c4500700340001c00710b03a507035a1600000710140101c107119211450102c1c0c042030043c20702c7c9640320305a49002c0c00800c0950601e00070449035030500b01c1c0c00c03281c0355010803a920200d000ba60300d80b40316a180014400c801861480e005103801c80541c40880150014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 346230521 1250 346229271 346229321
    0x30f0206100504020c01110c1006080c220608010f02071103121e090d060204180b03101a040e0d110703081c021207020d09080c060405120307050607020a06 68
    0x3840e07a031010b54070700303840068561100e0904e250041c0a1021104400301020464000c1d0302d500046140000200000034403d466691602541d1030b40410b480907400303504400d20803660780c0c803107c140c40c19910b410001b240660762150f0848c2110340c100ca40058050700002c181d0203008144076640d018610a80003404904100c070745a00040c0580f28203281d030282221941c0040c0c03003942054484120005140d00e98206152170180025401407041420104d40310b0b01d41e4407468210301c504040000c0c050094004800d1420038034009203521030b520303001882d40d00211101600d8621603d950f8102040081c401c2c140d40c44006021881003040e414003650001070300344006010802078038800711071b8030010303085503901120240190003a0000e03585900c0c020000c001090740c0c0001c15181004840c0c80b0a5041038036641c1040d201c007104072180740c0003801003004000034144413200390b148040d0034040d6810041680d80d820700b4441d0a0710039130b0041e4030451420302489624400c21200700358880e0845d0103032540c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 346231771 1250 346230521 346230541
    0xc020c13051509060f211f0e030a0210050601050f0c0717031804051018060906171513050d23030402030a0f020a0f0605040f080a1e0204020909010909030f0206 70
    0x111400b5500446c10201400c101818985018042d180c2c41c1d400c0c1d40d41d031415031003c3c1910880c17101d044e452140c1407034100311000c1c40100c203c2c0c44001403680580103540c444003040f030262101401180c100441041019400c041600140902c507034800c025003801840d15940c03001c0c01c2c00d12021505d00e03410800880161410b003040c1c11010304130588012a482e500c0514070040884140e00c2500001340d00308003a8020f444550000c401d44c2c540c070300d0820016840e95900f8000540d515440318965000c4803460015403078400803c1d40c040ca0303403145100400d0321070b0340e01400e00701d01d2441880420980030910798280401c2c080320034401c44941d040303030552805400080c0c0d141c4943c0805020644a6491042503440709010203001e07100c5d1500e0b400c0019507440c0f008101e50b019200d10300d5031f406045008100c0650200d802840f554010352209289002d0461880804100b21422a4019401c00c904600e40e220203035080c1c003c1400c000b002401c040c1c0c0d0304020b81001014644030007190406010803102c1c0d00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 346233021 1250 346231771 346231789
    0xc031809151e0406050d0308040209160f110703051e1b0f1e06042603180616020901030312150503100905031e0306100305130201030c020c1305150906 66
    0x1003902c04000001e010200c2d00401d0300750131841d0001c5c40c003103071581070542003400d003801a40300b030340e00b81c10310713070754a02156090040c07424444000381410407900c051503c0f803905d224907549090140c4a01a030307a0780d595854000c02c011f000104910410104076611014842d410f0148610b00e48202988170220014041d100290700182c450310618200000d00200014254103040001c0c3c40c0590303507500c039910001d4140111015a4881c00d14040c800410b5902106440c603c10f43e020094200381c0c0da12081002c55005410460010600106144003503946c500005000394040d441b104100720411000c2c1d003c1d02e01112100040300c000c000200320644000130390300380b2040c0c007007000034090b051498028111321403a1440290030044054043c41c010030803009601801007113807040d102900302402541603500440307004004e10050101c1e400994001d401503401410544190b80306030410000080076204000311005a29644d0000c0020a20208101090040c1c04442e96065446c0c010f00059a0355 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 346234271 1250 346233021 346233049
    0xc0609080c010e2701031407050f090103060e1203040b06150a0c0204050a0b0618100807020d0e220501090f1a040905150a0209030c0a0308120702030c03180915 70
    0x910100901102d40b107080292946154113241d10b5449503521b0a00c1c02c00d045403641ea0590034000c0700c0001481d45000e19444030807040c094642d0321030347c0ca140ca90780020204000080c003540148910403103024003460095206612455000e131290401c00305000c0c200280540725041a142000003240458108041c1c400081d812200401c0503900d01c41f174003010707140c07680820342c1040300498000c5500f02d40b00c04041c410141a00c0c021800b100302a001c40b240301c030035039508000d07070803401071003030040d105040e16003000201520301a030040003a0540d8020702d02a409100d491303956400184417002542c0207402105508190510100d4403880014860b04020314500303104031380d91044482000000d00c0913151251041400d070415182110000003e5800303e480903100c1e014040c207005041c94111001130035030340c0000d2803608200003030140045d81600545002d09510040c80a40d00c05401040102556031910300101038004c500400d01410f600c0240c00e9034140e901c1154200c0184d15210a124410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 346235521 1250 346234271 346234279
    0x120309101a0301021804110301030b040f08120a14010608090709050414030f0d11040b070609020415060210050c0c03030c0d060807060314090c10030b0109120c0609080c010e 76
    0x1d00c400300840415100401c80140e010350001c980031202c074010000c40c0705809800c1d14140682050b100c2200c0c190302c000d01004002d092440042000b185a0b10031583d0b40d14401d0000e286440d00c21091065000411524620b05a48524254100d0040e104031680140100e08048690f030070081c000d05d44803002c60060640056540c00050107000700c80c1215410308100d40705a95440444083c0543d541e07005d00000341010342000780e40348900080300c1c00c44049a40c04e95203a1b00f00035441d41c0c0c1c0d00141c00c00203400e81c2e03c142c40d013185005010408043e04010314407a001081c44c1218100c00000f9030310010100419040240200c25030400040300304da030f001c0300b400307503495840c0700c02c0c00c00c58021b0907140c000c14030600c100c680c0410b0f0150103a1000b0414444c500c05c1c407040342d50381c0404a5a0300c0e122007040c0d81201440305012500d6020307410485609805040124520b521484c24001c8468400d9003076a0b40108108100949600000c040300039008070405824811062000a441d528440d1200c40c01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 346236771 1250 346235521 346235531
    0x31b0e010212040602161509090c0c0b0106090518040b01050108040f0512270d08090a05090406090c0e010605040b0703120c1809060e0a05041a04030504060212030910 73
    0x500d80c070030310184440001e21015143ca0b182c031080020b65039030382c5548520200a885d0300104410b21200c05d5140c05505c2a51004030050906041c0c201810a40c3d9600d410320803070310222400170b00441205800b0308095502d40d07034001d182c1002c100b0004900305c1d100429141c80000d000c041010100d40c5419030b03100382007100c4541c90314a0441e80c00c42d401403000d8144d0182c000006041300e038107001000f035501c40e264048040c0d0712042c8100001c460348007800b40d0103c0d4840c00c0b4000614004050302e01104004d001c6080140c0e40da000c11140201200c1c1168603e64800c41c200c1044907504d03c1c03c028002e0000e1a403001d6042000240072485a80900c000200011880c01c040512a82841202c22a161800c1c04491700004c8090601920742d1049240920700d008041104440b03441148116180e5080c480e503940c6501820768020880034006a85400091041c01034101502100d03170701480c070130380c1c86a0707480346440390090502c0f48440e0a1041343c1401c2040c810b408100042801c1b42000100e00015 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 346238021 1250 346236771 346236797
    0x305130809210303040c0305070f1d0901060b0c03042303070306050903160b07110607051e13030309080c041e050718090207030206132d0b010905010302040c031b 71
    0xc0311544181d141d21070b0744800000c01041003e001e41c8241201c1c446c0040b81c0d0030315281c444030b1800007441d00a071f03e801c7d040b005524854504a40d240d135040f000410001071103039104d5017000303072690107000302c0c00c113030350000400b0080307583e909000700c014180c620401c50b9031140c0b41001035200c078990312000c1d00b00ca8884000c925480018411030740d40b484c241c010108540c09502e09204403440c11a802c502080c100c089a0003a04008160f152040c4016541d403032034071440c81513400301d0a10003500d01554803418400074410744d00145800014500940f651014a850714540d2031a00c1c0955031214011030030986010304880c0e00034004550b842440c0305c041603994918000301c2d00c0600c03c800007070f80000b41600001d400c8505a00a00300c0354069400c2c0c98141e601d00602c002185171000e0020a4200b0600c5820b4410b000407040750500301055140910b41e40301e5032900c15144030203030000354141c0da40d800100f0447c03400380710b2091558240d003014000c000890804000404400e103c00c8280302b4400460341d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 346239271 1250 346238021 346238059
    0x14070311010c0909050a051620010e010914031608070203030d050f150405090a0204090314070c090e0105130204050c0403051b01030c0230041203030506010305130809 73
    0x180c90203180d8002045002607603600102510418816021542d140002040e030341c1c01c09015043c031540c01d04038003026400460204079810b207a10041c0482074480c41c0e034407034409102800b410815011747c000102e03146280c2d050200f00d00c28204c0c94121168010400031030b2982166805216503500200002e48030085400803134114802d8409a0600919010400980c403c290354818000c4001404451154000e4004d000440c1c00544003c1600d90202000000514094001c849000c0c80303464801003600f0b5054054025412070401241c1d0380c4583c940a104c0c21000c1c0c800c190b11202090002d002d681025660040f00407000305010340103940ba140007070000b050202c2210003c0d544070b0100d410503078030150710303140082c1c10383d559600080c1890065010f140c40001e04014620480b4101c90303440c1400805c22095110707170860516041014031000450059104004506500a0310f0200322072901e00b000404540e00244090301c1048a12030030f01c04202c00109480c1940400d88541d526552000d6480c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 346240521 1250 346239271 346239287
    0xe0f390a1d010329040206030c040312020304031208070c030c02010e030a03090801110405060d09111512010f0b0a0e03012a0807030c0c110d02040606051803030901140703 75
    0x740d810301010103010500c8091601d2614100c9020310341d40e24103290244c1e8000841d0314003125088810324650041009032034842c1c0210303000b00407014030f01c2c640f503034998842c0c00011102014a0158202240420600c548100508500d004030320304440e8604d010100600101041c1c0b80c09000c1005448081c01164000c07098901520301c018100c404a030780d645001012140c890186400d15400c083d030030390500100c14141c50683d00010010f50a0044240d5004020082d032141a1800001c002c805401c1e030300c1d0007083c05001c048482102d66580c0700c11411015482d8103a2000c111a0b1000108000010507441503c00d008402d01c0d09248010b120300010f03014110420541a41c00c1c1c0e910854020000c0e007604000c07007840035464203130b20750340d032071009904544018034040082082e0310180c400080540214042408004000004450040e000304040750074903007009000c00c00005a030001c001e07040320400080340c002c074011440c01c0300001c0000d0810310b5112003036001c0b08011464004050040c160 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 346241771 1250 346240521 346240529
    0xc0c0106170a03030e0a020a17010b040903030911100e0d0501110f04030302060c03010e01030f1505090721080f030c041703090f010302072001050d0e0f390a 69
    0xc12103407510401520749603030950104030301180c030740b50000d00c210300d010820004217a0000d208804d11842d00350104201201078907114000d5503a41c4410080340d0f614450401c42da8040d96000a1920003403400c1144a81e070503030824400c161303c601051002d0781c81500c6607041d5205445440200220340b0b010340c0500f040400c107484820010032524413410901c4090f0084074003036800c8544c0c5850340401d0a12610080c006c8104180c615401800881c0c0318003202c4100c41d01c141c1c81080c03004200400e410445100f07031030940b00c070340120b03001b0803d0111044190b01c0292205910b0794402c840c6a491941e01d1040d504ac201e0400004000610881c40040c261002884c0c00010080b4000200051984940c4003407036082c841c103c0c403c001d04041d44244281d0b628503601100d04032005501c0707050403410f00d0040000504003c400c01200080101c580140010071006c0401081c54103804c1130b00906000e0a00b6211201c4804401c0728408450200d203420302d00c1d120764400025094009002c10301c44101500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 346243021 1250 346241771 346241789
    0xa15050702150903010615020303071805030303070905100302090f04090609080c300702040e100f0905060108150a090218040b1503011506120b0907020304081b090c0c0106 75
    0x4a00c501d04002c0c00c00070304442404030020031000c6e4840500c0c2010842119050005030f00501c001200302c0d0081c002518803035554616906d4841d910b100007403541c0d00c1110307103100150580f0780400150411985e5000c16080c2401c0650821207000040f44103000c030100050b01c10f135205c2c102401401000e90120348900d400105447d07984040800c80340d561000c0c100c60000000c00781d291214800c000030f9529004072005940e45103441802e400f000050220100c0c03d000314003d0110340d0018010500c91019440607001e00400c136161941889400c01030160300260140c0c00446d5600544802b0144290b800100e0760300000e0440340c50700105080906408a084450311000c0521040c8200c49003a43d110b100c0c1100080140e1000c1c9050600b60740d81258401c0c00001140d0042c40454018640d05034031007000b010020b911300d80d11000483c440c10680308640940c00c0000c0610000754184200724248503410444051415458041811f9000080110030418000f18400c9681c003001c0d0003903001846030348 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 346244271 1250 346243021 346243039
    0xd0e04020a172a03091b0d020118050618010207050609010504030b0702190b01081915020903010e010207030809070617060409082701020709140c030702100507180b03060a15050702 79
    0x110507031074503902c02c0c0c407440014072503003510f055441101b0158150509001d054040704880a500541e80780303410401c000300898a152020a450f102c05024046030702200c41a918000807520000e400c0c040c1070740085020740400c00420780030b41d800004440841343c0c041c200c19041c0d039403030000b02d0808400c08002c9050302901925941030129604085041c0e4490700151600c05032400084803250105000051407040006c6003004c0282032640545a01040a80081014984200803608a9220035021030210f030040d02441018801041950042c110504040c6821100f00c0745100c0f404c0001001c09209544480800c030030054054165441d48003040007420020f1000000d100b003000c00d061600b80123204038003001507000940d000e413840c6880200300c510181d8a511980102c1548000c1c6003809601c1600340c0905540701c107103d11803240405558604002021902840c800400d5610100541c40700b80188106a80c44a20080440d021500000e80c07054080d08290342e503001e11017001e54415502 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 346245521 1250 346244271 346244341
    0x2220c050405040c030209030d08070903020604030506010f081b10140d0507110d0c140309190e33211024030308070504090c020d0e04020a17 62
    0x30080e10070b0354000c035800d008404407440c1c204c0c228011440e1066160744013410350400d450040342c00355000782042c0382c450142a120380201303000341d00c00e60088403160b001c4401000310005500004c00500800303c05000c00c00c102c100da04140100070304d403080c86070320030f0441b0410083c0a441d40185041090402a403105058028600240030880d8070034081800c00d0320481602202041e010071100036900c4015684209403541c440c2d00c408501c01c80c1444c4010010400c0984e50840d03601d01c401d2050355030480380c90030101036440c3d012000e84541000c681c1c620703a0760300c80070b0407904400040418142c421604108a00001c00007584880c500402045815006412140c046610303c140e01c1901000d00015243c1c05034040d4440d8001c003041c1c503421000c102800064424a40180c001e00d881c0740540c2020340701e031500e0084400b03081801c0051782c091101200300e0b5800c00c071081b48290b0100c40445c180428030748003074525180000440440d00550000424800c506240010b00b1103d680c0114060b6030b003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 346246771 1250 346245521 346245527
    0x3121407020c10050306241608031807050a090e160b0d0617060601050d091a18120409020703030e010c080118090c0e090102070203061023060702220c 66
    0x18403250350f0702800c010011118007901940880e400760748013415005080901c06110072004409130b450361030441f002c120011030014602102e0a506004007140c6a0780c1c01c2424904680e000a107490b46243e42045108122a5a4095255003180c10000000c94113681e1116000e040440c40000802091803034180071540d030314600050403c01d0b0f20803004002c425113842e10340d4140300003850b0701a050f41c03014000402c04e502c48c001402d1096402400400c840519541d103400d4800d40e8608680044030304020030542d041015540500785441c100907107071842c0044a205650700c200d00400c071000c0c2d00021070380d0805101317030300885090300715100070803844100e044000c009010038403c1d8110140620f1103e0801750252190845c00ea500465610b0424600303d059942c1800c01052109155428091480584c4042c054203102c3d18040b2801c010650810455140308001140e0721040f11818614032507480c1c4410782255042c40d0102c83c25644058519aa405078001c4124410700c4941481943e140e50342d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 346248021 1250 346246771 346246783
    0x60212012903090c2d01030515040b0a0e0a05060f06030412080903070c0f1e0b03060f010516141e0a02060c1204140a050f0105070605190c02060a050a09050601030312140702 76
    0x5d00c4510700d041407400c060044060302e0b0155211040d11340418103100c11443c03e544400030481014280728441a503a600303410501d00125640d5400e90f4541e0308002c05031401d904269a507460031a80742d810740c00c103074803101d5a081d01c0e800181e0500040340c1c080fa994803010002d558070030794059241d2a10a440d043c25000c2c1c415184949407500c0c0c8403803d0078000601441c40001500d02e0319842e00c2c2585c0d21881080030200201e2251414880304100700c8002ca003c00040c040741901850310000480c0c0f045415510705410f140240907030700c01130000f80041805c00711b00d91544030340455078181c846001c5001282406988242500d00440000c0c000072000c0041c40741c0d5404070b40c00c0f02d803042c55594640a005020f10018012070004404102c81c90000300c00380c1c0140c1d0400c0c020b00304041c00f000d01458403001ca6041c03a40110150340414100081c600c0c860180540c410303a1124148041050f5030b8600d9034408042c04000e0030322000c1c4006c0350104e02e07a9446400303480b20320001d4145c40c0c282010081d44580e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 346249271 1250 346248021 346248079
    0x5090705030f030d200d020a0e040c02011a12150c0909070908102304030c0b01230303071208150301090b06010314090d0c02010516060212012903090c 66
    0xd81040318460354032111760031110600100d01a803a1516800ea2100307002988011610700c10311103040d035440560b444030320501010403640c0d0000240785004203030030b841004030185082d01c00d5010240104541601049566103418128143e04164494004070310003402440242904070900000b0040026805070b50b200840d88240181d46040f482c82d4500343c02e45035000607007001250321480d2a29502d25040c00d040d4040e00070f2503da1445140c540e55140454000c6e4401c1081503075200a4980384109003200392a800c070128001e61030712031070759100b0b04a10040b06c1d08070184002c47e4001201a8640f00c1e14074211ba1005008210300c00d01031400b00030000d41640e601d80001c0ca008801007408601e5404035004001c00d00c01424647d0403804102d40c0c80494101c1241000340c00d04c901c003035522410041c080980d2050001588403000c0c10301040500d0416407001c00d85159101000583c581000c0514a00b4500140d12540e40d03980c40000c103241010070407110360440805484c8940120b00002d1848c004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 346250521 1250 346249271 346249297
    0x10c150219020a050c10020a020a09020c07080a050c30010504030e01020307020a05060307030e070e0105120a0b070503061c060902010306050a450618090f0605090705030f03 76
    0x40c5800780c50803661002207a8008101c0d5120440b4260240b509001c0708003200300a01c111849050301c1d9000c41e8451425038050030500341c010072842c42d80c036410301800c405041c5030401084011500d448140d62100700b82807407406a80c1c000c02181910685500c4c1500d01c401d2041e03600b0700741c2c5005050314024642240c1c1500050307444285100190b2010045038980e03070b00140040200c81c100b00803c040c59002520b401c06050740d65040041e60402401700000a1040b180d190f031041d8904014444420780e8619004020b4012410540010f0340841c4c103990800c0d42864281c0e100da40d850702248a0f8007019155485001800410300104002d41c1c01116445200b80d0702031210507526410b03c43e82c8141f074080e03c02203520b000c030008038601003803484030300c0c414101c1041118049400040890010300e2000040700d9521000148200420000d4280d06900c651104105820164a031504207014400000780a10380314070100348900750030000000900360003400c2d9180102918511942d0b54405507055501d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 346251771 1250 346250521 346250557
    0xc111c0302030d0b0604030b06131d07080606010206220c12060b130b01020a0f08090d080c010e03040e0126190b0f07050f1e030a050f1302030c040b010c1502 69
    0x51411728034143d0742101d601c60a14280c0340c9440d42044030060035400b0301c03426165a455040c04040c1d0f440c94a0007601070b441c0c042d00320181460701c2c081c01c1c650010f00300e0f410340d400a02446180303403010754035100d502100d411022800c04c403071030001144c40682d0f000c1a0641a05200b180030f210741d503400340d4030120b001c0300c2038120210001c0400040c0e90311610b4807070141e0010f001e03103008502c0184030900c07814410346840c0d140c00002000503c0d07202c0340400903540c030807022a81a142d54001d1264014842034480154145031516500d040c0b001d4050040c00d0500100426000008001c03c0c844c04004e0001000d031407582ca08440780304803a24410805807010304480011401400e4590159401000e0366541e1a02c2c028909032101c40d1541b0080108418150088402c100000c912002c0c42c058030004101207840d003005421442c143c400507103001e500d5003110500000603034001414100d000000c1e117000c52052559001a1242900c04102400301401c02f031104404542c0c650040001c00394007900282 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 346253021 1250 346251771 346251791
    0x3071101050601020a020f0f041404030504060f3905010f0b18010513230a0921020726071203080c0f07060504080405060a0f020c100c111c0302030d 65
    0x641c48000f020087c0d01b003900c101001100742004401c1c0b01c40381c0300c06000030401103241610708082400440d0181c00042c008281030000e10b0344407140c094007030010303e00351140560301100d120780c080403010412105c5043c24000002100e2003050414800d4000008101707495504c80140302a1001070003881c0b05403440e4528541d4201100c0d001816104090300c040b10010455820200500810503148400707412240384c0320b000b000da5a50fa900c60f12452001080c072034018a002984c4021007252800038002e034440e040700c5180d000403d0000c5902105558842e140800188450a0064a0801c1040c01a9100032620705030380c105107031620b4071035943d0358516520304003040e115003e54011034131440001c10030761001c1a810342000d60054040c03031465140690710f2001800741da00000c150303008165a80000c120b0a1f406010b80744041009450314550706800e4078006048614410000380503158404040d0303211f840d142c24a43e01c0702c0b40c21107102565907640c14040e641c2c2d000840c4001c0b62034140302420b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 346254271 1250 346253021 346253023
    0x50103020a090e1905030c060c090a140108060904060f0903050c100507020307080702040209040501120c060f020d0c0618050303010e01050406032d0813050a0803030606030115140307110105060102 86
    0x2d03c0080003100504900030b460000c5800e00c1032014400c0d211444207101561800c0000d1108500a00a052425035168403020034001201c0c10340d84000301200c2e190b03064903c02e913001000945d02040071148405142d886140110090901e8500c801d91341d0315100b4080d040641102c01003522041650844001c449000c00000c107843c030460b03c400041e0424051800041c9111010306000f40c0b0003440542000415004a13003112001d0b44a04071114141156400740441d204003003001d481940b510820b001008240a582c41040120100400128103491002d1106030b9004c41c100c21054180d5807030444a034140141d803074201b80149043c00d50404000187d6250500c101d104807540b045000c28071500c00c2d44c00301e2030030458103041d44503130503044400c00c00210880c1c001e1018603500d11401108600308030500c2135403941c03030304a03c000f6482041800080d55481090781d0464140028096507081015401c540408401400b006090710200510859941041d507801c0000503050081245a072030b40012 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 346255521 1250 346254271 346254281
    0x150518100e060c12120105010e091b09040b0402070308040203100507080406020304140f0d02010f060e0a0e120d0c08070203070b01030b070306080714010824041806020d050103020a09 80
    0x4202003005101440942d04201000d07225014480c1d050b07400c0f005003620a20010b5000d40125100b4405160040c080c0d50780045200c04d0103402541c40680310303c0e180e803105902901c0b8800e4900c00f81e50214119043d0754480e000410040c902800642d10765106280c0684408002c1d581207109010301e1600c0c00701754200c1c1c800c040c41030311305944850f2252510384809009503c0a8400c0e602200d401036990840b20013001944020440707a00100094034000e8402421103d02c2145019071900340b007400c00103180c0c0c60f0306180c1c015501031310015040a0403000320f840d00109150040c50803902094060044901d03900904400560340c8901d81140e0f10b0500407a01d0784950b000003082e59198500500c00f1500a031304140c1d0184450800040494965001500c0d0602590100303000d070380006003100107960701c1044544c0080034000c00c4180110b5645071500b00d600d03040b0005004643d0b41f420785003030041000030810041d03085101107654001444036440600024001a40a4114510f0015190241d0311030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 346256771 1250 346255521 346255549
    0x303050c0a0c110a05040c020a0501050121120905130506041a030d0305040519060e07060905150a0215040506060a1a040303031a04140a0606030603030e0904030306150518 75
    0x2030b030003180c0619a1400c0312602c0b4111110b820548494001c030707403070f2100d106040c0703100c41640041022100c50b01e0081d0940f00145c018005500305c4e110603000717100c401e05c0c0308044564000348101300d205583e03908032204003840c0d000d0303a0303c4181c01140100b8503505900941c01090f041d5824000c01021341c200150b000710003265650190302a1a1a0510610070b900140d00b00d4444c0098482203868000310360300024607080c1c2900c4140d0303200100300c00c2400401c0020018159414a000c06501d803600007200d2a8000022020700c441c00540c50074414801d02c5540039800310003100e100d05003441d0801030f90741e1000b20744a6000c1c012000c4041a0503604103050500c210403007221614007802c6a6044000c1e015a204020040d100140c0307110003543d035406030701d1404080401d0000a458418125025951a5407210091618043c1c1c10300c0801c0d408001058150b0050707616072020340701c41c070b0100d00a02c442c0c0d10100c12885441c00d6184502d900000401c0c50310031080b030707440d0030fa0400340401c81c0344112161 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 346258021 1250 346256771 346256777
    0x70b0c0c010801050f0418080c0c191505031806010603020901110a0c051e0607050d080117030f250303020307121505040e030d0203010e01061715011413120303050c0a 73
    0xd00070042c900741d0808100e0780342c03d000e1b00702240c5c19550323460304039041224080c0280e0040c0c030380030f861401c140011100c0103040d460010125454410103200a00e50035800c0d104000380000041c40041c1c400d221030f81d030031000c0d404568242da03445c40000e00070342111034540d001030b24003030051400442c0041d1860384143c004c8101d558991501d400c01401c07048020310341901d05440500100c0558072040600390301800392000e0600e491594030001d00d0240142c0011400c6c08040042104e0500300100380e5500c0910010031369918051142c814005940c0460b26040190720b0614403420103034990085e40c040d06240e1200c9201205000704503082d5000e801d2128446035600400b04010701e0039411411007034a1034000e9034a06480415240183e0740b090300f110115104200c01000010f600003035826105030801e4105003c0c0c00c00022013000841c000359280e041080f0031100144507a048811500c0c20003010b03500e0f071402c0f03640b141e0240e80c0ca0940d0009601003450303e03000030082c0400c2c07000c841d050003240d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 346259271 1250 346258021 346258039
    0x3220504061509060e0103060b0706090b01080a05062410030906050606040506220506160302060708040506040b10080d080118020a02070902130b030123031c0503090f070b0c0c01080105 81
    0x1008452404100f505d0034105502e43e000018403010039401804880d00500c1d001c075040c2c2d07442c01c1036002103c040c1e0148106d41d0010f000c0c40c0109e80f01142e081c0e00401007002d00c094a104041e01340386080200d0704c040d0342c0036402500200c242601688200b11080c4202e0f4140a90342d0741e10100f0102d8002c620510f078022004022440e640c2c80301ca0b0cc0e21982c040303d200c07075068840e1240c020502d6600140c00054a207402030100d40145901003200035440021403810708030300d2a0035a05d05031035880182c00204820a40800300e030903143c00201e0000503110820459417890f02c90300d00103129100a101b03010245070354000c021016400390080300d00e00758858000b841402d1600504800a5004000c001e0080420480c0032524840601c0214020a05038042203004008440f205030b40c2496000d116110342d01201a03c3e486603000322400c60079010b02c0c1015516680d42d404018180000407442090b44d0190f0603020440030707020340242c00f10a0840003160a803080100056400321428024658001520 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 346260521 1250 346259271 346259279
    0x30a06230103051f030f170306060f0a0309061b0905030303010e0f0c0705010f0207021018060e0d0f030906021c020601150c0c030b071d0609100203220504061509 71
    0xf0382200e0b40107840003543c071051803025092418079507099001102c10322030718401e100c244484481c440c004044404c0038a481c50a02100145040c801c800a0014041c400b00345c02e000c0343d01981c0714609164102000703100050b80c9903507041c0e1600c120007142002c51076014004c03a081c240003040e603040e1014101640713007640b502c0b40502e44142006002e052400340421284c40065428000d59100600300e010140c2c41e12418410400c0868138101e60030104021240300c80202c0c07001083c120200d40789800d1105915403075401003400007081340e1010708403401d080007480802d17902c62001c070101d6120790300380c2e0002036680307550014208440b00d50740010390048005006e19204601481105882400c01c100c1b10119a91000352003000d40e8001d44226207503a003040300031500110254a900c102c01d410f40110003820700095034501841244a000308450700070609510300030402c031901141600c0d044040c4500800b0459a086568040c4901950405070001805500c02c1e01c4450b503d9081e41703c1d11101400c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 346261771 1250 346260521 346260527
    0x60403030209030a1202010911040507201e03040306061d0106200a051507020f0601030b060a0e0f070e090f04171902070302040b0a0e19021905030a062301 68
    0x502d2981e858002c00d26010b002500d024a5821a58900d800101d40e1803064200100f01c0861041d00ea03000314108420000f48591001001034003901c00407040c05130b010005091440d18454403200d4421084003c40c10440e030314000064011a0300c200c0080c882c181c0c5884a2030300441018003c0301440400c3d00050003001d0060444071800444032800c2142c07000200c9081e0301d807a1241c0000d0710a90070840c0103061025501c0111984605a40010100340c10946605650780005120140050080308007003200d69464480700c034010308025150303100d20b042c600c1c20ba4160000551f005030200d200d041940c1010301382041c9540c440d0810074a0410710f03036a41c0d103403a03079031940035400f18031809400c108440d140800e0490601105c0751590041c2107550941c130601044420040c04e040c07050216400801c03141c2d60395000c055100318802c003002ca1440e1034911090103030084d0141c0c9100c00600400200d20f00768007101541c89a0f140440601100d996860100c80100e80c2440c1481f985009510311038207940 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 346263021 1250 346261771 346261777
    0x20901050301091109040f02030703050c09030a0303020d020c0d08090613110108071403131a10060f0c08040e1f06080a11040509180f010605060403030311090d0c260604030302 77
    0x41c5080a1314505200e140001e41144c2102403450050344c1c2c04002c0c400d000741d041c4142a400109850107503d0400c0441c0081da039150001c50040400d03400244a01d101c1c0102d0f016900c00c1a1828126541c2600e424005032081100700c841d6070071072041600103422040700c0c005114034960001110b0240c3c0c0c90100044400500040100d0240b101c40480048038210020042d442aa960609550700c1d684519140b6410103031906070110341d001420500160030f244411200c1211034905001d040f840c50380105488811400c18090041c4c0800309000401c001e1422115120300e6000d0034881a034460240059150383e5a8020100000d6640707000a0700c0f50702a0340840c1c605510b010051741042d81d50000074100300c000b144e8410002c2c07944c040400da11a01045240405102c050003402030360700382004640c050080b8800a02010b8541d0300c0b1100c1d4018010440fa4a10b10140620150091500b401d98880c8018462020498842526000142803488103161324210001c0035001907103903901c0480c0a90 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 346264271 1250 346263021 346263041
    0x60503030403060c3f09021203040807060e030325050303090105180102191211030a06030501050c0301080d1809020a09050a0b0906030c280e190501021c050c030423010302090105030109 81
    0x6580d40c0350740340941d80e1074042c2401c03a823991000799526420009680e0800807607602c000244142080c19442a690100a42d110a052400b034004d03031003003484c0703601c0380c400f843d2401814a0000206010300f800e01908900e10803091020080f10800140f24000c0c00c07032080d52620462401030850b41c503559841100c015804000113400880c5450f041d50040302603500c25940703103d00541d06e007001c100f042020b00400350b001072016100d50a640c54440201d13126480c1c1e8400c10200f0004245004420107410542741c00f1305407092045465202c5408007510101050080e1031180320105400610011790320f04549030410b020301414150340b221040c0d51900d41008a02c04020b0060b09480254644010158107000c00d43d643c0302540000741d841405040d1041038400c0045040800083c455070f40c0000f003c0c200078138081032402c00c0b080b1010044404d402904c00c0c0700c002d400000380c0050903169000c640710b80303200c0c2c8204840c607a085000041d0100e1141c1d0016a01081092004120500460340100c00d51 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 346265521 1250 346264271 346264397
    0x30207051e1809031e0d0f020c0a080c03070803040b04020321091507080a091404090b040b06030c09011d090d20100f0504050c030c010210020d060503030403060c 71
    0x100b000060205c10824840040400c4000c000c82c1b20342032078146014001010440300e10440c41d143d03036030400740e882d11b03010f500c050580c1300001010400c45400b04202e40403030390000f41854032810f00c0d14040e0180242950242d00c42d2040f201c88041d198080d09002c400c07000d44141040ca00009007041c40404201e000c0350b140800e00c180060400300c0d4049000307180c8042030f507a95000300750400348407032500410451b005008038508403070383d0001403144004036046600305540203259a62100042c0c84c00c088a00038a420204c50301c00018180c8004041089201d281c5078071480c16903c000c00d0541e41c2100d219000000b484500c64035028900c0000300c841e01c11002403e449241a04035000010b030380d000000c1880043d916030802040c84000d01001164150840140c444000002d0000b980c46040074143c0c88081d0b80040d0314034a083c640d900201c014038010342543d480d80d80ea03040030402050005413103000708941a0702110358110b246548100d40ba02040b410340c0040f040049280d020f81c83c0503102c415 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 346266771 1250 346265521 346265527
    0x309050c0a06021c0f0f03050c070c06050c15090703110604091b090501170604050a0b04240806010b0412080d020d1d210c0304030f030207051e180903 66
    0x110303121407029030050140c940080c4203400300000c541c4084e403500403c0008100e03082c10120f0005911030f0307898240310070034500411300340ca8002074090288105440100900703281540000c0d000e4110020384515021075081d5503a000c680d4607109a40d403400c607292026508118018000a44154121849080040c0030607060030344070150701307048507109410a1004100b90355419502a40203e41501904c0c0030300c0e203503905409034020b5482c04000600f405108a03125400100c490489612000c481900280140030703a03030740d5a0480e403080c21824105c43c0152a500c001249070f07640007034228100c0c3d010040041c54a4680030b45c03400300c010603010855081034200710000c12080d4074005807001c04c030307041400944910718801c41d4840304000201c0b050b407508000643c541b0b001e0010030300c8000c0c0c44002e1010f5654076800d002281140b0840e0801001c2c04034a00103e03080c180c0c0001d8030300507540c090703641a0524080044500e1442c110886442c4e000c541002c0410031030388403958140d0849049000c03281 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 346268021 1250 346266771 346266793
    0xa050a0b06070c030203120a0e0d110315192715141812040b09060c03040e090c012c0a270f18030c0f0b0a0b0909010b0105030106030905 60
    0x1400b80e22401c01074800c12445001801580b400b4007a5151014042031400d15020301036801030182c2d14003684541c40703441c002c01e010701071240c1002901c0290300001c040c0c40340780b0080c070000b2010160603542107403460040c51904012420920076201c2541044442d40101074503c00d22981a01f08190203c900c22080f00c1a11180d207181d000304960b0b0070b010003040c00c070f0b890310101020300140d1101e604c0c4900e41c01400383e030045a1000c030444040d82c015160f120756845030040803032000d100e4440c1c4001c0b14400000e002554890002d5894000e04981c0d00f40e462090942c0e004443c0a04002d880002c1a0042d119004050190f00f988030300144000e8070001c4d51940e900740d10110701e90b07000e100068078070001200e0b004882040c401c03101e242402030720030442d0510040c2030409418103400001c0138004507249030024000c42c551440200c0e0b40c09007441c6070718a803100b550409003c6c010031150143d000040840c0d460030060050144a24069407003e0541c2e280c410110040e025240e000e4036207028002c40743d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 346269271 1250 346268021 346268029
    0xd0609020703170c0705070b0306030d03060311060c1c0203030103140703020303030a0b040906060303111501030503030f1b0406020304030606140f0f040902090907050312040f0b0a200a170c060a050a0b 88
    0x40c000306022230080b500c03440d12009043c00d01121001345010549844401e000090000318895404c08058400a4841c08924040c0f45020603184442c0e8907016080c0e264900d0550020045060700d21440810506030580c06245a0b604018007000394941c1050000903900300d00c50b03101c45440b040051020034000100d4032200215061500142d0001d01c10102d06080200e082107103404407565050514010362550303e440351a400b001c0c01400c1c000300d007030300400d0740014400d0501c294103200d410f0203039889a5414010f9920750040c0720442c0c0c4141018000100c0c400c010341a00400d4070003410100c04a04244100221010310248107a030180d41d40360343c01c015883d402542c1c0d2241100310018405641024201454001401c0302c1d402440000c12003400030010103000381c0100c0303d56110307040d00c41c0400c08041c2da411458446442040c480075586a001000004640403218010394603c0e000174040680019030344241c0710b030180940c0c44030b40481c4244c0800d60296900a00345840060f001342904002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 346270521 1250 346269271 346269283
    0x1513090504030c020d050a02041a01090909020406050306090a12140d0b0103060f1806050306070c0605041109090a0309080706021209150403050d08060612071d04110d0609020703170c0705 82
    0x15106e5900404079881141014851301c543c24001e5060701c1d5803240313071100003030502d141e60150904980e19109040c00f107440380d401840c082e2800905403421344c0751942c0c480e90340c2c01d00c026080e01c0d840c0d052046029050f000e0780b8a42c52100260015071300d400c4600c00708401a00c643c0b6890fa0400d0307668000081c000e01001c11100c09460f00301c0c4c00c1c4000650172440b10b002d481158000307500c41d0b0403400034041a1a0468809190179130b10013004103c0c3d41e80c5082c04012083d25903022038101800c0410002d034010042400d0070454440d864500e1441d46a06005a0b2038881d07014000250703008000c4d00120302000d50183c414100000c05c040070306d9000000202c21a001544225520351140942c1510700ba0803000296115000343d03880c034200021203c4c1d88002e006e010b040202442091402d004001c0c8102c0c0e58408a0b040190050010341d2000d0440060399200242c040aa18584000414400c580d4000c480c0065016910809a0004161000e0b88440c0c050b0110720388a50400100000610a10003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 346271771 1250 346270521 346270523
    0x12030a0e0c0406050a120f0606030807050f2e110a021507020109030c080705010f2909010f03030e0604081002031e1911120a05061513090504030c020d 66
    0x4203409646564051600c04919541403060f0b003041d000f80169119042c1000403285081808481e9400b181016224035400b003601614281c2000c0c6c011040c000d0110007810780c24814001c80d100c0345012510541ca8081401484021048641c5000100340d04070713842c0f001e070071212600003801c0341030110100314540c49585014091f030000041c140704403c8640740580e0002c002e000912082c4bc00780e900900c24070032440d009100b09004a58a028880e00758040422032821384010001c04146016606c07810f040d03d040c0390116030305450303092905c2c1000d03c4036034102c03141c007c081c03908107080d42e800380e07500f004240c6075a410100a120002c0c1900c404c01406210302140140140d880c2031241da111041c018201803404011070f180c092018a01000c84c800c019040d40720310009400491152000351442140c9081c1d05030f041c004180200f80d01254840c50080801700e4050524100d000d015203094010700201c0002140124410491121180c0102340c2c024403031300d04000f59a4242d40044c01040007240 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 346273021 1250 346271771 346271791
    0x20f01050c251d0a020a1b0b04212c180a0506040c050a08061c052404020a030b07020c060a02160b0405030a06020f07080301030b0a0c050301060c080901021203 70
    0x15222642040b010107000c2d100703078442c0380303900314440601500858000d081803c48030360018040e01c899105a1001400c42c00414aa40410000c0d091550706500309607010348100c0381c000c400d400b41079940c08403901c081506446680d0301c0c0d14a01021103a1804281d1600c0c000d41091111801503a01d00350b16407103c007403242d50320305030f402c008040f0f200700e030b0004003168000d620344612803010940100698107140040c0c507240c00207540c0c4d400452142e0964108402001403100084010480046100da5036000c5041010a40d00042020b5502c030703010542d0080d4001c072540d003080c008110300401440e0702a00c034ac011103203002862001b10f415580000300e09030040c0c1064950274900c0c12a080c0c000002c0c09500c05003400c1c281002d00081e00c54500e80402416198002082451030503e2070a0f91122504040c1140d140e6a42c1d04060280800841d920303d0f42074500800081040e000f0360959060710080d0391081550b03541075490100c10391107040c0c41d038150f204e050380442192111000031403003a48000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 346274271 1250 346273021 346273063
    0x30903070303050106090506030609190f020a02060c031e09070302131406010e032a030106030602070c0b030405030a030b01110a0c050f011e1b05030d090b010504090c03020f01050c 79
    0x414002c00311601038008a04000d9016000c0140b95600740540c1c2c2c000004035410501d6442d184020040609946003841017203040140620401416034007600952410307030291541591881c002c2c24040c80f0444000482480c4030524450380c41d06d16552903401080300045500031602c94001600803c104640ca20625403611995039101b85080c50541d0040000e00b068000600c4410009483c0e180c86a2814650503c0c10442402c20014810040c00b020703000d802001003c0d1241040c0f4041d61050314159a420111a40004d6594641040300d01c01d80c0c002025600b0214152411005000000b0450f4100440071408240640050080601c214071481500140310701c3c00d000d0101d01803c030007015041c00350345142d101811042200e01156000c80c1d00e0500009075000040009484441070007a11901c1702058550f41054035034000324086001c4c2001100c20386c0d840f0100001e540e0307544801001030b07000c03078070070401410400d000c1c01103003a05040240c10884241d82c410f180c02010b4242584c1440f400c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 346275521 1250 346274271 346274273
    0xe01050a0905060d0b090109020a0b19050a17060112020d090c0b0f030a0c02070b0318070510020a06090201090b0705010203010e150109030f0f140a03020f011a120106090203090307 79
    0x90840300004220210303090003203140c08000130707001d10395141c40035050541201c00200701c00c03820350003024826030051030f490300b503a19a00d4a00d910741140b1305400604000010555406000e4410381e078201d581a134504840b18500351000c4d020000241c00c0c03038184132300703400c0089929140b0300203001500303461900052440701c107051514440425a21440d0300c40b00c10011071a41085400c1102e501520074140480e4081c01c075181280713095403a03400507004c078402005100b07030a0340381e1604003182c80d00041280c004139181c1d01040407259140c1700700790140e480b200005001400701e82080280c1e03070050410705d640342c1d0f85580449443d441500100c0d4140d6000005200c441d05050a164018021000c640b540203581340c00a01110464000900400201e000341020048102c0100d64426480803008011441c9000342a940f204c0043c0100c0c0035002d291070841d000c00c01403090140d40800048103034030140c4c500050124503545114001c0c030355501d131407000c5100f0410380001d5002c2d00c41d54000719518445 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 346276771 1250 346275521 346275529
    0x503121303080a0629040801110c01050c13030605060f030f010905060a091a0a021606050f1303090911070b0c040315150b0306040b03160513050c0706090302070b040e0105 75
    0x1c0203103c820b035545480c0050045c610340903041d8428803c010320b01c0c00c00c0300c014418420341d80501e030b0041c4519030030700802e54584140d03a8098404803e4400080c423403511001e0b003c85041c081c05001300c0910000000030400720341a5005184c1019019181280140134940480d0030249a0104290280e4580c42c0d00d07410410208001944000f03078503030412000b0850390780c1d0550400e001d90807132040240c120100340e129105a0403981c0c0614007041e0750410341c00b00e16102c1c001d8103007143c0c602100c120345400038008e400344004019400da410340e11202079a080090f40c40041980610801c800c100c140001000241200310090041c4000110140c890b0302c0c614002c42201e8040e45d42800302418060f4818540068103031401c1074801d800c80c40f90701ca90701e42d4007040003040110300301c0d43e0620480760140510005480d0160907120142e8031001d070860b80741154000d4800170368080c160204204040404610700d43d100d068554420310503144501d40e12041c0894580242e009003010455070801040a454 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 346278021 1250 346276771 346276787
    0xe0705161a15030c1f05280e041406040e0708070801020904060602030c0a0b0c16061b020d021f020f031503010609180b1b1b060907031502070503121303 67
    0x4001c43c02400e00d40c85090104420b180260046800301520310030001020303004005950206021070403841081403044910414000c6409502d0085805214040d0442c01c0601403120709501003c2c1006203500c9039400e0000508840329101440d01a0190115441c1d1080c80000000c2050000150701c40342d07442c04200442d07a256011034103550003002070341742001e40820001c0c4103a4210780c459800e680d40050354180d80c441d080139000c0000946220f10104510f03030380140401003d41812862060807947c0c20b0340d5500b80d03603680d600035a014840113945c201c0400720006000c1482003003d4241811582d501030160070584d02d2104003204030080381c4aa060902c1194000c0030b84035014045d0a456581c1d0f51003491080c04041d10b9810803000003041d03041070076454140000e142c05550f6031030301c1103130414404c001c0c01141c0b80854003c44001c140e03540c5c000202502940d0b0841d040058101e01c0030352010082d03019880c100d40900042c019440c2071001c0b817090341d119010149140303802046902c0d004184203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 346279271 1250 346278021 346278061
    0x19090e03210403080106030e1002071b09021620030109050d12050f0a0b1f0c020117100e0703060509010b040611070b03071d06220f0e0705161a 63
    0x100340070200004240d0010500b4111480e80c100000e012042412550600100e03407482806c083c00000e102040280c80703400849804282d5440b81c407844c2d159045c042c02d91042c40c07590610f6003a40ba500102140c214562425001e000310f00054004e459000403a081d140d0220080c0c6564001c040c150324000d0f085514125000c542c0c410812187c0303060781d110995001d02600c0c481e401036840c000038416031258440bd050001d440413100c4040d0405280080a400e14042d00b280092042030012051400d4a89a213010300e09410050500c0c41c201380b005c1c0c0c030200c40140000101612200006566100c1d00b1019020b4901e1040311903442d82071003006044820340390b1080a0560000380704100d120b20310030a1365080440d0740b41c880d440b0b803260441514580c000d0f0030b5035540200001400c0500258852445240440015a041d40d0540d5040880c195082c030f88114058980c50000080e04d1500c030b1002020070360007004400301c00303400546442042d100131164100e040300d04602400709206805444102c40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 346280521 1250 346279271 346279327
    0x506010317070c0e190516180b040302010e060d060303030204030b0c070c030b27010207031e020a0201030207021f110615030a080c070e0903180901030305070219090e03 74
    0x480030543d981ca21081603071050300ca0000c08003020514061607011503000034401164103002c5c038100010b066070302c050017202c6107010a5104078960380c044401080641154818080340303060510703680040d9101920210910f80c480740400c0343c103018030300c1846440c0c007850095a0040c0c56504503c2c060f00c80e000f02425201020030244003050000c2c84d64225075041d2540411128200c1e20743c01c50400d081c00f01802c86030244030a5101c41403d81d80e0540c080c00041d40a40c3d9041c001400e402c1d80342241003051150000143c000b0510800594060380042a0103807024007082e074060941940008442141510301d400140307034041464030080304000081d04004441c003812130308142200000c0d6111a030301c0c00100405404214401414801c0c00740200521040241000c81d1401c0a07125450350b2140d0000b11020481100303107822400d1142e1503605a07a895107a4504c0c0038216001c1054869100016151600360a00c0104528240b0301400446003581d41c011900c8191000c401c1011180c0084c83e014a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 346281771 1250 346280521 346280527
    0x30601090b030603100915020406031a01050c060f060102030706020a02030310050f03100e071205030a0f02012d09050d03060f092706140403121b0504060e0301180506010317 76
    0xc0c3d40110306905e10144100b0001000400d41c03500e0346410314002c00e405041440444d0001d40340d50149c0144410426804207540c03e0000040152014010221801095441000020b9210022115241d00150140110f9045c54200d54070f590990348450391900050300084244400c120894081030050517080781d07017581c0703408004082591030b4055802c107d621074031900000c10010003840700d840507102014801e00424803908029540ba4050fa440e407000442100e08090094410300c1254220490500c0300c0da620700410254002c2910212800e00782c40c1c1d500d44100700010780c104610503a0003460f860116246180c9031280c03072810300300d90100c2a21800e014258a601c050030601c11499024185003616070302c114207261008107902c0004d42c1070318030382d0010300092540101003141e03403031000d0a003809a150700c14010f0808031016400c1c007011403030512040c40107034000e02c8202146034001c0c6c000207000100b04680801c086c3d04000a03a126040a001402400b081e04038a69440c1008a0721a02e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 346283021 1250 346281771 346281781
    0x101b0804081b1f0908060a0209180105010815010512090609010c02010504020d0305070c0803030c030f090a0b1b0c0a060605010e010504030b13080706140a0c020c150d02040b0f030601090b03 83
    0x342c2000c002840341c0307410840c43d001c203250040f0341d442d002e843c040d0200c03400c0789070104014000f580034100c1ca92040b200c0b016542d2040109804860503a1303070603543c00d100c68842c03940320341500307100d40c00c03860601c071080c4864405100c4403000d6038842ea041c140104141d05003000e0060840354221000821641003c04002c05a224001c50401127030303041c0781055888246041c051001c0034143c200c00c20500000003800442181c1e0b0000e14020281c4c180c4000142e120b1100840d0349800750200140144983e400080d80c0c3d80d56401c0342030b00420080d1005141842d503a4446003001024403080b03079a565200b00910241d40d10600c0d18208030030130b09003a0b14090841e00c0322581c51800a20761001c848005800c0020400310a050340d00703550303000c24140400c685800c1034400c84002100d500c6050351600c83c222081a10000b81031120050241a600d20709000f400d003c0c2c00c42d48207407085100680c00300702c0090b202510710002d04d9a4800ca4011580342e081100c001418181745a200481901090007888 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 346284271 1250 346283021 346283029
    0x30d05070f0309030212030711070905010f0e0114010f031b111006050a1206060306020a0804060506060a0c060e16150e03010207031b0f02130c1b11101b0804081b 71
    0x41c014118000e40e007a01e99035248c3e42240d400e003000720841058041d0036000201e4610342d4200a0507100c148010400003505c034098003800d14801d1140f08a40301d00301c02d0400c85035005911b00d011000e0980340100c0e15005a0012030074607110400520700140392032a00c13000004052107208440e001c01d50060100700e1603c00018942003183c051050400030810300141080950b900403030056611820540d00c403000709a001d844640304072010b440745030515000031080d14000e401c690445103151203042c0c0b08501600ea0314000e0686180d9015a8860820f00003495000414450001c004003201c0154260720890000c1020701402c452a000f03078010311038840001c0d081028109611985c0321810705c03000081c144a1585c1490300006904007030480d5510b42c80c43c0640d000b039018164551601d50040d8a00e0002d001001ca40440c0a402800e8851501084d491305461200840e0100d00e0a0313007100000002c503c01d1010814003c907401ca0002030308210b03403503041c00700000914144072044800c1032104045 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 346285521 1250 346284271 346284283
    0xb0720011d120c0a1203021c020a031802030706030f0905060a02190201140a0507030f0e070f0815061519020a02040615080c0f130801060e1b09010e0f03030d05070f03090302 76
    0x71708a96010000c5c145051003581038030f0303100100e85054001031a8034804417001b58003c648407030009040c04d114811034081f205c0800c4c0400e41c0a40103000051508504400901c01000c26200c0786444a41c21f10200b40c00300400360058150000060359034058407e881c0c4c030020407544000659052200c0d4412a814010010354018103560300401c00340e4412900710000c1c0002150f41e610b00b03203070000c3c10852000c0002c0e600241e408401c04450300784d860303005040c5c3d40d80100c441c0d0040039005100140740f9040080241d02929034202941c1d0810030b4180d0462412442c0d00e0610f0010790000c1080819031a043c0980300040020810b42d006081030300304024115200100000300a210000f41d1420440961088a586012110070020002c0d02c2d040c1f014007038034451040c4641e810502c00851041380b07440020300034030f0524118039440c2a1a190056881e02030142540d50300502c19054403c0342c0d107090004001c10303414032034001214548140c02030400c14507001d04008045ca04600400021780000c0d103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 346286771 1250 346285521 346285523
    0x130804090507090f0e280c0f020d0201140c0d02091c020901140d0b04050c0a08010204080d0e100806041805150f070c0f150c0f0f05070b0720011d120c0a 67
    0x64078024810061110302419220030007440002c4c41c0c00ca41f1680c0700c0c0d010a4600303142413182d00b51000340d415104101d0030f03035405d8540c6070720034144080841c01603600c8030000c2149000400d0003600344000d8500040801003902c03e40e44400e42e000000e48210700d042a5914090b0040c404180c1e00622014003007910952305010041c144250400401c041c03000400c1110005800101030035021511240854084d401600ca004198400c1d00d141440380b0780542280c0704055130141c10541e8010b0210001c503001107000d0f10581d0040d699400900586e510484101038450040004092240c3e81c0081940544c074020158540da1441e10b00b407041c2070354070040048000e50807260746000007005041c4401c421a0351041c503040d0614048800c08030315003004290090001e692a8035202e404d0708101662079100d1a48001c08103a41c0321b00241c00039004445603a04150608a94041034080f240c0c50390841c1d0244555aa0000c2e91500070540100e0400c10382d02c400500721222402c0514941c006a9101043c0e10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 346288021 1250 346286771 346286791
    0x60f0e0409062007021305070c0201180b0a0c1101230702040e0607020601050a0f030308010b181003021c060320011b0c0e0702031e03130804090507090f0e 68
    0x56940d0034402a500032101c1107440468010140907a014030f00140d078010b5000b24016100e901c100000300000b440307080d02c503580300d880e18480302e0389641c01101c0d040704640c0820540100c1e1034004c5a0210400041c0c01c01c030540384c0320203283e080075051a01020084c000e480b410002d40c4060810075000d501405a0700000062805444141505c0003602400701e40003900d10383d118035410801d035264005205812101c045d00c2031007145864940502c0084d807036020240c0400c45000040041c41f04a40090000c0d40c80b40c80c0120b00301c034a000002c0c4d05030000d95003280c0041e80100d48998101d41001150341d800d01006030800c8420302c0c654a01145913044504010003408440c441e030300903401900c1c1c1e002c00040c2e0b099030141a60007441d02d0700401002e80100d00c0d030310080030009081240000211050301c202d030b00380409044510325030307104c05600091032110300d0000490100e0001d01d1303107009807018003442080410b03a460000c10003025003c00e030b40303c2c0c040a10603400800c011226221a1342c0c01084141c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 346289271 1250 346288021 346288031
    0xb090a0c090b03120c0a050a0f12050f0f07020a03050303100306050a1e090f020604081b0904080702090c090301020c0c041808040e06013b011e0c0c0806130c060f0e04 73
    0x480c0f12411b200c12404042c2c158042c8440000c20881a0300c3c0c200342444c8100110400045041000c49450240c52030000c0032450070483c0c071041d00182130141030280d00c01840380c40030755200c1c0c0e58281581c00950f805039140b1032501c824001c2001602640358043c1502c9020400801001002e12400030151ba2034050348d5134803c0d52006100c52292409a103a4003c1c1130144ea540d03640082035512050b61a0702220b40b160002012854030b0304401301801240c014010798285483c0d5007c01c901c00901a190501945041004640da40c60078000b81074080c10500160101c000c502b8184010380d400d6a4560401086400782c0c100020504000d5800740c608007801074090ba5108001a5010515051207901071540c083e403105901100f0040004605030301c55542025070260b00c0190703140d001e500c415030026203410b010509201c0c0b062000c40f43d00ea01600711400600da4600100342002c2040d00c1558500c078002d0210b00038460381c44455002880c0503d041140c0c07006030300c40184040c01140c6078511603070f210 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 346290521 1250 346289271 346289287
    0x4030213020f1b070902070308040602030a060e090114010f0b03010b160f0809030c090f07050a0c1b080d0903081602030a0507150e0f1c020d0b090a0c090b0312 70
    0xa5415902d07050780d00220a540c03000078400e048090b04030005160098402c151012860202500a550b00c1550649400c101d68039665140c0000e50401007015807003039030301d23200000c43c0505007505034041c0590000000d2000e0488500690f480701c16001210808000541000304032029002c907411601d001070159210881100803440400310b141000e4914840c0c28681030500501000415203158101c08031039144017400c06004d065075040b541c1e15158415107001400b40b0b4020802058501403614001018a02c2d03942c540c0c006001c00c0880348600111040103000c240f0382000851920040e505000340c240b40b650342e83e80c000b40305078003001c50820744142c1e03408210f403020016810740c1c030341c00b0013950f4083c0e0303d41c40200c2d4189e40c0c5803461000601080c120703444c0e90400c00e40c1644c94610151910440d944294000b03810388004100407a0428918550341d40481e5900104034040d118030720151420355042d091050601903d5000010b1551400300786100680e00020b85007407144903e181240c032042c075 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 346291771 1250 346290521 346290559
    0x90a020a021207061e052703220302040606050c1902120f0c04060f050a090515030709050a0b04050112030c0201050c15010915030c1a0d090809040c080c040302 70
    0x4a00c03922419a02c1c0450720504000580c2c00403561140003100d101c0014548080c59415250191a121480c041c15417000710701355880204a608010f0600444c1d141a585e544205030305032003140079048580210906004500e010f004001c020500380c80c0140c18011621101030300c0307003603034003e500b0006200388000c2c00b1500d88007030414481564005a0312422940c1d100581c40c1c4a8408003c1d108134a050000b08000440d0440d071000e5400141c08182464140325000c801040d0141c204004035103400303100f009964080000001a04c4030740740129103070500001c50000e0b609044241881182000c0042c800e41d5940d0345602c010b241c25162009001c50341e0f0005952920442c402409540520344960010110118815048070321981e0108a5203080000300c0d41000b505020003058011406c10420620f00101c2d20140024966160f041c07a00740001c40b600220754000f00201d0324541c021888548030f20b402d01c00c0814070390260a01c450070b407404e030300d0603100c1340705074040288140300440c603280039145 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 346293021 1250 346291771 346291783
    0x70303091202030702040e062e0f060c030e04050408030f0403030908030a20071119050306070c030314010501050423030109082d0d0b0d0606090209041406090a020a02 73
    0x40c200c034529401c03a80d2600000e480c1d900014081e0700883c245006801c0c41c840001d40d0b584101c0350305101d02040600c44146c56180e80081c42540000c03110001c02040000003100382c0703001490981c66406c3c44403404e1030098118900c1e10009403041d8030348010400821b09580499034824200700364090507944900c1d0540003482c450340060300c8140003204020200655602000c10340b0304c640c0e082c1d2a0b0516085809005200e5000c00410444001c03203409083e0801c00319090300844c10031100c1400030b4550010910f0308404440301c6001543e0b01c0181410b060f014403900c801a102030721a0701156042100107010751286110710410b40400c44140380880c0c84000640c0c020b114003c009100e4a10746080005c41c030340000c40700e540d1440201c1d184120180751280e0f4038800e00d0040d045e26042121207200907004100c180c01444d0007a40340c06000000860a03c00c003006083d141000603190a69070083c00216001da81e1380810721901d800511003d640c807100e03c5540103035200c1015980341684441241008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 346294271 1250 346293021 346293023
    0xc0103050402060d09080306130908040509060a1d06120c0a0317041a0c06060d030c03080a0e01020c071503020a05030609060f0d050d170106050304020108090c0307090b0906010302120c07030309 85
    0x50310b0101700341c0801881000641c010f400072a9001d00c400982085002260380c1c4210003443e0b80e408100401042c04c1c40b50486d544000011b01d245622595071900540200d0a11070000c2c0100000e400c105503481c0148044c0c0040704001d000301011a00c00d8045240340d21140405810020701c4205504801d00d010101e401508100c000c0d458403900c1420682c010750448980f048a5000d0400040c0940c240780c14580f801c103406580d82d660701c056640b0252103d00c0c001d010080c00716201c10b05443d000100b40000d0a100c8403003c01809490310304402c0b00d4426050321000800c041c010080c01800341d03400010341c1e0700034004403a02c00e81c5888440c000784202007821481c41c0c00110f60204082401030106040401c600c85480e81b21050380101c0e240e290007042405941c011480502c00f00f405540300b821066032109900085843c04003580001a1802010b50f100320b81e04c40d1a81045d42c0e13142810220903410640a080940c20480c581c22550092100181030783c0b07040c903002c900c21f014103200b600108095 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 346295521 1250 346294271 346294297
    0x5031903061409280e1c050306060d021e040e0f0601020d090e1003060c120b030d140a020c0901080705011403060f060a03020f030103030c14060f070509040915200301080c010305040206 81
    0x51704420a2403034803908140003048111000070f0241c640d00d80100c0c102d0380b041500030005498020880000343c029002444041ca16108410f60060306140d030301c00600240030200345d042e0152501c504195150790004282c80d045401c6802c11504a03908007a0350000e540403807800d20243d42e41d80d00c240b8000f501c154406802c080c1800b41011145810900d4000d00900201c8148603cad91500240740d55650204400c00c001250043d405160304980303000707098074444920580b070b80e09003084001380010800703800014054000030010002583c120203040d64000d01a422982117140020002c0c4d86607003407048950145400240d96499548650304031440041100599038907542c40e41001440004030443c03c4440f0221012104604030340024100c1c82048030400c45c0c00b01d41d039440402c0340d203604203a280300d80140e100c200101c001003001c030360341c0080c844c46400019601c884003805041e01380d88103104400360408200501401a0211f0300d5240e820342800c012035a034484d440850702511034520a0009 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 346296771 1250 346295521 346295531
    0x4181b21060e0907080714060a0c02040905070512060115050f04032f011d0105090d0b01030f1209030f20040c03060305160b04050d02010207030503190306140928 71
    0x240056044a41d000c0e5202d441144c98003a101d004041d9100940d0143c01d444000408294280d8500040207000e9900c40d0314213080105000e5001c0f41c142c0715021380c21542a0400300e0140b02c02c0c01d03c0b00030181c021102e0750003081154501401c141c50500d2500c0c0e5041080f00c00200300e80000d14820480300103550002e02c030038040c14182611206030300d8049c400c8141c00c14004143d03000358854000c161070704ca2001c0d030150401c4003034801035401c0d0307000d074030081e4025252115040110702c40d0b9840d58021805014100b02d180081c0c13400d42c100d015010384010074006011014070200b1032800342888042d0740622210a11070882134040100a445011079501c54184040b080450754590000400c40b403185040f03071440103681444d00401d8925008201c110f100c140010030040c40e0103440301900500600503107407030380d850f07494160455109031a401c203400070000040f88200d6141c0f01e14002409100c03420411000d103140041e5900000ad03005203801d003403540102594200402d03075903c440c0c81c07001040007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 346298021 1250 346296771 346296779
    0x27050a0f05060f06010903110910090c080f0901020c03030106080408041a0a03050c3f01031a0106021506041a0a1d012102090705070c090204181b2106 66
    0x3688850407200710380e81da00b601004c07407281d5000d040c040c42030340ea004651300b0004841c8024441e40c00401084001014a6507800041c910113501c11024420490782d42c00b042392410f1032a0301d1900002030222650f6a10400c459400c100021080e80d0540b401403910040700d0301d403802d0078880d40c0525080b55143d0303040c1c031200486110a2100519a90000d62420f00c078a65503000080d810340515180d0200c0007101b80707500d825051541300e202d100c1207030340325000481e4152038040407a115004d030030031651140688007007007003c10458013840c01081c0318401402c40c0d03044440d2000052030007400080c05070351030705010301500509025408003048050010020196111140c0d03101703072000403012440d151600004516040f6901950701d0a804c008002d9580c0300290742800103c1d68010a06401c02c40244900400100051a900e0081107036500c05a2101e08000111000105019025030b6003840c211405d140d4814510320f44291080b582089441035004038034000c400300702c08201c444018600b0002103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 346299271 1250 346298021 346298023
    0x613151101150504050601020114180a0501022d19030b06120f060109080c100c0c08031305120a0f020402090103020c03030c0c060108060702100b010309020d0f0b0a27050a0f05 77
    0x82c12100200d409010035260300d8016422650481d07040082095643d0000d0340c5184884c2d000c24000e40150110b614480440d200c1342d089070409088400c14014098070142000c0e1a010010301196100c0c1c5031600e4010080346ca8114010345003da101072685524101415960345d90503548100c0304200410350500c2c01c01294180e660b0110717481c90200d0301140001c2011603001654040c0f41601030052031607684400810784400010080440306003e81240c0807650003810300c09011200c0d60010340d40e11035828081004411050401c2c0610740368840d0b0040e002140d0030100059103550151001680c502140004130081e20a244070b5045600c000421700c042041d1000080c44e01e0303151003081da402642c030380700f9241d2110000d5a81100680c0000c1c44015500f030150301050f4403800c14140040c4030035a40d401321b1131407514250207981c0c2d100310040342c0b014003400600d19648420325a80c208401082c00e00a0010f2b1003001c1c2800743c114240d00003002c100b00e01007105400d06034001d01c00d441070307102624140e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 346300521 1250 346299271 346299311
    0x1504020109050d030e0a08010b060421050f0a0303110306061c0f020720010f02061906031e0c0b0301080a0f050717100f020313030e011215140613151101 67
    0x10340c006c140d00c15000070021010300c00c18070075100c000c014500d000d280680c0150080c110309081c642d2240c5420354400042c9003048124207071480c44000d04100070007810040d0803504000305000011004000304901c3e0341c1e42e0011901c000350308a00191389a402c0b407200f10014030045000040892000900700c06201d603404441824520400c2800454a800e44c01102c1103030041c09183e026900c000701040d05451482c0010845c50072010001a1142ea00e44801030140710640d00310403550300008803a0b080c00324458a003000341814034001c9246500d0f01c5450ac1d030300c443c003107030180c0040055250b8004020080c0420300c01000200d4950751448488031030f03161540c078180d583d00380071071515035000c0c0386196500959220322184100c0404a0a07951010781c0c0d45840c40107840e040208145400010014078071810b0404545114020380050500c00903a680c0707540004010f2040d20203004e68680141c20a07082d00c1a18582c0100c0728881ea41114255031105200d114050a9402c00b1010414a4007090701 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 346301771 1250 346300521 346300547
    0x7020307110a0608040b040f0503070f0203060a0507050316020c040627090305070807051c0306260307030f12020a021506040b0f1216091406121504020109050d03 71
    0x41000503a5207182003100d909014481d00001c02c100038005004501802d00155000d40101500c078112042c0d03990700360840c0d0046008840980f4801e40100550600b0009698012402501000141040740000c0c0240c00010085802070071201c6081940510910100003846000380c4140302c03140e00d992014101880d03400b641984004000e05215442401340a4810340b150152502480c088840c0c440003500d0344980001c0c0c6491280c098210009440c02a20006000d01c6641c00182d95003049145424902210001340074602801e10307000528501004984c156985818003078102c05d515041916031600500b9030b456050320114000050310b07004203020384121a01440426556501e0042008841826070031540104070071181c0110750400f83da401e480062004116112070303440b00102c81c00002e09130000800305490701c00c41c0211895401070070f90046401c590841c0c0b00c0c18000450b603581c28a20f25424180102d00707020030203590148042030080c00018080c8802c128040c24082c0c003940301c0040c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 346303021 1250 346301771 346301783
    0x309022101140708010918020907090911070b0c180603040804080d141204030302160c2903040318050607110f0109080304060309060e0d0206091b0904030c0f0b07020307 74
    0x20981510070b2040c0103d20542064468a08076402d143e480002400d10403c11184907001100140c05aa21203076454810704181d039905011500300041070080c0c440030720841403018070a10002d4001005114440e0f84600020341003900c6521410524128581035549030390000c0002062109000075070001f0300071f44480a00311094201c0d141000c442d0290640c1c0f84005008050150b1547c006101d80440d820030300034600941403922904081048441076a0101c4a011100c80701301b02141c0d40201c000381c2c4040029842214840781c40c203545081c440204000c0801210f17230980b2080055405011000c0c207809030070360b601d4100500d80400d10b8080c0d20a0b00b4070401944000c00c8496100302ea412007a540e03404099800d0a1401601347c019214001d0308032082a00c5408000450408200d0120046980e074001c100781e080042c0031740d0500c9010010101c142041c0000e800041c1c498005007508981e15180141c9010694180304a804040e95401450760400000744441540e001010b0251507000751 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 346304271 1250 346303021 346303031
    0x2071a10030b0103020603070e1003020a08221202070e04030e030f0706020721021302090112110901080901140403090815041a0603102408010207030801090209010309022101 76
    0x5680c03180000440e110040c695240340300180014140031003c0c54201c003c50034100806549800080c6851900003282d200007540440c0d60444503500c002180e8101c60804601d60300400b508407c40303c13109801401034020000500c1c0c43c0c0c0701700d2003007100500030901020fa100c880c2c1810f03e8001c1c20680c5920920744280310b1003000315000c182c0030070f068048038699002006003900d050080d1212000c1500c004141841d068a5240940c8403042c0308401400c04141c0140d440c086100003425400a000040d66814545510400307913008001c2261001c0c1c0003402c10b0500d41d5944000c603805040d0401e4000880c0c0440c3d0140304c109508041400c0941301400c065800c0315040302c5a54080c010216005400070814600400029800c180e000ba000721000d42919901e0310942c10780420f81d00c1c490041c08460000d9065260303090f200210b01c90180543c14020b41c035000460b14028814041030040c0741c0d40660000d1981e660382c8c0613074424084250701038543c40d100c4c0062301c40315426040c4184400150350034a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 346305521 1250 346304271 346304281
    0x30c0f05010215041104090c0305060a05010b07080a1224030201030c0c080405040b030c0a060906020c01030603080d050c0904090605041217010314030d0203010801050414011a040b1302071a 83
    0x3080340c01c0c20400c05083c0712156034490300c5002d10303400c5510460741c1040d99081880b000c140f044d00000080c6006800400345070414042500031140140c0c0030300d040031400c1c0000000a09004220b075010361051920340508030280f00c01000038000c064040e0104011401e40301c0301c000440025108483c000d8800f08900d070030b03590f0305640240c12a40d0080100304104000e0002d4a03056001d2001004080c04903010369801c00003042c051b020300e802090100b2004c00c0e0401074140c1c1000304c605144000c1ca03084c40030502e183c3d61900c060041c4000864101e45810005088050540c00c0d1003070201d001304280804005802c00c1c1000b0311080e9400e8444100c074021240505004a540c0400043d13890b401d91070982c80d40c2c9a22110810040e18080c2030b000130020200111602d00186028200c0480002441e00b0245000318000c021f2500c000b0780740e414a64203419084038110b056009a070140c41c007280d011110301c00903540290049a03003109520100b000814018050601c0e0f48092900c03070030742019100e03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 346306771 1250 346305521 346305523
    0xf060509010506040911120f01030b0105030a080703030506120313031703010302060a0f0c08210601020d0f14070b070201150e040c03110105131401091a0915040f030c0f050102 77
    0xc01d00032a50400d00030441004407103500e501044d400d00b003800c151800c007048030001d491020001c4d07a0a001d0980030720014418002c014010360300402c411402030000310b909680703800a0780101d00f00070b01419a540000b81c1e140d200d84548090b04140d5000392982c031401e200c03541c08821010702098460608549003c52070b43c0d4003404490507241c000f0012414044104012906160000c084c0e40401010b100e425000803040005071010401c9041c44500031100c0340d15607075000300c0c01012541154042c110746d01103160400340003007841290780341c03054110321a1181c5003128468004018a411001010450600ea040d8480e4000441e1900c0c07500c000ea81d500b61940003200300707480103062a8800541040052000c0c02e1840420b035043c10070900381402010f14094416169004230200c40440c10306420790341e40088000003910341044c20408040c616012a55103003d0b00c429140150f070140c10343c0c40c03060020401e0702d000308181003450f0401e54987c41c10102c41402c1d4810380c6400a8111004200d80d80 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 346308021 1250 346306771 346306789
    0x10204060f020a0c09020a02030d02030408030402130b0d1103120f04092009014d0a0c0b2a0c18060315150d03050c0606010801051c0c0b0d0f0605 64
    0xd0003104c21342585003040c03074070740095004070f00701000e511003000072180d980300030300165115500030b0003029100e140c5801442200d8030f80b0143c403200d40389400c3c041056035613002910b1318007903001183c0200c8860f040010078030300f0b58021002400303000c01003582c1e02c0340c5030040000d000380e40c120242071042907005989880c1d4501034a070890318a010a2140c2181755210f6608400d01421421908a000c280c2d000813008441c0d04001031107030350b4580c0b80f41030703001856518144040c10582006086254440c0c032029502c1442d07028186400d032000821316681600071401c01d00440030000000c0c4800303490450540d0301d003180030065014440c8030f0310001300b80b10b03561140e520030400540506020085031a08840064004040903440c88600054134142d8030f9030310400a03603d04c00d0300c0e00c66a13011904259031a080d401070145041004a60040c41140c4451440d449062004840110800c1007481e000030100016000302400c28008500c0c0d0b07400c88425046854070126203a800c00150b51a48240021a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 346309271 1250 346308021 346308023
    0x1106090303040b030a060f030b0402040b0604120807020f0a1710050c03070c0501060b180a050603040317040f0614040219230a090204060309021207030b3402010204060f020a 76
    0x1d003042c001003081c101d800d80103545c001d1900c84005000da483d85000c900c0382900350810386042c10306004110442c1800d20400d12411012182c480c03c0c180f070300220000703503c80c1003c01001c590000c070380c0e04215111708140000e4081c00400070f001140d1101d02c1840303221080c5404a95500c2400300b02070000e0810b00c07405009400c41403c2d00c0c40c41e070b50701506130354400025004035101d40da0f4180010b2003082c500c010701005480382c0081c1c180404010708016101c0352941010307119a808105010000e81c214111b02c4d1440c1418103a90b540e9500c1b418074003040c9100705400361140b41441038513140400f180564502c10740c0700716081009440404a00700c142911801040b03e48103172a0010607282c01c00100000c0c04810040c10315451507207400d4404141d802991100707010a4a4260800840c685004a00300c04107003000105002440c40e140d0300c0807680041d12034000f05240d081d1105591607802114608229a00c41d01850300c003505800034000d50003481880002803240c1c18490b151032010aa075000340d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 346310521 1250 346309271 346309273
    0x30506060304020f0d020d05030a0f090506031609030c09020304061a0a1e18021801020a1106070c05040e0c090601020d050d0e0c130903020c04140a0902030f010f05010311060903 78
    0x641d030b00c0d400c0c005140b501006407607110502508040c0107a503124a110355083c4104007854803032186e247d003e000d91580500380400c2c000c6005061007161585c81c1501d5000c50401400260700b45110b000b030714441e0307160b00040d01118003440d010842080c5a0000c6004d035100704410000c0d02d140c0c15003070280c010741a00599005941030780422514960085202191041402c0380801966a5040c201f851140300c5507212040d0b004501500c9250304401c1198032a402070001d03100d260302c03a945c0d14007900c03600f120b41071080c000424400c050004c85050f107006004058420040341510181c403985e2803003001800307480380e95482d0000d0754951010505604601c2c003910b85505020b01d03020400f0140c50700c0800c1c1040c5110b040c024603101d0b0f031920f00c0c1c1c0d21201100e51001900c0085414000c2c288250b608483e4016410704240e0f40341d040407241a0765000e6842400005c1c020341c2c520006c0e0070014a10702e520306030b40c240000803403680c078181d104a040f00d210b00c1d0700860310a00d1509200240c05441140d6601d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 346311771 1250 346310521 346310527
    0x910050f0a0e030f0a062a05040b0d140708040c0b0a020c04021b0706050c010f0c0801120309180b090108060402060708030718030f051921050d09111003050606 70
    0x300e601860b82502c80c0742c0014261002e6100c0402e8035840c2c904d001c80150b820984466100218080c0002214025545070005034886400604003402e248554441e09002850004001d407030400d643d400050394029a0400300d03064103000100030302d41c0300e00b9039060713035800048400020b980e6203210440f555600941c020707102c8042c0c81d4081000075005071001c0c2032000340440304607001c04002e0060704c029188645507103482d042c44000307036421100208606400c0313a140c501d10307400e5940c002030380d00d044034080041100846114641180e130081940c0c000346000c06c62400800703504200b0341203480c4610003540c3c00149681d075644100d03915030701a0380c00394000f0fa04210318030200da00700008591019803401e0480d0382c0241c01c0080e0032800ba0036881030716106800d0040904000703060001c9106035400c0d00705001211225240c0841000d03c800d85900401c0b050760060b021140240309407009000800020807070ba264900749890050045021300d4440d00d4100c1030750030781901a104a9020b070701c000d494941 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 346313021 1250 346311771 346311787
    0x50d030306080d2a02040e100c1715100201021210060f08010e01060e12060108031308390307030609050d051c0b01091205011b11150a02041a0910050f 66
    0x40200f45407201170307030443d403a070440b401481e80c00c002c604059500c035000060461a04c3c00c0c010003020101011344410101070080c8440030841e8000d110404404651201e9141c21070041680240b080881c602d884000000802107451084201001100c06c03d031506102c11850040865102e4001d010f0f802032005041c0050006034801d0900c80c810700070146c04280000034030a5114a030146c00da00c140b845900000e901c0c048036081511250061460a00170040003080e21b890104030340382c00c6405020808190010344440d070684240c20030a02029041d03580050301ca04205d006000d8420082da868441c00c052501c1c0c0c0761140003120021010500c01500c4003480c604414050880c0300070740c0d4108401c00001081445061126000b803921403800000c061884a103200d00406101e4a10340503c003480000000007076000c034a2a00b040c40140b02c200e095662040000000e00480d080380316900b0b1440d4518640e4160781e8028003030150110760100c2c1c00c116001007151a41b060380c009643d0300c0c100307005480c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 346314271 1250 346313021 346313087
    0x10504170f030a0c0309020d0807060b06120f0403090f030f0c080718020a0e090f04050d0e06070204051b07030c0b0c0f04050d03020a0605090a0c080105092104050d030306080d 77
    0x1213020011031034007242800e0703103030001600820a48000d491a908c00150390040241610450041c40d40036a038950230b008105001d0300c501d84006010031111b080300710010301050f110303400744809440e254403c108038585a00704008248040042101c201e400001c02290040000500e80c0c2220310082d107504903443d88a8080020390054403241003842145400c2c0c0c68282e45102005204d0f01103140308032203a107058242203140c0940240000240031034504c1408243e10390300111510035030160b40100707081d00c070034004001e80c1c28602d20240131041d0100700701d410942d1001c101010136010740d1518440e601c1c0c0c20300810607031061b0104074401d09420442088641001140030b5a4070b4000d005803080c1e40c03519254441580c0e801c83e0b6043c280d402c003140e84401c01400b00c01540161130400000c10003440c0450000380d456a802d212015682440c601c955003202c916000c50700034101c06420f1189003c0c5518000c0d002d4101401200068040c82340340d41941c91088800300842d80341c0c1100300711200064a075031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 346315521 1250 346314271 346314281
    0xd050a0305130e0c1c0e03040504020f0705010e010507020f01050121080d0606030b03070b04050d06050c071205090411070f120212160201030501051c0b0c070b0702010504170f030a 79
    0x82c0340c03114030038000044444002103030b20301c68400042031503a20700141c8103141201c000c101c03500604c07600d00540c00762807010000507202502c106440c0103030303180609690b1510300d004e5010001e20710f60804140b0a00c0040c19040700d07000701d840c0d40071640e6503a00f0a801d11300340c1d0001d016441103c3d000300d0a80f410180a2946840d0b114060000035107025a8044030b10117a4040e5004800400d0701c1c0d03d07803015182410414003000302140380e00903092030b04100c00105a00090314010f885d1030340f2000440d240401c0034080302c401c968488030711005441c02180140080d0007000a1070b00c01d51508082c82401d000079000c854840c4d0780702c2c02c180c08640b410350b02d21007645030000c8203008521807104041c1a100c4101c2c010071181c088912440301170780c81807000405032501604145d000740303031064002d201d101d54400000e4446a201601c507070503940e145c501e803407a80990040501042064010b12058607010341c099405140a4283d480011880c1a2001514419003000681c060300030800502014003990107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 346316771 1250 346315521 346315537
    0x70f03050909090d080106050c0304030f050102040f0303170604020403020f100207080a0609060b010905010c080705010902360709050405130503220807120209060f0907050901020c0d050a0305 84
    0x1400d00303a201000c81c100d841c040316040d240c0d0744550654040945c000611034014011071410074600081030f1249a100d025510005041c0c968400005007082403c0d01648d02811290300514a071b550740307060062460381d4140a10004040300c41c00f18605c1e08190007220142e0b81c000e00010300d82a4144103014a00c3c9000b5445000c6015108001c01e07442800d011000302c15000f22000b00e8500b1180c205a0122001504524107008400c08200030598010080c0700d11541c102410366118000c5082c024054001100004d502000300601014141d040300c00d10f5003c4102440b50705c01d03c40201544000318402a580308004c190a103204100500d01038020651042030002150058240303075881c1499600144925041c0300c0840860400b10030340000c002c0010003a00000300145481d12008802490600b42e01074001e5251800045240e04d400172845041c40c40030b0084c1e0300518101070001c00c0c1d50451450503006010b0519001c00d01e16244a500c40c59607040409440010403580e41a05d02d64480c0c0e034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 346318021 1250 346316771 346316777
    0x9050603130c06050a02010612022206091d06090109030e0402130909050a14030901051902160602061501030501030203030405121221090a0c050402160204051006081605070f03 77
    0x816a00042c850014020050100d5160141c1380d592030300001c0c1c01d581381074102c40c00e2100800b031007001580c2c4e100036941003084059224552160903110610140c8610740100c041c15080c944406600b0404402260000c9007000641e141d50311346549039030981c2c4801c0780150019051107203451140c0381c160300600c0351406c04405108000d07030302c041500549426141c160381d19000b544c0d04105101080d00d140b503100b00d101000d5407403c100f100001e4894081c5100301010030107500c1c80700c150540200081d0702c1012a40350000740c801d584020095076400704031000c020704050a8030020f00c5500a0003403d0689a00802841c02c3c00c3c109014000c442c480004d03212900d1060144c0401c10b5945000180301c0070100405041d0b141980030340d910000c07040500501c4042c0e10401101000c140081c00020507601d045402607618000d940c3c03a900b545660700d201030341c020314244c00c1c03240088014254404880e59a110140e90303550f2145440c00e8002d001a060000c5201080190002a074030aa006c10b02032180c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 346319271 1250 346318021 346318051
    0x171b0a03050718110316030203040c0e18010605030a0c14010918020703080f040201020d23040e0f01051503010e040f081b151302010e0406030602030c030703060605090109050603 78
    0x28440d039140003034039444400711808041440d62041a01d005260213040c902521500d1401d0070002407115a240700003000401d68040042402c0000c000324903002800420b81c040d1751401d060340b4041604513140100019986000303800121401c000c91078010217504001c0c1c0e040c86a251461800c1c150500551071410801803550200c1d02090181500e001c54003600001a1074480700c0c54003610900c00585200b044224200800c00148c0e8000303a8104661040d1803c1c1c60b103c1d50071610001c9040e486900c0c2c80c02c0c54030119011907000300c200e21651044490b07503404415a640c2c0c40500800d5000380900b00b6140b40108014810070740741450098000d4440c4000100200c0c481c0c80d101000c1d04480e4800c0000202c87c803c0032543d8408020340a00610452070017041401c145a00741d0a0402c0303ca002411b110b0304524144e640e9440380e0040000303580140c400d65881c600044e6100150780121156004a0f1074540f0201d40d00c0d1140054034002c01c03040e118051081d040000700900c035000241506400800b107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 346320521 1250 346319271 346319273
    0x10503010509071e120515061909020a0e0909240402010c081602040606080708060a180b040f090c050a08030322021c26031e04050a060606020601090501171b0a03 71
    0x1180300e172a202e030700400140144600e5100300c1085180c010b0b000b24801c100c090444607081d0719061020040303456440c40140c2e200f03452201582c07030103500313402583d120804208100b020702006c100d000600341c07030104a0840a5100c038510a84510076100030b0b000032100001d1400044003180148185443c55900d140710503101c0d4006403d5810310b400c035500180c904024482c1036504210b00c1d03a0040d004807040c00005051985c8004031400f145424107001d134070303090340248030b8075154040041c90400307003c184000055810034030f100e08032510491f030040c20301ca00009180c01004c01681e005207600309101c0b15100c01d0a80800c00ca520681050768000004414400759482c501c2001c4031443c410064071012007002007102080341c2008038200c25a08007041007003145041d0748040100282d510040101c551290b05209250004401000340b003c6c3c98002c000c1140ca400149850498009520521590384c84005100081104001800c007540c000704074035119501c02c546505a02e200a0281c240a85c0c0c1d03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 346321771 1250 346320521 346320539
    0x7020603040311030705011d0a0222061a070203070501050f12180109030801050f06040617040305041a03190b1f1215150e0105030406110712030e0105010503010509071e 74
    0x20407402210035a40d180340e6000442d941e020303410000560900505054141500820059008940d5000c07006d5072f464000340c030062290f4002005414000701c140c840140d100c0c0403920540c44a9402c5e80300b8402c030040018207600c10720484980d40080d0195034101854001c1030780d10510080c00c40191300c6032070031101c1907040d0248608000180603660f40c0e82194540000d0011152101c0609070003500f040100380200f0f604101485400d0b00500c090805603134940c00e0882d10f034019034001002030744404000c03124107000f80000d507000e2840210800b81c80c1c003444200074201d400c0f8001464010304903810030080c0c1d00451381030358245080303400c0c08048400410340000840d0550300014a030000599024040c041c20340f44441c242200c2818180e0b0041e600e0300c00600280002000200000c1c1c07101c0489a0340480402034400301944403003110b64032017064030081d018041090100c0000d6190000006007840c05002e203074001c8121002502da81810682031500300380c0c0c80c404a08601d00404000035034980 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 346323021 1250 346321771 346321777
    0xd0c11030a170703080106020d1706060c01060b120606090d11030c040f0c0908030f1c090506010905040b1312030908070c0f0821040501050c01090c0e090106060201050c0702060304031103 82
    0x645000d060365030300f1291a02600da070106800102c11544001d0b020700801e0b800c08406201c003403c00c03170780502c01d40c7c80b10001030035440348140d5681d69509041000641c2c00d101805850180700d0140c119030340740e03140d10a1207141e001d00640c0c560b100004242d2880418181d9096400c0303520301800382c0d4a04650540468150b0f948150110819030340e402c6590701e190b50141d20713a4060084203000e5460032041034881d2106000d080d84000f4175001108500e21038004030351140d800950300400761043da607507822509008000807182a0740d4010704000040c40c40c043e131030208014941c4030031055104c0001800440007485801c2c42240d8003242045400c02041800101d90001d014108000c0c0300e007414040c1082c1001c454400444540501002d400d104003400030643d0140d600c2841e1103900c42d851a0305d02805009104400351078106140c0e000314051102c6843c40784030b110000c000340415a0358042c12402c0340e41c126050b45410030213101110040c94207000139500603010b8940301290f84070080350181564 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 346324271 1250 346323021 346323053
    0x10b090f19050907090e0a050109030207060914130b06070807060533090601030618091e050c0d02060f0406110606010c0b0a0c051b0102040f080d0c11030a 68
    0x810000400603900c003206185040740c80019000c0c042c0d8100300d90001d42e50318140c014030003410749460b020340d24513508104248140750000001c0c82036020a05010791650464040c0c18009400720728041011400404503c002281c00b03000700440d0303081c52a803071000301007009946038451000c02560780807a140785e01528045000e0724000a02d403c02a1201c0030480b42038008444450407510610501d107078100503074410a5080c3c1da130060550b12140100c0040030780d80c21a2880c00041c482d0003040705040c0e807141065510403603088104219034142d0b00d10800030300c000203040d40d0185030000814281010b040a8440c4003501d0a1b0501c840c004105904d604945c00c0900050b115222004031407004020f02600580c080c01c000d501048140c50301800383d580100103211490310748184d21102da1180d0200c41191010049608405520301d200303a005c2e40c803c0c0304a14000412440126581c94041005000b9115503100d0446980040e80c680c0090f0182082055050060219280108201c0726002d0111 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 346325521 1250 346324271 346324291
    0x32e0c030e061b0a0f0c0602161104020f1c020f030903180a0e010b072604032001020604020d050309090c03040605070f02030a051612031d0c010903020f03010b09 71
    0x34425608020b01d00100100182000a0700070b609902c0420b040c001ca40c1c119159103040c2c414034142e00e405540c06140f100c00100b555100040c81101903031b141c00d001c00751038071800003142c01030354140c104416800740a81c80d44440c135041100c86000c80c40c51080781c02100700804050300f00301054079000400d4004440303049040d0070020b140c01c0d0b1514120103102090b9402c4400c03112181c149804030300408014015285d00c0000054110240111034444940402604505042d0040c0010a81455400c588000c9420740264210700b450f004509041032140c5106a0040103550344980800c01c103c0719681c03098400740010446020b294803400e20761440790388080704540d81ea007020710f000811554000c0899040004442c0f0800410b42d01000f1a091140c1614240703071500300707241540c40b40b0300c0385600040004e241d4101c2140e4031905a04009031403811a07410b01e0311040440c0b405500d0303d140d91042c60005102e28418001450101c2c44910241c3c4003400004104250700d010460f104001e44000c211 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 346326771 1250 346325521 346325531
    0x220b04060b0127030f020f040e03181206060d0f0b070201020304140c09010e060609130c080105010c03092c09010e060718030b1b070809030c01090302032e0c03 70
    0x40d580010300351101c1c08081a03883e034440445004905008014000100101c0e503560142c4250341d135042c80e140c04018010801c200d075140400c0159620b0b403190890880140d00903060804614248800c000e03004002c5015228664a6104000f128001000111094207443c008040400d922821044c07103a80c06800041c0d03a801c09041081d001082c2040901c0315921807040700d03806840d00458281180d0310420f80a03196100d1400058450040d1101c05802c0360003140780d0010110315400507000d41c0340f1a101c2e060281d8903900111132200c2c902d10040d01240020340c040041c18619609080c0f0180103c003000c04d428000600d21380e03c050140c424000c0c80c1c4d19071240e062100c00510515400074841e007030690104030104201c1c0c14590301880058032a81d0364a0025901c546401c0c014036085260b401c0607923a6008626000f803851304001910b500030321403403030b41c00e1195014403224015650000d00804611405204144015010750001c001e110700185030700c2d42d0640c06c1d026000c01d4070700390340380450303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 346328021 1250 346326771 346326791
    0x30216060c1b060518060c01150f0b040e010605130302100c0b0703060f0b0d02040b0307080910090803040803070c05070f090b030c0d150204180204061106040506220b0406 75
    0x1c0d914103a03404800d0000b03000100240e54009080b20800ca068075204040b10203860000b03410b03401500d001390519402d10340300c001d1100340c017415001038a8840031101c1001d52921b0b400da07245d0040740111003810603040010b00c0110701490117031560040750300c120b4040686940c08034040f031603000101e4012a4022128074100800c05890035408405490f08000785450301c6541000e0b915030f442a05044400001e0181c2015040c1d0100e0b4060001d202d032495890924010080c0f0755441100e655419004001d0b2240741c0c070a080c00703500c5586402142c400d003552501c0d1110f04459001800c48001d105010f911000000c600b0312081c0000d02c10104607600741490b0541100503281d8007181580729401c001c90003886540c455a58840d45074010721140049003134100c0550091159410010102030102e81c0d01404000c2c41e0002c00507514282d940034071406a59540e00c2da614130540d0300900a821004c001043c00e03071104004928880d030058004c5820303201e61180405444243e0b002c1c5d91144e1280c0d102d074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 346329271 1250 346328021 346328033
    0x6060914040c08160207030b011523030609090c040608061f030f170409090c0914040b06191208030405060105090417090d0816111219030216060c 64
    0x203100c128064074288112180840b005100c0200180003002a507000181c0480c424400c004010103140d2000002004d5611210240082551003900f4000a0120000300c41c154440c0310803601c036914000340c03071030444d1035450401c02000c0c4002c20664484c46030f80d01c2c85515507030f140241c000a0072000040d00140c1804084850742d4000500440d288810300c0f6402c0000408003049510040d422400803900340c0c211031000000381c400c40d4450782085041071540003d008545001c83c0441d10500010004281ca400303000b12601011500500000d940000048040c00c19401964810f440340304103d03000b81d10342c10905641c0080b0f40301610301c0000441040b0810030704016560240800301c8071346101e07240c56929801c21a1000d0201035403000003207040c82c080e84031502c0c5440640c0c0e0041c900340e25403698680c0b0400004c41100306680c9002c04c1d2543c1021030a0000c001c400c011815806080d054000030354100b03c401100c0e0040f81181302e40300520360401452460340b030280c400340c2e49480d800e0006040032 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 346330521 1250 346329271 346329299
    0x4020304260a0212070614010e07030614011209020f030a0804050f010c0818010e0a06050c120a0504030305130504110304120f0503040320121c06060f0c06020d060609 73
    0x1c101d0080c030030010381c03100c5038002a54910711a1115001da0365107205140c01c0005d0442030681c2c4c00710b8904c61f40041040d542c0032120601c00e010f0707541c00f0031080d5070b04e40d0380b540c0d00074280200a0204410741c80101d02d6a02a40001c0782d005c3c009400301e20f03c501c01c64086403412860050a8800c6440468140003d161000030164100000d280a003c90285500c2e2507903584030302843e225464202181942c8940d0080703c80d020a040004d10604a035039540101400d9a440350f000310001d80280c0c500146004070343c2082d0762011507a5a00e4605090031a40d06484a41c40708803184d600c00140307440092150354030702840700b442104421068480c14517203400e60315000141d800e242440000380b1616030241d0f214003526406601403070800c0d40302c0c2c085500105299416484503425000f8400c801c15a500e04000a05001001c2d0240384200c400704501c0808507090b0707001d6a800030315001c500c1410745220b105203000e0603024407001440d024200c0302c44412a08294090b0000c10305132502082148110042 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 346331771 1250 346330521 346330583
    0x2109040608070602061f09020d09060f0c021906020c03030c04080f010207020609090c0c010f060501020d1e080c19120b0d0c0303081b03011205070f0f090f020904020304 74
    0x2d01c0010b08040d00070b9110b40000305000c28442d8000d2040100c40005101400204aa034074119900c1500c040c000e40500740b6602c0c20f4171541c1c1851603c00b41b140c0d0902c10018090a1396028003140e4140b8010140c144004007415150141c080c0aa25403e030401e000560282414916159880349072405860a03e080292150b94030303481400b0b524050703200c240803112661021540741d0465038904001000c00d000f10752000a030343d8601401d803145100d440e031180741a11026001c4488292015000729050500c0da840d0300014170091a600074050300414002c0d4100078aa00c103981001c00b120800000250503481d070500107194030040050300001842101080c1005540c02000f44100b0b40303c0789a04c140318803005040005280010f01c404818800081c1036a000e412036035500d5a407a0401c8000304107101c0c041da214001c400000900780951403840c003c88907001000c007203031464a40301030010104107080a48403a020040c44c40aa030306e504c000c42c800d80c49a0010350b04024000896440c040481c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 346333021 1250 346331771 346331773
    0x30209070c1406042f0609010c06020a030501050f0d080f0721030f060b18011d04020c06040501050a02090a1505040312200f0718060506030403090305011109010f0c03022109040608 79
    0x130b001481c0901c60941e044080004c6d12210703558071141c070048a076481c0a4402401a83c4080350310b064082d850b0300251304072001120100246a404000c01600c404076a038000c210750030400281c00800464005401458001d00503c0c01e1030114285c02ca56803520030000d0310000b51b48100d4158842400e100305da014044000c07009042c0745101d28944001a4074010300d80c140041060700b421f00302505060f050815001a000355180c9906250056442c801500c0454231f40d420b00c00087c19000d41d5100f601c070b50740380c0100111407591030191124041d03c4a0030800040000400010010801400a001008000c0c0d5540c850034900d1740c1c201038540382a40300d12400ca030094411a0300341d90f400940c0c00296001950748504844500500c040141810f0f40034641041001c0104010305d030b0090051300441c2c3c000c900034003424450341030b542103e11400d04514041f4600000d8080d01521800c24102001c0c803d0048a0803042d007203541d04017818080300d00c4117425400140c05815070503d801218018a1018 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 346334271 1250 346333021 346333073
    0x2010504030c02040515030304090204030c0510210e1902040b030601050919020903100903020d1b030c1103070801061a0c1b18070e151201030209070c140604 69
    0x1d50700420b82c58a40340082d01c00d54a0754007140341445c2840f0216a004002000c07203036202c1e980d94411019400511040c0c1d09800714030030004250410b8503420012003015a9040d00c00c05006c0505080414640d2450f5011640d440d0400728504080200a41401c0c1140a44d110006184100025162000c0205011b60441030040282d07071501c640340c40e08083d414603060103258100c840c5078000d00800c003116034117106580c0380d40c000401d81e600c00c1c0c1c4124041e41c2501c5000082240c29184041010b10b000f800d070382110240030100e84200d511580c1c9a102d0f20f000c2c00e40c3d80b035501c000f03031070f12009400c8091940d544010401481421003001590040d800310058101400e4441d248d0300ca1020600701d01d56080c040803003540c0c80e44e1f030241d550509a40345d148a1400c2c10441402403035640d0341e02c08030340140000800401c1e261108030654020950700c442c041426801e650030b104403008064581c00034072030340d01c46080009103803894804002031260300814080c81c2c80d0400d403030002509110b0180702007030703c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 346335521 1250 346334271 346334273
    0x9050a0207110f0319080a08070207210c03080d0507020706110613051c03020c07050604080a0f08040506040303020a06110c06010b07051f0b01030b0f0307230405040312060602010504 80
    0x501c2418a0b00d00c0c1124200421400000820708006003d10781d80300390700542160404100c91580030744084459547e4030f81c1c0036502c054060743c0e101e03098010000e07d400340701503140c0d4184650100000c2144201d5102c00110350703039960110310fa000041405039140e11402000b00455040050b48018002c0f45001c01040c0c011501031600c5140142071403003104500242d52050100412250003003080f07405140d050b0710700d032100060003034000000c3c007510350040600000300c903e0050291070540d03104c0000750461640c80e40c0c40d02488000c2d03000480c0c003140280000212556541d010b00300450180d0003800d90a51240b03040402c60780014070264018600b8080880016000100391741501c440a803d00d96480c22030808900c1d11a05080e0050b40545c00c4840407081c0d140c0da00140c0140000fa02d0500001c0741c0f010403c182040d407841ca060b00340d4416682089a10717000c0c4007404401e0722940410803603102d1036020409840d070442e015004100c40c0c208107400c8810f135104440060140c1d1008200505207 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 346336771 1250 346335521 346335533
    0x6091b0e0f09060301091b080d020604082d0c010f0b1c080c01020706050411030d17060f120304060c0c0b07020a050918070e0a0614060306062508030109050a0207 71
    0x6501c16004511000000303100c2d41342580030a44081d040303020b404e5155200b20a1641c0ca003003d004548840c00b460080040715400024a00e028581c402c1503a8100040035140105800c2d03060818040c00724046940c10511217800c004044003024030300041007521800440c0c03000c1d5800d00b41f85502400f203407610516000f1f00800c0d0480d4450703100705140d6940e07031400304050182c010310401501d00e03450728041c4020800c021003445034504083d000e450103000d055a0540703025820320029000b83c01d02c0da00149032894400c0000480140041007924100d00c880d00325455600f1540000c0c02083c018200e1806109070025520014081ea0000d030346000181c1c0d02186d6010100d1190702e006081c1078022a0100e02c1c0c45046281e05010304044800c225500c500082e5801000d0f40c4154603645000c2011030504100002d03415104005404545541c03102020b0120560000c2801580e0b03c6500407440e010312031842c05e807100d490090403c0c9440317504154460048640141000300c000e0710410190002480c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 346338021 1250 346336771 346336789
    0x90501080705030c060d11070606331d010512100e0c1c09080d05040c0e060d02010c0b070c050d0c0204060608070c0f140d17060906090a0504060f06091b0e 68
    0xb802000100304500b1047c1d45c85514050303940000d08030350600b0001309140e007485080e800b900c0303c21030046800180310808c400d91b804c866070401002944004914001046104250300f5800c010715000d850319541c85600e1201c004151203031115406841020001003042c480c1e010b13040701c0302624283c03804112100d044075000c1446141000141c0701d6441c0c0c0c0502c04040251800d40fa0181c030280b001e8900f525088000080502507011005104000300f8094140414503050055061f12400140e44090b11040b4656100030030300410000c1c0b075094180090805d20441b40c42c40001e880300e0420940742d1041105031151a0080d4003048440e504115110754001c0e068901c140d0001e10210701200d00e820442542c07040c000382e0100034420028100c01c104c1e80966001154600c0802b000c0c1c1c507485100070401d50b41410b07941c0681c003403800000f168030341300e956120540161064000240d0002c840c9044010303160642d0110300920f41e01c840c8800354200a00044250990625018140c1001000040d8290b5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 346339271 1250 346338021 346338037
    0x62c0c150306060d3216050c0a0609021923090403091403210703030501050a030209010302100e190501020f010522031101180c0f0b0f07030c0c090501080705030c06 72
    0x540f01d4941150075486881120a0004522405c481020040420600b00c4409a502d00d0007201c010000c01d8607180302c0e80c11f440075910040091b0180e0032541d10346401400b003104003680d0080305003007108248650341240400030840c12a04a80c10140d5840e807001c503445d0340074090f0040000b134041000285c3d20008a005440400c01440c000201c0c050119292454895034644000740d6500c040306041050b4014000c480c0c4260f4040c0282d07a02c41c014841c807001541f00083d04501e10100600042c070b025035041082040514014a0318074000000424400800c03000b20345084000c0d03400c0c410707543c1c140800ca2002058030000d03c000d003080c601002c000c09907507201028108210740c0300e804052050136940e00b02a1303402c000388610f0072248080d8124490240c2e048900d210015030001c0c0c5660320045400c100d0303107174a407010b00382112214150000d5124590450400161034514070000b8945100240980882c000005031907040c03101c410300d400781d1508464402e40c0041e130000c20036556030301240c90136 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 346340521 1250 346339271 346339297
    0x708040309050d2604050406080a0807030503060111010f05060f0316030b090a060203192909060604050409060507021b03060c130b03070203070204060e0103020607062c0c15030606 79
    0x2c1e0400d00302500300050100000f1504106265403010400b04200608146c4808680c104006551109003070340d0b030410b05400810088050203d8408640290061580440e041c1401404190655103950850f88406000c03404541d548061040c142058884e1986802c000e4000302015944041c06642410b601e1000804c0400c4501c00120304460900401680950021045d5101d0601d10111400c240540c074140c0c0b20b19240040880399001610080c074943c8070b0496420591018038070900544400c020b003295000b0700c0421000078213884034411001814000e0f00d0000c1d10f07050804000b030401e030721190118800c110043c40c0048070366010440c40e030805000b030319266642c2500c260f4070010b80841d030701c60040b940d00441000001074010001740200b17882100c1c2009a5502c420f013058020340c080c040a500701c90103204000010b611a1f005c2c42c060815101c1c2003084084503200e00d00c4402e1800303420f0b9842d409c10150145503092240400084c1d450030102e243c150324001c1d01190b824010084000300b4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 346341771 1250 346340521 346340539
    0x9020405061c022514121b070e04230d050d360314040f2c0a021b0321070903120f020d0306030809010c02011809060e070804030905 58
    0x140b9a001d50440d0212040310480e01c01c3c0c00a218000300070502c000c5400c2e140182c2086100c0e03c1c0710408580d0401e0303031200030103542c10701c0741038504e0804a100105410031144625000407030300001c0c0040580c80361340309480030180f103d959804414408103904140fa00e0f84e2103008503525076900141500c124020307494001907029408420f84884c0c0c26880c1400310664031410000000b25400721442c840b4901a4030b400b101108030407000096403207a4801d5590b145101801401020041c0d03503e251044414281045a001e0701800f80501520030b81e2a04801c42c2d000485030b80c0c0c1e000403104480040c000310041c505040309000301c07a01064074100408820340072000014a02405216180c014580000d500406200c206c8401742c00c6001224101c00584a54540e81e074542d803280c001c40d0705995200b101d00341800c200d0001559031007142d11040703051204045507180e0b5281202d00c082c0c018240e1707020110b942d45c509596500ca00001820807020040301d0b204000210750006200c0c421504180da929031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 346343021 1250 346341771 346341817
    0x40f022d18190603020406150f08041a04030c06050f0117010b0303072310090c05040921030f1b030522020d0c0803071202010b0f2107080d020d03060902040506 70
    0x40c1204d030002507115150140124043ea81c0c80d40380c4a880c00c483d01c41c07015007104180300351108481141d0042c880401c2044181040c13000e4980c09400502c03e0030681d2614225a43c4c0d40141c0c0c1d0210390055a80c0c4428004104080c02c104142841ca80340390000c0221990b080d0100b44c50f40b10b1048040e101946940c54403401460310400070318140c0e141400d44090f861320b0959a006844c45c03040986030f58a400f800490107180c03922031583c5060b480310010998a1340010b503e40c0c0161188034000901d95160000141c460290141c104480c00403400b1081d44521420080c2c02c84e40041d20341850364070005040c4208005623a501506e82e60101d60f0300540452038940701c40340e0b00580d041888240804a54901040700c03180c03415214040079002407000c0030700d1000384140d61301e96001d5143c0c0b01c1c6032445083e90031552800790322400040c1000361103000c0d444596291030f081c4112566001640014480c800b2140d051280f203003d45201c480c15403400e860b14001540c0d6004103409542c030368103905d003070751 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 346344271 1250 346343021 346343071
    0x23010203071208070305060603011d0606160b0a060b0f0d0b0402040f061107090506030a02060d060305120304060506010c030f08061801080d12090317040f022d18 71
    0x40e504951240c0d07807030a03112071000024214541502e02e413022034204408541c40f850a0429a0305a0f450394485805800f100900790443d1030003d42620781040040113000481c000215165103075500640b407511540c1030422580d812174039a80e00034021204203100010004040d4011645d9880d80e04902185030880170300000c00900c69580301690300311003400001005500420001c1060168409442d006a51012006c00b0350700308540140d41a0403100b0765070010714051001c2d18242400240010702d030754407955160b15004009031408100d0b840801007004022081c000d05074800000e10309055031944d9540d020307004908000e50030b01071200d4400019003a445a1070741400c20038400c0780c03031002542e44c3c2c2c3e60749441c0c90480c0880300005030381e0380001010104502615288940c1540e41d40001403004041c40c0302000c018108a61921050103600050f0741c03405032003d15000150318400b84850f844103a0201000c90144260050008184002003211100211580a45d05900040811030b50178030b10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 346345521 1250 346344271 346344277
    0x6060310180f1e2301060c0614040f12020d3606030f0e030906040308130e0a02030a0b03060f0a020c030f070c0503060c070b04020f21061005010923010203 68
    0x810099440d255034840003030003a511404030030f11140c10400c0b844201c1e40c442c0856188190401c44020b400034010000c852150621b01242405410001a8a180200c2c06554040d007541c0c01d5403000c960181003c284444203003007581c0580c41e40010800c40b4292040a000700345e004107554817441d481c01e0040c00013500a0744100d947e113990611684001e4403280090300034200c4190b43d03140c0701c1c5808410512088004201c908551004240070f041510799503e480440d03000d000c0140f02d940f82403000150104841951038003500201d0304c050303140d142c840c002104a690041005101c1d5001006101ea210001f0101517000000070602503030368a012200c461071413090403c0c9001102d8006940000d01039410b110301c060712421029141140ca071000009001e0080d400003400e241e8024012a0061500e1914a445404080c1501c0030301c00f065483c404507480c0f00411420b00380c00c40400c0050f820166070945019000c2424200038090600e0401141d1404080d5544001e000d010b00c0244240e00030019 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 346346771 1250 346345521 346345541
    0x13030204050403080f100e1605090d0303020702030c0d12031505120f0601080619020a120204090b090601211104030209070f1202040b0d0504030e0301051501080606031018 75
    0x41440981480c0c640108a40011242070100b4070951011800381d00b00b0030001022160707140c0045c8260f4666234910310100c11894401d03402e0140800140c0c889448814a0642c1319002e40c80042e110302450050504004a50514a04c40c0c504078000e10002452806500358101180c50009a4540c040070181000e240c1900004c0e400744007540074201000b400a0240d5014800382c060707600d282d90b1140d4040c0d4540e0250307802040510320702c4046000800c282d0207010804001c2c81e0042d0015044205201240d01a400c4000110784824450040c0d0402e4003000e504040b0a28240d40801d4404002000018034400380c034058544410215026500c150705480c041c0d50010300c543c503a418040c0016002114903d10740004c5204402d840b400120315200303075000c6844500710145071a41011340c81d801444001c0c42282400f05c003041030b03c0305440034030035944101c104d07010018050010500140c0198402401c00c0e00c680c008108000c0e614000504000450304442e4210035038418007a0300c600900f41040f1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 346348021 1250 346346771 346346779
    0x1b060a030509160801020c0123040b09030409090f120e0130050a020c070f0303050307030c030f240906050d0f0203030c0f061e040b0114030102041802030612070e0408130302 76
    0x800b040c003213410b500800a0740d00081c002c20203040c07902c3c0c01c101c5540d10005d50000086640000402080b2050300803584013042c00d00380c82ca131648403140c58049034032190341500c84e4014170a8800030418141c41450610354241840c403d48800740c80001d121004d0301400b46031003290705041d5115522a00107a41d0000f0140c08180300c0361414070701c00c50080d000544040c1c414840c0600000702c05000c2e40e2658141c0fa01503641902e150740e500c405030040d1a4110003a001c0541e149100040143d00e482284104e289040c2492006140820a86040c1070b00e40c00824a0b18a00700040015650702d0901e040100ea00440e140300c19484da00000303055000d440e4845501d80610b00c00da4028400100e40756128010321060201c0003095109c9096440e00101d800804441c3c03160010300c40814040f81000c4a050000c0000d481c11303442e0354524a5090300689806035a6402105001c0c4074039141c02c481c1042101c2d40003c008503440d10301004e2811b00d02a001418104000030b21002031545195900701654001c3c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 346349271 1250 346348021 346348063
    0xc0105090d240c08060a060f1b060906050609040503030f1b031008010606020102040810052701050105030d0c02030a200a03031e0f1d18010b1206010503060a030201140705011d1b060a030509 83
    0x70605001602440c0c40c0cc1b41c0d194603041c0060682c0c80c108100500640d00f0900079800c50b9901d90518030002009000e4500020090b0202e11540080d10f00943c4206648c80703121554500c0e0603106400c0d03a51540001c425640107220070f00800380005401c14155a18107000b01b803d8036002c800280f4841e0760208110292528040702c1803001701500301c1070481e03100746c044400e072a0690000320f404494600d002585070b04207100d00c00204440078144c624800d40800c1041105950074005201c02c0083d134000c8001c2041016100403080030308001c3c03442070805040202e1111042da1000b06140649268029948102c3c0101d5011f80c0380c83c6030420460032072040d2200b40d56160b041d005100d401c016802c410052005000440c2075200d40d00352800784401520700080c0310f041d0390042d10031403144803503059000d01c00d00801000ca0400d014069805802600d288074007083e5030318940c100082600c0085036140d01408007150f588414044940c580068600010b20b6252450803604082440316010200020740d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 346350521 1250 346349271 346349273
    0x6091e031701140603040219090c020c090f010303080c0a090506070605160908121b0109030809060a020a05090103020f1e041707080c0105090d240c08060a060f1b 71
    0x304000d030715048020a01c82e80d85401d01001107034a5001141c1000040c00810018144105103901905650102c00c41143d03c482c14002101c5855510a00582c08100741c04100e080c5640903035001022804d0040c629811620054614980a0a480c0500c200050b0b80d2880c180b040d29044050903006103080e642d20210309200c409040265842c0c50350f006001c5020074114000e40c00784088071034603805401c1d17000c079583d40302d0b16036042182c1c5005c80001c600982c203200c40007803040d90b1081e8032a0329444110f042c0020040e250400040801d40818030400043e844240c1042c155920400246400750380d4222810342203016019003c86201c200461100c0e07018402000405042915044803a00c4005205107554540d00c42c03d610401c851600400e502d444c095104100504180d00050480e164028542c1e80e07900000305020444851040300c01c1542d4419100781c010414034440f07074502100281072130000a0b00416071407040e281070144200400518600824107804400360710643d00c04000e6007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 346351771 1250 346350521 346350527
    0x2031b1219110f010c08030a110c011b0810050d02180403120e01021201120609080a030506033a231b150414070b0705011416050706091e03 61
    0x100070000c54948510003041400340c104400d00d07a204040507500c289404a50751160580c65002401108202d0345130801c00301081c5124000b802c41d00310f000c00000791210101d80001b0003e440010038010403200f00b06112628040c03100100a6134401c071003501083c240c510002d900c090540e107102c4804041d0004120926402000d101092000f40b02c0c24003500c42c1000b5000e00303e01c0340520200305061081d00601140e840680401031a038440caa000400142d0317915a400c40d030300060209000a615201000301c1c9003002c0c0b1050b401203241d200b441c00e690b444106040c540c0380c0c1c81400764000e04004614200c4c2c984c0304008005400d51068060200c07007508100310569035004400780ba8048a0902c9800b50a1100007840707800e210071118400450b8444d50b4400c42115010809040c0c0d1348076218000c9806940c40c070007041914030801c00010000b020700403c10030004001c00c4a0040e0560302d00121495401404031154964000700000d4800040d14000c003107444032405120002122102c0c030320030150 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 346353021 1250 346351771 346351813
    0xa0e011b0503100803191809021204110d1a1b04140a08060f0c07030302040e07090302040b040e0c0f0103020c010507170a0515040902130f2702031b12 66
    0x20f1a105221070750b0301c460f01c080d503a11070183c90311200d0840784800c007122846042c404185a5139001c945d56610703035034903d00050342c003c1c040c8450900c211809120800040c158000203600c0300b03407013079a43c10040703484d0302d81c451a03000600c10303040e0203480c0020310481540c1c43c0001cbd40d210100e10702d0b03141d40d110b60b910280740e601e903800c45010300308000c40454a1100014002d104840002e0150040d950300d100040b0640c120410403800c1c10340078000402d104482181e140d00c22009030380c0d05504030349540100026602c000b48503d015910f81051b02c1c1103c80302196222403c2003d4880701610224600120300900c100031102c0314951a00c0103008120781d1054460441900d400354032525502d41c5c00f1020211081a2a8000202c60441103500c444c10507820880d9640c2c001001c00040c82490962881543c2624501c210059541c03100d03100010721794940b0304440945c0c4102000546041d50101350f42d00e513660001800300d0398a880940007552080040c014218a0b01c1c10744100c01000010040482 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 346354271 1250 346353021 346353031
    0xa050a0c03020c0607031d0f031207030b1005032211030d02070609120309080d0c051b01120e03090303070f031e051605010e1207060608070e0a0e011b0503 68
    0x80c181124429814032034001d807542e1504480152516441d0503400f6001401d0808200070900c81480c5585a01342007802281e00e200c1109014550b51000139869040c408801810f540500d490510080100c2d11003154820300c00d9141c1c20301560342e880f201c84104060552403255800a03003d0040201040f0b40502e0001d20a4401d030304468600c0c00c41801662103900c58094140050800401007041884050b901c890050003400c03c0c1c10007544503460301b4240703207010702007401042481c00c0041c2040381c204400c005640c180d54030504a181c018000030030104100781c142c00c84d10b80390b60401340c2c00303c000c0c01110012140141180ea880070f83c1e20381103106280042007034002c81c210150311071a140e03410381a12078005095507074902d0074400404418800d1001001911a59a10a8819031000d810010308001031603d03030713030251034540310b00e04102a104607070030645071a0001e04082004810144809420580c0c8c4900450400403115819005017001c000b903050522154140f10780301c81e0400001e50240c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 346355521 1250 346354271 346354291
    0x7050d031101060609080a110d0c030b04030e151206030123010e0a02031501110a050d09090f0b0a1a070602030f01080f0a12050904150b040f090903090603020f070b0a05 74
    0xc030360348004c20303224820144101011a0031465540c070004061907801504908001c01043e07009140f501c9456070501150000c0741c0c0c0d2041c440500082c10380041c21502d81c5c810450303d800c400310900404001030b000b400709a84108004130041122964290860004040c071003007080306c0c0f220320071840000c4084c02e02c10307101503490b15000b25003115054002c80b8819404803154503000d5500200440c0e10081c20395000c00d007806038041c200c0000f403048c068210320401c96070b982d0ba035050500742182c2c02c5403c941c00b014042c500c0c2901484454642c142c6c254200c5210400300d0303450030300d4010b00011522444400612940c070001c100403401c0403510360315042e9100d110458001c04c4503552899a40d0680281c06484440c0010035105824403034801003a0f00c01000c1c1000c220101400030b0407d41152542000d000e2a2002c2000e05c440d115000e0303050020038140c40144010041514040c0202507180a000105900082d844103004c1c100d204503000143d0060880c3c1270303440e02080107001044190744140c84 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 346356771 1250 346355521 346355531
    0x106090815060d0213050a0219030e070e040203150708040c0602030304230709020d090303150f09020708042d080c09060603070c02031630031107050d031101 69
    0x30540001402240316207084444819580710740042201001100800b04e9110030188074059040c4524025a4064000d00d2000350301c0e0b48401c3c0e800c803d0500e0001070301c400c062400580c1600c142d4006141e80460303003a81803041e6a80c5030b500100342090a4000311076101c0c1d000e0814002400d50084010f0702c51805081c91000d40c0f41c640d08101d031a44410b0300e001d4900005415010150b0754261400c04083c40c050085980017a0b98110340c2c410b80e000f003151701c1c9000e03070b590005405150305409035400f00a009400e09035454184001500e10182c03501a901295a010501c1c00801c108407080b074018000171896044400250703046c41485c1c0305110200404041034400000301c030350002a10a460140040c1140ba4540c0c6400500c03040742c200030051010400c03100886405070300c1c140309020030b041c903400400c4041030414409110f01040f4018081c400b501e640003408c1c801402031060948660b0514000800c1e0005042c81841c02c40250440c0390b00c014204100020181c200c684003060958040080c01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 346358021 1250 346356771 346356779
    0x20d03111e36011707030f0b0a090b040f1812021603051e0d0e060d0908030c07060e0c0607020d02150c100e0601030c0515070b01030b0103030305090c060910020a05011103010609 78
    0x41c3c01c420341c215144d00300805404100e40b07500a4120750410b41140c0000a05000d6000000b080c08040f80e1104403c1a51211041c41c5424640183d1080030040c00c414014502a901e40000c000c0c40c44601600e140a9000500003161003440303020700c41451084001c04054803400c20f25100c2400785c03842d0380791001c220000c0568120100720481c61200e1902d40102042010007840203d5105c00a8024104d503101541c10010300002d014600808490100c1c41d142c070708619040044900724403e8000a902c48481a9a04c0d0741310411580301550642d144504d001e418804283e100c00043c401c2c2110190201d400290b541e03000032000b101405024043c01810b4005004688500b801c3c003014000e400d421206100307604042c40001144038003109005d18104094542000308407080c1c00454403150940010000d060307040c09480d8001c624400902943c96014000400342c1c410740000b01d0285100c007402000d901e000344041c4030080c1d007110082c400d007508007840308040e80c000d001b4080400e40e80780c400310f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 346359271 1250 346358021 346358027
    0x50910020a02220618150807030b071d031537110c010207030504050a050306100302120c04050f1b0703020303150607020d0302070303020d03111e3601 66
    0x74000380c0d00900054205405158080fa01070307108491080c40f9600c42c10009450f0403403560110103100c40744000280c3d41d80916011804607225440302909600180003400810b03002c1c1350058101c1c00e40c0c00c12000a41002c0f00955812185192030703603050080e400518004030f040711030341d1720a01140c00b48900c11044a1394941c030007104ca9a8010a4a1101c00c41d0240b000c895030201c44c1c141320104002e0300300181002038034203903403100c1f00c100d001410105080045080000c1040007415003200034003c1380c902507460300c2e85179800c2c0c40b01910400503118820b001d0300040c0030540c04107402078428000c0e0300d0304801650708070000340c52003403c50407000d50300c00c0c448901e0015554082c0e40f41c2c0c003862950b207800c00349003070302411103491907070024ac2000a640181d07508061900320601c6038003d02032552070350030040e0900c000340741d125062504102104510500d00302c02c44e05001c83c80324401e050710b80ca2a410071014040c0c0b00b10300258000d80d03580c0950f2403100e0301e410130741c2e41440301000c0c0521302000011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 346360521 1250 346359271 346359283
    0x5040204062a0f05030d05010614070314040801020406030e0c04060302030a0f0201090509040f11150a1d04051f050105090a1401111c09120c15090e0705091002 70
    0x100c00060800070095801d614842c000e001002034a048a007622009840d11910a11078140031503003903000203400c14044900340290740c0140900c1c05c0080ca85014101d8000c000e11400c07000a04000045c2c0c00b40c01600040c1003501c000e400b200c80210f4a0300c0e11600c01074018803400004c0000c500c600440204980350902455081d294080c003c5e00200030740343d807601d071580c4412070200d06001d0305e0000480c00e0f460790102c00d481140a852000007a44132400c04509800351204054001c0c0c226440207940d01107004100c40300038205281ca0559040786484003061944ca00d07414642c090309100610201c6445018000d00d40d40400000416543d078070001507a80b803240c00c81c1caa412517544070040250140d541c01d5080319007010f041448070060f204c14501e046c03001101151074002c010040f000280380d8000c0c0140c0151000300b804230040c1c856601e406824001510400d0b00e2020700094207035038548114080c400820110b03c50989030304111401800540024560074019182407080148540c800168 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 346361771 1250 346360521 346360529
    0xf0d020d0b01260a0804050616060f05061305100b1b191506030b13080d050a021e0309031b16080c0f01051201210519030e0306090d080712020c06040c05040204 70
    0x17500c0c40e040c80e00042c4081a0080e1000d0100344803040a89000f10704240200c0301d00740020100003589203000800c000541501070180007075546824100310030070843c40070603415034580881542d02c4420090b0306007400800c0b401610300c43d016001c0c0080ba00d6041080c1840510300c2010000c4802e50122449002c032000c07444080c12284608010450080030030f44035000041c052116646481034044000c020380394180c40c8107602e590b00017071480304145256442e005112280b001c01740303141070440c82513030359007e010034014030001500040c0d42412001c020101c6126440d42c00080310035605c0501d181c5412982950038020102d1540c001c000d50b101704102c2d004a80240c000504503402e20180b0f00300108500f9000100e0f8040381c14040209104004009946040b1500c0660030f42851400903c002d50b04400f281c002c2e0301c01e80c1408101140459440940c405618141905580c2c0c40d40450301602007400e03048441d0302c0020031403c0084042012032140340240d4016503140c1c0d0381c00900c0124441d500c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 346363021 1250 346361771 346361783
    0x8150f090c060d0b03031810020d0507110a0807090903031d0a060c031d010203012103050d0c12060311010f1d1507230610050f0d020d0b01260a 63
    0x1c945506141c440e000e00203020780d40d08006808040701c8040703803855100c1112402d284805078207028280c076120b0001c80d0840c40324409410040100003000d0075a0244410041213182d01c0c210a04183c0c481084200080c0311807001c40d03500075503603070b80b56000300180c1c2c2054000a00f40389500c14040c0c920f501c44a00802c00b400204049040c07a00e0f02c400601100c00f44a0406840c3e0341c240c0303100c0c0840c2010411024041c2c1c0016a25490f00520f54079810112003074645100c2280003500c0070a4005082d030b50141013104000c910030000180c1159003001111002440c81d20b0301d440030050002c4d04402c80c2c0007210a0b250040081c01c00201075070300c2d084e1044d410341441d503070440c258002d0801040c142800810303484c0444c20290141d480b130b0382c420b00207100d140c03100703442110002c1589001c0042d25041410300c06081642414013010800869210101601a00b07074041030004649a080c42050541c1d0007010070b18003540c4400f00100003002d0f41400c02640d0800500000e16002c001c501440c1d040c3d4800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 346364271 1250 346363021 346363033
    0x1909051003020c1501080708100c230d0216110f03061807050406090e21250203060403030606120203010b0d1508010903020c040608010b03060c030a1508150f09 70
    0x100c0c04502030b40c440c3c07400001030700480d41c0401c1050200030702c00d8040c140c16405400440d08000c041444d020003454280d8405040024625030303103401c600540c501e40140c40d0f105141c004418529201031007040c426500142c400525003120322840800d0f040c0081c808c2803040c88281c03000d0204280e0b1900100a954150000e6001c140c07018103020400d40d580c442c08080e2054182c0d2400010100c4d1040e5114140e02c0d511224610401ca006000030000b2005003007030324410f000c50301d62403a168000c0e0010300e00003901d004007006140351240300842d00c40307600408492642c6003619004026025501c54400800c522006152902d4a0307802600e050b2442003482e1380c203100c2075201542c05807055140d400c24400e128400452001c1080c080c040c0110b0181d00100420384159003800101e0b21160b0003038082d80d14040c040607040d0b90104210750000080507040391a40c640800c81001402c0841c0e100c440a6000040050002c00100390b03a404071002101c404582e0340c900c01240700c0300c64201c1d28141250071003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 346365521 1250 346364271 346364299
    0x20609100f060b0c011508030403030f1229010e1c06051b07050f1b0d02010f0908030c0f1903020a0f0c0f090209030c10050412020f0411190905 63
    0x5036000d81800240d101c804250982c0d40d00f001c041c00d41c044040c084259450b0404141c2c041200c3e081e03500145040790045242c1455602c00500c0c59000e0b8148400300092020344403a61907898000700b100140105c3c05170a62903807e4007034288407180300003550124400f1000300f90345e483d1040d040300d0444180e330001140e100190355084000d00c0e00034685100b0001c84a100010b404000000d0441144508000e108008140042c036140403508142c2a465070007440b8a00d1803030321032520080c40b095080c244181145c1400400342c94200c681d0b08610218070010400c0c83d8009400668480c40701109000d41d1100c0001c045412800705480074090007590129210500007094005504202e03400780c07505011440d02c038241884000001d80c406660140c0105503140180780078000507043c1e035400c59213041000704026020b8402c2c000e502c01c1c62a111020070484040d51220031100a9480d2b00030410000801030310782c905401c1d000a42d20908400c601d0000320002c5014100200c20384000914465168040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 346366771 1250 346365521 346365553
    0x1309050c0f07050708061f09020903010e01020f18040506180a021215030d09150e0301020d020d02030709090b0f1c060903020c1801140105220b030115020609 69
    0x140291128400400c010200d0040610140c140c480c4543d000d020964034044907140f8042d4042c00c2021051083c1c00c2d40c0d08030501d0180c80b00c0440d14000c8000da103800d01c1400103401410302ca01e814006500015910914582d21002005040800600c00f894921440c060004880003200d4071130300010b90144140d2885451b4111607030081d103e14000d0720303011841c441c0400d44e2205545103c20440e017005100d07030a00c1c3c00d20550051404610b84400c1c1245402e0180811881356400d50081c050345070041c200f5a102134040303e411055508055607600105030704070000758012110400020025403022600c410f6a00400f0746401c4028031080c1c2403030900e000c00520310000d034542c20006541c0042c00000030b0707881c05107580c01400703500039200e80c44603102031000060390713103880d080c08400c58070041c414003d14090300791103e2403e2030300c4d680f2110454440420b8810310b5802c2820460b5403140020584c4070040198141e42840390041c40262100d40260b070b331010241c801500c3d50b0000401c0d0440005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 346368021 1250 346366771 346366781
    0x50f09040206070609060203180307020a05100c0215030718060215100819030806010e03071412120307021c020c1504150215010e0402030a06020d06050a17060702031309 74
    0x400201400e14000305a80c1e404100c540c40ca0041b922907402108000c0109111824000d8001c014400303186030550030b5000a0b1003540f140500c0d442a005000c0b00c100c11031090030903c40c01d550141c00a484031303005060305004c5810450b14080016501c4004051488148214208444a0b50024003540042071010074114800600201500b00c0c4040b0014000384204006107800050018844448005003001070842d04020005130501500c46403422564400140d450f007201c000342c2403641114405400680c0400800d20182d03254031901d00c00c620607582c840b0042d401640c0d25021148034141c09004c81c038a00c4051400034001d60450b481e402c003141003080c800d0741609070501855140980701c1428913160384482c1c2c1c141c0d0040e80080c03c0c58000c0d0740030401c03803030140c400c459141810b131515500183d541c1085c20001440031b600451340144040303d03070300142c2c040d0100900440806860750f2851b601840328400701089445240b000c100d103070380040101c4121224100184140c40c0c2450019030180c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 346369271 1250 346368021 346368023
    0x406020703031b0618060c051606050408090a080706090618060807030e01020301090902120f1903030204120b040605310f050a08090a0b0424020f0f0f010e07050f0904 73
    0x1040c0b0403d40008002d4861004003181301803920480c202542090021208920103c0061010401c22400c410041c41419040682c1c4481e0102d9155160325145a03180900d03581c10350801c000310f4010400c0c0b0030200c0c0c400c0c103480c00d40e521554280d40e11601110f00b45800003014031101003a1078180319944c4200c9036030b07610a28508000c9041e00038004101d0880e80242d01c0703000d41da66510542c40031881c0c914007240004030100d00814250465080a64032130b601100524104802c40300900c0815000783c041e10010070f005401e540104d0801c1c11300389809001150119070540c90034000519402d840c6110301c1818604807034440d80c4442c018034001403102209002d175886020502140d0015a080150b444c00130310030a6066250700200c03003070007902c2289820401c00c500080c00b0070702c0580e40b0701101115251085c090580d1021500409906000507605038026a00400070b001d0842c0000003020701a0307030a60b200070000c269800d004240c860078107015050348070f11440e40c00d8406180102e07200d5009 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 346370521 1250 346369271 346369307
    0x30304110f0609090106090801060b0f16020d0c060807080a0207030e09130501020d0c021e030a080a14040302010b0306010807050f0603181009150527010b060a110c06040602070303 79
    0x10021840010f04110b030240d110301b001400203481809111402c4c099540202580f560403420040d4455040751070b4010044143c88400800102c40c09641d141c1040b2145141c100d60304036181a299603008101600403a100390102e8401c401007900d2198030b100b2a904260550348406103545034000300280b000c405400e00101640201808012401c00e200401d400614000b00180c06400140e000c2e09090810744916a07040c0555104c04d11102c0c040101d40548441d460028965500c0b60151001450f40f40e11041e03c121200040108141e0154000890703030078114100c41407070381d131400d6031903072100c450142d16005401e803d14518030381482030141d508010b00c4080b040007440707111019450504100c0d003150189807140e40701000c2c441c1050740c00648a5050900b40418501591450040d054454200403002c1c903000e0300301c1015000b9880409c040f10000d100c1d50b5200810a00105540c507140b0300b2422500810188444501c0c09004403002c07100303141c0141c0703036443c91500c3c1903d00440c604403140c0d003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 346371771 1250 346370521 346370527
    0xb030105090414012c100e060a15090e0c010e0405010609050603090f0a0b07030606020c01200109020415091407210908040e0109050f0403052209050c0912030304110f06 74
    0x5a40b036144220717841c40404080040c0e580c5100c05541e10b403042e65607003c40128503248015004403008904168403c0b455280841e01e00c04e10006c0700d40f4440c05a0180c016680780848040240002042e042070401d001d030385584c2c01000c3d042c20007040b54002e100d01d8000c101b107843c2c100b1040c1000c0300550b0b404402102580c10004100c00403600f40b1010706000c641022884042244090700340c800c00020303044510041c01d460a00e500003900360030f641800313600f4455440409100c0001d094000d200035903800f510901c062603803000702d407806078014091340f4040d506007070541194040b03004220340700e40001d40d03c54800c444500c0200c3c44090780308004a283c0c4e61242e180c400410035080080000b0a41c08011141c95807600216a04270b03940548017028600c00d860500c80425400015600c88110550744682d5419250700c400d12600f1480e8091008a801c0604128411149001421800100744d07200da03091002c51100b40d07220711048500070107180b08031b13500400604050a40c074408000207460325207 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 346373021 1250 346371771 346371791
    0x10309110307080c130203040b0403140c0d0801052704030c080d0504084612050a090b060a031a0711030c0c0f120304031704050d050102040f0b03010509041401 70
    0xb042c030401e500800f503903a11a10440c02217041500360f8000c00104040308508504195841e128294406800034080120040000c0408415001210300844000d002c441071100031000144c40040d00f4410140f007a80c80010a185880380300c0808680c5012a12031340c01d284d540d0f0785d0166900700b100d540540d0000010301000850481c035101c2ea50003540101e066540300d4503402300000c0c0c0351721600043e90481e88407101041c045c4900d64200b200c4841e1703100c800380a120206904079440b40d810100c2e504200d041c841030005086855011026207030048008013190350710765060141643c0b0f1840000d200c0c54440d42c40c03080d144080c00c160f0f9001045841d002c0302403142e200c1c4e107078616080340301010496001005148070608d071480c52702c030348607c013a221a1051602c1420700780e1203015a21018100000c0c032440b2501050944040341d003d490f004007080650001d07803c00e40d00079080350281580904454002081060041054034102d0fa00104402c0c00365946603284c026813000807880c00150741d200c0310005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 346374271 1250 346373021 346373023
    0x31c0c091a030604050121030c0501020d06030843020402160b090105011a0f070606030b011e05010318110a18020901020114100e04030e0303040e070e031b0103091103 73
    0x50250208a81c0980c80e401d01400700b0084540c1030303100c00001854030150162003d0414000c600c80c0783c0505004030a0000d80c10241d000e480b400110088141c070b001404410040c12001600f10036140da102c02400303e0703100c10790180c28442d1140c00304040c51085540301c00d880c05200c58a181c20300c00707032000d030405403900940c4c095140000c00c101c038145070880070803040d60300034030801e80101010781023111001c84600301c0003101c0c4101242d00004e07000c009100740a02c42c4641007003005590009200643c0e6035207800c0d0065001e0f54138016441d01400c0c3c1070005840d84030f07000740a003610501303910210120080d62111748a5910700916904180820400101080468007403515101c129201682e2818a400024212501c002c0703d440c0000382c16061003540038119100314251070740541e068409403980e080507034030100d5814001d5454400080c000c00d56540c010011805004561600c5003102c024108151700c900c40070b10000d8a594641c03001803420344c4203403c004406030140e11300c4501402d0f05008a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 346375521 1250 346374271 346374299
    0xd0803090f060f0108190c0b070f0f0f0b010807030206270a03030f02010b03010203100e0408070b04200111210c010e0102031b0c07050f30060702031c0c09 68
    0x31145000d0800f0040051380018041011140c1c05500100154507580d40c6051411406014420302c1a0000c66448104080d503605100000c0e00488405000c40701c501d8004034954503031780d003103c2e89030309000002092000055101c2c1902d9000382024204451030003294440711a407000034040d0640000841c219888040c40c5601540c0603503034a040960200001038255207922800f240240c0c4104208845200d1700f034000b809a40c55088454000c2d1100c0c00c000f805030107a000050511601030060004121401c0030341d500d0071040d04401003048081d1401900d04104010341c0c59840e4201d501c945aa090007800911054450820424103145140c0b84d0030782110917090710320034140c0d40041888006480000c0307221544146007569440c000c40e19400c90b4880086103c0d55002e000b5003072101e00d8503034400c07101c0728002c1519500c608020301002c007083c602e2661011700c5e89440c0940d8020440d00c0d07102000707c076a843e8405031a0380c208034a0440d940010302941d184136041083c00c03039003c10007142c1300a00c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 346376771 1250 346375521 346375531
    0x120e0f0907090e01080d1e0e0613090b06030106020a020108450105010303050706051909231207140a14150709060c0201080a0e0d030204090f06050d0803090f06 70
    0x502102c00f810810201030301901070b00004a56800454100d04070b50307000c000710001002c1c3e02000c030650b29908005032440782c0314840003035000c003000c1141100403c01485000031206540d1007441039040390802e200315440700303000b2100140c104d4030441025501841ca11034018506030180c0c01500018002481c10300c2440c40040007441c002c08002d501043c00d0700500c1106011040200324651441d60081e1403445015001440b079516140062000514204d4074001202c003041c00307008220762440c0106c440040d10140b803c06100c008541c009480000400c01c4030340412020761ba203480c0e0380c2d45403d0b16800441620202c10300c038851b035040000c1c03081c800da89410942c240003811a2200f2018032050f01c50020071450420804c80300810000780c1c030030f40c0c2c0a00d454080c02c00c0d554a850f07410002d40a0003449020a0441c1f00ba00121642c00d07505900810480f4048841000001650300c0400300f51172076031041d1940310002c4580302d00840e140800543d0010500c0e03040351445601e07280c01ca820b06000310741c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 346378021 1250 346376771 346376777
    0xb03010b0c060a11030f070e040f020714120301090f020c030a0309020306070e0102032502031f240905090f10050f01120c09020a03020f0f090f030307120e0f0907 71
    0x503108003a168100720443e04161408420b12465040c0120920b40b400002c1004004030000b101194041d0700072080880100c80143c8180034402e542c4110001a5110400444a0380103601a1040728000403421684809540d49144d05d9a441e009400c1d018045042040b11620f50800500500301c03c204001e0141c0903007520b02082c240003d0041500b4050020044018000450060903003a079001c01203038402d16400c80401c1c2c4400c49504081190204840000c0d0103110f04018030007082180c2110301d0f00d440e042d4400b40304064159521041a0301c2049036500b00c0c13641c01c1811300c440480740e005a80d05c10a00c0080311615001c03411680d02e8422110095054203944005002c0080301c2480b550b40501044038282c840c81c81c555175864a40303112445080c18099002c2018a4200c1c42901120b028501c9175509585035a510005400d141e403151604038400c1904e10364824550501204bc0c1b0700140c1c01c04021030403400c10f25000c1d11400d144101c031560080169400a41541e00c1c00c9155001e500266 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 346379271 1250 346378021 346378027
    0x120e121c090f0204060b0a0c1b0302031e0601090209010c080304050a23060105060909041b1706250f0f0509040507020c100503061005130812030403180b041e0b03010b 73
    0x10062004455890b00310011206c010000030728815005440c182c07685c0d52269100b8405040003031328170003001503904001d5050040d224000b104080840c11000c06404210686003183d80c0c0f148030790228410503506901091480181d880424048009991f2041c01403069811100483c0c2c3d40740e000b081d0907000351596424992290301c18120801805014100c00d55881e403030041790b440002d20a06004200030041041490f9100100c10800c4041e0010406601281c8641402e4003000c3c0c0c907100304844180c030850024035000f040030100c040c0407100c00ea4a031030344890301e000d02c0b400300c40d0301860390001c000f03114081101c3d1020b9202e034401c1912a190300d0f4041c0642074120700400100300210340d4581d040107402d02c24000b466440b4840440e64400604041303980789014100640014401c0d0300c8031419000d00307040f041601e68104000d42c810751080e5100c02e15814500c202103500ca600740191b80503a01c043c002449402c1a4a841000c04120441000da50340d640ba40c002e509136000360810b5402482c04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 346380521 1250 346379271 346379273
    0xf06062d10091d13020d14060c07141207081608040e27031b0c0a081c0c08030c03090a0c09150503070803030a0203060a120507030201120e121c090f 65
    0x150326141c489540307a000059070a00e085001800d0030b0600c000380c820701648034a81c00700000301d56400d00f81031000c7c098409915140c040901150407a00c000d46a14461640186490740c0204803040b49400c60f000150400003d91500281c580043c800380a5103503c07000244c0110741c40401610091054107030b011905c1c0f5042c0710602c0c4245954a016261915040c2007a0014501000f03079a590030489241d5640010502116884d280102d0903082d080b00c051080071901003004101c455050b50740005154400a01c01402c0b1a010300c0c20501511414060005c00c0707480511038019900011700100300d41d0f8050654445403901300d019030140011035a9007500c02c1d06c04010305201c00090204a002d03000042c40d00200c9600c034400100203428295001000940e60b56482c500000981010030910192401c0c0e8581160303208401d02041c1e000c0f42c01001030f00c000c0b0003180941d80e800ca1811020304100300341c400003200c89800c03101060f4107400200d090845030941a10070324030064098540c1c0d581210751 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 346381771 1250 346380521 346380539
    0xf0403032405011209020a1d01080d022a0402031618030506040b041b0305070306050a1b0f091503051803070803010608090307080f0702030f06062d1009 67
    0x26810754041d000e0024050100300c8941e54016904658003824180b9040c0d0201c5440c00007071880c54002984410200c10110304031003a5001400c0302140300603582c05076600c0341d041e642d8404081c418800143d02c040e824400710504540821000560700c40200e000a040c440010181e07081290700c20348201508140381c070020351100348a40b18800d42c4000814590079901c90a46843c1c00520181003003c4100c085400c2282c1648503580300800741c10070300092030710307464580d440307410f644019980d99040102151954810344103944543c10702d42074034508142d10351401c0d124170f141d210040050000131800003034494032a140c10801218641c2e4005400d10b800050303800e01e598403503107490140c0d0007881003400040c540380843e41501e203641015080799684007540c620303621500034000c108101c042844c1080350300140c045c0190907c00c400b51802c200200221555404045a0b401e902c50f0f0104145c50460b810b400300c2c04100300307100000900c03500b40c400101d010308454061910008900d41010404252 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 346383021 1250 346381771 346381781
    0x51f050d0e06060f1906210c0810060503060d060905150702010c0809060c16110a260c03060a0207030306050301140912120a020d020d0501030803060f01030908030c07050f060f040303 80
    0x18048400540400a2174508101182140500c005110b140941e446c0c12030620000c6a104076081c0c50140710350200c3e108000c140c1c190956656100b140251408580e0501980640e407091901a0617000d4003401c6803200030281c485584140c03418020100e43c00c1260a102c801c84e4402d60707560b0000b064031004080010b1004200a01c1c1013440e4005030180216040514101c0c0c500300008030045e4080283c60411a00c58203500c10203650007d114400003034481007240440c503c64071a5158028040b4a64040688903504080b5555050b080744001600f4004154050144140289000a10141c440000c2400c6402005199421004500c00c0201e040010086100f000604e01c00980c20092004407004680c8400f50820350180c1d00410300c1c03003500155605842990740c4110007070104e960b5138103080030342e688141c610a02840c4691000a0305501034007946050300e1f03224005038515620705030102141d8000c541d08440c9401030b688610440a010008180507080200010143d0306145c607020b000c4403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 346384271 1250 346383021 346383049
    0x1080c040902060714030f0a0e31020f2b0e030a08010b0d0e100f0605010f0912140f030309060f060105030402010309050709060609050415051f050d0e0606 68
    0xd081c04900300040c1c07100c0e0103540e00964025003041c0b0211402c0d900c00e0941c0103c00c920a5940300100c1d11090309035210440800019095421030080d69020301911030310401e030782d806503000c00ca00c000d01c0c09001031075005181868a82000d10304003a50f02e0401b0803904c02200200c80c8645801100210741210303442840148c0f000c0708003c1d0310b0801040c2c4060902c0320140f00e6040301500c00b140d0900343d0101c580050005c802a4416205640c9900441030024800752412449003490309a0211751035000c4e02410813a1241038881c0c0c09030910f40596150751140c0d845003256074940380c40d0300c12884d503010030281c0764010034407001e181c481c601820300780e103400c4004011a1a0511000c24003002d641c204040f030741c00980a19011500c1007990814508e45072040d030005050034500390000914903171002c680c02c191401107070184003020300c1c0d100000004589006180e44071810084000c0c9004002080b144103009a0030424105a640400241118a0400d610040e900700c2004c0280500c0c0a00740c00c0c1e010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 346385521 1250 346384271 346384279
    0x50f060a0504021e060d0e010912030e1b0f040203070804060f09020108070c06142a030c0a2607030204150801060f0323090f1e0a171309020301080c 65
    0x41c0b5160700010310004141c2c0004151144c1c4e0b854240c4c0e44d4030303a00101c2d0300d0240348210621034610280c070800d000304000c000c1540e40b02615000b0802c0e0a1081c05070160b1180614000d000c01561025080040c9400a00e8150702181840380d1032103940303450004d503100e10082e89440640b49000d08005050381c0860440400b02c52410300400b005030f81000446800280c1803401b9034008015241410081c1510b50f0062076404580d0200b00007148400300310355020b600c8014088040d00c19100e0314050303000c01e6801441c1d2607800d00111071260f00c600c00703c601e55291107411103044001e44840c0c412841058900000003900003400740200c18001d00954a217503031f03500d400300266150410003000780300581180030400d51902094400241c0c416010070750001160081c1d2054101000c1c0076079035950454101e0700a010f1407492803003481e070004c40e1441c00761400001d0100e0030010f41d520034010b10f41a200d010541014042d040703a80128500003c09014440001a03036541041c1980c1c4c43c08110099261003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 346386771 1250 346385521 346385531
    0x120c0702012a0b1501020c0f093402031e03070e010315050307092309120304150203130c151403070309170a1e270909050f060a 56
    0x180d03800310400b80c40310b42100c0340d2110003080320000c44540d001000007410719040e0780306011954150455840020600741c00300c80f801a520400d0200400180380900d5020b0141000541c645082e007408045060030600d9410b6101e01d500c503403084240c000c81000f8011790000c220025000712045010084007a51a115815444c044200410340000141036604158581c1c004603800022051011f020700b8004041c5c4e404540c031203c40301c0007881c0d03141c28560310400441c05821a0003501c001940035002100203421007000c006170146942e840a0411520f03100d105458642504040c0f000e94003034110050555602e00c5981881b50750f0304110f070031404006010210700f040c0710390000c05070803040784000f80c0700740c44c0c0d41d4103401580100800c3c0009132101d820182401071401d482d074014402c000090316400c080c00703403241000003146540c1601c03101040048821840d500e80c103014100e034600c0c0002981403102c1d10340000c0b03405d40d41280011a085d41c80440382414440d400d0107007950080195408000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 346388021 1250 346386771 346386773
    0x60402030411040e10140a110a09060507020f0a170f0303060a05010c02030c041d0615090f0901063f05030403021207050a172a011b0b010308120c07 65
    0x914081c190301c4511a07956813000c0c10100e1001e1103100c4580501100802500c5801044020310140884080c070b256441c00e40c8901c0005008000d4070162240da55a03242ca20b800d0042c16180c642c041750042c0e9020002c5034a841e41513032a44d517030402034010b1440d100d00c840c80042c000c52400d00d0400000800c1d400510030070819441e044550400c071442417a00c0c81d141c0c1035500100782000c03109001e60340c1007410208051180c2c0c50b201c4450016120682c101c1d041685c921446000b942042d81c071b115400302c1650007080581c190361040c160080c80200000482c255101201002032070076140d05841180c01800088196244031a00420004442452031104840350740303e80d1a0b216500001f442194001000c800403601040000d02030840039001c0c80b2241d843d0700a010203500080c0100100744103c0c022510031600300c030500c2ca601d008810502640c110380c003005490412031000016251b0b41e41d10140d4000c21110000c45000b103009000c1e069481c1c07444000b090305004010036a000d60002000b4441c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 346389271 1250 346388021 346388033
    0x6080d0302041707210615270e0d03050406020909091605041505060714030a030f0f230a20040602060912040e1003020d14010b0a180e0c030715080604020304 69
    0x44c42119880c1c0d80d05c07010240d5480c0c40320041c044410306014100b0001000f0a92145402040c140c0d044040c0124002c14184201d07901511414185450260800d00240381682c0c06a04510f07040b620031031016041501c14000328400756401c503480141c66029001840151781c0c0c02c0d0b11500900b40540b000d20450400302072808100e0198410103000e10340000b6480305210101c045d10b071035800c40009490707075510328403801006080080046103c04c0d15050007115041c40d54818200f00c2c100d05a1755842101d5034203c0b00400b85002003420580e1030300d9a920708552903201c0004a2004441c14100c1d45a40c10000001c1c0361010080581e03240340e03c409007000302162002e05807001c64003c2100c44006075261300d880301202c00140d0000b5086298440401c08100b4040c410f0405a140a4001c10003039424508201e0b103101c3e54440c4c181420410501c00900201642220300c00c1190001114003090059020a15104c555400b40b8009010f100c041032200b944064a1030300302d10200d9041d415800c7c141c640e1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 346390521 1250 346389271 346389299
    0x3020103110901081801240602100e0c1003060b0403030309140d0c06091712190c0e0d06022a0d02010912080421020d12020406080105060d06080d0302041707 69
    0xc0c2001400b0160078540c8011700b50440940c02104090892101c8424200300c040c420030b6000365070250281800070800442e42d441400b42e620845801412800c0d0150148104050755204460400d521a14045103104271840140011882030b0f600042060860504ca1400d0406143c000070302d4214120442c00c19a200303042070051500000005190301c070a15100140055000e50344a00c081d0210303040b075440c1c5811021a11410000c0b4040040107074145002e41190b88c03608140c008101030080307030540da045c811591260350303108810044c41d1010030102c946049492030020074410310a103a00d001c05400c14482c0c510703818000d00003130240003425529a88640d0030001d00404012500b00000d05010000260405800d0020441030303800b295010025181e265418540e00418901d40841540b10b2591084508880c501da50340e2081f40d0070441081401c0c2c2c08941c61500c1d00b62030f0440400c501906000c50b0740400c24030380340143c0d0340b450111202100c14419180490b250442803003080455090900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 346391771 1250 346390521 346390531
    0x1b060c0b0a150314011d03030c0c0f0a0804050a0608061c0515100501030e060f0114190f0603061202090103080903010905151b03010f06030c050d05100302010311090108 74
    0x60340010340c1e00c80d04550002d01c106681a025900c00c0a00001800700c50b070302e81e0b00069031500003488100040807010a04080803c002050366000b000098030100600026242d0580304409070b9503189180000d05184ca0350188044d1407201d8002030130031051512205890040010b401c0101c1540340c602c00041650300c41d403299401050042100c0000c21605006484c2100c40340e0030200c41d0b03804c02000b0004056014018140800e1802e070850400c1000011518817403c01040703440c00c56800c04050380d030049001d0311403a400456079400e0100c406119914070000c0d10b6901000c0c0340e400d213000c000a00791340c9181e000c0381c0501000c0d460800962030f8500b0642c10b49800504403555507080201090060090301c42c05012030041407141e0181e880c0c03442c40c842c007503140f25280c002d041540c8180345c410b51100707101d5403501943d120820800b05000f900f240000f0b65280c1017041c148195850490103031082150380d50140105844c0620856030144540c1000b540711030740290424040307000184ca46080500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 346393021 1250 346391771 346391783
    0xa1b0203071211030d050103060b0a03022d0303030f0703050703050103030e040504170705010603143906120a050702010209030c01080a0b040e07140d020a050d020a03080a020a1b060c 80
    0x4030000030f80903199010700300c120081201d58540e13255159070002e09081c001160010704000003900707185881c8810100fa00c1e0024601194007070702440c18aa03c102c1000c02c00c07240d0140c02d41402213a134080c0041c1d07100300c0c0030380c50380d2075540762107003000301128030040541081c907180c5070040c004079074008421140c9580070303140001d1684450500c2150701c032842820210784403000408800300541034124400300c91107404401041d4561151b1103440314200044010407024003252042c03520300758030184075071003106011a40c2d41264180400c2c4558401c40c0c9070011050b001042c401d0a0034544601c6501402c540300841c0cd00300c040000a80741da00814806041205210120304006003581c460704d6038503001030081001c031a130181c0041e15a40c0328410700c051840000c2020001d410002d00d40450958010207595210f800c0c041081908000c2c01c10903030b000402080040009460000201190309440d001861040041e1801c0000703485061007040070700301c121104000c80fa07000100d9070704669002c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 346394271 1250 346393021 346393043
    0xa03022506051c0c030605040e030304080f070f0b0a091b052103040801090b0603070618030b09010209100e270601051b01020703030f1d0604030f03090c0e0a1b020307 73
    0x440381100c03902280c4a00540d480c000b1400341c155011b0740a1012079205807002d0080425074480c2d2500c3c0d0100702c03406001d4000070850700b6038004c3c40748001c0405510420305000d01119030b450b801381b411803c1320008015580c4084550030b004205419829100d024401c400e020303414840031900c8944001c60303000c9070408280c50b0b02a00b00c01170040c0c5025028020081000407440d00305170306440400d440c040d000e409104400300300a803103580700c10310004444008101c410301c0c1d80c3d1941d00480300200900340656086c00701c1c518503940c0826403203140820713940e000840d45101041004a03044524180710074401581c034000e6580002c488181e0140090070025154100004030a0b08907804490780c3c10340f54070006a840805415900c036a591504c0d14208104200d50030008400d840d6800d05c803c0c032258044000500082d100c3d203180410012507140100740ca481580e80e240381020a50000c080f4003080b001001281d00d0244070301c07001c0f00c521103071150700c403400403001a4991061110150401c0c01e10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 346395521 1250 346394271 346394287
    0x303020a0306030b04052413080304020105040b0c0a0b0606180f01020a02151804020a120507051c020403061103011a0724150504020307090909140304080a0302250605 73
    0x41d6220000950300541c4d540040d207024904181c58400444c1803d1604081d450304480303103000c03041c030a03109000901d14100441e1b207607220b901c200c0d04000d104034104001040b005c01d8043c0c0e008090031250003c40018200550036140c0aa02d04000514090003403405101c0400e1211107089000e810b00c8040d036180000d002e81d00c0040781004144040a03402c4100d440c0701010b8031106900401c1d44807440c1e00c94281346c0300f26404000c142d129100c45800062b0055034681d03241603441c0c5c00140c0002c0e01d030501d103250401d80c10700801c0c444103001681c40255030118003001809030350f01841d030340030a544155600e10740c113280f0014a09680c1c501e030a085060082581020001001113200d4601c0c03000c0c400c20f81d000b841584100103041034070264440584040c0d00094107042c94000e032805078440380c56920a25007007081d2000140700001c070035503002421a01600d0b51402c00d200500c0a402c40e900640010710003401c000e454245402442d0520b0007100002902c0540c00c07240100c29505245449540c5500c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 346396771 1250 346395521 346395527
    0x90624150a0c0506100513051f060509040f1b0c1103061503100c1409030a06020c07050108130c0311010e041b110303091e0a050a060b0f0402160303020a 67
    0x811540520480d100294a0328040e4006500d01c214038400c0040710f8242d42c8084040f0420402e03441465084405d54212031008005038004aa0040040c6142c0700c4000d010851340f04241c12580c000750110700c00048100160426014100480118034014080c4103110701c103041040d044104048204050714050070100402d4040d025420000241120181e05003000c28091075850705205a20910a4648403072074113000e8050345203000003603142c81808ce0074011100103594851002681e0602444d01c1c0b50000a05a2015100181c003440c0105442810103001605600015001c2090242c801140d040010501c06105084d01d50058202c1c030f141c6411401030341d403000a800c6180d07005042141c048200c12480042d803800799615a140880c2c101888104c03900e0b84001e440d020881c1e0481040c030341c0740405504a150441202e2011101c5c21100750b25214101301c02000102d42840c0c0b1b40003041c50f0303031400242500d0300c4042220214a0115440d00e02e103c2583d10080040030315801044c0034000ca80 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 346398021 1250 346396771 346396789
    0x20d0212070b070c0e01080a050d03054f08030604020d1415150a080133020703050c040516030506030309030a0f2102073515090624 58
    0x2c402e02c5440d448000c107240c131a1514805004601c00420312000020703611800242e070440b10b98106000e40201407858404401400c0c3c018a000442c1003110241624a5645110781c803481c6520448a038003204c466a054443c400c0001c15416442c3c0c44c07421603004121507908403600800c04660043c0d0f02c04105800b00c0c0030300f02c0341049200c0300039400100700d00b01c40d40c1310031441684000c42c0d2403008030180310010420b5010791094400040c1030140180003610081c508030420110385c1c41145d00002041080c84a818103030880f00005810551082080080811861510050842d020b00c1589040000c84003103c6082100e00101510317071003c40c50688040c0308407180b024003e815950112040d041030800103180a074112610311617544040300404010501c4a10030f00c0342d41c0a4150540762209541d1102d24808003c5044038124040c80000104074240700f40070b82041c000b40040101014040c2d18403100102000e081390002010083c1c0380341010400510004000125801c3c4000940420f00d20300d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 346399271 1250 346398021 346398029
    0xc0403030f08070915020c040606090b070f050f011b0e0303041505071110030914010506030303130503040e010f0608100513020f0904020f030435031302090106090801060f03020d021207 81
    0x1809900c2a485a501047c4440304102c2a141441020b41d104811218400d00e4170400141500c2400b01400054070740040c0269940914202d0300030131011507000d070841304481300b00f403c401d241d14820030035180c00c040c0300000c45000310301550610b4030700282050b051a9000c41c2400f000700020303107a404c00c501901e0146d001304001d44480e400540c00e540240082230003d6083d100105402707181140040b05002c0c00e40320301000750207103046407541c40d445480448445011140c2c0d02040c04042421042c10b003501c0d00826601c82c41c0d480c160314102014040c284041c01c2d452080750816400c0c84a0f443e404002c0c072032120b0004c80184d9880700400540040c4c012018101d501c14000521080300290350740245000794007410b84029001d80842000744128200381c1020b4050005200b00c000b01040b001c040d5a12107010008107940201e01d034000340c1407540076080800846d29010044c460141c0902c03404001c1e04044072400c0802e8156000110305981883c0000c1c800d2150b101c0c104680c1401780030342c500038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 346400521 1250 346399271 346399289
    0x8040201051210060210060f120c0929011b08160b0a05161e080408091807020d02070302060906030403022e0c050328320c0403030f080709 61
    0x90401c09070a681003d86482410018824800d40148860907407050108230780c1120410101c00c0e25003c01e0003201562401c090703540c0d1004480000d801c1d441c6010303e010b00c46012840407880c6614840b841000c442980100d070410009000083c02d15000c1e191941e80c041c1c200000f2512007109000d420601048410010241515001423003040d80da030b03821050142c028102809554803034404221100c004404601c03010350f040191070884613003e26030907904070740140110382ca4401c0030b001003029000c00e2451010307214808020041000d605001000f52203c45201500f6014a17603000141a40104580188a10320001c0494200342c0208238941c044902c81d4a0785410749901c0c00e86110103080190301c91070b52824040400c40c028490400c8034404c1c40407004141103244080307410300300446620f002c42e0a40d0b666082808402602c90210207403041c80307115840c40010b0300f0075003440241000d084c89801d00410b01052001a4020382c0d00002c0141514241c11540c2d2500b0702141c1c0740107198000e00c0345d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 346401771 1250 346400521 346400557
    0x180f0706020c0906060304080f2a0606010905101215030209010305100f021c0e0111030a09110a0302011709012c06060307031101050a050717041805060603070804020105 74
    0x581c02041042440341d084a8800746643c03140f062046034441220000c0120400300000701c1c040e01c0318806003e0340c8400300e01d14400d80f4068280c2e500108550410124540d00140404c81c0301c0da40114181c000e00000c1d2041c00310f0307402000340075020300d03a920100e035040c6450b0340c40d2100302c440c8a020000216002094a205540c3d80c0c01d0041d100c1540e082c45d0b800c0c20b400c0c1649061241d9003802103498280c02c0b1482c0400c0b401c044006440106942c0c1007804c280d54880903440c01d0404004e004c4c5018039024400012081d41d603160801004134242d200b24020b00c2c0400007000545e07004001001c901e04e01000512169031a10768442c01004031036000720441030710120100219080169091328801c1c4601210f240340c48040030186c1d940514480100f050040c2020900c1070752041000d0300f1010000c0c14a5420071000c1e40d107405010382203078580e0002d400049420004862042060380d40090b500d41e04020754200031002c60040d00c001000d240c28040341b800880d046921500c100c0b603042844030745080d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 346402877 1106 346401771 346401779
    0x6011503091709040f1b0c2301090b010e0907060f0311070f0506010e13110609032514010203190201180b0601020601120506180f07 58
    0x201521200c0d4000040c2e038100c00034000215000c1d00d60b480d00842800e100485a8010740d0401c184d080c240c41d010241c6c03041c04092070b107400d14034016529289030304080900b8080b0400c00c61035000c8041101920480c194480041d851080700b03c40c00907666110b1484080b80d0544244e40fa03508248401c0109900420310003141c1c610310704012500d036545508080254200c4603040c1c4200002141410410009000781c6015100c401000c0d83d40c0e0030141000110031581c2603004220004c1101e80c4012035803803000f074408a90f4020111084203034200401500c0701401103030104030016106001c1010785c0c001c0300b0b203500d41078181d0046007002a80300b14a081a66101301d0710055558400e4451101c3c1c1e034599401e80040c2c06042d0404c00740c2085000240b60000507404900500703211074200c00050b4000c07070102c0c4c001007200b00b0300001c4c2000c4036880d0b007403002e01088618507100340d0034002 = true := by decide +kernel

theorem cover : BRFrame.Cov 346223021 346402877 := by
  have h0 := BRFrame.cov_init 346223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 346223021 ≤ n) (h2 : n < 346402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
