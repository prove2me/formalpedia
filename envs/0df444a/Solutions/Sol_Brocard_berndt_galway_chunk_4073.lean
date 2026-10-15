-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4073
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:29:44.78108+00:00
-- url     : https://prove2.me/submissions/5d9f2023-0674-489f-914a-7618fb3905da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 732374100 ≤ n < 732553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 732375350 1250 732374100 732374143
    0x3031e09170304050c090c04030201030b063c0703020703110102060702060114060412060f0507050903190f08032e03030512040f0c06170105030a081210050a0b0318 72
    0x18800e918a400040c03013600d49003e4800780342200e4035030f00c6285108694031f2080d1a5224114400982203c07100000c181c0255014001c400c1640960b144107850031510300c5005804176841c80c03103444e9901c0e2483d48011030070000b00341c0710200b50f000144941541d114600c0c4c4c10780c2a150b64012a0380d1201290280c0c01a840b09004210104800c0b0203910b2100c0060000361074903890359200c02900c120344808540c801c2d0340d2944c180e2941c0d094404c90b500118145400d0389440d903004000303940e40c0b8501c0e00382902400e40c0d5000d84104440c000b20ba540482c3e02a114644074580349800321100c8c031854074800c0c01d829514059614108000110100b5240e042e00c80c01e0400720360422821002d10010411540780b00f050507000003080c50000500014412640c580040e100d4069904090301c8041c0d02c800d009078041c05e92040021041c0d0700343c0e85000c0140160091a640e04a0850008610b46e8070142e0081e07810900802c1e885200b000440c418a011041c942408440c1c05410344d54000c14090201c01c0071161 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 732376600 1250 732375350 732375383
    0x1b0304080a1404030b07081501021c0e1f2007030b1e0f2403060a02070f0b040c060314060117060307081606021213090b130903031e09 59
    0x40a050140418680340310b481c2025144042c196005810548401803240c04101480750310100942c0d000c20000f5030540302403d00380c0041c2d80d81c01d43c04501e502c204040e2054081e414407550480d10f400d0001044d001100644a11b848401d0b024182040d00044020032a52003203072400041091480e5410000c0c00000d207103840d074400c10640a85150b80c855a0619810660540d94410034000c0b81da12400704810f0030800c8018910201000903001580c0c443c1400d0402d640d404100240d020212a00260352a01c039454880e40800780583c0050864100b80700707000601414042d903506a42031a101009100202d4243c0a1071620451346a40020740c0c000e207100454000122964110f40302030120740c80340342c842d4134050030070710a24820042401c5106003081042da040240104944001ca0f0041c6070100081401d040c01c01c540c00344c00810741d19100d0102070360300c81c00d80c80031400c24941c4040051b90806e2a004024203056041e50308403138040001c98111401b5071045010240d4092443d01c15203401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 732377850 1250 732376600 732376613
    0x605090f0103020d0629192402010204054c0c0303230f100e0a0b0a05100f030509010c0207030b090c030604150c05270a0803040f08061b0304 62
    0x210112201750711194840c0c091000f03c000c07024103500d0092803a44c14049941403068481a15040b00e00e954004e0344100316018054200d000c6a8215807203503808000f110320240d0191041c2e500164001c200c50307480c80c00504501180e0b01c0f900110380440f0902aa2005003190803494644610b00c81040b880690b0760002d020300c00816089102e8200820b2854120510100c0d1707a00511500d412401960700700158420701400070395201c40e40c0854200700d1400c0c49901181c10711700400407410141e0720100440c4a42ea10b05610008101c007c3c40781110540c071070780040605284d24017400100341050007050048406005100e00c84c2358a071700070140d1038503545544260000c00b4129203083d0268901002698030240903440c4203a0080741e840b0102c0d00d06102d660300315420b08400e2010411700380003402c004c0c0301e2341c8071040d14501e0040400c40000d150800041d00c640d52640040ca9034803000500141100c000b0611004565089060390b010b0303543d44a0a450265100c1918101e82c04104002000540c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 732379100 1250 732377850 732377869
    0x1060f0509010228020f030114062803030509030f0f060a1805150603060901090201080118022119020301030209060405041a07031d0c0307180b031f0605090f010302 72
    0x510403a0341c0641401c201d400c400e40380103132110f4601040c02243d81941030600d1a4101004150000c01c0075030b5111a1080741020003070501c40c412658070a90f00344018200c501089160540444003d103d0340d01e14010705241d0007400007500034002c0000703007034030004041508000c114003107000d050180d070b5101a51004106980340701160052003059400854070420903071400314144603440710719061000c10075240c82001440811603a040481d0200141d0380480000d04403054058082c03030310b500000100010780200c0c1107001c0b580100f04014940c07e019403c05501038006561030701c6008901041c2c580980c4030034000603400500380300101c0d20904050344855807140c081c5070301c5100000c00508800c0d10000035508440040c0c2c59061121104215400540095000b0070051491800c090042519800c40b445182e40017409a428040c0c4c1c990740360050180c8150040a5480d0304480b04a80460000c4a04c21700710340b240740c001d02080904112000301d001e680816003070500c0740e01e590b00f04900c0c1007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 732380350 1250 732379100 732379117
    0x12007120e01140f0a1808032a0303040302010902090612120c0304081906050c09030a0f02120a08030f070e0d060e010b06030114041b17090a020303040816090501060f05 74
    0x2114016900801e5100c0c405403c1c01d8220101142d50307085d07240002009190a450a50010903200c6020045501d0010403107080f504031100c030192403020f00700c0140d4400041d5403501c00c03900001040004055040d440629894801c98400c034940c0c4900081c0451a82028101056030b402440c1c5003046000304030243c04811901e0044038580354485800c541441212448501000718910301c1c0c508100d0316005144e03120628500d81400c200300c600010f551b07440c1303800c005010440d074402c4410a545440c034000f1041d01561003102c00c841003a1400e0012a84200c0300290940c101e41c0100301064861034080d003c1c55401060000c041c182511a0001442c10b1018000c03030f9960317400903d00a44840014600030316103880c00044513000c1c10180f205440080200f10b0902504401a40e503250700140c00501c524040c5001700c140f41d90780c0500c0c03031502d114540080d51510002c10b000803100c0d400944102a0740c2d40440960701c02d542d801d5000162384cc01e00896010440031056108014030402c05404040f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 732381600 1250 732380350 732380357
    0xc0e0a030219030f050d0e0d022b05060106022503051213030c0e1510020d180f14121903030f1409010e01110f090f0102030c010c02012007120e01 64
    0x181c0e04d950300141441921011145500143e0a040805400164070364400c08103554960b600c0c121a80084d03001c500003410a040040042450614501c0c141400d09800790300c1003c880d12540c44110107507845180700c400c05e041400058001c0403514800068500b125072100c02440c21015850140d03607aa000b00320034000b903205413000040400d03030001086008100c1e009802d003407818095000100c21601c0c81d10742e4001c100c410883c400807a070026070079200040c07510300881200800b2803203402894031944071110703205c0d1184000c603100c80a098884a4101c0449080010700c3c0480c00700e5494510300c86207800f540d50007101e070501290107604804482c3d10715400009600100180356a82c10a040d80c0c048103a03991949240280700d805d02c6141d0702116225461410100701c04905e03541803003519030207801495512403020882e40200207454034000301400174446d0b00c0c103e000090007450203007200b184200c1c02c2142220010141c1c4100c4202c070b50044a80c030a070342c1440784c094800d00070000a41c0e040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 732382850 1250 732381600 732381649
    0x15050d08070204320f0f070207140d0c0902030a180c09090206040512060403120612060f0e0303040b1f06050a0e21010207050c040c050a14070f060506040c0e0a0302 72
    0x5100300548140c4011261003840d501030a003030340071781031103200105092004d040712800e0158a5400081d0b283c00c81c4e014100180341b03100c141c2d004c202c0da080b000200800350802c800c0045010380d01a00998854503010100300182084145911a40d000f28000601200d04100080c451030503590445c900c40c0d4005411145059030326008903200b5001c0200008850301301c50280010550b10030040042241804400d00c20740e410300400305082c15030420300403d919620041e0104d10000ea4002800f042154401d894891815050643d10010125480b04030780c941c03618840c80d880d100a518000390fa80c1c5a83d90780c203080c1002e0342561720712510f0f210140d100960b81e00801042a00311000c4070310200310000562100d0151611500d03003001d941420b8070071401c6c00751010f071080e44101039600c214000d02c2c2868080c805000175002501c503c220140109070314966600c02c2c0003c541141d80502c905a0b01000b401c00a1101107c452007070b921f030b0642c0000d072003000b0001740c80c051103076880c13800c8603840b040c40c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 732384100 1250 732382850 732382901
    0x30c0206030f15010806180901090605070f020d03050f0c03100503101505040b240405040606030902010f0201090305220b0a020a020a0f0f150e03010c0315050d08070204 74
    0x300e40c0003220400010071481040000d06502098060359101080c00d0000c268148540021920b41401c00520300054109000400d1020250070000789141c202e0300810140c14201001421100c80801210143c420345400c1c503041403080c41954405c0c0b0380003602900c1a255800813012561020745045504480c1c07000201c1e0340e9400344412803000c214603500041e10504010300c0040316080341e00880c4618504009074845450316000c11040072258207100c030104104240500d110300494001d1600180340900101c1c4054169000c1da0b0300e0750003602d8101505908841c100e09a40c40d075000100011401d218030300420b031260b0300f4015444104440c00410a8a038945402180c01c81c500120050340030303076100e0f010341c200000580080c161022940f141517040901c0100f00d5001407185c5d0f1341103049110703800c654074420030101182d604c008000384403628200e40001d001d0314621984003441d03040e2003400260ba217455a80040400c2d8420881400c4c00c610380c00b040001c0480c182500804440701e8107200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 732385350 1250 732384100 732384109
    0x15020102071703221703060d06060b0901080f101a09090c130e1501050a0306051c06050c160807020402070c0801051012080d0c050409020c101104050105070609030c02 73
    0x42e00b1402c03900309a07403240340600110b2034800c8004c0c00c140303400210031203035800b00d00180170500050f42003040c034542e04c4d2281004203c03a00b00c6044054401880d00381d011814164502c01400d07408000d0740e60402945640340200320804007900c1440d04586c0d18030007040781091b0706168411440c241100d035800d0440319001714030303102d801b01c8440c06201400035205081c80040385000c0301070038102c09030300d40620b0880d2290700d10058050411b410300c100400c160150b58425040800a00070213028440c92000c0f104038082c403060000f00843e13001d0304101c001000010b0b4001a1540d10340c2820200c1c051009036250400c5990020714281e8000c0d4003041040c4c041541c13904603000500650000284501c0d040c5501516500d66400104050040f00401404640d03600140d40c803198450a0009280054540a0b50340e0304c616803106810343e001107a607503407410022441c448a018245010b22026035900c5900842e8420390184901081c1e0600c0f4803030220303215501009034584242413500b030707110107500080c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 732386600 1250 732385350 732385373
    0x10f0e011d01140d0603170a05030a0203040f020d11040e120f070c05030a12080601020703080d15180204060e03070e280f05060f0f0306010b070305120703050912040f1502010207 78
    0x3804d0254032404100304100d5210b2800007200d440c40202c50608101020007001c910020b0003501c0c10680100c0070030180411142c155100039401800300e1007609081c03074120320150180545600c50f80c034080580003400008580310074260303005024546400b40700460200a074000342810b82d0b8003a8901408101d80d02e0401c0752000290250b014030124040948008108800050000c0d0440d0040c420070800502e5000070384815110421010400350348641180e070240f8183da0060300c00d000c5605001181c40700d01e038020805e5900f00c1da90b00c1f41901820042c103070351710035070310443d8405022080020110100c60b0901c08140400340c01184210700c15a0003401516640507404000f80d98803018403049240440c8020307601c000682d0810441c0a080380000e483d0881445900c0114400143c4081054410003c982050520440b5a204e03400c1120000340144000c40b0854040c2c410a92150303121405501030b10202c3c2d0420407200703a01c03801c00e030716004080c14408201040d99002e002c018009180d44095 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 732387850 1250 732386600 732386617
    0x607050a05060c0408061e1303031e05060f0103091502070c080706090f05010f020d0305220605070801080318042018011209022d091005010f0e011d0114 67
    0x483d5111810451044d08003107014100708038105032003202c1e0360410f102d042c2c1d5940c86a81584c0203052000d8904042d8080d00310701d010702c800038403107412282a20015500c81d07030282c40151000c0c8544503004c8015400c640680c0300c0130b0802032900c40c0c46c4500405c0d58006125041c403c00000d2502903403410041d28040054000b03401240d0b04820500c20811300e44042c400800c824a80b0040ea0501c0044c06500c6880141c02c01007016100c2c0c0000c1c507240788800b00c0d15144280c3e080070307004074102d0341810300c01403009440480c006070403080002440140001500c007039461540840e0015402e060403c8010701034183d00c503038036500401c4000c0300903030400701602c4540500543c000e07000300080c000400c84058007200740324403450071481c000036840da03000b01802e001543e2038960003c2640c17201c82c5c55030011501d5190b884640c0b80100548480b200c1010001c94000380c0310740f0001d140321102655515000c200c0f07035000843c1d14403004580c00c0e144103030528860040c10225024104455006a6a84003180 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 732389100 1250 732387850 732387871
    0x1020f0c0d020a0e0c0903010c080f130c080a03020c100e0a140a050414061809070b18040e03130e01030218040f02191707060806010c0c08010218010e040506010e0607050a0506 77
    0x1b51102281401e005070001030005141140316440c05250050541d01d0140220031a402084a00002c204480c5503000185c004501212040c644070715009640b07485c00d14806024411000c1ca0141007800b030041c40c1d07107004000f000c89042a04241c44002d003692410f1104d0b5003d001c2c0c5600092540302c43c403410210301710141c1034406c1f074a4003900340a4508003524200c0c1302604803000700316480750040b81e1a030a41d24120000390b600c1d880c031030446040041c00414030340e00618100044503020340c000000c011902199598581080d5583d040840380917007440040d4210710244941c4020703580340c0c1d240d00e80c8544201041c110310b40700c40d0089120300000d60070842030017030024130502c1034a40c80e5a0240201080700010458281031400c000c1180101400ca607050003410034100e801c1140d03409030380c0e01416010008548500352540494100c200d150041070100b80c440b08141c1c10fa04250044610506040e15041c3c0c001c183c0200b889960f40c4860416103941c040d81c00e11800040341486000d008002c1e051 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 732390350 1250 732389100 732389107
    0x7051003050405010e0d0815180901051801110403080c16170705060c1513050d02010519020910080a020708030408030901050919030e04060e0702011a01020f0c0d020a0e0c 75
    0x5002400c481141084143d154400e0650741c01b099803152503550300200c4403070f0103900c58a544000c203040084044c0d0040707081e0b92003010800e000c43d0541c031283c81404801c445c1170102501c161464221880000040400c940030403007070000c2403000d40102325401c0e124007141d440c1d141d00c1c011503158601541100b1310524250002d140310000c20044580034040484200b450183c01c0c03001b03a41e0300c424500d2a0100c03030322404001005080d2041000003195040400d4030000140c0c002c00a00802c021030f01c240540382801e0680000200c24420f0f687c1d1000c001c1c05001c5084841d90050300c504d0002031190010360340070010407001400742d0001c0c41c01244030700e041c0c5499080000409096a0000f000790341c440d444100e094800c04107288080c0701482d01820308240e08030b003202c042005400036811002644218405001050342c2c150701c00481240035403480b08010302403000482e2610a447c082135450b5011000600c241d00e040c90840c0640d81c401440c40041a95910300400348200454139801e07000c0300070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 732391600 1250 732390350 732390353
    0x50717030906030c040513062408060f0619030c0305011703070b09121b01140c070f022e080108030310350607110303130605071206150201150506040b070302070510030504 75
    0x2541403203680303050425069107550352175500802d004401003440c0d10441330f1031296a159225941281c001d80e140e400d0741d8440132460100580a0079034006803030300191410740001038148000b90003944481407a0099484c1041507281c18070305607405841501e0f9401004d43ca2050500c24000400d4803207441d03003412100708802034a56003147c6480c005804004c0ca29801c0201a200f18001c480200e076100c40c01c81a008101e00218500c4000f018002450000401c614202d4410f68000511402650307038810300e41d80c0e02d81d20100d40700d0000b45c1d20312a10310070581d000d002404840403092540400d031a5059444c00b00f80c2418040341c000700000307585d11b030024030070b10003502c2d8448091000008500015861418421191402c41700c070ba04000d0300d00c5548402141070340307104020480c2103a0402200b48096a01c07950740c90314620310720409401540ca81050fa450b142c140c01c1c00c09044030f01c000c090600301450b00c440b0102c281d0107041c0841c214022501c01007081d42e41c0b80c6614501c00760030740d03000030703189005d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 732392850 1250 732391600 732391619
    0x1d0109050c030708031e0403020a030b091902130c1b260a0504061d03060108100c080609041b0b1804060e0910021b0604050307050717030906030c04051306 68
    0x7016841c026005514140406000001144e0012103401000c941018003a286c640b5a4000d540000350300002c90000002480618201c80e030047c03a031501581c80e00024070411903018140400001d4111440c0095505c10701c1040d070284a04c4074032800c054100d01d11148000c8003020b82d4440032980f0695a80000c20750802d034140c40c0e5082400a0046841c01c0005040640b1074000d51044104001d440d00c3c07003000b607004403041c08469060140c00c50340196101d101290300d4040b00c090664007245010b802c0320040340301c0d14005014801c0503000719200d4413552146000c90001c141a07006861315000700041200880d0000c01b0708048a00c83c0b542d080c440c038400c020555009920000c00b00510f0001e00509540225803040e01d1030b108400103907141c19900c5c408000044004100202d801038808110510201100030b002076845082a6504180c580070440b05460024800c10803130b0380144a02d1403c0d00340301000751b40100389400410b05103641e42c00054036409407200d1041200d501c510040058121 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 732394100 1250 732392850 732392863
    0x2040312050c120d0609360b04060f0209031b0a05060a0f0309170c030414150304030f05070b0c0a0215090c0f13090b01140103020a0c080903011d010905 67
    0x400346006454640d42e101050b5a59010052401c0c140303800090002c09a0710f80ea01942c018107440340244040144005400041c414202089401d6821712410000c0d005444400e50005944001100550b40703560725801c0003446180500c20074154200200314850b81c08000b1000407084540c405242c24075000d043c404c0d58070184e030085005001c24403600f0004d503000020407010260038070780040c58901e1402c15030400c1d107d460070200041030015000701c0c5004040003c0c820b039180d502a80c481d5070743c9102801030110080007110b03408082400414002407040084000b1034580d4a4010709010403522054913500090f00c0d280c0060500050707017408279405000e001104203101e54a84614030780990303001d4031140c544030302ca8452040444250b1040d6111000c5c0e6165102c00c0e141048480035900d00403022010038000c809034000400c140c0855903229000f03c0314580ca2603a0f6182c81a0000d54520710190070804138682d155413550300c0070011883c140c0d0386010102c950740010603501603a0400302c0c180803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 732395350 1250 732394100 732394133
    0x52d041b0201060b160b06030c041505041805060408071a010b041409371517010e07030f0203100f0b01030e010b030d1107080f0a060501050102032b020c10020403 71
    0x1380148110054081072910401110350811160410f9965490000b42032a50300c0480c241d01c00c0c501145d28003000d51f202504d00075100242c80801c0269075052168800b039030540d600800c20b51080d4002400909103402070035003548036496210f1005c44200c07075181d040000341c00c12640c2d0440400c08008403c030b91000c203031280800355140c0e83c40341010183d031032079101d6411281c0b006405000502d5070041ca04800d03503a400c140f0038400c010043d03c102c0d0000301818944a8044440c6c0001c0c1100ca142c00c0620600c8500d0240030024503e4a01e15912882400380550091b80c0c0340c012241400b054511074080e4021410f40f010000854000340030000d4102d0f400c1a1f00d21405a02d00302d40e210b120b0f200095401400509410504040d40c0501041440c1002c240c0254149028650107008407403000645004002c0c42804107004680c0c90b03100482e6079021309180903030405d11a074010010500503a8101c0900d00ea150300144c0f900d10b4541d4020b1600b91048460700c02ca980c001800c106108a2801580c0c82c3e8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 732396600 1250 732395350 732395369
    0x2090312121611070b030601110105100303091502150c0405060a03150b0f040506030405010914060703061403030a0c05070b0a1e090522200c010c09052d041b020106 72
    0xd914002c1c140e60b84c614900403407500356000008103000b07138014840012a010020028001850030001c10202c8001a01c01117010416040c00450100d228500f204c0c102d0b0003584c005d00034074682c00f10214400e40e02401d2a1140d01d42007001040f5500d405c1c1c01014172006c16240414002200b0041c202404640d41c4440e0001d801841055003607482c0c00c048504403030b000c0b02d400f078480c2c50f582400c130b00604c0e4004004000e011680c241e00b440d808049000303407103400f054030b007040901c2e0380302c1a03140700d030101c603402c2c5038140c204004013030300d10b4010440c0c0040c180c040c400316803086442c1d460342080c9502a514060201f0250b401d03407040302c455100b07a591032100d2481e01b209964506800701e48188032070403090507185000a07040303000d80382c6540000031111041d2078002c03e400c48027031081e6055100442071341c03155081c0340600030150300617180c4104441d4064007110642c8a41e00500045041c8288003411041150031100f400daa124010b08040d404040b0203517902c2c8080c90340107421030750954000c8440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 732397850 1250 732396600 732396617
    0x53d091a0f03191a040b1b03130b1e0109020705070807050f0d0602070b0c0903010b03120307031e0e030a18211110080114030a021003020903121216 65
    0x26528041107016100003110b007030140c03180c654904090318103074203000d0b880f40b0141c4e00c00f00401c1c4428038503940c0c00741c01041c0f05444d12100400c14005684030481c4c14011602041e480840004d60102c2003c0c0e021400805900001c0c898074000641c01d4400c0c0e010040c01500410410203020041c0148401042c1c224010100d891812002c60840700c9059601486952080c044005100c0b5580450f21790b41d611212403402840c1141407500c3c02c0d0882561300b4040c5d8a040c1810321503050002d0110755a148c5041490301395603402c017046016000d01e2080c40c00741016220043d1258109004041881c2e003d00c0146448a0131003a00805c912002640c1248081003683c0402c0324035020318003102e400069004c1201c00440320300341098001c90307411107240c00c802c6224800c8500380d40100740c94103a0b00707807032070219001040e1010180c1c1e956406070040d40c00b0f4406119160840d00070390041c40c0d00d200140a032a50703829004455103103070300600650010546502d0802c500b4201d601340d505680c2c42c0c1410075040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 732399100 1250 732397850 732397879
    0x30a051b0939070302030d0501170a02090c040f030f12090e0103020d03050c16030b010803090f090402011106070302030906070302160b0405030412050f060109053d091a 74
    0x1000c50655403001c03080280c41c0c00004141c0b04641400706031502082600d80e03151241e1800a41e680e0000380f001c905980362000108a40d8418400b08440d032001d00000e251220341602000300700000640109608282004005170701800319206100550040010f9103880c403180c1421000605401800700403c0600901840f840480c01e0b01103040d030f5010341e04c013003594005150a640da0300c128240100030b0b1040003e04200801b04164400079240710710541c5a160b40e07101851503032801540c0352070f82e0214002012000354200400c80581c01801450b08460040c08009030034100a42500c0450002c1e80020030007007600000c000464026a00d490110300d071a1140a01c5201614000c5000f8440a0740c0d10200d010b010b000c00035100548142c903078111900c007103464803c0d910000012145124017610000080d080210b200b40e52080b550788905030400000c148074494449000424400c0341000000755480010031650f0703e00140c4009000003841c020110f048090400c601000140300e9160054181c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 732400350 1250 732399100 732399121
    0x3082403060721020c0a05070b0a020705090901200a09050904020a03030f170705120f010303170414015702010b060a1e08042609030a051b09 62
    0x182e020b241c41c0b424003201500108495601d280700480316030070301d0010880d1a0480000320740c40810a04c100101c42507207a407050407a03054001c1c20080409a006001308200a090504c3e8865014121100000d80070f0080e02e07e501c0c80810f07190b0b0b81c1d540400080355901e500c5810107400d00c050001150401e0640c5003681c0001e0504001f80002010042005100c20303241e0300a01070180e6030300d2204412580c2d4500140d005009070408a4032403460f003103820108254503e881c40d0b07103040c1d0380c050b514650070070303484146011050360190040b00c402a0485c0c0c19004508284180214204968550080b8580d2040100d14060940c0d0400c84800d0390012150810740d42c941440f5900d0349415440300c40000802d01c182c0c0145090141e181e004880000d030540e150394018100110043c3d0b01c0100048040d003142c0c1150300381402c543c018100d808400c40c61092a01001280c444181040c5072140381060100210381000703220501126a644545d00644c045141d600b00b06841c04002d40d1903007050301c1c2260350340307 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 732401600 1250 732400350 732400363
    0x1203091e0b0d02120103140d080c070f020a03120302090414190b03070b0316090b16020906060d1d010e0c011706030a0c06120f09150b0f0a0303082403 66
    0x3800c00c1e2400044504032100c858060300c64200204c0b41c0b4900b59a034078104042107119803a42c9000a004411080c44220b014410042c0030703581505000707052070420f981c1c0e41245141ca07103069a02110b012070000000d1014074a00500c140a980e0141e2070300c1107501484283c89880c90910320401d83c00081201e6845070308031001b6216000000031841400c418040383c20900070b41c0010959001c000204641800080d8056a0b0040166500404d41e55240c480c0569030013002e040c080446403240e0b41d94090701d0544419601b0a100410b0240740403030525078102102e2110302c160581034000054440e14074400e20406080c5074814001e04007890304200020324850105081608400e0302c507003c110103840c108031a280442c0d2220b40e030301c0c0303080c0c07115000b6201c8810000030b840c505007404e481c41038102841c000c1241150f0b12002c80744450041d164450060990b4081e0b003600b00400402000c0c2655541c052480218002e84a030119810040d24036003d4290311182c0d0001d50404400311203441e140007908 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 732402850 1250 732401600 732401609
    0x2130c0c060b060c0706020625021002070c05040e160902090f090405151e0705120c0a030b06040906081506060304260706060501173705011203091e 65
    0xa01d042010000542c1c50180007100b100c103209000000c6080382d00002c08501407100a070141d506484662720062500d4a40101c100050708489495200d001076500a4807520380b0581d24101c010b6117540104003205d83c00d05018080c0d40c807629108400303207500c1c09020049c20205c0c209514203000c040105d45c1403d044012070703005185043c00581802030500c2107103040c1d183c54505070001d040900101000510300d86e4024400100e41c804140f001e80140c04444015840c010302c1103e9996800035182a500305941c000281034449101000341da56440081c0042e0500c100300280850070006a145403402c1c0c2107a1032000c1031035034148405a5101c0054a40c00381d0b00440b0346100385110141c42c40e41e41ca03c5500300d48014004a0850104445908017005903070080e07130b54803824540c111880840c03000c2030f03071144203620741030440d40c501c50041210990b01685028070803e101148010b24802c0b0365090f44034018001d0509036540406501150b00002000200311400d0b00840742d00195070307521601e124 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 732404100 1250 732402850 732402863
    0x3010605070201020a15140c0403020906060d14010b0309070b13050906010522150e0907031a060418060f03030503010b0313061d06100f050607030908030309010902130c0c 75
    0x1d00d0411a032080100081c8141e1108400814940720400300c0c0240000d0060035502c0820f080000342100c044500303035811603030014041c001d50b45501e41844441e6100c40203007456661103181d03406075081607a860900030801c1c088542d40e40e20381140010300340f05a5070004245141d04100c02047d01e05609510030940e0000c66800340c0b0b549a90780161228414024401c50000648400403820342042c0000d02c11204592401c114400c0c5c102c0741203407810320700c0c2052540010032001160080d03100313078040c09400070032500b407500310040140001c8458210703902144041000c1c004002e5940e1032409040001c003201003030401031605664010303165000500400072a20b40100010b03914000c0c0d50149040700d50004002c000050b10380401049840d42511003d00520401e00070a0b2490b0145200e0001c884a030703070304504c2c42401c04c0200007107a80303d800250204205c00c000030403951018801180101e0041000140c803024074418400703200d40300031007110602d2420346221041078102da59924026400070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 732405350 1250 732404100 732404107
    0xc030e0303010323060117060106090b19051c1d0303071d0d0c0924050f0103050a0e0f07030317100504090302010f020a03021b2805100c20060c03010605 67
    0x1000900f4200c0004d1075545640308140000420b4425462141180302c00c9130b05861081e070700ca10703095448240c10b01c29900c02080810090072502c1101c8580b01c01107500e49881458008800001c1200090002020302d50303558074003281c940386034248907001440000d10051411490114000303001c0000310b81804184140220001004e0b0362000c07000369509030312204101c00c0c1c5484020f480010014250388400100f1844d2209250303c04040f2a201158001400030300c0720301c2d860f00110090900503291102094950400302403000007071044c03d0004403c0130040450394a54180241134985a1000e44d555102c840e003030103110000304d05c004081d50b03001d40b400f003020401881c007240109201c0c400c03100d070701d072000c5900d841e4268580c00810a09980d080c4602012070058a803a03121b0540020380198a000090b4503803014092491008900c1d0003002542d5a440c4031652000035180d9a109104c0051041b0099034804401d40ca10854440c007918002e016510305610071401c40c1c0310601540d010b110010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 732406600 1250 732405350 732405383
    0x7200f0c09041a270a08042102090a020705070603050402060904050c13060f0e03010b0319021207030c030b09010b03070303140c030c0d140a051e0c03070b0a0c030e03030103 76
    0xc1240c400f9011400100091615040d045908400c408072800500c0031076160038480c01500010f4071400c0c06412001107890585030100300040210100390741c25041e4603054200d00035071389100030301d4820a40000056503c8040b49001410324440350000d2090500e07040074800541c0300c10050710403603407041c0c80c0062640c46580d00c468050040842c4030a20f0460114082800b0364030000303100703068410b42c0b40c0201900d8070341c08050989280c0503846070540e1186105110f00300701032440018480c0003410003c0e41d4a050000b80341004180e400c19580700c400240200100301000c00000e5010380c0e051f00800020002000203500c82c4410f11002d820000c01c41c20301d01070344001c0000c407030b40c6000032002c032940c540441c480c40c1cbc0c441c010321714203401290209004c010703070350519000c81c1c4103049581d0301c1a2404621600c01c0500f440c5070006102141014010320071200000c000800d092802504661618070f0002c98003802e80b4001032941d8101400c0c0890b18100030300010540f03043d00c0d4001d10814000095 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 732407850 1250 732406600 732406613
    0xe040b070903080c1005090d0203030406110702030f01140c09090a24030c03020a050307030506011502030706020c01051f06120f020c06010e09060f070905130b060307200f0c0904 78
    0x25000980008000a100c401c0902d0015801741a0701c041c0c1404d010980e20021000d0f00c07142100d0303403180903800420000340024881d40c81000e2000e4414001d90911400d50082441c24442d007907140002c1e950b46250b0801d6100480055070301c80314581000c1e182c150142e0208244040142605090303540343c250340c04004ca25006c600301648114100e030b4000540c0c0f0308000484d004144000c0e4012190550045004d08011652105507600180200203a9180c0514040d042e1a01c0e00810f046000902a0400081650000701140c1030514000700f16420065801404402e0440303008401800d282c0d801c010310b1b03410001c2a081c0a0000400040d14921803255074041c1c8100000f0751064050480080303032492034690f0329405102c1c04c001700e803205d968003600b03184620000c2d030f80d00b008110145401c03c42854040504004441600c4011800d0300451011400541090340d0410104202c2302a81c0125a12904070f01c051000c2100145541390306030580c5505e941c180901203010300008130015091010303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 732409100 1250 732407850 732407867
    0xf0906040b060f040509010503120a1404050a2d381315020102120117032a011a0a05090c042d082e0f0f0b040b0a0e040b07 54
    0x4018021590f210000040644554400d01955129010702d50002c40c0341d090024200e0b8080d134414074502c0c5409485c28040c2c03607201e01112060078071601004089100d0b1101d815420040203120b1341d0550400909a0410a11807081260702405135510020000c07080100602a6a215280003840b030304e5109110f200411103000d40036010502c0c0016101d113a007014115a4001c44400b21007030740840420210480c01d03403290300301001419100304014084ca0040003104c6103400802c07011245024402c03802c18020084100d00c50185201c403100c602c2400030280130b144802c03105110124100101c4500144845101d40102c078080c90840700080c42c9280d1541c110307005081c4141c030500f112420b80000d060420181482c2c0514152100c40015680f040012900090b00e58900510040015503a450006200311003007188015250004064640b1480c400c001c800d4000c9000840e550040c4000d00080c0c503440c03041d190107140d052004002025480e1442030b08140d021642c003500c1d4803500000c880800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 732410350 1250 732409100 732409121
    0x330030e03090d08031e040f020f041d0109030f0504030512071b1811030c0a031e110d0e150a11131e14030a02120a0b01080f0105010e060f090604 64
    0x1191180e44062042c1d40f4081c610031514020200d1101314001b400d8405a4010340700213103c41c10f104100d0005251000078070600e490064000561101c60700d088140180c00e20004113256503440c518081411791200c2024a6213a82c0d080c500d1030f05103550361345a80e900b1185220a9a00f40100e2130a01304280c4007040d44440c05985030785580c05454903010050240c1c404c55141d01649000e0f001c0403900314040661b44150038800c1b141d81840d1f503040c0c0c1a4081c1001d4003000c0c01c080030b000c2007183c01038420300c2640f2907819825100c0d52242c03e119125002c50f001120201c10341c0c0e000328400381c004010344040c01d03401000041c012607605031481c0440c0050084000c0c051200c84101e5020a00419401c543c08030a0101810042420380d580c50b103038130119040c000395070150401032994003d8202041020140282c02040b00d0002c042605c2d503106a000030b80045095400118110b42d00f44003d010f10341c05000c010302c2840413400c00070005801c0c04502c0061502400010f40000d03819540c50388040c0301003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 732411600 1250 732410350 732410359
    0x212a050a0c060801060201050a0606091806080d0f021002040e22170304262706070605072a060c03020c010516090812070f0c08160330030e0309 63
    0x16a160b0102038002d9a0902a1500540c82c1c03100090340008203016407070841c0d106898091583c1c0c00d060003d01c16060044620850316100d1000049180c400c010990394900301d0b45c6d80c40800c2c54031480003402d08040c146202e04d00c9005000900c8141e0421192a800c0031580910305034041c0409100c0c0e202406182e8041d00041c180800ea200c80704108006510032071040351410025481d075444c00742c101494101032040b80f10288035403124508200b181124528994005805030030100b400210681e000040031a241030f11141400561078000400c412104601000015800303403a0500c040d03540e01d007120240100e0349038880403078a98002d034103c8000d40c044030003c0c01146040702c2251304004000343c5d8000001c40b0308400043c1c001010503149840c0034003050040c44d0140e961904d150306c0e50315000c1a182d00700042e00001d60100c2c1000710301745c408283d00711b003c4c02034514200005800001c8005a40e804690802000e480c0b200543c6100603150504001030000400701c20540346001d044503440c0c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 732412850 1250 732411600 732411623
    0x25020f070e010f1203211d01091106040e130606030605090703200a1701110a030e010c0e030a140c060703050d060b1903020705010f0603212a050a 64
    0x401030071020181603c004003255205a561a8101422000403003009000200024040e00000c810748040482e05030028a010070a41142041d19803c0ea64125000c506a0345d1000043c0801c0b81c140c000d903143c0e460843c4c00c9801c192810501d6020f240c2c000b001144011040c8a5450030030400c0da008001942d0090002c008a14105442540c1c03441240070035918602c49074208007559500030050281400d0182000501070b20700703040c03070024940440f0b0728038640d5220980d000c0c11249001c003905580440d540c2c08500e0030b602a9100c0e0031250006454002c0000310910203070291400101d0045043d8465202084080e17200042e40c00c01504040c07490380700300e002813248207041c1e11001400d511600c003172040000603602e40c03030b5002500c0743e00c8202000700d200030f0351031b21f80390700aa001c1c011082c02500013140baa50021103141c12110075810456410501d030811030503020a0510741c04200c041414152070030141c2268109000d0b21100b51004401c00c0700945400b04102400310041c031545c840010b00b00e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 732414100 1250 732412850 732412859
    0x807060c020c031e0d080a0f0c180816120204330504090302340b0a030f060b04170a140604050f0c01050d020306010509130507030c0825020f07 63
    0x445224044038140f0034460340c03444841e08600d211440413001c01c004028000850200c1781a42c003148003d0001012590780e01c0e503201d240301c03903004d440c2e0303642420f82da5140034288520000d454400941c200e03000d03681c003a249041c1c1100040c2d030741900b0b644e00b14807416034080803031000801400030072031001100c10b02810301283e034521108402132800c0b0342016402009032039105000880d4440440034005038040f1814019803a06554000c032080b685058410980c0b01c00c1101c0000301c1846c1d40041380b4110300162a262030366045c441c25545401c648414824145000d01e40c17050f0b8000c90007800c003a00c0000001e0911140104181d0041603409800768041226603420580c4600085400b640c2c54000e82d0a09010180003081441c4d8211058449609291903110324400030340000b02094144001084419403e030fa0700a12407080c0003800b0004581440e05400040a84401c0d6900f1400d0001c46020b206607040c4020074901d6005000f08403c8408070560000c80c0342054142d079400342405450b00104 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 732415350 1250 732414100 732414103
    0x4020304081e1b0a17031e09060105011d01120b1210050105090106020f0a03050a171303030e0f15060f0607050c010e060702090f061f1701080c1c0807060c02 69
    0x11030030107a185500698210f910401e03440f0080c255005085450801a1400580c00740c4051508500e01c0034007d81c5200c4800320040e8594002d82d89415664070400040003e517030303c14510b022592814004101c20003008002825105102504598160b02c510000328180c80307090b1401c5062a280003100d100c000310420b0100248000c2c050103001c0e1410034000b1038210700000c1c000400c0344a410040c110050350b07480441c0c10341c000080000421901c5041c10708403002d0420701c9800340c910131441d10300c07480703a0385400b5084035010764520390a07030003200108104910210b01194820750f0104450400c0c0d440b03c0001c0c0140030228002e56100f040400d2800c1030040010300401c010f102030301c0d0312030705805a03020040c0d07038010030000a5001114000046440000310030160700502c0240c8282902051080e03000c1602c40d1955004000894640d442000e405044030054011322454000d400c1035035044003c41c204001c1400c41520342d80d400f5151104120f00d5604a8810640180042162031940134000f0b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 732416600 1250 732415350 732415357
    0xf02120f15041a0c07140c12060f06150405010c050f0d0c05010b09010e0411030106150c11090108120a02121603030f0b06030115050706060303030b0102060a06030302070504020304081e 81
    0x90750562290751812003040c861502180c0600c2c07100d22810f08017031265650007501581c180300c1d14828002c0704000c000320344519000fa049842014050412443d2042c0ca000b40410700070b00c1d05229100100400028980400c2210165003080c07078041c520f4040c4d820181e1404160701c040c132046208584403001016404082800f9240c403940013800b19000b15400c0201103c401e000b0241c48466030004680069a0070541650020b000b0740040b030107035550609418420401c40108022904d042000030801c039146211104031441210a02401d5040143d407a54031030110482028030400018414607141c02005148032045004643c550340f01a00080a071501c0302d0004204c012030f041c241d51f00d10441d1035005804915601a01840c2941e10700041e0100c8503200c10414020b01808201160201d14a4003680010b180640c43c08554148140c000915203071009010780802d515140e01800001d6001c2040e90441c0d604603405038494035241003101c0320340308a640d520041d031210489a0f00c5c505510019 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 732417850 1250 732416600 732416603
    0xa03050406021011031306150303081501090321140703050409050112052806060914090d0507020d1a0708090d090b03061306030c0b091005070f02120f1504 68
    0x2c1e07030283d42110355800150360400701c0c01440c0368030500010341907410030b480c82e60166018440104540910040c50b410284158000790001040102001101056103920052401003840d2041e1083d10b5034462141d40076619010800504901d150340701814424803444e1203940d6055121651500b2920b0003614036403062045440032403c0c0000000d22068401007480142c1d00314019080040002c03800003090503034258070706100103030b40f20381101140c00c600c182c070003606d9440000501c0722240740c114111544c0090000119901214401c4991030340305050b102c2d0541d042d503103040300e00010310300418076451030381c04620320280100400c99510780c40f4504a001705101016207841240b8010201c0e031010007801000c1c08801c040021a1060034000b200030300a020151000a200391281d481010822581d1301c003507603044c404210a402e51820607144500400f45060891074403c55541d1100207040e4240c010f880340c0c020303412011400c9024000c3c00d031040514000c3c1c5006c41080e400e541da1540090f5070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 732419100 1250 732417850 732417853
    0xf0a140103050f0c0a12020d0f0b041a01090e0a02090d0609061406061b010b0a17010b0612071116120b0c131e030803010e1f030c1e080a0305040602 65
    0xc182d840c0100204070b8025113032090510b00e4078040000545600e40030014041080d503007040310306100c40180c820131410400345880410384d00c0d509020002a20385243d6001e40c4140122074055140c2c1e08042d065048503040d24030300703900d5a68641c01074000c0c01060980c03500009130fa21f40f20b08000c0554413406103240302d00c008114050244c80b0410030f4210444816070171a108000b030044800c110a41c503003c1c10941e0300003281c0310724a4404128009000d6010f40d00c2c040c0d10b071140e0300c8240820700039800700850503200b581c1003004060b20328a03200000303000801807280fa906403001144040c000d209808100c090417420041d581c840741442e08141b05416580e0031620808a00306416070012103682203034401c1419010fa081c2aa003c41c1242020305180f079403080150004001424100598001c00d8003016111491600b298842d48080c0c2c980650900030023102400c0c800200000310060540f09101c0080031016490034448a0fa00260b8015504038850a07041c5004c055000b070040047ea01c0f0b40c0d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 732420350 1250 732419100 732419111
    0xc0f0f050f0a020609010c0f0f060501030c08030316260c0a1d091501050c120315040207020a09020a0c05032a151b071a01081b03070b07020f0a140103 66
    0xa40c065255205002d0013584180c04000303254407507100707121000c10315025030000001200701d44c0d100201850b20080880b01940c4820041040c48a0840c0400060440e0005540f440c50440c0c05642024603400c81c42d02449a000d03120050f00090300c8241860325880030010180741071540e03684010f43c010102100006a00f041e4200140180b01403502020034081d101c0c0c5059180c6112400e0282024450a0704200d0148140008483e0030050b0344006a400405d917690790800c5030360244a07150441055014500401080300140c135003100d050216400c441d03006031100c585000480c0c806ca803860015007030703100100b4a910003141492102c03454100c0400300c070b689644401c6085481c0c481151207100e400d00d8040000c1c0302c030410401950b80c4e051003a14810700d045060364410303400c0c075542654a01d01306149030050003550000c0042e01040c4040c0c03481082a00303d0342000030b60355004c41c0184120b28401045050441d184c8092170318451070b0040028038010340790010010714801285219000074240f4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 732421600 1250 732420350 732420373
    0x309150f0603110301020403020a03060f20040e010f0b0d0c11030f090a0f0b03190f0204080c210d0e120303070507170a171003050138030705100c0f0f05 67
    0x500c00c844c200c1e60f014041c141210f1a641760f20740104495372180c42c543d41c9a940030b101c00100c0c18201c4105003800391401c0d4031503003000d03041c000e8100b050704951700d45481800207000e40b96500c010354962418201000c07070703420905001107a01384e074071181c210b49034440440d242120442030300107440719600170f030f84054803c3d9641b042044c601c2864803824081400400c003007508184056009551540400f0300498008103154801c000c0764003a030b2007800b80e5088030204007071a1900e1100340702c01c0350480100710308091107034a40c1611102414100c00500215550944813616000d82c269441d211403000c2c1d0341c072860444e43c00703006a4481c0740d00319510a0400e6413019138012250a40380035a07030390b640c0c500440308004007071024002c0203441c205d1f501c00c05060003c0019401d0250003045000098a2103940d51100c448044241101c840002005045c00c2c2014503510002000011034808450007041c0355200c5030300395440d484861000d000d000107882d4880501c9500958800e1451141085030040e0001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 732422850 1250 732421600 732421603
    0xf1203110102090a050d030504051302030604140603030919050303131502071409181e011103060d030e010c0c0b130806131403121302010e0d050a02010309150f06031103 74
    0xa54020b40d80c0200d200c9824805e80c103001c8242d00009100c2e09089240545402c000740b80c041d074071441714440307640020801080f07051501541c062100c0b045840d003010700b006c000098a9001f0180d406000d001800c0c5480740059030542c40c00f00074603015040d283e8508040c690200c007204180102d038002500149150302c80c9200203010700441d100c04a0361181500c4000401646800c0603002d0040d89850681000c0c1320780041c07003e01d140724400600340800061010215007500c10601c5001040c0c1d4060081000c0e40c0c80750b4507140c1b901989850002c08482c1c5c2b410060300c17020007117540900075828084000c01e207104000000c200e4141d0040ca0203486a82c1d5030b8880303599000840d0045031400300c1c0e503145400101075404201c803201100041d2400d03d10b01030b403410140e18080b0391400400300003101c0b11040d560440c2c3d4244100030181c0c0c048200c5030598540e950360f1520b0380c034024105580c0d00b00300f0080c06204a040f86d60035481190501001010b1411440138014500060faa886143d014581141ca030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 732424100 1250 732422850 732422857
    0x4060e010f0807031a10022d06040809011710030b0105092e080d030f0b090105210c04180201080709050319020f15071a1312090f1203110102 62
    0x42652840c142e075035041411005420194045803c070131000325a0510f9540d200040440030000da8001c1045040052444441441d0044403140421081c550406200c0e030104101307502c55000b055056640c0c01400040b01d001000c0e0007800071582100c400d0081d0702246200700c5040b2400b5900f1503003a6600c0b001009101c42040e60fa103004d0311500784981a00309600b8031452007400c00621101c201d203541300516400c0803080049040026514252660010b52510600303400b5031041e1001031481d1b04202c0411aa02c504000c2100d080910b000c1324103410804100c0302d006410040d20034007140b171000070741c1e030141c3d00d101004a02141008001031840f501c1240c5800c11200000c004000034500d4240292041e6001c41e82aa0840540701d02c01c2242d8888170510ba400c0c0200c0790085a56002d5401d02500c484040c10f241000a5105002d1107a0000e070400031540994109090074207114036920f042c3c65520b401c2d40150351141c002d06002170100303242d00203480000e000b91140b550304c40100741414202d10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 732425350 1250 732424100 732424127
    0x6040203060f0904170a0e041514150d1d100c090b07080c030c160e06030709020c0c0d03020c01170f0f0417030108031803031c0b04090b09010204060e01 67
    0x42e441800403082c901940f8154100303028040000420303103a8451500c80d0303480340400c0c00c08a48003c0c08500b9a04051082e414a44004242609503a003800140c5045080c051100b9200d401c0c2030a6419520501c4c40840d82c84c20f001e030034108041884400c0500c8403055000b4220f8042c0904c03001c0c011806480c2c05008000360301d503038640e0000e50512504640300d401250040e0380c0c3c20001e00c44a180701000b00010319180c102400102036143c2e40c1081c003227001003203130841010141ea2a050182c2601e0000c2c034401a5204404056120210000c620307290001c2140000c0e442406842c02d1428550007045c2c0080590302a612184440d0104107000c81021060341e08403441c0e150100007421010015248541080c45541d0750b41800d02035440e01921600b013a0021199900b000038103109030304000541c00b2000350140c012b541000203050490101c1c884200c2141c0100343c4640d580001a43c41d68041c0382c0c1c456002259286908005075054000c0d0094010580070541d00340850100c0e6000c2c15140280d00d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 732426600 1250 732425350 732425359
    0xc090203060907050f09120c211507031b0e040b040603081e1b0c0a06110606151306030f05133c0b07300e151303080604020306 56
    0x15100c11030f0454195201c1c4c44143c144842c14044a0810756425280e02060800f003802807141145050801240300121640c1000a40a1088001080d480801c0003a8a82d4100030401d40d26621441d0a401500c1144010700204c508010410042c58210480d1010b00100351010014100300750180401c5640030f00024182c0c1d40248807030564801c0760241c8040700d8007580c03412414424400b000c000381c80010031034503034035801100940360242485140d41c002040d9500c0c00020034503000c5076075034076480060402d60062618154a0074200d000004848080c103c0c1c82070881072680e81d8200400070002c64a10301c507841d044c540481c1081c043c40742405041e6400080314483c490140744070514641c860200000340521b00ca00b50300d07202c0350740c008040c0c015000741500c000b0340c5400c1c1c400070111a030007000310840d0318020780e4a4001000d190315412030792101302c1d00016984103400c40342d850240046c00d92840301210300c041140140c29044501c40d010320988034000c0c4c0713840741c604000c141d000407120150007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 732427850 1250 732426600 732426619
    0x307080c0a170402060d05010f090b06071703040f0c1502070902090f091009050109020703030f0603050706180e01081608060f150609040516020d0203070b0109110409060609030c09020306 82
    0x10a02e403400c110f40c02034401030001e8a802c821803101415100260f02c6083c9881c401b5004200601c040d004601c03401d84122401458009140d0f25111035812141801d1030700e1310080700103000c0240101c0c2c14403065401041400505544041c4492500c00140885005002e032001c0012607130401c4c02942d040700001802070500305801001e101443c0740040c030307011410342c0000000402c0449440f42c5806400010405655440355040c080c0545010300100c100d00d5103030401c00c0000c58000f01e4001c0c16201145454205405034210500d04820b0540111070907002c0c4c07000000d05050006a8805020101401d600300030b0b58911601c2c0e142c0b90104d80c41c5800464800019070000c4810982c00c110b0315008004a00346007034000450111a011100e800300d1040c90401c001c082501040394940702141c610040d81350a8079a903c50b9004d40042c03103240019070300c809042c880c00060600351405090754900c10001c00343e442800414085c000c3c807003520046080b200124549029000f100c0c81841d01030604543e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 732429100 1250 732427850 732427877
    0x70e01020a0b150d1a0109140f0609150a0f05040606050a020a02041508030d1a040c12090201090b0c01090c0b09010e011107180b030d0f081f051003020307080c0a 71
    0x1e02c00904043d0a51094240400000041d10b81040e40941440340380368010b030350704100700e00307007120034a0b16000d151540e201d080040905500c115198084000d545070600c1d13480c0d403c0300d0442110034044003948130030142000f0901e5a0342e01304100031918111018060540d81c3c017000c0d115449009030000058100c0c0c80100c001d030400d40c00c0246440c10101c0c644882d550740d800b04c1401c42c0c0249055520003601c622880501e061024a100b01804080b64200b0507440384000103000d4920040c3c1ca4080c0391384858000081da8096034006008000911055581d0003010940d1402008022411185c0008181000c00c1342d8020000340c401003001a11000140030703150b801074030440f200228195092040b03e002041c40211080401c180324000b00c40480c88000c40020541094204120001003182e03c1c142c0c0075460741d001e51b001e5004074407000011002d11303882c403580030031110540205410104590904014981c558019480380405607a5000242c6955401078158441c102c81e4400144c00310031180c0c0d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 732430350 1250 732429100 732429121
    0xc0d02011421071e141309150807180b03010212070f090e0601090b18100302070606090c0507022205190b010206060102100c03091a040308010f0302061204050c0a0806070e01020a0b 79
    0x505d10014040001d06115050b4010040c022140d0011149140c844800e042c02c0981808801e016002d0040901015809d0200004140d5001c426401040f071f20340380b8029081e202941150000400208a12401e00c2c024101615104d082285500000d290100c00500300042da20924083c0310160b5814803420310741041d20480c1d802070007a8295071880811000100d80c1c03000c07101e520548094401684662481c1003403000c903021680541c0c29281003041072144154000d0865040f90b074111604018910400c1c0800000f81e0b02d119004020361400080c000110403140d1066005480401c0502c41c410104004a07103c940c150f9105000d42e100701c542d0080b200c0709030401809001d8030714000440400d41d4a4404510300a4001072120302c40306424001810380c00061180034214803103206074614038690129030a8440e09000d0400b0f000c21070041010441c05101d982c0f24900005c0205004a8903150300588409054444202044240b4055105035001182e034000f15030300181488000c2da00c111010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 732431600 1250 732430350 732430367
    0x607020d1e03080601030c1b120507062a02011b03021b03070c24020a06111204060605011b0224070b0702030c120702030c0d02011421071e 61
    0x48802010340020301c0d4400120041c0008900c1c0280e03103034400360402c10005400c03030390707941c03146000c00c05120481c1011950344070071000703050350046084c4c9003050213080440b001e0089070001030540b8140000e0f00d0080e40700340c101c880901544451620441700c00300044c3d00701c0351004807012418500003844d5107618000c0e0701818401c0414000f2641e038144500d01982107a003c01021607007591503280521104201900d42000100c40a101202304001c00300040e40e600c08098005207076680b0b80000701507814418042c0c40d40b00a075110300c40e400b03007800e01d40280903000a0050724002003003c010540746204c540c03541c068168004e008803c000c840d900340c00700000e10408400944130401c200e8240041e04283d041407107138640b54003954030b4100c07880d4040c2c00c0000f030801c843d048800500040c07000d66008144000204401c1f00c100900c07001500c0181c904601700042089201400305034400e8a040f1b44070944500c6207498880201e550340c0c1802699441411186620300c80c600c00070300d062482c055081d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 732432850 1250 732431600 732431603
    0x17030108071d1311031e0610030305191205040f021002061308031e04030906032301140409050129180403120f020d06030b07031b0507030507080f21060607020d 70
    0x1d4000910511010915000000140b1b8580c0110100c6101482c1414895036410050781140141304c01d2460704d00401034019451144440030a122403204410b000d0000486d541598000500007407134142400c101e8240d60305010b074050340351120321800207403010500300d100e2040c6072a2002880c1d140d41b0b659a040d0402040c51408404111641d107d000c0c405c8040c606c0755219070364200341c44c0d080100050a03500c000351f6400e03140c49d020161003072403006018001d066502c201180d008804c1c14074005000307006910000f80031035103843c00da0825a00c22104100a4151200007003130440710131000e005110350020a01c16400d0a0400850000b034400e0611030341c1c1a9540c4004160340840d07400100407640003078060459984d440c1410010000d61140c0030350302c507401c4d003401c0154401c60040b580c0704001c1d0784000400c210340001c24008040c062402d5440042d04641d4260300c1d41040300141c0c0d465400031040c00822106c2ca4071500031202c2c110190761050002418080c140040f40d4240a001c9030031100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 732434100 1250 732432850 732432863
    0x71a0c0301170c06031305071a07150b090a45081b0723182e0608010f0b071104020f0a09090c0c05061302010c17030108071d13 56
    0x1d150380b030703513070800514040c80e003912500b446003545260541c03500c42c0581c007280d02d00c0100c2c164615800c015000303a4100a0308041c0c4002e0408001d0f4000d1300511041a90341c0e030000e00740d028440e0084940d40b00811110803c01d1504029038203811040300002010308611404410100604075651034111021040344101c5020b801c0c00c441e14545600340c0580c40c212070301c5074070031101080b01d503005801814440401c1980e510f8040940004070307280e02c00c00b40c1c24080e47c0301c1003804141001c100896824040d145401031002c40c41c10b110500c2c84590f500e100d600c00050500e400400c800b4140d05001044804d03503d003007480c2c00019a03d0a00d814024640d90750320907402c2c051030703668281c05001003280c50300c5642c0b00c1e961542040f000d1022500c400e101c0c1020020080103c20006a00046981d00b1040f6901c8540c469a02c41c40100ca034410414401410346c3d2a68801d030510018550195050f9099a8165456070352034a60700046c260014240d0320300680480b0215003194080042102c20900401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 732435350 1250 732434100 732434113
    0x51e0708070303032306181b0c010b03010e0c0a18060b070302010510090b06160609050a0c0602070911090103020d0906021303061112011802130605071a0c030117 71
    0xd141003070942d034000c0c0c003c00d855060b940c1c540000c8500740801480c2124000e0440e040c020701041d0a640e5a5500003206040c00011420070000110400ca112448903203246d40c442ca01180b0502038070890f03131410b02941c01d0021a004403180424880140c00004e00307003a17510b030324103d909d00b0549090b1442540c11540c4e43d4000c034010f0344100013420454000d800102c0c041c14a4240c01070030b4005607101c0350006150081c120780507940c51040b40e4079442c0081d16540180f4482c18442d00034109041c006040d071180410070b01c00c200000d440b01e01110004c0c0c080d955100d50702e000d600300b51850841c1600200404201c40e04c815806a8050807201c01056070000304ca180780d84d43c0034101d904c0408200c440c00b00941c01082044114005d074408407003007221050420900201084d942103040c081d0f08000c90100c031112000b81c0d01e50381a201d0740e04500300c482c4401a503900b009090b5a0001900741e40240940d0a1503074451021030780300d40034450151036949103038600b00300741c0e80090722000314484500404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 732436600 1250 732435350 732435359
    0xc0b030108150a090f23010b010e01030906020417010c0813030206070819060b04050420070308130b13030305070302070201080f09100510050a0f030312180501090308091603051e07 79
    0x1d2001c80ca24500c50800c160a943e9001b490441e03014241d42000c1180e030422001500e50799028255142a6400b8200424580d49901d0481c020380140e800100c910408110f81f0340202405400440804500d038440e1852034882408001c12107a107408044c001d40d00080104983c28071a04645500c20003450100c40c0c0e1003d240194410386034291b01c101c452030070204040c00186003d110b40000700855800360152000701c0d8a9600207401504006408c0c00741d0900000c3d07000c44050074055000c1e6110414181c61b00c0d000303810b00c980f56003460341038002a00c0e00300000c400c1c9010b8800c481e0365640585a02c01e480c1c1d1000e09003000307000d00415031075560240b480044c5402c0354034000c190040c1c1070518030703e11480c2800c05000050307e142d88194098400b003d010400303c1e03082150440071443c0f400001c149109008007100c2c40690103c07000f001980703000c5801003859841032300c0d9030090b90b040c0700707440c81804c5405440644810500002e80340b500700031014008500103002d4880c00d40141401d50f10130135030b00c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 732437850 1250 732436600 732436613
    0xf010b04051905130c02120c0a14120f071104050127020c0a0c030209071e0309030e0913060f0b1c1a0c04030c080303151311160c0b030108150a09 64
    0x50704030a583c40d880e5a441e58280e50184440287e2800c01015541003143d00002c1a5403010881c2015103e0a240c0c0c4840034480e400b4041c6e200425024221107540c2d08191641c140294040041a10002000d040454203440c043c000c241c102c40700b000c15014058041c03900c2d040c82000c2da80c0e25140707142c2d08010140311071405100304042d40b409106d40030342c0c542c0b45006000d04030000601500c00c01002e00e8401c0c90b2881c1c0c00b141a46500c042d4500080c2081c0d0354681a00c2d4031402c0d500c920fa00000c0c040070491607079901183d41300c8091084a041c004c01800b10340030002c2d116402103143d4040d00c55441717201c40b40307821001c82c40018080e811aa1400320500c581804002007522142d052003000a400e10a02c00701c004000007d025803002140b4500d070081d28060000b8180c0c100a1140c020006800f003034002c96085001b103880e00500195603000b10440500f03220301f801c14101e07940030801c480040c5980c00070060324100da01c280d0281005540986215455800040c943c12290350b45124000124a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 732439100 1250 732437850 732437869
    0x11190309061b1509051002030606071403091915030b010918090204020d1b080105090c0d0905010509012418150f030812090d0e13020c03070c06080f010b04051905 71
    0x140c0f03000245480403420401e040c400b036146100c011a0040051040589440d8100c4002c5038000214002c0c0300b80d03d180c594114030a010030b0340d40c06501410400b050900e8041558204c0c2c6100a000c203a4141e8803a0503016120000b20b41070210340c8031681048840320340440c514000481c4c00001554008681c0001c040740c0001c5c4a40c0365041d40c60000740510100c40d00300209a0519003040c640719890030000034152030000300369180b40d1030007107010740300480107400c21624241d01038004c0c0714514211024074005d0413001d00240c0c0d8540b080d079501003000120542c0d803040c0e489090107840c26000917884040900030000004000000c2d00c00f000401410702c03e0403001841c8101c03001a680c0f60780c0501003100e500e01900c142e025800a1800c100c0c2c05400081d4000b9004c0144c4820320415040a00e1400901804c0c4180025010004e14507003000704c20704460050320900d440c2d03402540c60300f580450900d0024040d0b43d5409104000a0103d49003080700400d1660708642c44100d11034843c2c010428044 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 732440350 1250 732439100 732439133
    0x801020d05100509010317090f0303031f09021c02090d0807030e01180e040303050403050d0606020606030d050c100b040f090b0a0605040c020d030f0e03030711190309061b 75
    0x196224240b084441040c4203410007030200b101c00007110f50440e1100f0056941d5418160703609100020085c040b501c48040c0704128100c010141c035200d191007141540c09540c4c03021403511003540c85202184c90400ca06c02d4135403c0869491446800a01c402494020f5200b0101381d0f50180c1c2828540001405c010000d1090610981d1416215980040090103a07001c03000c601400f20902d40f800e01070003010b810300d1503003c1d0f018540400c041d00d4604040e2403500c5038003c0307105c10302e00300440400c0701500050698002c510503000c0700c03451048901d00300c401e03003d4400c44403407c1d00300130600382405115030002041d161b0001c00024500240c41044000c8400d104001c0300c0314100750081001450311845048024403045d203040c040603140f40d000035203d512840d08001890303500c0c04126844c01280c0e02440f028916101101c0e6641000400a0450003148070aa01c59104050f91411040c041c0c800c00c00109506440e451040e03400c150083d103264a5055606e00c00d009426041004039400c000e044402d076 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 732441600 1250 732440350 732440377
    0x8070503120105030a030e0418082b090c0302010f0908031c0e0c28050d08070b090106080a080f0c1e01060911040b1c1e0b100c03050a0306080102 64
    0x1c6a14160a40c00c401d4140d105500c20b8000d540c032500420b8202c2e001c10740400e01241e0010b0000703846050712103a10403500c00545040c81c003203200781d02c0e45035100d203444c000704182a940e1103180b038030012082921129607004101d058044000c10040d4000c0102e802d074181203060051002ba1212030700e9145410090110850048100981c0e03c1140b481c80f41c1d1440c100c0d9007014041101c00000070414110b1760741404403450400360410442540d00360610009041c0c001d009001c52007060408602c9034102c04815a069001c0001040c12034038144194012075071614040e104442c101c2d15100b082e0740168400c00154001003290410701d14043c0810f94148501d00c1c00106c2c1008500e09c014212402500502c41061400b081d150416514200b40e41c1100da403244410b540726031810310200d802100007420800ca03401c00700142a40501c80780e40404410102c0020898104c180007040004640c0c1c1e207600c0042281c1f0a5040b010a1149005005500711030801080c45959181030300d00b242d00c10f010381c0800c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 732442850 1250 732441600 732441607
    0xc04200705011b0206100501080a09060203090102041a0a0804080904090501050414010507020705010e0f010c1a0906150d020d02120a140d030b01170a06090204120b010501030e0a140a08070503 84
    0x1032074640d882c0041202591008005c2c5103401c22481c620318003035005203418048040c0002d881e01d022038000440032588420290740340d041c442c4105010b508103001e02c40345040a42040041941240295800441241d682e041951034949034405994088a0746a0b0415110302604004c0b0b43d0034001c060145100d100f8000001480c2c14215007112409413242046400c103032020031043e81c0c800403c44040100f11848400c00c2c101c0801030321240003000d0700602d0800c02c00d4031003004865081c0e04520608128040d626640c2c0e0718141c00320720f540e1b100c0045038040715100d0313501c000d4200112068009880a4100b00203080001a1285001e0345220110340c0051000c1c842d44204900303100000000003907050505c4420b020000203402c008036607450380741c041036003000510300010a4002c14010030034030b54110364544d150f60340d5101c880420b2400713903210544800001055403182c0b00c0d07500e80c801d4000103040c10100a40e144e040e411424100322246224609981011503042c0c801014110300c07846c0115034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 732444100 1250 732442850 732442871
    0x7120c08042301110706080630010b101205090a0b090d020c1008060603090c0a06090801050609240a0302040c0306030212060f072d03020a09090902030c0420070501 72
    0x84441c01c82c0e6890341041800100030a01030300025401c802d640540c100404141d8075200820100c1024030040680440140d850202d09400c5d240d150358600f01c200002d021003401c0e0f10030b10a1008440100c40c0001d00b044000c80395200440d800780344c00810490035240141100c1c0c4510403080783c20b03201620f480d084040b1380d0844640400c01c10016207000e40d8040c0c0c008811110203483e24000070107090181070004001a1985010b1000c100801c400918980c0340d241c81d107100618110460051082c10340c0381c40701084091401c241c415108203110014a207201c3d01a8100d0020425408440c94000c60480c10200040e0396900074514842070030303540010441c0c55801049a007100b151210802a0003810900c0a07101c441d600301580070f5800c3c140702c0c240c0e0606110100b89039440885144251320207041c02e6000c2541a001081c0c07041c2e407640c91200a0342c554001030200c0320a108001d61540c4040c80f103007068102a000b01d9204005c80c403054064840d4102a2003440d8015041120281d645494280 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 732445350 1250 732444100 732444149
    0x50a05031b0c0607060b01020a0b090307150e0a021507230c060a020307120903240b0a080c04050a090209090d02010f0e06040611090a030510110a020307120c0804 71
    0x25034115075400140007442c039000200d20248078818010b4440c5459503128015640208506400ea9602c100d0b25400307494a040001d840707401100040711588440100188030015a018405203000d40e40060071024066500f0880c1000001c070707496100d000240544400b08000604051244004640004265800e00d05103424180c001d4480ca01c101014451ba00c642c0e0740c0041500e44803907010640241d5048944001e443d0034065078002402814520300b90040f5200c1190701200203584410f06002d040c111400700b00315600c0d1800368030741941c0f040491401074901904140d07002244d079800001d508020350040303082d030641103030340800079032240030b00040040e07091042282480b1000402c1140905441c4e21544440000d480546080d860b42540b183c1202c3d901c0840b0320116000b003160090030703640d241441d03d8002c1c00c004072008519140604040f141d100c0c0403107580041c10f40c0910700d04025951b030414418035903a140c03020800300c12160070004110300d008102411500514200180b82d100000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 732446600 1250 732445350 732445387
    0x30d0507030503010e09030d09061406030f030a3912030c0801330207062304060809160303030905010f1109100e0306010f05120307030801060503090a050a0503 70
    0x100801504001803030100381d101c02a64107440880c001030100303484900d0030f41d140d0f0240f4150b803140d851401c60319408001141d44811410041a000409265680030030591a0808aa400c07a8190000c00072100607500c100305e40300c1c9440a4400300e28130a5a1001404121300c00e0314004040e000c0c44807036001c140308422000d1042d81c00c2034a800d21101100c07610040c0b480c0c00610407181e070b92800036683d2002d19001c968090b11080c200e40d90041c0244203420083d960011403088002091140402c2c3e40e401c518806140903244031040007920b4246410421107210400030320100b22030041408582e14248407240b1600198001e5401184145c00d90a00a086691103002e0302c03512450821200a8100a01c0650310407100c11a140d031100d03e031441003943e14140c0300000308d60500854002240c01200c0341018015a60283c442c299030701842c440e9142c2d42d210352000500414001d10041102501c81c000859221000806555408045036982460444140c40c1184c1c55000455040d2010400381d140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 732447850 1250 732446600 732446623
    0x170609060c09010212160501090308150402040311310c110307230c06070803040314030c180a081f0b04020a090311011107060305040203241915060306030203 69
    0x11a45804040341c000b0b035541901740c01085121700c020517054200000d5240c00401c240d0048028040c0211901d001820300d14211010016103982c2a5101c4080c10b2a10a80b0b094036480941581c00c0b901d81c8080159810543d030101c08000000c40000501c20001011f07400c0c1d03044141404921036001000c041d003030701031040034402951b07c1404400e005c21080d0032041960b40220f90300c5414504001c50090510042c4080c181c1c000800003403c004001001c0000d5102d80c0c0640da8007501c514119000030a42d21050300c0c0b80d000c40ca42070114929281c016101000e044500424009125a650229070300300420075501c1111703000880d00c21986a030751801001544402206d003149069075006025220743d0480c00054400180300340e079180079034080c042c01c075003044840e0202c4a0840c0d607550010041c10b02220700300c0c041c1c041ca00043d140201072040780803441003074001c542c1d1155140c2c651480c0504800311219941074a400f10034042000440b0048040c0c20103681c04512141140107151910440501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 732449100 1250 732447850 732447871
    0x306010e1023040f0f050f060703080f130209510406080f0601230d02010c02010314090d08061516080c030d09031d01090b0c0717060906 60
    0x710191040d84010003070529a220490341020880400c0040e08500583c2c0201c1e40c0364105150205000c00455008011a4021030301c02c050400208107100c503030300803c1e1004000c50001004611040344041c4030325440304400e04201c084030025000580859800e03035048034041d0706502c441400400c400003400f01c904100820644118918084110340ca40c002c2e0904440c1914000421950740c2d5a0089001454030a0840303a80030701807916580c03620700070700c00d0035181d60200c0301e10202100b848504010f5480000c04260602c00250010345595014200c00ca0400d960703515030701440d0f4081e504281c001d10f0450018070014444100140031524041e000074814001c41d001e80d82c0070410748044941d80960054401083c6000740b034070031080d0042e1030750045c0ca800041010903074030180391b100640c418042d64800e40c10010807a00e064900c0046c800090000701558401c0c003044886d0002051050054000c039115156500b08043d9050421515101180c02c141b007440400380080291036082030743c03c40c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 732450350 1250 732449100 732449119
    0xc09020408070312020c0307090509011d12090a0f0602030a0206100b0a03050601020a0605042f0904020d0203070f140f01050901090603050c1606020405011e09030231150603141302061306050306010e 87
    0x1d001c0e40c0e981c800c040d3b203030b00c01040014a5155500d50b00100d000030480c1201c80001613072100700281d1a5044100341c1c1005110300c07800608500e23107400e82c113400c80d108003421514001000e00110081c1100901e2181507202e00a0040c0024906100d01c9102d540113003440c582c000b140091101401f01407241445500c4c1d003c03200ca404070365500351403d0b0450360441d00c0c0d0540c0d18032403010a041c001a50f000e00d054078005000062030882c02451030300802000c039004000714a070540103440c2800b504284600080d0104020321209000740d000740e422004c0001910304241102241d0340740c090100c070f0101e80164020604200d00e503042206036150b00e409007044c0b52107403205007004185150500c000ba2181c206481e9424004810394149034801e041582000030402d510b0740210003600d03107505c40c80002c4400d01000120b1512074815070f2031030404034002503560307212034804241d030082809041e07900c075408100f001c500348503106e032860040c00e40341c40d41902c9240005c005030800e40d84e51583c1d8010711850 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 732451600 1250 732450350 732450401
    0x12010b01140705070803071103010501060807020a03120b1903060b04051902070201051209150f2206152c0c04121407120c09020408070312020c030709050901 69
    0x42050001d01000400d959181d00a40c20114542010b81d8010391460000107207920600590b208580e202c000294024445a60ba4190894424030704030303058030040c6c00c0035440000080c899611500110003402000c01c0c410001e0002401c520803000700642041c42d04402041041801d02440c2c548100485041000d45407115000141c2d40e94007966000c280c1c8d000840c3c0c42160302840c103450b1b001c20507256200b000d15104130342c2942c80031040c41340e400d590700690009400e401020f59180c4608894084c0840c0c081152030010b00c1c10814840803508180c441c80c440c4114018010098000c244241c1c10745001102c51040055aa0310b8106e80041103060030100324008010340704542c216891005044000302c9141804140c80c1407018650340140034040000031014940303c2042e0810340130300c804ca4000d0742e035801d10000b280308074450845190401c5a00300041001401c1030301110095006440980380054002800e20640703170808070f103032a07031070741030008032042481070640e03a40380019400c0c00110032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 732452850 1250 732451600 732451607
    0x20c03070b0406060b1305031504120311090907081602010c022a04110307030b4e0703030e040507020c0f1309050a1209031106251112010b01 62
    0xe03400090064200100071808018440d48501d00800c0b00d01d10194517111740130b0181094900510505100e03100e007200d000c1d542081100748a00580d030001f40004000d4002c80207501814200c3c0040400c0502804079051a4890041903841801c0c3d503076800d004e903d407800298a0403003082005104681c5003410f4842201e07000951406140100c41044035a2032042c211940122510b114051f0058100502d48210012000c0518000e051036201800a0201d07007040c80444041404c0b0b03100404860ba036640310000b10582c1516500e054410424103c450007481c0c207010000d048030001c0548c1c0720070402c20a00d503010740704104140003101c0c14081403e100e04000c1d03640001d4090940700c1c11407a0003100c1d0301d6444581200c0c180c804c0d01002d00115180d03045c601e4884030b03688800c0e980409403641c0501003510480400c001d90350702c00600403042c400d0b14144201c076001440e03040705071541c0202c400c06048107610044801c51140c4000e0302921321400610440e20b1005481008036814414410b503a41c3e007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 732454100 1250 732452850 732452857
    0x20a051230040320150106020d300213031202064501060f030c0906121515140312040803070321051e010e0408070209070c02060f07060b0301020c03 65
    0x20949083c0100540e44004c10b141d01407214401d448500c18101d2140d08501c5d0100c81070f041752416020b450504070652000e88000a030641d001d149540c1c105101c2c03114a20b403000500190300215001401c080702035542240440058105450701a98152440e443d2541084115440b103128032030030b000c42000382e1201012000e0710031140b103802c00700d030303002d030502036030b581048282c2c620160082c0710640c0e45518859121000b80030554010724075802c00314083c10140941d00031a8544605242a5840c48d194000c0200220801c1040c2c191120406000c1003441c3c1001c4001e403110b101c400c2d40540040341054504407141c2c02110900744c051204021070344d00482540c070900e0b00340c00c00e4030403980c21488042d00b1140000c0c02c02c5120b4070348030a0002940c9054825901e10014206603513003a41ca400c80d120008500329401040c2c5602041140b0060400c0540749802808a007440c0541a1b031542c0081e1864120140f14000d0620210304001400000d004594400b04298001c5140c4010f002c00641c6034030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 732455350 1250 732454100 732454103
    0x130e06011b0209070e090106030f0518030a0c0807020a0e220308070c0302070e101a0906040506090f0a060e01090f080706080c1611150a12050601020a05123004 70
    0x40d00c3d100002c2c04240184000384c10075400401d07415403076850350700290040103074582c481042d40c41d21000400c40030b1150112500446e0400c01141412104002207036501c0c01004121019039090001c000103844114455002c3d00310100c054040386080d00c0c1d80031701060048081505400d0f01070000d00405e0304003030315076040b4460f0f280030030030b4a2160034240e26005840d0f1001c501c41d0140001c1054035519078406c40140d640700c00d02d9000e0714600d0080120721340258a510b1790301580402c800c10241c034040000301040003014000810500b404030008003a40e103d43c1c490001b282001041c1c180039a8000c0c20100504600d025801d152820601004d984003410700514061100140129003c81c2c001015111103e0281c00c04e880346103000d1a105074581d043c81800d90141c90050109480301080f501584c2000c0c00a55404030210654801c29010340340c05051a41503000c0c07200d01c50b000c210f003484003e0004540710019a540c0c0c0780480100d04240f9004c0c80e80314a261100c00304640030a40100c6a900a03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 732456600 1250 732455350 732455359
    0x270c210109050c09100509030c0315070807051e03060a031a070e03030a051e070b0118060906050108060d150908190311160204060f23040b06070f050a0206130e06011b02 74
    0x5640e02030201c0c1c61300021520140d0b25206442f514600040240009440343c0c0c010754443c0365030b07120101e080e9407500815048083d10261f95064154070b08044d4051070340714100410008405a0305e03150b800012001d03113a0308880c0110300d002c01c00100d4018020020703240c3d00790021449e2a42252004005000c2d000e03910721480d6111103c400d121107540240c4100e43c3c0c121100741700b01e5071b5404001d0b46030b100421000200605203031002034001e4040c403800b01100c41c10b84510311705075241c004022500380c2c40300d411100c400c182c0813483c550a031644984e50882d842410003d9584000000010744118000705130300c205401c100000041c0403000013660704028142503420707403035656440001d02500c066080109a1307140071900090340070a29a64146041c07019150340c02c0701400c0300920064807041e140c3c0c10b4100c0410020040082c4200c1c40d00000e071800b40080e1400c14801b540012032903807000010804002224009000c0390300b000720f4141e0001000d090812007414003900282c0d0602c2440e0000e4442c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 732457850 1250 732456600 732456607
    0xc032f09040902041b02071a03010e070806011e1d04050903040e04050102160809010e010309080f0c2b020d0f0e0907020a060c02010e010605270c210109050c091005 72
    0x1c41d2501d070010b085d440802c84040341c8905602070000d40e664414414240a001c0d92902d002c1001108011603040ea00d205402091503a02c620041d540b101000c0c00490402c086041da44180414410300240030b58107540e00c0301480a07032070040c850040162006544075174540420301c04001c800000b01c40c2204c1c5000100850f60f5a1401e0490080c004c0e454034028100e01c4001080410030b401c402485c1d080d20036290018013101407030044081b2141e107000100f9200301000b17650074204142014144080c0c42c02d0840d075180010041300c0c412402d2002050220201c444400c604803601400300310103500042c5040c01c82094000d100500c081260302d4002d0140c1c2818011030381c2140300b40a900503945d000030080c0050400e85078024000d095103d1302c01e00c13130b503c1c2142c08a8035103040d58201d6110f21017008818803e840000313480d9000000a020112008010420240490030303181d0708082501c0300e10300d4400782e90b14000c620002d4600007450705070480e03000c015101c5280d48208c17181590780c0c01458840c1c2c9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 732459100 1250 732457850 732457853
    0x21612020a031707200f01030e07120f141c14070f0b011a1c02030a0e12070b0a0e100b031011190804020d240c032f090409 54
    0x400742500d400c080c1c081c010341415542c150242800030b103080ba11451854a04040030350f848160096840b43c429448040c0c000c02d6541503101c0d40202d41e48040c04002c1e00c0300e42e60703241c000d40318800746090111110007a83e00c011061000d20b603090543d8068040c00b400c0341010007060640903442c0120f07501e0a118562602c1e064040b182000c0c1c0b1318440d0700100c4c0388202103150400442e11349003480380c17515810b40465814509412a415128911080584c08a0b841583c1c0308000103904020018040203aa540300b40d41000ea0802050003072003001c0b40c1260707440115041100349aa8018a40103519092041d070384501e890010b01c0202d2043c18440008102c0d4618002a060581c9001c88141060400c5003011070003240c04010b01100808140004040d45208030559241d40f04035000f0b0b42c0580041d40040200d400d95010081c2d0b900e0842d00f41c4107a418a01855089801c901130300c0b000a5500c0055442c48801800e105031840d858a410802034880504a08100d00c204000170f800ba644400c038440 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 732460350 1250 732459100 732459109
    0xd0b04080705071d09070f0b12130206030106080403030c080714070c051f1d061c060e15091b0d0b040207051203062b02040c0512070306080d02161202 66
    0x40107041c90403070600c00098121854031142e1000d0795170040b2406200000588103c6001000007191030b20b0556a0030403034462110040100000c0a8460030540c14021100598982c802140a01444c1d02d60081d1800d00c0e081c01000c454039070001000344500b400034040c069400560004100d9501e50025075103900900d0441c1405200740e200325040805000803840e180c481c403003119803441141e511030300c00001144601e0101c03000a0b400035003003030003048a4143c441c0b428542c0b10030b00019110103d05955110500d400040c4115030703032114031a0540034084649001b8680f150840034910000200c80f110410039002e600c1f0b410004c0074416901c103c0d6980e00c0d211a0140e07058246c00006990745030400c4000c03514a64002c44406110710f061030380c0303004031564101c0d1400b980501c00c0c41036910000e899080c000100079144c01e2030184a01801903003510640c11581c1c0340b04520554020070102d141c11201d5141500b448102c9041d50091002da006907240c5a0748901102c0b1400891440030500d0300214 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 732461600 1250 732460350 732460363
    0x11061003061a040903080105180f160504080d1d0306161d15030103060b03060106020c0103021309020d0b09070219110d0b01060806310b01030f180605060d0b04080705 73
    0x200c0d0064200b0280711305064001d44858100c6406030b9074070358610101030203024100f8080b14215a03420b0b16a01151001c01101501805a84c803810720034607060312040014038050203103402c84000303483c0381200120211b04800742610745406070002c10007803d290a00e1480700060000c16030800c090001010301c1d6204004043c0700c280d6002e04200d0f01e0720401075040c6055842400240d8075641030034a00030f15410001895070403125a5030103400394204d808011000381d1f008510607242d51800c10300204820606100800e40104014030000c2c16003249018040014030080c0181c5c20741d080b400e2602e42d00e2092624121540303600050528502504400140045071104c03005400301010070f001141007500404a00c1c002c00c01203c3c01941f00203c10007104a00d8040001300403140c00c1500440d0141a06400080900405050210300a43c4644407101100c01c00701202c0c240c00d0803286d0a00501c20705104407a009081a00c1110100d1810740313a25412642c084c00040c494000020f2b0881444800d0101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 732462850 1250 732461600 732461651
    0x5070506041706010509040201090306111c0c0801060509060f030603010207060504120e101d0a23040f020702090415020c010c030515030106060f051c0612031106100306 74
    0x14603129512070103403401490000d418482e80c2e00c903560001c501813420001c410302c00e55059490852850850755008080e29091200b0b4142c424144400040d000a0107800401d0495036540058001e83c00030005004413010392000045c058200032406442d124102160031100144d003c15540c2c0c1c899801090081c4200031024004a00d46003c3c042000306002d0003002c80c0ca07181e40c8040301380e50712104110140751034081000c0800d8601424201d880e003030380c40d00b81c1e02860041010303460302d0307607043e00d40045e9829411110900d180c501b041e40d524a41880b0312000b03114034841c11400c0c110700b640420313132101000d0f0004e007a64551100e420701c9800707039404491580c4000e01c000c0c00b961000410150251500395003a082c0b03480c2c1c6020f032000341c1c10144503000c120388550791080300303001002c003081c0d6141d0700409404418164035403120104141c1c50040344000c02c40400505580d01043c21700800c0441d0f031641c1d40c40190441d8040c40300c0c200c01c0388004400d80342c00140c000f030354080e49880405041c0d43c1c41c84 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 732464100 1250 732462850 732462859
    0x906051603090e040c0503070f080a0f06140f070201140c04120507231002010c090302190314030306010306050607030f080a091a040201020c010c1707170d02040303030b0d0b13050705 80
    0x1080300b045010312445d0125003040d0201c40c01a902c40404859070780d45400b40c81d0b040e52200c1c2400012550710013444255a02900e40041c400132061401c851240c812586420412158814406110b609114562156010408448032418400c03880900c51103188101801c4100b00c203454400d100052001d10002e1425480c14041c1c40002032881c0344c0c21141d8000c1c6842480000c1b401d601c424010301500e107000d240c45c0e4940f6840b506660070402c0540c8548150309017100481e002000180c03060200c0c8207400303a04401591207241c204001000d891858010b01c0c0106010321800000940001e981a110592420288055501e91054600030300014201a101c08564030703002543d010482c1d09240201d00070b81c00d076a5200c42510040d54441c00d4031100420240702003044259440c07400300030b004000d2107070745001d41800d036400c20b200c00740d001004441e01d5168002410800c050b094070030001110340640d80f80448900c01d8481c5500d5000040408121200e610707898000c20000740255005000000d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 732465350 1250 732464100 732464129
    0xf0b04120501060f06030b1804020f0409030323090106140105030f0a0f0603080d060b030907031410092409030f120b09070c02010e06042402030c1c020607090605160309 74
    0x170001405000c800b0980360103079013001009074040300454003081c4180e030060083c0000000d41000d000c000c1410b03203010b43c00c06a66148220a00564240184580c42c1d1184128002d0804c44036042c2100e0b160740c00840ea900049110b1090760342c11134242c82c1c0c404010080142590390340500d800140801022a1604c40d150000200401c0302c504007034003154003400c20400c505511030044940d140700654003c0011ba01421081000900300c032150710444071004251584419a04001000d075a03461074126014602c202c61800384404191405210400d000e01c207225550080d180a400c82821942c8003042142c002c0080c010103003203411031070324013074013338075002d07561810900c01001007170300100803070002d10101007104052500800380c90035a41c26090320040151062910302d141c6140e02c0c5003906502040c003250540c5c0700140414088010005052000143d80c3c0d90000e040080c0108000c003404080b220034052164000252000300306c603115000300b85010b60a0a071442030003a44003010049010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 732466600 1250 732465350 732465359
    0x80601030f0308070c05031b032101080d0302130509060102031902010e0c01020c0f060a111c260411210a0515150f0d06051f0f0b04120501060f 63
    0x3150746049180c080d40e03502c500354489040889546a4011015280740d0081c0405224203020904100c40c3c83c2c103001c00c40f0700d891080811a0310388032030080b0f0f030184042d1110041000c0c040030300a15203c230a041c1b408510302104848a0303000b50301103005182c010124000020b036141d0007001164032111082454185a42ea081c1e8028080e00c0c0ca0fa10303058050003540c521049950000078402c0e11814000e105030b119010005c24801150041603200b001c0104c4421201400e40080c02148144c0c0c0085160429031035044001030f06180c8411144290f503455403404070040b101e0702d0111504968000c40000310724210f800041c4542d40105803c5410744807400030341c1c18000e40041c03d440703034902c41c0050751403c1403c071034014035001d000c44940d10711501030a01d01e1080d02d401144403030b901d0380040101601c0301c86e907143c9034100c2d40c04a80d1921200505403004035803800e0610741200030649011034000c02414011945c2c0304c2d00aa2040c02800306001044504000d02900203401600c41d282c52092480d0741c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 732467850 1250 732466600 732466613
    0x31401060302031608100c090f0602070e010e240609280b0a020718060b0f0304111002030d020921100e0c0a23090c0702090a05070e130608060103 64
    0x2511080b442441408104d142404209010200304c5d06800b000d4152071615070a032902030600b0242030020002c264402241800340c0032100c03005800a07500411455080210291180d54180c111045001d50310302001420301158080012010003103400700e0036040c901d000300390980220490654018036542d42170102d81129200b44140304541103a15a0031561500a6030705441002e58400c010382002901f80b00180030050300c030046c2c01180a0020701142d41c0e0f80f0b420500e81010f20711a0a03130000001344000d006000c1882000c554048920424103169090003a50343d01c0344680007034204e5000f041007145592201514100e8103c070300e00c0302c00c000e400000359644410750b004008524524082c0240c0008600141003290704901170316050b074047c1041030481004403042c28005030004c850301d444c080c030344136440c0d0035002c7d080e00c203107560b214030b8548100108170382c00824494071a460001081062544085007089410040c0c402e030f80790042c1400f8a07805003416400c0000940304401c0000104182e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 732469100 1250 732467850 732467861
    0xe0c04050f0f15090405130224041508070206060307080c0f0f1c050f0a020d080306040e1605040e1209040216062901020f0a0b0c0d050103060f0b0105040e0f060a031401 74
    0x803c41701002207950300d810744403407100d0250020390046140ca400b40c038052001801148010348074a040350400d55104907104240940710b8240000961010070f000c1444c0c0c040104c55040b00741140a451030a04298506a558000925051003482e17071401508054a9034582e42d80010009071012904540741440c2c1642c0c1069183c0841d142d1141c1088250105070108080050560003001609070078881d880e40c6649030400741226502c9035484101e803100d4601005141d00c504a150310402c00c05150500b000111640c0c0303091451940c0040309090180070030682103415911040b500140c6515842003640032101d4070200003401207240045041e40e40500e11344103d0b81c072240d200c17402d40760881c41004985a203110ba0030707007040d64000c10203940090344c4462181c0d400511880041d0420312104100000c0e0b50003030b0300c00d480031651020540c00c00e4a05020314134101100b0308000d8030341450304d6042c010613040104081d4ad02c04425010800c0d40c0e071034601c1c0700010b540155081182190b110a039a00804 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 732470350 1250 732469100 732469117
    0x3061b0c250b0f0d0504080c19030801060302120a020706140f040c0f120f0204020d150905010b030105100e010210052805190f060803070b010303090e0c04050f0f15 72
    0x34100300380068291100b004681010310280141030500b500a21500040d000250084600c40c10a210041541d00c0811100001c460260741442200e40079050140ca4004180c000404150041282090400300b03400000d40009840d02c005a4410342414000f00800d20580788040340032401c001e00410200c1c80da03034640030b240200e1104004030365454412031002d405206682142032400450004120507482c000015800540b000d4581402d05120004540719000000f102c801c0d070f241e00744002c1d2050300c00d107400b405000428524650401e80007818003180808401c080290301c200d000ca0591003480f81005130300109600b44004e04011480041c9450043d411815480f0502111000c10110340034030341c01081074100900440e850441e445020f0040c2182a01080d43c484100207101d010800c010720f0040d0040826001d00d50561034000d028055950140b01a070030f00c41d092120251580044804498040b1240d40498050703001159000c0001805240e2000f040c110604221066400411106 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 732471600 1250 732470350 732470413
    0x6040b0630010e1006020a02010e060307090902040b120906041e05011506050913050403050301121e110a0e1012210e03010f05040807060c1e05041d0603061b0c 70
    0x858403417204a0303807420601e50180c0000d400260742a070300d00f000e030001c5420504074603004a1094884102a041e03900507404a48a42c10002c2c0750f843c10300301100f59617080414034002d09001e050544400c0701d0100d454681c0300d40c000c0c3d14102c510412100754040d000b03054528080004c580c0c1c2e40c0d10060902d422103020103000b841410200e142c811a20712456106581c5274403924103607400d2255130310b846d1403001030850b00291110285004000b51601551505110b00798182112004100f4064000f0540d4401345d118034420050015020041100300265481032081d0b40d101c6004d0b0a00448032100b41e030182c500c01061092031564140c3c045594250b5440c1030b8000c4c03005400c1c003080d0100311030045a010701141024400c1c01c00140c01c2c0c1e084034022104614101c0740f80341c551040c00c000844032080314001300e000082d041140e01c03903203050a4801c030082162403105140c001e020035210100200480c10740155500c000e0f00212240c0151b030307188a0744400300c0e42c0285601c100490f2001c0d9141511082d17 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 732472850 1250 732471600 732471631
    0xf191b020318151b15101701090b0c0f0c01020f0409061205030414040212040b0403021b01080c0c01151d10030b0703050423030301080f06091b030c090a09030806040b0630010e 77
    0x1c80c905002740b82907140c4c000b403101034603074074401c202181742c000140a81001c0c004218207001e0311000d0002e4100010740d00406942c1d145401c014004a6013a0351228117940d14070f40741d034004900044181d400b1546180c10b80b00c000d40a40c000940248158003290024020500c1030109020300c0340761183c8038070300c40e03000c55480100c7c0c05418442243c840224900150a100000303985900c0100600003002401c400030130310001400751601b07821441c0d001001e4269545112000c8590200501c075007020390300c80b80468550440d01c038808a0f03c0c006041d20180f607101c902090801c00c042c01e1400042800e50018540303a401c105c0c449841c1d52080c411141c640c800c00c072596603030031000b1600c82d001e2503069004100302c2d0f01500c80380140184210889906004403405000c868440000213440703400c5a00d00050f28bc0428940903148a00c0500320602540c540550180c1d25207400c0212900789405414204d206418034054a40c5840404240311204828100010314000f060b04414001d560301030040d0b12 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 732474100 1250 732472850 732472889
    0x180b011106150114040306020f07030e0d120804020d08040902070303061d0415140705040603050f04030806190503100c170f191b020318151b1510 64
    0x680315020745814941ea2400042c10540f0760060710300d0680c450700d25180c01d0038140d603601c450007282c202e200310043c000c600080000805a12203143d40d6a088111145512424141c03502e04000c41c04241410502030081c000c0b41c2955503507140306110950201c40541e403540c8402405000e90442c000c21804603042000c04550041220012040000002c003100b405669a03141c180c40600b030381c2c140701030669480c80354040045516000b60710582c450344605a9a42c81d0110090840d0b500800241c0c00f458401c0500c0b0000354000641c68003d0021148820303040f8510341003080c643e407507510681e4103200b040d2006603a075880da0000c09922070261100c80802e280c813010694800421a0030b0000100c0c0d03100012521082014a140010f036000c10005203a8448401c040e529404001c1d4017002d80d00104201303030748040181d2001c00b501c00944140c00180c00d0307215605158082c40d01c482d24822002607401110703081c200140d11501c44090203810b135030700f0602101810b04503a4000d402025003a8544001c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 732475350 1250 732474100 732474103
    0x30c1b1206011406071a0c090901091506031e0f05010e061e0d1a0f150d03020a080322060209100e0303190e030109060b09100e150109180b0111 63
    0xb03040320741181c01d4240034509003040242642c000002199000c420a001c0c5562100c0584040d04c1500401c45940d581c0450004004003120140d1051010301e00309171246608425101c05602103e0050601040d4015118000c800c0240340e801d12032002d504d0001d007200d1459454100034101c1c0ea21006c402516143c1c2c5007401040b40042c1d49c0002c1a020780880040141003140321004a01d0141e032030108188600c0d00ca50a694506031030010788000542d00b84051a061a01c99464a02c2c04a0304250304a0140c2d80107504d0300d00c145005001c0d040b010000400c1103070706c800c04604496151550606203402071034140020f4001e000070a004030126103003c2002070080340c14072660b00005000718103106280754202e072001a42c0e49483d0400030701400102c000d0300c0034000e0603480c034807526000c180001460b052203061100146086000d454602041107503064400007550080161100402c600c0e60490040e90040c545e0b80c0301960450711212010804002c1b940040e502c43ca09a9403624840d01d40080a03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 732476600 1250 732475350 732475363
    0x140f04090c0915110313080a030806010e0a0513022203060e060601090506070c08030c010603060e0705150307140d0e010528090f140f0d020109051e030c1b12 69
    0x28603450001a1010f015018010049100e40c1d00400c0742d282c0711140c0b10003030305055079a01903003240d030011007010101600940301c0c030340c058001e00c1c0084c15079210780001a0704201c1c0f4811240a0542c034406550020340e541c044800c2e605120458060305440c10a0380d50a01142e0321080d0754980c90818020148600405c011303003e601305960b4030380d205040c4802c1250315480420200d40020380e40c5400601d0260920140c51002c03031042c0005800c51460414030151008510f000c9c5140c0c104110034003042d524031010009403400d4500560322a41ca2603002c2e294050107064003140043c0200b002c1a10091f1600f0501107195100000d100d6030312100342c40c00a0400f6600118010144448115112803040e40000c40460045900c2c1140380020f032191340c081c048501d00344034603400103c00104400340411a074414010355100030031511440b40ca541c0e468840e070480160b41041030040504041b0410000d5034400f40c0c030103082d03072404010802485d141420501000e401180905400d410f2401c002c20304 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 732477850 1250 732476600 732476609
    0x3060f0106050d0b0402070203120913020408030a03050916030b0a0c05031b03090304031a160212030a1a0402030708070207120f02090a200418050103050d0807140f04090c09 76
    0x7078505180140722901e000d40604138040f41c015900740018005640c04110041c9030b03800e080761140da0b6072540c05c2888805498005c0e01113485004200c03c0100740d800004031303520a0722070706e00000c543d12908a0641001441d1405c030360500b80c2d505c40803052141c6c490344180907285c0d030241000b0a00302c0c80b10665a0b0700003203e10080c2d001c0f010200304040c1b84071a00456004003c1c03000d4034038058070f83d90b80780c03c119440740c00c0d02000620038007000b190983d078824146039000c640c00200280142c010b40840248001800d000c0d03030700d4641d0540440c0c003060459403280444010402d5480c0e10f03110381d00070400300c82100c0e100b0062051742c80c005100490745441c01e044e140c00c59071401e41103000381c003804600c04e0043c092105d002c1e61482107903202c111805180c042d00d541c00c250b25a03107528001503040700c03c402407005208549428010800240006107040440360642020151640c44040541300a1043c01074000b00401c0003512109a03045070000340160340c02e00703c08000b900641c040449501845014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 732479100 1250 732477850 732477857
    0xf03031d01031e0c0905130605040b0f090114031e0f06060f0a0e1003060c0207031217070f030b0316030209182d0109151406010f1101090c0e0603060f0106 68
    0x880109112160050342c903109440c01d18900c4980d1b070340c0c0410040c0b50896a0249200d5442d4024000c51803c3c1c06800c80d4105d044030200c01c40031610002880d120700611980c043e0100301c098005058030203002e5101c0e01e05480070a43d00d9441c41d0090b0548903805c000c9412054002c1c040013421502e001e00d42114100c0000d004bc440c0c0c90f0070070032448512000a045140d202c800301d1000000540c683c00717059094040c030744c040d0681307070314621f408405505845109010720014000e06000600c980b5032a941c814124608840010b8003000c068008064039880c807901809103051550314400b1a00f09801100e200f0741c0d0180705a9030300140e0740d0400b450303075044202c00d070000c00d0391909640c03416a031040803040e42550884241c0d1401c0e0001c0c00c60b9104402100d651840070b030a103030452124820700203011907280c0100c100c3e01c2c2000c0003c4c00902c501c03404000b4001c2c071540e140a1070300b0940c0041e140b942d008480f148402d032031341e80881d444d8a0413507000384a44600380004860440107030116040360460785 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 732480350 1250 732479100 732479141
    0x6090105010803090d03110a060615050a0f0f0e090405010b12061003030c05120307030b0a0501030903020a03050f0c0f0a020f2b0204021c05100801060e0a0e03040f03031d0103 77
    0x200400300b84174940079010800601d01d00d046100c02400301070441c5110b258005516850034403154402c00c81e0740d1044080c4481840340c040c2c800e070008501e07580400d07245080541e80f085550140d94174240c03041001d411040344e50410040290550140e011904120f50107040c8075060084c032980c404089a40a04101c0c81d00300820000f80180010b01e50240320b1429155800c50440310f52440b500200c4805000139180d001c0c01c43c660800710082c4d000341c0028681800f2201c0d0035107010f5540d40c40c0703d0f001402c0000c00140307101c0f4920040195054030f40720030f041d02c240e000260489903840f481010140d20a0b5041d15001c801da103000342d030250403c181c440364110742813052440c554602040c400300b603812a800304691001c0485811427804540c408010000e91410180c162801c4988180c0008500c1c3e0f161101c1441596201035006620141d040000b113424001031103454214041c96200840c030300318048000c0201500070802c601050b0302150038617403840d02c1600441c1a54a60380d0f41088032890350 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 732481600 1250 732480350 732480367
    0x906090f03020a031e0503120709060e09040b07050f120108010c080919050a06050906090c0312120406020906030115080a0c080408091807050d0f06060f180905040606050306090105010803 82
    0x2080300c071144040000d1345d0045240c0b503940c250741c4040042a04500310208016107940c0041d501806083d030362074124a1042c001c40410360001c4050b0020702203240c1d0600007691140304c3d03c21114011021080d60b901c412010b501d01900c1c000c01e001e58075155082460541c4600c1c424440c59106148080040c0001840f003440e8002e000861481601e01d8014a55a400881c040f800303214001e0840b5001003a035840c0520045003080d4800180301c0c46508042d21190b4440c10403001ced9401c08401000d00c1a071902c952400000920841c484240c2111010000240d4022129150030101d255901c824016640d0300351310300308691a04101c0b601180d2007002207030100b80030f64041c01021101070098400903400020f0b014803a2011141c1c40005000021810810701c09030040d45c8400702124800d010b110b042c104003911440da5148008100201021340b621a40e100c0e80603400284482c16042101d400c00d4203140300070b00b04038094107009100ea030021481443c0d051080c14100d03200c1c58041c50134540103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 732482850 1250 732481600 732481613
    0xb0f031e010b0d08071401232a1e1b01020a110a020904030302030a09020a14040b0d0b150d06050c13140d030e03070803030109050f0f09060109021c05070906090f03020a03 75
    0x100f10103102d030f544d6030f410610f030a081c0014828941614a034202c403034520300700001022880241455030008603070052410016581c07400ae468840003014401c180c88401c03034074000100d0003280400010768843c0c480b00408141c0c194001c07c4480e910340d0758403642c080c20b61440d0f41d84206008000f07421480313500000f00400c0c82070b8051500704080d40400310f007407065a0000303890030322990451400711a607e81c5c0704003140390502c2100f00301001070340d5000e000081c64541c40318042006000d801020403207007542802d036a41c2880c0c101d405038400c2c0104800d00b400c24140c0b060340c00030300c02524145201d0601080860b0201c20072a49048000c1102c00700300c095075011581c0c4050213084c0c076018410303603002080c1c22a050016502800b00b1740000217082c40c00120340441c59401a0052043c0c0d038103542030003104407000c240281510202080540d44110790502032249003075103c12000014038250920050660140e2042d04071a0555125804140c41d1440040d02c001d1510000358040d2202c074042000401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 732484100 1250 732482850 732482873
    0x9030b1902160309140118050409050c03030c0708241614070b060f15190909060b0a09171902031c091d07120b0f031e010b0d0807 57
    0x30042005801c0800d40d201001c0c541007144000c8020070032a18080c420201c1500c11890305000034a40780d940b5541403500f03500060250f000d540d0040f130b21909143c05000040020140072030014003242d6840300118401510345c0840e0041302a1070168090f6204a84a0403500c1c04a00c122002100010341301c0207504801c1e4403c0030950380c05e010110300144502421302015040761800380d070304001d031403070458108080a030480141600c0b44e40c81c103019a9413803002c0401d40e04951030000e24134a050000d10002c1d50200d82c1644215901410810041240311601d0040c0c030300a507003901e60902858582800c20001458000c840c02281d0015031450781c101101401918064000303030685000000f0b85441c0041c04284c1d8002c000071480d620400c004c00c000030721407907690044401640125041ca44002048004051612440c0741d4542d0381e0b070f8009039680d68000b5007080d8000c0403105c01810742005031414043d00c1c00800c00c40d503e085403104d19070610469071244654015a4949040316640d100c400620 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 732485350 1250 732484100 732484141
    0x20909061014130f091107020d060e0624040603030e0d0213020c060115050a0e09090c0301061701060608010b0702190801090c0e0a0207020f122b08060109030b 70
    0x4509041c81c1500d07010b80080548034511100702e80c5590403c030240c0a650090b034004842140741c0403030030218054020940d07818030b034111452040c10032702e414028040d000300700200403180541000c0c400b06502102640c40304182e101000c0304402d0201040000302c588910000e00468540e18035a845403a0151026064504c001e0102d6040215640120102e8000e4502545c496000f1030060288041000600c0310703c040c0303881d20f689031501300500201282c039103c00c80d500842100d4041002d12406001f0307002d6040c0050020003849a6418000352400c2115110a01e55442d03c100032030401c1c0305d100d41c1e90584441883c102d140c0b452035420701100034090f004801d4441d01540c004144d41100380103000a03140202c3e400502ca1f401c3c4246a0301100c00030307184841c00d910422000340180c0303500d5074450281c18110f60a0f804809044922824a420034096410a07903c60f60320000c00c081400025030707204c900d42e48490455540703074010f682e80c40c10f41c0006807007040d003000050680018520200c9400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 732486600 1250 732485350 732485357
    0x415020913050f101e05090406061d07031508031806070c060c060f020a0e010c020312070f050f01060b0d2316080f070504090b031e030304060b040209090610 69
    0xc0500201d0001250b00548103019400000c40c2400391075510660110003500d504890181c0c680d040c03091482404117079202c0c2c40d0050b19118002001d000f000c0e07100300001c080e2074001030380d901002880384526a02c1110080d001c41c1c5003d0081c01d084a4482c111410b440700113000b949058590201c960f0705890030801c0c02c1c3c5c4481d0400001000680a40304400140a203840303031038119850f4074203601a01c1712242d8401e41e2a02c140101c4c80e03070b01d07400038810004542c01e0070448180401400420708010080706170602d031042c001000b50800c1404030700000582d020b5420340e9001014000304909072002c44c030400700440d100340f00d012000f07015580102020425081d46541d007034081d10340f44070030354403c407080c411b00418604880c5c100e40c0c00800842e0300000070060001e240c90011170113402405180070b400c1d200c2d5038a229075403440d10700b000116041c00f601d040c041c0015001170702055499000321400c4900e00c0c10301202034080c1c1440d000340c40940c04028507881039582c0b58428091b60030074117050030080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 732487850 1250 732486600 732486619
    0x6040e07060e0105130932040f03080703062301090503060103052e0c1e030605100507050309031902120a03050403140a02130e0f070b0f0a09170102090907050304150209 74
    0x43c1005110b02c59586507840c6c0200780b844c070040c1540036071f00681c1c0004031860741d0100804c0002085884681d0007207505041c1010360307440305e0600310010030003500002035030102503080406805c03d008480c42421002d980c0c110100c0c0e1603800340740e2641c0d42840014065844081e030f0f9581014981c0c40700302d00000300381014032140583c000c4001a20090103d840124802400600010461608160102040b418103204192400000c110302c1c8049201c001e0800c500400c0000800c075092046520085e0020211a50b080e80e601c00c4401c1c00481110803486080d0020f03202540c41c03400316503203403a16010f86545080030310b547c540f000c4107055541041d00c2d90090440d141c0042c4da4045c0c0301410a44c51600001c1c0f0a910035858074034100390091341d8801580100030411640301c0c620115071003010149040c5c0e407107401e40070003519144000c0d0440c890741c20242c5583c0c1c2260b4015809030541010458242c0215100c403070f42610a0b1105607006850f02000310084106120b00340c0003041c10880180400d910f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 732489100 1250 732487850 732487859
    0x306010e06071e0c050d05060619050406170106080d08010b161e12030605060f0d0b0d0506161119111804060506151617030c0306040e07060e010513 65
    0x7104160000344080b50f4840680d03400a0100c512000c1000e00000d5a20420961081d140d259645d140200303450b12070060014140c0100e41c1070301c1c5070030007090301510170b014994036041d14410901c2e00408505180d0328210000820713800014000d030000055841d400c003241d0030b02000500c039a10803400b14000c01c5811004070001101c00d000d1101c4d0408030340c0c002d204401c203860303c003c1006004a1000030982000303814405da60300d01048881060f00356110390380d6041c00e28608400740c4440c680260303001740c0c1200c2d40014050049605480b5204030b90002075a00d00501003a611101002913042191303100c04003000c106085000c0c0014414014000c030040d007a0143d001803a0000302040132403031803001c00244820891907010b41ca0704010219450800c160500d42140b0b414000e04860701d00405540b41d50700180405010801c940000f0780c8015580d910746420004402d030300070344425010302d280090f008070031480468414140c60080d6159a0816501030045455070400305840d030030442c41800028 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 732490350 1250 732489100 732489113
    0x405031b03090301110a0e01210507050a180e13050f010e01091a04170711090c070212060f2e1409070302041a0a180611160b0306010e0607 61
    0x44460140021903442d00c5040c00c0c1030035150070075030b0840501340034483c0d00900b5802560104040c42c081c80c10210240801d809071015081880020b100701345080e0031310400c640e1200082c10700038041e85618a00320344844034031404640034402c000004800a02048403699418441c64134203016100b02c0e10008811040c9508568007640410705503950b48040034200000301103c03601c05181110701c82002d180a8684840040c0212a110b000c800300081410400c50418182698500003808000760352034103042480e540d51015100381d2044200c2c401042041000107401032003034003209110f84031038840022040c60b107480031825084c512100000e801c0c1004e50001c0c9103005018084600c003440c40d6000c180310541c0009400201007500400050051a1f1740344410750281c414243c1e00b0307541e1101e107941200c094540c900c80c8190481640c01c00121503502c0301e414120f04886106a130300528103010903a1048549124040b4002c00610004080d980600f0041d28481e4003d400d1034078000042d038500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 732491600 1250 732490350 732490387
    0x31511070512040611010519110c07060824030a021003090203100f0b060c0703030e01050d0e0a03091733070f0906030b010804060b0a0b1b010e0703020d030503040503 73
    0xd0b0240c2008101005582c2d40114851101109140204880e080030100032018480b441500180d0a80b25142050189040c030122412601d600c000e81e540300341c450100805040040d40c00d8050340201300c0e55401c0202d002c090b0542c2c5a00020010410001c481c6d00b03104100940d101e01d2401d0664071500714000da00c090105104041e00314030f001407c46240f1400354200c61fa14030510b40210814048043c51a10001c1d0340030541e501418510340204081004072a28414030f03d03d400d0740c905091072840c00b800d0015040b400e491081e19000704064039903515108110201d041d8820941c4806402e01003a40000882c0030700c41000e56002450221082d4440c0b01580c081d10310b180011004100c4035001588040003001078000b614046c8040010310300000c0c040079000e00080c02c655990111000c1c655030b0b02450800800594182584507440000d4603014400794581030205035081522201203250045402c40580f07600030413030700408100d81c804076000e410050045400d0320040241144034000c0d4441e9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 732492850 1250 732491600 732491623
    0x90320063408040c080a0b040b041707030314010b090f1314090616091d0604060f17010b150724020d0902010f02010c140a2015010e010315110705 64
    0x3440001e040c6131900503401d40361340d0301082d40c640000003c01d001400c0c00100d1500700d41c108940102c5500c0c1c81c20529071003142c51221450354040014039400b015016001a03c410300b40800390001aa0781d07140c1d0107d113228502e4200e9101c489030596090390300e01528640302070041480005407419100d00066610401900ca00b2925482841005080500c45010301000846403516000d140e2402c02220074410285a03489024142900026003e44482d804480186a00380642d80120b50790704078010030062050241c407a550070400c3c02c60050424142011158110118003450482151242d034611071200380002c4162130309940b003450365919400600701180301608005000801c9100240510003495100010340e4180b2268800003500400000c402c441841d40c170a50f2a0503070902218805184c95007020b4000700d026985880d45030000301d0b00c2425441070310707508940c0d881300350328a03490b10309110040410074620000e150842c680d800401c5110100302481e4140102a0f4030607003000b414510 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 732494100 1250 732492850 732492857
    0x1e0f042121060f14101e0e1c0605070e090105030a321509010510030209130c090501060810080a031b050a03020a050c0d050a02060c03120a0903200634 66
    0x6000d074524001302005041c2d0120300340003c0120800d4038140e121007021182d04c051100c2c00303452200580780c94041c010401c0c03a0314000080c8090b036149c030a00130b04068031444c0010341142000d00c0c0a007002850b00d0f040c1c440050040c202034803a0341c1c030b8498588101d0f00b680d401e040205a9500021051058a6140b0b0580005801034816100440111110042c001c9410317030b040c142444a45401c400510081d681c06580d2001a40d4803526058000c0416200090401c01c8000000403810615441030b810380707060f540d8691042e201c01c440320031003101d40d00035204990072400c0d0200000c0d024203000b02600c0301e0b51805100d961390b29203400382440100302040c2d0241c0c00c142c980c102001818411192116001c07204400c4880542d00d40d01d580741c2c801c0d10000d004030000104841c0c140320800944440725000320500d102807426100d9200a0111003d080380416103080220361015080c000701c0040082510040c244c650f03c00508240525064001d0031021002c50002c19001c0305a40e45007d00341600d84 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 732495350 1250 732494100 732494129
    0x504052a0d050c09012f12041502211303021302030910020c07050d14240106020a0b0a0506010e030706020106050a0b0a080f1e0f042121060f 62
    0x2080038152000100340c0400c0c00d004002d410340c16a00160a042411b054219500320044901c603450401c111150f00c9040511806c1c0c0941d00e910340d41c3c0b009206031031050404141001c1e09801c140e17030f0350f0f003403d152096001c01c00012400050112024010390300004058100407680da80114843c03d1300e04c0b02c52040a500082040346404042100d03818024030102d00718a0007030141005a2120301074000c451140c1e28041d003410600c44a40c010450440f0400c040d242070484424003451003090100240780da008400f0000140340d40007240e5408001d4020400b601c0c01ea8070504113000030040140301c0b50601003101e28003441034034200132000240495400000700d060504081140c4002d41390300020745800b04021400c4811b1703000588a8103c520701e03543c40255282c160031180c0314948c400040b9010380c0814108400400361104050149000e42d040469140032703009032290104140308900082001100da008c4420300c0c40d5000604015214800a0095200e42c0940c01c44100741e03000105807202e18 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 732496600 1250 732495350 732495367
    0x120f180a0b12070c080f0a0201090b01121e030221120a15050d02100507080f13090f020a020c090703060b0c0604020406050d030206010909020a0b07200117010504052a 73
    0x150b01250b0004018280740c0040310782540c2c0c990309445481c410703402020703010442022160003500403a503101d03400780840c1c0c1d0325a100c0403100179000090300e0543d4411228100d03001c01030100300d0041c1e03031907030190f001d800800c0c840380c10703040c15007101030300b41410740c0c0100b203101c04080000505a002e00c1211001041e400310110924480d81065002507208803088c4403000010b80e0746545601c5401c00b1401d00946820181c2003540040c001c2c070440082c4081c00103803800a038a000012081610b2040204100c2914803076070078001c13030203403281d0a000341c0d001620b50f4002d03260034044141d000c601c601d000700d003d0b51280c14503403643e00500041e5070302c0c1d8081010700c011890a8010720340500b0043c0c0e03a4403401c500c562002517132000b06100d0100084e03544c0c00c0090035903c5484610000e0009448203d95607111461b00c602c1c03000b0110310b8685c25001800087c6e504c0d42c801c1110180c240902d40342a00300d0307420300f0104401000003805050700e5807100742d01740111044002508411060280d40c154442003070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 732497850 1250 732496600 732496627
    0x122d010e01061b0b0a021c0c090605092d0d0c2105060a1a060309100608030418150305010e2512030e0a05150714120f180a0b 55
    0x603080001800300b0300c00c0300743d107400c46500070841a6800441080050300c4901c90a0002c0c4610b0300c03250485144125012090561500f11540200b01c941d981c030049a80e42c00c040b00d040c004c2046d55a030201c2a1041c40982d1240b0703d40d6043d05102c0c040040b402c3d500004000703040d0900f040801c584070b4002c000c0800524440862201000d981f00b030403010400d5007030751441c0c0c5070303140140b4210381d559840049045450450b0184401d00001902080d07480c00c103400002e035510203c180404c02607003080000b08003900b000c130a03074040307400d00408141300d808405202c43c090001c40f0168007919140b0030340000800c000340a070184682020340586902241d01c07002c03414079400300042280c221413200d030070050b0032140d41c0594501e68061030080c242a165a0020f120541107900c00e03640b064102000c1059140070000400c04c0501c19411102110100841d058a4103480e1100c1d6080e4071090290086489258000346061002c24a070764181207004e4002905140e09500320f0710761801c0c00b0800c402850807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 732499100 1250 732497850 732497879
    0x1d04240b03100e0316080c011415041a0d020f04020f09010f02010207020915061201091506030506062b180b07020c0333090307020906090705122d01 65
    0x1a41c1403e01041c80c11080342c0c0e54902c45c822011211a5001700c080080c04008001c1d105050280002800028180368580b074040c1402d6660308540403400350500c1c000d2800f0712851841c000ca10004000e581d003000c08102c05000500d0003070360069015180950160b03038601c0240f150b403403042c000d26103c1d00001c0004114241440240703056a10401002000d40c2c0c27842003465000380c0004c55842011030000114450740a400d800484205d0880000705d914034551704222041d00703018a81d40d56071566000220107481c020785209401000803c031f044040b400d1002c0c02c1003001c2654644184004400c094041180c061141c0300d01100c10060300d010030090385040c01c41d001000c0c0d00c000d00c07460f620f03100001e44901490040003503030001816134900320b1142c01450005101908420540c91922419064481e4000030040317220300003100001d00d0a241540c0902c0c0100d810750703681d40c10403241c01c0443c000318078081e00d9a10202040c1280a50007802c0706407008142e034045050345201d5150410341c06070582d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 732500350 1250 732499100 732499123
    0x70c0801050a051f09020f1902010501080f070e01090f1806020a0905091501080928020306250e061603170702030301081504061d0f0c09011d04240b03 66
    0x340041c5890424000c10811000b526640240187c0c0d1703441c0040d514041c0d2240f4400f00d1401d4003d4402d04a03103e4040d884070b4100d600780001d5503d14402010300761b80300c2c41580a20302c10321061100500558001d1752082070b013545030300f200040d036030f500302412405007081c10001c035040ca40008441e400194000c030200c2c0189801c0e585048241032000c0303c02c00c030a1203461880d04001d0140c00050001a081140101c00403581c179924001c0014608406900c140e04941030f40a40b1440020800b03100000f02c5102e0240702c101c400c1c0c9a20508041e044555000480f41560300c920705018502005821002109410380700703031070702c42940b034401c41903420741c1e00c0c002d001106640090004004010001c00c2f19580080d000e503a0b110955554908400248a0340d0f481c0d10030109d0b613100060007220b0004500b20f600c482b13481100c0c208001c010820031001404d01030a48003581c40341c03281d80703100401102281c0052084102803401310300a80f00311403214003015450445a160900c540304c0d810203101e190300c1c14 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 732501600 1250 732500350 732500371
    0x3021f030615090e1f06020d0809030c06040b04080f0418150f090b0301020c0f0a021206060d020d08090d05010b0406091103040b0402060c0a0606051f020a08030c070c0801050a05 78
    0x1d680c5118060020001d81c0f181100d05010000010903100611700140c59075020303800c0807008103496030802503a819281320000c0200c0c0d110008035081c1c140001c140c5022000210003441c140d81c40b50b60302e140480014000300c90455050101a5200201d04081d202801c100881401800d20a240400542e030114070010742032604190140302c1a40303a5184803003554500c0e24007044000340745020a009100701d00c0441c015000d801d02c9011002004207801460074001c0b41d17541078000f02e0300c00b550f490360015904940d0000c4100720302c100504200c20500c1201e406225024141354000000c45c40052128104581596441101e881707103181501c201d60161008288c2008100200030807880c00e4800540040d2500e01c2d0030f40002c0455640704102c8101c1c020340b80a5131000442ea2501501030560390007098072411a14002034050540440403060003441e550052007004030a8503000340c258406050500c880108020000200c0c40208050004100c0c2c0d41c0000303000d240c0b40b100e00c02152070107000300111 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 732502850 1250 732501600 732501629
    0x1312031223010b030f0114061611010329130e0d0c061104050105030a090224121501051801110f03071203020304080a0819050406020c06090616030e0703021f0306 71
    0x2545c000c03c0720707641943c0f10086581d124032100c00005903680203e072100290492040100010405103420007444048281c070180004150803000c4454004803040380c60080c590308080303d0141c500710061007410b801e040c00015000240701c0303d0314101702501d01e060001c203164140320400c0182c1c601c01c001c89800054182d6003054200300c0028500e1101800600e40b5940310125402596104034200c4401f0f003004911034010b1040001034050303900804589149403818000141c5c06404866038102d069005035240351411003c0310b960b480030604451102d0402075603501491950204004a03a401e02e2440002c0d506c5000360b1a080220000500c404820940180140400180c480055440c3d290482c1840d802c56900c040050700c0c031104004240d166141001e0501040c40030700c0d03009120084046003503494071341e03c0c5048a556a4010303500d040c50501c000c1c09001c07466100303921000e0742107040415210202e0756600004c039400211050b00f800042135140408003680c0501c030b010010240240035006 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 732504100 1250 732502850 732502861
    0x1a190e010e06061c030e1801080d2604060509070b0a03020919030c05010f05132709030e0f04110706020306180f1909020d030e0a0603021312031223010b03 68
    0x10050a0024005c0620020031a460320341e43e10b0480303641d920b58049629280c0340d07942c2c0085e1070350b50350b803401d620010452a1414005420749003171500b01d000c0c540ca410300b00940b101c1e503d1400402c401007050301c140c01181e4002c203107811804014101d0401c2c1e0f0781c2c0540c4401225082101502c410449008007586200f0300b0000500525902c00460b6000d08244541c1000310308192994410145040c01e00800d014000c1180300408280401410343c4131041402c025008032030000326140ca21020700171a40000c2c201c0040d24051040000380400a2f20224169020480150b80744d00f0141003258000c4e001f0041008074108429100c0031131400c01009116400d0004880c9000e44001d0311101d45080185038000b0264882d40240c010b0b40c1d40940f0781d5262940904008280b401d28013031092203004030007000281c9074424001d071901000c151840307030f5119103400385180c0141ca6161085040c00300c901d8a08c61191005e206400c04100c18403a0300c603010300c032901d403c414118140c00801103d130f803d005004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 732505350 1250 732504100 732504139
    0x5070e09060306010509040c0e070c150b0d080d0b091305190f1b03081b07090c090b0706060b040308070605010b19030e0c040c02100e07031a190e010e0606 68
    0x3411544103446c217150544903030400301100340803908001340410023182800500e50784040b00303803603d5004610000030000c41103a46d105440343c164405500034140040310010070b002c0801014108000c80c0d0004c0c01c2840722010462081084841d450f00e04116102c61003405002e22050750501d8008000090f46c441c81e9a4645c0980c4c803070100038192203507010543c990001440c500c0c03405150072104c2103444002c0740f05ca240100540d1007084d062401503101c0002c1541c1c86004210501003980c41d000c0106040a0204000b43c104400a8400d00d40320078000500c12281380c0100003860040b6451a0f449103141400303020340d00180c0c80164008410850000d6500c11b0f05080f18141c005841d012600c2c02d00040040c0c078081940300569070140c542000c3c000c141c0e0b000aa8104442080e990502000e40c146c5082d0783c40301c0c078170310001c4d100c1000104840500c00303c2020060340854100d4049070460170a90014044610701c08100582e0ba640720180d00c030014041104541c4200211002800d0298248844 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 732506600 1250 732505350 732505363
    0x70b0910080406060e010e070908010510090504110607050f012009040e01060510020c0a050d020108041704120f0312050108030f0d0b130912033605060a05070e090603 73
    0x403010001410003103070400c0b905070041c400800d801012442c1c40c3d40c462450307020285003507038414041540060000341c40003040c040c3d24421100d01c442c8030701070351038105020040d00000700100c800c012207030640905070b903910300585816801400181001c410503030505086850090800400d440611031807100d46142a04403080490160707008544000103808140c0174080741c0e088140c0c4042441069000c1030b50008440303c500c0c008846c990201c9030703200103200ca4071000c50000f0b400901128002000305070b01090303003010b5881c07205000d460541d03500c0401d0084803108200300d40ca004811200002c1c507500c50700313018200414040420441d490040341c686e0380d108841740f011070711001003542c1640d608981d216888450740030b0448824641902c006c8001002050012036142d1818141114403e1192244e22100101003d40d903103440c1207240c0c550341070148016032814100190041900140342440914090024480c0110b00740c1401c50000c0d1104040181c0503004135070800800a00c1e90b07000600 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 732507850 1250 732506600 732506629
    0x71a030115030f1406030106060908030f161403040303080c0a0e09090c061b06010819020103051801020a09080f0a1e080c0601030c03020f061810020f0d02010b03070b09 74
    0x484658a10480098002d0040c840c1d0351005240303850004219200003401c480d1003520701b02c008104298803501c09075142112406a901e0303507407003030210a29401124000340056544208031075400c1900d40c0e42d0b02c25504a800003403000c1c0e04003103400c00800d0380000c0540d4004440c00800e45c2044941030f0001d011510102805100300e400380041070940d0300502400703101110103001070343e441c038202c0e5205000110080840045110343d40c000a8100c101280807901d0105070312041c4c0c4000070342d40045020b82805803500d0040721280448054155092000b03004454450b100d00c24840c3c54083c0340d5042040f08208141c45811600300e00001031000183c0c1c0d03012904418503558015001d04060840d40220805030402d44900340000c414086183c4a0b441128421180c04144c6418030003480b40320302901e00e489580f1441c3e40c07400500b914000c0124610503090388115081c60003034a03900c5140035140b16004015035514603580c007080c01d040c04030380090010818990301c0d00407040085411082e80e42d1a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 732509100 1250 732507850 732507869
    0x80c04050a0617150604200307020304050402030406090309050307151103160b010e13120f032903160b091203040503010501030b0a180c0b090310140603071a0301 71
    0x181d02034907a58000005000c0c40407400083d550002001940d84203c14950782a0868480c001141e500c3d04d070180818241d1062400290250004001c483d143c0000d412402940801c1c170012881c0d0310f0703500c05035200ba4010407004c03807010130030b05010704146501d40203c1e000303402200050000702d41e00391581c44c41c000a8600440c108085415450030b5000e49413194a00504281c01320061101c3e21b0f007918103803011194100c00b00d0301d850450010081031280010a04e0f04040c011010b05405941c60020741c281d0f070304000c07816189140f0b04400d12166610056101c12907960418503a017010000901c080b40700319050b180e0345041c42d403146940d0007031080d054450002d80200c800554414400d0700c0081202400074821561686400d056940b02245c000005030320704840f200c549190703400c281e81041c1d04401d607404040e0400900d0310455115183c0c06405204000200800c0340c000e00c40c04800400c5510010620306000b0105818809594080307048581a12444404580c104040700e045031500746 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 732510350 1250 732509100 732509111
    0x219031a190b03010f06080106030c090509070201090f05060709060203030f041e0515072d0315050607150b060c0613060906020c0604020f0a0f0302120307050f030a18080c04 76
    0x504000401e04076000015001004000012010b0078400c44d241591104d403a442c01d1681c07600300c00c41c1181c141400c400c1c0000e42044080002d420808640703a0401e1103840081902c190380c0c1c8031180700512000c4112401e500441c100814541c1c0300d50b401d0b0182450b84051891410500d6001e0720004001e80003a0100211040c149180c40080c90650307246540002039816100c0c1400e600050000d044445902081c01c0c10301c650100c1c01a040105400502c44509100612040c142100240300018000b4620490b0f0303a40807a02d9900e03040070b811101e00c81d00c3d00040c9402c0381c83c1c540307043d14206540d03d40521000d101e81c6101d03040100b000344d401406407102c1d050b00704080c10400d0141c20841c3e0094001c620004100c2c1120102084480c42140292014120010800103200e2404150302c6490b4514240305400c0c0014500f400410201304d117640c048034105036107030b01d803c0d08101c101d0f800e0b401280e2000592a81658001c1c4110841c1420442800080303481c00040540314800140524030840e40d84 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 732511600 1250 732510350 732510379
    0xd05090a05061b0a0b0103020a0e070503040b0702191518052a0916142d090a060c030306050d0c0b1b010c0216080d090501051803010f0219031a 63
    0x3d48552200801c80d0044404620305030400c43d01102081c0404e80c0134520f1a00c0101e40408884819805145582d480d5440c603500e94560ba00c1a80c0094a941c1c00c5000351401c0d081500108414405058001e8051030100603c0d0400b0004860400018074030050b4081201c0002c5000842d60014009210a2008032903246047c4001c802001d0000543e2141404003440007408200d41307003010b6100340d0749507517403100a14071208095001e60f1303030060311080c00c0142041040e000b0044c0c840e80c0e241c40200450804100f440018440070f0546c10210020f94120240024981c3c1401130f400103110070746140a45601d1a200c15081106034051a16982000500350b010801d002d8030546c540400e100c002c0240c180c401d04000e4854030031103605c2e013034240c50060102d0018004500c0e5204c1d0800c80c1c5510100c10300d0702d001542c00c1c0d0040c0d00d40581c0e41c08031a4143d00151028024011010756031400142c0d00d0005d003200c440c103104411501ca0030103150203260304c95801071a03038469403c1c1d0119141072100e0042d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 732512850 1250 732511600 732511627
    0x8060417070303090c09020a080603060c0405010e010516050f19020607060b0f190501110708071403070b0a0207030c060507020d02130b06040e15150703230304050f0d05090a0506 78
    0x1401c8005d00c002d40b20100015419540da0241080003031507500d0001c0c5480700310030142d60b0402a0b030126181181042708100540c00b440d80800350030010b0400c107090180c5140a040d45400c54102a1441e401c5050b84e103034030b80414080e1100c1c01554000704400d4141035004181c00303010710751004010b41e0780d500d5004a5035460004180d84580010403440741c03680c0390b43c001144070b002441518049030030803600301440800482e010041d02e001d40700809165240645d0400c0c120f01c0304040c103405000d044004222801c405004040032000b5030000c01d9803e2a5103030840000295610079002c01c50240001b10060351450422030f9810f40440d943c07100c07540c3d2002c074103005018040c11140c0c480000107000408842480001d40b00d4001154000710b4a01c1850902c403140701f00c0d1089946091b4100104000240202100b000c21510b03800310401124042c1c004c3e00c02544191000d0390700360301003450b0152a5a08000380da01990030b40c50164205104400030032050701c464021248110700200701c030500d4441 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 732514100 1250 732512850 732512861
    0x101412060a0f0b0a122c010b04021204120e0307060e03060f0106080f0603010f090f0c0b2b090b090a06064406010f0311090112060504050c0a0f0e0108060417070303 72
    0x981d9404803046d01690200101d8842c0800044c041075080c410540818038140c42505c6000d414141c0340c8040d60340740c0d40c0f101c150001c440e0101090020110700c148007a1001c00580002e00441d8480c00c101301d221808251400c1c4008200a0140107450014080c8503031002a5a0304015644110980f41c0c5034000040d001d4055010042c259078685090101070003080d10343da2030114050580c0c1c00300181c0f540c65a110340d120701301000c1d2141081e04440100b508641003041c510240040000070840b540e03a8440c440c0b0b4400b51403620307040d0301426003481032103054491a00102510781505920b000040c2c0c7c540c44c94800c0400d5006122100001d003040d5074002d101404120b85110240c408560f151180c0f00804039003804240d500003100d0f15400c0c01c80c00d1401d403a5040c0d46254069591602a6940f02c2001d0031005004460034001c0c5030b40c1ca1816140c020012020300030410301034005504240c3c284203211016840400300786e1049040c0408170380d039030035465950390f8100c0000b581e42e0b4a90078154007800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 732515350 1250 732514100 732514121
    0x11070f060e120c070905060a0311060706140a020403150b1e061908100b07050a0f02180c030702010e06040f03180f080109031d010e101412060a0f0b0a12 67
    0x80b40003c0702c0f50300a80102e032038002c0c0c60502c0000c0207180c0725441031026044003400700508811482c0d410101a103865005030820074480c01001c12151403e0900400400040c0e0700110043c2d004601401001a400e22004039a4000ea8080121801400000b055441780d1200f001c0c0718031441d03446440c00c1c2c803000304403080c1d01040d0001803a20308120350001d0004008071120b0521505804c40030454014141c200e40304c00b81c22070000c22464070161a500010050000103da000c180b0075017880e1038643c42a09a032180300c107035074240d8980c034220a000c0c0c2900c0304400444403540000040000080103041d110580941500c0c14415a05440b400f000e8204a9034000354841d07084e010000500c1c180540001100f45d1096030380400840b008600c043c580301d0700040b418040f5800440701c07901750074040c0c044103210a19141144411100f0091100140d03c800c1020401d8032640c42008490700f00140854010b002414207042c545161a400d00c105010701c030010000c10445140c0d801205895400508851 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 732516600 1250 732515350 732515383
    0x15100c05012307110c040c0e03010c030603030e040b0303030f0705090904051c050c0a0609060b0613091d060a020c011b020a06050a1a01230301030b01030611070f060e 73
    0x2030194040d452034982d405040d5851480d580c0c000690764a104290101a034220040104666100d0f4810040502102c22064040102410500303030907903024003c10080e10140e4900080007401d6003802845801d070a0140c501039030425464229640b0004201c03a4484c02e000c00107441b035224050115114410b85102e80e031b0100869050106000f0049a0130403132055081d44181e00c02681710007500c290250001802d00b035000b0061000110301260803014159120b0702000035a51440d1002604a81102ca820110501d041c4d1050100e000301d4816140e0246d4110014148864580542503803440c001f800c20310900d801107038400e481e00003504098011400d86100003110388010344000d641c0d484045040d1151410100400e900c0d080d2441840b4252000801d0340000004050040d107a81454000035000070180c0454021003050840185000c0c0d4450300e80600313154503500f848000d0f200306200c510001c2c10200404400508015044211642d00810120308000c100c3c681a040100c031440c0010034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 732517850 1250 732516600 732516611
    0x108070636030305031914010501081e010609050a0902030108031c020d020d02190306050102070623040801290a03110111060a0b0a17060c03100f0303020c011715100c0501 75
    0x30180c0000107144200c1c80b00011b442d0035a91200b0b080301b9500d225884081c480d581000600c40c03548194501039111400380c07580d10142031a200c0c01d120400c000d0f4045400140c205105200382e14008071680000c3c00f44120a40c01c3d0b5040c07602041d140e102e410152044500d40081c081601d00440c0c054070b83c1c980354450f0440d100d1441d1548180658001d000308000c000702d4141d02c0c04110301910400d070590308107a0092896505095095540300d07030303047c60b00c1a000748100c80c0000f003003d024010409407100400110b0014442100042c081c58050010311100190b41404c0440352a100c0c8540e0840741c200c00000580e000a0b0010394a000407003034010721602984003046005006504500d58088064483d204125603074192201c00c10609869200290080000b00d0902d00080019640101c0541c07824483c1990340c04180314042140d50048016130002943d02000b50317000b022020044034455002d6855107480f028415083c0e00707150350f4501c503600300d411407580305110301d00061101d139004008000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 732519100 1250 732517850 732517853
    0x1603021312020102190c03031b051203060102151602160e2d150307050d0b1501031107060c0207060305010323190c140111150903090a06030c020105010807063603 71
    0x81d006d1450200341c0125090b2500069884001092a01c03440d030040090a24107018030b026800c1940041c005034118400c00c3ea0800070103402c240442d00941d6000503002c1d41e070120745400303400d204131080c524002c1d80d50702c0c40c10010494040c4600e5440042e03000c1c2d540600000c805c0e9565000f61012808003000c2c08002041000000c0d441c2c107081c540c0003201220003c0d41e0314400c025006072403c030000c00300804840072a00c0d40ca4141c0240313880391014100850081310b0022260115004094141c4182d51600c100c1030010b074040c0031380350113010306180500c42581140c80d20f142d0025002d0305c0142a240d01b0091000d12102402407400030b401041c012616074480b81005228018031f402084034940d004005c61030903601414102c2884822603001d480e1550060020489089000f480004640070401110703000703544402003c070107408552800580d0130345002c0e000b82110b40503080000320307a006610600410f6040000ea105040d800042c0500c070b44900382103d89914080c1c2101903c0d122804800310 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 732520350 1250 732519100 732519113
    0xf010507121b1e03120501050f011206050d0b04060b011d060d1b05070314090a030b04030309050102071a1b040b0a020a12110d0302120a05040f1505160302131202010219 74
    0x3c0300350081d41c440501c09210601c0c5000c41e070003803041c40e500400001d903403801c550090302c1e2091015140d2000086d03480c0d5440c01718044004c940e40440d6001c0c840320810041068034483d40490005c00c1c81c000340070b01c14406c2c0c20040307104441d000074466038010440024000700f5800500c60300d507680302c050104c80c0110ba070292441c2c0101000b14003040301400000060880320013502d900d01801488180d565207191031b022404003028200350105a120341006000c01c20900080003150305c20b00720541c80c0288041c00362000c28018040b5003100300100d000d11040c040e02c0090318141c6001d884103550b42c0c610244140d15101c40c455000340326002c021038644100e0340015005030204441400d5610252810324100c00328814855000110003258012136100d1102c0c2d0701007680305103c0c121070321109031030341c50f2100401c5443d00030a80258440080001c140c052640400d440000c90500394180811440c4044242c8070a00444002c0b00e541d06a0406580c800c104500000382641004000f00206080c800c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 732521600 1250 732520350 732520403
    0x60b10021006091803030e0a050102071a0112050a060203090705090103050f0c010503090d030515041a040e0d02190c0b040b0c010615080411040e0712020f010507121b 73
    0x900307014a40800011040024020068a150120284c21a01242d5076003a001041c0d4502c441e1403a00c02c00603501c00154092004040e210300034903810303200800040080e03400540c140c008140ba886440624800920f0004000c6001c80d404000942c4aa070780c64001c40c50701c0305503440329500440c40700001040c001d01080500001d1008010786a61659400064411340f1040d20214815445000c0c6009264400da01403600b15450528004514803001c0010b4140e074080000a0074004400310900e99500e8903100e40101c2c0d08140000d820075420540d00a03480d01009640d10150780004c00100040011400c10000500300f11040301e510b40e40c1700d00301804541c00c11200003045600c0c0503004500031080c450312001d0b45900365540e03021959259a4081100344032001c25810a485854640c18144140025000340101c01c2c0c07007503100d206a004200624440d40001414004c040210502280103c92603820b0101e05052582c000b81440400d1801c0c0d451614014240484040101e0014002d40060 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 732522850 1250 732521600 732521623
    0x1b141c110606030c0a03120203042402060703051902030406020405120a051b1e0102010e07081f0603230a020307140102160e01061b021206071b12030207060b1002 71
    0x4485075941c809041c540d80d0a103809030580e0100b070896040000a02e05c10312080410b28a20549040651300c2c1490f0001c56441003032110140d2051030b02e03c040030b43c10040c980e44540c0d10f2409000c0c5003040390014120240f2200c2c4900550340000000341805059011a0010800a850014a10780815589407245103a6800304d40702d00803110045005201d20b01c04800244000b41958059074032140342c031788141545240d03d419552250340c0c42c4c1403017130244500c0c00280145000303050807480610303840211080140802e056585816000d101142015429201d00a101c4600041c0f54640c4a40c6600d001c0050b2002541446006004500c62200c2d07840c2454000082c1c088543c40d00f80d4011512800e54a4040d100c11031340454010072009224948007844c4580c55006078030807092a80108811302d2028000d40c0c9251b1084003070001031613202001840f00122a5100144110142e9414004180e8649a48201a00410080117104132503201440c4000000c0000505000b4030038040c5d100c4d0003401c0c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 732524100 1250 732522850 732522853
    0x60a0e181602070e06090915070f030b0402040b0724020c0a0309090b030604030e06070b16090609080a020f01050f0c010b040b0f1807210608010b011b141c11 69
    0x81ca0210300002c1e020f03040d20100694441142d84e11824003c0c5000001d0980c203591143c44405803880d0382e0070350014001c0074a40c0d515804c0009560025083e100301824941c01a441044104607168411013502e0305541d010095641080030920080900c490b9105440b40132807000440a200f03144c009819520789120391100c503141903807100000104c074200034510b500350f00103200050001e44121f401c0030020313000403d03460400455450b0007461082c2180d501c2907045c4454143c0b1445a08103d01c000145a240743c0303c583c143c24501080c0c1c4585015400a00449024140f15100c1c2c0c068400d8403450326481c1c0b5419192041a040a0702030a030500d603c9016516101d81c400d0135081a92000c040b004004c0c4c00c90910070740708482016858002485903041020018154241c00b85075802c4403030f00308510501107451803e110100703084a5a012070b040c148090315a220318190843c2c444c48550b1604221400c20103130321540d0f02420031154000d03101c020104502129000394000214143c000607440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 732525350 1250 732524100 732524131
    0xe030c10350a02090114030c162102030d2403080a09150f080a0b102d09031a040c120507050301021309060b042d090515030129060a0e18 60
    0x11b410442c944820344122058250400030040090007040c01da41000b8412000c0124090108115440c1032081080b0040113800000c0c0790360320000d542c003400d1381040b80031080495442c54441054100703800c52000401c954000306403581aa401000610002c1100780c1c100d411580902c180104941407455481740411103c00201380d200219200d000c3c900c44000e8024610403204000039110160039402203124004011410488901e050703600c038101c0c40e01516403007003044c00d5141100501c00c0c00381c1c000c4029200c0d0410400031a01402154040303401006089102e01c2d000d082071780c10640341740c000ea1b80540c0001902c2d40b529001140d41000c8030b0103810204030698989901481d944142c0c4101d1110080541e4400075800c1d90b41038580405880340c180c0c05241d41d480b40c0c4181500c2003100c450a400c0080c066001203410207001d542102d40101c0e08000144036503402d140501520744480a001e26000700f100983d079030081f0054440c98100038130b401c81c1a503105800b0f12100f00708a4444c00c5040381c64 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 732526600 1250 732525350 732525377
    0x1908040305152208210103020102060a11031308120c090f0a03110118090f050f15010f050319020d050105030f0a0c0501051602100e030c10350a020901 66
    0x141042c0380503020724104840d800300710700543c220020b228041514807102c100540328107001c880c0e100324154148101062078070b40c9036000190070414000c010b00c080c41c0c1406032480030b00e100d28040301e40c400f0a0b0f0300d031158005002e003840c038543c0c05180f00c02a803a914400a22040704400000341c800441c00b116001d801c1e050683c148520640c0074170000704000f600c0b490000359913004000c144a42d0003548460303251195500300080c2621000359101481980d00c0f014003212507900e52031990b00107080f50b0340c1c0200c0c0c41d621000800034070301d041e144400c01c0404004244900c0380090a00342d10b281c40f800c10744d1202d20f1503071810000c0100384521480f80c494004c2c48080c0880c0414100b4045406c041c00a10047c038110041d01d00c2c0c1e0044c5500d4401003040d04c0c0d00c40040c2e0f6507101d00100551141d98403038400c5862001d240c50045002d604600c21180b6403100d000450748101c803c070f400c40044450000d8020004085c0500a00040440610a88580810400e42d50135400340480302026659017032402640e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 732527850 1250 732526600 732526633
    0x81b2b11040606050901090b16120503150a08150a0f021b070f0605030f0a02040f08031206030f0d0e03030409110319020a082410090512012c1908040305 67
    0x340c5c50301501103803090a08215180740c01000d0110414508440906001269170343d000c6041031205130000f0402c0841481518403940c41f5060480c4000e03500200320b1f030b04008000b951a68070040c48440b4250a000140340c1840b190407001c143d2450300010340d1a00c04801d4924082017086420f0b0040d80b00e030300400902c00602e1080402180d445880320342c03841d26401c54101d100f200080032190040e8082100254001440c40080c004041d190003440e19070121111001000034094036041c441c2d17000b1900003140d02000b003170040d003000441c01c105001c400701c20007090030360045500100c2c0703403880e000e481100180620000c0d4440c01520b090780d00344426010500301240604c0244100080b5400f00280b010340306a200ea181d01c403407149840424041c00c4002811211144100c80000784c9415410025400c0c139441c100303808800c0d980203201c80d0b500101c004080046401c443d810907000c1004481c242e07007060003c211031007028085508100d0b02802c0041d041e911501c011130362449050a04c0c5070f41d25a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 732529100 1250 732527850 732527857
    0x606060708040e10081605121b01030f0b090c0a0206160c0221011d0f010b1311040b0307260610180519060207081b2b1104060605 57
    0x107000024030300b0281060503400800380000c3c0202d10b0740d1280071001c02e00c424100864000e072040380030544400b41c189070078032010741c250342d0300d16500340e000c502a018080103c00d02940c40c1002844d00017a800c04402148005d412140c030322a4201d100d030024003d05000342c20091415030210340885941ea110343c10700507108800001c16400240a5625402c0140382c64070f41086940c000980072601c80c48076204550071a44072902907080005001d507c802981000e002008200071000006c00000010704007240e8003503d0031043c4088541e5920015180140d0842900c018000144241d9107900d0160390107411030002800095848118056040210102c454032b5445080060868807084185440c00e0380d030b45500104200e405943c2e0300d0302103165101c02d19a4010031354801c4075200344c58079042000e8180780140c0c2101c0391642241c0c074030112646c403141d000c1c2c000007815684042500411801d5040c0d5240c200001d282d414400d11141c01845038103902c404400000311810000990b85035025103082c403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 732530350 1250 732529100 732529103
    0x27050411210604021209070611070b0315010201021b0a0c0e15040504080903160f08010b0109030821180609030901020c040b03210717041a0304170d0e06060607 70
    0xc84910780314500040865220340011016001509040745511108170200c0115414021640000010800142c1c440c08402901c070080303000c3c01107a400d040005200b8480104401d100c1c1e41e640080c81420b1340700354100e8000f56080d00707000301c4807403050380820385031400ba044c01d64140c0e43ca000c2c040390003160002400d02605524546418284104d824480502002001510070500a00c00f50607107440034030070031480060482c11546640e082c8028000e0103c92a0001d40340da0307251064005042c0d0700000e16030300781c07034114400e50388991004010320184a040c814020b45812801d040c0a8078560700907003126241c0e900e0068820343c0c0c0d11522020355901583e5042c80c0181e00209401d0340a0806600c020440803010b01503c00d890401103001c01d0502c0070300c1440c4110540022030406102c0e0441201070300f2035100b442ca903d044c0c54004410b03600e00e84501c6052910301c0c0000800c04008804a041c10741200da010304c42d448080d131354101c5008110600300d510321805088000b4000385004001c440f071340ca = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 732531600 1250 732530350 732530377
    0xc1504391a0403020d0215210a20030a02071b140d020325030203060106200106030201050d02032205100b030601030c0b09060c3c070608060127050411 66
    0x2d442d540800c1509949140103a030480c4015045e0108450581d0090441046104070791440c01080c124081c41d00400800304400b59180c402013003400140c0c0c44a01d004d69483e0300c001c5407603840e000c0350b1038002c2c86580c40c000c00f02e8081683c00d20480c01440f407031604450744000042043c005040174000010410140250b050700800fa60b80f444e181407100d58010b810079064034108081d142c0c1d0104c0c1c42d0031070030380084020460380030f05410b040070b03502c209682c01801704000b07001303180c907582c00039020b8001c030501c059001d40c01000207001400c02c1c0304491104100704904919000755400c229486e02e030344414170408181818400165410001226412254048180c252080c82c01e1000140d42c0c10001015a0040081151017200c4004118400c042510240c0940c3d140c6038a100001000304030030308214a9603920745482105001c08100c10381110039a0a00c1e0090755907100040300c4000e030101019902c1c800d2000c5a968640003144483d090302d00984041003e0782041484d2130b15400751001c00440c0d03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 732532850 1250 732531600 732531607
    0x150414121c030507030f090606030209090a08070209070e180f1807030602090f0604170105070f05070311010608030d1b08101401090504060902030610050c1504391a 72
    0x410301c0383e400260310149038500024400400c0c1e03031000903507041000070760340c1f2912604140305518183d0201c0703400800c000300030700551091343e4924440c0e018118029200d04c4080d0001414180146100c000425000706500c0e030a0308881a104c0c2c2030503054924440491255000070700410b00c140c05000c0e02c0d144240140921031842d694900694003203402650049107400440c001c6450b442c0282016048204c1c0204076082c10600d16800c43d000240450f040101c8010003213544c5030040f00303c1d00b4160705403030420f1a040b03590040e2341c0500144c0e03000c030110f4800060518510801544400c1d0250544034149507980c00c80d0344100c0781003c040c1ea10003000c0d2070b168020809061890a01102101c06040504545a8500c0014211b402641c042104e2640000402c2124135000402c65044061804c09134201031070180001d5030790500700300c00c19207008002e01060900c880d400c1080d4001c08441c00030115540b00030701c80c44a821038102c056101d0034dc0100080349841144020100c0c070103038031013120706 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 732534100 1250 732532850 732532903
    0x30b010b0d1104060905361501080c0d090501060b030108010b0108010503160b03150a060e0306060405040b131502030c0a1b05031e1e0406020c06180d0215041412 71
    0x10145c080000680c034080070804c86130841c020404450900307c1e141444a203181420319a0f0502d41e03991205810070124408014071021400161055040346003400600380070145811401420140c101003001c0d1808400040c00e0901504220110107081e40c4003c03244c0da9400c00e2540d9412100c580c000f039010030351801d0015016540165074007400c594040f1401c00d001d1004240c031a0590780001001070b4880304403140d281000c0001c2a00700c1b1041d1410401c91415468100d8100c20103003241c140c0e0100c180d148824000940b610086424582004665038101241020442d80c85007920b02c1c0070a10980c0d000014008403a418107100d5000070155140548648406c0402400400c24140800b1f051200001580e288608440b030303484928500c40d0b9503070a0074000307450f080600b030110f4452071040110351055904107a2035016090281d40c42812035003141300068886802003805203440c44003090000d81040c50380c400181d8468191150000c1404070b002071030b02d500c400c4602011004e031042c490318 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 732535350 1250 732534100 732534109
    0x50c0414090f150102190809090f0603070b0d0603050601090b12070605030a05040f14100e0109080913110c0601030b0a1a0d170706020d11070c140a030b010b0d1104060905 75
    0x400f80b014815074010213001042c5140c030650385001a036840101041804150030f154180d107070061034146910100c1d1502c01d00181e50368a043c015816569004208540386030070640000000d07590000540f8020b40e140c406010080c0301d502e008500c10207a02c4103c07000004003181030b4041d00c1030365031003034515a100000c0704090880540111103d104135144140030407101a039500c450004100a00401030b915850a8103407000302e031001e820342e49032164400005180e501181d40c40102a110301c980c0704d40301280840140041d43e0307100500d0b0000914065140004030b001816244905200c22031a140c044d1030404554141c074070500b051030366801c00925842c042d81e4002c1007910030490007a141d000416007081c039801600c3e00f12021500030642c010060064061945180103040d420390901c152500d610001014a114514824258815801c41030f02c03540c1650380610f412514083d484d580d80d0300654296401702c96001c00c0d60f0310301192179500c500000c084400b00d641d20341e102c124803400c0a0410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 732536600 1250 732535350 732535381
    0x60f0207210209040f02120c06121906031208090a03140310170d030506121f110a080406383616080712020706050c0414090f 55
    0x20300701480c00300554006994010010784aa8401c002008a03500d140c418080c0c0385084903150780c0c803030704071208089a81d261007054940c204908540a0300a03194540e620082244000b21100890300700307540441071128100301e15580c3c40d000d07914181d5540c0c4100740700d0f80b1104070207002000110820510f410b01e0901034040d5400c410140c0413041b03001d41d564042e41004c1c0c26280c242045402c00c0c2c800700031240c0c06110f920750142d810b0b645490305030a00766081e503c0b07c046111554444500d882400d40304c002c150300421125500183c8181d0b140b152150280c0b0510085404950450419503c4032007440007402d42d80070b8103c07080e9090300720b05001003181141741102c0740c6290803446101280034007001d1041d46110b01a1144441c039582000840e02a05105000344001d143c0c0e61000252210b06078400c484540c04416864002c6420309040070f40f8011384214400940007504244c14840c041650304020411a9000c0032035032a0610085c0034001e030510200c0310101d8131030700d24001558048011104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 732537850 1250 732536600 732536639
    0x180306110c010f06080c0d050c0103090f140a12031a01030b040f180c080d05030f040c030f05072105030313060603080d020c0c09061c020301150605090307060f0207 72
    0x103a80c140321103180354078216400310700c080701502e80350030080115007024040000c004106035081d060030b21032502d4035aa00d03409036811504150351000303c40c050220f0707601c05415a42d40420700e401d001581d9407400399290310308281a1100641611049000740c0072f8860408100b1040c81181c28001007140198010050303001c07600e402a803500c1c00060320488501c01c3d443c4455611707015001e0015075003004034405289801401581d805481c02111054004003600d074850399031410307164a6074482c500000941c4059200601749850030858404015010680c2e4090b1034003603500d1146003012600c44501c000009001410b01d41041000c41c8442c0459030b081d05217a03008503000301c0ca480d627940d40d108241c1d0240580701c90aa6001ca0290074803581031205141695003180c040c0c4d03c5040410010380d1650701140e24041c0c60344500060b8045490031f4005201684030540010a030300d503a02c03400f8105a0059800911900500c4008507145000c1c2e000c20114440650041007130034200f514151906803625036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 732539100 1250 732537850 732537881
    0x302060f1b0d02070c05010906080a0b0a03140607111903050c12070b04050105070e09010905060f1306061202030405031b0c0415090510030209130606090603051507180306 75
    0x50245103084041c00501d2003281d02000141da51884d410801038481054000c06e040200d04081004030307980c080f000607000340710a40700184144800000810012070340d030009003001000ca030002810400400d070184100d0880d1590b1001e000c01d280d4054607016100144419140740300201e034040307445440a0601440c41c041203e14542d00a401140c4982000c1c0040750343e0041d810400040001c00e00071182c0000541c101045621340d00c0c00040d0100c0d105000700700b4000c0e0340e44000380c13040d504d00e000b001285034058001c1100418070341c0228050700031801018046140455031140c154424800c592080d90090301650405045c80c07401c0c00040041081a0341d42d2040c581d815003d5500e82c0304450106504e640000c03c1a0303c3c0042004c1603402c0101030500e00600b0f64800c01c0903899401d252a030004c0460903550045556290103401482c09400210740c0c145446804410042d00040f00440c0d000d1002c0d030992555280702c421215207056000201c1101c00040c82000000c0d10f5070407052450301d0802 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 732540350 1250 732539100 732539131
    0x6180307050a08010c140405010906050903010b0a0e010623040603090302030408010608010507090602010e0a060c0903062909220f060c020a11010e01020309060f041a130906030302060f 81
    0x40000c18005940c0c1080c106655200d409444103038011600310f141d6a001210301b03051914010003c0c20805192140032f06000340024449070994081d40300e0a281ca1004100149841c1c03298419840b00c1d109014040c003044420030780c481c00c0103a007501a402000c80000a03840e003403d000c401c6014100415044040d44018040030034132090a001d40d1019145800001030640303032444005000d61502d501c00c00c10b5926011820307c0000d80800e0001459800c140d0200d0354140c140c0c000c4984021941c8064050352030001040807203801c50130304028554207400b03044400340905042020000f000e4905030702d02c04240308201801c8044100c40107905020741c24484030024141c8428082e600c000c102180103803c07a800480421280400f001b00081c400c3c03910048c0d4809085c0040e503684950102c0074032604000c50203150303501c0c140c021107028102c0751104001c03104031080d5050f0203411038200d0661000c00e9900110f01d00443d40f068000301c1384c00d17038000c14141c0c0b910703401c0e00c402d00c001804005140c201d81 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 732541600 1250 732540350 732540359
    0xe3c0a0b06091c02040507090312030e03090301020f1306050306030312091c110d0503011a031f06090303080f06011202030406090c14011101050f0123030703110f09040206180307 78
    0x1020005620080c040c52840d0f2105244108412180010654802d01201c0344092001c14041344101501c40007500340061140b61410380c842c07035070043c0c0b000d01b40d0643c0002101c840603d44440980f0100403003401c0c1d01007643e00c4800030741701c500044500d55003540c428041ca43d04e031001c115a10742c01c000c06100350780414203100186400e4400382440342004c0340c240030580020001c200302103481d1440c585441402d55040c50031102c803000764249040c062000120200b1500d001c011100c030280e0707040d030780f903983e0081d600e80000d840c00c48580300c142c01140380c54000820907086150081d11a84051356902680c000031030202d002900068000d484140da01e12070240024801030720100582400070600ca480c104980005216080190308442a0790624040c4408806210b8a2506440e04141a103842c5035505907a00683c03194070f56000d5040c85001c00000a0086602686802c10010740c1e101003104201824403c5544060f10002d4110008000c18401e030010380c2c140807089100141035550603940c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 732542850 1250 732541600 732541609
    0x20409062c19060e071d03031611090405010b130908040501050d0e10051b04081c1202030c0a110c0306010504051e0c0a091508011a040e3c0a0b0609 65
    0x19500301a00100c035440a00880c0d0f9000700080640e2180034400d02d10a8011b10041fa80368000c03645ea44580c5001e203100c0c0401c2080300c840c0600c08070b1011309500080d03d0076050650183c08003540c1a030044080001d00c40701440280509020250040300c000d29007864038004440a912010340c12040c90b5a6210f0134280318010f100111f5000061340c1e0101d19400d10030314400144040c2042d0140c0510200010409420041028030111054901c40c101580c08000184c0710022044450f0300007a10000c1001100540d400160003400c40c142d8036121020f0204003100d0391002400f0002da410391111004020506e4281c1140780e10101c901702e01c80402011046004031420203651507041c074140401c504812940c482403441c000c01e1040d00c50b060051000c18064a250018003610814100d52800c44090000d001704480080c203811208449515240350b0b0000b03401803141242e00c00c08041c00b500202c0d401c40f94400e0141e8107000c0c218003010f80b929095403009228860f00345401c07030300522501040b0b984 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 732544100 1250 732542850 732542861
    0x3030e040b190801060b1c0504050f03070c1a0315130e010e06041b05060a0c0f120f080109050903090f0f101d011e0e180109020409062c19 61
    0x444800540c8990a02c9201c81c01e4500d940c020340c451040a01c00488401040307d50b104004640c603500042c0e64032141040f5042c04043c0c0d00c9440301d8480042c1000c100880701841004449903192003484032131208a40b4185440282c0b003091724800501a550034900c0d11000c00c052001c21010700244038524996040c0c250b4202e4031504409412007800c20007440003074401040190880f41260526908200c001156400703464840f40800140400c80004c200f46660f60304900390b000b02c01d16000000401e4002c10000254462100242503074000242e4204a0b0207500d0180c80360401842c2400d800009000c0408003070b1204a91118090640b01202d03129400c00005066650750b60980ca83e81561051485480103c0028100020300c1d0800b060510007008034101c440051601c11a01c250030b800240c201b803006885a20840c101c2c40c00040d04860b1580200100c1d12662414060a5a101521415460326a0204081c00ca00c0002109036060062089902a00d40484180f003d160007118000320352 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 732545350 1250 732544100 732544129
    0x1b090141041d060c0a090509040b0a0e010905060105190b040902220e13021305090309040c110303040f1407081b0603070c080d0e16031106031003030e040b 68
    0x862145404203400c15015122030482d120b40b181c03000864641c00b05035220001010002c0f20540400c095455070701c5214584010040140659078500b0a410134074101807045d10707010380303651501003000014a0107004603044190410042c01c0c6a03031810062010802042c1890b02d60710002c0c0c0004111442120041c0000d404d18910042e00e844031121085076440b003440c12203001c03400100c8100b096100015410f64000141104034050b0384451001c100518024403001c15100d042c8410000220000006000311080c1200c0030301403d82e4400059a9405c01e00f60481130540082000401007101800c428082e940310b01f080b40904200038001c282409600d0300300f100300760030060402d010408112043d001c0d01808503a5245141009000640150142d0070001c0c0030460104035461416440e03031002c1c0caa076805c24140d030a5200c0c070174100c0404a54170701080b90101e1907903404410034202182070720710a0007044100c1c0101411f40d102503441440b1820389a03880341d114201e1049540360721000e0b040c8407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 732546600 1250 732545350 732545459
    0x120b13050f070216260303070309020a090c090e06011709030403060c050c0c041d0a110405070306050904201c050618150a020f16051b0901 61
    0x50030080a000d00901002d4207440443d0b221819509071502020f1440007143c4a80035001c4d551038106500511100c2c10f068160104d00000c004c226250f50503811407501c480c42180d25809160310384140c001101c141c040d1460001c2c55181d400c1c06000b605844060300141c05043c01c4010030350b200303001c0034000c400701d408001e0381e040403504100704040c50042e9a041c0b480340c1041801e10080111250340c540c5c45a03001c900c5030352150003895040340c40340c40c000b003003902400a540c12030403181070104806c078007240c685020b00c0c07030301c0c0000d042c4900c64403c0304e080c1d540c028600d00c00b030f803516160182c0511074003c980b902d20300c1101e0218040e03500c00d03260348100340c4102140c104004240c10440d042000040410020071b040788610b00904078041801d284808003080d040c3c0041e01d60f600301c0c400902648441c500051000101e842c030075690408614400c80c0726004075003c0c0907001070b0f0900c0d40e040c088510307904440c02c1c0e0014801c0480b101400c0e4008010a080e40340f02010a00c1144000361194a002080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 732547850 1250 732546600 732546611
    0x72904060c03020c180c070201090e1f091505010818031c1503030e061b250b04050a0e0c0903101b05070804030303020c0a05010c02010507032a120b13 66
    0x2c040d014044011181801c684039501000e42d01100c020f180700040200c85110360006000302117a000341d1052015180c4240031281a1510b4851410292380380030040181002c00c800019155205010b052031500981d804245070034681070040d50703a0400507100b58500e68410340c5410301c07060200080e2410605005900300c3c1d03400a05401021140c080613210814140c2160500100e07400105a43c0003800503900c551740d030307008a602c403403864000c00c140007128081d0b000821020f90102003007040c4104055920b2120568a481200140c0b00b1489403a4010100c400304204003025003446075400b85010140074600040c850010381400d041002c81c1c2e5800d80da903410700481e0448403242914050707060406a02d0b1104030b8458503034601452200074105a00014401c41e40842800080800745e409002403000b6420030300061b001c0c010403a9640002480c1600d844582c1c24404001540d45100c140103010210742400d00720f030078640b0322001c0c520480d20340710200d5041e1148900390812203118840010b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 732549100 1250 732547850 732547853
    0x11010e1207050907170a0b0a1e061d150c1608060a090c0b0d06170a0b160905180406110708092b050a140a050d0822060212061002072904060c 62
    0x148c400f090f821558441100c4400c1028800e030480c2090300307442a500300394400704007002806004104c03160700346401c138400c00c0e180c0d042c0c101c00070041c0016030000003e40e0300032031a2224851082410303200e2015540e1001c804100d030621164040b004903030107141d06040ba2603c4a1072400164000c40b03d0f1054956517030010480100c00a9404002074200c0010b40120034035038a401000081c09407000151440d50402a60001e01400103803009180140400c400c207040301c031105004020889040d500a42091201c010710072400003103d503c44c0d400700321103041c024104c05002c840804403c40c2c1c0b04d44013078060805030f001c41c030656040c2da20b40715070000e1944002c1c924010400415240d9103180c01c0e408002c0100c0020000b042514803540300c5c0c60440c640799165814110b030741c08081400c498083c50510034405100d8150014036180b04004424401915420203125600404842c12801078102400500020300981c001c2e412842e5010300720b50310001031070804801580581e1080001c9138146030b1000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 732550350 1250 732549100 732549109
    0x80c28050c010c0f0207031506030204050f0a06080c280801050a1a090103170a03110a030506190513020903011b030606020d080606070212010e0105010311010e1207050907170a0b 78
    0x3d420030091420314030904c00c51a002c1d565481c50302005180801200410382c0403510390b80700d0300003150010424811801c1c42000b00a0b040420740e02c0303a050b641018400300d800c010005110940c1d900113840000c00200d01d5006180101c0040001075040903c8180000c4541090080c203000d89070720000001d410100e9805080c0c880100d00442c1e0088910a004101064203030360800e010804242c0d07200d45d11781c1403010440040103030700e9111088040110f800d00722a523050384407a01c20807003a50012500d4840c50300e1402400351034801c40e68082c0d940e0505a19502954001e8000080d010700041080100108034a1040740c1c0c00f500040000d958440030402c5035810007111040d1911414003040c142020b1011480501c50540064041c02200400030700c01c0b0804d620408080c0c210b18000c00003940c50745000e04450b1480040d2900003a115411000140b40c02009109064034840050003070754178100c01d000e880000109200c0c18085682241c1e0501d80e100f900f102d205085600e00011041c4800c81080b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 732551600 1250 732550350 732550361
    0x501050c0a0f030e0304031218030b010914040b042312030901060e10050d0c0b031014060901081b090603040c06030f09030c060914011404020306090d080c28050c01 72
    0xb201014142283c83e22030349004000c07074007a242c0101c0302103100380c0c11903020b03070310350340d0b2560a0325150503c0f000020034405880c040780d06032002e4030014088021005c00c60fa25a40041c6c402a1803140c0d03090101d00041c0780a02e100c000004051290340c1c01d20100d001143c1880514100e01101003400810004c0500c000e03ca00c0300640350061504a045c01d000940600c0d1000900510307005101402440d0240906842043c00411200b08155541d00c1d144160950035000d070302c562481d5240303a41c0c0881c0c00b13140407820b03525841e906a50b07642c0142d448440f01101c142440700c401d468404200110801600c920300150300c40c1317018401101c00e10340340190040454600c1e48603e481c80e4640500c0c000003a600c200d41007040f81d000f010200d000c04050901c1250510f03110741c2200150301c2e02d01390803081c661040350303244100d008070280e4000c2e98030340b0003142d02ca41c0081c202c04002000c220025240f000da0001400c100c131201c943c0ea92291114200c5081e4040400d40b80341d0110b40007180d000181403090140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 732552850 1250 732551600 732551627
    0xf02030a050f01030503031603060b04030f020a080106270905011508070803030106051c06080f070e06040203040807020607051606090311010f020d11010b03060f061e09060d030201090501050c0a 85
    0x4000b100d42c5561945503d038003020703084202c0c01140c01000c0d0a4617210f5001300c000703000304070329a0fa552607403442d0010705181c104074200e00a5049410015480700107102d0703601122102c010030f403040f80c81d1009030710b61011a02c03481d011480e5143c4101c0f0103c0c40034484c4081d130318003042c8942100380c2020301951078800241d1103500d00368010001403241c41d900a0545409032107696079580118120f03119400070b00f056409c042028840c13145120700709400010340b80b0445112031010800394946000b0b00c0103901c811100541000001c0000c00c00500b404801815818001c0c400e5a019602e00f004511391184560310402c0050f030840001d02c01c2c880503200e0705504010901b080602c82000c60000703511803c04d0000c0e803060016940075415403200c03c3d0402200d800700101601d109181c69544180303100d074241c1d180781c042c600204400341d042c0e40460114020300d4000b031a021036541e40c0c0c42003203202c041d030309400c030215501d40c002c10000840c00d0007194001c0f03800c501c3c03140e206c1180700710050070803038600c55 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 732553956 1106 732552850 732552871
    0x5190303020a1103040b120430080109090210080c0c101b021b1c2906040605010903080705010e031c0c0915081503010f02030a05 57
    0xe054150403a00d803075031020744502d0490703034a0040b40030f00d80300480c0401201150840307401c3d500323502512648884e56680c42d225400c10f108000784052403510a500c0c41410140ca8210f04003501400b64100c040241d102290001500070281f40075407402c4c412040f01081c116100481111001900034003180c00b802001c46881e401804c520305020301e628011070186032032a2002c5180f40084200074606001a00c0580412580200f07503140c1d0490042001d580000165110001c410f546600f5800d151040784800d0a8040805005000601c65032403c801032107180c0c0c00541d04001d0304d80065442d51182c02300d1500b1401450300d506008001d10000c1a40a0f0030031001000760460500c0710001d01c48840e083c04d0a84043d29a806034002c00c003460004002641d2140c14810b5004078071144085241c0c4080012a08440710b0a15600c0455000000c0021161141c09060b070072120401 = true := by decide +kernel

theorem cover : BRFrame.Cov 732374100 732553956 := by
  have h0 := BRFrame.cov_init 732374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 732374100 ≤ n) (h2 : n < 732553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
